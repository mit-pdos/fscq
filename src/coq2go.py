#!/usr/bin/env python3

import json
import sys
import os

(_, fn) = sys.argv

## Coq can produce very deep JSON data structures..
sys.setrecursionlimit(10000)

## XXX hack for now
import_prefix = 'codegen/'

this_pkgname = None

with open(fn) as f:
  s = f.read()
  d = json.loads(s)

def coqname_in_mod(s):
  return 'Coq_' + s.replace("'", "_prime").replace(".", "_")

def coqname(s):
  global this_pkgname
  if '.' in s:
    (mod, rest) = s.split('.', 1)
    if mod == this_pkgname:
      return coqname_in_mod(rest)
    else:
      return '%s.%s' % (mod, coqname_in_mod(rest))
  else:
    return coqname_in_mod(s)

varname_ctr = 0
def varname():
  global varname_ctr
  varname_ctr += 1
  return "__v_%d" % varname_ctr

def gen_fix_expr(names, lambdas):
  s = ''
  s += 'func (__fixarg CoqT) CoqT {\n'

  for name in names:
    s += '  var %s CoqT\n' % coqname(name)

  for (name, lambd) in zip(names, lambdas):
    s += gen_expr_assign(lambd, coqname(name))

  s += '  return %s.(func (CoqT) CoqT)(__fixarg)\n' % coqname(names[-1])
  s += '}\n'
  return s

def gen_expr_assign(e, retname):
  s = ''

  if e['what'] == 'expr:lambda':
    lambda_name = retname

    closure_vars = []
    for argname in e['argnames']:
      closure_var = varname()
      closure_vars = [closure_var] + closure_vars
      s += '%s = func (%s CoqT) CoqT {\n' % (lambda_name, coqname(argname))
      s += '  var %s CoqT\n' % closure_var
      lambda_name = closure_var

    s += gen_expr_assign(e['body'], lambda_name)

    for closure_var in closure_vars:
      s += '  return %s\n' % closure_var
      s += '}\n'

  elif e['what'] == 'expr:fix':
    fixnames = [x['name'] for x in e['funcs']]
    fixlambdas = [x['body'] for x in e['funcs']]
    s += '%s = %s\n' % (retname, gen_fix_expr(fixnames, fixlambdas))

  elif e['what'] == 'expr:case':
    switchvar = varname()
    s += 'var %s CoqT\n' % switchvar
    s += gen_expr_assign(e['expr'], switchvar)
    s += 'switch __typesw := (%s).(type) {\n' % switchvar

    have_default = False
    for case in e['cases']:
      body = gen_expr_assign(case['body'], retname)
      pat = case['pat']

      if pat['what'] == 'pat:constructor':
        s += 'case *%s:\n' % coqname(pat['name'])
        for idx, argname in enumerate(pat['argnames']):
          s += 'var %s CoqT = __typesw.A%d\n' % (coqname(argname), idx)
          s += 'var _ = %s\n' % coqname(argname)
        s += body

      elif pat['what'] == 'pat:wild':
        s += 'default:\n'
        s += '  var _ = __typesw\n'
        s += body
        have_default = True

      elif pat['what'] == 'pat:rel':
        s += 'default:\n'
        s += '  var _ = __typesw\n'
        s += '  var %s CoqT\n' % coqname(pat['name'])
        s += '  %s = %s\n' % (coqname(pat['name']), switchvar)
        s += body
        have_default = True

      else:
        s += 'UNKNOWN PAT %s' % pat['what']

    if not have_default:
      s += 'default:\n'
      s += '  var _ = __typesw\n'
      s += '  %s = nil\n' % retname
      s += '  panic("switch returned")\n'
    s += '}\n'

  elif e['what'] == 'expr:rel':
    s += '%s = %s\n' % (retname, coqname(e['name']))

  elif e['what'] == 'expr:global':
    s += '%s = %s\n' % (retname, coqname(e['name']))

  elif e['what'] == 'expr:constructor':
    arg_vars = []
    for a in e['args']:
      argvar = varname()
      arg_vars.append(argvar)
      s += 'var %s CoqT\n' % argvar
      s += gen_expr_assign(a, argvar)

    s += '%s = &%s{ %s }\n' % (retname, coqname(e['name']), ', '.join(arg_vars))

  elif e['what'] == 'expr:exception':
    s += '%s = nil\n' % retname
    s += 'panic("%s")\n' % e['msg']

  elif e['what'] == 'expr:apply':
    funvar = varname()
    s += 'var %s CoqT\n' % funvar
    s += gen_expr_assign(e['func'], funvar)

    arg_vars = []
    for a in e['args']:
      argvar = varname()
      arg_vars.append(argvar)
      s += 'var %s CoqT\n' % argvar
      s += gen_expr_assign(a, argvar)

    apply_expr = funvar
    for arg in arg_vars:
      apply_expr = '(%s).(func (CoqT) CoqT)(%s)' % (apply_expr, arg)

    s += '%s = %s\n' % (retname, apply_expr)

  elif e['what'] == 'expr:dummy':
    s += '%s = CoqDummy\n' % retname

  elif e['what'] == 'expr:let':
    s += 'var %s CoqT\n' % coqname(e['name'])
    s += gen_expr_assign(e['nameval'], coqname(e['name']))
    s += gen_expr_assign(e['body'], retname)

  elif e['what'] == 'expr:axiom':
    s += '%s = nil\n' % retname
    s += 'panic("Axiom not realized")\n'

  elif e['what'] == 'expr:coerce':
    s += gen_expr_assign(e['value'], retname)

  else:
    s += 'UNKNOWN EXPR %s\n' % e['what']

  return s

def gen_header(d):
  global this_pkgname
  this_pkgname = d['name']

  s = ''
  s += 'package %s\n' % d['name']
  s += 'import . "gocoq"\n'
  for modname in d['used_modules']:
    s += 'import "%s%s"\n' % (import_prefix, modname)
  return s

def gen_ind(dec):
  s = ''
  for c in dec['constructors']:
    s += 'type %s struct {\n' % coqname(c['name'])
    for idx, typ in enumerate(c['argtypes']):
      s += '  A%d CoqT\n' % idx
    s += '}\n'
  return s

def gen_term(dec):
  v = varname()
  s = ''
  s += 'func () CoqT {\n'
  s += '  var %s CoqT\n' % v
  s += gen_expr_assign(dec['value'], v)
  s += '  return %s\n' % v
  s += '} ()'

  return 'var %s CoqT = %s\n' % (coqname(dec['name']), s)

def gen_fix(dec):
  e = gen_fix_expr([dec['name']], [dec['value']])
  return 'var %s CoqT = %s\n' % (coqname(dec['name']), e)

print(gen_header(d))

for dec in d['declarations']:
  if dec['what'] == 'decl:type':
    pass
  elif dec['what'] == 'decl:term':
    print(gen_term(dec))
  elif dec['what'] == 'decl:fix':
    print(gen_fix(dec))
  elif dec['what'] == 'decl:ind':
    print(gen_ind(dec))
  else:
    assert False, dec
