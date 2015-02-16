#!/usr/bin/env python3

import json
import sys

(_, fn) = sys.argv

pkgname = 'main'

with open(fn) as f:
  s = f.read()
  d = json.loads(s)

def coqname(s):
  return s.replace("'", "_prime")

def gen_expr(e, fixname = None):
  s = ''
  if e['what'] == 'expr:lambda':
    if fixname is not None:
      s += 'func (__fixarg CoqT) CoqT {\n'
      s += 'var %s CoqT\n' % coqname(fixname)
      s += '%s = ' % coqname(fixname)
    for argname in e['argnames']:
      s += 'func (%s CoqT) CoqT {\n' % coqname(argname)
      s += 'return '
    s += '%s\n' % gen_expr(e['body'])
    for argname in e['argnames']:
      s += '}'
    if fixname is not None:
      s += '\n'
      s += 'return %s.(func (CoqT) CoqT)(__fixarg)\n' % coqname(fixname)
      s += '}'
  elif e['what'] == 'expr:case':
    s += 'func () CoqT {\n'
    s += 'switch __typesw := (%s).(type) {\n' % gen_expr(e['expr'])
    for case in e['cases']:
      body = gen_expr(case['body'])
      pat = case['pat']
      if pat['what'] == 'pat:constructor':
        s += 'case *%s:\n' % coqname(pat['name'])
        for idx, argname in enumerate(pat['argnames']):
          s += 'var %s CoqT = __typesw.a%d\n' % (coqname(argname), idx)
          s += 'var _ = %s\n' % coqname(argname)
        s += 'return %s\n' % body
      else:
        s += 'UNKNOWN PAT %s' % pat['what']
    s += 'default:\n'
    s += 'var _ = __typesw\n'
    s += 'panic("switch returned")\n'
    s += 'return nil\n'
    s += '}\n'
    s += '}()'
  elif e['what'] == 'expr:rel':
    s += '%s' % coqname(e['name'])
  elif e['what'] == 'expr:global':
    s += '%s' % coqname(e['name'])
  elif e['what'] == 'expr:constructor':
    s += '&%s{' % coqname(e['name'])
    s += ', '.join(gen_expr(a) for a in e['args'])
    s += '}'
  elif e['what'] == 'expr:exception':
    s += 'func () CoqT {\n'
    s += 'panic("%s")\n' % e['msg']
    s += 'return nil\n'
    s += '} ()'
  elif e['what'] == 'expr:apply':
    s = gen_expr(e['func'])
    for arg in e['args']:
      s = '(%s).(func (CoqT) CoqT)(%s)' % (s, gen_expr(arg))
  elif e['what'] == 'expr:dummy':
    s += 'CoqDummy'
  else:
    s += 'UNKNOWN EXPR %s\n' % e['what']
  return s

def gen_header(d):
  s = ''
  s += 'package %s\n' % pkgname
  s += 'import . "gocoq"\n'
  return s

def gen_ind(dec):
  s = ''
  for c in dec['constructors']:
    s += 'type %s struct {\n' % coqname(c['name'])
    for idx, typ in enumerate(c['argtypes']):
      s += '  a%d CoqT\n' % idx
    s += '}\n'
  return s

def gen_term(dec):
  return 'var %s CoqT = %s\n' % (coqname(dec['name']),
                                 gen_expr(dec['value']))

def gen_fix(dec):
  return 'var %s CoqT = %s\n' % (coqname(dec['name']),
                                 gen_expr(dec['value'],
                                          fixname = dec['name']))

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
