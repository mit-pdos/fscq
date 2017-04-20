def FlagsForFile( filename, **kwargs ):
  return {
    'flags': [ '-x', 'c', '-Wall', '-Werror', '-pthread' ],
  }
