import os


if __name__ == '__main__':
    import sys

    if len(sys.argv) <= 2:
        print "python crash-parse.py <crashlogs-dir> <output-dir>"
        quit()

    tmp_dir = sys.argv[1]
    out_dir = sys.argv[2]

    crash_states = set()
    for filename in os.listdir(tmp_dir):
        if not (filename.startswith('crashlog') and filename.endswith('out')):
            continue
        crash_state = []
        with open(os.path.join(tmp_dir, filename), 'r') as f:
            for line in f.readlines():
                if line.startswith('Filesystem'):
                    break
                crash_state.append(line.strip())
            crash_state = '\n'.join(crash_state)
            crash_state += '\n'
            if crash_state not in crash_states:
                print "Found new crash state"
            crash_states.add(crash_state)

    for i, crash_state in enumerate(crash_states):
        with open(os.path.join(out_dir, 'crashstate-{0}.out'.format(i)), 'w') as f:
            f.write(crash_state)
