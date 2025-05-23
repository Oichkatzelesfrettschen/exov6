#!/usr/bin/env python3
import subprocess, json, shlex, os, re, sys

def main():
    make_args = ["make", "-n"] + sys.argv[1:]
    try:
        output = subprocess.check_output(make_args, text=True)
    except subprocess.CalledProcessError as e:
        output = e.output
    commands = []
    for line in output.splitlines():
        line = line.strip()
        if not line:
            continue
        if not re.match(r'^(?:gcc|cc|clang) ', line):
            continue
        tokens = shlex.split(line)
        src = None
        for tok in tokens:
            if tok.endswith('.c'):
                src = tok
        if not src:
            continue
        cmd = line
        commands.append({"directory": os.getcwd(), "command": cmd, "file": src})
    if commands:
        with open('compile_commands.json', 'w') as f:
            json.dump(commands, f, indent=2)
    else:
        sys.stderr.write('No compile commands captured\n')
        return 1

if __name__ == '__main__':
    sys.exit(main())
