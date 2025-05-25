import subprocess
import tempfile
import pathlib

ROOT = pathlib.Path(__file__).resolve().parents[2]
MB_DIR = ROOT / 'tests' / 'microbench'


def build_and_run(sources):
    with tempfile.TemporaryDirectory() as td:
        exe = pathlib.Path(td) / 'bench'
        cmd = [
            'gcc',
            '-std=c11',
            '-I', str(ROOT),
            '-I', str(ROOT / 'src-headers'),
        ]
        cmd.extend(str(s) for s in sources)
        cmd.extend(['-o', str(exe)])
        subprocess.check_call(cmd)
        return subprocess.check_output([str(exe)]).decode()


def main():
    cap_out = build_and_run([
        MB_DIR / 'cap_verify.c'
    ])
    print(cap_out.strip())

    ctx_out = build_and_run([
        MB_DIR / 'context_switch.c',
        ROOT / 'src-kernel' / 'swtch64.S',
    ])
    print(ctx_out.strip())


if __name__ == '__main__':
    main()
