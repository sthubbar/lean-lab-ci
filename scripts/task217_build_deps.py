from pathlib import Path
import re, subprocess, sys, time
root = Path('.').resolve()
outroot = root / '.lake' / 'build' / 'lib' / 'lean'
mod = sys.argv[1]
seen = set()
building = set()
pat = re.compile(r'^import\s+(LeanLab(?:\.[A-Za-z0-9_\u00c0-\uFFFF]+)+)\s*$', re.M)

def source_for(m):
    return root / (m.replace('.', '/') + '.lean')

def out_for(m):
    return outroot / (m.replace('.', '/') + '.olean')

def build(m):
    if m in seen:
        return
    if m in building:
        raise RuntimeError('cycle ' + m)
    src = source_for(m)
    if not src.exists():
        print('SKIP external', m, flush=True)
        seen.add(m)
        return
    building.add(m)
    text = src.read_text(encoding='utf-8')
    deps = pat.findall(text)
    print('DEPS', m, len(deps), flush=True)
    for d in deps:
        build(d)
    out = out_for(m)
    if out.exists():
        print('HAVE', m, flush=True)
        seen.add(m)
        building.remove(m)
        return
    out.parent.mkdir(parents=True, exist_ok=True)
    t = time.time()
    print('BUILD', m, flush=True)
    cmd = ['lake', 'env', 'lean', '-R', '.', '-o', str(out), str(src.relative_to(root))]
    p = subprocess.run(cmd, cwd=root, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    print(p.stdout, end='', flush=True)
    print('DONE', m, 'code', p.returncode, 'sec', round(time.time()-t,1), flush=True)
    if p.returncode:
        raise SystemExit(p.returncode)
    seen.add(m)
    building.remove(m)

build(mod)
