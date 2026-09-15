#!/usr/bin/env python3
"""Assemble the single-file deliverable `SpherePackingRefactored.lean` (Step 1 of
`RefactoringPlan.md`) from the module trees `CohnElkiesForMathlib/` and `CohnElkies/`.

Modules are concatenated in topological (import) order, each wrapped in a `section` named after
it, with their `import` lines removed (`import Mathlib` is kept once at the top). Duplicate
`private` declaration names across modules would clash in a single file and abort the assembly.

Run from the project root: `python3 scripts/assemble_single_file.py`.
"""
import collections
import glob
import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
LIBS = ['CohnElkiesForMathlib', 'CohnElkies']
OUT = os.path.join(ROOT, 'SpherePackingRefactored.lean')


def module_name(path):
    return os.path.relpath(path, ROOT)[:-5].replace('/', '.')


def module_path(name):
    return os.path.join(ROOT, name.replace('.', '/') + '.lean')


imports = {}
for lib in LIBS:
    for f in glob.glob(os.path.join(ROOT, lib, '**', '*.lean'), recursive=True):
        name = module_name(f)
        imports[name] = [l.split()[1] for l in open(f, encoding='utf-8') if l.startswith('import ')]

order, done = [], set()


def visit(m):
    if m in done or m not in imports:
        return
    done.add(m)
    for dep in imports[m]:
        visit(dep)
    order.append(m)


for lib in LIBS:
    for m in sorted(n for n in imports if n.startswith(lib + '.')):
        visit(m)

private = collections.defaultdict(list)
for m in order:
    for l in open(module_path(m), encoding='utf-8'):
        mm = re.match(r'^private (?:noncomputable )?(?:theorem|lemma|def|abbrev|instance|structure) ([^\s:({\[]+)', l)
        if mm:
            private[mm.group(1)].append(m)
dups = {k: v for k, v in private.items() if len(v) > 1}
if dups:
    print('duplicate private names (rename before assembling):')
    for k, v in dups.items():
        print(' ', k, v)
    sys.exit(1)

out = ['/-', 'Refactored single-file version of `SpherePacking.lean` (OpenAI, ten-proofs).',
       'Assembled automatically from the modules of `CohnElkiesForMathlib/` and `CohnElkies/`',
       '(each module wrapped in a section named after it) by `scripts/assemble_single_file.py`;',
       'see `RefactoringResult.md`.', '-/', 'import Mathlib', '']
for m in order:
    body = [l for l in open(module_path(m), encoding='utf-8').read().split('\n')
            if not l.startswith('import ')]
    while body and body[0].strip() == '':
        body.pop(0)
    while body and body[-1].strip() == '':
        body.pop()
    sec = m.replace('.', '_')
    out += [f'/-! ## Module `{m}` -/', '', f'section {sec}', ''] + body + ['', f'end {sec}', '']
open(OUT, 'w', encoding='utf-8').write('\n'.join(out) + '\n')
print(f'assembled {len(order)} modules; {sum(1 for _ in open(OUT, encoding="utf-8"))} lines')
