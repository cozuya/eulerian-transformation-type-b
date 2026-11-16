#!/usr/bin/env python3
"""Audit build pins, source mechanisms, and printed axiom dependencies.

This checks what the build used and what the theorems depend on; it does not check
mathematical truth.
"""
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parent.parent
STANDARD = {'propext', 'Classical.choice', 'Quot.sound'}
TARGETS = {name: STANDARD for name in (
    'TypeBEulerianVerification.real_rooted',
    'TypeBEulerianVerification.real_rooted_strong',
    'TypeBEulerianVerification.zero_vector',
    'TypeBEulerianVerification.degree_zero',
    'TypeBEulerianVerification.basis_image',
    'TypeBEulerianVerification.sequence_exists',
    'TypeBEulerianVerification.map_exists',
    'TypeBEulerian.mathcalB_coneInput_splits',
    'TypeBEulerian.mathcalB_coneInput_realRooted',
    'TypeBEulerian.mathcalB_coneInput_zero',
    'TypeBEulerian.mathcalB_coneInput_n_zero',
    'TypeBEulerian.b_eval_mul_derivative_nonpos',
)}
LEAN_FILES = (
    'TypeBEulerian.lean', 'Verification.lean', 'TypeBEulerian/Basic.lean',
    'TypeBEulerian/EulerNumerator.lean', 'TypeBEulerian/CommonInterlacer.lean',
    'TypeBEulerian/MainTheorem.lean',
)
FORBIDDEN = re.compile(r'\b(sorry|sorryAx|admit|axiom|unsafe|implemented_by|extern|csimp|'
                       r'opaque|native_decide|decide_cbv|ofReduceBool|skipKernelTC|debug|'
                       r'notation|infix|infixl|infixr|prefix|postfix|macro|macro_rules|syntax|'
                       r'elab|elab_rules|instance|attribute|export)\b|@\[')


def require(condition, message):
    if not condition:
        raise SystemExit('FAIL: ' + message)


def output(*args):
    return subprocess.check_output(args, cwd=ROOT, text=True).strip()


def manifest_hashes():
    entries = {}
    for line in (ROOT / 'SOURCE_SHA256SUMS').read_text().splitlines():
        digest, name = line.split('  ', 1)
        require(re.fullmatch(r'[0-9a-f]{64}', digest), 'Malformed source digest')
        path = ROOT / name
        require(path.resolve().is_relative_to(ROOT), 'Source path escapes project')
        actual = hashlib.sha256(path.read_bytes()).hexdigest()
        require(actual == digest, 'Source digest mismatch: ' + name)
        require(name not in entries, 'Duplicate source digest: ' + name)
        entries[name] = actual
    return entries


def axiom_reports(transcript):
    require(not re.search(r'\b(?:warning|error):', transcript),
            'Compiler warning or error in the restatement check')
    records = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", transcript)
    found = {}
    for name, axioms in records:
        require(name in TARGETS, 'Unexpected axiom report: ' + name)
        require(name not in found, 'Duplicate axiom report: ' + name)
        deps = {a.strip() for a in axioms.split(',') if a.strip()}
        require(deps == TARGETS[name], 'Unexpected axiom dependencies: ' + name)
        found[name] = sorted(deps)
    require(set(found) == set(TARGETS), 'Missing axiom reports')
    return found


mode = sys.argv[1]
if mode == 'pins':
    pin = json.loads((ROOT / 'TOOLCHAIN.json').read_text())
    require((ROOT / 'lean-toolchain').read_text().strip() ==
            'leanprover/lean4:v' + pin['lean_version'], 'Toolchain file')
    require(output('lean', '--short-version') == pin['lean_version'], 'Lean version')
    require(output('lean', '--githash') == pin['lean_commit'], 'Lean commit')
    require(output('lake', '--version').startswith('Lake version ' + pin['lake_version']),
            'Lake version')
    manifest = json.loads((ROOT / 'lake-manifest.json').read_text())
    packages = {p['name']: p for p in manifest['packages']}
    require(packages['mathlib']['rev'] == pin['mathlib_commit'], 'mathlib revision')
    require(packages['mathlib']['inputRev'] == pin['mathlib_tag'], 'mathlib tag')
    require(packages['RealRooted']['rev'] == pin['realrooted_commit'], 'RealRooted revision')
    for package in manifest['packages']:
        require(package['type'] == 'git' and
                re.fullmatch(r'[0-9a-f]{40}', package['rev']),
                'Unpinned dependency: ' + package['name'])
        require(output('git', '-C', '.lake/packages/' + package['name'],
                       'rev-parse', 'HEAD') == package['rev'],
                'Dependency checkout: ' + package['name'])
        rr_toolchain = ROOT / '.lake/packages' / package['name'] / 'lean-toolchain'
        if package['name'] in ('RealRooted', 'mathlib'):
            require(rr_toolchain.read_text().strip() == 'leanprover/lean4:v' + pin['lean_version'],
                    'Dependency toolchain: ' + package['name'])
    print('PASS: Lean, Lake, toolchain file, RealRooted, mathlib, and every locked dependency agree.')
elif mode == 'sources':
    paths = sorted(ROOT / name for name in LEAN_FILES)
    found = sorted(p for p in ROOT.rglob('*.lean')
                   if not any(part in ('.lake', '.tools', '.build') for part in p.relative_to(ROOT).parts))
    require(found == paths, 'Unexpected Lean file inventory: ' +
            ', '.join(p.relative_to(ROOT).as_posix() for p in found))
    for path in paths:
        name = path.relative_to(ROOT).as_posix()
        match = FORBIDDEN.search(path.read_text())
        require(match is None, f'Forbidden mechanism {match and match.group(0)!r} in {name}')
    print(f'PASS: {len(paths)} Lean files; no sorry, admit, axiom declarations, native_decide, '
          f'unsafe code, implemented_by, extern, csimp, kernel-check options, attributes, '
          f'instances, notation, or macros.')
elif mode == 'axioms':
    transcript = Path(sys.argv[2]).read_text()
    found = axiom_reports(transcript)
    for name in sorted(found):
        print('PASS:', name, 'uses exactly', ', '.join(found[name]))
    print('PASS: no sorryAx, native_decide axiom, or project-specific axiom in any audited theorem.')
elif mode == 'hashes':
    for name, digest in manifest_hashes().items():
        print(digest, name)
elif mode == 'record':
    exit_code = int(sys.argv[2])
    commit = None
    try:
        git_root = Path(subprocess.check_output(
            ['git', 'rev-parse', '--show-toplevel'], cwd=ROOT, text=True,
            stderr=subprocess.DEVNULL).strip()).resolve()
        if git_root == ROOT:
            commit = output('git', 'rev-parse', 'HEAD')
    except subprocess.CalledProcessError:
        pass
    dirty = output('git', 'status', '--porcelain', '--untracked-files=no') != '' if commit else None
    actual_axioms = axiom_reports((ROOT / '.build/kernel-check.log').read_text()) if exit_code == 0 else None
    data = {
        'verification_exit_code': exit_code,
        'status': 'PASS' if exit_code == 0 else 'FAIL',
        'started_utc': sys.argv[3],
        'finished_utc': sys.argv[4],
        'repository_commit_at_run': commit,
        'tracked_worktree_dirty': dirty,
        'identity_note': 'Precommit verification is identified by source hashes; timestamps do not establish priority.',
        'trust_note': 'All audited theorems use only propext, Classical.choice and Quot.sound; '
                      'they are checked by the Lean kernel, including the RealRooted lemmas they use.',
        'toolchain': json.loads((ROOT / 'TOOLCHAIN.json').read_text()),
        'source_sha256': manifest_hashes(),
        'audited_theorems': sorted(TARGETS),
        'expected_axioms': {k: sorted(v) for k, v in sorted(TARGETS.items())},
        'axiom_dependencies': actual_axioms,
        'transcript': 'verification.log',
        'theorem_types_and_axioms': 'kernel-check.log',
    }
    (ROOT / '.build/verification.json').write_text(json.dumps(data, indent=2) + '\n')
    print('Wrote .build/verification.json')
else:
    raise SystemExit('Unknown audit mode: ' + mode)
