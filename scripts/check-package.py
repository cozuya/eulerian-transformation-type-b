#!/usr/bin/env python3
"""Check the package inventory, source manifest, evidence, and local documentation links.

SOURCE_SHA256SUMS covers every file that can affect verification or that preserves
supplied material. Documentation is inventoried and link-checked but not hashed, so that
editing prose does not invalidate recorded verification evidence.
"""
import hashlib
import json
import os
from pathlib import Path
import re
import sys
from urllib.parse import unquote, urlsplit

ROOT = Path(__file__).resolve().parent.parent
LEAN = {
    'TypeBEulerian.lean', 'Verification.lean', 'TypeBEulerian/Basic.lean',
    'TypeBEulerian/EulerNumerator.lean', 'TypeBEulerian/CommonInterlacer.lean',
    'TypeBEulerian/MainTheorem.lean',
}
ORIGINAL = {'original/' + n for n in (
    'MANIFEST.sha256', 'REPORT.md', 'requirements.txt',
    'research/derangement/DB_OPERATOR_APPENDIX.md',
    'research/derangement/GENERAL_CONE_PROOF.md',
    'research/derangement/check_refined_cone.py',
    'research/derangement/check_refined_cone_n14.json',
    'research/operator/GENERALIZED_CONE.md', 'research/operator/PROOF.md',
    'research/operator/check_generalized_cone.py',
    'research/operator/check_generalized_cone.stdout.txt',
    'research/operator/check_operator.py', 'research/operator/check_operator.stdout.txt',
    'research/refinement/common_a_interlacer.out', 'research/refinement/common_a_interlacer.py',
    'research/refinement/common_interlacer_proof.md',
    'research/refinement/identity_and_sign_check.out',
    'research/refinement/identity_and_sign_check.py',
    'research/refinement/ptype_expansion.out', 'research/refinement/ptype_expansion.py',
    'research/root/LIFT_LEMMA.md', 'research/root/check_sympy_independent.py',
    'research/root/logs/check_sympy_independent.json',
    'research/root/logs/checker_development.txt', 'research/root/logs/packet_probe_n18.txt',
    'research/type-b-eulerian-packet/code/eul.py',
    'research/type-b-eulerian-packet/code/typeB_conjecture_probe.py',
    'research/type-b-eulerian-packet/outputs/typeB_conjecture_probe_n18.txt',
)}
SOURCES = LEAN | ORIGINAL | {
    'lean-toolchain', 'lakefile.toml', 'lake-manifest.json', 'TOOLCHAIN.json',
    'verify.sh', '.gitignore',
    'scripts/install-lean.sh', 'scripts/fetch-deps.sh', 'scripts/audit.py',
    'scripts/check-package.py',
}
DOCS = {
    'README.md', 'PROOF.md', 'PRIOR_ART.md', 'PROVENANCE.md', 'VERIFICATION_REPORT.md',
    'REPRODUCE.md', 'CITATION.cff', 'LICENSE', 'original/README.md',
}
EVIDENCE = {'evidence/' + n for n in ('verification.log', 'kernel-check.log', 'verification.json')}
GENERATED = {'.git', '.lake', '.tools', '.build', '.crbuddy', '__pycache__'}
# GitHub's math renderer rejects \operatorname and \phantom ("The following macros are not
# allowed"). The rest are avoided because their support is unconfirmed or they are unsafe.
BLOCKED_MATH = re.compile(r'\\(operatorname|phantom|tag|boxed|text|DeclareMathOperator|'
                          r'newcommand|renewcommand|def|href|url|class|style|cssId|require|'
                          r'html[A-Za-z]*)\b')


def math_segments(text):
    """Math rendered by GitHub: ```math fences, $$...$$ and $...$ outside code."""
    segments, prose, fence, buffer = [], [], None, []
    for line in text.splitlines():
        stripped = line.strip()
        if stripped.startswith('```'):
            if fence is None:
                fence, buffer = stripped[3:].strip(), []
            else:
                if fence == 'math':
                    segments.append('\n'.join(buffer))
                fence = None
            continue
        (buffer if fence is not None else prose).append(line)
    rest = re.sub(r'`[^`\n]*`', '', '\n'.join(prose))
    segments += re.findall(r'\$\$(.*?)\$\$', rest, flags=re.S)
    rest = re.sub(r'\$\$.*?\$\$', '', rest, flags=re.S)
    return segments + re.findall(r'\$([^$\n]+)\$', rest)


def require(condition, message):
    if not condition:
        raise SystemExit('FAIL: ' + message)


def main():
    require(sys.argv[1:] in ([], ['--sources-only']), 'Unexpected arguments')
    sources_only = sys.argv[1:] == ['--sources-only']
    expected = SOURCES | DOCS | EVIDENCE | {'SOURCE_SHA256SUMS'}
    required = SOURCES | {'SOURCE_SHA256SUMS'} | (set() if sources_only else DOCS | EVIDENCE)
    present = set()
    for parent, dirs, files in os.walk(ROOT):
        dirs[:] = [n for n in dirs if n not in GENERATED]
        for name in files:
            path = Path(parent) / name
            require(not path.is_symlink(), 'Package must contain regular files')
            present.add(path.relative_to(ROOT).as_posix())
    require(not (present - expected), 'Unexpected package files: ' +
            ', '.join(sorted(present - expected)))
    require(required <= present, 'Missing required package files: ' +
            ', '.join(sorted(required - present)))

    hashes = {}
    for line in (ROOT / 'SOURCE_SHA256SUMS').read_text().splitlines():
        digest, name = line.split('  ', 1)
        require(name in SOURCES and name not in hashes, 'Invalid manifest inventory: ' + name)
        require(re.fullmatch(r'[0-9a-f]{64}', digest), 'Malformed digest')
        require(hashlib.sha256((ROOT / name).read_bytes()).hexdigest() == digest,
                'Source hash mismatch: ' + name)
        hashes[name] = digest
    require(set(hashes) == SOURCES, 'Incomplete source manifest')

    # The preserved original material must still match the subset of its own manifest.
    for line in (ROOT / 'original/MANIFEST.sha256').read_text().splitlines():
        digest, name = line.split('  ', 1)
        require('original/' + name in ORIGINAL, 'Unexpected original manifest entry: ' + name)
        require(hashlib.sha256((ROOT / 'original' / name).read_bytes()).hexdigest() == digest,
                'Original material changed: ' + name)

    # Math in the preserved original/ material is historical and not checked for rendering.
    math = 0
    for doc in sorted(ROOT.rglob('*.md')):
        rel = doc.relative_to(ROOT)
        if any(part in GENERATED for part in rel.parts) or rel.parts[0] == 'original':
            continue
        for segment in math_segments(doc.read_text()):
            bad = BLOCKED_MATH.search(segment)
            require(bad is None, f'Math macro {bad and bad.group(0)} will not render on GitHub: '
                    + rel.as_posix())
            math += 1

    links = 0
    for doc in sorted([*ROOT.glob('*.md'), ROOT / 'original/README.md']):
        if not doc.exists():
            continue
        text = re.sub(r'```.*?```', '', doc.read_text(), flags=re.S)
        for match in re.finditer(r'\[[^\]\n]+\]\(([^)]+)\)', text):
            target = match.group(1).strip().strip('<>')
            url = urlsplit(target)
            if url.scheme or url.netloc:
                continue
            path = (doc.parent / unquote(url.path)).resolve() if url.path else doc
            relative = path.relative_to(ROOT).as_posix() if path.is_relative_to(ROOT) else None
            require(relative is not None, 'Documentation link outside package: ' + target)
            is_dir = path.is_dir() and any(e.startswith(relative + '/') for e in expected)
            require(relative in expected or is_dir,
                    f'Documentation link to an uninventoried path in {doc.name}: {target}')
            require(path.exists() or (sources_only and relative in EVIDENCE),
                    f'Broken documentation link in {doc.name}: {target}')
            links += 1

    if not sources_only:
        report = json.loads((ROOT / 'evidence/verification.json').read_text())
        require(report['verification_exit_code'] == 0 and report['status'] == 'PASS',
                'Recorded verification did not pass')
        require(report['source_sha256'] == hashes, 'Evidence covers different sources')
        require(report['toolchain'] == json.loads((ROOT / 'TOOLCHAIN.json').read_text()),
                'Evidence uses different pins')
        require('VERIFY_EXIT_CODE=0' in (ROOT / 'evidence/verification.log').read_text(),
                'Missing successful verification transcript')
    print(f'PASS: package inventory, {len(hashes)} source hashes, {links} local links, and '
          f'{math} math segments free of macros GitHub rejects.')


if __name__ == '__main__':
    main()
