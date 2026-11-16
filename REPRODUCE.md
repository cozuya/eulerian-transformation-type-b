# Reproducing the verification

Everything needed is in this repository and its pinned dependencies (RealRooted, Mathlib and
their locked transitive packages). No files from any other repository are used.

## Requirements

- Linux x86_64, with Bash, Git, Python 3, curl, tar, zstd and coreutils. Without zstd,
  Python 3.14 or later can unpack the Lean archive instead.
- About 15 GB of free disk: about 2.5 GB for Lean, and the rest for the dependency
  checkouts, prebuilt Mathlib, and the RealRooted modules compiled locally.
- About 8 GB of RAM.

Other platforms can install Lean 4.35.0 from [lean-toolchain](lean-toolchain), put it on
`PATH`, and run the same fetch and verification commands in Bash.

## Commands

```sh
git clone https://github.com/cozuya/eulerian-transformation-type-b.git
cd eulerian-transformation-type-b
bash scripts/install-lean.sh                  # checksum-pinned Lean 4.35.0 into .tools/
export PATH="$PWD/.tools/lean-4.35.0-linux/bin:$PATH"
bash scripts/fetch-deps.sh                    # locked RealRooted + Mathlib, prebuilt Mathlib
./verify.sh                                   # rebuild and statement/axiom audit
python3 scripts/check-package.py              # inventory, hashes, links, evidence
```

If Lean 4.35.0 is already installed elsewhere, skip the installer. Put its `bin` directory on
`PATH`, or set `LEAN_BIN_DIR` for `fetch-deps.sh` and `verify.sh`.

`fetch-deps.sh` runs `lake exe cache get` and then checks that `lake-manifest.json` is
unchanged and that every dependency is checked out at its pinned revision. No `lake update`
is needed. Only Mathlib and its dependencies come from the prebuilt cache. RealRooted has no
prebuilt cache: the first `lake build` compiles the RealRooted modules this project imports
(about 360 of them) from source, and every module of this project is compiled from source by
`verify.sh`.

## What `verify.sh` does

1. It prints the Lean, Lake, Mathlib and RealRooted versions and checks them against
   [TOOLCHAIN.json](TOOLCHAIN.json) and the lockfile.
2. It scans the six Lean files with [scripts/audit.py](scripts/audit.py) `sources`. The scan
   rejects `sorry`, `admit`, axiom declarations, `native_decide`, `unsafe`,
   `implemented_by`, `extern`, `csimp`, `opaque`, kernel-check options, attributes,
   instances, notation and macros.
3. It checks [SOURCE_SHA256SUMS](SOURCE_SHA256SUMS) and the package inventory.
4. It deletes this project's `.lake/build` and runs `lake build TypeBEulerian`. Dependency
   build outputs under `.lake/packages` are kept; in a fresh clone they are built in the same
   step.
5. It runs `lake env lean --trust=0 Verification.lean`, which prints the type and the axioms
   of 12 declarations.
6. It checks with `audit.py axioms` that each declaration depends on exactly `propext`,
   `Classical.choice` and `Quot.sound`. Any warning, error, `sorryAx` or other axiom fails
   the run.
7. It writes `.build/verification.log`, `.build/kernel-check.log` and
   `.build/verification.json`, with the commit, source hashes, exit codes and timings.

The final lines of a successful transcript include `AXIOM_AUDIT=PASS` and
`VERIFY_EXIT_CODE=0`.

## Rebuilding RealRooted from source as well

To rebuild the RealRooted modules too, not only this project, delete their build outputs
before running `verify.sh`:

```sh
rm -rf .lake/packages/RealRooted/.lake/build .lake/packages/LeanLGV/.lake/build
./verify.sh
```

Mathlib itself is taken from its official prebuilt cache in every case.

## Re-running the informal checks

The exact-arithmetic scripts of the informal proof are described in
[original/README.md](original/README.md). They are corroboration only and are not part of
`verify.sh`.
