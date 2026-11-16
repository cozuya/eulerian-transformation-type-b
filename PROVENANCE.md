# Provenance

**Chris Ozols, with AI-assisted proof development and formalization.** Chris directed the
work and its verification.

- **Informal proof, computations and literature review:** AI assistants produced these
  ([original/](original/README.md)). No exact model identity is asserted for that work.
- **Lean formalization and this package:** Anthropic's Claude (Claude Opus 5.5, in Claude
  Code) wrote the Lean proof ([TypeBEulerian/](TypeBEulerian)),
  [Verification.lean](Verification.lean), the scripts and the documentation.
- **Library:** the proof builds on the
  [RealRooted](https://github.com/PerAlexandersson/RealRooted) Lean library, pinned at
  `d667074269bb822fa18ca9142a14fdd90734dd57`. RealRooted supplies the type B Eulerian
  polynomials, Euler numerators, its formalization of Brändén's Theorem 4.6, and the
  interlacing criteria. It is a dependency and is not redistributed here.

Nobody wrote the Lean proofs by hand. Chris Ozols is listed as author in
[CITATION.cff](CITATION.cff) as the person responsible for the work and the repository.

## Timeline

| Date (UTC) | Event | Record and its limits |
| --- | --- | --- |
| 2026-11-14 | Informal proof and exact computations ([original/REPORT.md](original/REPORT.md)) | Date written in the report ("Prepared November 14, 2026, America/Chicago"); not an authenticated timestamp |
| 2026-11-15, 23:09–23:43 | Lean formalization in a private local development repository: five commits, each checked by a full Lean build and an automated multi-model code review | Private local Git history; commit dates are editable metadata |
| 2026-11-15 | This package assembled from the final development commit `27d5823`; fresh verification run | [evidence/](evidence/verification.json) in this repository |
| Not yet | First public availability | — |

Git commit dates are editable metadata, and hashes identify bytes. Neither proves
mathematical truth, an authenticated creation date, or discovery priority.

## The Lean sources

The files in [TypeBEulerian/](TypeBEulerian), `TypeBEulerian.lean`, `lakefile.toml`,
`lake-manifest.json` and `lean-toolchain` are byte-identical to the final commit of the
private development repository. [Verification.lean](Verification.lean) and the
[scripts](scripts) were written for this package. The development repository's own
statement-audit file is superseded by `Verification.lean`, which proves the same results
under weaker assumptions (any sequence with the recurrence and any linear map with the right
basis values).

During development every batch was reviewed by an automated panel of four language models
in addition to the Lean build. The reports found no defects in the proofs; their minor
documentation notes were fixed. These reviews are process records, not evidence of
correctness: correctness rests on the Lean kernel check.

## The informal proof material

[original/](original/README.md) preserves part of the informal proof bundle byte-for-byte:
the report, the proof write-ups, the exact-arithmetic check scripts and their recorded
output. [original/MANIFEST.sha256](original/MANIFEST.sha256) lists their SHA-256 values,
copied unchanged from the bundle's own manifest. Withheld from the bundle are the task
prompt and research instructions given to the AI assistants, and the supplied packet's
notes and reference material on a separate three-term problem. None of the withheld files
is needed to read or check anything here.

The informal material claims more than is formalized: simple roots, the strict interlacing
of the basis images, a larger cone, and the derangement map. Those claims are not checked
by Lean. Its check scripts are finite-range corroboration, not proofs.

## Verification evidence

The package uses Lean **4.35.0** at `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`, Mathlib
**v4.35.0** at `56a005855ea17e0b0958f73ec801ae140b0a1679` and RealRooted at `d667074`, the
versions RealRooted itself pins. [TOOLCHAIN.json](TOOLCHAIN.json) and
[lake-manifest.json](lake-manifest.json) record every pin.
[SOURCE_SHA256SUMS](SOURCE_SHA256SUMS) identifies every file that can affect verification,
plus the preserved material.

Evidence files:

- [verification report](evidence/verification.json)
- [transcript](evidence/verification.log)
- [theorem types and axioms](evidence/kernel-check.log)

These are fresh checks of the sources in this package. They can be repeated with
`./verify.sh`.
