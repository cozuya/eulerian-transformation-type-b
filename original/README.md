# Informal proof material

This directory preserves, byte-for-byte, part of the informal proof bundle that preceded the
Lean formalization. [MANIFEST.sha256](MANIFEST.sha256) gives each file's SHA-256 value,
copied unchanged from the bundle's own manifest. The material is historical; it is not needed
to rebuild or check the Lean theorems.

**Start with [REPORT.md](REPORT.md).** It states the informal results, gives the complete
arguments, and records the exact computations. Its mathematics uses LaTeX delimiters that
GitHub may not render.

| Path | Contents |
| --- | --- |
| [REPORT.md](REPORT.md) | Statements, the operator proof, the larger cone, the refined-family proof, computation record, packet audit and prior-art notes |
| [research/operator/](research/operator) | Operator (Cayley-transform) proof of the strict interlacing sequence; larger cone and both maps; checks |
| [research/refinement/](research/refinement) | Refined-Eulerian common-interlacer proof of the cone; checks, including a deliberately recorded failed lemma |
| [research/derangement/](research/derangement) | Larger-cone proof via the refined family; secondary interlacing for $\mathcal D^B$; checks |
| [research/root/](research/root) | An independent vertical interlacing lemma; independent SymPy re-check; logs |
| [research/type-b-eulerian-packet/](research/type-b-eulerian-packet) | From the supplied packet: the exact-arithmetic toolkit `eul.py`, the probe script and its recorded output only |

## What is and is not checked

Only the statements listed in the [README](../README.md) as *Formalized* are checked by Lean.
The informal claims beyond them (simple roots, strict interlacing of the basis images, the
larger cone, and $\mathcal D^B$) are not. The scripts check exact identities and root
counts for bounded degrees; they are corroboration, not proofs.

The report also mentions supplied packet files that are withheld here (notes, checks and
reference material on a separate three-term problem). It treats them as preexisting packet
material; none of its proofs or included scripts depends on them.

## Reproducing the checks

Original environment: Python 3.12.14, python-flint 0.9.0, SymPy 1.14.0. From this
directory:

```sh
python -m pip install -r requirements.txt
python research/type-b-eulerian-packet/code/typeB_conjecture_probe.py 18
python research/refinement/ptype_expansion.py
python research/refinement/common_a_interlacer.py
python research/refinement/identity_and_sign_check.py
python research/operator/check_operator.py
python research/operator/check_generalized_cone.py
python research/derangement/check_refined_cone.py
python research/root/check_sympy_independent.py
```

`ptype_expansion.py` deliberately records a failed exploratory lemma and ends by printing
`FAIL 5 4 ...`. Run from this directory, because one script uses a relative import path.
Runtime fields can differ.
