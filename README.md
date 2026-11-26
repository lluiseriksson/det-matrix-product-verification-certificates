# DET-MATMUL-VERIF-CERT-1.0

Independent zero-floating-point exact algebraic and constructive Lean 4.35.0 companion verification suite for Chen Xiangle's *"Deterministic Verification and Computation of Real Matrix Products Have the Same Arithmetic Exponent"* (`arXiv:2611.34814v1`, November 25, 2026).

## Reproduction
```bash
(cd lean && lake build)
python -m src.det_matmul_verif_verifier certificates
pytest -q
```

## Licenses
- Code, Lean 4 proofs, scripts, and certificates: **MIT** (`LICENSE-CODE`)
- Manuscript and figures: **CC-BY-4.0** (`LICENSE-DOCS`)
