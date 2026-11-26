"""Generate all 16 canonical JSON certificates (C01..C16) for DET-MATMUL-VERIF-CERT-1.0."""

from __future__ import annotations

import json
import pathlib
import sys
from fractions import Fraction

ROOT = pathlib.Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.det_matmul_verif_verifier import SCHEMA_VERSION, verify_file

CERTS_DIR = ROOT / "certificates"
CERTS_DIR.mkdir(parents=True, exist_ok=True)


def _r(num: int, den: int = 1) -> list[int]:
    f = Fraction(num, den)
    return [f.numerator, f.denominator]


def _mat(rows: list[list[int]]) -> list[list[list[int]]]:
    return [[_r(x, 1) for x in row] for row in rows]


def _write(filename: str, cert_id: str, mode: str, payload: dict) -> pathlib.Path:
    doc = {"schema_version": SCHEMA_VERSION, "cert_id": cert_id, "mode": mode, "payload": payload}
    out = CERTS_DIR / filename
    out.write_text(json.dumps(doc, indent=2) + "\n", encoding="utf-8")
    return out


def main() -> int:
    written: list[pathlib.Path] = []

    # C01: Mode 1 — Exact Section 1 2x2 Freivalds counterexample (A=B=I_2, C=[[0,1],[0,1]], false accept = 1/2)
    written.append(_write(
        "C01_freivalds_sec1_counterexample_2x2.json", "C01", "freivalds_and_bilinear_perturbation",
        {
            "matrix_dim": 2,
            "A": _mat([[1, 0], [0, 1]]),
            "B": _mat([[1, 0], [0, 1]]),
            "C": _mat([[0, 1], [0, 1]]),
            "U": _mat([[2, -1], [3, 5]]),
            "V": _mat([[1, 4], [-2, 3]]),
            "t_step": _r(3, 7),
            "s_step": _r(5, 11),
        },
    ))

    # C02: Mode 1 — Exact 3x3 valid product AB = C (false accept = 1, cross-term verified)
    written.append(_write(
        "C02_freivalds_valid_3x3_cross_term.json", "C02", "freivalds_and_bilinear_perturbation",
        {
            "matrix_dim": 3,
            "A": _mat([[1, 2, -1], [0, 3, 2], [2, -1, 1]]),
            "B": _mat([[2, 0, 1], [-1, 1, 3], [1, 2, -2]]),
            "C": _mat([[-1, 0, 9], [-1, 7, 5], [6, 1, -3]]),
            "U": _mat([[1, 0, 2], [-1, 1, 0], [0, 3, -1]]),
            "V": _mat([[0, 2, -1], [1, -1, 2], [3, 0, 1]]),
            "t_step": _r(2, 5),
            "s_step": _r(3, 8),
        },
    ))

    # C03: Mode 1 — 4x4 sparse rank-1 error (false accept = 1/2 tight)
    written.append(_write(
        "C03_freivalds_4x4_tight_half.json", "C03", "freivalds_and_bilinear_perturbation",
        {
            "matrix_dim": 4,
            "A": _mat([[1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1]]),
            "B": _mat([[1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1]]),
            "C": _mat([[0, 0, 0, 0], [0, 1, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1]]),
        },
    ))

    # C04: Mode 1 — 4x4 full-rank error (false accept = 1/16)
    written.append(_write(
        "C04_freivalds_4x4_full_rank_err.json", "C04", "freivalds_and_bilinear_perturbation",
        {
            "matrix_dim": 4,
            "A": _mat([[1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1]]),
            "B": _mat([[2, 0, 0, 0], [0, 2, 0, 0], [0, 0, 2, 0], [0, 0, 0, 2]]),
            "C": _mat([[1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1]]),
        },
    ))

    # C05..C08: Mode 2 — Dual-ring Q[alpha,beta]/(alpha^2,beta^2) straight-line rational circuits & 30s bound
    # C05: Bilinear product a(U)*b(V) -> (2 + 3a + 0b + 0ab) * (5 + 0a + 7b + 0ab) => ab coeff = 21
    written.append(_write(
        "C05_dual_ring_bilinear_mul.json", "C05", "dual_ring_circuit_rank_30s",
        {
            "arith_steps_q": 1, "zero_tests_r": 1, "tree_cost_s": 2,
            "dual_inputs": [
                [_r(2), _r(3), _r(0), _r(0)],
                [_r(5), _r(0), _r(7), _r(0)],
            ],
            "gates": [{"op": "mul", "a": 0, "b": 1}],
            "expected_ab_coeff": _r(21),
        },
    ))

    # C06: Exact dual-ring reciprocal 1 / (3 + 2a + 5b + 7ab) -> ab coeff = -7/9 + 2*2*5/27 = -1/27
    written.append(_write(
        "C06_dual_ring_reciprocal_exact.json", "C06", "dual_ring_circuit_rank_30s",
        {
            "arith_steps_q": 2, "zero_tests_r": 1, "tree_cost_s": 3,
            "dual_inputs": [[_r(3), _r(2), _r(5), _r(7)]],
            "gates": [{"op": "inv", "a": 0}],
            "expected_ab_coeff": _r(-1, 27),
        },
    ))

    # C07: Rational division (1 + 2a + 3b)/(2 + a + 4b) = (1+2a+3b)*(1/2 - a/4 - b + ab)
    # ab coeff = 1*1 + 2*(-1) + 3*(-1/4) = 1 - 2 - 3/4 = -7/4!
    written.append(_write(
        "C07_dual_ring_rational_quotient.json", "C07", "dual_ring_circuit_rank_30s",
        {
            "arith_steps_q": 3, "zero_tests_r": 1, "tree_cost_s": 4,
            "dual_inputs": [
                [_r(1), _r(2), _r(3), _r(0)],
                [_r(2), _r(1), _r(4), _r(0)],
            ],
            "gates": [{"op": "inv", "a": 1}, {"op": "mul", "a": 0, "b": 2}],
            "expected_ab_coeff": _r(-7, 4),
        },
    ))

    # C08: Perturbed scalar minimizer circuit P = (c - ab)^4 -> dP/dc = 4*(c - ab)^3
    # Inputs: a = (1, 1, 0, 0), b = (2, 0, 1, 0), c = (3, 2, 1, 1) [so c - ab = (1, 0, 0, 0) + ... wait:
    # ab = (2, 2, 1, 1), c - ab = (1, 0, 0, 0) -> (c-ab)^3 has ab coeff = 0!
    # Pick c = (3, 1, 0, 0): c - ab = (1, -1, -1, -1) -> (c-ab)^2 = (1, -2, -2, 0), (c-ab)^3 = (1, -3, -3, 3)!]
    written.append(_write(
        "C08_dual_ring_cubic_gradient_circuit.json", "C08", "dual_ring_circuit_rank_30s",
        {
            "arith_steps_q": 4, "zero_tests_r": 1, "tree_cost_s": 5,
            "dual_inputs": [
                [_r(1), _r(1), _r(0), _r(0)],
                [_r(2), _r(0), _r(1), _r(0)],
                [_r(3), _r(1), _r(0), _r(0)],
            ],
            "gates": [
                {"op": "mul", "a": 0, "b": 1},
                {"op": "sub", "a": 2, "b": 3},
                {"op": "mul", "a": 4, "b": 4},
                {"op": "mul", "a": 5, "b": 4},
            ],
            "expected_ab_coeff": _r(3),
        },
    ))

    # C09..C10: Mode 3a — Sec. 2 rank-2 border-rank degeneration convergence over Q
    written.append(_write(
        "C09_border_rank2_degeneration_unit.json", "C09", "bini_border_rank_and_laurent",
        {
            "submode": "rank2_border_degeneration",
            "u1": _r(1), "u2": _r(2), "v1": _r(3), "v2": _r(5), "c1": _r(7), "c2": _r(11),
            "t_values": [_r(1, 10), _r(1, 100), _r(1, 1000), _r(1, 10000)],
        },
    ))
    written.append(_write(
        "C10_border_rank2_degeneration_signed.json", "C10", "bini_border_rank_and_laurent",
        {
            "submode": "rank2_border_degeneration",
            "u1": _r(3, 2), "u2": _r(-5, 3), "v1": _r(-1, 4), "v2": _r(7, 5), "c1": _r(2, 3), "c2": _r(-4, 7),
            "t_values": [_r(1, 8), _r(1, 64), _r(1, 512)],
        },
    ))

    # C11..C12: Mode 3b — Bini Lemma 4 Laurent truncation & exact Lagrange interpolation of t^{kh}
    written.append(_write(
        "C11_bini_laurent_k1_M1.json", "C11", "bini_border_rank_and_laurent",
        {
            "submode": "bini_laurent_interpolation",
            "pole_order_M": 1, "poly_degree_D": 5, "border_rank_r": 7, "tensor_power_k": 1,
            "poly_coeffs": [_r(0), _r(0), _r(0), _r(42), _r(-7, 3), _r(11, 5)],
            "target_coeff_index": 3,
        },
    ))
    written.append(_write(
        "C12_bini_laurent_k2_M1.json", "C12", "bini_border_rank_and_laurent",
        {
            "submode": "bini_laurent_interpolation",
            "pole_order_M": 1, "poly_degree_D": 4, "border_rank_r": 7, "tensor_power_k": 2,
            "poly_coeffs": [_r(0), _r(0), _r(0), _r(0), _r(0), _r(0), _r(1764), _r(-13, 2), _r(9, 4)],
            "target_coeff_index": 6,
        },
    ))

    # C13..C14: Mode 4a — Proposition 5(i)-(ii) white-box quadratic & univariate PIT encodings
    written.append(_write(
        "C13_prop5_pit_nonzero_2x2.json", "C13", "whitebox_pit_and_dense_quadratic",
        {
            "submode": "prop5_pit_encodings",
            "matrix_dim": 2,
            "A": _mat([[1, 0], [0, 1]]),
            "B": _mat([[1, 0], [0, 1]]),
            "C": _mat([[0, 1], [0, 1]]),
        },
    ))
    written.append(_write(
        "C14_prop5_pit_valid_3x3.json", "C14", "whitebox_pit_and_dense_quadratic",
        {
            "submode": "prop5_pit_encodings",
            "matrix_dim": 3,
            "A": _mat([[1, 2, 0], [0, 1, -1], [2, 0, 1]]),
            "B": _mat([[1, 0, 1], [0, 2, 1], [1, -1, 0]]),
            "C": _mat([[1, 4, 3], [-1, 3, 1], [3, -1, 2]]),
        },
    ))

    # C15..C16: Mode 4b — Section 6 dense quadratic Gram equivalence (R J R^T == 0 iff H J H == 0) + 9/4 block bound
    # C15: Non-vanishing d=6 > c=4 (K=2)
    written.append(_write(
        "C15_dense_quad_gram_nonzero_d6_c4.json", "C15", "whitebox_pit_and_dense_quadratic",
        {
            "submode": "dense_quadratic_gram_equivalence",
            "ambient_d": 6, "num_pairs_K": 2,
            "R": _mat([
                [1, 0, 0, 1],
                [0, 1, 1, 0],
                [1, 1, 0, 0],
                [0, 0, 1, 1],
                [2, -1, 1, 0],
                [0, 1, -1, 2],
            ]),
        },
    ))
    # C16: Identically vanishing R J R^T == 0 with d=5 > c=4 (K=2):
    # First two cols u1, u2; next two cols v1, v2 with u1*v1^T + u2*v2^T + v1*u1^T + v2*u2^T = 0!
    # Pick u1 = (1,0,0,0,0)^T, u2 = (0,1,0,0,0)^T, v1 = (0,1,0,0,0)^T, v2 = (-1,0,0,0,0)^T:
    # R J R^T = u1 v1^T + u2 v2^T + v1 u1^T + v2 u2^T = E_{01} - E_{10} + E_{10} - E_{01} = 0!!
    written.append(_write(
        "C16_dense_quad_gram_zero_d5_c4.json", "C16", "whitebox_pit_and_dense_quadratic",
        {
            "submode": "dense_quadratic_gram_equivalence",
            "ambient_d": 5, "num_pairs_K": 2,
            "R": _mat([
                [1, 0, 0, -1],
                [0, 1, 1, 0],
                [0, 0, 0, 0],
                [0, 0, 0, 0],
                [0, 0, 0, 0],
            ]),
        },
    ))

    for p in written:
        res = verify_file(p)
        print(f"[GEN+PASS] {res['cert_id']} -> {p.name}")
    print(f"Generated and verified {len(written)} certificates.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
