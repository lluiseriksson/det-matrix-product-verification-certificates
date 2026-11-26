"""Unit, forgery, AST zero-float, and exact algebraic tests for DET-MATMUL-VERIF-CERT-1.0."""

from __future__ import annotations

import ast
import copy
import json
import pathlib
import sys

import pytest

ROOT = pathlib.Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src import det_matmul_verif_verifier as V

CERTS_DIR = ROOT / "certificates"


def _load(name: str) -> dict:
    return json.loads((CERTS_DIR / name).read_text(encoding="utf-8"))


def test_ast_zero_float_and_no_forbidden_imports() -> None:
    src_path = ROOT / "src" / "det_matmul_verif_verifier.py"
    tree = ast.parse(src_path.read_text(encoding="utf-8"), filename=str(src_path))
    for node in ast.walk(tree):
        if isinstance(node, ast.Constant) and isinstance(node.value, float):
            pytest.fail(f"Forbidden float literal {node.value!r} at line {node.lineno}")
        if isinstance(node, ast.Call) and isinstance(node.func, ast.Name) and node.func.id == "float":
            pytest.fail(f"Forbidden float() call at line {node.lineno}")
        if isinstance(node, ast.Div):
            pytest.fail(f"Forbidden true-division operator / at line {node.lineno}")
        if isinstance(node, ast.AugAssign) and isinstance(node.op, ast.Div):
            pytest.fail(f"Forbidden true-division /= at line {node.lineno}")
        if isinstance(node, ast.Import):
            for alias in node.names:
                assert alias.name not in {"math", "numpy", "scipy", "decimal"}
        if isinstance(node, ast.ImportFrom):
            assert node.module not in {"math", "numpy", "scipy", "decimal"}


@pytest.mark.parametrize("cert_path", sorted(CERTS_DIR.glob("*.json")), ids=lambda p: p.name)
def test_all_16_canonical_certificates_pass(cert_path: pathlib.Path) -> None:
    res = V.verify_file(cert_path)
    assert res["schema_version"] == V.SCHEMA_VERSION
    assert res["cert_id"].startswith("C")


def test_key_exact_witness_metrics() -> None:
    r01 = V.verify_file(CERTS_DIR / "C01_freivalds_sec1_counterexample_2x2.json")
    assert r01["false_accept_prob"] == [1, 2] and r01["cross_term_verified"] is True
    r06 = V.verify_file(CERTS_DIR / "C06_dual_ring_reciprocal_exact.json")
    assert r06["output_ab_coeff"] == [-1, 27]
    r08 = V.verify_file(CERTS_DIR / "C08_dual_ring_cubic_gradient_circuit.json")
    assert r08["output_ab_coeff"] == [3, 1] and r08["theorem1_30s_bound"] == 150
    r12 = V.verify_file(CERTS_DIR / "C12_bini_laurent_k2_M1.json")
    assert r12["recovered_coeff"] == [1764, 1] and r12["bini_exact_rank_bound"] == 9 * 49
    r16 = V.verify_file(CERTS_DIR / "C16_dense_quad_gram_zero_d5_c4.json")
    assert r16["rjrt_is_zero"] is True and r16["hjh_is_zero"] is True


# Adversarial forgery tests
def test_reject_float_and_dup_json(tmp_path: pathlib.Path) -> None:
    p1 = tmp_path / "f.json"
    p1.write_text('{"x": 2.25}', encoding="utf-8")
    with pytest.raises(V.VerificationError, match="floating-point"):
        V.verify_file(p1)
    p2 = tmp_path / "d.json"
    p2.write_text('{"a": 1, "a": 2}', encoding="utf-8")
    with pytest.raises(V.VerificationError, match="Duplicate"):
        V.verify_file(p2)


def test_reject_non_reduced_rational() -> None:
    c = _load("C06_dual_ring_reciprocal_exact.json")
    c["payload"]["expected_ab_coeff"] = [-2, 54]
    with pytest.raises(V.VerificationError, match="lowest terms"):
        V.verify_certificate(c)


def test_reject_dual_ring_division_by_zero() -> None:
    c = _load("C06_dual_ring_reciprocal_exact.json")
    c["payload"]["dual_inputs"][0][0] = [0, 1]
    with pytest.raises(V.VerificationError, match="Division by zero"):
        V.verify_certificate(c)


def test_reject_wrong_ab_coeff() -> None:
    c = _load("C07_dual_ring_rational_quotient.json")
    c["payload"]["expected_ab_coeff"] = [0, 1]
    with pytest.raises(V.VerificationError, match="cross-term output mismatch"):
        V.verify_certificate(c)


def test_reject_q_plus_r_exceeds_s() -> None:
    c = _load("C05_dual_ring_bilinear_mul.json")
    c["payload"]["tree_cost_s"] = 1
    with pytest.raises(V.VerificationError, match="q \\+ r"):
        V.verify_certificate(c)


def test_reject_zero_t_in_border_degeneration() -> None:
    c = _load("C09_border_rank2_degeneration_unit.json")
    c["payload"]["t_values"] = [[0, 1]]
    with pytest.raises(V.VerificationError, match="nonzero"):
        V.verify_certificate(c)


def test_reject_wrong_schema_and_mode() -> None:
    bad = copy.deepcopy(_load("C01_freivalds_sec1_counterexample_2x2.json"))
    bad["schema_version"] = "BAD"
    with pytest.raises(V.VerificationError, match="schema_version"):
        V.verify_certificate(bad)
    bad["schema_version"] = V.SCHEMA_VERSION
    bad["mode"] = "bogus"
    with pytest.raises(V.VerificationError, match="Unknown verification mode"):
        V.verify_certificate(bad)


def test_reject_dir_and_oversized(tmp_path: pathlib.Path) -> None:
    with pytest.raises(V.VerificationError, match="regular file"):
        V.verify_file(tmp_path)
    big = tmp_path / "big.json"
    big.write_bytes(b" " * (V.MAX_JSON_BYTES + 1))
    with pytest.raises(V.VerificationError, match="size"):
        V.verify_file(big)


def test_reject_half_specified_uv_in_mode1() -> None:
    c = _load("C01_freivalds_sec1_counterexample_2x2.json")
    del c["payload"]["V"]
    with pytest.raises(V.VerificationError, match="provided together"):
        V.verify_certificate(c)


def test_reject_gates_exceed_bs_bound() -> None:
    c = _load("C05_dual_ring_bilinear_mul.json")
    c["payload"]["tree_cost_s"] = 1
    c["payload"]["arith_steps_q"] = 0
    c["payload"]["zero_tests_r"] = 1
    # s=1 -> H <= 3 -> bs_bound = 15, add 16 gates to exceed 15
    c["payload"]["gates"] = [{"op": "add", "a": 0, "b": 0} for _ in range(16)]
    with pytest.raises(V.VerificationError, match="Baur-Strassen"):
        V.verify_certificate(c)


def test_reject_bini_bad_target_index_and_nonzero_lower_coeffs() -> None:
    c = _load("C11_bini_laurent_k1_M1.json")
    c["payload"]["target_coeff_index"] = 2  # must equal k*h = 3
    with pytest.raises(V.VerificationError, match="target_coeff_index"):
        V.verify_certificate(c)
    c2 = _load("C11_bini_laurent_k1_M1.json")
    c2["payload"]["poly_coeffs"][1] = [1, 1]  # violates Bini vanishing below kh
    with pytest.raises(V.VerificationError, match="vanish"):
        V.verify_certificate(c2)
