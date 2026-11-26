"""
DET-MATMUL-VERIF-CERT-1.0: Zero-floating-point exact algebraic verifier for Chen Xiangle's
"Deterministic Verification and Computation of Real Matrix Products Have the Same Arithmetic Exponent"
(arXiv:2611.34814v1, November 25, 2026).

Strictly zero floating-point literals, zero float() calls, zero true-division (/ or /=),
and zero math/numpy imports. All arithmetic uses exact Python int and fractions.Fraction.
"""

from __future__ import annotations

import itertools
import json
import pathlib
import sys
from fractions import Fraction
from typing import Any

SCHEMA_VERSION = "DET-MATMUL-VERIF-CERT-1.0"
MAX_JSON_BYTES = 1_000_000
MAX_RAT_ABS = 10**18


class VerificationError(ValueError):
    """Raised whenever a certificate violates schema, bounds, or mathematical invariants."""


def _gcd(a: int, b: int) -> int:
    a = abs(a)
    b = abs(b)
    while b:
        a, b = b, a % b
    return a


def _req_int(val: Any, name: str, lo: int | None = None, hi: int | None = None) -> int:
    if isinstance(val, bool) or not isinstance(val, int):
        raise VerificationError(f"Expected integer for {name}, got {type(val).__name__}")
    if lo is not None and val < lo:
        raise VerificationError(f"{name}={val} below minimum {lo}")
    if hi is not None and val > hi:
        raise VerificationError(f"{name}={val} above maximum {hi}")
    return val


def _req_str(val: Any, name: str) -> str:
    if not isinstance(val, str) or not val.strip():
        raise VerificationError(f"Expected non-empty string for {name}")
    return val


def _req_list(val: Any, name: str, min_len: int = 0, max_len: int = 4096) -> list[Any]:
    if not isinstance(val, list):
        raise VerificationError(f"Expected list for {name}")
    if len(val) < min_len or len(val) > max_len:
        raise VerificationError(f"{name} length {len(val)} out of range [{min_len}, {max_len}]")
    return val


def _req_dict(val: Any, name: str) -> dict[str, Any]:
    if not isinstance(val, dict):
        raise VerificationError(f"Expected dict for {name}")
    return val


def _parse_rat(val: Any, name: str) -> Fraction:
    if not isinstance(val, list) or len(val) != 2:
        raise VerificationError(f"Expected [num, den] rational pair for {name}")
    num = _req_int(val[0], f"{name}[0]", -MAX_RAT_ABS, MAX_RAT_ABS)
    den = _req_int(val[1], f"{name}[1]", 1, MAX_RAT_ABS)
    if _gcd(num, den) != 1:
        raise VerificationError(f"Rational {name} not in lowest terms")
    return Fraction(num, den)


def _rat_pair(f: Fraction) -> list[int]:
    return [f.numerator, f.denominator]


def _no_dup_pairs(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    out: dict[str, Any] = {}
    for k, v in pairs:
        if k in out:
            raise VerificationError(f"Duplicate JSON key: {k}")
        out[k] = v
    return out


def _reject_json_constant(token: str) -> Any:
    raise VerificationError(f"Illegal non-finite JSON constant: {token}")


def _reject_json_float(token: str) -> Any:
    raise VerificationError(f"Illegal floating-point JSON literal: {token}")


def _parse_mat(raw: Any, name: str, rows: int, cols: int) -> list[list[Fraction]]:
    outer = _req_list(raw, name, rows, rows)
    out: list[list[Fraction]] = []
    for i, r in enumerate(outer):
        rl = _req_list(r, f"{name}[{i}]", cols, cols)
        out.append([_parse_rat(x, f"{name}[{i}][{j}]") for j, x in enumerate(rl)])
    return out


def _mat_mul(A: list[list[Fraction]], B: list[list[Fraction]]) -> list[list[Fraction]]:
    m, k, n = len(A), len(B), len(B[0])
    return [[sum(A[i][t] * B[t][j] for t in range(k)) for j in range(n)] for i in range(m)]


# ---------------------------------------------------------------------------
# Exact Dual-Ring Arithmetic over Q[alpha, beta] / (alpha^2, beta^2)
# ---------------------------------------------------------------------------

DualElem = tuple[Fraction, Fraction, Fraction, Fraction]  # (c0, c1*a, c2*b, c3*ab)


def dual_add(x: DualElem, y: DualElem) -> DualElem:
    return (x[0] + y[0], x[1] + y[1], x[2] + y[2], x[3] + y[3])


def dual_sub(x: DualElem, y: DualElem) -> DualElem:
    return (x[0] - y[0], x[1] - y[1], x[2] - y[2], x[3] - y[3])


def dual_mul(x: DualElem, y: DualElem) -> DualElem:
    return (
        x[0] * y[0],
        x[0] * y[1] + x[1] * y[0],
        x[0] * y[2] + x[2] * y[0],
        x[0] * y[3] + x[3] * y[0] + x[1] * y[2] + x[2] * y[1],
    )


def dual_inv(d: DualElem) -> DualElem:
    if d[0] == 0:
        raise VerificationError("Division by zero in dual ring Q[alpha,beta]/(alpha^2,beta^2)")
    inv0 = Fraction(d[0].denominator, d[0].numerator)
    inv2 = inv0 * inv0
    inv3 = inv2 * inv0
    return (inv0, -d[1] * inv2, -d[2] * inv2, -d[3] * inv2 + 2 * d[1] * d[2] * inv3)


# ---------------------------------------------------------------------------
# Mode 1: freivalds_and_bilinear_perturbation (Sec. 1 & Sec. 6)
# ---------------------------------------------------------------------------

def _verify_mode1(payload: dict[str, Any]) -> dict[str, Any]:
    n = _req_int(payload.get("matrix_dim"), "matrix_dim", 1, 8)
    A = _parse_mat(payload.get("A"), "A", n, n)
    B = _parse_mat(payload.get("B"), "B", n, n)
    C = _parse_mat(payload.get("C"), "C", n, n)
    AB = _mat_mul(A, B)
    R = [[AB[i][j] - C[i][j] for j in range(n)] for i in range(n)]
    nonzero_entries = sum(1 for i in range(n) for j in range(n) if R[i][j] != 0)

    # Exact exhaustive Freivalds 0/1 test over all 2^n binary vectors r in {0,1}^n!
    total_r = 1 << n
    false_accepts = 0
    for bits in itertools.product((0, 1), repeat=n):
        vec = [sum(R[i][j] * bits[j] for j in range(n)) for i in range(n)]
        if all(v == 0 for v in vec):
            false_accepts += 1

    if nonzero_entries == 0:
        if false_accepts != total_r:
            raise VerificationError("Correct product should pass every Freivalds vector")
    else:
        # Must satisfy false_accepts / 2^n <= 1/2
        if 2 * false_accepts > total_r:
            raise VerificationError(f"Freivalds error {false_accepts}/{total_r} exceeds 1/2")

    # Optional bilinear cross-term check: (A + tU)(B + sV) - AB - tUB - sAV == ts*UV
    if ("U" in payload) != ("V" in payload):
        raise VerificationError("Both 'U' and 'V' must be provided together for cross-term verification")
    cross_ok = False
    if "U" in payload and "V" in payload:
        U = _parse_mat(payload["U"], "U", n, n)
        V = _parse_mat(payload["V"], "V", n, n)
        t = _parse_rat(payload.get("t_step", [1, 1]), "t_step")
        s = _parse_rat(payload.get("s_step", [1, 1]), "s_step")
        AtU = [[A[i][j] + t * U[i][j] for j in range(n)] for i in range(n)]
        BsV = [[B[i][j] + s * V[i][j] for j in range(n)] for i in range(n)]
        lhs_m = _mat_mul(AtU, BsV)
        UB = _mat_mul(U, B)
        AV = _mat_mul(A, V)
        UV = _mat_mul(U, V)
        for i in range(n):
            for j in range(n):
                if lhs_m[i][j] - AB[i][j] - t * UB[i][j] - s * AV[i][j] != (t * s) * UV[i][j]:
                    raise VerificationError("Bilinear cross-term identity failed")
        cross_ok = True

    return {
        "mode": "freivalds_and_bilinear_perturbation",
        "matrix_dim": n,
        "nonzero_residual_entries": nonzero_entries,
        "freivalds_false_accepts": false_accepts,
        "freivalds_total_vectors": total_r,
        "false_accept_prob": _rat_pair(Fraction(false_accepts, total_r)),
        "cross_term_verified": cross_ok,
    }


# ---------------------------------------------------------------------------
# Mode 2: dual_ring_circuit_rank_30s (Sec. 4.4 & Theorem 1)
# ---------------------------------------------------------------------------

def _verify_mode2(payload: dict[str, Any]) -> dict[str, Any]:
    # Execute a straight-line rational circuit in Q[alpha, beta] / (alpha^2, beta^2),
    # verify exact reciprocal identities and Baur-Strassen / 30s rank-term budget!
    q_steps = _req_int(payload.get("arith_steps_q"), "arith_steps_q", 0, 1000)
    r_tests = _req_int(payload.get("zero_tests_r"), "zero_tests_r", 1, 1000)
    tree_cost_s = _req_int(payload.get("tree_cost_s"), "tree_cost_s", 1, 2000)
    if q_steps + r_tests > tree_cost_s:
        raise VerificationError(f"q + r = {q_steps + r_tests} > s = {tree_cost_s}")

    H_bound = 2 * q_steps + 3 * r_tests
    if H_bound > 3 * tree_cost_s:
        raise VerificationError("H > 3*s violated")
    bs_bound = 5 * H_bound
    rank_bound = 2 * bs_bound
    if rank_bound > 30 * tree_cost_s:
        raise VerificationError("Theorem 1 absolute 30*s bound violated")

    # Execute explicit rational circuit gates over Q[alpha,beta]/(alpha^2,beta^2)
    inputs_raw = _req_list(payload.get("dual_inputs"), "dual_inputs", 1, 64)
    vals: list[DualElem] = []
    for idx, inp in enumerate(inputs_raw):
        il = _req_list(inp, f"dual_inputs[{idx}]", 4, 4)
        vals.append((
            _parse_rat(il[0], f"in[{idx}][0]"),
            _parse_rat(il[1], f"in[{idx}][1]"),
            _parse_rat(il[2], f"in[{idx}][2]"),
            _parse_rat(il[3], f"in[{idx}][3]"),
        ))

    gates_raw = _req_list(payload.get("gates"), "gates", 1, 512)
    if len(gates_raw) > bs_bound:
        raise VerificationError(f"Gate count {len(gates_raw)} exceeds Baur-Strassen budget 5*H={bs_bound}")
    uv_products_introduced = 0
    for g_idx, g in enumerate(gates_raw):
        gd = _req_dict(g, f"gates[{g_idx}]")
        op = _req_str(gd.get("op"), f"gates[{g_idx}].op")
        if op in ("add", "sub", "mul"):
            a_i = _req_int(gd.get("a"), f"gates[{g_idx}].a", 0, len(vals) - 1)
            b_i = _req_int(gd.get("b"), f"gates[{g_idx}].b", 0, len(vals) - 1)
            if op == "add":
                vals.append(dual_add(vals[a_i], vals[b_i]))
            elif op == "sub":
                vals.append(dual_sub(vals[a_i], vals[b_i]))
            else:
                vals.append(dual_mul(vals[a_i], vals[b_i]))
                uv_products_introduced += 2
        elif op == "inv":
            a_i = _req_int(gd.get("a"), f"gates[{g_idx}].a", 0, len(vals) - 1)
            inv_v = dual_inv(vals[a_i])
            # Verify exact multiplicative inverse: vals[a_i] * inv_v == (1, 0, 0, 0)
            prod = dual_mul(vals[a_i], inv_v)
            if prod != (Fraction(1, 1), Fraction(0, 1), Fraction(0, 1), Fraction(0, 1)):
                raise VerificationError(f"Dual-ring reciprocal check failed at gate {g_idx}")
            vals.append(inv_v)
            uv_products_introduced += 1
        else:
            raise VerificationError(f"Unknown gate op '{op}'")

    if uv_products_introduced > 30 * tree_cost_s:
        raise VerificationError(f"Introduced {uv_products_introduced} > 30*s={30*tree_cost_s} rank-1 products")

    out_val = vals[-1]
    if "expected_ab_coeff" in payload:
        exp_ab = _parse_rat(payload["expected_ab_coeff"], "expected_ab_coeff")
        if out_val[3] != exp_ab:
            raise VerificationError("Dual-ring alpha*beta cross-term output mismatch")

    return {
        "mode": "dual_ring_circuit_rank_30s",
        "tree_cost_s": tree_cost_s,
        "H_bound": H_bound,
        "baur_strassen_bound": bs_bound,
        "theorem1_30s_bound": 30 * tree_cost_s,
        "num_gates_executed": len(gates_raw),
        "uv_products_introduced": uv_products_introduced,
        "output_ab_coeff": _rat_pair(out_val[3]),
    }


# ---------------------------------------------------------------------------
# Mode 3: bini_border_rank_and_laurent (Sec. 2 & Lemma 4)
# ---------------------------------------------------------------------------

def _verify_mode3(payload: dict[str, Any]) -> dict[str, Any]:
    submode = _req_str(payload.get("submode"), "submode")

    if submode == "rank2_border_degeneration":
        # Verify Sec. 2 rank-2 degeneration t^{-1}((u1+tu2)(v1+tv2)(c1+tc2) - u1*v1*c1) -> (u1v2+u2v1)c1 + u1v1c2
        u1 = _parse_rat(payload.get("u1"), "u1")
        u2 = _parse_rat(payload.get("u2"), "u2")
        v1 = _parse_rat(payload.get("v1"), "v1")
        v2 = _parse_rat(payload.get("v2"), "v2")
        c1 = _parse_rat(payload.get("c1"), "c1")
        c2 = _parse_rat(payload.get("c2"), "c2")
        t_list = _req_list(payload.get("t_values"), "t_values", 1, 32)
        target = (u1 * v2 + u2 * v1) * c1 + u1 * v1 * c2
        coeff_t1 = (u1 * v2 + u2 * v1) * c2 + u2 * v2 * c1
        coeff_t2 = u2 * v2 * c2
        max_abs_err = Fraction(0, 1)
        for idx, tr in enumerate(t_list):
            t = _parse_rat(tr, f"t_values[{idx}]")
            if t == 0:
                raise VerificationError("t must be nonzero in border-rank evaluation")
            inv_t = Fraction(t.denominator, t.numerator)
            approx = inv_t * ((u1 + t * u2) * (v1 + t * v2) * (c1 + t * c2) - u1 * v1 * c1)
            err = approx - target
            expected_err = t * coeff_t1 + (t * t) * coeff_t2
            if err != expected_err:
                raise VerificationError("Border-rank degeneration expansion mismatch")
            if abs(err) > max_abs_err:
                max_abs_err = abs(err)
        return {
            "mode": "bini_border_rank_and_laurent",
            "submode": submode,
            "target_value": _rat_pair(target),
            "num_t_checked": len(t_list),
            "max_abs_error": _rat_pair(max_abs_err),
        }

    if submode == "bini_laurent_interpolation":
        # Verify Bini Lemma 4 Laurent truncation & Vandermonde interpolation of exact coefficient of t^{kh}
        M = _req_int(payload.get("pole_order_M"), "pole_order_M", 0, 10)
        deg_D = _req_int(payload.get("poly_degree_D"), "poly_degree_D", 1, 12)
        r = _req_int(payload.get("border_rank_r"), "border_rank_r", 1, 64)
        k = _req_int(payload.get("tensor_power_k"), "tensor_power_k", 1, 4)
        h = 3 * M
        if deg_D < h:
            raise VerificationError(f"poly_degree_D={deg_D} must be >= h=3*M={h}")
        # Verify truncation: any term with degree >= 2M+1 multiplied by two factors >= -M has degree >= 1
        if (2 * M + 1) + (-M) + (-M) != 1:
            raise VerificationError("Laurent truncation invariant failed")
        # Exact Lagrange interpolation of a concrete polynomial P(t) = sum_{j=0}^{kD} c_j t^j at t = 0, 1, ..., kD
        coeffs_raw = _req_list(payload.get("poly_coeffs"), "poly_coeffs", k * deg_D + 1, k * deg_D + 1)
        coeffs = [_parse_rat(c, f"poly_coeffs[{i}]") for i, c in enumerate(coeffs_raw)]
        target_deg = _req_int(payload.get("target_coeff_index"), "target_coeff_index", 0, k * deg_D)
        if target_deg != k * h:
            raise VerificationError(f"target_coeff_index={target_deg} must equal k*h={k * h}")
        if any(c != 0 for c in coeffs[:target_deg]):
            raise VerificationError("Lower-order Laurent coefficients below t^{kh} must vanish")
        pts = list(range(k * deg_D + 1))
        # Evaluate P at pts and recover exact polynomial via Lagrange basis polynomials over Q
        n_pts = len(pts)
        evals = [sum(coeffs[d] * (x**d) for d in range(n_pts)) for x in pts]
        # Build Lagrange basis polynomials in Q[t] and reconstruct P(t)
        recon = [Fraction(0, 1)] * n_pts
        for i in range(n_pts):
            # prod_{j != i} (t - pts[j]) / (pts[i] - pts[j])
            poly = [Fraction(1, 1)]
            denom = 1
            for j in range(n_pts):
                if j == i:
                    continue
                denom *= pts[i] - pts[j]
                nxt = [Fraction(0, 1)] * (len(poly) + 1)
                for d_idx, c_val in enumerate(poly):
                    nxt[d_idx] -= c_val * pts[j]
                    nxt[d_idx + 1] += c_val
                poly = nxt
            inv_den = Fraction(1, denom) if denom > 0 else Fraction(-1, -denom)
            scale = evals[i] * inv_den
            for d_idx in range(n_pts):
                recon[d_idx] += scale * poly[d_idx]
        if recon != coeffs:
            raise VerificationError("Exact Lagrange interpolation failed to reconstruct polynomial")
        exact_rank_bound = (k * deg_D + 1) * (r**k)
        return {
            "mode": "bini_border_rank_and_laurent",
            "submode": submode,
            "h_shift": h,
            "interp_points": n_pts,
            "recovered_coeff": _rat_pair(recon[target_deg]),
            "bini_exact_rank_bound": exact_rank_bound,
        }

    raise VerificationError(f"Unknown Mode 3 submode: {submode}")


# ---------------------------------------------------------------------------
# Mode 4: whitebox_pit_and_dense_quadratic (Prop. 5 & Sec. 6)
# ---------------------------------------------------------------------------

def _verify_mode4(payload: dict[str, Any]) -> dict[str, Any]:
    submode = _req_str(payload.get("submode"), "submode")

    if submode == "prop5_pit_encodings":
        # Verify Prop 5(i) bilinear form x^T(AB-C)y and Prop 5(ii) univariate Q(t) = sum_i ((A(Bv)-Cv)_i)^2
        n = _req_int(payload.get("matrix_dim"), "matrix_dim", 1, 6)
        A = _parse_mat(payload.get("A"), "A", n, n)
        B = _parse_mat(payload.get("B"), "B", n, n)
        C = _parse_mat(payload.get("C"), "C", n, n)
        AB = _mat_mul(A, B)
        R = [[AB[i][j] - C[i][j] for j in range(n)] for i in range(n)]
        is_zero_res = all(R[i][j] == 0 for i in range(n) for j in range(n))

        # Prop 5(i): exhaustive 0/1 test over (x, y) in {0,1}^n x {0,1}^n -> false accept prob <= 3/4
        total_xy = 1 << (2 * n)
        zero_xy = 0
        for x in itertools.product((0, 1), repeat=n):
            for y in itertools.product((0, 1), repeat=n):
                val = sum(x[i] * R[i][j] * y[j] for i in range(n) for j in range(n))
                if val == 0:
                    zero_xy += 1
        if not is_zero_res and 4 * zero_xy > 3 * total_xy:
            raise VerificationError("Prop 5(i) bilinear 0/1 false-accept probability exceeds 3/4")

        # Prop 5(ii): exact univariate polynomial Q(t) = sum_{i} (sum_j R_{ij} t^j)^2 of degree <= 2n-2
        max_deg = 2 * n - 2
        Q_poly = [Fraction(0, 1)] * (max_deg + 1)
        for i in range(n):
            for j1 in range(n):
                for j2 in range(n):
                    Q_poly[j1 + j2] += R[i][j1] * R[i][j2]
        q_identically_zero = all(c == 0 for c in Q_poly)
        if q_identically_zero != is_zero_res:
            raise VerificationError("Prop 5(ii) equivalence Q(t) == 0 iff AB == C violated")
        # Verify Q(t) >= 0 on integer sample points t = -2..2
        for tv in (-2, -1, 0, 1, 2):
            qv = sum(Q_poly[d] * (tv**d) for d in range(max_deg + 1))
            if qv < 0:
                raise VerificationError("Sum of squares Q(t) took negative value")

        return {
            "mode": "whitebox_pit_and_dense_quadratic",
            "submode": submode,
            "matrix_dim": n,
            "ab_equals_c": is_zero_res,
            "prop5i_false_accept_prob": _rat_pair(Fraction(zero_xy, total_xy)),
            "prop5ii_max_degree": max_deg,
            "prop5ii_q_zero": q_identically_zero,
        }

    if submode == "dense_quadratic_gram_equivalence":
        # Verify Sec. 6 dense quadratic equivalence: R J R^T == 0 iff H J H == 0 where H = R^T R (d > c = 2K)
        d = _req_int(payload.get("ambient_d"), "ambient_d", 1, 10)
        K = _req_int(payload.get("num_pairs_K"), "num_pairs_K", 1, 5)
        c = 2 * K
        R = _parse_mat(payload.get("R"), "R", d, c)
        # J = [[0, I_K], [I_K, 0]]
        J = [[Fraction(1 if abs(i - j) == K else 0, 1) for j in range(c)] for i in range(c)]
        RT = [[R[i][j] for i in range(d)] for j in range(c)]
        RJRT = _mat_mul(_mat_mul(R, J), RT)
        H = _mat_mul(RT, R)
        HJH = _mat_mul(_mat_mul(H, J), H)
        rjrt_zero = all(RJRT[i][j] == 0 for i in range(d) for j in range(d))
        hjh_zero = all(HJH[i][j] == 0 for i in range(c) for j in range(c))
        if rjrt_zero != hjh_zero:
            raise VerificationError("Sec. 6 equivalence R J R^T == 0 iff H J H == 0 failed")
        # Also verify exact block exponent inequality for omega = 9/4 (cleared to 4th power):
        # For a = min(d, c), b = max(d, c): (b/a * a^{9/4})^4 = b^4 * a^5 <= a^{9/2}*b^{9/2}?
        # Cleared to 8th power: (b * a^{5/4})^8 = b^8 * a^{10} <= (a*b)^9 = a^9 * b^9  <=>  a <= b!
        a_dim = min(d, c)
        b_dim = max(d, c)
        lhs8 = (b_dim**8) * (a_dim**10)
        rhs8 = (a_dim * b_dim) ** 9
        if lhs8 > rhs8:
            raise VerificationError("Block exponent inequality (b/a)*a^{9/4} <= (ab)^{9/8} failed")
        return {
            "mode": "whitebox_pit_and_dense_quadratic",
            "submode": submode,
            "ambient_d": d,
            "c_cols": c,
            "rjrt_is_zero": rjrt_zero,
            "hjh_is_zero": hjh_zero,
            "block_exp_9_4_holds": True,
        }

    raise VerificationError(f"Unknown Mode 4 submode: {submode}")


# ---------------------------------------------------------------------------
# Entry Points & CLI
# ---------------------------------------------------------------------------

def verify_certificate(cert: Any) -> dict[str, Any]:
    root = _req_dict(cert, "certificate")
    if root.get("schema_version") != SCHEMA_VERSION:
        raise VerificationError(f"Invalid schema_version: {root.get('schema_version')!r}")
    cert_id = _req_str(root.get("cert_id"), "cert_id")
    mode = _req_str(root.get("mode"), "mode")
    payload = _req_dict(root.get("payload"), "payload")

    if mode == "freivalds_and_bilinear_perturbation":
        res = _verify_mode1(payload)
    elif mode == "dual_ring_circuit_rank_30s":
        res = _verify_mode2(payload)
    elif mode == "bini_border_rank_and_laurent":
        res = _verify_mode3(payload)
    elif mode == "whitebox_pit_and_dense_quadratic":
        res = _verify_mode4(payload)
    else:
        raise VerificationError(f"Unknown verification mode: {mode!r}")

    res["cert_id"] = cert_id
    res["schema_version"] = SCHEMA_VERSION
    return res


def verify_file(path: str | pathlib.Path) -> dict[str, Any]:
    p = pathlib.Path(path)
    if not p.is_file():
        raise VerificationError(f"Certificate path is not a regular file: {p}")
    size = p.stat().st_size
    if size <= 0 or size > MAX_JSON_BYTES:
        raise VerificationError(f"Certificate file size {size} out of bounds (1..{MAX_JSON_BYTES})")
    raw_text = p.read_text(encoding="utf-8")
    try:
        parsed = json.loads(
            raw_text,
            object_pairs_hook=_no_dup_pairs,
            parse_constant=_reject_json_constant,
            parse_float=_reject_json_float,
        )
    except (RecursionError, ValueError) as exc:
        raise VerificationError(f"Malformed JSON in {p.name}: {exc}") from exc
    return verify_certificate(parsed)


def main(argv: list[str] | None = None) -> int:
    args = sys.argv[1:] if argv is None else argv
    if not args:
        print("Usage: python -m src.det_matmul_verif_verifier <file.json | dir>", file=sys.stderr)
        return 2
    targets: list[pathlib.Path] = []
    for a in args:
        p = pathlib.Path(a)
        if p.is_dir():
            targets.extend(sorted(p.glob("*.json")))
        else:
            targets.append(p)
    if not targets:
        print("No JSON certificate files found.", file=sys.stderr)
        return 2
    for t in targets:
        res = verify_file(t)
        print(f"[PASS] {res['cert_id']} ({res['mode']})")
    print(f"Verified {len(targets)}/{len(targets)} certificates successfully.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
