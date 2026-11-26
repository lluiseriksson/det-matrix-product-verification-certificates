"""Generate the 3 publication-grade figures for paper81-det-matrix-product-verification-certificates."""

from __future__ import annotations

import pathlib
import sys

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

ROOT = pathlib.Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from src.det_matmul_verif_verifier import verify_file

CERTS_DIR = ROOT / "certificates"
FIG_DIR = ROOT / "paper" / "figures"
FIG_DIR.mkdir(parents=True, exist_ok=True)

plt.rcParams.update({
    "font.family": "serif",
    "font.size": 9.5,
    "axes.titlesize": 10.5,
    "axes.labelsize": 9.5,
    "legend.fontsize": 8.0,
    "xtick.labelsize": 8.5,
    "ytick.labelsize": 8.5,
    "figure.dpi": 240,
})


def fig1_separation_and_rank_budget() -> None:
    """Figure 1: (a) Conditional Omega(N^{9/8}) vs Freivalds O(N) separation; (b) Exact 30s gate budget across Mode 2."""
    r05 = verify_file(CERTS_DIR / "C05_dual_ring_bilinear_mul.json")
    r06 = verify_file(CERTS_DIR / "C06_dual_ring_reciprocal_exact.json")
    r07 = verify_file(CERTS_DIR / "C07_dual_ring_rational_quotient.json")
    r08 = verify_file(CERTS_DIR / "C08_dual_ring_cubic_gradient_circuit.json")

    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(9.6, 3.55))

    # Panel (a): Unit-constant asymptotic scaling in total input length N = 3*n^2 (no small-n crossover!)
    Ns = [10.0 ** (2 + 0.5 * k) for k in range(13)]  # 10^2 .. 10^8
    freiv = [N for N in Ns]
    det_94 = [N ** (9.0 / 8.0) for N in Ns]
    det_w = [N ** (2.371552 / 2.0) for N in Ns]
    ax1.loglog(Ns, det_w, ls=":", color="#7570b3", lw=1.7, label=r"Current upper bound $N^{2.3716/2}$ (unit const.)")
    ax1.loglog(Ns, det_94, color="#cb181d", lw=2.2, label=r"Det. lower bound $N^{9/8}$ (cond., $\omega_{\mathbb{C}}=9/4$)")
    ax1.loglog(Ns, freiv, color="#1b9e77", lw=2.2, label=r"Freivalds randomized $O(N)$")
    ax1.fill_between(Ns, freiv, det_94, color="#fcbba1", alpha=0.38, label=r"$\Omega(N^{1/8})$ deterministic-vs-randomized gap")
    ax1.set_xlabel(r"Input length $N = 3n^2$ real scalars (log scale)")
    ax1.set_ylabel("Asymptotic operations (unit constant)")
    ax1.set_title(r"(a) Verification Exponent $\omega_{\mathbb{C}}$ & $\Omega(N^{1/8})$ Gap")
    ax1.legend(loc="upper left", frameon=True, framealpha=0.92, fontsize=7.2)
    ax1.grid(True, which="both", alpha=0.22)

    # Panel (b): Mode 2 exact 3s / 15s / 30s budget chain vs introduced U*V products
    items = [r05, r06, r07, r08]
    names = [f"{r['cert_id']}\n($s={r['tree_cost_s']}$)" for r in items]
    x = list(range(len(items)))
    w = 0.25
    b1 = ax2.bar([i - w for i in x], [r["H_bound"] for r in items], width=w, color="#6baed6", label=r"Path circuit $H \leq 3s$")
    b2 = ax2.bar(x, [r["baur_strassen_bound"] for r in items], width=w, color="#2171b5", label=r"Baur-Strassen $5H \leq 15s$")
    b3 = ax2.bar([i + w for i in x], [r["theorem1_30s_bound"] for r in items], width=w, color="#fd8d3c", label=r"Thm. 1 rank cap $30s$")
    for bars in (b1, b2, b3):
        for bar in bars:
            h = int(bar.get_height())
            ax2.text(bar.get_x() + bar.get_width() / 2.0, h + 2.5, str(h), ha="center", va="bottom", fontsize=7.0)
    ax2.set_xticks(x)
    ax2.set_xticklabels(names)
    ax2.set_ylim(0, 178)
    ax2.set_ylabel("Exact gate / rank-1 product count")
    ax2.set_title("(b) Live Mode 2 Circuit & Rank-30$s$ Budget Chain")
    ax2.legend(loc="upper left", frameon=True, framealpha=0.92, fontsize=7.5)
    ax2.grid(axis="y", alpha=0.25)

    fig.tight_layout()
    fig.savefig(FIG_DIR / "fig1_separation_and_rank_budget.png")
    plt.close(fig)


def fig2_border_rank_and_bini() -> None:
    """Figure 2: (a) Exact Sec. 2 rank-2 degeneration error |err(t)| vs t; (b) Bini Lemma 4 (kD+1)r^k interpolation."""
    r09 = verify_file(CERTS_DIR / "C09_border_rank2_degeneration_unit.json")
    r11 = verify_file(CERTS_DIR / "C11_bini_laurent_k1_M1.json")
    r12 = verify_file(CERTS_DIR / "C12_bini_laurent_k2_M1.json")

    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(9.6, 3.55))

    # Panel (a): C09 exact degeneration error t * c1 + t^2 * c2 over Q (live 4 t_values from C09!)
    import json
    c09_doc = json.loads((CERTS_DIR / "C09_border_rank2_degeneration_unit.json").read_text(encoding="utf-8"))
    ts = [pair[0] / pair[1] for pair in c09_doc["payload"]["t_values"]]
    u1, u2, v1, v2, c1, c2 = 1, 2, 3, 5, 7, 11
    k1 = (u1 * v2 + u2 * v1) * c2 + u2 * v2 * c1  # 191
    k2 = u2 * v2 * c2  # 110
    errs = [t * k1 + (t * t) * k2 for t in ts]
    ax1.loglog(ts, errs, marker="o", color="#1b5e9c", lw=2.0, ms=5.5,
               label=r"Exact $|E(t)| = 191 t + 110 t^2$ (C09, 4 pts)")
    ax1.loglog(ts, [k1 * t for t in ts], ls="--", color="#d95f02", lw=1.4, label=r"Leading linear term $191 t$")
    ax1.invert_xaxis()
    ax1.set_xlabel("Degeneration parameter $t \\to 0$ (log scale)")
    ax1.set_ylabel("Exact approximation error (log scale)")
    ax1.set_title("(a) Sec. 2 Rank-2 Border Degeneration Convergence")
    ax1.legend(loc="upper right", frameon=True, framealpha=0.92, fontsize=7.5)
    ax1.grid(True, which="both", alpha=0.22)

    # Panel (b): Bini Lemma 4 root convergence ((kD+1)*r^k)^{1/k} -> r for BOTH D=4 (C12) and D=5 (C11)
    ks = list(range(1, 17))
    r_val = 7
    eff_d4 = [((k * 4 + 1) ** (1.0 / k)) * r_val for k in ks]
    eff_d5 = [((k * 5 + 1) ** (1.0 / k)) * r_val for k in ks]
    ax2.plot(ks, eff_d5, marker="^", ms=4.0, ls="--", color="#7570b3", lw=1.6,
             label=r"$(kD+1)^{1/k} r$ ($r=7, D=5$)")
    ax2.plot(ks, eff_d4, marker="s", ms=4.2, color="#238b45", lw=2.0,
             label=r"$(kD+1)^{1/k} r$ ($r=7, D=4$)")
    ax2.axhline(r_val, color="#cb181d", lw=1.5, ls=":", label=r"Border-rank limit $r = 7$ (Lemma 4)")
    ax2.scatter([1], [42.0], color="#e6550d", s=65, zorder=5, label="C11 ($k=1, D=5$: 42)")
    ax2.scatter([2], [21.0], color="#d95f02", marker="D", s=55, zorder=5, label="C12 ($k=2, D=4$: 21)")
    ax2.set_xlabel("Tensor power $k$")
    ax2.set_ylabel("Effective exact rank per copy")
    ax2.set_title("(b) Bini Interpolation Overhead Vanishes as $k\\to\\infty$")
    ax2.legend(loc="upper right", frameon=True, framealpha=0.92, fontsize=7.1)
    ax2.grid(alpha=0.25)

    assert r09["num_t_checked"] == 4 and r11["interp_points"] == 6 and r12["interp_points"] == 9
    fig.tight_layout()
    fig.savefig(FIG_DIR / "fig2_border_rank_and_bini.png")
    plt.close(fig)


def fig3_freivalds_and_pit_witnesses() -> None:
    """Figure 3: (a) Exact exhaustive 0/1 false-accept probabilities across Mode 1 & Mode 4a; (b) Dense quadratic cost."""
    r01 = verify_file(CERTS_DIR / "C01_freivalds_sec1_counterexample_2x2.json")
    r03 = verify_file(CERTS_DIR / "C03_freivalds_4x4_tight_half.json")
    r04 = verify_file(CERTS_DIR / "C04_freivalds_4x4_full_rank_err.json")
    r13 = verify_file(CERTS_DIR / "C13_prop5_pit_nonzero_2x2.json")

    fig, (ax1, ax2) = plt.subplots(1, 2, figsize=(9.6, 3.55))

    cats = ["C01\n($2\\times 2$)", "C03\n($4\\times 4$ rk-1)", "C04\n($4\\times 4$ full)", "C13 Prop 5(i)\n(2-sided $x^TRy$)"]
    probs = [
        r01["false_accept_prob"][0] / r01["false_accept_prob"][1],
        r03["false_accept_prob"][0] / r03["false_accept_prob"][1],
        r04["false_accept_prob"][0] / r04["false_accept_prob"][1],
        r13["prop5i_false_accept_prob"][0] / r13["prop5i_false_accept_prob"][1],
    ]
    bars = ax1.bar(range(len(cats)), probs, width=0.52, color=["#3182bd", "#3182bd", "#6baed6", "#fd8d3c"])
    ax1.axhline(0.5, color="#1b9e77", lw=1.4, ls="--", label="Freivalds 1-trial cap $1/2$")
    ax1.axhline(0.75, color="#cb181d", lw=1.4, ls=":", label="Prop. 5(i) 1-trial cap $3/4$")
    for bar, v in zip(bars, probs):
        ax1.text(bar.get_x() + bar.get_width() / 2.0, v + 0.025, f"{v:.4f}", ha="center", va="bottom", fontsize=7.6)
    ax1.set_xticks(range(len(cats)))
    ax1.set_xticklabels(cats, fontsize=7.8)
    ax1.set_ylim(0.0, 0.92)
    ax1.set_ylabel("Exact exhaustive false-accept probability")
    ax1.set_title(r"(a) Exhaustive $\{0,1\}^n$ / $\{0,1\}^{2n}$ Soundness Checks")
    ax1.legend(loc="upper left", frameon=True, framealpha=0.92, fontsize=7.6)
    ax1.grid(axis="y", alpha=0.25)

    # Panel (b): Sec. 6 dense quadratic block-multiplication cost vs S^{9/8} across aspect ratio a/b in (0, 1]
    ratios = [i / 100.0 for i in range(5, 101)]
    # Normalized by (a*b)^{9/8}: ((b/a)*a^{9/4}) / (a*b)^{9/8} = (a/b)^{1/8} <= 1!
    norm_cost_94 = [r ** (1.0 / 8.0) for r in ratios]
    norm_cost_3 = [r ** 0.5 for r in ratios]
    ax2.plot(ratios, norm_cost_94, color="#1b5e9c", lw=2.2, label=r"$\omega_{\mathbb{C}} = 9/4$: ratio $(a/b)^{1/8} \leq 1$")
    ax2.plot(ratios, norm_cost_3, color="#7570b3", lw=1.8, ls="--", label=r"Classical $\omega = 3$: ratio $(a/b)^{1/2} \leq 1$")
    ax2.axhline(1.0, color="#cb181d", lw=1.4, ls=":", label=r"Matched upper bound $S^{\omega/2}$")
    ax2.scatter([4.0 / 6.0, 4.0 / 5.0], [(4.0 / 6.0) ** 0.125, (4.0 / 5.0) ** 0.125],
                color="#e6550d", s=55, zorder=5, label="Live C15 ($4/6$), C16 ($4/5$)")
    ax2.set_xlabel(r"Aspect ratio $a/b = \min(d,c)/\max(d,c)$")
    ax2.set_ylabel(r"Normalized cost $((b/a)a^{\omega}) / (ab)^{\omega/2}$")
    ax2.set_title(r"(b) Dense Quadratic Upper Bound Matching $S^{\omega_{\mathbb{C}}/2}$")
    ax2.set_ylim(0.15, 1.12)
    ax2.legend(loc="lower right", frameon=True, framealpha=0.92, fontsize=7.5)
    ax2.grid(alpha=0.25)

    fig.tight_layout()
    fig.savefig(FIG_DIR / "fig3_freivalds_and_pit_witnesses.png")
    plt.close(fig)


def main() -> int:
    fig1_separation_and_rank_budget()
    fig2_border_rank_and_bini()
    fig3_freivalds_and_pit_witnesses()
    print(f"Generated 3 figures in {FIG_DIR}.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
