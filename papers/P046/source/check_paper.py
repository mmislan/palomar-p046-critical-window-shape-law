"""Replay every printed constant of the paper in exact arithmetic and draw Figure 2.

Run from this folder with the repository .venv Python (needs matplotlib).
Writes check_paper_output.json, figures/history_bounds.pdf, figures/history_bounds.svg
and figures/bound_curves.csv.  Exact checks use fractions.Fraction and Python
integers; floating point is used only to render the figure.

These checks are finite diagnostics of printed numbers.  They are not a
substitute for the universal proofs in the paper or the Lean receipts.
"""
from fractions import Fraction as F
from itertools import product
from math import comb, log, log10, prod, ceil
from pathlib import Path
import csv
import json
import sys

HERE = Path(__file__).resolve().parent
FIG = HERE / "figures"
FIG.mkdir(exist_ok=True)

results = {}
failures = []


def check(name, ok, detail=None):
    results[name] = {"pass": bool(ok)}
    if detail is not None:
        results[name]["detail"] = detail
    if not ok:
        failures.append(name)
    print(("PASS " if ok else "FAIL ") + name)


# ---------------------------------------------------------------- word model
def words(n):
    return ["".join(w) for k in range(1, n + 1) for w in product("01", repeat=k)]


FOOD = frozenset(words(2))


def channel(u, v, mode):
    """Split channel = ordered factor pair; quotient merges (u,v),(v,u) iff uv == vu."""
    if mode == "qt" and u + v == v + u and (len(u), u) > (len(v), v):
        u, v = v, u
    return (u, v, u + v)


def all_channels(n, mode):
    return {channel(w[:i], w[i:], mode) for w in words(n) for i in range(1, len(w))}


def closure(S):
    C = set(FOOD)
    while True:
        old = len(C)
        for u, v, w in S:
            if u in C and v in C:
                C.add(w)
            if w in C:
                C.update([u, v])
        if old == len(C):
            return frozenset(C)


def productive(C, mode):
    out = {channel(u, v, mode) for u in C for v in C if u + v not in C}
    out.update(
        channel(w[:i], w[i:], mode)
        for w in C
        for i in range(1, len(w))
        if w[:i] not in C or w[i:] not in C
    )
    return out


# ---------------------------------------------------------- channel counts
def split_count(n):
    return (n - 2) * 2 ** (n + 1) + 4


def primitive_count(d):
    return 2 ** d - sum(primitive_count(k) for k in range(1, d) if d % k == 0)


def deletion_terms(n):
    terms = {}
    for d in range(1, n // 3 + 1):
        pairs = sum(1 for i in range(1, n) for j in range(i + 1, n) if d * (i + j) <= n)
        terms[d] = primitive_count(d) * pairs
    return terms


def quotient_count(n):
    return split_count(n) - sum(deletion_terms(n).values())


# Section 2: exact channel counts against literal enumeration, n = 4..9.
for n in range(4, 10):
    sp = len(all_channels(n, "sp"))
    qt = len(all_channels(n, "qt"))
    check(f"channel_count_split_n{n}", sp == split_count(n), {"enumerated": sp, "formula": split_count(n)})
    check(f"channel_count_quotient_n{n}", qt == quotient_count(n), {"enumerated": qt, "formula": quotient_count(n)})

# Section 5.3: n = 16 counts and deletion contributions 112, 24, 24, 24, 30.
terms16 = deletion_terms(16)
check("deletion_terms_n16", [terms16[d] for d in range(1, 6)] == [112, 24, 24, 24, 30] and sum(terms16.values()) == 214, terms16)
check("R16_split", split_count(16) == 1835012, split_count(16))
check("R16_quotient", quotient_count(16) == 1834798, quotient_count(16))
check("M16", 2 ** 17 - 2 == 131070)

# Table 1: gateways, growth gateways, food-only channels and singleton witnesses (n = 4 suffices).
for mode, (g, G, A) in {"sp": (32, 36, 248), "qt": (30, 34, 234)}.items():
    R = all_channels(4, mode)
    gates = {r for r in R if (r[0] in FOOD and r[1] in FOOD) or r[2] in FOOD}
    growth = {r for r in gates if r[2] not in FOOD}
    food_only = {r for r in gates if r[2] in FOOD}
    witnesses = {(x, r) for r in gates for x in closure({r})}
    # every gateway is a singleton RAF exactly when catalysed by a member of its own closure;
    # non-gateway channels have singleton closure F and cannot fire alone.
    nongate_fire = [r for r in R - gates if closure({r}) != FOOD]
    check(f"gateways_{mode}", len(gates) == G and len(growth) == g and len(food_only) == 4,
          {"gateways": len(gates), "growth": len(growth), "food_only": len(food_only)})
    check(f"singleton_witnesses_{mode}", len(witnesses) == A == 4 * 6 + 7 * g, len(witnesses))
    check(f"nongateway_cannot_fire_alone_{mode}", not nongate_fire)
    check(f"growth_closure_seven_{mode}", all(len(closure({r})) == 7 for r in growth))
    check(f"foodonly_closure_six_{mode}", all(closure({r}) == FOOD for r in food_only))

# Section 4: history budgets, exhaustive at depths 0, 1, 2 (Lemma 4.2 and the census of Theorem 4.3).
def budget(j):
    return (6 + 2 * j) ** 2 + 4 * 2 ** j - j


def coefficient(r, mode):
    g = 32 if mode == "sp" else 30
    return 1 if r == 0 else g * prod(budget(j) for j in range(1, r))


history_rows = {}
for mode in ["sp", "qt"]:
    states = {FOOD: frozenset()}
    rows = []
    ok = True
    for j in range(3):
        nxt = {}
        transitions = 0
        for C, S in states.items():
            ok &= closure(S) == C and all(set(r) <= C for r in S)
            ok &= len(C) <= 6 + 2 * j and max(map(len, C)) <= 2 ** (j + 1)
            ok &= sum(map(len, C)) <= 2 ** (j + 2) + 6
            ok &= sum(len(w) - 1 for w in C) <= 4 * 2 ** j - j
            cand = productive(C, mode)
            ok &= len(cand) <= ((32 if mode == "sp" else 30) if j == 0 else budget(j))
            for r in cand:
                D = frozenset(C | set(r))
                U = S | {r}
                ok &= r not in S and closure(U) == D and all(set(t) <= D for t in U)
                ok &= sum(map(len, D)) - sum(map(len, C)) <= 2 ** (j + 2)
                ok &= sum(len(w) - 1 for w in D) - sum(len(w) - 1 for w in C) <= 2 ** (j + 2) - 1
                transitions += 1
                if j < 2:
                    nxt[D] = U
        rows.append({"j": j, "states": len(states), "transitions": transitions,
                     "max_choices": max(len(productive(C, mode)) for C in states),
                     "max_T": max(sum(map(len, C)) for C in states),
                     "max_Q": max(sum(len(w) - 1 for w in C) for C in states)})
        states = nxt
    history_rows[mode] = rows
    check(f"history_budget_census_{mode}", ok, rows)

check("history_coefficients_r2", coefficient(2, "sp") == 2272 and coefficient(2, "qt") == 2130 and budget(1) == 71)
check("closed_envelope_bj", all(budget(j) <= 36 * 2 ** j for j in range(1, 400)) and budget(1) == 71 and (6 + 2) ** 2 == 32 * 2)
check("closed_envelope_Cr", all(coefficient(r, "sp") <= 36 ** r * 2 ** (r * (r - 1) // 2) for r in range(0, 120)))
check("quotient_le_split_coefficient", all(coefficient(r, "qt") <= coefficient(r, "sp") for r in range(0, 120)))

# Table 2: exact history-product certificates (also Lean: history_certificate_003/004/006/020).
certs = []
for power, r, target in [(3, 8, 5), (4, 12, 15), (6, 18, 45), (20, 65, 629)]:
    ok = True
    for mode in ["sp", "qt"]:
        v = F(coefficient(r, mode), 10 ** (power * r))
        ok &= v < F(1, 10 ** target)
    certs.append({"a": f"1e-{power}", "r": r, "target": f"1e-{target}",
                  "log10_C_r_split": round(log10(coefficient(r, "sp")), 3)})
    check(f"certificate_a1e-{power}_r{r}", ok, certs[-1])
check("certificate_020_integer_form", coefficient(65, "sp") < 10 ** 671 and 10 ** 670 < coefficient(65, "sp"))

# Old sparse-support coefficient at r = 2 (Lean: split_second_coefficient) and the worked bound.
N2 = 2 * (2 ** 3 + 2)
J2 = split_count(N2)
sparse2 = comb(J2, 2)
check("sparse_coefficient_r2", sparse2 == 712483666919430, {"cap": N2, "channels": J2})
check("worked_bound_1e-20", F(sparse2, 10 ** 40) < F(8, 10 ** 26))

# Section 5.3: exact finite examples at n = 16, lambda = 1e-4, r = 2, B = 8.
finite = []
for mode in ["sp", "qt"]:
    n, r, B = 16, 2, 8
    M = 2 ** (n + 1) - 2
    R = split_count(n) if mode == "sp" else quotient_count(n)
    p = F(n, 10000 * R)
    g, G, A = (32, 36, 248) if mode == "sp" else (30, 34, 234)
    lo = A * p - comb(A, 2) * p * p
    singleton = 1 - (1 - p) ** A
    hist = coefficient(r, mode) * (M * p) ** r
    short = G * (2 ** (B + 1) - 2) * p
    upper = hist + short
    lower_print = F(216, 10 ** 9) if mode == "sp" else F(204, 10 ** 9)
    upper_print = F(457, 10 ** 7) if mode == "sp" else F(431, 10 ** 7)
    row = {"mode": mode, "R": R, "M": M, "p": str(p), "C2": coefficient(r, mode),
           "lower_display": float(lo), "singleton_display": float(singleton),
           "history_display": float(hist), "short_display": float(short), "upper_display": float(upper)}
    finite.append(row)
    check(f"finite_example_{mode}", lower_print < lo <= singleton <= upper < upper_print and 2 * B <= n and M * p < 1, row)
    check(f"finite_example_p_{mode}", p == (F(1, 1146882500) if mode == "sp" else F(1, 1146748750)))

# Rounded table entries printed in Table 3 (six significant digits of the mantissa).
def mant(x, e):
    return f"{x / 10 ** e:.6f}"


table_rows = {row["mode"]: (mant(row["lower_display"], -7), mant(row["history_display"], -5), mant(row["short_display"], -5))
              for row in finite}
check("table4_rounded_entries",
      table_rows["sp"] == ("2.162383", "2.967407", "1.600861") and table_rows["qt"] == ("2.040551", "2.782593", "1.512101"),
      table_rows)

# a_lambda < lambda (1 - exp(-x) < x for x > 0) is used to invoke the 1e-15 certificate at lambda = 1e-4.
# Certify it with the rational enclosure of Remark 6.5: upper bound of 1 - exp(-x) from the alternating series.
def openness_enclosure(z, tol):
    """Rational [lower, upper] for 1 - exp(-z), z >= 0 rational, via the exponential series."""
    if z == 0:
        return F(0), F(0)
    N = 0
    while True:
        if N + 2 >= 2 * z:
            T = sum(z ** k / F(__import__("math").factorial(k)) for k in range(N + 1))
            tail = 2 * z ** (N + 1) / F(__import__("math").factorial(N + 1))
            lo, hi = 1 - 1 / T, 1 - 1 / (T + tail)
            if hi - lo <= tol:
                return lo, hi
        N += 1


def intensity_enclosure(a, tol):
    """Rational [lower, upper] for -log(1 - a), 0 <= a < 1 rational, via the logarithmic series."""
    if a == 0:
        return F(0), F(0)
    N = 1
    while True:
        Lsum = sum(a ** k / k for k in range(1, N + 1))
        rem = a ** (N + 1) / ((N + 1) * (1 - a))
        if rem <= tol:
            return Lsum, Lsum + rem
        N += 1


lo_a, hi_a = openness_enclosure(F(1, 10 ** 4), F(1, 10 ** 12))
check("a_lambda_below_lambda", hi_a < F(1, 10 ** 4), {"lower": str(lo_a), "upper": str(hi_a)})
lo_l, hi_l = intensity_enclosure(F(1, 2), F(1, 10 ** 8))
check("rational_log_enclosure_half", lo_l <= F(69314718, 10 ** 8) <= hi_l and hi_l - lo_l <= F(1, 10 ** 8), {"lower": str(lo_l), "upper": str(hi_l)})

# Section 3 cost remark: seed lengths at m = 100, q = 1/2 and the trial-count scale.
C_star = 2 * 7 ** 64 * 81


def seed_k(b, m):
    k = 1
    while C_star * (1 - b * b) ** k * (m * (m + 1) + 1) > 1:
        k += 1
    return k


k_sp = seed_k(F(1, 2), 100)
k_qt = seed_k(F(1, 4), 100)
check("seed_length_split_m100_q1/2", 10 * k_sp == 4830, k_sp)
check("seed_length_quotient_m100_q1/2", 10 * k_qt == 21520, k_qt)
L = 4830
# Scale of the least r with 2^(L+1)(1-2^-(L+1))^r <= 1/100 (Remark 3.6, display estimate only):
# r ~ 2^(L+1)((L+1) ln 2 + ln 100), so log2 r ~ (L+1) + log2((L+1) ln 2 + ln 100).
r_log2 = (L + 1) + log((L + 1) * log(2) + log(100), 2)
check("repair_trial_scale_log2r", abs(r_log2 - 4843) < 1, round(r_log2, 2))
check("precision_index", ceil(4 / F(1, 100)) + 2 == 402)

# Section 6: normalisation drift envelopes n = 4..100 (Proposition 6.5).
ok = True
for n in range(4, 101):
    M = 2 ** (n + 1) - 2
    R = split_count(n)
    D = sum(deletion_terms(n).values())
    rho = F(1, 2 ** (n // 2))
    ok &= F(D, R) <= rho <= F(1, 4)
    ok &= 0 <= F(n * M, R) - 1 <= F(2, n - 2)
    ok &= F(n * M, R - D) - 1 <= (F(2, n - 2) + rho) / (1 - rho)
    ok &= n * M - R == 2 ** (n + 2) - 2 * n - 4
check("normalisation_envelopes_n4_100", ok)

# Section 6: strict-increase constant uses |T| <= (L+1) M_L with L = 4: 5 * 30 = 150 repair channels at most.
check("repair_support_size_L4", (4 + 1) * (2 ** 5 - 2) == 150)

# ------------------------------------------------------------------ Figure 2
rows = []
coeff = [coefficient(r, "sp") for r in range(0, 81)]
lc = [log10(c) for c in coeff]
old = []
for r in range(1, 11):
    N = 2 * (2 ** (r + 1) + 2)
    old.append(log10(comb(split_count(N), r)))
xs = [1 + 0.05 * i for i in range(0, 381)]
for x in xs:
    nh = [lc[r] - x * r for r in range(81)]
    oh = [0.0] + [old[r - 1] - x * r for r in range(1, 11)]
    nr = min(range(len(nh)), key=nh.__getitem__)
    orr = min(range(len(oh)), key=oh.__getitem__)
    rows.append({"log10_inverse_openness": x, "sparse_log10_bound": min(0.0, oh[orr]),
                 "history_log10_bound": min(0.0, nh[nr]), "sparse_index": orr, "history_index": nr})
with (FIG / "bound_curves.csv").open("w", newline="", encoding="utf-8") as f:
    w = csv.DictWriter(f, fieldnames=list(rows[0]))
    w.writeheader()
    w.writerows(rows)

try:
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    plt.rcParams.update({"font.size": 9, "axes.spines.top": False, "axes.spines.right": False,
                         "pdf.fonttype": 42, "axes.labelsize": 10, "font.family": "serif"})
    fig, axes = plt.subplots(1, 2, figsize=(6.6, 2.8), layout="constrained")
    for ax, stop in zip(axes, [6, 20]):
        data = [r for r in rows if r["log10_inverse_openness"] <= stop + 1e-9]
        xx = [r["log10_inverse_openness"] for r in data]
        ax.plot(xx, [r["sparse_log10_bound"] for r in data], color="#8a8a8a", lw=1.8, label="sparse-support bound")
        ax.plot(xx, [r["history_log10_bound"] for r in data], color="#1f5f8b", lw=2.0, label="total-length history bound")
        ax.set_xlabel(r"$\log_{10}(1/a)$")
        ax.set_ylabel(r"$\log_{10}$ of the upper bound")
        ax.set_xlim(1, stop)
        ax.set_ylim((-50, 0) if stop == 6 else (-680, 0))
        ax.grid(alpha=0.18)
    axes[0].legend(loc="lower left", fontsize=7.6, frameon=False)
    fig.savefig(FIG / "history_bounds.pdf")
    fig.savefig(FIG / "history_bounds.svg")
    plt.close(fig)
    check("figure_written", (FIG / "history_bounds.pdf").exists())
except Exception as exc:  # pragma: no cover
    check("figure_written", False, repr(exc))

summary = {"status": "ALL CHECKS PASSED" if not failures else "FAILURES: " + ", ".join(failures),
           "checks": len(results), "failed": failures, "results": results,
           "history_census": history_rows, "finite_examples": finite, "certificates": certs}
(HERE / "check_paper_output.json").write_text(json.dumps(summary, indent=1), encoding="utf-8")
print(f"{summary['status']} ({len(results)} checks)")
sys.exit(1 if failures else 0)
