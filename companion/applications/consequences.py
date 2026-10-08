"""Numerical checks and figures for the applications report.

Every corollary stated in applications.tex is tested here on random inputs, and every
counterexample quoted in the report is recomputed. Run with

    python3 consequences.py

The script prints one line per check, exits with status 1 if any check fails, and writes
the figures to figures/.
"""

import sys
from pathlib import Path

import numpy as np
import matplotlib

matplotlib.use("Agg")
import matplotlib.pyplot as plt

HERE = Path(__file__).resolve().parent
FIG = HERE / "figures"
FIG.mkdir(exist_ok=True)

rng = np.random.default_rng(20261008)
TRIALS = 100_000
TOL = 1e-9
failures = []


def report(name, ok, detail=""):
    print(f"{'ok  ' if ok else 'FAIL'} {name} {detail}")
    if not ok:
        failures.append(name)


def sides(v, w, p):
    """Left and right side of the real-power Cauchy-Schwarz inequality."""
    lhs = np.linalg.norm(v**p) * np.linalg.norm(w**p) - np.dot(v**p, w**p)
    rhs = (np.linalg.norm(v) * np.linalg.norm(w)) ** p - np.dot(v, w) ** p
    return lhs, rhs


def random_pair(n):
    mask_v = rng.random(n) < 0.85
    mask_w = rng.random(n) < 0.85
    v = rng.exponential(size=n) * mask_v
    w = rng.exponential(size=n) * mask_w
    return v, w


def rel(excess, scale):
    return excess / max(1.0, abs(scale))


# 1. The theorem itself, and its failure for 1 < p < 2.
worst = 0.0
for _ in range(TRIALS):
    v, w = random_pair(rng.integers(1, 8))
    p = rng.uniform(2, 9)
    lhs, rhs = sides(v, w, p)
    worst = max(worst, rel(lhs - rhs, rhs))
report("theorem 1 on random pairs", worst < TOL, f"(worst relative excess {worst:.1e})")

v0, w0 = np.array([2.0, 1.0]), np.array([1.0, 2.0])
grid = np.linspace(1.01, 1.99, 99)
fails_everywhere = all(sides(v0, w0, p)[0] > sides(v0, w0, p)[1] for p in grid)
report("(2,1),(1,2) fails for every sampled p in (1,2)", fails_everywhere)
l15, r15 = sides(v0, w0, 1.5)
report("(2,1),(1,2) at p = 1.5", l15 > r15, f"(left {l15:.4f}, right {r15:.4f})")
l1, r1 = sides(v0, w0, 1.0)
l2, r2 = sides(v0, w0, 2.0)
report("(2,1),(1,2) equality at p = 1 and p = 2", abs(l1 - r1) < TOL and abs(l2 - r2) < TOL)

# 2. Corollary 2.1: the quadratic form version, for all real s, t.
worst = 0.0
for _ in range(TRIALS):
    v, w = random_pair(rng.integers(1, 8))
    p = rng.uniform(2, 7)
    s, t = rng.normal(size=2)
    left = np.sum((s * v**p - t * w**p) ** 2)
    right = s**2 * np.dot(v, v) ** p + t**2 * np.dot(w, w) ** p - 2 * s * t * np.dot(v, w) ** p
    worst = max(worst, rel(left - right, right))
report("corollary 2.1 (quadratic form)", worst < TOL, f"(worst relative excess {worst:.1e})")
p = 1.5
left = np.sum((v0**p - w0**p) ** 2)
right = np.dot(v0, v0) ** p + np.dot(w0, w0) ** p - 2 * np.dot(v0, w0) ** p
report("corollary 2.1 fails at p = 1.5 for (2,1),(1,2)", left > right, f"({left:.4f} > {right:.4f})")

# 3. Corollary 2.2: the norm form.
worst = 0.0
for _ in range(TRIALS):
    v, w = random_pair(rng.integers(1, 8))
    p = rng.uniform(2, 7)
    inner_loss = np.dot(v, w) ** p - np.sum((v * w) ** p)
    norm_loss = (np.linalg.norm(v) * np.linalg.norm(w)) ** p - (
        np.linalg.norm(v, 2 * p) * np.linalg.norm(w, 2 * p)
    ) ** p
    scale = (np.linalg.norm(v) * np.linalg.norm(w)) ** p
    worst = max(worst, rel(inner_loss - norm_loss, scale), rel(-inner_loss, scale))
report("corollary 2.2 (norm form)", worst < TOL, f"(worst relative excess {worst:.1e})")


# 4. Corollary 4.1: Hellinger affinity of escort distributions.
def escort(P, p):
    Pp = P**p
    return Pp / Pp.sum()


def bc(P, Q):
    return np.sum(np.sqrt(P * Q))


def hellinger_sides(P, Q, p):
    left = np.sqrt(np.sum(P**p) * np.sum(Q**p)) * (1 - bc(escort(P, p), escort(Q, p)))
    right = 1 - bc(P, Q) ** p
    return left, right


worst = 0.0
for _ in range(TRIALS):
    n = rng.integers(2, 9)
    P = rng.dirichlet(np.full(n, rng.uniform(0.1, 3)))
    Q = rng.dirichlet(np.full(n, rng.uniform(0.1, 3)))
    p = rng.uniform(2, 9)
    left, right = hellinger_sides(P, Q, p)
    worst = max(worst, left - right)
report("corollary 4.1 (escort distributions)", worst < TOL, f"(worst excess {worst:.1e})")
P0, Q0 = np.array([0.8, 0.2]), np.array([0.2, 0.8])
l, r = hellinger_sides(P0, Q0, 1.5)
report("corollary 4.1 fails at p = 1.5 for (0.8,0.2),(0.2,0.8)", l > r, f"({l:.5f} > {r:.5f})")

# The Renyi form of the prefactor.
P = rng.dirichlet(np.ones(5))
Q = rng.dirichlet(np.ones(5))
p = 2.5
renyi = lambda X, a: np.log(np.sum(X**a)) / (1 - a)
pref = 1 / np.sqrt(np.sum(P**p) * np.sum(Q**p))
report(
    "prefactor equals exp((p-1)(H_p(P)+H_p(Q))/2)",
    abs(pref - np.exp((p - 1) * (renyi(P, p) + renyi(Q, p)) / 2)) < 1e-9,
)


# 5. Corollary 4.2: partition functions at inverse temperatures beta and p*beta.
def Z(E, beta, g=None):
    g = np.ones_like(E) if g is None else g
    return np.sum(g * np.exp(-beta * E))


worst = 0.0
strict_min = np.inf
for _ in range(TRIALS):
    n = rng.integers(2, 8)
    E = rng.normal(scale=2, size=n)
    F = rng.normal(scale=2, size=n)
    beta = rng.uniform(0.1, 2)
    p = rng.uniform(2, 6)
    M = (E + F) / 2
    left = np.sqrt(Z(E, p * beta) * Z(F, p * beta)) - Z(M, p * beta)
    right = (Z(E, beta) * Z(F, beta)) ** (p / 2) - Z(M, beta) ** p
    worst = max(worst, rel(left - right, right))
    if p > 2.05:
        strict_min = min(strict_min, (right - left) / max(right, 1e-300))
report("corollary 4.2 (partition functions)", worst < TOL, f"(worst relative excess {worst:.1e})")
report("corollary 4.2 is strict for p > 2 and non-constant E - E'", strict_min > 0, f"(smallest relative gap {strict_min:.1e})")


# 6. Corollary 4.3: degeneracies g with g_i g_j >= 1 keep the inequality, and a
#    normalised reference measure breaks it for suitable finite energies.
def gibbs_weighted_sides(E, F, beta, p, g):
    M = (E + F) / 2
    left = np.sqrt(Z(E, p * beta, g) * Z(F, p * beta, g)) - Z(M, p * beta, g)
    right = (Z(E, beta, g) * Z(F, beta, g)) ** (p / 2) - Z(M, beta, g) ** p
    return left, right


worst = 0.0
for _ in range(TRIALS // 2):
    n = rng.integers(2, 6)
    g = rng.uniform(1, 4, size=n)
    k = rng.integers(n)
    g[k] = rng.uniform(1 / g[np.arange(n) != k].min(), 1)  # one weight below 1, still g_i g_j >= 1
    E = rng.normal(scale=2, size=n)
    F = rng.normal(scale=2, size=n)
    beta, p = rng.uniform(0.1, 2), rng.uniform(2, 6)
    left, right = gibbs_weighted_sides(E, F, beta, p, g)
    worst = max(worst, rel(left - right, right))
report("corollary 4.3 with g_i g_j >= 1", worst < TOL, f"(worst relative excess {worst:.1e})")
g = np.array([0.5, 0.5])
E = np.array([0.0, 30.0])
F = np.array([30.0, 0.0])
l, r = gibbs_weighted_sides(E, F, 1.0, 3.0, g)
report("corollary 4.3 fails for g = (1/2, 1/2)", l > r, f"(left {l:.4f} > right {r:.4f})")


# 7. Sharpening as used in UDA (softmax temperature 0.4, exponent 2.5).
def softmax(z):
    e = np.exp(z - z.max())
    return e / e.sum()


z1, z2 = rng.normal(size=10), rng.normal(size=10)
tau = 0.4
report(
    "softmax(z/tau) equals the escort of softmax(z) with exponent 1/tau",
    np.allclose(softmax(z1 / tau), escort(softmax(z1), 1 / tau)),
)
worst = 0.0
for _ in range(TRIALS // 2):
    z1, z2 = rng.normal(scale=2, size=(2, 10))
    P, Q = softmax(z1), softmax(z2)
    left, right = hellinger_sides(P, Q, 1 / tau)
    worst = max(worst, left - right)
report("UDA sharpening (p = 2.5) on random logits", worst < TOL, f"(worst excess {worst:.1e})")

# 8. Proposition 6.1 of the paper as a kernel statement: for k points and p in N or p >= k,
#    the power-feature Gram matrix is dominated by the entrywise power of the Gram matrix.
worst = 0.0
for _ in range(TRIALS // 10):
    k = rng.integers(2, 6)
    n = rng.integers(1, 7)
    X = rng.exponential(size=(k, n)) * (rng.random((k, n)) < 0.8)
    p = rng.choice([rng.integers(1, 6), rng.uniform(k, k + 4)])
    T = (X @ X.T) ** p
    D = T - (X**p) @ (X**p).T
    worst = max(worst, -np.linalg.eigvalsh(D).min() / max(1, np.abs(T).max()))
report("k-point Loewner domination for p in N or p >= k", worst < 1e-9, f"(most negative eigenvalue {-worst:.1e})")

# 9. Integer p: the tensor-power picture. v^p is the diagonal part of the p-fold tensor power.
v, w = rng.exponential(size=3), rng.exponential(size=3)
p = 3
T = lambda x: np.einsum("i,j,k->ijk", x, x, x).ravel()
report("<v^(x3), w^(x3)> = <v,w>^3", abs(np.dot(T(v), T(w)) - np.dot(v, w) ** 3) < 1e-9)
diag = [i * 9 + i * 3 + i for i in range(3)]
report("diagonal of v^(x3) is v^3", np.allclose(T(v)[diag], v**3))


# Figures.
plt.rcParams.update(
    {
        "font.family": "serif",
        "mathtext.fontset": "cm",
        "font.size": 10,
        "axes.spines.top": False,
        "axes.spines.right": False,
        "savefig.bbox": "tight",
    }
)
NAVY, ORANGE, GREY, RED = "#1f3a5f", "#d9822b", "#8a8f98", "#b23a48"

# Figure 1: the gap R - L for (2,1),(1,2) as a function of p.
ps = np.linspace(1.0, 3.2, 600)
gap = np.array([sides(v0, w0, p)[1] - sides(v0, w0, p)[0] for p in ps])
fig, ax = plt.subplots(figsize=(5.2, 2.8))
ax.axhline(0, color=GREY, lw=0.8)
ax.axvspan(1, 2, color=RED, alpha=0.08)
ax.plot(ps, gap, color=NAVY, lw=1.8)
ax.fill_between(ps, gap, 0, where=(ps > 1) & (ps < 2), color=RED, alpha=0.35)
ax.plot([1, 2], [0, 0], "o", color=ORANGE, ms=5, zorder=5)
ax.set_xlabel("exponent $p$")
ax.set_ylabel("right side $-$ left side")
ax.set_ylim(-0.4, 2.2)
ax.text(1.5, 0.35, "fails", color=RED, ha="center")
ax.text(2.7, 1.2, "holds", color=NAVY, ha="center")
ax.set_title(r"$v=(2,1)$, $w=(1,2)$", fontsize=10)
fig.savefig(FIG / "gap_vs_p.pdf")
plt.close(fig)

# Figure 2: escort distributions, both sides of corollary 4.1 at p = 2.5 and p = 1.5.
fig, axes = plt.subplots(1, 2, figsize=(6.4, 3.0), sharey=True)
for ax, p, colour in ((axes[0], 2.5, NAVY), (axes[1], 1.5, GREY)):
    xs, ys = [], []
    for _ in range(4000):
        n = rng.integers(2, 6)
        P = rng.dirichlet(np.full(n, rng.uniform(0.2, 2)))
        Q = rng.dirichlet(np.full(n, rng.uniform(0.2, 2)))
        l, r = hellinger_sides(P, Q, p)
        xs.append(r)
        ys.append(l)
    xs, ys = np.array(xs), np.array(ys)
    above = ys > xs + 1e-12
    ax.scatter(xs[~above], ys[~above], s=3, color=colour, alpha=0.35, lw=0)
    ax.scatter(xs[above], ys[above], s=6, color=RED, alpha=0.9, lw=0)
    ax.plot([0, 1], [0, 1], color=GREY, lw=0.8)
    ax.set_xlim(0, 1)
    ax.set_ylim(0, 1)
    ax.set_aspect("equal")
    ax.set_title(f"$p={p}$" + ("  (UDA)" if p == 2.5 else f"  ({above.sum()} points above)"), fontsize=10)
    ax.set_xlabel(r"$1-\mathrm{BC}(P,Q)^p$")
axes[0].set_ylabel(r"$\sqrt{\sum P_i^p\sum Q_i^p}\,(1-\mathrm{BC}(P^{(p)},Q^{(p)}))$")
fig.savefig(FIG / "escort_scatter.pdf")
plt.close(fig)

# Figure 3: two Gibbs distributions at beta and 2.5 beta.
E = np.array([0.0, 0.6, 1.1, 1.5, 2.4, 3.0])
F = np.array([1.2, 0.2, 0.9, 2.0, 0.5, 2.6])
fig, axes = plt.subplots(1, 2, figsize=(6.4, 2.4), sharey=True)
x = np.arange(len(E))
for ax, beta, title in ((axes[0], 1.0, r"inverse temperature $\beta$"), (axes[1], 2.5, r"inverse temperature $2.5\beta$")):
    P = np.exp(-beta * E) / Z(E, beta)
    Q = np.exp(-beta * F) / Z(F, beta)
    ax.bar(x - 0.18, P, width=0.36, color=NAVY, label="energy $E$")
    ax.bar(x + 0.18, Q, width=0.36, color=ORANGE, label="energy $E'$")
    ax.set_title(title + f",  BC = {bc(P, Q):.3f}", fontsize=10)
    ax.set_xticks(x)
    ax.set_xlabel("state")
axes[0].set_ylabel("probability")
axes[0].legend(frameon=False, fontsize=8)
fig.savefig(FIG / "gibbs_cooling.pdf")
plt.close(fig)

# Figure 4: the weighted condition in the (g_1, g_2) plane.
fig, ax = plt.subplots(figsize=(3.4, 3.2))
gs = np.linspace(0.05, 3, 400)
ax.fill_between(gs, 1 / gs, 3.2, color=NAVY, alpha=0.15)
ax.plot(gs, 1 / gs, color=NAVY, lw=1.5)
ax.plot([0.5], [0.5], "o", color=RED)
ax.annotate("normalised\n$(1/2,1/2)$", (0.5, 0.5), (1.0, 0.2), color=RED, fontsize=8, arrowprops=dict(arrowstyle="-", color=RED, lw=0.6))
ax.plot([1], [1], "o", color=NAVY)
ax.annotate("counting\nmeasure", (1, 1), (1.6, 1.4), color=NAVY, fontsize=8, arrowprops=dict(arrowstyle="-", color=NAVY, lw=0.6))
ax.text(2.0, 2.6, "holds", color=NAVY)
ax.text(0.25, 1.1, "fails", color=RED)
ax.set_xlim(0, 3)
ax.set_ylim(0, 3.2)
ax.set_xlabel("$g_1$")
ax.set_ylabel("$g_2$")
ax.set_aspect("equal")
fig.savefig(FIG / "weights_region.pdf")
plt.close(fig)

print(f"\n{len(failures)} failures")
sys.exit(1 if failures else 0)
