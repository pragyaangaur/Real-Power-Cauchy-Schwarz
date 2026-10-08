"""Numerical checks of the statements proved in Lean.

The script needs numpy only and makes no network request. It checks the inequality on random
nonnegative vectors, the equality families for p = 2 and p > 2, and the weighted threshold
w_i w_j >= 1. It exits with a nonzero code if any check fails.
"""
import sys
import numpy as np

rng = np.random.default_rng(2026)
TOL = 1e-9


def gap(v, w, p, om=None):
    """Right-hand side minus left-hand side, with optional weights."""
    if om is None:
        om = np.ones_like(v)
    lhs = np.sqrt((om * v ** (2 * p)).sum()) * np.sqrt((om * w ** (2 * p)).sum()) - (om * (v * w) ** p).sum()
    rhs = (om * v * v).sum() ** (p / 2) * (om * w * w).sum() ** (p / 2) - (om * v * w).sum() ** p
    return rhs - lhs


failures = 0


def check(name, ok):
    global failures
    print(("ok    " if ok else "FAIL  ") + name)
    failures += 0 if ok else 1


# The inequality on random unit vectors.
worst = min(
    gap(v / np.linalg.norm(v), w / np.linalg.norm(w), p)
    for p, v, w in ((2 + 6 * rng.random(), rng.random(n) ** 3, rng.random(n) ** 3)
                    for n in rng.integers(1, 8, 100000))
)
check(f"inequality holds on 100000 random pairs (smallest gap {worst:.2e})", worst > -TOL)

# Equality families.
for p in (2.0, 2.5, 3.0, 7.0):
    check(f"p = {p}: parallel vectors give equality", abs(gap(np.array([1., 2, 3]), np.array([2., 4, 6]), p)) < TOL * 1e4)
    check(f"p = {p}: single entries in different places give equality", abs(gap(np.array([3., 0, 0]), np.array([0, 5., 0]), p)) < TOL)
swap = (np.array([1., 2, 0]), np.array([4., 2, 0]))  # v1 w1 = v2 w2 = 4
check("p = 2: two-entry swap family gives equality", abs(gap(*swap, 2.0)) < TOL)
check("p = 3: the same pair is strict", gap(*swap, 3.0) > 1e-3)
check("p = 2: three entries are strict", gap(np.array([1., 2, 3]), np.array([3., 2, 1]), 2.0) > 1e-3)

# The weighted threshold.
for p in (2.0, 3.0, 4.5):
    om = np.array([0.5, 2.0, 3.0])  # every product of two different weights is at least 1
    worst = min(gap(rng.random(3) ** 2, rng.random(3) ** 2, p, om) for _ in range(50000))
    check(f"p = {p}: weights (0.5, 2, 3) satisfy the inequality on 50000 random pairs", worst > -TOL)
    om = np.array([0.5, 1.9, 3.0])  # 0.5 * 1.9 < 1
    check(f"p = {p}: weights (0.5, 1.9, 3) fail at e1, e2", gap(np.array([1., 0, 0]), np.array([0, 1., 0]), p, om) < 0)

sys.exit(1 if failures else 0)
