# Real-Power-Cauchy-Schwarz: a Lean proof of a Cauchy-Schwarz inequality for real powers

This repository contains a Lean 4 proof, built on Mathlib, of Conjecture 5.1 in the paper *Generalizing the Cauchy-Schwarz inequality: Hadamard powers and tensor products* by N. Johnston, S. Plosker, C. Torrance and L. M. B. Varona ([arXiv:2507.10327](https://arxiv.org/abs/2507.10327), Linear and Multilinear Algebra, 2026, [doi:10.1080/03081087.2026.2707240](https://doi.org/10.1080/03081087.2026.2707240)). For a vector v with nonnegative entries, write v^p for the vector of p-th powers of its entries. The conjecture states the following.

> Let p ≥ 2 be a real number. For any pair of vectors v, w with positive entries, ‖v^p‖ ‖w^p‖ − ⟨v^p, w^p⟩ ≤ ‖v‖^p ‖w‖^p − ⟨v, w⟩^p.

The authors proved the inequality for integer p, showed that it fails for p between 1 and 2, and checked the remaining case numerically. We prove it for every real p ≥ 2 and all vectors with nonnegative entries. We also determine every case of equality and decide exactly which weighted versions of the inequality hold.

## Main statements

```lean
theorem RealPowerCauchySchwarz.generalized_cauchy_schwarz (n : ℕ) (p : ℝ) (hp : 2 ≤ p)
    (v w : EuclideanSpace ℝ (Fin n)) (hv : ∀ i, 0 ≤ v i) (hw : ∀ i, 0 ≤ w i) :
    ‖epow p v‖ * ‖epow p w‖ - inner ℝ (epow p v) (epow p w)
      ≤ ‖v‖ ^ p * ‖w‖ ^ p - (inner ℝ v w) ^ p

theorem RealPowerCauchySchwarz.conjecture_5_1_true : Conjecture_5_1

theorem RealPowerCauchySchwarz.equality_iff_of_two_lt {n : ℕ} {p : ℝ} (hp : 2 < p)
    (v w : EuclideanSpace ℝ (Fin n)) (hv : ∀ i, 0 ≤ v i) (hw : ∀ i, 0 ≤ w i) :
    ‖epow p v‖ * ‖epow p w‖ - inner ℝ (epow p v) (epow p w) = ‖v‖ ^ p * ‖w‖ ^ p - (inner ℝ v w) ^ p
      ↔ ((∀ i j, v i * w j = v j * w i) ∨ (∀ i j, i ≠ j → v i * v j = 0 ∧ w i * w j = 0))

theorem RealPowerCauchySchwarz.equality_iff_two {n : ℕ} (v w : EuclideanSpace ℝ (Fin n))
    (hv : ∀ i, 0 ≤ v i) (hw : ∀ i, 0 ≤ w i) :
    ‖epow 2 v‖ * ‖epow 2 w‖ - inner ℝ (epow 2 v) (epow 2 w)
        = ‖v‖ ^ (2:ℝ) * ‖w‖ ^ (2:ℝ) - (inner ℝ v w) ^ (2:ℝ)
      ↔ ((∀ i j, v i * w j = v j * w i) ∨
          ∃ i j, i ≠ j ∧ (∀ k, k ≠ i → k ≠ j → v k = 0 ∧ w k = 0) ∧ v i * w i = v j * w j)

theorem RealPowerCauchySchwarz.weighted_iff {n : ℕ} (ω : Fin n → ℝ) (hω : ∀ i, 0 < ω i)
    (p : ℝ) (hp : 2 ≤ p) :
    (∀ v w : Fin n → ℝ, (∀ i, 0 ≤ v i) → (∀ i, 0 ≤ w i) → wLHS ω p v w ≤ wRHS ω p v w) ↔
      ∀ i j, i ≠ j → 1 ≤ ω i * ω j
```

Here `epow p v` is the vector with entries `v i ^ p`, using the real power `Real.rpow`. The condition `∀ i j, v i * w j = v j * w i` says that every 2 × 2 minor of the pair vanishes, which means that v and w are linearly dependent. In words, the three results beyond the conjecture say the following.

* For p > 2, equality holds exactly when v and w are linearly dependent, or each of them has at most one nonzero entry.
* For p = 2, equality holds exactly when v and w are linearly dependent, or both vanish outside two coordinates i ≠ j and v_i w_i = v_j w_j. For example v = (1, 2) and w = (4, 2) give equality when p = 2 and a strict inequality when p > 2.
* Give coordinate i a weight ω_i > 0, and use the same weighted counting measure in every norm and inner product. These are `wLHS` and `wRHS`. Then the weighted inequality holds for all nonnegative v and w exactly when ω_i ω_j ≥ 1 for every pair of different coordinates. The condition is the same for every p ≥ 2.

`Conjecture_5_1` is the conjecture as stated, with n ≥ 1 and strictly positive entries. The main theorem assumes less, since it allows zero entries.

## Proof outline

Put A_i equal to the 2 × 2 rank-one matrix with rows (v_i², v_i w_i) and (v_i w_i, w_i²). The proof shows that the entrywise p-th power of A_1 + ... + A_n minus the sum of the entrywise p-th powers of the A_i is positive semidefinite. This is superadditivity of entrywise powers for 2 × 2 matrices, a special case of a theorem of Guillot, Khare and Rajaratnam, and the Lean file proves it from a double integral formula and the Cauchy-Schwarz inequality for integrals. A scalar Cauchy-Schwarz step then turns the matrix inequality into the stated one.

The equality cases come from a strict form of the same 2 × 2 estimate. Equality forces every pair of coordinates to contribute a degenerate piece, and for p > 2 the strict estimate allows this only for proportional pairs. For p = 2 the estimate is an identity, and a direct computation gives the extra family.

For the weighted inequality, a weight below 1 can occur at one coordinate at most. That coordinate is split off, the rest is bounded with the unweighted theorem, and a supremum over one scaling parameter reduces everything to a two-dimensional estimate that follows from the 2 × 2 superadditivity.

| File | What it proves |
| --- | --- |
| `Basic.lean` | This file proves the 2 × 2 superadditivity and the main inequality. |
| `Equality.lean` | This file proves the strict 2 × 2 estimate and both equality theorems in sum form. |
| `Weighted.lean` | This file proves the characterisation of the admissible weights. |
| `Main.lean` | This file restates the equality theorems with the Euclidean norm and inner product. |

## Building

```bash
lake exe cache get
lake build
scripts/check.sh
```

`scripts/check.sh` builds the project, fails on any `sorry`, `native_decide` or declared axiom, and prints the axioms of every theorem listed in `THEOREMS`. Each of them depends only on `propext`, `Classical.choice` and `Quot.sound`. The project uses Lean `v4.35.0-rc1` and a pinned Mathlib commit.

## Numerical check

The script `scripts/numerics.py` tests the inequality on random vectors, checks the equality families for p = 2 and p > 2, and checks the weighted threshold on both sides of ω_i ω_j = 1. It needs numpy and makes no network request.

```bash
python3 scripts/numerics.py
```

## Exposition and applications

An illustrated explanation of the proof, with interactive plots, is published at [pragyaangaur.github.io/Real-Power-Cauchy-Schwarz](https://pragyaangaur.github.io/Real-Power-Cauchy-Schwarz/). Its source is `docs/index.html`, and it needs no build step.

The applications report *What a Cauchy-Schwarz inequality for real powers is good for* is [`docs/applications.pdf`](docs/applications.pdf). It derives consequences for tempered and escort distributions, partition functions, sharpening in semi-supervised learning and kernels on nonnegative features, and it labels each claim as proved, cited or proposed. The folder `companion/applications/` holds its LaTeX source and the script `consequences.py`, which tests every corollary in the report on random inputs and draws its figures.

The folder `companion/video/` holds the Manim source of the exposition video, the script that assembles it, its subtitles and a narration script.

## Credits

The conjecture is due to Johnston, Plosker, Torrance and Varona. The informal proof of the inequality first appeared on [Principia Math](https://principia-math.com) as the solution to problem MathDB 369283, and the 2 × 2 superadditivity it uses is a case of a result of D. Guillot, A. Khare and B. Rajaratnam. Pragyaan Gaur wrote the formal proofs, the equality cases and the weighted characterisation.

## License

MIT. See `LICENSE`.
