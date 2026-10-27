# Real-Power-Cauchy-Schwarz: a Lean proof of a Cauchy-Schwarz inequality for real powers

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.23237507.svg)](https://doi.org/10.5281/zenodo.23237507)

This repository contains a Lean 4 proof, built on Mathlib, of Conjecture 5.1 in the paper *Generalizing the Cauchy-Schwarz inequality: Hadamard powers and tensor products* by N. Johnston, S. Plosker, C. Torrance and L. M. B. Varona ([arXiv:2507.10327](https://arxiv.org/abs/2507.10327), Linear and Multilinear Algebra, 2026, [doi:10.1080/03081087.2026.2707240](https://doi.org/10.1080/03081087.2026.2707240)). For a vector v with nonnegative entries, write v^p for the vector of p-th powers of its entries. The conjecture states the following.

> Let p ≥ 2 be a real number. For any pair of vectors v, w with positive entries, ‖v^p‖ ‖w^p‖ − ⟨v^p, w^p⟩ ≤ ‖v‖^p ‖w‖^p − ⟨v, w⟩^p.

The authors proved the inequality for integer p, showed that it fails for p between 1 and 2, and checked the remaining case numerically. We prove it for every real p ≥ 2 and all vectors with nonnegative entries. We also determine every case of equality and decide exactly which weighted versions of the inequality hold.

Nathaniel Johnston and Mohammad Sababheh proved the conjecture and its equality cases independently and at the same time, in [arXiv:2610.12063](https://arxiv.org/abs/2610.12063). Their preprint was submitted on 8 October 2026, the day the paper below was posted on Zenodo, and Johnston has said that their next version will cite this work as concurrent. Their work does not contain the weighted characterisation or a formal proof, and it proves a lower bound for the gap that this repository does not.

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

For the weighted inequality, write Q_i for the rank-one 2 × 2 matrix of entrywise p-th powers at coordinate i, with rows ((v_i^p)², v_i^p w_i^p) and (v_i^p w_i^p, (w_i^p)²). The condition ω_i ω_j ≥ 1 allows at most one weight below 1. If every weight is at least 1, each coordinate adds the positive semidefinite correction (ω_i^(p-1) − 1) ω_i Q_i, and these corrections together with the 2 × 2 superadditivity give the weighted inequality. If one weight ω_k is below 1, put t = ω_k^(−(p−1)), so that t ≥ 1. Every other weight satisfies ω_j ≥ 1/ω_k, hence ω_j^(p−1) ≥ t, so the weight-dependent corrections (ω_j^(p−1) − t) ω_j Q_j are positive semidefinite. This is exactly where the pairwise condition enters. Adding these corrections to the superadditivity over the coordinates other than k shows that the left-hand side is at most the defect of t times the matrix of coordinate k plus 1/t times the entrywise p-th power of the weighted Gram matrix of the other coordinates. An arithmetic-geometric mean estimate that holds for every t ≥ 1 bounds this defect, and a two-dimensional estimate that follows from the 2 × 2 superadditivity finishes the proof. These steps are `psd2_extra`, `sup_bound`, `two_dim` and `weighted_of_pairwise` in `Weighted.lean`.

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

`scripts/check.sh` builds the project, fails on any `sorry`, `native_decide` or declared axiom, and prints the axioms of every theorem listed in `THEOREMS`. Each of them depends only on `propext`, `Classical.choice` and `Quot.sound`. The project uses Lean `v4.35.0` and the Mathlib tag `v4.35.0`, and every Lean file uses the module system. The paper describes the earlier build on Lean `v4.35.0-rc1`, and apart from the module headers the proofs did not change in the upgrade.

## Numerical check

The script `scripts/numerics.py` tests the inequality on random vectors, checks the equality families for p = 2 and p > 2, and checks the weighted threshold on both sides of ω_i ω_j = 1. It needs numpy and makes no network request.

```bash
python3 scripts/numerics.py
```

## Paper, exposition and applications

The paper *A Cauchy-Schwarz inequality for real powers: proof, equality cases and weighted forms* is on Zenodo at [doi:10.5281/zenodo.23237507](https://doi.org/10.5281/zenodo.23237507). It has the full proofs, the case of more than two vectors and the open questions. A 7 minute narrated video explains the proof on [YouTube](https://youtu.be/OIpJ6RpFTUA).

An illustrated explanation of the proof, with interactive plots, is published at [pragyaangaur.github.io/Real-Power-Cauchy-Schwarz](https://pragyaangaur.github.io/Real-Power-Cauchy-Schwarz/). Its source is `docs/index.html`, and it needs no build step.

The applications report *What a Cauchy-Schwarz inequality for real powers is good for* is [`docs/applications.pdf`](docs/applications.pdf). It derives consequences for tempered and escort distributions, partition functions, sharpening in semi-supervised learning and kernels on nonnegative features, and it labels each claim as proved, cited or proposed. The folder `companion/applications/` holds its LaTeX source and the script `consequences.py`, which tests every corollary in the report on random inputs and draws its figures.

## Palomar files

The repository is laid out for the [Palomar](https://palomar-registry.org) registry of machine-checked results.

* `Challenge.lean` states the five advertised theorems with `sorry`. It imports only Mathlib, so a reader can audit the statements without reading the proofs. It contains Conjecture 5.1 in its original form, the inequality for nonnegative vectors, the two equality characterisations and the weighted characterisation.
* `Solution.lean` repeats the same five statements and proves each of them by quoting a theorem of the library.
* `comparator.json` names the five theorems, so that `lake comparator` can check that each proof in `Solution.lean` proves exactly the statement in `Challenge.lean` with only the standard axioms.
* `formalization.yaml` records the sources, the scope, the known divergences and how the work was produced.
* `.github/workflows/palomar-preflight.yml` runs Palomar's own mechanical verification on a commit without submitting it.

## How this was made

The first informal proof of the inequality was produced by the automated proof system of the Principia Math project, whose underlying model was not disclosed. Pragyaan Gaur used Claude Opus 5.5 (Anthropic) through Claude Code on 8 October 2026 to help find the equality cases and the weighted characterisation, to write the Lean proofs and the numerical script, and to prepare the paper and its companions. Claude Opus 5.5 prepared the Palomar files and the upgrade to Lean `v4.35.0` on 26 October 2026. Pragyaan Gaur checked the mathematics, compared every statement in `Challenge.lean` with the paper, and is responsible for the content. No AI system is an author.

## Credits

The conjecture is due to Johnston, Plosker, Torrance and Varona. The informal proof of the inequality first appeared on [Principia Math](https://principia-math.com) as the solution to problem MathDB 369283, and the 2 × 2 superadditivity it uses is a case of a result of D. Guillot, A. Khare and B. Rajaratnam. Pragyaan Gaur directed the work, found the equality cases and the weighted characterisation with the help of Claude, checked all the mathematics and the statements in `Challenge.lean`, and is responsible for the content. The Lean proofs and the numerical script were written with Claude under the author's direction, as described in the section above.

## License

MIT. See `LICENSE`.
