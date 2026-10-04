/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

-- Adapted for Lean Pool's pinned Lean and Mathlib; upstream commit is recorded in projects.yml.
module

public import LeanPool.EllipticPDE.Poincare.BoxSlice


/-!
# Existence and uniqueness via Lax-Milgram (dependency-chain step 6)

On the Hilbert space `H₀¹(Ω)` the bilinear form of the Laplacian is bounded (continuous) and,
given the Poincaré inequality, coercive (`laplaceBilin_coercive`). Mathlib's Lax-Milgram
theorem `IsCoercive.continuousLinearEquivOfBilin` then yields for every continuous linear
functional `f` on `H₀¹(Ω)` a unique weak solution `u` of `B[u, v] = f v` for all `v`.

This is the abstract existence-and-uniqueness statement. The elliptic right-hand side
`f ∈ L²(Ω)` enters as the continuous functional `v ↦ ∫_Ω f · v` (continuous by
Cauchy-Schwarz, the `L² ⊂ H⁻¹` embedding), so the classical Poisson-Dirichlet problem is
the instance with that functional.
-/

@[expose] public section

open MeasureTheory
open scoped RealInnerProductSpace

noncomputable section

namespace EllipticPdes

open EllipticPdes.Sobolev EllipticPdes.Poincare

variable {d : ℕ}

/-- **Weak solvability of the Poisson problem.** Given the test-function Poincaré
bound in squared form with constant `C ≥ 0`, for every continuous linear functional
`f` on `H₀¹(Ω)` there is a unique `u ∈ H₀¹(Ω)` solving the weak Dirichlet problem
`B[u, v] = f v` for all `v ∈ H₀¹(Ω)`, where `B` is the bilinear form of the Laplacian
`B[u, v] = ∑ᵢ ⟪∂ᵢu, ∂ᵢv⟫`.

This is [`lax_milgram`] at that form: boundedness is the type, and the test-function
bound supplies coercivity through [`laplaceBilin_coercive`], with constant
`1 / (C + 1)`. The unsquared Poincaré constant is the square root of `C`. -/
theorem poisson_weak_solution
    (Ω : Set (EuclideanSpace ℝ (Fin d))) (C : ℝ) (hC : 0 ≤ C)
    (hbase : ∀ {φ : EuclideanSpace ℝ (Fin d) → ℝ} (h : IsTestFn Ω φ),
      ‖(h.testGraph 0 : L2D Ω)‖ ^ 2 ≤ C * ∑ i : Fin d, ‖h.testGraph i.succ‖ ^ 2)
    (f : H01 Ω →L[ℝ] ℝ) :
    ∃! u : H01 Ω, ∀ v : H01 Ω, laplaceBilin Ω u v = f v :=
  lax_milgram (laplaceBilin_coercive Ω C hC hbase) f

/-- **A-priori estimate for the weak solution (Poisson form).** Under the hypotheses
of [`poisson_weak_solution`], any weak solution obeys `‖u‖_{H₀¹} ≤ α⁻¹ ‖f‖` with the
coercivity constant `α = 1 / (C_P + 1)`, i.e. `‖u‖_{H₀¹} ≤ (C_P + 1) ‖f‖`. -/
theorem poisson_weak_solution_bound
    (Ω : Set (EuclideanSpace ℝ (Fin d))) (CP : ℝ) (hCP : 0 ≤ CP)
    (hbase : ∀ {φ : EuclideanSpace ℝ (Fin d) → ℝ} (h : IsTestFn Ω φ),
      ‖(h.testGraph 0 : L2D Ω)‖ ^ 2 ≤ CP * ∑ i : Fin d, ‖h.testGraph i.succ‖ ^ 2)
    {f : H01 Ω →L[ℝ] ℝ} {u : H01 Ω}
    (hu : ∀ v : H01 Ω, laplaceBilin Ω u v = f v) :
    ‖u‖ ≤ (CP + 1) * ‖f‖ := by
  have h := norm_weak_solution_le (α := 1 / (CP + 1)) (by positivity)
    (laplaceBilin_coercive_const Ω CP hCP hbase) hu
  rwa [one_div, inv_inv] at h

/-- **Unconditional existence, uniqueness, and a-priori bound on an open coordinate box.**
Specialising `poisson_weak_solution` to the box `∏ₖ (aₖ, bₖ)`, the test-function Poincaré
hypothesis is discharged from the box geometry: the per-direction slice bound
`Poincare.slice_bound_euclBox` (which rests on the one-dimensional/Fubini bound
`Poincare.poincare_box_dir`) is averaged by `Poincare.poincare_testfn` into the graph-coordinate
bound with constant `C_P = C / (n + 1)`. So for every continuous functional `f` on `H₀¹` of the
box there is a unique weak solution of `B[u, v] = f v`, satisfying the Lax-Milgram estimate
`‖u‖_{H₀¹} ≤ α⁻¹ ‖f‖` with coercivity constant `α = 1 / (C / (n + 1) + 1)`, with no abstract
Poincaré input. This is the box instance of Theorem `thm: main` for the Poisson form.

Terminal result of the library. Nothing else consumes it. -/
theorem poisson_weak_solution_euclBox {n : ℕ} (a b : Fin (n + 1) → ℝ)
    (hab : ∀ k, a k ≤ b k) (C : ℝ) (hC : ∀ i, (b i - a i) ^ 2 / 2 ≤ C)
    (f : H01 (euclBox a b) →L[ℝ] ℝ) :
    (∃! u : H01 (euclBox a b),
      ∀ v : H01 (euclBox a b), laplaceBilin (euclBox a b) u v = f v)
    ∧ ∀ u : H01 (euclBox a b),
        (∀ v : H01 (euclBox a b), laplaceBilin (euclBox a b) u v = f v) →
          ‖u‖ ≤ (C / (n + 1) + 1) * ‖f‖ := by
  have hCnonneg : 0 ≤ C := le_trans (by positivity) (hC 0)
  have hbase : ∀ {φ : EuclideanSpace ℝ (Fin (n + 1)) → ℝ} (h : IsTestFn (euclBox a b) φ),
      ‖(h.testGraph 0 : L2D (euclBox a b))‖ ^ 2
        ≤ C / (n + 1) * ∑ i : Fin (n + 1), ‖h.testGraph i.succ‖ ^ 2 :=
    fun {_φ} h => testfn_bound_euclBox hab hC h
  have hCP : 0 ≤ C / (n + 1) := div_nonneg hCnonneg (by positivity)
  refine ⟨poisson_weak_solution (euclBox a b) (C / (n + 1)) hCP hbase f, ?_⟩
  intro u hu
  exact poisson_weak_solution_bound (euclBox a b) (C / (n + 1)) hCP hbase hu

end EllipticPdes
