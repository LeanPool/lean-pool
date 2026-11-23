/-
Copyright (c) 2026 Carlo Perassi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Carlo Perassi
-/
module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Complex.Exponential
import LeanPool.SixExponentials.CauchyEstimate
import Mathlib.Algebra.Order.Star.Real
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Monotonicity.Lemmas
import Mathlib.Tactic.ReduceModChar

/-!
# Exponential polynomials on a grid

A size estimate for exponential polynomials at the points of a finite grid.

From `SixExponentials/Basic/expPoly_grid_estimate.lean` of `carlok/six-exponentials-lean`;
see `LeanPool.SixExponentials` for provenance.
-/

@[expose] public section

namespace SixExponentials.Transcendence

/-!
# A Cauchy estimate for an exponential polynomial on a grid

Let `F(z) = ∑ c_k z^(e_k) e^(ω_k z)` vanish to order `n` at every point `∑ m'_j y_j` with
`m'_j < t_j`. These `∏ t_j` points are distinct, since the `y_j` are `ℚ`-linearly independent, and
they lie within `ρ = ∑ A_j |y_j|` of the target `w = ∑ m_j y_j` (`m_j < A_j`). On the circle of
radius `R = (ρ + 1) u` about `w` we have `|z| ≤ Z`, so `|F(z)| ≤ (∑ |c_k|) Z^E e^(W Z)`. The Cauchy
estimate with zeros bounds `|F⁽ʳ⁾(w)|` by `r! · R/(R - 1) · ((ρ + 1)/(R - ρ))^(n ∏ t_j)` times this
maximum, and for `u ≥ 2` we have `R/(R - 1) ≤ 2` and `(ρ + 1)/(R - ρ) ≤ 1/(u - 1)`.
-/

theorem expPoly_grid_estimate {ι κ : Type*} [Fintype ι] (y : ι → ℂ)
    (hy : LinearIndependent ℚ y) (s : Finset κ) (c ω : κ → ℂ) (e : κ → ℕ) (F : ℂ → ℂ)
    (hF : ∀ z, F z = ∑ k ∈ s, c k * z ^ e k * Complex.exp (ω k * z))
    (W : ℝ) (E : ℕ) (hω : ∀ k ∈ s, ‖ω k‖ ≤ W) (he : ∀ k ∈ s, e k ≤ E)
    (t A : ι → ℕ) (htA : ∀ j, t j ≤ A j) (n : ℕ)
    (hvan : ∀ m : ι → ℕ, (∀ j, m j < t j) → ∀ i < n,
      iteratedDeriv i F (∑ j, (m j : ℂ) * y j) = 0)
    (u Z : ℝ) (hu : 2 ≤ u) (hZ : (∑ j, (A j : ℝ) * ‖y j‖ + 1) * (u + 1) ≤ Z)
    (m : ι → ℕ) (hm : ∀ j, m j < A j) (r : ℕ) :
    ‖iteratedDeriv r F (∑ j, (m j : ℂ) * y j)‖
      ≤ (r.factorial : ℝ) * 2 * (1 / (u - 1)) ^ ((∏ j, t j) * n) *
        ((∑ k ∈ s, ‖c k‖) * Z ^ E * Real.exp (W * Z)) := by
  classical
  have hFd : Differentiable ℂ F := by
    rw [show F = fun z => ∑ k ∈ s, c k * z ^ e k * Complex.exp (ω k * z) from funext hF]
    fun_prop
  set ρ : ℝ := ∑ j, (A j : ℝ) * ‖y j‖ with hρ
  have hρ0 : 0 ≤ ρ := by positivity
  -- the lattice points `∑ m' j * y j`, `m' j < t j`, are pairwise distinct
  set P : Finset ℂ := (Fintype.piFinset fun j => Finset.range (t j)).image
    (fun m' : ι → ℕ => ∑ j, (m' j : ℂ) * y j) with hP
  have hcard : P.card = ∏ j, t j := by
    rw [hP, Finset.card_image_of_injective, Fintype.card_piFinset]
    · simp
    intro a b hab
    have := hy.fintypeLinearCombination_injective (a₁ := fun j => (a j : ℚ))
      (a₂ := fun j => (b j : ℚ))
      (by simpa [Fintype.linearCombination_apply, Rat.smul_def] using hab)
    funext j; exact_mod_cast congrFun this j
  -- every point of the grid is within `ρ` of the target
  have hdist : ∀ m' : ι → ℕ, (∀ j, m' j < A j) →
      ‖∑ j, (m' j : ℂ) * y j - ∑ j, (m j : ℂ) * y j‖ ≤ ρ := by
    intro m' hm'
    rw [← Finset.sum_sub_distrib]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [← sub_mul, norm_mul, show (m' j : ℂ) - (m j : ℂ) = (((m' j : ℝ) - (m j : ℝ) : ℝ) : ℂ) by
      push_cast; ring, Complex.norm_real, Real.norm_eq_abs]
    have a1 : (m' j : ℝ) < A j := by exact_mod_cast hm' j
    have a2 : (m j : ℝ) < A j := by exact_mod_cast hm j
    exact mul_le_mul_of_nonneg_right (abs_sub_le_iff.2 ⟨by linarith [(m j).cast_nonneg (α := ℝ)],
      by linarith [(m' j).cast_nonneg (α := ℝ)]⟩) (norm_nonneg _)
  have hw : ‖∑ j, (m j : ℂ) * y j‖ ≤ ρ := by
    simpa using hdist (fun _ => 0) fun j => (Nat.zero_le _).trans_lt (hm j)
  -- the bound on the circle of radius `(ρ + 1) * u` around the target
  have hZ1 : 1 ≤ Z := by nlinarith
  have hM : ∀ z : ℂ, ‖z - ∑ j, (m j : ℂ) * y j‖ = (ρ + 1) * u →
      ‖F z‖ ≤ (∑ k ∈ s, ‖c k‖) * Z ^ E * Real.exp (W * Z) := by
    intro z hz
    have hzZ : ‖z‖ ≤ Z := by
      have := norm_le_insert' z (∑ j, (m j : ℂ) * y j)
      nlinarith
    rw [hF, Finset.sum_mul, Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k hk => ?_)
    rw [norm_mul, norm_mul, norm_pow, Complex.norm_exp]
    gcongr
    · exact (pow_le_pow_left₀ (norm_nonneg _) hzZ _).trans (pow_le_pow_right₀ hZ1 (he k hk))
    · exact (Complex.re_le_norm _).trans (by
        rw [norm_mul]
        exact mul_le_mul (hω k hk) hzZ (norm_nonneg _) ((norm_nonneg _).trans (hω k hk)))
  -- the target and the grid; every grid point is a zero of order at least `n`
  set w : ℂ := ∑ j, (m j : ℂ) * y j with hwdef
  set R : ℝ := (ρ + 1) * u with hR
  have hPw : ∀ z ∈ P, ‖z - w‖ ≤ ρ := fun z hz => by
    obtain ⟨m', hm', rfl⟩ := Finset.mem_image.1 hz
    exact hdist m' fun j =>
      ((by simpa using Fintype.mem_piFinset.1 hm' j) : m' j < t j).trans_le (htA j)
  have hM0 : 0 ≤ (∑ k ∈ s, ‖c k‖) * Z ^ E * Real.exp (W * Z) := by
    have : 0 ≤ Z ^ E := pow_nonneg (by linarith) _
    positivity
  by_cases hF0 : F = 0
  · rw [hF0, iteratedDeriv_const_zero, norm_zero]
    have : 0 ≤ 1 / (u - 1) := div_nonneg zero_le_one (by linarith)
    positivity
  have hle : P.card * n ≤ ∑ z ∈ P, analyticOrderNatAt F z := by
    rw [← smul_eq_mul]
    refine Finset.card_nsmul_le_sum _ _ _ fun z hz => ?_
    obtain ⟨m', hm', rfl⟩ := Finset.mem_image.1 hz
    have h1 := (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (hFd.analyticAt _)).2
      (hvan m' fun j => by simpa using Fintype.mem_piFinset.1 hm' j)
    rw [← Nat.cast_analyticOrderNatAt fun h => hF0
      ((AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero _ fun u => hFd.analyticAt u).1 h)] at h1
    exact_mod_cast h1
  -- the Cauchy estimate on the circle of radius `R = (ρ + 1) u` around the target
  have key := SixExponentials.cauchy_estimate_with_zeros F hFd w ρ R _ hρ0 (by nlinarith) P hPw hM r
  refine key.trans ?_
  have h1 : R / (R - 1) ≤ 2 := by rw [div_le_iff₀ (by nlinarith)]; nlinarith
  have h2 : (ρ + 1) / (R - ρ) ≤ 1 / (u - 1) := by
    rw [div_le_div_iff₀ (by nlinarith) (by linarith)]; nlinarith
  have h3 : 0 ≤ (ρ + 1) / (R - ρ) := div_nonneg (by positivity) (by nlinarith)
  have h4 : (ρ + 1) / (R - ρ) ≤ 1 := h2.trans (by rw [div_le_one (by linarith)]; linarith)
  rw [← hcard]
  calc _ ≤ (r.factorial : ℝ) * 2 * ((ρ + 1) / (R - ρ)) ^ (P.card * n) *
        ((∑ k ∈ s, ‖c k‖) * Z ^ E * Real.exp (W * Z)) := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul (mul_le_mul_of_nonneg_left h1 (by positivity))
          (pow_le_pow_of_le_one h3 h4 hle) (by positivity) (by positivity)) hM0
    _ ≤ _ := by gcongr

end SixExponentials.Transcendence
