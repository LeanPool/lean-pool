/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Prerequisites.Serrin.CutoffProfiles
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.BallBasics
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Derivative bounds for the Serrin cutoff profiles

The ball cutoff of radius `ρ` has `n`-th derivative of size `ρ⁻ⁿ` and the time cutoff of
parabolic length `ρ²` has `n`-th derivative of size `ρ⁻²ⁿ`, uniformly in the centre. These are
the scaling bounds for the cutoffs of the backward windows used in the interior estimates of the
proof of `lem:aniso:annulus`.
-/

public section

open Set
open CKN.Foundation.Parabolic

noncomputable section
namespace CIV



/-- The ball cutoff at `x` of radius `ρ` is the unit cutoff at the origin evaluated at
`ρ⁻¹ (y - x)`. -/
theorem serrinBallCutoff_eq_unit (x : Vec3) {ρ : ℝ} (hρ : 0 < ρ) (y : Vec3) :
    serrinBallCutoff x ρ y = serrinBallCutoff 0 1 (ρ⁻¹ • (y - x)) := by
  unfold serrinBallCutoff
  congr 1
  simp only [Pi.smul_apply, Pi.sub_apply, Pi.zero_apply, sub_zero, smul_eq_mul, one_pow, div_one]
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  field_simp

/-- The unit ball cutoff has compact support. -/
theorem hasCompactSupport_serrinBallCutoff_unit : HasCompactSupport (serrinBallCutoff 0 1) := by
  refine HasCompactSupport.intro (K := closure (vec3Ball 0 1))
    (isCompact_closure_vec3Ball one_pos) (fun y hy => ?_)
  rw [closure_vec3Ball one_pos] at hy
  simp only [mem_ofPred_eq, not_le] at hy
  exact (serrinBallCutoff_support 0 one_pos y).2.1 hy.le

/-- Scaling bound for the derivatives of the ball cutoff. -/
theorem norm_iteratedFDeriv_serrinBallCutoff_le : ∃ C : ℕ → ℝ, ∀ (n : ℕ) (x : Vec3) (ρ : ℝ),
    0 < ρ → ∀ y : Vec3, ‖iteratedFDeriv ℝ n (serrinBallCutoff x ρ) y‖ ≤ C n / ρ ^ n := by
  have hB : ContDiff ℝ (⊤ : ℕ∞) (serrinBallCutoff 0 1) := (serrinBallCutoff_support 0 one_pos 0).2.2
  have hbd : ∀ n : ℕ, ∃ C, ∀ y, ‖iteratedFDeriv ℝ n (serrinBallCutoff 0 1) y‖ ≤ C := fun n =>
    (hB.continuous_iteratedFDeriv (by exact_mod_cast le_top)).bounded_above_of_compact_support
      (hasCompactSupport_serrinBallCutoff_unit.iteratedFDeriv n)
  choose C hC using hbd
  refine ⟨C, fun n x ρ hρ y => ?_⟩
  set L : Vec3 →L[ℝ] Vec3 := ρ⁻¹ • ContinuousLinearMap.id ℝ Vec3 with hL
  have hfun : serrinBallCutoff x ρ = fun y => (serrinBallCutoff 0 1 ∘ L) (y - x) := by
    funext y
    rw [serrinBallCutoff_eq_unit x hρ y]
    rfl
  have hLn : ‖L‖ ≤ ρ⁻¹ := by
    rw [hL]
    refine (norm_smul_le (ρ⁻¹ : ℝ) (ContinuousLinearMap.id ℝ Vec3)).trans ?_
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hρ)]
    exact mul_le_of_le_one_right (inv_pos.mpr hρ).le ContinuousLinearMap.norm_id_le
  rw [hfun, iteratedFDeriv_comp_sub n x y,
    L.iteratedFDeriv_comp_right hB (y - x) (by exact_mod_cast le_top)]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, div_eq_mul_inv, ← inv_pow]
  have hC0 : 0 ≤ C n := (norm_nonneg _).trans (hC n 0)
  exact mul_le_mul (hC n _) (pow_le_pow_left₀ (norm_nonneg _) hLn n) (by positivity) hC0

/-- The time profile is smooth. -/
theorem contDiff_serrinTimeBump : ContDiff ℝ (⊤ : ℕ∞) serrinTimeBump :=
  (serrinTimeBump_support (s := 0) one_pos 0).2.2

/-- The derivative of the time profile vanishes off `[-1, -1/2]`. -/
theorem hasCompactSupport_deriv_serrinTimeBump : HasCompactSupport (deriv serrinTimeBump) := by
  refine HasCompactSupport.intro (K := Icc (-1 : ℝ) (-1 / 2)) isCompact_Icc (fun τ hτ => ?_)
  rcases not_and_or.mp hτ with h | h
  · have hlt : τ < -1 := lt_of_not_ge h
    have hev : serrinTimeBump =ᶠ[nhds τ] fun _ => (0 : ℝ) := by
      filter_upwards [Iio_mem_nhds hlt] with σ hσ
      unfold serrinTimeBump
      exact Real.smoothTransition.zero_of_nonpos (by linarith only [show σ < -1 from hσ])
    rw [hev.deriv_eq]
    simp
  · have hlt : -1 / 2 < τ := lt_of_not_ge h
    have hev : serrinTimeBump =ᶠ[nhds τ] fun _ => (1 : ℝ) := by
      filter_upwards [Ioi_mem_nhds hlt] with σ hσ
      unfold serrinTimeBump
      exact Real.smoothTransition.one_of_one_le (by linarith only [show -1 / 2 < σ from hσ])
    rw [hev.deriv_eq]
    simp

/-- The derivatives of the time profile are bounded. -/
theorem exists_abs_iteratedDeriv_serrinTimeBump_le (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ τ : ℝ, |iteratedDeriv n serrinTimeBump τ| ≤ C := by
  cases n with
  | zero =>
    refine ⟨1, zero_le_one, fun τ => ?_⟩
    rw [iteratedDeriv_zero]
    unfold serrinTimeBump
    rw [abs_of_nonneg (Real.smoothTransition.nonneg _)]
    exact Real.smoothTransition.le_one _
  | succ m =>
    have hd : ContDiff ℝ (⊤ : ℕ∞) (deriv serrinTimeBump) :=
      contDiff_serrinTimeBump.iterate_deriv 1
    obtain ⟨C, hC⟩ := (hd.continuous_iteratedFDeriv (m := m) (by exact_mod_cast le_top)
      ).bounded_above_of_compact_support (hasCompactSupport_deriv_serrinTimeBump.iteratedFDeriv m)
    refine ⟨C, (norm_nonneg _).trans (hC 0), fun τ => ?_⟩
    rw [iteratedDeriv_succ', ← Real.norm_eq_abs, ← norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    exact hC τ

/-- Scaling bound for the derivatives of the time cutoff of parabolic length `ρ²`. -/
theorem abs_iteratedDeriv_serrinTimeBump_scaled_le : ∃ C : ℕ → ℝ, ∀ (n : ℕ) (s ρ : ℝ), 0 < ρ →
    ∀ s' : ℝ, |iteratedDeriv n (fun r : ℝ => serrinTimeBump ((r - s) / ρ ^ 2)) s'| ≤
      C n / ρ ^ (2 * n) := by
  choose C hC0 hC using exists_abs_iteratedDeriv_serrinTimeBump_le
  refine ⟨C, fun n s ρ hρ s' => ?_⟩
  set c : ℝ := (ρ ^ 2)⁻¹ with hc
  have hfun : (fun r : ℝ => serrinTimeBump ((r - s) / ρ ^ 2)) =
      fun r => (fun y => serrinTimeBump (y + -(c * s))) (c * r) := by
    funext r
    congr 1
    rw [hc]
    ring
  have hH : ContDiff ℝ (n : ℕ∞) (fun y => serrinTimeBump (y + -(c * s))) :=
    (contDiff_serrinTimeBump.comp (contDiff_id.add contDiff_const)).of_le
      (by exact_mod_cast le_top)
  rw [hfun, iteratedDeriv_comp_const_mul hH c]
  simp only
  rw [iteratedDeriv_comp_add_const, abs_mul, abs_pow, abs_of_pos (by positivity : 0 < c)]
  have hcn : c ^ n = 1 / ρ ^ (2 * n) := by
    rw [hc, pow_mul, inv_pow, one_div]
  rw [hcn, div_eq_mul_one_div (C n)]
  rw [mul_comm]
  exact mul_le_mul_of_nonneg_right (hC n _) (by positivity)

end CIV
