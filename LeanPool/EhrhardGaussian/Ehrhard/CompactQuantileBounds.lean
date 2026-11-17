/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.EhrhardGaussian.Ehrhard.CompactDerivativeBounds
import Mathlib.Analysis.Calculus.MeanValue

/-! # Quantile bounds and Lipschitz continuity on compact interior boxes -/

@[expose] public noncomputable section

open Set
open scoped ContDiff

namespace EhrhardGaussian.Ehrhard

/-- Gaussian quantiles are uniformly bounded on a compact subinterval of the probability interval.
-/
theorem exists_quantile_bound {k : ℕ} {a b : ℝ} (ha : 0 < a) (hb : b < 1) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ x : Fin k → ℝ, (∀ i, x i ∈ Icc a b) →
      ∀ i, |gaussianCDFChart.symm (x i)| ≤ L := by
  let Q := fun x : Fin k → ℝ => fun i => gaussianCDFChart.symm (x i)
  have hcont : ContinuousOn Q {x : Fin k → ℝ | ∀ i, x i ∈ Icc a b} := by
    intro x hx
    apply continuousWithinAt_pi.mpr
    intro i
    have hi : ContinuousAt gaussianCDFChart.symm (x i) :=
      (contDiffAt_gaussianCDFChart_symm ⟨ha.trans_le (hx i).1, ((hx i).2).trans_lt hb⟩).continuousAt
    exact (hi.comp (f := fun z : Fin k → ℝ => z i) (continuous_apply
      i).continuousAt).continuousWithinAt
  obtain ⟨C, hC⟩ := (isCompact_probabilitySubbox a b).exists_bound_of_continuousOn hcont
  refine ⟨max 0 C, le_max_left _ _, ?_⟩
  intro x hx i
  have h : ‖Q x i‖ ≤ max 0 C := (norm_le_pi_norm (Q x) i).trans ((hC x hx).trans (le_max_right _ _))
  simpa only [Q, Real.norm_eq_abs] using h

/-- A box defined by a common closed interval in each coordinate is convex. -/
theorem convex_probabilitySubbox {k : ℕ} (a b : ℝ) :
    Convex ℝ {x : Fin k → ℝ | ∀ i, x i ∈ Icc a b} := by
  have h := convex_pi (s := (Set.univ : Set (Fin k)))
    (fun _ _ => (show Convex ℝ (Icc a b) from convex_Icc a b))
  simpa only [Set.pi, mem_univ, forall_const] using h

/-- A linear combination of Gaussian quantiles is Lipschitz on each compact probability box. -/
theorem exists_quantileLinear_lipschitz {k : ℕ} (θ : Fin k → ℝ) {a b : ℝ}
    (ha : 0 < a) (hb : b < 1) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ x y : Fin k → ℝ,
      (∀ i, x i ∈ Icc a b) → (∀ i, y i ∈ Icc a b) →
        |quantileLinear θ x - quantileLinear θ y| ≤ L * ‖x - y‖ := by
  have hdiff (z : Fin k → ℝ) (hz : ∀ i, z i ∈ Icc a b) : ContDiffAt ℝ 2 (quantileLinear θ) z :=
    (contDiffAt_quantileLinear θ (fun i => ⟨ha.trans_le (hz i).1, ((hz i).2).trans_lt hb⟩)).of_le
      (by simp)
  obtain ⟨L, hL, _, hbound, _, _⟩ :=
    IsCompact.exists_bound_secondDerivatives (isCompact_probabilitySubbox a b) hdiff
  refine ⟨L, hL, ?_⟩
  intro x y hx hy
  simpa only [Real.norm_eq_abs] using (convex_probabilitySubbox (k := k) a
    b).norm_image_sub_le_of_norm_fderiv_le
    (fun z hz => (hdiff z hz).differentiableAt (by norm_num : (2 : WithTop ℕ∞) ≠ 0))
    hbound hy hx

/-- A single uniform tolerance preserves the coupled strict gap and keeps
every approximating probability coordinate in a fixed interior box. -/
theorem exists_quantile_gap_tolerance {k : ℕ} (θ : Fin k → ℝ) {a b η : ℝ}
    (ha : 0 < a) (hb : b < 1) (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x y : Fin k → ℝ,
      (∀ i, x i ∈ Icc a b) → (∀ i, |y i - x i| < δ) → quantileLinear θ x ≤ -η →
        (∀ i, y i ∈ Icc (a / 2) ((b + 1) / 2)) ∧ quantileLinear θ y ≤ -η / 2 := by
  have ha' : 0 < a / 2 := half_pos ha
  have hb' : (b + 1) / 2 < 1 := by linarith only [hb]
  obtain ⟨L, hL, hLip⟩ := exists_quantileLinear_lipschitz θ ha' hb'
  let δ := min (a / 2) (min ((1 - b) / 2) (η / (2 * (L + 1))))
  have hL₁ : 0 < L + 1 := by linarith only [hL]
  have hδ : 0 < δ := lt_min ha' (lt_min (half_pos (sub_pos.mpr hb)) (div_pos hη (by positivity)))
  have hδa : δ ≤ a / 2 := min_le_left _ _
  have hδb : δ ≤ (1 - b) / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hδL : δ ≤ η / (2 * (L + 1)) := (min_le_right _ _).trans (min_le_right _ _)
  have hδcoeff : L * δ ≤ η / 2 := by
    have h := (le_div_iff₀ (by positivity : 0 < 2 * (L + 1))).mp hδL
    nlinarith only [h, hδ]
  refine ⟨δ, hδ, ?_⟩
  intro x y hx hclose hgap
  have hx' (i) : x i ∈ Icc (a / 2) ((b + 1) / 2) := by
    constructor <;> linarith only [(hx i).1, (hx i).2, ha, hb]
  have hy (i) : y i ∈ Icc (a / 2) ((b + 1) / 2) := by
    have h := abs_lt.mp (hclose i)
    constructor <;> linarith only [h.1, h.2, (hx i).1, (hx i).2, hδa, hδb]
  have hnorm : ‖y - x‖ ≤ δ := (pi_norm_le_iff_of_nonneg hδ.le).mpr fun i => by
    simpa only [Pi.sub_apply, Real.norm_eq_abs] using (hclose i).le
  have h := hLip y x hy hx'
  have hdiff := (le_abs_self (quantileLinear θ y - quantileLinear θ x)).trans
    (h.trans (mul_le_mul_of_nonneg_left hnorm hL))
  exact ⟨hy, by linarith only [hdiff, hδcoeff, hgap]⟩

end EhrhardGaussian.Ehrhard

end
