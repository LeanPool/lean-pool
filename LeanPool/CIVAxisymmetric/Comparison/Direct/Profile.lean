/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# A smooth convex profile vanishing on the nonpositive half-line

The energy of the comparison argument of `lem:aniso:comparison` measures the excess of the
mollified solution over the barrier through a profile `G` applied pointwise. The manuscript uses
`G(y) = (y₊)²` (`eq:aniso:comparison:positive:energy`); here `G` is the primitive
`G(y) = ∫₀^y smoothTransition` of Mathlib's smooth monotone transition function. It has the three
properties the argument uses of `(y₊)²`: it vanishes exactly on `(-∞, 0]`, it is convex with
`0 ≤ G' ≤ 1`, and it is smooth, so that `G ∘ w` is an admissible test function whenever `w` is
smooth with `w < 0` off a compact set.

The last part of the file is the chain rule for `G` along a primitive `c + ∫ₐᵗ h` of an
integrable function, obtained from absolute continuity.
-/

public section

open MeasureTheory Set Filter Topology intervalIntegral
open scoped ContDiff


noncomputable section

namespace CIV

/-- The comparison profile `G(y) = ∫₀^y smoothTransition`. -/
@[expose] def comparisonProfile (y : ℝ) : ℝ := ∫ t in (0 : ℝ)..y, Real.smoothTransition t

theorem hasDerivAt_comparisonProfile (y : ℝ) :
    HasDerivAt comparisonProfile (Real.smoothTransition y) y :=
  (Real.smoothTransition.continuous.integral_hasStrictDerivAt 0 y).hasDerivAt

theorem differentiable_comparisonProfile : Differentiable ℝ comparisonProfile :=
  fun y => (hasDerivAt_comparisonProfile y).differentiableAt

theorem deriv_comparisonProfile : deriv comparisonProfile = Real.smoothTransition :=
  funext fun y => (hasDerivAt_comparisonProfile y).deriv

theorem contDiff_comparisonProfile : ContDiff ℝ (⊤ : ℕ∞) comparisonProfile := by
  have h : ContDiff ℝ ∞ comparisonProfile := by
    rw [contDiff_infty_iff_deriv, deriv_comparisonProfile]
    exact ⟨differentiable_comparisonProfile, Real.smoothTransition.contDiff⟩
  exact h

theorem comparisonProfile_eq_zero_of_nonpos {y : ℝ} (hy : y ≤ 0) : comparisonProfile y = 0 := by
  unfold comparisonProfile
  have h : ∀ t ∈ uIcc (0 : ℝ) y, Real.smoothTransition t = 0 := by
    intro t ht
    rw [uIcc_of_ge hy] at ht
    exact Real.smoothTransition.zero_of_nonpos ht.2
  rw [intervalIntegral.integral_congr h]
  simp

theorem comparisonProfile_pos {y : ℝ} (hy : 0 < y) : 0 < comparisonProfile y :=
  intervalIntegral_pos_of_pos_on (Real.smoothTransition.continuous.intervalIntegrable _ _)
    (fun _ ht => Real.smoothTransition.pos_of_pos ht.1) hy

theorem comparisonProfile_nonneg (y : ℝ) : 0 ≤ comparisonProfile y := by
  rcases le_or_gt y 0 with hy | hy
  · exact (comparisonProfile_eq_zero_of_nonpos hy).ge
  · exact (comparisonProfile_pos hy).le

theorem comparisonProfile_eq_zero_iff {y : ℝ} : comparisonProfile y = 0 ↔ y ≤ 0 :=
  ⟨fun h => not_lt.mp fun hy => (comparisonProfile_pos hy).ne' h,
    comparisonProfile_eq_zero_of_nonpos⟩

/-- `G` is `1`-Lipschitz, since `0 ≤ G' ≤ 1`. -/
theorem lipschitzWith_comparisonProfile : LipschitzWith 1 comparisonProfile := by
  refine lipschitzWith_of_nnnorm_deriv_le differentiable_comparisonProfile fun y => ?_
  rw [deriv_comparisonProfile, ← NNReal.coe_le_coe, coe_nnnorm, Real.norm_eq_abs,
    abs_of_nonneg (Real.smoothTransition.nonneg y)]
  exact Real.smoothTransition.le_one y

theorem abs_comparisonProfile_sub_le (a b : ℝ) :
    |comparisonProfile a - comparisonProfile b| ≤ |a - b| := by
  have h := lipschitzWith_comparisonProfile.dist_le_mul a b
  simpa [Real.dist_eq] using h

/-- Chain rule for `G` along a primitive: if `h` is integrable on `[a, b]`, then
`G(c + ∫ₐᵇ h) = G(c) + ∫ₐᵇ G'(c + ∫ₐˢ h) h(s) ds`. -/
theorem comparisonProfile_add_intervalIntegral {h : ℝ → ℝ} {a b : ℝ}
    (hh : IntervalIntegrable h volume a b) (c : ℝ) :
    comparisonProfile (c + ∫ s in a..b, h s) = comparisonProfile c
      + ∫ s in a..b, Real.smoothTransition (c + ∫ r in a..s, h r) * h s := by
  set F : ℝ → ℝ := fun t => c + ∫ s in a..t, h s with hFdef
  have ha : a ∈ uIcc a b := left_mem_uIcc
  have hFac : AbsolutelyContinuousOnInterval F a b := by
    have hprim : AbsolutelyContinuousOnInterval (fun t => ∫ s in a..t, h s) a b :=
      hh.absolutelyContinuousOnInterval_intervalIntegral ha
    have hconst : AbsolutelyContinuousOnInterval (fun _ : ℝ => c) a b := by
      have hLip : LipschitzOnWith 0 (fun _ : ℝ => c) (uIcc a b) := fun x _ y _ => by simp
      exact hLip.absolutelyContinuousOnInterval
    exact hconst.add hprim
  have hGF : AbsolutelyContinuousOnInterval (comparisonProfile ∘ F) a b :=
    lipschitzWith_comparisonProfile.comp_absolutelyContinuousOnInterval hFac
  have hFTC := hGF.integral_deriv_eq_sub
  have hderiv : ∀ᵐ s, s ∈ uIoc a b →
      deriv (comparisonProfile ∘ F) s = Real.smoothTransition (F s) * h s := by
    filter_upwards [hh.ae_hasDerivAt_integral] with s hs hsmem
    have hF : HasDerivAt F (h s) s := (hs (uIoc_subset_uIcc hsmem) a ha).const_add c
    exact ((hasDerivAt_comparisonProfile (F s)).comp s hF).deriv
  rw [intervalIntegral.integral_congr_ae hderiv] at hFTC
  have hFa : F a = c := by simp [hFdef]
  simp only [Function.comp_apply, hFa] at hFTC
  simp only [hFdef] at hFTC ⊢
  linarith only [hFTC]

end CIV
