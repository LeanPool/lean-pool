/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.EhrhardGaussian.Ehrhard.TimeInterpolationComparison
public import LeanPool.EhrhardGaussian.Ehrhard.OUUniformTimeBounds
public import LeanPool.EhrhardGaussian.Ehrhard.StrictSublevelContinuation

/-!
# Sufficient restricted time-dependent interpolation on finite intervals

The uniform initial gap is propagated by a proved continuation argument.
The matrix condition is required only on the strict sublevel. The conclusion
retains the full OU comparison, not just the uniform upper bound.
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Set
open EhrhardGaussian.Gaussian (coordinateDerivative)
open scoped Matrix BigOperators

namespace EhrhardGaussian.Ehrhard

/-- The restricted Hessian and gradient conditions propagate a strict sublevel bound and give the
interpolation inequality. -/
theorem restricted_time_interpolation {n k : ℕ} {f : Fin k → (Fin n → ℝ) → ℝ}
    (hf : ∀ i, HasPolynomiallyBoundedThirdCoordinateDerivatives (f i))
    {lo hi G H M : ℝ} (hG : 0 ≤ G) (hH : 0 ≤ H) (hM : 0 ≤ M)
    (hbound : ∀ i y, f i y ∈ Icc lo hi) (hgrad : ∀ i y, ‖fderiv ℝ (f i) y‖ ≤ G)
    (hsecond : ∀ i j l y, |coordinateDerivative (coordinateDerivative (f i) j) l y| ≤ H)
    (hgenerator : ∀ i y, |ouGenerator (f i) y| ≤ M)
    {l c T : ℝ} (hl : 0 < l) (hlc : l < c) (hcT : c ≤ T)
    {J : ℝ × (Fin k → ℝ) → ℝ}
    (hJ : ∀ s ∈ Icc l T, ∀ z : Fin k → ℝ, (∀ i, z i ∈ Icc lo hi) → ContDiffAt ℝ 2 J (s, z))
    (C : Matrix (Fin k) (Fin n) ℝ) (v : ℝ → (Fin n → ℝ) → (Fin k → ℝ))
    (D : ℝ → (Fin k → ℝ) → Matrix (Fin k) (Fin k) ℝ) (K : ℝ → ℝ)
    (hK : ∀ s ∈ Icc c T, 0 < K s)
    (hshape : ∀ s ∈ Icc c T, ∀ y i j,
      coordinateDerivative (fun z => ouAverage (f i) z s) j y = v s y i * C i j)
    (hgradient : ∀ s ∈ Icc c T, ∀ y,
      v s y ⬝ᵥ (D s (ouFamily f (s, y)) *ᵥ v s y) ≤ 1 / K s)
    {a b : ℝ} (hba : b < a)
    (hconditions : ∀ s ∈ Icc c T, ∀ y, J (s, ouFamily f (s, y)) < a →
      fderiv ℝ J (s, ouFamily f (s, y)) (1, 0) ≤ 0 ∧
      (((C * Cᵀ) ⊙ coordinateHessian (fun z => J (s, z)) (ouFamily f (s, y))) -
        (K s * fderiv ℝ J (s, ouFamily f (s, y)) (1, 0)) • D s (ouFamily f (s, y))).PosSemidef)
    (hstart : ∀ y, J (c, ouFamily f (c, y)) ≤ b) :
    (∀ s ∈ Icc c T, ∀ y, J (s, ouFamily f (s, y)) ≤ b) ∧
      ∀ x, J (T, ouFamily f (T, x)) ≤
        ouAverage (fun y => J (c, ouFamily f (c, y))) x (T - c) := by
  have hf₂ := fun i => hasPolynomiallyBoundedSecond_of_third (hf i)
  have hJrestrict (s) (hs : s ∈ Icc c T) (z) (hz : ∀ i, z i ∈ Icc lo hi) :=
    hJ s ⟨hlc.le.trans hs.1, hs.2⟩ z hz
  obtain ⟨L, hL, hLip⟩ := exists_time_ouComposition_lipschitz hf₂ (hl.trans hlc) hM
    hbound hgenerator hJrestrict
  let F := fun s y => J (s, ouFamily f (s, y))
  have hpropagate (r s : ℝ) (hr : r ∈ Icc c T) (hs : s ∈ Icc c T) (hrs : r ≤ s)
      (hsub : ∀ t ∈ Icc r s, ∀ y, F t y < a) (hinit : ∀ y, F r y ≤ b) : ∀ y, F s y ≤ b := by
    have hmem (t) (ht : t ∈ Icc r s) : t ∈ Icc c T := ⟨hr.1.trans ht.1, ht.2.trans hs.2⟩
    have hresult := time_interpolation_comparison hf hG hH hbound hgrad hsecond
      hl (hlc.trans_le hr.1) hrs
      (fun t ht z hz => hJ t ⟨ht.1, ht.2.trans hs.2⟩ z hz) C v D K
      (fun t ht => hK t (hmem t ht)) (fun t ht => hshape t (hmem t ht))
      (fun t ht => hgradient t (hmem t ht))
      (fun t ht => hconditions t (hmem t ht)) hsub hinit
    exact fun y => (hresult y).2
  have hstay : ∀ s ∈ Icc c T, ∀ y, F s y ≤ b := by
    intro s hs
    have hmem (r) (hr : r ∈ Icc c s) : r ∈ Icc c T := ⟨hr.1, hr.2.trans hs.2⟩
    exact strict_sublevel_continuation_of_uniform_lipschitz hs.1 hba hL
      (fun r hr t ht y => hLip r (hmem r hr) t (hmem t ht) y)
      (fun r t hr ht => hpropagate r t (hmem r hr) (hmem t ht)) hstart
  refine ⟨hstay, ?_⟩
  have hresult := time_interpolation_comparison hf hG hH hbound hgrad hsecond hl hlc hcT hJ C v D K
    hK hshape hgradient hconditions (fun s hs y => (hstay s hs y).trans_lt hba) hstart
  exact fun x => (hresult x).1

end EhrhardGaussian.Ehrhard

end
