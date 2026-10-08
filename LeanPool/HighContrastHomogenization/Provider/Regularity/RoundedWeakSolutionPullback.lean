/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Analytic.AffineWeakGradient
public import LeanPool.HighContrastHomogenization.Analytic.AffineWeakSolution
public import LeanPool.HighContrastHomogenization.Analytic.SkewGauge
public import LeanPool.HighContrastHomogenization.Provider.Regularity.AffineGradientQuotientInverse
public import LeanPool.HighContrastHomogenization.Provider.Regularity.RoundedAffineFields
public import LeanPool.HighContrastHomogenization.Provider.Selection.EnclosureGeometry

/-!
# High-contrast homogenization: Provider.Regularity.RoundedWeakSolutionPullback

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Weak-solution transfer through the rounded normalization

The physical equation is first put in the constant-skew gauge, then multiplied
by the nonzero scalar normalizer, and finally pulled back by the rounded map.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory Set

noncomputable section

variable {d : ℕ}

/-- Multiplying a coefficient field by a nonzero scalar does not change its
homogeneous weak-solution class. -/
theorem isWeakSolutionOn_smul_coefficient_iff {U : Set (Vec d)}
    (b : CoeffField d) (F : Vec d → Vec d) {c : ℝ} (hc : c ≠ 0) :
    IsWeakSolutionOn (fun x ↦ c • b x) U F ↔
      IsWeakSolutionOn b U F := by
  let p : (Vec d → ℝ) → Vec d → ℝ := fun φ x ↦
    vecDot (smoothGrad φ x) (matVecMul (b x) (F x))
  have hpair : ∀ φ : Vec d → ℝ,
      (fun x ↦ vecDot (smoothGrad φ x)
        (matVecMul (c • b x) (F x))) = fun x ↦ c * p φ x := by
    intro φ
    funext x
    simp only [smul_matVecMul, vecDot_smul_right, p]
  constructor
  · intro h φ hφ
    obtain ⟨hint, hzero⟩ := h φ hφ
    rw [hpair] at hint hzero
    have hpint : IntegrableOn (p φ) U volume :=
      (integrable_const_mul_iff (isUnit_iff_ne_zero.mpr hc) (p φ)).mp hint
    constructor
    · exact hpint
    · rw [integral_const_mul] at hzero
      exact (mul_eq_zero.mp hzero).resolve_left hc
  · intro h φ hφ
    obtain ⟨hint, hzero⟩ := h φ hφ
    rw [hpair]
    constructor
    · exact hint.const_mul c
    · rw [integral_const_mul, hzero, mul_zero]

end

end HighContrast
end HCPolySupport
