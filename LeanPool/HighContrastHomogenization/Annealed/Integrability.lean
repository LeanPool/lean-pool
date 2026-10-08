/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Annealed.SourceIntegrability
public import LeanPool.HighContrastHomogenization.Annealed.ResponseBound
public import LeanPool.HighContrastHomogenization.Annealed.Measurability

/-!
# High-contrast homogenization: Annealed.Integrability

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Integrability of the coarse response over the law

Under `e.coarse.ellipticity` every entry of the coarse response on a centered
cube is integrable over the law, at every scale.  The assumption run at the
sample's own burn scale bounds the response by an affine function of the source,
and the gauge tail makes the source integrable; the measurability of the coarse
observable for the local sigma-fields holds on the coefficient space itself.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-- **The integrability of the annealed block.**  Under
`e.coarse.ellipticity` every entry of the coarse response on a centered cube
is integrable over the law, at every scale. -/
theorem hasIntegrableCoarseBlock_of_coarseEllipticityDagger
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P] {g : ℝ} {E : BlockMat d}
    {Ψ : ℝ → ℝ} {K : ℝ} {S : CoeffSpace d → ℝ}
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S) (m : ℤ) :
    HasIntegrableCoarseBlock P (centeredCube d m) := by
  have hmeas : HasMeasurableCoarseBlock P (centeredCube d m) :=
    hasMeasurableCoarseBlock_centeredCube P m
  have hS := integrable_source_of_coarseEllipticityDagger hdag
  have hdom : Integrable
      (fun a => 6 * blockEntrySum E * (1 + (3 : ℝ) ^ (-m) * S a)) P :=
    ((integrable_const (1 : ℝ)).add (hS.const_mul ((3 : ℝ) ^ (-m)))).const_mul
      (6 * blockEntrySum E)
  intro α β
  refine Integrable.mono' hdom (hmeas α β) ?_
  filter_upwards [ae_abs_blockMatEntry_coarseBlock_le hdag m] with a ha
  rw [Real.norm_eq_abs]
  exact ha α β

end

end HighContrast
end HCPolySupport
