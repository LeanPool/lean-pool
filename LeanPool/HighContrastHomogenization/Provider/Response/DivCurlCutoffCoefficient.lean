/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Response.DivCurlWeakNormTerm

/-!
# High-contrast homogenization: Provider.Response.DivCurlCutoffCoefficient

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The div-curl coefficient at a cutoff of the cube's own scale

The div-curl weak-norm coefficient depends on the cube through its side length
and through the two bounds carried by the cutoff's gradient field: the sup norm
of that field and a bound for its derivative.  For a cutoff adapted to the cube
these two bounds carry one and two negative powers of the side length
respectively, so the side length cancels once and the coefficient inherits a
single negative power of the side length with a dimension-only prefactor.

The prefactor is recorded here explicitly.  The cutoff's own constant is kept
abstract: for the canonical smooth product cutoff it necessarily grows with the
dimension, so no numeral is available.
-/

namespace HCPolySupport
namespace HighContrast
namespace Response

noncomputable section

open Book.Ch05.Section53.JUpperBoundWeakNorms

/-- The dimension-only prefactor of the div-curl coefficient. -/
@[expose]
def divCurlDimensionCoeff (d : ℕ) [NeZero d] : ℝ :=
  (6 * (((d : ℝ) * Legacy.cubeNeumannW22CalderonZygmundConstant d *
      (3 : ℝ) ^ ((d : ℝ) + 1)) * (d : ℝ))) *
    ((d : ℝ) * (3 : ℝ) ^ ((d : ℝ) + (1 / 2 : ℝ)))

/-- The dimension-only prefactor is nonnegative. -/
theorem divCurlDimensionCoeff_nonneg (d : ℕ) [NeZero d] :
    0 ≤ divCurlDimensionCoeff d := by
  have hcz : 0 ≤ Legacy.cubeNeumannW22CalderonZygmundConstant d :=
    Legacy.cubeNeumannW22CalderonZygmundConstant_nonneg d
  rw [divCurlDimensionCoeff]
  positivity

/-- **The div-curl coefficient at an adapted cutoff.**  With the cutoff's
gradient field bounded by `Ccut` times the reciprocal side length and its
derivative by `Ccut` times the square of the reciprocal side length, the
coefficient is at most a dimension-only multiple of `Ccut` times the reciprocal
side length. -/
theorem divCurlWeakNormCoeff_originCube_le {d : ℕ} [NeZero d] (t : ℤ)
    {B Bone Ccut : ℝ}
    (hBbound : B ≤ Ccut * (3 : ℝ) ^ (-2 * t))
    (hBonebound : Bone ≤ Ccut * (3 : ℝ) ^ (-t)) :
    divCurlWeakNormCoeff (originCube d t) B Bone ≤
      divCurlDimensionCoeff d * (Ccut * (3 : ℝ) ^ (-t)) := by
  have hthree : (3 : ℝ) ≠ 0 := by norm_num
  have hcz : 0 ≤ Legacy.cubeNeumannW22CalderonZygmundConstant d :=
    Legacy.cubeNeumannW22CalderonZygmundConstant_nonneg d
  have hpoincare :
      Book.Ch01.Legacy.fullVectorPoincareConstant (originCube d t) =
        (d : ℝ) * Legacy.cubeNeumannW22CalderonZygmundConstant d :=
    fullVectorPoincareCubeConstant_eq_dimensionConstant (originCube d t)
  have hscale : cubeScaleFactor (originCube d t) = (3 : ℝ) ^ t :=
    cubeScaleFactor_originCube t
  have hpow : (3 : ℝ) ^ t * (3 : ℝ) ^ (-2 * t) = (3 : ℝ) ^ (-t) := by
    rw [← zpow_add₀ hthree]
    congr 1
    ring
  have hfront :
      cubeScaleFactor (originCube d t) * B + Bone ≤
        2 * (Ccut * (3 : ℝ) ^ (-t)) := by
    have hpos : (0 : ℝ) < (3 : ℝ) ^ t := by positivity
    have hfirst : (3 : ℝ) ^ t * B ≤ Ccut * (3 : ℝ) ^ (-t) := by
      calc (3 : ℝ) ^ t * B ≤ (3 : ℝ) ^ t * (Ccut * (3 : ℝ) ^ (-2 * t)) :=
            mul_le_mul_of_nonneg_left hBbound hpos.le
        _ = Ccut * ((3 : ℝ) ^ t * (3 : ℝ) ^ (-2 * t)) := by ring
        _ = Ccut * (3 : ℝ) ^ (-t) := by rw [hpow]
    rw [hscale]
    linarith only [hfirst, hBonebound]
  have hKnonneg :
      0 ≤ (Book.Ch01.Legacy.fullVectorPoincareConstant (originCube d t) *
        (3 : ℝ) ^ ((d : ℝ) + 1)) * (d : ℝ) := by
    rw [hpoincare]
    positivity
  have hLnonneg : 0 ≤ (d : ℝ) * (3 : ℝ) ^ ((d : ℝ) + (1 / 2 : ℝ)) := by
    positivity
  have hstep :
      3 * (cubeScaleFactor (originCube d t) * B + Bone) ≤
        3 * (2 * (Ccut * (3 : ℝ) ^ (-t))) := by
    linarith only [hfront]
  rw [divCurlWeakNormCoeff_eq]
  calc
    3 * (cubeScaleFactor (originCube d t) * B + Bone) *
          ((Book.Ch01.Legacy.fullVectorPoincareConstant (originCube d t) *
            (3 : ℝ) ^ ((d : ℝ) + 1)) * (d : ℝ)) *
          ((d : ℝ) * (3 : ℝ) ^ ((d : ℝ) + (1 / 2 : ℝ))) ≤
        3 * (2 * (Ccut * (3 : ℝ) ^ (-t))) *
          ((Book.Ch01.Legacy.fullVectorPoincareConstant (originCube d t) *
            (3 : ℝ) ^ ((d : ℝ) + 1)) * (d : ℝ)) *
          ((d : ℝ) * (3 : ℝ) ^ ((d : ℝ) + (1 / 2 : ℝ))) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hstep hKnonneg) hLnonneg
    _ = divCurlDimensionCoeff d * (Ccut * (3 : ℝ) ^ (-t)) := by
      rw [divCurlDimensionCoeff, hpoincare]
      ring

end

end Response
end HighContrast
end HCPolySupport
