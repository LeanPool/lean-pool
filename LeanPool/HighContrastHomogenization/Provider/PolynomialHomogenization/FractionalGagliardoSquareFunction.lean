/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.FractionalBoundaryWeightedSchur
public import LeanPool.HighContrastHomogenization.Analytic.TestNorms

/-!
# High-contrast homogenization: Provider.PolynomialHomogenization.FractionalGagliardoSquareFunction

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The global fractional Gagliardo square function
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- The unnormalized pointwise fractional energy in the second variable. -/
@[expose]
def fractionalGagliardoSquareFunction (U : Set (Vec d)) (s : ℝ)
    (F : Vec d → Vec d) (x : Vec d) : ℝ≥0∞ :=
  ∫⁻ y in U, ENNReal.ofReal
    (vecNormSq (F x - F y) /
      euclideanDist x y ^ ((d : ℝ) + 2 * s)) ∂volume

/-- The square root of the pointwise fractional energy. -/
@[expose]
def fractionalGagliardoAmplitude (U : Set (Vec d)) (s : ℝ)
    (F : Vec d → Vec d) (x : Vec d) : ℝ≥0∞ :=
  fractionalGagliardoSquareFunction U s F x ^ (1 / 2 : ℝ)

private theorem measurable_fractionalGagliardoKernel
    {s : ℝ} {F : Vec d → Vec d} (hF : Measurable F) :
    Measurable (fun z : Vec d × Vec d => ENNReal.ofReal
      (vecNormSq (F z.1 - F z.2) /
        euclideanDist z.1 z.2 ^ ((d : ℝ) + 2 * s))) := by
  have hsub : Measurable (fun z : Vec d × Vec d => F z.1 - F z.2) :=
    (hF.comp measurable_fst).sub (hF.comp measurable_snd)
  have hnum : Measurable (fun z : Vec d × Vec d =>
      vecNormSq (F z.1 - F z.2)) :=
    continuous_vecNormSq.measurable.comp hsub
  have hdist : Measurable (fun z : Vec d × Vec d =>
      euclideanDist z.1 z.2) := by
    unfold euclideanDist euclideanNorm
    exact (continuous_vecNormSq.comp
      (continuous_fst.sub continuous_snd)).sqrt.measurable
  exact (hnum.div ((hdist.pow measurable_const))).ennreal_ofReal

theorem measurable_fractionalGagliardoSquareFunction
    {U : Set (Vec d)} {s : ℝ}
    {F : Vec d → Vec d} (hF : Measurable F) :
    Measurable (fractionalGagliardoSquareFunction U s F) := by
  have hkernel := measurable_fractionalGagliardoKernel (d := d) (s := s) hF
  change Measurable fun x => ∫⁻ y, ENNReal.ofReal
    (vecNormSq (F x - F y) /
      euclideanDist x y ^ ((d : ℝ) + 2 * s)) ∂volume.restrict U
  exact hkernel.lintegral_prod_right'

theorem measurable_fractionalGagliardoAmplitude
    {U : Set (Vec d)} {s : ℝ}
    {F : Vec d → Vec d} (hF : Measurable F) :
    Measurable (fractionalGagliardoAmplitude U s F) := by
  exact (measurable_fractionalGagliardoSquareFunction hF).pow_const _

theorem fractionalGagliardoAmplitude_rpow_two
    (U : Set (Vec d)) (s : ℝ) (F : Vec d → Vec d) (x : Vec d) :
    fractionalGagliardoAmplitude U s F x ^ (2 : ℝ) =
      fractionalGagliardoSquareFunction U s F x := by
  unfold fractionalGagliardoAmplitude
  rw [← ENNReal.rpow_mul]
  norm_num

/-- The squared amplitude integrates to the raw regional fractional energy. -/
theorem setLIntegral_fractionalGagliardoAmplitude_rpow_two
    (U : Set (Vec d)) (s : ℝ) (F : Vec d → Vec d) :
    (∫⁻ x in U, fractionalGagliardoAmplitude U s F x ^ (2 : ℝ) ∂volume) =
      ∫⁻ x in U, ∫⁻ y in U, ENNReal.ofReal
        (vecNormSq (F x - F y) /
          euclideanDist x y ^ ((d : ℝ) + 2 * s)) ∂volume := by
  refine lintegral_congr fun x => ?_
  rw [fractionalGagliardoAmplitude_rpow_two]
  rfl

/-- On a positive finite-volume domain, the squared amplitude is the volume
times the normalized fractional seminorm. -/
theorem setLIntegral_fractionalGagliardoAmplitude_rpow_two_eq
    {U : Set (Vec d)} (hUpos : 0 < volume U) (hUtop : volume U ≠ ⊤)
    (s : ℝ) (F : Vec d → Vec d) :
    (∫⁻ x in U, fractionalGagliardoAmplitude U s F x ^ (2 : ℝ) ∂volume) =
      volume U * fracSeminormSq U s F := by
  rw [setLIntegral_fractionalGagliardoAmplitude_rpow_two]
  unfold fracSeminormSq eVolumeAverage euclideanDist euclideanNorm
  rw [ENNReal.mul_div_cancel hUpos.ne' hUtop]

end

end HighContrast
end HCPolySupport
