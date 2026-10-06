/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Support.Book.Ch05.Theorems.Section53.JUpperBoundWeakNorms.Product.Bound

/-!
# High-contrast homogenization: Provider.Response.DivCurlWeakNormTerm

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The div-curl weak-norm term on a reference triadic cube

The cutoff-product term of the centered response split is the quantity the
manuscript controls by a quantitative div-curl argument: testing the equation
for the maximizer with the cutoff multiple of the potential defect and
integrating by parts turns the product into a pairing of the potential
fluctuation against the flux defect, and Besov duality bounds that pairing by
the product of the two negative-order weak seminorms.

The estimate is recorded here for an arbitrary Chapter 2 coefficient on the
reference cube domain, with the two weak seminorm bounds as data.  This is the
carrier on which the manuscript states the estimate; an adapted geometry is
reached from it by a change of variables.
-/

namespace HCPolySupport.HighContrast.Response

open Book.Ch05.Section53.JUpperBoundWeakNorms
open MeasureTheory

open scoped ENNReal

noncomputable section

/-- **The div-curl weak-norm term** for a Chapter 2 coefficient on the
reference cube: the cutoff-product term of the centered response split is
bounded by the product of the scaled gradient-defect and flux-defect weak
seminorms, with the coefficient carried by the cutoff's gradient field.

The gradient exponent `s` and the flux exponent `t` are only required to satisfy
`0 < s < 1` and `s + t ≤ 1`; the manuscript's own reading is the symmetric one
`s = t = 1/2`. -/
theorem abs_cutoffProductTermOnCube_le_scaledWeakNormProduct
    {d : ℕ} [NeZero d] (Q : TriadicCube d) {s t : ℝ}
    (hs_pos : 0 < s) (hs_lt_one : s < 1) (hst : s + t ≤ 1)
    (a : Book.Ch02.CoeffOn (Book.Ch02.cubeDomain Q))
    {φ : Vec d → ℝ} (p q p0 q0 : Vec d) {B gradWeak fluxWeak : ℝ}
    (hB : 0 ≤ B)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφ_compact : HasCompactSupport φ)
    (hφ_sub : tsupport φ ⊆ openCubeSet Q)
    (hcutoffGradient :
      MemLp (scalarCutoffGradientField φ) ∞ (normalizedCubeMeasure Q))
    (hcutoffSmooth :
      ∀ i : Fin d, ContDiff ℝ (⊤ : ℕ∞)
        (fun x => scalarCutoffGradientField φ x i))
    (hcutoffDeriv :
      ∀ i : Fin d, ∀ z ∈ cubeSet Q,
        ‖fderiv ℝ (fun x => scalarCutoffGradientField φ x i) z‖ ≤ B)
    (hgradWeak :
      ∀ N : ℕ,
        cubeBesovNegativeVectorPartialSeminorm Q s N
          (canonicalMaximizerGradientDefectOnCube Q a p q p0) ≤ gradWeak)
    (hfluxWeak :
      ∀ N : ℕ,
        cubeBesovNegativeVectorPartialSeminorm Q t N
          (canonicalMaximizerFluxDefectOnCube Q a p q q0) ≤ fluxWeak) :
    |cutoffProductTermOnCube Q a φ p q p0 q0| ≤
      cutoffProductScaledWeakNormCoeff Q s t B (scalarCutoffGradientField φ) *
        ((cubeBesovScaleWeight (-s) Q * gradWeak) *
          (cubeBesovScaleWeight (-t) Q * fluxWeak)) := by
  classical
  let u : H1Function (openCubeSet Q) :=
    canonicalMaximizerPotentialDefectH1OnCube Q a p q p0
  let flux : Vec d → Vec d := canonicalMaximizerFluxDefectOnCube Q a p q q0
  let ξ : Vec d → Vec d := scalarCutoffGradientField φ
  let A : ℝ :=
    cubeAverage Q
      (fun x => vecDot (flux x)
        (((u x - cubeAverage Q (fun y => u y)) • ξ x : Vec d)))
  have hid : cutoffProductTermOnCube Q a φ p q p0 q0 = -(1 / 2 : ℝ) * A := by
    have hraw :=
      cutoffProduct_eq_neg_half_cubeMean_centeredFluxDefect_smul_cutoffGradient
        (Q := Q) (a := a) (φ := φ) p q p0 q0
        hφ hφ_compact hφ_sub hcutoffGradient
    simpa [A, u, flux, ξ] using hraw
  have hhalf :
      |cutoffProductTermOnCube Q a φ p q p0 q0| ≤ |A| := by
    rw [hid, abs_mul]
    have habs : |-(1 / 2 : ℝ)| = (1 / 2 : ℝ) := by norm_num
    rw [habs]
    have hA : 0 ≤ |A| := abs_nonneg A
    linarith only [hA]
  have hmain :
      |A| ≤
        cutoffProductScaledWeakNormCoeff Q s t B (scalarCutoffGradientField φ) *
          ((cubeBesovScaleWeight (-s) Q * gradWeak) *
            (cubeBesovScaleWeight (-t) Q * fluxWeak)) := by
    simpa [A, u, flux, ξ, cutoffProductScaledWeakNormCoeff,
      canonicalMaximizerPotentialDefectH1OnCube_grad,
      canonicalMaximizerGradientDefectOnCube] using
      abs_cubeAverage_vecDot_centered_scalar_cutoff_le_scaledWeakNormProduct
        (Q := Q) (s := s) (t := t) hs_pos hs_lt_one hst
        (flux := flux) (u := u) (ξ := ξ) (B := B)
        (gradWeak := gradWeak) (fluxWeak := fluxWeak)
        hB hcutoffGradient hcutoffSmooth hcutoffDeriv
        (by simpa [flux] using canonicalMaximizerFluxDefectOnCube_memLp Q a p q q0)
        (by
          intro N
          have h := hgradWeak N
          change cubeBesovNegativeVectorPartialSeminorm Q s N
            (fun x => canonicalMaximizerGradientOnCube Q a p q x - p0) ≤
              gradWeak at h
          simpa only [u, canonicalMaximizerPotentialDefectH1OnCube_grad,
            canonicalMaximizerGradientDefectOnCube] using h)
        (by
          intro N
          simpa [flux] using hfluxWeak N)
  exact hhalf.trans hmain

/-- The div-curl coefficient at the symmetric exponents, for a cutoff whose
gradient field has sup norm at most `Bone` and derivative at most `B`.  The
first factor is the manuscript's scale gain: on a cube of side `3^n` a cutoff
with `‖∇φ‖ ≲ 3^{-n}` and `‖∇²φ‖ ≲ 3^{-2n}` makes it `O(3^{-n})`. -/
@[expose]
def divCurlWeakNormCoeff {d : ℕ} [NeZero d] (Q : TriadicCube d) (B Bone : ℝ) : ℝ :=
  (3 * (cubeScaleFactor Q * B + Bone) *
      ((Book.Ch01.Legacy.fullVectorPoincareConstant Q *
        (3 : ℝ) ^ ((d : ℝ) + 1)) * (d : ℝ))) *
    ((d : ℝ) * (3 : ℝ) ^ ((d : ℝ) + (1 / 2 : ℝ)))

/-- The defining equation of the div-curl coefficient. -/
theorem divCurlWeakNormCoeff_eq {d : ℕ} [NeZero d] (Q : TriadicCube d)
    (B Bone : ℝ) :
    divCurlWeakNormCoeff Q B Bone =
      (3 * (cubeScaleFactor Q * B + Bone) *
          ((Book.Ch01.Legacy.fullVectorPoincareConstant Q *
            (3 : ℝ) ^ ((d : ℝ) + 1)) * (d : ℝ))) *
        ((d : ℝ) * (3 : ℝ) ^ ((d : ℝ) + (1 / 2 : ℝ))) := rfl

/-- **The div-curl weak-norm term at the manuscript's exponents.**  Both weak
seminorms are read at order `-1/2`, and the cutoff enters only through the sup
norm `Bone` of its gradient field and the bound `B` on that field's
derivative. -/
theorem abs_cutoffProductTermOnCube_le_divCurlWeakNormCoeff
    {d : ℕ} [NeZero d] (Q : TriadicCube d)
    (a : Book.Ch02.CoeffOn (Book.Ch02.cubeDomain Q))
    {φ : Vec d → ℝ} (p q p0 q0 : Vec d) {B Bone gradWeak fluxWeak : ℝ}
    (hB : 0 ≤ B)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφ_compact : HasCompactSupport φ)
    (hφ_sub : tsupport φ ⊆ openCubeSet Q)
    (hcutoffGradient :
      MemLp (scalarCutoffGradientField φ) ∞ (normalizedCubeMeasure Q))
    (hcutoffSmooth :
      ∀ i : Fin d, ContDiff ℝ (⊤ : ℕ∞)
        (fun x => scalarCutoffGradientField φ x i))
    (hcutoffDeriv :
      ∀ i : Fin d, ∀ z ∈ cubeSet Q,
        ‖fderiv ℝ (fun x => scalarCutoffGradientField φ x i) z‖ ≤ B)
    (hBone : cubeLpNorm Q ∞ (scalarCutoffGradientField φ) ≤ Bone)
    (hgradWeak :
      ∀ N : ℕ,
        cubeBesovNegativeVectorPartialSeminorm Q (1 / 2) N
          (canonicalMaximizerGradientDefectOnCube Q a p q p0) ≤ gradWeak)
    (hfluxWeak :
      ∀ N : ℕ,
        cubeBesovNegativeVectorPartialSeminorm Q (1 / 2) N
          (canonicalMaximizerFluxDefectOnCube Q a p q q0) ≤ fluxWeak) :
    |cutoffProductTermOnCube Q a φ p q p0 q0| ≤
      divCurlWeakNormCoeff Q B Bone *
        ((cubeBesovScaleWeight (-(1 / 2 : ℝ)) Q * gradWeak) *
          (cubeBesovScaleWeight (-(1 / 2 : ℝ)) Q * fluxWeak)) := by
  have hmain :=
    abs_cutoffProductTermOnCube_le_scaledWeakNormProduct (Q := Q)
      (s := (1 / 2 : ℝ)) (t := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
      (by norm_num) a p q p0 q0 hB hφ hφ_compact hφ_sub hcutoffGradient
      hcutoffSmooth hcutoffDeriv hgradWeak hfluxWeak
  have hgradWeak_nonneg : 0 ≤ gradWeak :=
    (cubeBesovNegativeVectorPartialSeminorm_nonneg Q (1 / 2) 0
      (canonicalMaximizerGradientDefectOnCube Q a p q p0)).trans (hgradWeak 0)
  have hfluxWeak_nonneg : 0 ≤ fluxWeak :=
    (cubeBesovNegativeVectorPartialSeminorm_nonneg Q (1 / 2) 0
      (canonicalMaximizerFluxDefectOnCube Q a p q q0)).trans (hfluxWeak 0)
  have hprod_nonneg :
      0 ≤ (cubeBesovScaleWeight (-(1 / 2 : ℝ)) Q * gradWeak) *
        (cubeBesovScaleWeight (-(1 / 2 : ℝ)) Q * fluxWeak) :=
    mul_nonneg
      (mul_nonneg (cubeBesovScaleWeight_nonneg _ Q) hgradWeak_nonneg)
      (mul_nonneg (cubeBesovScaleWeight_nonneg _ Q) hfluxWeak_nonneg)
  refine hmain.trans (mul_le_mul_of_nonneg_right ?_ hprod_nonneg)
  have hzero : cubeBesovScaleWeight (-((1 / 2 : ℝ) - (1 / 2 : ℝ))) Q = 1 := by
    norm_num [cubeBesovScaleWeight]
  have hfront :
      2 * cubeScaleFactor Q * B +
          3 * cubeLpNorm Q ∞ (scalarCutoffGradientField φ) ≤
        3 * (cubeScaleFactor Q * B + Bone) := by
    have hcf : 0 ≤ cubeScaleFactor Q * B :=
      mul_nonneg (cubeScaleFactor_nonneg Q) hB
    linarith only [hcf, hBone]
  have hpoincare :
      0 ≤ (Book.Ch01.Legacy.fullVectorPoincareConstant Q *
        (3 : ℝ) ^ ((d : ℝ) + 1)) * (d : ℝ) :=
    mul_nonneg
      (mul_nonneg (Book.Ch01.Legacy.fullVectorPoincareConstant_nonneg Q)
        (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _))
      (Nat.cast_nonneg d)
  have hlast :
      0 ≤ (d : ℝ) * (3 : ℝ) ^ ((d : ℝ) + (1 / 2 : ℝ)) :=
    mul_nonneg (Nat.cast_nonneg d)
      (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _)
  have hsub : (1 : ℝ) - 1 / 2 = 1 / 2 := by norm_num
  simp only [cutoffProductScaledWeakNormCoeff, divCurlWeakNormCoeff,
    Fintype.card_fin, hzero, hsub, mul_one]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hfront hpoincare) hlast

end

end HCPolySupport.HighContrast.Response
