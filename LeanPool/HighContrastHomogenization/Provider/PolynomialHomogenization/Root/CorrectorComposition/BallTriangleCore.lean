/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Corrector.C1CoefficientEnergySeminorm
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Corrector.C1FixedProjectionIncrement
public import LeanPool.HighContrastHomogenization.Provider.Regularity.CorrectorWeightedGradientBridge

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.CorrectorComposition.BallTriangleCore

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Minkowski for the volume-normalized weighted norm, on an arbitrary domain

`weightedGradNorm b V F = ‖s(b)^{1/2} F‖_{L_underlined²(V)}` is built on `∫⁻`, Mathlib's
**lower** Lebesgue integral, so the triangle inequality is **false** for
arbitrary `F, G`: for a Bernstein set `S` the pair `F = 1_S • v`,
`G = -1_{Sᶜ} • v` has both norms `0` while `F - G = v`.  It is true, and is
proved here, for **square-integrable** fields, where the norm is the genuine
seminorm of the positive symmetric coefficient form on `HilbertVectorL2 V`.

Three steps.

* `ofReal_sqrt_normalizedLocalSymmetricEnergy_eq_weightedGradNorm` identifies
  `ENNReal.ofReal (√ E(F))` with `weightedGradNorm b V F` on an `L²` witness.
  It is the square root of the `ofReal_normalizedLocalSymmetricEnergy_eq_weightedGradNorm_sq`,
  taken in
  `ℝ≥0∞` through the injectivity of squaring.
* `weightedGradNorm_sub_le_add_of_memVectorL2` is then Minkowski for the
  positive form (`sqrt_normalizedLocalSymmetricEnergy_add_le`, stated for an
  **arbitrary** `U : Set (Vec d)`), applied to `F` and `-G` and transported
  through the class identity for a difference.
* `weightedGradNorm_sub_le_add_of_aeElliptic` removes the pointwise
  `IsEllipticFieldOn` hypothesis: a field of the coefficient class is elliptic
  only *almost* everywhere on the bounded measurable set carrying the norm, with
  that set's constants, so the estimate is transported along
  `weightedGradNorm_congr_coeff_ae_on` from the pointwise-good representative
  that fills the exceptional set with `lam • I` — the construction of
  `Internal.Ch02.BookCh02.pointwiseCoeffField`, redone here for an arbitrary
  measurable set rather than for a `Domain`.

The degenerate case `volume V = 0` needs no hypothesis at all: the lower
integral over a null set vanishes and `0 / 0 = 0` in `ℝ≥0∞`, so every weighted
norm is `0` there.
-/

namespace HCPolySupport
namespace HighContrast
namespace CorrectorComposition

open MeasureTheory Set
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## The degenerate domain -/

/-- On a null domain every weighted norm vanishes: the restricted measure is
zero, so the lower integral is `0`, and `0 / 0 = 0` in `ℝ≥0∞`. -/
theorem weightedGradNorm_of_volume_eq_zero {U : Set (Vec d)} (hU : volume U = 0)
    (b : CoeffField d) (F : Vec d → Vec d) :
    weightedGradNorm b U F = 0 := by
  have hz : (∫⁻ x in U,
      ENNReal.ofReal (vecDot (F x) (matVecMul (symmPart (b x)) (F x))) ∂volume)
      = 0 := by
    rw [Measure.restrict_eq_zero.2 hU, lintegral_zero_measure]
  unfold weightedGradNorm eVolumeAverage
  rw [hz, ENNReal.zero_div, ENNReal.zero_rpow_of_pos (by norm_num)]

/-! ## The square-root bridge -/

private theorem ennreal_sq_rpow_half (x : ℝ≥0∞) : (x ^ 2) ^ (1 / 2 : ℝ) = x := by
  rw [← ENNReal.rpow_natCast x 2, ← ENNReal.rpow_mul]
  norm_num

private theorem ennreal_eq_of_sq_eq {x y : ℝ≥0∞} (h : x ^ 2 = y ^ 2) : x = y := by
  rw [← ennreal_sq_rpow_half x, ← ennreal_sq_rpow_half y, h]

/-- The `ℝ≥0∞` weighted norm of a square-integrable field is the square root of
its normalized symmetric class energy. -/
theorem ofReal_sqrt_normalizedLocalSymmetricEnergy_eq_weightedGradNorm
    {U : Set (Vec d)} {b : CoeffField d} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam U b)
    {f : Vec d → Vec d} (hf : MemVectorL2 U f) :
    ENNReal.ofReal
        (Real.sqrt (normalizedLocalSymmetricEnergy hEll
          (toHilbertVectorL2OfVecField hf))) =
      weightedGradNorm b U f := by
  refine ennreal_eq_of_sq_eq ?_
  rw [← ofReal_normalizedLocalSymmetricEnergy_eq_weightedGradNorm_sq hEll hf, sq,
    ← ENNReal.ofReal_mul (Real.sqrt_nonneg _),
    Real.mul_self_sqrt (normalizedLocalSymmetricEnergy_nonneg hEll _)]

/-! ## The class identity for a difference -/

private theorem coeFn_toHilbertVectorL2OfVecField {U : Set (Vec d)}
    {f : Vec d → Vec d} (hf : MemVectorL2 U f) :
    toHilbertVectorL2OfVecField hf =ᵐ[volumeMeasureOn U] hilbertifyVecField f :=
  coeFn_toHilbertVectorL2 (memHilbertVectorL2_hilbertifyVecField hf)

private theorem toHilbertVectorL2OfVecField_sub {U : Set (Vec d)}
    {F G : Vec d → Vec d} (hF : MemVectorL2 U F) (hG : MemVectorL2 U G)
    (hFG : MemVectorL2 U fun x ↦ F x - G x) :
    toHilbertVectorL2OfVecField hFG =
      toHilbertVectorL2OfVecField hF - toHilbertVectorL2OfVecField hG := by
  apply MeasureTheory.Lp.ext
  filter_upwards [coeFn_toHilbertVectorL2OfVecField hFG,
    coeFn_toHilbertVectorL2OfVecField hF,
    coeFn_toHilbertVectorL2OfVecField hG,
    MeasureTheory.Lp.coeFn_sub (toHilbertVectorL2OfVecField hF)
      (toHilbertVectorL2OfVecField hG)] with x hxFG hxF hxG hsub
  rw [hxFG, hsub, Pi.sub_apply, hxF, hxG]
  change WithLp.toLp 2 (F x - G x) = WithLp.toLp 2 (F x) - WithLp.toLp 2 (G x)
  rw [← WithLp.toLp_sub]

/-! ## Minkowski, for a pointwise elliptic coefficient -/

/-- **The triangle inequality for `‖s^{1/2} ·‖_{L_underlined²(U)}`**, on two
square-integrable fields.  The membership hypotheses are not removable (`∫⁻`
is the lower integral). -/
theorem weightedGradNorm_sub_le_add_of_memVectorL2
    {U : Set (Vec d)} {b : CoeffField d} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam U b)
    (hvol : 0 < volume U) (hvoltop : volume U ≠ ⊤)
    {F G : Vec d → Vec d} (hF : MemVectorL2 U F) (hG : MemVectorL2 U G) :
    weightedGradNorm b U (fun x ↦ F x - G x) ≤
      weightedGradNorm b U F + weightedGradNorm b U G := by
  have hFG : MemVectorL2 U fun x ↦ F x - G x := hF.sub hG
  have hclass := toHilbertVectorL2OfVecField_sub hF hG hFG
  have htri := sqrt_normalizedLocalSymmetricEnergy_add_le hEll hvol hvoltop
    (toHilbertVectorL2OfVecField hF) (-(toHilbertVectorL2OfVecField hG))
  rw [Root.normalizedLocalSymmetricEnergy_neg_increment hEll,
    ← sub_eq_add_neg, ← hclass] at htri
  rw [← ofReal_sqrt_normalizedLocalSymmetricEnergy_eq_weightedGradNorm hEll hFG,
    ← ofReal_sqrt_normalizedLocalSymmetricEnergy_eq_weightedGradNorm hEll hF,
    ← ofReal_sqrt_normalizedLocalSymmetricEnergy_eq_weightedGradNorm hEll hG,
    ← ENNReal.ofReal_add (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)]
  exact ENNReal.ofReal_le_ofReal htri

/-! ## The pointwise-good representative on an arbitrary measurable set -/

/-- A strongly measurable field elliptic almost everywhere on a measurable set,
with that set's constants, has a pointwise elliptic representative there,
agreeing with it almost everywhere on the set: fill the exceptional set with
`lam • I`. -/
theorem exists_isEllipticFieldOn_ae_eq {b0 : CoeffField d} {lam Lam : ℝ}
    (hlam : 0 < lam) (hle : lam ≤ Lam) (hb0 : StronglyMeasurable b0)
    {U : Set (Vec d)} (hU : MeasurableSet U)
    (hell : ∀ᵐ x ∂volume.restrict U, IsEllipticMatrix lam Lam (b0 x)) :
    ∃ b' : CoeffField d, IsEllipticFieldOn lam Lam U b' ∧
      b' =ᵐ[volume.restrict U] b0 := by
  classical
  obtain ⟨E, hEae, hEmeas, hEell⟩ := hell.exists_measurable_mem
  refine ⟨fun x ↦ if x ∈ E then b0 x else lam • (1 : Mat d), ⟨?_, ?_⟩, ?_⟩
  · refine measurable_pi_iff.2 fun i ↦ measurable_pi_iff.2 fun j ↦ ?_
    have hb0ij : Measurable fun x : Vec d ↦ b0 x i j :=
      ((continuous_id.matrix_elem i j).comp_stronglyMeasurable hb0).measurable
    have hite : Measurable fun x : Vec d ↦
        if x ∈ E then b0 x i j else (lam • (1 : Mat d)) i j :=
      Measurable.ite (by simpa using hEmeas) hb0ij measurable_const
    have hinner : Measurable fun x : Vec d ↦
        (if x ∈ E then b0 x else lam • (1 : Mat d)) i j := by
      convert hite using 1
      funext x
      by_cases hx : x ∈ E <;> simp [hx]
    exact Measurable.ite (by simpa using hU) hinner measurable_const
  · intro x _
    by_cases hx : x ∈ E
    · simpa only [ite_eq_left hx] using hEell x hx
    · simpa only [ite_eq_right hx] using
        Internal.Ch02.BookCh02.isEllipticMatrix_smul_one (d := d) hlam hle
  · filter_upwards [hEae] with x hxE
    simp only [ite_eq_left hxE]

/-! ## Minkowski, for an almost-everywhere elliptic coefficient -/

/-- **The triangle inequality on a measurable set of finite volume**, for a
coefficient field elliptic only almost everywhere on that set, with that set's
constants — the situation of every field of the coefficient class. -/
theorem weightedGradNorm_sub_le_add_of_aeElliptic
    {U : Set (Vec d)} (hU : MeasurableSet U) (hvoltop : volume U ≠ ⊤)
    {b b0 : CoeffField d} {lam Lam : ℝ} (hlam : 0 < lam) (hle : lam ≤ Lam)
    (hb0 : StronglyMeasurable b0) (hb0ae : b0 =ᵐ[volume] b)
    (hell : ∀ᵐ x ∂volume.restrict U, IsEllipticMatrix lam Lam (b0 x))
    {F G : Vec d → Vec d} (hF : MemVectorL2 U F) (hG : MemVectorL2 U G) :
    weightedGradNorm b U (fun x ↦ F x - G x) ≤
      weightedGradNorm b U F + weightedGradNorm b U G := by
  rcases eq_or_lt_of_le (zero_le : (0 : ENNReal) ≤ volume U) with hvol | hvol
  · simp [weightedGradNorm_of_volume_eq_zero hvol.symm]
  obtain ⟨b', hb'ell, hb'ae⟩ := exists_isEllipticFieldOn_ae_eq hlam hle hb0 hU hell
  have hae : b' =ᵐ[volume.restrict U] b :=
    hb'ae.trans (ae_restrict_of_ae hb0ae)
  have hcongr : ∀ H : Vec d → Vec d,
      weightedGradNorm b U H = weightedGradNorm b' U H := fun H ↦
    (weightedGradNorm_congr_coeff_ae_on H hae).symm
  simp only [hcongr]
  exact weightedGradNorm_sub_le_add_of_memVectorL2 hb'ell hvol hvoltop hF hG

end

end CorrectorComposition
end HighContrast
end HCPolySupport
