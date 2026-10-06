/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastBootstrapIdentityGrid
public import LeanPool.HighContrastHomogenization.Provider.Quenched.Prop42Tilt.AdapterScalarization

/-!
# High-contrast homogenization: Provider.Quenched.SmallContrastBootstrapTilt

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The bootstrap tilt bridge

The tilt scalarization reads a one-sided Loewner adapter error against the
reference block as a multiplicative comparison of intrinsic contrasts.  The
bootstrap consumes it in the Euclidean direction: the adapted mean on the
selection grid at generation `n` is compared with the annealed block of a
centered cube at a strictly earlier scale `k`, the cube being presented as the
adapted cell of the Euclidean rounded grid.

Two scalar inputs enter: the absorbed adapter size `η = c·|𝐄 : 𝐀(□_k)|` and
the Euclidean hatted defect `x = d(hatΘ_k − 1)`.  The output is the same
degree-two polynomial the scalarization produces, evaluated at any upper
bounds for those two — the hatted carrier of the adapted mean sits below its
intrinsic contrast, so the polynomial bounds the hatted defect on the
selection grid as well.
-/

namespace HCPolySupport.HighContrast.Quenched

open Book.Ch02 MeasureTheory

open scoped Matrix MatrixOrder

noncomputable section

variable {d : ℕ}

/-- The bootstrap tilt polynomial `(1+σ)²(1 + (5/4)x + (1/4)x²) − 1`: the
scalarized adapter comparison at absorbed size `σ` and Euclidean hatted defect
`x`. -/
@[expose]
def bootstrapTiltPolynomial (sigma x : ℝ) : ℝ :=
  (1 + sigma) ^ 2 * (1 + (5 / 4 : ℝ) * x + (1 / 4 : ℝ) * x ^ 2) - 1

/-- The tilt polynomial is monotone in both arguments on the nonnegative
quadrant. -/
theorem bootstrapTiltPolynomial_le {s t x y : ℝ} (hs : 0 ≤ s) (hst : s ≤ t)
    (hx : 0 ≤ x) (hxy : x ≤ y) :
    bootstrapTiltPolynomial s x ≤ bootstrapTiltPolynomial t y := by
  have hsq : (1 + s) ^ 2 ≤ (1 + t) ^ 2 := by nlinarith only [hs, hst]
  have hquad : 1 + (5 / 4 : ℝ) * x + (1 / 4 : ℝ) * x ^ 2 ≤
      1 + (5 / 4 : ℝ) * y + (1 / 4 : ℝ) * y ^ 2 := by
    nlinarith only [hx, hxy]
  have hquad0 : (0 : ℝ) ≤ 1 + (5 / 4 : ℝ) * x + (1 / 4 : ℝ) * x ^ 2 := by
    nlinarith only [hx]
  have hmul := mul_le_mul hsq hquad hquad0 (sq_nonneg (1 + t))
  rw [bootstrapTiltPolynomial, bootstrapTiltPolynomial]
  linarith only [hmul]

/-- **The bootstrap tilt bridge.**  A one-sided adapter error against the
reference block, from the adapted mean at generation `n` down to the annealed
block of the centered cube at scale `k`, bounds the hatted defect of the
adapted mean by the tilt polynomial at any upper bounds `σ` for the absorbed
adapter size and `x` for the Euclidean hatted defect. -/
theorem adaptedHattedContrast_sub_one_le_of_euclidean_adapter [NeZero d]
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {E : BlockMat d} (hEsymm : IsSymmetricBlockMat E) (hEpos : BlockPosDef E)
    {lq : ℤ} {q : Mat d} (hq : IsRoundedGrid lq q) {k n : ℤ}
    (hfinq : HasFiniteAdaptedMean P q n)
    (hfin1 : HasFiniteAdaptedMean P (1 : Mat d) k)
    {c : ℝ} (hc : 0 ≤ c)
    (hsub : BlockMatLoewnerLE
      (blockSub (adaptedMean P q n) (annealedBlock P (centeredCube d k)))
      (blockScale c E))
    {sigma x : ℝ}
    (heta : c * blockSize E (adaptedMean P (1 : Mat d) k) ≤ sigma)
    (hx : (d : ℝ) * (adaptedHattedContrast P (1 : Mat d) k - 1) ≤ x) :
    (d : ℝ) * (adaptedHattedContrast P q n - 1) ≤
      (d : ℝ) * bootstrapTiltPolynomial sigma x := by
  classical
  let : Nonempty (Fin d) := ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne d)⟩⟩
  have hgrid1 : IsRoundedGrid ((kZero d : ℤ)) (1 : Mat d) :=
    isRoundedGrid_one le_rfl
  have hAsymm : IsSymmetricBlockMat (adaptedMean P q n) :=
    Recurrence.isSymmetricBlockMat_adaptedMean P q n
  have hApos : BlockPosDef (adaptedMean P q n) :=
    Recurrence.blockPosDef_adaptedMean_of_isRoundedGrid hq n hfinq
  have hsub' : BlockMatLoewnerLE
      (blockSub (adaptedMean P q n) (adaptedMean P (1 : Mat d) k))
      (blockScale c E) := by
    rw [adaptedMean_one]
    exact hsub
  have hpoly := blockContrast_sub_one_le_adaptedHatted_of_adapter
    hAsymm hApos hEsymm hEpos hgrid1 hfin1 hc hsub'
  dsimp only at hpoly
  -- the two scalar inputs are nonnegative
  have hsize0 : 0 ≤ blockSize E (adaptedMean P (1 : Mat d) k) :=
    PortableHistory.blockSize_nonneg hEsymm
      (Recurrence.isSymmetricBlockMat_adaptedMean P (1 : Mat d) k)
      (Recurrence.blockPosDef_adaptedMean_of_isRoundedGrid hgrid1 k hfin1)
  have heta0 : 0 ≤ c * blockSize E (adaptedMean P (1 : Mat d) k) :=
    mul_nonneg hc hsize0
  have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  have hx0 : 0 ≤ (d : ℝ) * (adaptedHattedContrast P (1 : Mat d) k - 1) :=
    mul_nonneg hd0
      (sub_nonneg.mpr (one_le_adaptedHattedContrast_of_rounded hgrid1 hfin1))
  -- monotonicity of the tilt polynomial in both scalar inputs
  have hmono := bootstrapTiltPolynomial_le heta0 heta hx0 hx
  simp only [bootstrapTiltPolynomial] at hmono
  -- the hatted carrier of the adapted mean sits below its intrinsic contrast
  have hhat : adaptedHattedContrast P q n ≤ blockContrast (adaptedMean P q n) :=
    hattedContrast_le_blockContrast hAsymm hApos
  have hchain : adaptedHattedContrast P q n - 1 ≤
      bootstrapTiltPolynomial sigma x := by
    rw [bootstrapTiltPolynomial]
    linarith only [hhat, hpoly, hmono]
  exact mul_le_mul_of_nonneg_left hchain hd0

end

end HCPolySupport.HighContrast.Quenched
