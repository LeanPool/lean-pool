/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.Prop42Tilt.CorrectedTiltAdapter
public import LeanPool.HighContrastHomogenization.Provider.Quenched.Prop42Scalar.CorrectedTiltTransfer

/-!
# High-contrast homogenization: Provider.Quenched.Prop42Tilt.CorrectedTiltConsumer

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Consumption by the corrected halfway transfer

The native additive adapter is put in the exact scalar shape consumed by the
corrected halfway-scale arithmetic.  The only remaining estimates are the
hatted tail and the numerical adapter-error bound.
-/

namespace HCPolySupport.HighContrast.Quenched

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-- At the single boundary scale where the corrected halfway index equals the
outer index, entry smallness supplies the scalar transfer directly.  Thus the
strict scale inequality required by the geometric adapter is needed only after
this base case. -/
theorem corrected_tilt_base_transfer [NeZero d]
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {g : ℝ} {E : BlockMat d} {Ψ : ℝ → ℝ} {K : ℝ}
    {S : CoeffSpace d → ℝ}
    (hstat : HCPoly.Frozen.IsStationaryLaw P)
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S)
    {l : ℤ} {q : Mat d} (hq : IsRoundedGrid l q) {n₀ : ℕ}
    (hfin : HasFiniteAdaptedMean P q
      (Prop42Scalar.correctedTiltScale n₀ (2 * n₀) : ℤ))
    {cStar A : ℝ} (hentry : annealedContrast P 0 - 1 ≤ cStar)
    (hcStarA : cStar ≤ A) :
    annealedContrast P ((2 * n₀ : ℕ) : ℤ) - 1 ≤
      (9 / 2 : ℝ) * ((d : ℝ) *
        (adaptedHattedContrast P q
          (Prop42Scalar.correctedTiltScale n₀ (2 * n₀) : ℤ) - 1)) +
        A * Real.rpow (3 : ℝ)
          (-(((2 * n₀ : ℕ) -
            Prop42Scalar.correctedTiltScale n₀ (2 * n₀) : ℕ) : ℝ)) := by
  have hscale : Prop42Scalar.correctedTiltScale n₀ (2 * n₀) = 2 * n₀ := by
    dsimp only [Prop42Scalar.correctedTiltScale]
    omega
  have hmono := annealedContrast_antitone hstat hdag (Nat.zero_le (2 * n₀))
  change annealedContrast P ((2 * n₀ : ℕ) : ℤ) ≤ annealedContrast P 0 at hmono
  have hF : annealedContrast P ((2 * n₀ : ℕ) : ℤ) - 1 ≤ cStar := by
    linarith only [hmono, hentry]
  have hhat1 := one_le_adaptedHattedContrast_of_rounded hq hfin
  have hx0 : 0 ≤ (d : ℝ) *
      (adaptedHattedContrast P q
        (Prop42Scalar.correctedTiltScale n₀ (2 * n₀) : ℤ) - 1) :=
    mul_nonneg (Nat.cast_nonneg d) (sub_nonneg.mpr hhat1)
  have hx0' : 0 ≤ (d : ℝ) *
      (adaptedHattedContrast P q ((2 * n₀ : ℕ) : ℤ) - 1) := by
    simpa only [hscale] using hx0
  rw [hscale]
  rw [Nat.sub_self, Nat.cast_zero, neg_zero]
  have hrpow : Real.rpow (3 : ℝ) 0 = 1 := Real.rpow_zero 3
  rw [hrpow, mul_one]
  linarith only [hF, hcStarA, hx0']

end

end HCPolySupport.HighContrast.Quenched
