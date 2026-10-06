/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.Prop42Scalar.CorrectedTiltTransfer
public import LeanPool.HighContrastHomogenization.Provider.Quenched.Prop42Tilt.AdaptedHatIntrinsic
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastHattedCarrier
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastRecursionShape

/-!
# High-contrast homogenization: Provider.Quenched.SmallContrastHatDecay

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The hatted decay `hhat`

The drive-through from the drop-history recursion to the exact input the
corrected tilt transfer consumes.

The iteration decay is stated for an abstract nonincreasing sequence.
Here it is instantiated at

  `F j := d · (hatΘ^q_{N₀ + j} − 1)`,

whose two structural hypotheses are theorems of the construction
(`one_le_adaptedHattedContrast_of_rounded` for nonnegativity,
`adaptedHattedContrast_le` for monotonicity), and the conclusion is turned
into the literal `hhat` clause of the corrected tilt transfer, at the corrected
intermediate scale `correctedTiltScale n₀ m = ⌊m/2⌋ + n₀` of the midpoint-scale identity, taken at
`n₀ := N₀`.

The rate `κ = α/(320A)` and the prefactor `B = (12(α+10A)/α)·δ` are the
iteration lemma's own; the passage `n ↦ correctedTiltScale N₀ m` costs
nothing because `⌊m/2⌋ ≥ correctedTiltScale N₀ m − 2N₀` — the parity defect
is absorbed on the *exponent* side, not in the prefactor.
-/

namespace HCPolySupport.HighContrast.Quenched

open Book.Ch02 MeasureTheory

open scoped Matrix MatrixOrder Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-- The hatted excess sequence based at a generation `N₀`. -/
@[expose]
def hatExcess (P : Measure (CoeffSpace d)) (q : Mat d) (N₀ : ℕ) (j : ℕ) : ℝ :=
  (d : ℝ) * (adaptedHattedContrast P q ((N₀ : ℤ) + (j : ℤ)) - 1)

/-- The hatted excess sequence is nonnegative. -/
theorem hatExcess_nonneg [NeZero d]
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {l : ℤ} {q : Mat d} (hgrid : IsRoundedGrid l q)
    (hfin : ∀ k : ℤ, HasFiniteAdaptedMean P q k) (N₀ j : ℕ) :
    0 ≤ hatExcess P q N₀ j := by
  have h := one_le_adaptedHattedContrast_of_rounded hgrid (hfin ((N₀ : ℤ) + (j : ℤ)))
  have hd : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  exact mul_nonneg hd (by linarith only [h])

/-- The hatted excess sequence is nonincreasing. -/
theorem hatExcess_antitone [NeZero d]
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    (hstat : HCPoly.Frozen.IsStationaryLaw P)
    {l : ℤ} {q : Mat d} (hgrid : IsRoundedGrid l q)
    (hfin : ∀ k : ℤ, HasFiniteAdaptedMean P q k)
    {N₀ : ℕ} (hlN : l ≤ (N₀ : ℤ)) {p j : ℕ} (hpj : p ≤ j) :
    hatExcess P q N₀ j ≤ hatExcess P q N₀ p := by
  have hle : adaptedHattedContrast P q ((N₀ : ℤ) + (j : ℤ)) ≤
      adaptedHattedContrast P q ((N₀ : ℤ) + (p : ℤ)) := by
    refine adaptedHattedContrast_le hstat hgrid ?_ ?_
      (hfin ((N₀ : ℤ) + (p : ℤ))) (hfin ((N₀ : ℤ) + (j : ℤ)))
    · have : (0 : ℤ) ≤ (p : ℤ) := Int.natCast_nonneg p
      omega
    · have hz : (p : ℤ) ≤ (j : ℤ) := Int.ofNat_le.mpr hpj
      omega
  have hd : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  exact mul_le_mul_of_nonneg_left (by linarith only [hle]) hd

end

end HCPolySupport.HighContrast.Quenched
