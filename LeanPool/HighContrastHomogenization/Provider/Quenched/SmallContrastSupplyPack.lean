/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastSupplyPorts
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastEntryRateMean
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastRealClauses
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastFusionStep
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastAnnealedEnvelope
public import LeanPool.HighContrastHomogenization.Provider.Response.PreYoungFixedGridCells
public import LeanPool.HighContrastHomogenization.Provider.Response.ProfileRowSchur
public import LeanPool.HighContrastHomogenization.Provider.Response.ProfileRowSkewCarriers
public import LeanPool.HighContrastHomogenization.Provider.Response.ProfileRowOscillationSum
public import LeanPool.HighContrastHomogenization.Provider.Response.DiagonalWeakNormAdjointAlgebra
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastRowAtCenters
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastWeakValue
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastCenteringCap
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastTerminalComparability
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastSingleCellVariance
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastMeanDropCarrier
public import LeanPool.HighContrastHomogenization.Provider.Quenched.FixedGridWindowAccount
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastAlignedGeometry
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastWeakCap
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastAdjointMirrors
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastAverageDrops
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastEntrySupply
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastEntryEnvelope
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastOneStepHub
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastAbsorptionChoice
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastEntryCapsIsotropy
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastHvarFamily
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastSlotValue
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastVarianceLagged
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastEntryRateParts

/-!
# High-contrast homogenization: Provider.Quenched.SmallContrastSupplyPack

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The account supply pack

The variance, mean and drop clauses of the isotropic-variance account core body,
at the families the one-step family
delivers and at the rate pack's window and depth.

The three source constants are **defined as their bounds**, so the clauses
that connect them to the entry slot are `le_rfl`:

```
vsum n  := slotVsumSharp d Csub Msc delta (rateDepth n)
vmsrc n := conv * slotSourceSeq d Csub Msc delta (rateDepth n) 0
bsrc n  := the bad expression at (badMomentMajorantScaled …) and rateWindow n
cVsum   := slotCVsum d          cVm := cVmConstant d conv
```

and the clauses that connect them to the *account* are's two producers,
applied one generation at a time.  Nothing here is an estimate; every line is a
re-indexing of a bound.
-/

namespace HCPolySupport.HighContrast.Quenched

open Book.Ch02 MeasureTheory

open scoped Matrix MatrixOrder Matrix.Norms.L2Operator

noncomputable section

/-! ## The variance slots -/

/-- `hVsum`: the weighted slot sum against the source constant and the base
coefficient, one generation at a time. -/
theorem supply_hVsum {d : ℕ} [NeZero d] (hd : 2 ≤ d) {Csub Msc delta : ℝ}
    (hCsub : 0 ≤ Csub) (hMsc : 0 ≤ Msc) (hdelta : 0 ≤ delta)
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {l : ℤ} {q : Mat d} (hgrid : IsRoundedGrid l q)
    (hfin : ∀ k : ℤ, HasFiniteAdaptedMean P q k) (N₀ : ℕ) (jb J Hw : ℕ → ℕ)
    (n : ℕ) :
    (∑ j ∈ Finset.range (Hw n + 1),
        (3 : ℝ) ^ (-(1 / 2 : ℝ) * (j : ℝ)) *
          (slotFamilyValue d Csub Msc delta
              (hatExcess P q N₀ (jb n)) (J n) j +
            slotFamilyValue d Csub Msc delta
              (hatExcess P q N₀ (jb n)) (J n) 0)) ≤
      slotVsumSharp d Csub Msc delta (J n) +
        slotCVsum d * hatExcess P q N₀ (jb n) :=
  hVsum_of_family_sharp hd hCsub hMsc hdelta
    (hatExcess_nonneg hgrid hfin N₀ (jb n)) (Hw n) (J n)

/-- `hVmeanle`: the mean slot against its own source constant, definitionally.
-/
theorem supply_hVmeanle {d : ℕ} {conv Csub Msc delta Fjb : ℝ} {J : ℕ}
    (hconv0 : 0 ≤ conv) :
    conv * slotFamilyValue d Csub Msc delta Fjb J 0 ≤
      conv * slotSourceSeq d Csub Msc delta J 0 + cVmConstant d conv * Fjb :=
  hVmeanle_of_slot_family hconv0 le_rfl

/-! ## The drop channel -/

/-- `hDrnn`, at the truncated family: nonnegative at **every** lag, which is
what `hrec_line_of_slots_isotropy_sharp_at_jb_at_level_src` demands. -/
theorem supply_hDrnn {d : ℕ} [NeZero d] (P : Measure (CoeffSpace d))
    [IsProbabilityMeasure P] (lAl : ℤ) {cF : ℝ} (hcF : 0 ≤ cF) (mAl : Mat d)
    {E F : BlockMat d} (hbS : 0 ≤ blockSize E F)
    (hstat : HCPoly.Frozen.IsStationaryLaw P)
    (hgrid : IsRoundedGrid lAl (roundedGrid lAl mAl))
    (hfin : ∀ k : ℤ, HasFiniteAdaptedMean P (roundedGrid lAl mAl) k)
    {N₀ : ℕ} (hlN : lAl ≤ (N₀ : ℤ)) (n j : ℕ) :
    0 ≤ meanDrop2ValueIsotropy P lAl cF mAl E F ((N₀ : ℤ) + (n : ℤ)) (min j n) :=
  meanDrop2ValueIsotropy_nonneg P lAl hcF mAl hbS
    (fun _ _ hpm => hatExcess_antitone hstat hgrid hfin hlN hpm) n (min j n)
    (Nat.min_le_right j n)

/-- `hDrdelta`, at the truncated family. -/
theorem supply_hDrdelta {d : ℕ} (P : Measure (CoeffSpace d)) (lAl : ℤ)
    (cF : ℝ) (mAl : Mat d) (E F : BlockMat d) {N₀ : ℕ} {delta0 delta : ℝ}
    (hFnn : ∀ m : ℕ, 0 ≤ hatExcess P (roundedGrid lAl mAl) N₀ m)
    (hfloor : ∀ m : ℕ, hatExcess P (roundedGrid lAl mAl) N₀ m ≤ delta0)
    (hdc0 : 0 ≤ dropConstantIsotropy cF E F)
    (hchoice : dropConstantIsotropy cF E F * delta0 ≤ delta)
    (n j : ℕ) :
    meanDrop2ValueIsotropy P lAl cF mAl E F ((N₀ : ℤ) + (n : ℤ)) (min j n) ≤ delta :=
  hDrdelta_of_floor_isotropy P lAl cF mAl E F hFnn hfloor hdc0 hchoice n (min j n)
    (Nat.min_le_right j n)

/-- `hDrdrop`, at the truncated family: the cap is the identity of, read at
the truncated lag. -/
theorem supply_hDrdrop {d : ℕ} [NeZero d] (P : Measure (CoeffSpace d))
    [IsProbabilityMeasure P] (lAl : ℤ) (cF : ℝ) (mAl : Mat d)
    (E F : BlockMat d) {N₀ : ℕ} {cD : ℝ}
    (hcD : dropConstantIsotropy cF E F ≤ cD)
    (hstat : HCPoly.Frozen.IsStationaryLaw P)
    (hgrid : IsRoundedGrid lAl (roundedGrid lAl mAl))
    (hfin : ∀ k : ℤ, HasFiniteAdaptedMean P (roundedGrid lAl mAl) k)
    (hlN : lAl ≤ (N₀ : ℤ)) (n j : ℕ) (hj : j ≤ n) :
    meanDrop2ValueIsotropy P lAl cF mAl E F ((N₀ : ℤ) + (n : ℤ)) (min j n) ≤
      cD * (hatExcess P (roundedGrid lAl mAl) N₀ (n - j) -
        hatExcess P (roundedGrid lAl mAl) N₀ n) := by
  have hmin : min j n = j := Nat.min_eq_left hj
  rw [hmin, meanDrop2ValueIsotropy_eq_dropConstantIsotropy_mul P lAl cF mAl E F N₀ n j hj]
  refine mul_le_mul_of_nonneg_right hcD ?_
  have := hatExcess_antitone hstat hgrid hfin hlN (Nat.sub_le n j)
  linarith only [this]

end

end HCPolySupport.HighContrast.Quenched
