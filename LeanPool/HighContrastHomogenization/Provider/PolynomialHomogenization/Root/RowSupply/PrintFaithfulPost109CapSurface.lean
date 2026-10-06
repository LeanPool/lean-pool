/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.RuledPairingAggregation
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.RowSupply.PrintDirectGradientResponsePrice

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.RowSupply.PrintFaithfulPost109CapSurface

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Print-faithful coarse-row cap surface

The localization proof uses two negative rows: the physical gradient and the
physical flux defect.  Its positive row belongs to the arbitrary dual test
field.  This interface therefore contains no fractional seminorm of a
constant-coefficient comparison extension.
-/

namespace HCPolySupport
namespace HighContrast
namespace RowSupply

open Book Book.Ch03 MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- The positive row in the printed pairing belongs to the dual test field.
It is independent of the response cap and of every comparison extension. -/
@[expose]
def PrintFaithfulPositiveTestRow
    {U : Set (Vec d)} {rho Rad : ℝ}
    (system : EnlargedMarginRuledTriadicWhitneySystem U rho Rad)
    (s : ℝ) (G : Vec d → Vec d) (hardyConstant : ℝ≥0∞) : Prop :=
  normalizedWhitneyRowEnergy system
      (ruledPositiveWhitneyCellEnergy system s G) ≤
    hardyConstant * hsNormSq U s G

/-- The domain duality step used after the printed flux-defect estimate.  This
is the exact comparison-extension occurrence on the printed route: it occurs
only on the left side, never through `hsNormSq U s h.grad`. -/
@[expose]
def PrintFaithfulDomainFluxDefectDuality
    (U : Set (Vec d)) (s : ℝ) (aPhysical : CoeffField d)
    (u h : H1Function U) (Cdual : ℝ) : Prop :=
  0 ≤ Cdual ∧
    negSobolevNorm U s (fun x ↦ u.grad x - h.grad x) +
        negSobolevNorm U s (fun x ↦
          matVecMul (aPhysical x) (u.grad x) - h.grad x) ≤
      ENNReal.ofReal Cdual *
        negSobolevNorm U s (fun x ↦
          matVecMul (aPhysical x - 1) (u.grad x))

/-- Generic printed pairing consumption for the physical full-dual row.  In
particular it applies to the physical flux-defect field without introducing a
comparison extension. -/
theorem ofReal_abs_globalPairing_le_printFaithfulFullDualCap [NeZero d]
    {U : Set (Vec d)} {rho Rad s : ℝ}
    (system : EnlargedMarginRuledTriadicWhitneySystem U rho Rad)
    (hd : 1 ≤ d) (hU : IsOpenBoundedConvexDomain U)
    (hUpos : 0 < volume U) (hUtop : volume U ≠ ⊤)
    (hs : 0 < s) (hsHalf : s < 1 / 2)
    (F : system.CellIndex → Vec d → Vec d) (G : Vec d → Vec d)
    (f : Vec d → ℝ) (hf : IntegrableOn f U volume)
    (hpair : ∀ i, volumeAverage (system.cell i) f =
      volumeAverage (system.cell i) (fun x ↦ vecDot (F i x) (G x)))
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict (system.cell i)))
    (hG : ∀ i, Integrable G (volume.restrict (system.cell i)))
    (hGfinite : ∀ i, hsNormSq (system.cell i) s G ≠ ⊤)
    {cap hardyConstant : ℝ≥0∞}
    (hcap : normalizedWhitneyRowEnergy system
      (physicalFullDualWhitneyFamilyCellEnergy system s F) ≤ cap)
    (hHardy : PrintFaithfulPositiveTestRow system s G hardyConstant) :
    ENNReal.ofReal |volumeAverage U f| ≤
      ((fractionalDualToBesovConstant d) ^ (2 : ℕ) * cap) ^
          (1 / 2 : ℝ) *
        (hardyConstant * hsNormSq U s G) ^ (1 / 2 : ℝ) := by
  have hbase :=
    ofReal_abs_volumeAverage_vecDot_le_fullDualWhitneyRow_mul_hs
      hd system hU hUpos hUtop hs hsHalf F G f hf hpair hF hG hGfinite
        hHardy
  have hnegative :
      (fractionalDualToBesovConstant d) ^ (2 : ℕ) *
          normalizedWhitneyRowEnergy system
            (physicalFullDualWhitneyFamilyCellEnergy system s F) ≤
        (fractionalDualToBesovConstant d) ^ (2 : ℕ) * cap :=
    mul_le_mul_right hcap _
  exact hbase.trans (mul_le_mul
    (ENNReal.rpow_le_rpow hnegative (by norm_num)) le_rfl bot_le bot_le)

end

end RowSupply
end HighContrast
end HCPolySupport
