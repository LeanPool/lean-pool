/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Response.PreYoungRecentDefectRows
public import LeanPool.HighContrastHomogenization.Provider.Response.PreYoungFixedGridComponentRows

/-!
# High-contrast homogenization: Provider.Response.PreYoungFixedGridRows

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Cutoff-mean rows, fixed grid

The cutoff-mean rows on a fixed rounded grid: the grid stays rounded at the fixed
alignment `l` while the generation window `{s, t}` moves, the aligned-cell
integrability coming from the `AlignedCellsIntegrable` carrier instead of the
window multiplier's carrier equality.  The proof is unchanged apart from the
window bundle replaced by the carrier.
-/

namespace HCPolySupport.HighContrast.Response.FixedGrid

open Book.Ch02 MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- The primal cutoff mean satisfies both component row estimates whenever the
profile weak quantity is finite. -/
theorem profile_primal_cutoff_mean_rows_le [NeZero d]
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    (hstat : HCPoly.Frozen.IsStationaryLaw P)
    {l : ℤ} {m0 q : Mat d} (hm0 : m0.PosDef)
    (hgrid : IsRoundedGrid l q)
    {s t : ℤ} (hls : l ≤ s) (H : ℕ) (ht : t = s + (H : ℤ))
    (hcells : AlignedCellsIntegrable P q s t)
    (hblocks : ∀ k : ℤ, l ≤ k → k ≤ t →
      HasFiniteAdaptedMean P q k ∧ BlockPosDef (adaptedMean P q k))
    (g : Mat d) (hg : IsSkewMat g) (p r : Vec d)
    (hweak : profilePrimalWeakQuantity P m0
      (Recurrence.posDef_of_isRoundedGrid hgrid) t
      (fun a ↦ a.subSkew g hg) p r ≠ ⊤) :
    let hq := Recurrence.posDef_of_isRoundedGrid hgrid
    let X := profilePrimalCenter P hq t (fun a ↦ a.subSkew g hg) p r
    let tau := profilePrimalResponseDefect P hq g hg s t p r
    let EJ := ∫ a, responseJ (adaptedDomain hq t)
      ((a.subSkew g hg).coeffOn (adaptedDomain hq t)) p r ∂P
    let gain := preYoungComponentCoefficient d *
      (3 : ℝ) ^ (-(H : ℝ)) * Real.sqrt EJ
    let cut := adaptedPreYoungCutoff q hq t
    ENNReal.ofReal
        |vecDot X.2 (profilePrimalCutoffMean P hq t
          (fun a ↦ a.subSkew g hg) cut p r).1| ≤
        ENNReal.ofReal (Real.sqrt (4 * tau) *
          profileSchurLoadFlux (profileHattedBlock g (adaptedMean P q s)) X.2) +
          ENNReal.ofReal gain *
            profilePrimalHattedEarlierRow P q g s X.1 X.2 ^ (1 / 2 : ℝ) ∧
      ENNReal.ofReal
        |vecDot X.1 (profilePrimalCutoffMean P hq t
          (fun a ↦ a.subSkew g hg) cut p r).2| ≤
        ENNReal.ofReal (Real.sqrt (4 * tau) *
          profileSchurLoadGradient (profileHattedBlock g (adaptedMean P q s)) X.1) +
          ENNReal.ofReal gain *
            profilePrimalHattedEarlierRow P q g s X.1 X.2 ^ (1 / 2 : ℝ) := by
  have hst : s ≤ t := by omega
  have hints := (hblocks s hls hst).1
  have hjt : l ≤ t := hls.trans hst
  have hintt := (hblocks t hjt le_rfl).1
  let hq := Recurrence.posDef_of_isRoundedGrid hgrid
  let X := profilePrimalCenter P hq t (fun a ↦ a.subSkew g hg) p r
  have hrecent := profile_primal_recent_defect_rows_le
    hstat hgrid hls hst hints hintt hm0 g hg p r X.1 X.2 hweak
  refine profile_primal_cutoff_mean_rows_le_of_recent_defect
    hstat hm0 hgrid hls H ht hcells hblocks g hg p r hweak ?_
  dsimp only at hrecent ⊢
  exact ⟨ENNReal.ofReal_le_ofReal hrecent.1,
    ENNReal.ofReal_le_ofReal hrecent.2⟩

/-- The adjoint cutoff mean satisfies both component row estimates whenever the
profile weak quantity is finite. -/
theorem profile_adjoint_cutoff_mean_rows_le [NeZero d]
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    (hstat : HCPoly.Frozen.IsStationaryLaw P)
    {l : ℤ} {m0 q : Mat d} (hm0 : m0.PosDef)
    (hgrid : IsRoundedGrid l q)
    {s t : ℤ} (hls : l ≤ s) (H : ℕ) (ht : t = s + (H : ℤ))
    (hcells : AlignedCellsIntegrable P q s t)
    (hblocks : ∀ k : ℤ, l ≤ k → k ≤ t →
      HasFiniteAdaptedMean P q k ∧ BlockPosDef (adaptedMean P q k))
    (g : Mat d) (hg : IsSkewMat g) (p r : Vec d)
    (hweak : profileAdjointWeakQuantity P m0
      (Recurrence.posDef_of_isRoundedGrid hgrid) t
      (fun a ↦ a.subSkew g hg) p r ≠ ⊤) :
    let hq := Recurrence.posDef_of_isRoundedGrid hgrid
    let X := profileAdjointCenter P hq t (fun a ↦ a.subSkew g hg) p r
    let tau := profileAdjointResponseDefect P hq g hg s t p r
    let EJ := ∫ a, responseJ (adaptedDomain hq t)
      ((a.subSkew g hg).transpose.coeffOn (adaptedDomain hq t)) p r ∂P
    let gain := preYoungComponentCoefficient d *
      (3 : ℝ) ^ (-(H : ℝ)) * Real.sqrt EJ
    let cut := adaptedPreYoungCutoff q hq t
    ENNReal.ofReal
        |vecDot X.2 (profileAdjointCutoffMean P hq t
          (fun a ↦ a.subSkew g hg) cut p r).1| ≤
        ENNReal.ofReal (Real.sqrt (4 * tau) *
          profileSchurLoadFlux (profileHattedAdjointBlock g (adaptedMean P q s)) X.2) +
          ENNReal.ofReal gain *
            profileAdjointHattedEarlierRow P q g s X.1 X.2 ^ (1 / 2 : ℝ) ∧
      ENNReal.ofReal
        |vecDot X.1 (profileAdjointCutoffMean P hq t
          (fun a ↦ a.subSkew g hg) cut p r).2| ≤
        ENNReal.ofReal (Real.sqrt (4 * tau) *
          profileSchurLoadGradient (profileHattedAdjointBlock g (adaptedMean P q s)) X.1) +
          ENNReal.ofReal gain *
            profileAdjointHattedEarlierRow P q g s X.1 X.2 ^ (1 / 2 : ℝ) := by
  have hst : s ≤ t := by omega
  have hints := (hblocks s hls hst).1
  have hjt : l ≤ t := hls.trans hst
  have hintt := (hblocks t hjt le_rfl).1
  let hq := Recurrence.posDef_of_isRoundedGrid hgrid
  let X := profileAdjointCenter P hq t (fun a ↦ a.subSkew g hg) p r
  have hrecent := profile_adjoint_recent_defect_rows_le
    hstat hgrid hls hst hints hintt hm0 g hg p r X.1 X.2 hweak
  refine profile_adjoint_cutoff_mean_rows_le_of_recent_defect
    hstat hm0 hgrid hls H ht hcells hblocks g hg p r hweak ?_
  dsimp only at hrecent ⊢
  exact ⟨ENNReal.ofReal_le_ofReal hrecent.1,
    ENNReal.ofReal_le_ofReal hrecent.2⟩

end

end HCPolySupport.HighContrast.Response.FixedGrid
