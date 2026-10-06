/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastMeanDilation
public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastProfileDefectCap

/-!
# High-contrast homogenization: Provider.Quenched.SmallContrastDefectComposition

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The calibrated profile defects from the hatted drop alone

Composing the fine-to-coarse mean dilation with the profile-defect cap
removes the dilation hypothesis: on one fixed rounded grid, a small
hatted-carrier drop and terminal intrinsic smallness bound both canonical
calibrated profile defects by `16 d` times the drop.  This is the mechanical
composition of `adaptedMean_le_hattedContrast_dilation` with
`calibratedProfileDefects_le_of_hattedMeanDilation` at `j = s`, `p = t`.
-/

namespace HCPolySupport.HighContrast.Quenched

open Book.Ch02 MeasureTheory

open scoped Matrix MatrixOrder Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-- **The two canonical profile defects are controlled by the hatted drop.**
On one fixed rounded grid, if the hatted drop from `s` to `t` is perturbatively
small and the terminal intrinsic contrast is small, then both calibrated
profile defects at the Schur representation of the terminal adapted mean are
at most `16 d` times the hatted drop. -/
theorem calibratedProfileDefects_le_of_smallDrop
    [NeZero d] {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    (hstat : HCPoly.Frozen.IsStationaryLaw P)
    {l : ℤ} {qGrid : Mat d} (hgrid : IsRoundedGrid l qGrid)
    {s t : ℤ} (hls : l ≤ s) (hst : s ≤ t)
    (hfins : HasFiniteAdaptedMean P qGrid s)
    (hfint : HasFiniteAdaptedMean P qGrid t)
    {S SStar K : Mat d} (hS : S.PosDef) (hStar : SStar.PosDef)
    (hEtform : toFullBlockMat (adaptedMean P qGrid t) =
      schurBlock S SStar K)
    (hsmall : 6 * (blockContrast (adaptedMean P qGrid t) - 1) ≤ 1)
    (hdrop :
      (d : ℝ) *
          (adaptedHattedContrast P qGrid s -
            adaptedHattedContrast P qGrid t) ≤ 1)
    (e : Vec d) (he : e ⬝ᵥ e = 1) :
    let h0 := Response.responseSkew K
    let p := Response.centeredResponseLoadP S SStar K e
    let r := Response.centeredResponseLoadQ S SStar K e
    Response.profilePrimalResponseDefect P (Recurrence.posDef_of_isRoundedGrid hgrid)
          h0 (Response.is_skew_mat_response_skew K) s t p r ≤
        16 * (d : ℝ) *
          (adaptedHattedContrast P qGrid s -
            adaptedHattedContrast P qGrid t) ∧
      Response.profileAdjointResponseDefect P (Recurrence.posDef_of_isRoundedGrid hgrid)
          h0 (Response.is_skew_mat_response_skew K) s t p r ≤
        16 * (d : ℝ) *
          (adaptedHattedContrast P qGrid s -
            adaptedHattedContrast P qGrid t) := by
  have hupper :
      toFullBlockMat (adaptedMean P qGrid s) ≤
        (1 + 4 * (d : ℝ) *
            (adaptedHattedContrast P qGrid s -
              adaptedHattedContrast P qGrid t)) •
          toFullBlockMat (adaptedMean P qGrid t) :=
    adaptedMean_le_hattedContrast_dilation hstat hgrid hls hst
      hfins hfint hdrop
  exact calibratedProfileDefects_le_of_hattedMeanDilation hstat hgrid hls hst
    hfins hfint hS hStar hEtform hsmall hupper e he

end

end HCPolySupport.HighContrast.Quenched
