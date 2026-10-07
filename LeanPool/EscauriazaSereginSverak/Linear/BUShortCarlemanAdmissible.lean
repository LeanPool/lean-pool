/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUShortL2Sum

/-!
# Admissibility of the short-time cutoff

The smooth spatial and temporal cutoff of `lem:bu-small-time` supplies the
weak derivative and quadratic energy assumptions of the half-space estimate.
-/

public section


open MeasureTheory Set CKN CKN.Foundation.Parabolic
open scoped ENNReal

noncomputable section

namespace ESS

/-- The short-time cutoff has precisely the weak data, support, and finite
quadratic energy required for the half-space Sobolev Carleman inequality. -/
theorem bu_short_cutoff_carleman_admissible
    (scale R ε : ℝ) (hscale : 0 < scale) (hscale1 : scale ≤ 1)
    (hR : 0 < R) (hε : 0 < ε)
    (w : ParabolicPoint → Vec3)
    (Dw : ParabolicPoint → Fin 3 → Vec3)
    (D2w : ParabolicPoint → Fin 3 → Fin 3 → Vec3)
    (Dtw : ParabolicPoint → Vec3)
    (hcont : ContinuousOn w ({x : Vec3 | 0 < x 2} ×ˢ Ico (0 : ℝ) 1))
    (hweak : HasSpaceTimeWeakDerivs {x : Vec3 | 0 < x 2} (Ioo 0 1)
      w Dw D2w Dtw)
    (hL2 : ∀ S : Set ParabolicPoint,
      S ⊆ spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo 0 1) →
      Bornology.IsBounded S →
      (∫⁻ z in S, ‖Dw z‖ₑ ^ (2 : ℝ) +
        ‖D2w z‖ₑ ^ (2 : ℝ) + ‖Dtw z‖ₑ ^ (2 : ℝ)) < ⊤) :
    let κ := buShortFullCutoff scale R hR ε
    let v := buAffineField (-scale ^ 2 / 2) scale w
    let Dv := buAffineDw (-scale ^ 2 / 2) scale Dw
    let D2v := buAffineD2w (-scale ^ 2 / 2) scale D2w
    let Dtv := buAffineDtw (-scale ^ 2 / 2) scale Dtw
    let W := buCutField κ v
    let DW := buCutDw κ v Dv
    let D2W := buCutD2 κ v Dv D2v
    let DtW := buCutDt κ v Dtv
    HasSpaceTimeWeakDerivs {x : Vec3 | 1 < x 2} (Ioo 0 1)
      W DW D2W DtW ∧
    HasCompactSupport W ∧
    tsupport W ⊆ spaceTimeSet {x : Vec3 | 1 < x 2} (Ioo 0 1) ∧
    (∫⁻ z in spaceTimeSet {x : Vec3 | 1 < x 2} (Ioo 0 1),
      ‖W z‖ₑ ^ (2 : ℝ) + ‖DW z‖ₑ ^ (2 : ℝ) +
        ‖D2W z‖ₑ ^ (2 : ℝ) + ‖DtW z‖ₑ ^ (2 : ℝ)) < ⊤ := by
  obtain ⟨hderiv, hcompact, hts, hw, hDw, hD2w, hDtw⟩ :=
    bu_short_cutoff_carleman_data scale R ε hscale hscale1 hR hε
      w Dw D2w Dtw hcont hweak hL2
  exact ⟨hderiv, hcompact, hts,
    bu_memLp_four_sum_lintegral_lt_top _ _ _ _ _ hw hDw hD2w hDtw⟩

end ESS
