/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUShortSupportData

/-!
# Quadratic data of the short-time cutoff field

Compact support and the source local quadratic bounds imply global `L²`
data for the field to which the half-space Carleman estimate is applied.
-/

public section


open MeasureTheory Set CKN CKN.Foundation.Parabolic
open scoped ENNReal

noncomputable section

namespace ESS

/-- The cut-off rescaled field and its weak derivative data are globally
square integrable. -/
theorem bu_short_cutoff_memLp_data
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
    MemLp (buCutField κ v) 2 volume ∧
      MemLp (buCutDw κ v Dv) 2 volume ∧
      MemLp (buCutD2 κ v Dv D2v) 2 volume ∧
      MemLp (buCutDt κ v Dtv) 2 volume := by
  let κ := buShortFullCutoff scale R hR ε
  obtain ⟨hv, hDv, hD2v, hDtv⟩ :=
    bu_short_support_memLp_data scale R ε hscale hscale1 hR hε
      w Dw D2w Dtw hcont hweak hL2
  exact buCut_memLp_data κ
    (buShortFullCutoff_smooth scale R hR ε)
    (buShortFullCutoff_compact_support hscale hscale1 hR hε).1
    (buAffineField (-scale ^ 2 / 2) scale w)
    (buAffineDw (-scale ^ 2 / 2) scale Dw)
    (buAffineD2w (-scale ^ 2 / 2) scale D2w)
    (buAffineDtw (-scale ^ 2 / 2) scale Dtw)
    hv hDv hD2v hDtv

end ESS
