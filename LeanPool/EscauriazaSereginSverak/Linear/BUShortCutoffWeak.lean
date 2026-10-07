/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUShortWeakProductBasis
public import LeanPool.EscauriazaSereginSverak.Linear.BUShortRescalingValues

/-!
# Weak derivatives of the short-time cutoff field

The product field formed from the shifted solution and the smooth compact
cutoff has the exact weak derivative data required by the half-space estimate.
-/

public section


open MeasureTheory Set CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- The short-time cut-off field has the expected weak spatial and time
derivatives on the shifted positive half-space cylinder. -/
theorem bu_short_cutoff_weak_derivatives
    (scale R ε : ℝ) (hscale : 0 < scale) (hscale1 : scale ≤ 1)
    (hR : 0 < R)
    (w : ParabolicPoint → Vec3)
    (Dw : ParabolicPoint → Fin 3 → Vec3)
    (D2w : ParabolicPoint → Fin 3 → Fin 3 → Vec3)
    (Dtw : ParabolicPoint → Vec3)
    (hweak : HasSpaceTimeWeakDerivs {x : Vec3 | 0 < x 2} (Ioo 0 1)
      w Dw D2w Dtw) :
    HasSpaceTimeWeakDerivs {x : Vec3 | 0 < x 2} (Ioo (1 / 2 : ℝ) 1)
      (buCutField (buShortFullCutoff scale R hR ε)
        (buAffineField (-scale ^ 2 / 2) scale w))
      (buCutDw (buShortFullCutoff scale R hR ε)
        (buAffineField (-scale ^ 2 / 2) scale w)
        (buAffineDw (-scale ^ 2 / 2) scale Dw))
      (buCutD2 (buShortFullCutoff scale R hR ε)
        (buAffineField (-scale ^ 2 / 2) scale w)
        (buAffineDw (-scale ^ 2 / 2) scale Dw)
        (buAffineD2w (-scale ^ 2 / 2) scale D2w))
      (buCutDt (buShortFullCutoff scale R hR ε)
        (buAffineField (-scale ^ 2 / 2) scale w)
        (buAffineDtw (-scale ^ 2 / 2) scale Dtw)) := by
  exact buCut_hasSpaceTimeWeakDerivs
    (buShortFullCutoff scale R hR ε)
    (buShortFullCutoff_smooth scale R hR ε)
    (bu_short_weak_derivatives scale hscale hscale1 w Dw D2w Dtw hweak)

end ESS
