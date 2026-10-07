/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUShortWeightCompact
public import LeanPool.EscauriazaSereginSverak.Linear.BUShortSupportData

/-!
# Weighted cutoff error at fixed parameters

The scalar cutoff heat error has a finite weighted integral on the compact
support of the cutoff for every fixed Carleman parameter.
-/

public section


open MeasureTheory Set CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- The weighted squared heat error is integrable on the compact
short-time cutoff support. -/
theorem bu_short_weighted_error_integrable
    (scale R ε c₁ a : ℝ) (hscale : 0 < scale) (hscale1 : scale ≤ 1)
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
    let K := buCutSupportSet (buShortFullCutoff scale R hR ε)
    let v := buAffineField (-scale ^ 2 / 2) scale w
    let Dv := buAffineDw (-scale ^ 2 / 2) scale Dw
    IntegrableOn (fun z => buShortCarlemanWeight a z *
      buShortCutoffHeatErrorSize scale R hR ε c₁ v Dv z ^ 2)
      K volume := by
  let K := buCutSupportSet (buShortFullCutoff scale R hR ε)
  let v := buAffineField (-scale ^ 2 / 2) scale w
  let Dv := buAffineDw (-scale ^ 2 / 2) scale Dw
  have hK : IsCompact K :=
    (bu_short_cutoff_support_geometry scale R ε hscale hscale1 hR hε).1
  obtain ⟨hv, hDv, _, _⟩ := bu_short_support_memLp_data
    scale R ε hscale hscale1 hR hε w Dw D2w Dtw hcont hweak hL2
  have herror : IntegrableOn (fun z =>
      buShortCutoffHeatErrorSize scale R hR ε c₁ v Dv z ^ 2)
      K volume :=
    bu_short_cutoff_error_sq_integrable scale R ε c₁ hR K hK v Dv hv hDv
  exact bu_integrableOn_mul_continuous_compact hK _ _ herror
    (buShortCarlemanWeight_continuousOn_support
      scale R ε a hscale hscale1 hR hε)

end ESS
