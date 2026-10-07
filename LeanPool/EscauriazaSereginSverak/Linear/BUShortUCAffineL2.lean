/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUShortUCSpatialRestriction
public import LeanPool.EscauriazaSereginSverak.Linear.BUAffineIntervalDerivativeL2

/-!
# Local quadratic energy after the final time change

The velocity and all specified weak derivatives retain finite quadratic
energy on bounded subcylinders after the affine change of variables.
-/

public section


open MeasureTheory Set CKN CKN.Foundation.Parabolic
open scoped ENNReal

noncomputable section

namespace ESS

/-- Full local quadratic weak-derivative data transfers through an affine
parabolic change of variables on the translated time interval. -/
theorem bu_short_uc_affine_l2
    (τ scale a b : ℝ) (hscale : 0 < scale) (hscale1 : scale ≤ 1)
    (w : ParabolicPoint → Vec3)
    (Dw : ParabolicPoint → Fin 3 → Vec3)
    (D2w : ParabolicPoint → Fin 3 → Fin 3 → Vec3)
    (Dtw : ParabolicPoint → Vec3)
    (hweak : HasSpaceTimeWeakDerivs {x : Vec3 | 0 < x 2}
      (Ioo (τ + scale ^ 2 * a) (τ + scale ^ 2 * b))
      w Dw D2w Dtw)
    (hL2 : ∀ S : Set ParabolicPoint,
      S ⊆ spaceTimeSet {x : Vec3 | 0 < x 2}
        (Ioo (τ + scale ^ 2 * a) (τ + scale ^ 2 * b)) →
      Bornology.IsBounded S →
      (∫⁻ z in S, ‖w z‖ₑ ^ (2 : ℝ) + ‖Dw z‖ₑ ^ (2 : ℝ) +
        ‖D2w z‖ₑ ^ (2 : ℝ) + ‖Dtw z‖ₑ ^ (2 : ℝ)) < ⊤)
    (K : Set ParabolicPoint)
    (hK : K ⊆ spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo a b))
    (hKb : Bornology.IsBounded K) :
    (∫⁻ z in K,
      ‖(buAffineField τ scale w) z‖ₑ ^ (2 : ℝ) +
        ‖(buAffineDw τ scale Dw) z‖ₑ ^ (2 : ℝ) +
          ‖(buAffineD2w τ scale D2w) z‖ₑ ^ (2 : ℝ) +
            ‖(buAffineDtw τ scale Dtw) z‖ₑ ^ (2 : ℝ)) < ⊤ := by
  have hWsource (S : Set ParabolicPoint)
      (hS : S ⊆ spaceTimeSet {x : Vec3 | 0 < x 2}
        (Ioo (τ + scale ^ 2 * a) (τ + scale ^ 2 * b)))
      (hSb : Bornology.IsBounded S) :
      (∫⁻ z in S, ‖w z‖ₑ ^ (2 : ℝ)) < ⊤ := by
    refine (lintegral_mono (fun z => ?_)).trans_lt (hL2 S hS hSb)
    exact le_add_of_nonneg_right (by positivity) |>.trans
      (le_add_of_nonneg_right (by positivity) |>.trans
        (le_add_of_nonneg_right (by positivity)))
  have hDsource (S : Set ParabolicPoint)
      (hS : S ⊆ spaceTimeSet {x : Vec3 | 0 < x 2}
        (Ioo (τ + scale ^ 2 * a) (τ + scale ^ 2 * b)))
      (hSb : Bornology.IsBounded S) :
      (∫⁻ z in S, ‖Dw z‖ₑ ^ (2 : ℝ) +
        ‖D2w z‖ₑ ^ (2 : ℝ) + ‖Dtw z‖ₑ ^ (2 : ℝ)) < ⊤ := by
    refine (lintegral_mono (fun z => ?_)).trans_lt (hL2 S hS hSb)
    simpa only [add_assoc] using
      (le_add_of_nonneg_left
        (show (0 : ℝ≥0∞) ≤ ‖w z‖ₑ ^ (2 : ℝ) from bot_le) :
        ‖Dw z‖ₑ ^ (2 : ℝ) + ‖D2w z‖ₑ ^ (2 : ℝ) +
          ‖Dtw z‖ₑ ^ (2 : ℝ) ≤
          ‖w z‖ₑ ^ (2 : ℝ) +
            (‖Dw z‖ₑ ^ (2 : ℝ) + ‖D2w z‖ₑ ^ (2 : ℝ) +
              ‖Dtw z‖ₑ ^ (2 : ℝ)))
  have hW := bu_affine_l2_comp_interval τ scale a b hscale w
    hweak.1 hWsource K hK hKb
  have hD := bu_affine_derivative_l2_interval τ scale a b
    hscale hscale1 w Dw D2w Dtw hweak hDsource K hK hKb
  have hscaled := bu_affine_weak_derivatives_interval τ scale a b
    hscale w Dw D2w Dtw hweak
  have hWmeas : AEMeasurable
      (fun z => ‖(buAffineField τ scale w) z‖ₑ ^ (2 : ℝ))
      (volume.restrict K) :=
    ENNReal.continuous_rpow_const.measurable.comp_aemeasurable
      ((hscaled.1.mono_set hK).aestronglyMeasurable.enorm)
  have hsplit := lintegral_add_left' hWmeas
    (fun z => ‖(buAffineDw τ scale Dw) z‖ₑ ^ (2 : ℝ) +
      ‖(buAffineD2w τ scale D2w) z‖ₑ ^ (2 : ℝ) +
      ‖(buAffineDtw τ scale Dtw) z‖ₑ ^ (2 : ℝ))
  simp only [add_assoc] at hsplit ⊢
  rw [hsplit]
  exact ENNReal.add_lt_top.mpr ⟨hW, by simpa only [add_assoc] using hD⟩

end ESS
