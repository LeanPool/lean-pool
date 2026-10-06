/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUAffineIntervalL2

/-!
# Derivative energy on affine time intervals

The three quadratic derivative terms used in `lem:bu-small-time` remain
finite on bounded subsets after the translated parabolic change of variables.
-/

public section


open MeasureTheory Set CKN CKN.Foundation.Parabolic
open scoped ENNReal

noncomputable section

namespace ESS

/-- The three quadratic weak-derivative terms remain finite on bounded
subsets after a subunit affine parabolic change of variables. -/
theorem bu_affine_derivative_l2_interval
    (τ scale a b : ℝ) (hscale : 0 < scale)
    (hscale1 : scale ≤ 1)
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
      (∫⁻ z in S, ‖Dw z‖ₑ ^ (2 : ℝ) +
        ‖D2w z‖ₑ ^ (2 : ℝ) + ‖Dtw z‖ₑ ^ (2 : ℝ)) < ⊤) :
    ∀ K : Set ParabolicPoint,
      K ⊆ spaceTimeSet {x : Vec3 | 0 < x 2} (Ioo a b) →
      Bornology.IsBounded K →
      (∫⁻ z in K,
        ‖(buAffineDw τ scale Dw) z‖ₑ ^ (2 : ℝ) +
        ‖(buAffineD2w τ scale D2w) z‖ₑ ^ (2 : ℝ) +
        ‖(buAffineDtw τ scale Dtw) z‖ₑ ^ (2 : ℝ)) < ⊤ := by
  have hscale2le : scale ^ 2 ≤ 1 := pow_le_one₀ hscale.le hscale1
  have hDwL2 (S : Set ParabolicPoint)
      (hS : S ⊆ spaceTimeSet {x : Vec3 | 0 < x 2}
        (Ioo (τ + scale ^ 2 * a) (τ + scale ^ 2 * b))) (hSb : Bornology.IsBounded S) :
      (∫⁻ z in S, ‖Dw z‖ₑ ^ (2 : ℝ)) < ⊤ := by
    refine (lintegral_mono (fun z => ?_)).trans_lt
      (hL2 S hS hSb)
    exact le_add_of_nonneg_right (by positivity) |>.trans
      (le_add_of_nonneg_right (by positivity))
  have hD2L2 (S : Set ParabolicPoint)
      (hS : S ⊆ spaceTimeSet {x : Vec3 | 0 < x 2}
        (Ioo (τ + scale ^ 2 * a) (τ + scale ^ 2 * b))) (hSb : Bornology.IsBounded S) :
      (∫⁻ z in S, ‖D2w z‖ₑ ^ (2 : ℝ)) < ⊤ := by
    refine (lintegral_mono (fun z => ?_)).trans_lt
      (hL2 S hS hSb)
    exact le_add_of_nonneg_left (by positivity) |>.trans
      (le_add_of_nonneg_right (by positivity))
  have hDtL2 (S : Set ParabolicPoint)
      (hS : S ⊆ spaceTimeSet {x : Vec3 | 0 < x 2}
        (Ioo (τ + scale ^ 2 * a) (τ + scale ^ 2 * b))) (hSb : Bornology.IsBounded S) :
      (∫⁻ z in S, ‖Dtw z‖ₑ ^ (2 : ℝ)) < ⊤ := by
    refine (lintegral_mono (fun z => ?_)).trans_lt
      (hL2 S hS hSb)
    exact le_add_of_nonneg_left (by positivity)
  intro K hKsub hKb
  have hDwK := bu_affine_l2_smul_interval τ scale a b scale hscale hscale.le hscale1
    Dw hweak.2.1 hDwL2 K hKsub hKb
  have hD2K := bu_affine_l2_smul_interval τ scale a b (scale ^ 2) hscale
    (sq_nonneg scale) hscale2le D2w hweak.2.2.1 hD2L2 K hKsub hKb
  have hDtK := bu_affine_l2_smul_interval τ scale a b (scale ^ 2) hscale
    (sq_nonneg scale) hscale2le Dtw hweak.2.2.2.1 hDtL2 K hKsub hKb
  have hscaled := bu_affine_weak_derivatives_interval τ scale a b hscale
    w Dw D2w Dtw hweak
  have hmDw : AEMeasurable
      (fun z => ‖(buAffineDw τ scale Dw) z‖ₑ ^ (2 : ℝ))
      (volume.restrict K) :=
    ENNReal.continuous_rpow_const.measurable.comp_aemeasurable
      ((hscaled.2.1.mono_set hKsub).aestronglyMeasurable.enorm)
  have hmD2 : AEMeasurable
      (fun z => ‖(buAffineD2w τ scale D2w) z‖ₑ ^ (2 : ℝ))
      (volume.restrict K) :=
    ENNReal.continuous_rpow_const.measurable.comp_aemeasurable
      ((hscaled.2.2.1.mono_set hKsub).aestronglyMeasurable.enorm)
  have hsum :
      (∫⁻ z in K,
        ‖(buAffineDw τ scale Dw) z‖ₑ ^ (2 : ℝ) +
        ‖(buAffineD2w τ scale D2w) z‖ₑ ^ (2 : ℝ) +
        ‖(buAffineDtw τ scale Dtw) z‖ₑ ^ (2 : ℝ)) =
      (∫⁻ z in K, ‖(buAffineDw τ scale Dw) z‖ₑ ^ (2 : ℝ)) +
      (∫⁻ z in K, ‖(buAffineD2w τ scale D2w) z‖ₑ ^ (2 : ℝ)) +
      (∫⁻ z in K, ‖(buAffineDtw τ scale Dtw) z‖ₑ ^ (2 : ℝ)) := by
    have h12 :
        (∫⁻ z in K,
          ‖(buAffineDw τ scale Dw) z‖ₑ ^ (2 : ℝ) +
          ‖(buAffineD2w τ scale D2w) z‖ₑ ^ (2 : ℝ)) =
        (∫⁻ z in K, ‖(buAffineDw τ scale Dw) z‖ₑ ^ (2 : ℝ)) +
        (∫⁻ z in K, ‖(buAffineD2w τ scale D2w) z‖ₑ ^ (2 : ℝ)) := by
      simpa only [Pi.add_apply] using
        (lintegral_add_left' hmDw
          (fun z => ‖(buAffineD2w τ scale D2w) z‖ₑ ^ (2 : ℝ)))
    have h123 :
        (∫⁻ z in K,
          (‖(buAffineDw τ scale Dw) z‖ₑ ^ (2 : ℝ) +
            ‖(buAffineD2w τ scale D2w) z‖ₑ ^ (2 : ℝ)) +
          ‖(buAffineDtw τ scale Dtw) z‖ₑ ^ (2 : ℝ)) =
        (∫⁻ z in K,
          ‖(buAffineDw τ scale Dw) z‖ₑ ^ (2 : ℝ) +
          ‖(buAffineD2w τ scale D2w) z‖ₑ ^ (2 : ℝ)) +
        (∫⁻ z in K, ‖(buAffineDtw τ scale Dtw) z‖ₑ ^ (2 : ℝ)) := by
      simpa only [Pi.add_apply] using
        (lintegral_add_left' (hmDw.add hmD2)
          (fun z => ‖(buAffineDtw τ scale Dtw) z‖ₑ ^ (2 : ℝ)))
    exact h123.trans (congrArg (· + _ ) h12)
  rw [hsum]
  have hDwEq : buAffineDw τ scale Dw =
      fun z => scale • Dw (buAffinePoint τ scale z) := by
    funext z i j
    rfl
  have hD2Eq : buAffineD2w τ scale D2w =
      fun z => scale ^ 2 • D2w (buAffinePoint τ scale z) := by
    funext z i j k
    rfl
  have hDtEq : buAffineDtw τ scale Dtw =
      fun z => scale ^ 2 • Dtw (buAffinePoint τ scale z) := by
    funext z i
    rfl
  apply ENNReal.add_lt_top.mpr
  constructor
  · apply ENNReal.add_lt_top.mpr
    constructor
    · rw [hDwEq]
      exact hDwK
    · rw [hD2Eq]
      exact hD2K
  · rw [hDtEq]
    exact hDtK

end ESS
