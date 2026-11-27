/-
Copyright (c) 2026 Mark Gladden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mark Gladden
-/

/- Modified for Lean Pool: adapt module imports and source presentation. -/

module

public import LeanPool.VenNullClockRoundRates.VenRateUpperPhysical
public import LeanPool.VenNullClockRoundRates.VenRateUpperClassGap

/-! The printed common-profile witness and matching class rates on round area. -/

@[expose] public section
open MeasureTheory VenMask VenRate
open scoped ContDiff

namespace VenRateUpper

/-- The smooth common-profile witness with the exact two-supremum error in Eq. (31). -/
theorem smooth_round_common_profile_error {a b θ : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hθ : 0 < 1 - Real.cos θ ^ 2) :
    ∃ c M₁ : ℝ, 0 < c ∧ 1 < M₁ ∧ ∀ M ≥ M₁,
      ∃ W : ℝ × ℝ × ℝ → ℝ, ContDiff ℝ ∞ W ∧
        (∀ y : UnitSphere, 2 ≤ W y.val ∧ W y.val ≤ M) ∧
        dataDistance roundArea (fun y => W y.val) (fun y => W y.val) θ b a ≤
          Real.exp (-c * Real.log M * Real.log (Real.log M)) := by
  obtain ⟨c, M₁, hc, hM₁, existsProfile⟩ := smooth_round_common_profile_upper ha hb hθ
  refine ⟨c, M₁, hc, hM₁,?_⟩
  intro M hM
  obtain ⟨W, hW, rangeW, hclose⟩ := existsProfile M hM
  have hw : Continuous (fun y : UnitSphere => W y.val) :=
    hW.continuous.comp continuous_subtype_val
  have hint : Integrable (fun y : UnitSphere => W y.val) roundArea :=
    hw.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  exact ⟨W, hW, rangeW, (dataDistance_le_iff_dataClose ha.le hb.le hint hint).mpr hclose⟩

/-- Equation (34), jointly for the broad class and the restrictions of
ambient smooth profiles. The upper witness uses one fixed admissible angle. -/
theorem matching_round_class_rates {a b d : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hd : 0 < d) (hd1 : d ≤ 1) :
    ∃ C c M₀ : ℝ, 0 < C ∧ 0 < c ∧ 1 < M₀ ∧ ∀ M ≥ M₀,
      let lower := Real.exp (-C * Real.log M * Real.log (Real.log M))
      let upper := Real.exp (-c * Real.log M * Real.log (Real.log M))
      lower ≤ roundClassGap a b d M (fun _ => True) ∧
      roundClassGap a b d M (fun _ => True) ≤ upper ∧
      lower ≤ roundClassGap a b d M AmbientSmooth ∧
      roundClassGap a b d M AmbientSmooth ≤ upper := by
  have separation : d ≤ 1 - Real.cos (Real.pi / 2) ^ 2 := by
    simpa using hd1
  exact matching_round_class_rates_of_smooth_witness ha hb hd hd1 separation
    (smooth_round_common_profile_upper ha hb (hd.trans_le separation))

/-- Any admissible profile subclass containing the smooth ambient restrictions
has the same two-sided rate. In particular the upper construction remains valid
for the intrinsic smooth class, while the lower applies to the broad class. -/
theorem matching_round_class_rate_for_subclass {a b d : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hd : 0 < d) (hd1 : d ≤ 1)
    (Q : (UnitSphere → ℝ) → Prop) (hQ : ∀ w, AmbientSmooth w → Q w) :
    ∃ C c M₀ : ℝ, 0 < C ∧ 0 < c ∧ 1 < M₀ ∧ ∀ M ≥ M₀,
      Real.exp (-C * Real.log M * Real.log (Real.log M)) ≤ roundClassGap a b d M Q ∧
      roundClassGap a b d M Q ≤ Real.exp (-c * Real.log M * Real.log (Real.log M)) := by
  obtain ⟨C, c, M₀, hC, hc, hM₀, rate⟩ := matching_round_class_rates ha hb hd hd1
  refine ⟨C, c, M₀, hC, hc, hM₀,?_⟩
  intro M hM
  have compare := round_class_gap_between_broad_and_ambient ha.le hb.le hd1
    (hM₀.le.trans hM) hQ
  have h := rate M hM
  exact ⟨h.1.trans compare.1, compare.2.trans h.2.2.2⟩

end VenRateUpper
