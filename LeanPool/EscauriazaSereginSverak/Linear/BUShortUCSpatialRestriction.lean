/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUShortPositiveZero

/-!
# Spatial restriction on translated time intervals

The weak derivative identities remain valid on an open spatial subdomain
on the corresponding cylinder, including after the initial-time shift.
-/

public section


open MeasureTheory Set CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- Space-time weak derivatives restrict from the positive half-space to
a spatial subset at any measurable time interval. -/
theorem bu_weak_restrict_space_interval
    {I : Set ℝ} (hI : MeasurableSet I) {B : Set Vec3}
    (hB : B ⊆ {x : Vec3 | 0 < x 2})
    (w : ParabolicPoint → Vec3)
    (Dw : ParabolicPoint → Fin 3 → Vec3)
    (D2w : ParabolicPoint → Fin 3 → Fin 3 → Vec3)
    (Dtw : ParabolicPoint → Vec3)
    (hweak : HasSpaceTimeWeakDerivs {x : Vec3 | 0 < x 2} I
      w Dw D2w Dtw) :
    HasSpaceTimeWeakDerivs B I w Dw D2w Dtw := by
  let Q := spaceTimeSet {x : Vec3 | 0 < x 2} I
  let Q' := spaceTimeSet B I
  have hQsub : Q' ⊆ Q := by
    rintro z ⟨hx, ht⟩
    exact ⟨hB hx, ht⟩
  have hQmeas : MeasurableSet Q := by
    change MeasurableSet
      ({x : Vec3 | 0 < x 2} ×ˢ I : Set ParabolicPoint)
    exact ((isOpen_lt continuous_const (continuous_apply 2)).measurableSet).prod
      hI
  rcases hweak with ⟨hwloc, hDwloc, hD2loc, hDtloc, hweakid⟩
  refine ⟨hwloc.mono_set hQsub, hDwloc.mono_set hQsub,
    hD2loc.mono_set hQsub, hDtloc.mono_set hQsub, ?_⟩
  intro φ hφ
  have hφbig : φ ∈ spaceTimeTestFunction (V := ℝ)
      {x : Vec3 | 0 < x 2} I :=
    ⟨hφ.1, hφ.2.1, hφ.2.2.trans hQsub⟩
  have hφsupp : tsupport (show Vec3 × ℝ → ℝ from φ) ⊆ Q' := hφ.2.2
  have hrestr (F : ParabolicPoint → ℝ)
      (hF : ∀ z, z ∉ tsupport (show Vec3 × ℝ → ℝ from φ) → F z = 0) :
      (∫ z in Q, F z) = ∫ z in Q', F z := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hQmeas hQsub
    intro z hz
    exact hF z (fun h => hz.2 (hφsupp h))
  have hφzero (z : ParabolicPoint)
      (hz : z ∉ tsupport (show Vec3 × ℝ → ℝ from φ)) : φ z = 0 :=
    image_eq_zero_of_notMem_tsupport
      (f := show Vec3 × ℝ → ℝ from φ) hz
  have hspzero (z : ParabolicPoint)
      (hz : z ∉ tsupport (show Vec3 × ℝ → ℝ from φ)) (j : Fin 3) :
      spatialPartial φ j z = 0 :=
    CKN.spatialPartial_eq_zero_off_tsupport hz j
  have htimezero (z : ParabolicPoint)
      (hz : z ∉ tsupport (show Vec3 × ℝ → ℝ from φ)) :
      timePartial φ z = 0 :=
    CKN.timePartial_eq_zero_off_tsupport hz
  obtain ⟨hfirst, hsecond, htime⟩ := hweakid φ hφbig
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    calc
      (∫ z in Q', w z i * spatialPartial φ j z) =
          ∫ z in Q, w z i * spatialPartial φ j z :=
        (hrestr _ (fun z hz => by simp [hspzero z hz j])).symm
      _ = -∫ z in Q, Dw z i j * φ z := hfirst i j
      _ = -∫ z in Q', Dw z i j * φ z := by
        rw [hrestr _ (fun z hz => by simp [hφzero z hz])]
  · intro i j k
    calc
      (∫ z in Q', Dw z i j * spatialPartial φ k z) =
          ∫ z in Q, Dw z i j * spatialPartial φ k z :=
        (hrestr _ (fun z hz => by simp [hspzero z hz k])).symm
      _ = -∫ z in Q, D2w z i j k * φ z := hsecond i j k
      _ = -∫ z in Q', D2w z i j k * φ z := by
        rw [hrestr _ (fun z hz => by simp [hφzero z hz])]
  · intro i
    calc
      (∫ z in Q', w z i * timePartial φ z) =
          ∫ z in Q, w z i * timePartial φ z :=
        (hrestr _ (fun z hz => by simp [htimezero z hz])).symm
      _ = -∫ z in Q, Dtw z i * φ z := htime i
      _ = -∫ z in Q', Dtw z i * φ z := by
        rw [hrestr _ (fun z hz => by simp [hφzero z hz])]

end ESS
