/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.UCFlatness
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Topology
public import LeanPool.CaffarelliKohnNirenberg.ClassEquivalence.TestSupport

/-!
# Restriction to smaller space-time cylinders

Weak derivatives and the differential inequality restrict to smaller
product domains, as used in the radius iteration of `thm:uc`.
-/

public section


open MeasureTheory Set
open scoped ENNReal
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- Smooth test integrals can be restricted to a smaller domain containing
the test's topological support. -/
private theorem uc_setIntegral_restrict_of_tsupport
    {Ω' Ω : Set Vec3} {I' I : Set ℝ}
    (hΩ : IsOpen Ω) (hI : IsOpen I)
    (hΩsub : Ω' ⊆ Ω) (hIsub : I' ⊆ I)
    {φ : ParabolicPoint → ℝ}
    (hφU : tsupport (show Vec3 × ℝ → ℝ from φ) ⊆
      spaceTimeSet Ω' I')
    (F : ParabolicPoint → ℝ)
    (hF : ∀ z, z ∉ tsupport (show Vec3 × ℝ → ℝ from φ) → F z = 0) :
    (∫ z in spaceTimeSet Ω I, F z) =
      ∫ z in spaceTimeSet Ω' I', F z := by
  have hbig : MeasurableSet (spaceTimeSet Ω I) :=
    (CKN.Foundation.Parabolic.isOpen_spaceTimeSet Ω I hΩ hI).measurableSet
  have hsub : spaceTimeSet Ω' I' ⊆ spaceTimeSet Ω I := by
    rintro z ⟨hzx, hzt⟩
    exact ⟨hΩsub hzx, hIsub hzt⟩
  apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hbig hsub
  intro z hz
  exact hF z (fun h => hz.2 (hφU h))

/-- Restriction preserves the weak derivative identities and all source
integrability and differential-inequality hypotheses. -/
theorem uc_restrict_data
    (c₁ : ℝ) (Ω' Ω : Set Vec3) (I' I : Set ℝ)
    (w : ParabolicPoint → Vec3)
    (Dw : ParabolicPoint → Fin 3 → Vec3)
    (D2w : ParabolicPoint → Fin 3 → Fin 3 → Vec3)
    (Dtw : ParabolicPoint → Vec3)
    (hΩ : IsOpen Ω) (hI : IsOpen I)
    (hΩsub : Ω' ⊆ Ω) (hIsub : I' ⊆ I)
    (hcont : ContinuousOn w (Ω ×ˢ I))
    (hweak : HasSpaceTimeWeakDerivs Ω I w Dw D2w Dtw)
    (hL2 : (∫⁻ z in spaceTimeSet Ω I,
      ‖w z‖ₑ ^ (2 : ℝ) + ‖Dw z‖ₑ ^ (2 : ℝ) +
        ‖D2w z‖ₑ ^ (2 : ℝ) + ‖Dtw z‖ₑ ^ (2 : ℝ)) < ⊤)
    (hineq : ∀ᵐ z ∂(volume.restrict (spaceTimeSet Ω I)),
      vec3EuclideanNorm (ucWeakHeatVector D2w Dtw z) ≤
        c₁ * (vec3EuclideanNorm (w z) +
          Real.sqrt (spatialGradientSq w Dw z))) :
    ContinuousOn w (Ω' ×ˢ I') ∧
      HasSpaceTimeWeakDerivs Ω' I' w Dw D2w Dtw ∧
      (∫⁻ z in spaceTimeSet Ω' I',
        ‖w z‖ₑ ^ (2 : ℝ) + ‖Dw z‖ₑ ^ (2 : ℝ) +
          ‖D2w z‖ₑ ^ (2 : ℝ) + ‖Dtw z‖ₑ ^ (2 : ℝ)) < ⊤ ∧
      (∀ᵐ z ∂(volume.restrict (spaceTimeSet Ω' I')),
        vec3EuclideanNorm (ucWeakHeatVector D2w Dtw z) ≤
          c₁ * (vec3EuclideanNorm (w z) +
            Real.sqrt (spatialGradientSq w Dw z))) := by
  have hsub : spaceTimeSet Ω' I' ⊆ spaceTimeSet Ω I := by
    rintro z ⟨hzx, hzt⟩
    exact ⟨hΩsub hzx, hIsub hzt⟩
  refine ⟨hcont.mono (fun _ hz => ⟨hΩsub hz.1, hIsub hz.2⟩), ?_,
    (lintegral_mono_set hsub).trans_lt hL2,
    ae_restrict_of_ae_restrict_of_subset hsub hineq⟩
  rcases hweak with ⟨hwloc, hDwloc, hD2loc, hDtloc, hweakid⟩
  refine ⟨hwloc.mono_set hsub, hDwloc.mono_set hsub,
    hD2loc.mono_set hsub, hDtloc.mono_set hsub, ?_⟩
  intro φ hφ
  have hφbig : φ ∈ spaceTimeTestFunction (V := ℝ) Ω I := by
    rcases hφ with ⟨hφsmooth, hφcompact, hφsupport⟩
    exact ⟨hφsmooth, hφcompact, hφsupport.trans hsub⟩
  have hφsupport : tsupport (show Vec3 × ℝ → ℝ from φ) ⊆
      spaceTimeSet Ω' I' := hφ.2.2
  have hnot (z : ParabolicPoint)
      (hz : z ∉ tsupport (show Vec3 × ℝ → ℝ from φ)) : φ z = 0 :=
    image_eq_zero_of_notMem_tsupport
      (f := show Vec3 × ℝ → ℝ from φ) hz
  have hsp (z : ParabolicPoint)
      (hz : z ∉ tsupport (show Vec3 × ℝ → ℝ from φ)) (j : Fin 3) :
      spatialPartial φ j z = 0 :=
    CKN.spatialPartial_eq_zero_off_tsupport hz j
  have htm (z : ParabolicPoint)
      (hz : z ∉ tsupport (show Vec3 × ℝ → ℝ from φ)) :
      timePartial φ z = 0 :=
    CKN.timePartial_eq_zero_off_tsupport hz
  obtain ⟨hfirst, hsecond, htime⟩ := hweakid φ hφbig
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    calc
      (∫ z in spaceTimeSet Ω' I', w z i * spatialPartial φ j z) =
          ∫ z in spaceTimeSet Ω I, w z i * spatialPartial φ j z :=
            (uc_setIntegral_restrict_of_tsupport hΩ hI hΩsub hIsub
              hφsupport _ (fun z hz => by simp [hsp z hz j])).symm
      _ = -∫ z in spaceTimeSet Ω I, Dw z i j * φ z := hfirst i j
      _ = -∫ z in spaceTimeSet Ω' I', Dw z i j * φ z := by
        rw [uc_setIntegral_restrict_of_tsupport hΩ hI hΩsub hIsub
          hφsupport _ (fun z hz => by simp [hnot z hz])]
  · intro i j k
    calc
      (∫ z in spaceTimeSet Ω' I', Dw z i j * spatialPartial φ k z) =
          ∫ z in spaceTimeSet Ω I, Dw z i j * spatialPartial φ k z :=
            (uc_setIntegral_restrict_of_tsupport hΩ hI hΩsub hIsub
              hφsupport _ (fun z hz => by simp [hsp z hz k])).symm
      _ = -∫ z in spaceTimeSet Ω I, D2w z i j k * φ z := hsecond i j k
      _ = -∫ z in spaceTimeSet Ω' I', D2w z i j k * φ z := by
        rw [uc_setIntegral_restrict_of_tsupport hΩ hI hΩsub hIsub
          hφsupport _ (fun z hz => by simp [hnot z hz])]
  · intro i
    calc
      (∫ z in spaceTimeSet Ω' I', w z i * timePartial φ z) =
          ∫ z in spaceTimeSet Ω I, w z i * timePartial φ z :=
            (uc_setIntegral_restrict_of_tsupport hΩ hI hΩsub hIsub
              hφsupport _ (fun z hz => by simp [htm z hz])).symm
      _ = -∫ z in spaceTimeSet Ω I, Dtw z i * φ z := htime i
      _ = -∫ z in spaceTimeSet Ω' I', Dtw z i * φ z := by
        rw [uc_setIntegral_restrict_of_tsupport hΩ hI hΩsub hIsub
          hφsupport _ (fun z hz => by simp [hnot z hz])]

end ESS
