/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.LocalStrongRegTimeWeak

/-!
# Spatial weak derivatives on a slab from weak derivatives of the time slices

If almost every time slice of a slab function has a spatial weak partial derivative, and both are
square integrable on the slabs strictly inside, then the space-time integration by parts identity
holds against smooth compactly supported tests on the slab (`prop:lps-local-strong`).
-/

public section

open MeasureTheory Set Filter Topology
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS.LPS

/-- A time slice of a smooth compactly supported space-time function is smooth with compact
support. -/
theorem lps_test_slice {φ : Vec3 × ℝ → ℝ} (hd : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ)
    (t : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec3 => φ (x, t)) ∧
      HasCompactSupport (fun x : Vec3 => φ (x, t)) := by
  refine ⟨hd.comp (contDiff_id.prodMk contDiff_const), ?_⟩
  have hK : IsCompact ((fun z : Vec3 × ℝ => z.1) '' tsupport φ) := hc.isCompact.image continuous_fst
  refine hK.of_isClosed_subset (isClosed_tsupport _) ?_
  refine closure_minimal ?_ hK.isClosed
  intro x hx
  exact ⟨(x, t), subset_tsupport φ hx, rfl⟩

/-- A smooth function has its derivative as weak partial derivative on the whole space. -/
theorem lps_smooth_hasWeakPartialDerivOn {f : Vec3 → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (j : Fin 3) :
    HasWeakPartialDerivOn (Set.univ : Set Vec3) j f (spatialDeriv f j) := by
  intro φ hφ hφc _
  simp only [Measure.restrict_univ]
  have := lps_ibp_compactSupport hf hφ hφc j
  rw [this, neg_neg]
  rfl

/-- Integration by parts on a slab against smooth compactly supported tests, from weak spatial
derivatives of the time slices. -/
theorem lps_slab_spatial_weak_of_slices {a T : ℝ} (hab : a < T) (j : Fin 3)
    {F G : Vec3 × ℝ → ℝ}
    (hslice : ∀ᵐ t ∂(volume.restrict (Ioo a T)),
      HasWeakPartialDerivOn (Set.univ : Set Vec3) j (fun x => F (x, t)) (fun x => G (x, t)))
    (hF : ∀ a' b', a < a' → a' < b' → b' < T → MemLp F 2 (volume.restrict (vlSlab a' b')))
    (hG : ∀ a' b', a < a' → a' < b' → b' < T → MemLp G 2 (volume.restrict (vlSlab a' b')))
    {φ : Vec3 × ℝ → ℝ}
    (hφ : φ ∈ spaceTimeTestFunction (V := ℝ) (Set.univ : Set Vec3) (Ioo a T)) :
    ∫ z in vlSlab a T, F z * spatialPartial φ j z = -∫ z in vlSlab a T, G z * φ z := by
  obtain ⟨a', b', h1, h2, h3, hout⟩ := lps_test_time_margin hab hφ
  have hφ0 : ∀ z : Vec3 × ℝ, z.2 ∉ Ioo a' b' → φ z = 0 := fun z hz =>
    image_eq_zero_of_notMem_tsupport (hout z hz)
  have hφs0 : ∀ z : Vec3 × ℝ, z.2 ∉ Ioo a' b' → spatialPartial φ j z = 0 := fun z hz =>
    CKN.spatialPartial_eq_zero_off_tsupport (hout z hz) j
  have hsub : vlSlab a' b' ⊆ vlSlab a T := fun z hz =>
    ⟨hz.1, ⟨by linarith only [h1, hz.2.1], by linarith only [h3, hz.2.2]⟩⟩
  have hmeasT : MeasurableSet (vlSlab a T) := MeasurableSet.univ.prod measurableSet_Ioo
  have hred : ∀ H : Vec3 × ℝ → ℝ, (∀ z : Vec3 × ℝ, z.2 ∉ Ioo a' b' → H z = 0) →
      ∫ z in vlSlab a T, H z = ∫ z in vlSlab a' b', H z := fun H hH =>
    setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hmeasT hsub fun z hz =>
      hH z fun hz2 => hz.2 ⟨hz.1.1, hz2⟩
  rw [hred _ (fun z hz => by rw [hφs0 z hz, mul_zero]),
    hred _ (fun z hz => by rw [hφ0 z hz, mul_zero])]
  obtain ⟨hT0, hT1, -⟩ := lps_test_memLp_slab hφ j
  have hT0' := hT0.mono_measure (Measure.restrict_mono hsub le_rfl)
  have hT1' := hT1.mono_measure (Measure.restrict_mono hsub le_rfl)
  have hIf : Integrable (fun z => F z * spatialPartial φ j z) (volume.restrict (vlSlab a' b')) :=
    (hF a' b' h1 h2 h3).integrable_mul hT1'
  have hIg : Integrable (fun z => G z * φ z) (volume.restrict (vlSlab a' b')) :=
    (hG a' b' h1 h2 h3).integrable_mul hT0'
  rw [vlSlab_integral_eq hIf, vlSlab_integral_eq hIg, ← integral_neg]
  have hsl : ∀ᵐ t ∂(volume.restrict (Ioo a' b')),
      HasWeakPartialDerivOn (Set.univ : Set Vec3) j (fun x => F (x, t)) (fun x => G (x, t)) :=
    ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo h1.le h3.le) hslice
  refine integral_congr_ae ?_
  filter_upwards [hsl] with t ht
  obtain ⟨hs, hsc⟩ := lps_test_slice hφ.1 hφ.2.1 t
  have := ht (fun x => φ (x, t)) hs hsc (Set.subset_univ _)
  simp only [Measure.restrict_univ] at this
  exact this

end ESS.LPS

end
