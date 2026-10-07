/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.MixedNormPairing
public import LeanPool.EscauriazaSereginSverak.PartV.SerrinCrossLimitTerms

/-!
# Mixed norm pairings on shorter time slabs

Finite mixed norm mollification limits restrict from a full time slab to
every shorter slab. This is the pairing limit used in cross-testing at an
almost every terminal time.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- The cutoff-weighted pairing of two spatial mollifications converges on
every shorter slab when the factors have conjugate finite mixed norms. -/
theorem lps_mixed_cutoff_pairing_limit_slab
    {T t px qx pt qt : ℝ} (ht : t ≤ T)
    (hpx1 : 1 ≤ px) (hqx1 : 1 ≤ qx)
    (hpt1 : 1 ≤ pt) (hqt1 : 1 ≤ qt)
    (hSpace : px.HolderConjugate qx)
    (hTime : pt.HolderConjugate qt)
    {f g : ParabolicPoint → ℝ}
    (hf : AEStronglyMeasurable f
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))))
    (hg : AEStronglyMeasurable g
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))))
    (hfSlice : ∀ᵐ τ ∂(volume.restrict (Ioo 0 T)),
      MemLp (fun x : Vec3 => f (x,τ)) (ENNReal.ofReal px) volume)
    (hgSlice : ∀ᵐ τ ∂(volume.restrict (Ioo 0 T)),
      MemLp (fun x : Vec3 => g (x,τ)) (ENNReal.ofReal qx) volume)
    (hfMoment : (∫⁻ τ in Ioo 0 T,
      eLpNorm (fun x : Vec3 => f (x,τ)) (ENNReal.ofReal px) volume ^ pt) < ⊤)
    (hgMoment : (∫⁻ τ in Ioo 0 T,
      eLpNorm (fun x : Vec3 => g (x,τ)) (ENNReal.ofReal qx) volume ^ qt) < ⊤) :
    (∀ᶠ n in atTop, Integrable
      (fun z : ParabolicPoint =>
        serrinCutoff n (parabolicHomeomorph z).1 * serrinSM f n z * serrinSM g n z)
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t)))) ∧
    Tendsto (fun n => ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t),
      serrinCutoff n (parabolicHomeomorph z).1 * serrinSM f n z * serrinSM g n z) atTop
      (𝓝 (∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t), f z * g z)) := by
  have hQ : spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t) ⊆
      spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T) := by
    intro z hz
    exact ⟨hz.1, hz.2.1, lt_of_lt_of_le hz.2.2 ht⟩
  have hf' : AEStronglyMeasurable f
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t))) :=
    hf.mono_measure (Measure.restrict_mono hQ le_rfl)
  have hg' : AEStronglyMeasurable g
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 t))) :=
    hg.mono_measure (Measure.restrict_mono hQ le_rfl)
  have hfSlice' : ∀ᵐ τ ∂(volume.restrict (Ioo 0 t)),
      MemLp (fun x : Vec3 => f (x,τ)) (ENNReal.ofReal px) volume := by
    exact ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo_right ht) hfSlice
  have hgSlice' : ∀ᵐ τ ∂(volume.restrict (Ioo 0 t)),
      MemLp (fun x : Vec3 => g (x,τ)) (ENNReal.ofReal qx) volume := by
    exact ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioo_right ht) hgSlice
  have hfMoment' : (∫⁻ τ in Ioo 0 t,
      eLpNorm (fun x : Vec3 => f (x,τ)) (ENNReal.ofReal px) volume ^ pt) < ⊤ := by
    refine lt_of_le_of_lt ?_ hfMoment
    exact lintegral_mono_set (Ioo_subset_Ioo_right ht)
  have hgMoment' : (∫⁻ τ in Ioo 0 t,
      eLpNorm (fun x : Vec3 => g (x,τ)) (ENNReal.ofReal qx) volume ^ qt) < ⊤ := by
    refine lt_of_le_of_lt ?_ hgMoment
    exact lintegral_mono_set (Ioo_subset_Ioo_right ht)
  simpa using (lps_mixed_cutoff_pairing_limit (T := t) hpx1 hqx1 hpt1 hqt1
    hSpace hTime hf' hg' hfSlice' hgSlice' hfMoment' hgMoment')

end ESS

end
