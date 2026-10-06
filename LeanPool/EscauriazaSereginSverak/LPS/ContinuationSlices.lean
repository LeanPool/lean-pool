/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.H1EstimateTestField

/-!
# Almost-everywhere equality on a slab and on its time slices

Almost-everywhere equality of two measurable fields on a slab is equivalent to
almost-everywhere equality of almost every pair of time slices
(`lem:lps-continuation`).
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- Almost-everywhere statements on a slab transfer to the product slab measure. -/
theorem lps_ae_slab_to_prod {a b : ℝ} {P : ParabolicPoint → Prop}
    (h : ∀ᵐ z ∂(volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo a b))), P z) :
    ∀ᵐ q ∂((volume : Measure Vec3).prod (volume.restrict (Ioo a b))),
      P (parabolicHomeomorph.symm q) := by
  have hSmeas : MeasurableSet (spaceTimeSet (Set.univ : Set Vec3) (Ioo a b)) :=
    MeasurableSet.univ.prod measurableSet_Ioo
  have hpre : parabolicHomeomorph.symm ⁻¹' spaceTimeSet (Set.univ : Set Vec3) (Ioo a b) =
      (Set.univ : Set Vec3) ×ˢ Ioo a b := by
    ext z
    rfl
  have hmp := CKN.parabolicHomeomorphSymm_measurePreserving.restrict_preimage hSmeas
  rw [hpre] at hmp
  have hslab : (volume : Measure (Vec3 × ℝ)).restrict ((Set.univ : Set Vec3) ×ˢ Ioo a b) =
      (volume : Measure Vec3).prod (volume.restrict (Ioo a b)) := by
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]
  rw [← hslab]
  exact hmp.quasiMeasurePreserving.ae h

/-- The converse transfer to the product slab measure. -/
theorem lps_ae_prod_to_slab {a b : ℝ} {P : ParabolicPoint → Prop}
    (h : ∀ᵐ q ∂((volume : Measure Vec3).prod (volume.restrict (Ioo a b))),
      P (parabolicHomeomorph.symm q)) :
    ∀ᵐ z ∂(volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo a b))), P z := by
  have hSmeas : MeasurableSet (spaceTimeSet (Set.univ : Set Vec3) (Ioo a b)) :=
    MeasurableSet.univ.prod measurableSet_Ioo
  have hpre : parabolicHomeomorph.symm ⁻¹' spaceTimeSet (Set.univ : Set Vec3) (Ioo a b) =
      (Set.univ : Set Vec3) ×ˢ Ioo a b := by
    ext z
    rfl
  have hmp := CKN.parabolicHomeomorphSymm_measurePreserving.restrict_preimage hSmeas
  rw [hpre] at hmp
  have hslab : (volume : Measure (Vec3 × ℝ)).restrict ((Set.univ : Set Vec3) ×ˢ Ioo a b) =
      (volume : Measure Vec3).prod (volume.restrict (Ioo a b)) := by
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]
  rw [← hslab] at h
  have hemb : MeasurableEmbedding (parabolicHomeomorph.symm : Vec3 × ℝ → ParabolicPoint) :=
    parabolicHomeomorph.symm.measurableEmbedding
  rw [← hmp.map_eq]
  exact hemb.ae_map_iff.mpr h

/-- From almost-everywhere validity on `ℝ³ × (a,b)` to almost every time slice. -/
theorem lps_ae_slices_of_prod {a b : ℝ} {P : Vec3 × ℝ → Prop}
    (h : ∀ᵐ q ∂((volume : Measure Vec3).prod (volume.restrict (Ioo a b))), P q) :
    ∀ᵐ t ∂(volume.restrict (Ioo a b)), ∀ᵐ x ∂(volume : Measure Vec3), P (x, t) := by
  have hsw : ∀ᵐ z ∂((volume.restrict (Ioo a b) : Measure ℝ).prod (volume : Measure Vec3)),
      P z.swap :=
    (Measure.measurePreserving_swap (μ := (volume.restrict (Ioo a b) : Measure ℝ))
      (ν := (volume : Measure Vec3))).quasiMeasurePreserving.ae h
  exact Measure.ae_ae_of_ae_prod hsw

/-- From almost every time slice to almost-everywhere validity, for a measurable
condition. -/
theorem lps_ae_prod_of_slices {a b : ℝ} {P : Vec3 × ℝ → Prop} (hP : MeasurableSet {q | P q})
    (h : ∀ᵐ t ∂(volume.restrict (Ioo a b)), ∀ᵐ x ∂(volume : Measure Vec3), P (x, t)) :
    ∀ᵐ q ∂((volume : Measure Vec3).prod (volume.restrict (Ioo a b))), P q := by
  have hmeas : MeasurableSet {z : ℝ × Vec3 | P z.swap} := hP.preimage measurable_swap
  have h1 : ∀ᵐ z ∂((volume.restrict (Ioo a b) : Measure ℝ).prod (volume : Measure Vec3)),
      P z.swap := (Measure.ae_prod_iff_ae_ae hmeas).mpr h
  have := (Measure.measurePreserving_swap (μ := (volume : Measure Vec3))
    (ν := (volume.restrict (Ioo a b) : Measure ℝ))).quasiMeasurePreserving.ae h1
  simpa using this

/-- Almost-everywhere equality on a slab gives almost-everywhere equality of almost
every pair of time slices. -/
theorem lps_slices_ae_eq_of_slab {a b : ℝ} {E : Type} {F G : ParabolicPoint → E}
    (h : F =ᵐ[volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo a b))] G) :
    ∀ᵐ t ∂(volume.restrict (Ioo a b)),
      (fun x : Vec3 => F (x, t)) =ᵐ[volume] (fun x : Vec3 => G (x, t)) := by
  have hq := lps_ae_slab_to_prod (P := fun z => F z = G z) h
  exact lps_ae_slices_of_prod (P := fun q => F (parabolicHomeomorph.symm q) =
    G (parabolicHomeomorph.symm q)) hq

/-- Almost-everywhere equality of almost every pair of time slices gives
almost-everywhere equality on the slab, for square-integrable fields. -/
theorem lps_slab_ae_eq_of_slices {a b : ℝ} {E : Type} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] {F G : ParabolicPoint → E}
    (hF : MemLp F 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo a b))))
    (hG : MemLp G 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo a b))))
    (h : ∀ᵐ t ∂(volume.restrict (Ioo a b)),
      (fun x : Vec3 => F (x, t)) =ᵐ[volume] (fun x : Vec3 => G (x, t))) :
    F =ᵐ[volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo a b))] G := by
  have hFν := (lps_memLp_slab_to_prod hF).aestronglyMeasurable
  have hGν := (lps_memLp_slab_to_prod hG).aestronglyMeasurable
  set F' := hFν.mk with hF'
  set G' := hGν.mk with hG'
  have sF := lps_ae_slices_of_prod (P := fun q => F (parabolicHomeomorph.symm q) = F' q)
    hFν.ae_eq_mk
  have sG := lps_ae_slices_of_prod (P := fun q => G (parabolicHomeomorph.symm q) = G' q)
    hGν.ae_eq_mk
  have hslice : ∀ᵐ t ∂(volume.restrict (Ioo a b)),
      ∀ᵐ x ∂(volume : Measure Vec3), F' (x, t) = G' (x, t) := by
    filter_upwards [sF, sG, h] with t h1 h2 h3
    filter_upwards [h1, h2, h3] with x hx1 hx2 hx3
    rw [← hx1, ← hx2]
    exact hx3
  have hmeas : MeasurableSet {q : Vec3 × ℝ | F' q = G' q} :=
    measurableSet_eq_fun hFν.stronglyMeasurable_mk.measurable hGν.stronglyMeasurable_mk.measurable
  have hprod := lps_ae_prod_of_slices (P := fun q => F' q = G' q) hmeas hslice
  have hfin : ∀ᵐ q ∂((volume : Measure Vec3).prod (volume.restrict (Ioo a b))),
      F (parabolicHomeomorph.symm q) = G (parabolicHomeomorph.symm q) := by
    filter_upwards [hFν.ae_eq_mk, hGν.ae_eq_mk, hprod] with q h1 h2 h3
    rw [h1, h2]
    exact h3
  exact lps_ae_prod_to_slab (P := fun z => F z = G z) hfin

end ESS

end
