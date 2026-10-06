/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.LocalStrongLimitRegularity

/-!
# Almost everywhere equality on a slab and on its time slices

Almost everywhere equality of two fields on a slab gives almost everywhere equality of almost every
time slice, and conversely for almost everywhere measurable fields (`prop:lps-local-strong`).
-/

public section

open MeasureTheory Set Filter Topology
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS.LPS

/-- Almost everywhere equality on a slab gives almost everywhere equality of almost every time
slice. -/
theorem lps_slab_slice_ae_eq {E : Type*} {a b : ℝ} {f g : Vec3 × ℝ → E}
    (h : f =ᵐ[volume.restrict (vlSlab a b)] g) :
    ∀ᵐ s ∂(volume.restrict (Ioo a b)),
      (fun x : Vec3 => f (x, s)) =ᵐ[volume] fun x => g (x, s) := by
  have hprod : f =ᵐ[(volume : Measure Vec3).prod (volume.restrict (Ioo a b))] g := by
    rw [vlSlab_measure] at h
    exact h
  have hswap : MeasurePreserving Prod.swap
      ((volume.restrict (Ioo a b)).prod (volume : Measure Vec3))
      ((volume : Measure Vec3).prod (volume.restrict (Ioo a b))) :=
    Measure.measurePreserving_swap
  have hswapEq := hswap.quasiMeasurePreserving.ae_eq_comp hprod
  exact Measure.ae_ae_of_ae_prod hswapEq

/-- Two almost everywhere measurable fields on a slab whose almost every time slices agree almost
everywhere agree almost everywhere on the slab. -/
theorem lps_slab_ae_eq_of_slices {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E] {a b : ℝ}
    {f g : Vec3 × ℝ → E}
    (hf : AEStronglyMeasurable f (volume.restrict (vlSlab a b)))
    (hg : AEStronglyMeasurable g (volume.restrict (vlSlab a b)))
    (h : ∀ᵐ s ∂(volume.restrict (Ioo a b)),
      (fun x : Vec3 => f (x, s)) =ᵐ[volume] fun x => g (x, s)) :
    f =ᵐ[volume.restrict (vlSlab a b)] g := by
  have hfs := lps_slab_slice_ae_eq hf.ae_eq_mk
  have hgs := lps_slab_slice_ae_eq hg.ae_eq_mk
  have hmeas : MeasurableSet {p : Vec3 × ℝ | hf.mk f p = hg.mk g p} :=
    measurableSet_eq_fun hf.stronglyMeasurable_mk.measurable hg.stronglyMeasurable_mk.measurable
  have hslice : ∀ᵐ s ∂(volume.restrict (Ioo a b)), ∀ᵐ x ∂(volume : Measure Vec3),
      hf.mk f (x, s) = hg.mk g (x, s) := by
    filter_upwards [hfs, hgs, h] with s h1 h2 h3
    filter_upwards [h1, h2, h3] with x x1 x2 x3
    rw [← x1, ← x2]
    exact x3
  have h4 := (Measure.ae_ae_comm hmeas).2 hslice
  have h5 : ∀ᵐ z ∂((volume : Measure Vec3).prod (volume.restrict (Ioo a b))),
      hf.mk f z = hg.mk g z :=
    (Measure.ae_prod_iff_ae_ae hmeas).2 h4
  rw [← vlSlab_measure] at h5
  have h6 : hf.mk f =ᵐ[volume.restrict (vlSlab a b)] hg.mk g := h5
  exact hf.ae_eq_mk.trans (h6.trans hg.ae_eq_mk.symm)

end ESS.LPS

end
