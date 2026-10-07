/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.LocalStrongKineticMollified
public import LeanPool.EscauriazaSereginSverak.LPS.LocalStrongLimitRegularity

/-!
# Convolution identities on almost every slice

Kernel-convolution identities that hold at every point of space for almost
every time also hold for almost every time at almost every point of space,
for fields that are only almost everywhere strongly measurable
(`prop:lps-local-strong`).
-/

public section

open MeasureTheory Set Filter
open scoped Interval Topology ENNReal
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS.LPS

variable {a b : ℝ}

/-- Convolutions of almost everywhere equal slab fields agree at every point
for almost every time. -/
theorem lps_vlConvT_congr_ae_time {f f' : Vec3 × ℝ → ℝ}
    (h : f =ᵐ[volume.restrict (vlSlab a b)] f') (k : Vec3 → ℝ) :
    ∀ᵐ t ∂(volume.restrict (Ioo a b)), ∀ x : Vec3,
      vlConvT k f x t = vlConvT k f' x t := by
  filter_upwards [lps_slab_ae_slice h] with t ht x
  simp only [vlConvT, vlConv_apply_swap]
  refine integral_congr_ae ?_
  filter_upwards [ht] with y hy
  rw [hy]

/-- The first spatial derivative of a slab field as an identity between kernel
convolutions, for almost every time and almost every point, for fields that are
only almost everywhere strongly measurable. -/
theorem lps_conv_first_deriv_ae_aem {w g : Vec3 × ℝ → ℝ} (j : Fin 3)
    (hw : MemLp w 2 (volume.restrict (vlSlab a b)))
    (hg : MemLp g 2 (volume.restrict (vlSlab a b)))
    (hgrad : ∀ φ ∈ CKN.spaceTimeTestFunction (V := ℝ) (univ : Set Vec3) (Ioo a b),
      ∫ p in vlSlab a b, w p * CKN.spatialPartial φ j p =
        -∫ p in vlSlab a b, g p * φ p)
    {κ : Vec3 → ℝ} (hκ : IsVlKernel κ) :
    ∀ᵐ s ∂(volume.restrict (Ioo a b)), ∀ᵐ x ∂(volume : Measure Vec3),
      vlConvT (vlDeriv κ j) w x s = vlConvT κ g x s := by
  have hwe := hw.aestronglyMeasurable.ae_eq_mk
  have hge := hg.aestronglyMeasurable.ae_eq_mk
  set wm := hw.aestronglyMeasurable.mk w
  set gm := hg.aestronglyMeasurable.mk g
  have hwm : StronglyMeasurable wm := hw.aestronglyMeasurable.stronglyMeasurable_mk
  have hgm : StronglyMeasurable gm := hg.aestronglyMeasurable.stronglyMeasurable_mk
  have hw' : MemLp wm 2 (volume.restrict (vlSlab a b)) := hw.ae_eq hwe
  have hg' : MemLp gm 2 (volume.restrict (vlSlab a b)) := hg.ae_eq hge
  have hgrad' : ∀ φ ∈ CKN.spaceTimeTestFunction (V := ℝ) (univ : Set Vec3) (Ioo a b),
      ∫ p in vlSlab a b, wm p * CKN.spatialPartial φ j p =
        -∫ p in vlSlab a b, gm p * φ p := by
    intro φ hφ
    rw [lps_slab_integral_mul_congr (t := fun p => CKN.spatialPartial φ j p) hwe.symm,
      lps_slab_integral_mul_congr (t := φ) hge.symm]
    exact hgrad φ hφ
  filter_upwards [lps_conv_first_deriv_ae j hwm hgm hw' hg' hgrad' hκ,
    lps_vlConvT_congr_ae_time hwe (vlDeriv κ j), lps_vlConvT_congr_ae_time hge κ]
    with s h1 h2 h3
  filter_upwards [h1] with x hx
  rw [h2 x, h3 x]
  exact hx

/-- The mollified strong equation holds for almost every time at almost every
point of space (`prop:lps-local-strong`). -/
theorem lps_strong_mollified_equation_slice
    {t₀ T : ℝ} {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hU : IsLpsStrongSolution t₀ T u Du p)
    {D2u : ParabolicPoint → Fin 3 → Fin 3 → Vec3} {Dtu : ParabolicPoint → Vec3}
    (hDerivs : HasSpaceTimeWeakDerivs (Set.univ : Set Vec3) (Ioo t₀ T) u Du D2u Dtu)
    (hu : ∀ i, MemLp (fun z : Vec3 × ℝ => u z i) 2 (volume.restrict (vlSlab t₀ T)))
    (hDu : ∀ i j, MemLp (fun z : Vec3 × ℝ => Du z i j) 2
      (volume.restrict (vlSlab t₀ T)))
    (hD2 : ∀ i j, MemLp (fun z : Vec3 × ℝ => D2u z i j j) 2
      (volume.restrict (vlSlab t₀ T)))
    (hDt : ∀ i, MemLp (fun z : Vec3 × ℝ => Dtu z i) 2 (volume.restrict (vlSlab t₀ T)))
    (hp : MemLp p 2 (volume.restrict (vlSlab t₀ T)))
    (i : Fin 3) {κ : Vec3 → ℝ} (hκ : IsVlKernel κ) :
    ∀ᵐ t ∂(volume.restrict (Ioo t₀ T)), ∀ᵐ x ∂(volume : Measure Vec3),
      vlConvT κ (fun z : Vec3 × ℝ => Dtu z i) x t +
        ∑ j : Fin 3, vlConvT (vlDeriv κ j) (fun z : Vec3 × ℝ => u z i * u z j) x t -
        ∑ j : Fin 3, vlConvT κ (fun z : Vec3 × ℝ => D2u z i j j) x t +
        vlConvT (vlDeriv κ i) p x t = 0 := by
  have hF : ∀ j, Integrable (fun z : Vec3 × ℝ => u z i * u z j)
      (volume.restrict (vlSlab t₀ T)) := fun j => (hu i).integrable_mul (hu j)
  set A : Vec3 × ℝ → ℝ := fun z => Dtu z i with hAdef
  set B : Fin 3 → Vec3 × ℝ → ℝ := fun j z => u z i * u z j with hBdef
  set C : Fin 3 → Vec3 × ℝ → ℝ := fun j z => D2u z i j j with hCdef
  have hAe := (hDt i).aestronglyMeasurable.ae_eq_mk
  have hBe := fun j => (hF j).aestronglyMeasurable.ae_eq_mk
  have hCe := fun j => (hD2 i j).aestronglyMeasurable.ae_eq_mk
  have hDe := hp.aestronglyMeasurable.ae_eq_mk
  set A' := (hDt i).aestronglyMeasurable.mk A
  set B' : Fin 3 → Vec3 × ℝ → ℝ := fun j => (hF j).aestronglyMeasurable.mk (B j)
  set C' : Fin 3 → Vec3 × ℝ → ℝ := fun j => (hD2 i j).aestronglyMeasurable.mk (C j)
  set D' := hp.aestronglyMeasurable.mk p
  have hA'm : StronglyMeasurable A' := (hDt i).aestronglyMeasurable.stronglyMeasurable_mk
  have hB'm : ∀ j, StronglyMeasurable (B' j) := fun j =>
    (hF j).aestronglyMeasurable.stronglyMeasurable_mk
  have hC'm : ∀ j, StronglyMeasurable (C' j) := fun j =>
    (hD2 i j).aestronglyMeasurable.stronglyMeasurable_mk
  have hD'm : StronglyMeasurable D' := hp.aestronglyMeasurable.stronglyMeasurable_mk
  let E' : Vec3 × ℝ → ℝ := fun q =>
    vlConvT κ A' q.1 q.2 + ∑ j : Fin 3, vlConvT (vlDeriv κ j) (B' j) q.1 q.2 -
      ∑ j : Fin 3, vlConvT κ (C' j) q.1 q.2 + vlConvT (vlDeriv κ i) D' q.1 q.2
  have hE'm : StronglyMeasurable E' := by
    refine (((vlConvT_stronglyMeasurable hκ.continuous hA'm).add ?_).sub ?_).add
      (vlConvT_stronglyMeasurable (hκ.deriv i).continuous hD'm)
    · exact Finset.stronglyMeasurable_fun_sum _ fun j _ =>
        vlConvT_stronglyMeasurable (hκ.deriv j).continuous (hB'm j)
    · exact Finset.stronglyMeasurable_fun_sum _ fun j _ =>
        vlConvT_stronglyMeasurable hκ.continuous (hC'm j)
  have hall : ∀ᵐ t ∂(volume.restrict (Ioo t₀ T)), ∀ x : Vec3,
      (vlConvT κ A x t + ∑ j : Fin 3, vlConvT (vlDeriv κ j) (B j) x t -
        ∑ j : Fin 3, vlConvT κ (C j) x t + vlConvT (vlDeriv κ i) p x t) = E' (x, t) := by
    filter_upwards [lps_vlConvT_congr_ae_time hAe κ,
      ae_all_iff.2 fun j => lps_vlConvT_congr_ae_time (hBe j) (vlDeriv κ j),
      ae_all_iff.2 fun j => lps_vlConvT_congr_ae_time (hCe j) κ,
      lps_vlConvT_congr_ae_time hDe (vlDeriv κ i)] with t h1 h2 h3 h4 x
    have e2 : ∑ j : Fin 3, vlConvT (vlDeriv κ j) (B j) x t =
        ∑ j : Fin 3, vlConvT (vlDeriv κ j) (B' j) x t :=
      Finset.sum_congr rfl fun j _ => h2 j x
    have e3 : ∑ j : Fin 3, vlConvT κ (C j) x t = ∑ j : Fin 3, vlConvT κ (C' j) x t :=
      Finset.sum_congr rfl fun j _ => h3 j x
    simp only [E']
    rw [h1 x, e2, e3, h4 x]
  have hx : ∀ x : Vec3, ∀ᵐ t ∂(volume.restrict (Ioo t₀ T)), E' (x, t) = 0 := by
    intro x
    filter_upwards [lps_strong_mollified_equation hU hDerivs hu hDu hD2 hDt hp i hκ x, hall]
      with t h0 h1
    rw [← h1 x]
    exact h0
  have hswap := lps_ae_slice_of_ae_time (a := t₀) (b := T) (F := E') (G := fun _ => 0)
    hE'm stronglyMeasurable_const hx
  filter_upwards [hswap, hall] with t h1 h2
  filter_upwards [h1] with x hx'
  rw [h2 x]
  exact hx'

end ESS.LPS

end
