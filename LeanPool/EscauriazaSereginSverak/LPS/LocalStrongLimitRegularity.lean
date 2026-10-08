/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.LocalStrongLimitTimeCurves
public import LeanPool.CaffarelliKohnNirenberg.Statements.HasSpaceTimeWeakDerivs
public import Mathlib.MeasureTheory.SpecificCodomains.Pi

/-!
# Time regularity of a field with square-integrable derivatives

The continuous `L²` curves of a field and of its first gradient, for fields
that are only almost everywhere strongly measurable (`prop:lps-local-strong`).
-/

public section

open MeasureTheory Set Filter
open scoped Interval Topology ENNReal
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS.LPS

variable {a b : ℝ}

/-- Almost everywhere equality on a slab gives almost everywhere equality of
almost every time slice. -/
theorem lps_slab_ae_slice {f g : Vec3 × ℝ → ℝ}
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

/-- Almost everywhere equal factors give equal slab integrals against a
fixed weight. -/
theorem lps_slab_integral_mul_congr {f f' t : Vec3 × ℝ → ℝ}
    (hf : f =ᵐ[volume.restrict (vlSlab a b)] f') :
    ∫ p in vlSlab a b, f p * t p = ∫ p in vlSlab a b, f' p * t p := by
  refine integral_congr_ae ?_
  filter_upwards [hf] with z hz
  rw [hz]

/-- The field itself, for a field that is only almost everywhere strongly
measurable. -/
theorem lps_l2_time_curve_ae {w r : Vec3 × ℝ → ℝ} (hab : a < b)
    (hw : MemLp w 2 (volume.restrict (vlSlab a b)))
    (hr : MemLp r 2 (volume.restrict (vlSlab a b)))
    (hweak : ∀ φ ∈ CKN.spaceTimeTestFunction (V := ℝ) (univ : Set Vec3) (Ioo a b),
      ∫ p in vlSlab a b, w p * CKN.timePartial φ p =
        -∫ p in vlSlab a b, r p * φ p) :
    ∃ L : Icc a b → Lp ℝ 2 (volume : Measure Vec3), Continuous L ∧
      (∀ᵐ s ∂(volume.restrict (Ioo a b)), ∀ hs : s ∈ Icc a b,
        ((L ⟨s, hs⟩ : Lp ℝ 2 (volume : Measure Vec3)) : Vec3 → ℝ) =ᵐ[volume]
          fun x => w (x, s)) ∧
      ∀ (s t : ℝ) (hs : s ∈ Icc a b) (ht : t ∈ Icc a b), s ≤ t →
        ‖L ⟨t, ht⟩‖ ^ 2 - ‖L ⟨s, hs⟩‖ ^ 2 = 2 * ∫ z in vlSlab s t, w z * r z := by
  have hwe := hw.aestronglyMeasurable.ae_eq_mk
  have hre := hr.aestronglyMeasurable.ae_eq_mk
  set wm := hw.aestronglyMeasurable.mk w
  set rm := hr.aestronglyMeasurable.mk r
  have hwm : StronglyMeasurable wm := hw.aestronglyMeasurable.stronglyMeasurable_mk
  have hrm : StronglyMeasurable rm := hr.aestronglyMeasurable.stronglyMeasurable_mk
  have hw' : MemLp wm 2 (volume.restrict (vlSlab a b)) := hw.ae_eq hwe
  have hr' : MemLp rm 2 (volume.restrict (vlSlab a b)) := hr.ae_eq hre
  have hweak' : ∀ φ ∈ CKN.spaceTimeTestFunction (V := ℝ) (univ : Set Vec3) (Ioo a b),
      ∫ p in vlSlab a b, wm p * CKN.timePartial φ p =
        -∫ p in vlSlab a b, rm p * φ p := by
    intro φ hφ
    rw [lps_slab_integral_mul_congr (t := fun p => CKN.timePartial φ p) hwe.symm,
      lps_slab_integral_mul_congr (t := φ) hre.symm]
    exact hweak φ hφ
  obtain ⟨L, hLc, hLq, hLid⟩ := lps_l2_time_curve hab hwm hrm hw' hr' hweak'
  refine ⟨L, hLc, ?_, fun s t hs ht hst => ?_⟩
  · filter_upwards [hLq, lps_slab_ae_slice hwe.symm] with s h1 h2 hs
    exact (h1 hs).trans h2
  · rw [hLid s t hs ht hst]
    congr 1
    have hsub : vlSlab s t ⊆ vlSlab a b := prod_mono subset_rfl (Ioo_subset_Ioo hs.1 ht.2)
    refine integral_congr_ae ?_
    have hwe' := ae_restrict_of_ae_restrict_of_subset hsub hwe
    have hre' := ae_restrict_of_ae_restrict_of_subset hsub hre
    filter_upwards [hwe', hre'] with z h1 h2
    rw [← h1, ← h2]

/-- The specified first gradient, for fields that are only almost everywhere
strongly measurable. -/
theorem lps_gradient_time_curve_ae {w r g h : Vec3 × ℝ → ℝ} (hab : a < b) (j : Fin 3)
    (hw : MemLp w 2 (volume.restrict (vlSlab a b)))
    (hr : MemLp r 2 (volume.restrict (vlSlab a b)))
    (hg : MemLp g 2 (volume.restrict (vlSlab a b)))
    (hh : MemLp h 2 (volume.restrict (vlSlab a b)))
    (hweak : ∀ φ ∈ CKN.spaceTimeTestFunction (V := ℝ) (univ : Set Vec3) (Ioo a b),
      ∫ p in vlSlab a b, w p * CKN.timePartial φ p =
        -∫ p in vlSlab a b, r p * φ p)
    (hgrad : ∀ φ ∈ CKN.spaceTimeTestFunction (V := ℝ) (univ : Set Vec3) (Ioo a b),
      ∫ p in vlSlab a b, w p * CKN.spatialPartial φ j p =
        -∫ p in vlSlab a b, g p * φ p)
    (hhess : ∀ φ ∈ CKN.spaceTimeTestFunction (V := ℝ) (univ : Set Vec3) (Ioo a b),
      ∫ p in vlSlab a b, g p * CKN.spatialPartial φ j p =
        -∫ p in vlSlab a b, h p * φ p) :
    ∃ L : Icc a b → Lp ℝ 2 (volume : Measure Vec3), Continuous L ∧
      (∀ᵐ s ∂(volume.restrict (Ioo a b)), ∀ hs : s ∈ Icc a b,
        ((L ⟨s, hs⟩ : Lp ℝ 2 (volume : Measure Vec3)) : Vec3 → ℝ) =ᵐ[volume]
          fun x => g (x, s)) ∧
      ∀ (s t : ℝ) (hs : s ∈ Icc a b) (ht : t ∈ Icc a b), s ≤ t →
        ‖L ⟨t, ht⟩‖ ^ 2 - ‖L ⟨s, hs⟩‖ ^ 2 = -(2 * ∫ z in vlSlab s t, h z * r z) := by
  have hwe := hw.aestronglyMeasurable.ae_eq_mk
  have hre := hr.aestronglyMeasurable.ae_eq_mk
  have hge := hg.aestronglyMeasurable.ae_eq_mk
  have hhe := hh.aestronglyMeasurable.ae_eq_mk
  set wm := hw.aestronglyMeasurable.mk w
  set rm := hr.aestronglyMeasurable.mk r
  set gm := hg.aestronglyMeasurable.mk g
  set hm := hh.aestronglyMeasurable.mk h
  have hwm : StronglyMeasurable wm := hw.aestronglyMeasurable.stronglyMeasurable_mk
  have hrm : StronglyMeasurable rm := hr.aestronglyMeasurable.stronglyMeasurable_mk
  have hgm : StronglyMeasurable gm := hg.aestronglyMeasurable.stronglyMeasurable_mk
  have hhm : StronglyMeasurable hm := hh.aestronglyMeasurable.stronglyMeasurable_mk
  have hw' : MemLp wm 2 (volume.restrict (vlSlab a b)) := hw.ae_eq hwe
  have hr' : MemLp rm 2 (volume.restrict (vlSlab a b)) := hr.ae_eq hre
  have hg' : MemLp gm 2 (volume.restrict (vlSlab a b)) := hg.ae_eq hge
  have hh' : MemLp hm 2 (volume.restrict (vlSlab a b)) := hh.ae_eq hhe
  have hweak' : ∀ φ ∈ CKN.spaceTimeTestFunction (V := ℝ) (univ : Set Vec3) (Ioo a b),
      ∫ p in vlSlab a b, wm p * CKN.timePartial φ p =
        -∫ p in vlSlab a b, rm p * φ p := by
    intro φ hφ
    rw [lps_slab_integral_mul_congr (t := fun p => CKN.timePartial φ p) hwe.symm,
      lps_slab_integral_mul_congr (t := φ) hre.symm]
    exact hweak φ hφ
  have hgrad' : ∀ φ ∈ CKN.spaceTimeTestFunction (V := ℝ) (univ : Set Vec3) (Ioo a b),
      ∫ p in vlSlab a b, wm p * CKN.spatialPartial φ j p =
        -∫ p in vlSlab a b, gm p * φ p := by
    intro φ hφ
    rw [lps_slab_integral_mul_congr (t := fun p => CKN.spatialPartial φ j p) hwe.symm,
      lps_slab_integral_mul_congr (t := φ) hge.symm]
    exact hgrad φ hφ
  have hhess' : ∀ φ ∈ CKN.spaceTimeTestFunction (V := ℝ) (univ : Set Vec3) (Ioo a b),
      ∫ p in vlSlab a b, gm p * CKN.spatialPartial φ j p =
        -∫ p in vlSlab a b, hm p * φ p := by
    intro φ hφ
    rw [lps_slab_integral_mul_congr (t := fun p => CKN.spatialPartial φ j p) hge.symm,
      lps_slab_integral_mul_congr (t := φ) hhe.symm]
    exact hhess φ hφ
  obtain ⟨L, hLc, hLq, hLid⟩ := lps_gradient_time_curve hab j hwm hrm hgm hhm hw' hr' hg' hh'
    hweak' hgrad' hhess'
  refine ⟨L, hLc, ?_, fun s t hs ht hst => ?_⟩
  · filter_upwards [hLq, lps_slab_ae_slice hge.symm] with s h1 h2 hs
    exact (h1 hs).trans h2
  · rw [hLid s t hs ht hst]
    congr 2
    have hsub : vlSlab s t ⊆ vlSlab a b := prod_mono subset_rfl (Ioo_subset_Ioo hs.1 ht.2)
    refine integral_congr_ae ?_
    have hhe' := ae_restrict_of_ae_restrict_of_subset hsub hhe
    have hre' := ae_restrict_of_ae_restrict_of_subset hsub hre
    filter_upwards [hhe', hre'] with z h1 h2
    rw [← h1, ← h2]

/-- Time regularity of a field, its first gradient, second gradient and time
derivative that are square integrable on a slab with the space-time weak
derivative relations: continuous `L²` representatives with the energy
identities (`prop:lps-local-strong`). -/
theorem lps_strong_time_regularity {t₀ T : ℝ} (hT : t₀ < T)
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {D2u : ParabolicPoint → Fin 3 → Fin 3 → Vec3} {Dtu : ParabolicPoint → Vec3}
    (hDerivs : HasSpaceTimeWeakDerivs (Set.univ : Set Vec3) (Ioo t₀ T) u Du D2u Dtu)
    (hMemU : MemLp u 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ T))))
    (hMemDu : MemLp Du 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ T))))
    (hMemD2u : MemLp D2u 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ T))))
    (hMemDtu : MemLp Dtu 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ T)))) :
    ∃ (Lu : Fin 3 → Icc t₀ T → Lp ℝ 2 (volume : Measure Vec3))
      (LD : Fin 3 → Fin 3 → Icc t₀ T → Lp ℝ 2 (volume : Measure Vec3)),
      (∀ i, Continuous (Lu i)) ∧ (∀ i j, Continuous (LD i j)) ∧
      (∀ i, ∀ᵐ s ∂(volume.restrict (Ioo t₀ T)), ∀ hs : s ∈ Icc t₀ T,
        ((Lu i ⟨s, hs⟩ : Lp ℝ 2 (volume : Measure Vec3)) : Vec3 → ℝ) =ᵐ[volume]
          fun x => u (x, s) i) ∧
      (∀ i j, ∀ᵐ s ∂(volume.restrict (Ioo t₀ T)), ∀ hs : s ∈ Icc t₀ T,
        ((LD i j ⟨s, hs⟩ : Lp ℝ 2 (volume : Measure Vec3)) : Vec3 → ℝ) =ᵐ[volume]
          fun x => Du (x, s) i j) ∧
      (∀ (s t : ℝ) (hs : s ∈ Icc t₀ T) (ht : t ∈ Icc t₀ T), s ≤ t →
        ∑ i : Fin 3, (‖Lu i ⟨t, ht⟩‖ ^ 2 - ‖Lu i ⟨s, hs⟩‖ ^ 2) =
          2 * ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo s t),
            ∑ i : Fin 3, u z i * Dtu z i) ∧
      (∀ (s t : ℝ) (hs : s ∈ Icc t₀ T) (ht : t ∈ Icc t₀ T), s ≤ t →
        ∑ i : Fin 3, ∑ j : Fin 3, (‖LD i j ⟨t, ht⟩‖ ^ 2 - ‖LD i j ⟨s, hs⟩‖ ^ 2) =
          -(2 * ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo s t),
            ∑ i : Fin 3, Dtu z i * ∑ j : Fin 3, D2u z i j j)) := by
  have hslab : spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ T) = vlSlab t₀ T := rfl
  rw [hslab] at hMemU hMemDu hMemD2u hMemDtu
  obtain ⟨_, _, _, _, hweak⟩ := hDerivs
  have hu : ∀ i, MemLp (fun z : Vec3 × ℝ => u z i) 2 (volume.restrict (vlSlab t₀ T)) :=
    fun i => memLp_pi_iff.1 hMemU i
  have hDt : ∀ i, MemLp (fun z : Vec3 × ℝ => Dtu z i) 2 (volume.restrict (vlSlab t₀ T)) :=
    fun i => memLp_pi_iff.1 hMemDtu i
  have hDu : ∀ i j, MemLp (fun z : Vec3 × ℝ => Du z i j) 2
      (volume.restrict (vlSlab t₀ T)) :=
    fun i j => memLp_pi_iff.1 (memLp_pi_iff.1 hMemDu i) j
  have hD2 : ∀ i j, MemLp (fun z : Vec3 × ℝ => D2u z i j j) 2
      (volume.restrict (vlSlab t₀ T)) :=
    fun i j => memLp_pi_iff.1 (memLp_pi_iff.1 (memLp_pi_iff.1 hMemD2u i) j) j
  have hcurveU : ∀ i, ∃ L : Icc t₀ T → Lp ℝ 2 (volume : Measure Vec3), Continuous L ∧
      (∀ᵐ s ∂(volume.restrict (Ioo t₀ T)), ∀ hs : s ∈ Icc t₀ T,
        ((L ⟨s, hs⟩ : Lp ℝ 2 (volume : Measure Vec3)) : Vec3 → ℝ) =ᵐ[volume]
          fun x => u (x, s) i) ∧
      ∀ (s t : ℝ) (hs : s ∈ Icc t₀ T) (ht : t ∈ Icc t₀ T), s ≤ t →
        ‖L ⟨t, ht⟩‖ ^ 2 - ‖L ⟨s, hs⟩‖ ^ 2 =
          2 * ∫ z in vlSlab s t, u z i * Dtu z i :=
    fun i => lps_l2_time_curve_ae hT (hu i) (hDt i)
      (fun φ hφ => (hweak φ hφ).2.2 i)
  have hcurveD : ∀ i j, ∃ L : Icc t₀ T → Lp ℝ 2 (volume : Measure Vec3), Continuous L ∧
      (∀ᵐ s ∂(volume.restrict (Ioo t₀ T)), ∀ hs : s ∈ Icc t₀ T,
        ((L ⟨s, hs⟩ : Lp ℝ 2 (volume : Measure Vec3)) : Vec3 → ℝ) =ᵐ[volume]
          fun x => Du (x, s) i j) ∧
      ∀ (s t : ℝ) (hs : s ∈ Icc t₀ T) (ht : t ∈ Icc t₀ T), s ≤ t →
        ‖L ⟨t, ht⟩‖ ^ 2 - ‖L ⟨s, hs⟩‖ ^ 2 =
          -(2 * ∫ z in vlSlab s t, D2u z i j j * Dtu z i) :=
    fun i j => lps_gradient_time_curve_ae hT j (hu i) (hDt i) (hDu i j) (hD2 i j)
      (fun φ hφ => (hweak φ hφ).2.2 i) (fun φ hφ => (hweak φ hφ).1 i j)
      (fun φ hφ => (hweak φ hφ).2.1 i j j)
  choose Lu hLuc hLuq hLuid using hcurveU
  choose LD hLDc hLDq hLDid using hcurveD
  refine ⟨Lu, LD, hLuc, hLDc, hLuq, hLDq, fun s t hs ht hst => ?_, fun s t hs ht hst => ?_⟩
  · have hsub : vlSlab s t ⊆ vlSlab t₀ T := prod_mono subset_rfl (Ioo_subset_Ioo hs.1 ht.2)
    have hint : ∀ i, Integrable (fun z : Vec3 × ℝ => u z i * Dtu z i)
        (volume.restrict (vlSlab s t)) := fun i =>
      ((hu i).mono_measure (Measure.restrict_mono hsub le_rfl)).integrable_mul
        ((hDt i).mono_measure (Measure.restrict_mono hsub le_rfl))
    simp_rw [hLuid _ s t hs ht hst]
    change ∑ i : Fin 3, 2 * ∫ z in vlSlab s t, u z i * Dtu z i =
      2 * ∫ z in vlSlab s t, ∑ i : Fin 3, u z i * Dtu z i
    rw [integral_finsetSum _ (fun i _ => hint i), Finset.mul_sum]
  · have hsub : vlSlab s t ⊆ vlSlab t₀ T := prod_mono subset_rfl (Ioo_subset_Ioo hs.1 ht.2)
    have hint : ∀ i j, Integrable (fun z : Vec3 × ℝ => D2u z i j j * Dtu z i)
        (volume.restrict (vlSlab s t)) := fun i j =>
      ((hD2 i j).mono_measure (Measure.restrict_mono hsub le_rfl)).integrable_mul
        ((hDt i).mono_measure (Measure.restrict_mono hsub le_rfl))
    simp_rw [hLDid _ _ s t hs ht hst]
    change ∑ i : Fin 3, ∑ j : Fin 3, -(2 * ∫ z in vlSlab s t, D2u z i j j * Dtu z i) =
      -(2 * ∫ z in vlSlab s t, ∑ i : Fin 3, Dtu z i * ∑ j : Fin 3, D2u z i j j)
    have hsum : ∫ z : Vec3 × ℝ in vlSlab s t,
          ∑ i : Fin 3, Dtu z i * ∑ j : Fin 3, D2u z i j j =
        ∑ i : Fin 3, ∑ j : Fin 3, ∫ z : Vec3 × ℝ in vlSlab s t, D2u z i j j * Dtu z i := by
      have h1 : (fun z : Vec3 × ℝ => ∑ i : Fin 3, Dtu z i * ∑ j : Fin 3, D2u z i j j) =
          fun z => ∑ i : Fin 3, ∑ j : Fin 3, D2u z i j j * Dtu z i := by
        funext z
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => mul_comm _ _
      have hint2 : ∀ i ∈ (Finset.univ : Finset (Fin 3)), Integrable
          (fun z : Vec3 × ℝ => ∑ j : Fin 3, D2u z i j j * Dtu z i)
          (volume.restrict (vlSlab s t)) :=
        fun i _ => integrable_finsetSum Finset.univ fun j _ => hint i j
      rw [h1]
      exact (integral_finsetSum Finset.univ hint2).trans
        (Finset.sum_congr rfl fun i _ => integral_finsetSum Finset.univ fun j _ => hint i j)
    rw [hsum, Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]

end ESS.LPS

end
