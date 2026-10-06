/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.ContinuationConcatEq
public import LeanPool.EscauriazaSereginSverak.LPS.ContinuationSlices
public import LeanPool.EscauriazaSereginSverak.LPS.ContinuationGradient

/-!
# Matching a strong solution with a Leray–Hopf solution

A strong solution that agrees almost everywhere with a Leray–Hopf solution on a
slab has the same gradient there, and its slice at the end time agrees with the
Leray–Hopf slice in the weak sense (`lem:lps-continuation`).
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- Weak gradients of almost everywhere equal square-integrable functions agree
almost everywhere. -/
theorem lps_weak_gradient_ae_eq {f g : Vec3 → ℝ} {G G' : Vec3 → Vec3}
    (hf : HasWeakGradientOn (Set.univ : Set Vec3) f G)
    (hg : HasWeakGradientOn (Set.univ : Set Vec3) g G')
    (hfg : f =ᵐ[volume] g) (hG : MemLp G 2 volume) (hG' : MemLp G' 2 volume) :
    G =ᵐ[volume] G' := by
  have hcomp : ∀ j : Fin 3, (fun x : Vec3 => G x j) =ᵐ[volume] (fun x : Vec3 => G' x j) := by
    intro j
    have hfW : HasWeakPartialDerivOn (Set.univ : Set Vec3) j g (fun x => G x j) := by
      intro φ hφ hφc hφs
      have hfg' : f =ᵐ[volume.restrict Set.univ] g := by simpa using hfg
      calc ∫ x in (Set.univ : Set Vec3), g x * (fderiv ℝ φ x) (basisVec j) ∂volume =
          ∫ x in (Set.univ : Set Vec3), f x * (fderiv ℝ φ x) (basisVec j) ∂volume := by
            apply integral_congr_ae
            filter_upwards [hfg'] with x hx
            rw [hx]
        _ = -∫ x in (Set.univ : Set Vec3), G x j * φ x ∂volume := hf j φ hφ hφc hφs
    have hLoc : LocallyIntegrableOn (fun x : Vec3 => G x j) (Set.univ : Set Vec3) volume :=
      ((memLp_pi_iff.1 hG j).locallyIntegrable (by norm_num)).locallyIntegrableOn _
    have hLoc' : LocallyIntegrableOn (fun x : Vec3 => G' x j) (Set.univ : Set Vec3) volume :=
      ((memLp_pi_iff.1 hG' j).locallyIntegrable (by norm_num)).locallyIntegrableOn _
    simpa [CKN.volumeOn, Measure.restrict_univ] using
      HasWeakPartialDerivOn.ae_eq isOpen_univ hLoc hLoc' hfW (hg j)
  filter_upwards [ae_all_iff.2 hcomp] with x hx
  exact funext hx

/-- A strong solution that agrees with a Leray–Hopf solution on a slab has the same
gradient there (`lem:lps-continuation`). -/
theorem lps_strong_gradient_ae_eq_slab {T t₀ t₁ : ℝ} {a : Vec3 → Vec3}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {U : ParabolicPoint → Vec3} {DU : ParabolicPoint → Fin 3 → Vec3} {p : ParabolicPoint → ℝ}
    (hLH : IsLerayHopfSolution T a u Du) (hU : IsLpsStrongSolution t₀ t₁ U DU p)
    (ht₀ : 0 ≤ t₀) (ht₁ : t₁ ≤ T)
    (hae : U =ᵐ[volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ t₁))] u) :
    DU =ᵐ[volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ t₁))] Du := by
  obtain ⟨D2, Dt, -, -, hDU, -, -⟩ := hU.2.2.2.1
  have hsub : Ioo t₀ t₁ ⊆ Ioo 0 T := fun t ht => ⟨lt_of_le_of_lt ht₀ ht.1, lt_of_lt_of_le ht.2 ht₁⟩
  have hQsub : spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ t₁) ⊆
      spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T) := fun z hz => ⟨hz.1, hsub hz.2⟩
  have hDu : MemLp Du 2 (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ t₁))) :=
    (lps_lh_memLp_slab hLH).2.mono_measure (Measure.restrict_mono hQsub le_rfl)
  refine lps_slab_ae_eq_of_slices hDU hDu ?_
  have hsl := lps_slices_ae_eq_of_slab hae
  have hgr : ∀ᵐ t ∂(volume.restrict (Ioo t₀ t₁)), ∀ i : Fin 3,
      HasWeakGradientOn (Set.univ : Set Vec3) (fun x => u (x, t) i) (fun x => Du (x, t) i) :=
    ae_restrict_of_ae_restrict_of_subset hsub hLH.2.2.2.2.2.2.1
  have hDum := lps_slice_memLp_two_ae_slab hDu
  filter_upwards [hsl, hgr, hDum, ae_restrict_mem measurableSet_Ioo] with t h1 h2 h3 ht
  have ht' : t ∈ Icc t₀ t₁ := ⟨ht.1.le, ht.2.le⟩
  have hUg := lps_strong_solution_slice_weak_gradient hU ht'
  have hDUs := (lps_strong_solution_slice_memLp_two hU ht').2
  have hcomp : ∀ i : Fin 3, (fun x : Vec3 => DU (x, t) i) =ᵐ[volume] (fun x : Vec3 => Du (x, t)
    i) := by
    intro i
    have hUi : (fun x : Vec3 => U (x, t) i) =ᵐ[volume] (fun x : Vec3 => u (x, t) i) := by
      filter_upwards [h1] with x hx
      rw [hx]
    exact lps_weak_gradient_ae_eq (hUg i) (h2 i) hUi (memLp_pi_iff.1 hDUs i)
      (memLp_pi_iff.1 h3 i)
  filter_upwards [ae_all_iff.2 hcomp] with x hx
  exact funext hx

/-- The end-time slice of a strong solution that agrees with a Leray–Hopf solution on
a slab agrees with the Leray–Hopf slice in the weak sense (`lem:lps-continuation`). -/
theorem lps_weak_slice_eq {T t₀ t₁ : ℝ} {a : Vec3 → Vec3}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {U : ParabolicPoint → Vec3} {DU : ParabolicPoint → Fin 3 → Vec3} {p : ParabolicPoint → ℝ}
    (hLH : IsLerayHopfSolution T a u Du) (hU : IsLpsStrongSolution t₀ t₁ U DU p)
    (ht₀ : 0 ≤ t₀) (ht₁ : t₁ ≤ T)
    (hae : U =ᵐ[volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo t₀ t₁))] u)
    (w : Vec3 → Vec3) (hw : MemLp w 2 volume) :
    (∫ x : Vec3, ∑ i : Fin 3, U (x, t₁) i * w x i) = ∫ x : Vec3, ∑ i : Fin 3, u (x, t₁) i * w x
      i := by
  have hlt : t₀ < t₁ := hU.1
  set f : ℝ → ℝ := fun t => ∫ x : Vec3, ∑ i : Fin 3, u (x, t) i * w x i with hf
  set g : ℝ → ℝ := fun t => ∫ x : Vec3, ∑ i : Fin 3, U (x, t) i * w x i with hg
  have hfc : ContinuousOn f (Icc t₀ t₁) :=
    (hLH.2.2.2.2.2.2.2.2.1 w hw).mono (Icc_subset_Icc ht₀ ht₁)
  have hgc : ContinuousOn g (Icc t₀ t₁) :=
    lps_pairing_continuousOn_of_l2 (fun t ht => (lps_strong_solution_slice_memLp_two hU ht).1)
      (fun t ht => (hU.2.2.1 t ht).1) hw
  have hsl := lps_slices_ae_eq_of_slab hae
  have hA : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Ioo t₀ t₁ → g t = f t := by
    rw [← ae_restrict_iff' measurableSet_Ioo]
    filter_upwards [hsl] with t ht
    refine integral_congr_ae ?_
    filter_upwards [ht] with x hx
    rw [hx]
  have hfreq : ∃ᶠ t in nhdsWithin t₁ (Icc t₀ t₁), g t = f t := by
    rw [Filter.frequently_iff]
    intro V hV
    obtain ⟨ε, hε, hεV⟩ := Metric.mem_nhdsWithin_iff.mp hV
    set c : ℝ := max t₀ (t₁ - ε) with hc
    have hct : c < t₁ := max_lt hlt (by linarith only [hε])
    have hpos : (volume.restrict (Ioo c t₁) : Measure ℝ) ≠ 0 := by
      rw [Ne, Measure.restrict_eq_zero]
      rw [Real.volume_Ioo]
      simpa using hct
    have : NeBot (ae (volume.restrict (Ioo c t₁) : Measure ℝ)) := ae_neBot.2 hpos
    have hA' : ∀ᵐ t ∂(volume.restrict (Ioo c t₁) : Measure ℝ), t ∈ Ioo t₀ t₁ → g t = f t :=
      ae_restrict_of_ae hA
    obtain ⟨t, ht1, ht2⟩ := (hA'.and (ae_restrict_mem measurableSet_Ioo)).exists
    have htI : t ∈ Ioo t₀ t₁ := ⟨lt_of_le_of_lt (le_max_left _ _) ht2.1, ht2.2⟩
    refine ⟨t, hεV ⟨?_, ⟨htI.1.le, htI.2.le⟩⟩, ht1 htI⟩
    rw [Metric.mem_ball, Real.dist_eq, abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr htI.2.le)]
    have : t₁ - ε ≤ c := le_max_right _ _
    linarith only [ht2.1, this]
  have hlim := tendsto_nhds_unique_of_frequently_eq
    (hgc t₁ ⟨hlt.le, le_rfl⟩) (hfc t₁ ⟨hlt.le, le_rfl⟩) hfreq
  exact hlim

end ESS

end
