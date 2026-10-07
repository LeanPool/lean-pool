/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.CaffarelliKohnNirenberg.Statements.IsLerayHopfSolution
public import LeanPool.CaffarelliKohnNirenberg.ClassEquivalence.Data
public import LeanPool.CaffarelliKohnNirenberg.ClassEquivalence.DivergenceFreeIntegrand
public import LeanPool.CaffarelliKohnNirenberg.ClassEquivalence.MomentumIntegrand
public import LeanPool.CaffarelliKohnNirenberg.ClassEquivalence.TestSupport
public import LeanPool.CaffarelliKohnNirenberg.Setting.ScalingInvarianceTests
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Integration.Average

/-!
# Source facts on a finite slab for `lem:pv-positive-bound`

For a Leray–Hopf solution on ℝ³ × (0, T) with a pressure p whose spatial
L^{3/2} norms are essentially bounded in time, this file records the facts on
the whole slab ℝ³ × (0, T) that feed the rescaling step of
`lem:pv-positive-bound`: a Tonelli bound for slab integrals of functions with
uniformly bounded slices, the global L^{3/2} membership of the pressure, the
CKN data clauses on every compact box of the slab, and the space-time form of
the divergence-free condition.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- Tonelli bound on a slab: if almost every time slice of a nonnegative
integrand has spatial integral at most K, the slab integral is at most
|J| K. -/
theorem pv_setLIntegral_slab_le {J : Set ℝ} {F : ParabolicPoint → ℝ≥0∞} {K : ℝ≥0∞}
    (hF : AEMeasurable F (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) J)))
    (hK : ∀ᵐ t ∂volume.restrict J, ∫⁻ x : Vec3, F (x, t) ≤ K) :
    ∫⁻ z in spaceTimeSet (Set.univ : Set Vec3) J, F z ≤ volume J * K := by
  have hFprod : AEMeasurable (fun z : Vec3 × ℝ => F (z.1, z.2))
      ((volume.restrict (Set.univ : Set Vec3)).prod (volume.restrict J)) := by
    rw [Measure.prod_restrict]
    exact hF
  change (∫⁻ z : Vec3 × ℝ in (Set.univ : Set Vec3) ×ˢ J,
    F (z.1, z.2) ∂((volume : Measure Vec3).prod (volume : Measure ℝ))) ≤ _
  rw [← Measure.prod_restrict, lintegral_prod_symm _ hFprod]
  calc
    (∫⁻ t, ∫⁻ x, F (x, t) ∂volume.restrict (Set.univ : Set Vec3) ∂volume.restrict J)
        ≤ ∫⁻ _t in J, K := by
          apply lintegral_mono_ae
          filter_upwards [hK] with t ht
          simpa only [Measure.restrict_univ] using ht
    _ = volume J * K := by rw [setLIntegral_const]; exact mul_comm _ _

/-- A pressure with essentially bounded spatial L^{3/2} norms lies in
L^{3/2} of the finite slab ℝ³ × (0, T). -/
theorem pv_pressure_memLp_threeHalves_slab {T : ℝ} {p : ParabolicPoint → ℝ}
    (hp : AEStronglyMeasurable p
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))))
    (hPMixed : essSup
      (fun t : ℝ => ∫⁻ x : Vec3, ‖p (x, t)‖ₑ ^ (3 / 2 : ℝ))
      (volume.restrict (Ioo 0 T)) < ⊤) :
    MemLp p (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) := by
  have hF : AEMeasurable (fun z => ‖p z‖ₑ ^ (3 / 2 : ℝ))
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) :=
    ENNReal.continuous_rpow_const.measurable.comp_aemeasurable hp.enorm
  have hbound := pv_setLIntegral_slab_le hF
    (ae_le_essSup (μ := volume.restrict (Ioo 0 T))
      (f := fun t : ℝ => ∫⁻ x : Vec3, ‖p (x, t)‖ₑ ^ (3 / 2 : ℝ)))
  have hfin : (∫⁻ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T),
      ‖p z‖ₑ ^ (3 / 2 : ℝ)) < ⊤ := by
    refine lt_of_le_of_lt hbound (ENNReal.mul_lt_top ?_ hPMixed)
    rw [Real.volume_Ioo]
    exact ENNReal.ofReal_lt_top
  rw [memLp_iff, eLpNorm_eq_lintegral_rpow_enorm_toReal
    (by norm_num) (by norm_num) hp]
  rw [ENNReal.toReal_ofReal (by norm_num : 0 ≤ (3 / 2 : ℝ))]
  exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) hfin.ne

/-- A Leray–Hopf solution together with a slab L^{3/2} pressure satisfies the
CKN data clauses on every compact box of ℝ³ × (0, T). -/
theorem pv_lerayHopf_suitableData {T : ℝ} {a : Vec3 → Vec3}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} (hLH : IsLerayHopfSolution T a u Du)
    (hpLp : MemLp p (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T)))) :
    CKN.IsSuitableWeakSolutionData (Set.univ : Set Vec3) (Ioo 0 T) 3
      u Du p (0 : ParabolicPoint → Vec3) := by
  rcases hLH with ⟨_, _, hU, hDu, hL2, hEnergy, hGrad, _, _, _, _, _⟩
  refine ⟨isOpen_univ, isOpen_Ioo, ordConnected_Ioo, by norm_num, ?_, ?_⟩
  · intro Ω' J _ i
    change MemLp (fun z : ParabolicPoint => (0 : Vec3) i) (ENNReal.ofReal 3)
      (volume.restrict (spaceTimeSet Ω' J))
    exact MemLp.zero
  · intro Ω' J hbox
    have hΩ : Ω' ⊆ (Set.univ : Set Vec3) := Set.subset_univ _
    have hJ : J ⊆ Ioo 0 T := subset_closure.trans hbox.2.2.2.2.2
    have hQ : spaceTimeSet Ω' J ⊆ spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T) :=
      Set.prod_mono hΩ hJ
    have hmono := Measure.restrict_mono hQ (le_refl (volume : Measure ParabolicPoint))
    have hL2bound : ∀ᵐ s ∂volume.restrict J,
        (∫⁻ x in Ω', ‖u (x, s)‖ₑ ^ (2 : ℝ)) ≤
          essSup (fun s : ℝ => ∫⁻ x : Vec3, ‖u (x, s)‖ₑ ^ (2 : ℝ))
            (volume.restrict (Ioo 0 T)) := by
      have hglobal := ae_le_essSup (μ := volume.restrict (Ioo 0 T))
        (f := fun s : ℝ => ∫⁻ x : Vec3, ‖u (x, s)‖ₑ ^ (2 : ℝ))
      filter_upwards [ae_restrict_of_ae_restrict_of_subset hJ hglobal] with s hs
      exact (lintegral_mono_set hΩ).trans (by
        simpa only [Measure.restrict_univ] using hs)
    have hGradJ := hGrad.filter_mono (ae_mono (Measure.restrict_mono hJ le_rfl))
    refine ⟨hU.mono_measure hmono, hDu.mono_measure hmono,
      hpLp.aestronglyMeasurable.mono_measure hmono, aestronglyMeasurable_const,
      lt_of_le_of_lt (essSup_le_of_ae_le _ hL2bound) hL2,
      lt_of_le_of_lt (lintegral_mono_set hQ) hEnergy,
      hpLp.mono_measure hmono, MemLp.zero, ?_⟩
    intro i
    filter_upwards [hGradJ] with s hs
    exact (hs i).restrict hbox.1 hΩ

/-- The time slice of a whole-space test function, as a spatial test function. -/
@[expose] def pvSliceTest {I : Set ℝ} {ψ : Vec3 × ℝ → ℝ}
    (hψ : ψ ∈ spaceTimeTestFunction (V := ℝ) (Set.univ : Set Vec3) I)
    (t : ℝ) : CKN.WeakTestFunction (Set.univ : Set Vec3) := by
  let ψt : Vec3 → ℝ := fun x => ψ (x, t)
  have hsupport : Function.support ψt ⊆ Prod.fst '' tsupport ψ := by
    intro x hx
    exact ⟨(x, t), subset_tsupport ψ (Function.mem_support.mpr hx), rfl⟩
  have hcompact : HasCompactSupport ψt :=
    HasCompactSupport.of_support_subset_isCompact
      (hψ.2.1.isCompact.image continuous_fst) hsupport
  exact ⟨ψt, hψ.1.comp (by fun_prop), hcompact, Set.subset_univ _⟩

/-- The divergence-free clause of a Leray–Hopf solution in space-time form on
the slab ℝ³ × (0, T), with the integrability of the tested integrand on the
support of the test function. -/
theorem pv_lerayHopf_divergence_spaceTime {T : ℝ} {a : Vec3 → Vec3}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} (hLH : IsLerayHopfSolution T a u Du)
    (hdata : CKN.IsSuitableWeakSolutionData (Set.univ : Set Vec3) (Ioo 0 T) 3
      u Du p (0 : ParabolicPoint → Vec3))
    (ψ : ParabolicPoint → ℝ)
    (hψ : ψ ∈ spaceTimeTestFunction (V := ℝ) (Set.univ : Set Vec3) (Ioo 0 T)) :
    IntegrableOn (fun z => ∑ i : Fin 3, u z i * spatialPartial ψ i z)
        (tsupport ψ) volume ∧
      ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T),
        ∑ i : Fin 3, u z i * spatialPartial ψ i z = 0 := by
  have hint := CKN.divergenceFree_integrand_integrableOn_of_data hdata hψ
  refine ⟨hint, ?_⟩
  have hDiv := hLH.2.2.2.2.2.2.2.1
  let Q : Set ParabolicPoint := spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T)
  let F : ParabolicPoint → ℝ := fun z => ∑ i : Fin 3, u z i * spatialPartial ψ i z
  have hFzero : ∀ z, z ∉ tsupport ψ → F z = 0 := by
    intro z hz
    have hpartial : ∀ i : Fin 3, spatialPartial ψ i z = 0 := by
      intro i
      have hq : parabolicHomeomorph z ∉ tsupport (show Vec3 × ℝ → ℝ from ψ) := by
        intro hmem
        apply hz
        rw [CKN.tsupport_parabolic_eq (show ParabolicPoint → ℝ from ψ)]
        exact hmem
      have hzero := CKN.spatialPartial_zero_of_not_mem_tsupport_public hψ.1 hq i
      change spatialPartial ψ i (z.1, z.2) = 0
      exact hzero
    simp [F, hpartial]
  have hFint : Integrable F volume := by
    apply hint.integrable_of_forall_notMem_eq_zero
    exact hFzero
  have hFintQ : IntegrableOn F Q volume := hFint.integrableOn
  have hslice : ∀ᵐ t ∂volume.restrict (Ioo 0 T), ∫ x : Vec3, F (x, t) = 0 := by
    filter_upwards [hDiv] with t ht
    have hpartial (i : Fin 3) (x : Vec3) :
        (pvSliceTest hψ t).partialDeriv i x = spatialPartial ψ i (x, t) := rfl
    have hzero := ht (pvSliceTest hψ t)
    simpa only [hpartial, F] using hzero
  have hiter : (∫ z in Q, F z) = ∫ t in Ioo 0 T, ∫ x : Vec3, F (x, t) := by
    change (∫ z in (Set.univ : Set Vec3) ×ˢ Ioo 0 T, F z
        ∂((volume : Measure Vec3).prod (volume : Measure ℝ))) = _
    have hswap : IntegrableOn (fun z : ℝ × Vec3 => F z.swap)
        (Ioo 0 T ×ˢ (Set.univ : Set Vec3))
        ((volume : Measure ℝ).prod (volume : Measure Vec3)) := hFintQ.swap
    calc
      _ = ∫ z in Ioo 0 T ×ˢ (Set.univ : Set Vec3), F z.swap
          ∂((volume : Measure ℝ).prod (volume : Measure Vec3)) :=
        (setIntegral_prod_swap (μ := (volume : Measure Vec3))
          (ν := (volume : Measure ℝ)) (Set.univ : Set Vec3) (Ioo 0 T) F).symm
      _ = ∫ t in Ioo 0 T, ∫ x : Vec3, F (x, t) := by
        rw [setIntegral_prod _ hswap]
        simp only [MeasureTheory.setIntegral_univ, Prod.swap]
  change (∫ z in Q, F z) = 0
  rw [hiter]
  calc
    (∫ t in Ioo 0 T, ∫ x : Vec3, F (x, t)) = ∫ t in Ioo 0 T, (0 : ℝ) :=
      integral_congr_ae hslice
    _ = 0 := by simp

end ESS
