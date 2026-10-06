/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.WeakDerivative
public import LeanPool.CaffarelliKohnNirenberg.Statements.SpaceTimeSet
public import LeanPool.CaffarelliKohnNirenberg.Statements.SpaceTimeTestFunction
public import LeanPool.CaffarelliKohnNirenberg.Statements.SpatialPartial
public import LeanPool.CaffarelliKohnNirenberg.Statements.TimePartial
public import LeanPool.CaffarelliKohnNirenberg.Statements.ParabolicHolderVecOn
public import LeanPool.CaffarelliKohnNirenberg.Statements.IsLerayHopfSolution
public import LeanPool.EscauriazaSereginSverak.Endpoint.GoodPointsShift
public import LeanPool.EscauriazaSereginSverak.Endpoint.RescalingRegularity
public import LeanPool.CaffarelliKohnNirenberg.Setting.ScalingInvariance
public import LeanPool.CaffarelliKohnNirenberg.ClassEquivalence.Data
public import LeanPool.CaffarelliKohnNirenberg.ClassEquivalence.DivergenceFreeIntegrand
public import LeanPool.CaffarelliKohnNirenberg.ClassEquivalence.MomentumIntegrand
public import LeanPool.CaffarelliKohnNirenberg.ClassEquivalence.TestSupport
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Integration.Average
public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupTerminal
public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupTimeAE

public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

private theorem memLp_two_of_sq_lintegral_lt_top
    {α E : Type} [MeasurableSpace α] [TopologicalSpace E] [ContinuousENorm E]
    {μ : Measure α} {f : α → E}
    (hf : AEStronglyMeasurable f μ)
    (hfin : (∫⁻ x, ‖f x‖ₑ ^ (2 : ℝ) ∂μ) < ⊤) : MemLp f 2 μ := by
  rw [memLp_iff, eLpNorm_eq_lintegral_rpow_enorm_toReal
    (by norm_num) (by norm_num) hf]
  simp only [ENNReal.toReal_ofNat]
  exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) hfin.ne

private theorem integrableOn_superset_of_zero_off
    {S K : Set ParabolicPoint} {f : ParabolicPoint → ℝ}
    (hS : NullMeasurableSet S volume) (hfK : IntegrableOn f K volume)
    (hfzero : ∀ z, z ∉ K → f z = 0) : IntegrableOn f S volume := by
  apply hfK.of_ae_sdiff_eq_zero hS
  filter_upwards [] with z hz
  exact hfzero z hz.2

@[expose] def sliceWeakTestFunction
    {I : Set ℝ} {ψ : Vec3 × ℝ → ℝ} (hψ : ψ ∈
      spaceTimeTestFunction (V := ℝ) (Set.univ : Set Vec3) I)
    (t : ℝ) : CKN.WeakTestFunction (Set.univ : Set Vec3) := by
  let ψt : Vec3 → ℝ := fun x => ψ (x, t)
  have hcompactSupport : Function.support ψt ⊆ Prod.fst '' tsupport ψ := by
    intro x hx
    refine ⟨(x, t), ?_, rfl⟩
    exact subset_tsupport ψ (Function.mem_support.mpr hx)
  have hcompact : HasCompactSupport ψt :=
    HasCompactSupport.of_support_subset_isCompact
      (hψ.2.1.isCompact.image continuous_fst) hcompactSupport
  exact ⟨ψt, hψ.1.comp (by fun_prop), hcompact, Set.subset_univ _⟩

private theorem lerayHopf_spaceTime_divergence
    (T : ℝ) (a : Vec3 → Vec3) (u : ParabolicPoint → Vec3)
    (Du : ParabolicPoint → Fin 3 → Vec3)
    (hLH : IsLerayHopfSolution T a u Du) :
    ∀ ψ : ParabolicPoint → ℝ,
      ψ ∈ spaceTimeTestFunction (V := ℝ) (Set.univ : Set Vec3) (Ioo 0 T) →
      ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T),
        ∑ i : Fin 3, u z i * spatialPartial ψ i z = 0 := by
  rcases hLH with ⟨hT, _, hU, _, _, hEnergy, _, hDiv, _, _, _, _⟩
  intro ψ hψ
  let K : Set ParabolicPoint := tsupport ψ
  let Q : Set ParabolicPoint := spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T)
  let F : ParabolicPoint → ℝ := fun z =>
    ∑ i : Fin 3, u z i * spatialPartial ψ i z
  have hKcompact : IsCompact K := CKN.isCompact_tsupport_parabolic hψ.2.1
  have hKQ : K ⊆ Q := CKN.tsupport_parabolic_subset_spaceTimeSet hψ
  have hUmeas : AEStronglyMeasurable u (volume.restrict K) :=
    hU.mono_measure (Measure.restrict_mono hKQ le_rfl)
  have hUenergy : (∫⁻ z in K, ‖u z‖ₑ ^ (2 : ℝ)) < ⊤ := by
    refine lt_of_le_of_lt (lintegral_mono_set hKQ) ?_
    exact lt_of_le_of_lt
      (lintegral_mono fun z => le_add_right le_rfl) hEnergy
  have hUtwo : MemLp u 2 (volume.restrict K) :=
    memLp_two_of_sq_lintegral_lt_top hUmeas hUenergy
  have hFintK : IntegrableOn F K volume := by
    let : IsFiniteMeasure (volume.restrict K) :=
      CKN.isFiniteMeasure_restrict_of_isCompact hKcompact
    dsimp [F]
    refine integrable_finsetSum Finset.univ fun i _ => ?_
    have hUi : IntegrableOn (fun z : ParabolicPoint => u z i) K volume := by
      have hUiLp : MemLp (fun z : ParabolicPoint => u z i) 2
          (volume.restrict K) := (memLp_pi_iff.mp hUtwo) i
      exact hUiLp.integrable (by norm_num)
    obtain ⟨C, hC⟩ := CKN.exists_bound_spatialPartial_of_mem_spaceTimeTestFunction hψ i
    exact hUi.mul_bdd (c := C)
      (g := fun z : ParabolicPoint => spatialPartial ψ i z)
      (CKN.spatialPartial_contDiff hψ.1 i).continuous.measurable.aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => hC z)
  have hFzero : ∀ z, z ∉ K → F z = 0 := by
    intro z hz
    have hpartial : ∀ i : Fin 3, spatialPartial ψ i z = 0 := by
      intro i
      have hq : parabolicHomeomorph z ∉ tsupport (show Vec3 × ℝ → ℝ from ψ) := by
        intro hmem
        apply hz
        dsimp [K]
        rw [CKN.tsupport_parabolic_eq (show ParabolicPoint → ℝ from ψ)]
        exact hmem
      have hzero := CKN.spatialPartial_zero_of_not_mem_tsupport_public hψ.1 hq i
      change spatialPartial ψ i (z.1, z.2) = 0
      exact hzero
    simp [F, hpartial]
  have hQmeas : MeasurableSet Q := by
    exact (isOpen_spaceTimeSet _ _ isOpen_univ isOpen_Ioo).measurableSet
  have hFintQ : IntegrableOn F Q volume :=
    integrableOn_superset_of_zero_off hQmeas.nullMeasurableSet hFintK hFzero
  have hslice : ∀ᵐ t ∂volume.restrict (Ioo 0 T),
      ∫ x : Vec3, F (x, t) = 0 := by
    filter_upwards [hDiv] with t ht
    let φt := sliceWeakTestFunction hψ t
    have hpartial (i : Fin 3) (x : Vec3) :
        φt.partialDeriv i x = spatialPartial ψ i (x, t) := by
      rfl
    have hzero := ht φt
    simpa only [hpartial, F] using hzero
  have hiter :
      (∫ z in Q, F z) = ∫ t in Ioo 0 T, ∫ x : Vec3, F (x, t) := by
    rw [CKN.Foundation.Parabolic.Integration.volume_parabolicPoint_eq_prod]
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
  rw [hiter]
  calc
    (∫ t in Ioo 0 T, ∫ x : Vec3, F (x, t)) =
        ∫ t in Ioo 0 T, (0 : ℝ) := integral_congr_ae hslice
    _ = 0 := by simp

private theorem pressure_memLp_three_halves_of_mixed_bound
    (p : ParabolicPoint → ℝ) (T : ℝ) (Ω' : Set Vec3) (J : Set ℝ)
    (hΩ' : Ω' ⊆ (Set.univ : Set Vec3)) (hJ : J ⊆ Ioo 0 T)
    (hJvol : volume J < ⊤)
    (hp : AEStronglyMeasurable p
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))))
    (hPMixed : essSup
      (fun t : ℝ => ∫⁻ x : Vec3, ‖p (x, t)‖ₑ ^ (3 / 2 : ℝ))
      (volume.restrict (Ioo 0 T)) < ⊤) :
    MemLp p (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (spaceTimeSet Ω' J)) := by
  let Q : Set ParabolicPoint := spaceTimeSet Ω' J
  let μx : Measure Vec3 := volume.restrict Ω'
  let μt : Measure ℝ := volume.restrict J
  let F : ParabolicPoint → ℝ≥0∞ := fun z => ‖p z‖ₑ ^ (3 / 2 : ℝ)
  let G : ℝ → ℝ≥0∞ := fun t => ∫⁻ x : Vec3, ‖p (x, t)‖ₑ ^ (3 / 2 : ℝ)
  let M : ℝ≥0∞ := essSup G (volume.restrict (Ioo 0 T))
  have hQsub : Q ⊆ spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T) := by
    intro z hz
    exact ⟨hΩ' hz.1, hJ hz.2⟩
  have hP : AEStronglyMeasurable p (volume.restrict Q) := by
    exact hp.mono_measure (Measure.restrict_mono hQsub le_rfl)
  have hFprod : AEMeasurable (fun z : Vec3 × ℝ => F (z.1, z.2))
      (μx.prod μt) := by
    have hPprod : AEStronglyMeasurable (fun z : Vec3 × ℝ => p (z.1, z.2))
        (μx.prod μt) := by
      rw [Measure.prod_restrict]
      rw [CKN.Foundation.Parabolic.Integration.volume_parabolicPoint_eq_prod] at hP
      change AEStronglyMeasurable
        (fun z : Vec3 × ℝ => p (z.1, z.2))
        ((volume.prod volume).restrict (Ω' ×ˢ J)) at hP
      change AEStronglyMeasurable (fun z : Vec3 × ℝ => p (z.1, z.2))
        ((volume.prod volume).restrict (Ω' ×ˢ J))
      simpa only [Measure.prod_restrict] using hP
    exact ENNReal.continuous_rpow_const.measurable.comp_aemeasurable
      hPprod.enorm
  have hGbound : ∀ᵐ t ∂volume.restrict J, G t ≤ M := by
    have hae := ae_le_essSup (μ := volume.restrict (Ioo 0 T)) (f := G)
    have hJae := ae_restrict_of_ae_restrict_of_subset hJ hae
    filter_upwards [hJae] with t ht
    exact ht
  have hGlocal : ∀ᵐ t ∂μt,
      (∫⁻ x in Ω', ‖p (x, t)‖ₑ ^ (3 / 2 : ℝ)) ≤ M := by
    filter_upwards [hGbound] with t ht
    exact (lintegral_mono_set hΩ').trans (by simpa [G] using ht)
  have htimeBound :
      (∫⁻ t in J, ∫⁻ x in Ω', ‖p (x, t)‖ₑ ^ (3 / 2 : ℝ)) ≤
        volume J * M := by
    calc
      _ ≤ ∫⁻ _t in J, M := lintegral_mono_ae hGlocal
      _ = volume J * M := by rw [setLIntegral_const]; exact mul_comm _ _
  have hQfinite : (∫⁻ z in Q, F z) < ⊤ := by
    rw [CKN.Foundation.Parabolic.Integration.volume_parabolicPoint_eq_prod]
    change (∫⁻ z : Vec3 × ℝ in Ω' ×ˢ J,
      F (z.1, z.2) ∂(volume.prod volume)) < ⊤
    rw [← Measure.prod_restrict]
    change (∫⁻ z : Vec3 × ℝ, F (z.1, z.2) ∂(μx.prod μt)) < ⊤
    rw [lintegral_prod_symm _ hFprod]
    exact lt_of_le_of_lt htimeBound
      (ENNReal.mul_lt_top hJvol (by simpa [M] using hPMixed))
  have hPq : AEStronglyMeasurable p (volume.restrict Q) := hP
  have hFlin : (∫⁻ z in Q, ‖p z‖ₑ ^ (3 / 2 : ℝ)) < ⊤ := by
    simpa only [F] using hQfinite
  rw [memLp_iff, eLpNorm_eq_lintegral_rpow_enorm_toReal
    (by norm_num) (by norm_num) hPq]
  rw [ENNReal.toReal_ofReal (by norm_num : 0 ≤ (3 / 2 : ℝ))]
  exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) hFlin.ne

private theorem lerayHopf_pressureData
    (T : ℝ) (a : Vec3 → Vec3)
    (u : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ)
    (hLH : IsLerayHopfSolution T a u Du)
    (hp : MemLp p (ENNReal.ofReal (5 / 3 : ℝ))
      (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))))
    (hPMixed : essSup
      (fun t : ℝ => ∫⁻ x : Vec3, ‖p (x, t)‖ₑ ^ (3 / 2 : ℝ))
      (volume.restrict (Ioo 0 T)) < ⊤)
    : CKN.IsSuitableWeakSolutionData (Set.univ : Set Vec3) (Ioo 0 T) 3
      u Du p (0 : ParabolicPoint → Vec3) := by
  rcases hLH with ⟨hT, hIn, hU, hDu, hL2, hEnergy, hGrad, hDiv, hCont,
    hMomentum, hEnergyIneq, hTrace⟩
  unfold CKN.IsSuitableWeakSolutionData
  constructor
  · exact isOpen_univ
  constructor
  · exact isOpen_Ioo
  constructor
  · exact ordConnected_Ioo
  constructor
  · norm_num
  constructor
  · intro Ω' J hbox i
    change MemLp (fun z : ParabolicPoint => (0 : Vec3) i) (ENNReal.ofReal 3)
      (volume.restrict (spaceTimeSet Ω' J))
    exact MemLp.zero
  · intro Ω' J hbox
    let Q : Set ParabolicPoint := spaceTimeSet Ω' J
    let Q₀ : Set ParabolicPoint := spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T)
    have hΩ : Ω' ⊆ (Set.univ : Set Vec3) := Set.subset_univ _
    have hJ : J ⊆ Ioo 0 T := subset_closure.trans hbox.2.2.2.2.2
    have hQ : Q ⊆ Q₀ := Set.prod_mono hΩ hJ
    have hQmeas : MeasurableSet Q := by
      exact hbox.1.measurableSet.prod hbox.2.2.2.1.measurableSet
    have hspace : volume Ω' < ⊤ :=
      (measure_mono subset_closure).trans_lt hbox.2.1.measure_lt_top
    have htime : volume J < ⊤ :=
      (measure_mono subset_closure).trans_lt hbox.2.2.2.2.1.measure_lt_top
    have hQvol : volume Q < ⊤ := by
      change volume (Ω' ×ˢ J) < ⊤
      rw [Measure.volume_eq_prod, Measure.prod_prod]
      exact ENNReal.mul_lt_top hspace htime
    have hU' : AEStronglyMeasurable u (volume.restrict Q) :=
      hU.mono_measure (Measure.restrict_mono hQ le_rfl)
    have hDu' : AEStronglyMeasurable Du (volume.restrict Q) :=
      hDu.mono_measure (Measure.restrict_mono hQ le_rfl)
    have hp' : AEStronglyMeasurable p (volume.restrict Q) :=
      hp.aestronglyMeasurable.mono_measure (Measure.restrict_mono hQ le_rfl)
    have hL2bound : ∀ᵐ s ∂volume.restrict J,
        (∫⁻ x in Ω', ‖u (x, s)‖ₑ ^ (2 : ℝ)) ≤
          essSup (fun s : ℝ => ∫⁻ x : Vec3, ‖u (x, s)‖ₑ ^ (2 : ℝ))
            (volume.restrict (Ioo 0 T)) := by
      have hglobal := ae_le_essSup (μ := volume.restrict (Ioo 0 T))
        (f := fun s : ℝ =>
        ∫⁻ x : Vec3, ‖u (x, s)‖ₑ ^ (2 : ℝ))
      have hJglobal := ae_restrict_of_ae_restrict_of_subset hJ hglobal
      filter_upwards [hJglobal] with s hs
      exact (lintegral_mono_set hΩ).trans (by
        simpa only [Measure.restrict_univ] using hs)
    have hL2' : essSup
        (fun s : ℝ => ∫⁻ x in Ω', ‖u (x, s)‖ₑ ^ (2 : ℝ))
        (volume.restrict J) < ⊤ := by
      refine lt_of_le_of_lt (essSup_le_of_ae_le _ hL2bound) hL2
    have hEnergy' :
        (∫⁻ z in Q, ‖u z‖ₑ ^ (2 : ℝ) + ‖Du z‖ₑ ^ (2 : ℝ)) < ⊤ := by
      refine lt_of_le_of_lt (lintegral_mono_set hQ) hEnergy
    have hpLp' : MemLp p (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict Q) :=
      pressure_memLp_three_halves_of_mixed_bound p T Ω' J hΩ hJ htime
        hp.aestronglyMeasurable hPMixed
    have hGradJ := hGrad.filter_mono
      (ae_mono (Measure.restrict_mono hJ le_rfl))
    refine ⟨hU', hDu', hp', aestronglyMeasurable_const, hL2', hEnergy', hpLp',
      MemLp.zero, ?_⟩
    intro i
    filter_upwards [hGradJ] with s hs
    exact (hs i).restrict hbox.1 hΩ

private theorem rescaledSpace_image_eq
    (r : ℝ) (hr : 0 < r) (x₀ : Vec3) (Ω : Set Vec3) :
    CKN.rescaledSpace r x₀ (CKN.scalingSpace r x₀ '' Ω) = Ω := by
  let e : Vec3 ≃ₜ Vec3 :=
    (Homeomorph.smulOfNeZero r hr.ne').trans (Homeomorph.addLeft x₀)
  have he : CKN.scalingSpace r x₀ = e := by
    funext x
    rfl
  rw [CKN.rescaledSpace, he]
  exact e.preimage_image Ω

private theorem rescaledTime_image_eq
    (r : ℝ) (hr : 0 < r) (t₀ : ℝ) (I : Set ℝ) :
    CKN.rescaledTime r t₀ (CKN.scalingTime r t₀ '' I) = I := by
  let e : ℝ ≃ₜ ℝ :=
    (Homeomorph.smulOfNeZero (r ^ 2) (sq_pos_of_pos hr).ne').trans
      (Homeomorph.addLeft t₀)
  have he : CKN.scalingTime r t₀ = e := by
    funext t
    rfl
  rw [CKN.rescaledTime, he]
  exact e.preimage_image I

@[expose] def localScalingHomeomorph (r : ℝ) (hr : 0 < r) (z₀ : ParabolicPoint) :
    ParabolicPoint ≃ₜ ParabolicPoint :=
  (parabolicHomeomorph.trans
    (Homeomorph.prodCongr
      ((Homeomorph.smulOfNeZero r hr.ne').trans (Homeomorph.addLeft z₀.1))
      ((Homeomorph.smulOfNeZero (r ^ 2) (sq_pos_of_pos hr).ne').trans
        (Homeomorph.addLeft z₀.2)))).trans parabolicHomeomorph.symm

private theorem localScalingHomeomorph_eq
    (r : ℝ) (hr : 0 < r) (z₀ : ParabolicPoint) :
    ⇑(localScalingHomeomorph r hr z₀) = CKN.scalingParabolic r z₀ := by
  funext z
  rfl

private theorem scalingParabolic_measurable
    (r : ℝ) (hr : 0 < r) (z₀ : ParabolicPoint) :
    Measurable (CKN.scalingParabolic r z₀) := by
  rw [← localScalingHomeomorph_eq r hr z₀]
  exact (localScalingHomeomorph r hr z₀).measurable

private theorem aestronglyMeasurable_comp_scaling
    {E : Type} [TopologicalSpace E]
    (r : ℝ) (hr : 0 < r) (z₀ : ParabolicPoint)
    {Ω : Set Vec3} {I : Set ℝ} {f : ParabolicPoint → E}
    (hΩ : MeasurableSet Ω) (hI : MeasurableSet I)
    (hf : AEStronglyMeasurable f (volume.restrict (spaceTimeSet Ω I))) :
    AEStronglyMeasurable (f ∘ CKN.scalingParabolic r z₀)
      (volume.restrict
        (spaceTimeSet (CKN.rescaledSpace r z₀.1 Ω)
          (CKN.rescaledTime r z₀.2 I))) := by
  have hmap := CKN.map_scalingParabolic_restrict hr z₀ hΩ hI
  have hs := hf.smul_measure (ENNReal.ofReal (r⁻¹ ^ 5))
  rw [← hmap] at hs
  exact hs.comp_measurable (scalingParabolic_measurable r hr z₀)

private theorem memLp_comp_scaling
    {E : Type} [TopologicalSpace E] [ContinuousENorm E]
    (r : ℝ) (hr : 0 < r) (z₀ : ParabolicPoint)
    {Ω : Set Vec3} {I : Set ℝ} {f : ParabolicPoint → E} {q : ℝ≥0∞}
    (hΩ : MeasurableSet Ω) (hI : MeasurableSet I)
    (hf : MemLp f q (volume.restrict (spaceTimeSet Ω I))) :
    MemLp (f ∘ CKN.scalingParabolic r z₀) q
      (volume.restrict
        (spaceTimeSet (CKN.rescaledSpace r z₀.1 Ω)
          (CKN.rescaledTime r z₀.2 I))) := by
  have hmap := CKN.map_scalingParabolic_restrict hr z₀ hΩ hI
  have hs := hf.smul_measure (c := ENNReal.ofReal (r⁻¹ ^ 5)) ENNReal.ofReal_ne_top
  rw [← hmap] at hs
  exact hs.comp_of_map (scalingParabolic_measurable r hr z₀).aemeasurable

private theorem aemeasurable_comp_scaling
    (r : ℝ) (hr : 0 < r) (z₀ : ParabolicPoint)
    {Ω : Set Vec3} {I : Set ℝ} {F : ParabolicPoint → ℝ≥0∞}
    (hΩ : MeasurableSet Ω) (hI : MeasurableSet I)
    (hF : AEMeasurable F (volume.restrict (spaceTimeSet Ω I))) :
    AEMeasurable (F ∘ CKN.scalingParabolic r z₀)
      (volume.restrict
        (spaceTimeSet (CKN.rescaledSpace r z₀.1 Ω)
          (CKN.rescaledTime r z₀.2 I))) := by
  have hmap := CKN.map_scalingParabolic_restrict hr z₀ hΩ hI
  have hs := hF.smul_measure (ENNReal.ofReal (r⁻¹ ^ 5))
  rw [← hmap] at hs
  exact hs.comp_measurable (scalingParabolic_measurable r hr z₀)

private theorem lintegral_comp_scaling
    (r : ℝ) (hr : 0 < r) (z₀ : ParabolicPoint)
    {Ω : Set Vec3} {I : Set ℝ} {F : ParabolicPoint → ℝ≥0∞}
    (hΩ : MeasurableSet Ω) (hI : MeasurableSet I)
    (hF : AEMeasurable F (volume.restrict (spaceTimeSet Ω I))) :
    ∫⁻ z in spaceTimeSet (CKN.rescaledSpace r z₀.1 Ω)
        (CKN.rescaledTime r z₀.2 I), F (CKN.scalingParabolic r z₀ z) =
      ENNReal.ofReal (r⁻¹ ^ 5) * ∫⁻ z in spaceTimeSet Ω I, F z := by
  have hmap := CKN.map_scalingParabolic_restrict hr z₀ hΩ hI
  have hFmap : AEMeasurable F
      (Measure.map (CKN.scalingParabolic r z₀)
        (volume.restrict
          (spaceTimeSet (CKN.rescaledSpace r z₀.1 Ω)
            (CKN.rescaledTime r z₀.2 I)))) := by
    rw [hmap]
    exact hF.smul_measure (ENNReal.ofReal (r⁻¹ ^ 5))
  have hcomp := lintegral_map' hFmap
    (scalingParabolic_measurable r hr z₀).aemeasurable
  rw [hmap, lintegral_smul_measure] at hcomp
  simpa [Function.comp_def, smul_eq_mul] using hcomp.symm

private theorem lintegral_comp_scaling_space
    (r : ℝ) (hr : 0 < r) (x₀ : Vec3)
    {Ω : Set Vec3} {F : Vec3 → ℝ≥0∞} (hΩ : MeasurableSet Ω)
    (hF : AEMeasurable F (volume.restrict Ω)) :
    ∫⁻ x in CKN.rescaledSpace r x₀ Ω, F (CKN.scalingSpace r x₀ x) =
      ENNReal.ofReal (r⁻¹ ^ 3) * ∫⁻ x in Ω, F x := by
  have hmap := CKN.map_scalingSpace_restrict hr x₀ hΩ
  have hFmap : AEMeasurable F
      (Measure.map (CKN.scalingSpace r x₀)
        (volume.restrict (CKN.rescaledSpace r x₀ Ω))) := by
    rw [hmap]
    exact hF.smul_measure (ENNReal.ofReal (r⁻¹ ^ 3))
  have hmeas : Measurable (CKN.scalingSpace r x₀) := by
    change Measurable (fun x : Vec3 => x₀ + r • x)
    fun_prop
  have hcomp := lintegral_map' hFmap hmeas.aemeasurable
  rw [hmap, lintegral_smul_measure] at hcomp
  simpa [Function.comp_def, smul_eq_mul] using hcomp.symm

private theorem ae_slice_aemeasurable
    {α β E : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace E] {μ : Measure α} {ν : Measure β}
    [SFinite μ] [SFinite ν] {F : α × β → E}
    (hF : AEMeasurable F (μ.prod ν)) :
    ∀ᵐ s ∂ν, AEMeasurable (fun x => F (x, s)) μ := by
  let Fs : β × α → E := fun z => F z.swap
  have hFs : AEMeasurable Fs (ν.prod μ) := by simpa [Fs] using hF.prod_swap
  let G : β × α → E := AEMeasurable.mk Fs hFs
  have hG : Measurable G := hFs.measurable_mk
  have heq : ∀ᵐ s ∂ν, Function.curry Fs s =ᵐ[μ] Function.curry G s :=
    Measure.ae_ae_eq_curry_of_prod hFs.ae_eq_mk
  filter_upwards [heq] with s hs
  have hGs : AEMeasurable (fun x => G (s, x)) μ :=
    (hG.comp (measurable_const.prodMk measurable_id)).aemeasurable
  exact hGs.congr hs.symm

private theorem ae_slice_aestronglyMeasurable
    {α β E : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [TopologicalSpace E] {μ : Measure α} {ν : Measure β}
    [SFinite μ] [SFinite ν] {F : α × β → E}
    (hF : AEStronglyMeasurable F (μ.prod ν)) :
    ∀ᵐ s ∂ν, AEStronglyMeasurable (fun x => F (x, s)) μ := by
  let Fs : β × α → E := fun z => F z.swap
  have hFs : AEStronglyMeasurable Fs (ν.prod μ) := by simpa [Fs] using hF.prod_swap
  let G : β × α → E := AEStronglyMeasurable.mk Fs hFs
  have hG : StronglyMeasurable G := hFs.stronglyMeasurable_mk
  have heq : ∀ᵐ s ∂ν, Function.curry Fs s =ᵐ[μ] Function.curry G s :=
    Measure.ae_ae_eq_curry_of_prod hFs.ae_eq_mk
  filter_upwards [heq] with s hs
  have hGs : StronglyMeasurable (fun x => G (s, x)) := by
    simpa [Function.comp_def] using
      hG.comp_measurable (measurable_const.prodMk measurable_id)
  exact hGs.aestronglyMeasurable.congr hs.symm

private theorem rescaled_velocity_pointwise
    (r : ℝ) (hr : 0 < r) (z₀ : ParabolicPoint)
    (u : ParabolicPoint → Vec3) (z : ParabolicPoint) :
    ‖CKN.rescaleVelocity r z₀ u z‖ₑ ^ (2 : ℝ) =
      ENNReal.ofReal (r ^ 2) *
        (‖u (CKN.scalingParabolic r z₀ z)‖ₑ ^ (2 : ℝ)) := by
  change ‖r • u (CKN.scalingParabolic r z₀ z)‖ₑ ^ (2 : ℝ) = _
  rw [enorm_smul, ← ofReal_norm r, Real.norm_eq_abs, abs_of_pos hr]
  rw [ENNReal.mul_rpow_of_nonneg, ENNReal.ofReal_rpow_of_nonneg hr.le (by norm_num)]
  norm_num
  positivity

private theorem rescaled_energy_pointwise
    (r : ℝ) (hr : 0 < r) (z₀ : ParabolicPoint)
    (u : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3)
    (z : ParabolicPoint) :
    ‖CKN.rescaleVelocity r z₀ u z‖ₑ ^ (2 : ℝ) +
      ‖CKN.rescaleGradient r z₀ Du z‖ₑ ^ (2 : ℝ) =
      ENNReal.ofReal (r ^ 2) *
          (‖u (CKN.scalingParabolic r z₀ z)‖ₑ ^ (2 : ℝ)) +
        ENNReal.ofReal (r ^ 4) *
          (‖Du (CKN.scalingParabolic r z₀ z)‖ₑ ^ (2 : ℝ)) := by
  change ‖r • u (CKN.scalingParabolic r z₀ z)‖ₑ ^ (2 : ℝ) +
      ‖r ^ 2 • Du (CKN.scalingParabolic r z₀ z)‖ₑ ^ (2 : ℝ) = _
  rw [enorm_smul, enorm_smul]
  rw [← ofReal_norm r, ← ofReal_norm (r ^ 2)]
  rw [Real.norm_eq_abs, abs_of_pos hr]
  rw [Real.norm_eq_abs, abs_of_pos (sq_pos_of_pos hr)]
  rw [ENNReal.mul_rpow_of_nonneg, ENNReal.mul_rpow_of_nonneg]
  rw [ENNReal.ofReal_rpow_of_nonneg hr.le (by norm_num),
    ENNReal.ofReal_rpow_of_nonneg (sq_pos_of_pos hr).le (by norm_num)]; norm_num
  have hcoef : ENNReal.ofReal ((r ^ 2) ^ 2) = ENNReal.ofReal (r ^ 4) := by
    congr 1
    ring
  rw [hcoef]
  all_goals first | rfl | norm_num

private theorem memLp_rescale_pressure
    (r : ℝ) (hr : 0 < r) (z₀ : ParabolicPoint)
    {Ω : Set Vec3} {I : Set ℝ} {p : ParabolicPoint → ℝ} {q : ℝ≥0∞}
    (hΩ : MeasurableSet Ω) (hI : MeasurableSet I)
    (hp : MemLp p q (volume.restrict (spaceTimeSet Ω I))) :
    MemLp (CKN.rescalePressure r z₀ p) q
      (volume.restrict
        (spaceTimeSet (CKN.rescaledSpace r z₀.1 Ω)
          (CKN.rescaledTime r z₀.2 I))) := by
  have hcomp := memLp_comp_scaling r hr z₀ hΩ hI hp
  have heq : CKN.rescalePressure r z₀ p =
      (r ^ 2) • (p ∘ CKN.scalingParabolic r z₀) := by
    funext z
    rfl
  rw [heq]
  exact hcomp.const_smul (r ^ 2)

private theorem aestronglyMeasurable_rescale_velocity
    (r : ℝ) (hr : 0 < r) (z₀ : ParabolicPoint)
    {Ω : Set Vec3} {I : Set ℝ} {u : ParabolicPoint → Vec3}
    (hΩ : MeasurableSet Ω) (hI : MeasurableSet I)
    (hu : AEStronglyMeasurable u (volume.restrict (spaceTimeSet Ω I))) :
    AEStronglyMeasurable (CKN.rescaleVelocity r z₀ u)
      (volume.restrict
        (spaceTimeSet (CKN.rescaledSpace r z₀.1 Ω)
          (CKN.rescaledTime r z₀.2 I))) := by
  have hcomp := aestronglyMeasurable_comp_scaling r hr z₀ hΩ hI hu
  have heq : CKN.rescaleVelocity r z₀ u =
      r • (u ∘ CKN.scalingParabolic r z₀) := by
    funext z
    rfl
  rw [heq]
  exact hcomp.const_smul r

private theorem aestronglyMeasurable_rescale_gradient
    (r : ℝ) (hr : 0 < r) (z₀ : ParabolicPoint)
    {Ω : Set Vec3} {I : Set ℝ} {Du : ParabolicPoint → Fin 3 → Vec3}
    (hΩ : MeasurableSet Ω) (hI : MeasurableSet I)
    (hDu : AEStronglyMeasurable Du (volume.restrict (spaceTimeSet Ω I))) :
    AEStronglyMeasurable (CKN.rescaleGradient r z₀ Du)
      (volume.restrict
        (spaceTimeSet (CKN.rescaledSpace r z₀.1 Ω)
          (CKN.rescaledTime r z₀.2 I))) := by
  have hcomp := aestronglyMeasurable_comp_scaling r hr z₀ hΩ hI hDu
  have heq : CKN.rescaleGradient r z₀ Du =
      (r ^ 2) • (Du ∘ CKN.scalingParabolic r z₀) := by
    funext z
    ext i j
    rfl
  rw [heq]
  exact hcomp.const_smul (r ^ 2)

private theorem rescaleData_local
    {Ω I : Set _} {u : ParabolicPoint → Vec3}
    {Du : ParabolicPoint → Fin 3 → Vec3} {p : ParabolicPoint → ℝ}
    (hdata : CKN.IsSuitableWeakSolutionData Ω I 3 u Du p
      (0 : ParabolicPoint → Vec3))
    (z₀ : ParabolicPoint) (r : ℝ) (hr : 0 < r)
    (Ω' : Set Vec3) (J : Set ℝ)
    (hbox : CKN.localBox (CKN.rescaledSpace r z₀.1 Ω)
      (CKN.rescaledTime r z₀.2 I) Ω' J) :
    AEStronglyMeasurable (CKN.rescaleVelocity r z₀ u)
      (volume.restrict (spaceTimeSet Ω' J)) ∧
    AEStronglyMeasurable (CKN.rescaleGradient r z₀ Du)
      (volume.restrict (spaceTimeSet Ω' J)) ∧
    AEStronglyMeasurable (CKN.rescalePressure r z₀ p)
      (volume.restrict (spaceTimeSet Ω' J)) ∧
    essSup (fun s : ℝ => ∫⁻ x in Ω',
      ‖CKN.rescaleVelocity r z₀ u (x, s)‖ₑ ^ (2 : ℝ))
        (volume.restrict J) < ⊤ ∧
    (∫⁻ z in spaceTimeSet Ω' J,
      ‖CKN.rescaleVelocity r z₀ u z‖ₑ ^ (2 : ℝ) +
        ‖CKN.rescaleGradient r z₀ Du z‖ₑ ^ (2 : ℝ)) < ⊤ ∧
    MemLp (CKN.rescalePressure r z₀ p) (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (spaceTimeSet Ω' J)) ∧
    ∀ i : Fin 3, ∀ᵐ s ∂volume.restrict J,
      HasWeakGradientOn Ω' (fun x => CKN.rescaleVelocity r z₀ u (x, s) i)
        (fun x => CKN.rescaleGradient r z₀ Du (x, s) i) := by
  rcases hdata with ⟨_, _, _, _, _, hlocal⟩
  have hforward := CKN.localBox_forward hr z₀ hbox
  let Ωf : Set Vec3 := CKN.scalingSpace r z₀.1 '' Ω'
  let Jf : Set ℝ := CKN.scalingTime r z₀.2 '' J
  obtain ⟨hu, hDu, hp, _, hL2, hEnergy, hpLp, _, hgrad⟩ := hlocal Ωf Jf hforward
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hscaled := aestronglyMeasurable_rescale_velocity r hr z₀
      hforward.1.measurableSet hforward.2.2.2.1.measurableSet hu
    simpa [Ωf, Jf, rescaledSpace_image_eq r hr z₀.1 Ω',
      rescaledTime_image_eq r hr z₀.2 J] using hscaled
  · have hscaled := aestronglyMeasurable_rescale_gradient r hr z₀
      hforward.1.measurableSet hforward.2.2.2.1.measurableSet hDu
    simpa [Ωf, Jf, rescaledSpace_image_eq r hr z₀.1 Ω',
      rescaledTime_image_eq r hr z₀.2 J] using hscaled
  · have hcomp := aestronglyMeasurable_comp_scaling r hr z₀
      hforward.1.measurableSet hforward.2.2.2.1.measurableSet hp
    have hscaled : AEStronglyMeasurable (CKN.rescalePressure r z₀ p)
        (volume.restrict
          (spaceTimeSet (CKN.rescaledSpace r z₀.1 Ωf)
            (CKN.rescaledTime r z₀.2 Jf))) := by
      have heq : CKN.rescalePressure r z₀ p =
          (r ^ 2) • (p ∘ CKN.scalingParabolic r z₀) := by
        funext z
        rfl
      rw [heq]
      exact hcomp.const_smul (r ^ 2)
    simpa [Ωf, Jf, rescaledSpace_image_eq r hr z₀.1 Ω',
      rescaledTime_image_eq r hr z₀.2 J] using hscaled
  · let U : ParabolicPoint → ℝ≥0∞ := fun z => ‖u z‖ₑ ^ (2 : ℝ)
    let E : ℝ → ℝ≥0∞ := fun s => ∫⁻ x in Ωf, U (x, s)
    let R : ℝ → ℝ≥0∞ := fun s =>
      ∫⁻ x in Ω', ‖CKN.rescaleVelocity r z₀ u (x, s)‖ₑ ^ (2 : ℝ)
    have hU : AEMeasurable U (volume.restrict (spaceTimeSet Ωf Jf)) := by
      exact ENNReal.continuous_rpow_const.measurable.comp_aemeasurable
        hu.enorm
    have hUprod : AEMeasurable U ((volume.restrict Ωf).prod (volume.restrict Jf)) := by
      rw [Measure.prod_restrict]
      exact hU
    have hE : AEMeasurable E (volume.restrict Jf) := hUprod.lintegral_prod_left'
    have hUslice : ∀ᵐ s ∂volume.restrict Jf,
        AEMeasurable (fun x => U (x, s)) (volume.restrict Ωf) :=
      ae_slice_aemeasurable hUprod
    have hmapT := CKN.map_scalingTime_restrict hr z₀.2
      (I := Jf) hforward.2.2.2.1.measurableSet
    rw [rescaledTime_image_eq r hr z₀.2 J] at hmapT
    have hTmeas : Measurable (CKN.scalingTime r z₀.2) := by
      change Measurable (fun s : ℝ => z₀.2 + r ^ 2 * s)
      fun_prop
    have hUslice' : ∀ᵐ s ∂volume.restrict J,
        AEMeasurable (fun x => U (x, CKN.scalingTime r z₀.2 s))
          (volume.restrict Ωf) := by
      have hc : ENNReal.ofReal ((r ^ 2)⁻¹) ≠ 0 :=
        ne_of_gt (ENNReal.ofReal_pos.mpr (by positivity))
      dsimp [Jf] at hUslice
      rw [← Measure.ae_ennreal_smul_measure_eq hc] at hUslice
      rw [← hmapT] at hUslice
      exact ae_of_ae_map hTmeas.aemeasurable hUslice
    have hR : ∀ᵐ s ∂volume.restrict J,
        R s = ENNReal.ofReal (r ^ 2) *
          (ENNReal.ofReal (r⁻¹ ^ 3) * E (CKN.scalingTime r z₀.2 s)) := by
      filter_upwards [hUslice'] with s hs
      have hsp := lintegral_comp_scaling_space r hr z₀.1
        (Ω := Ωf) hforward.1.measurableSet hs
      rw [rescaledSpace_image_eq r hr z₀.1 Ω'] at hsp
      have hmapS := CKN.map_scalingSpace_restrict hr z₀.1
        (Ω := Ωf) hforward.1.measurableSet
      rw [rescaledSpace_image_eq r hr z₀.1 Ω'] at hmapS
      have hFmap : AEMeasurable
          (fun x => U (x, CKN.scalingTime r z₀.2 s))
          (Measure.map (CKN.scalingSpace r z₀.1) (volume.restrict Ω')) := by
        rw [hmapS]
        exact hs.smul_measure (ENNReal.ofReal (r⁻¹ ^ 3))
      have hcomp : AEMeasurable
          (fun x => U (CKN.scalingParabolic r z₀ (x, s)))
          (volume.restrict Ω') := by
        exact hFmap.comp_measurable (by
          change Measurable (fun x : Vec3 => z₀.1 + r • x)
          fun_prop)
      have hconst := lintegral_const_mul''
        (μ := volume.restrict Ω')
        (f := fun x => U (CKN.scalingParabolic r z₀ (x, s)))
        (ENNReal.ofReal (r ^ 2)) hcomp
      calc
        R s = ENNReal.ofReal (r ^ 2) *
            (∫⁻ x in Ω', U (CKN.scalingParabolic r z₀ (x, s))) := by
              dsimp [R]
              rw [show (fun x : Vec3 =>
                  ‖CKN.rescaleVelocity r z₀ u (x, s)‖ₑ ^ (2 : ℝ)) =
                  (fun x => ENNReal.ofReal (r ^ 2) * U (CKN.scalingParabolic r z₀ (x, s)))
                  from by funext x; exact rescaled_velocity_pointwise r hr z₀ u (x, s)]
              simpa [R] using hconst
        _ = ENNReal.ofReal (r ^ 2) *
            (ENNReal.ofReal (r⁻¹ ^ 3) * E (CKN.scalingTime r z₀.2 s)) := by
              have hpar : (fun x : Vec3 => U (CKN.scalingParabolic r z₀ (x, s))) =
                  (fun x => U (CKN.scalingSpace r z₀.1 x,
                    CKN.scalingTime r z₀.2 s)) := by
                funext x
                rw [CKN.scalingParabolic_eq]
              rw [hpar]
              simpa [E] using congrArg
                (fun y => ENNReal.ofReal (r ^ 2) * y) hsp
    have hsource : essSup E (volume.restrict Jf) < ⊤ := by
      simpa [E, Ωf, Jf, U] using hL2
    have hmapE : AEMeasurable E
        (Measure.map (CKN.scalingTime r z₀.2) (volume.restrict J)) := by
      rw [hmapT]
      exact hE.smul_measure (ENNReal.ofReal ((r ^ 2)⁻¹))
    have hess := essSup_map_measure hmapE hTmeas.aemeasurable
      (hg_co := ⟨0, fun _ _ => bot_le⟩)
      (hgf := isBoundedUnder_of_eventually_le (Eventually.of_forall fun _ => le_top))
      (hgf_co := ⟨0, fun _ _ => bot_le⟩)
      (hg_bdd := isBoundedUnder_of_eventually_le (Eventually.of_forall fun _ => le_top))
    have hess' : essSup E (Measure.map (CKN.scalingTime r z₀.2)
        (volume.restrict J)) =
      essSup (fun s => E (CKN.scalingTime r z₀.2 s)) (volume.restrict J) := by
      simpa [Function.comp_def] using hess
    have hres : essSup R (volume.restrict J) < ⊤ := by
      rw [essSup_congr_ae hR]
      rw [ENNReal.essSup_const_mul]
      rw [ENNReal.essSup_const_mul]
      rw [← hess']
      rw [hmapT, essSup_ennreal_smul_measure]
      · exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
          (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hsource)
      · exact ne_of_gt (ENNReal.ofReal_pos.mpr (by positivity))
    simpa [R] using hres
  · let U : ParabolicPoint → ℝ≥0∞ := fun z => ‖u z‖ₑ ^ (2 : ℝ)
    let D : ParabolicPoint → ℝ≥0∞ := fun z => ‖Du z‖ₑ ^ (2 : ℝ)
    have hU : AEMeasurable U (volume.restrict (spaceTimeSet Ωf Jf)) := by
      exact ENNReal.continuous_rpow_const.measurable.comp_aemeasurable hu.enorm
    have hD : AEMeasurable D (volume.restrict (spaceTimeSet Ωf Jf)) := by
      exact ENNReal.continuous_rpow_const.measurable.comp_aemeasurable hDu.enorm
    have hUcomp := aemeasurable_comp_scaling r hr z₀
      hforward.1.measurableSet hforward.2.2.2.1.measurableSet hU
    have hDcomp := aemeasurable_comp_scaling r hr z₀
      hforward.1.measurableSet hforward.2.2.2.1.measurableSet hD
    rw [rescaledSpace_image_eq r hr z₀.1 Ω',
      rescaledTime_image_eq r hr z₀.2 J] at hUcomp hDcomp
    have hUchange := lintegral_comp_scaling r hr z₀
      (Ω := Ωf) (I := Jf) hforward.1.measurableSet
      hforward.2.2.2.1.measurableSet hU
    have hDchange := lintegral_comp_scaling r hr z₀
      (Ω := Ωf) (I := Jf) hforward.1.measurableSet
      hforward.2.2.2.1.measurableSet hD
    rw [rescaledSpace_image_eq r hr z₀.1 Ω',
      rescaledTime_image_eq r hr z₀.2 J] at hUchange hDchange
    have hUfin : (∫⁻ z in spaceTimeSet Ωf Jf, U z) < ⊤ := by
      exact lt_of_le_of_lt
        (lintegral_mono fun z => le_add_right le_rfl) hEnergy
    have hDfin : (∫⁻ z in spaceTimeSet Ωf Jf, D z) < ⊤ := by
      exact lt_of_le_of_lt
        (lintegral_mono fun z => le_add_left le_rfl) hEnergy
    have hpoint : ∀ z : ParabolicPoint,
        ‖CKN.rescaleVelocity r z₀ u z‖ₑ ^ (2 : ℝ) +
            ‖CKN.rescaleGradient r z₀ Du z‖ₑ ^ (2 : ℝ) =
          ENNReal.ofReal (r ^ 2) * U (CKN.scalingParabolic r z₀ z) +
            ENNReal.ofReal (r ^ 4) * D (CKN.scalingParabolic r z₀ z) := by
      intro z
      exact rescaled_energy_pointwise r hr z₀ u Du z
    calc
      (∫⁻ z in spaceTimeSet Ω' J,
          ‖CKN.rescaleVelocity r z₀ u z‖ₑ ^ (2 : ℝ) +
            ‖CKN.rescaleGradient r z₀ Du z‖ₑ ^ (2 : ℝ)) =
        ∫⁻ z in spaceTimeSet Ω' J,
          ENNReal.ofReal (r ^ 2) * U (CKN.scalingParabolic r z₀ z) +
            ENNReal.ofReal (r ^ 4) * D (CKN.scalingParabolic r z₀ z) := by
              exact lintegral_congr hpoint
      _ = ENNReal.ofReal (r ^ 2) *
            (∫⁻ z in spaceTimeSet Ω' J, U (CKN.scalingParabolic r z₀ z)) +
          ENNReal.ofReal (r ^ 4) *
            (∫⁻ z in spaceTimeSet Ω' J, D (CKN.scalingParabolic r z₀ z)) := by
              have hsum := lintegral_add_left'
                (μ := volume.restrict (spaceTimeSet Ω' J))
                (hUcomp.const_mul (ENNReal.ofReal (r ^ 2)))
                (fun z => ENNReal.ofReal (r ^ 4) * D (CKN.scalingParabolic r z₀ z))
              calc
                _ = (∫⁻ z in spaceTimeSet Ω' J,
                    ENNReal.ofReal (r ^ 2) * (U ∘ CKN.scalingParabolic r z₀) z) +
                    ∫⁻ z in spaceTimeSet Ω' J,
                      ENNReal.ofReal (r ^ 4) * D (CKN.scalingParabolic r z₀ z) := by
                        simpa [Function.comp_def] using hsum
                _ = _ := by
                  rw [lintegral_const_mul'' _ hUcomp]
                  have hDconst := lintegral_const_mul''
                    (μ := volume.restrict (spaceTimeSet Ω' J))
                    (f := D ∘ CKN.scalingParabolic r z₀)
                    (ENNReal.ofReal (r ^ 4)) hDcomp
                  rw [show (∫⁻ z in spaceTimeSet Ω' J,
                      ENNReal.ofReal (r ^ 4) * D (CKN.scalingParabolic r z₀ z)) =
                    ENNReal.ofReal (r ^ 4) *
                      ∫⁻ z in spaceTimeSet Ω' J, D (CKN.scalingParabolic r z₀ z) by
                    simpa [Function.comp_def] using hDconst]
                  simp only [Function.comp_apply]
      _ = ENNReal.ofReal (r ^ 2) *
            (ENNReal.ofReal (r⁻¹ ^ 5) *
              ∫⁻ z in spaceTimeSet Ωf Jf, U z) +
          ENNReal.ofReal (r ^ 4) *
            (ENNReal.ofReal (r⁻¹ ^ 5) *
              ∫⁻ z in spaceTimeSet Ωf Jf, D z) := by
              rw [hUchange, hDchange]
      _ < ⊤ := by
        apply ENNReal.add_lt_top.mpr
        constructor
        · exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
            (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hUfin)
        · exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
            (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hDfin)
  · have hscaled := memLp_rescale_pressure r hr z₀
      (Ω := Ωf) (I := Jf) hforward.1.measurableSet
      hforward.2.2.2.1.measurableSet hpLp
    simpa [Ωf, Jf, rescaledSpace_image_eq r hr z₀.1 Ω',
      rescaledTime_image_eq r hr z₀.2 J] using hscaled
  · intro i
    have hUi : AEStronglyMeasurable (fun z => u z i)
        (volume.restrict (spaceTimeSet Ωf Jf)) :=
      (continuous_apply i).comp_aestronglyMeasurable hu
    have hDui : AEStronglyMeasurable (fun z => Du z i)
        (volume.restrict (spaceTimeSet Ωf Jf)) :=
      (continuous_apply i).comp_aestronglyMeasurable hDu
    have hUiProd : AEStronglyMeasurable (fun z => u z i)
        ((volume.restrict Ωf).prod (volume.restrict Jf)) := by
      rw [Measure.prod_restrict]
      exact hUi
    have hDuiProd : AEStronglyMeasurable (fun z => Du z i)
        ((volume.restrict Ωf).prod (volume.restrict Jf)) := by
      rw [Measure.prod_restrict]
      exact hDui
    have hUiSlice : ∀ᵐ s ∂volume.restrict Jf,
        AEStronglyMeasurable (fun x => u (x, s) i) (volume.restrict Ωf) :=
      ae_slice_aestronglyMeasurable hUiProd
    have hDuiSlice : ∀ᵐ s ∂volume.restrict Jf,
        AEStronglyMeasurable (fun x => Du (x, s) i) (volume.restrict Ωf) :=
      ae_slice_aestronglyMeasurable hDuiProd
    have hgradSource : ∀ᵐ s ∂volume.restrict Jf,
        HasWeakGradientOn Ωf (fun x => u (x, s) i)
          (fun x => Du (x, s) i) := hgrad i
    have hmapT := CKN.map_scalingTime_restrict hr z₀.2
      (I := Jf) hforward.2.2.2.1.measurableSet
    rw [rescaledTime_image_eq r hr z₀.2 J] at hmapT
    have hTmeas : Measurable (CKN.scalingTime r z₀.2) := by
      change Measurable (fun s : ℝ => z₀.2 + r ^ 2 * s)
      fun_prop
    have hsliceU : ∀ᵐ s ∂volume.restrict J,
        AEStronglyMeasurable
          (fun x => u (x, CKN.scalingTime r z₀.2 s) i) (volume.restrict Ωf) := by
      have hc : ENNReal.ofReal ((r ^ 2)⁻¹) ≠ 0 :=
        ne_of_gt (ENNReal.ofReal_pos.mpr (by positivity))
      dsimp [Jf] at hUiSlice
      rw [← Measure.ae_ennreal_smul_measure_eq hc] at hUiSlice
      rw [← hmapT] at hUiSlice
      exact ae_of_ae_map hTmeas.aemeasurable hUiSlice
    have hsliceDu : ∀ᵐ s ∂volume.restrict J,
        AEStronglyMeasurable
          (fun x => Du (x, CKN.scalingTime r z₀.2 s) i) (volume.restrict Ωf) := by
      have hc : ENNReal.ofReal ((r ^ 2)⁻¹) ≠ 0 :=
        ne_of_gt (ENNReal.ofReal_pos.mpr (by positivity))
      dsimp [Jf] at hDuiSlice
      rw [← Measure.ae_ennreal_smul_measure_eq hc] at hDuiSlice
      rw [← hmapT] at hDuiSlice
      exact ae_of_ae_map hTmeas.aemeasurable hDuiSlice
    have hgradTarget : ∀ᵐ s ∂volume.restrict J,
        HasWeakGradientOn Ωf
          (fun x => u (x, CKN.scalingTime r z₀.2 s) i)
          (fun x => Du (x, CKN.scalingTime r z₀.2 s) i) := by
      have hc : ENNReal.ofReal ((r ^ 2)⁻¹) ≠ 0 :=
        ne_of_gt (ENNReal.ofReal_pos.mpr (by positivity))
      dsimp [Jf] at hgradSource
      rw [← Measure.ae_ennreal_smul_measure_eq hc] at hgradSource
      rw [← hmapT] at hgradSource
      exact ae_of_ae_map hTmeas.aemeasurable hgradSource
    filter_upwards [hgradTarget, hsliceU, hsliceDu] with s hs hUs hDs
    change ∀ j : Fin 3, _
    intro j
    have hDsj : AEStronglyMeasurable
        (fun x => Du (x, CKN.scalingTime r z₀.2 s) i j)
        (volume.restrict Ωf) :=
      (continuous_apply j).comp_aestronglyMeasurable hDs
    have hscaled := CKN.hasWeakPartialDerivOn_scaling r hr z₀.1
      hforward.1.measurableSet j (by rfl) (hs j) hUs hDsj
    simpa [CKN.rescaleVelocity, CKN.rescaleGradient, CKN.scalingParabolic,
      CKN.scalingSpace, CKN.scalingTime, parabolicTranslate, parabolicScale] using hscaled

private theorem setIntegral_eq_of_support_subset
    {D Q K : Set ParabolicPoint} (f : ParabolicPoint → ℝ)
    (hD : MeasurableSet D) (hQD : Q ⊆ D) (hKQ : K ⊆ Q)
    (hzero : ∀ z, z ∉ K → f z = 0) :
    ∫ z in D, f z = ∫ z in Q, f z := by
  apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hD hQD
  intro z hz
  apply hzero z
  intro hK
  exact hz.2 (hKQ hK)

private theorem spatialPartial_zero_outside_parabolic_tsupport
    {ψ : ParabolicPoint → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) (show Vec3 × ℝ → ℝ from ψ))
    {z : ParabolicPoint} (hz : z ∉ tsupport (show ParabolicPoint → ℝ from ψ))
    (i : Fin 3) : spatialPartial ψ i z = 0 := by
  have hq : parabolicHomeomorph z ∉ tsupport (show Vec3 × ℝ → ℝ from ψ) := by
    intro hmem
    apply hz
    rw [CKN.tsupport_parabolic_eq (show ParabolicPoint → ℝ from ψ)]
    exact hmem
  have hzero := CKN.spatialPartial_zero_of_not_mem_tsupport_public hψ hq i
  change spatialPartial ψ i (z.1, z.2) = 0
  exact hzero

private theorem timePartial_zero_outside_parabolic_tsupport
    {ψ : ParabolicPoint → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) (show Vec3 × ℝ → ℝ from ψ))
    {z : ParabolicPoint} (hz : z ∉ tsupport (show ParabolicPoint → ℝ from ψ)) :
    timePartial ψ z = 0 := by
  have hq : parabolicHomeomorph z ∉ tsupport (show Vec3 × ℝ → ℝ from ψ) := by
    intro hmem
    apply hz
    rw [CKN.tsupport_parabolic_eq (show ParabolicPoint → ℝ from ψ)]
    exact hmem
  have hzero := CKN.timePartial_zero_of_not_mem_tsupport_public hψ hq
  change timePartial ψ (z.1, z.2) = 0
  exact hzero

private theorem component_tsupport_subset
    {φ : Vec3 × ℝ → Vec3} (i : Fin 3) :
    tsupport (fun z => φ z i) ⊆ tsupport φ := by
  apply closure_mono
  intro z hz
  change φ z i ≠ 0 at hz
  apply Function.mem_support.mpr
  intro hzero
  exact hz (congrFun hzero i)

private theorem component_contDiff
    {φ : Vec3 × ℝ → Vec3}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (i : Fin 3) :
    ContDiff ℝ (⊤ : ℕ∞) (fun z => φ z i) :=
  (contDiff_apply ℝ ℝ i).comp hφ

private theorem regularPoint_mono_time
    {Ω : Set Vec3} {I J : Set ℝ} {u : ParabolicPoint → Vec3}
    {z : ParabolicPoint} (hIJ : I ⊆ J)
    (hreg : IsRegularPoint Ω I u z) : IsRegularPoint Ω J u z := by
  rcases hreg with ⟨hz, N, hNopen, hzN, hNsub, γ, hγ, hγle, w, hAE, hHolder⟩
  refine ⟨?_, N, hNopen, hzN, ?_, γ, hγ, hγle, w, hAE, hHolder⟩
  · exact ⟨hz.1, hIJ hz.2⟩
  · intro y hy
    exact ⟨(hNsub hy).1, hIJ (hNsub hy).2⟩

private theorem regularPoint_restrict_time
    {Ω : Set Vec3} {I J : Set ℝ} {u : ParabolicPoint → Vec3}
    {z : ParabolicPoint} (hΩ : IsOpen Ω) (hJ : IsOpen J)
    (hzJ : z ∈ spaceTimeSet Ω J)
    (hreg : IsRegularPoint Ω I u z) : IsRegularPoint Ω J u z := by
  rcases hreg with ⟨_, N, hNopen, hzN, hNsub, γ, hγ, hγle, w, hAE, hHolder⟩
  let N' := N ∩ spaceTimeSet Ω J
  have hN'open : IsOpen N' := by
    exact hNopen.inter (isOpen_spaceTimeSet Ω J hΩ hJ)
  have hzN' : z ∈ N' := ⟨hzN, hzJ⟩
  have hN'sub : N' ⊆ spaceTimeSet Ω J := inter_subset_right
  have hAE' : w =ᵐ[volume.restrict N'] u :=
    ae_restrict_of_ae_restrict_of_subset inter_subset_left hAE
  rcases hHolder with ⟨B, K, hB, hK, hbound, hsemi⟩
  have hHolder' : ParabolicHolderVecOn N' w γ := by
    refine ⟨B, K, hB, hK, ?_, ?_⟩
    · intro y hy
      exact hbound y hy.1
    · intro y hy y' hy'
      exact hsemi y hy.1 y' hy'.1
  exact ⟨hzJ, N', hN'open, hzN', hN'sub, γ, hγ, hγle, w, hAE', hHolder'⟩


/-- The global Escauriaza–Seregin–Šverák theorem follows from the local
regularity and associated-pressure statements. -/
theorem essGlobal_of_localRegularity_and_associatedPressure
    (hE1 : ∀ u : ParabolicPoint → Vec3,
    ∀ Du : ParabolicPoint → Fin 3 → Vec3,
    ∀ p : ParabolicPoint → ℝ,
      AEStronglyMeasurable u
        (volume.restrict
          (spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0))) →
      AEStronglyMeasurable Du
        (volume.restrict
          (spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0))) →
      AEStronglyMeasurable p
        (volume.restrict
          (spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0))) →
      essSup
        (fun t : ℝ => ∫⁻ x in vec3Ball (0 : Vec3) 1, ‖u (x, t)‖ₑ ^ (2 : ℝ))
        (volume.restrict (Ioo (-1) 0)) < ⊤ →
      (∫⁻ z in spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0),
        ‖u z‖ₑ ^ (2 : ℝ) + ‖Du z‖ₑ ^ (2 : ℝ)) < ⊤ →
      MemLp p (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict
          (spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0))) →
      essSup
        (fun t : ℝ => ∫⁻ x in vec3Ball (0 : Vec3) 1,
          ENNReal.ofReal (vec3EuclideanNorm (u (x, t))) ^ (3 : ℝ))
        (volume.restrict (Ioo (-1) 0)) < ⊤ →
      (∀ᵐ t ∂(volume.restrict (Ioo (-1) 0)), ∀ i : Fin 3,
        HasWeakGradientOn (vec3Ball (0 : Vec3) 1)
          (fun x => u (x, t) i) (fun x => Du (x, t) i)) →
      (∀ ψ : ParabolicPoint → ℝ,
        ψ ∈ spaceTimeTestFunction (V := ℝ)
          (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0) →
        ∫ z in spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0),
          ∑ i : Fin 3, u z i * spatialPartial ψ i z = 0) →
      (∀ φ : ParabolicPoint → Vec3,
        φ ∈ spaceTimeTestFunction (V := Vec3)
          (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0) →
        ∫ z in spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0),
          (-(∑ i : Fin 3, u z i * timePartial (fun y => φ y i) z))
            - ∑ i : Fin 3, ∑ j : Fin 3,
                u z i * u z j * spatialPartial (fun y => φ y i) j z
            + ∑ i : Fin 3, ∑ j : Fin 3,
                Du z i j * spatialPartial (fun y => φ y i) j z
            - p z * ∑ i : Fin 3, spatialPartial (fun y => φ y i) i z
            - ∑ i : Fin 3, ((0 : ParabolicPoint → Vec3) z i) * φ z i = 0) →
      ∃ γ : ℝ, 0 < γ ∧ γ ≤ 1 ∧
        ∃ w : ParabolicPoint → Vec3,
          w =ᵐ[volume.restrict
            (parabolicCylinder (0 : Vec3) 0 (1 / 2 : ℝ))] u ∧
          ParabolicHolderVecOn
            (closure (parabolicCylinder (0 : Vec3) 0 (1 / 2 : ℝ))) w γ)
    (hL3 : ∀ T : ℝ, ∀ a : Vec3 → Vec3,
    ∀ u : ParabolicPoint → Vec3,
    ∀ Du : ParabolicPoint → Fin 3 → Vec3,
      IsLerayHopfSolution T a u Du →
      ∃ p : ParabolicPoint → ℝ,
        MemLp p (ENNReal.ofReal (5 / 3 : ℝ))
          (volume.restrict (spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T))) ∧
        (∀ φ : ParabolicPoint → Vec3,
          φ ∈ spaceTimeTestFunction (V := Vec3) (Set.univ : Set Vec3) (Ioo 0 T) →
          ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T),
            (-(∑ i : Fin 3, u z i * timePartial (fun y => φ y i) z))
              - ∑ i : Fin 3, ∑ j : Fin 3,
                  u z i * u z j * spatialPartial (fun y => φ y i) j z
              + ∑ i : Fin 3, ∑ j : Fin 3,
                  Du z i j * spatialPartial (fun y => φ y i) j z
              - p z * ∑ i : Fin 3, spatialPartial (fun y => φ y i) i z
              - ∑ i : Fin 3, ((0 : ParabolicPoint → Vec3) z i) * φ z i = 0) ∧
        (essSup
          (fun t : ℝ => ∫⁻ x : Vec3,
            ENNReal.ofReal (vec3EuclideanNorm (u (x, t))) ^ (3 : ℝ))
          (volume.restrict (Ioo 0 T)) < ⊤ →
          essSup
            (fun t : ℝ => ∫⁻ x : Vec3, ‖p (x, t)‖ₑ ^ (3 / 2 : ℝ))
            (volume.restrict (Ioo 0 T)) < ⊤)) :
    ∀ T : ℝ, ∀ a : Vec3 → Vec3,
    ∀ u : ParabolicPoint → Vec3,
    ∀ Du : ParabolicPoint → Fin 3 → Vec3,
      IsLerayHopfSolution T a u Du →
      essSup
        (fun t : ℝ => ∫⁻ x : Vec3,
          ENNReal.ofReal (vec3EuclideanNorm (u (x, t))) ^ (3 : ℝ))
        (volume.restrict (Ioo 0 T)) < ⊤ →
      SingularSet (Set.univ : Set Vec3) (Ioo 0 T) u = ∅ := by
  intro T a u Du hLH hVel
  classical
  obtain ⟨p, hpMem, hpMom, hpMixed⟩ := hL3 T a u Du hLH
  have hTpos : 0 < T := hLH.1
  let M : ℝ≥0∞ := essSup
    (fun t : ℝ => ∫⁻ x : Vec3,
      ENNReal.ofReal (vec3EuclideanNorm (u (x, t))) ^ (3 : ℝ))
    (volume.restrict (Ioo 0 T))
  have hMtop : M < ⊤ := hVel
  have hPMixed : essSup
      (fun t : ℝ => ∫⁻ x : Vec3, ‖p (x, t)‖ₑ ^ (3 / 2 : ℝ))
      (volume.restrict (Ioo 0 T)) < ⊤ := hpMixed hVel
  have hSourceData := lerayHopf_pressureData T a u Du p hLH hpMem hPMixed
  have hDivSource := lerayHopf_spaceTime_divergence T a u Du hLH
  have hS2Source : ∀ ψ : ParabolicPoint → ℝ,
      ψ ∈ spaceTimeTestFunction (V := ℝ) (Set.univ : Set Vec3) (Ioo 0 T) →
      IntegrableOn (fun z => ∑ i : Fin 3, u z i * spatialPartial ψ i z)
          (tsupport ψ) volume ∧
      ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T),
        ∑ i : Fin 3, u z i * spatialPartial ψ i z = 0 := by
    intro ψ hψ
    exact ⟨CKN.divergenceFree_integrand_integrableOn_of_data hSourceData hψ,
      hDivSource ψ hψ⟩
  have hS3Source : ∀ φ : ParabolicPoint → Vec3,
      φ ∈ spaceTimeTestFunction (V := Vec3) (Set.univ : Set Vec3) (Ioo 0 T) →
      IntegrableOn (fun z =>
        (-(∑ i : Fin 3, u z i * timePartial (fun y => φ y i) z))
          - ∑ i : Fin 3, ∑ j : Fin 3,
              u z i * u z j * spatialPartial (fun y => φ y i) j z
          + ∑ i : Fin 3, ∑ j : Fin 3,
              Du z i j * spatialPartial (fun y => φ y i) j z
          - p z * ∑ i : Fin 3, spatialPartial (fun y => φ y i) i z
          - ∑ i : Fin 3, ((0 : ParabolicPoint → Vec3) z i) * φ z i)
          (tsupport φ) volume ∧
      ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioo 0 T),
        (-(∑ i : Fin 3, u z i * timePartial (fun y => φ y i) z)
          - ∑ i : Fin 3, ∑ j : Fin 3,
              u z i * u z j * spatialPartial (fun y => φ y i) j z
          + ∑ i : Fin 3, ∑ j : Fin 3,
              Du z i j * spatialPartial (fun y => φ y i) j z
          - p z * ∑ i : Fin 3, spatialPartial (fun y => φ y i) i z
          - ∑ i : Fin 3, ((0 : ParabolicPoint → Vec3) z i) * φ z i) = 0 := by
    intro φ hφ
    exact ⟨CKN.momentum_integrand_integrableOn_of_data hSourceData hφ,
      hpMom φ hφ⟩
  have hReg : ∀ z : ParabolicPoint, z ∈ spaceTimeSet (Set.univ : Set Vec3)
      (Ioo 0 T) → IsRegularPoint (Set.univ : Set Vec3) (Ioo 0 T) u z := by
    intro z hz
    have hx : z.1 ∈ (Set.univ : Set Vec3) := Set.mem_univ _
    have ht : z.2 ∈ Ioo 0 T := hz.2
    let q : ℝ := min (8 * z.2 / 7) (8 * (T - z.2))
    have hq : 0 < q := by
      dsimp [q]
      apply lt_min
      · exact div_pos (mul_pos (by norm_num) ht.1) (by norm_num)
      · exact mul_pos (by norm_num) (sub_pos.mpr ht.2)
    let r : ℝ := Real.sqrt (q / 2)
    have hr : 0 < r := Real.sqrt_pos.2 (by positivity)
    have hrSq : r ^ 2 = q / 2 := by
      dsimp [r]
      exact Real.sq_sqrt (by positivity)
    have hrLower : r ^ 2 < 8 * z.2 / 7 := by
      calc
        r ^ 2 = q / 2 := hrSq
        _ < q := half_lt_self hq
        _ ≤ 8 * z.2 / 7 := min_le_left _ _
    have hrUpper : r ^ 2 < 8 * (T - z.2) := by
      calc
        r ^ 2 = q / 2 := hrSq
        _ < q := half_lt_self hq
        _ ≤ 8 * (T - z.2) := min_le_right _ _
    let t₁ : ℝ := z.2 + r ^ 2 / 8
    have htLower : 0 < t₁ - r ^ 2 := by
      dsimp [t₁]
      nlinarith only [ht.1, hrLower]
    have htUpper : t₁ < T := by
      dsimp [t₁]
      nlinarith only [ht.2, hrUpper]
    let Iᵣ : Set ℝ := CKN.rescaledTime r t₁ (Ioo 0 T)
    have hIcc : Icc (-1 : ℝ) 0 ⊆ Iᵣ := by
      intro s hs
      change 0 < t₁ + r ^ 2 * s ∧ t₁ + r ^ 2 * s < T
      have hr2 : 0 ≤ r ^ 2 := sq_nonneg r
      have hlow := mul_le_mul_of_nonneg_left hs.1 hr2
      have hupp := mul_le_mul_of_nonneg_left hs.2 hr2
      constructor <;> linarith only [htLower, htUpper, hlow, hupp]
    have hIoo : Ioo (-1 : ℝ) 0 ⊆ Iᵣ := by
      intro s hs
      exact hIcc ⟨le_of_lt hs.1, le_of_lt hs.2⟩
    let Ωᵣ : Set Vec3 := CKN.rescaledSpace r z.1 (Set.univ : Set Vec3)
    have hBall : closure (vec3Ball (0 : Vec3) 1) ⊆ Ωᵣ := by
      intro x _
      simp [Ωᵣ, CKN.rescaledSpace]
    have hBallOpen : vec3Ball (0 : Vec3) 1 ⊆ Ωᵣ :=
      subset_closure.trans hBall
    have hLocalBox : CKN.localBox Ωᵣ Iᵣ (vec3Ball (0 : Vec3) 1)
        (Ioo (-1) 0) := by
      refine ⟨isOpen_vec3Ball _ _, CKN.Foundation.Parabolic.isCompact_closure_vec3Ball
        (by norm_num : (0 : ℝ) < 1), hBall, ordConnected_Ioo, ?_, ?_⟩
      · rw [closure_Ioo (by norm_num : (-1 : ℝ) ≠ 0)]
        exact isCompact_Icc
      · rw [closure_Ioo (by norm_num : (-1 : ℝ) ≠ 0)]
        exact hIcc
    have hScaledData := rescaleData_local hSourceData (z.1, t₁) r hr
      (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0) hLocalBox
    rcases hScaledData with
      ⟨hUscaled, hDuscaled, hPscaled, hL2scaled, hEnergyscaled,
        hPressureScaled, hGradientScaled⟩
    have hUprod : AEStronglyMeasurable
        (fun z : Vec3 × ℝ => u (z.1, z.2))
        ((volume.restrict (Set.univ : Set Vec3)).prod
          (volume.restrict (Ioo 0 T))) := by
      rw [Measure.prod_restrict]
      have hU := hLH.2.2.1
      rw [CKN.Foundation.Parabolic.Integration.volume_parabolicPoint_eq_prod] at hU
      change AEStronglyMeasurable (fun z : Vec3 × ℝ => u (z.1, z.2))
        ((volume.prod volume).restrict ((Set.univ : Set Vec3) ×ˢ Ioo 0 T)) at hU
      simpa only [Measure.prod_restrict] using hU
    have hUSlice' : ∀ᵐ s ∂volume.restrict (Ioo 0 T),
        AEStronglyMeasurable (fun x : Vec3 => u (x, s))
          (volume.restrict (Set.univ : Set Vec3)) :=
      ae_slice_aestronglyMeasurable hUprod
    have hUSlice : ∀ᵐ s ∂volume.restrict (Ioo 0 T),
        AEStronglyMeasurable (fun x : Vec3 => u (x, s)) volume := by
      filter_upwards [hUSlice'] with s hs
      simpa only [Measure.restrict_univ] using hs
    have hMassSlice : ∀ᵐ s ∂volume.restrict (Ioo 0 T),
        ∫⁻ x : Vec3, ENNReal.ofReal (vec3EuclideanNorm (u (x, s))) ^ (3 : ℝ)
          ≤ M := by
      exact ae_le_essSup (μ := volume.restrict (Ioo 0 T))
        (f := fun s : ℝ =>
          ∫⁻ x : Vec3,
            ENNReal.ofReal (vec3EuclideanNorm (u (x, s))) ^ (3 : ℝ))
    have hSourceSlice := hUSlice.and hMassSlice
    have hScaledSlice := blowup_ae_time_pullback_on r t₁ hr
      (Ioo 0 T) (Ioo (-1) 0) measurableSet_Ioo hIoo
      (fun s => AEStronglyMeasurable (fun x : Vec3 => u (x, s)) volume ∧
        ∫⁻ x : Vec3,
          ENNReal.ofReal (vec3EuclideanNorm (u (x, s))) ^ (3 : ℝ) ≤ M)
      hSourceSlice
    have hVelocityBound : ∀ᵐ s ∂volume.restrict (Ioo (-1) 0),
        ∫⁻ x in vec3Ball (0 : Vec3) 1,
          ENNReal.ofReal (vec3EuclideanNorm
            (parabolicRescaleVelocity z.1 t₁ r u (x, s))) ^ (3 : ℝ) ≤ M := by
      filter_upwards [hScaledSlice] with s hs
      have hmass := blowup_rescaled_ball_velocity_mass_eq
        (fun x : Vec3 => u (x, CKN.scalingTime r t₁ s)) hs.1 z.1 0 r hr
      have hpoint (x : Vec3) :
          parabolicRescaleVelocity z.1 t₁ r u (x, s) =
            r • u (z.1 + r • x, CKN.scalingTime r t₁ s) := by
        simp [parabolicRescaleVelocity, CKN.scalingTime,
          parabolicTranslate, parabolicScale]
      calc
        _ = ∫⁻ x in vec3Ball (0 : Vec3) 1,
            ENNReal.ofReal (vec3EuclideanNorm
              (r • u (z.1 + r • x, CKN.scalingTime r t₁ s))) ^ (3 : ℝ) := by
                apply lintegral_congr
                intro x
                rw [hpoint]
        _ = ∫⁻ y in vec3Ball (z.1 + r • (0 : Vec3)) r,
            ENNReal.ofReal (vec3EuclideanNorm
              (u (y, CKN.scalingTime r t₁ s))) ^ (3 : ℝ) := hmass
        _ ≤ ∫⁻ y : Vec3,
            ENNReal.ofReal (vec3EuclideanNorm
              (u (y, CKN.scalingTime r t₁ s))) ^ (3 : ℝ) :=
            by
              simpa only [MeasureTheory.setLIntegral_univ] using
                (lintegral_mono_set (μ := (volume : Measure Vec3))
                  (f := fun y : Vec3 => ENNReal.ofReal
                    (vec3EuclideanNorm (u (y, CKN.scalingTime r t₁ s))) ^
                      (3 : ℝ))
                  (Set.subset_univ (vec3Ball (z.1 + r • (0 : Vec3)) r)))
        _ ≤ M := by simpa using hs.2
    have hL3scaled : essSup
        (fun s : ℝ => ∫⁻ x in vec3Ball (0 : Vec3) 1,
          ENNReal.ofReal (vec3EuclideanNorm
            (parabolicRescaleVelocity z.1 t₁ r u (x, s))) ^ (3 : ℝ))
        (volume.restrict (Ioo (-1) 0)) < ⊤ := by
      exact (essSup_le_of_ae_le M hVelocityBound).trans_lt hMtop
    let uᵣ : ParabolicPoint → Vec3 := parabolicRescaleVelocity z.1 t₁ r u
    let Duᵣ : ParabolicPoint → Fin 3 → Vec3 :=
      parabolicRescaleGradient z.1 t₁ r Du
    let pᵣ : ParabolicPoint → ℝ := parabolicRescalePressure z.1 t₁ r p
    have huEq : uᵣ = CKN.rescaleVelocity r (z.1, t₁) u := by
      funext y
      rfl
    have hDuEq : Duᵣ = CKN.rescaleGradient r (z.1, t₁) Du := by
      funext y
      funext i
      rfl
    have hpEq : pᵣ = CKN.rescalePressure r (z.1, t₁) p := by
      funext y
      rfl
    have hUᵣ : AEStronglyMeasurable uᵣ
        (volume.restrict (spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0))) := by
      rw [huEq]
      exact hUscaled
    have hDuᵣ : AEStronglyMeasurable Duᵣ
        (volume.restrict (spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0))) := by
      rw [hDuEq]
      exact hDuscaled
    have hpᵣ : AEStronglyMeasurable pᵣ
        (volume.restrict (spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0))) := by
      rw [hpEq]
      exact hPscaled
    have hL2ᵣ : essSup
        (fun s : ℝ => ∫⁻ x in vec3Ball (0 : Vec3) 1,
          ‖uᵣ (x, s)‖ₑ ^ (2 : ℝ)) (volume.restrict (Ioo (-1) 0)) < ⊤ := by
      simpa only [huEq] using hL2scaled
    have hEnergyᵣ : (∫⁻ z in spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0),
        ‖uᵣ z‖ₑ ^ (2 : ℝ) + ‖Duᵣ z‖ₑ ^ (2 : ℝ)) < ⊤ := by
      simpa only [huEq, hDuEq] using hEnergyscaled
    have hpLpᵣ : MemLp pᵣ (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict
          (spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0))) := by
      simpa only [hpEq] using hPressureScaled
    have hGradientᵣ : ∀ᵐ s ∂volume.restrict (Ioo (-1) 0),
        ∀ i : Fin 3, HasWeakGradientOn (vec3Ball (0 : Vec3) 1)
          (fun x => uᵣ (x, s) i) (fun x => Duᵣ (x, s) i) := by
      apply ae_all_iff.mpr
      intro i
      simpa only [huEq, hDuEq] using hGradientScaled i
    have hS2ᵣ : ∀ ψ : ParabolicPoint → ℝ,
        ψ ∈ spaceTimeTestFunction (V := ℝ) (vec3Ball (0 : Vec3) 1)
          (Ioo (-1) 0) →
        ∫ z in spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0),
          ∑ i : Fin 3, uᵣ z i * spatialPartial ψ i z = 0 := by
      intro ψ hψ
      have hψᵣ : ψ ∈ spaceTimeTestFunction (V := ℝ) Ωᵣ Iᵣ := by
        refine ⟨hψ.1, hψ.2.1, ?_⟩
        exact hψ.2.2.trans
          (Set.prod_mono hBallOpen hIoo)
      have hscaled := CKN.s2_rescale (MeasurableSet.univ)
        measurableSet_Ioo hS2Source (z.1, t₁) hr ψ hψᵣ
      have hzero : ∀ y, y ∉ tsupport (show ParabolicPoint → ℝ from ψ) →
          ∑ i : Fin 3, CKN.rescaleVelocity r (z.1, t₁) u y i *
            spatialPartial ψ i y = 0 := by
        intro y hy
        have hpartial i := spatialPartial_zero_outside_parabolic_tsupport hψ.1 hy i
        simp [hpartial]
      have hset := setIntegral_eq_of_support_subset
        (f := fun y => ∑ i : Fin 3,
          CKN.rescaleVelocity r (z.1, t₁) u y i * spatialPartial ψ i y)
        (MeasurableSet.univ.prod
          (measurableSet_Ioo.preimage (by
            change Measurable (fun s : ℝ => t₁ + r ^ 2 * s)
            fun_prop)))
        (Set.prod_mono hBallOpen hIoo)
        (CKN.tsupport_parabolic_subset_spaceTimeSet hψ) hzero
      have hscaledZero := hset.symm.trans hscaled.2
      simpa [spaceTimeSet, uᵣ, CKN.rescaleVelocity, CKN.scalingParabolic,
        CKN.scalingSpace, CKN.scalingTime, parabolicRescaleVelocity,
        parabolicTranslate, parabolicScale] using hscaledZero
    have hS3ᵣ : ∀ φ : ParabolicPoint → Vec3,
        φ ∈ spaceTimeTestFunction (V := Vec3) (vec3Ball (0 : Vec3) 1)
          (Ioo (-1) 0) →
        ∫ z in spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0),
          (-(∑ i : Fin 3, uᵣ z i * timePartial (fun y => φ y i) z)
            - ∑ i : Fin 3, ∑ j : Fin 3,
                uᵣ z i * uᵣ z j * spatialPartial (fun y => φ y i) j z
            + ∑ i : Fin 3, ∑ j : Fin 3,
                Duᵣ z i j * spatialPartial (fun y => φ y i) j z
            - pᵣ z * ∑ i : Fin 3, spatialPartial (fun y => φ y i) i z
            - ∑ i : Fin 3, ((0 : ParabolicPoint → Vec3) z i) * φ z i) = 0 := by
      intro φ hφ
      have hφᵣ : φ ∈ spaceTimeTestFunction (V := Vec3) Ωᵣ Iᵣ := by
        refine ⟨hφ.1, hφ.2.1, ?_⟩
        exact hφ.2.2.trans
          (Set.prod_mono hBallOpen hIoo)
      have hscaled := CKN.s3_rescale (MeasurableSet.univ)
        measurableSet_Ioo hS3Source (z.1, t₁) hr φ hφᵣ
      have hzero : ∀ y, y ∉ tsupport (show ParabolicPoint → Vec3 from φ) →
          (-(∑ i : Fin 3,
                CKN.rescaleVelocity r (z.1, t₁) u y i *
                  timePartial (fun w => φ w i) y))
            - ∑ i : Fin 3, ∑ j : Fin 3,
                CKN.rescaleVelocity r (z.1, t₁) u y i *
                  CKN.rescaleVelocity r (z.1, t₁) u y j *
                  spatialPartial (fun w => φ w i) j y
            + ∑ i : Fin 3, ∑ j : Fin 3,
                CKN.rescaleGradient r (z.1, t₁) Du y i j *
                  spatialPartial (fun w => φ w i) j y
            - CKN.rescalePressure r (z.1, t₁) p y *
                ∑ i : Fin 3, spatialPartial (fun w => φ w i) i y
            - ∑ i : Fin 3, ((0 : ParabolicPoint → Vec3) y i) * φ y i = 0 := by
        intro y hy
        have hcomponent_not : ∀ i : Fin 3,
            y ∉ tsupport (show ParabolicPoint → ℝ from fun w => φ w i) := by
          intro i hmem
          apply hy
          change y ∈ closure
            (Function.support (show ParabolicPoint → ℝ from fun w => φ w i)) at hmem
          exact closure_mono
            (show Function.support
                (show ParabolicPoint → ℝ from fun w => φ w i) ⊆
              Function.support (show ParabolicPoint → Vec3 from φ) from by
              intro w hw
              change φ w i ≠ 0 at hw
              apply Function.mem_support.mpr
              intro hzero
              exact hw (congrFun hzero i)) hmem
        have hcont (i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞)
            (fun w : Vec3 × ℝ => φ w i) := component_contDiff hφ.1 i
        have htime (i : Fin 3) : timePartial (fun w => φ w i) y = 0 :=
          timePartial_zero_outside_parabolic_tsupport
            (ψ := fun w : ParabolicPoint => φ w i) (hcont i)
            (hcomponent_not i)
        have hspace (i j : Fin 3) :
            spatialPartial (fun w => φ w i) j y = 0 :=
          spatialPartial_zero_outside_parabolic_tsupport
            (ψ := fun w : ParabolicPoint => φ w i) (hcont i)
            (hcomponent_not i) j
        simp [htime, hspace]
      have hset := setIntegral_eq_of_support_subset
        (f := fun y =>
          (-(∑ i : Fin 3,
                CKN.rescaleVelocity r (z.1, t₁) u y i *
                  timePartial (fun w => φ w i) y))
            - ∑ i : Fin 3, ∑ j : Fin 3,
                CKN.rescaleVelocity r (z.1, t₁) u y i *
                  CKN.rescaleVelocity r (z.1, t₁) u y j *
                  spatialPartial (fun w => φ w i) j y
            + ∑ i : Fin 3, ∑ j : Fin 3,
                CKN.rescaleGradient r (z.1, t₁) Du y i j *
                  spatialPartial (fun w => φ w i) j y
            - CKN.rescalePressure r (z.1, t₁) p y *
                ∑ i : Fin 3, spatialPartial (fun w => φ w i) i y
            - ∑ i : Fin 3, ((0 : ParabolicPoint → Vec3) y i) * φ y i)
        (MeasurableSet.univ.prod
          (measurableSet_Ioo.preimage (by
            change Measurable (fun s : ℝ => t₁ + r ^ 2 * s)
            fun_prop)))
        (Set.prod_mono hBallOpen hIoo)
        (CKN.tsupport_parabolic_subset_spaceTimeSet hφ) hzero
      have hscaledZeroFull :
          ∫ y in spaceTimeSet Ωᵣ Iᵣ,
            (-(∑ i : Fin 3,
                  CKN.rescaleVelocity r (z.1, t₁) u y i *
                    timePartial (fun w => φ w i) y))
              - ∑ i : Fin 3, ∑ j : Fin 3,
                  CKN.rescaleVelocity r (z.1, t₁) u y i *
                    CKN.rescaleVelocity r (z.1, t₁) u y j *
                    spatialPartial (fun w => φ w i) j y
              + ∑ i : Fin 3, ∑ j : Fin 3,
                  CKN.rescaleGradient r (z.1, t₁) Du y i j *
                    spatialPartial (fun w => φ w i) j y
              - CKN.rescalePressure r (z.1, t₁) p y *
                  ∑ i : Fin 3, spatialPartial (fun w => φ w i) i y
              - ∑ i : Fin 3, ((0 : ParabolicPoint → Vec3) y i) * φ y i = 0 := by
        simpa [Ωᵣ, Iᵣ, CKN.rescaledSpace, CKN.rescaledTime,
          CKN.scalingTime, CKN.rescaleForce] using hscaled.2
      have hscaledZero := hset.symm.trans hscaledZeroFull
      simpa [spaceTimeSet, uᵣ, Duᵣ, pᵣ, CKN.rescaleVelocity, CKN.rescaleGradient,
        CKN.rescalePressure, CKN.scalingParabolic, CKN.scalingSpace,
        CKN.scalingTime, parabolicRescaleVelocity, parabolicRescaleGradient,
        parabolicRescalePressure, CKN.rescaleForce, parabolicTranslate,
        parabolicScale] using hscaledZero
    obtain ⟨γ, hγ, hγle, w, hAE, hHolder⟩ := hE1 uᵣ Duᵣ pᵣ
      hUᵣ hDuᵣ hpᵣ hL2ᵣ hEnergyᵣ hpLpᵣ hL3scaled hGradientᵣ hS2ᵣ hS3ᵣ
    have hAEshift : w =ᵐ[volume.restrict
        (goodPointPastCylinder (0 : Vec3) (-(1 / 8 : ℝ) + 1 ^ 2 / 8)
          (1 / 2 : ℝ))] uᵣ := by
      have hsub : goodPointPastCylinder (0 : Vec3)
          (-(1 / 8 : ℝ) + 1 ^ 2 / 8) (1 / 2 : ℝ) ⊆
          parabolicCylinder (0 : Vec3) 0 (1 / 2 : ℝ) := by
        intro y hy
        simp only [goodPointPastCylinder, parabolicCylinder] at hy ⊢
        rcases hy with ⟨hyx, hyt⟩
        have hytUpper : y.2 < 0 := by nlinarith only [hyt.2]
        refine ⟨hyx, ⟨?_, le_of_lt hytUpper⟩⟩
        nlinarith only [hyt.1]
      exact ae_restrict_of_ae_restrict_of_subset hsub hAE
    have hHolderDomain : closure (parabolicCylinder (0 : Vec3) 0 (1 / 2 : ℝ)) ⊆
        spaceTimeSet (Set.univ : Set Vec3) Iᵣ := by
      rw [closure_parabolicCylinder (by norm_num : (0 : ℝ) < (1 / 2 : ℝ))]
      intro y hy
      refine ⟨Set.mem_univ _, hIcc ?_⟩
      exact ⟨by linarith only [hy.2.1], hy.2.2⟩
    have hHolderDomainShift : closure (parabolicCylinder (0 : Vec3)
        (-(1 / 8 : ℝ) + 1 ^ 2 / 8) (1 / 2 : ℝ)) ⊆
        spaceTimeSet (Set.univ : Set Vec3) Iᵣ := by
      simpa only [show -(1 / 8 : ℝ) + 1 ^ 2 / 8 = 0 by norm_num] using hHolderDomain
    have hHolderShift : ParabolicHolderVecOn
        (closure (parabolicCylinder (0 : Vec3)
          (-(1 / 8 : ℝ) + 1 ^ 2 / 8) (1 / 2 : ℝ))) w γ := by
      simpa only [show -(1 / 8 : ℝ) + 1 ^ 2 / 8 = 0 by norm_num] using hHolder
    have hRegularᵣ : IsRegularPoint (Set.univ : Set Vec3) Iᵣ uᵣ
        (0, -(1 / 8 : ℝ)) :=
      isRegularPoint_of_holder_on_shifted_cylinder
        (Set.univ : Set Vec3) Iᵣ uᵣ 0 (-(1 / 8 : ℝ)) 1 γ
        (by norm_num) w hAEshift hγ hγle hHolderShift hHolderDomainShift
    have hIsubset : Iᵣ ⊆ Ioi (-(t₁ / r ^ 2)) := by
      rw [← rescaledTime_Ioi_zero t₁ r hr]
      exact Set.preimage_mono (by
        intro s hs
        exact hs.1)
    have hRegularᵣ' : IsRegularPoint (Set.univ : Set Vec3)
        (Ioi (-(t₁ / r ^ 2))) uᵣ (0, -(1 / 8 : ℝ)) :=
      regularPoint_mono_time hIsubset hRegularᵣ
    have hRegularOriginal :=
      isRegularPoint_parabolicRescale u z.1 t₁ r hr hRegularᵣ'
    have htime : t₁ + r ^ 2 * (-(1 / 8 : ℝ)) = z.2 := by
      dsimp [t₁]
      ring
    have hpoint : (z.1, t₁ + r ^ 2 * (-(1 / 8 : ℝ))) = z :=
      Prod.ext rfl htime
    have hRegularPositive : IsRegularPoint (Set.univ : Set Vec3) (Ioi 0) u z := by
      simpa only [hpoint] using hRegularOriginal
    exact regularPoint_restrict_time isOpen_univ isOpen_Ioo hz hRegularPositive
  ext z
  simp only [CKN.SingularSet, Set.mem_ofPred_eq, Set.mem_empty_iff_false,
    iff_false]
  rintro ⟨hz, hsing⟩
  exact hsing (hReg z hz)

end ESS
