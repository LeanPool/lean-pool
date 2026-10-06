/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.ParabolicMeasure
public import LeanPool.CaffarelliKohnNirenberg.Foundation.WeakDerivMollify
public import LeanPool.CaffarelliKohnNirenberg.Statements.HasSpaceTimeWeakDerivs
public import LeanPool.CaffarelliKohnNirenberg.ClassEquivalence.TestSupport
public import LeanPool.CaffarelliKohnNirenberg.Setting.ScalingInvarianceTests

/-!
# Translating the normalized Gaussian field in time

The positive initial time in `lem:bu-gaussian` is obtained by translating the
already rescaled field by one sixth of a unit.
-/

public section


open MeasureTheory Set CKN CKN.Foundation.Parabolic
open scoped Topology

noncomputable section

namespace ESS

@[expose] def buGaussianTimeShiftHomeomorph (σ : ℝ) : (Vec3 × ℝ) ≃ₜ (Vec3 × ℝ) :=
  Homeomorph.prodCongr (Homeomorph.refl Vec3) (Homeomorph.addLeft σ)

private theorem buGaussianTimeShiftHomeomorph_apply (σ : ℝ) (z : Vec3 × ℝ) :
    buGaussianTimeShiftHomeomorph σ z = (z.1, z.2 + σ) := by
  change (z.1, σ + z.2) = (z.1, z.2 + σ)
  congr 1
  ring

/-- The parabolic homeomorphism translating time forward by `σ`.
(`lem:bu-gaussian#time-shift`). -/
@[expose] def buGaussianTimeShiftPoint (σ : ℝ) : ParabolicPoint ≃ₜ ParabolicPoint :=
  parabolicHomeomorph.trans
    ((buGaussianTimeShiftHomeomorph σ).trans parabolicHomeomorph.symm)

private theorem buGaussianTimeShiftPoint_eq_scaling (σ : ℝ) :
    scalingParabolic 1 (0, σ) = buGaussianTimeShiftPoint σ := by
  funext z
  apply parabolicHomeomorph.injective
  simp [buGaussianTimeShiftPoint, buGaussianTimeShiftHomeomorph,
    scalingParabolic, parabolicTranslate, parabolicScale,
    parabolicHomeomorph_apply, parabolicHomeomorph_symm_apply]

/-- Evaluation of the inverse time translation in normalized coordinates. -/
theorem buGaussian_timeShift_point_symm_apply (σ : ℝ) (z : ParabolicPoint) :
    (buGaussianTimeShiftPoint σ).symm z = (z.1, z.2 - σ) := by
  apply (buGaussianTimeShiftPoint σ).injective
  rw [(buGaussianTimeShiftPoint σ).apply_symm_apply]
  rw [← buGaussianTimeShiftPoint_eq_scaling σ]
  simp [scalingParabolic, parabolicTranslate, parabolicScale]
  rfl

/-- Inverting the time translation is the translation by the negative amount. -/
theorem buGaussian_timeShift_inverse (σ : ℝ) :
    (buGaussianTimeShiftPoint σ).symm = buGaussianTimeShiftPoint (-σ) := by
  ext z
  rw [buGaussian_timeShift_point_symm_apply,
    ← buGaussianTimeShiftPoint_eq_scaling]
  simp [scalingParabolic, parabolicTranslate, parabolicScale]
  congr 1
  ring

/-- Time translation preserves parabolic volume (`lem:bu-gaussian#time-shift`). -/
theorem buGaussian_timeShift_measurePreserving (σ : ℝ) :
    MeasurePreserving (buGaussianTimeShiftPoint σ)
      (volume : Measure ParabolicPoint) (volume : Measure ParabolicPoint) := by
  have hprod : MeasurePreserving (buGaussianTimeShiftHomeomorph σ)
      (volume : Measure (Vec3 × ℝ)) (volume : Measure (Vec3 × ℝ)) := by
    exact (MeasurePreserving.id volume).prod
      (measurePreserving_add_left (volume : Measure ℝ) σ)
  have h₁ := hprod.comp parabolicHomeomorph_measurePreserving
  have h₂ := parabolicHomeomorphSymm_measurePreserving.comp h₁
  change MeasurePreserving
    (parabolicHomeomorph.symm ∘ buGaussianTimeShiftHomeomorph σ ∘
      parabolicHomeomorph) volume volume at h₂
  convert h₂ using 1
  · funext z
    rfl

/-- Time translation maps the source interval onto its positive-time image
(`lem:bu-gaussian#time-shift`). -/
theorem buGaussian_timeShift_image (ρ σ : ℝ) :
    buGaussianTimeShiftPoint σ ''
        spaceTimeSet (vec3Ball 0 ρ) (Ioo 0 (2 - σ)) =
      spaceTimeSet (vec3Ball 0 ρ) (Ioo σ 2) := by
  have hprod : buGaussianTimeShiftHomeomorph σ ''
      (vec3Ball 0 ρ ×ˢ Ioo 0 (2 - σ)) = vec3Ball 0 ρ ×ˢ Ioo σ 2 := by
    ext q
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨hz.1, ?_⟩
      rw [buGaussianTimeShiftHomeomorph_apply]
      change σ < z.2 + σ ∧ z.2 + σ < 2
      constructor
      · linarith only [hz.2.1]
      · linarith only [hz.2.2]
    · rintro ⟨hqₓ, ⟨hqₜ₀, hqₜ₁⟩⟩
      refine ⟨(q.1, q.2 - σ), ⟨hqₓ, ?_⟩, ?_⟩
      · constructor
        · linarith only [hqₜ₀]
        · linarith only [hqₜ₁]
      · rw [buGaussianTimeShiftHomeomorph_apply]
        exact Prod.ext rfl (by ring)
  have hsource : parabolicHomeomorph ''
      spaceTimeSet (vec3Ball 0 ρ) (Ioo 0 (2 - σ)) =
      vec3Ball 0 ρ ×ˢ Ioo 0 (2 - σ) := by
    ext q
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact hp
    · intro hq
      exact ⟨parabolicHomeomorph.symm q, hq,
        parabolicHomeomorph.apply_symm_apply q⟩
  have htarget : parabolicHomeomorph.symm ''
      (vec3Ball 0 ρ ×ˢ Ioo σ 2) =
      spaceTimeSet (vec3Ball 0 ρ) (Ioo σ 2) := by
    ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact hq
    · intro hp
      exact ⟨parabolicHomeomorph p, hp,
        parabolicHomeomorph.symm_apply_apply p⟩
  have hTfun : (buGaussianTimeShiftPoint σ : ParabolicPoint → ParabolicPoint) =
      parabolicHomeomorph.symm ∘ buGaussianTimeShiftHomeomorph σ ∘
        parabolicHomeomorph := by rfl
  let S₀ := spaceTimeSet (vec3Ball 0 ρ) (Ioo 0 (2 - σ))
  have hImageComp :
      (parabolicHomeomorph.symm ∘ buGaussianTimeShiftHomeomorph σ ∘
        parabolicHomeomorph) '' S₀ =
      parabolicHomeomorph.symm ''
        (buGaussianTimeShiftHomeomorph σ '' (parabolicHomeomorph '' S₀)) := by
    ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact ⟨buGaussianTimeShiftHomeomorph σ (parabolicHomeomorph q),
        ⟨parabolicHomeomorph q,
          ⟨q, hq, rfl⟩, rfl⟩, rfl⟩
    · rintro ⟨u, hu, rfl⟩
      rcases hu with ⟨v, hv, rfl⟩
      rcases hv with ⟨q, hq, rfl⟩
      exact ⟨q, hq, rfl⟩
  calc
    buGaussianTimeShiftPoint σ '' S₀ =
      parabolicHomeomorph.symm ''
        (buGaussianTimeShiftHomeomorph σ ''
          (parabolicHomeomorph '' S₀)) := by rw [hTfun, hImageComp]
    _ = spaceTimeSet (vec3Ball 0 ρ) (Ioo σ 2) := by
      rw [show S₀ = spaceTimeSet (vec3Ball 0 ρ) (Ioo 0 (2 - σ)) from rfl,
        hsource, hprod, htarget]

private theorem buGaussian_timeShift_locallyIntegrable
    {ρ σ : ℝ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : ParabolicPoint → E}
    (hf : LocallyIntegrableOn f
      (spaceTimeSet (vec3Ball 0 ρ) (Ioo 0 (2 - σ))) volume) :
    LocallyIntegrableOn (fun z => f ((buGaussianTimeShiftPoint σ).symm z))
      (spaceTimeSet (vec3Ball 0 ρ) (Ioo σ 2)) volume := by
  let S₀ := spaceTimeSet (vec3Ball 0 ρ) (Ioo 0 (2 - σ))
  let S₁ := spaceTimeSet (vec3Ball 0 ρ) (Ioo σ 2)
  intro z hz
  let q := (buGaussianTimeShiftPoint σ).symm z
  have himage : buGaussianTimeShiftPoint σ '' S₀ = S₁ := by
    simpa [S₀, S₁] using buGaussian_timeShift_image ρ σ
  have hq : q ∈ S₀ := by
    have hz' : z ∈ buGaussianTimeShiftPoint σ '' S₀ := by rw [himage]; exact hz
    rcases hz' with ⟨y, hy, hTy⟩
    have hqy : q = y := by
      dsimp [q]
      rw [← hTy]
      exact (buGaussianTimeShiftPoint σ).symm_apply_apply y
    rw [hqy]
    exact hy
  have hloc := hf q hq
  have hmap := (buGaussianTimeShiftPoint σ).measurableEmbedding
    |>.integrableAtFilter_map_iff
      (f := fun y => f ((buGaussianTimeShiftPoint σ).symm y))
      (l := 𝓝[S₀] q) (μ := (volume : Measure ParabolicPoint))
  rw [buGaussian_timeShift_measurePreserving σ |>.map_eq] at hmap
  have hfilter : Filter.map (buGaussianTimeShiftPoint σ) (𝓝[S₀] q) =
      𝓝[S₁] z := by
    rw [(buGaussianTimeShiftPoint σ).isEmbedding.map_nhdsWithin_eq]
    rw [himage]
    simp [q]
  rw [← hfilter]
  exact hmap.mpr (by simpa [q, Function.comp_def] using hloc)

/-- Spatial and time derivatives commute with parabolic time translation. -/
theorem buGaussian_timeShift_test_derivatives
    (σ : ℝ) {ψ : Vec3 × ℝ → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (z : ParabolicPoint) (j : Fin 3) :
    spatialPartial (ψ ∘ buGaussianTimeShiftHomeomorph σ) j z =
        spatialPartial ψ j (buGaussianTimeShiftPoint σ z) ∧
      timePartial (ψ ∘ buGaussianTimeShiftHomeomorph σ) z =
        timePartial ψ (buGaussianTimeShiftPoint σ z) := by
  let φ : Vec3 × ℝ → ℝ := ψ ∘ buGaussianTimeShiftHomeomorph σ
  have hφ : ContDiff ℝ (⊤ : ℕ∞) φ := by
    change ContDiff ℝ (⊤ : ℕ∞)
      (fun q : Vec3 × ℝ => ψ (q.1, σ + q.2))
    fun_prop
  let z₀ : ParabolicPoint := (0, σ)
  have hpoint (q : ParabolicPoint) :
      scalingParabolic 1 z₀ q = buGaussianTimeShiftPoint σ q := by
    apply parabolicHomeomorph.injective
    simp [buGaussianTimeShiftPoint, buGaussianTimeShiftHomeomorph,
      scalingParabolic, parabolicTranslate, parabolicScale, z₀,
      parabolicHomeomorph_apply, parabolicHomeomorph_symm_apply]
  have hp := CKN.spatialPartial_pullback 1 (by norm_num) z₀ hφ j z
  have ht := CKN.timePartial_pullback 1 (by norm_num) z₀ hφ z
  rw [hpoint] at hp ht
  have hcomp : (fun y : Vec3 × ℝ =>
      φ (((1 : ℝ)⁻¹) • (y.1 - z₀.1), (((1 : ℝ) ^ 2)⁻¹) * (y.2 - z₀.2))) = ψ := by
    funext q
    change ψ (buGaussianTimeShiftHomeomorph σ
      (((1 : ℝ)⁻¹) • (q.1 - z₀.1), (((1 : ℝ) ^ 2)⁻¹) * (q.2 - z₀.2))) = ψ q
    congr 1
    rw [buGaussianTimeShiftHomeomorph_apply]
    ext <;> simp [z₀]
  change spatialPartial (fun y : Vec3 × ℝ =>
    φ (((1 : ℝ)⁻¹) • (y.1 - z₀.1), (((1 : ℝ) ^ 2)⁻¹) * (y.2 - z₀.2))) j
      (buGaussianTimeShiftPoint σ z) =
      (1 : ℝ)⁻¹ * spatialPartial φ j z at hp
  change timePartial (fun y : Vec3 × ℝ =>
    φ (((1 : ℝ)⁻¹) • (y.1 - z₀.1), (((1 : ℝ) ^ 2)⁻¹) * (y.2 - z₀.2)))
      (buGaussianTimeShiftPoint σ z) =
      (((1 : ℝ) ^ 2)⁻¹) * timePartial φ z at ht
  rw [hcomp] at hp ht
  norm_num at hp ht
  exact ⟨hp.symm, ht.symm⟩

/-- Time translation transports all three weak integration-by-parts
identities from a short interval onto its positive-time image. -/
theorem buGaussian_timeShift_weak_derivatives
    {ρ σ : ℝ}
    {w : ParabolicPoint → Vec3}
    {Dw : ParabolicPoint → Fin 3 → Vec3}
    {D2w : ParabolicPoint → Fin 3 → Fin 3 → Vec3}
    {Dtw : ParabolicPoint → Vec3}
    (hweak : HasSpaceTimeWeakDerivs (vec3Ball 0 ρ) (Ioo 0 (2 - σ))
      w Dw D2w Dtw) :
    HasSpaceTimeWeakDerivs (vec3Ball 0 ρ) (Ioo σ 2)
      (fun z => w ((buGaussianTimeShiftPoint σ).symm z))
      (fun z i j => Dw ((buGaussianTimeShiftPoint σ).symm z) i j)
      (fun z i j k => D2w ((buGaussianTimeShiftPoint σ).symm z) i j k)
      (fun z i => Dtw ((buGaussianTimeShiftPoint σ).symm z) i) := by
  let B := vec3Ball 0 ρ
  let I₀ := Ioo (0 : ℝ) (2 - σ)
  let I₁ := Ioo σ 2
  let T := buGaussianTimeShiftPoint σ
  let H := buGaussianTimeShiftHomeomorph σ
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact buGaussian_timeShift_locallyIntegrable hweak.1
  · exact buGaussian_timeShift_locallyIntegrable hweak.2.1
  · exact buGaussian_timeShift_locallyIntegrable hweak.2.2.1
  · exact buGaussian_timeShift_locallyIntegrable hweak.2.2.2.1
  · intro ψ hψ
    let ψprod : Vec3 × ℝ → ℝ := ψ
    let φ : Vec3 × ℝ → ℝ := ψprod ∘ H
    let φp : ParabolicPoint → ℝ := fun z => φ (parabolicHomeomorph z)
    have hψprod : ψprod ∈ spaceTimeTestFunction (V := ℝ) B I₁ := by
      change (show Vec3 × ℝ → ℝ from ψ) ∈ spaceTimeTestFunction (V := ℝ) B I₁
      exact hψ
    have hψprodSmooth : ContDiff ℝ (⊤ : ℕ∞) ψprod := hψprod.1
    have hφsmooth : ContDiff ℝ (⊤ : ℕ∞) φ := by
      dsimp [φ, H]
      exact hψprodSmooth.comp (by
        change ContDiff ℝ (⊤ : ℕ∞)
          (fun q : Vec3 × ℝ => (q.1, σ + q.2))
        fun_prop)
    have hφcompact : HasCompactSupport φ := by
      dsimp [φ]
      exact hψprod.2.1.comp_homeomorph H
    have hφsupport : tsupport φ ⊆ B ×ˢ I₀ := by
      rw [show φ = ψprod ∘ H from rfl, tsupport_comp_eq_preimage ψprod H]
      intro z hz
      change H z ∈ tsupport ψprod at hz
      have hz' : H z ∈ B ×ˢ I₁ := hψprod.2.2 hz
      rcases hz' with ⟨hzx, hzt⟩
      refine ⟨hzx, ?_⟩
      change σ < σ + z.2 ∧ σ + z.2 < 2 at hzt
      constructor <;> linarith only [hzt.1, hzt.2]
    have hφtest : φ ∈ spaceTimeTestFunction (V := ℝ) B I₀ :=
      ⟨hφsmooth, hφcompact, hφsupport⟩
    have hφpEq : φp = (show ParabolicPoint → ℝ from φ) := by
      funext z
      rfl
    have hφptest : φp ∈ spaceTimeTestFunction (V := ℝ) B I₀ := by
      change (show Vec3 × ℝ → ℝ from φp) ∈ spaceTimeTestFunction (V := ℝ) B I₀
      rw [hφpEq]
      exact hφtest
    obtain ⟨hfirst, hsecond, htime⟩ := hweak.2.2.2.2 φp hφptest
    have hφeval (z : ParabolicPoint) : φp z = ψ (T z) := by
      change ψprod (H (parabolicHomeomorph z)) =
        ψprod (parabolicHomeomorph (T z))
      apply congrArg ψprod
      apply Prod.ext
      · rfl
      · change (buGaussianTimeShiftHomeomorph σ (z.1, z.2)).2 = σ + z.2
        rw [buGaussianTimeShiftHomeomorph_apply]
        exact add_comm _ _
    have hsp (z : ParabolicPoint) (j : Fin 3) :
        spatialPartial φp j z = spatialPartial ψ j (T z) := by
      calc
        spatialPartial φp j z = spatialPartial φ j z := by rw [hφpEq]
        _ = spatialPartial ψprod j (T z) :=
          (buGaussian_timeShift_test_derivatives σ hψprodSmooth z j).1
        _ = spatialPartial ψ j (T z) := rfl
    have htm (z : ParabolicPoint) :
        timePartial φp z = timePartial ψ (T z) := by
      calc
        timePartial φp z = timePartial φ z := by rw [hφpEq]
        _ = timePartial ψprod (T z) :=
          (buGaussian_timeShift_test_derivatives σ hψprodSmooth z 0).2
        _ = timePartial ψ (T z) := rfl
    have hrespace : rescaledSpace 1 0 B = B := by
      ext x
      simp [rescaledSpace, scalingSpace]
    have hretime : rescaledTime 1 σ I₁ = I₀ := by
      ext s
      change σ + 1 ^ 2 * s ∈ Ioo σ 2 ↔ s ∈ Ioo 0 (2 - σ)
      simp only [mem_Ioo]
      constructor <;> intro hs <;> constructor <;> norm_num at hs ⊢ <;>
        (first | linarith only [hs.1] | linarith only [hs.2])
    have hcoef : (ENNReal.ofReal (1⁻¹ ^ 5)).toReal = 1 := by norm_num
    have hTfunc : scalingParabolic 1 (0, σ) = T :=
      buGaussianTimeShiftPoint_eq_scaling σ
    have hsourceMeas : MeasurableSet (spaceTimeSet B I₀) := by
      exact (isOpen_spaceTimeSet B I₀ (isOpen_vec3Ball _ _) isOpen_Ioo).measurableSet
    have hpartialCont (j : Fin 3) :
        Continuous (fun z : ParabolicPoint => spatialPartial ψ j z) := by
      have hc := (spatialPartial_contDiff hψprod.1 j).continuous.comp
        parabolicHomeomorph.continuous
      exact hc.congr (fun _ => rfl)
    have htimeCont : Continuous (fun z : ParabolicPoint => timePartial ψ z) := by
      have hc := (contDiff_timePartial hψprod.1).continuous.comp
        parabolicHomeomorph.continuous
      exact hc.congr (fun _ => rfl)
    refine ⟨?_, ?_, ?_⟩
    · intro i j
      let F : ParabolicPoint → ℝ := fun z =>
        w (T.symm z) i * spatialPartial ψ j z
      let G : ParabolicPoint → ℝ := fun z =>
        Dw (T.symm z) i j * ψ z
      have hwi : LocallyIntegrableOn (fun z => w z i)
          (spaceTimeSet B I₀) volume :=
        locallyIntegrableOn_pi_eval hweak.1 i
      have hFmeas : AEStronglyMeasurable F
          (volume.restrict (spaceTimeSet B I₁)) := by
        have hwi' := buGaussian_timeShift_locallyIntegrable hwi
        have hwi'' : AEStronglyMeasurable (fun z => w (T.symm z) i)
            (volume.restrict (spaceTimeSet B I₁)) :=
          LocallyIntegrableOn.aestronglyMeasurable hwi'
        have hwi''₁ : AEStronglyMeasurable
            (fun z => w (T.symm z) i)
            (volume.restrict (spaceTimeSet B I₁)) := by
          simpa only [T] using hwi''
        dsimp [F]
        exact hwi''₁.mul (hpartialCont j).aestronglyMeasurable
      have hGmeas : AEStronglyMeasurable G
          (volume.restrict (spaceTimeSet B I₁)) := by
        have hdwi : LocallyIntegrableOn (fun z => Dw z i j)
            (spaceTimeSet B I₀) volume :=
          locallyIntegrableOn_pi_eval (locallyIntegrableOn_pi_eval hweak.2.1 i) j
        have hdwi' : AEStronglyMeasurable
            (fun z => Dw (T.symm z) i j)
            (volume.restrict (spaceTimeSet B I₁)) :=
          LocallyIntegrableOn.aestronglyMeasurable
            (buGaussian_timeShift_locallyIntegrable hdwi)
        have hψcont : Continuous ψ := by
          have hc := hψprod.1.continuous.comp parabolicHomeomorph.continuous
          exact hc.congr (fun _ => rfl)
        have hdwi'' : AEStronglyMeasurable
            (fun z => Dw (T.symm z) i j)
            (volume.restrict (spaceTimeSet B I₁)) := by
          simpa only [T] using hdwi'
        dsimp [G]
        exact hdwi''.mul hψcont.aestronglyMeasurable
      have hchangeF := CKN.integral_comp_scaling_test 1 (by norm_num)
        ((0 : Vec3), σ) (Ω := B) (I := I₁) (F := F)
        (vec3Ball_measurable _ _) measurableSet_Ioo hFmeas
      have hchangeG := CKN.integral_comp_scaling_test 1 (by norm_num)
        ((0 : Vec3), σ) (Ω := B) (I := I₁) (F := G)
        (vec3Ball_measurable _ _) measurableSet_Ioo hGmeas
      rw [hrespace, hretime, hcoef, smul_eq_mul] at hchangeF hchangeG
      have hchangeF' :
          (∫ z in spaceTimeSet B I₀, F (T z)) =
            ∫ z in spaceTimeSet B I₁, F z := by
        simpa only [hTfunc, one_mul] using hchangeF
      have hchangeG' :
          (∫ z in spaceTimeSet B I₀, G (T z)) =
            ∫ z in spaceTimeSet B I₁, G z := by
        simpa only [hTfunc, one_mul] using hchangeG
      have hFpoint (z : ParabolicPoint) :
          F (T z) = w z i * spatialPartial φp j z := by
        simp [F, T.symm_apply_apply, hsp]
      have hGpoint (z : ParabolicPoint) :
          G (T z) = Dw z i j * φp z := by
        simp [G, T.symm_apply_apply, hφeval]
      calc
        (∫ z in spaceTimeSet B I₁, F z) =
            ∫ z in spaceTimeSet B I₀, F (T z) := hchangeF'.symm
        _ = ∫ z in spaceTimeSet B I₀, w z i * spatialPartial φp j z := by
          apply setIntegral_congr_ae hsourceMeas
          filter_upwards [] with z hz
          exact hFpoint z
        _ = -∫ z in spaceTimeSet B I₀, Dw z i j * φp z := hfirst i j
        _ = -∫ z in spaceTimeSet B I₀, G (T z) := by
          congr 1
          apply setIntegral_congr_ae hsourceMeas
          filter_upwards [] with z hz
          exact (hGpoint z).symm
        _ = -∫ z in spaceTimeSet B I₁, G z := by rw [hchangeG']
    · intro i j k
      let F : ParabolicPoint → ℝ := fun z =>
        Dw (T.symm z) i j * spatialPartial ψ k z
      let G : ParabolicPoint → ℝ := fun z =>
        D2w (T.symm z) i j k * ψ z
      have hdwij : LocallyIntegrableOn (fun z => Dw z i j)
          (spaceTimeSet B I₀) volume :=
        locallyIntegrableOn_pi_eval
          (locallyIntegrableOn_pi_eval hweak.2.1 i) j
      have hFmeas : AEStronglyMeasurable F
          (volume.restrict (spaceTimeSet B I₁)) := by
        have hdwij' := buGaussian_timeShift_locallyIntegrable hdwij
        have hdwij'' : AEStronglyMeasurable
            (fun z => Dw (T.symm z) i j)
            (volume.restrict (spaceTimeSet B I₁)) := by
          simpa only [T] using
            (LocallyIntegrableOn.aestronglyMeasurable hdwij')
        dsimp [F]
        exact hdwij''.mul (hpartialCont k).aestronglyMeasurable
      have hGmeas : AEStronglyMeasurable G
          (volume.restrict (spaceTimeSet B I₁)) := by
        have hD2wij : LocallyIntegrableOn (fun z => D2w z i j k)
            (spaceTimeSet B I₀) volume :=
          locallyIntegrableOn_pi_eval
            (locallyIntegrableOn_pi_eval
              (locallyIntegrableOn_pi_eval hweak.2.2.1 i) j) k
        have hD2wij' := buGaussian_timeShift_locallyIntegrable hD2wij
        have hD2wij'' : AEStronglyMeasurable
            (fun z => D2w (T.symm z) i j k)
            (volume.restrict (spaceTimeSet B I₁)) := by
          simpa only [T] using
            (LocallyIntegrableOn.aestronglyMeasurable hD2wij')
        have hψcont : Continuous ψ := by
          have hc := hψprod.1.continuous.comp parabolicHomeomorph.continuous
          exact hc.congr (fun _ => rfl)
        dsimp [G]
        exact hD2wij''.mul hψcont.aestronglyMeasurable
      have hchangeF := CKN.integral_comp_scaling_test 1 (by norm_num)
        ((0 : Vec3), σ) (Ω := B) (I := I₁) (F := F)
        (vec3Ball_measurable _ _) measurableSet_Ioo hFmeas
      have hchangeG := CKN.integral_comp_scaling_test 1 (by norm_num)
        ((0 : Vec3), σ) (Ω := B) (I := I₁) (F := G)
        (vec3Ball_measurable _ _) measurableSet_Ioo hGmeas
      rw [hrespace, hretime, hcoef, smul_eq_mul] at hchangeF hchangeG
      have hchangeF' :
          (∫ z in spaceTimeSet B I₀, F (T z)) =
            ∫ z in spaceTimeSet B I₁, F z := by
        simpa only [hTfunc, one_mul] using hchangeF
      have hchangeG' :
          (∫ z in spaceTimeSet B I₀, G (T z)) =
            ∫ z in spaceTimeSet B I₁, G z := by
        simpa only [hTfunc, one_mul] using hchangeG
      have hFpoint (z : ParabolicPoint) :
          F (T z) = Dw z i j * spatialPartial φp k z := by
        simp [F, T.symm_apply_apply, hsp]
      have hGpoint (z : ParabolicPoint) :
          G (T z) = D2w z i j k * φp z := by
        simp [G, T.symm_apply_apply, hφeval]
      calc
        (∫ z in spaceTimeSet B I₁, F z) =
            ∫ z in spaceTimeSet B I₀, F (T z) := hchangeF'.symm
        _ = ∫ z in spaceTimeSet B I₀, Dw z i j * spatialPartial φp k z := by
          apply setIntegral_congr_ae hsourceMeas
          filter_upwards [] with z hz
          exact hFpoint z
        _ = -∫ z in spaceTimeSet B I₀, D2w z i j k * φp z := hsecond i j k
        _ = -∫ z in spaceTimeSet B I₀, G (T z) := by
          congr 1
          apply setIntegral_congr_ae hsourceMeas
          filter_upwards [] with z hz
          exact (hGpoint z).symm
        _ = -∫ z in spaceTimeSet B I₁, G z := by rw [hchangeG']
    · intro i
      let F : ParabolicPoint → ℝ := fun z =>
        w (T.symm z) i * timePartial ψ z
      let G : ParabolicPoint → ℝ := fun z =>
        Dtw (T.symm z) i * ψ z
      have hwi : LocallyIntegrableOn (fun z => w z i)
          (spaceTimeSet B I₀) volume :=
        locallyIntegrableOn_pi_eval hweak.1 i
      have hFmeas : AEStronglyMeasurable F
          (volume.restrict (spaceTimeSet B I₁)) := by
        have hwi' := buGaussian_timeShift_locallyIntegrable hwi
        have hwi'' : AEStronglyMeasurable
            (fun z => w (T.symm z) i)
            (volume.restrict (spaceTimeSet B I₁)) := by
          simpa only [T] using
            (LocallyIntegrableOn.aestronglyMeasurable hwi')
        dsimp [F]
        exact hwi''.mul htimeCont.aestronglyMeasurable
      have hGmeas : AEStronglyMeasurable G
          (volume.restrict (spaceTimeSet B I₁)) := by
        have hDtw : LocallyIntegrableOn (fun z => Dtw z i)
            (spaceTimeSet B I₀) volume :=
          locallyIntegrableOn_pi_eval hweak.2.2.2.1 i
        have hDtw' := buGaussian_timeShift_locallyIntegrable hDtw
        have hDtw'' : AEStronglyMeasurable
            (fun z => Dtw (T.symm z) i)
            (volume.restrict (spaceTimeSet B I₁)) := by
          simpa only [T] using
            (LocallyIntegrableOn.aestronglyMeasurable hDtw')
        have hψcont : Continuous ψ := by
          have hc := hψprod.1.continuous.comp parabolicHomeomorph.continuous
          exact hc.congr (fun _ => rfl)
        dsimp [G]
        exact hDtw''.mul hψcont.aestronglyMeasurable
      have hchangeF := CKN.integral_comp_scaling_test 1 (by norm_num)
        ((0 : Vec3), σ) (Ω := B) (I := I₁) (F := F)
        (vec3Ball_measurable _ _) measurableSet_Ioo hFmeas
      have hchangeG := CKN.integral_comp_scaling_test 1 (by norm_num)
        ((0 : Vec3), σ) (Ω := B) (I := I₁) (F := G)
        (vec3Ball_measurable _ _) measurableSet_Ioo hGmeas
      rw [hrespace, hretime, hcoef, smul_eq_mul] at hchangeF hchangeG
      have hchangeF' :
          (∫ z in spaceTimeSet B I₀, F (T z)) =
            ∫ z in spaceTimeSet B I₁, F z := by
        simpa only [hTfunc, one_mul] using hchangeF
      have hchangeG' :
          (∫ z in spaceTimeSet B I₀, G (T z)) =
            ∫ z in spaceTimeSet B I₁, G z := by
        simpa only [hTfunc, one_mul] using hchangeG
      have hFpoint (z : ParabolicPoint) :
          F (T z) = w z i * timePartial φp z := by
        simp [F, T.symm_apply_apply, htm]
      have hGpoint (z : ParabolicPoint) :
          G (T z) = Dtw z i * φp z := by
        simp [G, T.symm_apply_apply, hφeval]
      calc
        (∫ z in spaceTimeSet B I₁, F z) =
            ∫ z in spaceTimeSet B I₀, F (T z) := hchangeF'.symm
        _ = ∫ z in spaceTimeSet B I₀, w z i * timePartial φp z := by
          apply setIntegral_congr_ae hsourceMeas
          filter_upwards [] with z hz
          exact hFpoint z
        _ = -∫ z in spaceTimeSet B I₀, Dtw z i * φp z := htime i
        _ = -∫ z in spaceTimeSet B I₀, G (T z) := by
          congr 1
          apply setIntegral_congr_ae hsourceMeas
          filter_upwards [] with z hz
          exact (hGpoint z).symm
        _ = -∫ z in spaceTimeSet B I₁, G z := by rw [hchangeG']

/-- Almost-everywhere statements on a cylinder commute with the positive-time translation. -/
theorem buGaussian_timeShift_ae
    {ρ σ : ℝ}
    {P : ParabolicPoint → Prop}
    (hP : ∀ᵐ z ∂(volume.restrict
      (spaceTimeSet (vec3Ball 0 ρ) (Ioo 0 (2 - σ)))), P z) :
    ∀ᵐ z ∂(volume.restrict
      (spaceTimeSet (vec3Ball 0 ρ) (Ioo σ 2))),
      P ((buGaussianTimeShiftPoint σ).symm z) := by
  let T := buGaussianTimeShiftPoint σ
  let U₀ := spaceTimeSet (vec3Ball 0 ρ) (Ioo 0 (2 - σ))
  let U₁ := spaceTimeSet (vec3Ball 0 ρ) (Ioo σ 2)
  have himage : T '' U₀ = U₁ := by
    simpa [T, U₀, U₁] using buGaussian_timeShift_image ρ σ
  have hpres : MeasurePreserving T (volume : Measure ParabolicPoint)
      (volume : Measure ParabolicPoint) :=
    buGaussian_timeShift_measurePreserving σ
  have hrestrict := hpres.restrict_image_emb T.measurableEmbedding U₀
  have hPmap : ∀ᵐ z ∂(Measure.map T (volume.restrict U₀)),
      P (T.symm z) := by
    exact T.measurableEmbedding.ae_map_iff.2 (by
        filter_upwards [hP] with z hz
        simpa only [Homeomorph.symm_apply_apply] using hz)
  rw [hrestrict.map_eq, himage] at hPmap
  simpa [T, U₁] using hPmap

end ESS
