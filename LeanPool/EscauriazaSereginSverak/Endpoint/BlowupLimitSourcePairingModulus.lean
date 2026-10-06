/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupLimitPairingAllTests
public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupLimitPairingSourceModulus
public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupLimitPairingTestBounds
public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupLimitLocalEnergy
public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupVelocityUniform
public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupPressureUniform
public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupGradientComponent
public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupSuitable
public import LeanPool.CaffarelliKohnNirenberg.Setting.ScalingInvarianceBasic

/-!
# Source bounds for the pairing modulus on each exhaustion cylinder

The source pressure split, local energy inequality, and momentum identity give
the uniform modulus needed at each fixed compactness stage, including time zero.
-/

public section


open MeasureTheory Set Filter
open scoped ENNReal Topology
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

private theorem blowupLimit_rescaleGradient_aestronglyMeasurable
    {Du : ParabolicPoint → Fin 3 → Vec3}
    (hDu : AEStronglyMeasurable Du (volume.restrict goodPointDomain))
    (x₀ : Vec3) (t₀ r R a : ℝ)
    (hr : 0 < r) (hx₀ : vec3EuclideanNorm x₀ ≤ 1 / 2)
    (ht₀ : t₀ ∈ Icc (-(1 / 4 : ℝ)) 0)
    (hspace : r * R < 1 / 2) (htime : r ^ 2 * (-a) < 3 / 4) :
    AEStronglyMeasurable (parabolicRescaleGradient x₀ t₀ r Du)
      (volume.restrict (spaceTimeSet (vec3Ball 0 R) (Ioo a 0))) := by
  have hsource : goodPointDomain =
      spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1 : ℝ) 0) := rfl
  have hDu' : AEStronglyMeasurable Du
      (volume.restrict (spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1 : ℝ) 0))) := by
    simpa only [hsource] using hDu
  let z₀ : ParabolicPoint := (x₀,t₀)
  have hscaledOpen : AEStronglyMeasurable
      (fun z => r ^ 2 • Du (CKN.scalingParabolic r z₀ z))
      (volume.restrict
        (spaceTimeSet (CKN.rescaledSpace r x₀
          (vec3Ball (0 : Vec3) 1))
          (CKN.rescaledTime r t₀ (Ioo (-1 : ℝ) 0)))) := by
    have hmap := CKN.map_scalingParabolic_restrict (μ := r) hr z₀
      (Ω := vec3Ball 0 1) (I := Ioo (-1 : ℝ) 0)
      ((isOpen_vec3Ball 0 1).measurableSet) measurableSet_Ioo
    have hs := hDu'.smul_measure (ENNReal.ofReal (r⁻¹ ^ 5))
    rw [← hmap] at hs
    have hcontinuous : Continuous (CKN.scalingParabolic r z₀) := by
      rw [CKN.scalingParabolic_eq r z₀]
      exact continuous_prod_to_parabolicPoint.comp
        (((continuous_const.add (continuous_const_smul r)).comp continuous_fst).prodMk
          ((continuous_const.add (continuous_const.mul continuous_id)).comp continuous_snd)
          |>.comp continuous_parabolicPoint_to_prod)
    have hmeas : Measurable (CKN.scalingParabolic r z₀) := hcontinuous.measurable
    have hcomp := hs.comp_measurable hmeas
    change AEStronglyMeasurable
      (fun z => r ^ 2 • Du (CKN.scalingParabolic r z₀ z)) _
    exact hcomp.const_smul (r ^ 2)
  have hdomain : spaceTimeSet (vec3Ball (0 : Vec3) R) (Ioo a 0) ⊆
      spaceTimeSet (CKN.rescaledSpace r x₀
        (vec3Ball (0 : Vec3) 1))
        (CKN.rescaledTime r t₀ (Ioo (-1 : ℝ) 0)) := by
    intro z hz
    have hz' := blowupCylinder_subset_domain x₀ t₀ r R a hx₀ ht₀ hr
      hspace htime hz
    change parabolicTranslate x₀ t₀ (parabolicScale r z) ∈
      spaceTimeSet (vec3Ball 0 1) (Ioo (-1 : ℝ) 0)
    change parabolicTranslate x₀ t₀ (parabolicScale r z) ∈
      goodPointDomain at hz'
    rw [hsource] at hz'
    exact hz'
  have hmono := hscaledOpen.mono_measure
    (Measure.restrict_mono_set volume hdomain)
  have heq : parabolicRescaleGradient x₀ t₀ r Du =
      fun z => r ^ 2 • Du (CKN.scalingParabolic r z₀ z) := by
    funext z
    ext i j
    rfl
  rw [heq]
  exact hmono

private theorem blowupLimit_restrict_closed_interval_le_open
    {C D : Set Vec3} {a b c d : ℝ}
    (hC : C ⊆ D) (hI : Icc a b ⊆ Icc c d) :
    volume.restrict (C ×ˢ Icc a b) ≤
      volume.restrict (D ×ˢ Ioo c d) := by
  have htime : Icc c d =ᵐ[volume] Ioo c d := Ioo_ae_eq_Icc.symm
  have hrect : C ×ˢ Icc c d =ᵐ[volume] C ×ˢ Ioo c d :=
    Measure.set_prod_ae_eq (ae_eq_refl C) htime
  have hsub : C ×ˢ Icc a b ⊆ C ×ˢ Icc c d :=
    Set.prod_mono Subset.rfl hI
  calc
    volume.restrict (C ×ˢ Icc a b) ≤ volume.restrict (C ×ˢ Icc c d) :=
      Measure.restrict_mono_set volume hsub
    _ = volume.restrict (C ×ˢ Ioo c d) := Measure.restrict_congr_set hrect
    _ ≤ volume.restrict (D ×ˢ Ioo c d) :=
      Measure.restrict_mono_set volume (Set.prod_mono hC Subset.rfl)

private theorem blowupLimit_component_memLp_of_norm
    {p : ℝ≥0∞} (μ : Measure ParabolicPoint) (M : ℝ≥0∞)
    (f : ParabolicPoint → Vec3) (i : Fin 3)
    (hvec : AEStronglyMeasurable f μ)
    (hnorm : MemLp (fun z => vec3EuclideanNorm (f z)) p μ)
    (hbound : eLpNorm (fun z => vec3EuclideanNorm (f z)) p μ ≤ M) :
    MemLp (fun z => f z i) p μ ∧
      eLpNorm (fun z => f z i) p μ ≤ M := by
  have hcomp : AEStronglyMeasurable (fun z => f z i) μ :=
    (continuous_apply i).comp_aestronglyMeasurable hvec
  have hpoint (z : ParabolicPoint) :
      ‖f z i‖ ≤ ‖vec3EuclideanNorm (f z)‖ := by
    calc
      ‖f z i‖ ≤ vec3EuclideanNorm (f z) :=
        (norm_le_pi_norm (f z) i).trans (norm_le_vec3EuclideanNorm (f z))
      _ = ‖vec3EuclideanNorm (f z)‖ := by
        rw [Real.norm_of_nonneg (vec3EuclideanNorm_nonneg _)]
  have hmem : MemLp (fun z => f z i) p μ :=
    hnorm.of_le hcomp (Filter.Eventually.of_forall hpoint)
  have hle := eLpNorm_mono_ae (p := p) hcomp
    (Filter.Eventually.of_forall hpoint)
  exact ⟨hmem, hle.trans hbound⟩

/-! The theorem below is the source estimate used by every fixed stage of
`lem:compactness` of the CKN manuscript. -/

/-- The source flux bounds give a scale-uniform modulus for the weakly
continuous trace pairings used in `prop:blowup-limit`. -/
theorem blowup_limit_pairing_modulus_from_source_data
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hu : AEStronglyMeasurable u
      (volume.restrict (spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0))))
    (hDu : AEStronglyMeasurable Du
      (volume.restrict (spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0))))
    (hpmeas : AEStronglyMeasurable p
      (volume.restrict (spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0))))
    (hL2 : essSup (fun t : ℝ => ∫⁻ x in vec3Ball (0 : Vec3) 1,
      ‖u (x,t)‖ₑ ^ (2 : ℝ)) (volume.restrict (Ioo (-1) 0)) < ⊤)
    (henergy : (∫⁻ z in spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0),
      ‖u z‖ₑ ^ (2 : ℝ) + ‖Du z‖ₑ ^ (2 : ℝ)) < ⊤)
    (hpLp : MemLp p (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0))))
    (hL3 : essSup (fun t : ℝ => ∫⁻ x in vec3Ball (0 : Vec3) 1,
      ENNReal.ofReal (vec3EuclideanNorm (u (x,t))) ^ (3 : ℝ))
      (volume.restrict (Ioo (-1) 0)) < ⊤)
    (hgrad : ∀ᵐ t ∂(volume.restrict (Ioo (-1) 0)), ∀ i : Fin 3,
      HasWeakGradientOn (vec3Ball (0 : Vec3) 1) (fun x => u (x,t) i)
        (fun x => Du (x,t) i))
    (hS2 : ∀ ψ : ParabolicPoint → ℝ,
      ψ ∈ spaceTimeTestFunction (V := ℝ)
        (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0) →
      ∫ z in spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0),
        ∑ i : Fin 3, u z i * spatialPartial ψ i z = 0)
    (hS3 : ∀ φ : ParabolicPoint → Vec3,
      φ ∈ spaceTimeTestFunction (V := Vec3)
        (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0) →
      ∫ z in spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0),
        (-(∑ i : Fin 3, u z i * timePartial (fun y => φ y i) z)
          - ∑ i : Fin 3, ∑ j : Fin 3,
              u z i * u z j * spatialPartial (fun y => φ y i) j z
          + ∑ i : Fin 3, ∑ j : Fin 3,
              Du z i j * spatialPartial (fun y => φ y i) j z
          - p z * ∑ i : Fin 3, spatialPartial (fun y => φ y i) i z
          - ∑ i : Fin 3, ((0 : ParabolicPoint → Vec3) z i) * φ z i) = 0)
    (x₀ : Vec3) (t₀ : ℝ) (r : ℕ → ℝ)
    (hx₀ : x₀ ∈ closure (vec3Ball 0 (1 / 2 : ℝ)))
    (ht₀ : t₀ ∈ Icc (-(1 / 4 : ℝ)) 0)
    (hr : ∀ k, 0 < r k) (hr0 : Tendsto r atTop (nhds 0))
    (v : Icc (-(3 / 4 : ℝ) ^ 2) 0 →
      Lp L2Vec3 3 (volume.restrict (vec3Ball (0 : Vec3) (3 / 4 : ℝ))))
    (W : Vec3 × Icc (-(3 / 4 : ℝ) ^ 2) 0 → Vec3)
    (hW : ∀ t, (fun x => W (x,t)) =ᵐ[
      volume.restrict (vec3Ball (0 : Vec3) (3 / 4 : ℝ))]
      (fun x => weakContL3OfLp (v t x)))
    (hsourceFormula : ∀ ψ : Vec3 → Vec3,
      ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ ⊆ vec3Ball (0 : Vec3) (3 / 4 : ℝ) →
      ∀ s t : Icc (-(3 / 4 : ℝ) ^ 2) 0,
        (∫ y in vec3Ball (0 : Vec3) (3 / 4 : ℝ),
          ∑ i : Fin 3, v t y i * ψ y i) -
        (∫ y in vec3Ball (0 : Vec3) (3 / 4 : ℝ),
          ∑ i : Fin 3, v s y i * ψ y i) =
        ∫ τ in s.1..t.1, ∫ y in vec3Ball (0 : Vec3) 1,
          (∑ i : Fin 3, ∑ j : Fin 3,
            u (y,τ) i * u (y,τ) j * spatialDeriv (fun z => ψ z i) j y)
          - (∑ i : Fin 3, ∑ j : Fin 3,
            Du (y,τ) i j * spatialDeriv (fun z => ψ z i) j y)
          + p (y,τ) * ∑ i : Fin 3, spatialDeriv (fun z => ψ z i) i y
          ∂volume)
    (m : ℝ) (hm : 0 < m) :
    ∃ N : ℕ,
      ∀ C : Set Vec3, IsCompact C → C ⊆ vec3Ball (0 : Vec3) m →
      ∀ a b : ℝ, Icc a b ⊆ Icc (-m) 0 →
      ∀ w : Vec3 → L2Vec3, ContDiff ℝ (⊤ : ℕ∞) w →
        HasCompactSupport w → tsupport w ⊆ C →
        ∃ A B θ : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ 0 < θ ∧
          ∀ n s t, s ∈ Icc a b → t ∈ Icc a b →
            |(∫ x : Vec3, ∑ i : Fin 3,
                blowupLimitTraceRescaling W x₀ t₀ (r (n + N)) (x,t) i * w x i)
              - (∫ x : Vec3, ∑ i : Fin 3,
                blowupLimitTraceRescaling W x₀ t₀ (r (n + N)) (x,s) i * w x i)| ≤
              A * dist t s + B * (dist t s) ^ θ := by
  have hgoodOpen : MeasurableSet goodPointDomain := by
    rw [goodPointDomain]
    exact ((isOpen_vec3Ball (0 : Vec3) 1).measurableSet).prod measurableSet_Ioo
  have huExt : AEStronglyMeasurable (goodPointDomain.indicator u)
      (volume : Measure ParabolicPoint) :=
    (aestronglyMeasurable_indicator_iff hgoodOpen).2 hu
  rcases blowup_limit_pressure_split_data hu hDu hpmeas hL2 henergy hpLp
      hL3 hgrad (fun ψ hψ => hS2 ψ hψ) hS3 with
    ⟨hp₁, ⟨Mᵤ, hMᵤ, hsourceU⟩, ⟨Mₚ, hMₚ, hsourceP⟩, hp₂, hharm⟩
  let F : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ := pressureSplitTensor u
  let hF : ∀ i j, MemLp (F i j) (ENNReal.ofReal (3 / 2 : ℝ))
      (volume : Measure (Vec3 × ℝ)) :=
    pressureSplitTensor_memLp hu hDu henergy hL3 hgrad
  let p₁ : ParabolicPoint → ℝ := pressureSplitRieszPressure F hF
  let μsplit : Measure (Vec3 × ℝ) :=
    (volume.restrict (CKN.euclideanBall 0 1)).prod
      (volume.restrict (Ioo (-1 : ℝ) 0))
  have hμsplit : μsplit = (volume : Measure ParabolicPoint).restrict
      (spaceTimeSet (CKN.euclideanBall 0 1) (Ioo (-1 : ℝ) 0)) := by
    dsimp [μsplit]
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod Vec3 ℝ]
    rfl
  have hball1 : CKN.euclideanBall (0 : Vec3) 1 = vec3Ball 0 1 :=
    CKN.Foundation.Parabolic.euclideanBall_eq_vec3Ball (by norm_num)
  have hsplitSet : MeasurableSet
      (spaceTimeSet (CKN.euclideanBall 0 1) (Ioo (-1 : ℝ) 0)) :=
    by rw [hball1]; exact (isOpen_vec3Ball 0 1).measurableSet.prod measurableSet_Ioo
  have hsplitMem : ∀ᵐ z ∂μsplit,
      z ∈ spaceTimeSet (CKN.euclideanBall 0 1) (Ioo (-1 : ℝ) 0) := by
    rw [hμsplit]
    exact ae_restrict_mem hsplitSet
  have hp₂ind : MemLp (fun z : Vec3 × ℝ =>
      pressureSplitRemainder p p₁ (z.1,z.2)) (3 / 2 : ℝ≥0∞) μsplit := by
    simpa only [F, hF, p₁] using hp₂
  have hp₂' : MemLp (fun z : Vec3 × ℝ => p (z.1,z.2) - p₁ (z.1,z.2))
      (3 / 2 : ℝ≥0∞)
      ((volume.restrict (CKN.euclideanBall 0 1)).prod
        (volume.restrict (Ioo (-1 : ℝ) 0))) := by
    have hEq : (fun z : Vec3 × ℝ =>
        p (show ParabolicPoint from (z.1,z.2)) -
          p₁ (show ParabolicPoint from (z.1,z.2))) =ᵐ[μsplit]
        (fun z => pressureSplitRemainder p p₁ (z.1,z.2)) := by
      filter_upwards [hsplitMem] with z hz
      rcases z with ⟨x,t⟩
      change x ∈ CKN.euclideanBall 0 1 ∧ t ∈ Ioo (-1 : ℝ) 0 at hz
      have hx : x ∈ vec3Ball 0 1 := hball1 ▸ hz.1
      let z : ParabolicPoint := (x,t)
      have hmem : z ∈ goodPointDomain := by
        change x ∈ vec3Ball 0 1 ∧ t ∈ Ioo (-1 : ℝ) 0
        exact ⟨hx, hz.2⟩
      change p z - p₁ z = goodPointDomain.indicator (fun y => p y - p₁ y) z
      simp [Set.indicator, hmem]
    change MemLp (fun z : Vec3 × ℝ => p (z.1,z.2) - p₁ (z.1,z.2))
      (3 / 2 : ℝ≥0∞) μsplit
    exact (memLp_congr_ae hEq).2 hp₂ind
  have hharm' : ∀ᵐ t ∂volume.restrict (Ioo (-1 : ℝ) 0),
      CKN.Foundation.Heat.WeaklyHarmonicOn (CKN.euclideanBall 0 1)
        (fun x : Vec3 => p (x,t) - p₁ (x,t)) := by
    filter_upwards [hharm, ae_restrict_mem measurableSet_Ioo] with t hht ht
    intro ψ hψ hψc hψsupport
    have hEq : ∫ x in CKN.euclideanBall 0 1,
        (p (x,t) - p₁ (x,t)) * CKN.spatialLaplacian ψ x =
      ∫ x in CKN.euclideanBall 0 1,
        pressureSplitRemainder p p₁ (x,t) * CKN.spatialLaplacian ψ x := by
      apply setIntegral_congr_fun (CKN.isOpen_euclideanBall 0 1).measurableSet
      intro x hx
      have hx' : x ∈ vec3Ball 0 1 := hball1 ▸ hx
      let z : ParabolicPoint := (x,t)
      have hmem : z ∈ goodPointDomain := by
        change x ∈ vec3Ball 0 1 ∧ t ∈ Ioo (-1 : ℝ) 0
        exact ⟨hx', ht⟩
      have hpoint : p z - p₁ z = pressureSplitRemainder p p₁ z := by
        change p z - p₁ z = goodPointDomain.indicator (fun y => p y - p₁ y) z
        simp [Set.indicator, hmem]
      calc
        (p z - p₁ z) *
            CKN.spatialLaplacian ψ x =
          pressureSplitRemainder p p₁ z *
            CKN.spatialLaplacian ψ x := by rw [hpoint]
        _ = _ := rfl
    rw [hEq]
    exact hht ψ hψ hψc hψsupport
  have hlocal := blowup_limit_local_energy_pressure_of_source_data
    hu hDu hpmeas hL2 henergy hpLp hL3 hgrad
    (fun ψ hψ => hS2 ψ hψ) hS3 x₀ t₀ r hx₀ ht₀ hr hr0
    (m + 1) (-(m + 1)) (by linarith only [hm]) (by linarith only [hm])
  rcases hlocal with ⟨_hSuitable, ⟨Cg, Cp, hCg, hCp, henergyPressure⟩⟩
  obtain ⟨Bvel, hBvel, hvel⟩ :=
    blowupRescaledVelocity_eventually_bounded_pastBox
      (goodPointDomain.indicator u) huExt Mᵤ hMᵤ hsourceU
      x₀ t₀ r ht₀ hr hr0 (m + 1) (-(m + 1))
  obtain ⟨Bpress, hBpress, hpress⟩ :=
    blowupPressure_eventually_bounded_pastBox
      p p₁ hp₁ Mₚ hMₚ hsourceP hp₂' hharm' x₀ t₀ r hx₀ ht₀ hr hr0
      (m + 1) (-(m + 1)) (by linarith only [hm]) (by linarith only [hm])
  have hxnorm : vec3EuclideanNorm x₀ ≤ 1 / 2 := by
    rw [closure_vec3Ball (by norm_num : (0 : ℝ) < 1 / 2)] at hx₀
    simpa only [Set.mem_ofPred_eq, sub_zero] using hx₀
  have hspaceLim : Tendsto (fun k => r k * (m + 3)) atTop (nhds 0) := by
    simpa using hr0.mul_const (m + 3)
  have htimeLim : Tendsto (fun k => (r k) ^ 2 * (m + 3)) atTop (nhds 0) := by
    simpa using (hr0.pow 2).mul_const (m + 3)
  have hpairTimeLim : Tendsto (fun k => (r k) ^ 2 * m) atTop (nhds 0) := by
    simpa using (hr0.pow 2).mul_const m
  have hspaceSmall : ∀ᶠ k in atTop, r k * (m + 3) < 1 / 4 :=
    hspaceLim.eventually (eventually_lt_nhds (by norm_num))
  have htimeSmall : ∀ᶠ k in atTop, (r k) ^ 2 * (m + 3) < 3 / 4 :=
    htimeLim.eventually (eventually_lt_nhds (by norm_num))
  have hpairTimeSmall : ∀ᶠ k in atTop, (r k) ^ 2 * m < 5 / 16 :=
    hpairTimeLim.eventually (eventually_lt_nhds (by norm_num))
  have htail : ∀ᶠ k in atTop,
      eLpNorm (fun z => vec3EuclideanNorm (blowupVelocity x₀ t₀ (r k) u z))
          3 (volume.restrict (vec3Ball 0 (m + 1) ×ˢ Ioo (-(m + 1)) 0)) ≤ Bvel ∧
      eLpNorm (blowupPressure x₀ t₀ (r k) p) (3 / 2 : ℝ≥0∞)
          (volume.restrict (vec3Ball 0 (m + 1) ×ˢ Ioo (-(m + 1)) 0)) ≤ Bpress ∧
      (IntegrableOn (fun z => spatialGradientSq
          (parabolicRescaleVelocity x₀ t₀ (r k) u)
          (parabolicRescaleGradient x₀ t₀ (r k) Du) z)
          (spaceTimeSet (CKN.euclideanBall 0 (m + 1)) (Ioo (-(m + 1)) 0)) volume ∧
        2 * (∫ z in spaceTimeSet (CKN.euclideanBall 0 (m + 1))
            (Ioo (-(m + 1)) 0),
          spatialGradientSq (parabolicRescaleVelocity x₀ t₀ (r k) u)
            (parabolicRescaleGradient x₀ t₀ (r k) Du) z) ≤ Cg) ∧
      r k * (m + 3) < 1 / 4 ∧
      (r k) ^ 2 * (m + 3) < 3 / 4 ∧
      (r k) ^ 2 * m < 5 / 16 := by
    filter_upwards [hvel, hpress, henergyPressure, hspaceSmall,
      htimeSmall, hpairTimeSmall] with k hv hp he hs ht hpt
    exact ⟨hv, hp, ⟨he.1, he.2.1⟩, hs, ht, hpt⟩
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 htail
  refine ⟨N, ?_⟩
  intro C hC hCU a b hab w hw _hcompact hwsupport
  let R₀ : ℝ := m + 1
  let a₀ : ℝ := -(m + 1)
  let μC : Measure ParabolicPoint := volume.restrict (C ×ˢ Icc a b)
  let μOpen : Measure ParabolicPoint := volume.restrict
    (vec3Ball 0 R₀ ×ˢ Ioo a₀ 0)
  have hR₀ : 0 < R₀ := by dsimp [R₀]; positivity
  have ha₀ : a₀ < 0 := by dsimp [a₀]; linarith only [hm]
  have hCbig : C ⊆ vec3Ball (0 : Vec3) R₀ := by
    intro x hx
    have hx' : vec3EuclideanNorm x < m := by
      simpa only [mem_vec3Ball, sub_zero] using hCU hx
    have hmR : m < R₀ := by dsimp [R₀]; linarith only [hm]
    exact mem_vec3Ball.mpr (by simpa only [sub_zero] using lt_trans hx' hmR)
  have hIbig : Icc a b ⊆ Icc a₀ 0 := by
    intro t ht
    have ht' := hab ht
    have ha₀m : a₀ < -m := by dsimp [a₀]; nlinarith only [hm]
    exact ⟨le_of_lt (lt_of_lt_of_le ha₀m ht'.1), ht'.2⟩
  have hμbound : μC ≤ μOpen := by
    dsimp [μC, μOpen, R₀, a₀]
    exact blowupLimit_restrict_closed_interval_le_open hCbig hIbig
  have hball : CKN.euclideanBall (0 : Vec3) R₀ = vec3Ball 0 R₀ :=
    CKN.Foundation.Parabolic.euclideanBall_eq_vec3Ball hR₀
  have hterm : ∀ k, N ≤ k →
      eLpNorm (fun z => vec3EuclideanNorm (blowupVelocity x₀ t₀ (r k) u z))
          3 μOpen ≤ Bvel ∧
      eLpNorm (blowupPressure x₀ t₀ (r k) p) (3 / 2 : ℝ≥0∞) μOpen ≤ Bpress ∧
      (IntegrableOn (fun z => spatialGradientSq
          (parabolicRescaleVelocity x₀ t₀ (r k) u)
          (parabolicRescaleGradient x₀ t₀ (r k) Du) z)
          (spaceTimeSet (CKN.euclideanBall 0 R₀) (Ioo a₀ 0)) volume ∧
        2 * (∫ z in spaceTimeSet (CKN.euclideanBall 0 R₀) (Ioo a₀ 0),
          spatialGradientSq (parabolicRescaleVelocity x₀ t₀ (r k) u)
            (parabolicRescaleGradient x₀ t₀ (r k) Du) z) ≤ Cg) ∧
      r k * (m + 3) < 1 / 4 ∧ (r k) ^ 2 * (m + 3) < 3 / 4 ∧
      (r k) ^ 2 * m < 5 / 16 := by
    intro k hk
    have hk' := hN k hk
    simpa only [R₀, a₀] using hk'
  have hMgrad : (ENNReal.ofReal (Cg / 2)) ^ (1 / 2 : ℝ) < ⊤ := by
    apply ENNReal.rpow_lt_top_of_nonneg (by norm_num)
    exact ENNReal.ofReal_lt_top.ne
  let Mgrad : ℝ≥0∞ := (ENNReal.ofReal (Cg / 2)) ^ (1 / 2 : ℝ)
  have hsourceMeas : AEStronglyMeasurable
      (goodPointDomain.indicator u) (volume : Measure ParabolicPoint) := huExt
  have hDuGood : AEStronglyMeasurable Du
      (volume.restrict goodPointDomain) := by
    simpa only [goodPointDomain, spaceTimeSet] using hDu
  have hmodStage : ∀ n, ∀ i,
      MemLp (fun z => blowupVelocity x₀ t₀ (r (n + N)) u z i) 3 μC ∧
      eLpNorm (fun z => blowupVelocity x₀ t₀ (r (n + N)) u z i) 3 μC ≤ Bvel := by
    intro n i
    have hn := hterm (n + N) (Nat.le_add_left N n)
    have hnormMemOpen : MemLp
        (fun z => vec3EuclideanNorm (blowupVelocity x₀ t₀ (r (n + N)) u z))
        3 μOpen := by
      rw [memLp_iff]
      exact lt_of_le_of_lt hn.1 hBvel
    have hnormMem : MemLp
        (fun z => vec3EuclideanNorm (blowupVelocity x₀ t₀ (r (n + N)) u z))
        3 μC := hnormMemOpen.mono_measure hμbound
    have hnormBound := (eLpNorm_mono_measure _ hμbound).trans hn.1
    have hvec : AEStronglyMeasurable
        (blowupVelocity x₀ t₀ (r (n + N)) u) μC := by
      have hglobal := blowupRescaledVelocity_aestronglyMeasurable
        (goodPointDomain.indicator u) hsourceMeas x₀ t₀ (r (n + N)) (hr (n + N))
      simpa only [blowupVelocity] using hglobal.restrict
    exact blowupLimit_component_memLp_of_norm μC Bvel _ i hvec hnormMem hnormBound
  have hpressStage : ∀ n,
      MemLp (blowupPressure x₀ t₀ (r (n + N)) p) (3 / 2 : ℝ≥0∞) μC ∧
      eLpNorm (blowupPressure x₀ t₀ (r (n + N)) p) (3 / 2 : ℝ≥0∞) μC ≤ Bpress := by
    intro n
    have hn := hterm (n + N) (Nat.le_add_left N n)
    have hmemOpen : MemLp (blowupPressure x₀ t₀ (r (n + N)) p)
        (3 / 2 : ℝ≥0∞) μOpen := by
      rw [memLp_iff]
      exact lt_of_le_of_lt hn.2.1 hBpress
    exact ⟨hmemOpen.mono_measure hμbound,
      (eLpNorm_mono_measure _ hμbound).trans hn.2.1⟩
  have hgradStage : ∀ n i j,
      MemLp (fun z => blowupGradient x₀ t₀ (r (n + N)) Du z i j) 2 μC ∧
      eLpNorm (fun z => blowupGradient x₀ t₀ (r (n + N)) Du z i j) 2 μC ≤ Mgrad := by
    intro n i j
    have hn := hterm (n + N) (Nat.le_add_left N n)
    have hspaceQuarter : r (n + N) * R₀ < 1 / 4 := by
      have hsmall := hn.2.2.2.1
      have hRle : R₀ < m + 3 := by dsimp [R₀]; nlinarith only [hm]
      exact (mul_lt_mul_of_pos_left hRle (hr (n + N))).trans hsmall
    have htimeBound : (r (n + N)) ^ 2 * (-a₀) < 3 / 4 := by
      have hsmall := hn.2.2.2.2.1
      have hRle : -a₀ < m + 3 := by dsimp [a₀]; nlinarith only [hm]
      exact (mul_lt_mul_of_pos_left hRle (sq_pos_of_pos (hr (n + N)))).trans hsmall
    have hInt : IntegrableOn (fun z => spatialGradientSq
        (parabolicRescaleVelocity x₀ t₀ (r (n + N)) u)
        (parabolicRescaleGradient x₀ t₀ (r (n + N)) Du) z)
        (spaceTimeSet (vec3Ball 0 R₀) (Ioo a₀ 0)) volume := by
      simpa only [hball, R₀, a₀, spaceTimeSet] using hn.2.2.1.1
    have henergyBound : (∫ z in spaceTimeSet (vec3Ball 0 R₀) (Ioo a₀ 0),
        spatialGradientSq (parabolicRescaleVelocity x₀ t₀ (r (n + N)) u)
          (parabolicRescaleGradient x₀ t₀ (r (n + N)) Du) z) ≤ Cg / 2 := by
      apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).2
      simpa only [hball, R₀, a₀, spaceTimeSet, mul_comm] using hn.2.2.1.2
    have hDuRescale := blowupLimit_rescaleGradient_aestronglyMeasurable
      hDuGood x₀ t₀ (r (n + N)) R₀ a₀ (hr (n + N)) hxnorm ht₀
      (by exact hspaceQuarter.trans (by norm_num : (1 / 4 : ℝ) < 1 / 2))
      htimeBound
    have hrow := blowup_gradient_component_eLpNorm_le_of_integral_bound
      (spaceTimeSet (vec3Ball 0 R₀) (Ioo a₀ 0))
      (parabolicRescaleVelocity x₀ t₀ (r (n + N)) u)
      (parabolicRescaleGradient x₀ t₀ (r (n + N)) Du) i (Cg / 2)
      hDuRescale hInt henergyBound
    have hrowMem : MemLp (fun z => vec3EuclideanNorm
        (parabolicRescaleGradient x₀ t₀ (r (n + N)) Du z i)) 2 μOpen := by
      rw [memLp_iff]
      have hfin := ENNReal.rpow_lt_top_of_nonneg
        (by norm_num : (0 : ℝ) ≤ (1 / 2 : ℝ))
        (ENNReal.ofReal_lt_top.ne : ENNReal.ofReal (Cg / 2) ≠ ⊤)
      exact lt_of_le_of_lt hrow hfin
    have hrowBound : eLpNorm (fun z => vec3EuclideanNorm
        (parabolicRescaleGradient x₀ t₀ (r (n + N)) Du z i)) 2 μOpen ≤ Mgrad := by
      change eLpNorm (fun z => vec3EuclideanNorm
        (parabolicRescaleGradient x₀ t₀ (r (n + N)) Du z i)) 2
        (volume.restrict (spaceTimeSet (vec3Ball 0 R₀) (Ioo a₀ 0))) ≤
          (ENNReal.ofReal (Cg / 2)) ^ (1 / 2 : ℝ)
      exact hrow
    have hrowVecAEM : AEStronglyMeasurable
        (fun z => parabolicRescaleGradient x₀ t₀ (r (n + N)) Du z i) μOpen :=
      (continuous_apply i).comp_aestronglyMeasurable hDuRescale
    have hscalarAEM : AEStronglyMeasurable
        (fun z => parabolicRescaleGradient x₀ t₀ (r (n + N)) Du z i j) μOpen :=
      (continuous_apply j).comp_aestronglyMeasurable hrowVecAEM
    have hpoint (z : ParabolicPoint) :
        ‖parabolicRescaleGradient x₀ t₀ (r (n + N)) Du z i j‖ ≤
          ‖vec3EuclideanNorm
            (parabolicRescaleGradient x₀ t₀ (r (n + N)) Du z i)‖ := by
      calc
        ‖parabolicRescaleGradient x₀ t₀ (r (n + N)) Du z i j‖ ≤
            vec3EuclideanNorm
              (parabolicRescaleGradient x₀ t₀ (r (n + N)) Du z i) :=
          (norm_le_pi_norm _ j).trans (norm_le_vec3EuclideanNorm _)
        _ = ‖vec3EuclideanNorm
            (parabolicRescaleGradient x₀ t₀ (r (n + N)) Du z i)‖ := by
          rw [Real.norm_eq_abs,
            abs_of_nonneg (vec3EuclideanNorm_nonneg _)]
    have hscalarMemOpen : MemLp
        (fun z => parabolicRescaleGradient x₀ t₀ (r (n + N)) Du z i j) 2 μOpen :=
      hrowMem.of_le hscalarAEM (Filter.Eventually.of_forall hpoint)
    have hscalarBoundOpen : eLpNorm
        (fun z => parabolicRescaleGradient x₀ t₀ (r (n + N)) Du z i j) 2 μOpen ≤ Mgrad :=
      (eLpNorm_mono_ae hscalarAEM (Filter.Eventually.of_forall hpoint)).trans hrowBound
    have hmu : μC ≤ μOpen := by
      dsimp [μC, μOpen, R₀, a₀]
      exact blowupLimit_restrict_closed_interval_le_open hCbig hIbig
    have hscalarMem : MemLp
        (fun z => parabolicRescaleGradient x₀ t₀ (r (n + N)) Du z i j) 2 μC :=
      hscalarMemOpen.mono_measure hmu
    have hscalarBound := (eLpNorm_mono_measure _ hmu).trans hscalarBoundOpen
    have heqFields := blowupFields_eq_rescale_on_cylinder u Du p
      x₀ t₀ (r (n + N)) R₀ a₀ hxnorm ht₀ (hr (n + N))
      hspaceQuarter htimeBound
    have hsetMeas : MeasurableSet (spaceTimeSet (vec3Ball 0 R₀) (Ioo a₀ 0)) :=
      (isOpen_vec3Ball 0 R₀).measurableSet.prod measurableSet_Ioo
    have htargetMem : ∀ᵐ z ∂μC,
        z ∈ spaceTimeSet (vec3Ball 0 R₀) (Ioo a₀ 0) := by
      exact ae_mono hmu (ae_restrict_mem hsetMeas)
    have heqAE : (fun z => blowupGradient x₀ t₀ (r (n + N)) Du z i j) =ᵐ[μC]
        (fun z => parabolicRescaleGradient x₀ t₀ (r (n + N)) Du z i j) := by
      filter_upwards [htargetMem] with z hz
      exact congrArg (fun d => d i j) (heqFields.2.1 hz)
    refine ⟨(memLp_congr_ae heqAE).2 hscalarMem, ?_⟩
    rw [eLpNorm_congr_ae heqAE]
    exact hscalarBound
  have hpairTime (n : ℕ) (τ : ℝ) (hτ : τ ∈ Icc a b) :
      t₀ + (r (n + N)) ^ 2 * τ ∈ Icc (-(3 / 4 : ℝ) ^ 2) 0 := by
    have hτ' := hab hτ
    have hτlo : -m ≤ τ := hτ'.1
    have hτup : τ ≤ 0 := hτ'.2
    have hr2 : 0 ≤ (r (n + N)) ^ 2 := sq_nonneg _
    have hmulLo : -((r (n + N)) ^ 2 * m) ≤ (r (n + N)) ^ 2 * τ := by
      have := mul_le_mul_of_nonneg_left hτlo hr2
      simpa only [mul_neg] using this
    have hsmall := (hN (n + N) (Nat.le_add_left N n)).2.2.2.2.2
    have hlow : -(3 / 4 : ℝ) ^ 2 ≤ t₀ + (r (n + N)) ^ 2 * τ := by
      have hstrict : -(1 / 4 : ℝ) - (r (n + N)) ^ 2 * m >
          -(3 / 4 : ℝ) ^ 2 := by
        nlinarith only [hsmall]
      exact le_trans (le_of_lt hstrict) (by nlinarith only [ht₀.1, hmulLo])
    have hupper : t₀ + (r (n + N)) ^ 2 * τ ≤ 0 := by
      have hmulUp := mul_le_mul_of_nonneg_left hτup hr2
      have hmulUp' : (r (n + N)) ^ 2 * τ ≤ 0 := by simpa using hmulUp
      exact add_nonpos ht₀.2 hmulUp'
    exact ⟨hlow, hupper⟩
  have himage (n : ℕ) :
      (fun x : Vec3 => x₀ + r (n + N) • x) '' C ⊆
        vec3Ball (0 : Vec3) (3 / 4 : ℝ) := by
    intro y hy
    rcases hy with ⟨x, hxC, rfl⟩
    have hxnorm' : vec3EuclideanNorm x < m := by
      simpa only [mem_vec3Ball, sub_zero] using hCU hxC
    have hsmall := (hN (n + N) (Nat.le_add_left N n)).2.2.2.1
    have hmR : m < m + 3 := by nlinarith only [hm]
    have hscale : vec3EuclideanNorm (r (n + N) • x) =
        r (n + N) * vec3EuclideanNorm x := by
      rw [vec3EuclideanNorm_smul, abs_of_pos (hr (n + N))]
    have hscaleLt : vec3EuclideanNorm (r (n + N) • x) < 1 / 4 := by
      rw [hscale]
      calc
        r (n + N) * vec3EuclideanNorm x < r (n + N) * m :=
          mul_lt_mul_of_pos_left hxnorm' (hr (n + N))
        _ < r (n + N) * (m + 3) :=
          mul_lt_mul_of_pos_left hmR (hr (n + N))
        _ < 1 / 4 := hsmall
    have hadd := vec3EuclideanNorm_add_le x₀ (r (n + N) • x)
    have hnormY : vec3EuclideanNorm (x₀ + r (n + N) • x) < 3 / 4 := by
      have hsum : vec3EuclideanNorm x₀ +
          vec3EuclideanNorm (r (n + N) • x) < 3 / 4 := by
        nlinarith only [hxnorm, hscaleLt]
      exact lt_of_le_of_lt hadd hsum
    simpa only [mem_vec3Ball, sub_zero] using hnormY
  have htestBounds := blowup_limit_smooth_test_derivative_bounds
    hC a b w hw hwsupport
  obtain ⟨Mtest, Mdiv, hMtest, hMdiv, hDw, hdivw⟩ := htestBounds
  have hDw' : ∀ i j,
      MemLp (fun z : ParabolicPoint => spatialDeriv (fun x => w x i) j z.1)
        ⊤ μC ∧
      eLpNorm (fun z : ParabolicPoint => spatialDeriv (fun x => w x i) j z.1)
        ⊤ μC ≤ Mtest := by
    intro i j
    simpa only [μC, PiLp.toLp_apply] using hDw i j
  have hdivw' : MemLp (fun z : ParabolicPoint =>
      ∑ i : Fin 3, spatialDeriv (fun x => w x i) i z.1) ⊤ μC ∧
      eLpNorm (fun z : ParabolicPoint =>
        ∑ i : Fin 3, spatialDeriv (fun x => w x i) i z.1) ⊤ μC ≤ Mdiv := by
    simpa only [μC, PiLp.toLp_apply] using hdivw
  have hmod : ∃ A B θ : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ 0 < θ ∧
      ∀ n s t, s ∈ Icc a b → t ∈ Icc a b →
        |(∫ x : Vec3, ∑ i : Fin 3,
            blowupLimitTraceRescaling W x₀ t₀ (r (n + N)) (x,t) i * w x i)
          - (∫ x : Vec3, ∑ i : Fin 3,
            blowupLimitTraceRescaling W x₀ t₀ (r (n + N)) (x,s) i * w x i)| ≤
          A * dist t s + B * (dist t s) ^ θ := by
    by_cases hab' : a ≤ b
    · have hb0 : b ≤ 0 := (hab ⟨hab', le_rfl⟩).2
      exact blowup_limit_rescaled_trace_pairing_modulus_of_source_flux
        v W hW hsourceFormula hC a b hb0
        (fun n => r (n + N)) (fun n => hr (n + N)) himage t₀ ht₀.2
        (fun n τ hτ => hpairTime n τ hτ)
        Bvel Mgrad Bpress Mtest Mdiv hBvel hMgrad hBpress hMtest hMdiv
        (by
          intro n i
          simpa only [blowupVelocity] using hmodStage n i)
        (by
          intro n i j
          exact hgradStage n i j)
        hpressStage w hw hwsupport hDw' hdivw'
    · refine ⟨0, 0, 1, by norm_num, by norm_num, by norm_num, ?_⟩
      intro n s t hs ht
      exact (hab' (le_trans hs.1 hs.2)).elim
  obtain ⟨A, B, θ, hA, hB, hθ, hmod⟩ := hmod
  refine ⟨A, B, θ, hA, hB, hθ, ?_⟩
  intro n s t hs ht
  exact hmod n s t hs ht

end ESS

end
