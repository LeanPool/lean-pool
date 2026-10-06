/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.EssLocalProofGlue
public import LeanPool.EscauriazaSereginSverak.Endpoint.EssLocalProofLiouville
public import LeanPool.EscauriazaSereginSverak.Endpoint.EssLocalProofExterior
public import LeanPool.EscauriazaSereginSverak.Endpoint.EssLocalProofVorticity
public import LeanPool.EscauriazaSereginSverak.Endpoint.EssLocalProofBackwardUniqueness
public import LeanPool.EscauriazaSereginSverak.Endpoint.EssLocalProofInteriorVorticity
public import LeanPool.EscauriazaSereginSverak.Endpoint.EssLocalInteriorVanishing
public import LeanPool.EscauriazaSereginSverak.Endpoint.LocalEnergyResult
public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupLimitBadPoint
public import LeanPool.EscauriazaSereginSverak.Endpoint.VorticityTopTrace
public import LeanPool.EscauriazaSereginSverak.Endpoint.VorticityRegularity
public import LeanPool.EscauriazaSereginSverak.Endpoint.VorticityTopExtension
public import LeanPool.EscauriazaSereginSverak.Endpoint.EssLocalProofGlobalSuitable
public import LeanPool.EscauriazaSereginSverak.Endpoint.LocalTimeProjection
public import LeanPool.EscauriazaSereginSverak.Linear.BUAffineIntervalWeak
public import LeanPool.EscauriazaSereginSverak.Linear.BUAffineIntervalHeat

public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- The local Escauriaza–Seregin–Šverák regularity conclusion from its local
weak-solution hypotheses. -/
theorem essLocal_of_inputs
    {u : ParabolicPoint → Vec3}
    {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ}
    (hu : AEStronglyMeasurable u
      (volume.restrict
        (spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0))))
    (hDu : AEStronglyMeasurable Du
      (volume.restrict
        (spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0))))
    (hp : AEStronglyMeasurable p
      (volume.restrict
        (spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0))))
    (hL2 : essSup
      (fun t : ℝ => ∫⁻ x in vec3Ball (0 : Vec3) 1, ‖u (x, t)‖ₑ ^ (2 : ℝ))
      (volume.restrict (Ioo (-1) 0)) < ⊤)
    (henergy : (∫⁻ z in spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0),
      ‖u z‖ₑ ^ (2 : ℝ) + ‖Du z‖ₑ ^ (2 : ℝ)) < ⊤)
    (hpLp : MemLp p (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict
        (spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0))))
    (hL3 : essSup
      (fun t : ℝ => ∫⁻ x in vec3Ball (0 : Vec3) 1,
        ENNReal.ofReal (vec3EuclideanNorm (u (x, t))) ^ (3 : ℝ))
      (volume.restrict (Ioo (-1) 0)) < ⊤)
    (hgrad : ∀ᵐ t ∂(volume.restrict (Ioo (-1) 0)), ∀ i : Fin 3,
      HasWeakGradientOn (vec3Ball (0 : Vec3) 1)
        (fun x => u (x, t) i) (fun x => Du (x, t) i))
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
    (hBlowup : ∀ (ε₀ : ℝ), 0 < ε₀ →
      ∀ (x₀ : Vec3) (t₀ : ℝ) (r : ℕ → ℝ),
        x₀ ∈ closure (vec3Ball 0 (1 / 2 : ℝ)) →
        t₀ ∈ Icc (-(1 / 4 : ℝ)) 0 →
        ¬ IsGoodPoint ε₀ u p (x₀, t₀) →
        (∀ k, 0 < r k) → Tendsto r atTop (nhds 0) →
        ∃ (U : ParabolicPoint → Vec3)
          (DU : ParabolicPoint → Fin 3 → Vec3)
          (q : ParabolicPoint → ℝ),
          Measurable U ∧
          (∀ (R a : ℝ), 0 < R → a < 0 →
            IsSuitableWeakSolution (vec3Ball 0 R) (Ioo a 0) 3
              U DU q (0 : ParabolicPoint → Vec3)) ∧
          (∀ᵐ t ∂(volume.restrict (Ioo (-2 : ℝ) 0)),
            ∀ i : Fin 3,
              HasWeakGradientOn Set.univ
                (fun x : Vec3 => U (x, t) i)
                (fun x : Vec3 => DU (x, t) i)) ∧
          (∀ T : ℝ, 0 < T →
            essSup (fun t : ℝ => eLpNorm
              (fun x : Vec3 => vec3EuclideanNorm (U (x, t)))
              (3 : ℝ≥0∞) volume)
              (volume.restrict (Ioo (-T) 0)) < ⊤) ∧
          (∀ T : ℝ, 0 < T →
            MemLp q (3 / 2 : ℝ≥0∞)
              (volume.restrict
                (spaceTimeSet Set.univ (Ioo (-T) 0)))) ∧
          HasZeroDistributionalVelocityTrace U ∧
          (U =ᵐ[volume.restrict
              (spaceTimeSet Set.univ (Ioo (-2 : ℝ) 0))] 0 →
            Tendsto (fun k =>
              goodPointEnergy (blowupVelocity x₀ t₀ (r k) u)
                (blowupPressure x₀ t₀ (r k) p) 0 0 1)
              atTop (nhds 0)))
    :
    ∃ γ : ℝ, 0 < γ ∧ γ ≤ 1 ∧
      ∃ w : ParabolicPoint → Vec3,
        w =ᵐ[volume.restrict
          (parabolicCylinder (0 : Vec3) 0 (1 / 2 : ℝ))] u ∧
        ParabolicHolderVecOn
          (closure (parabolicCylinder (0 : Vec3) 0 (1 / 2 : ℝ))) w γ := by
  have hdata := essLocal_suitableData_of_inputs hu hDu hp hL2 henergy hpLp hgrad
  have henergyEq : ∀ r : ℝ, 0 < r → r < 1 →
      ∀ ψ : Vec3 × ℝ → ℝ,
        ψ ∈ spaceTimeTestFunction (V := ℝ)
          (vec3Ball (0 : Vec3) r) (Ioo (-1) 0) →
        2 * ∫ z in spaceTimeSet (vec3Ball (0 : Vec3) r) (Ioo (-1) 0),
            spatialGradientSq u Du z * ψ z =
          ∫ z in spaceTimeSet (vec3Ball (0 : Vec3) r) (Ioo (-1) 0),
            (vec3EuclideanNorm (u z)) ^ 2 *
                (timePartial ψ z + ∑ i, spatialSecondPartial ψ i i z)
              + ((vec3EuclideanNorm (u z)) ^ 2 + 2 * p z) *
                  ∑ i, u z i * spatialPartial ψ i z := by
    intro r hrpos hr1 ψ hψ
    exact (leiL4_of_essLocalData hrpos hr1 hu hDu hp hL2 henergy hpLp
      hL3 hgrad hS2 hS3).2.1 ψ hψ
  have hSuitable := essLocal_suitable_of_localEnergyEqualities hdata hS2 hS3 henergyEq
  obtain ⟨ε₀, γ₀, C₄, hε₀, hγ₀, hγ₀le, hC₄,
      hGlueAndOpen, hBadLower⟩ := goodPoint_open_glue
  obtain ⟨_hOpen, hGlue⟩ := hGlueAndOpen hSuitable
  let K : Set ParabolicPoint :=
    closure (parabolicCylinder (0 : Vec3) 0 (1 / 2 : ℝ))
  have hKregion : K ⊆ {z : ParabolicPoint |
      vec3EuclideanNorm (z.1 - 0) ≤ 1 / 2 ∧
        z.2 ∈ Icc (-(1 / 4 : ℝ)) 0} := by
    intro z hz
    change z ∈ closure (parabolicCylinder (0 : Vec3) 0 (1 / 2 : ℝ)) at hz
    rw [closure_parabolicCylinder (by norm_num : (0 : ℝ) < 1 / 2)] at hz
    rcases hz with ⟨hx, ht⟩
    refine ⟨hx, ?_⟩
    rcases ht with ⟨htlo, htup⟩
    refine ⟨?_, htup⟩
    calc
      -(1 / 4 : ℝ) ≤ 0 - (1 / 2 : ℝ) ^ 2 := by norm_num
      _ ≤ z.2 := htlo
  have hgood : ∀ z ∈ K, IsGoodPoint ε₀ u p z := by
    intro z hz
    by_contra hnotgood
    have hzregion := hKregion hz
    have hx₀ : z.1 ∈ closure (vec3Ball (0 : Vec3) (1 / 2 : ℝ)) := by
      rw [closure_vec3Ball (by norm_num : (0 : ℝ) < 1 / 2)]
      simpa only [Set.mem_ofPred_eq, sub_zero] using hzregion.1
    have ht₀ : z.2 ∈ Icc (-(1 / 4 : ℝ)) 0 := hzregion.2
    let r : ℕ → ℝ := fun k => (1 / 8 : ℝ) * (1 / ((k : ℝ) + 1))
    have hr : ∀ k, 0 < r k := by
      intro k
      dsimp [r]
      positivity
    have hr0 : Tendsto r atTop (nhds 0) := by
      simpa [r] using
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (1 / 8 : ℝ)
    have hbadEnergy := blowup_limit_bad_point_lower_bound
      ε₀ u p z.1 z.2 r hx₀ ht₀ hnotgood hr hr0
    have henergyContradiction
        (hdecay : Tendsto (fun k =>
          goodPointEnergy (blowupVelocity z.1 z.2 (r k) u)
            (blowupPressure z.1 z.2 (r k) p) 0 0 1)
            atTop (nhds 0)) : False := by
      have hpositive : (0 : ℝ≥0∞) < ENNReal.ofReal (ε₀ / 8) := by
        exact ENNReal.ofReal_pos.mpr (by positivity)
      have hsmall := hdecay.eventually_lt_const hpositive
      obtain ⟨k, hklower, hksmall⟩ := (hbadEnergy.and hsmall).exists
      exact (not_le_of_gt hksmall) hklower
    apply henergyContradiction
    obtain ⟨U, DU, q, hUmeas, hUSuitable, hUGrad, hUL3, hqLp,
      hUtrace, hdecay⟩ :=
      hBlowup ε₀ hε₀ z.1 z.2 r hx₀ ht₀ hnotgood hr hr0
    apply hdecay
    have hSliceL3 : ∀ᵐ t ∂(volume.restrict (Ioo (-2 : ℝ) 0)),
        MemLp (fun x : Vec3 => U (x, t)) (3 : ℝ≥0∞) volume :=
      essLocal_slices_memLp_of_euclidean_essSup U hUmeas
        (Ioo (-2 : ℝ) 0) (hUL3 2 (by norm_num))
    have hSliceDiv : ∀ᵐ t ∂(volume.restrict (Ioo (-2 : ℝ) 0)),
        CKN.DistributionalDivergenceFree (fun x : Vec3 => U (x, t)) :=
      essLocal_slices_divergenceFree_of_local_suitable
        U DU q hUSuitable hSliceL3
    have hUSuitableGlobal :
        IsSuitableWeakSolution Set.univ (Ioo (-12 : ℝ) 0) 3 U DU q
          (0 : ParabolicPoint → Vec3) :=
      essLocal_globalSuitable_of_local U DU q hUSuitable (-12) (by norm_num)
    have hRegularTimes := timeProjection_regularNeighborhoods_of_suitable
      (Ioo (-12 : ℝ) 0) U DU q hUSuitableGlobal
    have hRegularLocalVelocityBounds :=
      essLocal_regularTimes_localVelocityBound hRegularTimes
    obtain ⟨εA, γA, C4, hεA, hγA, hγAle, hC4, hTheoremA⟩ :=
      epsilonRegularityL3_rescaled 3 (by norm_num)
    let J : Set ℝ := Ioo (-12 : ℝ) 0
    have hJ : volume J < ⊤ := by
      simp [J]
    have htail := essLocal_exteriorCriticalTail U q hUmeas J hJ
      measurableSet_Ioo (hUL3 12 (by norm_num)) (hqLp 12 (by norm_num))
      (ENNReal.ofReal_pos.mpr hεA)
    obtain ⟨N, hNtail⟩ := htail
    let R₂ : ℝ := (N : ℝ) + 3
    have hR₂ : 2 < R₂ := by dsimp [R₂]; exact_mod_cast (by omega : 2 < N + 3)
    let M : ℝ := C4 / 2
    have hM : 0 ≤ M := by dsimp [M]; positivity
    have hUExteriorBound : ∀ (x₁ : Vec3) (t₁ : ℝ),
        R₂ < vec3EuclideanNorm x₁ → t₁ ∈ Ioo (-2 : ℝ) 0 →
        ∀ᵐ z ∂(volume.restrict (parabolicCylinder x₁ t₁ 1)),
          vec3EuclideanNorm (U z) ≤ M := by
      intro x₁ t₁ hx₁ ht₁
      have hQ2time : parabolicCylinder x₁ t₁ 2 ⊆
          spaceTimeSet Set.univ J := by
        intro z hz
        rcases (mem_parabolicCylinder.mp hz) with ⟨_hx, htlo, hthi⟩
        change z.1 ∈ Set.univ ∧ z.2 ∈ J
        refine ⟨Set.mem_univ _, ?_⟩
        dsimp [J]
        constructor
        · have htime : t₁ - 4 < z.2 := by
            simpa only [show (2 : ℝ) ^ 2 = 4 by norm_num] using htlo
          linarith only [htime, ht₁.1]
        · exact lt_of_le_of_lt hthi ht₁.2
      have hQ2tail : parabolicCylinder x₁ t₁ 2 ⊆
          {z : Vec3 × ℝ | (N : ℝ) < vec3EuclideanNorm z.1} := by
        intro z hz
        rcases (mem_parabolicCylinder.mp hz) with ⟨hx, _htlo, _hthi⟩
        have htri := vec3EuclideanNorm_add_le z.1 (x₁ - z.1)
        have hadd : z.1 + (x₁ - z.1) = x₁ := by abel
        rw [hadd] at htri
        have hdist : vec3EuclideanNorm (x₁ - z.1) =
            vec3EuclideanNorm (z.1 - x₁) := by
          rw [show x₁ - z.1 = -(z.1 - x₁) by abel,
            vec3EuclideanNorm_neg]
        rw [hdist] at htri
        have hnormx : vec3EuclideanNorm x₁ > (N : ℝ) + 3 := by
          simpa [R₂] using hx₁
        have hnormz : (N : ℝ) < vec3EuclideanNorm z.1 := by
          have hdistlt : vec3EuclideanNorm (z.1 - x₁) < 2 := by
            simpa using hx
          linarith only [htri, hnormx, hdistlt]
        exact hnormz
      have hmass : goodPointEnergy U q x₁ t₁ 2 < ENNReal.ofReal εA := by
        have hbound := hNtail N (le_rfl)
        have hprod := essLocal_setIntegral_eq_productTimeRestriction J
          (parabolicCylinder x₁ t₁ 2) hQ2time
          (fun z : Vec3 × ℝ =>
            ENNReal.ofReal (vec3EuclideanNorm (U z)) ^ (3 : ℝ) +
              ENNReal.ofReal |q z| ^ (3 / 2 : ℝ))
        unfold goodPointEnergy
        change (∫⁻ z in parabolicCylinder x₁ t₁ 2,
          ENNReal.ofReal (vec3EuclideanNorm (U z)) ^ (3 : ℝ) +
            ENNReal.ofReal |q z| ^ (3 / 2 : ℝ) ∂(volume : Measure ParabolicPoint)) < _
        calc
          _ = ∫⁻ z in parabolicCylinder x₁ t₁ 2,
              ENNReal.ofReal (vec3EuclideanNorm (U z)) ^ (3 : ℝ) +
                ENNReal.ofReal |q z| ^ (3 / 2 : ℝ)
              ∂(volume.prod (volume.restrict J)) := hprod
          _ ≤ ∫⁻ z in {z : Vec3 × ℝ | (N : ℝ) < vec3EuclideanNorm z.1},
              ENNReal.ofReal (vec3EuclideanNorm (U z)) ^ (3 : ℝ) +
                ENNReal.ofReal |q z| ^ (3 / 2 : ℝ)
              ∂(volume.prod (volume.restrict J)) := lintegral_mono_set hQ2tail
          _ < ENNReal.ofReal εA := hbound
      have hsmall : goodPointEnergy U q x₁ t₁ 2 *
          ENNReal.ofReal ((2 : ℝ)⁻¹ ^ 2) < ENNReal.ofReal εA := by
        calc
          _ ≤ goodPointEnergy U q x₁ t₁ 2 * 1 :=
            mul_le_mul_of_nonneg_left (by norm_num :
              ENNReal.ofReal ((2 : ℝ)⁻¹ ^ 2) ≤ 1) bot_le
          _ = goodPointEnergy U q x₁ t₁ 2 := by simp
          _ < ENNReal.ofReal εA := hmass
      obtain ⟨w, hwAE, hwBound, _hwHolder⟩ :=
        hTheoremA Set.univ (Ioo (-12 : ℝ) 0) U DU q hUSuitableGlobal
          x₁ t₁ 2 (by norm_num)
          (by
            intro z hz
            rw [closure_parabolicCylinder (by norm_num : (0 : ℝ) < 2)] at hz
            rcases hz with ⟨_hx, ht⟩
            change z.1 ∈ Set.univ ∧ z.2 ∈ J
            refine ⟨Set.mem_univ _, ?_⟩
            dsimp [J]
            constructor
            · linarith only [ht.1, ht₁.1]
            · exact lt_of_le_of_lt ht.2 ht₁.2)
          hsmall
      have hQ1meas : MeasurableSet (parabolicCylinder x₁ t₁ 1) :=
        measurableSet_parabolicCylinder x₁ t₁ 1
      have hwAE1 : w =ᵐ[volume.restrict (parabolicCylinder x₁ t₁ 1)] U := by
        simpa only [show (2 : ℝ) / 2 = 1 by norm_num] using hwAE
      filter_upwards [hwAE1, ae_restrict_mem hQ1meas] with z hz hzin
      rw [← hz]
      have hzcl : z ∈ closure (parabolicCylinder x₁ t₁ 1) := subset_closure hzin
      have hzcl' : z ∈ closure (parabolicCylinder x₁ t₁ (2 / 2)) := by
        simpa only [show (2 : ℝ) / 2 = 1 by norm_num] using hzcl
      have hw := hwBound z hzcl'
      simpa [M, div_eq_mul_inv] using hw
    have hCriticalMass := essLocal_globalCriticalEnergy_memLp U q hUmeas J hJ
      measurableSet_Ioo (hUL3 12 (by norm_num)) (hqLp 12 (by norm_num))
    have hCriticalMasses := essLocal_globalCriticalMasses_parabolic U q J hCriticalMass
    have hsolIntegrable := CKN.isSuitableWeakSolution_iff_integrable.mp hUSuitableGlobal
    obtain ⟨E, hE, hGradientExteriorBound⟩ :=
      essLocal_uniformGradientEnergy_of_globalMass U DU q hsolIntegrable
        (by simpa [J] using hCriticalMasses.1)
        (by simpa [J] using hCriticalMasses.2)
    have hExteriorLocalData : ∀ (x₁ : Vec3) (t₁ : ℝ),
        R₂ < vec3EuclideanNorm x₁ → t₁ ∈ Ioo (-2 : ℝ) 0 →
        ∃ (Ω : Set Vec3) (I : Set ℝ), IsOpen Ω ∧ IsOpen I ∧
          closure (parabolicCylinder x₁ t₁ 1) ⊆ spaceTimeSet Ω I ∧
          IsSuitableWeakSolution Ω I 3 U DU q (0 : ParabolicPoint → Vec3) ∧
          (∀ᵐ z ∂(volume.restrict (parabolicCylinder x₁ t₁ 1)),
            vec3EuclideanNorm (U z) ≤ M) ∧
          (∫⁻ z in parabolicCylinder x₁ t₁ 1,
            ‖DU z‖ₑ ^ (2 : ℝ)) ≤ ENNReal.ofReal (E ^ 2) := by
      intro x₁ t₁ _hx₁ ht₁
      refine ⟨Set.univ, Ioo (-12 : ℝ) 0, isOpen_univ, isOpen_Ioo, ?_,
        hUSuitableGlobal, hUExteriorBound x₁ t₁ _hx₁ ht₁,
        hGradientExteriorBound x₁ t₁ ht₁⟩
      intro z hz
      rw [closure_parabolicCylinder (by norm_num : (0 : ℝ) < 1)] at hz
      rcases hz with ⟨_hx, htI⟩
      change z.1 ∈ Set.univ ∧ z.2 ∈ Ioo (-12 : ℝ) 0
      exact ⟨Set.mem_univ _, ⟨by linarith only [htI.1, ht₁.1],
        lt_of_le_of_lt htI.2 ht₁.2⟩⟩
    have hUSuitableT : IsSuitableWeakSolution Set.univ (Ioo (-4 * 3) 0) 3
        U DU q (0 : ParabolicPoint → Vec3) := by
      simpa only [show (-4 : ℝ) * 3 = -12 by norm_num] using hUSuitableGlobal
    have hUL3T : essSup (fun t : ℝ => eLpNorm
        (fun x : Vec3 => vec3EuclideanNorm (U (x, t)))
        (3 : ℝ≥0∞) volume) (volume.restrict (Ioo (-4 * 3) 0)) < ⊤ := by
      simpa only [show (-4 : ℝ) * 3 = -12 by norm_num] using hUL3 12 (by norm_num)
    obtain ⟨Cext, hCext, ω, Dω, D2ω, Dtω,
      hωAE, hωCont, hωtop, hωbound, hωderiv, hωL2, hωineq⟩ :=
      vorticityTopExtension 3 R₂ M E (by norm_num)
        (lt_trans (by norm_num : (0 : ℝ) < 2) hR₂) hM hE
        U DU q hUSuitableT hUL3T hUtrace hExteriorLocalData
    have hVorticityZero : ∀ᵐ t ∂(volume.restrict (Ioo (-2 : ℝ) 0)),
        (fun x : Vec3 => weakVorticity DU (x, t)) =ᵐ[volume] 0 := by
      have hR₂pos : 0 < R₂ := lt_trans (by norm_num : (0 : ℝ) < 2) hR₂
      have hHalf := essLocal_exteriorVorticityZero_halfSpace R₂ Cext hR₂pos hCext
        ω Dω D2ω Dtω hωCont hωtop hωbound hωderiv hωL2 hωineq
      have hseed : ∀ᵐ z ∂(volume.restrict
          (spaceTimeSet {x : Vec3 | R₂ < x 2} (Ioo (-2 : ℝ) 0))),
          weakVorticity DU z = 0 := by
        have hsub : spaceTimeSet {x : Vec3 | R₂ < x 2} (Ioo (-2 : ℝ) 0) ⊆
            spaceTimeSet {x : Vec3 | R₂ < vec3EuclideanNorm x} (Ioo (-2 : ℝ) 0) := by
          rintro z ⟨hz1, hz2⟩
          refine ⟨?_, hz2⟩
          have hcoord := abs_apply_le_vec3EuclideanNorm z.1 2
          have hz1' : R₂ < z.1 2 := hz1
          change R₂ < vec3EuclideanNorm z.1
          linarith only [hcoord, hz1', le_abs_self (z.1 2)]
        have hmeas : MeasurableSet
            (spaceTimeSet {x : Vec3 | R₂ < x 2} (Ioo (-2 : ℝ) 0)) :=
          (isOpen_spaceTimeSet _ _ (isOpen_lt continuous_const (continuous_apply 2))
            isOpen_Ioo).measurableSet
        filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub hωAE,
          ae_restrict_mem hmeas] with z hz hzS
        rw [← hz]
        exact hHalf z.1 hzS.1 z.2 hzS.2
      exact essLocal_interiorVorticityZero hUSuitableGlobal R₂ hR₂pos hseed
    have hSliceCurl := essLocal_slices_curlFree_of_zero_vorticity
      U DU hSliceL3 hUGrad hVorticityZero
    apply essLocal_limit_zero_of_slicewise_div_curl U hUmeas
    filter_upwards [hSliceL3, hSliceDiv, hSliceCurl] with t ht hdiv hcurl
    exact ⟨by simpa using ht, hdiv, hcurl⟩
  have hγ₀le1 : γ₀ ≤ 1 := le_trans hγ₀le (by norm_num)
  exact essLocal_holder_of_all_good hγ₀ hγ₀le1 hGlue
    (by simpa only [K] using hgood)

end ESS
