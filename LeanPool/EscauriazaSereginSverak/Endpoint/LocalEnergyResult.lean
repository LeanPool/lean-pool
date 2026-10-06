/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.LocalEnergyLimit
public import LeanPool.CaffarelliKohnNirenberg.Leray.Support.LocalEnergyCylinderL4
public import LeanPool.EscauriazaSereginSverak.Endpoint.LocalEnergySuitability
public import LeanPool.CaffarelliKohnNirenberg.Foundation.ParabolicMeasure
public import LeanPool.CaffarelliKohnNirenberg.ClassEquivalence.Constructor
public import LeanPool.CaffarelliKohnNirenberg.ClassEquivalence.TestSupport
public import LeanPool.CaffarelliKohnNirenberg.Statements.SuitableWeakSolution
public import LeanPool.CaffarelliKohnNirenberg.ClassEquivalence.MainTheorems

/-!
# Local Energy Result

Local energy identities and limit passages for the endpoint regularity proof.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic CKN


noncomputable section

namespace ESS

private theorem localEnergyExpandedIdentityAlgebra
    (v : Vec3) (G : Fin 3 → Fin 3 → ℝ) (p ψ ψt : ℝ)
    (ψs ψss : Fin 3 → ℝ) :
    -(∑ i : Fin 3, v i * v i) * (ψt + ∑ i, ψss i)
      - ∑ i : Fin 3, ∑ j : Fin 3, v i * v i * v j * ψs j
      - ∑ i : Fin 3, p * v i * (2 * ψs i)
      + ∑ i : Fin 3, ∑ j : Fin 3, G i j * G i j * (2 * ψ) =
    2 * (∑ i : Fin 3, ∑ j : Fin 3, G i j * G i j) * ψ
      - ((vec3EuclideanNorm v) ^ 2 * (ψt + ∑ i, ψss i)
        + ((vec3EuclideanNorm v) ^ 2 + 2 * p) * ∑ i, v i * ψs i) := by
  have hnorm : vec3EuclideanNorm v ^ 2 = ∑ i : Fin 3, v i ^ 2 := by
    unfold vec3EuclideanNorm
    rw [Real.sq_sqrt]
    exact Finset.sum_nonneg fun i _ => sq_nonneg (v i)
  have hconv :
      ∑ i : Fin 3, ∑ j : Fin 3, v i * v i * v j * ψs j =
        (∑ i : Fin 3, v i ^ 2) * ∑ j : Fin 3, v j * ψs j := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring_nf
  have hp :
      ∑ i : Fin 3, p * v i * (2 * ψs i) =
        (2 * p) * ∑ i : Fin 3, v i * ψs i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring_nf
  have hgrad :
      ∑ i : Fin 3, ∑ j : Fin 3, G i j * G i j * (2 * ψ) =
        2 * (∑ i : Fin 3, ∑ j : Fin 3, G i j * G i j) * ψ := by
    calc
      _ = (∑ i : Fin 3, ∑ j : Fin 3, G i j * G i j) * (2 * ψ) := by
        rw [Finset.sum_mul]
        congr 1
        funext i
        rw [Finset.sum_mul]
      _ = _ := by ring_nf
  rw [hnorm, hconv, hp, hgrad]
  ring_nf

private theorem integral_eq_of_support_inside
    {S T K : Set ParabolicPoint} {f : ParabolicPoint → ℝ}
    (hKS : K ⊆ S) (hST : S ⊆ T)
    (hSmeas : MeasurableSet S) (hTmeas : MeasurableSet T)
    (hf : ∀ z, z ∉ K → f z = 0) :
    (∫ z in T, f z ∂(volume : Measure ParabolicPoint)) =
      ∫ z in S, f z ∂(volume : Measure ParabolicPoint) := by
  have hindicator : T.indicator f =ᵐ[volume] S.indicator f := by
    filter_upwards [] with z
    by_cases hzK : z ∈ K
    · simp [hST (hKS hzK), hKS hzK]
    · have hz0 := hf z hzK
      by_cases hzS : z ∈ S
      · simp [hST hzS, hzS, hz0]
      · simp [hzS, hz0]
  calc
    _ = ∫ z, T.indicator f z ∂(volume : Measure ParabolicPoint) :=
      (integral_indicator hTmeas).symm
    _ = ∫ z, S.indicator f z ∂(volume : Measure ParabolicPoint) :=
      integral_congr_ae hindicator
    _ = _ := integral_indicator hSmeas

private theorem localEnergyIdentityDensityProduct_parabolic
    (u : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (ψ : Vec3 × ℝ → ℝ) (z : ParabolicPoint) :
    localEnergyIdentityDensityProduct u Du p ψ (parabolicHomeomorph z) =
      2 * (spatialGradientSq u Du z *
        (show ParabolicPoint → ℝ from ψ) z) -
        ((vec3EuclideanNorm (u z)) ^ 2 *
            (timePartial (show ParabolicPoint → ℝ from ψ) z +
              ∑ i, spatialSecondPartial (show ParabolicPoint → ℝ from ψ) i i z) +
          ((vec3EuclideanNorm (u z)) ^ 2 + 2 * p z) *
            ∑ i, u z i * spatialPartial (show ParabolicPoint → ℝ from ψ) i z) := by
  rcases z with ⟨x, t⟩
  simp [localEnergyIdentityDensityProduct, parabolicHomeomorph_apply,
    parabolicHomeomorph_symm_apply]
  ring_nf

private theorem setIntegral_eq_two_mul_sub
    {α : Type} [MeasurableSpace α] {μ : Measure α} {S : Set α}
    {F G H : α → ℝ} (hF : IntegrableOn F S μ) (hG : IntegrableOn G S μ)
    (hpoint : ∀ z, H z = 2 * F z - G z) :
    (∫ z in S, H z ∂μ) = 2 * (∫ z in S, F z ∂μ) - ∫ z in S, G z ∂μ := by
  calc
    _ = ∫ z in S, (2 * F z - G z) ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with z
      exact hpoint z
    _ = _ := by
      rw [integral_sub (hF.const_mul 2) hG, integral_const_mul]

private theorem parabolicHomeomorph_symm_eq_product (z : Vec3 × ℝ) :
    (parabolicHomeomorph.symm z : ParabolicPoint) = z := by
  rcases z with ⟨x, t⟩
  rfl

private theorem parabolicHomeomorph_eq_product (z : ParabolicPoint) :
    (parabolicHomeomorph z : Vec3 × ℝ) = z := by
  rcases z with ⟨x, t⟩
  rfl

private theorem parabolic_tsupport_iff_product
    {V : Type} [Zero V] {φ : Vec3 × ℝ → V} (z : ParabolicPoint) :
    z ∈ tsupport (show ParabolicPoint → V from φ) ↔
      parabolicHomeomorph z ∈ tsupport φ := by
  rw [tsupport_parabolic_eq]
  rcases z with ⟨x, t⟩
  rfl

@[expose] def localEnergyIdentityDensityProduct
    (u : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (ψ : Vec3 × ℝ → ℝ) : Vec3 × ℝ → ℝ := fun z =>
  let q : ParabolicPoint := parabolicHomeomorph.symm z
  2 * spatialGradientSq u Du q * ψ z -
    ((vec3EuclideanNorm (u q)) ^ 2 *
        (timePartial ψ z + ∑ i, spatialSecondPartial ψ i i z) +
      ((vec3EuclideanNorm (u q)) ^ 2 + 2 * p q) *
        ∑ i, u q i * spatialPartial ψ i z)

private theorem setIntegral_parabolic_to_product_on
    {S : Set ParabolicPoint} {F : ParabolicPoint → ℝ} :
    (∫ p in S, F p ∂(volume : Measure ParabolicPoint)) =
      ∫ z in parabolicHomeomorph '' S, F (parabolicHomeomorph.symm z)
        ∂(volume : Measure (Vec3 × ℝ)) := by
  have htrans := parabolicHomeomorph_measurePreserving.setIntegral_image_emb
    parabolicHomeomorph.measurableEmbedding
    (fun q : Vec3 × ℝ => F (parabolicHomeomorph.symm q)) S
  have hright :
      (∫ p in S,
        F (parabolicHomeomorph.symm (parabolicHomeomorph p))
          ∂(volume : Measure ParabolicPoint)) =
      ∫ p in S, F p ∂(volume : Measure ParabolicPoint) := by
    apply integral_congr_ae
    filter_upwards [] with p
    exact congrArg F (parabolicHomeomorph.left_inv p)
  exact hright.symm.trans htrans.symm

private theorem localEnergyExpandedBaseEqualsIndicator
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {r : ℝ} (hr1 : r < 1)
    {ψ : Vec3 × ℝ → ℝ}
    (hψ : ψ ∈ spaceTimeTestFunction (V := ℝ)
      (vec3Ball (0 : Vec3) r) (Ioo (-1) 0))
    (z : Vec3 × ℝ) :
    localEnergyLimitExpandedBaseIntegrand
      (fun q i => localEnergyVelocityZeroExtension u i q)
      (fun _ _ _ => 0)
      (fun q i j => localEnergyGradientZeroExtension Du i j q)
      (localEnergyPressureZeroExtension p)
      (show ParabolicPoint → ℝ from ψ) z =
        (tsupport ψ).indicator (localEnergyIdentityDensityProduct u Du p ψ) z := by
  let Ωr : Set Vec3 := vec3Ball (0 : Vec3) r
  let I : Set ℝ := Ioo (-1) 0
  let Q : Set (Vec3 × ℝ) := Ωr ×ˢ I
  let K : Set (Vec3 × ℝ) := tsupport ψ
  let U : Set (Vec3 × ℝ) := localEnergyUnitProductCylinder
  let ψP : ParabolicPoint → ℝ := show ParabolicPoint → ℝ from ψ
  have hQsub : Q ⊆ U := by
    intro z hz
    rcases hz with ⟨hzx, hzt⟩
    change z.1 ∈ vec3Ball (0 : Vec3) 1 ∧ z.2 ∈ Ioo (-1) 0
    constructor
    · apply mem_vec3Ball.mpr
      calc
        vec3EuclideanNorm (z.1 - 0) < r := mem_vec3Ball.mp hzx
        _ < 1 := hr1
    · exact hzt
    rcases z with ⟨x, t⟩
    let z : Vec3 × ℝ := (x, t)
    by_cases hz : z ∈ K
    · have hzQ : z ∈ Q := hψ.2.2 hz
      have hzU : z ∈ U := hQsub hzQ
      have hvel (i : Fin 3) :
          localEnergyVelocityZeroExtension u i z =
            u (parabolicHomeomorph.symm z) i := by
        change localEnergyUnitProductCylinder.indicator
          (fun q => u q i) z = u (parabolicHomeomorph.symm z) i
        have hzU' : z ∈ localEnergyUnitProductCylinder := by
          simpa [U] using hzU
        rw [Set.indicator_of_mem hzU']
        rw [parabolicHomeomorph_symm_eq_product]
      have hgrad0 (i j : Fin 3) :
          localEnergyGradientZeroExtension Du i j z =
            Du (parabolicHomeomorph.symm z) i j := by
        change localEnergyUnitProductCylinder.indicator
          (fun q => Du q i j) z = Du (parabolicHomeomorph.symm z) i j
        have hzU' : z ∈ localEnergyUnitProductCylinder := by
          simpa [U] using hzU
        rw [Set.indicator_of_mem hzU']
        rw [parabolicHomeomorph_symm_eq_product]
      have hpress : localEnergyPressureZeroExtension p z =
          p (parabolicHomeomorph.symm z) := by
        change localEnergyUnitProductCylinder.indicator
          (fun q : Vec3 × ℝ => p (parabolicHomeomorph.symm q)) z =
          p (parabolicHomeomorph.symm z)
        have hzU' : z ∈ localEnergyUnitProductCylinder := by
          simpa [U] using hzU
        rw [Set.indicator_of_mem hzU']
      change localEnergyLimitExpandedBaseIntegrand
        (fun q i => localEnergyVelocityZeroExtension u i q)
        (fun _ _ _ => 0)
        (fun q i j => localEnergyGradientZeroExtension Du i j q)
        (localEnergyPressureZeroExtension p) ψP z =
          (tsupport ψ).indicator (localEnergyIdentityDensityProduct u Du p ψ) z
      simp only [Set.indicator_of_mem hz]
      dsimp [localEnergyLimitExpandedBaseIntegrand]
      simp only [hvel, hgrad0, hpress, ψP]
      change _ = 2 * (∑ i : Fin 3, ∑ j : Fin 3,
          Du (parabolicHomeomorph.symm z) i j ^ 2) * ψ z - _
      have hcalc := localEnergyExpandedIdentityAlgebra
        (u (parabolicHomeomorph.symm z))
        (fun i j => Du (parabolicHomeomorph.symm z) i j)
        (p (parabolicHomeomorph.symm z)) (ψ z)
        (timePartial ψP (parabolicHomeomorph.symm z))
        (fun i => spatialPartial ψP i (parabolicHomeomorph.symm z))
        (fun i => spatialSecondPartial ψP i i (parabolicHomeomorph.symm z))
      have hnorm : vec3EuclideanNorm (u (parabolicHomeomorph.symm z)) ^ 2 =
          ∑ i : Fin 3, (u (parabolicHomeomorph.symm z) i) ^ 2 := by
        unfold vec3EuclideanNorm
        rw [Real.sq_sqrt]
        exact Finset.sum_nonneg fun i _ => sq_nonneg (u (parabolicHomeomorph.symm z) i)
      simpa [localEnergyIdentityDensityProduct, spatialGradientSq,
        hnorm, pow_two, parabolicHomeomorph_apply,
        parabolicHomeomorph_symm_apply, Prod.eta, ψP] using hcalc
    · have hz' : (x, t) ∉ tsupport ψ := by
        simpa [K] using hz
      have hψzero : ψ (x, t) = 0 := image_eq_zero_of_notMem_tsupport hz'
      have htime : timePartial ψ (x, t) = 0 := timePartial_eq_zero_off_tsupport hz'
      have hspace (i : Fin 3) : spatialPartial ψ i (x, t) = 0 :=
        spatialPartial_eq_zero_off_tsupport hz' i
      have hsecond (i : Fin 3) : spatialSecondPartial ψ i i (x, t) = 0 :=
        spatialSecondPartial_eq_zero_off_tsupport hz' i i
      simp only [K, Set.indicator_of_notMem hz']
      dsimp [localEnergyLimitExpandedBaseIntegrand]
      simp [hψzero, htime, hspace, hsecond, ψP]

/-- The energy equality on a smaller cylinder, obtained as the limit of the
space-time mollified local energy identities. -/
theorem localEnergyIdentity_of_essLocalData
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {r : ℝ} (hr1 : r < 1)
    (hu : AEStronglyMeasurable u
      (volume.restrict (spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0))))
    (hDu : AEStronglyMeasurable Du
      (volume.restrict (spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0))))
    (hp : AEStronglyMeasurable p
      (volume.restrict (spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0))))
    (hL2 : essSup
      (fun t : ℝ => ∫⁻ x in vec3Ball (0 : Vec3) 1, ‖u (x, t)‖ₑ ^ (2 : ℝ))
      (volume.restrict (Ioo (-1) 0)) < ⊤)
    (henergy : (∫⁻ z in spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0),
      ‖u z‖ₑ ^ (2 : ℝ) + ‖Du z‖ₑ ^ (2 : ℝ)) < ⊤)
    (hpLp : MemLp p (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0))))
    (hL3 : essSup (fun t : ℝ => ∫⁻ x in vec3Ball (0 : Vec3) 1,
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
    {ψ : Vec3 × ℝ → ℝ}
    (hψ : ψ ∈ spaceTimeTestFunction (V := ℝ)
      (vec3Ball (0 : Vec3) r) (Ioo (-1) 0)) :
    2 * ∫ z in spaceTimeSet (vec3Ball (0 : Vec3) r) (Ioo (-1) 0),
        spatialGradientSq u Du z * ψ z =
      ∫ z in spaceTimeSet (vec3Ball (0 : Vec3) r) (Ioo (-1) 0),
        (vec3EuclideanNorm (u z)) ^ 2 *
            (timePartial ψ z + ∑ i, spatialSecondPartial ψ i i z) +
          ((vec3EuclideanNorm (u z)) ^ 2 + 2 * p z) *
            ∑ i, u z i * spatialPartial ψ i z := by
  let Ωr : Set Vec3 := vec3Ball (0 : Vec3) r
  let I : Set ℝ := Ioo (-1) 0
  let Q : Set (Vec3 × ℝ) := Ωr ×ˢ I
  let K : Set (Vec3 × ℝ) := tsupport ψ
  let Kp : Set ParabolicPoint := tsupport (show ParabolicPoint → ℝ from ψ)
  let U : Set (Vec3 × ℝ) := localEnergyUnitProductCylinder
  let u0 : Vec3 × ℝ → Vec3 := fun z i => localEnergyVelocityZeroExtension u i z
  let g0 : Vec3 × ℝ → Fin 3 → Fin 3 → ℝ :=
    fun z i j => localEnergyGradientZeroExtension Du i j z
  let p0 : Vec3 × ℝ → ℝ := localEnergyPressureZeroExtension p
  let ψP : ParabolicPoint → ℝ := show ParabolicPoint → ℝ from ψ
  let F : Vec3 × ℝ → ℝ :=
    localEnergyLimitExpandedBaseIntegrand u0 (fun _ _ _ => 0) g0 p0 ψP
  let Hprod : Vec3 × ℝ → ℝ := localEnergyIdentityDensityProduct u Du p ψ
  let Hpara : ParabolicPoint → ℝ :=
    fun z => Hprod (parabolicHomeomorph z)
  have hQsub : Q ⊆ U := by
    intro z hz
    rcases hz with ⟨hzx, hzt⟩
    change z.1 ∈ vec3Ball (0 : Vec3) 1 ∧ z.2 ∈ Ioo (-1) 0
    constructor
    · apply mem_vec3Ball.mpr
      calc
        vec3EuclideanNorm (z.1 - 0) < r := mem_vec3Ball.mp hzx
        _ < 1 := hr1
    · exact hzt
  have hψU : tsupport ψ ⊆ U := by
    intro z hz
    exact hQsub (hψ.2.2 hz)
  have hdata := suitableData_of_essLocalData hr1 hu hDu hp hL2 henergy hpLp hgrad
  have hS3base : ∀ φ : ParabolicPoint → Vec3,
      φ ∈ spaceTimeTestFunction (V := Vec3)
        (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0) →
      ∫ z in spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0),
        (-(∑ i : Fin 3, u z i * timePartial (fun y => φ y i) z)
          - ∑ i : Fin 3, ∑ j : Fin 3,
              u z i * u z j * spatialPartial (fun y => φ y i) j z
          + ∑ i : Fin 3, ∑ j : Fin 3,
              Du z i j * spatialPartial (fun y => φ y i) j z
          - p z * ∑ i : Fin 3, spatialPartial (fun y => φ y i) i z) = 0 := by
    intro φ hφ
    simpa using hS3 φ hφ
  have hglobal := localEnergy_mollifiedBase_integral_limit_zero
    hu hDu henergy hpLp hL3 hgrad hS2 hS3base hψ.1 hψ.2.1 hψU
  have hpoint := localEnergyExpandedBaseEqualsIndicator hr1 hψ
  have hKmeas : MeasurableSet K := isClosed_tsupport ψ |>.measurableSet
  have hFset : ∫ z, F z ∂(volume : Measure (Vec3 × ℝ)) =
      ∫ z in K, Hprod z ∂(volume : Measure (Vec3 × ℝ)) := by
    calc
      _ = ∫ z, K.indicator Hprod z
          ∂(volume : Measure (Vec3 × ℝ)) :=
            integral_congr_ae (Filter.Eventually.of_forall hpoint)
      _ = _ := integral_indicator hKmeas
  have hKintD : IntegrableOn
      (fun z : ParabolicPoint => spatialGradientSq u Du z * ψP z) Kp volume := by
    simpa [Kp, ψP] using
      dissipation_integrand_integrableOn_of_data hdata hψ
  have hKintR : IntegrableOn
      (fun z : ParabolicPoint =>
        (vec3EuclideanNorm (u z)) ^ 2 *
            (timePartial ψP z + ∑ i, spatialSecondPartial ψP i i z) +
          ((vec3EuclideanNorm (u z)) ^ 2 + 2 * p z) *
            ∑ i, u z i * spatialPartial ψP i z) Kp volume := by
    simpa [Kp, ψP] using localEnergy_integrand_integrableOn_of_data hdata hψ
  have hsplitPoint (z : ParabolicPoint) : Hpara z =
      2 * (spatialGradientSq u Du z * ψP z) -
        ((vec3EuclideanNorm (u z)) ^ 2 *
            (timePartial ψP z + ∑ i, spatialSecondPartial ψP i i z) +
          ((vec3EuclideanNorm (u z)) ^ 2 + 2 * p z) *
            ∑ i, u z i * spatialPartial ψP i z) := by
    simpa [Hpara, ψP] using
      localEnergyIdentityDensityProduct_parabolic u Du p ψ z
  have hsplit := setIntegral_eq_two_mul_sub hKintD hKintR hsplitPoint
  have himage : parabolicHomeomorph '' Kp = K := by
    ext z
    constructor
    · rintro ⟨q, hq, hqz⟩
      have hqprod : parabolicHomeomorph q ∈ tsupport ψ :=
        (parabolic_tsupport_iff_product (φ := ψ) q).mp hq
      simpa [K, hqz] using hqprod
    · intro hz
      refine ⟨parabolicHomeomorph.symm z, ?_,
        parabolicHomeomorph.apply_symm_apply z⟩
      apply (parabolic_tsupport_iff_product (φ := ψ)
        (parabolicHomeomorph.symm z)).2
      rw [parabolicHomeomorph.apply_symm_apply]
      exact hz
  have hproductZero : ∫ z in K, Hprod z
      ∂(volume : Measure (Vec3 × ℝ)) = 0 := by
    rw [← hFset]
    exact hglobal
  have hparabolicZero : ∫ z in Kp, Hpara z ∂(volume : Measure ParabolicPoint) = 0 := by
    have htrans := setIntegral_parabolic_to_product_on (S := Kp) (F := Hpara)
    rw [himage] at htrans
    have hfun : (fun z : Vec3 × ℝ => Hpara (parabolicHomeomorph.symm z)) = Hprod := by
      funext z
      change Hprod (parabolicHomeomorph (parabolicHomeomorph.symm z)) = Hprod z
      rw [parabolicHomeomorph.apply_symm_apply]
    rw [hfun] at htrans
    exact htrans.trans hproductZero
  have hidentity : 2 * ∫ z in Kp, spatialGradientSq u Du z * ψP z ∂volume -
      ∫ z in Kp,
        ((vec3EuclideanNorm (u z)) ^ 2 *
            (timePartial ψP z + ∑ i, spatialSecondPartial ψP i i z) +
          ((vec3EuclideanNorm (u z)) ^ 2 + 2 * p z) *
            ∑ i, u z i * spatialPartial ψP i z) ∂volume = 0 := by
    rw [← hsplit]
    exact hparabolicZero
  have hKpQ : Kp ⊆ spaceTimeSet (vec3Ball (0 : Vec3) r) (Ioo (-1) 0) :=
    tsupport_parabolic_subset_spaceTimeSet hψ
  have hQmeas : MeasurableSet
      (spaceTimeSet (vec3Ball (0 : Vec3) r) (Ioo (-1) 0)) :=
    (isOpen_spaceTimeSet _ _ (isOpen_vec3Ball (0 : Vec3) r) isOpen_Ioo).measurableSet
  have hKpmeas : MeasurableSet Kp := isClosed_tsupport ψP |>.measurableSet
  have hDoff (z : ParabolicPoint) (hz : z ∉ Kp) :
      spatialGradientSq u Du z * ψP z = 0 := by
    have hzprod : (parabolicHomeomorph z : Vec3 × ℝ) ∉ K := by
      intro hk
      apply hz
      exact (parabolic_tsupport_iff_product (φ := ψ) z).2 hk
    have hψzero := image_eq_zero_of_notMem_tsupport hzprod
    have hψzeroP : ψP z = 0 := by
      change ψ (parabolicHomeomorph z) = 0
      exact hψzero
    simp [hψzeroP]
  have hRoff (z : ParabolicPoint) (hz : z ∉ Kp) :
      (vec3EuclideanNorm (u z)) ^ 2 *
          (timePartial ψP z + ∑ i, spatialSecondPartial ψP i i z) +
        ((vec3EuclideanNorm (u z)) ^ 2 + 2 * p z) *
          ∑ i, u z i * spatialPartial ψP i z = 0 := by
    have hzprod : (parabolicHomeomorph z : Vec3 × ℝ) ∉ K := by
      intro hk
      apply hz
      exact (parabolic_tsupport_iff_product (φ := ψ) z).2 hk
    have htime : timePartial ψP z = 0 := by
      change timePartial ψ (parabolicHomeomorph z) = 0
      exact timePartial_eq_zero_off_tsupport hzprod
    have hspace (i : Fin 3) : spatialPartial ψP i z = 0 := by
      change spatialPartial ψ i (parabolicHomeomorph z) = 0
      exact spatialPartial_eq_zero_off_tsupport hzprod i
    have hsecond (i : Fin 3) : spatialSecondPartial ψP i i z = 0 := by
      change spatialSecondPartial ψ i i (parabolicHomeomorph z) = 0
      exact spatialSecondPartial_eq_zero_off_tsupport hzprod i i
    simp [htime, hspace, hsecond]
  have hDset :
      ∫ z in spaceTimeSet (vec3Ball (0 : Vec3) r) (Ioo (-1) 0),
          spatialGradientSq u Du z * ψP z ∂volume =
        ∫ z in Kp, spatialGradientSq u Du z * ψP z ∂volume :=
    integral_eq_of_support_inside (K := Kp) (S := Kp)
      (T := spaceTimeSet (vec3Ball (0 : Vec3) r) (Ioo (-1) 0))
      (by intro z hz; exact hz) hKpQ hKpmeas hQmeas hDoff
  have hRset :
      ∫ z in spaceTimeSet (vec3Ball (0 : Vec3) r) (Ioo (-1) 0),
          ((vec3EuclideanNorm (u z)) ^ 2 *
              (timePartial ψP z + ∑ i, spatialSecondPartial ψP i i z) +
            ((vec3EuclideanNorm (u z)) ^ 2 + 2 * p z) *
              ∑ i, u z i * spatialPartial ψP i z) ∂volume =
        ∫ z in Kp,
          ((vec3EuclideanNorm (u z)) ^ 2 *
              (timePartial ψP z + ∑ i, spatialSecondPartial ψP i i z) +
            ((vec3EuclideanNorm (u z)) ^ 2 + 2 * p z) *
              ∑ i, u z i * spatialPartial ψP i z) ∂volume :=
    integral_eq_of_support_inside (K := Kp) (S := Kp)
      (T := spaceTimeSet (vec3Ball (0 : Vec3) r) (Ioo (-1) 0))
      (by intro z hz; exact hz) hKpQ hKpmeas hQmeas hRoff
  have hidentityQ : 2 * ∫ z in spaceTimeSet (vec3Ball (0 : Vec3) r) (Ioo (-1) 0),
        spatialGradientSq u Du z * ψP z ∂volume =
      ∫ z in spaceTimeSet (vec3Ball (0 : Vec3) r) (Ioo (-1) 0),
        ((vec3EuclideanNorm (u z)) ^ 2 *
            (timePartial ψP z + ∑ i, spatialSecondPartial ψP i i z) +
          ((vec3EuclideanNorm (u z)) ^ 2 + 2 * p z) *
            ∑ i, u z i * spatialPartial ψP i z) ∂volume := by
    rw [← hDset, ← hRset] at hidentity
    exact (sub_eq_zero.mp hidentity)
  simpa [ψP] using hidentityQ
/-- The conclusion of `lem:lei-L4`: local space-time L⁴ regularity, local
energy equality, and suitability on every smaller cylinder. -/
theorem leiL4_of_essLocalData
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    (hu : AEStronglyMeasurable u
      (volume.restrict (spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0))))
    (hDu : AEStronglyMeasurable Du
      (volume.restrict (spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0))))
    (hp : AEStronglyMeasurable p
      (volume.restrict (spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0))))
    (hL2 : essSup
      (fun t : ℝ => ∫⁻ x in vec3Ball (0 : Vec3) 1, ‖u (x, t)‖ₑ ^ (2 : ℝ))
      (volume.restrict (Ioo (-1) 0)) < ⊤)
    (henergy : (∫⁻ z in spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0),
      ‖u z‖ₑ ^ (2 : ℝ) + ‖Du z‖ₑ ^ (2 : ℝ)) < ⊤)
    (hpLp : MemLp p (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0))))
    (hL3 : essSup (fun t : ℝ => ∫⁻ x in vec3Ball (0 : Vec3) 1,
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
          - ∑ i : Fin 3, ((0 : ParabolicPoint → Vec3) z i) * φ z i) = 0) :
    MemLp u 4 (volume.restrict
        (spaceTimeSet (vec3Ball (0 : Vec3) r) (Ioo (-1) 0))) ∧
      (∀ ψ : Vec3 × ℝ → ℝ, ψ ∈ spaceTimeTestFunction (V := ℝ)
          (vec3Ball (0 : Vec3) r) (Ioo (-1) 0) →
        2 * ∫ z in spaceTimeSet (vec3Ball (0 : Vec3) r) (Ioo (-1) 0),
            spatialGradientSq u Du z * ψ z =
          ∫ z in spaceTimeSet (vec3Ball (0 : Vec3) r) (Ioo (-1) 0),
            (vec3EuclideanNorm (u z)) ^ 2 *
                (timePartial ψ z + ∑ i, spatialSecondPartial ψ i i z) +
              ((vec3EuclideanNorm (u z)) ^ 2 + 2 * p z) *
                ∑ i, u z i * spatialPartial ψ i z) ∧
      IsSuitableWeakSolution (vec3Ball (0 : Vec3) r) (Ioo (-1) 0) 3 u Du p 0 := by
  have hL4 := velocity_memLp_four_of_essLocalData hr0 (le_of_lt hr1)
    hu hDu henergy hL3 hgrad
  have hdata := suitableData_of_essLocalData hr1 hu hDu hp hL2 henergy hpLp hgrad
  have hQopen : IsOpen
      (spaceTimeSet (vec3Ball (0 : Vec3) r) (Ioo (-1) 0)) :=
    isOpen_spaceTimeSet _ _ (isOpen_vec3Ball (0 : Vec3) r) isOpen_Ioo
  have hQmeas : MeasurableSet
      (spaceTimeSet (vec3Ball (0 : Vec3) r) (Ioo (-1) 0)) := hQopen.measurableSet
  have hQbigOpen : IsOpen
      (spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0)) :=
    isOpen_spaceTimeSet _ _ (isOpen_vec3Ball (0 : Vec3) 1) isOpen_Ioo
  have hQbigMeas : MeasurableSet
      (spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0)) := hQbigOpen.measurableSet
  have hQsmallBig :
      spaceTimeSet (vec3Ball (0 : Vec3) r) (Ioo (-1) 0) ⊆
        spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0) := by
    intro z hz
    rcases hz with ⟨hzx, hzt⟩
    refine ⟨?_, hzt⟩
    apply mem_vec3Ball.mpr
    calc
      vec3EuclideanNorm (z.1 - 0) < r := mem_vec3Ball.mp hzx
      _ < 1 := hr1
  have hdiv : ∀ ψ : Vec3 × ℝ → ℝ,
      ψ ∈ spaceTimeTestFunction (V := ℝ) (vec3Ball (0 : Vec3) r) (Ioo (-1) 0) →
      ∫ z in spaceTimeSet (vec3Ball (0 : Vec3) r) (Ioo (-1) 0),
        ∑ i, u z i * spatialPartial ψ i z = 0 := by
    intro ψ hψ
    have hψ1 : ψ ∈ spaceTimeTestFunction (V := ℝ)
        (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0) := by
      refine ⟨hψ.1, hψ.2.1, ?_⟩
      intro z hz
      rcases hψ.2.2 hz with ⟨hzx, hzt⟩
      refine ⟨?_, hzt⟩
      apply mem_vec3Ball.mpr
      calc
        vec3EuclideanNorm (z.1 - 0) < r := mem_vec3Ball.mp hzx
      _ < 1 := hr1
    let Kψ : Set ParabolicPoint :=
      tsupport (show ParabolicPoint → ℝ from ψ)
    have hKsmall : Kψ ⊆ spaceTimeSet (vec3Ball (0 : Vec3) r) (Ioo (-1) 0) := by
      intro z hz
      exact hψ.2.2 ((parabolic_tsupport_iff_product (φ := ψ) z).mp hz)
    have hzero : ∀ z, z ∉ Kψ →
        (∑ i : Fin 3, u z i * spatialPartial ψ i z) = 0 := by
      intro z hz
      have hzprod : parabolicHomeomorph z ∉ tsupport ψ := by
        intro hk
        exact hz ((parabolic_tsupport_iff_product (φ := ψ) z).2 hk)
      have hspace (i : Fin 3) : spatialPartial ψ i z = 0 := by
        rw [← parabolicHomeomorph_eq_product z]
        exact spatialPartial_eq_zero_off_tsupport hzprod i
      simp [hspace]
    have htransfer := integral_eq_of_support_inside hKsmall hQsmallBig
      hQmeas hQbigMeas hzero
    exact htransfer.symm.trans (hS2 ψ hψ1)
  have hmom : ∀ φ : Vec3 × ℝ → Vec3,
      φ ∈ spaceTimeTestFunction (V := Vec3) (vec3Ball (0 : Vec3) r) (Ioo (-1) 0) →
      ∫ z in spaceTimeSet (vec3Ball (0 : Vec3) r) (Ioo (-1) 0),
        (-(∑ i, u z i * timePartial (fun w => φ w i) z)
          - ∑ i, ∑ j, u z i * u z j * spatialPartial (fun w => φ w i) j z
          + ∑ i, ∑ j, Du z i j * spatialPartial (fun w => φ w i) j z
          - p z * ∑ i, spatialPartial (fun w => φ w i) i z
          - ∑ i, (0 : Vec3) i * φ z i) = 0 := by
    intro φ hφ
    have hφ1 : φ ∈ spaceTimeTestFunction (V := Vec3)
        (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0) := by
      refine ⟨hφ.1, hφ.2.1, ?_⟩
      intro z hz
      rcases hφ.2.2 hz with ⟨hzx, hzt⟩
      refine ⟨?_, hzt⟩
      apply mem_vec3Ball.mpr
      calc
        vec3EuclideanNorm (z.1 - 0) < r := mem_vec3Ball.mp hzx
        _ < 1 := hr1
    let Kφ : Set ParabolicPoint :=
      tsupport (show ParabolicPoint → Vec3 from φ)
    have hKsmall : Kφ ⊆ spaceTimeSet (vec3Ball (0 : Vec3) r) (Ioo (-1) 0) := by
      intro z hz
      exact hφ.2.2 ((parabolic_tsupport_iff_product (φ := φ) z).mp hz)
    have hzero : ∀ z, z ∉ Kφ →
        (-(∑ i : Fin 3, u z i * timePartial (fun w => φ w i) z)
          - ∑ i : Fin 3, ∑ j : Fin 3,
              u z i * u z j * spatialPartial (fun w => φ w i) j z
          + ∑ i : Fin 3, ∑ j : Fin 3,
              Du z i j * spatialPartial (fun w => φ w i) j z
          - p z * ∑ i : Fin 3, spatialPartial (fun w => φ w i) i z) = 0 := by
      intro z hz
      have hzprod : parabolicHomeomorph z ∉ tsupport φ := by
        intro hk
        exact hz ((parabolic_tsupport_iff_product (φ := φ) z).2 hk)
      have hcomponent (i : Fin 3) :
          parabolicHomeomorph z ∉ tsupport (fun w => φ w i) := by
        intro hmem
        apply hzprod
        exact (tsupport_component_subset φ i (fun w hzero =>
          congrArg (fun v : Vec3 => v i) hzero)) hmem
      have htime (i : Fin 3) : timePartial (fun w => φ w i) z = 0 := by
        rw [← parabolicHomeomorph_eq_product z]
        exact timePartial_eq_zero_off_tsupport (hcomponent i)
      have hspace (i j : Fin 3) :
          spatialPartial (fun w => φ w i) j z = 0 := by
        rw [← parabolicHomeomorph_eq_product z]
        exact spatialPartial_eq_zero_off_tsupport (hcomponent i) j
      simp [htime, hspace]
    have htransfer := integral_eq_of_support_inside hKsmall hQsmallBig
      hQmeas hQbigMeas hzero
    have hbig :
        ∫ z in spaceTimeSet (vec3Ball (0 : Vec3) 1) (Ioo (-1) 0),
          (-(∑ i : Fin 3, u z i * timePartial (fun w => φ w i) z)
            - ∑ i : Fin 3, ∑ j : Fin 3,
                u z i * u z j * spatialPartial (fun w => φ w i) j z
            + ∑ i : Fin 3, ∑ j : Fin 3,
                Du z i j * spatialPartial (fun w => φ w i) j z
            - p z * ∑ i : Fin 3, spatialPartial (fun w => φ w i) i z) = 0 := by
      simpa using hS3 φ hφ1
    have hsmall := htransfer.symm.trans hbig
    simpa using hsmall
  have hlei : ∀ ψ : Vec3 × ℝ → ℝ,
      ψ ∈ spaceTimeTestFunction (V := ℝ) (vec3Ball (0 : Vec3) r) (Ioo (-1) 0) →
      (∀ z, 0 ≤ ψ z) →
      2 * ∫ z in spaceTimeSet (vec3Ball (0 : Vec3) r) (Ioo (-1) 0),
          spatialGradientSq u Du z * ψ z ≤
        ∫ z in spaceTimeSet (vec3Ball (0 : Vec3) r) (Ioo (-1) 0),
          (vec3EuclideanNorm (u z)) ^ 2 *
              (timePartial ψ z + ∑ i, spatialSecondPartial ψ i i z) +
            ((vec3EuclideanNorm (u z)) ^ 2 + 2 * p z) *
              ∑ i, u z i * spatialPartial ψ i z := by
    intro ψ hψ _hψnn
    exact le_of_eq (localEnergyIdentity_of_essLocalData hr1 hu hDu hp hL2
      henergy hpLp hL3 hgrad hS2 hS3 hψ)
  have hsi := isSuitableWeakSolutionIntegrable_of_identities hdata hdiv hmom
    (by
      intro ψ hψ hψnn
      simpa using hlei ψ hψ hψnn)
  exact ⟨hL4, fun ψ hψ =>
    localEnergyIdentity_of_essLocalData hr1 hu hDu hp hL2 henergy hpLp hL3
      hgrad hS2 hS3 hψ,
    (isSuitableWeakSolution_iff_integrable).2 hsi⟩

end ESS
