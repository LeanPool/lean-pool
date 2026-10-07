/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegUniformMomentum
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegUniformIntegrationByParts
public import LeanPool.CaffarelliKohnNirenberg.Leray.RegUniformLocalEnergyFlux
public import LeanPool.CaffarelliKohnNirenberg.Statements.SpaceTimeTestFunction
public import LeanPool.CaffarelliKohnNirenberg.ClassEquivalence.TestSupport
public import LeanPool.CaffarelliKohnNirenberg.Core.Step3.LocalizedEquationBasics

/-!
# Reg Uniform Local Energy

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory Set
open scoped Topology ENNReal
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray

/-- The product topology on parabolic space-time points used in this weak identity. -/
abbrev regUniformParabolicTopologyLocalEnergy : TopologicalSpace ParabolicPoint :=
  inferInstance

/-- The product normed additive group used for spatial and temporal regularity. -/
local instance regUniformLocalEnergyNormedAddCommGroup : NormedAddCommGroup ParabolicPoint :=
  inferInstanceAs (NormedAddCommGroup (Vec3 × ℝ))

/-- The product real normed space used for spatial and temporal derivatives. -/
local instance regUniformLocalEnergyNormedSpace : NormedSpace ℝ ParabolicPoint :=
  inferInstanceAs (NormedSpace ℝ (Vec3 × ℝ))

/-- The product topology on parabolic space-time points used in this weak identity. -/
local instance (priority := 10000) regUniformLocalEnergyTopologicalSpace :
    TopologicalSpace ParabolicPoint :=
  instTopologicalSpaceProd

private def regUniformSpatialGradientDensity
    (u : ParabolicPoint → Vec3)
    (Du : ParabolicPoint → Fin 3 → Vec3)
    (z : Vec3 × ℝ) : ℝ :=
  spatialGradientSq u Du ((z.1, z.2) : ParabolicPoint)

private theorem regUniform_vec3EuclideanNorm_sq (v : Vec3) :
    vec3EuclideanNorm v ^ (2 : ℕ) = ∑ i : Fin 3, v i ^ (2 : ℕ) := by
  change (Real.sqrt (∑ i : Fin 3, v i ^ (2 : ℕ))) ^ (2 : ℕ) = _
  rw [Real.sq_sqrt (Finset.sum_nonneg fun i hi => sq_nonneg (v i))]

private theorem regUniform_finitePressureGradient_reindex
    (velocitySq mollifiedVelocity testGradient : Fin 3 → ℝ) :
    (∑ i : Fin 3, ∑ j : Fin 3,
      mollifiedVelocity j * (velocitySq i * testGradient j)) =
      ∑ i : Fin 3, (∑ j : Fin 3, velocitySq j * mollifiedVelocity i) *
        testGradient i := by
  calc
    _ = ∑ j : Fin 3, ∑ i : Fin 3,
        mollifiedVelocity j * (velocitySq i * testGradient j) := by
      rw [Finset.sum_comm]
    _ = ∑ j : Fin 3, ∑ i : Fin 3,
        velocitySq i * mollifiedVelocity j * testGradient j := by
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = ∑ j : Fin 3, (∑ i : Fin 3, velocitySq i * mollifiedVelocity j) *
        testGradient j := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.sum_mul]
    _ = ∑ i : Fin 3, (∑ j : Fin 3, velocitySq j * mollifiedVelocity i) *
        testGradient i := by rfl

private theorem regUniform_localEnergy_spatialProduct
    (F G : Vec3 × ℝ → ℝ) (z : Vec3 × ℝ) (j : Fin 3)
    (hF : DifferentiableAt ℝ (fun x : Vec3 => F (x, z.2)) z.1)
    (hG : DifferentiableAt ℝ (fun x : Vec3 => G (x, z.2)) z.1) :
    spatialPartial (show ParabolicPoint → ℝ from fun z => F z * G z) j z =
      spatialPartial (show ParabolicPoint → ℝ from F) j z * G z +
        F z * spatialPartial (show ParabolicPoint → ℝ from G) j z := by
  rw [regUniform_spatialPartial_mul z.1 z.2 j hF hG]
  ring

private theorem regUniform_localEnergy_timeProduct
    (F G : Vec3 × ℝ → ℝ) (z : Vec3 × ℝ)
    (hF : DifferentiableAt ℝ (fun t : ℝ => F (z.1, t)) z.2)
    (hG : DifferentiableAt ℝ (fun t : ℝ => G (z.1, t)) z.2) :
    timePartial (show ParabolicPoint → ℝ from fun z => F z * G z) z =
      timePartial (show ParabolicPoint → ℝ from F) z * G z +
        F z * timePartial (show ParabolicPoint → ℝ from G) z := by
  rw [regUniform_timePartial_mul z.1 z.2 hF hG]
  ring

private theorem regUniform_localEnergy_squareSpatial
    (F : Vec3 × ℝ → ℝ) (z : Vec3 × ℝ) (j : Fin 3)
    (hF : DifferentiableAt ℝ (fun x : Vec3 => F (x, z.2)) z.1) :
    spatialPartial (show ParabolicPoint → ℝ from fun z => F z * F z) j z =
      2 * F z * spatialPartial (show ParabolicPoint → ℝ from F) j z := by
  rw [regUniform_localEnergy_spatialProduct F F z j hF hF]
  ring

private theorem regUniform_localEnergy_squareTime
    (F : Vec3 × ℝ → ℝ) (z : Vec3 × ℝ)
    (hF : DifferentiableAt ℝ (fun t : ℝ => F (z.1, t)) z.2) :
    timePartial (show ParabolicPoint → ℝ from fun z => F z * F z) z =
      2 * F z * timePartial (show ParabolicPoint → ℝ from F) z := by
  rw [regUniform_localEnergy_timeProduct F F z hF hF]
  ring

private theorem regUniform_fin3_sum_eq
    (f g : Fin 3 → ℝ) (h : ∀ i, f i = g i) :
    (∑ i : Fin 3, f i) = ∑ i : Fin 3, g i := by
  apply Finset.sum_congr rfl
  intro i hi
  exact h i

private theorem regUniform_fin3_doubleSum_eq
    (f g : Fin 3 → Fin 3 → ℝ) (h : ∀ i j, f i j = g i j) :
    (∑ i : Fin 3, ∑ j : Fin 3, f i j) =
      ∑ i : Fin 3, ∑ j : Fin 3, g i j := by
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  exact h i j

private theorem regUniform_fin3_doubleSum_divergence_mul_zero
    (divergence weight : Fin 3 → ℝ)
    (hdivergence : ∑ j : Fin 3, divergence j = 0) :
    (∑ i : Fin 3, ∑ j : Fin 3, divergence j * weight i) = 0 := by
  calc
    _ = ∑ j : Fin 3, divergence j * ∑ i : Fin 3, weight i := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j hj
      rw [← Finset.mul_sum]
    _ = (∑ j : Fin 3, divergence j) * ∑ i : Fin 3, weight i := by
      rw [Finset.sum_mul]
    _ = 0 := by rw [hdivergence]; simp

private theorem regUniform_fin3_diagonal_mul_zero
    (diagonal : Fin 3 → ℝ) (factor : ℝ)
    (hdiagonal : ∑ i : Fin 3, diagonal i = 0) :
    (∑ i : Fin 3, factor * diagonal i) = 0 := by
  rw [← Finset.mul_sum]
  rw [hdiagonal]
  simp

private theorem regUniform_localEnergy_pointwise_flux_balance
    (u mollified : Vec3 × ℝ → Vec3) (p Φ : Vec3 × ℝ → ℝ) (z : Vec3 × ℝ)
    (hUspace : ∀ i : Fin 3,
      DifferentiableAt ℝ (fun x : Vec3 => u (x, z.2) i) z.1)
    (hUtime : ∀ i : Fin 3,
      DifferentiableAt ℝ (fun t : ℝ => u (z.1, t) i) z.2)
    (hDspace : ∀ i j : Fin 3, DifferentiableAt ℝ
      (fun x : Vec3 => spatialPartial (fun y => u y i) j (x, z.2)) z.1)
    (hPspace : DifferentiableAt ℝ (fun x : Vec3 => p (x, z.2)) z.1)
    (hMspace : ∀ j : Fin 3,
      DifferentiableAt ℝ (fun x : Vec3 => mollified (x, z.2) j) z.1)
    (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ)
    (hMdiv : ∑ j : Fin 3, spatialPartial (fun y => mollified y j) j z = 0)
    (hUdiv : ∑ i : Fin 3, spatialPartial (fun y => u y i) i z = 0) :
    (∑ i : Fin 3, 2 * (u z i * Φ z) *
      (timePartial (fun y => u y i) z -
        (∑ j : Fin 3, spatialPartial
          (fun y => spatialPartial (fun x => u x i) j y) j z) +
        (∑ j : Fin 3, mollified z j * spatialPartial (fun y => u y i) j z) +
        spatialPartial p i z)) =
      ((∑ i : Fin 3, timePartial (fun y => u y i * u y i * Φ y) z) -
        2 * (∑ i : Fin 3, ∑ j : Fin 3,
          spatialPartial (fun y => spatialPartial (fun x => u x i) j y *
            (u y i * Φ y)) j z) +
        (∑ i : Fin 3, ∑ j : Fin 3,
          spatialPartial (fun y => u y i * u y i * spatialPartial Φ j y) j z) +
        (∑ i : Fin 3, ∑ j : Fin 3,
          spatialPartial (fun y => mollified y j * (u y i * u y i * Φ y)) j z) +
        2 * (∑ i : Fin 3, spatialPartial (fun y => p y * (u y i * Φ y)) i z)) +
      (2 * (∑ i : Fin 3, ∑ j : Fin 3,
          spatialPartial (fun y => u y i) j z ^ 2) * Φ z -
        (∑ i : Fin 3, u z i * u z i) *
          (timePartial Φ z + ∑ j : Fin 3, spatialPartial
            (fun y => spatialPartial Φ j y) j z) -
        ∑ i : Fin 3, ((∑ j : Fin 3, u z j * u z j) * mollified z i +
          2 * p z * u z i) * spatialPartial Φ i z) := by
  let Ui (i : Fin 3) : Vec3 × ℝ → ℝ := fun y => u y i
  let J (j : Fin 3) : Vec3 × ℝ → ℝ := fun y => mollified y j
  let D (i j : Fin 3) : Vec3 × ℝ → ℝ := fun y => spatialPartial (Ui i) j y
  let H (i : Fin 3) : Vec3 × ℝ → ℝ := fun y => Ui i y * Ui i y
  let W (i : Fin 3) : Vec3 × ℝ → ℝ := fun y => Ui i y * Φ y
  let V (i : Fin 3) : Vec3 × ℝ → ℝ := fun y => H i y * Φ y
  have hΦspace : DifferentiableAt ℝ (fun x : Vec3 => Φ (x, z.2)) z.1 :=
    regUniform_contDiffOn_spatialSlice_differentiableAt isOpen_univ
      (hΦ.of_le (by norm_num)).contDiffOn (Set.mem_univ z)
  have hΦtime : DifferentiableAt ℝ (fun t : ℝ => Φ (z.1, t)) z.2 :=
    regUniform_contDiffOn_timeSlice_differentiableAt isOpen_univ
      (hΦ.of_le (by norm_num)).contDiffOn (Set.mem_univ z)
  have hΦgradient (j : Fin 3) : DifferentiableAt ℝ
      (fun x : Vec3 => spatialPartial Φ j (x, z.2)) z.1 :=
    regUniform_contDiffOn_spatialSlice_differentiableAt isOpen_univ
      ((spatialPartial_contDiff hΦ j).of_le (by norm_num)).contDiffOn (Set.mem_univ z)
  have hHspace (i j : Fin 3) : spatialPartial (H i) j z = 2 * Ui i z * D i j z :=
    regUniform_localEnergy_squareSpatial (Ui i) z j (hUspace i)
  have hHtime (i : Fin 3) : timePartial (H i) z =
      2 * Ui i z * timePartial (Ui i) z :=
    regUniform_localEnergy_squareTime (Ui i) z (hUtime i)
  have hWspace (i j : Fin 3) : spatialPartial (W i) j z =
      Ui i z * spatialPartial Φ j z + Φ z * D i j z := by
    change spatialPartial (show ParabolicPoint → ℝ from fun y => Ui i y * Φ y) j z = _
    rw [regUniform_localEnergy_spatialProduct (Ui i) Φ z j (hUspace i) hΦspace]
    ring
  have hVspace (i j : Fin 3) : spatialPartial (V i) j z =
      2 * Ui i z * D i j z * Φ z + H i z * spatialPartial Φ j z := by
    change spatialPartial (show ParabolicPoint → ℝ from fun y => H i y * Φ y) j z = _
    rw [regUniform_localEnergy_spatialProduct (H i) Φ z j
      ((hUspace i).mul (hUspace i)) hΦspace, hHspace i j]
  have hTime (i : Fin 3) : timePartial (V i) z =
      2 * Ui i z * timePartial (Ui i) z * Φ z + H i z * timePartial Φ z := by
    change timePartial (show ParabolicPoint → ℝ from fun y => H i y * Φ y) z = _
    rw [regUniform_localEnergy_timeProduct (H i) Φ z
      ((hUtime i).mul (hUtime i)) hΦtime, hHtime i]
  have hDiff (i j : Fin 3) : spatialPartial (fun y => D i j y * W i y) j z =
      spatialPartial (D i j) j z * W i z +
        D i j z * (Ui i z * spatialPartial Φ j z + Φ z * D i j z) := by
    rw [regUniform_localEnergy_spatialProduct (D i j) (W i) z j
      (hDspace i j) ((hUspace i).mul hΦspace), hWspace i j]
  have hTest (i j : Fin 3) :
      spatialPartial (fun y => H i y * spatialPartial Φ j y) j z =
      2 * Ui i z * D i j z * spatialPartial Φ j z +
        H i z * spatialPartial (fun y => spatialPartial Φ j y) j z := by
    rw [regUniform_localEnergy_spatialProduct (H i)
      (fun y => spatialPartial Φ j y) z j
      ((hUspace i).mul (hUspace i)) (hΦgradient j), hHspace i j]
    rfl
  have hConv (i j : Fin 3) : spatialPartial (fun y => J j y * V i y) j z =
      spatialPartial (J j) j z * V i z +
        J j z * (2 * Ui i z * D i j z * Φ z + H i z * spatialPartial Φ j z) := by
    rw [regUniform_localEnergy_spatialProduct (J j) (V i) z j
      (hMspace j) (((hUspace i).mul (hUspace i)).mul hΦspace), hVspace i j]
  have hPressure (i : Fin 3) : spatialPartial (fun y => p y * W i y) i z =
      spatialPartial p i z * W i z +
        p z * (Ui i z * spatialPartial Φ i z + Φ z * D i i z) := by
    rw [regUniform_localEnergy_spatialProduct p (W i) z i
      hPspace ((hUspace i).mul hΦspace), hWspace i i]
  change (∑ i : Fin 3, 2 * W i z *
    (timePartial (Ui i) z - ∑ j : Fin 3, spatialPartial (D i j) j z +
      ∑ j : Fin 3, J j z * D i j z + spatialPartial p i z)) =
    ((∑ i : Fin 3, timePartial (V i) z) -
      2 * (∑ i : Fin 3, ∑ j : Fin 3,
        spatialPartial (fun y => D i j y * W i y) j z) +
      (∑ i : Fin 3, ∑ j : Fin 3,
        spatialPartial (fun y => H i y * spatialPartial Φ j y) j z) +
      (∑ i : Fin 3, ∑ j : Fin 3,
        spatialPartial (fun y => J j y * V i y) j z) +
      2 * (∑ i : Fin 3, spatialPartial (fun y => p y * W i y) i z)) + _
  simp_rw [hTime, hDiff, hTest, hConv, hPressure]
  simp only [Ui, J, D, H, W, V]
  simp only [Fin.sum_univ_three] at hMdiv hUdiv ⊢
  simp only [spatialPartial, timePartial] at hMdiv hUdiv ⊢
  linear_combination
    -((u z 0 * u z 0 + u z 1 * u z 1 + u z 2 * u z 2) * Φ z) * hMdiv -
      (2 * p z * Φ z) * hUdiv

private theorem regUniform_localEnergy_heatTest_integrable
    {S : Set (Vec3 × ℝ)} {coefficient ψ : Vec3 × ℝ → ℝ}
    (hS : IsOpen S) (hcoefficient : ContinuousOn coefficient S)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hcompact : HasCompactSupport ψ)
    (hsupport : tsupport ψ ⊆ S) :
    Integrable (fun z : Vec3 × ℝ => coefficient z *
      (timePartial ψ z + ∑ i : Fin 3, spatialSecondPartial ψ i i z)) volume := by
  let heat : Vec3 × ℝ → ℝ := fun z =>
    timePartial ψ z + ∑ i : Fin 3, spatialSecondPartial ψ i i z
  have hcontinuous : ContinuousOn heat S :=
    (CKN.Core.Step3.timePartial_contDiff_full hψ).continuous.continuousOn.add
      (continuousOn_finsetSum Finset.univ fun i hi =>
        (CKN.Core.Step3.spatialSecondPartial_contDiff_full hψ i i).continuous.continuousOn)
  have hheatSupport : tsupport heat ⊆ tsupport ψ := by
    refine closure_minimal ?_ (isClosed_tsupport ψ)
    intro z hz
    by_contra hnot
    apply hz
    change timePartial ψ z + ∑ i : Fin 3, spatialSecondPartial ψ i i z = 0
    rw [timePartial_eq_zero_off_tsupport hnot]
    simp [spatialSecondPartial_eq_zero_off_tsupport hnot]
  exact regUniform_integrable_mul_of_tsupport_subset hS hcoefficient hcontinuous
    (hcompact.isCompact.of_isClosed_subset (isClosed_tsupport _) hheatSupport)
    (hheatSupport.trans hsupport)

private theorem regUniform_localEnergy_gradientTest_integrable
    {S : Set (Vec3 × ℝ)} {D : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ}
    {ψ : Vec3 × ℝ → ℝ} (hS : IsOpen S)
    (hD : ∀ i j, ContinuousOn (D i j) S) (hψ : ContinuousOn ψ S)
    (hcompact : HasCompactSupport ψ) (hsupport : tsupport ψ ⊆ S) :
    Integrable (fun z => (∑ i : Fin 3, ∑ j : Fin 3, D i j z ^ 2) * ψ z)
      (volume.restrict S) := by
  exact (regUniform_integrable_mul_of_tsupport_subset hS
    (continuousOn_finsetSum Finset.univ fun i hi =>
      continuousOn_finsetSum Finset.univ fun j hj => (hD i j).pow 2)
    hψ hcompact hsupport).mono_measure Measure.restrict_le_self

private theorem regUniform_localEnergy_transportTest_integrable
    {S : Set (Vec3 × ℝ)} {energy pressure ψ : Vec3 × ℝ → ℝ}
    {velocity mollified : Fin 3 → Vec3 × ℝ → ℝ}
    (hS : IsOpen S) (henergy : ContinuousOn energy S)
    (hpressure : ContinuousOn pressure S)
    (hvelocity : ∀ i, ContinuousOn (velocity i) S)
    (hmollified : ∀ i, ContinuousOn (mollified i) S)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hcompact : HasCompactSupport ψ)
    (hsupport : tsupport ψ ⊆ S) :
    Integrable (fun z : Vec3 × ℝ => ∑ i : Fin 3,
      (energy z * mollified i z + 2 * pressure z * velocity i z) *
        spatialPartial ψ i z) (volume.restrict S) := by
  apply integrable_finsetSum Finset.univ
  intro i hi
  exact (regUniform_integrable_mul_of_tsupport_subset hS
    ((henergy.mul (hmollified i)).add
      ((continuousOn_const.mul hpressure).mul (hvelocity i)))
    (spatialPartial_contDiff hψ i).continuous.continuousOn
    (CKN.hasCompactSupport_spatialPartial hcompact i)
    ((CKN.tsupport_spatialPartial_subset i).trans hsupport)).mono_measure
      Measure.restrict_le_self

private theorem regUniform_localEnergy_normSq_continuousOn
    {S : Set (Vec3 × ℝ)} {u : Vec3 × ℝ → Vec3}
    (hU : ∀ i : Fin 3, ContinuousOn (fun z => u z i) S) :
    ContinuousOn (fun z => vec3EuclideanNorm (u z) ^ (2 : ℕ)) S := by
  apply ContinuousOn.congr (continuousOn_finsetSum Finset.univ
    fun i hi => (hU i).pow 2)
  intro z hz
  exact regUniform_vec3EuclideanNorm_sq (u z)

private theorem regUniform_localEnergy_mollifiedSlice_differentiableAt
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (u : ParabolicPoint → Vec3) {z : Vec3 × ℝ}
    (hdiv : CKN.IsWeakDivFreeL2 (fun x : Vec3 => u (x, z.2))) (i : Fin 3) :
    DifferentiableAt ℝ
      (fun x : Vec3 => regUniformMollifiedVelocity ρ ε hε u (x, z.2) i) z.1 := by
  have hsmooth := regUniformMollifiedInitial_contDiff ρ ε hε
    (CKN.weakDivFreeL2_isInJ hdiv)
  have hcoord := hsmooth.continuousLinearMap_comp
    (ContinuousLinearMap.proj (R := ℝ) i)
  exact hcoord.differentiable (by norm_num) z.1

private theorem regUniform_localEnergy_velocity_divergence_zero
    (u : ParabolicPoint → Vec3) {z : Vec3 × ℝ}
    (hU : ∀ i : Fin 3, ContDiffOn ℝ 1 (fun y => u y i)
      (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0)))
    (hz : 0 < z.2)
    (hdiv : CKN.IsWeakDivFreeL2 (fun x : Vec3 => u (x, z.2))) :
    ∑ i : Fin 3, spatialPartial (fun y => u y i) i z = 0 := by
  have hC1 : ∀ i : Fin 3, ContDiff ℝ 1 (fun x : Vec3 => u (x, z.2) i) := by
    intro i
    apply contDiffOn_univ.mp
    exact (hU i).comp (by fun_prop) (by
      intro x hx
      exact ⟨Set.mem_univ _, hz⟩)
  have hzero := regUniform_weakDivFree_contDiff_divergence_eq_zero hC1 hdiv z.1
  simpa [spatialPartial] using hzero

private theorem regUniform_localEnergy_integral_balance
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {G R F : α → ℝ}
    (hG : Integrable G μ) (hR : Integrable R μ)
    (hbalance : ∀ᵐ z ∂μ, 2 * G z - R z = -F z)
    (hflux : (∫ z, F z ∂μ) = 0) :
    2 * (∫ z, G z ∂μ) = ∫ z, R z ∂μ := by
  have hzero : (∫ z, 2 * G z - R z ∂μ) = 0 := by
    rw [integral_congr_ae hbalance, integral_neg, hflux, neg_zero]
  rw [integral_sub (hG.const_mul 2) hR, integral_const_mul] at hzero
  exact sub_eq_zero.mp hzero

/-- The pointwise regularized equation (R3) gives the local energy identity
in `lem:reg-local-energy`. -/
theorem regUniform_local_energy_identity
    (ρ : RegMollifierProfile) (ε : ℝ) (hε : 0 < ε)
    (u : ParabolicPoint → Vec3) (p : ParabolicPoint → ℝ)
    (hSliceL2 : ∀ t : ℝ, 0 ≤ t →
      MemLp (fun x : Vec3 => u (x, t)) 2 volume)
    (hWeakDivFree : ∀ t : ℝ, 0 ≤ t →
      CKN.IsWeakDivFreeL2 (fun x : Vec3 => u (x, t)))
    (hUcont : letI : TopologicalSpace ParabolicPoint := regUniformParabolicTopologyLocalEnergy
      ∀ i : Fin 3, ContinuousOn (fun z => u z i)
        (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0)))
    (hDcont : letI : TopologicalSpace ParabolicPoint := regUniformParabolicTopologyLocalEnergy
      ∀ i j : Fin 3, ContinuousOn
        (fun z => spatialPartial (fun y => u y i) j z)
        (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0)))
    (hDDcont : letI : TopologicalSpace ParabolicPoint := regUniformParabolicTopologyLocalEnergy
      ∀ i j k : Fin 3, ContinuousOn
        (fun z => spatialPartial
          (fun y => spatialPartial (fun x => u x i) j y) k z)
        (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0)))
    (hDtcont : letI : TopologicalSpace ParabolicPoint := regUniformParabolicTopologyLocalEnergy
      ∀ i : Fin 3, ContinuousOn
        (fun z => timePartial (fun y => u y i) z)
        (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0)))
    (hPcont : letI : TopologicalSpace ParabolicPoint := regUniformParabolicTopologyLocalEnergy
      ContinuousOn p (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0)))
    (hDpcont : letI : TopologicalSpace ParabolicPoint := regUniformParabolicTopologyLocalEnergy
      ∀ i : Fin 3, ContinuousOn
        (fun z => spatialPartial (fun y => p y) i z)
        (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0)))
    (hUcontDiff : letI : TopologicalSpace ParabolicPoint := instTopologicalSpaceProd
      letI : NormedAddCommGroup ParabolicPoint :=
        inferInstanceAs (NormedAddCommGroup (Vec3 × ℝ))
      letI : NormedSpace ℝ ParabolicPoint :=
        inferInstanceAs (NormedSpace ℝ (Vec3 × ℝ))
      ∀ i : Fin 3, ContDiffOn ℝ 1 (fun z => u z i)
        (spaceTimeSet (Set.univ : Set Vec3) (Ioi 0)))
    (hDdiff : ∀ z ∈ spaceTimeSet (Set.univ : Set Vec3) (Ioi 0),
      ∀ i j : Fin 3,
        DifferentiableAt ℝ (fun x : Vec3 =>
          spatialPartial (fun y => u y i) j (x, z.2)) z.1)
    (hPdiff : ∀ z ∈ spaceTimeSet (Set.univ : Set Vec3) (Ioi 0),
      DifferentiableAt ℝ (fun x : Vec3 => p (x, z.2)) z.1)
    (hEquation : ∀ z : ParabolicPoint, 0 < z.2 → ∀ i : Fin 3,
      timePartial (fun y => u y i) z -
        (∑ j : Fin 3, spatialPartial
          (fun y => spatialPartial (fun x => u x i) j y) j z) +
        (∑ j : Fin 3, regUniformMollifiedVelocity ρ ε hε u z j *
          spatialPartial (fun y => u y i) j z) +
        spatialPartial (fun y => p y) i z = 0)
    (ψ : ParabolicPoint → ℝ)
    (hψ : ψ ∈ spaceTimeTestFunction (V := ℝ)
      (Set.univ : Set Vec3) (Ioi 0)) :
    2 * ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioi 0),
        spatialGradientSq u
          (fun z i j => spatialPartial (fun y => u y i) j z) z * ψ z =
      ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioi 0),
        (vec3EuclideanNorm (u z)) ^ (2 : ℕ) *
            (timePartial ψ z + ∑ i : Fin 3, spatialSecondPartial ψ i i z) +
          ∑ i : Fin 3,
            ((vec3EuclideanNorm (u z)) ^ (2 : ℕ) *
                regUniformMollifiedVelocity ρ ε hε u z i +
              2 * p z * u z i) * spatialPartial ψ i z := by
  let S : Set (Vec3 × ℝ) := (Set.univ : Set Vec3) ×ˢ Ioi (0 : ℝ)
  let Smetric : Set ParabolicPoint := spaceTimeSet (Set.univ : Set Vec3) (Ioi (0 : ℝ))
  have hSopen : IsOpen S := isOpen_univ.prod isOpen_Ioi
  have hSmeas : MeasurableSet S := MeasurableSet.prod MeasurableSet.univ measurableSet_Ioi
  have hSsymm : ∀ z ∈ S, ((z.1, z.2) : ParabolicPoint) ∈ Smetric := by
    intro z hz
    exact ⟨Set.mem_univ _, hz.2⟩
  let Ui (i : Fin 3) : Vec3 × ℝ → ℝ := fun z => u z i
  let D (i j : Fin 3) : Vec3 × ℝ → ℝ :=
    fun z => spatialPartial (fun y => u y i) j z
  let J (i : Fin 3) : Vec3 × ℝ → ℝ :=
    fun z => regUniformMollifiedVelocity ρ ε hε u z i
  let Phi : Vec3 × ℝ → ℝ := fun z => ψ z
  let H (i : Fin 3) : Vec3 × ℝ → ℝ := fun z => Ui i z * Ui i z
  let W (i : Fin 3) : Vec3 × ℝ → ℝ := fun z => Ui i z * Phi z
  let V (i : Fin 3) : Vec3 × ℝ → ℝ := fun z => H i z * Phi z
  let GradTest (j : Fin 3) : Vec3 × ℝ → ℝ := fun z => spatialPartial Phi j z
  let TimeFlux (i : Fin 3) : Vec3 × ℝ → ℝ := fun z => V i z
  let DiffFlux (i j : Fin 3) : Vec3 × ℝ → ℝ := fun z => D i j z * W i z
  let TestGradientFlux (i j : Fin 3) : Vec3 × ℝ → ℝ := fun z => H i z * GradTest j z
  let ConvFlux (i j : Fin 3) : Vec3 × ℝ → ℝ := fun z => J j z * V i z
  let PressureFlux (i : Fin 3) : Vec3 × ℝ → ℝ := fun z => p z * W i z
  let HeatTest : Vec3 × ℝ → ℝ := fun z => CKN.timePartialProd Phi z +
    ∑ i : Fin 3, CKN.spatialPartialProd (GradTest i) i z
  let GradientEnergy : Vec3 × ℝ → ℝ := fun z => regUniformSpatialGradientDensity u
    (fun z i j => spatialPartial (fun y => u y i) j z) z * Phi z
  let RightEnergy : Vec3 × ℝ → ℝ := fun z =>
    vec3EuclideanNorm (u (z.1, z.2)) ^ (2 : ℕ) * HeatTest z + ∑ i : Fin 3,
      (vec3EuclideanNorm (u (z.1, z.2)) ^ (2 : ℕ) * J i z +
        2 * p z * Ui i z) * GradTest i z
  let FluxResidual : Vec3 × ℝ → ℝ := fun z =>
    (∑ i : Fin 3, CKN.timePartialProd (TimeFlux i) z) -
      2 * ∑ i : Fin 3, ∑ j : Fin 3, CKN.spatialPartialProd (DiffFlux i j) j z +
      ∑ i : Fin 3, ∑ j : Fin 3, CKN.spatialPartialProd (TestGradientFlux i j) j z +
      ∑ i : Fin 3, ∑ j : Fin 3, CKN.spatialPartialProd (ConvFlux i j) j z +
      2 * ∑ i : Fin 3, CKN.spatialPartialProd (PressureFlux i) i z
  have hU (i : Fin 3) : ContinuousOn (Ui i) S := by
    simpa [Ui] using regUniform_continuousOn_pullback (hUcont i) hSsymm
  have hD (i j : Fin 3) : ContinuousOn (D i j) S := by
    simpa [D] using regUniform_continuousOn_pullback (hDcont i j) hSsymm
  have hP : ContinuousOn (fun z : Vec3 × ℝ => p z) S :=
    regUniform_continuousOn_pullback hPcont hSsymm
  have hJcontMetric := regUniform_mollified_velocity_continuousOn
    ρ ε hε (S := S) (fun t ht => hSliceL2 t (le_of_lt ht))
    hUcontDiff (fun z hz => hz.2) (fun z hz y => ⟨Set.mem_univ _, hz.2⟩)
  have hJ (i : Fin 3) : ContinuousOn (J i) S := by simpa [J] using hJcontMetric i
  have hNormSqCont : ContinuousOn
      (fun z : Vec3 × ℝ => vec3EuclideanNorm (u (z.1, z.2)) ^ (2 : ℕ)) S :=
    regUniform_localEnergy_normSq_continuousOn hU
  have hBaseInt : Integrable GradientEnergy (volume.restrict S) := by
    change Integrable (fun z => (∑ i : Fin 3, ∑ j : Fin 3, D i j z ^ 2) * Phi z)
      (volume.restrict S)
    exact regUniform_localEnergy_gradientTest_integrable (D := D) (ψ := Phi) hSopen hD
      hψ.1.continuous.continuousOn hψ.2.1 hψ.2.2
  have hHeatInt : Integrable (fun z : Vec3 × ℝ =>
      vec3EuclideanNorm (u (z.1, z.2)) ^ (2 : ℕ) * HeatTest z) volume :=
    regUniform_localEnergy_heatTest_integrable (ψ := Phi) hSopen hNormSqCont
      hψ.1 hψ.2.1 hψ.2.2
  have hTransportInt : Integrable (fun z : Vec3 × ℝ => ∑ i : Fin 3,
      (vec3EuclideanNorm (u (z.1, z.2)) ^ (2 : ℕ) * J i z +
        2 * p z * Ui i z) * GradTest i z) (volume.restrict S) :=
    regUniform_localEnergy_transportTest_integrable (ψ := Phi)
      (velocity := Ui) (mollified := J) hSopen hNormSqCont hP hU hJ hψ.1 hψ.2.1 hψ.2.2
  have hRightInt : Integrable RightEnergy (volume.restrict S) :=
    (hHeatInt.mono_measure Measure.restrict_le_self).add hTransportInt
  have hFluxZero : (∫ z in S, FluxResidual z ∂volume) = 0 := by
    simpa [S] using (regUniform_local_energy_flux_integral_zero ρ ε hε u p
      hSliceL2 hWeakDivFree hUcont hDcont hDDcont hDtcont hPcont hDpcont
      hUcontDiff hDdiff hPdiff ψ hψ)
  have hResidualPoint (z : Vec3 × ℝ) (hz : z ∈ S) :
      2 * GradientEnergy z - RightEnergy z = -FluxResidual z := by
    have hbalance := regUniform_localEnergy_pointwise_flux_balance
      (fun y => u y) (fun y => regUniformMollifiedVelocity ρ ε hε u y) p Phi z
      (fun i => regUniform_contDiffOn_spatialSlice_differentiableAt hSopen (hUcontDiff i) hz)
      (fun i => regUniform_contDiffOn_timeSlice_differentiableAt hSopen (hUcontDiff i) hz)
      (hDdiff z hz) (hPdiff z hz)
      (regUniform_localEnergy_mollifiedSlice_differentiableAt ρ ε hε u
        (hWeakDivFree z.2 (le_of_lt hz.2))) hψ.1
      (regUniform_mollified_velocity_divergence_eq_zero ρ ε hε u z.2
        (hWeakDivFree z.2 (le_of_lt hz.2)) z.1)
      (regUniform_localEnergy_velocity_divergence_zero u hUcontDiff hz.2
        (hWeakDivFree z.2 (le_of_lt hz.2)))
    have hWeightedZero : (∑ i : Fin 3, 2 * (u z i * Phi z) *
        (timePartial (fun y => u y i) z -
          (∑ j : Fin 3, spatialPartial
            (fun y => spatialPartial (fun x => u x i) j y) j z) +
          (∑ j : Fin 3, regUniformMollifiedVelocity ρ ε hε u z j *
            spatialPartial (fun y => u y i) j z) + spatialPartial p i z)) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      rw [hEquation z hz.2 i]
      ring
    rw [hWeightedZero] at hbalance
    have hNormSqFormula : vec3EuclideanNorm (u (z.1, z.2)) ^ (2 : ℕ) =
        ∑ i : Fin 3, u z i * u z i := by
      simpa only [pow_two] using regUniform_vec3EuclideanNorm_sq (u (z.1, z.2))
    change 2 * (regUniformSpatialGradientDensity u
      (fun z i j => spatialPartial (fun y => u y i) j z) z * Phi z) -
      (vec3EuclideanNorm (u (z.1, z.2)) ^ (2 : ℕ) * HeatTest z + ∑ i : Fin 3,
        (vec3EuclideanNorm (u (z.1, z.2)) ^ (2 : ℕ) * J i z +
          2 * p z * Ui i z) * GradTest i z) = -FluxResidual z
    simp only [regUniformSpatialGradientDensity, spatialGradientSq, hNormSqFormula,
      HeatTest, FluxResidual, Ui, D, J, H, W, V, GradTest, TimeFlux, DiffFlux,
      TestGradientFlux, ConvFlux, PressureFlux]
    simp only [CKN.timePartialProd, CKN.spatialPartialProd, timePartial, spatialPartial]
      at hbalance ⊢
    linarith only [hbalance]
  exact regUniform_localEnergy_integral_balance hBaseInt hRightInt
    (by
      filter_upwards [ae_restrict_mem hSmeas] with z hz
      exact hResidualPoint z hz) hFluxZero

end CKN.Leray

end
