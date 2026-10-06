/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegTailsLocalized
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Time identities for localized regularized energy

Compactly supported spatial weights reduce the local energy identity to a
scalar weak time identity, as used in `lem:reg-tails`.
-/

public section

open MeasureTheory Filter Set
open scoped ENNReal Topology
open CKN CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Leray

local instance regTailsTimeIdentityNormedAddCommGroup : NormedAddCommGroup ParabolicPoint :=
  inferInstanceAs (NormedAddCommGroup (Vec3 × ℝ))

local instance regTailsTimeIdentityNormedSpace : NormedSpace ℝ ParabolicPoint :=
  inferInstanceAs (NormedSpace ℝ (Vec3 × ℝ))

private theorem regTails_continuous_mul_timeFactor
    {A : Vec3 × ℝ → ℝ} {η : ℝ → ℝ}
    (hS : IsOpen ((Set.univ : Set Vec3) ×ˢ Ioi (0 : ℝ)))
    (hA : ContinuousOn A ((Set.univ : Set Vec3) ×ˢ Ioi (0 : ℝ)))
    (hη : Continuous η) (hηI : tsupport η ⊆ Ioi (0 : ℝ)) :
    Continuous (fun z : Vec3 × ℝ => A z * η z.2) := by
  rw [continuous_iff_continuousAt]
  intro z
  by_cases hz : z ∈ (Set.univ : Set Vec3) ×ˢ Ioi (0 : ℝ)
  · exact (hA z hz).continuousAt (hS.mem_nhds hz) |>.mul
      (hη.continuousAt.comp continuousAt_snd)
  · have htnot : z.2 ∉ tsupport η := by
      intro ht
      exact hz ⟨Set.mem_univ _, hηI ht⟩
    have hηzero : ∀ᶠ t : ℝ in 𝓝 z.2, η t = 0 := by
      rw [notMem_tsupport_iff_eventuallyEq] at htnot
      exact htnot
    have hprodzero : ∀ᶠ z' : Vec3 × ℝ in 𝓝 z, A z' * η z'.2 = 0 := by
      filter_upwards [continuousAt_snd.eventually hηzero] with z' hz'
      simp [hz']
    exact continuousAt_const.congr_of_eventuallyEq hprodzero

private theorem regTails_vec3EuclideanNorm_sq (v : Vec3) :
    vec3EuclideanNorm v ^ (2 : ℕ) = ∑ i : Fin 3, (v i) ^ (2 : ℕ) := by
  rw [vec3EuclideanNorm, Real.sq_sqrt]
  exact Finset.sum_nonneg fun i hi => sq_nonneg (v i)

/-- Spatial compact support and a compact positive-time factor give
integrability on the positive space-time product. -/
theorem regTails_integrable_timeFactor_of_spatial_support
    (A : Vec3 × ℝ → ℝ) (K : Set Vec3)
    (hS : IsOpen ((Set.univ : Set Vec3) ×ˢ Ioi (0 : ℝ)))
    (hA : ContinuousOn A ((Set.univ : Set Vec3) ×ˢ Ioi (0 : ℝ)))
    (hK : IsCompact K)
    (hAzero : ∀ z : Vec3 × ℝ, 0 < z.2 → z.1 ∉ K → A z = 0)
    (η : ℝ → ℝ) (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hηc : HasCompactSupport η)
    (hηI : tsupport η ⊆ Ioi (0 : ℝ)) :
    Integrable (fun z : Vec3 × ℝ => A z * η z.2)
      ((volume : Measure Vec3).prod (volume.restrict (Ioi (0 : ℝ)))) := by
  let G : Vec3 × ℝ → ℝ := fun z => A z * η z.2
  have hGcont : Continuous G := regTails_continuous_mul_timeFactor
    hS hA hη.continuous hηI
  have hGsupport : Function.support G ⊆ K ×ˢ tsupport η := by
    intro z hz
    have hzG : G z ≠ 0 := Function.mem_support.mp hz
    constructor
    · by_contra hx
      by_cases ht : 0 < z.2
      · exact hzG (by simp [G, hAzero z ht hx])
      · have hηz : η z.2 = 0 := by
          by_contra hne
          exact ht (hηI (subset_tsupport η (Function.mem_support.mpr hne)))
        exact hzG (by simp [G, hηz])
    · by_contra ht
      have hηz : η z.2 = 0 := by
        by_contra hne
        exact ht (subset_tsupport η (Function.mem_support.mpr hne))
      exact hzG (by simp [G, hηz])
  have hProductCompact : IsCompact (K ×ˢ tsupport η) :=
    hK.prod hηc.isCompact
  have hClosed : IsClosed (K ×ˢ tsupport η) := hProductCompact.isClosed
  have hGtsupport : tsupport G ⊆ K ×ˢ tsupport η :=
    closure_minimal hGsupport hClosed
  have hGc : HasCompactSupport G :=
    hProductCompact.of_isClosed_subset (isClosed_tsupport (f := G)) hGtsupport
  have hFull : Integrable G (volume : Measure (Vec3 × ℝ)) :=
    hGcont.integrable_of_hasCompactSupport hGc
  have hRestricted : Integrable G
      ((volume : Measure (Vec3 × ℝ)).restrict
        ((Set.univ : Set Vec3) ×ˢ Ioi (0 : ℝ))) :=
    hFull.mono_measure Measure.restrict_le_self
  have hMeasure :
      (volume : Measure (Vec3 × ℝ)).restrict
          ((Set.univ : Set Vec3) ×ˢ Ioi (0 : ℝ)) =
        (volume : Measure Vec3).prod (volume.restrict (Ioi (0 : ℝ))) := by
    change ((volume : Measure Vec3).prod (volume : Measure ℝ)).restrict
        ((Set.univ : Set Vec3) ×ˢ Ioi (0 : ℝ)) = _
    rw [← Measure.prod_restrict (μ := (volume : Measure Vec3))
      (ν := (volume : Measure ℝ)) Set.univ (Ioi (0 : ℝ))]
    simp [Measure.restrict_univ]
  rw [← hMeasure]
  simpa [G] using hRestricted

/-- The local energy identity tested against a product of compact spatial and
positive time weights separates into the localized energy term and its
time-independent spatial flux coefficients. -/
theorem regTails_localEnergy_product_test
    (u : ParabolicPoint → Vec3) (p : ParabolicPoint → ℝ)
    (J : ParabolicPoint → Vec3)
    (hLE : ∀ (ψ : ParabolicPoint → ℝ),
      ψ ∈ spaceTimeTestFunction (V := ℝ) (Set.univ : Set Vec3) (Ioi 0) →
      2 * ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioi 0),
          spatialGradientSq u
            (fun z i j => spatialPartial (fun y => u y i) j z) z * ψ z =
        ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioi 0),
          (vec3EuclideanNorm (u z)) ^ (2 : ℕ) *
              (timePartial ψ z + ∑ i : Fin 3, spatialSecondPartial ψ i i z) +
            ∑ i : Fin 3,
              ((vec3EuclideanNorm (u z)) ^ (2 : ℕ) * J z i +
                2 * p z * u z i) * spatialPartial ψ i z)
    (q : Vec3 → ℝ) (hq : ContDiff ℝ (⊤ : ℕ∞) q)
    (hqc : HasCompactSupport q)
    (η : ℝ → ℝ) (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hηc : HasCompactSupport η)
    (hηI : tsupport η ⊆ Ioi (0 : ℝ)) :
    let qST : ParabolicPoint → ℝ := fun z => q z.1
    let A : ParabolicPoint → ℝ := fun z =>
      (vec3EuclideanNorm (u z)) ^ (2 : ℕ) * q z.1
    let L : ParabolicPoint → ℝ := fun z =>
      (vec3EuclideanNorm (u z)) ^ (2 : ℕ) *
        (∑ i : Fin 3, spatialSecondPartial qST i i z)
    let V : ParabolicPoint → ℝ := fun z =>
      ∑ i : Fin 3,
        ((vec3EuclideanNorm (u z)) ^ (2 : ℕ) * J z i +
          2 * p z * u z i) * spatialPartial qST i z
    2 * ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioi 0),
        spatialGradientSq u
          (fun z i j => spatialPartial (fun y => u y i) j z) z *
          q z.1 * η z.2 =
      ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioi 0),
        A z * deriv η z.2 + (L z + V z) * η z.2 := by
  classical
  let S : Set ParabolicPoint := spaceTimeSet (Set.univ : Set Vec3) (Ioi (0 : ℝ))
  let qST : ParabolicPoint → ℝ := fun z => q z.1
  let ψ : ParabolicPoint → ℝ := fun z => q z.1 * η z.2
  let D : ParabolicPoint → Fin 3 → Vec3 := fun z i j =>
    spatialPartial (fun y => u y i) j z
  let A : ParabolicPoint → ℝ := fun z =>
    (vec3EuclideanNorm (u z)) ^ (2 : ℕ) * q z.1
  let L : ParabolicPoint → ℝ := fun z =>
    (vec3EuclideanNorm (u z)) ^ (2 : ℕ) *
      (∑ i : Fin 3, spatialSecondPartial qST i i z)
  let V : ParabolicPoint → ℝ := fun z =>
    ∑ i : Fin 3,
      ((vec3EuclideanNorm (u z)) ^ (2 : ℕ) * J z i +
        2 * p z * u z i) * spatialPartial qST i z
  have htest : ψ ∈ spaceTimeTestFunction (V := ℝ)
      (Set.univ : Set Vec3) (Ioi (0 : ℝ)) := by
    exact regTails_scalarTimeProduct_test q hq hqc η hη hηc hηI
  have hSmeasP : MeasurableSet (S : Set ParabolicPoint) := by
    change MeasurableSet ((Set.univ : Set Vec3) ×ˢ Ioi (0 : ℝ))
    exact MeasurableSet.prod MeasurableSet.univ measurableSet_Ioi
  have hqST : ContDiff ℝ (⊤ : ℕ∞) qST := by
    exact hq.comp (ContinuousLinearMap.fst ℝ Vec3 ℝ).contDiff
  have htime (z : ParabolicPoint) : timePartial ψ z =
      q z.1 * deriv η z.2 := by
    have h := timePartial_mul_time hqST hη z
    have hqtime : timePartial qST z = 0 := by
      simp [timePartial, qST]
    rw [h, hqtime]
    simp only [zero_mul, zero_add]
    rfl
  have hspace (i : Fin 3) (z : ParabolicPoint) :
      spatialPartial ψ i z = spatialPartial qST i z * η z.2 := by
    simpa [ψ, qST] using spatialPartial_mul_time hqST i z
  have hsecond (i : Fin 3) (z : ParabolicPoint) :
      spatialSecondPartial ψ i i z =
        spatialSecondPartial qST i i z * η z.2 := by
    simpa [ψ, qST] using spatialSecondPartial_mul_time hqST i i z
  have hlocal := hLE ψ htest
  change 2 * ∫ z in S, spatialGradientSq u D z * ψ z =
    ∫ z in S,
      (vec3EuclideanNorm (u z)) ^ (2 : ℕ) *
          (timePartial ψ z + ∑ i : Fin 3, spatialSecondPartial ψ i i z) +
        ∑ i : Fin 3,
          ((vec3EuclideanNorm (u z)) ^ (2 : ℕ) * J z i +
            2 * p z * u z i) * spatialPartial ψ i z at hlocal
  have hLeft : ∫ z in S, spatialGradientSq u D z * ψ z =
      ∫ z in S, spatialGradientSq u D z * q z.1 * η z.2 := by
    apply setIntegral_congr_fun hSmeasP
    intro z hz
    dsimp [ψ]
    ring
  have hRight : ∫ z in S,
      (vec3EuclideanNorm (u z)) ^ (2 : ℕ) *
          (timePartial ψ z + ∑ i : Fin 3, spatialSecondPartial ψ i i z) +
        ∑ i : Fin 3,
          ((vec3EuclideanNorm (u z)) ^ (2 : ℕ) * J z i +
            2 * p z * u z i) * spatialPartial ψ i z =
      ∫ z in S, A z * deriv η z.2 + (L z + V z) * η z.2 := by
    apply setIntegral_congr_fun hSmeasP
    intro z hz
    change (vec3EuclideanNorm (u z)) ^ (2 : ℕ) *
          (timePartial ψ z + ∑ i : Fin 3, spatialSecondPartial ψ i i z) +
        ∑ i : Fin 3,
          ((vec3EuclideanNorm (u z)) ^ (2 : ℕ) * J z i +
            2 * p z * u z i) * spatialPartial ψ i z =
      A z * deriv η z.2 + (L z + V z) * η z.2
    rw [htime z]
    simp_rw [hsecond, hspace]
    have hsumSecond :
        (∑ i : Fin 3, spatialSecondPartial qST i i z * η z.2) =
          (∑ i : Fin 3, spatialSecondPartial qST i i z) * η z.2 := by
      rw [Finset.sum_mul]
    have hsumFlux :
        (∑ i : Fin 3,
          ((vec3EuclideanNorm (u z)) ^ (2 : ℕ) * J z i + 2 * p z * u z i) *
            (spatialPartial qST i z * η z.2)) =
          (∑ i : Fin 3,
            ((vec3EuclideanNorm (u z)) ^ (2 : ℕ) * J z i + 2 * p z * u z i) *
              spatialPartial qST i z) * η z.2 := by
      calc
        _ = ∑ i : Fin 3,
            (((vec3EuclideanNorm (u z)) ^ (2 : ℕ) * J z i + 2 * p z * u z i) *
              spatialPartial qST i z) * η z.2 := by
                apply Finset.sum_congr rfl
                intro i hi
                ring
        _ = _ := (Finset.sum_mul _ _ _).symm
    rw [hsumSecond, hsumFlux]
    dsimp [A, L, V, qST, ψ]
    ring
  rw [hLeft, hRight] at hlocal
  simpa [D] using hlocal

private theorem regTails_integral_double_sum
    {X : Type*} [MeasurableSpace X] (μ : Measure X) (f : Fin 3 → Fin 3 → X → ℝ)
    (hf : ∀ i j, Integrable (f i j) μ) :
    (∫ x, ∑ i : Fin 3, ∑ j : Fin 3, f i j x ∂μ) =
      ∑ i : Fin 3, ∑ j : Fin 3, ∫ x, f i j x ∂μ := by
  rw [integral_finsetSum Finset.univ (by
    intro i hi
    exact integrable_finsetSum Finset.univ (by intro j hj; exact hf i j))]
  apply Finset.sum_congr rfl
  intro i hi
  rw [integral_finsetSum Finset.univ (by intro j hj; exact hf i j)]

/-- Summing the componentwise spatial integration by parts gives the cutoff
Laplacian contribution to the localized energy identity. -/
theorem regTails_laplacian_ibp_sum
    (u : ParabolicPoint → Vec3)
    (q : Vec3 → ℝ) (η : ℝ → ℝ)
    (hq : ContDiff ℝ (⊤ : ℕ∞) q) (hqc : HasCompactSupport q)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (hηI : tsupport η ⊆ Ioi (0 : ℝ))
    (hUcont : ∀ k : Fin 3, ContinuousOn
      (fun z : Vec3 × ℝ => u (z.1, z.2) k)
      ((Set.univ : Set Vec3) ×ˢ Ioi (0 : ℝ)))
    (hDcont : ∀ k j : Fin 3, ContinuousOn
      (fun z : Vec3 × ℝ => spatialPartial
        (fun y : ParabolicPoint => u y k) j z)
      ((Set.univ : Set Vec3) ×ˢ Ioi (0 : ℝ)))
    (hUdiff : ∀ k : Fin 3, ContDiffOn ℝ 1
      (fun z : Vec3 × ℝ => u (z.1, z.2) k)
      ((Set.univ : Set Vec3) ×ˢ Ioi (0 : ℝ)))
    :
    (∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioi (0 : ℝ)),
      (vec3EuclideanNorm (u z)) ^ (2 : ℕ) *
        (∑ j : Fin 3,
          spatialSecondPartial (fun y : ParabolicPoint => q y.1) j j z) * η z.2) =
      -2 * ∫ z in spaceTimeSet (Set.univ : Set Vec3) (Ioi (0 : ℝ)),
        (∑ i : Fin 3, ∑ j : Fin 3,
          u z i * spatialPartial (fun y : ParabolicPoint => u y i) j z *
            spatialPartial (fun y : ParabolicPoint => q y.1) j z) * η z.2 := by
  classical
  let S : Set (Vec3 × ℝ) := (Set.univ : Set Vec3) ×ˢ Ioi (0 : ℝ)
  let qST : ParabolicPoint → ℝ := fun z => q z.1
  let qj : Fin 3 → Vec3 → ℝ := fun j x => (fderiv ℝ q x) (basisVec j)
  let qjj : Fin 3 → Vec3 → ℝ := fun j x => (fderiv ℝ (qj j) x) (basisVec j)
  have hqjCompact (j : Fin 3) : HasCompactSupport (qj j) := by
    exact hqc.fderiv_apply (𝕜 := ℝ) (basisVec j)
  have hqjjCompact (j : Fin 3) : HasCompactSupport (qjj j) := by
    exact (hqjCompact j).fderiv_apply (𝕜 := ℝ) (basisVec j)
  have hqjSmooth (j : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (qj j) := by
    change ContDiff ℝ (⊤ : ℕ∞)
      (CKN.spatialDeriv q j)
    exact contDiff_spatialDeriv_smooth hq j
  have hqjjSmooth (j : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (qjj j) := by
    change ContDiff ℝ (⊤ : ℕ∞)
      (CKN.spatialDeriv (qj j) j)
    exact contDiff_spatialDeriv_smooth (hqjSmooth j) j
  have hqjSupport (j : Fin 3) : tsupport (qj j) ⊆ tsupport q := by
    exact tsupport_fderiv_apply_subset ℝ (basisVec j)
  have hqjjSupport (j : Fin 3) : tsupport (qjj j) ⊆ tsupport (qj j) := by
    exact tsupport_fderiv_apply_subset ℝ (basisVec j)
  have hqjEq (j : Fin 3) (z : Vec3 × ℝ) :
      spatialPartial qST j z = qj j z.1 := by
    rfl
  have hqjjEq (j : Fin 3) (z : Vec3 × ℝ) :
      spatialSecondPartial qST j j z = qjj j z.1 := by
    rfl
  have hqjZero (j : Fin 3) (x : Vec3) (hx : x ∉ tsupport q) :
      qj j x = 0 := by
    by_contra hne
    exact hx ((hqjSupport j) (subset_tsupport _ (Function.mem_support.mpr hne)))
  have hqjjZero (j : Fin 3) (x : Vec3) (hx : x ∉ tsupport q) :
      qjj j x = 0 := by
    by_contra hne
    have hqjjMem : x ∈ tsupport (qjj j) :=
      subset_tsupport _ (Function.mem_support.mpr hne)
    exact hx ((hqjSupport j) (hqjjSupport j hqjjMem))
  have hS : IsOpen ((Set.univ : Set Vec3) ×ˢ Ioi (0 : ℝ)) :=
    isOpen_univ.prod isOpen_Ioi
  have hSmeas : MeasurableSet ((Set.univ : Set Vec3) ×ˢ Ioi (0 : ℝ)) :=
    hS.measurableSet
  have hMeasure :
      (volume : Measure (Vec3 × ℝ)).restrict
          ((Set.univ : Set Vec3) ×ˢ Ioi (0 : ℝ)) =
        (volume : Measure Vec3).prod (volume.restrict (Ioi (0 : ℝ))) := by
    change ((volume : Measure Vec3).prod (volume : Measure ℝ)).restrict
        ((Set.univ : Set Vec3) ×ˢ Ioi (0 : ℝ)) = _
    rw [← Measure.prod_restrict (μ := (volume : Measure Vec3))
      (ν := (volume : Measure ℝ)) Set.univ (Ioi (0 : ℝ))]
    simp [Measure.restrict_univ]
  have hLeftCompInt (i j : Fin 3) : Integrable
      (fun z : Vec3 × ℝ => u (z.1, z.2) i ^ (2 : ℕ) * qjj j z.1 * η z.2)
      ((volume : Measure Vec3).prod (volume.restrict (Ioi (0 : ℝ)))) := by
    apply regTails_integrable_timeFactor_of_spatial_support
      (A := fun z => u (z.1, z.2) i ^ (2 : ℕ) * qjj j z.1)
      (K := tsupport q) hS ?_ hqc.isCompact ?_ η hη hηc hηI
    · have hUi : ContinuousOn (fun z : Vec3 × ℝ => u (z.1, z.2) i) _ := hUcont i
      have hqjj : Continuous (qjj j) := (hqjjSmooth j).continuous
      exact hUi.pow 2 |>.mul (hqjj.comp continuous_fst).continuousOn
    · intro z ht hz
      simp [hqjjZero j z.1 hz]
  have hCrossCompInt (i j : Fin 3) : Integrable
      (fun z : Vec3 × ℝ =>
        u (z.1, z.2) i * spatialPartial
          (fun y : ParabolicPoint => u y i) j z * qj j z.1 * η z.2)
      ((volume : Measure Vec3).prod (volume.restrict (Ioi (0 : ℝ)))) := by
    apply regTails_integrable_timeFactor_of_spatial_support
      (A := fun z => u (z.1, z.2) i * spatialPartial
        (fun y : ParabolicPoint => u y i) j z * qj j z.1)
      (K := tsupport q) hS ?_ hqc.isCompact ?_ η hη hηc hηI
    · have hUi : ContinuousOn (fun z : Vec3 × ℝ => u (z.1, z.2) i) _ := hUcont i
      have hDij : ContinuousOn (fun z : Vec3 × ℝ => spatialPartial
          (fun y : ParabolicPoint => u y i) j z) _ :=
        hDcont i j
      have hqj : Continuous (qj j) := (hqjSmooth j).continuous
      exact (hUi.mul hDij).mul (hqj.comp continuous_fst).continuousOn
    · intro z ht hz
      simp [hqjZero j z.1 hz]
  have hLeftCompIntOn (i j : Fin 3) : Integrable
      (fun z : Vec3 × ℝ => u (z.1, z.2) i ^ (2 : ℕ) * qjj j z.1 * η z.2)
      ((volume : Measure (Vec3 × ℝ)).restrict
        ((Set.univ : Set Vec3) ×ˢ Ioi (0 : ℝ))) := by
    rw [hMeasure]
    exact hLeftCompInt i j
  have hCrossCompIntOn (i j : Fin 3) : Integrable
      (fun z : Vec3 × ℝ =>
        u (z.1, z.2) i * spatialPartial
          (fun y : ParabolicPoint => u y i) j z * qj j z.1 * η z.2)
      ((volume : Measure (Vec3 × ℝ)).restrict
        ((Set.univ : Set Vec3) ×ˢ Ioi (0 : ℝ))) := by
    rw [hMeasure]
    exact hCrossCompInt i j
  have hLhsExpand :
      (∫ z in S,
        (vec3EuclideanNorm (u (z.1, z.2))) ^ (2 : ℕ) *
          (∑ j : Fin 3, qjj j z.1) * η z.2) =
      ∑ i : Fin 3, ∑ j : Fin 3,
          ∫ z in S, u (z.1, z.2) i ^ (2 : ℕ) * qjj j z.1 * η z.2 := by
    calc
      _ = ∫ z in S, ∑ i : Fin 3, ∑ j : Fin 3,
          u (z.1, z.2) i ^ (2 : ℕ) * qjj j z.1 * η z.2 := by
        apply integral_congr_ae
        filter_upwards [] with z
        rw [regTails_vec3EuclideanNorm_sq]
        simp only [Finset.sum_mul, Finset.mul_sum]
        exact Finset.sum_comm
      _ = _ := regTails_integral_double_sum _ _ hLeftCompIntOn
  have hRhsExpand :
      (∫ z in S,
        (∑ i : Fin 3, ∑ j : Fin 3,
          u (z.1, z.2) i * spatialPartial (fun y : ParabolicPoint => u y i) j z *
            qj j z.1) * η z.2) =
      ∑ i : Fin 3, ∑ j : Fin 3,
          ∫ z in S, u (z.1, z.2) i * spatialPartial
            (fun y : ParabolicPoint => u y i) j z * qj j z.1 * η z.2 := by
    calc
      _ = ∫ z in S, ∑ i : Fin 3, ∑ j : Fin 3,
          u (z.1, z.2) i * spatialPartial (fun y : ParabolicPoint => u y i) j z *
            qj j z.1 * η z.2 := by
        apply integral_congr_ae
        filter_upwards [] with z
        simp only [Finset.sum_mul]
      _ = _ := regTails_integral_double_sum _ _ hCrossCompIntOn
  have hCompIBP (i j : Fin 3) :
      (∫ z in S, u (z.1, z.2) i ^ (2 : ℕ) * qjj j z.1 * η z.2) =
      -2 * ∫ z in S, u (z.1, z.2) i * spatialPartial
        (fun y : ParabolicPoint => u y i) j z *
        qj j z.1 * η z.2 := by
    have hIBP := regTails_laplacian_ibp u q η i j hq hqc hη hηc hηI
      hUcont hDcont hUdiff
    calc
      _ = ∫ z in S, u (z.1, z.2) i ^ (2 : ℕ) *
          spatialSecondPartial qST j j z * η z.2 := by
            apply setIntegral_congr_fun hSmeas
            intro z hz
            change u ((z.1, z.2) : ParabolicPoint) i ^ (2 : ℕ) *
                qjj j z.1 * η z.2 =
              u ((z.1, z.2) : ParabolicPoint) i ^ (2 : ℕ) *
                spatialSecondPartial qST j j z * η z.2
            rw [← hqjjEq j z]
      _ = -2 * ∫ z in S, u (z.1, z.2) i * spatialPartial
          (fun y : ParabolicPoint => u y i) j z * spatialPartial qST j z * η z.2 := by
            simpa [S, qST] using hIBP
      _ = -2 * ∫ z in S, u (z.1, z.2) i * spatialPartial
          (fun y : ParabolicPoint => u y i) j z * qj j z.1 * η z.2 := by
            congr 1
  have hRhsPartial :
      (∫ z in S,
        (∑ i : Fin 3, ∑ j : Fin 3,
          u z i * spatialPartial (fun y : ParabolicPoint => u y i) j z *
            qj j z.1) * η z.2) =
      ∫ z in S,
        (∑ i : Fin 3, ∑ j : Fin 3,
          u z i * spatialPartial (fun y : ParabolicPoint => u y i) j z *
            spatialPartial qST j z) * η z.2 := by
    apply setIntegral_congr_fun hSmeas
    intro z hz
    simp_rw [hqjEq]
  calc
    _ = ∑ i : Fin 3, ∑ j : Fin 3,
        ∫ z in S, u (z.1, z.2) i ^ (2 : ℕ) *
          qjj j z.1 * η z.2 := hLhsExpand
    _ = -2 * ∑ i : Fin 3, ∑ j : Fin 3,
        ∫ z in S, u (z.1, z.2) i * spatialPartial
          (fun y : ParabolicPoint => u y i) j z * qj j z.1 * η z.2 := by
          simp_rw [hCompIBP]
          calc
            ∑ i : Fin 3, ∑ j : Fin 3,
                (-2) * ∫ z in S, u (z.1, z.2) i * spatialPartial
                  (fun y : ParabolicPoint => u y i) j z *
                  qj j z.1 * η z.2
              = ∑ i : Fin 3, (-2) * ∑ j : Fin 3,
                  ∫ z in S, u (z.1, z.2) i * spatialPartial
                    (fun y : ParabolicPoint => u y i) j z *
                    qj j z.1 * η z.2 := by
                    apply Finset.sum_congr rfl
                    intro i hi
                    rw [← Finset.mul_sum]
            _ = (-2) * ∑ i : Fin 3, ∑ j : Fin 3,
                  ∫ z in S, u (z.1, z.2) i * spatialPartial
                    (fun y : ParabolicPoint => u y i) j z *
                    qj j z.1 * η z.2 := by
                    rw [← Finset.mul_sum]
    _ = -2 * ∫ z in S,
        (∑ i : Fin 3, ∑ j : Fin 3,
          u z i * spatialPartial (fun y : ParabolicPoint => u y i) j z *
            spatialPartial qST j z) * η z.2 := by
          calc
            _ = -2 * ∫ z in S,
                (∑ i : Fin 3, ∑ j : Fin 3,
                  u z i * spatialPartial (fun y : ParabolicPoint => u y i) j z *
                    qj j z.1) * η z.2 := by
                    rw [← hRhsExpand]
            _ = _ := by rw [hRhsPartial]

end CKN.Leray

end
