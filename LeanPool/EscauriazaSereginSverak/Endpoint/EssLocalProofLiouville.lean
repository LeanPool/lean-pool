/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.LocalLiouville
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Vec3Norm
public import LeanPool.CaffarelliKohnNirenberg.Setting.DivergenceFreeSlice
public import LeanPool.CaffarelliKohnNirenberg.Pressure.ForceDivergenceFreeBridge
public import LeanPool.CaffarelliKohnNirenberg.Statements.SuitableWeakSolution
public import LeanPool.CaffarelliKohnNirenberg.ClassEquivalence.MainTheorems
public import LeanPool.EscauriazaSereginSverak.Endpoint.VorticityDefinitions

public section

open MeasureTheory Set CKN CKN.Foundation.Parabolic
open scoped ENNReal


noncomputable section

namespace ESS

/-- A uniform essential bound for Euclidean slice norms gives ordinary
`L³` membership on almost every time slice. -/
theorem essLocal_slices_memLp_of_euclidean_essSup
    (U : ParabolicPoint → Vec3) (hU : Measurable U) (J : Set ℝ)
    (hbound : essSup (fun t : ℝ => eLpNorm
      (fun x : Vec3 => vec3EuclideanNorm (U (x, t)))
      (3 : ℝ≥0∞) volume) (volume.restrict J) < ⊤) :
    ∀ᵐ t ∂(volume.restrict J),
      MemLp (fun x : Vec3 => U (x, t)) (3 : ℝ≥0∞) volume := by
  filter_upwards [ENNReal.ae_le_essSup (fun t : ℝ => eLpNorm
    (fun x : Vec3 => vec3EuclideanNorm (U (x, t)))
    (3 : ℝ≥0∞) volume)] with t ht
  have hslice : Measurable (fun x : Vec3 => U (x, t)) :=
    hU.comp measurable_prodMk_right
  have hscalar : MemLp (fun x : Vec3 =>
      vec3EuclideanNorm (U (x, t))) (3 : ℝ≥0∞) volume :=
    lt_of_le_of_lt ht hbound
  apply hscalar.of_le hslice.aestronglyMeasurable
  filter_upwards with x
  simpa only [Real.norm_eq_abs,
    abs_of_nonneg (vec3EuclideanNorm_nonneg (U (x, t)))] using
      norm_le_vec3EuclideanNorm (U (x, t))

/-- Suitability on every bounded past cylinder makes almost every global
spatial slice divergence free. -/
theorem essLocal_slices_divergenceFree_of_local_suitable
    (U : ParabolicPoint → Vec3)
    (DU : ParabolicPoint → Fin 3 → Vec3)
    (q : ParabolicPoint → ℝ)
    (hsol : ∀ (R a : ℝ), 0 < R → a < 0 →
      IsSuitableWeakSolution (vec3Ball 0 R) (Ioo a 0) 3
        U DU q (0 : ParabolicPoint → Vec3))
    (hL3 : ∀ᵐ t ∂(volume.restrict (Ioo (-2 : ℝ) 0)),
      MemLp (fun x : Vec3 => U (x, t)) (3 : ℝ≥0∞) volume) :
    ∀ᵐ t ∂(volume.restrict (Ioo (-2 : ℝ) 0)),
      CKN.DistributionalDivergenceFree (fun x : Vec3 => U (x, t)) := by
  have hloc : ∀ᵐ t ∂(volume.restrict (Ioo (-2 : ℝ) 0)),
      ∀ i : Fin 3, LocallyIntegrable (fun x : Vec3 => U (x, t) i) volume := by
    filter_upwards [hL3] with t ht i
    exact (ht.continuousLinearMap_comp
      (ContinuousLinearMap.proj i : Vec3 →L[ℝ] ℝ)).locallyIntegrable
        (by norm_num)
  have htest : ∀ ψ : Vec3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ →
      HasCompactSupport ψ →
      ∀ᵐ t ∂(volume.restrict (Ioo (-2 : ℝ) 0)),
        ∫ x, ∑ i : Fin 3,
          U (x, t) i * (fderiv ℝ ψ x) (CKN.basisVec i) = 0 := by
    intro ψ hψ hψc
    obtain ⟨S, hS⟩ := hψc.isCompact.isBounded.subset_ball (0 : Vec3)
    let R : ℝ := Real.sqrt 3 * (max S 0 + 1)
    have hR : 0 < R := by
      dsimp [R]
      positivity
    have hψR : tsupport ψ ⊆ vec3Ball 0 R := by
      intro x hx
      have hxS : ‖x‖ < S := by
        simpa using hS hx
      have hxR : ‖x‖ < max S 0 + 1 := by
        have hSmax : S ≤ max S 0 := le_max_left _ _
        linarith only [hxS, hSmax]
      change vec3EuclideanNorm (x - 0) < R
      simpa only [sub_zero] using
        (vec3EuclideanNorm_le_sqrt_three_mul_norm x).trans_lt
          (mul_lt_mul_of_pos_left hxR (by positivity))
    have hsolR := hsol R (-2) hR (by norm_num)
    have hball := CKN.divfree_slice_weak_of_suitable
      (CKN.isSuitableWeakSolution_iff_integrable.mp hsolR)
      ψ hψ hψc hψR
    filter_upwards [hball] with t ht
    have hzeroOut (x : Vec3) (hx : x ∉ tsupport ψ) :
        (∑ i : Fin 3,
          U (x, t) i * (fderiv ℝ ψ x) (CKN.basisVec i)) = 0 := by
      rw [fderiv_of_notMem_tsupport (𝕜 := ℝ) hx]
      simp
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun x hx => hzeroOut x (fun h => hx (hψR h)))] at ht
    exact ht
  exact CKN.pressure_force_slice_divergenceFree_of_spacetime hloc htest

private theorem essLocal_weakVorticity_zero_symmetric
    (DU : ParabolicPoint → Fin 3 → Vec3) (z : ParabolicPoint)
    (hzero : weakVorticity DU z = 0) (i j : Fin 3) :
    DU z i j = DU z j i := by
  have h01 : DU z 0 1 = DU z 1 0 := by
    have h := congrFun hzero (2 : Fin 3)
    simp only [weakVorticity_two, Pi.zero_apply, sub_eq_zero] at h
    exact h.symm
  have h02 : DU z 0 2 = DU z 2 0 := by
    have h := congrFun hzero (1 : Fin 3)
    simpa only [weakVorticity_one, Pi.zero_apply, sub_eq_zero] using h
  have h12 : DU z 1 2 = DU z 2 1 := by
    have h := congrFun hzero (0 : Fin 3)
    simp only [weakVorticity_zero, Pi.zero_apply, sub_eq_zero] at h
    exact h.symm
  fin_cases i <;> fin_cases j <;> simp [h01, h02, h12]

/-- A zero weak vorticity and the slice weak-gradient identity imply the
distributional curl condition used by `liouvilleL3`. -/
theorem essLocal_slices_curlFree_of_zero_vorticity
    (U : ParabolicPoint → Vec3) (DU : ParabolicPoint → Fin 3 → Vec3)
    (hL3 : ∀ᵐ t ∂(volume.restrict (Ioo (-2 : ℝ) 0)),
      MemLp (fun x : Vec3 => U (x, t)) (3 : ℝ≥0∞) volume)
    (hgrad : ∀ᵐ t ∂(volume.restrict (Ioo (-2 : ℝ) 0)),
      ∀ i : Fin 3,
        HasWeakGradientOn Set.univ
          (fun x : Vec3 => U (x, t) i)
          (fun x : Vec3 => DU (x, t) i))
    (hzero : ∀ᵐ t ∂(volume.restrict (Ioo (-2 : ℝ) 0)),
      (fun x : Vec3 => weakVorticity DU (x, t)) =ᵐ[volume] 0) :
    ∀ᵐ t ∂(volume.restrict (Ioo (-2 : ℝ) 0)),
      ∀ (i j : Fin 3) (φ : Vec3 → ℝ), CKN.SmoothCompactTest φ →
        ∫ x, U (x, t) i * CKN.spatialDeriv φ j x -
          U (x, t) j * CKN.spatialDeriv φ i x = 0 := by
  filter_upwards [hL3, hgrad, hzero] with t htL3 htgrad htzero
  intro i j φ hφ
  have hA := (htgrad i j) φ (contDiff_infty.2 hφ.1) hφ.2
    (Set.subset_univ _)
  have hB := (htgrad j i) φ (contDiff_infty.2 hφ.1) hφ.2
    (Set.subset_univ _)
  simp only [setIntegral_univ] at hA hB
  have hDU : (fun x : Vec3 => DU (x, t) i j * φ x) =ᵐ[volume]
      (fun x : Vec3 => DU (x, t) j i * φ x) := by
    filter_upwards [htzero] with x hx
    rw [essLocal_weakVorticity_zero_symmetric DU (x, t) hx i j]
  have hInt := integral_congr_ae hDU
  have hpairInt (k l : Fin 3) :
      Integrable (fun x : Vec3 => U (x, t) k *
        CKN.spatialDeriv φ l x) volume := by
    have hcomp : MemLp (fun x : Vec3 => U (x, t) k) 3 volume :=
      htL3.continuousLinearMap_comp
        (ContinuousLinearMap.proj k : Vec3 →L[ℝ] ℝ)
    have hderivSmooth : Continuous (CKN.spatialDeriv φ l) :=
      (CKN.contDiff_spatialDeriv_smooth (contDiff_infty.2 hφ.1) l).continuous
    have hderivCompact : HasCompactSupport (CKN.spatialDeriv φ l) :=
      hφ.2.fderiv_apply (𝕜 := ℝ) (CKN.basisVec l)
    have hint :=
      (hcomp.locallyIntegrable (by norm_num)).integrable_smul_left_of_hasCompactSupport
        hderivSmooth hderivCompact
    convert hint using 1
    funext x
    simp only [smul_eq_mul]
    exact mul_comm _ _
  rw [integral_sub (hpairInt i j) (hpairInt j i)]
  simp only [CKN.spatialDeriv] at *
  rw [hA, hB, hInt]
  ring

/-- Divergence-free and curl-free critical slices make the ancient velocity
vanish on the final two time units. -/
theorem essLocal_limit_zero_of_slicewise_div_curl
    (U : ParabolicPoint → Vec3) (hU : Measurable U)
    (hslices : ∀ᵐ t ∂(volume.restrict (Ioo (-2 : ℝ) 0)),
      MemLp (fun x : Vec3 => U (x, t)) (ENNReal.ofReal (3 : ℝ)) volume ∧
      CKN.DistributionalDivergenceFree (fun x : Vec3 => U (x, t)) ∧
      ∀ (i j : Fin 3) (φ : Vec3 → ℝ), CKN.SmoothCompactTest φ →
        ∫ x, U (x, t) i * CKN.spatialDeriv φ j x -
          U (x, t) j * CKN.spatialDeriv φ i x = 0) :
    U =ᵐ[volume.restrict
      (spaceTimeSet Set.univ (Ioo (-2 : ℝ) 0))] 0 := by
  let μt : Measure ℝ := volume.restrict (Ioo (-2 : ℝ) 0)
  let E : Set (Vec3 × ℝ) := {z | U z = 0}
  have hE : MeasurableSet E := measurableSet_eq_fun hU measurable_const
  have htime : ∀ᵐ t ∂μt, ∀ᵐ x : Vec3 ∂volume, U (x, t) = 0 := by
    filter_upwards [hslices] with t ht
    exact liouvilleL3 ht.1 ht.2.1 ht.2.2
  have hspace : ∀ᵐ x : Vec3 ∂volume, ∀ᵐ t ∂μt, U (x, t) = 0 :=
    (Measure.ae_ae_comm hE).mpr htime
  have hprod : ∀ᵐ z : Vec3 × ℝ ∂((volume : Measure Vec3).prod μt),
      U z = 0 :=
    (Measure.ae_prod_iff_ae_ae hE).2 hspace
  change U =ᵐ[(volume : Measure (Vec3 × ℝ)).restrict
    (Set.univ ×ˢ Ioo (-2 : ℝ) 0)] 0
  rw [Measure.volume_eq_prod Vec3 ℝ, ← Measure.prod_restrict,
    Measure.restrict_univ]
  exact hprod

end ESS
