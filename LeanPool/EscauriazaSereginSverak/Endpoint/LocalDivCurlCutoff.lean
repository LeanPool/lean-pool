/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.LocalSobolevCalculus

/-!
# Divergence and curl of a cutoff field

If `div v = 0` and `curl v = ζ` in distributions on an open set `U`, and `χ` is
smooth with compact support in `U`, then the field `V = χv`, extended by zero,
has on `ℝ³` the distributional divergence `∇χ · v` and the distributional
curl `χζ + ∇χ × v` (`lem:local-div-curl`).
-/

public section

open MeasureTheory Set
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

section Cutoff

variable {U : Set Vec3} {χ : Vec3 → ℝ} {v ζ : Vec3 → Vec3}

/-- A continuous function with compact support is square integrable on every
restriction. -/
theorem memLp_two_restrict_of_compact {g : Vec3 → ℝ} (hg : Continuous g)
    (hgc : HasCompactSupport g) (U : Set Vec3) : MemLp g 2 (volume.restrict U) :=
  (hg.memLp_of_hasCompactSupport hgc).restrict U

/-- Whole-space integrals of integrands vanishing outside `tsupport χ ⊆ U` are
integrals over `U`. -/
theorem integral_eq_setIntegral_of_tsupport {F : Vec3 → ℝ} (hχU : tsupport χ ⊆ U)
    (hF : ∀ x, x ∉ tsupport χ → F x = 0) : ∫ x, F x = ∫ x in U, F x :=
  (setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => hF x fun h => hx (hχU h)).symm

theorem spatialDeriv_eq_zero_of_notMem_tsupport {g : Vec3 → ℝ} {x : Vec3}
    (hx : x ∉ tsupport g) (i : Fin 3) : spatialDeriv g i x = 0 :=
  image_eq_zero_of_notMem_tsupport (f := spatialDeriv g i)
    fun h => hx (tsupport_fderiv_apply_subset ℝ (basisVec i) h)

/-- The distributional divergence of the cutoff field. -/
theorem cutoff_weakDiv (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχc : HasCompactSupport χ)
    (hχU : tsupport χ ⊆ U) (hv : ∀ i, MemLp (fun x => v x i) 2 (volume.restrict U))
    (hdiv : ∀ φ : Vec3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ U →
      ∫ x in U, ∑ i : Fin 3, v x i * spatialDeriv φ i x = 0)
    (φ : Vec3 → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) :
    ∫ x, ∑ i : Fin 3, χ x * v x i * spatialDeriv φ i x =
      -∫ x, (∑ i : Fin 3, spatialDeriv χ i x * v x i) * φ x := by
  let ψ : Vec3 → ℝ := fun x => χ x * φ x
  have hψ : ContDiff ℝ (⊤ : ℕ∞) ψ := hχ.mul hφ
  have hψc : HasCompactSupport ψ := hχc.mul_right
  have hψU : tsupport ψ ⊆ U := (tsupport_mul_subset_left (f := χ) (g := φ)).trans hχU
  have hχd : Differentiable ℝ χ := hχ.differentiable (by simp)
  have hφd : Differentiable ℝ φ := hφ.differentiable (by simp)
  have hdψ (i : Fin 3) (x : Vec3) :
      spatialDeriv ψ i x = spatialDeriv χ i x * φ x + χ x * spatialDeriv φ i x :=
    spatialDeriv_mul (hχd x) (hφd x) i
  have h0 := hdiv ψ hψ hψc hψU
  -- square integrable factors
  have hdχ (i : Fin 3) : Continuous (spatialDeriv χ i) :=
    (contDiff_spatialDeriv_smooth hχ i).continuous
  have hdχc (i : Fin 3) : HasCompactSupport (spatialDeriv χ i) :=
    hχc.fderiv_apply (𝕜 := ℝ) (basisVec i)
  have hdψL (i : Fin 3) : MemLp (spatialDeriv ψ i) 2 (volume.restrict U) :=
    memLp_two_restrict_of_compact (contDiff_spatialDeriv_smooth hψ i).continuous
      (hψc.fderiv_apply (𝕜 := ℝ) (basisVec i)) U
  have hgL (i : Fin 3) : MemLp (fun x => spatialDeriv χ i x * φ x) 2 (volume.restrict U) :=
    memLp_two_restrict_of_compact ((hdχ i).mul hφ.continuous) (hdχc i).mul_right U
  have i1 (i : Fin 3) : Integrable (fun x => v x i * spatialDeriv ψ i x) (volume.restrict U) :=
    (hv i).integrable_mul (hdψL i)
  have i2 (i : Fin 3) : Integrable (fun x => v x i * (spatialDeriv χ i x * φ x))
      (volume.restrict U) := (hv i).integrable_mul (hgL i)
  -- to integrals over `U`
  rw [integral_eq_setIntegral_of_tsupport hχU fun x hx => by
      simp [image_eq_zero_of_notMem_tsupport hx],
    integral_eq_setIntegral_of_tsupport hχU fun x hx => by
      simp [spatialDeriv_eq_zero_of_notMem_tsupport hx]]
  have hpt (x : Vec3) : ∑ i : Fin 3, χ x * v x i * spatialDeriv φ i x =
      ∑ i : Fin 3, v x i * spatialDeriv ψ i x -
        ∑ i : Fin 3, v x i * (spatialDeriv χ i x * φ x) := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hdψ i x]
    ring
  have hpt2 (x : Vec3) : (∑ i : Fin 3, spatialDeriv χ i x * v x i) * φ x =
      ∑ i : Fin 3, v x i * (spatialDeriv χ i x * φ x) := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [integral_congr_ae (ae_of_all _ hpt), integral_congr_ae (ae_of_all _ hpt2)]
  have hs1 : Integrable (fun x => ∑ i : Fin 3, v x i * spatialDeriv ψ i x)
      (volume.restrict U) := integrable_finsetSum _ fun i _ => i1 i
  have hs2 : Integrable (fun x => ∑ i : Fin 3, v x i * (spatialDeriv χ i x * φ x))
      (volume.restrict U) := integrable_finsetSum _ fun i _ => i2 i
  rw [integral_sub hs1 hs2, h0, zero_sub]

/-- The distributional curl of the cutoff field. -/
theorem cutoff_weakCurl (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hχc : HasCompactSupport χ)
    (hχU : tsupport χ ⊆ U) (hv : ∀ i, MemLp (fun x => v x i) 2 (volume.restrict U))
    (hζ : ∀ k, MemLp (fun x => ζ x k) 2 (volume.restrict U))
    (hcurl : ∀ φ : Vec3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ U →
      ∀ k : Fin 3,
        ∫ x in U, ζ x k * φ x =
          ∫ x in U, (v x (k + 1) * spatialDeriv φ (k + 2) x -
            v x (k + 2) * spatialDeriv φ (k + 1) x))
    (φ : Vec3 → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (k : Fin 3) :
    ∫ x, (χ x * ζ x k + (spatialDeriv χ (k + 1) x * v x (k + 2) -
        spatialDeriv χ (k + 2) x * v x (k + 1))) * φ x =
      ∫ x, (χ x * v x (k + 1) * spatialDeriv φ (k + 2) x -
        χ x * v x (k + 2) * spatialDeriv φ (k + 1) x) := by
  let ψ : Vec3 → ℝ := fun x => χ x * φ x
  have hψ : ContDiff ℝ (⊤ : ℕ∞) ψ := hχ.mul hφ
  have hψc : HasCompactSupport ψ := hχc.mul_right
  have hψU : tsupport ψ ⊆ U := (tsupport_mul_subset_left (f := χ) (g := φ)).trans hχU
  have hχd : Differentiable ℝ χ := hχ.differentiable (by simp)
  have hφd : Differentiable ℝ φ := hφ.differentiable (by simp)
  have hdψ (i : Fin 3) (x : Vec3) :
      spatialDeriv ψ i x = spatialDeriv χ i x * φ x + χ x * spatialDeriv φ i x :=
    spatialDeriv_mul (hχd x) (hφd x) i
  have h0 := hcurl ψ hψ hψc hψU k
  have hdχ (i : Fin 3) : Continuous (spatialDeriv χ i) :=
    (contDiff_spatialDeriv_smooth hχ i).continuous
  have hdχc (i : Fin 3) : HasCompactSupport (spatialDeriv χ i) :=
    hχc.fderiv_apply (𝕜 := ℝ) (basisVec i)
  have hdψL (i : Fin 3) : MemLp (spatialDeriv ψ i) 2 (volume.restrict U) :=
    memLp_two_restrict_of_compact (contDiff_spatialDeriv_smooth hψ i).continuous
      (hψc.fderiv_apply (𝕜 := ℝ) (basisVec i)) U
  have hgL (i : Fin 3) : MemLp (fun x => spatialDeriv χ i x * φ x) 2 (volume.restrict U) :=
    memLp_two_restrict_of_compact ((hdχ i).mul hφ.continuous) (hdχc i).mul_right U
  have hψL : MemLp ψ 2 (volume.restrict U) :=
    memLp_two_restrict_of_compact hψ.continuous hψc U
  rw [integral_eq_setIntegral_of_tsupport hχU fun x hx => by
      simp [image_eq_zero_of_notMem_tsupport hx, spatialDeriv_eq_zero_of_notMem_tsupport hx],
    integral_eq_setIntegral_of_tsupport hχU fun x hx => by
      simp [image_eq_zero_of_notMem_tsupport hx]]
  -- the pointwise identities
  let A : Vec3 → ℝ := fun x => v x (k + 1) * spatialDeriv ψ (k + 2) x -
    v x (k + 2) * spatialDeriv ψ (k + 1) x
  let Bf : Vec3 → ℝ := fun x => v x (k + 1) * (spatialDeriv χ (k + 2) x * φ x) -
    v x (k + 2) * (spatialDeriv χ (k + 1) x * φ x)
  have hA : Integrable A (volume.restrict U) :=
    ((hv _).integrable_mul (hdψL _)).sub ((hv _).integrable_mul (hdψL _))
  have hB : Integrable Bf (volume.restrict U) :=
    ((hv _).integrable_mul (hgL _)).sub ((hv _).integrable_mul (hgL _))
  have hZ : Integrable (fun x => ζ x k * ψ x) (volume.restrict U) :=
    (hζ k).integrable_mul hψL
  have hpt1 (x : Vec3) : χ x * v x (k + 1) * spatialDeriv φ (k + 2) x -
      χ x * v x (k + 2) * spatialDeriv φ (k + 1) x = A x - Bf x := by
    simp only [A, Bf, hdψ]
    ring
  have hpt2 (x : Vec3) : (χ x * ζ x k + (spatialDeriv χ (k + 1) x * v x (k + 2) -
      spatialDeriv χ (k + 2) x * v x (k + 1))) * φ x = ζ x k * ψ x - Bf x := by
    simp only [ψ, Bf]
    ring
  rw [integral_congr_ae (ae_of_all _ hpt1), integral_congr_ae (ae_of_all _ hpt2),
    integral_sub hA hB, integral_sub hZ hB]
  change (∫ x in U, ζ x k * ψ x) - _ = (∫ x in U, A x) - _
  rw [h0]

end Cutoff

end ESS
