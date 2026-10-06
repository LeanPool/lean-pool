/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.ForcedRegLocalEnergyLimit

/-!
# Static identities for the local energy inequality

For a square-integrable weakly differentiable velocity slice `u` with gradient
`D` and a smooth compactly supported weight `ψ`, the chain rule
`∑ⱼ ∫ D_kj u_k ∂ⱼψ = -½ ∫ u_k² Δψ`, the transport identity
`∑ⱼ ∫ Vⱼ u_k D_kj ψ = -½ ∫ u_k² V·∇ψ` for a divergence-free `C¹` field `V`,
and the pressure identity `∑ₖ ∫ u_k ψ Gₖ = -∫ p u·∇ψ` for a pressure `p`
with weak gradient `G` hold, by mollification. These are the spatial
identities of `eq:reg-local-energy-forced`.
-/

public section

open MeasureTheory Set Filter
open CKN CKN.Foundation.Parabolic
open scoped ENNReal Convolution Topology

noncomputable section

namespace CKN.Leray

/-- Integration by parts of the square of a smooth function against a smooth
compactly supported factor. -/
theorem integral_sq_mul_fderiv {w g : Vec3 → ℝ} (hw : ContDiff ℝ (⊤ : ℕ∞) w)
    (hg : ContDiff ℝ 1 g) (hgc : HasCompactSupport g) (j : Fin 3) :
    ∫ x, w x ^ 2 * fderiv ℝ g x (CKN.basisVec j) =
      -∫ x, 2 * (w x * fderiv ℝ w x (CKN.basisVec j)) * g x := by
  have hwd : ∀ x, HasFDerivAt (fun y => w y ^ 2) (w x • fderiv ℝ w x + w x • fderiv ℝ w x) x := by
    intro x
    have h := ((hw.differentiable (by simp)) x).hasFDerivAt
    have hmul := h.mul h
    convert hmul using 1
    funext y
    simp only [sq, Pi.mul_apply]
  have hgder : ∀ x, fderiv ℝ (fun y => w y ^ 2) x (CKN.basisVec j) =
      2 * (w x * fderiv ℝ w x (CKN.basisVec j)) := by
    intro x
    rw [(hwd x).fderiv]
    simp only [add_apply, smul_apply, smul_eq_mul]
    ring
  have hwc : Continuous fun x => w x ^ 2 := hw.continuous.pow 2
  have hdw : Continuous fun x => fderiv ℝ w x (CKN.basisVec j) :=
    (hw.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdg : Continuous fun x => fderiv ℝ g x (CKN.basisVec j) :=
    (hg.continuous_fderiv (by simp)).clm_apply continuous_const
  have h1 : Integrable fun x => fderiv ℝ (fun y => w y ^ 2) x (CKN.basisVec j) * g x := by
    simp_rw [hgder]
    exact integrable_mul_of_hasCompactSupport_right (continuous_const.mul (hw.continuous.mul hdw))
      hg.continuous hgc
  have h2 : Integrable fun x => w x ^ 2 * fderiv ℝ g x (CKN.basisVec j) :=
    integrable_mul_of_hasCompactSupport_right hwc hdg (hgc.fderiv_apply (𝕜 := ℝ) (CKN.basisVec j))
  have h3 : Integrable fun x => w x ^ 2 * g x :=
    integrable_mul_of_hasCompactSupport_right hwc hg.continuous hgc
  have hibp := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
    (f := fun y => w y ^ 2) (g := g) (v := CKN.basisVec j) h1 h2 h3
    (fun x _ => (hwd x).differentiableAt) (fun x _ => (hg.differentiable (by simp)) x)
  simp_rw [hgder] at hibp
  exact hibp

section Identities

variable {u : Vec3 → Vec3} (hu : ∀ k, MemLp (fun x => u x k) 2 volume)
  {D : Vec3 → Fin 3 → Vec3} (hD : ∀ k j, MemLp (fun x => D x k j) 2 volume)
  (hweak : ∀ k, CKN.HasWeakGradientOn (Set.univ : Set Vec3) (fun x => u x k) (fun x => D x k))

theorem leConv_leMol_contDiff {g : Vec3 → ℝ} (hg : MemLp g 2 volume) (n : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (leConv (leMol n) g) :=
  leConv_contDiff (leMol_contDiff n) (leMol_hasCompactSupport n)
    (hg.locallyIntegrable (by norm_num))

theorem tendsto_mul_leConv_leMol {g h : Vec3 → ℝ} (hg : MemLp g 2 volume) (hh : Continuous h)
    (hhc : HasCompactSupport h) :
    Tendsto (fun n => eLpNorm ((fun x => leConv (leMol n) g x * h x) - fun x => g x * h x) 2
      volume) atTop (𝓝 0) := by
  obtain ⟨M, hM⟩ := Continuous.bounded_above_of_compact_support hh hhc
  exact tendsto_eLpNorm_mul_bounded (tendsto_leConv_leMol hg)
    (fun n => ((memLp_leConv_leMol hg n).sub hg).aestronglyMeasurable) hh.aestronglyMeasurable hM

theorem memLp_mul_compact {g h : Vec3 → ℝ} (hg : MemLp g 2 volume) (hh : Continuous h)
    (hhc : HasCompactSupport h) : MemLp (fun x => g x * h x) 2 volume := by
  obtain ⟨M, hM⟩ := Continuous.bounded_above_of_compact_support hh hhc
  exact memLp_mul_bounded hg hh.aestronglyMeasurable hM

include hu hD hweak in
/-- The chain rule `∑ⱼ ∫ D_kj u_k ∂ⱼψ = -½ ∫ u_k² Δψ`. -/
theorem sum_integral_grad_mul_eq {ψ : Vec3 → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψc : HasCompactSupport ψ) (k : Fin 3) :
    ∑ j : Fin 3, ∫ x, D x k j * (u x k * fderiv ℝ ψ x (CKN.basisVec j)) =
      -(1 / 2) * ∫ x, u x k * (u x k * CKN.spatialLaplacian ψ x) := by
  have hdψ : ∀ j, ContDiff ℝ (⊤ : ℕ∞) fun x => fderiv ℝ ψ x (CKN.basisVec j) := fun j =>
    CKN.contDiff_spatialDeriv_smooth hψ j
  have hdψc : ∀ j, HasCompactSupport fun x => fderiv ℝ ψ x (CKN.basisVec j) := fun j =>
    hψc.fderiv_apply (𝕜 := ℝ) (CKN.basisVec j)
  have hΔ : ContDiff ℝ (⊤ : ℕ∞) (CKN.spatialLaplacian ψ) := CKN.contDiff_spatialLaplacian_smooth hψ
  have hΔc : HasCompactSupport (CKN.spatialLaplacian ψ) :=
    CKN.hasCompactSupport_spatialLaplacian hψc
  have hdelta : ∀ n, ∑ j : Fin 3, ∫ x, leConv (leMol n) (fun y => D y k j) x *
      (leConv (leMol n) (fun y => u y k) x * fderiv ℝ ψ x (CKN.basisVec j)) =
      -(1 / 2) * ∫ x, leConv (leMol n) (fun y => u y k) x *
        (leConv (leMol n) (fun y => u y k) x * CKN.spatialLaplacian ψ x) := by
    intro n
    have hw := leConv_leMol_contDiff (hu k) n
    have hderiv : ∀ j x, leConv (leMol n) (fun y => D y k j) x =
        fderiv ℝ (leConv (leMol n) (fun y => u y k)) x (CKN.basisVec j) :=
      fun j x => by
        rw [fderiv_leConv (leMol_contDiff n) (leMol_hasCompactSupport n) (hu k) x j,
          leConv_spatialDeriv_leMol (hu k) (hD k j) (hweak k j) n x]
    have hj : ∀ j, ∫ x, leConv (leMol n) (fun y => D y k j) x *
        (leConv (leMol n) (fun y => u y k) x * fderiv ℝ ψ x (CKN.basisVec j)) =
          -(1 / 2) * ∫ x, leConv (leMol n) (fun y => u y k) x ^ 2 *
          fderiv ℝ (fun y => fderiv ℝ ψ y (CKN.basisVec j)) x (CKN.basisVec j) := by
      intro j
      rw [integral_sq_mul_fderiv hw ((hdψ j).of_le (by simp)) (hdψc j) j, ← integral_neg,
        ← integral_const_mul]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only
      rw [hderiv j x]
      ring
    simp_rw [hj]
    have hint : ∀ j, Integrable fun x => leConv (leMol n) (fun y => u y k) x ^ 2 *
        fderiv ℝ (fun y => fderiv ℝ ψ y (CKN.basisVec j)) x (CKN.basisVec j) := fun j =>
      integrable_mul_of_hasCompactSupport_right (hw.continuous.pow 2)
        (CKN.contDiff_spatialDeriv_smooth (hdψ j) j).continuous
        (CKN.hasCompactSupport_spatialDeriv (hdψc j) j)
    rw [← Finset.mul_sum, ← integral_finsetSum _ fun j _ => hint j]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [CKN.spatialLaplacian, CKN.spatialDeriv, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [sq, mul_assoc]; rfl
  have hL : Tendsto (fun n => ∑ j : Fin 3, ∫ x, leConv (leMol n) (fun y => D y k j) x *
      (leConv (leMol n) (fun y => u y k) x * fderiv ℝ ψ x (CKN.basisVec j))) atTop
      (𝓝 (∑ j : Fin 3, ∫ x, D x k j * (u x k * fderiv ℝ ψ x (CKN.basisVec j)))) :=
    tendsto_finsetSum _ fun j _ => tendsto_integral_leConv_mul (hD k j)
      (fun n => memLp_mul_compact (memLp_leConv_leMol (hu k) n) (hdψ j).continuous (hdψc j))
      (memLp_mul_compact (hu k) (hdψ j).continuous (hdψc j))
      (tendsto_mul_leConv_leMol (hu k) (hdψ j).continuous (hdψc j))
  have hR : Tendsto (fun n => -(1 / 2) * ∫ x, leConv (leMol n) (fun y => u y k) x *
      (leConv (leMol n) (fun y => u y k) x * CKN.spatialLaplacian ψ x)) atTop
      (𝓝 (-(1 / 2) * ∫ x, u x k * (u x k * CKN.spatialLaplacian ψ x))) :=
    (tendsto_integral_leConv_mul (hu k)
      (fun n => memLp_mul_compact (memLp_leConv_leMol (hu k) n) hΔ.continuous hΔc)
      (memLp_mul_compact (hu k) hΔ.continuous hΔc)
      (tendsto_mul_leConv_leMol (hu k) hΔ.continuous hΔc)).const_mul _
  simp_rw [hdelta] at hL
  exact tendsto_nhds_unique hL hR

include hu hD hweak in
/-- The transport identity `∑ⱼ ∫ D_kj u_k Vⱼ ψ = -½ ∫ u_k² V·∇ψ` for a
divergence-free `C¹` field `V`. -/
theorem sum_integral_transport_eq {V : Vec3 → Vec3} (hV : ∀ j, ContDiff ℝ 1 fun x => V x j)
    (hdiv : ∀ x, ∑ j : Fin 3, fderiv ℝ (fun y => V y j) x (CKN.basisVec j) = 0)
    {ψ : Vec3 → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ) (k : Fin 3) :
    ∑ j : Fin 3, ∫ x, D x k j * (u x k * (V x j * ψ x)) =
      -(1 / 2) * ∫ x, u x k * (u x k * ∑ j : Fin 3, V x j * fderiv ℝ ψ x (CKN.basisVec j)) := by
  have hg : ∀ j, ContDiff ℝ 1 fun x => V x j * ψ x := fun j => (hV j).mul (hψ.of_le (by simp))
  have hgc : ∀ j, HasCompactSupport fun x => V x j * ψ x := fun j => hψc.mul_left
  have hdψ : ∀ j, Continuous fun x => fderiv ℝ ψ x (CKN.basisVec j) := fun j =>
    (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hh : Continuous fun x => ∑ j : Fin 3, V x j * fderiv ℝ ψ x (CKN.basisVec j) :=
    continuous_finsetSum _ fun j _ => (hV j).continuous.mul (hdψ j)
  have hhc : HasCompactSupport fun x => ∑ j : Fin 3, V x j * fderiv ℝ ψ x (CKN.basisVec j) := by
    refine HasCompactSupport.intro hψc (fun x hx => ?_)
    have h0 : fderiv ℝ ψ x = 0 := by
      by_contra h
      exact hx (support_fderiv_subset ℝ h)
    simp [h0]
  have hgd : ∀ j x, fderiv ℝ (fun y => V y j * ψ y) x (CKN.basisVec j) =
      fderiv ℝ (fun y => V y j) x (CKN.basisVec j) * ψ x +
        V x j * fderiv ℝ ψ x (CKN.basisVec j) := by
    intro j x
    have hd : HasFDerivAt (fun y => V y j * ψ y)
        (V x j • fderiv ℝ ψ x + ψ x • fderiv ℝ (fun y => V y j) x) x :=
      (((hV j).differentiable (by simp)) x).hasFDerivAt.mul
        ((hψ.differentiable (by simp)) x).hasFDerivAt
    rw [hd.fderiv]
    simp only [add_apply, smul_apply, smul_eq_mul]
    ring
  have hdelta : ∀ n, ∑ j : Fin 3, ∫ x, leConv (leMol n) (fun y => D y k j) x *
      (leConv (leMol n) (fun y => u y k) x * (V x j * ψ x)) =
      -(1 / 2) * ∫ x, leConv (leMol n) (fun y => u y k) x *
        (leConv (leMol n) (fun y => u y k) x *
          ∑ j : Fin 3, V x j * fderiv ℝ ψ x (CKN.basisVec j)) := by
    intro n
    have hw := leConv_leMol_contDiff (hu k) n
    have hderiv : ∀ j x, leConv (leMol n) (fun y => D y k j) x =
        fderiv ℝ (leConv (leMol n) (fun y => u y k)) x (CKN.basisVec j) :=
      fun j x => by
        rw [fderiv_leConv (leMol_contDiff n) (leMol_hasCompactSupport n) (hu k) x j,
          leConv_spatialDeriv_leMol (hu k) (hD k j) (hweak k j) n x]
    have hj : ∀ j, ∫ x, leConv (leMol n) (fun y => D y k j) x *
        (leConv (leMol n) (fun y => u y k) x * (V x j * ψ x)) =
          -(1 / 2) * ∫ x, leConv (leMol n) (fun y => u y k) x ^ 2 *
            fderiv ℝ (fun y => V y j * ψ y) x (CKN.basisVec j) := by
      intro j
      rw [integral_sq_mul_fderiv hw (hg j) (hgc j) j, ← integral_neg, ← integral_const_mul]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only
      rw [hderiv j x]
      ring
    have hint : ∀ j, Integrable fun x => leConv (leMol n) (fun y => u y k) x ^ 2 *
        fderiv ℝ (fun y => V y j * ψ y) x (CKN.basisVec j) := fun j =>
      integrable_mul_of_hasCompactSupport_right (hw.continuous.pow 2)
        (((hg j).continuous_fderiv (by simp)).clm_apply continuous_const)
        ((hgc j).fderiv_apply (𝕜 := ℝ) (CKN.basisVec j))
    simp_rw [hj]
    rw [← Finset.mul_sum, ← integral_finsetSum _ fun j _ => hint j]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [hgd, ← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.sum_mul, hdiv x, zero_mul,
      zero_add]
    ring
  have hL : Tendsto (fun n => ∑ j : Fin 3, ∫ x, leConv (leMol n) (fun y => D y k j) x *
      (leConv (leMol n) (fun y => u y k) x * (V x j * ψ x))) atTop
      (𝓝 (∑ j : Fin 3, ∫ x, D x k j * (u x k * (V x j * ψ x)))) :=
    tendsto_finsetSum _ fun j _ => tendsto_integral_leConv_mul (hD k j)
      (fun n => memLp_mul_compact (memLp_leConv_leMol (hu k) n) (hg j).continuous (hgc j))
      (memLp_mul_compact (hu k) (hg j).continuous (hgc j))
      (tendsto_mul_leConv_leMol (hu k) (hg j).continuous (hgc j))
  have hR := (tendsto_integral_leConv_mul (hu k)
      (fun n => memLp_mul_compact (memLp_leConv_leMol (hu k) n) hh hhc)
      (memLp_mul_compact (hu k) hh hhc)
      (tendsto_mul_leConv_leMol (hu k) hh hhc)).const_mul (-(1 / 2 : ℝ))
  simp_rw [hdelta] at hL
  exact tendsto_nhds_unique hL hR

end Identities

end CKN.Leray

end
