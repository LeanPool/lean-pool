/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.StabilitySliceGradientCommon
public import LeanPool.CaffarelliKohnNirenberg.Leray.StabilitySliceZero
public import LeanPool.CaffarelliKohnNirenberg.Leray.StabilityWeakSetIntegral
public import LeanPool.CaffarelliKohnNirenberg.Statements.SuitableWeakSolution
public import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-!
# Stability Weak Gradient Product

Supporting estimates for the Navier–Stokes development.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal
open CKN CKN.Foundation.Parabolic
noncomputable section

namespace CKN

/-- Weak `L²` convergence of a spatial derivative and strong `L³`
convergence of its primitive preserve the almost-every-time weak derivative
identity on a local box. -/
theorem stability_weak_partial_on_localBox_of_product_limits
    {Ω : Set Vec3} {J : Set ℝ} (hΩ : IsOpen Ω)
    (hΩfinite : (volume : Measure Vec3) Ω < ⊤)
    (hJfinite : (volume : Measure ℝ) J < ⊤)
    (U D : ℕ → Vec3 × ℝ → ℝ)
    (u d : Vec3 × ℝ → ℝ) (j : Fin 3)
    (hU : ∀ n, MemLp (U n) 3
      ((volume.restrict Ω).prod (volume.restrict J)))
    (hD : ∀ n, MemLp (D n) 2
      ((volume.restrict Ω).prod (volume.restrict J)))
    (hd : MemLp d 2 ((volume.restrict Ω).prod (volume.restrict J)))
    (hUconv : Tendsto (fun n => eLpNorm (U n - u) 3
      ((volume.restrict Ω).prod (volume.restrict J))) atTop (nhds 0))
    (hDweak : ∀ w : Vec3 × ℝ → ℝ,
      MemLp w 2 ((volume.restrict Ω).prod (volume.restrict J)) →
      Tendsto (fun n => ∫ z, D n z * w z
        ∂(volume.restrict Ω).prod (volume.restrict J)) atTop
        (nhds (∫ z, d z * w z
          ∂(volume.restrict Ω).prod (volume.restrict J))))
    (hgrad : ∀ n, ∀ᵐ t ∂(volume.restrict J),
      HasWeakPartialDerivOn Ω j (fun x => U n (x, t))
        (fun x => D n (x, t))) :
    ∀ᵐ t ∂(volume.restrict J),
      HasWeakPartialDerivOn Ω j (fun x => u (x, t))
        (fun x => d (x, t)) := by
  let μ : Measure Vec3 := volume.restrict Ω
  let ν : Measure ℝ := volume.restrict J
  let ρ : Measure (Vec3 × ℝ) := μ.prod ν
  let _ : IsFiniteMeasure μ := by
    exact isFiniteMeasure_restrict.mpr hΩfinite.ne
  let _ : IsFiniteMeasure ν := by
    exact isFiniteMeasure_restrict.mpr hJfinite.ne
  let _ : IsFiniteMeasure ρ := inferInstance
  have hu : MemLp u 3 ρ :=
    Lp.memLp_of_cauchy_tendsto (by norm_num) hU u hUconv
  have hUi (n : ℕ) : Integrable (U n) ρ :=
    memLp_one_iff_integrable.mp ((hU n).mono_exponent (by norm_num))
  have hDi (n : ℕ) : Integrable (D n) ρ :=
    memLp_one_iff_integrable.mp ((hD n).mono_exponent (by norm_num))
  have hui : Integrable u ρ :=
    memLp_one_iff_integrable.mp (hu.mono_exponent (by norm_num))
  have hdi : Integrable d ρ :=
    memLp_one_iff_integrable.mp (hd.mono_exponent (by norm_num))
  have hloc : ∀ᵐ t ∂ν,
      LocallyIntegrableOn (fun x : Vec3 => u (x, t)) Ω volume ∧
      LocallyIntegrableOn (fun x : Vec3 => d (x, t)) Ω volume := by
    filter_upwards [hui.prod_left_ae, hdi.prod_left_ae] with t hut hdt
    exact ⟨(show IntegrableOn (fun x => u (x, t)) Ω volume from hut).locallyIntegrableOn,
      (show IntegrableOn (fun x => d (x, t)) Ω volume from hdt).locallyIntegrableOn⟩
  refine stability_ae_slice_weak_partial_of_forall_test hΩ j hloc ?_
  intro ψ hψ hψc hψΩ
  have hψcont : Continuous ψ := hψ.continuous
  let dψ : Vec3 → ℝ := fun x => (fderiv ℝ ψ x) (basisVec j)
  have hdψcont : Continuous dψ :=
    (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdψc : HasCompactSupport dψ :=
    hψc.mono' (subset_closure.trans
      (tsupport_fderiv_apply_subset ℝ (basisVec j)))
  obtain ⟨Cψ, hCψ⟩ := hψc.exists_bound_of_continuous hψcont
  obtain ⟨Cdψ, hCdψ⟩ := hdψc.exists_bound_of_continuous hdψcont
  have hψTop : MemLp (fun z : Vec3 × ℝ => ψ z.1) ∞ ρ :=
    memLp_top_of_bound (hψcont.comp continuous_fst).aestronglyMeasurable Cψ
      (Eventually.of_forall fun z => hCψ z.1)
  have hdψTop : MemLp (fun z : Vec3 × ℝ => dψ z.1) ∞ ρ :=
    memLp_top_of_bound (hdψcont.comp continuous_fst).aestronglyMeasurable Cdψ
      (Eventually.of_forall fun z => hCdψ z.1)
  have hmulProd {f φ : Vec3 × ℝ → ℝ}
      (hf : Integrable f ρ) (hφ : MemLp φ ∞ ρ) :
      Integrable (fun z => f z * φ z) ρ := by
    have heq : f * φ = (fun z => f z * φ z) := by
      funext z
      rfl
    rw [← heq]
    exact hf.mul_of_top_left hφ
  have hmulSpatial {f φ : Vec3 → ℝ}
      (hf : Integrable f μ) (hφ : MemLp φ ∞ μ) :
      Integrable (fun z => f z * φ z) μ := by
    have heq : f * φ = (fun z => f z * φ z) := by
      funext z
      rfl
    rw [← heq]
    exact hf.mul_of_top_left hφ
  let F : ℕ → Vec3 × ℝ → ℝ := fun n z =>
    U n z * dψ z.1 + D n z * ψ z.1
  let G : Vec3 × ℝ → ℝ := fun z => u z * dψ z.1 + d z * ψ z.1
  have hFi (n : ℕ) : Integrable (F n) ρ := by
    have h1 : Integrable (fun z => U n z * dψ z.1) ρ := by
      exact hmulProd (hUi n) hdψTop
    have h2 : Integrable (fun z => D n z * ψ z.1) ρ := by
      exact hmulProd (hDi n) hψTop
    exact h1.add h2
  have hGi : Integrable G ρ := by
    have h1 : Integrable (fun z => u z * dψ z.1) ρ := by
      exact hmulProd hui hdψTop
    have h2 : Integrable (fun z => d z * ψ z.1) ρ := by
      exact hmulProd hdi hψTop
    exact h1.add h2
  have hzero (n : ℕ) : ∀ᵐ t ∂ν, ∫ x, F n (x, t) ∂μ = 0 := by
    filter_upwards [hgrad n, (hUi n).prod_left_ae, (hDi n).prod_left_ae]
      with t ht hUt hDt
    have hδψ : IntegrableOn (fun x : Vec3 => U n (x, t) * dψ x) Ω volume := by
      have h : Integrable (fun x : Vec3 => U n (x, t)) μ := hUt
      exact hmulSpatial h
        (memLp_top_of_bound hdψcont.aestronglyMeasurable Cdψ
          (Eventually.of_forall hCdψ))
    have hψD : IntegrableOn (fun x : Vec3 => D n (x, t) * ψ x) Ω volume := by
      have h : Integrable (fun x : Vec3 => D n (x, t)) μ := hDt
      exact hmulSpatial h
        (memLp_top_of_bound hψcont.aestronglyMeasurable Cψ
          (Eventually.of_forall hCψ))
    change ∫ x in Ω, U n (x, t) * dψ x + D n (x, t) * ψ x = 0
    rw [integral_add hδψ hψD]
    have hweak := ht ψ hψ hψc hψΩ
    change (∫ x in Ω, U n (x, t) * dψ x) =
      -(∫ x in Ω, D n (x, t) * ψ x) at hweak
    rw [hweak]
    exact neg_add_cancel _
  have hconv : ∀ s : Set ℝ, MeasurableSet s → ν s < ⊤ →
      Tendsto (fun n => ∫ z in (univ : Set Vec3) ×ˢ s, F n z ∂ρ)
        atTop (nhds (∫ z in (univ : Set Vec3) ×ˢ s, G z ∂ρ)) := by
    intro s hs _
    let S : Set (Vec3 × ℝ) := univ ×ˢ s
    have hS : MeasurableSet S := MeasurableSet.univ.prod hs
    have hvc := stability_tendsto_setIntegral_mul_test_of_Lthree
      ρ U u (fun z => dψ z.1) S hU hdψTop hS hUconv
    have hgc := stability_tendsto_setIntegral_mul_test_of_weak_Ltwo
      ρ D d (fun z => ψ z.1) S hψTop hS hDweak
    have hsum := hvc.add hgc
    have heqFn (n : ℕ) :
        (∫ z in S, F n z ∂ρ) =
          (∫ z in S, dψ z.1 * U n z ∂ρ) +
          (∫ z in S, D n z * ψ z.1 ∂ρ) := by
      change (∫ z in S, U n z * dψ z.1 + D n z * ψ z.1 ∂ρ) = _
      have h1 : IntegrableOn (fun z => U n z * dψ z.1) S ρ := by
        exact (hmulProd (hUi n) hdψTop).integrableOn
      have h2 : IntegrableOn (fun z => D n z * ψ z.1) S ρ := by
        exact (hmulProd (hDi n) hψTop).integrableOn
      rw [integral_add h1 h2]
      congr 1
      apply integral_congr_ae
      filter_upwards [] with z
      ring
    have heqG :
        (∫ z in S, G z ∂ρ) =
          (∫ z in S, dψ z.1 * u z ∂ρ) +
          (∫ z in S, d z * ψ z.1 ∂ρ) := by
      change (∫ z in S, u z * dψ z.1 + d z * ψ z.1 ∂ρ) = _
      have h1 : IntegrableOn (fun z => u z * dψ z.1) S ρ := by
        exact (hmulProd hui hdψTop).integrableOn
      have h2 : IntegrableOn (fun z => d z * ψ z.1) S ρ := by
        exact (hmulProd hdi hψTop).integrableOn
      rw [integral_add h1 h2]
      congr 1
      apply integral_congr_ae
      filter_upwards [] with z
      ring
    change Tendsto (fun n => ∫ z in S, F n z ∂ρ) atTop
      (nhds (∫ z in S, G z ∂ρ))
    simpa only [heqFn, heqG] using hsum
  exact stability_ae_slice_integral_zero_of_setIntegral_tendsto
    μ ν F G hFi hGi hzero hconv

end CKN
