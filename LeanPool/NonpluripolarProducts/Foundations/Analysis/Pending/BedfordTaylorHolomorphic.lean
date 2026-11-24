/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.BedfordTaylorGauge
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.HolomorphicMixedDensity

/-!
# Holomorphic covariance of Bedford–Taylor limits

Let `τ : A → B` be a biholomorphism between open sets with inverse `σ`. If `μ`
is the Bedford–Taylor limit of a tuple `u` on `B`, then the push-forward of
`μ|_B` under `σ` is the Bedford–Taylor limit of `u ∘ τ` on `A`: approximations
pull back to approximations, `MA(f ∘ τ) = |det J_τ|² MA(f) ∘ τ`, and the change
of variables formula turns the tests on `A` into tests on `B`.
-/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ContDiff ComplexOrder

namespace SGPT.Foundations.Analysis.Pending.BedfordTaylor

open FirstPass FirstPass.MongeAmpere FirstPass.MixedMongeAmpere HolomorphicMixedDensity

variable {n : ℕ}

/-- A biholomorphism between two open sets, given by mutually inverse maps. -/
structure IsBiholomorphicPair (A B : Opens (ComplexModel n))
    (τ σ : ComplexModel n → ComplexModel n) : Prop where
  holo : ContDiffOn ℂ ∞ τ A
  holo_inv : ContDiffOn ℂ ∞ σ B
  mapsTo : MapsTo τ A B
  mapsTo_inv : MapsTo σ B A
  left_inv : ∀ x ∈ A, σ (τ x) = x
  right_inv : ∀ w ∈ B, τ (σ w) = w

namespace IsBiholomorphicPair

variable {A B : Opens (ComplexModel n)} {τ σ : ComplexModel n → ComplexModel n}

theorem image_eq (h : IsBiholomorphicPair A B τ σ) {U : Set (ComplexModel n)} (hUA : U ⊆ A) :
    τ '' U = (B : Set (ComplexModel n)) ∩ σ ⁻¹' U := by
  ext w
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨h.mapsTo (hUA hx), by simpa [h.left_inv x (hUA hx)] using hx⟩
  · rintro ⟨hwB, hw⟩
    exact ⟨σ w, hw, h.right_inv w hwB⟩

theorem preimage_inter_subset_image (h : IsBiholomorphicPair A B τ σ) (K : Set (ComplexModel n)) :
    (B : Set (ComplexModel n)) ∩ σ ⁻¹' K ⊆ τ '' K := fun w hw ↦ ⟨σ w, hw.2, h.right_inv w hw.1⟩

end IsBiholomorphicPair

/-- **Holomorphic covariance of Bedford–Taylor limits.** -/
theorem IsBTLimit.comp_biholomorphic {A B : Opens (ComplexModel n)}
    {τ σ : ComplexModel n → ComplexModel n} (h : IsBiholomorphicPair A B τ σ)
    {u : Fin n → ComplexModel n → ℝ} {μ : Measure (ComplexModel n)} (hμ : IsBTLimit B u μ) :
    IsBTLimit A (fun i x ↦ u i (τ x)) ((μ.restrict B).map σ) := by
  classical
  have h2 : (2 : WithTop ℕ∞) ≤ ∞ := ENat.natCast_le_of_coe_top_le_withTop le_rfl 2
  have hτc : ContinuousOn τ A := h.holo.continuousOn
  have hσc : ContinuousOn σ B := h.holo_inv.continuousOn
  have hσm : AEMeasurable σ (μ.restrict B) := hσc.aemeasurable B.isOpen.measurableSet
  have hmap (E : Set (ComplexModel n)) (hE : MeasurableSet E) :
      (μ.restrict B).map σ E = μ (σ ⁻¹' E ∩ B) := by
    rw [Measure.map_apply_of_aemeasurable hσm hE,
      Measure.restrict_apply' B.isOpen.measurableSet]
  refine ⟨?_, fun K hK hKA ↦ ?_, fun U hU ↦ ?_⟩
  · rw [hmap _ A.isOpen.measurableSet.compl]
    have : σ ⁻¹' (A : Set (ComplexModel n))ᶜ ∩ B = ∅ :=
      eq_empty_of_forall_notMem fun w hw ↦ hw.1 (h.mapsTo_inv hw.2)
    rw [this, measure_empty]
  · rw [hmap K hK.measurableSet]
    have hcpt : IsCompact (τ '' K) := hK.image_of_continuousOn (hτc.mono hKA)
    have hsub : σ ⁻¹' K ∩ (B : Set (ComplexModel n)) ⊆ τ '' K :=
      fun w hw => h.preimage_inter_subset_image K ⟨hw.2, hw.1⟩
    exact (measure_mono hsub).trans_lt
      (hμ.2.1 _ hcpt fun w ⟨x, hx, hxw⟩ ↦ hxw ▸ h.mapsTo (hKA hx))
  -- the image of a relatively compact subset
  have hUA : (U : Set (ComplexModel n)) ⊆ A := subset_closure.trans hU.2
  set V : Opens (ComplexModel n) :=
    ⟨B ∩ σ ⁻¹' U, hσc.isOpen_inter_preimage B.isOpen U.isOpen⟩ with hV_def
  have hVimg : (V : Set (ComplexModel n)) = τ '' U := (h.image_eq hUA).symm
  have hclcpt : IsCompact (τ '' closure (U : Set (ComplexModel n))) :=
    hU.1.image_of_continuousOn (hτc.mono hU.2)
  have hVrc : RelativelyCompactIn V B := by
    have hcl : closure (V : Set (ComplexModel n)) ⊆ τ '' closure (U : Set (ComplexModel n)) :=
      closure_minimal (hVimg ▸ image_mono subset_closure) hclcpt.isClosed
    exact ⟨hclcpt.of_isClosed_subset isClosed_closure hcl,
      hcl.trans fun w ⟨x, hx, hxw⟩ ↦ hxw ▸ h.mapsTo (hU.2 hx)⟩
  have hτUV : MapsTo τ U V := fun x hx ↦ hVimg ▸ mem_image_of_mem τ hx
  obtain ⟨F, hF, hFT⟩ := hμ.2.2 V hVrc
  have hFs (i : Fin n) (k : ℕ) : IsSmoothPsdOn V (F i k) := (hF.1 i).1 k
  have hτU : ContDiffOn ℂ ∞ τ U := h.holo.mono hUA
  refine ⟨fun i k x ↦ F i k (τ x), ⟨fun i ↦ ⟨fun k ↦ ⟨?_, fun x hx ↦ ?_⟩, fun x hx ↦ ?_,
    fun x hx ↦ ?_, fun K hK hKU ↦ ?_⟩, fun i hi ↦ absurd i.isLt (not_lt.mpr hi)⟩,
    fun φ hφ hφc hφU ↦ ?_⟩
  · exact (hFs i k).1.comp (hτU.restrict_scalars ℝ) hτUV
  · rw [complexHessian_comp_holomorphic U.isOpen V.isOpen hτU (hFs i k).1 hτUV hx]
    have hJ : (jacobianMatrix τ x).transpose =
        ((jacobianMatrix τ x).map (starRingEnd ℂ)).conjTranspose := by
      ext a b; simp [Matrix.conjTranspose_apply]
    rw [hJ]
    exact ((hFs i k).2 _ (hτUV hx)).conjTranspose_mul_mul_same _
  · exact (hF.1 i).2.1 _ (hτUV hx)
  · exact (hF.1 i).2.2.1 _ (hτUV hx)
  · have hcpt : IsCompact (τ '' K) := hK.image_of_continuousOn (hτc.mono (hKU.trans hUA))
    obtain ⟨m, hm⟩ := (hF.1 i).2.2.2 _ hcpt (image_mono hKU |>.trans hVimg.symm.subset)
    exact ⟨m, by rintro _ ⟨x, hx, rfl⟩; exact hm ⟨τ x, mem_image_of_mem τ hx, rfl⟩⟩
  -- the test transported to `B`
  set ψ : ComplexModel n → ℝ := (B : Set (ComplexModel n)).indicator (fun w ↦ φ (σ w)) with hψ_def
  have hKψ : IsCompact (τ '' tsupport φ) := hφc.image_of_continuousOn (hτc.mono (hφU.trans hUA))
  have hψ0 : ∀ w ∉ τ '' tsupport φ, ψ w = 0 := by
    intro w hw
    by_cases hwB : w ∈ (B : Set (ComplexModel n))
    · rw [hψ_def, indicator_of_mem hwB]
      exact image_eq_zero_of_notMem_tsupport fun hs ↦ hw ⟨σ w, hs, h.right_inv w hwB⟩
    · rw [hψ_def, indicator_of_notMem hwB]
  have hKψV : τ '' tsupport φ ⊆ V := (image_mono hφU).trans hVimg.symm.subset
  have hψc : Continuous ψ := by
    refine continuous_of_continuousOn_of_eq_zero B.isOpen hKψ.isClosed
      (hKψV.trans fun w hw ↦ hw.1) ?_ hψ0
    refine (hφ.comp_continuousOn hσc).congr fun w hw ↦ ?_
    simp [hψ_def, indicator_of_mem hw]
  have hψsupp : tsupport ψ ⊆ τ '' tsupport φ :=
    closure_minimal (fun w hw ↦ by_contra fun h' ↦ hw (hψ0 w h')) hKψ.isClosed
  have hψcs : HasCompactSupport ψ := hKψ.of_isClosed_subset (isClosed_tsupport _) hψsupp
  have hlim := hFT ψ hψc hψcs (hψsupp.trans hKψV)
  have hR : ∫ w, ψ w ∂μ = ∫ x, φ x ∂((μ.restrict B).map σ) := by
    rw [integral_map hσm hφ.aestronglyMeasurable]
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := (B : Set (ComplexModel n)))
      fun w hw ↦ by simp [hψ_def, indicator_of_notMem hw]]
    exact setIntegral_congr_fun B.isOpen.measurableSet fun w hw ↦ by
      simp [hψ_def, indicator_of_mem hw]
  rw [← hR]
  refine hlim.congr fun k ↦ ?_
  -- change of variables
  have hderiv : ∀ x ∈ (U : Set (ComplexModel n)),
      HasFDerivWithinAt τ (fderiv ℝ τ x) (U : Set (ComplexModel n)) x := fun x hx ↦
    ((((hτU.restrict_scalars ℝ) x hx).contDiffAt (U.isOpen.mem_nhds hx)).differentiableAt
      (by simp)).hasFDerivAt.hasFDerivWithinAt
  have hinj : InjOn τ U := fun x hx y hy hxy ↦ by
    rw [← h.left_inv x (hUA hx), ← h.left_inv y (hUA hy), hxy]
  have hcov := integral_image_eq_integral_abs_det_fderiv_smul volume U.isOpen.measurableSet
    hderiv hinj (fun w ↦ ψ w * mixedDensity (fun i ↦ F i k) w)
  have hL : ∫ w, ψ w * mixedDensity (fun i ↦ F i k) w =
      ∫ w in τ '' U, ψ w * mixedDensity (fun i ↦ F i k) w :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero fun w hw ↦ by
      rw [hψ0 w fun hw' ↦ hw (image_mono hφU hw'), zero_mul]).symm
  have hRHS : ∫ z, φ z * mixedDensity (fun i x ↦ F i k (τ x)) z =
      ∫ z in U, φ z * mixedDensity (fun i x ↦ F i k (τ x)) z :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ by
      rw [image_eq_zero_of_notMem_tsupport fun h' ↦ hx (hφU h'), zero_mul]).symm
  change ∫ z, ψ z * mixedDensity (fun i ↦ F i k) z =
    ∫ z, φ z * mixedDensity (fun i x ↦ F i k (τ x)) z
  rw [hL, hcov, hRHS]
  refine setIntegral_congr_fun U.isOpen.measurableSet fun x hx ↦ ?_
  have hFy : DifferentiableAt ℂ τ x :=
    ((hτU x hx).contDiffAt (U.isOpen.mem_nhds hx)).differentiableAt (by simp)
  have hψx : ψ (τ x) = φ x := by
    rw [hψ_def, indicator_of_mem (h.mapsTo (hUA hx)), h.left_inv x (hUA hx)]
  rw [det_fderiv_eq_normSq hFy, abs_of_nonneg (Complex.normSq_nonneg _), hψx,
    mixedDensity_comp_holomorphic U.isOpen V.isOpen hτU (fun i ↦ (hFs i k).1) hτUV hx,
    smul_eq_mul]
  ring

end SGPT.Foundations.Analysis.Pending.BedfordTaylor
