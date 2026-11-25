/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.LocalCurrentPullbackDdc
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.LocalBedfordTaylorSmoothProductDensity

/-!
# Covariance of smooth local products

Describes coordinate changes of Bedford–Taylor products for smooth potentials.
-/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions ENNReal ContDiff

namespace SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorSmoothCovariance

open FirstPass FirstPass.MongeAmpere StronglyPositiveForms LocalProductCurrents
  LocalBedfordTaylorProducts LocalBedfordTaylorSmooth LocalBedfordTaylorForms
  LocalCurrentLebesgue ConstantFormProducts TopDegreeDensity ProductTestForms
  LocalBedfordTaylorSmoothDensity LocalBedfordTaylorSmoothProductDensity
  LocalCurrentPullback LocalCurrentPullbackDdc BedfordTaylor
  LocalBedfordTaylorLocality LocalBedfordTaylorCollar

variable {n r k : ℕ} {A B : Opens (ComplexModel n)}
  {τ σ : ComplexModel n → ComplexModel n}
variable (hdeg : r + k = n)

/-- Full complementary-test covariance for a genuine smooth positive form. -/
theorem pullback_wedgeForm_apply (h : IsBiholomorphicPair A B τ σ)
    {α : ComplexModel n → RealForm n (2 * k)} (hα : ContDiffOn ℝ ∞ α B)
    (hαp : ∀ y ∈ B, α y ∈ spCone k) (γ : formSpan n r) (φ : 𝓓(A, ℝ)) :
    pullback h (isPositive_wedgeForm hdeg isPositive_oneCurrent hα hαp) γ φ =
      ∫ x, φ x * topDensity (wedgeTo (by omega : 2 * r + 2 * k = 2 * n)
        γ ((α (τ x)).compContinuousLinearMap ((fderiv ℂ τ x).restrictScalars ℝ))) := by
  exact pullback_apply_of_positive_form hdeg h _ hα.continuousOn hαp
    (wedgeForm_oneCurrent_apply hdeg hα
      (fun y hy => mem_formSpan_of_mem_spCone (hαp y hy))) γ φ

private theorem wedgeProd_positive : ∀ (q : ℕ) (β : Fin q → RealForm n 2),
    (∀ i, IsSemipositiveOneOne (β i)) → wedgeProd q β ∈ spCone q
  | 0, _, _ => unit_mem_spCone
  | q + 1, β, hβ => wedge_mem_spCone
      (wedgeProd_positive q (fun i => β i.castSucc) (fun i => hβ i.castSucc))
      (hβ (Fin.last q))

private theorem wedgeProd_comp (L : ComplexModel n →L[ℝ] ComplexModel n) :
    ∀ (q : ℕ) (β : Fin q → RealForm n 2),
      (wedgeProd q β).compContinuousLinearMap L =
        wedgeProd q (fun i => (β i).compContinuousLinearMap L)
  | 0, _ => by ext v; rfl
  | q + 1, β => by
    rw [wedgeProd_succ, wedgeProd_succ, coordinateWedge_compContinuousLinearMap,
      wedgeProd_comp L q]

variable {q : ℕ}

/-- The actual recursive smooth product is biholomorphically covariant in every degree. -/
theorem pullback_smooth_btProduct (hdegree : r + q = n)
    (h : IsBiholomorphicPair A B τ σ) {u : Fin q → ComplexModel n → ℝ}
    (hu : ∀ i, ContDiffOn ℝ ∞ (u i) B)
    (hup : ∀ i, PlurisubharmonicOn (fun z => (u i z : EReal)) B) :
    pullback h (isPositive_btProduct q r u (oneCurrentOf hdegree)
      (isPositive_oneCurrentOf hdegree) (isClosedAny_oneCurrentOf hdegree)
      (fun i => isLocallyBoundedPshOn_of_isSmoothPshOn
        (isSmoothPshOn_of_psh (hu i) (hup i)))).1 =
      btProduct q r (fun i x => u i (τ x)) (oneCurrentOf (U := A) hdegree) := by
  have huA (i : Fin q) : ContDiffOn ℝ ∞ (fun x => u i (τ x)) A :=
    (hu i).comp (h.holo.restrict_scalars ℝ) h.mapsTo
  have hpA (i : Fin q) : PlurisubharmonicOn (fun x => (u i (τ x) : EReal)) A :=
    HolomorphicPullback.plurisubharmonicOn_comp_holomorphic A.isOpen
      (h.holo.differentiableOn (by simp)) h.mapsTo (hup i)
  have eB := btProduct_eq_wedgeForm q r u hu hup (oneCurrentOf hdegree)
    (isPositive_oneCurrentOf hdegree) (isClosedAny_oneCurrentOf hdegree)
  have eA := btProduct_eq_wedgeForm q r (fun i x => u i (τ x)) huA hpA
    (oneCurrentOf (U := A) hdegree) (isPositive_oneCurrentOf hdegree)
    (isClosedAny_oneCurrentOf hdegree)
  have eqw {U : Opens (ComplexModel n)}
      {α : ComplexModel n → RealForm n (2 * q)} (hα : ContDiffOn ℝ ∞ α U) :
      wedgeForm rfl (oneCurrentOf (U := U) hdegree) hα =
        wedgeForm hdegree (oneCurrent U) hα := by cases hdegree; rfl
  rw [eqw] at eB eA
  have hpos : ∀ y ∈ B, wedgeProd q (fun i => ddcForm (u i) y) ∈ spCone q :=
    fun y hy => wedgeProd_positive q _ (fun i =>
      isSemipositiveOneOne_smoothDDC (hu i) (hup i) hy)
  have ePB : pullback h (isPositive_btProduct q r u (oneCurrentOf hdegree)
      (isPositive_oneCurrentOf hdegree) (isClosedAny_oneCurrentOf hdegree)
      (fun i => isLocallyBoundedPshOn_of_isSmoothPshOn
        (isSmoothPshOn_of_psh (hu i) (hup i)))).1 =
      pullback h (isPositive_wedgeForm hdegree isPositive_oneCurrent
        (contDiffOn_wedgeProd q (fun i => ddcForm (u i))
          (fun i => contDiffOn_ddcForm (hu i))) hpos) := by
    congr 1
  rw [ePB, eA]
  ext γ φ
  rw [pullback_wedgeForm_apply hdegree h _ hpos,
    wedgeForm_oneCurrent_apply hdegree
      (contDiffOn_wedgeProd q _ (fun i => contDiffOn_ddcForm (huA i)))
      (fun x hx => wedgeProd_mem_formSpan q _ (fun i =>
        ddcForm_mem_formSpan (huA i)
          (fun _ hz v => leviForm_nonneg_of_contDiffOn_plurisubharmonicOn
            (huA i) (hpA i) hz v) x hx))]
  apply integral_congr_ae
  filter_upwards [] with x
  by_cases hx : x ∈ A
  · rw [wedgeProd_comp]
    congr 3
    apply congrArg (wedgeProd q)
    funext i
    have ei := HolomorphicDDC.smoothDDC_comp A.isOpen B.isOpen h.holo (hu i)
      h.mapsTo hx
    rw [fderiv_real_eq h hx] at ei
    exact ei.symm
  · simp [LocalBedfordTaylorLocality.testFunction_eq_zero_of_notMem φ hx]

end SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorSmoothCovariance
