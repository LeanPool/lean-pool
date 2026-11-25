/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.NPP.NonPluripolarCurrentLocality
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.LocalBedfordTaylorBiholomorphicProducts

/-!
# Biholomorphic invariance of the non-pluripolar product of arbitrary degree

Source: `chapter_npp.tex`, `def:npp:L69` (the product on a complex manifold is computed in
holomorphic charts); Xia, *Foundations of pluripotential theory*, the paragraph after
`prop:nonpluripolar-local-calculus` ("They do not depend on the coordinates either": for a
biholomorphism `F`, `F^*(1_E S) = 1_{F^{-1}(E)} F^* S`, `F^* S_k(u) = S_k(u ∘ F)`, and
`F^* ⟨⋀ dd^c u_j⟩ = ⟨⋀ dd^c (u_j ∘ F)⟩` since `F^*` is weakly continuous).

For a biholomorphism `τ : A → B` between open sets of `ℂⁿ` (`BedfordTaylor.IsBiholomorphicPair`)
and the pull-back of positive currents `LocalCurrentPullback.pullback`
(`⟨τ^* T, φ γ⟩ = ⟨T, σ^*(φ γ)⟩`):

* `pullback_mulBorel` — `τ^*(u T) = (u ∘ τ) τ^* T` for a nonnegative locally bounded Borel `u`
  (FPT `cor:order-zero-current-pullback` (2));
* `pullback_truncatedProduct` — `τ^* S_k(φ) = S_k(φ ∘ τ)` for the truncated products;
* `pullback_nonPluripolarProduct` — if the product of `φ₁, …, φ_p` on `B` is well defined, so is
  that of `φ₁ ∘ τ, …, φ_p ∘ τ` on `A`, and `τ^* ⟨⋀ dd^c φⱼ⟩ = ⟨⋀ dd^c (φⱼ ∘ τ)⟩`.

The local statements use the convention at `NonPluripolarCurrent.nonPluripolarProduct`.
A factor may be identically `-∞` on an open component, where the product vanishes.
-/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions ContDiff ENNReal

namespace SGPT.NPP.NonPluripolarCurrent

open SGPT.Foundations.Analysis
open SGPT.Foundations.Analysis.FirstPass
open SGPT.Foundations.Analysis.FirstPass.MongeAmpere
open SGPT.Foundations.Analysis.Pending
open SGPT.Foundations.Analysis.Pending.StronglyPositiveForms
open SGPT.Foundations.Analysis.Pending.LocalProductCurrents
open SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorProducts
open SGPT.Foundations.Analysis.Pending.LocalCurrentLebesgue
open SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorForms
open SGPT.Foundations.Analysis.Pending.LocalCurrentPullback
open SGPT.Foundations.Analysis.Pending.BedfordTaylor (IsBiholomorphicPair)

attribute [local instance] addCommGroupFormSpan

variable {n : ℕ}

section Pullback

variable {A B : Opens (ComplexModel n)} {τ σ : (ComplexModel n) → (ComplexModel n)} {q : ℕ}

theorem pullback_congr_current (h : IsBiholomorphicPair A B τ σ) {T T' : LocalProductCurrent n B q}
    (hT : IsPositive T) (hT' : IsPositive T') (e : T = T') : pullback h hT = pullback h hT' :=
  pullback_congr h hT hT' e

theorem measurable_indicator_comp (h : IsBiholomorphicPair A B τ σ) {u : (ComplexModel n) → ℝ}
    (hu : Measurable u) : Measurable ((A : Set (ComplexModel n)).indicator fun x => u (τ x)) := by
  have hm : Measurable ((A : Set (ComplexModel n)).indicator fun x => u (onOpen A τ x)) :=
    (hu.comp (measurable_onOpen h.holo.continuousOn)).indicator A.isOpen.measurableSet
  convert hm using 1
  funext x
  by_cases hx : x ∈ (A : Set (ComplexModel n))
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, onOpen_of_mem hx]
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]

theorem isLocallyBoundedOn_indicator_comp (h : IsBiholomorphicPair A B τ σ) {u : (ComplexModel n)
    → ℝ}
    (hub : IsLocallyBoundedOn u B) : IsLocallyBoundedOn ((A : Set (ComplexModel n)).indicator fun
      x => u (τ x)) A := by
  intro K hK hKA
  have hτK : IsCompact (τ '' K) := hK.image_of_continuousOn (h.holo.continuousOn.mono hKA)
  obtain ⟨M, hM⟩ := hub _ hτK (image_subset_iff.mpr fun x hx => h.mapsTo (hKA hx))
  exact ⟨M, fun x hx => by
    rw [Set.indicator_of_mem (hKA hx)]
    exact hM _ (mem_image_of_mem τ hx)⟩

/-- **`τ^*(u T) = (u ∘ τ) τ^* T`** for a positive current `T` on `B` and a nonnegative Borel
function `u` bounded on the compact subsets of `B`. -/
theorem pullback_mulBorel (h : IsBiholomorphicPair A B τ σ) {T : LocalProductCurrent n B q}
    (hT : IsPositive T) {u : (ComplexModel n) → ℝ} (hu : Measurable u) (hub : IsLocallyBoundedOn u
      B)
    (hu0 : ∀ x, 0 ≤ u x) :
    pullback h (BedfordTaylorTopDegree.isPositive_mulBorel_of_nonneg hT hu hub hu0) =
      mulBorel (pullback h hT) ((A : Set (ComplexModel n)).indicator fun x => u (τ x)) := by
  classical
  have hT' := BedfordTaylorTopDegree.isPositive_mulBorel_of_nonneg hT hu hub hu0
  have hP := isPositive_pullback h hT
  ext γ φ
  have hK : IsCompact (τ '' tsupport φ) :=
    φ.hasCompactSupport.image_of_continuousOn (h.holo.continuousOn.mono φ.tsupport_subset)
  obtain ⟨χ, hχ⟩ := LocalCurrentPullbackDdc.exists_testFunction_eq_one hK
    (image_subset_iff.mpr fun x hx => h.mapsTo (φ.tsupport_subset hx))
  have hL : pullback h hT' γ φ = ∫ y in B, φ (σ y) *
      (u y * densityForm hT y (pullSpan q (fderiv ℂ σ y) γ)) ∂hT.traceMeasure := by
    rw [LocalCurrentPullbackDdc.pullback_apply_eq_sum_mulBorel h hT' γ φ hχ]
    simp_rw [mulBorel_mulBorel hT hu hub hu0 (LocalCurrentPullbackDdc.measurable_pbCoeffFun h γ φ
      _)
      (LocalCurrentPullbackDdc.isLocallyBoundedOn_pbCoeffFun h γ φ _)]
    exact LocalCurrentPullbackDdc.sum_mulBorel_pbCoeffFun_eq_integral h hT hu hub γ φ hχ
  have hR : mulBorel (pullback h hT) ((A : Set (ComplexModel n)).indicator fun x => u (τ x)) γ φ =
      ∫ y in B, φ (σ y) * (u y * densityForm hT y (pullSpan q (fderiv ℂ σ y) γ))
        ∂hT.traceMeasure := by
    have hd : IsLocalDensity (U := A) (pbMeasure σ hT) (pbDensity A τ σ hT γ) :=
      ⟨pbMeasure_compl h hT, fun K hK hKA => pbMeasure_lt_top h hT hK hKA,
        measurable_pbDensity h hT γ, fun K hK hKA => exists_abs_pbDensity_le h hT γ hK hKA⟩
    rw [mulBorel_apply_of_integral_eq hP γ hd (fun ψ => pullback_apply_eq h hT γ ψ)
      (measurable_indicator_comp h hu) (isLocallyBoundedOn_indicator_comp h hub) φ,
      integral_pbMeasure h hT (g := fun x => φ x * ((A : Set (ComplexModel n)).indicator (fun x =>
        u (τ x)) x *
        pbDensity A τ σ hT γ x)) (by
          exact (φ.continuous.measurable.mul ((measurable_indicator_comp h hu).mul
            (measurable_pbDensity h hT γ))).aestronglyMeasurable)]
    refine setIntegral_congr_fun B.isOpen.measurableSet fun y hy => ?_
    simp only [Set.indicator_of_mem (h.mapsTo_inv hy), h.right_inv y hy, pbDensity_comp h hT γ hy]
  rw [hL, hR]

end Pullback

section Product

variable {p q : ℕ} (hqp : q + p = n)

variable {A B : Opens (ComplexModel n)} {τ σ : (ComplexModel n) → (ComplexModel n)} {φ : Fin p →
    (ComplexModel n) → EReal}

theorem plurisubharmonicOn_comp (h : IsBiholomorphicPair A B τ σ)
    (hφ : ∀ i, PlurisubharmonicOn (φ i) B) (i : Fin p) :
    PlurisubharmonicOn (fun x => φ i (τ x)) A :=
  HolomorphicPullback.plurisubharmonicOn_comp_holomorphic A.isOpen
    (h.holo.differentiableOn (by simp)) h.mapsTo (hφ i)

/-- `τ^* ⋀ⱼ dd^c (φⱼ ∨ (-k)) = ⋀ⱼ dd^c ((φⱼ ∘ τ) ∨ (-k))`. -/
theorem pullback_truncatedBT (h : IsBiholomorphicPair A B τ σ)
    (hφ : ∀ i, PlurisubharmonicOn (φ i) B) (k : ℕ) :
    pullback h (isPositive_truncatedBT hqp hφ k).1 =
      truncatedBT hqp A (fun i x => φ i (τ x)) k :=
  LocalBedfordTaylorBiholomorphicProducts.pullback_btProduct hqp h
    (fun i => truncationReal_isLocallyBoundedPshOn (hφ i) k)

theorem indicator_strictLocus_comp (h : IsBiholomorphicPair A B τ σ) (k : ℕ) :
    (BedfordTaylorTopDegree.strictLocus A (fun i x => φ i (τ x)) k).indicator
        (fun _ => (1 : ℝ)) =
      (A : Set (ComplexModel n)).indicator fun x => (BedfordTaylorTopDegree.strictLocus B φ
        k).indicator
        (fun _ => (1 : ℝ)) (τ x) := by
  funext x
  by_cases hx : x ∈ (A : Set (ComplexModel n))
  · rw [Set.indicator_of_mem hx]
    have : x ∈ BedfordTaylorTopDegree.strictLocus A (fun i x => φ i (τ x)) k ↔
        τ x ∈ BedfordTaylorTopDegree.strictLocus B φ k :=
      ⟨fun h' => ⟨h.mapsTo hx, h'.2⟩, fun h' => ⟨hx, h'.2⟩⟩
    by_cases h' : x ∈ BedfordTaylorTopDegree.strictLocus A (fun i x => φ i (τ x)) k
    · rw [Set.indicator_of_mem h', Set.indicator_of_mem (this.mp h')]
    · rw [Set.indicator_of_notMem h', Set.indicator_of_notMem (fun h'' => h' (this.mpr h''))]
  · have hnot : x ∉ BedfordTaylorTopDegree.strictLocus A (fun i x => φ i (τ x)) k :=
      fun h' => hx h'.1
    rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hnot]

/-- **The truncated products are biholomorphically invariant**: `τ^* S_k(φ) = S_k(φ ∘ τ)`. -/
theorem pullback_truncatedProduct (h : IsBiholomorphicPair A B τ σ)
    (hφ : ∀ i, PlurisubharmonicOn (φ i) B) (k : ℕ) :
    pullback h ((isTruncationFamily hqp hφ).isPositive_trunc k) =
      BedfordTaylorTopDegree.truncatedProduct hqp A (fun i x => φ i (τ x)) k := by
  have hB := (isPositive_truncatedBT hqp hφ k).1
  have hO := BedfordTaylorTopDegree.measurableSet_strictLocus hφ k
  have e := pullback_mulBorel h hB (measurable_const.indicator hO)
    (isLocallyBoundedOn_indicator_one _) (fun x => by
      by_cases hx : x ∈ BedfordTaylorTopDegree.strictLocus B φ k <;> simp [hx])
  refine e.trans ?_
  rw [BedfordTaylorTopDegree.truncatedProduct, ← indicator_strictLocus_comp h k,
    pullback_truncatedBT hqp h hφ k]
  rfl

/-- **Biholomorphic invariance of the non-pluripolar product**: if the product of `φ₁, …, φ_p`
on `B` is well defined, then so is that of `φ₁ ∘ τ, …, φ_p ∘ τ` on `A`, and
`τ^* ⟨⋀ⱼ dd^c φⱼ⟩ = ⟨⋀ⱼ dd^c (φⱼ ∘ τ)⟩`. -/
theorem pullback_nonPluripolarProduct (h : IsBiholomorphicPair A B τ σ)
    (hφ : ∀ i, PlurisubharmonicOn (φ i) B) (hW : IsWellDefinedOn hqp B φ) :
    IsWellDefinedOn hqp A (fun i x => φ i (τ x)) ∧
      pullback h (isPositive_nonPluripolarProduct hqp hφ hW) =
        nonPluripolarProduct hqp A (fun i x => φ i (τ x)) := by
  have hφA := plurisubharmonicOn_comp h hφ
  have hS := isPositive_nonPluripolarProduct hqp hφ hW
  have hconv := LocalCurrentPullbackDdc.weakTendsto_pullback h
    (fun k => (isTruncationFamily hqp hφ).isPositive_trunc k) hS
    (weakTendsto_truncatedProduct hqp hφ hW)
  have e : (fun k => pullback h ((isTruncationFamily hqp hφ).isPositive_trunc k)) =
      truncAt (truncatedBT hqp A (fun i x => φ i (τ x)))
        (BedfordTaylorTopDegree.strictLocus A (fun i x => φ i (τ x))) := by
    funext k
    exact pullback_truncatedProduct hqp h hφ k
  rw [e] at hconv
  have hWA : IsWellDefinedOn hqp A (fun i x => φ i (τ x)) :=
    (isWellDefinedOn_iff hqp hφA).mpr
      ((isTruncationFamily hqp hφA).hasLocallyFiniteMass_of_weakTendsto hconv)
  refine ⟨hWA, ?_⟩
  ext γ ψ
  exact tendsto_nhds_unique (hconv γ ψ) (weakTendsto_truncatedProduct hqp hφA hWA γ ψ)

end Product

end SGPT.NPP.NonPluripolarCurrent
