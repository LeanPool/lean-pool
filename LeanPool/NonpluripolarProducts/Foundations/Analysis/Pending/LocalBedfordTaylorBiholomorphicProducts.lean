/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.LocalBedfordTaylorSmoothCovariance

/-!
# Local products under biholomorphic maps

Relates the Bedford–Taylor recursion to pullback by biholomorphic changes of coordinates.
-/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions ContDiff

namespace SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorBiholomorphicProducts

open FirstPass FirstPass.MongeAmpere StronglyPositiveForms LocalProductCurrents
  LocalBedfordTaylorProducts LocalBedfordTaylorSmooth LocalBedfordTaylorForms
  LocalCurrentPullback LocalCurrentPullbackDdc BedfordTaylor
  LocalBedfordTaylorLocality LocalBedfordTaylorCollar LocalBedfordTaylorDecreasing

variable {n q r : ℕ} {A B : Opens (ComplexModel n)}
  {τ σ : ComplexModel n → ComplexModel n}

/-- The genuine locally bounded recursive product commutes with an actual
biholomorphism in every degree, with no approximation or limit input. -/
theorem pullback_btProduct (hdegree : r + q = n)
    (h : IsBiholomorphicPair A B τ σ) {u : Fin q → ComplexModel n → ℝ}
    (hu : ∀ i, IsLocallyBoundedPshOn B (u i)) :
    pullback h (isPositive_btProduct q r u (oneCurrentOf hdegree)
      (isPositive_oneCurrentOf hdegree) (isClosedAny_oneCurrentOf hdegree) hu).1 =
      btProduct q r (fun i x => u i (τ x)) (oneCurrentOf (U := A) hdegree) := by
  classical
  ext γ φ
  have hK : IsCompact (τ '' tsupport φ) :=
    φ.hasCompactSupport.image_of_continuousOn (h.holo.continuousOn.mono φ.tsupport_subset)
  have hKB : τ '' tsupport φ ⊆ B :=
    image_subset_iff.mpr fun x hx => h.mapsTo (φ.tsupport_subset hx)
  obtain ⟨V₀, hVo, hKV, hVcl, hVc⟩ :=
    exists_open_between_and_isCompact_closure hK B.isOpen hKB
  let V : Opens (ComplexModel n) := ⟨V₀, hVo⟩
  have hVB : V ≤ B := subset_closure.trans hVcl
  have hVrc : RelativelyCompactIn V B := ⟨hVc, hVcl⟩
  have hex (i : Fin q) := HolomorphicPullback.exists_decreasingMollifierApproximation
    (hu i) hVrc
  choose f hf using hex
  let h' := isBiholomorphicPair_preOpen h hVB
  have hφA' : tsupport φ ⊆ preOpen h V :=
    fun x hx => ⟨φ.tsupport_subset hx, hKV ⟨x, hx, rfl⟩⟩
  let φ' : 𝓓(preOpen h V, ℝ) := ⟨φ, φ.contDiff, φ.hasCompactSupport, hφA'⟩
  have hext : extTest (preOpen_le h V) φ' = φ := by
    ext x
    rw [extTest_apply]
    rfl
  have huV : ∀ i, IsLocallyBoundedPshOn V (u i) :=
    fun i => isLocallyBoundedPshOn_mono (hu i) hVB
  have hS : ∀ j i, IsLocallyBoundedPshOn V (f i j) :=
    fun j i => LocalBedfordTaylorDecreasing.isLocallyBoundedPshOn_of_isSmoothPshOn
      ((hf i).1 j)
  have eB : restrict hVB (btProduct q r u (oneCurrentOf (U := B) hdegree)) =
      btProduct q r u (oneCurrentOf (U := V) hdegree) := by
    rw [← btProduct_restrict hVB q r u (oneCurrentOf hdegree)
      (isPositive_oneCurrentOf _) (isClosedAny_oneCurrentOf _) hu, restrict_oneCurrentOf hVB]
  have e1 : pullback h (isPositive_btProduct q r u (oneCurrentOf hdegree)
      (isPositive_oneCurrentOf _) (isClosedAny_oneCurrentOf _) hu).1 γ φ =
      pullback h' (isPositive_btProduct q r u (oneCurrentOf hdegree)
        (isPositive_oneCurrentOf _) (isClosedAny_oneCurrentOf _) huV).1 γ φ' := by
    rw [← hext, ← LocalBedfordTaylorLocality.restrict_apply, ← pullback_restrict h _ hVB]
    rw [pullback_congr h' _ _ eB]
  have hconvB := weakTendsto_btProduct_of_antitone q r (oneCurrentOf (U := V) hdegree)
    (isPositive_oneCurrentOf _) (isClosedAny_oneCurrentOf _) (fun j i => f i j) u hS huV
    (fun i => (hf i).2.1) (fun i => (hf i).2.2)
  have hpb := weakTendsto_pullback h'
    (fun j => (isPositive_btProduct q r (fun i => f i j) (oneCurrentOf hdegree)
      (isPositive_oneCurrentOf _) (isClosedAny_oneCurrentOf _) (hS j)).1)
    (isPositive_btProduct q r u (oneCurrentOf hdegree)
      (isPositive_oneCurrentOf _) (isClosedAny_oneCurrentOf _) huV).1 hconvB γ φ'
  have hsm : ∀ j, pullback h'
      (isPositive_btProduct q r (fun i => f i j) (oneCurrentOf hdegree)
        (isPositive_oneCurrentOf _) (isClosedAny_oneCurrentOf _) (hS j)).1 =
      btProduct q r (fun i x => f i j (τ x)) (oneCurrentOf (U := preOpen h V) hdegree) :=
    fun j => LocalBedfordTaylorSmoothCovariance.pullback_smooth_btProduct hdegree h'
      (fun i => ((hf i).1 j).1) (fun i => ((hf i).1 j).2.1)
  have hconvA := weakTendsto_btProduct_of_antitone q r
    (oneCurrentOf (U := preOpen h V) hdegree)
    (isPositive_oneCurrentOf _) (isClosedAny_oneCurrentOf _)
    (fun j i x => f i j (τ x)) (fun i x => u i (τ x))
    (fun j i => isLocallyBoundedPshOn_comp h' (hS j i))
    (fun i => isLocallyBoundedPshOn_comp h' (huV i))
    (fun i x hx => (hf i).2.1 (τ x) hx.2)
    (fun i x hx => (hf i).2.2 (τ x) hx.2) γ φ'
  have e2 : pullback h' (isPositive_btProduct q r u (oneCurrentOf hdegree)
      (isPositive_oneCurrentOf _) (isClosedAny_oneCurrentOf _) huV).1 γ φ' =
      btProduct q r (fun i x => u i (τ x)) (oneCurrentOf (U := preOpen h V) hdegree) γ φ' := by
    refine tendsto_nhds_unique hpb ?_
    simp only [hsm]
    exact hconvA
  rw [e1, e2, ← restrict_oneCurrentOf (preOpen_le h V) hdegree,
    btProduct_restrict (preOpen_le h V) q r (fun i x => u i (τ x))
      (oneCurrentOf hdegree) (isPositive_oneCurrentOf _) (isClosedAny_oneCurrentOf _)
      (fun i => isLocallyBoundedPshOn_comp h (hu i)),
    LocalBedfordTaylorLocality.restrict_apply, hext]

end SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorBiholomorphicProducts
