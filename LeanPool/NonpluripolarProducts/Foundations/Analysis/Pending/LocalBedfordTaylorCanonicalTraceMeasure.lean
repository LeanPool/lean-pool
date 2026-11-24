/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.LocalBedfordTaylorSmoothTraceMeasure

/-!
# Canonical Bedford–Taylor trace measures

Compares the trace of a local Bedford–Taylor product with its canonical measure.
-/

@[expose] public section

noncomputable section
open Set Filter MeasureTheory TopologicalSpace
open scoped Topology Distributions ContDiff
namespace SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorCanonicalTraceMeasure
open FirstPass FirstPass.MongeAmpere FirstPass.MixedMongeAmpere
  LocalProductCurrents LocalBedfordTaylorProducts LocalBedfordTaylorLocality
  LocalBedfordTaylorDecreasing LocalBedfordTaylorSmoothTraceMeasure
variable {n : ℕ} {U V : Opens (ComplexModel n)}

private theorem restrict_oneCurrent (hVU : V ≤ U) :
    restrict hVU (oneCurrent U) = oneCurrent V := by
  ext γ φ
  simp only [LocalBedfordTaylorLocality.restrict_apply, oneCurrent_apply]
  have hφ : (extTest hVU φ : ComplexModel n → ℝ) = φ := funext (extTest_apply hVU φ)
  rw [hφ]

private theorem restrict_oneCurrentOf {k : ℕ} (hk : k = n) (hVU : V ≤ U) :
    restrict hVU (oneCurrentOf (U := U) hk) = oneCurrentOf (U := V) hk := by
  subst hk
  exact restrict_oneCurrent hVU

private theorem traceMeasure_congr {k : ℕ} {A B : LocalProductCurrent n U k}
    (hA : IsPositive A) (hB : IsPositive B) (e : A = B) :
    hA.traceMeasure = hB.traceMeasure := by
  subst B
  rfl

/-- Literal open restriction of the independently constructed recursive mixed trace. -/
theorem recursiveMixedTraceMeasure_restrict {u : Fin n → ComplexModel n → ℝ}
    (hu : ∀ i, IsLocallyBoundedPshOn U (u i)) (hVU : V ≤ U) :
    (recursiveMixedTraceMeasure U u hu).restrict (V : Set (ComplexModel n)) =
      recursiveMixedTraceMeasure V u (fun i => isLocallyBoundedPshOn_mono (hu i) hVU) := by
  let hT := (isPositive_btProduct n 0 u (oneCurrentOf (U := U) (Nat.zero_add n))
    (isPositive_oneCurrentOf _) (isClosedAny_oneCurrentOf _) hu).1
  have e : restrict hVU (btProduct n 0 u (oneCurrentOf (U := U) (Nat.zero_add n))) =
      btProduct n 0 u (oneCurrentOf (U := V) (Nat.zero_add n)) := by
    rw [← btProduct_restrict hVU n 0 u _ (isPositive_oneCurrentOf _)
      (isClosedAny_oneCurrentOf _) hu, restrict_oneCurrentOf]
  have er := traceMeasure_restrict hT hVU
  exact er.symm.trans (traceMeasure_congr (isPositive_restrict hT hVU)
    (isPositive_btProduct n 0 u (oneCurrentOf (U := V) (Nat.zero_add n))
      (isPositive_oneCurrentOf _) (isClosedAny_oneCurrentOf _)
      (fun i => isLocallyBoundedPshOn_mono (hu i) hVU)).1 e)

/-- Every independently varying genuine smooth decreasing mixed approximation tests the trace. -/
theorem isLocalMixedBedfordTaylorMeasure_recursiveMixedTraceMeasure
    {Ω : Opens (ComplexModel n)} {u : Fin n → ComplexModel n → ℝ}
    (hu : IsLocallyBoundedMixedPshOn Ω u) :
    IsLocalMixedBedfordTaylorMeasure Ω u (recursiveMixedTraceMeasure Ω u hu) := by
  let hT := (isPositive_btProduct n 0 u (oneCurrentOf (U := Ω) (Nat.zero_add n))
    (isPositive_oneCurrentOf _) (isClosedAny_oneCurrentOf _) hu).1
  refine ⟨hu, hT.traceMeasure_compl, fun K hK hKΩ => hT.traceMeasure_lt_top hK hKΩ,
    fun D hD => ⟨MixedMongeAmpere.exists_decreasingMixedApproximation hu hD, ?_⟩⟩
  intro f hf h hc hk ht
  have hDΩ : D ≤ Ω := subset_closure.trans hD.2
  let huD := fun i => isLocallyBoundedPshOn_mono (hu i) hDΩ
  let hfD := fun j i => isLocallyBoundedPshOn_of_isSmoothPshOn ((hf.1 j).component i)
  let hP := fun j => (isPositive_btProduct n 0 (f j)
    (oneCurrentOf (U := D) (Nat.zero_add n)) (isPositive_oneCurrentOf _)
    (isClosedAny_oneCurrentOf _) (hfD j)).1
  let hP₀ := (isPositive_btProduct n 0 u (oneCurrentOf (U := D) (Nat.zero_add n))
    (isPositive_oneCurrentOf _) (isClosedAny_oneCurrentOf _) huD).1
  have hw := weakTendsto_btProduct_of_antitone n 0 (oneCurrentOf (U := D) (Nat.zero_add n))
    (isPositive_oneCurrentOf _) (isClosedAny_oneCurrentOf _) f u hfD huD hf.2.1 hf.2.2
  have hl := tendsto_integral_traceMeasure_of_weakTendsto hP hP₀ hw hc hk ht
  change Tendsto (fun j => ∫ x, h x ∂recursiveMixedTraceMeasure D (f j) (hfD j)) atTop
    (𝓝 (∫ x, h x ∂recursiveMixedTraceMeasure D u huD)) at hl
  have es (j : ℕ) : recursiveMixedTraceMeasure D (f j) (hfD j) =
      smoothMixedMeasure D (f j) (hf.1 j) := by
    exact recursiveMixedTraceMeasure_eq_smoothMixedMeasure
      (fun i => ((hf.1 j).component i).1) (fun i => ((hf.1 j).component i).2.1)
  have et : (∫ x, h x ∂recursiveMixedTraceMeasure D u huD) =
      ∫ x, h x ∂recursiveMixedTraceMeasure Ω u hu := by
    rw [← recursiveMixedTraceMeasure_restrict hu hDΩ]
    exact setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx =>
      image_eq_zero_of_notMem_tsupport (fun hxt => hx (ht hxt)))
  simp only [es, et] at hl
  exact hl

/-- The canonical mixed weak-limit measure is literally the independently built Riesz trace. -/
theorem canonicalMixedBedfordTaylorMeasure_eq_recursiveMixedTraceMeasure
    {Ω : Opens (ComplexModel n)} {u : Fin n → ComplexModel n → ℝ}
    (hu : IsLocallyBoundedMixedPshOn Ω u) :
    MixedMongeAmpere.canonicalMixedBedfordTaylorMeasure Ω u hu =
      recursiveMixedTraceMeasure Ω u hu :=
  MixedMongeAmpere.canonicalMixedBedfordTaylorMeasure_eq hu
    (isLocalMixedBedfordTaylorMeasure_recursiveMixedTraceMeasure hu)

end SGPT.Foundations.Analysis.Pending.LocalBedfordTaylorCanonicalTraceMeasure
