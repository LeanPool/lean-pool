/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Analysis.LocalExtension
public import LeanPool.KLS.FunctionalInequalities.Analysis.Graph.Integral
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-! # Weighted graph area over an open parameter domain

The weighted change of variables
`setLIntegral_image_graphChartMap` of `Analysis/Graph/Integral.lean` requires the graph function to
be `C¹` on the **whole** parameter space.  Here it is localized to a function that is `C¹` only on
an open set `O`, for measurable parameter sets `S ⊆ O`.

A `ContDiffOn` function on an open set does **not** extend to a globally `C¹` function — `1 / x`
on `(0, ∞)` is the standard counterexample — so the localization is genuinely countable and cannot
be done by one global extension.  What is true, and is what `exists_contDiff_eqOn_ball` proves,
is that every point of `O` has a ball on which some globally `C¹` function agrees with the given
one: multiply by a `ContDiffBump` supported inside `O`.  This is an interior localization;
it is **not** the Whitney extension from a closed set, which is the separate unproved
compact Whitney extension problem.

Second countability then extracts a countable subfamily of such balls covering `O`, `disjointed`
turns it into countably many pairwise disjoint measurable pieces of `S`, and the graph map is
injective (`graphMap_injective`), so the images of the pieces are disjoint and measurable.  Both
sides of the identity are countably additive over those pieces, and on each piece the global
theorem applies to the local extension; the gradients agree because the functions agree on an
**open** ball around each point (`Filter.EventuallyEq.gradient_eq`).

`Analysis/LocalExtension.lean` supplies the shared finite-order and smooth bump
extension; this module uses its explicit agreement ball.

No integrability, boundedness or finiteness hypothesis is used; the weight may be unbounded or
identically `∞`, `S` need not be bounded or of finite measure, and `O = ∅` or `S = ∅` are covered.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal ContDiff RealInnerProductSpace

namespace FunctionalInequalities.Analysis

section Extension

end Extension

section OpenGraph

universe u v

variable {H : Type u} {V : Type v} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [FiniteDimensional ℝ H] [MeasurableSpace H] [BorelSpace H]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- The weighted change of variables for the untranslated graph map: the `x₀ = 0` case of
`setLIntegral_image_graphChartMap`. -/
theorem setLIntegral_image_graphMap (ι : H →ₗᵢ[ℝ] V) {e : V} (he : ‖e‖ = 1)
    (hperp : ∀ v : H, ⟪ι v, e⟫ = (0 : ℝ)) {g : H → ℝ} (hg : ContDiff ℝ 1 g)
    {s : Set H} (hs : MeasurableSet s) {f : V → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x in graphMap ι e g '' s, f x ∂(KLS.hausdorffNormalized V (Module.finrank ℝ H))
      = ∫⁻ y in s, ENNReal.ofReal (graphJacobian (gradient g y)) * f (graphMap ι e g y)
          ∂(volume : Measure H) := by
  have h : graphChartMap ι e 0 g = graphMap ι e g := by
    funext y; rw [graphChartMap, zero_add]
  simpa [h] using setLIntegral_image_graphChartMap ι he hperp 0 hg hs hf

/-- **Weighted graph area over an open parameter domain.**  The graph function is
`C¹` only on the open set `O`, and the parameter set is any measurable `S ⊆ O`.

No integrability of the weight, no boundedness or finite measure of `S`, and no global regularity
of `v` outside `O`; `O = ∅` and `S = ∅` are covered. -/
theorem setLIntegral_image_graphMap_of_contDiffOn (ι : H →ₗᵢ[ℝ] V) {e : V} (he : ‖e‖ = 1)
    (hperp : ∀ v : H, ⟪ι v, e⟫ = (0 : ℝ)) {O S : Set H} {v : H → ℝ} {f : V → ℝ≥0∞}
    (hO : IsOpen O) (hv : ContDiffOn ℝ 1 v O) (hS : MeasurableSet S) (hSO : S ⊆ O)
    (hf : Measurable f) :
    ∫⁻ x in graphMap ι e v '' S, f x ∂(KLS.hausdorffNormalized V (Module.finrank ℝ H))
      = ∫⁻ y in S, ENNReal.ofReal (graphJacobian (gradient v y)) * f (graphMap ι e v y)
          ∂(volume : Measure H) := by
  rcases S.eq_empty_or_nonempty with hSe | ⟨z₀, hz₀⟩
  · simp [hSe]
  -- every point of `O` carries a ball with a global `C¹` representative
  choose ρ w hρ hballO hwC hwEq using fun z : O => exists_contDiff_eqOn_ball hO hv z.2
  obtain ⟨T, hTc, hTu⟩ := TopologicalSpace.isOpen_iUnion_countable
    (fun z : O => Metric.ball (z : H) (ρ z)) (fun _ => Metric.isOpen_ball)
  have hOcov : ⋃ z : O, Metric.ball ((z : H)) (ρ z) = O :=
    Set.Subset.antisymm (Set.iUnion_subset fun z => hballO z) fun y hy =>
      Set.mem_iUnion.2 ⟨⟨y, hy⟩, Metric.mem_ball_self (hρ ⟨y, hy⟩)⟩
  have hTne : T.Nonempty := by
    have : z₀ ∈ ⋃ z ∈ T, Metric.ball ((z : H)) (ρ z) := by rw [hTu, hOcov]; exact hSO hz₀
    obtain ⟨z, hzT, -⟩ := Set.mem_iUnion₂.1 this
    exact ⟨z, hzT⟩
  obtain ⟨σ, hσ⟩ := hTc.exists_eq_range hTne
  set B : ℕ → Set H := fun n => Metric.ball ((σ n : O) : H) (ρ (σ n)) with hB
  have hBcov : O ⊆ ⋃ n, B n := by
    rw [← hOcov, ← hTu, hσ, Set.biUnion_range]
  have hWeq : ∀ n, Set.EqOn (w (σ n)) v (B n) := fun n => hwEq (σ n)
  -- disjoint measurable pieces of `S`
  set P : ℕ → Set H := disjointed fun n => S ∩ B n with hP
  have hPmeas : ∀ n, MeasurableSet (P n) :=
    MeasurableSet.disjointed fun n => hS.inter Metric.isOpen_ball.measurableSet
  have hPdisj : Pairwise (Function.onFun Disjoint P) := disjoint_disjointed _
  have hPsub : ∀ n, P n ⊆ B n := fun n =>
    (disjointed_subset _ n).trans Set.inter_subset_right
  have hPunion : ⋃ n, P n = S := by
    rw [hP, iUnion_disjointed, ← Set.inter_iUnion]
    exact Set.inter_eq_self_of_subset_left (hSO.trans hBcov)
  -- the images are the images of the local representatives
  have himgEq : ∀ n, graphMap ι e v '' P n = graphMap ι e (w (σ n)) '' P n := fun n =>
    (Set.image_congr fun y hy => by
      simp only [graphMap]; rw [hWeq n (hPsub n hy)]).symm
  have himgMeas : ∀ n, MeasurableSet (graphMap ι e v '' P n) := fun n => by
    rw [himgEq n]
    exact measurableSet_image_graphMap ι hperp (hwC (σ n)).continuous (hPmeas n)
  have himgDisj : Pairwise (Function.onFun Disjoint fun n => graphMap ι e v '' P n) := by
    intro i j hij
    exact (Set.disjoint_image_iff (graphMap_injective ι hperp v)).2 (hPdisj hij)
  calc ∫⁻ x in graphMap ι e v '' S, f x ∂(KLS.hausdorffNormalized V (Module.finrank ℝ H))
      = ∫⁻ x in ⋃ n, graphMap ι e v '' P n, f x
          ∂(KLS.hausdorffNormalized V (Module.finrank ℝ H)) := by
        rw [← Set.image_iUnion, hPunion]
    _ = ∑' n, ∫⁻ x in graphMap ι e v '' P n, f x
          ∂(KLS.hausdorffNormalized V (Module.finrank ℝ H)) :=
        lintegral_iUnion himgMeas himgDisj f
    _ = ∑' n, ∫⁻ y in P n, ENNReal.ofReal (graphJacobian (gradient v y)) * f (graphMap ι e v y)
          ∂(volume : Measure H) := by
        refine tsum_congr fun n => ?_
        rw [himgEq n, setLIntegral_image_graphMap ι he hperp (hwC (σ n)) (hPmeas n) hf]
        refine setLIntegral_congr_fun (hPmeas n) fun y hy => ?_
        have hnb : w (σ n) =ᶠ[𝓝 y] v :=
          Filter.eventuallyEq_of_mem (Metric.isOpen_ball.mem_nhds (hPsub n hy)) (hWeq n)
        simp only [graphMap]
        rw [hnb.gradient_eq, hWeq n (hPsub n hy)]
    _ = ∫⁻ y in ⋃ n, P n, ENNReal.ofReal (graphJacobian (gradient v y)) * f (graphMap ι e v y)
          ∂(volume : Measure H) := (lintegral_iUnion hPmeas hPdisj _).symm
    _ = ∫⁻ y in S, ENNReal.ofReal (graphJacobian (gradient v y)) * f (graphMap ι e v y)
          ∂(volume : Measure H) := by rw [hPunion]

end OpenGraph

end FunctionalInequalities.Analysis
