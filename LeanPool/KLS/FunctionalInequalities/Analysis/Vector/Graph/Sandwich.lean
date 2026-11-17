/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Analysis.MeasurableCover
public import LeanPool.KLS.FunctionalInequalities.Analysis.Vector.Graph.Basic

/-! # Two-sided estimates for vector-valued graphs

The sandwich estimates.  A graph map that is `ε`-close to its linear
model has `k`-dimensional image measure within a factor `(1 + ε)^k` of the linear one, on both
sides.

Both directions reduce to the same generic comparison
`Analysis.hausdorffMeasure_image_le_of_norm_le`, already proved for the codimension-one file, and
both need the **Pythagorean identity** `‖ι y + κ z‖² = ‖y‖² + ‖z‖²`, which holds because the two
embeddings have orthogonal ranges.  Its consequence `‖y - y'‖ ≤ ‖Ψ y - Ψ y'‖` is what makes a graph
map expansive, and that is exactly the lower bound the general area-formula route has to obtain
from an inverse it does not have.

This module supplies the two-sided estimates. `Analysis/Vector/Graph/Area.lean` takes the
`ε → 0` limit and performs the countable patching for the area formula.
-/

@[expose] public section

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal RealInnerProductSpace Topology

namespace FunctionalInequalities.Analysis

section Pythagoras

variable {H K V : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup K] [InnerProductSpace ℝ K]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- **Pythagoras across the two factors.** -/
theorem norm_add_sq_of_perp (ι : H →ₗᵢ[ℝ] V) (κ : K →ₗᵢ[ℝ] V)
    (hperp : ∀ (y : H) (z : K), ⟪ι y, κ z⟫ = (0 : ℝ)) (y : H) (z : K) :
    ‖ι y + κ z‖ ^ 2 = ‖y‖ ^ 2 + ‖z‖ ^ 2 := by
  have hyz : ⟪ι y, κ z⟫ = (0 : ℝ) := hperp y z
  have hzy : ⟪κ z, ι y⟫ = (0 : ℝ) := by rw [real_inner_comm]; exact hyz
  rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq]
  simp only [inner_add_left, inner_add_right, hyz, hzy, ι.inner_map_map, κ.inner_map_map]
  ring

/-- The graph map moves points at least as far as the identity. -/
theorem norm_sub_vectorGraphMap_sq (ι : H →ₗᵢ[ℝ] V) (κ : K →ₗᵢ[ℝ] V)
    (hperp : ∀ (y : H) (z : K), ⟪ι y, κ z⟫ = (0 : ℝ)) (γ : H → K) (y y' : H) :
    ‖vectorGraphMap ι κ γ y - vectorGraphMap ι κ γ y'‖ ^ 2
      = ‖y - y'‖ ^ 2 + ‖γ y - γ y'‖ ^ 2 := by
  have hsub : vectorGraphMap ι κ γ y - vectorGraphMap ι κ γ y'
      = ι (y - y') + κ (γ y - γ y') := by
    simp only [vectorGraphMap_apply, map_sub]
    abel
  rw [hsub, norm_add_sq_of_perp ι κ hperp]

theorem norm_sub_le_norm_sub_vectorGraphMap (ι : H →ₗᵢ[ℝ] V) (κ : K →ₗᵢ[ℝ] V)
    (hperp : ∀ (y : H) (z : K), ⟪ι y, κ z⟫ = (0 : ℝ)) (γ : H → K) (y y' : H) :
    ‖y - y'‖ ≤ ‖vectorGraphMap ι κ γ y - vectorGraphMap ι κ γ y'‖ := by
  have h := norm_sub_vectorGraphMap_sq ι κ hperp γ y y'
  nlinarith [norm_nonneg (vectorGraphMap ι κ γ y - vectorGraphMap ι κ γ y'),
    norm_nonneg (y - y'), sq_nonneg ‖γ y - γ y'‖, norm_nonneg (γ y - γ y')]

/-- The same for the linear model. -/
theorem norm_le_norm_graphMapLinear (ι : H →ₗᵢ[ℝ] V) (κ : K →ₗᵢ[ℝ] V)
    (hperp : ∀ (y : H) (z : K), ⟪ι y, κ z⟫ = (0 : ℝ)) (A : H →L[ℝ] K) (v : H) :
    ‖v‖ ≤ ‖graphMapLinear ι κ A v‖ := by
  have h : ‖graphMapLinear ι κ A v‖ ^ 2 = ‖v‖ ^ 2 + ‖A v‖ ^ 2 := by
    rw [graphMapLinear_apply, norm_add_sq_of_perp ι κ hperp]
  nlinarith [norm_nonneg (graphMapLinear ι κ A v), norm_nonneg v, norm_nonneg (A v),
    sq_nonneg ‖A v‖]

theorem injective_graphMapLinear (ι : H →ₗᵢ[ℝ] V) (κ : K →ₗᵢ[ℝ] V)
    (hperp : ∀ (y : H) (z : K), ⟪ι y, κ z⟫ = (0 : ℝ)) (A : H →L[ℝ] K) :
    Function.Injective (graphMapLinear ι κ A) := by
  intro v v' h
  have hv := norm_le_norm_graphMapLinear ι κ hperp A (v - v')
  rw [map_sub, h, sub_self, norm_zero] at hv
  have : ‖v - v'‖ = 0 := le_antisymm hv (norm_nonneg _)
  simpa [sub_eq_zero] using this

end Pythagoras

section Sandwich

variable {H K V : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
  [MeasurableSpace H] [BorelSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℝ K] [FiniteDimensional ℝ K]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- **Upper sandwich estimate.** -/
theorem hausdorffMeasure_image_vectorGraphMap_le (ι : H →ₗᵢ[ℝ] V) (κ : K →ₗᵢ[ℝ] V)
    (hperp : ∀ (y : H) (z : K), ⟪ι y, κ z⟫ = (0 : ℝ)) (γ : H → K) (A : H →L[ℝ] K)
    {t : Set H} {ε : ℝ≥0}
    (happ : ApproximatesLinearOn (vectorGraphMap ι κ γ) (graphMapLinear ι κ A) t ε) :
    μH[(Module.finrank ℝ H : ℝ)] (vectorGraphMap ι κ γ '' t)
      ≤ ((1 + ε : ℝ≥0) : ℝ≥0∞) ^ (Module.finrank ℝ H : ℝ)
        * ENNReal.ofReal (LinearMap.normDet ((graphMapLinear ι κ A : H →ₗ[ℝ] V)))
        * μH[(Module.finrank ℝ H : ℝ)] t := by
  have hd : (0 : ℝ) ≤ (Module.finrank ℝ H : ℝ) := by positivity
  have hAinj : Set.InjOn (graphMapLinear ι κ A) t :=
    (injective_graphMapLinear ι κ hperp A).injOn
  have hcmp : ∀ y ∈ t, ∀ y' ∈ t,
      ‖vectorGraphMap ι κ γ y - vectorGraphMap ι κ γ y'‖
        ≤ ((1 + ε : ℝ≥0) : ℝ) * ‖graphMapLinear ι κ A y - graphMapLinear ι κ A y'‖ := by
    intro y hy y' hy'
    have h1 := happ y hy y' hy'
    have h2 : ‖y - y'‖ ≤ ‖graphMapLinear ι κ A (y - y')‖ :=
      norm_le_norm_graphMapLinear ι κ hperp A _
    have h3 : graphMapLinear ι κ A (y - y')
        = graphMapLinear ι κ A y - graphMapLinear ι κ A y' := map_sub _ _ _
    have h4 : ‖vectorGraphMap ι κ γ y - vectorGraphMap ι κ γ y'‖
        ≤ ‖vectorGraphMap ι κ γ y - vectorGraphMap ι κ γ y' - graphMapLinear ι κ A (y - y')‖
          + ‖graphMapLinear ι κ A (y - y')‖ := by
      have := norm_add_le
        (vectorGraphMap ι κ γ y - vectorGraphMap ι κ γ y' - graphMapLinear ι κ A (y - y'))
        (graphMapLinear ι κ A (y - y'))
      simpa using this
    rw [h3] at h1 h2 h4
    have h5 : (ε : ℝ) * ‖y - y'‖
        ≤ (ε : ℝ) * ‖graphMapLinear ι κ A y - graphMapLinear ι κ A y'‖ :=
      mul_le_mul_of_nonneg_left h2 ε.coe_nonneg
    push_cast
    linarith
  calc μH[(Module.finrank ℝ H : ℝ)] (vectorGraphMap ι κ γ '' t)
      ≤ ((1 + ε : ℝ≥0) : ℝ≥0∞) ^ (Module.finrank ℝ H : ℝ)
          * μH[(Module.finrank ℝ H : ℝ)] (graphMapLinear ι κ A '' t) :=
        hausdorffMeasure_image_le_of_norm_le hAinj hcmp hd
    _ = _ := by
        rw [hausdorffMeasure_image_graphMapLinear ι κ hperp A t,
          normDet_graphMapLinear ι κ hperp A, mul_assoc]

omit [FiniteDimensional ℝ K] in
/-- **Lower sandwich estimate.**  This is where the graph structure pays: expansiveness comes from
the Pythagorean identity, not from an inverse that has to be constructed. -/
theorem le_hausdorffMeasure_image_vectorGraphMap (ι : H →ₗᵢ[ℝ] V) (κ : K →ₗᵢ[ℝ] V)
    (hperp : ∀ (y : H) (z : K), ⟪ι y, κ z⟫ = (0 : ℝ)) (γ : H → K) (A : H →L[ℝ] K)
    {t : Set H} {ε : ℝ≥0}
    (happ : ApproximatesLinearOn (vectorGraphMap ι κ γ) (graphMapLinear ι κ A) t ε) :
    ENNReal.ofReal (LinearMap.normDet ((graphMapLinear ι κ A : H →ₗ[ℝ] V)))
        * μH[(Module.finrank ℝ H : ℝ)] t
      ≤ ((1 + ε : ℝ≥0) : ℝ≥0∞) ^ (Module.finrank ℝ H : ℝ)
        * μH[(Module.finrank ℝ H : ℝ)] (vectorGraphMap ι κ γ '' t) := by
  have hd : (0 : ℝ) ≤ (Module.finrank ℝ H : ℝ) := by positivity
  have hΨinj : Set.InjOn (vectorGraphMap ι κ γ) t :=
    (vectorGraphMap_injective ι κ hperp γ).injOn
  have hcmp : ∀ y ∈ t, ∀ y' ∈ t,
      ‖graphMapLinear ι κ A y - graphMapLinear ι κ A y'‖
        ≤ ((1 + ε : ℝ≥0) : ℝ) * ‖vectorGraphMap ι κ γ y - vectorGraphMap ι κ γ y'‖ := by
    intro y hy y' hy'
    have h1 := happ y hy y' hy'
    have h2 : ‖y - y'‖ ≤ ‖vectorGraphMap ι κ γ y - vectorGraphMap ι κ γ y'‖ :=
      norm_sub_le_norm_sub_vectorGraphMap ι κ hperp γ y y'
    have h3 : graphMapLinear ι κ A (y - y')
        = graphMapLinear ι κ A y - graphMapLinear ι κ A y' := map_sub _ _ _
    have h4 : ‖graphMapLinear ι κ A (y - y')‖
        ≤ ‖vectorGraphMap ι κ γ y - vectorGraphMap ι κ γ y'
            - graphMapLinear ι κ A (y - y')‖
          + ‖vectorGraphMap ι κ γ y - vectorGraphMap ι κ γ y'‖ := by
      have := norm_add_le (graphMapLinear ι κ A (y - y')
          - (vectorGraphMap ι κ γ y - vectorGraphMap ι κ γ y'))
        (vectorGraphMap ι κ γ y - vectorGraphMap ι κ γ y')
      have hnn : ‖graphMapLinear ι κ A (y - y')
            - (vectorGraphMap ι κ γ y - vectorGraphMap ι κ γ y')‖
          = ‖vectorGraphMap ι κ γ y - vectorGraphMap ι κ γ y'
            - graphMapLinear ι κ A (y - y')‖ := by
        rw [← norm_neg]; congr 1; abel
      rw [hnn] at this
      simpa using this
    rw [h3] at h1 h4
    have h5 : (ε : ℝ) * ‖y - y'‖
        ≤ (ε : ℝ) * ‖vectorGraphMap ι κ γ y - vectorGraphMap ι κ γ y'‖ :=
      mul_le_mul_of_nonneg_left h2 ε.coe_nonneg
    push_cast
    linarith
  calc ENNReal.ofReal (LinearMap.normDet ((graphMapLinear ι κ A : H →ₗ[ℝ] V)))
        * μH[(Module.finrank ℝ H : ℝ)] t
      = μH[(Module.finrank ℝ H : ℝ)] (graphMapLinear ι κ A '' t) :=
        (LinearMap.hausdorffMeasure_image ((graphMapLinear ι κ A : H →ₗ[ℝ] V)) t).symm
    _ ≤ ((1 + ε : ℝ≥0) : ℝ≥0∞) ^ (Module.finrank ℝ H : ℝ)
          * μH[(Module.finrank ℝ H : ℝ)] (vectorGraphMap ι κ γ '' t) :=
        hausdorffMeasure_image_le_of_norm_le hΨinj hcmp hd

/-! ### The approximating partition -/

omit [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ V] [FiniteDimensional ℝ K] in
/-- A countable measurable partition of `H` on which the graph map is `ε`-approximated by linear
graph maps and the derivative stays `ε`-close to the corresponding slope.  This is the input of the
remaining, fifth phase of vector-valued graph area. -/
theorem exists_approximating_partition_vectorGraph (ι : H →ₗᵢ[ℝ] V) (κ : K →ₗᵢ[ℝ] V)
    {γ : H → K} (hγ : ContDiff ℝ 1 γ) {ε : ℝ≥0} (hε : 0 < ε) :
    ∃ (t : ℕ → Set H) (A : ℕ → (H →L[ℝ] K)),
      (∀ n, MeasurableSet (t n)) ∧ Pairwise (Function.onFun Disjoint t) ∧
      (⋃ n, t n) = Set.univ ∧
      (∀ n, ApproximatesLinearOn (vectorGraphMap ι κ γ) (graphMapLinear ι κ (A n)) (t n) ε) ∧
      (∀ n, ∀ z ∈ t n, ‖fderiv ℝ γ z - A n‖ ≤ (ε : ℝ)) := by
  classical
  have hgc : Continuous (fderiv ℝ γ) := hγ.continuous_fderiv one_ne_zero
  have hrad : ∀ y₀ : H, ∃ r : ℝ, 0 < r ∧
      ∀ z ∈ Metric.ball y₀ r, ‖fderiv ℝ γ z - fderiv ℝ γ y₀‖ ≤ (ε : ℝ) := by
    intro y₀
    have hpos : (0 : ℝ) < (ε : ℝ) := by exact_mod_cast hε
    obtain ⟨r, hr, hball⟩ := Metric.continuousAt_iff.mp hgc.continuousAt (ε : ℝ) hpos
    refine ⟨r, hr, fun z hz => ?_⟩
    have := hball (Metric.mem_ball.mp hz)
    rw [dist_eq_norm] at this
    exact this.le
  choose r hrpos hrball using hrad
  obtain ⟨σ, T, hTm, hTd, hTu, hTsub⟩ :=
    exists_measurable_partition_subordinate MeasurableSet.univ (subset_refl _)
      ⟨(0 : H), Set.mem_univ _⟩
      (fun z : (Set.univ : Set H) => Metric.ball (z : H) (r z))
      (fun _ => Metric.isOpen_ball)
      (fun z => Metric.mem_ball_self (hrpos z)) (fun _ => Set.subset_univ _)
  let w : ℕ → H := fun n => σ n
  refine ⟨T, fun n => fderiv ℝ γ (w n), hTm, hTd, hTu, ?_, ?_⟩
  · intro n
    exact approximatesLinearOn_vectorGraphMap ι κ hγ (hrball (w n)) (hTsub n)
  · intro n z hz
    exact hrball (w n) z (hTsub n hz)
end Sandwich

end FunctionalInequalities.Analysis
