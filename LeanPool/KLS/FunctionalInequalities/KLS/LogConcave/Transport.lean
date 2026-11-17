/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Probability.Support.Affine
public import LeanPool.KLS.FunctionalInequalities.Probability.Transport
public import LeanPool.KLS.FunctionalInequalities.Probability.LogConcave
public import Mathlib.Analysis.Convex.Measure
public import Mathlib.Analysis.Normed.Affine.AddTorsorBases
public import Mathlib.Topology.Maps.Proper.Basic
public import Mathlib.Probability.ConditionalProbability

/-!
# Geometry of the compact-set log-concavity convention

These lemmas use the existing `KLS.LogConcave` definition. Read affine-isometric pullback,
then the intrinsic-coordinate corollary. They provide the coordinate reduction for the
absolute-continuity step in the general log-concave literature comparison. No density is
included in the definition and no representation theorem is assumed here.

Conditioning on a closed convex set of positive mass preserves log-concavity (`cond`), used to
truncate laws to balls (BKL arXiv:2610.05474v1, p. 19).
-/

@[expose] public section

noncomputable section

open MeasureTheory Set Topology

namespace FunctionalInequalities.KLS.LogConcave

section Transport

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F] [BorelSpace F]

/-- A probability law reconstructed by an affine isometry inherits compact-set log-concavity
from its ambient law. Images of compact sets supply the exact test sets. -/
theorem of_affineIsometry_map {μ : ProbabilityMeasure E} (hμ : LogConcave μ)
    (ν : ProbabilityMeasure F) (f : F →ᵃⁱ[ℝ] E)
    (hmap : Measure.map f (ν : Measure F) = (μ : Measure E)) : LogConcave ν := by
  intro K L hK hL t ht ht1
  have hm (S : Set F) (hS : IsCompact S) : (μ : Measure E) (f '' S) = (ν : Measure F) S := by
    rw [← hmap, Measure.map_apply f.continuous.measurable (hS.image f.continuous).measurableSet,
      Set.preimage_image_eq _ f.injective]
  have hcomb :
    f '' {z | ∃ x ∈ K, ∃ y ∈ L, z = t • x + (1 - t) • y} =
      {z | ∃ x ∈ f '' K, ∃ y ∈ f '' L, z = t • x + (1 - t) • y} := by
    have hf (x y : F) : f (t • x + (1 - t) • y) = t • f x + (1 - t) • f y := by
      simpa only [AffineMap.lineMap_apply_module, sub_sub_cancel,
        AffineIsometry.coe_toAffineMap] using f.toAffineMap.apply_lineMap x y (1 - t)
    ext z
    constructor
    · rintro ⟨_, ⟨x, hx, y, hy, rfl⟩, rfl⟩
      exact ⟨f x, ⟨x, hx, rfl⟩, f y, ⟨y, hy, rfl⟩, hf x y⟩
    · rintro ⟨_, ⟨x, hx, rfl⟩, _, ⟨y, hy, rfl⟩, rfl⟩
      exact ⟨t • x + (1 - t) • y, ⟨x, hx, y, hy, rfl⟩, hf x y⟩
  have hc : IsCompact {z : F | ∃ x ∈ K, ∃ y ∈ L, z = t • x + (1 - t) • y} := by
    have he :
      {z : F | ∃ x ∈ K, ∃ y ∈ L, z = t • x + (1 - t) • y} =
        (fun p : F × F => t • p.1 + (1 - t) • p.2) '' (K ×ˢ L) := by
      ext z
      simp only [mem_ofPred_eq, mem_image, mem_prod]
      constructor
      · rintro ⟨x, hx, y, hy, rfl⟩; exact ⟨(x, y), ⟨hx, hy⟩, rfl⟩
      · rintro ⟨⟨x, y⟩, ⟨hx, hy⟩, rfl⟩; exact ⟨x, hx, y, hy, rfl⟩
    rw [he]
    exact (hK.prod hL).image (by fun_prop)
  have h := hμ (f '' K) (f '' L) (hK.image f.continuous) (hL.image f.continuous) t ht ht1
  rwa [hm K hK, hm L hL, ← hcomb, hm _ hc] at h

/-- A probability law carried by a continuous linear equivalence inherits compact-set
log-concavity from its image law. -/
theorem of_continuousLinearEquiv_map {μ : ProbabilityMeasure E} (hμ : LogConcave μ)
    (ν : ProbabilityMeasure F) (T : F ≃L[ℝ] E)
    (hmap : Measure.map T (ν : Measure F) = (μ : Measure E)) : LogConcave ν := by
  intro K L hK hL t ht ht1
  have hm (S : Set F) (hS : IsCompact S) : (μ : Measure E) (T '' S) = (ν : Measure F) S := by
    rw [← hmap, Measure.map_apply T.continuous.measurable (hS.image T.continuous).measurableSet,
      Set.preimage_image_eq _ T.injective]
  have hcomb : T '' {z | ∃ x ∈ K, ∃ y ∈ L, z = t • x + (1 - t) • y} =
      {z | ∃ x ∈ T '' K, ∃ y ∈ T '' L, z = t • x + (1 - t) • y} := by
    have hf (x y : F) : T (t • x + (1 - t) • y) = t • T x + (1 - t) • T y := by
      rw [map_add, map_smul, map_smul]
    ext z
    constructor
    · rintro ⟨_, ⟨x, hx, y, hy, rfl⟩, rfl⟩
      exact ⟨T x, ⟨x, hx, rfl⟩, T y, ⟨y, hy, rfl⟩, hf x y⟩
    · rintro ⟨_, ⟨x, hx, rfl⟩, _, ⟨y, hy, rfl⟩, rfl⟩
      exact ⟨t • x + (1 - t) • y, ⟨x, hx, y, hy, rfl⟩, hf x y⟩
  have hc : IsCompact {z : F | ∃ x ∈ K, ∃ y ∈ L, z = t • x + (1 - t) • y} := by
    have he : {z : F | ∃ x ∈ K, ∃ y ∈ L, z = t • x + (1 - t) • y} =
        (fun p : F × F => t • p.1 + (1 - t) • p.2) '' (K ×ˢ L) := by
      ext z
      simp only [Set.mem_ofPred_eq, Set.mem_image, Set.mem_prod]
      constructor
      · rintro ⟨x, hx, y, hy, rfl⟩; exact ⟨(x, y), ⟨hx, hy⟩, rfl⟩
      · rintro ⟨⟨x, y⟩, ⟨hx, hy⟩, rfl⟩; exact ⟨x, hx, y, hy, rfl⟩
    rw [he]
    exact (hK.prod hL).image (by fun_prop)
  have h := hμ (T '' K) (T '' L) (hK.image T.continuous) (hL.image T.continuous) t ht ht1
  rwa [hm K hK, hm L hL, ← hcomb, hm _ hc] at h

/--
Pushforward along an affine isometric embedding of a complete space preserves compact-set
log-concavity
(the converse direction of `of_affineIsometry_map`; lower-dimensional images allowed, no density
assumed). -/
theorem map_affineIsometry [CompleteSpace F] (ν : ProbabilityMeasure F) (hν : LogConcave ν)
    (μ : ProbabilityMeasure E) (f : F →ᵃⁱ[ℝ] E)
    (hmap : (μ : Measure E) = (ν : Measure F).map f) : LogConcave μ := by
  intro K L hK hL t ht0 ht1
  have hK' := f.isometry.isClosedEmbedding.isProperMap.isCompact_preimage hK
  have hL' := f.isometry.isClosedEmbedding.isProperMap.isCompact_preimage hL
  have h := hν (f ⁻¹' K) (f ⁻¹' L) hK' hL' t ht0 ht1
  have hf (x y : F) : f (t • x + (1 - t) • y) = t • f x + (1 - t) • f y := by
    simpa only [AffineMap.lineMap_apply_module, sub_sub_cancel,
      AffineIsometry.coe_toAffineMap] using f.toAffineMap.apply_lineMap x y (1 - t)
  have hc : IsCompact {z : E | ∃ x ∈ K, ∃ y ∈ L, z = t • x + (1 - t) • y} := by
    have he :
      {z : E | ∃ x ∈ K, ∃ y ∈ L, z = t • x + (1 - t) • y} =
        (fun p : E × E => t • p.1 + (1 - t) • p.2) '' (K ×ˢ L) := by
      ext z
      simp only [mem_ofPred_eq, mem_image, mem_prod]
      constructor
      · rintro ⟨x, hx, y, hy, rfl⟩
        exact ⟨(x, y), ⟨hx, hy⟩, rfl⟩
      · rintro ⟨⟨x, y⟩, ⟨hx, hy⟩, rfl⟩
        exact ⟨x, hx, y, hy, rfl⟩
    rw [he]
    exact (hK.prod hL).image (by fun_prop)
  rw [hmap, Measure.map_apply f.continuous.measurable hK.measurableSet,
    Measure.map_apply f.continuous.measurable hL.measurableSet,
    Measure.map_apply f.continuous.measurable hc.measurableSet]
  apply h.trans (measure_mono ?_)
  rintro z ⟨x, hx, y, hy, rfl⟩
  exact ⟨f x, hx, f y, hy, hf x y⟩



variable [ProperSpace E]

section SupportConvexity

omit [BorelSpace E]
/-- Equal-radius closed-ball masses inherit the log-concavity inequality. This is the
pointwise inequality needed for ball-average regularizations of the measure. -/
theorem closedBall_mul_le {μ : ProbabilityMeasure E} (hμ : LogConcave μ)
    (x y : E) (r t : ℝ) (ht : 0 < t) (ht1 : t < 1) :
    (μ : Measure E) (Metric.closedBall x r) ^ t *
        (μ : Measure E) (Metric.closedBall y r) ^ (1 - t) ≤
      (μ : Measure E) (Metric.closedBall (t • x + (1 - t) • y) r) := by
  refine (hμ _ _ (isCompact_closedBall x r) (isCompact_closedBall y r) t ht ht1).trans
    (measure_mono ?_)
  rintro z ⟨u, hu, v, hv, rfl⟩
  rw [Metric.mem_closedBall, dist_eq_norm]
  rw [Metric.mem_closedBall, dist_eq_norm] at hu hv
  have heq : t • u + (1 - t) • v - (t • x + (1 - t) • y) =
      t • (u - x) + (1 - t) • (v - y) := by simp only [smul_sub]; abel
  rw [heq]
  calc
    _ ≤ ‖t • (u - x)‖ + ‖(1 - t) • (v - y)‖ := norm_add_le _ _
    _ = t * ‖u - x‖ + (1 - t) * ‖v - y‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_pos ht, abs_of_pos (sub_pos.mpr ht1)]
    _ ≤ t * r + (1 - t) * r :=
      add_le_add (mul_le_mul_of_nonneg_left hu ht.le)
        (mul_le_mul_of_nonneg_left hv (sub_nonneg.mpr ht1.le))
    _ = r := by ring

/-- Compact-set log-concavity forces the topological support to be convex. This uses positive
neighborhood masses, without presupposing an ambient density. -/
theorem convex_support {μ : ProbabilityMeasure E} (hμ : LogConcave μ) :
    Convex ℝ (μ : Measure E).support := by
  intro x hx y hy a b ha hb hab
  by_cases ha0 : a = 0
  · have hb1 : b = 1 := by linarith
    simpa [ha0, hb1] using hy
  by_cases hb0 : b = 0
  · have ha1 : a = 1 := by linarith
    simpa [hb0, ha1] using hx
  have ha' : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
  have hb' : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0)
  have ha1 : a < 1 := by linarith
  have hbeq : b = 1 - a := by linarith
  apply Metric.nhds_basis_closedBall.mem_measureSupport.mpr
  intro r hr
  have hxr := (Measure.mem_support_iff_forall x).mp hx _ (Metric.closedBall_mem_nhds x hr)
  have hyr := (Measure.mem_support_iff_forall y).mp hy _ (Metric.closedBall_mem_nhds y hr)
  have hpos : 0 < (μ : Measure E) (Metric.closedBall x r) ^ a *
      (μ : Measure E) (Metric.closedBall y r) ^ (1 - a) := by positivity
  simpa only [hbeq] using hpos.trans_le (hμ.closedBall_mul_le x y r a ha' ha1)

/-- Superlevel sets of equal-radius closed-ball masses are convex. -/
theorem convex_closedBall_superlevel {μ : ProbabilityMeasure E}
    (hμ : LogConcave μ) (r : ℝ) (A : ENNReal) :
    Convex ℝ {x | A ≤ (μ : Measure E) (Metric.closedBall x r)} := by
  intro x hx y hy a b ha hb hab
  by_cases ha0 : a = 0
  · have hb1 : b = 1 := by linarith
    simpa [ha0, hb1] using hy
  by_cases hb0 : b = 0
  · have ha1 : a = 1 := by linarith
    simpa [hb0, ha1] using hx
  have ha' : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
  have ha1 : a < 1 := by have : 0 < b := lt_of_le_of_ne hb (Ne.symm hb0); linarith
  have hbeq : b = 1 - a := by linarith
  change A ≤ _
  calc
    A = A ^ a * A ^ b := by
      rw [← ENNReal.rpow_add_of_nonneg a b ha hb, hab, ENNReal.rpow_one]
    _ ≤ (μ : Measure E) (Metric.closedBall x r) ^ a *
        (μ : Measure E) (Metric.closedBall y r) ^ b := by
      gcongr
      · exact hx
      · exact hy
    _ ≤ _ := by simpa only [hbeq] using hμ.closedBall_mul_le x y r a ha' ha1

end SupportConvexity

end Transport


section LinearEquivalence

variable {V₁ V₂ : Type*} [NormedAddCommGroup V₁] [InnerProductSpace ℝ V₁]
  [MeasurableSpace V₁] [BorelSpace V₁]
  [NormedAddCommGroup V₂] [InnerProductSpace ℝ V₂] [MeasurableSpace V₂] [BorelSpace V₂]

/-- The image of a log-concave law under a continuous linear equivalence is log-concave. -/
theorem mapContinuousLinearEquiv {ν : ProbabilityMeasure V₁} (hν : LogConcave ν)
    (T : V₁ ≃L[ℝ] V₂) : LogConcave (Probability.mapContinuousLinearEquiv ν T) :=
  hν.of_continuousLinearEquiv_map _ T.symm
    (Probability.measurePreserving_mapContinuousLinearEquiv_symm ν T).map_eq

end LinearEquivalence

section FullAffineSupport

variable {V₁ : Type*} [NormedAddCommGroup V₁] [InnerProductSpace ℝ V₁]
  [MeasurableSpace V₁] [FiniteDimensional ℝ V₁]

/-- A log-concave law with full affine support has support with nonempty interior. -/
theorem interior_support_nonempty_of_affineSupport_eq_top {ν : ProbabilityMeasure V₁}
    (hν : LogConcave ν) (h : Probability.affineSupport ν = ⊤) :
    (interior (ν : Measure V₁).support).Nonempty :=
  hν.convex_support.interior_nonempty_iff_affineSpan_eq_top.mpr h

end FullAffineSupport

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
  [FiniteDimensional ℝ E]

section IntrinsicSupport

omit [CompleteSpace E]
/-- Log-concavity is retained on the direction of the affine support, even for singular
ambient laws and a zero-dimensional carrier. -/
theorem intrinsicMeasure {μ : ProbabilityMeasure E} (hμ : LogConcave μ) :
    LogConcave (Probability.intrinsicMeasure μ) :=
  hμ.of_affineIsometry_map (Probability.intrinsicMeasure μ) (Probability.reconstruct μ)
    (Probability.measurePreserving_reconstruct μ).map_eq

/-- The intrinsic support has nonempty interior. This includes the singleton topology in
dimension zero and does not assert that the boundary has zero probability mass. -/
theorem interior_intrinsic_support_nonempty {μ : ProbabilityMeasure E}
    (hμ : LogConcave μ) :
    (interior (Probability.intrinsicMeasure μ :
      Measure (Probability.affineSupport μ).direction).support).Nonempty := by
  apply hμ.intrinsicMeasure.convex_support.interior_nonempty_iff_affineSpan_eq_top.mpr
  exact Probability.affineSupport_intrinsicMeasure μ

/-- The intrinsic support boundary is Haar-null. Transferring this null set to the probability
law still requires the separate absolute-continuity theorem. -/
theorem haar_frontier_intrinsic_support {μ : ProbabilityMeasure E}
    (hμ : LogConcave μ) (m : Measure (Probability.affineSupport μ).direction)
    [Measure.IsAddHaarMeasure m] :
    m (frontier (Probability.intrinsicMeasure μ : Measure _).support) = 0 :=
  hμ.intrinsicMeasure.convex_support.addHaar_frontier m

end IntrinsicSupport

section Conditioning

open ProbabilityTheory

/-- **Conditioning on a closed convex set preserves log-concavity**: if `μ` is log-concave (in the
compact-set sense of `LogConcave`) and `C` is closed and convex with `μ C ≠ 0`, then the
conditional law `μ[|C]` is log-concave. Used to truncate isotropic log-concave laws to balls
(BKL arXiv:2610.05474v1, p. 19: Theorem 4.1 reduces to compactly supported laws). -/
theorem cond {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] {μ : ProbabilityMeasure E} (hμ : LogConcave μ)
    {C : Set E} (hC : Convex ℝ C) (hCc : IsClosed C) (hpos : (μ : Measure E) C ≠ 0) :
    LogConcave (⟨(μ : Measure E)[|C], cond_isProbabilityMeasure hpos⟩ : ProbabilityMeasure E) := by
  intro K₀ K₁ hK₀ hK₁ t ht₀ ht₁
  change
    ((μ : Measure E)[|C] K₀) ^ t * ((μ : Measure E)[|C] K₁) ^ (1 - t) ≤
      (μ : Measure E)[|C]
        {z | ∃ x ∈ K₀, ∃ y ∈ K₁, z = t • x + (1 - t) • y}
  have hmain :
      (μ : Measure E) (K₀ ∩ C) ^ t * (μ : Measure E) (K₁ ∩ C) ^ (1 - t) ≤
        (μ : Measure E)
          {z | ∃ x ∈ K₀ ∩ C, ∃ y ∈ K₁ ∩ C,
            z = t • x + (1 - t) • y} :=
    hμ (K₀ ∩ C) (K₁ ∩ C) (hK₀.inter_right hCc) (hK₁.inter_right hCc) t ht₀ ht₁
  have hsubset :
      {z | ∃ x ∈ K₀ ∩ C, ∃ y ∈ K₁ ∩ C,
          z = t • x + (1 - t) • y} ⊆
        C ∩ {z | ∃ x ∈ K₀, ∃ y ∈ K₁,
          z = t • x + (1 - t) • y} := by
    intro z hz
    rcases hz with ⟨x, ⟨hx₀, hxC⟩, y, ⟨hy₀, hyC⟩, rfl⟩
    refine ⟨hC hxC hyC ht₀.le (sub_nonneg.mpr ht₁.le) (by ring), ?_⟩
    exact ⟨x, hx₀, y, hy₀, rfl⟩
  have hmono :
      (μ : Measure E)
          {z | ∃ x ∈ K₀ ∩ C, ∃ y ∈ K₁ ∩ C,
            z = t • x + (1 - t) • y} ≤
        (μ : Measure E)
          (C ∩ {z | ∃ x ∈ K₀, ∃ y ∈ K₁,
            z = t • x + (1 - t) • y}) :=
    measure_mono hsubset
  have hm_le_one : (μ : Measure E) C ≤ 1 := by
    calc
      (μ : Measure E) C ≤ (μ : Measure E) Set.univ :=
        measure_mono (Set.subset_univ C)
      _ = 1 := by simp
  have hm_top : (μ : Measure E) C ≠ ⊤ := by
    exact ne_of_lt (lt_of_le_of_lt hm_le_one (by simp))
  have hd₀ : ((μ : Measure E) C)⁻¹ ≠ 0 := by
    simp [hm_top]
  have hd_top : ((μ : Measure E) C)⁻¹ ≠ ⊤ := by
    simp [hpos]
  have hpow :
      ((μ : Measure E) C)⁻¹ ^ t * ((μ : Measure E) C)⁻¹ ^ (1 - t) =
        ((μ : Measure E) C)⁻¹ := by
    calc
      ((μ : Measure E) C)⁻¹ ^ t * ((μ : Measure E) C)⁻¹ ^ (1 - t) =
          ((μ : Measure E) C)⁻¹ ^ (t + (1 - t)) := by
            exact
              (ENNReal.rpow_add (x := ((μ : Measure E) C)⁻¹) t (1 - t) hd₀ hd_top).symm
      _ = ((μ : Measure E) C)⁻¹ := by
        rw [show t + (1 - t) = 1 by ring]
        simp
  have hfactor :
      (((μ : Measure E) C)⁻¹ * (μ : Measure E) (K₀ ∩ C)) ^ t *
          (((μ : Measure E) C)⁻¹ * (μ : Measure E) (K₁ ∩ C)) ^ (1 - t) =
        ((μ : Measure E) C)⁻¹ *
          ((μ : Measure E) (K₀ ∩ C) ^ t *
            (μ : Measure E) (K₁ ∩ C) ^ (1 - t)) := by
    calc
      (((μ : Measure E) C)⁻¹ * (μ : Measure E) (K₀ ∩ C)) ^ t *
            (((μ : Measure E) C)⁻¹ * (μ : Measure E) (K₁ ∩ C)) ^ (1 - t) =
          ((μ : Measure E) C)⁻¹ ^ t * (μ : Measure E) (K₀ ∩ C) ^ t *
            ((((μ : Measure E) C)⁻¹) ^ (1 - t) *
              (μ : Measure E) (K₁ ∩ C) ^ (1 - t)) := by
                rw [ENNReal.mul_rpow_of_nonneg
                      (x := ((μ : Measure E) C)⁻¹)
                      (y := (μ : Measure E) (K₀ ∩ C)) ht₀.le,
                  ENNReal.mul_rpow_of_nonneg
                      (x := ((μ : Measure E) C)⁻¹)
                      (y := (μ : Measure E) (K₁ ∩ C))
                      (sub_nonneg.mpr ht₁.le)]
      _ = ((μ : Measure E) C)⁻¹ ^ t *
            ((μ : Measure E) C)⁻¹ ^ (1 - t) *
              ((μ : Measure E) (K₀ ∩ C) ^ t *
                (μ : Measure E) (K₁ ∩ C) ^ (1 - t)) := by
                ac_rfl
      _ = ((μ : Measure E) C)⁻¹ *
          ((μ : Measure E) (K₀ ∩ C) ^ t *
            (μ : Measure E) (K₁ ∩ C) ^ (1 - t)) := by
              rw [hpow]
  have hcond₀ :
      (μ : Measure E)[|C] K₀ =
        ((μ : Measure E) C)⁻¹ * (μ : Measure E) (K₀ ∩ C) := by
    calc
      (μ : Measure E)[|C] K₀ =
          ((μ : Measure E) C)⁻¹ * (μ : Measure E) (C ∩ K₀) :=
        cond_apply' hK₀.measurableSet (μ : Measure E)
      _ = ((μ : Measure E) C)⁻¹ * (μ : Measure E) (K₀ ∩ C) := by
        rw [Set.inter_comm]
  have hcond₁ :
      (μ : Measure E)[|C] K₁ =
        ((μ : Measure E) C)⁻¹ * (μ : Measure E) (K₁ ∩ C) := by
    calc
      (μ : Measure E)[|C] K₁ =
          ((μ : Measure E) C)⁻¹ * (μ : Measure E) (C ∩ K₁) :=
        cond_apply' hK₁.measurableSet (μ : Measure E)
      _ = ((μ : Measure E) C)⁻¹ * (μ : Measure E) (K₁ ∩ C) := by
        rw [Set.inter_comm]
  have hcond₂ :
      (μ : Measure E)[|C]
          {z | ∃ x ∈ K₀, ∃ y ∈ K₁,
            z = t • x + (1 - t) • y} =
        ((μ : Measure E) C)⁻¹ *
          (μ : Measure E)
            (C ∩ {z | ∃ x ∈ K₀, ∃ y ∈ K₁,
              z = t • x + (1 - t) • y}) :=
    cond_apply hCc.measurableSet (μ : Measure E) _
  calc
    ((μ : Measure E)[|C] K₀) ^ t * ((μ : Measure E)[|C] K₁) ^ (1 - t) =
        (((μ : Measure E) C)⁻¹ * (μ : Measure E) (K₀ ∩ C)) ^ t *
          (((μ : Measure E) C)⁻¹ * (μ : Measure E) (K₁ ∩ C)) ^ (1 - t) := by
            rw [hcond₀, hcond₁]
    _ = ((μ : Measure E) C)⁻¹ *
          ((μ : Measure E) (K₀ ∩ C) ^ t *
            (μ : Measure E) (K₁ ∩ C) ^ (1 - t)) :=
      hfactor
    _ ≤ ((μ : Measure E) C)⁻¹ *
          (μ : Measure E)
            {z | ∃ x ∈ K₀ ∩ C, ∃ y ∈ K₁ ∩ C,
              z = t • x + (1 - t) • y} := by
      gcongr
    _ ≤ ((μ : Measure E) C)⁻¹ *
          (μ : Measure E)
            (C ∩ {z | ∃ x ∈ K₀, ∃ y ∈ K₁,
              z = t • x + (1 - t) • y}) := by
      gcongr
    _ = (μ : Measure E)[|C]
          {z | ∃ x ∈ K₀, ∃ y ∈ K₁,
            z = t • x + (1 - t) • y} :=
      hcond₂.symm

end Conditioning

end FunctionalInequalities.KLS.LogConcave
