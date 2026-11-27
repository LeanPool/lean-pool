/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Analysis.LocallyConvex.WeakDual
public import Mathlib.Analysis.Normed.Module.RCLike.Extend
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Topology.Algebra.Module.Spaces.WeakDual

/-!
The dual of a concrete subspace of E* is recovered from E if the image of
the original closed unit ball is weak-star compact. Surjectivity is proved
by separation and the weak representation theorem, not assumed. No
reflexivity, norm-attainment, nonzero vector or normality premise is used.
-/

@[expose] public section

noncomputable section
namespace VacuumBellSeparation.Bipartite

open Metric
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]

/-- Real-part control on the complex unit ball controls the exact dual norm.
The real-part restriction is isometric, and testing x and -x controls its
absolute value. No functional is asserted to attain its norm. -/
theorem dual_norm_le_of_re_le_unitBall (f : StrongDual ℂ E) (u : ℝ)
    (hu : 0 ≤ u) (h : ∀ x : E, ‖x‖ ≤ 1 → (f x).re ≤ u) : ‖f‖ ≤ u := by
  let fr : StrongDual ℝ E := (StrongDual.extendRCLikeₗᵢ (𝕜 := ℂ) (F := E)).symm f
  have he (x : E) : fr x = (f x).re := rfl
  have hn : ‖fr‖ = ‖f‖ := (StrongDual.extendRCLikeₗᵢ (𝕜 := ℂ) (F := E)).symm.norm_map f
  rw [← hn]
  apply ContinuousLinearMap.opNorm_le_of_unit_norm hu
  intro x hx
  rw [he, Real.norm_eq_abs]
  apply abs_le.mpr
  constructor
  · have hm := h (-x) (by simpa only [norm_neg, hx] using (le_refl (1 : ℝ)))
    simp only [map_neg, Complex.neg_re] at hm
    linarith
  · exact h x hx.le

/-- Canonical subtype and dual structures, cached before dependent dual headers. -/
instance dualEvaluationSubmoduleNormed (P : Submodule ℂ (StrongDual ℂ E)) :
    NormedAddCommGroup P := Submodule.normedAddCommGroup P

instance dualEvaluationSubmoduleSpace (P : Submodule ℂ (StrongDual ℂ E)) :
    NormedSpace ℂ P := Submodule.normedSpace P

instance dualEvaluationSecondDualNormed (P : Submodule ℂ (StrongDual ℂ E)) :
    NormedAddCommGroup (StrongDual ℂ P) := ContinuousLinearMap.toNormedAddCommGroup

instance dualEvaluationWeakAddGroup (P : Submodule ℂ (StrongDual ℂ E)) :
    AddCommGroup (WeakDual ℂ P) := WeakDual.instAddCommGroup

instance dualEvaluation_weakTower (P : Submodule ℂ (StrongDual ℂ E)) :
    IsScalarTower ℝ ℂ (WeakDual ℂ P) :=
  inferInstanceAs (IsScalarTower ℝ ℂ (P →L[ℂ] ℂ))

/-- Compactness of the literal evaluation image gives every dual unit vector
an original unit-ball preimage. The only pairing hypothesis is its formula. -/
theorem exists_unitBall_preimage_of_isCompact_evaluation
    (P : Submodule ℂ (StrongDual ℂ E)) (J : E →ₗ[ℂ] StrongDual ℂ P)
    (hJ : ∀ (x : E) (p : P), J x p = p.1 x)
    (hc : IsCompact ((fun x : E => StrongDual.toWeakDual (J x)) ''
      Metric.closedBall (0 : E) 1))
    (F : StrongDual ℂ P) (hF : ‖F‖ ≤ 1) :
    ∃ x : E, ‖x‖ ≤ 1 ∧ J x = F := by
  let : Module ℝ (WeakDual ℂ P) := Module.restrictScalars ℝ ℂ (WeakDual ℂ P)
  let : IsScalarTower ℝ ℂ (WeakDual ℂ P) := IsScalarTower.restrictScalars _ _ _
  let : LocallyConvexSpace ℝ (WeakDual ℂ P) :=
    (topDualPairing ℂ P).weakBilin_withSeminorms.toLocallyConvexSpace
  let W : E →ₗ[ℂ] WeakDual ℂ P := StrongDual.toWeakDual.toLinearMap.comp J
  have hconv : Convex ℝ (W '' Metric.closedBall (0 : E) 1) :=
    (convex_closedBall (0 : E) 1).linear_image (W.restrictScalars ℝ)
  have hc' : IsCompact (W '' Metric.closedBall (0 : E) 1) := hc
  have hmem : StrongDual.toWeakDual F ∈ W '' Metric.closedBall (0 : E) 1 := by
    by_contra hn
    obtain ⟨ell, u, hs, ht⟩ := RCLike.geometric_hahn_banach_closed_point
      (𝕜 := ℂ) (E := WeakDual ℂ P) hconv hc'.isClosed hn
    obtain ⟨p, hp⟩ := LinearMap.dualEmbedding_surjective (topDualPairing ℂ P) ell
    have he (z : WeakDual ℂ P) : ell z = z p := by
      rw [← hp]
      rfl
    have hu : 0 ≤ u := by
      have hz := hs (W 0) ⟨0, by simp, rfl⟩
      simpa only [map_zero, Complex.zero_re] using hz.le
    have hpbound : ‖(p : StrongDual ℂ E)‖ ≤ u := by
      apply dual_norm_le_of_re_le_unitBall p.1 u hu
      intro x hx
      have h := hs (W x) ⟨x, mem_closedBall_zero_iff.mpr hx, rfl⟩
      rw [he] at h
      change (J x p).re < u at h
      rw [hJ] at h
      exact h.le
    have hlarge : u < (F p).re := by
      simpa only [he, StrongDual.toWeakDual_apply, RCLike.re_to_complex] using ht
    have hsmall : (F p).re ≤ u := calc
      _ ≤ ‖F p‖ := Complex.re_le_norm _
      _ ≤ ‖F‖ * ‖p‖ := F.le_opNorm p
      _ ≤ 1 * ‖p‖ := mul_le_mul_of_nonneg_right hF (norm_nonneg _)
      _ = ‖p‖ := one_mul _
      _ ≤ u := hpbound
    exact (not_lt_of_ge hsmall) hlarge
  obtain ⟨x, hx, hxe⟩ := hmem
  refine ⟨x, mem_closedBall_zero_iff.mp hx, ?_⟩
  exact StrongDual.toWeakDual.injective hxe

/-- Scaling the proved unit-ball preimage theorem gives actual surjectivity.
Zero functionals are handled directly, without a nontrivial-space premise. -/
theorem surjective_of_isCompact_evaluation
    (P : Submodule ℂ (StrongDual ℂ E)) (J : E →ₗ[ℂ] StrongDual ℂ P)
    (hJ : ∀ (x : E) (p : P), J x p = p.1 x)
    (hc : IsCompact ((fun x : E => StrongDual.toWeakDual (J x)) ''
      Metric.closedBall (0 : E) 1)) : Function.Surjective J := by
  intro F
  by_cases hF : F = 0
  · refine ⟨0, ?_⟩
    simp only [map_zero, hF]
  · let c : ℂ := (‖F‖ : ℂ)
    have hc0 : c ≠ 0 := by
      change (‖F‖ : ℂ) ≠ 0
      exact Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hF)
    have hcn : ‖c‖ = ‖F‖ := by simp [c]
    have hscaled : ‖c⁻¹ • F‖ ≤ 1 := by
      rw [norm_smul, norm_inv, hcn, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hF)]
    obtain ⟨x, _, hx⟩ := exists_unitBall_preimage_of_isCompact_evaluation P J hJ hc
      (c⁻¹ • F) hscaled
    refine ⟨c • x, ?_⟩
    rw [map_smul, hx, smul_smul, mul_inv_cancel₀ hc0, one_smul]

end VacuumBellSeparation.Bipartite
