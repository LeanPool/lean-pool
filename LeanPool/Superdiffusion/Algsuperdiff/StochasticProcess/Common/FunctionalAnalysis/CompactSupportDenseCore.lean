/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import Mathlib.Topology.ContinuousMap.BoundedCompactlySupported
public import Mathlib.Topology.ContinuousMap.CompactlySupported
public import Mathlib.Topology.UrysohnsLemma

/-!
# CompactSupportDenseCore

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Compactly supported functions as a dense core of `C₀`

This file realizes compactly supported bounded continuous functions as a norm-preserving
continuous linear subspace of `C₀`.  On a locally compact regular space, its inclusion has dense
range.  The density proof cuts a function off by a compactly supported Urysohn function.

This is purely functional-analytic infrastructure.  In applications to divergence-form
regularity, a separate support-preserving smoothing argument can refine this continuous core to a
smooth compactly supported core.
-/

open Filter Set Topology
open scoped BoundedContinuousFunction ZeroAtInfty

noncomputable section

namespace DivergenceFormProcess.FunctionalAnalysis

variable {X : Type*} [TopologicalSpace X]

/-- Compactly supported bounded continuous real-valued functions, equipped with the uniform norm. -/
abbrev CompactSupportCore (X : Type*) [TopologicalSpace X] := compactlySupported X ℝ

/-- The linear inclusion of the compact-support core into continuous functions vanishing at
infinity. -/
def compactSupportCoreToC0Linear : CompactSupportCore X →ₗ[ℝ] C₀(X, ℝ) where
  toFun f :=
    { toFun := f
      continuous_toFun := f.val.continuous
      zero_at_infty' := HasCompactSupport.is_zero_at_infty
        (mem_compactlySupported.mp f.property) }
  map_add' _ _ := by ext; rfl
  map_smul' _ _ := by ext; rfl

/-- The compact-support inclusion preserves the uniform norm. -/
theorem norm_compactSupportCoreToC0Linear (f : CompactSupportCore X) :
    ‖compactSupportCoreToC0Linear f‖ = ‖f‖ := by
  rw [← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
  rfl

/-- The norm-preserving continuous linear inclusion of the compact-support core into `C₀`. -/
def compactSupportCoreToC0 : CompactSupportCore X →L[ℝ] C₀(X, ℝ) :=
  LinearMap.mkContinuous compactSupportCoreToC0Linear 1 (fun f ↦ by
    rw [one_mul, norm_compactSupportCoreToC0Linear])

/-- Compactly supported bounded continuous functions are uniformly dense in `C₀` on a locally
compact regular space. -/
theorem denseRange_compactSupportCoreToC0 [R1Space X] [LocallyCompactSpace X] :
    DenseRange (compactSupportCoreToC0 (X := X)) := by
  change Dense (range (compactSupportCoreToC0 (X := X)))
  rw [Metric.dense_iff]
  intro f ε hε
  have hhalf : 0 < ε / 2 := half_pos hε
  have hevent : {x : X | dist (f x) 0 < ε / 2} ∈ cocompact X :=
    (Metric.tendsto_nhds.mp (zero_at_infty f)) (ε / 2) hhalf
  obtain ⟨K, hKcompact, hK⟩ := mem_cocompact.mp hevent
  obtain ⟨φ, hφK, -, hφcompact, hφrange⟩ :=
    exists_continuous_one_zero_of_isCompact hKcompact isClosed_empty (disjoint_empty K)
  let φ₀ : C₀(X, ℝ) :=
    { toFun := φ
      continuous_toFun := φ.continuous
      zero_at_infty' := hφcompact.is_zero_at_infty }
  let g₀ : C₀(X, ℝ) := φ₀ * f
  have hg₀compact : HasCompactSupport g₀ := hφcompact.mul_right
  let g : CompactSupportCore X :=
    ⟨g₀.toBCF, mem_compactlySupported.mpr hg₀compact⟩
  refine ⟨compactSupportCoreToC0 g, ?_, ⟨g, rfl⟩⟩
  rw [Metric.mem_ball, dist_eq_norm, ← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
  apply lt_of_le_of_lt _ (half_lt_self hε)
  apply (BoundedContinuousFunction.norm_le hhalf.le).2
  intro x
  have hpoint : (compactSupportCoreToC0 g - f).toBCF x = φ x * f x - f x := by rfl
  rw [hpoint, ← norm_neg, neg_sub]
  by_cases hx : x ∈ K
  · rw [hφK hx]
    simp only [Pi.one_apply, one_mul, sub_self, norm_zero]
    exact hhalf.le
  · have hfx : ‖f x‖ < ε / 2 := by
      simpa only [Real.dist_eq, sub_zero, Real.norm_eq_abs] using! hK hx
    rw [show f x - φ x * f x = (1 - φ x) * f x by ring]
    rw [norm_mul, Real.norm_eq_abs,
      abs_of_nonneg (sub_nonneg.mpr (hφrange x).2)]
    exact (mul_le_of_le_one_left (norm_nonneg (f x))
      (sub_le_self 1 (hφrange x).1)).trans hfx.le

end DivergenceFormProcess.FunctionalAnalysis
