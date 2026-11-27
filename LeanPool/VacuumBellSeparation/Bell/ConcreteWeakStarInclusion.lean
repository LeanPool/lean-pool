/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Bell.CoefficientWeakStarHomeomorphism
public import Mathlib.Analysis.Normed.Operator.Bilinear

/-!
Concrete inclusions preserve the actual coefficient weak-star topology.
The proof restricts the norm-closed span of original-H matrix coefficients;
it does not assume a normal-state extension or predual quotient theorem.
-/

@[expose] public section

noncomputable section
namespace VacuumBellSeparation.Bipartite

open scoped Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Continuous linear inclusion associated with an inclusion of von Neumann algebras. -/
def vnaInclusionCLM {M N : VonNeumannAlgebra H}
    (h : M.toStarSubalgebra ≤ N.toStarSubalgebra) :
    M.toStarSubalgebra →L[ℂ] N.toStarSubalgebra :=
  (StarSubalgebra.inclusion h).toLinearMap.mkContinuous 1 (by
    intro a
    change ‖a‖ ≤ 1 * ‖a‖
    rw [one_mul])

@[simp] theorem vnaInclusionCLM_apply {M N : VonNeumannAlgebra H}
    (h : M.toStarSubalgebra ≤ N.toStarSubalgebra) (a : M.toStarSubalgebra) :
    vnaInclusionCLM h a = StarSubalgebra.inclusion h a := rfl

theorem coefficientPredual_restrict {M N : VonNeumannAlgebra H}
    (h : M.toStarSubalgebra ≤ N.toStarSubalgebra)
    (f : StrongDual ℂ N.toStarSubalgebra) (hf : f ∈ coefficientPredual N) :
    f.comp (vnaInclusionCLM h) ∈ coefficientPredual M := by
  have hc : IsClosed {g : StrongDual ℂ N.toStarSubalgebra |
      g.comp (vnaInclusionCLM h) ∈ coefficientPredual M} :=
    (matrixCoefficientSpan M).isClosed_topologicalClosure.preimage
      (continuous_id.clm_comp_const (vnaInclusionCLM h))
  apply closure_minimal ?_ hc hf
  intro g hg
  induction hg using Submodule.span_induction with
  | mem g hg =>
      obtain ⟨⟨x, y⟩, rfl⟩ := hg
      have he : (matrixCoefficientDual N x y).comp (vnaInclusionCLM h) =
          matrixCoefficientDual M x y := by
        ext a
        rfl
      change (matrixCoefficientDual N x y).comp (vnaInclusionCLM h) ∈ coefficientPredual M
      rw [he]
      exact matrixCoefficientDual_mem_predual M x y
  | zero =>
      change (0 : StrongDual ℂ N.toStarSubalgebra).comp (vnaInclusionCLM h) ∈ coefficientPredual M
      rw [ContinuousLinearMap.zero_comp]
      exact (coefficientPredual M).zero_mem
  | add g k hg hk hgc hkc =>
      change (g + k).comp (vnaInclusionCLM h) ∈ coefficientPredual M
      rw [ContinuousLinearMap.add_comp]
      exact (coefficientPredual M).add_mem hgc hkc
  | smul c g hg hgc =>
      change (c • g).comp (vnaInclusionCLM h) ∈ coefficientPredual M
      rw [ContinuousLinearMap.smul_comp]
      exact (coefficientPredual M).smul_mem c hgc

theorem continuous_coefficientWeak_inclusion {M N : VonNeumannAlgebra H}
    (h : M.toStarSubalgebra ≤ N.toStarSubalgebra) :
    Continuous (X := CoefficientWeakAlgebra M) (Y := CoefficientWeakAlgebra N)
      (fun a => StarSubalgebra.inclusion h a) := by
  apply WeakBilin.continuous_of_continuous_eval (coefficientPairing N)
  intro f
  exact continuous_coefficientWeak_of_mem M (f.1.comp (vnaInclusionCLM h))
    (coefficientPredual_restrict h f.1 f.2)

theorem tendsto_coefficientWeak_inclusion {ι : Type*} {l : Filter ι}
    {M N : VonNeumannAlgebra H} (h : M.toStarSubalgebra ≤ N.toStarSubalgebra)
    {T : ι → M.toStarSubalgebra} {L : M.toStarSubalgebra}
    (hT : Filter.Tendsto (β := CoefficientWeakAlgebra M) (fun i => T i) l
      (nhds (X := CoefficientWeakAlgebra M) L)) :
    Filter.Tendsto (β := CoefficientWeakAlgebra N)
      (fun i => StarSubalgebra.inclusion h (T i)) l
        (nhds (X := CoefficientWeakAlgebra N) (StarSubalgebra.inclusion h L)) :=
  (continuous_coefficientWeak_inclusion h).continuousAt.tendsto.comp hT

end VacuumBellSeparation.Bipartite
