/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Bell.NormalFunctionalFiniteVectorApproximation
public import LeanPool.VacuumBellSeparation.Bell.BoundedWOTFunctionalContinuity
public import LeanPool.VacuumBellSeparation.Bell.GNSNormalDirectedSuprema
public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.Analysis.InnerProductSpace.WeakOperatorTopology
public import Mathlib.Topology.Algebra.GroupWithZero

/-!
Order-normal positive functionals are continuous on the original bounded
WOT balls by ACTUAL finite-vector norm approximation. This applies to all
GNS diagonal coefficients. Polarization gives every matrix coefficient,
without assuming that the GNS representation image is already a VNA.
-/

@[expose] public section

noncomputable section
namespace VacuumBellSeparation.Bipartite

open scoped Topology ComplexOrder InnerProductSpace ComplexConjugate

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

instance normalWOT_vna_closed (M : VonNeumannAlgebra H) :
    IsClosed (M.toStarSubalgebra : Set (H →L[ℂ] H)) := isClosed_vonNeumannAlgebra M

/-- No global-WOT continuity is asserted: the domain is the actual bounded ball. -/
theorem continuous_vnaWOTBall_eval_of_positive_normal
    (M : VonNeumannAlgebra H) (R : ℝ)
    (φ : M.toStarSubalgebra →ₚ[ℂ] ℂ) (hn : IsNormalFunctional M φ) :
    Continuous (fun T : vnaWOTBall M R => φ (vnaWOTBallElement T)) := by
  apply continuous_vnaWOTBall_eval_of_norm_approximation M R
    (PositiveContinuousLinearMap.ofClass φ).toContinuousLinearMap
  intro ε hε
  obtain ⟨n, ξ, hξ⟩ := exists_finite_vectors_approx_normalFunctional M φ hn hε
  refine ⟨(PositiveContinuousLinearMap.ofClass (finiteVectorFunctional M ξ)).toContinuousLinearMap,
    continuous_vnaWOTBall_eval_of_finite_coefficients M R _ ?_, hξ⟩
  refine ⟨n, ξ, ξ, fun _ => 1, ?_⟩
  intro a
  change finiteVectorFunctional M ξ a = ∑ i, (1 : ℂ) * ⟪ξ i, (a : H →L[ℂ] H) (ξ i)⟫_ℂ
  simpa only [one_mul] using finiteVectorFunctional_apply M ξ a

/-- Actual completed-GNS diagonal coefficients, pulled back to original M. -/
theorem continuous_gns_diagonal_on_vnaWOTBall
    (M : VonNeumannAlgebra H) (R : ℝ)
    (φ : M.toStarSubalgebra →ₚ[ℂ] ℂ) (hn : IsNormalFunctional M φ) (x : φ.GNS) :
    Continuous (fun T : vnaWOTBall M R =>
      inner ℂ x (φ.gnsStarAlgHom (vnaWOTBallElement T) x)) :=
  continuous_vnaWOTBall_eval_of_positive_normal M R (gnsVectorPositiveLinearMap M φ x)
    (gns_vectorFunctional_isNormal M φ hn x)

/-- Continuity of the diagonal coefficients of a family of bounded operators
implies continuity of every matrix coefficient. -/
theorem continuous_inner_apply_of_diagonal {E X : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [TopologicalSpace X] (A : X → E →L[ℂ] E)
    (h : ∀ z : E, Continuous (fun t => inner ℂ z (A t z))) (x y : E) :
    Continuous (fun t => inner ℂ x (A t y)) := by
  let q (z : E) (t : X) : ℂ := inner ℂ (A t z) z
  have hq (z : E) : Continuous (q z) :=
    (Complex.continuous_conj.comp (h z)).congr (fun t => inner_conj_symm (A t z) z)
  have hpoly := (((hq (x + y)).sub (hq (x - y))).add
    ((hq (x + Complex.I • y)).const_mul Complex.I)).sub
      ((hq (x - Complex.I • y)).const_mul Complex.I)
  refine (Complex.continuous_conj.comp (hpoly.div_const 4)).congr fun t => ?_
  calc
    _ = conj (inner ℂ (A t y) x) :=
      congrArg conj (inner_map_polarization (A t).toLinearMap x y).symm
    _ = inner ℂ x (A t y) := inner_conj_symm x (A t y)

/-- Complex polarization uses the actual linear operator; self-adjointness
of the observable is not assumed. Both vector arguments range over all GNS. -/
theorem continuous_gns_coefficient_on_vnaWOTBall
    (M : VonNeumannAlgebra H) (R : ℝ)
    (φ : M.toStarSubalgebra →ₚ[ℂ] ℂ) (hn : IsNormalFunctional M φ) (x y : φ.GNS) :
    Continuous (fun T : vnaWOTBall M R =>
      inner ℂ x (φ.gnsStarAlgHom (vnaWOTBallElement T) y)) :=
  continuous_inner_apply_of_diagonal
    (fun T : vnaWOTBall M R => φ.gnsStarAlgHom (vnaWOTBallElement T))
    (continuous_gns_diagonal_on_vnaWOTBall M R φ hn) x y

/-- The actual representation is WOT-continuous on each bounded original ball.
No faithfulness or unit normalization is needed for this continuity assertion. -/
theorem continuous_gns_on_vnaWOTBall
    (M : VonNeumannAlgebra H) (R : ℝ)
    (φ : M.toStarSubalgebra →ₚ[ℂ] ℂ) (hn : IsNormalFunctional M φ) :
    Continuous (fun T : vnaWOTBall M R =>
      ContinuousLinearMapWOT.ofCLM (φ.gnsStarAlgHom (vnaWOTBallElement T))) := by
  apply ContinuousLinearMapWOT.continuous_iff.mpr
  intro x y
  exact continuous_gns_coefficient_on_vnaWOTBall M R φ hn y x

end VacuumBellSeparation.Bipartite
