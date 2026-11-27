/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Bell.CoefficientPredualDuality
public import LeanPool.VacuumBellSeparation.Bell.CoefficientWeakTopology
public import Mathlib.Topology.Homeomorph.Defs

/-!
The literal coefficient weak topology on the original VNA is the weak-star
topology of its proved Banach predual, through the canonical evaluation map.
The inverse continuity is proved by each coefficient evaluation. There is
no assertion of global WOT equality or operator-norm compactness.
-/

@[expose] public section

noncomputable section
namespace VacuumBellSeparation.Bipartite

open scoped Topology ComplexOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem coefficientPredual_completeSpace (M : VonNeumannAlgebra H) :
    CompleteSpace (coefficientPredual M) := by
  change CompleteSpace (matrixCoefficientSpan M).topologicalClosure
  infer_instance

@[simp] theorem coefficientPredualDualEquiv_symm_eval (M : VonNeumannAlgebra H)
    (F : StrongDual ℂ (coefficientPredual M)) (f : coefficientPredual M) :
    f.1 ((coefficientPredualDualEquiv M).symm F) = F f := by
  exact congrArg (fun G : StrongDual ℂ (coefficientPredual M) => G f)
    ((coefficientPredualDualEquiv M).apply_symm_apply F)

/-- The canonical evaluation is a homeomorphism for the actual paired weak
topology and the actual weak-star dual topology. Its bijectivity was proved
from the original WOT unit ball, rather than assumed in the topology. -/
def coefficientWeakDualHomeomorph (M : VonNeumannAlgebra H) :
    CoefficientWeakAlgebra M ≃ₜ WeakDual ℂ (coefficientPredual M) where
  toEquiv := (coefficientPredualDualEquiv M).toEquiv.trans StrongDual.toWeakDual.toEquiv
  continuous_toFun := by
    apply WeakDual.continuous_of_continuous_eval
    intro f
    exact WeakBilin.eval_continuous (coefficientPairing M) f
  continuous_invFun := by
    apply WeakBilin.continuous_of_continuous_eval
    intro f
    change Continuous (fun F : WeakDual ℂ (coefficientPredual M) =>
      f.1 ((coefficientPredualDualEquiv M).symm (WeakDual.toStrongDual F)))
    simpa only [coefficientPredualDualEquiv_symm_eval, WeakDual.toStrongDual_apply] using
      (WeakDual.eval_continuous (𝕜 := ℂ) f)

@[simp] theorem coefficientWeakDualHomeomorph_apply (M : VonNeumannAlgebra H)
    (a : CoefficientWeakAlgebra M) (f : coefficientPredual M) :
    coefficientWeakDualHomeomorph M a f = f.1 a := rfl

@[simp] theorem coefficientWeakDualHomeomorph_symm_apply (M : VonNeumannAlgebra H)
    (F : WeakDual ℂ (coefficientPredual M)) :
    (coefficientWeakDualHomeomorph M).symm F =
      (coefficientPredualDualEquiv M).symm (WeakDual.toStrongDual F) := rfl

/-- Order normality is continuity in the actual weak-star topology transported
through the proved canonical dual identification. -/
theorem isNormalFunctional_iff_continuous_weakStar
    (M : VonNeumannAlgebra H) (φ : M.toStarSubalgebra →ₚ[ℂ] ℂ) :
    IsNormalFunctional M φ ↔
      Continuous (fun F : WeakDual ℂ (coefficientPredual M) =>
        φ ((coefficientWeakDualHomeomorph M).symm F)) := by
  rw [isNormalFunctional_iff_continuous_coefficientWeak M φ]
  constructor
  · intro h
    exact h.comp (coefficientWeakDualHomeomorph M).symm.continuous
  · intro h
    have hc := h.comp (coefficientWeakDualHomeomorph M).continuous
    simpa only [Function.comp_def, Homeomorph.symm_apply_apply] using hc

end VacuumBellSeparation.Bipartite
