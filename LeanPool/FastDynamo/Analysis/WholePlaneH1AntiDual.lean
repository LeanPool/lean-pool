/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Analysis.AntiDual
public import LeanPool.FastDynamo.Analysis.WholePlaneH1Core
public import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Ambient `H¹` anti-duals as tempered distributions

This file realizes a continuous conjugate-linear functional on the concrete
whole-plane `H¹` graph as an element of the standard Bessel-potential
`H⁻¹` space.  Composing with the Sobolev realization of `WholePlaneSobolev` then gives a
canonical tempered distribution.

The coefficient pairing below records the normalization explicitly: the
functional is evaluated after the actual `h1CoeffToGraph` synthesis map,
rather than after an unproved identification of the graph and Bessel norms.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

/-- The `L²` Riesz coefficient of an anti-dual functional on the concrete
whole-plane `H¹` graph. -/
def wholePlaneH1AntiDualCoeff
    (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [CompleteSpace F] :
    (WholePlaneH1 F →L⋆[ℂ] ℂ) →L[ℂ] WholePlaneL2 F :=
  (h1CoeffToGraph F).adjoint.comp
    (complexToAntiDual (E := WholePlaneH1 F)).symm.toContinuousLinearEquiv.toContinuousLinearMap

/-- A continuous anti-dual functional on the concrete whole-plane `H¹`
graph, bundled canonically as a standard whole-plane `H⁻¹` element. -/
def wholePlaneH1AntiDualToSobolevMinusOne
    (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [CompleteSpace F] :
    (WholePlaneH1 F →L⋆[ℂ] ℂ) →L[ℂ] WholePlaneSobolev (-1) F :=
  (wholePlaneSobolevCoeff (-1) F).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (wholePlaneH1AntiDualCoeff F)

/-- The tempered distribution represented by a continuous anti-dual
functional on the concrete whole-plane `H¹` graph. -/
def wholePlaneH1AntiDualToTempered
    (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [CompleteSpace F] :
    (WholePlaneH1 F →L⋆[ℂ] ℂ) →L[ℂ]
      TemperedDistribution WholePlane F :=
  (wholePlaneSobolevToTempered (-1) F).comp
    (wholePlaneH1AntiDualToSobolevMinusOne F)

/-- The standard `H⁻¹` representative reproduces the original anti-dual
functional after the concrete `H¹` coefficient synthesis. -/
theorem wholePlaneH1AntiDualToSobolevMinusOne_pair
    (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [CompleteSpace F]
    (d : WholePlaneH1 F →L⋆[ℂ] ℂ) (c : WholePlaneL2 F) :
    d (h1CoeffToGraph F c) =
      inner ℂ c
        (wholePlaneSobolevCoeff (-1) F
          (wholePlaneH1AntiDualToSobolevMinusOne F d)) := by
  change d (h1CoeffToGraph F c) =
    inner ℂ c
      ((h1CoeffToGraph F).adjoint
        ((complexToAntiDual (E := WholePlaneH1 F)).symm d))
  calc
    d (h1CoeffToGraph F c) =
        inner ℂ (h1CoeffToGraph F c)
          ((complexToAntiDual (E := WholePlaneH1 F)).symm d) := by
      rw [← complexToAntiDual_apply_apply]
      rw [(complexToAntiDual (E := WholePlaneH1 F)).apply_symm_apply]
    _ = _ := ((h1CoeffToGraph F).adjoint_inner_right c
      ((complexToAntiDual (E := WholePlaneH1 F)).symm d)).symm

/-- The standard `H⁻¹` representative retains all information in the
original anti-dual functional. -/
theorem wholePlaneH1AntiDualToSobolevMinusOne_injective
    (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [CompleteSpace F] :
    Function.Injective (wholePlaneH1AntiDualToSobolevMinusOne F) := by
  intro d e hde
  ext phi
  obtain ⟨c, rfl⟩ := h1CoeffToGraph_surjective F phi
  rw [wholePlaneH1AntiDualToSobolevMinusOne_pair,
    wholePlaneH1AntiDualToSobolevMinusOne_pair]
  exact congrArg (fun s : WholePlaneSobolev (-1) F =>
    inner ℂ c (wholePlaneSobolevCoeff (-1) F s)) hde

/-- The tempered realization of an ambient whole-plane `H¹` anti-dual is
injective. -/
theorem wholePlaneH1AntiDualToTempered_injective
    (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [CompleteSpace F] :
    Function.Injective (wholePlaneH1AntiDualToTempered F) :=
  (wholePlaneSobolevToTempered_injective (-1) F).comp
    (wholePlaneH1AntiDualToSobolevMinusOne_injective F)

end

end FastDynamo
