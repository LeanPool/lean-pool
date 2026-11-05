/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.ForcingCorrection
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.CoarseGrainingL2Interior

/-!
# ReplacementDatum

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The coarse-graining datum, populated

Nothing here imports that file, and nothing here claims the anchor or any
source node.

## References

* ABK26, `l.harmonic.approximation.good.scales`.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open HCPolySupport HCPolySupport.Book
open scoped ENNReal

noncomputable section

variable {d : ℕ} [NeZero d] {Q : TriadicCube d}

/-! ## 1. The populated datum -/

/-- **The coarse-graining comparison datum, constructed.**

`u` is the given solution of `−∇·a∇u = ∇·g`; `v` is the auxiliary
constant-coefficient solution `v_g`; the zero-trace difference is the chosen
corrector, and the identity `u − v_g = ρ_g` holds pointwise. -/
def coarseGrainingDatum (a : Ch03.CoeffFamily d) (a0 : Ch03.ConstantCoeffMatrix d)
    {u : H1Function (openCubeSet Q)} {g : Vec d → Vec d}
    (hu : Ch03.IsForcedEquation Q a u g) (hg : MemVectorL2 (openCubeSet Q) g) :
    Ch03.CoarseGrainingComparisonDatum Q a a0 g where
  u := u
  v := forcedReplacement a0 u hg
  uWeakSolution := hu
  vWeakSolution := isConstantCoeffForcedEquation_forcedReplacement a0 u hg
  zeroTraceDifference :=
    ⟨dirichletCorrector a0 u hg,
      Filter.Eventually.of_forall fun x => dirichletCorrector_toFun_eq_sub a0 u hg x⟩

@[simp] theorem coarseGrainingDatum_u (a : Ch03.CoeffFamily d)
    (a0 : Ch03.ConstantCoeffMatrix d) {u : H1Function (openCubeSet Q)}
    {g : Vec d → Vec d} (hu : Ch03.IsForcedEquation Q a u g)
    (hg : MemVectorL2 (openCubeSet Q) g) :
    (coarseGrainingDatum a a0 hu hg).u = u :=
  rfl

@[simp] theorem coarseGrainingDatum_v (a : Ch03.CoeffFamily d)
    (a0 : Ch03.ConstantCoeffMatrix d) {u : H1Function (openCubeSet Q)}
    {g : Vec d → Vec d} (hu : Ch03.IsForcedEquation Q a u g)
    (hg : MemVectorL2 (openCubeSet Q) g) :
    (coarseGrainingDatum a a0 hu hg).v = forcedReplacement a0 u hg :=
  rfl

/-! ## 2. The `H¹₀` test function on the half-open cube -/

/-- The chosen corrector, transported to the half-open cube: the `H¹₀` function
whose value is `u − v_g` and whose gradient is `∇u − ∇v_g`. -/
def replacementDefect (a0 : Ch03.ConstantCoeffMatrix d)
    (u : H1Function (openCubeSet Q)) {g : Vec d → Vec d}
    (hg : MemVectorL2 (openCubeSet Q) g) : H10Function (cubeSet Q) :=
  (dirichletCorrector a0 u hg).toCubeSet

theorem replacementDefect_grad (a : Ch03.CoeffFamily d)
    (a0 : Ch03.ConstantCoeffMatrix d) {u : H1Function (openCubeSet Q)}
    {g : Vec d → Vec d} (hu : Ch03.IsForcedEquation Q a u g)
    (hg : MemVectorL2 (openCubeSet Q) g) (x : Vec d) :
    (replacementDefect a0 u hg).toH1Function.grad x =
      (coarseGrainingDatum a a0 hu hg).u.grad x -
        (coarseGrainingDatum a a0 hu hg).v.grad x := by
  rw [replacementDefect, H10Function.toCubeSet_toH1Function_grad,
    coarseGrainingDatum_u, coarseGrainingDatum_v]
  exact dirichletCorrector_grad_eq_sub a0 u hg x

end

end Algsuperdiff.Section4.Provider.ExcessDecay
