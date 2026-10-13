/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.Corrector.FreshShellUniqueness

/-!
# MeasurablePrereqSolutionOperator

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The solution operator of `e.def.w` as a continuous map of the forcing class

`FreshShellExistence` produces, and `FreshShellUniqueness` pins down, the two
correctors of `e.def.w` *one sample point at a time*: for each `omega` there is
a zero-trace Dirichlet solution and a mean-zero Neumann solution, and their
gradients are unique.  Nothing in that pair of statements says how the gradient
varies with the forcing, and therefore nothing in it can produce measurability
of `omega |-> grad w(omega)`: a `Classical.choose` selection is not measurable
for any reason coming from choice.

This module supplies the missing structural fact -- the *anticipated forgotten
Section 2 prerequisite* -- in the strongest form the development needs:

> the weak-solution gradient, read in the `L^2` carrier, is the value at the
> `L^2` class of the forcing of a fixed **continuous** map, the same map for
> every sample point.

Everything is assembled from CoarseGraining's own Hilbert-space realization of
the two variational problems, so no new analysis is performed here; what is new
is that the Lax--Milgram inverse is exposed as a map of the forcing *class*
rather than of a forcing *function together with a membership proof*, and that
the map is proved continuous.

## What is proved here

* `dirichletForcingRieszOfClass`, `dirichletGradientOfForcingClass` and
  `continuous_dirichletGradientOfForcingClass`: the Dirichlet solution operator
  `HilbertVectorL2 U -> HilbertVectorL2 U`, and its continuity.
* `gradToHilbertVectorL2_eq_dirichletGradientOfForcingClass`: **every** zero-trace
  Dirichlet weak solution with forcing `g` has gradient equal to the value of
  that operator at the class of `g`.  No selection, no choice, no measurability
  hypothesis.
* `neumannForcingRieszOfClass`, `neumannGradientOfForcingClass`,
  `continuous_neumannGradientOfForcingClass` and
  `gradToHilbertVectorL2_eq_neumannGradientOfForcingClass`: the mean-zero Neumann
  mirror of the four statements above.

## Method

For the Dirichlet leg the argument is the Lax--Milgram uniqueness clause read
backwards.  Given a weak solution `u`, its gradient class `z_u` lies in
CoarseGraining's closed potential-zero-trace subspace, and for every element
`w` of that subspace the closure-realization hypothesis writes `w` as the
gradient of an `H^1_0` function, so the weak formulation of `u` tested against
that function says exactly `B z_u w = <G, w>`.  Since the inner product
determines an element, `z_u` is the Lax--Milgram preimage of the Riesz
representative of the forcing class, which is the definition of the operator
below.

For the Neumann leg CoarseGraining already exports the corresponding uniqueness
statement
(`gradToVectorL2_eq_coeffGradientProblemSolution_of_h1CoerciveEstimate`), so
the only work is to transport it from the plain carrier `VectorL2` to the
Hilbert carrier `HilbertVectorL2` and to recognize CoarseGraining's canonical
solution as the value of the operator.

The continuity of both operators is the continuity of a composition of four
continuous maps: the Riesz isometry of the ambient `L^2`, restriction of a
functional along a fixed continuous linear map, the inverse Riesz isometry of
the solution space, and the Lax--Milgram continuous linear equivalence.

## Why the Hilbert carrier

`HilbertVectorL2 U` carries CoarseGraining's Borel measurable structure
(`instMeasurableSpaceHilbertVectorL2`, `instBorelSpaceHilbertVectorL2`), while
the plain carrier `VectorL2 U` carries none.  All statements below are
therefore phrased in the Hilbert carrier, which is also the carrier in which
the two CoarseGraining variational problems are solved.

## References

* ABK26, `e.def.w` (the two corrector problems).
* CoarseGraining, `Homogenization//Dirichlet.lean` (the
  `PotentialZeroTraceHilbert` layer) and `Homogenization//Neumann.lean` (the
  `H1CoerciveHilbert` layer).
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.Corrector

open HCPolySupport MeasureTheory
open HCPolySupport.PotentialZeroTraceHilbert

noncomputable section

variable {d : ℕ} {U : Set (Vec d)} [IsFiniteMeasure (volumeMeasureOn U)]

/-! ## The Dirichlet leg -/

/-- Unconditional: the Riesz representative, inside CoarseGraining's closed
potential-zero-trace subspace, of the forcing functional attached to an ambient
`L^2` class `G`.

This is `PotentialZeroTraceHilbert.forcingRieszRep` with the forcing *function
plus membership proof* replaced by the forcing *class*; the two agree
definitionally (`dirichletForcingRieszOfClass_toHilbertVectorL2OfVecField`). -/
def dirichletForcingRieszOfClass (M : PotentialSolenoidalL2Data U)
    (G : HilbertVectorL2 U) : Space M :=
  forcingRieszMap M ((InnerProductSpace.toDual ℝ (HilbertVectorL2 U) G).comp
    ((submodule (M := M)).subtypeL))

/-- Unconditional: **the Dirichlet solution operator of `e.def.w`.**  It sends
the `L^2` class of the forcing to the `L^2` class of the gradient of the
zero-trace weak solution.

The two hypotheses are the standing domain data of the variational problem:
`hne`, nonemptiness of the domain, and `hEll`, uniform ellipticity of the
coefficient field.  Both are discharged on every open triadic cube for the
ambient Laplacian (`Provider.Corrector.nonempty_openCubeSet`,
`isEllipticFieldOn_const_one_openCubeSet`). -/
def dirichletGradientOfForcingClass {a : CoeffField d} {lam Lam : ℝ}
    (M : PotentialSolenoidalL2Data U) (hne : Set.Nonempty U)
    (hEll : IsEllipticFieldOn lam Lam U a) (G : HilbertVectorL2 U) :
    HilbertVectorL2 U :=
  field ((isCoercive_coeffBilin (M := M) hne hEll).continuousLinearEquivOfBilin.symm
    (dirichletForcingRieszOfClass M G))

omit [IsFiniteMeasure (volumeMeasureOn U)] in
/-- Unconditional: **the Dirichlet solution operator is continuous.**

This is the property that no `Classical.choose` selection can have by itself and
that every measurability statement about the corrector rests on.  The proof is a
composition of four continuous maps and uses no property of the forcing. -/
theorem continuous_dirichletGradientOfForcingClass {a : CoeffField d} {lam Lam : ℝ}
    (M : PotentialSolenoidalL2Data U) (hne : Set.Nonempty U)
    (hEll : IsEllipticFieldOn lam Lam U a) :
    Continuous (dirichletGradientOfForcingClass M hne hEll) := by
  have hrestrict : Continuous fun l : HilbertVectorL2 U →L[ℝ] ℝ =>
      l.comp ((submodule (M := M)).subtypeL) :=
    ((ContinuousLinearMap.compL ℝ (Space M) (HilbertVectorL2 U) ℝ).flip
      ((submodule (M := M)).subtypeL)).continuous
  exact continuous_subtype_val.comp
    ((((isCoercive_coeffBilin (M := M) hne
        hEll).continuousLinearEquivOfBilin.symm).continuous).comp
      (((InnerProductSpace.toDual ℝ (Space M)).symm.continuous).comp
        (hrestrict.comp (InnerProductSpace.toDual ℝ (HilbertVectorL2 U)).continuous)))

omit [IsFiniteMeasure (volumeMeasureOn U)] in
/-- Unconditional: **every** zero-trace Dirichlet weak solution of `e.def.w`'s
Dirichlet problem has, for its gradient class, the value of the solution
operator at the class of its forcing.

There is no selection here and no measurability hypothesis: the statement is
about an arbitrary solution `u` supplied by the caller, and it says that its
gradient is already a *continuous* function of the forcing class alone.

The domain hypotheses are `hRealize`, CoarseGraining's zero-trace potential
closure realization (proved for every open triadic cube in
`Provider.Corrector.hasPotentialZeroTraceClosureRealization_openCubeSet`),
`hne` and `hEll`. -/
theorem gradToHilbertVectorL2_eq_dirichletGradientOfForcingClass
    {a : CoeffField d} {lam Lam : ℝ} {g : Vec d → Vec d} {u : H10Function U}
    (hg : MemVectorL2 U g)
    (hRealize : PotentialSolenoidalL2Data.HasPotentialZeroTraceClosureRealization U)
    (hne : Set.Nonempty U) (hEll : IsEllipticFieldOn lam Lam U a)
    (hu : IsZeroTraceDirichletRhsWeakSolution a U u g) :
    u.toH1Function.gradToHilbertVectorL2 =
      dirichletGradientOfForcingClass
        (PotentialSolenoidalL2Data.ofSubmoduleClosures U) hne hEll
        (toHilbertVectorL2OfVecField hg) := by
  set M : PotentialSolenoidalL2Data U := PotentialSolenoidalL2Data.ofSubmoduleClosures U with hM
  set zu : Space M := ofH10Function M u with hzu
  have key : ∀ w : Space M,
      inner ℝ (forcingRieszRep M hg) w = coeffBilin (M := M) hEll zu w := by
    intro w
    obtain ⟨phi, hphi⟩ :=
      PotentialSolenoidalL2Data.isPotentialZeroTraceOn_of_mem_potentialZeroTrace_ofSubmoduleClosures
        (U := U) hRealize (vectorField w) (by simpa [hM] using mem_potentialZeroTrace w)
    rw [inner_forcingRieszRep_apply, forcingFunctionalCLM_apply_eq_integral,
      coeffBilin_apply_eq_integral]
    have hzfield : vectorField zu = u.toH1Function.gradToVectorL2 := by
      rw [hzu]; exact vectorField_ofH10Function M u
    have hrhs :
        ∫ x in U, vecDot (matVecMul (a x) (vectorField zu x)) (vectorField w x)
            ∂MeasureTheory.volume =
          ∫ x in U, vecDot (matVecMul (a x) (u.toH1Function.grad x))
            (phi.toH1Function.grad x) ∂MeasureTheory.volume := by
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards [H1Function.coeFn_gradToVectorL2 u.toH1Function] with x hx
      rw [hphi, hzfield, hx]
    have hlhs :
        ∫ x in U, vecDot (g x) (vectorField w x) ∂MeasureTheory.volume =
          ∫ x in U, vecDot (g x) (phi.toH1Function.grad x) ∂MeasureTheory.volume := by
      rw [hphi]
    rw [hlhs, hrhs, hu phi]
  have heq : forcingRieszRep M hg =
      (isCoercive_coeffBilin (M := M) hne hEll).continuousLinearEquivOfBilin zu :=
    IsCoercive.unique_continuousLinearEquivOfBilin _ key
  have hz : zu = (isCoercive_coeffBilin (M := M) hne hEll).continuousLinearEquivOfBilin.symm
      (forcingRieszRep M hg) := by
    rw [heq, ContinuousLinearEquiv.symm_apply_apply]
  calc u.toH1Function.gradToHilbertVectorL2 = field zu := rfl
    _ = dirichletGradientOfForcingClass M hne hEll (toHilbertVectorL2OfVecField hg) := by
        rw [dirichletGradientOfForcingClass, hz]; rfl

/-! ## The Neumann leg -/

/-- Unconditional: the Riesz representative, inside CoarseGraining's coercive `H^1`
graph space, of the forcing functional attached to an ambient `L^2` class `G`. -/
def neumannForcingRieszOfClass (G : HilbertVectorL2 U) :
    H1CoerciveHilbertSpace (U := U) :=
  H1CoerciveHilbert.forcingRieszMap (U := U)
    ((InnerProductSpace.toDual ℝ (HilbertVectorL2 U) G).comp
      (H1CoerciveHilbert.gradientCLM (U := U)))

/-- Unconditional: **the mean-zero Neumann solution operator of `e.def.w`.**

The three hypotheses are the standing domain data: `hC`, the
Poincare--Wirtinger coercivity datum (proved for every triadic cube by
CoarseGraining's `translatedCubeMeanZeroH1CoerciveEstimate`), `hne` and `hEll`. -/
def neumannGradientOfForcingClass {a : CoeffField d} {lam Lam : ℝ}
    (hC : H1CoerciveEstimate U) (hne : Set.Nonempty U)
    (hEll : IsEllipticFieldOn lam Lam U a) (G : HilbertVectorL2 U) :
    HilbertVectorL2 U :=
  H1CoerciveHilbert.gradient (U := U)
    ((H1CoerciveHilbert.isCoercive_coeffGradientBilin (U := U)
      (a := a) (lam := lam) (Lam := Lam) hC hne hEll).continuousLinearEquivOfBilin.symm
      (neumannForcingRieszOfClass G))

/-- Unconditional: **the Neumann solution operator is continuous.** -/
theorem continuous_neumannGradientOfForcingClass {a : CoeffField d} {lam Lam : ℝ}
    (hC : H1CoerciveEstimate U) (hne : Set.Nonempty U)
    (hEll : IsEllipticFieldOn lam Lam U a) :
    Continuous
      (neumannGradientOfForcingClass (U := U) (a := a) (lam := lam) (Lam := Lam)
        hC hne hEll) := by
  have hrestrict : Continuous fun l : HilbertVectorL2 U →L[ℝ] ℝ =>
      l.comp (H1CoerciveHilbert.gradientCLM (U := U)) :=
    ((ContinuousLinearMap.compL ℝ (H1CoerciveHilbertSpace (U := U))
      (HilbertVectorL2 U) ℝ).flip (H1CoerciveHilbert.gradientCLM (U := U))).continuous
  exact (H1CoerciveHilbert.gradientCLM (U := U)).continuous.comp
    ((((H1CoerciveHilbert.isCoercive_coeffGradientBilin (U := U)
        (a := a) (lam := lam) (Lam := Lam) hC hne
        hEll).continuousLinearEquivOfBilin.symm).continuous).comp
      (((InnerProductSpace.toDual ℝ (H1CoerciveHilbertSpace (U := U))).symm.continuous).comp
        (hrestrict.comp (InnerProductSpace.toDual ℝ (HilbertVectorL2 U)).continuous)))

/-- Unconditional: **every** mean-zero Neumann weak solution of `e.def.w`'s
Neumann problem has, for its gradient class, the value of the solution operator
at the class of its forcing. -/
theorem gradToHilbertVectorL2_eq_neumannGradientOfForcingClass
    {a : CoeffField d} {lam Lam : ℝ} {g : Vec d → Vec d} {u : H1MeanZeroFunction U}
    (hg : MemVectorL2 U g) (hC : H1CoerciveEstimate U) (hne : Set.Nonempty U)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (hu : IsMeanZeroNeumannRhsWeakSolution a U u g) :
    u.gradToHilbertVectorL2 =
      neumannGradientOfForcingClass (U := U) (a := a) (lam := lam) (Lam := Lam)
        hC hne hEll (toHilbertVectorL2OfVecField hg) := by
  have hvec := gradToVectorL2_eq_coeffGradientProblemSolution_of_h1CoerciveEstimate
    (U := U) (a := a) (lam := lam) (Lam := Lam) hg hC hne hu hEll
  have hbridge : ∀ v : H1MeanZeroFunction U,
      v.gradToHilbertVectorL2 = vectorL2ToHilbertVectorL2 (U := U) v.gradToVectorL2 := fun v =>
    (vectorL2ToHilbertVectorL2_toVectorL2 (U := U) v.toH1Function.grad_memVectorL2).symm
  rw [hbridge u, hvec, ← hbridge]
  show (H1CoerciveHilbert.toH1MeanZeroFunction
      (H1CoerciveHilbert.coeffGradientProblemSolution (U := U) (a := a) (lam := lam) (Lam := Lam)
        hg hC hne hEll)).gradToHilbertVectorL2 = _
  rw [H1CoerciveHilbert.toH1MeanZeroFunction_gradToHilbertVectorL2]
  rfl

end

end Algsuperdiff.Section3.Provider.Diffusivity.Corrector
