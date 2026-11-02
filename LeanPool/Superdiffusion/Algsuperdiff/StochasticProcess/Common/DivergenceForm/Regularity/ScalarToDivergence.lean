/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.Regularity.CoordinatePrimitive
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.ScalarWeakSolution
public import LeanPool.HighContrastHomogenization.Support.Deterministic.ConstantCoefficientDirichletBesov.Basic
public import LeanPool.HighContrastHomogenization.Support.PDE.DirichletRHS

/-!
# ScalarToDivergence

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Smooth scalar forcing as divergence forcing

A globally `C¹` scalar field is converted into divergence forcing by placing
the negative of its one-coordinate primitive in one vector coordinate. The
resulting field is in `L²` on a bounded convex domain and has exactly the weak
pairing required by the literal divergence-right-hand-side predicate.

This module does not extend the construction to nonsmooth or merely almost
everywhere bounded scalar forcing.
-/

namespace DivergenceFormProcess

open HCPolySupport MeasureTheory
open scoped BigOperators RealInnerProductSpace

variable {d : ℕ} {U : Set (Vec d)}

/-- The coordinate primitive packaged as an `H¹` function on a bounded convex
domain. -/
noncomputable def coordinatePrimitiveH1 (hU : IsOpenBoundedConvexDomain U)
    (q : Vec d → ℝ) (hq : ContDiff ℝ 1 q) (i : Fin d) (z : ℝ) :
    H1Function U :=
  H1Function.ofContDiffOnIsOpenBoundedConvexDomain hU
    (contDiff_one_coordinatePrimitive q hq i z)

/-- The divergence field with selected coordinate equal to the negative
coordinate primitive and every other coordinate equal to zero. -/
noncomputable def scalarToDivergenceField (q : Vec d → ℝ) (i : Fin d) (z : ℝ) :
    Vec d → Vec d := fun x j ↦
  if j = i then -coordinatePrimitive q i z x else 0

/-- The selected weak-gradient coordinate of the packaged primitive is the
original scalar field. -/
theorem coordinatePrimitiveH1_grad_selected
    (hU : IsOpenBoundedConvexDomain U) (q : Vec d → ℝ)
    (hq : ContDiff ℝ 1 q) (i : Fin d) (z : ℝ) (x : Vec d) :
    (coordinatePrimitiveH1 hU q hq i z).grad x i = q x := by
  change (fderiv ℝ (coordinatePrimitive q i z) x) (basisVec i) = q x
  have hupdate : Function.update x i (x i) = x := by
    funext j
    classical
    by_cases hji : j = i
    · subst j
      simp [Function.update]
    · simp [Function.update, hji]
  have hfull : HasFDerivAt (coordinatePrimitive q i z)
      (fderiv ℝ (coordinatePrimitive q i z) x)
      (Function.update x i (x i)) := by
    rw [hupdate]
    exact (contDiff_one_coordinatePrimitive q hq i z).differentiable (by norm_num)
      |>.differentiableAt.hasFDerivAt
  have hline := hfull.comp (x i) (hasDerivAt_update x i (x i))
  have htarget := coordinatePrimitive_hasDerivAt_update q hq.continuous i z x
  have heq := congrArg (fun L : ℝ →L[ℝ] ℝ ↦ L 1) (hline.unique htarget)
  simpa only [ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.toSpanSingleton_apply,
    one_smul, basisVec] using! heq

/-- The smooth scalar-to-divergence field belongs to vector `L²` on the
bounded domain. -/
theorem scalarToDivergenceField_memVectorL2
    (hU : IsOpenBoundedConvexDomain U) (q : Vec d → ℝ)
    (hq : ContDiff ℝ 1 q) (i : Fin d) (z : ℝ) :
    MemVectorL2 U (scalarToDivergenceField q i z) := by
  classical
  apply MeasureTheory.MemLp.of_eval
  intro j
  by_cases hji : j = i
  · subst j
    simpa only [scalarToDivergenceField, ite_eq_left] using!
      (coordinatePrimitiveH1 hU q hq i z).memL2.neg
  · rw [show (fun x : Vec d ↦ scalarToDivergenceField q i z x j) =
        fun _ : Vec d ↦ (0 : ℝ) by
          funext x
          simp only [scalarToDivergenceField, hji, ite_false]]
    exact MeasureTheory.MemLp.zero'

/-- The divergence field pairs with every zero-trace test exactly as the
original scalar forcing. -/
theorem integral_scalarToDivergenceField_vecDot_grad_eq
    (hU : IsOpenBoundedConvexDomain U) (q : Vec d → ℝ)
    (hq : ContDiff ℝ 1 q) (i : Fin d) (z : ℝ) (φ : H10Function U) :
    (∫ x in U, vecDot (scalarToDivergenceField q i z x)
        (φ.toH1Function.grad x) ∂volume) =
      ∫ x in U, q x * φ.toH1Function.toFun x ∂volume := by
  let p : H1Function U := coordinatePrimitiveH1 hU q hq i z
  have hdot : ∀ x, vecDot (scalarToDivergenceField q i z x)
      (φ.toH1Function.grad x) =
      -coordinatePrimitive q i z x * φ.toH1Function.grad x i := by
    intro x
    classical
    unfold vecDot scalarToDivergenceField
    rw [Finset.sum_eq_single i]
    · simp only [ite_eq_left, neg_mul]
    · intro j _ hji
      simp only [hji, ite_false, zero_mul]
    · intro hi
      exact (hi (Finset.mem_univ i)).elim
  have hibp := p.integral_mul_zeroTrace_gradCoord_eq_neg_integral_gradCoord_mul φ i
  have hpFun : p.toFun = coordinatePrimitive q i z := rfl
  rw [hpFun] at hibp
  calc
    (∫ x in U, vecDot (scalarToDivergenceField q i z x)
        (φ.toH1Function.grad x) ∂volume) =
        ∫ x in U,
          -(coordinatePrimitive q i z x * φ.toH1Function.grad x i)
          ∂volume := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with x
      rw [hdot x]
      rw [neg_mul]
    _ = -(∫ x in U,
          coordinatePrimitive q i z x * φ.toH1Function.grad x i
          ∂volume) := by
      rw [MeasureTheory.integral_neg]
    _ = ∫ x in U, p.grad x i * φ.toH1Function x ∂volume := by
      rw [hibp, neg_neg]
    _ = ∫ x in U, q x * φ.toH1Function.toFun x ∂volume := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with x
      rw [coordinatePrimitiveH1_grad_selected hU q hq i z x]

end DivergenceFormProcess
