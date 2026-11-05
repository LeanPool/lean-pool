/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Support.HighContrast.Coupled.Stampacchia.LevelEnergy
public import LeanPool.HighContrastHomogenization.Support.PDE.DirichletRHS

/-!
# MeasurableRepresentative

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Measurable representatives of divergence-forced weak solutions

This file packages the measurable-representative bridge needed by pointwise
regularity arguments.  The representative remains in `H¹₀(U)` and satisfies
the original divergence-forced weak equation with its own weak gradient.
-/

namespace HCPolySupport.IsZeroTraceDirichletRhsWeakSolution

open HCPolySupport MeasureTheory

/-- A zero-trace divergence-forced weak solution on an open bounded convex
domain has a measurable `H¹` representative.  The representative is almost
everywhere equal to the original solution, remains in `H¹₀(U)`, and satisfies
the same weak equation with its own weak gradient. -/
theorem exists_measurableRep
    {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U)
    {a : CoeffField d} {u : H10Function U} {g : Vec d → Vec d}
    (hsol : IsZeroTraceDirichletRhsWeakSolution a U u g) :
    ∃ w : H1Function U,
      Measurable w.toFun ∧
        w.toFun =ᵐ[volumeMeasureOn U] u.toH1Function.toFun ∧
        MemH10 U w.toFun ∧
        ∀ φ : H10Function U,
          ∫ x in U, vecDot (matVecMul (a x) (w.grad x)) (φ.toH1Function.grad x)
              ∂volume =
            ∫ x in U, vecDot (g x) (φ.toH1Function.grad x) ∂volume := by
  obtain ⟨w, hwMeas, hwu, hwgrad⟩ :=
    HCPolySupport.exists_measurableRep u.toH1Function
  refine ⟨w, hwMeas, hwu, memH10_of_ae_eq_h10 hU w u hwu, ?_⟩
  intro φ
  rw [hwgrad]
  exact hsol φ

/-- A zero-trace divergence-forced weak solution has a measurable
`H10Function` representative which is almost everywhere equal to the original
solution and satisfies the same zero-trace weak-solution predicate. -/
theorem exists_measurableH10Rep
    {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U)
    {a : CoeffField d} {u : H10Function U} {g : Vec d → Vec d}
    (hsol : IsZeroTraceDirichletRhsWeakSolution a U u g) :
    ∃ v : H10Function U,
      Measurable v.toH1Function.toFun ∧
        v.toH1Function.toFun =ᵐ[volumeMeasureOn U] u.toH1Function.toFun ∧
        IsZeroTraceDirichletRhsWeakSolution a U v g := by
  obtain ⟨w, hwMeas, hwu, hwH10, _⟩ := exists_measurableRep hU hsol
  obtain ⟨v, hvw⟩ := hwH10
  have hvu : v.toH1Function.toFun =ᵐ[volumeMeasureOn U]
      u.toH1Function.toFun := by
    rw [hvw]
    exact hwu
  have hgrad : v.toH1Function.grad =ᵐ[volumeMeasureOn U]
      u.toH1Function.grad :=
    h1grad_ae_eq_of_toFun_ae_eq hU.isOpen hvu
  refine ⟨v, ?_, hvu, ?_⟩
  · rw [hvw]
    exact hwMeas
  · intro φ
    calc
      ∫ x in U,
          vecDot (matVecMul (a x) (v.toH1Function.grad x)) (φ.toH1Function.grad x)
            ∂volume =
          ∫ x in U,
            vecDot (matVecMul (a x) (u.toH1Function.grad x)) (φ.toH1Function.grad x)
              ∂volume := by
        apply integral_congr_ae
        filter_upwards [hgrad] with x hx
        rw [hx]
      _ = ∫ x in U, vecDot (g x) (φ.toH1Function.grad x) ∂volume := hsol φ

end HCPolySupport.IsZeroTraceDirichletRhsWeakSolution
