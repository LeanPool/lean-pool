/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.LocalizedFinite

/-!
# SolutionLinearity

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The solution map is linear, and representatives subtract

For a fixed coefficient field the localized Dirichlet problem is linear in the
pair (solution, forcing field): the difference of two solutions solves the
problem for the difference of the forcing fields. Continuous representatives
subtract as well.

This is the linearity input used to compare two localized problems.

## References

* ABK26, the localized Dirichlet problems of Section 5.1.
-/

namespace Algsuperdiff.Section5.Support

open Algsuperdiff.Section3
open HCPolySupport MeasureTheory
open Algsuperdiff.Section4.Support
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. Linearity of the localized Dirichlet problem -/

/-- **The difference of two solutions solves the problem for the difference of
the forcing fields.** -/
theorem isDirichletSolutionAt_sub {y : Vec d} {n : ℤ} {a : CoeffField d} {lam Lam : ℝ}
    (hEll : IsEllipticFieldOn lam Lam (cubeSetAt y n) a)
    {u u' : H1Function (cubeSetAt y n)} {g g' : Vec d → Vec d}
    (hgL2 : MemVectorL2 (cubeSetAt y n) g) (hg'L2 : MemVectorL2 (cubeSetAt y n) g')
    (hu : IsDirichletSolutionAt a y n u g) (hu' : IsDirichletSolutionAt a y n u' g') :
    IsDirichletSolutionAt a y n (u - u') fun x => g x - g' x := by
  obtain ⟨w1, h1f, h1g⟩ := hu.1
  obtain ⟨w2, h2f, h2g⟩ := hu'.1
  refine ⟨⟨w1 - w2, fun x => ?_, fun x => ?_⟩, ?_⟩
  · change (u - u').toFun x = (w1.toH1Function - w2.toH1Function).toFun x
    simp only [H1Function.sub_toFun]
    rw [h1f x, h2f x]
  · change (u - u').grad x = (w1.toH1Function - w2.toH1Function).grad x
    simp only [H1Function.sub_grad]
    rw [h1g x, h2g x]
  · intro phi
    have hAu : MemVectorL2 (cubeSetAt y n) fun x => matVecMul (a x) (u.grad x) :=
      memVectorL2_matVecMul_of_isEllipticFieldOn hEll u.grad_memVectorL2
    have hAu' : MemVectorL2 (cubeSetAt y n) fun x => matVecMul (a x) (u'.grad x) :=
      memVectorL2_matVecMul_of_isEllipticFieldOn hEll u'.grad_memVectorL2
    have hsplitA : ∀ x, matVecMul (a x) ((u - u').grad x) =
        matVecMul (a x) (u.grad x) - matVecMul (a x) (u'.grad x) := by
      intro x
      have hgx : (u - u').grad x = u.grad x - u'.grad x := by
        simp only [H1Function.sub_grad]
      rw [hgx, sub_eq_add_neg, matVecMul_add, matVecMul_neg, ← sub_eq_add_neg]
    rw [Section4.Provider.Schauder.integral_vecDot_sub_split hAu hAu' hsplitA phi,
      Section4.Provider.Schauder.integral_vecDot_sub_split hgL2 hg'L2 (fun _ => rfl) phi,
      hu.2 phi, hu'.2 phi]
    ring

/-! ## 2. Representatives subtract -/

theorem isCubeRepresentative_sub {y : Vec d} {n : ℤ}
    {u u' : H1Function (cubeSetAt y n)} {uRep u'Rep : Vec d → ℝ}
    (h : IsCubeRepresentative y n u uRep) (h' : IsCubeRepresentative y n u' u'Rep) :
    IsCubeRepresentative y n (u - u') fun x => uRep x - u'Rep x := by
  refine ⟨?_, h.2.sub h'.2⟩
  · filter_upwards [h.1, h'.1] with x hx hx'
    show uRep x - u'Rep x = (u - u').toFun x
    simp only [H1Function.sub_toFun]
    rw [hx, hx']

end

end Algsuperdiff.Section5.Support
