/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GaussianCurryLaw.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
The original source is MIT licensed; its notice follows.

MIT License

Copyright (c) 2026 Djalil Chafai

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

module

public import LeanPool.GinibrePoincare.Analysis.GaussianPiCoordinates

/-!
# Gaussian Curry Law
-/


@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal
namespace GinibrePoincare
noncomputable section

/-- Linear currying of a finite family of real coordinates. -/
def gaussianCurryEquiv (I : Type*) (J : I → Type*) [Fintype I] [∀ i, Fintype (J i)] :
    ((Sigma J) → ℝ) ≃L[ℝ] (∀ i, J i → ℝ) where
  __ := LinearEquiv.piCurry ℝ (fun _ _ => ℝ)
  continuous_toFun := by
    change Continuous (fun x : Sigma J → ℝ => fun i j => x ⟨i, j⟩)
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    exact continuous_apply (⟨i, j⟩ : Sigma J)
  continuous_invFun := by
    change Continuous (fun x : ∀ i, J i → ℝ => fun p : Sigma J => x p.1 p.2)
    apply continuous_pi
    intro p
    exact (continuous_apply p.2).comp (continuous_apply p.1)

/-- Finite Gaussian product measures commute with dependent currying. -/
theorem gaussianCurry_measurePreserving (I : Type*) (J : I → Type*)
    [Fintype I] [∀ i, Fintype (J i)] (v : ℝ≥0) :
    MeasurePreserving (gaussianCurryEquiv I J)
      (Measure.pi (fun _ : Sigma J => gaussianReal 0 v))
      (Measure.pi (fun i : I => Measure.pi (fun _ : J i => gaussianReal 0 v))) := by
  let e := MeasurableEquiv.piCurry (fun (i : I) (_ : J i) => ℝ)
  have hi : MeasurePreserving e.symm
      (Measure.pi (fun i : I => Measure.pi (fun _ : J i => gaussianReal 0 v)))
      (Measure.pi (fun _ : Sigma J => gaussianReal 0 v)) := by
    refine ⟨e.symm.measurable, ?_⟩
    apply Eq.symm
    apply Measure.pi_eq
    intro s hs
    rw [Measure.map_apply e.symm.measurable (MeasurableSet.univ_pi hs)]
    have hset : e.symm ⁻¹' (Set.univ.pi s) =
        Set.univ.pi (fun i : I => Set.univ.pi (fun j : J i => s ⟨i, j⟩)) := by
      ext x
      simp [e, Set.mem_pi, Sigma.forall, Sigma.uncurry]
    rw [hset, Measure.pi_pi]
    simp_rw [Measure.pi_pi]
    exact (Fintype.prod_sigma (fun p : Sigma J => gaussianReal 0 v (s p))).symm
  exact MeasurePreserving.symm e.symm hi

end
end GinibrePoincare
