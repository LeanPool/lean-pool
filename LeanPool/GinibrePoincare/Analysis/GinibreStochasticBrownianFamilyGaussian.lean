/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreStochasticBrownianFamilyGaussian.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticBrownianPlanarIncrement
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence

/-! Independent Brownian coordinates form one genuine joint Gaussian process. -/

@[expose] public section
open MeasureTheory ProbabilityTheory Finset
open scoped NNReal
namespace GinibrePoincare
noncomputable section

theorem ginibreBrownian_family_isGaussianProcess {Ω ι : Type*}
    [MeasurableSpace Ω] [Finite ι] (B : ι → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    (hB : ∀ i, IsPreBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P) :
    IsGaussianProcess (fun p : ι × ℝ≥0 => B p.1 p.2) P := by
  have := Fintype.ofFinite ι
  classical
  constructor
  intro J
  let T := J.image Prod.snd
  let A := fun i ω (t : T) => B i t ω
  have hA (i : ι) : HasGaussianLaw (A i) P := (hB i).isGaussianProcess.hasGaussianLaw T
  have hiA : iIndepFun A P := hind.comp
    (fun i p => fun t : T => p t) (fun i => by fun_prop)
  have hG := hiA.hasGaussianLaw hA
  let L : (ι → T → ℝ) →L[ℝ] (J → ℝ) :=
    { toFun := fun v j => v j.val.1 ⟨j.val.2, mem_image.mpr ⟨j.val, j.property, rfl⟩⟩
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  have h := hG.map L
  convert! h using 1

end
end GinibrePoincare
