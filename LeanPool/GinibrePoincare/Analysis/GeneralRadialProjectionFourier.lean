/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GeneralRadialProjectionFourier.lean.
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

public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# General radial projection Fourier

Part of the nonquadratic potentials development of the
Ginibre Poincaré formalization.

Main results: `continuous_circle_mem_closed_span_fourierCoeff`.
-/

@[expose] public section

open MeasureTheory Set
open scoped Topology InnerProductSpace
namespace GinibrePoincare
noncomputable section

/-- Completeness of actual circle Fourier coefficients for continuous scalar functions. -/
theorem continuous_circle_eq_zero_of_fourierCoeff_zero
    {T : ℝ} [Fact (0 < T)] (f : C(AddCircle T, ℂ))
    (h : ∀ k : ℤ, fourierCoeff f k = 0) : f = 0 := by
  let v := ContinuousMap.toLp (E := ℂ) 2 (@AddCircle.haarAddCircle T _) ℂ f
  have hv : v = 0 := by
    apply fourierBasis.repr.injective
    ext k
    rw [fourierBasis_repr, fourierCoeff_toLp]
    simp [h]
  have hae : (fun t => f t) =ᵐ[(@AddCircle.haarAddCircle T _)] (fun _ => (0 : ℂ)) := by
    have he := ContinuousMap.coeFn_toAEEqFun (@AddCircle.haarAddCircle T _) f
    have hz := Lp.coeFn_zero ℂ 2 (@AddCircle.haarAddCircle T _)
    filter_upwards [he, hz] with t ht ht0
    change v t = f t at ht
    rw [hv] at ht
    exact ht.symm.trans ht0
  ext t
  exact congrFun ((f.continuous.ae_eq_iff_eq (@AddCircle.haarAddCircle T _) continuous_const).mp
      hae) t

/-- Every value of a continuous Hilbert-valued circle function belongs to the
actual closed span of its Bochner Fourier coefficients. -/
theorem continuous_circle_mem_closed_span_fourierCoeff
    {T : ℝ} [Fact (0 < T)] {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E]
    (f : AddCircle T → E) (hf : Continuous f) (t : AddCircle T) :
    f t ∈ (Submodule.span ℂ (range (fourierCoeff f))).topologicalClosure := by
  let K := Submodule.span ℂ (range (fourierCoeff f))
  rw [← K.orthogonal_orthogonal_eq_closure]
  apply (Kᗮ.mem_orthogonal' (f t)).2
  intro w hw
  let g : C(AddCircle T, ℂ) := ⟨fun s => inner ℂ w (f s), continuous_const.inner hf⟩
  have hg : ∀ k : ℤ, fourierCoeff g k = 0 := by
    intro k
    have hi : Integrable (fun s : AddCircle T => fourier (-k) s • f s)
        (@AddCircle.haarAddCircle T _) := (hf.integrable_of_hasCompactSupport
            (HasCompactSupport.of_compactSpace f)).fourier_smul (-k)
    have he := (innerSL ℂ w).integral_comp_comm hi
    have hz : inner ℂ w (fourierCoeff f k) = 0 :=
      K.inner_left_of_mem_orthogonal (Submodule.subset_span (mem_range_self k)) hw
    rw [fourierCoeff] at hz ⊢
    simpa only [g, ContinuousMap.coe_mk, innerSL_apply_apply, inner_smul_right, smul_eq_mul] using
        he.trans hz
  have he := continuous_circle_eq_zero_of_fourierCoeff_zero g hg
  have hgt := congrArg (fun q : C(AddCircle T, ℂ) => q t) he
  have hz : inner ℂ w (f t) = 0 := hgt
  exact inner_eq_zero_symm.mp hz

end
end GinibrePoincare
