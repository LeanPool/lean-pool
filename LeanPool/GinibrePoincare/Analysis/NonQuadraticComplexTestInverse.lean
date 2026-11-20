/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/NonQuadraticComplexTestInverse.lean.
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

public import LeanPool.GinibrePoincare.Analysis.NonQuadraticBergmanComplex
public import LeanPool.GinibrePoincare.Analysis.NonQuadraticBoundedFactorization

/-! # Complex linear compact tests and the actual bounded ∂bar inverse -/

@[expose] public section
open MeasureTheory
open scoped ContDiff InnerProductSpace
namespace GinibrePoincare
noncomputable section

/-- The complex vector space of compactly supported `C²` functions `ℂ → ℂ`. -/
def planarComplexCompactTestSpace : Submodule ℂ (ℂ → ℂ) where
  carrier := {f | ContDiff ℝ 2 f ∧ HasCompactSupport f}
  zero_mem' := ⟨contDiff_const, by simp [HasCompactSupport]⟩
  add_mem' := fun hf hg => ⟨hf.1.add hg.1, hf.2.add hg.2⟩
  smul_mem' := fun c f hf => ⟨contDiff_const.smul hf.1, hf.2.smul_left⟩
/-- Compactly supported `C²` planar test functions, as a complex vector space. -/
abbrev PlanarComplexCompactTest := ↥planarComplexCompactTestSpace
instance : CoeFun PlanarComplexCompactTest (fun _ => ℂ → ℂ) := ⟨fun f => f.val⟩
/-- A complex test function, viewed as an element of the real test space `PlanarCompactTest`. -/
def planarComplexTestReal (f : PlanarComplexCompactTest) : PlanarCompactTest := ⟨f.val, f.property⟩

/-- The complex-linear map `f ↦ f * exp (-n V / 2)` multiplying a test function by the half
weight `planarPotentialHalfWeight n V`. -/
def planarComplexWeightedValue (n : ℕ) (V : ℂ → ℝ) :
    PlanarComplexCompactTest →ₗ[ℂ] (ℂ → ℂ) where
  toFun f z := f z * planarPotentialHalfWeight n V z
  map_add' f g := by ext z; exact add_mul _ _ _
  map_smul' c f := by ext z; simp only [Pi.smul_apply, Submodule.coe_smul, smul_eq_mul,
                        RingHom.id_apply]; exact mul_assoc _ _ _

/-- The complex-linear map `f ↦ ∂̄f * exp (-n V / 2)`, the Wirtinger derivative `planarDbar`
multiplied by the half weight `planarPotentialHalfWeight n V`. -/
def planarComplexWeightedDbar (n : ℕ) (V : ℂ → ℝ) :
    PlanarComplexCompactTest →ₗ[ℂ] (ℂ → ℂ) where
  toFun f z := planarDbar f z * planarPotentialHalfWeight n V z
  map_add' f g := by
    ext z
    change planarDbar (fun w => f w + g w) z * _ = _
    unfold planarDbar
    rw [fderiv_fun_add (f.property.1.differentiable (by norm_num) z)
      (g.property.1.differentiable (by norm_num) z)]
    simp only [add_apply, Pi.add_apply]
    ring
  map_smul' c f := by
    ext z
    change planarDbar (fun w => c * f w) z * _ = c * _
    rw [planarDbar_const_mul _ (f.property.1.differentiable (by norm_num))]
    ring

/-- A complex-linear map from tests to square-integrable functions, lifted to a map into
`PlanarLebesgueL2` by taking `L²` classes. -/
def planarComplexTestLpLift (P : PlanarComplexCompactTest →ₗ[ℂ] (ℂ → ℂ))
    (hP : ∀ f, MemLp (P f) 2 volume) : PlanarComplexCompactTest →ₗ[ℂ] PlanarLebesgueL2 where
  toFun f := (hP f).toLp (P f)
  map_add' f g := by
    rw [← MemLp.toLp_add (hP f) (hP g)]
    apply MemLp.toLp_congr
    exact Filter.Eventually.of_forall (fun z => congrFun (P.map_add f g) z)
  map_smul' c f := by
    simp only [RingHom.id_apply]
    rw [← MemLp.toLp_const_smul c (hP f)]
    apply MemLp.toLp_congr
    exact Filter.Eventually.of_forall (fun z => congrFun (P.map_smul c f) z)

/-- The weighted value map `f ↦ f * exp (-n V / 2)` on complex tests, with values in
`PlanarLebesgueL2`. -/
def planarComplexWeightedValueL2 (n : ℕ) (V : ℂ → ℝ) (hV : Continuous V) :
    PlanarComplexCompactTest →ₗ[ℂ] PlanarLebesgueL2 :=
  planarComplexTestLpLift (planarComplexWeightedValue n V)
    (fun f => planarWeightedTestMap_memLp n V hV (planarComplexTestReal f))

/-- The weighted `∂̄` map `f ↦ ∂̄f * exp (-n V / 2)` on complex tests, with values in
`PlanarLebesgueL2`. -/
def planarComplexWeightedDbarL2 (n : ℕ) (V : ℂ → ℝ) (hV : Continuous V) :
    PlanarComplexCompactTest →ₗ[ℂ] PlanarLebesgueL2 :=
  planarComplexTestLpLift (planarComplexWeightedDbar n V)
    (fun f => planarWeightedDbarTestFunction_memLp n V hV (planarComplexTestReal f))
/-- The actual scalar Hörmander bound constructs one bounded complex
linear inverse for every compact test simultaneously. -/
theorem rhoSubharmonicPotential_exists_bounded_dbar_inverse
    (n : ℕ) (hn : 0 < n) (V : ℂ → ℝ) (ρ : ℝ) (hρpos : 0 < ρ)
    (hV : ContDiff ℝ 2 V) (hρ : IsRhoSubharmonicPotential ρ V) :
    ∃ T : PlanarLebesgueL2 →L[ℂ] PlanarLebesgueL2,
      ‖T‖ ≤ Real.sqrt (2 / ((n : ℝ) * ρ)) ∧ ∀ f : PlanarComplexCompactTest,
      T (planarComplexWeightedDbarL2 n V hV.continuous f) =
        planarComplexWeightedValueL2 n V hV.continuous f -
          planarBergmanProjection n V hV (planarComplexWeightedValueL2 n V hV.continuous f) := by
  let A := planarComplexWeightedDbarL2 n V hV.continuous
  let B := ((ContinuousLinearMap.id ℂ PlanarLebesgueL2 - planarBergmanProjection n V
      hV).toLinearMap).comp
    (planarComplexWeightedValueL2 n V hV.continuous)
  have hc : 0 ≤ 2 / ((n : ℝ) * ρ) := by positivity
  have hb (f : PlanarComplexCompactTest) : ‖B f‖ ≤ Real.sqrt (2 / ((n : ℝ) * ρ)) * ‖A f‖ := by
    have hs := rhoSubharmonicPotential_compact_bergman_projection_gap n hn V ρ hρpos hV hρ
      (planarComplexTestReal f)
    rw [← planarWeightedDbarTestL2_norm_sq n V hV.continuous (planarComplexTestReal f)] at hs
    change ‖B f‖ ^ 2 ≤ (2 / ((n : ℝ) * ρ)) * ‖A f‖ ^ 2 at hs
    have hsqrt := Real.sq_sqrt hc
    have hnon : 0 ≤ Real.sqrt (2 / ((n : ℝ) * ρ)) * ‖A f‖ := mul_nonneg (Real.sqrt_nonneg _)
        (norm_nonneg _)
    nlinarith [norm_nonneg (B f), sq_nonneg (‖A f‖)]
  exact exists_bounded_hilbert_factor A B _ (Real.sqrt_nonneg _) hb

end
end GinibrePoincare
