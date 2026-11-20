/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/NonQuadraticPiTensorConvolution.lean.
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

public import LeanPool.GinibrePoincare.Analysis.NonQuadraticPiTensorMollification
public import LeanPool.GinibrePoincare.Analysis.NonQuadraticFiniteKernelIntegral

/-!
# Non quadratic pi tensor convolution

Part of the nonquadratic potentials development of the
Ginibre Poincaré formalization.

Main results: `planarPiTranslatedGraph_integral_value_ae`.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Filter
open scoped ContDiff InnerProductSpace Topology
namespace GinibrePoincare
noncomputable section

/-- The product half weight `x ↦ ∏ i, exp (-n V (x i) / 2)` on `ℂ^d`. -/
def piPotentialHalfWeight (d n : ℕ) (V : ℂ → ℝ) (x : Fin d → ℂ) : ℂ :=
  ∏ i, planarPotentialHalfWeight n V (x i)

theorem piPotentialHalfWeight_continuous (d n : ℕ) (V : ℂ → ℝ) (hV : Continuous V) :
    Continuous (piPotentialHalfWeight d n V) := by
  unfold piPotentialHalfWeight
  apply continuous_finsetProd
  intro i _
  have hw : Continuous (planarPotentialHalfWeight n V) := by
    unfold planarPotentialHalfWeight
    fun_prop
  exact hw.comp (continuous_apply i)

theorem planarPiTranslatedValue_coeFn {m : ℕ}
    (n : ℕ) (V : ℂ → ℝ) (hV : Continuous V) (φ : Fin (m + 1) → PlanarComplexCompactTest)
    (a : Fin (m + 1) → ℂ) :
    (planarPiPureWeightedValue n V hV (fun i => planarComplexTestTranslate (φ i) (a i)) :
      (Fin (m+1) → ℂ) → ℂ) =ᵐ[Measure.pi (fun _ => (volume : Measure ℂ))]
      (fun x => (∏ i, φ i (x i - a i)) * piPotentialHalfWeight (m+1) n V x) := by
  have hi (i : Fin (m+1)) :
      (planarComplexWeightedValueL2 n V hV (planarComplexTestTranslate (φ i) (a i)) : ℂ → ℂ)
        =ᵐ[volume] (fun x => φ i (x - a i) * planarPotentialHalfWeight n V x) := by
    rw [planarComplexTestTranslate_weightedValue]
    exact (planarWeightedTranslate_memLp n V hV (φ i) (φ i).property.1.continuous (φ i).property.2
        (a i)).coeFn_toLp
  have hall : ∀ᵐ x ∂Measure.pi (fun _ : Fin (m+1) => (volume : Measure ℂ)), ∀ i,
      planarComplexWeightedValueL2 n V hV (planarComplexTestTranslate (φ i) (a i)) (x i) =
        φ i (x i - a i) * planarPotentialHalfWeight n V (x i) :=
    ae_all_iff.mpr (fun i => (quasiMeasurePreserving_eval (fun _ => (volume : Measure ℂ))
        i).ae_eq_comp (hi i))
  filter_upwards [l2PiProductVector_coeFn (fun _ => (volume : Measure ℂ))
    (fun i => planarComplexWeightedValueL2 n V hV (planarComplexTestTranslate (φ i) (a i))), hall]
    with x hx hh
  unfold planarPiPureWeightedValue
  rw [hx]
  simp only [hh, Finset.prod_mul_distrib, piPotentialHalfWeight]

theorem planarPiTranslatedGraph_integral_value_ae {m : ℕ}
    (n : ℕ) (V : ℂ → ℝ) (hV : Continuous V) (φ : Fin (m + 1) → PlanarComplexCompactTest)
    (f : (Fin (m + 1) → ℂ) → ℂ) (hf : Continuous f) (hc : HasCompactSupport f) :
    (((∫ a, f a • planarPiPureDbarGraph n V hV
      (fun i => planarComplexTestTranslate (φ i) (a i))
      ∂Measure.pi (fun _ => (volume : Measure ℂ))).1) : (Fin (m+1) → ℂ) → ℂ)
      =ᵐ[Measure.pi (fun _ => (volume : Measure ℂ))]
        (fun x => (∫ a, f a * ∏ i, φ i (x i - a i)
          ∂Measure.pi (fun _ => (volume : Measure ℂ))) * piPotentialHalfWeight (m+1) n V x) := by
  let μ := Measure.pi (fun _ : Fin (m+1) => (volume : Measure ℂ))
  let k : (Fin (m+1) → ℂ) → ℂ := fun x => ∏ i, φ i (x i)
  have hk : Continuous k := continuous_finsetProd _ (fun i _ => (φ i).property.1.continuous.comp
      (continuous_apply i))
  have hkc : HasCompactSupport k := piSeparatedKernel_hasCompactSupport _ (fun i => (φ
      i).property.2)
  have hg : Continuous (fun p : (Fin (m+1) → ℂ) × (Fin (m+1) → ℂ) =>
      (f p.1 * k (p.2 - p.1)) * piPotentialHalfWeight (m+1) n V p.2) :=
    ((hf.comp continuous_fst).mul (hk.comp (continuous_snd.sub continuous_fst))).mul
      ((piPotentialHalfWeight_continuous (m+1) n V hV).comp continuous_snd)
  have hgc := (finiteTranslatedKernel_hasCompactSupport f k hc hkc).mul_right
    (f' := fun p => piPotentialHalfWeight (m+1) n V p.2)
  let G := fun a => f a • planarPiPureWeightedValue n V hV
    (fun i => planarComplexTestTranslate (φ i) (a i))
  have hG : Integrable G μ :=
    (planarPiTranslatedGraph_integrable n V hV φ f hf hc).fst
  have hcoef (a) : (G a : (Fin (m+1) → ℂ) → ℂ) =ᵐ[μ]
      (fun x => (f a * k (x-a)) * piPotentialHalfWeight (m+1) n V x) := by
    filter_upwards [Lp.coeFn_smul (f a) (planarPiPureWeightedValue n V hV
      (fun i => planarComplexTestTranslate (φ i) (a i))), planarPiTranslatedValue_coeFn n V hV φ a]
      with x hx hh
    rw [hx]
    change f a * _ = _
    rw [hh]
    exact (mul_assoc (f a) (∏ i, φ i (x i - a i)) (piPotentialHalfWeight (m+1) n V x)).symm
  have he := finiteDimensionalL2_kernel_integral_ae μ _ hg hgc G hG hcoef
  rw [fst_integral (planarPiTranslatedGraph_integrable n V hV φ f hf hc)]
  exact he.mono (fun x hx => hx.trans
    (integral_mul_const (piPotentialHalfWeight (m+1) n V x)
      (fun a : Fin (m+1) → ℂ => f a * ∏ i, φ i (x i - a i))))
end
end GinibrePoincare
