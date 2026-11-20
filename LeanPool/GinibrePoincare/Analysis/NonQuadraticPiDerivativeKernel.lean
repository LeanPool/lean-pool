/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/NonQuadraticPiDerivativeKernel.lean.
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

public import LeanPool.GinibrePoincare.Analysis.NonQuadraticPiSeparatedDerivatives

/-!
# Non quadratic pi derivative kernel

Part of the nonquadratic potentials development of the
Ginibre Poincaré formalization.

Main results: `planarPiTranslatedGraph_integral_dbar_ae`, `piSeparated_dbar_convolution_transfer`.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Filter
open scoped ContDiff Topology
namespace GinibrePoincare
noncomputable section

/-- The product `∏ j, φ j (x j)` with the `i`-th factor replaced by `∂̄ (φ i) (x i)`. -/
def piSeparatedDbarKernel {d : ℕ} (φ : Fin d → PlanarComplexCompactTest) (i : Fin d)
    (x : Configuration d) : ℂ :=
  ∏ j, Function.update (fun k => (φ k : ℂ → ℂ)) i (planarDbar (φ i)) j (x j)

theorem piSeparatedDbarKernel_continuous {d : ℕ} (φ : Fin d → PlanarComplexCompactTest) (i : Fin d)
    :
    Continuous (piSeparatedDbarKernel φ i) := by
  apply continuous_finsetProd
  intro j _
  by_cases hji : j = i
  · subst j
    simpa only [Function.update_self, Function.comp_def] using
      (planarComplexCompactTest_dbar_continuous (φ i)).comp (continuous_apply i)
  · simpa only [Function.update_of_ne hji, Function.comp_def] using (φ j).property.1.continuous.comp
      (continuous_apply j)

theorem piSeparatedDbarKernel_compact {d : ℕ} (φ : Fin d → PlanarComplexCompactTest) (i : Fin d) :
    HasCompactSupport (piSeparatedDbarKernel φ i) := by
  apply piSeparatedKernel_hasCompactSupport
  intro j
  by_cases hji : j = i
  · subst j
    simpa only [Function.update_self] using planarComplexCompactTest_dbar_compact (φ i)
  · simpa only [Function.update_of_ne hji] using (φ j).property.2

theorem piSeparatedDbarKernel_eq {d : ℕ} (φ : Fin d → PlanarComplexCompactTest) (i : Fin d) :
    piSeparatedDbarKernel φ i = piComplexDbar i (fun x : Configuration d => ∏ j, φ j (x j)) := by
  funext x
  rw [piSeparated_dbar _ (fun j => (φ j).property.1.differentiable (by norm_num))]
  unfold piSeparatedDbarKernel
  rw [Finset.prod_eq_mul_prod_sdiff_singleton_of_mem (Finset.mem_univ i)]
  simp only [Function.update_self, Finset.sdiff_singleton_eq_erase]
  rw [mul_comm]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  exact congrFun (Function.update_of_ne (Finset.ne_of_mem_erase hj) _ _) (x j)

theorem planarPiTranslatedDbar_coeFn {m : ℕ}
    (n : ℕ) (V : ℂ → ℝ) (hV : Continuous V) (φ : Fin (m + 1) → PlanarComplexCompactTest)
    (a : Configuration (m + 1)) (i : Fin (m + 1)) :
    (planarPiPureWeightedDbar n V hV (fun j => planarComplexTestTranslate (φ j) (a j)) i :
      Configuration (m+1) → ℂ) =ᵐ[Measure.pi (fun _ => (volume : Measure ℂ))]
      (fun x => piSeparatedDbarKernel φ i (x-a) * piPotentialHalfWeight (m+1) n V x) := by
  let u := Function.update
    (fun j => planarComplexWeightedValueL2 n V hV (planarComplexTestTranslate (φ j) (a j))) i
    (planarComplexWeightedDbarL2 n V hV (planarComplexTestTranslate (φ i) (a i)))
  let ψ := Function.update (fun j => (φ j : ℂ → ℂ)) i (planarDbar (φ i))
  have hi (j : Fin (m+1)) : (u j : ℂ → ℂ) =ᵐ[volume]
      (fun x => ψ j (x-a j) * planarPotentialHalfWeight n V x) := by
    by_cases hji : j = i
    · subst j
      dsimp only [u, ψ]
      simp only [Function.update_self, planarComplexTestTranslate_weightedDbar]
      exact (planarWeightedTranslate_memLp n V hV _
        (planarComplexCompactTest_dbar_continuous (φ i)) (planarComplexCompactTest_dbar_compact (φ
            i)) (a i)).coeFn_toLp
    · dsimp only [u, ψ]
      simp only [Function.update_of_ne hji, planarComplexTestTranslate_weightedValue]
      exact (planarWeightedTranslate_memLp n V hV (φ j) (φ j).property.1.continuous (φ j).property.2
          (a j)).coeFn_toLp
  have hall : ∀ᵐ x ∂Measure.pi (fun _ : Fin (m+1) => (volume : Measure ℂ)), ∀ j,
      u j (x j) = ψ j (x j-a j) * planarPotentialHalfWeight n V (x j) :=
    ae_all_iff.mpr (fun j => (quasiMeasurePreserving_eval (fun _ => (volume : Measure ℂ))
        j).ae_eq_comp (hi j))
  filter_upwards [l2PiProductVector_coeFn (fun _ => (volume : Measure ℂ)) u, hall] with x hx hh
  change l2PiProductVector (fun _ => (volume : Measure ℂ)) u x = _
  rw [hx]
  simp only [hh, Finset.prod_mul_distrib, piPotentialHalfWeight]
  rfl

theorem planarPiTranslatedGraph_integral_dbar_ae {m : ℕ}
    (n : ℕ) (V : ℂ → ℝ) (hV : Continuous V) (φ : Fin (m + 1) → PlanarComplexCompactTest)
    (f : Configuration (m + 1) → ℂ) (hf : Continuous f) (hc : HasCompactSupport f)
    (i : Fin (m + 1)) :
    (((∫ a, f a • planarPiPureDbarGraph n V hV
      (fun j => planarComplexTestTranslate (φ j) (a j))
      ∂Measure.pi (fun _ => (volume : Measure ℂ))).2 i) : Configuration (m+1) → ℂ)
      =ᵐ[Measure.pi (fun _ => (volume : Measure ℂ))]
        (fun x => (∫ a, f a * piSeparatedDbarKernel φ i (x-a)
          ∂Measure.pi (fun _ => (volume : Measure ℂ))) * piPotentialHalfWeight (m+1) n V x) := by
  let μ := Measure.pi (fun _ : Fin (m+1) => (volume : Measure ℂ))
  let k := piSeparatedDbarKernel φ i
  have hg : Continuous (fun p : Configuration (m+1) × Configuration (m+1) =>
      (f p.1 * k (p.2-p.1)) * piPotentialHalfWeight (m+1) n V p.2) :=
    ((hf.comp continuous_fst).mul ((piSeparatedDbarKernel_continuous φ i).comp
      (continuous_snd.sub continuous_fst))).mul
      ((piPotentialHalfWeight_continuous (m+1) n V hV).comp continuous_snd)
  have hgc := (finiteTranslatedKernel_hasCompactSupport f k hc (piSeparatedDbarKernel_compact φ
      i)).mul_right
    (f' := fun p => piPotentialHalfWeight (m+1) n V p.2)
  let G := fun a => f a • planarPiPureWeightedDbar n V hV
    (fun j => planarComplexTestTranslate (φ j) (a j)) i
  let E : PlanarPiDbarGraphSpace (m+1) →L[ℂ] PlanarPiLebesgueL2 (m+1) :=
    (ContinuousLinearMap.proj i).comp (ContinuousLinearMap.snd ℂ _ _)
  have hG : Integrable G μ := E.integrable_comp (planarPiTranslatedGraph_integrable n V hV φ f hf
      hc)
  have hcoef (a) : (G a : Configuration (m+1) → ℂ) =ᵐ[μ]
      (fun x => (f a * k (x-a)) * piPotentialHalfWeight (m+1) n V x) := by
    filter_upwards [Lp.coeFn_smul (f a) (planarPiPureWeightedDbar n V hV
      (fun j => planarComplexTestTranslate (φ j) (a j)) i), planarPiTranslatedDbar_coeFn n V hV φ a
          i]
      with x hx hh
    rw [hx]
    change f a * _ = _
    rw [hh]
    exact (mul_assoc (f a) (k (x-a)) (piPotentialHalfWeight (m+1) n V x)).symm
  have he := finiteDimensionalL2_kernel_integral_ae μ _ hg hgc G hG hcoef
  have hi := E.integral_comp_comm (planarPiTranslatedGraph_integrable n V hV φ f hf hc)
  change (∫ a, G a ∂μ) = (∫ a, f a • planarPiPureDbarGraph n V hV
    (fun j => planarComplexTestTranslate (φ j) (a j)) ∂μ).2 i at hi
  rw [← hi]
  exact he.mono (fun x hx => hx.trans (integral_mul_const (piPotentialHalfWeight (m+1) n V x)
    (fun a : Configuration (m+1) => f a * k (x-a))))

theorem piSeparated_dbar_convolution_transfer {d : ℕ}
    (f : Configuration d → ℂ) (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f)
    (φ : Fin d → PlanarComplexCompactTest) (i : Fin d) (x : Configuration d) :
    (∫ a, f a * piSeparatedDbarKernel φ i (x-a)) =
      ∫ a, piComplexDbar i f a * ∏ j, φ j (x j-a j) := by
  let k : Configuration d → ℂ := fun z => ∏ j, φ j (z j)
  have hk : ContDiff ℝ 1 k := contDiff_prod (fun j _ =>
    ((φ j).property.1.of_le (by norm_num)).comp (contDiff_apply ℝ (fun _ => ℂ) j))
  have hkc : HasCompactSupport k := piSeparatedKernel_hasCompactSupport _ (fun j => (φ
      j).property.2)
  rw [piSeparatedDbarKernel_eq]
  exact finiteComplexDbar_convolution_transfer (volume : Measure (Configuration d)) f k hf hk hc hkc
    (Pi.single i 1) (Pi.single i Complex.I) x

end
end GinibrePoincare
