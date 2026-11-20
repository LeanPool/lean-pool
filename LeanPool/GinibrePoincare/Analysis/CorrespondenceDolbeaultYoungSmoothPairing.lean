/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceDolbeaultYoungSmoothPairing.lean.
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
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceDolbeaultYoungSmoothGeometry

/-!
# Correspondence Dolbeault Young smooth pairing

Part of the complex Gaussian and Hermite analysis development of the
Ginibre Poincaré formalization.

Main results: `dolbeaultCoordinatePointwise_compact_test`.
-/

@[expose] public section
open MeasureTheory
namespace GinibrePoincare
noncomputable section

theorem dolbeaultCoordinatePointwise_integrable_prod {n : ℕ} (j : Fin n)
    (k : ℂ → ℂ) (hk : Integrable k volume) (f : Configuration n → ℂ)
    (hf : Continuous f) (hfi : Integrable f volume) :
    Integrable (fun p : ℂ × Configuration n => k p.1*f (p.2-Pi.single j p.1))
      (volume.prod volume) := by
  have hm : AEStronglyMeasurable
      (fun p : ℂ × Configuration n => k p.1*f (p.2-Pi.single j p.1)) (volume.prod volume) := by
    apply hk.aestronglyMeasurable.comp_fst.mul
    apply Continuous.aestronglyMeasurable
    apply hf.comp
    apply continuous_snd.sub
    apply continuous_pi
    intro l
    by_cases hl : l=j
    · subst l
      simpa using continuous_fst
    · simpa [Pi.single_eq_of_ne hl] using (continuous_const : Continuous (fun _ : ℂ × Configuration
        n => (0 : ℂ)))
  apply (integrable_prod_iff hm).mpr
  constructor
  · exact ae_of_all _ (fun y =>
      ((dolbeaultCoordinateTranslation_preserving j y).integrable_comp_of_integrable hfi).const_mul
          (k y))
  · have he (y : ℂ) : (∫ x : Configuration n, ‖k y*f (x-Pi.single j y)‖) =
        ‖k y‖*(∫ x : Configuration n, ‖f x‖) := by
      simp_rw [norm_mul]
      rw [integral_const_mul]
      have ht := integral_sub_right_eq_self (μ := (volume : Measure (Configuration n)))
        (fun x : Configuration n => ‖f x‖) (Pi.single j y : Configuration n)
      rw [ht]
    simp_rw [he]
    exact hk.norm.mul_const _

theorem dolbeaultCoordinatePointwise_compact_test {n : ℕ} (j : Fin n)
    (k : ℂ → ℂ) (hk : Integrable k volume) (f : Configuration n → ℂ)
    (hf : Continuous f) (hfi : Integrable f volume)
    (θ : Configuration n → ℂ) (hθ : Continuous θ) (hc : HasCompactSupport θ) :
    (∫ x : Configuration n, θ x*dolbeaultCoordinateConvolutionPointwise j k f x) =
      ∫ y : ℂ, k y*(∫ x : Configuration n, θ x*f (x-Pi.single j y)) := by
  obtain ⟨C, hC⟩ := hθ.bounded_above_of_compact_support hc
  have hi : Integrable (fun p : ℂ × Configuration n =>
      k p.1*f (p.2-Pi.single j p.1)*θ p.2) (volume.prod volume) :=
    (dolbeaultCoordinatePointwise_integrable_prod j k hk f hf hfi).mul_bdd
      (hθ.comp continuous_snd).aestronglyMeasurable (ae_of_all _ (fun p => hC p.2))
  have he (x : Configuration n) : θ x*dolbeaultCoordinateConvolutionPointwise j k f x =
      ∫ y : ℂ, k y*f (x-Pi.single j y)*θ x := by
    unfold dolbeaultCoordinateConvolutionPointwise
    rw [← integral_const_mul]
    congr 1
    funext y
    ring
  simp_rw [he]
  have hi' : Integrable (Function.uncurry (fun (x : Configuration n) (y : ℂ) =>
      k y*f (x-Pi.single j y)*θ x)) (volume.prod volume) := by
    convert hi.swap using 1
    funext p
    rcases p with ⟨x, y⟩
    rfl
  rw [integral_integral_swap hi']
  apply integral_congr_ae
  exact ae_of_all _ (fun y => by
    dsimp only
    rw [← integral_const_mul]
    congr 1
    funext x
    ring)

end
end GinibrePoincare
