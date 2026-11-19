/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceDolbeaultYoungMollifierPairing.lean.
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
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceDolbeaultYoungMultiplierComposition
public import LeanPool.GinibrePoincare.Analysis.NonQuadraticPiBumpAverage
public import Mathlib.Analysis.Calculus.ContDiff.Convolution
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-!
# Correspondence Dolbeault Young mollifier pairing

Part of the complex Gaussian and Hermite analysis development of the
Ginibre Poincaré formalization.

Main results: `dolbeaultPiBump_contDiff`, `dolbeaultPiBump_convolution_test`,
`dolbeaultPiBump_average_test`.
-/

@[expose] public section
open MeasureTheory Filter ContinuousLinearMap
open scoped Topology ContDiff Convolution
namespace GinibrePoincare
noncomputable section

theorem dolbeaultPiBump_contDiff (n : ℕ) (φ : ContDiffBump (0 : ℂ)) :
    ContDiff ℝ ∞ (piPlanarBump n φ) := by
  unfold piPlanarBump
  apply contDiff_prod
  intro i hi
  exact (φ.contDiff_normed (n := ⊤)).comp (contDiff_apply ℝ (fun _ => ℂ) i)

theorem dolbeaultPiBump_convolution_test (n : ℕ) (φ : ContDiffBump (0 : ℂ))
    (f θ : Configuration n → ℂ) (hf : Integrable f volume)
    (hθ : Continuous θ) (hc : HasCompactSupport θ) :
    (∫ x, (piPlanarBump n φ ⋆[lsmul ℝ ℝ, volume] f) x*θ x) =
      ∫ y, (piPlanarBump n φ y : ℂ)*(∫ x, f (x-y)*θ x) := by
  obtain ⟨C, hC⟩ := hθ.bounded_above_of_compact_support hc
  have hb : Integrable (fun p : Configuration n × Configuration n =>
      (piPlanarBump n φ p.2 : ℂ)*f (p.1-p.2)) (volume.prod volume) := by
    simpa only [lsmul_apply, Complex.real_smul] using
      (piPlanarBump_integrable n φ).convolution_integrand (lsmul ℝ ℝ) hf
  have hi : Integrable (fun p : Configuration n × Configuration n =>
      (piPlanarBump n φ p.2 : ℂ)*f (p.1-p.2)*θ p.1) (volume.prod volume) :=
    hb.mul_bdd (hθ.comp continuous_fst).aestronglyMeasurable (ae_of_all _ (fun p => hC p.1))
  calc
    _ = ∫ x, ∫ y, (piPlanarBump n φ y : ℂ)*f (x-y)*θ x := by
      simp only [convolution_lsmul, Complex.real_smul, integral_mul_const]
    _ = ∫ y, ∫ x, (piPlanarBump n φ y : ℂ)*f (x-y)*θ x := integral_integral_swap hi
    _ = _ := by
      apply integral_congr_ae
      exact ae_of_all _ (fun y => by simp only [mul_assoc, integral_const_mul])

theorem dolbeaultPiBump_average_test (n : ℕ) (φ : ContDiffBump (0 : ℂ))
    (u : dolbeaultOrdinaryL2 n) (θ : Configuration n → ℂ)
    (hθ : Continuous θ) (hc : HasCompactSupport θ) :
    (∫ x, (piL2BumpAverage n φ u) x*θ x) =
      ∫ y, (piPlanarBump n φ y : ℂ)*(∫ x, u (x-y)*θ x) := by
  let T := (dolbeaultCompactPairing θ hθ hc).restrictScalars ℝ
  have ht (v : dolbeaultOrdinaryL2 n) : T v=∫ x, v x*θ x := by
    change dolbeaultCompactPairing θ hθ hc v=_
    rw [dolbeaultCompactPairing_eq_integral θ hθ hc]
    apply integral_congr_ae
    exact ae_of_all _ (fun x => mul_comm _ _)
  rw [← ht]
  change T (∫ x, piPlanarBump n φ x • lebesgueL2Translate n x u) = _
  rw [← T.integral_comp_comm (integrable_piL2BumpIntegrand n φ u)]
  apply integral_congr_ae
  exact ae_of_all _ (fun y => by
    dsimp only
    rw [map_smul, ht, Complex.real_smul]
    congr 1
    apply integral_congr_ae
    filter_upwards [lebesgueL2Translate_ae n y u] with x hx
    rw [hx])

end
end GinibrePoincare
