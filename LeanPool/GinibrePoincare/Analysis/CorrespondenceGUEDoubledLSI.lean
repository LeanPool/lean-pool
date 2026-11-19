/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceGUEDoubledLSI.lean.
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
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceGUERegularizedPotential
/-!
# Correspondence GUE doubled LSI

Part of the gaussian log-Sobolev and entropy development of the
Ginibre Poincaré formalization.

Main results: `gueDoubledRegularizedGibbs_lsi`.
-/

@[expose] public section
open Set MeasureTheory
open scoped ContDiff
namespace GinibrePoincare
noncomputable section

/-- The real GUE chamber regularization with independent Gaussian dummy
imaginary coordinates, written in actual 2n-dimensional Euclidean space. -/
def gueDoubledRegularizedPotential (n : ℕ) (ε : ℝ)
    (x : EuclideanSpace ℝ (Fin n × Fin 2)) : ℝ :=
  (n : ℝ)/2*‖x‖^2 + ∑ p ∈ guePairs n, 2*gueLogBarrier ε (x (p.2, 0)-x (p.1, 0))

theorem gueDoubledRegularizedPotential_contDiff (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ContDiff ℝ 2 (gueDoubledRegularizedPotential n ε) := by
  apply ContDiff.add
  · exact contDiff_const.mul (contDiff_norm_sq ℝ)
  · apply ContDiff.sum
    intro p hp
    have hd : ContDiff ℝ 2 (fun x : EuclideanSpace ℝ (Fin n×Fin 2) => x (p.2, 0)-x (p.1, 0)) := by
      convert ((PiLp.proj 2 (fun _ : Fin n×Fin 2 => ℝ) (p.2, 0)).contDiff (𝕜 := ℝ)).sub
        ((PiLp.proj 2 (fun _ : Fin n×Fin 2 => ℝ) (p.1, 0)).contDiff (𝕜 := ℝ)) using 1
      funext x
      rfl
    exact contDiff_const.mul ((gueLogBarrier_contDiff hε).comp hd)

theorem gueDoubledRegularizedPotential_convex (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ConvexOn ℝ univ (fun x => gueDoubledRegularizedPotential n ε x-(n : ℝ)/2*‖x‖^2) := by
  have hc : ConvexOn ℝ univ (fun x : EuclideanSpace ℝ (Fin n×Fin 2) =>
      ∑ p ∈ guePairs n, 2*gueLogBarrier ε (x (p.2, 0)-x (p.1, 0))) := by
    refine ⟨convex_univ,?_⟩
    intro x hx y hy a b ha hb hab
    simp only [smul_eq_mul, Finset.mul_sum]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro p hp
    have hh := (gueLogBarrier_convex hε).2 (mem_univ (x (p.2, 0)-x (p.1, 0)))
      (mem_univ (y (p.2, 0)-y (p.1, 0))) ha hb hab
    simp only [smul_eq_mul] at hh
    have he : (a • x+b • y) (p.2, 0)-(a • x+b • y) (p.1, 0) =
        a*(x (p.2, 0)-x (p.1, 0))+b*(y (p.2, 0)-y (p.1, 0)) := by
      simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
      ring
    rw [he]
    nlinarith
  convert hc using 1
  funext x
  simp [gueDoubledRegularizedPotential]

/-- Concrete exact-curvature Bakry–Émery LSI for the real chamber's smooth
regularization with Gaussian dummy coordinates. No diffusion or LSI premise. -/
theorem gueDoubledRegularizedGibbs_lsi {n : ℕ} (hn : 0 < n) {ε : ℝ} (hε : 0 < ε)
    (f : EuclideanSpace ℝ (Fin n × Fin 2) → ℝ) (hf : ContDiff ℝ 1 f) (hs : HasCompactSupport f) :
    squareEntropy (bakryEmeryNormalizedGibbs volume (gueDoubledRegularizedPotential n ε)) f ≤
      (2/(n : ℝ))*∫ x, ‖gradient f x‖^2 ∂bakryEmeryNormalizedGibbs volume
          (gueDoubledRegularizedPotential n ε) := by
  let W := gueDoubledRegularizedPotential n ε ∘ configurationEuclideanEquiv n
  have hW : ContDiff ℝ 2 W := (gueDoubledRegularizedPotential_contDiff n hε).comp
    (configurationEuclideanEquiv n).contDiff
  have hc : ConvexOn ℝ univ (fun x : EuclideanSpace ℝ (Fin n×Fin 2) =>
      W ((configurationEuclideanEquiv n).symm x)-(n : ℝ)/2*‖x‖^2) := by
    simpa only [W, Function.comp_apply, ContinuousLinearEquiv.apply_symm_apply] using
      gueDoubledRegularizedPotential_convex n hε
  have hh := bakryEmeryConfigurationGibbs_square_lsi n hn W hW (n : ℝ) (Nat.cast_pos.mpr hn)
    hc f hf hs
  simpa only [W, Function.comp_def, ContinuousLinearEquiv.apply_symm_apply] using hh

end
end GinibrePoincare
