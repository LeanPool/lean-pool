/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceGUEH1Closure.lean.
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
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceGUERealPoincare
public import LeanPool.GinibrePoincare.Analysis.MatrixGaussianH1Closure
/-!
# Correspondence GUEH 1 closure

Part of the gaussian log-Sobolev and entropy development of the
Ginibre Poincaré formalization.

Main results: `gueH1Completion_square_lsi`, `gueH1Completion_poincare`.
-/

@[expose] public section
open MeasureTheory Filter Set
open scoped Topology ContDiff
namespace GinibrePoincare
noncomputable section

/-- Real `L²` with respect to the ordered GUE measure `gueOrderedMeasure n`. -/
abbrev GUEValueL2 (n : ℕ) := Lp ℝ 2 (gueOrderedMeasure n)
/-- `EuclideanSpace ℝ (Fin n)`-valued `L²` with respect to `gueOrderedMeasure n`, for gradients. -/
abbrev GUEGradientL2 (n : ℕ) := Lp (EuclideanSpace ℝ (Fin n)) 2 (gueOrderedMeasure n)
/-- Value–gradient pairs in `GUEValueL2 n × GUEGradientL2 n`. -/
abbrev GUESobolevPair (n : ℕ) := GUEValueL2 n×GUEGradientL2 n

/-- The value–gradient pairs `(f, gradient f)` of compactly supported `C¹` functions `f`. -/
def gueCompactC1Pairs (n : ℕ) : Set (GUESobolevPair n) :=
  {p | ∃f : EuclideanSpace ℝ (Fin n) → ℝ, ContDiff ℝ 1 f ∧ HasCompactSupport f ∧
    (p.1 : EuclideanSpace ℝ (Fin n) → ℝ)=ᵐ[gueOrderedMeasure n]f ∧
    (p.2 : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))=ᵐ[gueOrderedMeasure n]gradient f}

/-- The `H¹` space of `gueOrderedMeasure n`: the closure of `gueCompactC1Pairs n`. -/
def gueH1Completion (n : ℕ) : Set (GUESobolevPair n) := closure (gueCompactC1Pairs n)

theorem gueH1Completion_square_lsi {n : ℕ} (hn : 0 < n)
    (p : GUESobolevPair n) (hp : p ∈ gueH1Completion n) :
    Integrable (fun x => p.1 x^2*Real.log (p.1 x^2)) (gueOrderedMeasure n) ∧
    squareEntropy (gueOrderedMeasure n) p.1 ≤ (2/(n : ℝ))*‖p.2‖^2 := by
  let := gueOrderedMeasure_probability hn
  have hc : IsClosed {p : GUESobolevPair n |
      Integrable (fun x => p.1 x^2*Real.log (p.1 x^2)) (gueOrderedMeasure n) ∧
      squareEntropy (gueOrderedMeasure n) p.1 ≤ (2/(n : ℝ))*‖p.2‖^2} := by
    apply IsSeqClosed.isClosed
    intro q r hq hr
    exact squareEntropy_le_of_L2_tendsto (gueOrderedMeasure n) (fun k => (q k).1) r.1
      (fun k => (2/(n : ℝ))*‖(q k).2‖^2) ((2/(n : ℝ))*‖r.2‖^2)
      (continuous_fst.tendsto r |>.comp hr)
      ((continuous_snd.tendsto r |>.comp hr).norm.pow 2 |>.const_mul _)
      (fun k => (hq k).1) (fun k => (hq k).2)
  apply closure_minimal ?_ hc hp
  intro q hq
  obtain ⟨f, hf, hs, hv, hg⟩ := hq
  have hlog := (continuous_square_mul_log hf.continuous).integrable_of_hasCompactSupport
    (μ := gueOrderedMeasure n) (compactSupport_square_mul_log hs)
  refine ⟨hlog.congr ?_,?_⟩
  · filter_upwards [hv] with x hx
    simp [hx]
  · rw [squareEntropy_congr_ae _ hv,← integral_norm_sq_eq_L2_norm_sq]
    have he : (∫x, ‖q.2 x‖^2 ∂gueOrderedMeasure n)=
        (∫x, ‖gradient f x‖^2 ∂gueOrderedMeasure n) := by
      apply integral_congr_ae
      filter_upwards [hg] with x hx
      rw [hx]
    rw [he]
    exact gueOrderedMeasure_square_lsi hn f hf hs

/-- The constant function `1` in `GUEValueL2 n`. -/
def gueOneL2 (n : ℕ) (hn : 0 < n) : GUEValueL2 n := by
  letI := gueOrderedMeasure_probability hn
  exact (memLp_const (1 : ℝ)).toLp (fun _ => 1)

theorem gueOneL2_ae (n : ℕ) (hn : 0 < n) :
    (gueOneL2 n hn : EuclideanSpace ℝ (Fin n) → ℝ)=ᵐ[gueOrderedMeasure n]fun _ => 1 := by
  let := gueOrderedMeasure_probability hn
  exact (memLp_const (1 : ℝ)).coeFn_toLp

theorem gueH1Completion_poincare {n : ℕ} (hn : 0 < n)
    (p : GUESobolevPair n) (hp : p ∈ gueH1Completion n) :
    (∫x, p.1 x^2 ∂gueOrderedMeasure n)-(∫x, p.1 x ∂gueOrderedMeasure n)^2 ≤
      (1/(n : ℝ))*‖p.2‖^2 := by
  let := gueOrderedMeasure_probability hn
  have hv (u : GUEValueL2 n) :
      ‖u‖^2-(inner ℝ (gueOneL2 n hn) u)^2=
        (∫x, u x^2 ∂gueOrderedMeasure n)-(∫x, u x ∂gueOrderedMeasure n)^2 := by
    rw [← integral_square_eq_L2_norm_sq, L2.inner_def]
    congr 2
    apply integral_congr_ae
    filter_upwards [gueOneL2_ae n hn] with x hx
    simp [hx]
  have hc : IsClosed {p : GUESobolevPair n |
      ‖p.1‖^2-(inner ℝ (gueOneL2 n hn) p.1)^2≤(1/(n : ℝ))*‖p.2‖^2} := by
    apply isClosed_le
    · exact continuous_fst.norm.pow 2 |>.sub ((continuous_const.inner continuous_fst).pow 2)
    · exact continuous_const.mul (continuous_snd.norm.pow 2)
  rw [← hv p.1]
  apply closure_minimal ?_ hc hp
  intro q hq
  obtain ⟨f, hf, hs, huf, hgf⟩ := hq
  change ‖q.1‖^2-(inner ℝ (gueOneL2 n hn) q.1)^2≤(1/(n : ℝ))*‖q.2‖^2
  rw [hv q.1,← integral_norm_sq_eq_L2_norm_sq]
  have hsquare : (∫x, q.1 x^2 ∂gueOrderedMeasure n)=(∫x, f x^2 ∂gueOrderedMeasure n) :=
    integral_congr_ae (huf.fun_comp (fun t => t^2))
  have he : (∫x, ‖q.2 x‖^2 ∂gueOrderedMeasure n)=(∫x, ‖gradient f x‖^2 ∂gueOrderedMeasure n) :=
    integral_congr_ae (hgf.fun_comp (fun t => ‖t‖^2))
  rw [hsquare, integral_congr_ae huf, he]
  exact gueOrderedMeasure_poincare_compactC1 hn f hf hs

end
end GinibrePoincare
