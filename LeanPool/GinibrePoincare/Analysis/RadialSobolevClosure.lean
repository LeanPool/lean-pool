/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/RadialSobolevClosure.lean.
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

public import LeanPool.GinibrePoincare.Analysis.EntropyL2Closure
public import LeanPool.GinibrePoincare.Analysis.GaussianRadialLift
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-!
# Radial Sobolev Closure
-/


@[expose] public section

open MeasureTheory
open scoped BigOperators ContDiff
namespace GinibrePoincare
noncomputable section

/-- The actual real Euclidean gradient, as a vector with `2n` coordinates. -/
def ginibreEuclideanGradient {n : ℕ} (f : Configuration n → ℝ) (z : Configuration n) :
    EuclideanSpace ℝ (Fin n × Fin 2) :=
  WithLp.toLp 2 (fun k => if k.2 = 0 then fderiv ℝ f z (realCoordinateDirection k.1)
    else fderiv ℝ f z (imaginaryCoordinateDirection k.1))

theorem ginibreEuclideanGradient_norm_sq {n : ℕ} (f : Configuration n → ℝ) (z : Configuration n) :
    ‖ginibreEuclideanGradient f z‖ ^ 2 = realGradientNormSq f z := by
  rw [PiLp.norm_sq_eq_of_L2]
  simp [ginibreEuclideanGradient, realGradientNormSq, Fintype.sum_prod_type,
    Fin.sum_univ_two, Real.norm_eq_abs, sq_abs]

theorem continuous_ginibreEuclideanGradient {n : ℕ} (f : Configuration n → ℝ)
    (hf : ContDiff ℝ ∞ f) : Continuous (ginibreEuclideanGradient f) := by
  apply (PiLp.continuous_toLp 2 (fun _ : Fin n × Fin 2 => ℝ)).comp
  apply continuous_pi
  intro k
  by_cases h : k.2 = 0
  · simpa only [h, ite_true] using
      (hf.continuous_fderiv (by simp)).clm_apply (continuous_const (y := realCoordinateDirection
        k.1))
  · simpa only [h, ite_false] using
      (hf.continuous_fderiv (by simp)).clm_apply (continuous_const (y :=
        imaginaryCoordinateDirection k.1))

theorem compactSupport_ginibreEuclideanGradient {n : ℕ} (f : Configuration n → ℝ)
    (hf : HasCompactSupport f) : HasCompactSupport (ginibreEuclideanGradient f) := by
  apply (hf.fderiv (𝕜 := ℝ)).mono
  intro z hz hd
  apply hz
  simp [ginibreEuclideanGradient, hd]
  rfl

def IsRadialSobolevCore {n : ℕ} (f : Configuration n → ℝ) : Prop :=
  IsSmoothCompactSymmetric f ∧ ∃ F : (Fin n → ℝ) → ℝ,
    ∀ z, f z = F (fun i => Complex.normSq (z i))

/-- The smooth radial core embedded into the actual value-gradient L² product. -/
def radialSobolevCorePairs (n : ℕ) : Set
    (Lp ℝ 2 (ginibreMeasure n) × Lp (EuclideanSpace ℝ (Fin n × Fin 2)) 2 (ginibreMeasure n)) :=
  {p | ∃ f : Configuration n → ℝ, IsRadialSobolevCore f ∧
    (p.1 : Configuration n → ℝ) =ᵐ[ginibreMeasure n] f ∧
    (p.2 : Configuration n → EuclideanSpace ℝ (Fin n × Fin 2)) =ᵐ[ginibreMeasure n]
      ginibreEuclideanGradient f}

/-- The radial symmetric Sobolev closure is the L² closure of genuine core value-gradient pairs. -/
def radialSobolevClosure (n : ℕ) := closure (radialSobolevCorePairs n)

/-- Every smooth compact radial symmetric function has a genuine core pair. -/
theorem radialSobolevCore_has_pair (n : ℕ) (hn : 0 < n)
    (f : Configuration n → ℝ) (hf : IsRadialSobolevCore f) :
    ∃ p ∈ radialSobolevCorePairs n,
      (p.1 : Configuration n → ℝ) =ᵐ[ginibreMeasure n] f ∧
      (p.2 : Configuration n → EuclideanSpace ℝ (Fin n × Fin 2)) =ᵐ[ginibreMeasure n]
        ginibreEuclideanGradient f := by
  have := ginibreMeasure_isProbabilityMeasure hn
  have hv : MemLp f 2 (ginibreMeasure n) :=
    hf.1.1.continuous.memLp_of_hasCompactSupport hf.1.2.1
  have hg : MemLp (ginibreEuclideanGradient f) 2 (ginibreMeasure n) :=
    (continuous_ginibreEuclideanGradient f hf.1.1).memLp_of_hasCompactSupport
      (compactSupport_ginibreEuclideanGradient f hf.1.2.1)
  refine ⟨(hv.toLp f, hg.toLp (ginibreEuclideanGradient f)), ?_, ?_, ?_⟩
  · exact ⟨f, hf, hv.coeFn_toLp, hg.coeFn_toLp⟩
  · exact hv.coeFn_toLp
  · exact hg.coeFn_toLp

/-- Entropy respects equality of representatives almost everywhere. -/
theorem squareEntropy_congr_ae {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {f g : α → ℝ} (h : f =ᵐ[μ] g) : squareEntropy μ f = squareEntropy μ g := by
  apply squareEntropy_eq_of_moments
  · apply integral_congr_ae
    exact h.mono (fun x hx => by dsimp; rw [hx])
  · apply integral_congr_ae
    exact h.mono (fun x hx => by dsimp; rw [hx])

theorem integral_norm_sq_eq_L2_norm_sq {α V : Type*} [MeasurableSpace α]
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] (μ : Measure α) (v : Lp V 2 μ) :
    (∫ x, ‖v x‖ ^ 2 ∂μ) = ‖v‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp only [real_inner_self_eq_norm_sq]

/-- Once the actual smooth radial core inequality is proved, its full L²
value-gradient Sobolev extension follows, including finiteness of entropy. -/
theorem radialSobolevClosure_lsi_of_core (n : ℕ) (hn : 0 < n)
    (hcore : ∀ f : Configuration n → ℝ, IsRadialSobolevCore f →
      ginibreSquareEntropy n f ≤ smoothGinibreEnergy n f) :
    ∀ p ∈ radialSobolevClosure n,
      Integrable (fun z => p.1 z ^ 2 * Real.log (p.1 z ^ 2)) (ginibreMeasure n) ∧
        squareEntropy (ginibreMeasure n) p.1 ≤ (1 / (n : ℝ)) * ‖p.2‖ ^ 2 := by
  have := ginibreMeasure_isProbabilityMeasure hn
  apply entropy_bound_on_closure
  intro p hp
  obtain ⟨f, hf, hv, hg⟩ := hp
  have he : squareEntropy (ginibreMeasure n) p.1 = ginibreSquareEntropy n f :=
    squareEntropy_congr_ae _ hv
  have hgrad : ‖p.2‖ ^ 2 = ∫ z, realGradientNormSq f z ∂ginibreMeasure n := by
    rw [← integral_norm_sq_eq_L2_norm_sq]
    apply integral_congr_ae
    filter_upwards [hg] with z hz
    rw [hz, ginibreEuclideanGradient_norm_sq]
  constructor
  · apply (integrable_square_mul_log_ginibre hn hf.1.1.continuous hf.1.2.1).congr
    exact hv.symm.mono (fun z hz => by dsimp; rw [hz])
  · rw [he, hgrad]
    exact hcore f hf

end
end GinibrePoincare
