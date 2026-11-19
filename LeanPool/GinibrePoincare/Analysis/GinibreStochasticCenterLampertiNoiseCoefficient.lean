/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreStochasticCenterLampertiNoiseCoefficient.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticCenterCIRNoiseCoefficient
public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticCenterLampertiGenerator
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! The actual square-root center test is smooth away from zero center and
has the constant center Brownian noise amplitude prescribed by the paper. -/

@[expose] public section
open Set
open scoped Topology ContDiff
namespace GinibrePoincare
noncomputable section

theorem ginibre_fderiv_squareRootCenter {n : ℕ} (_ : 2 ≤ n)
    (z : Configuration n) (hz : 0 < ginibreCenterSquared n z) (v : Configuration n) :
    fderiv ℝ (ginibreSquareRootCenter n) z v =
      (1/(2*Real.sqrt ((ginibreCenterSquared n) z)))*fderiv ℝ (ginibreCenterSquared n) z v := by
  have hd : DifferentiableAt ℝ ((ginibreCenterSquared n) : Configuration n → ℝ) z :=
    (contDiff_ginibreCenterSquared n).differentiable (by simp) z
  change fderiv ℝ (fun w : Configuration n => Real.sqrt ((ginibreCenterSquared n) w)) z v = _
  rw [fderiv_sqrt hd hz.ne']
  rfl

theorem ginibreCenterCIR_noise_amplitude_factor {n : ℕ} (α : ℝ) (z : Configuration n)
    (hρ : 0 ≤ (ginibreCenterSquared n) z) :
    Real.sqrt ((8*α/(n : ℝ))*(ginibreCenterSquared n) z) =
      (2*Real.sqrt ((ginibreCenterSquared n) z))*Real.sqrt (2*α/(n : ℝ)) := by
  have he : (8*α/(n : ℝ))*(ginibreCenterSquared n) z=(4*(ginibreCenterSquared n) z)*(2*α/(n : ℝ)) :=
      by ring
  have h4 : Real.sqrt (4*(ginibreCenterSquared n) z)=2*Real.sqrt ((ginibreCenterSquared n) z) := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
    norm_num
  rw [he, Real.sqrt_mul (mul_nonneg (by norm_num) hρ), h4]

theorem ginibre_squareRootCenter_noise_coordinate {n : ℕ} (hn : 2 ≤ n)
    (α : ℝ) (hα : 0 ≤ α) (z : Configuration n) (hz : 0 < ginibreCenterSquared n z)
    (e : EuclideanSpace ℝ (Fin n × Fin 2)) (i : Fin n × Fin 2) :
    Real.sqrt (2*α/(n : ℝ)^2)*fderiv ℝ (ginibreSquareRootCenter n) z (ginibreCoordinateDirection i)
        =
      Real.sqrt (2*α/(n : ℝ))*ginibreCenterRadialDirection n e z i := by
  have hρ := hz
  have hs : Real.sqrt ((ginibreCenterSquared n) z) ≠ 0 := (Real.sqrt_pos.mpr hρ).ne'
  rw [ginibre_fderiv_squareRootCenter hn z hz]
  calc
    _ = (1/(2*Real.sqrt ((ginibreCenterSquared n) z)))*
        (Real.sqrt (2*α/(n : ℝ)^2)*fderiv ℝ (ginibreCenterSquared n) z (ginibreCoordinateDirection
            i)) := by ring
    _ = _ := by
      rw [ginibreCenterCIR_noise_coordinate (by omega) α hα z hz.ne' e i,
          ginibreCenterCIR_noise_amplitude_factor α z hρ.le]
      field_simp
end
end GinibrePoincare
