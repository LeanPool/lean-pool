/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GeneralRadialProjectionCharacters.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GeneralRadialProjectionFourier

/-!
# General radial projection characters

Part of the nonquadratic potentials development of the
Ginibre Poincaré formalization.

Main results: `circle_orbit_fourierCoeff_eigen`.
-/

@[expose] public section

open MeasureTheory Set
open scoped Topology
namespace GinibrePoincare
noncomputable section

/-- Translation of the actual Bochner circle coefficient has its exact character. -/
theorem circle_fourierCoeff_translate {T : ℝ} [Fact (0 < T)]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (f : AddCircle T → E) (k : ℤ) (s : AddCircle T) :
    fourierCoeff (fun t => f (t + s)) k = fourier k s • fourierCoeff f k := by
  have hchar (t : AddCircle T) : fourier k s * fourier (-k) (t + s) = fourier (-k) t := by
    have hsum : fourier (-k) (t + s) = fourier (-k) t * fourier (-k) s := by
      simp only [fourier_apply, smul_add, AddCircle.toCircle_add, Circle.coe_mul]
    have hcancel : fourier k s * fourier (-k) s = 1 := by
      rw [← fourier_add]
      simp only [add_neg_cancel, fourier_zero]
    rw [hsum]
    calc
      _ = fourier (-k) t * (fourier k s * fourier (-k) s) := by ring
      _ = _ := by rw [hcancel, mul_one]
  unfold fourierCoeff
  calc
    (∫ t : AddCircle T, fourier (-k) t • f (t + s) ∂AddCircle.haarAddCircle) =
        ∫ t : AddCircle T, fourier k s • (fourier (-k) (t + s) • f (t + s))
          ∂AddCircle.haarAddCircle := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun t => by simp only []; rw [smul_smul, hchar]
    _ = fourier k s • (∫ t : AddCircle T, fourier (-k) (t + s) • f (t + s)
          ∂AddCircle.haarAddCircle) := integral_smul _ _
    _ = _ := congrArg (fun v => fourier k s • v)
      (integral_add_right_eq_self (fun t : AddCircle T => fourier (-k) t • f t) s)

/-- Actual circle-orbit Fourier coefficients are genuine unitary eigenvectors. -/
theorem circle_orbit_fourierCoeff_eigen {T : ℝ} [Fact (0 < T)]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (U : AddCircle T → E ≃ₗᵢ[ℂ] E) (x : E)
    (_ : Continuous (fun t => U t x))
    (hadd : ∀ s t, U s (U t x) = U (t + s) x)
    (s : AddCircle T) (k : ℤ) :
    U s (fourierCoeff (fun t => U t x) k) =
      fourier k s • fourierCoeff (fun t => U t x) k := by
  rw [fourierCoeff]
  change (U s).toLinearIsometry (∫ t : AddCircle T, fourier (-k) t • U t x ∂AddCircle.haarAddCircle)
      = _
  rw [← (U s).toLinearIsometry.integral_comp_comm]
  have he : (fun t => U s (fourier (-k) t • U t x)) =
      (fun t => fourier (-k) t • U (t + s) x) := by
    funext t
    rw [map_smul, hadd]
  change (∫ t : AddCircle T, U s (fourier (-k) t • U t x) ∂AddCircle.haarAddCircle) = _
  rw [he]
  exact circle_fourierCoeff_translate (fun t => U t x) k s

end
end GinibrePoincare
