/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GeneralPotentialProjectionRealVariance.lean.
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

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import LeanPool.GinibrePoincare.Analysis.GeneralPotentialLpConjugation

/-!
# General potential projection real variance

Part of the nonquadratic potentials development of the
Ginibre Poincaré formalization.

Main results: `real_Lp_projection_norm_sq_le_two_residual`.
-/

@[expose] public section

open scoped InnerProductSpace ComplexConjugate
namespace GinibrePoincare
noncomputable section

/-- Real vectors lose at least half their squared norm to a complex orthogonal
projection when the projected vector is orthogonal to its conjugate. -/
theorem real_conjugation_projection_norm_sq_le_two_residual
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (P : H →L[ℂ] H) (ha : P.adjoint = P) (hi : P.comp P = P)
    (J : H →ₗᵢ[ℝ] H)
    (hJ : ∀ x y, inner ℂ (J x) (J y) = conj (inner ℂ x y))
    (u : H) (hu : J u = u) (ho : inner ℂ (P u) (J (P u)) = 0) :
    ‖u‖ ^ 2 ≤ 2 * ‖u - P u‖ ^ 2 := by
  let h := P u
  let r := u - h - J h
  have hp : P (P u) = P u := DFunLike.congr_fun hi u
  have hz : P (u - h) = 0 := by simp only [h, map_sub, hp, sub_self]
  have heh : inner ℂ (u - h) h = 0 := by
    change inner ℂ (u - h) (P u) = 0
    rw [← ha, ContinuousLinearMap.adjoint_inner_right, hz, inner_zero_left]
  have hhe : inner ℂ h (u - h) = 0 := by
    rw [← inner_conj_symm h (u - h), heh, map_zero]
  have hhr : inner ℂ h r = 0 := by
    dsimp [r]
    rw [inner_sub_right, hhe, ho, sub_self]
  have hse : inner ℂ (J h) (u - J h) = 0 := by
    have hh := hJ h (u - h)
    rw [map_sub, hu, hhe, map_zero] at hh
    exact hh
  have hsh : inner ℂ (J h) h = 0 := by
    rw [← inner_conj_symm (J h) h, ho, map_zero]
  have hsr : inner ℂ (J h) r = 0 := by
    dsimp [r]
    rw [inner_sub_right, inner_sub_right, hsh, sub_zero]
    simpa only [inner_sub_right] using hse
  have hsum : inner ℂ (h + J h) r = 0 := by rw [inner_add_left, hhr, hsr, add_zero]
  have hur : h + J h + r = u := by dsimp [r]; abel
  have hn : ‖u‖ ^ 2 = 2 * ‖h‖ ^ 2 + ‖r‖ ^ 2 := by
    rw [← hur]
    simp only [pow_two]
    rw [norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ hsum,
      norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ ho, J.norm_map]
    ring
  have her : u - h = J h + r := by dsimp [r]; abel
  have he : ‖u - h‖ ^ 2 = ‖h‖ ^ 2 + ‖r‖ ^ 2 := by
    rw [her]
    simpa only [pow_two, J.norm_map] using
      norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (J h) r hsr
  change ‖u‖ ^ 2 ≤ 2 * ‖u - h‖ ^ 2
  rw [hn, he]
  nlinarith [sq_nonneg ‖r‖]

/-- The same estimate for genuine value conjugation in arbitrary complex L². -/
theorem real_Lp_projection_norm_sq_le_two_residual
    {X : Type*} [MeasurableSpace X] (μ : MeasureTheory.Measure X)
    (P : MeasureTheory.Lp ℂ 2 μ →L[ℂ] MeasureTheory.Lp ℂ 2 μ)
    (ha : P.adjoint = P) (hi : P.comp P = P)
    (u : MeasureTheory.Lp ℂ 2 μ) (hu : star u = u)
    (ho : inner ℂ (P u) (star (P u)) = 0) :
    ‖u‖ ^ 2 ≤ 2 * ‖u - P u‖ ^ 2 := by
  exact real_conjugation_projection_norm_sq_le_two_residual P ha hi
    (complexLpConjugationIsometry μ) (complexLp_inner_star_star μ) u hu ho

end
end GinibrePoincare
