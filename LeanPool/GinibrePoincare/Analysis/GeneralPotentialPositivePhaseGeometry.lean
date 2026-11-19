/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GeneralPotentialPositivePhaseGeometry.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GeneralPotentialProjectionPhase
public import LeanPool.GinibrePoincare.Analysis.GeneralPotentialLpConjugation

/-!
# General potential positive phase geometry

Part of the nonquadratic potentials development of the
Ginibre Poincaré formalization.

Main results: `potentialPositivePhase_inner_star_zero`.
-/

@[expose] public section

open MeasureTheory
open scoped ComplexConjugate
namespace GinibrePoincare
noncomputable section

/-- The vectors of `L²(potentialMeasure n V)` of positive phase degree: those `x` with
`x ∘ (z ↦ a z) = a ^ d • x` for every unit complex number `a`, for some `d > 0`. -/
def potentialPositivePhaseVectors (n : ℕ) {V : Potential} (hV : Continuous V)
    (hrot : IsRotationalPotential V) : Set (Lp ℂ 2 (potentialMeasure n V)) :=
  {x | ∃ d : ℕ, 0 < d ∧ ∀ (a : ℂ) (ha : ‖a‖ = 1),
    potentialGlobalPhaseL2 n hV hrot a ha x = a ^ d • x}

theorem potentialPositivePhase_inner_star_zero {n d e : ℕ} {V : Potential}
    (hV : Continuous V) (hrot : IsRotationalPotential V) (hd : 0 < d) (he : 0 < e)
    (x y : Lp ℂ 2 (potentialMeasure n V))
    (hx : ∀ (a : ℂ) (ha : ‖a‖ = 1), potentialGlobalPhaseL2 n hV hrot a ha x = a ^ d • x)
    (hy : ∀ (a : ℂ) (ha : ‖a‖ = 1), potentialGlobalPhaseL2 n hV hrot a ha y = a ^ e • y) :
    inner ℂ x (star y) = 0 := by
  obtain ⟨a, ha, hpow⟩ := exists_unit_phase_pow_ne (d+e) 0 (by omega)
  have hs : potentialGlobalPhaseL2 n hV hrot a ha (star y) = conj (a^e) • star y := by
    rw [potentialGlobalPhaseL2_star, hy, complexLp_star_complex_smul]
  have hc : conj (a^d) * conj (a^e) ≠ 1 := by
    intro h
    apply hpow
    have hh : conj (a^(d+e)) = 1 := by simpa only [pow_add, map_mul] using h
    have hhh := congrArg (starRingEnd ℂ) hh
    simpa using hhh
  exact inner_eq_zero_of_isometry_eigencharacters (potentialGlobalPhaseL2 n hV hrot a ha)
    x (star y) (a^d) (conj (a^e)) (hx a ha) hs hc

end
end GinibrePoincare
