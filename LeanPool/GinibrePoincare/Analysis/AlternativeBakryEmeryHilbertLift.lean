/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/AlternativeBakryEmeryHilbertLift.lean.
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

public import LeanPool.GinibrePoincare.Analysis.AlternativeBakryEmeryConvexLift
public import LeanPool.GinibrePoincare.Analysis.AlternativeBakryEmeryRadialLift
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-! # Identification of the literal block lift with its Hilbert potential
The configuration coordinates carry a sup norm, while the diffusion uses
the Euclidean norm. This file explicitly bridges those two representations.
-/

@[expose] public section

open MeasureTheory
namespace GinibrePoincare
noncomputable section

/-- The Euclidean block coordinates, with complex dimension `k+1`. -/
abbrev BakryEmeryHilbertBlock (k : ℕ) := EuclideanSpace ℂ (Fin (k + 1))

/-- The physical squared radius is the squared Hilbert norm, not the square
of the configuration's sup norm. -/
theorem bakryEmeryBlock_radius_eq_hilbert_norm_sq (k : ℕ) (x : Configuration (k + 1)) :
    gaussianBlockRadius 1 (k + 1) x =
      ‖(WithLp.toLp 2 x : BakryEmeryHilbertBlock k)‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  simp only [gaussianBlockRadius, Nat.cast_one, one_mul, configurationNormSq,
    Complex.normSq_eq_norm_sq]

/-- The density in the literal Euclidean-volume construction uses precisely
the Hilbert potential whose strong convexity was proved. -/
theorem bakryEmeryBlock_profile_eq_hilbert_potential (n k : ℕ) (V : Potential)
    (x : Configuration (k + 1)) :
    (n : ℝ) * potentialSquaredRadiusProfile V (gaussianBlockRadius 1 (k + 1) x) =
      bakryEmeryEuclideanLiftPotential n V
        (WithLp.toLp 2 x : BakryEmeryHilbertBlock k) := by
  unfold potentialSquaredRadiusProfile bakryEmeryEuclideanLiftPotential
  rw [bakryEmeryBlock_radius_eq_hilbert_norm_sq, Real.sqrt_sq (norm_nonneg _)]

/-- The actual Hilbert block potential has exact `nρ` convexity, on the
Euclidean representation corresponding to the literal lift density. -/
theorem bakryEmeryBlock_hilbert_strongConvex (n k : ℕ) (ρ : ℝ) {V : Potential}
    (hrot : IsRotationalPotential V) (hc : IsRhoConvexPotential ρ V) :
    ConvexOn ℝ (Set.univ : Set (BakryEmeryHilbertBlock k))
      (fun x => bakryEmeryEuclideanLiftPotential n V x -
        ((n : ℝ) * ρ) / 2 * ‖x‖ ^ 2) :=
  bakryEmeryEuclideanLift_strongConvex n ρ hrot hc

end
end GinibrePoincare
