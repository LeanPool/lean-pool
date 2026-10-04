/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/

-- Adapted for Lean Pool's pinned Lean and Mathlib; upstream commit is recorded in projects.yml.
module

public import LeanPool.EllipticPDE.Regularity.CoeffC1


/-!
# `W^{1,∞}` principal coefficients

Evans, *Partial Differential Equations* (2nd ed.), §6.3.1, Theorem 1 asks `aᵢⱼ ∈ C¹` for the
interior `H²` estimate, where Guo, *Partial Differential Equations* (Course Lecture
Notes), Theorem VIII.3.2 (p. 65) asks `aᵢⱼ ∈ W^{1,∞}`. On `ℝᵈ` a `W^{1,∞}` function is one
with a Lipschitz representative, so in its pointwise form the hypothesis is the Lipschitz
estimate of `IsLipCoeff` below.

The estimate consumes the hypothesis through `abs_diffQuot_coeff_le` alone, which
`IsC1Coeff` supplies by the mean value inequality and a Lipschitz coefficient supplies
outright. `IsC1Coeff.toIsLipCoeff` is therefore what makes the `C¹` statement the instance:
the interior estimate, higher interior regularity and interior smoothness all run over
`IsLipCoeff` and no step of them asks a principal coefficient to be differentiable.

## Main declarations

* `IsLipCoeff`: the Lipschitz estimate on the principal coefficients.
* `IsLipCoeff.abs_diffQuot_coeff_le`: the coefficient difference-quotient bound.
* `IsC1Coeff.toIsLipCoeff`: the bridge, by the segment mean value inequality.

## Statements this file does not supply

The passage from an `IsWkInftyCoeff A 1` bundle, whose derivative bound is essential rather
than pointwise, to `IsLipCoeff`. That passage is the statement that a `W^{1,∞}` function has
a Lipschitz representative, and Mathlib has Rademacher's theorem in the opposite direction
alone (`LipschitzWith.ae_differentiableAt`). Until it is proved the two hypotheses are
distinct, and `interior_smooth` asks `IsLipCoeff` beside its `W^{k,∞}` bundles rather than
reading the first from the second.
-/

@[expose] public section

open MeasureTheory

noncomputable section

namespace EllipticPdes.Regularity

open EllipticPdes.Sobolev

variable {d : ℕ}

/-- A `W^{1,∞}` ellipticity bundle in pointwise form: every entry of the coefficient matrix
satisfies the Lipschitz estimate with one constant `A₁`, and no entry is asked to be
differentiable. -/
structure IsLipCoeff (A : EllipticCoeff d) where
  /-- The uniform Lipschitz constant of the entries. -/
  A1 : ℝ
  /-- `A1` is nonnegative. -/
  A1_nonneg : 0 ≤ A1
  /-- Every entry is Lipschitz with constant `A1`. -/
  lip : ∀ i j, ∀ x y : EuclideanSpace ℝ (Fin d), |A.a x i j - A.a y i j| ≤ A1 * ‖x - y‖

/-- The coefficient difference quotient is uniformly bounded: for the `(i, j)` coefficient
entry, `|Dₖʰ aᵢⱼ(x)| ≤ A₁` for every `x` and every `h ≠ 0`. This is the pointwise
commutator bound used in the master interior estimate to control the coefficient-
difference-quotient term `∑ ∫ (Dₖʰ aᵢⱼ) ∂ᵢu · ∂ⱼ(ζ² Dₖʰ u)` (Evans, *Partial Differential
Equations* (2nd ed.), §6.3.1), and it is the whole of what that estimate asks of the
principal coefficients beyond their bounds. -/
theorem IsLipCoeff.abs_diffQuot_coeff_le {A : EllipticCoeff d} (hA : IsLipCoeff A)
    (i j k : Fin d) {h : ℝ} (hh : h ≠ 0) (x : EuclideanSpace ℝ (Fin d)) :
    |(A.a (x + hshift k h) i j - A.a x i j) / h| ≤ hA.A1 := by
  have hnorm : ‖(x + hshift k h) - x‖ = |h| := by
    have hsub : (x + hshift k h) - x = hshift k h := by abel
    rw [hsub, hshift, norm_smul]
    simp
  have hlip : |A.a (x + hshift k h) i j - A.a x i j| ≤ hA.A1 * |h| := by
    have := hA.lip i j (x + hshift k h) x
    rwa [hnorm] at this
  rw [abs_div, div_le_iff₀ (abs_pos.mpr hh)]
  simpa [Real.norm_eq_abs] using hlip

/-- **A `C¹` bundle is a `W^{1,∞}` bundle.** The segment mean value inequality turns the
pointwise bound on the first derivatives into the Lipschitz estimate with the same constant,
so a result proved under `IsLipCoeff` applies to a `C¹` coefficient and Guo's hypothesis is
no stronger than Evans's as far as the principal coefficients go. -/
def IsC1Coeff.toIsLipCoeff {A : EllipticCoeff d} (hA : IsC1Coeff A) : IsLipCoeff A where
  A1 := hA.A1
  A1_nonneg := hA.A1_nonneg
  lip i j x y := by
    have hMVT : ‖A.a x i j - A.a y i j‖ ≤ hA.A1 * ‖x - y‖ :=
      Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (f := fun z => A.a z i j)
        (s := Set.univ) (C := hA.A1)
        (fun z _ => (hA.contDiff i j).differentiable_one z)
        (fun z _ => hA.grad_bdd i j z)
        convex_univ (Set.mem_univ y) (Set.mem_univ x)
    simpa [Real.norm_eq_abs] using hMVT

end EllipticPdes.Regularity
