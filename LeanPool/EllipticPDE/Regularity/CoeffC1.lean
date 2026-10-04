/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/
module

public import LeanPool.EllipticPDE.Sobolev.Coefficients
public import LeanPool.EllipticPDE.Regularity.DifferenceQuotient
public import Mathlib.Analysis.Calculus.MeanValue


/-!
# `C¹` coefficients and the coefficient difference-quotient bound

The interior `H²` estimate (Evans, *Partial Differential Equations* (2nd ed.), §6.3.1;
Gilbarg–Trudinger, *Elliptic Partial Differential Equations of Second Order*, Thm 8.8)
needs the manuscript hypothesis `aᵢⱼ ∈ C¹` only through one quantitative consequence: the
difference quotient of each coefficient entry is uniformly bounded by the sup of its
gradient. This file bundles that hypothesis as an added structure `IsC1Coeff` (a mixin on
top of `EllipticCoeff`, leaving every existing consumer of `EllipticCoeff` untouched) and
proves the coefficient difference-quotient bound `abs_diffQuot_coeff_le` by the segment
mean-value inequality.
-/

@[expose] public section

open MeasureTheory
open scoped RealInnerProductSpace

noncomputable section

namespace EllipticPdes.Regularity

open EllipticPdes.Sobolev

variable {d : ℕ}

/-- A `C¹` ellipticity bundle: the coefficient matrix is continuously differentiable with a
global bound `A₁` on the first derivatives of every entry. Faithful to `aᵢⱼ ∈ C¹` for the
interior estimate, where only `a ∈ C¹(closure W)` with `W ⋐ Ω` bounded matters, so
`A₁ < ∞`. -/
structure IsC1Coeff (A : EllipticCoeff d) where
  /-- Every coefficient entry is continuously differentiable. -/
  contDiff : ∀ i j, ContDiff ℝ 1 (fun x => A.a x i j)
  /-- The uniform bound on the first derivatives of every entry. -/
  A1 : ℝ
  /-- `A1` is nonnegative. -/
  A1_nonneg : 0 ≤ A1
  /-- The Fréchet derivative of every coefficient entry is bounded by `A1` at every point. -/
  grad_bdd : ∀ i j, ∀ x, ‖fderiv ℝ (fun y => A.a y i j) x‖ ≤ A1

/-- The coefficient difference quotient is uniformly bounded: for the `(i, j)` coefficient
entry, `|Dₖʰ aᵢⱼ(x)| ≤ A₁` for every `x` and every `h ≠ 0`. This is the pointwise
commutator bound used in the master interior estimate to control the coefficient-
difference-quotient term `∑ ∫ (Dₖʰ aᵢⱼ) ∂ᵢu · ∂ⱼ(ζ² Dₖʰ u)` (Evans, *Partial Differential
Equations* (2nd ed.), §6.3.1). -/
theorem IsC1Coeff.abs_diffQuot_coeff_le {A : EllipticCoeff d} (hA : IsC1Coeff A)
    (i j k : Fin d) {h : ℝ} (hh : h ≠ 0) (x : EuclideanSpace ℝ (Fin d)) :
    |(A.a (x + hshift k h) i j - A.a x i j) / h| ≤ hA.A1 := by
  have hMVT : ‖A.a (x + hshift k h) i j - A.a x i j‖ ≤ hA.A1 * ‖(x + hshift k h) - x‖ :=
    Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (f := fun y => A.a y i j)
      (s := Set.univ) (C := hA.A1)
      (fun y _ => (hA.contDiff i j).differentiable_one y)
      (fun y _ => hA.grad_bdd i j y)
      convex_univ (Set.mem_univ x) (Set.mem_univ (x + hshift k h))
  have hnorm : ‖(x + hshift k h) - x‖ = |h| := by
    have hsub : (x + hshift k h) - x = hshift k h := by abel
    rw [hsub, hshift, norm_smul]
    simp
  rw [hnorm] at hMVT
  rw [abs_div, div_le_iff₀ (abs_pos.mpr hh)]
  simpa [Real.norm_eq_abs] using hMVT

end EllipticPdes.Regularity
