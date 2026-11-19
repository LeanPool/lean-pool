/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Data.List.SignVariations
public import LeanPool.Ratpoints.Mathlib.Algebra.Polynomial.Sturm.Sequence
public import LeanPool.Ratpoints.Mathlib.Analysis.Polynomial.Order

import LeanPool.Ratpoints.Mathlib.Algebra.Polynomial.Eval.Coeff

/-!
# The sign variations of positive multiples and of polynomials near infinity

Candidates for a file of Mathlib on Sturm's theorem: lists of polynomials over an ordered field that
are entrywise positive multiples (`Polynomial.PosAssoc`), such as a generalized Sturm sequence and
the Sturm sequence of its first two entries, have the same sign variations at every point and at
`±∞` (`Polynomial.signVariations_map_eval_eq_of_forall₂`,
`Polynomial.signVariations_map_leadingCoeff_eq_of_forall₂`,
`Polynomial.signVariations_map_neg_one_pow_mul_leadingCoeff_eq_of_forall₂`); and far right, the sign
variations of a list of nonzero polynomials at a point are those of their leading coefficients, and
far left those of their leading coefficients, each times `(-1) ^ deg`
(`Polynomial.eventually_atTop_signVariations`, `Polynomial.eventually_atBot_signVariations`). The
image of a rational polynomial in an ordered field has at a rational point the sign of the value of
the polynomial (`Polynomial.sign_eval_map_ratCastHom`), so that a remainder chain computed over `ℚ`
has the signs of its image over `ℝ`.

## Implementation notes

The file has no Mathlib sibling: Mathlib has the Sturm sequence
(`Mathlib.Algebra.Polynomial.Sturm.Sequence`) and the sign variations of a list
(`Mathlib.Data.List.SignVariations`), but neither file imports the other, and Mathlib has neither
Sturm's theorem nor a file that imports both. So the file chooses its imports: the sign
variations, and the mirrors of the Sturm sequence (`Polynomial.PosAssoc`) and of the eventual signs
of polynomials (`Mathlib.Analysis.Polynomial.Order`, which brings the filters and the ordered
normed fields of the statements), and for its proofs the mirror of
`Mathlib.Algebra.Polynomial.Eval.Coeff`, with the values of the images of polynomials at rational
points (`Polynomial.eval_ratCast_map`).
-/

@[expose] public section

open Filter

namespace Polynomial

section PosAssoc

variable {K : Type*} [Field K] [LinearOrder K]

/-- Lists of polynomials that are entrywise positive multiples have the same sign variations under
every map `g` to a linear order that keeps the signs of positive multiples, such as the evaluation
at a point and the leading coefficient. -/
theorem signVariations_map_eq_of_forall₂ {β : Type*} [Zero β] [LinearOrder β] {g : K[X] → β}
    (hg : ∀ p q, PosAssoc p q → SignType.sign (g q) = SignType.sign (g p)) {l l' : List K[X]}
    (h : List.Forall₂ PosAssoc l l') : (l'.map g).signVariations = (l.map g).signVariations := by
  refine List.signVariations_congr ?_
  induction h with
  | nil => rfl
  | cons hpq _ ih => simp only [List.map_cons, hg _ _ hpq, ih]

variable [IsStrictOrderedRing K]

theorem PosAssoc.sign_eval {p q : K[X]} (h : PosAssoc p q) (x : K) :
    SignType.sign (q.eval x) = SignType.sign (p.eval x) := by
  obtain ⟨c, hc, rfl⟩ := h
  rw [eval_mul, eval_C, sign_mul, sign_pos hc, one_mul]

theorem PosAssoc.sign_leadingCoeff {p q : K[X]} (h : PosAssoc p q) :
    SignType.sign q.leadingCoeff = SignType.sign p.leadingCoeff := by
  obtain ⟨c, hc, rfl⟩ := h
  rw [leadingCoeff_mul, leadingCoeff_C, sign_mul, sign_pos hc, one_mul]

/-- Lists of polynomials that are entrywise positive multiples have the same sign variations at
every point. -/
theorem signVariations_map_eval_eq_of_forall₂ {l l' : List K[X]} (h : List.Forall₂ PosAssoc l l')
    (x : K) : (l'.map (eval x)).signVariations = (l.map (eval x)).signVariations :=
  signVariations_map_eq_of_forall₂ (fun _ _ hpq ↦ hpq.sign_eval x) h

/-- Lists of polynomials that are entrywise positive multiples have the same sign variations of
their leading coefficients, the count at `+∞`. -/
theorem signVariations_map_leadingCoeff_eq_of_forall₂ {l l' : List K[X]}
    (h : List.Forall₂ PosAssoc l l') :
    (l'.map leadingCoeff).signVariations = (l.map leadingCoeff).signVariations :=
  signVariations_map_eq_of_forall₂ (fun _ _ hpq ↦ hpq.sign_leadingCoeff) h

/-- Lists of polynomials that are entrywise positive multiples have the same sign variations of
their leading coefficients times `(-1) ^ deg`, the count at `-∞`. -/
theorem signVariations_map_neg_one_pow_mul_leadingCoeff_eq_of_forall₂ {l l' : List K[X]}
    (h : List.Forall₂ PosAssoc l l') :
    (l'.map fun p ↦ (-1) ^ p.natDegree * p.leadingCoeff).signVariations =
      (l.map fun p ↦ (-1) ^ p.natDegree * p.leadingCoeff).signVariations :=
  signVariations_map_eq_of_forall₂ (fun _ _ hpq ↦ by
    rw [sign_mul, sign_mul, hpq.natDegree_eq, hpq.sign_leadingCoeff]) h

end PosAssoc

section OrderTopology

variable {𝕜 : Type*} [NormedField 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [OrderTopology 𝕜]

/-- Far right, the sign variations of a list of nonzero polynomials at a point are those of their
leading coefficients. -/
theorem eventually_atTop_signVariations {ps : List 𝕜[X]} (h : ∀ p ∈ ps, p ≠ 0) :
    ∀ᶠ x in atTop, (ps.map (eval x)).signVariations = (ps.map leadingCoeff).signVariations := by
  have hall : ∀ᶠ x in atTop, ∀ p ∈ ps, SignType.sign (p.eval x) = SignType.sign p.leadingCoeff :=
    (eventually_all_finite ps.finite_toSet).mpr fun p hp ↦ eventually_atTop_sign_eval (h p hp)
  filter_upwards [hall] with x hx
  refine List.signVariations_congr ?_
  simpa only [List.map_map, Function.comp_def] using List.map_congr_left hx

/-- Far left, the sign variations of a list of nonzero polynomials at a point are those of their
leading coefficients, each times `(-1) ^ deg`. -/
theorem eventually_atBot_signVariations {ps : List 𝕜[X]} (h : ∀ p ∈ ps, p ≠ 0) :
    ∀ᶠ x in atBot, (ps.map (eval x)).signVariations =
      (ps.map fun p ↦ (-1) ^ p.natDegree * p.leadingCoeff).signVariations := by
  have hall : ∀ᶠ x in atBot, ∀ p ∈ ps, SignType.sign (p.eval x) =
      SignType.sign ((-1) ^ p.natDegree * p.leadingCoeff) :=
    (eventually_all_finite ps.finite_toSet).mpr fun p hp ↦ eventually_atBot_sign_eval (h p hp)
  filter_upwards [hall] with x hx
  refine List.signVariations_congr ?_
  simpa only [List.map_map, Function.comp_def] using List.map_congr_left hx

end OrderTopology

/-- The sign of the value of the image of a rational polynomial in an ordered field at a rational
point is the sign of the value of the polynomial. -/
theorem sign_eval_map_ratCastHom {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (p : ℚ[X]) (q : ℚ) :
    SignType.sign ((p.map (Rat.castHom K)).eval (q : K)) = SignType.sign (p.eval q) := by
  rw [eval_ratCast_map]
  simp only [sign_apply, Rat.coe_castHom, Rat.cast_id, Rat.cast_pos, Rat.cast_lt_zero]

end Polynomial

end
