/-
Copyright (c) 2026 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/

module

public import LeanPool.Zeta5Irrational.Growth.OuterPrime
public import LeanPool.Zeta5Irrational.Growth.TablePrime
import LeanPool.Zeta5Irrational.Growth.TableGen
import Mathlib.Data.Rat.BigOperators
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.FieldSimp -- shake: keep
import Mathlib.Tactic.FinCases -- shake: keep
import Mathlib.Tactic.Linarith -- shake: keep
import Mathlib.Tactic.LinearCombination -- shake: keep
import Mathlib.Tactic.Ring.Basic -- shake: keep

/-! # Rational certificates for the affine pieces

Between consecutive breakpoints, every minimum and maximum in the interval count selects
the same branch at both endpoints. The count therefore interpolates linearly. The certificate
checks these branch conditions and the two endpoint values over the rationals.
-/

@[expose] public section

namespace Zeta5Irrational.PieceCertificate

open Finset

/-- The endpoints of an affine function, with the branch checks used to obtain them. -/
structure Segment where
  /-- The value at the left endpoint. -/
  left : ℚ
  /-- The value at the right endpoint. -/
  right : ℚ
  /-- Whether every minimum and maximum used to build this segment passed its branch check. -/
  valid : Bool

namespace Segment

/-- The constant affine function. -/
def constantSegment (r : ℚ) : Segment := ⟨r, r, true⟩

/-- Subtraction preserves affine interpolation. -/
def sub (a b : Segment) : Segment :=
  ⟨a.left - b.left, a.right - b.right, a.valid && b.valid⟩

/-- Check that the same segment is below the other at both endpoints. -/
def ordered (a b : Segment) : Bool :=
  decide ((a.left ≤ b.left ∧ a.right ≤ b.right) ∨ (b.left ≤ a.left ∧ b.right ≤ a.right))

/-- Endpoint minimum, recording whether one affine branch suffices. -/
def lower (a b : Segment) : Segment :=
  ⟨min a.left b.left, min a.right b.right, a.valid && b.valid && a.ordered b⟩

/-- Endpoint maximum, recording whether one affine branch suffices. -/
def upper (a b : Segment) : Segment :=
  ⟨max a.left b.left, max a.right b.right, a.valid && b.valid && a.ordered b⟩

/-- Evaluate the affine function at the interpolation parameter. -/
noncomputable def eval (t : ℝ) (s : Segment) : ℝ :=
  (1 - t) * (s.left : ℝ) + t * (s.right : ℝ)

private lemma eval_const (t : ℝ) (r : ℚ) : (constantSegment r).eval t = (r : ℝ) := by
  unfold constantSegment eval
  ring1

private lemma eval_sub (t : ℝ) (a b : Segment) :
    (a.sub b).eval t = a.eval t - b.eval t := by
  simp only [sub, eval, Rat.cast_sub]
  ring1

private lemma eval_le {t : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) {a b : Segment}
    (hl : a.left ≤ b.left) (hr : a.right ≤ b.right) : a.eval t ≤ b.eval t :=
  add_le_add (mul_le_mul_of_nonneg_left (Rat.cast_le.mpr hl) (sub_nonneg.mpr ht₁))
    (mul_le_mul_of_nonneg_left (Rat.cast_le.mpr hr) ht₀)

private lemma eval_lower {t : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) {a b : Segment}
    (h : (a.lower b).valid = true) : (a.lower b).eval t = min (a.eval t) (b.eval t) := by
  have ho := (Bool.and_eq_true_iff.mp h).2
  have branches : (a.left ≤ b.left ∧ a.right ≤ b.right) ∨
      (b.left ≤ a.left ∧ b.right ≤ a.right) := of_decide_eq_true ho
  rcases branches with ⟨hl, hr⟩ | ⟨hl, hr⟩
  · rw [min_eq_left (eval_le ht₀ ht₁ hl hr)]
    simp only [lower, eval, min_eq_left hl, min_eq_left hr]
  · rw [min_eq_right (eval_le ht₀ ht₁ hl hr)]
    simp only [lower, eval, min_eq_right hl, min_eq_right hr]

private lemma eval_upper {t : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) {a b : Segment}
    (h : (a.upper b).valid = true) : (a.upper b).eval t = max (a.eval t) (b.eval t) := by
  have ho := (Bool.and_eq_true_iff.mp h).2
  have branches : (a.left ≤ b.left ∧ a.right ≤ b.right) ∨
      (b.left ≤ a.left ∧ b.right ≤ a.right) := of_decide_eq_true ho
  rcases branches with ⟨hl, hr⟩ | ⟨hl, hr⟩
  · rw [max_eq_right (eval_le ht₀ ht₁ hl hr)]
    simp only [upper, eval, max_eq_right hl, max_eq_right hr]
  · rw [max_eq_left (eval_le ht₀ ht₁ hl hr)]
    simp only [upper, eval, max_eq_left hl, max_eq_left hr]

private lemma sub_valid {a b : Segment} (h : (a.sub b).valid = true) :
    a.valid = true ∧ b.valid = true :=
  Bool.and_eq_true_iff.mp h

private lemma lower_valid {a b : Segment} (h : (a.lower b).valid = true) :
    a.valid = true ∧ b.valid = true :=
  Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp
    (show (a.valid && b.valid && a.ordered b) = true from h)).1

private lemma upper_valid {a b : Segment} (h : (a.upper b).valid = true) :
    a.valid = true ∧ b.valid = true :=
  Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp
    (show (a.valid && b.valid && a.ordered b) = true from h)).1

end Segment

/-- The continuous lower interval endpoint, evaluated on a segment. -/
def intervalLower (s : Segment) (i : Fin 3) : Segment :=
  ![.constantSegment 0, .constantSegment 0, (Segment.constantSegment 1).sub s] i

/-- The continuous upper interval endpoint, evaluated on a segment. -/
def intervalUpper (s : Segment) (i : Fin 3) : Segment :=
  ![.constantSegment (1 / 2), s, .constantSegment (1 / 2)] i

private lemma intervalLower_eval (s : Segment) (i : Fin 3) (t : ℝ) :
    (intervalLower s i).eval t = cvLo (s.eval t) i := by
  fin_cases i <;>
    simp [intervalLower, cvLo, Segment.eval_const, Segment.eval_sub]

private lemma intervalUpper_eval (s : Segment) (i : Fin 3) (t : ℝ) :
    (intervalUpper s i).eval t = cvHi (s.eval t) i := by
  fin_cases i <;> simp [intervalUpper, cvHi, Segment.eval_const]

/-- The continuous count with each minimum and maximum checked at both endpoints. -/
def count (f g : Segment) (i j : Fin 3) : Segment :=
  let hi := ((intervalUpper f i).lower (intervalUpper g j)).lower (.constantSegment (1 / 2))
  let lo := ((intervalLower f i).upper (intervalLower g j)).upper (.constantSegment 0)
  (Segment.constantSegment 0).upper (hi.sub lo)

private lemma count_eval {t : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) {f g : Segment} {i j : Fin 3}
    (h : (count f g i j).valid = true) :
    (count f g i j).eval t = ccount (f.eval t) (g.eval t) i j := by
  let hi := (intervalUpper f i).lower (intervalUpper g j)
  let lo := (intervalLower f i).upper (intervalLower g j)
  have hd :
      ((hi.lower (.constantSegment (1 / 2))).sub (lo.upper (.constantSegment 0))).valid = true :=
    (Segment.upper_valid (a := .constantSegment 0) h).2
  obtain ⟨hhi, hlo⟩ := Segment.sub_valid hd
  have hhi' := (Segment.lower_valid hhi).1
  have hlo' := (Segment.upper_valid hlo).1
  rw [count, Segment.eval_upper ht₀ ht₁ h, Segment.eval_sub,
    Segment.eval_lower ht₀ ht₁ hhi, Segment.eval_lower ht₀ ht₁ hhi',
    Segment.eval_upper ht₀ ht₁ hlo, Segment.eval_upper ht₀ ht₁ hlo']
  simp [ccount, intervalUpper_eval, intervalLower_eval, Segment.eval_const]

/-- Rational version of `bcoef`, for computing endpoint values. -/
def rationalBasis (h : ℕ → ℚ) (i : Fin 3) : ℚ :=
  ![h 0, h 1 - h 0, h 2 - h 1] i

private lemma cast_rationalBasis (h : ℕ → ℚ) (i : Fin 3) :
    (rationalBasis h i : ℝ) = bcoef (fun a ↦ (h a : ℝ)) i := by
  fin_cases i <;> simp [rationalBasis, bcoef]

/-- The rational coefficient computed using the closed form for `psiR`. -/
def rationalCoefficient (q q' : ℕ) (k : ℤ) (i j : Fin 3) : ℚ :=
  rationalBasis (fun a ↦ rationalBasis (fun b ↦
    let β : ℤ := 12 * (q' : ℤ) - 2 * (q : ℤ) - 4 + 6 * (b : ℤ) - a
    let rows : ℚ := lrow k β
    rows * (((k - β : ℤ) : ℚ) - rows + 1) / 2) j) i

private lemma cast_rationalCoefficient (q q' : ℕ) (k : ℤ) (i j : Fin 3) :
    (rationalCoefficient q q' k i j : ℝ) = bIn q q' k i j := by
  delta bIn
  simp only [rationalCoefficient, cast_rationalBasis, psiR_eq]

/-- The possible affine fractional parts at the ends of a piece. -/
def fractions (a b : ℚ) (q q' : ℕ) : Segment × Segment :=
  (⟨a - q, b - q, true⟩, ⟨3 / 40 * a - q', 3 / 40 * b - q', true⟩)

/-- Evaluate the weighted count at one endpoint. -/
def endpointSum (weight : Fin 3 → Fin 3 → ℚ) (select : Segment → ℚ) (f g : Segment) : ℚ :=
  ∑ i, ∑ j, weight i j * select (count f g i j)

private lemma cast_endpointSum (weight : Fin 3 → Fin 3 → ℚ)
    (select : Segment → ℚ) (f g : Segment) :
    (endpointSum weight select f g : ℝ) =
      ∑ i, ∑ j, (weight i j : ℝ) * (select (count f g i j) : ℝ) := by
  simp only [endpointSum, Rat.cast_sum, Rat.cast_mul]

private lemma weighted_count_eval {t : ℝ} (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1)
    {f g : Segment} (h : ∀ i j : Fin 3, (count f g i j).valid = true)
    (weight : Fin 3 → Fin 3 → ℝ) :
    (∑ i, ∑ j, weight i j * ccount (f.eval t) (g.eval t) i j) =
      (1 - t) * (∑ i, ∑ j, weight i j * ((count f g i j).left : ℝ)) +
        t * (∑ i, ∑ j, weight i j * ((count f g i j).right : ℝ)) := by
  simp only [mul_sum, ← sum_add_distrib]
  refine sum_congr rfl fun i _ ↦ sum_congr rfl fun j _ ↦ ?_
  rw [← count_eval ht₀ ht₁ (h i j)]
  unfold Segment.eval
  ring1

/-- The rational value of the expanded inner function at one endpoint. -/
def endpointValue (x : ℚ) (q q' μ : ℕ) (k : ℤ) (select : Segment → ℚ) (f g : Segment) : ℚ :=
  -2 * (37 / 40 * x) * q + 12 * (37 / 40 * x) * q' +
      (2 * μ * (37 / 40 * x) - (μ : ℚ) * (μ + 1) / 2) - 37 / 40 * x * k +
    2 * endpointSum (rationalCoefficient q q' k) select f g

/-- Bounds for a floor that is constant on the half-open segment.
The upper bound may hold with equality at the right endpoint. -/
abbrev floorBounds (left right : ℚ) (n : ℕ) : Prop :=
  (n : ℚ) ≤ left ∧ (n : ℚ) ≤ right ∧ left < (n : ℚ) + 1 ∧ right ≤ (n : ℚ) + 1

private lemma floorBounds_eval {left right : ℚ} {n : ℕ} {t : ℝ}
    (h : floorBounds left right n) (ht₀ : 0 ≤ t) (ht₁ : t < 1) :
    (n : ℝ) ≤ (⟨left, right, true⟩ : Segment).eval t ∧
      (⟨left, right, true⟩ : Segment).eval t < (n : ℝ) + 1 := by
  obtain ⟨hl, hr, hl', hr'⟩ := h
  have hleft : (n : ℝ) ≤ (left : ℝ) := by exact_mod_cast hl
  have hright : (n : ℝ) ≤ (right : ℝ) := by exact_mod_cast hr
  have hleft' : (left : ℝ) < (n : ℝ) + 1 := by exact_mod_cast hl'
  have hright' : (right : ℝ) ≤ (n : ℝ) + 1 := by exact_mod_cast hr'
  unfold Segment.eval
  constructor
  · have h₁ := mul_le_mul_of_nonneg_left hleft (sub_nonneg.mpr ht₁.le)
    have h₂ := mul_le_mul_of_nonneg_left hright ht₀
    linarith only [h₁, h₂]
  · have h₁ := mul_lt_mul_of_pos_left hleft' (sub_pos.mpr ht₁)
    have h₂ := mul_le_mul_of_nonneg_left hright' ht₀
    linarith only [h₁, h₂]

/-- Endpoint checks for the three floors in the piece formulas. -/
abbrev Floors (a b : ℚ) (q q' μ : ℕ) : Prop :=
  floorBounds a b q ∧ floorBounds (3 / 40 * a) (3 / 40 * b) q' ∧
  floorBounds (2 * (37 / 40 * a)) (2 * (37 / 40 * b)) μ ∧ b ≤ 400

/-- The endpoint checks for one half-open interval. -/
abbrev Valid (a b slope offset : ℚ) (q q' μ : ℕ) (k : ℤ) : Prop :=
  let (f, g) := fractions a b q q'
  Floors a b q q' μ ∧
  (∀ i j : Fin 3, (count f g i j).valid = true) ∧
  endpointValue a q q' μ k Segment.left f g = slope * a + offset ∧
  endpointValue b q q' μ k Segment.right f g = slope * b + offset

private lemma mix_endpoints {a b : ℚ} {x : ℝ} (ha : (a : ℝ) ≤ x) (hb : x < (b : ℝ)) :
    ∃ t : ℝ, 0 ≤ t ∧ t < 1 ∧ (⟨a, b, true⟩ : Segment).eval t = x := by
  have width : 0 < (b : ℝ) - (a : ℝ) := sub_pos.mpr (ha.trans_lt hb)
  let t := (x - a) / ((b : ℝ) - a)
  refine ⟨t, div_nonneg (sub_nonneg.mpr ha) width.le, (div_lt_one width).mpr ?_, ?_⟩
  · exact sub_lt_sub_right hb _
  · unfold Segment.eval t
    field_simp [ne_of_gt width]
    ring1

private lemma scaled_eval {a b c : ℚ} {x t : ℝ}
    (hx : (⟨a, b, true⟩ : Segment).eval t = x) :
    (⟨c * a, c * b, true⟩ : Segment).eval t = (c : ℝ) * x := by
  rw [← hx]
  simp only [Segment.eval, Rat.cast_mul]
  ring1

private lemma fractions_eval {a b : ℚ} {q q' : ℕ} {x t : ℝ}
    (hx : (⟨a, b, true⟩ : Segment).eval t = x) :
    (fractions a b q q').1.eval t = x - q ∧
      (fractions a b q q').2.eval t = 3 / 40 * x - q' := by
  rw [← hx]
  simp only [fractions, Segment.eval, Rat.cast_sub, Rat.cast_mul, Rat.cast_div,
    Rat.cast_ofNat, Rat.cast_natCast]
  constructor <;> ring1

private lemma floors_eval {a b : ℚ} {q q' μ : ℕ} {x t : ℝ}
    (h : Floors a b q q' μ) (ht₀ : 0 ≤ t) (ht₁ : t < 1)
    (hx : (⟨a, b, true⟩ : Segment).eval t = x) (hb : x < (b : ℝ)) :
    ((q : ℝ) ≤ x ∧ x < q + 1) ∧
      ((q' : ℝ) ≤ 3 / 40 * x ∧ 3 / 40 * x < q' + 1) ∧
      ((μ : ℝ) ≤ 2 * (37 / 40 * x) ∧ 2 * (37 / 40 * x) < μ + 1) ∧ x ≤ 400 := by
  obtain ⟨hq, hq', hμ, bound⟩ := h
  have evalRatio :
      (⟨3 / 40 * a, 3 / 40 * b, true⟩ : Segment).eval t = 3 / 40 * x := by
    simpa only [Rat.cast_div, Rat.cast_ofNat] using scaled_eval (c := 3 / 40) hx
  have evalTwice :
      (⟨2 * (37 / 40 * a), 2 * (37 / 40 * b), true⟩ : Segment).eval t =
        2 * (37 / 40 * x) := by
    simpa only [mul_assoc, Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat] using
      scaled_eval (c := 2 * (37 / 40)) hx
  have bound' : (b : ℝ) ≤ 400 := by exact_mod_cast bound
  exact ⟨hx ▸ floorBounds_eval hq ht₀ ht₁, evalRatio ▸ floorBounds_eval hq' ht₀ ht₁,
    evalTwice ▸ floorBounds_eval hμ ht₀ ht₁, hb.le.trans bound'⟩

/-- A rational certificate gives the exact affine formula throughout the piece. -/
theorem innerPiece {a b slope offset : ℚ} {q q' μ : ℕ} {k : ℤ}
    (h : Valid a b slope offset q q' μ k) {x : ℝ}
    (ha : (a : ℝ) ≤ x) (hb : x < (b : ℝ)) :
    Ein x k = (slope : ℝ) * x + (offset : ℝ) := by
  obtain ⟨t, ht₀, ht₁, hx⟩ := mix_endpoints ha hb
  obtain ⟨hfloor, hcounts, hleft, hright⟩ := h
  obtain ⟨hq, hq', hμ, hx400⟩ := floors_eval hfloor ht₀ ht₁ hx hb
  obtain ⟨hf, hg⟩ := fractions_eval (q := q) (q' := q') hx
  rw [Ein_expand k hq.1 hq.2 hq'.1 hq'.2 hμ.1 hμ.2 hx400, ← hf, ← hg,
    weighted_count_eval ht₀ ht₁.le (f := (fractions a b q q').1)
      (g := (fractions a b q q').2) hcounts (bIn q q' k)]
  have hl := congrArg (fun y : ℚ ↦ (y : ℝ)) hleft
  have hr := congrArg (fun y : ℚ ↦ (y : ℝ)) hright
  simp only [endpointValue, Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_div,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_natCast, Rat.cast_intCast, cast_endpointSum,
    cast_rationalCoefficient] at hl hr
  rw [← hx]
  simp only [Segment.eval, fractions]
  linear_combination (1 - t) * hl + t * hr

/-- Rational coefficients for the outer class counts. -/
noncomputable def outerCoefficient (q : ℕ) (i j : Fin 3) : ℚ :=
  rationalBasis (fun a ↦ rationalBasis (GO q a) j) i

private lemma cast_outerCoefficient (q : ℕ) (i j : Fin 3) :
    (outerCoefficient q i j : ℝ) = bGO q i j := by
  delta bGO
  simp only [outerCoefficient, cast_rationalBasis]

/-- The affine segment inside the last maximum of the outer formula. -/
def outerCorrection (a b : ℚ) : Segment :=
  (Segment.constantSegment 0).upper ⟨13 / 10 * a - 2, 13 / 10 * b - 2, true⟩

private lemma outerCorrection_eval {a b : ℚ} {x t : ℝ}
    (hx : (⟨a, b, true⟩ : Segment).eval t = x) (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1)
    (h : (outerCorrection a b).valid = true) :
    (outerCorrection a b).eval t = max 0 (13 / 10 * x - 2) := by
  unfold outerCorrection
  rw [Segment.eval_upper ht₀ ht₁ h, Segment.eval_const, Rat.cast_zero]
  congr 1
  rw [← hx]
  simp only [Segment.eval, Rat.cast_sub, Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat]
  ring1

/-- The rational value of the expanded outer function at one endpoint. -/
noncomputable def outerEndpointValue (x : ℚ) (q μ : ℕ)
    (select : Segment → ℚ) (f g correction : Segment) : ℚ :=
  -2 * (37 / 40 * x) * q + (2 * μ * (37 / 40 * x) - (μ : ℚ) * (μ + 1) / 2) -
    2 * endpointSum (outerCoefficient q) select f g + select correction

/-- The endpoint checks for a piece in the outer range. -/
abbrev OuterValid (a b slope offset : ℚ) (q q' μ : ℕ) : Prop :=
  let (f, g) := fractions a b q q'
  let correction := outerCorrection a b
  Floors a b q q' μ ∧ (∀ i j : Fin 3, (count f g i j).valid = true) ∧
    correction.valid = true ∧
    outerEndpointValue a q μ Segment.left f g correction = slope * a + offset ∧
    outerEndpointValue b q μ Segment.right f g correction = slope * b + offset

/-- A rational certificate gives the affine formula throughout an outer piece. -/
theorem outerPiece {a b slope offset : ℚ} {q q' μ : ℕ}
    (h : OuterValid a b slope offset q q' μ) {x : ℝ}
    (ha : (a : ℝ) ≤ x) (hb : x < (b : ℝ)) :
    Eout x = (slope : ℝ) * x + (offset : ℝ) := by
  obtain ⟨t, ht₀, ht₁, hx⟩ := mix_endpoints ha hb
  obtain ⟨hfloor, hcounts, hcorrection, hleft, hright⟩ := h
  obtain ⟨hq, hq', hμ, hx400⟩ := floors_eval hfloor ht₀ ht₁ hx hb
  obtain ⟨hf, hg⟩ := fractions_eval (q := q) (q' := q') hx
  rw [Eout_expand hq.1 hq.2 hq'.1 hq'.2 hμ.1 hμ.2 hx400, ← hf, ← hg,
    weighted_count_eval ht₀ ht₁.le (f := (fractions a b q q').1)
      (g := (fractions a b q q').2) hcounts (bGO q),
    ← outerCorrection_eval hx ht₀ ht₁.le hcorrection]
  have hl := congrArg (fun y : ℚ ↦ (y : ℝ)) hleft
  have hr := congrArg (fun y : ℚ ↦ (y : ℝ)) hright
  simp only [outerEndpointValue, Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_div,
    Rat.cast_neg, Rat.cast_ofNat, Rat.cast_natCast, cast_endpointSum,
    cast_outerCoefficient] at hl hr
  rw [← hx]
  simp only [Segment.eval, fractions]
  linear_combination (1 - t) * hl + t * hr

end Zeta5Irrational.PieceCertificate
