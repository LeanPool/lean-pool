/-
Copyright (c) 2026 Adam McKenna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam McKenna
-/
module

public import LeanPool.DistinctDistances.FarkasPackedCheck
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum

/-!
# Rational rows and their sound integer scaling

Rational linear inequalities are scaled by a common denominator before the packed
Farkas checker consumes them. Successful conversion preserves every satisfied row.
-/

@[expose] public section

namespace Esgk.S4

open Esgk.FarkasPackedCheck

/-! ### Rational rows -/

/-- A rational row `∑_{(k, q) ∈ ent} q * v k ≤ rhs`. -/
structure QRow where
  /-- the entries `(variable, coefficient)`; an index may repeat -/
  ent : List (Nat × ℚ)
  /-- the right-hand side -/
  rhs : ℚ

/-- The left-hand side of a rational row at `v`. -/
noncomputable def QRow.lhs (r : QRow) (v : Nat → ℝ) : ℝ :=
  (r.ent.map fun e ↦ (e.2 : ℝ) * v e.1).sum

/-- The point `v` satisfies the rational row `r`. -/
def QRow.Holds (r : QRow) (v : Nat → ℝ) : Prop := r.lhs v ≤ r.rhs

/-! ### Scaling a rational row to an integer row -/

/-- The lcm of the denominators of the entries and of the right-hand side. -/
noncomputable def QRow.den (r : QRow) : Nat :=
  List.rec (motive := fun _ ↦ Nat) r.rhs.den (fun (e : Nat × ℚ) _ ih ↦ Nat.lcm e.2.den ih) r.ent

/-- Every entry times `L` is an integer. -/
noncomputable def allInt (L : Nat) (E : List (Nat × ℚ)) : Bool :=
  List.rec (motive := fun _ ↦ Bool) true
    (fun (e : Nat × ℚ) _ ih ↦ Nat.beq ((e.2 : ℚ) * (L : ℚ)).den 1 && ih) E

/-- The positive entries times `L`. -/
noncomputable def posPart (L : Nat) (E : List (Nat × ℚ)) : List (Nat × Nat) :=
  List.rec (motive := fun _ ↦ List (Nat × Nat)) []
    (fun (e : Nat × ℚ) _ ih ↦
      bif decide (0 < e.2) then (e.1, ((e.2 : ℚ) * (L : ℚ)).num.toNat) :: ih else ih) E

/-- The negative entries times `-L`. -/
noncomputable def negPart (L : Nat) (E : List (Nat × ℚ)) : List (Nat × Nat) :=
  List.rec (motive := fun _ ↦ List (Nat × Nat)) []
    (fun (e : Nat × ℚ) _ ih ↦
      bif decide (e.2 < 0) then (e.1, (-((e.2 : ℚ) * (L : ℚ))).num.toNat) :: ih else ih) E

/-- The exact integer coefficient when the given denominator clears the rational. -/
def QRow.scaleNumerator (denominator : Nat) (value : ℚ) : Int :=
  value.num * ((denominator / value.den : Nat) : Int)

/-- Collect selected integer coefficients in the original row order. -/
noncomputable def QRow.signedEntries (keep : ℚ → Bool) (numerator : ℚ → Int)
    (entries : List (Nat × ℚ)) : List (Nat × Nat) :=
  List.rec (motive := fun _ ↦ List (Nat × Nat)) []
    (fun (entry : Nat × ℚ) _ rest ↦
      bif keep entry.2 then (entry.1, (numerator entry.2).toNat) :: rest else rest) entries

/-- Scale the row by its common denominator to obtain integer coefficients. -/
noncomputable def QRow.toRow (r : QRow) : Option Row :=
  let denominator := r.den
  let positive := QRow.signedEntries (fun value ↦ decide (0 < value))
    (QRow.scaleNumerator denominator) r.ent
  let negative := QRow.signedEntries (fun value ↦ decide (value < 0))
    (fun value ↦ -QRow.scaleNumerator denominator value) r.ent
  some ⟨positive, negative, QRow.scaleNumerator denominator r.rhs⟩

private theorem allInt_cons (L : Nat) (e : Nat × ℚ) (E : List (Nat × ℚ)) :
    allInt L (e :: E) = (Nat.beq (e.2 * L).den 1 && allInt L E) := rfl

private theorem posPart_cons (L : Nat) (e : Nat × ℚ) (E : List (Nat × ℚ)) :
    posPart L (e :: E) =
      bif decide (0 < e.2) then (e.1, (e.2 * L).num.toNat) :: posPart L E else posPart L E :=
  rfl

private theorem negPart_cons (L : Nat) (e : Nat × ℚ) (E : List (Nat × ℚ)) :
    negPart L (e :: E) =
      bif decide (e.2 < 0) then (e.1, (-(e.2 * L)).num.toNat) :: negPart L E
      else negPart L E :=
  rfl

private theorem entrySum_cons (x : Nat × Nat) (E : List (Nat × Nat)) (v : Nat → ℝ) :
    entrySum (x :: E) v = (x.2 : ℝ) * v x.1 + entrySum E v := by
  simp [entrySum]

private theorem intCast_num_of_den_eq_one {q : ℚ} (hd : q.den = 1) :
    ((q.num : ℤ) : ℝ) = (q : ℝ) := by
  rw [← Rat.cast_intCast, (Rat.den_eq_one_iff q).1 hd]

private theorem natCast_toNat_num {q : ℚ} (hd : q.den = 1) (h0 : 0 ≤ q) :
    ((q.num.toNat : ℕ) : ℝ) = (q : ℝ) := by
  rw [← Int.cast_natCast, Int.toNat_of_nonneg (Rat.num_nonneg.2 h0),
    intCast_num_of_den_eq_one hd]

private theorem entrySum_pos_sub_neg (L : Nat) (v : Nat → ℝ) :
    ∀ E : List (Nat × ℚ), allInt L E = true →
      entrySum (posPart L E) v - entrySum (negPart L E) v =
        (L : ℝ) * (E.map fun e ↦ (e.2 : ℝ) * v e.1).sum
  | [], _ => by simp [entrySum, posPart, negPart]
  | e :: E, h => by
    rw [allInt_cons, Bool.and_eq_true] at h
    have ih := entrySum_pos_sub_neg L v E h.2
    have hden : (e.2 * L).den = 1 := Nat.eq_of_beq_eq_true h.1
    rw [posPart_cons, negPart_cons, List.map_cons, List.sum_cons]
    have hL : (0 : ℚ) ≤ L := Nat.cast_nonneg L
    rcases lt_trichotomy e.2 0 with hneg | hzero | hpos
    · rw [decide_eq_false (show ¬ (0 < e.2) by linarith), decide_eq_true hneg, Bool.cond_false,
        Bool.cond_true, entrySum_cons]
      have hc := natCast_toNat_num (q := -(e.2 * L)) (by rw [Rat.neg_den]; exact hden)
        (neg_nonneg.2 (mul_nonpos_of_nonpos_of_nonneg hneg.le hL))
      push_cast at hc
      rw [hc]
      linear_combination ih
    · simp only [hzero, lt_irrefl, decide_false, Bool.cond_false, Rat.cast_zero, zero_mul, zero_add]
      exact ih
    · rw [decide_eq_true hpos, decide_eq_false (show ¬ (e.2 < 0) by linarith), Bool.cond_true,
        Bool.cond_false, entrySum_cons]
      have hc := natCast_toNat_num hden (mul_nonneg hpos.le hL)
      push_cast at hc
      rw [hc]
      linear_combination ih

private theorem commonDenominatorSpec (entries : List (Nat × ℚ)) (rhs : ℚ) :
    0 < (QRow.mk entries rhs).den ∧ rhs.den ∣ (QRow.mk entries rhs).den ∧
      ∀ e ∈ entries, e.2.den ∣ (QRow.mk entries rhs).den := by
  induction entries with
  | nil => exact ⟨rhs.den_pos, dvd_refl _, by simp⟩
  | cons entry entries ih =>
    let tailDen := (QRow.mk entries rhs).den
    change 0 < Nat.lcm entry.2.den tailDen ∧ rhs.den ∣ Nat.lcm entry.2.den tailDen ∧
      ∀ e ∈ entry :: entries, e.2.den ∣ Nat.lcm entry.2.den tailDen
    refine ⟨Nat.lcm_pos entry.2.den_pos ih.1, ih.2.1.trans (Nat.dvd_lcm_right _ _), ?_⟩
    intro e he
    rcases List.mem_cons.1 he with rfl | he
    · exact Nat.dvd_lcm_left _ _
    · exact (ih.2.2 e he).trans (Nat.dvd_lcm_right _ _)

private theorem scaleNumerator_cast {value : ℚ} {denominator : Nat}
    (divides : value.den ∣ denominator) :
    value * (denominator : ℚ) = (QRow.scaleNumerator denominator value : ℚ) := by
  have scale : value * (value.den : ℚ) = (value.num : ℚ) := calc
    value * (value.den : ℚ) = ((value.num : ℚ) / value.den) * value.den :=
      congrArg (fun x : ℚ ↦ x * (value.den : ℚ)) value.num_div_den.symm
    _ = (value.num : ℚ) := div_mul_cancel₀ _ (by exact_mod_cast value.den_ne_zero)
  have factor : (denominator : ℚ) =
      (value.den : ℚ) * ((denominator / value.den : Nat) : ℚ) := by
    exact_mod_cast (Nat.mul_div_cancel' divides).symm
  rw [factor, ← mul_assoc, scale, QRow.scaleNumerator, Int.cast_mul, Int.cast_natCast]

private theorem scaleNumerator_eq {value : ℚ} {denominator : Nat}
    (divides : value.den ∣ denominator) :
    QRow.scaleNumerator denominator value = (value * denominator).num := by
  simpa only [Rat.num_intCast] using (congrArg Rat.num (scaleNumerator_cast divides)).symm

private theorem signedEntries_congr (keep : ℚ → Bool) (a b : ℚ → Int)
    (entries : List (Nat × ℚ)) (h : ∀ e ∈ entries, a e.2 = b e.2) :
    QRow.signedEntries keep a entries = QRow.signedEntries keep b entries := by
  induction entries with
  | nil => rfl
  | cons entry entries ih =>
    change (bif keep entry.2 then (entry.1, (a entry.2).toNat) :: QRow.signedEntries keep a entries
      else QRow.signedEntries keep a entries) =
      (bif keep entry.2 then (entry.1, (b entry.2).toNat) :: QRow.signedEntries keep b entries
        else QRow.signedEntries keep b entries)
    rw [h entry (by simp), ih (fun e he ↦ h e (List.mem_cons_of_mem _ he))]

private theorem positiveEntries_eq (denominator : Nat) (entries : List (Nat × ℚ))
    (h : ∀ e ∈ entries, e.2.den ∣ denominator) :
    QRow.signedEntries (fun value ↦ decide (0 < value)) (QRow.scaleNumerator denominator) entries =
      posPart denominator entries := by
  exact signedEntries_congr _ _ (fun value ↦ (value * denominator).num) _
    (fun e he ↦ scaleNumerator_eq (h e he))

private theorem negativeEntries_eq (denominator : Nat) (entries : List (Nat × ℚ))
    (h : ∀ e ∈ entries, e.2.den ∣ denominator) :
    QRow.signedEntries (fun value ↦ decide (value < 0))
      (fun value ↦ -QRow.scaleNumerator denominator value) entries =
      negPart denominator entries := by
  refine signedEntries_congr _ _ (fun value ↦ (-(value * denominator)).num) _ ?_
  intro e he
  rw [Rat.neg_num, scaleNumerator_eq (h e he)]

private theorem mul_nat_den_eq_one {q : ℚ} {L : Nat} (h : q.den ∣ L) : (q * L).den = 1 := by
  simpa only [Rat.den_intCast] using congrArg Rat.den (scaleNumerator_cast h)

private theorem allInt_of_commonDenominator (L : Nat) (entries : List (Nat × ℚ))
    (h : ∀ e ∈ entries, e.2.den ∣ L) : allInt L entries = true := by
  induction entries with
  | nil => rfl
  | cons entry entries ih =>
    rw [allInt_cons, mul_nat_den_eq_one (h entry (by simp))]
    exact ih fun e he ↦ h e (List.mem_cons_of_mem _ he)

/-- Soundness of the scaling: the integer row holds wherever the rational row holds. -/
theorem QRow.toRow_sound {r : QRow} {R : Row} {v : Nat → ℝ} (h : r.toRow = some R)
    (hr : r.Holds v) : R.Holds v := by
  obtain ⟨positive, rhsDvd, entriesDvd⟩ := commonDenominatorSpec r.ent r.rhs
  have entriesIntegral := allInt_of_commonDenominator r.den r.ent entriesDvd
  have rhsIntegral := mul_nat_den_eq_one rhsDvd
  have scaling : r.toRow = some
      ⟨posPart r.den r.ent, negPart r.den r.ent, (r.rhs * r.den).num⟩ := by
    simp only [QRow.toRow, positiveEntries_eq _ _ entriesDvd, negativeEntries_eq _ _ entriesDvd,
      scaleNumerator_eq rhsDvd]
  rw [scaling] at h
  injection h with h
  subst h
  have denominatorPositive : (0 : ℝ) < r.den := by exact_mod_cast positive
  unfold Row.Holds Row.lhs
  rw [entrySum_pos_sub_neg _ _ _ entriesIntegral, intCast_num_of_den_eq_one rhsIntegral]
  push_cast
  unfold QRow.Holds QRow.lhs at hr
  have := mul_le_mul_of_nonneg_left hr denominatorPositive.le
  linarith

end Esgk.S4
