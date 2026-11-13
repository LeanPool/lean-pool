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

/-- The integer row `L * r` for the common denominator `L` of `r`, or `none` if the scaling
fails (it does not fail, but the checker does not need that). -/
noncomputable def QRow.toRow (r : QRow) : Option Row :=
  bif Nat.blt 0 r.den && allInt r.den r.ent && Nat.beq (r.rhs * r.den).den 1 then
    some ⟨posPart r.den r.ent, negPart r.den r.ent, (r.rhs * r.den).num⟩
  else none


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

/-- Soundness of the scaling: the integer row holds wherever the rational row holds. -/
theorem QRow.toRow_sound {r : QRow} {R : Row} {v : Nat → ℝ} (h : r.toRow = some R)
    (hr : r.Holds v) : R.Holds v := by
  unfold QRow.toRow at h
  cases hc : (Nat.blt 0 r.den && allInt r.den r.ent && Nat.beq (r.rhs * r.den).den 1) with
  | false => rw [hc, Bool.cond_false] at h; exact absurd h (by simp)
  | true =>
    rw [hc, Bool.cond_true] at h
    simp only [Bool.and_eq_true] at hc
    obtain ⟨⟨hL, hint⟩, hrhs⟩ := hc
    injection h with h
    subst h
    have hL' : (0 : ℝ) < r.den := by exact_mod_cast (by simpa [Nat.blt_eq] using hL : 0 < r.den)
    unfold Row.Holds Row.lhs
    rw [entrySum_pos_sub_neg _ _ _ hint, intCast_num_of_den_eq_one (Nat.eq_of_beq_eq_true hrhs)]
    push_cast
    unfold QRow.Holds QRow.lhs at hr
    have := mul_le_mul_of_nonneg_left hr hL'.le
    linarith

end Esgk.S4
