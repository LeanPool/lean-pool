/-
Copyright (c) 2026 Yaoyu Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaoyu Zhao
-/

module

public import LeanPool.DeciSigma1.Arithmetic.ElementaryBounds
public import LeanPool.DeciSigma1.Holes.Tail.Levels
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Linarith.Frontend

/-! Ported to Lean Pool’s module system and pinned Lean and Mathlib.

 # Elementary bounds for the level recursion

A logarithmic envelope controls the suffix search and every field of the level state.

## Main declarations

- `suffixLengthBound_le_exp2`: a logarithmic bound for a constant chain budget.
- `stateEnvelope`, `levelStep_envelope`: a common envelope for the five state fields.
-/

@[expose] public section


namespace DeciSigma1.Holes.Tail

open Arithmetic

private theorem exp2_pos (t : ℕ) : 0 < exp2 t := by
  exact Nat.two_pow_pos t

private theorem exponent_pos {b t : ℕ} (hb : b + 2 ≤ exp2 t) : 1 ≤ t := by
  by_contra h
  have : t = 0 := by omega
  simp [this, exp2] at hb

private theorem base_log_bound (m N b t : ℕ) (hb : b + 2 ≤ exp2 t) :
    suffixLengthBound m N [] b + b + 2 ≤ exp2 (exp2 (m + N + 10) * t) := by
  have ht := exponent_pos hb
  let B := exp2 t
  have hB : 1 ≤ B := exp2_pos t
  have hm := succ_le_exp2 m
  have hN := le_exp2 N
  have hd : b * (b + 1) / 2 ≤ B * B :=
    (Nat.div_le_self _ _).trans (Nat.mul_le_mul (by omega) (by omega))
  have hnode : m * (b * (b + 1) / 2) + 1 ≤ (m + 1) * (B * B) := by
    have := Nat.mul_le_mul_left m hd
    nlinarith
  have hfactor : factorLengthBound m N b ≤ exp2 (3 * t + m + N) := by
    calc
      _ ≤ B * (exp2 N * (exp2 m * (B * B))) := by
        unfold factorLengthBound suffixNodeBound
        exact Nat.mul_le_mul (by omega)
          (Nat.mul_le_mul hN (hnode.trans (Nat.mul_le_mul_right _ hm)))
      _ = _ := by
        dsimp [B]
        rw [← exp2_add, ← exp2_add, ← exp2_add, ← exp2_add]
        congr 1; omega
  have hbig : B ≤ exp2 (3 * t + m + N) := exp2_mono (by omega)
  have he : suffixLengthBound m N [] b + b + 2 ≤
      exp2 (3 * t + m + N + 2) := by
    rw [exp2_add (3 * t + m + N) 2]
    have hsmall := hb.trans hbig
    change factorLengthBound m N b + 1 + b + 2 ≤ exp2 (3 * t + m + N) * 4
    omega
  apply he.trans (exp2_mono _)
  have hc : m + N + 5 ≤ exp2 (m + N + 10) :=
    (by omega : m + N + 5 ≤ m + N + 10).trans (le_exp2 _)
  have := Nat.mul_le_mul_right t hc
  nlinarith

private theorem iterate_log_bound (f : ℕ → ℕ) (C : ℕ)
    (hf : ∀ b t, b + 2 ≤ exp2 t → f b + b + 2 ≤ exp2 (C * t))
    (s b t : ℕ) (hb : b + 2 ≤ exp2 t) :
    (fun x => x + f x)^[s] b + 2 ≤ exp2 (C ^ s * t) := by
  induction s with
  | zero => simpa using hb
  | succ s ih =>
    rw [Function.iterate_succ_apply']
    have h := hf _ _ ih
    simpa only [pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm,
      Nat.add_comm] using h

/-- The suffix search has a logarithmic bound whose slope depends only on the number of
 targets and their common chain budget. -/
theorem suffixLengthBound_le_exp2 (m N S j b t : ℕ) (hb : b + 2 ≤ exp2 t) :
    suffixLengthBound m N (List.replicate j S) b + b + 2 ≤
      exp2 (exp2 ((m + N + 10) * (S + 3) ^ j) * t) := by
  induction j generalizing b t with
  | zero => simpa using base_log_bound m N b t hb
  | succ j ih =>
    let C := exp2 ((m + N + 10) * (S + 3) ^ j)
    let f := suffixLengthBound m N (List.replicate j S)
    let x := (fun x => x + f x)^[S] b
    have ht := exponent_pos hb
    have hC : 4 ≤ C := by
      have hp : 1 ≤ (S + 3) ^ j := Nat.one_le_pow _ _ (by omega)
      have : 2 ≤ (m + N + 10) * (S + 3) ^ j := by nlinarith
      exact exp2_mono this
    have hx : x + 2 ≤ exp2 (C ^ S * t) := iterate_log_bound f C ih S b t hb
    have hfx : f x + x + 2 ≤ exp2 (C ^ (S + 1) * t) := by
      have h := ih x _ hx
      change f x + x + 2 ≤ exp2 (C * (C ^ S * t)) at h
      simpa only [pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h
    have hy : (x + f x) + 2 ≤ exp2 (C ^ (S + 1) * t) := by omega
    have hfy : f (x + f x) + (x + f x) + 2 ≤ exp2 (C ^ (S + 2) * t) := by
      have h := ih (x + f x) _ hy
      change f (x + f x) + (x + f x) + 2 ≤ exp2 (C * (C ^ (S + 1) * t)) at h
      simpa only [show S + 2 = (S + 1) + 1 by omega, pow_succ,
        Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h
    have hbx : b ≤ x := le_iterate_of_le_self (fun a => Nat.le_add_right a (f a)) S b
    have hpow : C ^ (S + 1) * t ≤ C ^ (S + 2) * t := by
      apply Nat.mul_le_mul_right
      exact Nat.pow_le_pow_right (by omega) (by omega)
    have hfx' := hfx.trans (exp2_mono hpow)
    have hsum : suffixLengthBound m N (List.replicate (j + 1) S) b + b + 2 ≤
        exp2 (C ^ (S + 2) * t + 2) := by
      rw [List.replicate_succ, suffixLengthBound_cons, exp2_add]
      change 2 * f x + f (x + f x) + 2 + b + 2 ≤
        exp2 (C ^ (S + 2) * t) * 4
      omega
    have hp : 1 ≤ C ^ (S + 2) := Nat.one_le_pow _ _ (by omega)
    have hnext : C ^ (S + 2) * t + 2 ≤ C ^ (S + 3) * t := by
      rw [show S + 3 = (S + 2) + 1 by omega, pow_succ C (S + 2)]
      have hprod := Nat.mul_le_mul hp ht
      have hmul := Nat.mul_le_mul_left (C ^ (S + 2) * t) hC
      nlinarith only [hprod, hmul]
    apply hsum.trans ((exp2_mono hnext).trans _)
    apply exp2_mono
    dsimp [C]
    rw [← exp2_mul, pow_succ]
    exact le_of_eq (congrArg (fun z => exp2 z * t) (by ring))

/-- A common logarithmic envelope for the five fields of a level state. -/
def stateEnvelope (H : ℕ) (st : LevelState) : Prop :=
  st.periodBound ≤ exp2 H ∧ st.chainLengthBound ≤ exp2 H ∧
  st.previousChainLengthBound ≤ exp2 H ∧ st.terminalLengthBound ≤ exp2 H ∧
  st.uncoveredBound ≤ exp2 H

private theorem levelStep_polynomial (k N Q M : ℕ) (st : LevelState)
    (hM : 1 ≤ M) (hN : N ≤ M) (hQ : Q ≤ M) (hfac : N.factorial ≤ M)
    (hst : st.periodBound ≤ M ∧ st.chainLengthBound ≤ M ∧
      st.previousChainLengthBound ≤ M ∧ st.terminalLengthBound ≤ M ∧
      st.uncoveredBound ≤ M)
    (hTp : suffixLengthBound k N (List.replicate k (Q + N))
      (levelStartWindow N Q st) ≤ M) :
    (levelStep k N Q st).periodBound ≤ 64 * M ^ 3 ∧
    (levelStep k N Q st).chainLengthBound ≤ 64 * M ^ 3 ∧
    (levelStep k N Q st).previousChainLengthBound ≤ 64 * M ^ 3 ∧
    (levelStep k N Q st).terminalLengthBound ≤ 64 * M ^ 3 ∧
    (levelStep k N Q st).uncoveredBound ≤ 64 * M ^ 3 := by
  let Tp := suffixLengthBound k N (List.replicate k (Q + N)) (levelStartWindow N Q st)
  let e := max (factorLengthBound k N (suffixLengthEnvelope k N
    (List.replicate k (Q + N)) (levelStartWindow N Q st))) st.periodBound
  have he : e ≤ M := max_le
    ((Nat.le_of_lt (factorLengthBound_suffixLengthEnvelope_lt _ _ _ _)).trans hTp) hst.1
  have hchain : (levelStep k N Q st).chainLengthBound ≤
      (M + 2) * (1 + 2 * M) + (M + 2) * (3 * M + 3) +
        ((1 + (M + M) * (M * M)) + 2 * (M * M) + M * M +
          (M + 3) * (3 * M) + M + M) + M := by
    change (Q + 2) * (1 + 2 * e) + (Q + 2) * (3 * Tp + 3) +
      ((1 + (st.chainLengthBound + N) * (e * N.factorial)) +
        2 * (e * N.factorial) + N * e + (Q + 3) * (3 * e) +
        st.uncoveredBound + st.terminalLengthBound) + N ≤ _
    gcongr <;> first | exact hst.2.1 |
      exact hst.2.2.2.1 | exact hst.2.2.2.2
  have hpoly : (M + 2) * (1 + 2 * M) + (M + 2) * (3 * M + 3) +
        ((1 + (M + M) * (M * M)) + 2 * (M * M) + M * M +
          (M + 3) * (3 * M) + M + M) + M ≤ 64 * M ^ 3 := by
    have h1 : M ≤ M * M := by nlinarith
    have h2 : M * M ≤ M ^ 3 := by nlinarith
    nlinarith only [hM, h1, h2]
  have hbound := hchain.trans hpoly
  have hsmall : M ≤ 64 * M ^ 3 := by
    have := Nat.pow_le_pow_right hM (by decide : 1 ≤ 3)
    simp only [pow_one] at this
    omega
  refine ⟨he.trans hsmall, hbound, hst.2.1.trans hsmall, ?_, ?_⟩
  · exact (by dsimp [levelStep]; omega :
      (levelStep k N Q st).terminalLengthBound ≤ (levelStep k N Q st).chainLengthBound).trans
        hbound
  · exact (by dsimp [levelStep]; omega :
      (levelStep k N Q st).uncoveredBound ≤ (levelStep k N Q st).chainLengthBound).trans
        hbound

/-- One level multiplies the logarithmic envelope by a fixed coefficient. -/
theorem levelStep_envelope (k N Q H : ℕ) {st : LevelState}
    (hH : k + N + Q + N * N + 20 ≤ H) (hst : stateEnvelope H st) :
    stateEnvelope (exp2 ((k + N + 10) * (Q + N + 3) ^ k + 5) * H)
      (levelStep k N Q st) := by
  have hpos : 1 ≤ H := by omega
  have hN : N ≤ exp2 H := (by omega : N ≤ H).trans (le_exp2 H)
  have hQ : Q ≤ exp2 H := (by omega : Q ≤ H).trans (le_exp2 H)
  have hwindow : levelStartWindow N Q st + 2 ≤ exp2 (4 * H) := by
    have hN1 : N + 1 ≤ exp2 H := (by omega : N + 1 ≤ H).trans (le_exp2 H)
    have hQ2 : Q + 2 ≤ exp2 H := (by omega : Q + 2 ≤ H).trans (le_exp2 H)
    have hb : levelStartWindow N Q st + 2 ≤
        exp2 H * exp2 H + exp2 H * (exp2 H + 1) + 2 := by
      unfold levelStartWindow
      gcongr
      · exact hst.1
      · exact hst.2.2.1
    have hE : 2 ≤ exp2 H := exp2_mono hpos
    have hmul : exp2 H * exp2 H = exp2 (2 * H) := by
      rw [← exp2_add]; congr 1; omega
    have hlow : exp2 H ≤ exp2 (2 * H) := exp2_mono (by omega)
    have hb' : levelStartWindow N Q st + 2 ≤ exp2 (2 * H + 2) := by
      rw [exp2_add]
      change _ ≤ exp2 (2 * H) * 4
      nlinarith only [hb, hmul, hlow, hE]
    exact hb'.trans (exp2_mono (by omega))
  let C := exp2 ((k + N + 10) * (Q + N + 3) ^ k)
  let T := C * (4 * H)
  have hC : 1 ≤ C := exp2_pos _
  have hHT : H ≤ T := by dsimp [T]; nlinarith
  have hT : 2 ≤ T := by dsimp [T]; nlinarith
  have hm := exp2_mono hHT
  have hTp := suffixLengthBound_le_exp2 k N (Q + N) k _ _ hwindow
  have hp := levelStep_polynomial k N Q (exp2 T) st (exp2_pos _)
    (hN.trans hm) (hQ.trans hm)
    ((factorial_le_exp2_sq N).trans (exp2_mono (by omega)))
    ⟨hst.1.trans hm, hst.2.1.trans hm, hst.2.2.1.trans hm,
      hst.2.2.2.1.trans hm, hst.2.2.2.2.trans hm⟩
    (by exact (Nat.le_add_right _ _).trans ((Nat.le_add_right _ _).trans hTp))
  have hlast : 64 * exp2 T ^ 3 ≤
      exp2 (exp2 ((k + N + 10) * (Q + N + 3) ^ k + 5) * H) := by
    calc
      _ = exp2 (3 * T + 6) := by
        rw [← exp2_mul]
        change exp2 6 * exp2 (T * 3) = _
        rw [← exp2_add]; congr 1; omega
      _ ≤ _ := by
        apply exp2_mono
        rw [exp2_add]
        change 3 * T + 6 ≤ (C * 32) * H
        dsimp [T] at *
        nlinarith only [hT]
  exact ⟨hp.1.trans hlast, hp.2.1.trans hlast, hp.2.2.1.trans hlast,
    hp.2.2.2.1.trans hlast, hp.2.2.2.2.trans hlast⟩

/-- Every iterate of the level recursion satisfies the same logarithmic envelope. -/
theorem levelState_envelope (k N A l : ℕ)
    (hA : k + N + levelMultiplicity k N + N * N + 20 ≤ A) :
    stateEnvelope
      (exp2 (((k + N + 10) * (levelMultiplicity k N + N + 3) ^ k + 5) * l) * A)
      (levelState k N l) := by
  let V := (k + N + 10) * (levelMultiplicity k N + N + 3) ^ k + 5
  induction l with
  | zero =>
    simp only [Nat.mul_zero, exp2, pow_zero, one_mul, levelState,
      Function.iterate_zero_apply, initialLevelState, stateEnvelope]
    exact ⟨Nat.one_le_pow _ _ (by decide), Nat.zero_le _, Nat.zero_le _,
      Nat.zero_le _, Nat.zero_le _⟩
  | succ l ih =>
    have hlow : A ≤ exp2 (V * l) * A :=
      Nat.le_mul_of_pos_left A (exp2_pos _)
    have h := levelStep_envelope k N (levelMultiplicity k N) _ (hA.trans hlow) ih
    rw [levelState_succ]
    convert h using 1
    change exp2 (V * (l + 1)) * A = exp2 V * (exp2 (V * l) * A)
    rw [Nat.mul_add, Nat.mul_one, exp2_add]
    ring

end DeciSigma1.Holes.Tail
