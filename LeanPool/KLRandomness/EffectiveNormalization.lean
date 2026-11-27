/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

-- Modified for Lean Pool.

module

public import LeanPool.KLRandomness.ComputableRational
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Effective rational capital with a positive reserve

A computable real capital process is replaced by a computable rational one
whose value stays within `1/4` of `(d + 1) / 2` on every finite transcript.
The replacement approximates additive stakes at a summable error rate.  It is
fair, starts at one, stays above `1/4`, and preserves unbounded capital.

This supplies the effective reserve and rationalization step needed before
applying the pathwise normalization estimates in Lemma 2.
-/

@[expose] public section

namespace Klr

open RationalComputability

private theorem foldl_take_succ {α β : Type*} (f : α → β → α) (s : α)
    (v : List β) (n : ℕ) :
    (v.take (n + 1)).foldl f s =
      match v[n]? with
      | none => (v.take n).foldl f s
      | some b => f ((v.take n).foldl f s) b := by
  induction v generalizing n s with
  | nil => simp
  | cons b v ih =>
    cases n with
    | zero => simp
    | succ n => simpa using ih (f s b) n

/-- Total computability is closed under folding a finite list, even when the
step function is computable rather than primitive recursive. -/
theorem computable_list_foldl {α β : Type*} [Primcodable α] [Primcodable β]
    (f : α → β → α) (hf : Computable₂ f) (s : α) :
    Computable (fun v : List β => v.foldl f s) := by
  let step (v : List β) (p : ℕ × α) :=
    match v[p.1]? with
    | none => p.2
    | some b => f p.2 b
  have hstep : Computable₂ step := by
    apply (Computable.option_casesOn
      (Computable.list_getElem?.comp Computable.fst (Computable.fst.comp Computable.snd))
      (Computable.snd.comp Computable.snd)
      (hf.comp (Computable.snd.comp (Computable.snd.comp Computable.fst))
        Computable.snd).to₂).of_eq
    intro p
    dsimp [step]
    cases p.1[p.2.1]? <;> rfl
  have hrec := Computable.nat_rec Computable.list_length (Computable.const s) hstep
  apply hrec.of_eq
  intro v
  have haux : ∀ n, Nat.rec s (fun k acc => step v (k, acc)) n = (v.take n).foldl f s := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => simp only [ih, foldl_take_succ, step]
  simpa using haux v.length

/-- The sign of the capital change for an observed Boolean answer. -/
def answerSign (b : Bool) : ℚ := if b then 1 else -1

@[simp] theorem answerSign_false : answerSign false = -1 := rfl
@[simp] theorem answerSign_true : answerSign true = 1 := rfl

@[simp] theorem abs_answerSign (b : Bool) : |answerSign b| = 1 := by
  cases b <;> norm_num [answerSign]

@[simp] theorem abs_cast_answerSign (b : Bool) : |(answerSign b : ℝ)| = 1 := by
  cases b <;> norm_num [answerSign]

@[simp] theorem cast_answerSign_sq (b : Bool) : (answerSign b : ℝ) ^ 2 = 1 := by
  cases b <;> norm_num [answerSign]

theorem primrec_answerSign : Primrec answerSign := Primrec.dom_bool _

/-- A uniformly computable rational approximation to a real capital process. -/
structure CapitalApproximation (d : CapitalProcess) where
  /-- Rational approximation to capital at a transcript and precision. -/
  value : List Bool → ℕ → ℚ
  computable_value : Computable (fun p : List Bool × ℕ => value p.1 p.2)
  error : ∀ v n, |(value v n : ℝ) - d.value v| ≤ (1 / 2 : ℝ) ^ n

/-- Choose the rational approximation supplied by uniform capital computability. -/
noncomputable def CapitalApproximation.ofComputable (d : CapitalProcess)
    (hd : ComputableRealCapital d.value) : CapitalApproximation d :=
  let q := hd.choose
  { value := q
    computable_value := computable_rat_of_numDen hd.choose_spec.1
    error := hd.choose_spec.2 }

namespace CapitalApproximation

variable {d : CapitalProcess}

/-- Approximate the additive stake of `(d + 1) / 2`, using two extra bits of
precision beyond the transcript length. -/
def stake (q : CapitalApproximation d) (v : List Bool) : ℚ :=
  (q.value (v ++ [true]) (v.length + 2) - q.value (v ++ [false]) (v.length + 2)) / 4

/-- Advance the rational account by the approximate stake's signed return. -/
def reserveStep (q : CapitalApproximation d) (p : List Bool × ℚ) (b : Bool) :
    List Bool × ℚ :=
  (p.1 ++ [b], p.2 + answerSign b * q.stake p.1)

/-- Transcript and capital obtained by applying all reserve-account updates. -/
def reserveAccount (q : CapitalApproximation d) (v : List Bool) : List Bool × ℚ :=
  v.foldl q.reserveStep ([], 1)

/-- Capital of the rational reserve account after the given transcript. -/
def reserveValue (q : CapitalApproximation d) (v : List Bool) : ℚ :=
  (q.reserveAccount v).2

@[simp] theorem reserveAccount_snoc (q : CapitalApproximation d) (v : List Bool) (b : Bool) :
    q.reserveAccount (v ++ [b]) = q.reserveStep (q.reserveAccount v) b := by
  simp [reserveAccount, List.foldl_append]

theorem reserveAccount_prefix (q : CapitalApproximation d) (v : List Bool) :
    (q.reserveAccount v).1 = v := by
  induction v using List.reverseRecOn with
  | nil => rfl
  | append_singleton v b ih => simp [reserveStep, ih]

@[simp] theorem reserveValue_nil (q : CapitalApproximation d) : q.reserveValue [] = 1 := rfl

theorem reserveValue_snoc (q : CapitalApproximation d) (v : List Bool) (b : Bool) :
    q.reserveValue (v ++ [b]) = q.reserveValue v + answerSign b * q.stake v := by
  simp [reserveValue, reserveStep, reserveAccount_prefix]

/-- Average of the original real capital and the constant reserve account. -/
noncomputable def target (d : CapitalProcess) (v : List Bool) : ℝ := (d.value v + 1) / 2

/-- Signed stake of the mixed account before rounding. -/
noncomputable def targetStake (d : CapitalProcess) (v : List Bool) : ℝ :=
  (d.value (v ++ [true]) - d.value (v ++ [false])) / 4

theorem target_snoc (d : CapitalProcess) (v : List Bool) (b : Bool) :
    target d (v ++ [b]) = target d v + (answerSign b : ℝ) * targetStake d v := by
  have hf := d.fair v
  cases b <;> simp [target, targetStake, answerSign] <;> linarith

theorem stake_error (q : CapitalApproximation d) (v : List Bool) :
    |(q.stake v : ℝ) - targetStake d v| ≤ (1 / 2 : ℝ) ^ (v.length + 3) := by
  obtain ⟨hlt, hut⟩ := abs_le.mp (q.error (v ++ [true]) (v.length + 2))
  obtain ⟨hlf, huf⟩ := abs_le.mp (q.error (v ++ [false]) (v.length + 2))
  have hp : (1 / 2 : ℝ) ^ (v.length + 3) = (1 / 2 : ℝ) ^ (v.length + 2) / 2 := by
    rw [show v.length + 3 = (v.length + 2) + 1 by omega, pow_succ]
    ring
  rw [hp, abs_le]
  unfold stake targetStake
  push_cast
  constructor <;> linarith

/-- The stronger geometric error estimate retains the unused error budget. -/
theorem reserve_error_geometric (q : CapitalApproximation d) (v : List Bool) :
    |(q.reserveValue v : ℝ) - target d v| ≤
      (1 / 4 : ℝ) * (1 - (1 / 2 : ℝ) ^ v.length) := by
  induction v using List.reverseRecOn with
  | nil => simp [target, d.initial]
  | append_singleton v b ih =>
    have heq : (q.reserveValue (v ++ [b]) : ℝ) - target d (v ++ [b]) =
        ((q.reserveValue v : ℝ) - target d v) +
          (answerSign b : ℝ) * ((q.stake v : ℝ) - targetStake d v) := by
      rw [reserveValue_snoc, target_snoc]
      push_cast
      ring
    rw [heq]
    calc
      _ ≤ |(q.reserveValue v : ℝ) - target d v| +
          |(answerSign b : ℝ) * ((q.stake v : ℝ) - targetStake d v)| := abs_add_le _ _
      _ = |(q.reserveValue v : ℝ) - target d v| +
          |(q.stake v : ℝ) - targetStake d v| := by simp [abs_mul]
      _ ≤ (1 / 4 : ℝ) * (1 - (1 / 2 : ℝ) ^ v.length) +
          (1 / 2 : ℝ) ^ (v.length + 3) := add_le_add ih (q.stake_error v)
      _ = _ := by
        simp only [List.length_append, List.length_singleton, pow_add]
        ring

theorem reserve_error (q : CapitalApproximation d) (v : List Bool) :
    |(q.reserveValue v : ℝ) - target d v| ≤ (1 / 4 : ℝ) := by
  have hg := q.reserve_error_geometric v
  have hp : 0 ≤ (1 / 2 : ℝ) ^ v.length := by positivity
  linarith

theorem reserve_lower (q : CapitalApproximation d) (v : List Bool) :
    (1 / 4 : ℚ) ≤ q.reserveValue v := by
  have h := (abs_le.mp (q.reserve_error v)).1
  have hd := d.nonneg v
  have hr : (1 / 4 : ℝ) ≤ (q.reserveValue v : ℝ) := by
    unfold target at h
    linarith
  apply (Rat.cast_le (K := ℝ)).mp
  simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using hr

theorem reserve_fair (q : CapitalApproximation d) (v : List Bool) :
    q.reserveValue (v ++ [false]) + q.reserveValue (v ++ [true]) = 2 * q.reserveValue v := by
  simp only [reserveValue_snoc, answerSign_false, answerSign_true]
  ring

theorem computable_stake (q : CapitalApproximation d) : Computable q.stake := by
  have hv (b : Bool) : Computable (fun v : List Bool =>
      q.value (v ++ [b]) (v.length + 2)) := by
    have hb : Computable (fun v : List Bool => v ++ [b]) :=
      (Primrec.list_concat.comp Primrec.id (Primrec.const b)).to_comp
    have hn : Computable (fun v : List Bool => v.length + 2) :=
      (Primrec.nat_add.comp Primrec.list_length (Primrec.const 2)).to_comp
    have hc := Computable.comp q.computable_value (hb.pair hn)
    exact hc.of_eq fun _ => rfl
  have hc := primrec_rat_div.to_comp.comp
    (primrec_rat_sub.to_comp.comp (hv true) (hv false)) (Computable.const 4)
  exact hc.of_eq fun _ => rfl

theorem computable_reserveStep (q : CapitalApproximation d) : Computable₂ q.reserveStep := by
  have hc := (Computable.list_concat.comp (Computable.fst.comp Computable.fst) Computable.snd).pair
    (primrec_rat_add.to_comp.comp (Computable.snd.comp Computable.fst)
      (primrec_rat_mul.to_comp.comp (primrec_answerSign.to_comp.comp Computable.snd)
        (q.computable_stake.comp (Computable.fst.comp Computable.fst))))
  exact hc.of_eq fun _ => rfl

theorem computable_reserveValue (q : CapitalApproximation d) : Computable q.reserveValue := by
  have hc := Computable.snd.comp
    (computable_list_foldl q.reserveStep q.computable_reserveStep ([], 1))
  exact hc.of_eq fun _ => rfl

end CapitalApproximation

/-- A computable rational fair capital process with a fixed positive reserve. -/
structure ReservedRationalCapital where
  /-- Exact rational capital assigned to each transcript. -/
  value : List Bool → ℚ
  initial : value [] = 1
  fair : ∀ v, value (v ++ [false]) + value (v ++ [true]) = 2 * value v
  lower : ∀ v, (1 / 4 : ℚ) ≤ value v
  computable_value : Computable value

/-- The uniformly computable rational process with a positive reserve. -/
def CapitalApproximation.reserve {d : CapitalProcess} (q : CapitalApproximation d) :
    ReservedRationalCapital where
  value := q.reserveValue
  initial := q.reserveValue_nil
  fair := q.reserve_fair
  lower := q.reserve_lower
  computable_value := q.computable_reserveValue

namespace ReservedRationalCapital

theorem positive (r : ReservedRationalCapital) (v : List Bool) : 0 < r.value v := by
  have := r.lower v
  linarith

/-- Interpret reserved rational capital as a real fair capital process. -/
def capital (r : ReservedRationalCapital) : CapitalProcess where
  value v := (r.value v : ℝ)
  initial := by simp [r.initial]
  nonneg v := Rat.cast_nonneg.mpr (r.positive v).le
  fair v := by exact_mod_cast r.fair v

/-- Bet with reserved capital while following the given scan. -/
def strategy (r : ReservedRationalCapital) (π : ScanRule) : BettingStrategy where
  scan := π
  capital := r.capital
  computable_capital := computableRealCapital_of_rat r.computable_value

/-- The fraction of current capital staked on the next answer. -/
def wager (r : ReservedRationalCapital) (v : List Bool) : ℚ :=
  (r.value (v ++ [true]) - r.value (v ++ [false])) / (2 * r.value v)

theorem update (r : ReservedRationalCapital) (v : List Bool) (b : Bool) :
    r.value (v ++ [b]) = r.value v * (1 + answerSign b * r.wager v) := by
  have hf := r.fair v
  have hn := ne_of_gt (r.positive v)
  unfold wager
  cases b <;> simp only [answerSign_false, answerSign_true] <;>
    field_simp <;> nlinarith

theorem abs_wager_lt_one (r : ReservedRationalCapital) (v : List Bool) :
    |r.wager v| < 1 := by
  have hf := r.fair v
  have ht := r.positive (v ++ [true])
  have hfalse := r.positive (v ++ [false])
  have hp := r.positive v
  rw [wager, abs_lt]
  constructor
  · apply (lt_div_iff₀ (by positivity : 0 < 2 * r.value v)).mpr
    linarith
  · apply (div_lt_iff₀ (by positivity : 0 < 2 * r.value v)).mpr
    linarith

theorem computable_wager (r : ReservedRationalCapital) : Computable r.wager := by
  have hv (b : Bool) : Computable (fun v : List Bool => r.value (v ++ [b])) := by
    have hc := Computable.comp r.computable_value
      (Computable.list_concat.comp Computable.id (Computable.const b))
    exact hc.of_eq fun _ => rfl
  have hc := primrec_rat_div.to_comp.comp
    (primrec_rat_sub.to_comp.comp (hv true) (hv false))
    (primrec_rat_mul.to_comp.comp (Computable.const 2) r.computable_value)
  exact hc.of_eq fun _ => rfl

end ReservedRationalCapital

theorem CapitalApproximation.reserve_preserves_success (s : BettingStrategy)
    (q : CapitalApproximation s.capital) {X : Cantor} (hs : s.Succeeds X) :
    (q.reserve.strategy s.scan).Succeeds X := by
  intro B
  obtain ⟨n, hn⟩ := hs (2 * B)
  refine ⟨n, ?_⟩
  change B < (q.reserveValue (s.scan.transcript X n) : ℝ)
  have he := (abs_le.mp (q.reserve_error (s.scan.transcript X n))).1
  unfold CapitalApproximation.target at he
  linarith

end Klr
