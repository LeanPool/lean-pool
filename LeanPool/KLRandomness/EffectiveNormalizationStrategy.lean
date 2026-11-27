/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

-- Modified for Lean Pool.

module

public import LeanPool.KLRandomness.EffectiveNormalization
public import LeanPool.KLRandomness.NormalizationSuccess
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Effective strategy normalization

This file completes Lemma 2 at the level of `BettingStrategy`.  Every total
computable-real strategy is replaced, with the same scan, by a computable
rational strategy with positive capital, wager magnitude at most `1/2`, and
pathwise sum of squared wagers at most `1/2`.  Success is preserved on every
input.  The real-valued analytic result is applied only after proving that the
constructed strategy has exactly the required multiplicative capital.
-/

@[expose] public section

namespace Klr

open RationalComputability

namespace ReservedRationalCapital

/-- Transcript, accumulated squared source wagers, and normalized capital. -/
abbrev NormalizationState := List Bool × (ℚ × ℚ)

/-- Advance the transcript, squared-wager total and normalized capital by one answer. -/
def normalizationStep (r : ReservedRationalCapital) (p : NormalizationState) (b : Bool) :
    NormalizationState :=
  let f := r.wager p.1
  let h := f / (2 * (1 + p.2.1))
  (p.1 ++ [b], p.2.1 + f ^ 2, p.2.2 * (1 + answerSign b * h))

/-- The normalization state obtained by processing a finite transcript. -/
def normalizationAccount (r : ReservedRationalCapital) (v : List Bool) : NormalizationState :=
  v.foldl r.normalizationStep ([], 0, 1)

/-- The accumulated sum of squared original wager fractions. -/
def variation (r : ReservedRationalCapital) (v : List Bool) : ℚ :=
  (r.normalizationAccount v).2.1

/-- The damped capital after processing the given transcript. -/
def normalizedValue (r : ReservedRationalCapital) (v : List Bool) : ℚ :=
  (r.normalizationAccount v).2.2

/-- The original wager fraction damped by the accumulated squared wagers. -/
def normalizedFraction (r : ReservedRationalCapital) (v : List Bool) : ℚ :=
  r.wager v / (2 * (1 + r.variation v))

@[simp] theorem normalizationAccount_snoc (r : ReservedRationalCapital)
    (v : List Bool) (b : Bool) :
    r.normalizationAccount (v ++ [b]) = r.normalizationStep (r.normalizationAccount v) b := by
  simp [normalizationAccount, List.foldl_append]

theorem normalizationAccount_prefix (r : ReservedRationalCapital) (v : List Bool) :
    (r.normalizationAccount v).1 = v := by
  induction v using List.reverseRecOn with
  | nil => rfl
  | append_singleton v b ih => simp [normalizationStep, ih]

@[simp] theorem variation_nil (r : ReservedRationalCapital) : r.variation [] = 0 := rfl

theorem variation_snoc (r : ReservedRationalCapital) (v : List Bool) (b : Bool) :
    r.variation (v ++ [b]) = r.variation v + (r.wager v) ^ 2 := by
  simp [variation, normalizationStep, normalizationAccount_prefix]

theorem variation_nonneg (r : ReservedRationalCapital) (v : List Bool) : 0 ≤ r.variation v := by
  induction v using List.reverseRecOn with
  | nil => simp
  | append_singleton v b ih => rw [variation_snoc]; positivity

theorem normalizedFraction_abs_le_half (r : ReservedRationalCapital) (v : List Bool) :
    |r.normalizedFraction v| ≤ (1 / 2 : ℚ) := by
  have hq := r.variation_nonneg v
  have hf := (r.abs_wager_lt_one v).le
  have hd : 0 < 2 * (1 + r.variation v) := by positivity
  rw [normalizedFraction, abs_div, abs_of_pos hd]
  apply (div_le_iff₀ hd).mpr
  linarith

@[simp] theorem normalizedValue_nil (r : ReservedRationalCapital) : r.normalizedValue [] = 1 := rfl

theorem normalizedValue_snoc (r : ReservedRationalCapital) (v : List Bool) (b : Bool) :
    r.normalizedValue (v ++ [b]) =
      r.normalizedValue v * (1 + answerSign b * r.normalizedFraction v) := by
  simp [normalizedValue, normalizationStep, normalizedFraction, variation,
    normalizationAccount_prefix]

theorem normalizedValue_positive (r : ReservedRationalCapital) (v : List Bool) :
    0 < r.normalizedValue v := by
  induction v using List.reverseRecOn with
  | nil => norm_num
  | append_singleton v b ih =>
    rw [normalizedValue_snoc]
    apply mul_pos ih
    obtain ⟨hl, hu⟩ := abs_le.mp (r.normalizedFraction_abs_le_half v)
    cases b <;> simp only [answerSign_false, answerSign_true] <;> linarith

theorem normalizedValue_fair (r : ReservedRationalCapital) (v : List Bool) :
    r.normalizedValue (v ++ [false]) + r.normalizedValue (v ++ [true]) =
      2 * r.normalizedValue v := by
  simp only [normalizedValue_snoc, answerSign_false, answerSign_true]
  ring

theorem computable_normalizationStep (r : ReservedRationalCapital) :
    Computable₂ r.normalizationStep := by
  have hf : Computable (fun p : NormalizationState × Bool => r.wager p.1.1) := by
    have hp : Computable (fun p : NormalizationState × Bool => p.1.1) :=
      Computable.fst.comp Computable.fst
    have hc := r.computable_wager.comp hp
    exact hc.of_eq fun _ => rfl
  have hq : Computable (fun p : NormalizationState × Bool => p.1.2.1) :=
    Computable.fst.comp (Computable.snd.comp Computable.fst)
  have hc : Computable (fun p : NormalizationState × Bool => p.1.2.2) :=
    Computable.snd.comp (Computable.snd.comp Computable.fst)
  have hh : Computable (fun p : NormalizationState × Bool =>
      r.wager p.1.1 / (2 * (1 + p.1.2.1))) := by
    have hc := primrec_rat_div.to_comp.comp hf
      (primrec_rat_mul.to_comp.comp (Computable.const 2)
        (primrec_rat_add.to_comp.comp (Computable.const 1) hq))
    exact hc.of_eq fun _ => rfl
  have hqq : Computable (fun p : NormalizationState × Bool => p.1.2.1 + (r.wager p.1.1)^2) := by
    have hc := primrec_rat_add.to_comp.comp hq
      (primrec_rat_mul.to_comp.comp hf hf)
    exact hc.of_eq fun _ => by simp only [pow_two]
  have hc := (Computable.list_concat.comp (Computable.fst.comp Computable.fst) Computable.snd).pair
    (hqq.pair (primrec_rat_mul.to_comp.comp hc
      (primrec_rat_add.to_comp.comp (Computable.const 1)
        (primrec_rat_mul.to_comp.comp (primrec_answerSign.to_comp.comp Computable.snd) hh))))
  exact hc.of_eq fun _ => rfl

theorem computable_normalizationAccount (r : ReservedRationalCapital) :
    Computable r.normalizationAccount := by
  have hc := computable_list_foldl r.normalizationStep r.computable_normalizationStep ([], 0, 1)
  exact hc.of_eq fun _ => rfl

theorem computable_normalizedValue (r : ReservedRationalCapital) :
    Computable r.normalizedValue := by
  have hc := Computable.snd.comp (Computable.snd.comp r.computable_normalizationAccount)
  exact hc.of_eq fun _ => rfl

/-- The normalized capital as a real fair process. -/
def normalizedCapital (r : ReservedRationalCapital) : CapitalProcess where
  value v := (r.normalizedValue v : ℝ)
  initial := by simp
  nonneg v := Rat.cast_nonneg.mpr (r.normalizedValue_positive v).le
  fair v := by exact_mod_cast r.normalizedValue_fair v

/-- The normalized process paired with the original adaptive scan. -/
def normalizedStrategy (r : ReservedRationalCapital) (π : ScanRule) : BettingStrategy where
  scan := π
  capital := r.normalizedCapital
  computable_capital := computableRealCapital_of_rat r.computable_normalizedValue

theorem normalizedCapital_positive (r : ReservedRationalCapital) (v : List Bool) :
    0 < r.normalizedCapital.value v := Rat.cast_pos.mpr (r.normalizedValue_positive v)

theorem normalizedCapital_wager (r : ReservedRationalCapital) (v : List Bool) :
    r.normalizedCapital.wager v = (r.normalizedFraction v : ℝ) := by
  have hn : (r.normalizedValue v : ℝ) ≠ 0 := ne_of_gt (r.normalizedCapital_positive v)
  change ((r.normalizedValue (v ++ [true]) : ℝ) -
    (r.normalizedValue (v ++ [false]) : ℝ)) / (2 * (r.normalizedValue v : ℝ)) = _
  rw [normalizedValue_snoc, normalizedValue_snoc]
  simp only [answerSign_true, answerSign_false]
  push_cast
  field_simp
  ring

theorem normalizedCapital_wager_abs_le_half (r : ReservedRationalCapital) (v : List Bool) :
    |r.normalizedCapital.wager v| ≤ (1 / 2 : ℝ) := by
  rw [normalizedCapital_wager]
  have h := (Rat.cast_le (K := ℝ)).mpr (r.normalizedFraction_abs_le_half v)
  simpa only [Rat.cast_abs, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using h

/-- Original wager fraction at one time along the run on an input. -/
noncomputable def pathWager (r : ReservedRationalCapital) (π : ScanRule) (X : Cantor) (n : ℕ) : ℝ :=
  (r.wager (π.transcript X n) : ℝ)

/-- Wager fraction multiplied by the sign of the next observed answer. -/
noncomputable def pathReturn (r : ReservedRationalCapital)
    (π : ScanRule) (X : Cantor) (n : ℕ) : ℝ :=
  (answerSign (X (π.query (π.transcript X n))) : ℝ) * r.pathWager π X n

theorem pathWager_abs_lt_one (r : ReservedRationalCapital) (π : ScanRule) (X : Cantor) (n : ℕ) :
    |r.pathWager π X n| < 1 := by
  have h := (Rat.cast_lt (K := ℝ)).mpr (r.abs_wager_lt_one (π.transcript X n))
  simpa only [Rat.cast_abs, Rat.cast_one, pathWager] using h

theorem pathReturn_abs_lt_one (r : ReservedRationalCapital) (π : ScanRule) (X : Cantor) (n : ℕ) :
    |r.pathReturn π X n| < 1 := by
  simpa [pathReturn, abs_mul] using r.pathWager_abs_lt_one π X n

theorem pathReturn_sq (r : ReservedRationalCapital) (π : ScanRule) (X : Cantor) (n : ℕ) :
    (r.pathReturn π X n)^2 = (r.pathWager π X n)^2 := by
  simp [pathReturn, mul_pow]

theorem variation_transcript (r : ReservedRationalCapital) (π : ScanRule) (X : Cantor) (n : ℕ) :
    (r.variation (π.transcript X n) : ℝ) = quadraticVariation (r.pathWager π X) n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [ScanRule.transcript_succ, variation_snoc, quadraticVariation_succ]
    push_cast
    rw [ih]
    rfl

theorem variation_return (r : ReservedRationalCapital) (π : ScanRule) (X : Cantor) (n : ℕ) :
    (r.variation (π.transcript X n) : ℝ) = quadraticVariation (r.pathReturn π X) n := by
  rw [variation_transcript]
  simp only [quadraticVariation, pathReturn_sq]

theorem normalizedFraction_transcript (r : ReservedRationalCapital)
    (π : ScanRule) (X : Cantor) (n : ℕ) :
    (r.normalizedFraction (π.transcript X n) : ℝ) = normalizedWager (r.pathWager π X) n := by
  unfold normalizedFraction normalizedWager
  push_cast
  rw [variation_transcript]
  rfl

theorem normalizedReturn_transcript (r : ReservedRationalCapital)
    (π : ScanRule) (X : Cantor) (n : ℕ) :
    (answerSign (X (π.query (π.transcript X n))) : ℝ) *
      (r.normalizedFraction (π.transcript X n) : ℝ) =
      normalizedWager (r.pathReturn π X) n := by
  unfold normalizedFraction normalizedWager
  push_cast
  rw [variation_return]
  unfold pathReturn pathWager
  ring

theorem reserve_product (r : ReservedRationalCapital) (π : ScanRule) (X : Cantor) (n : ℕ) :
    multiplicativeCapital (r.pathReturn π X) n = (r.value (π.transcript X n) : ℝ) := by
  induction n with
  | zero => simp [r.initial]
  | succ n ih =>
    rw [multiplicativeCapital_succ, ih, ScanRule.transcript_succ, r.update]
    push_cast
    rfl

theorem normalized_product (r : ReservedRationalCapital) (π : ScanRule) (X : Cantor) (n : ℕ) :
    multiplicativeCapital (normalizedWager (r.pathReturn π X)) n =
      (r.normalizedValue (π.transcript X n) : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [multiplicativeCapital_succ, ih, ScanRule.transcript_succ, normalizedValue_snoc]
    push_cast
    rw [normalizedReturn_transcript]

theorem normalized_wagers_summable (r : ReservedRationalCapital) (π : ScanRule) (X : Cantor) :
    Summable (fun n => (r.normalizedCapital.wager (π.transcript X n))^2) := by
  simp only [normalizedCapital_wager, normalizedFraction_transcript]
  exact summable_normalizedWager_sq _ (fun n => (r.pathWager_abs_lt_one π X n).le)

theorem normalized_wagers_sum_le_half (r : ReservedRationalCapital)
    (π : ScanRule) (X : Cantor) (N : ℕ) :
    (∑ n ∈ Finset.range N, (r.normalizedCapital.wager (π.transcript X n))^2) ≤
      (1 / 2 : ℝ) := by
  simp only [normalizedCapital_wager, normalizedFraction_transcript]
  exact sum_normalizedWager_sq_le_half _
    (fun n => (sq_le_one_iff_abs_le_one _).mpr (r.pathWager_abs_lt_one π X n).le) N

theorem normalized_wagers_tsum_le_half (r : ReservedRationalCapital) (π : ScanRule) (X : Cantor) :
    (∑' n, (r.normalizedCapital.wager (π.transcript X n))^2) ≤ (1 / 2 : ℝ) := by
  simp only [normalizedCapital_wager, normalizedFraction_transcript]
  exact tsum_normalizedWager_sq_le_half _ (fun n => (r.pathWager_abs_lt_one π X n).le)

theorem normalization_preserves_success (r : ReservedRationalCapital) (π : ScanRule)
    {X : Cantor} (hs : (r.strategy π).Succeeds X) : (r.normalizedStrategy π).Succeeds X := by
  have hunbounded : ¬ BddAbove (Set.range (multiplicativeCapital (r.pathReturn π X))) := by
    rintro ⟨B, hB⟩
    obtain ⟨n, hn⟩ := hs B
    have hb := hB (Set.mem_range_self n)
    rw [reserve_product] at hb
    exact (not_lt_of_ge hb) hn
  have hreserve : ∀ n, (1 / 4 : ℝ) ≤ multiplicativeCapital (r.pathReturn π X) n := by
    intro n
    rw [reserve_product]
    have h := (Rat.cast_le (K := ℝ)).mpr (r.lower (π.transcript X n))
    simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using h
  have hnorm := normalization_preserves_unbounded_capital (r.pathReturn π X) (1 / 4)
    (r.pathReturn_abs_lt_one π X) (by norm_num) hreserve hunbounded
  intro B
  by_contra! h
  apply hnorm
  refine ⟨B, ?_⟩
  rintro _ ⟨n, rfl⟩
  rw [normalized_product]
  exact h n

end ReservedRationalCapital

/-- The effective Lemma 2 transformation.  The chosen approximation is a
uniform computable witness from the input strategy's existing interface. -/
noncomputable def BettingStrategy.normalize (s : BettingStrategy) : BettingStrategy :=
  (CapitalApproximation.ofComputable s.capital s.computable_capital).reserve.normalizedStrategy
    s.scan

@[simp] theorem BettingStrategy.normalize_scan (s : BettingStrategy) :
    s.normalize.scan = s.scan := rfl

theorem BettingStrategy.normalize_positive (s : BettingStrategy) (v : List Bool) :
    0 < s.normalize.capital.value v :=
  ReservedRationalCapital.normalizedCapital_positive _ v

theorem BettingStrategy.normalize_wager_abs_le_half (s : BettingStrategy) (v : List Bool) :
    |s.normalize.capital.wager v| ≤ (1 / 2 : ℝ) :=
  ReservedRationalCapital.normalizedCapital_wager_abs_le_half _ v

theorem BettingStrategy.normalize_wagers_summable (s : BettingStrategy) (X : Cantor) :
    Summable (fun n => (s.normalize.capital.wager (s.normalize.scan.transcript X n))^2) :=
  ReservedRationalCapital.normalized_wagers_summable _ s.scan X

theorem BettingStrategy.normalize_wagers_sum_le_half (s : BettingStrategy) (X : Cantor) (N : ℕ) :
    (∑ n ∈ Finset.range N,
      (s.normalize.capital.wager (s.normalize.scan.transcript X n))^2) ≤ (1 / 2 : ℝ) :=
  ReservedRationalCapital.normalized_wagers_sum_le_half _ s.scan X N

theorem BettingStrategy.normalize_wagers_tsum_le_half (s : BettingStrategy) (X : Cantor) :
    (∑' n, (s.normalize.capital.wager (s.normalize.scan.transcript X n))^2) ≤ (1 / 2 : ℝ) :=
  ReservedRationalCapital.normalized_wagers_tsum_le_half _ s.scan X

theorem BettingStrategy.normalize_preserves_success (s : BettingStrategy) {X : Cantor}
    (hs : s.Succeeds X) : s.normalize.Succeeds X :=
  ReservedRationalCapital.normalization_preserves_success _ s.scan
    ((CapitalApproximation.ofComputable s.capital s.computable_capital).reserve_preserves_success
      s hs)

theorem BettingStrategy.normalize_rational (s : BettingStrategy) :
    ∃ d : List Bool → ℚ, Computable d ∧ ∀ v, s.normalize.capital.value v = (d v : ℝ) :=
  ⟨_, ReservedRationalCapital.computable_normalizedValue _, fun _ => rfl⟩

end Klr
