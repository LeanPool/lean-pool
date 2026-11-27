/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

-- Modified for Lean Pool.

module

public import LeanPool.KLRandomness.MaximalInequality
public import LeanPool.KLRandomness.EffectiveNormalization
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Bounded capital from fair steps and summable forced wagers

This is the probabilistic conclusion needed in Section 6, with its two genuine
application obligations stated explicitly: selected finite histories have fair
next-answer probabilities, and the absolute wagers at all other steps are
summable almost surely.  A weighted-cylinder maximal inequality bounds the
fair-only product.  The remaining product is bounded by the exponential of its
absolute-wager sum.  No martingale convergence assumption is used.
-/

@[expose] public section

namespace Klr.FairForced

open MeasureTheory
open scoped ENNReal

/-- The set of inputs with the specified observed transcript. -/
def event (π : ScanRule) (v : List Bool) : Set Cantor :=
  {X | π.transcript X v.length = v}

@[simp] theorem event_nil (π : ScanRule) : event π [] = Set.univ := by
  ext X
  simp [event]

theorem measurableSet_event (π : ScanRule) (v : List Bool) : MeasurableSet (event π v) :=
  π.measurableSet_transcript v

theorem event_snoc (π : ScanRule) (v : List Bool) (b : Bool) :
    event π (v ++ [b]) = event π v ∩ {X | X (π.query v) = b} := by
  ext X
  constructor
  · intro h
    change π.transcript X (v ++ [b]).length = v ++ [b] at h
    simp only [List.length_append, List.length_singleton] at h
    have ht := π.transcript_take X (m := v.length) (n := v.length + 1) (by omega)
    rw [h] at ht
    have hp : π.transcript X v.length = v := by simpa using ht.symm
    rw [ScanRule.transcript_succ, hp] at h
    have hb : X (π.query v) = b := by simpa using List.append_cancel_left h
    exact ⟨hp, hb⟩
  · rintro ⟨hp, hb⟩
    change π.transcript X v.length = v at hp
    simpa [event, ScanRule.transcript_succ, hp, hb]

theorem event_children_union (π : ScanRule) (v : List Bool) :
    event π (v ++ [false]) ∪ event π (v ++ [true]) = event π v := by
  rw [event_snoc, event_snoc]
  ext X
  cases hb : X (π.query v) <;> simp [hb]

theorem event_children_disjoint (π : ScanRule) (v : List Bool) :
    Disjoint (event π (v ++ [false])) (event π (v ++ [true])) := by
  rw [event_snoc, event_snoc]
  apply Set.disjoint_left.mpr
  intro X hX hY
  exact Bool.false_ne_true (hX.2.symm.trans hY.2)

theorem measure_event_children (μ : Measure Cantor) (π : ScanRule) (v : List Bool) :
    μ (event π (v ++ [false])) + μ (event π (v ++ [true])) = μ (event π v) := by
  rw [← measure_union (event_children_disjoint π v) (measurableSet_event π _),
    event_children_union]

/-- Advance the transcript and multiply capital by the next return factor. -/
noncomputable def capitalStep (w : List Bool → ℝ) (p : List Bool × ℝ) (b : Bool) :
    List Bool × ℝ :=
  (p.1 ++ [b], p.2 * (1 + (answerSign b : ℝ) * w p.1))

/-- The transcript and capital after applying each multiplicative update. -/
noncomputable def account (w : List Bool → ℝ) (v : List Bool) : List Bool × ℝ :=
  v.foldl (capitalStep w) ([], 1)

/-- The product of the return factors along the given transcript. -/
noncomputable def capital (w : List Bool → ℝ) (v : List Bool) : ℝ := (account w v).2

@[simp] theorem account_snoc (w : List Bool → ℝ) (v : List Bool) (b : Bool) :
    account w (v ++ [b]) = capitalStep w (account w v) b := by
  simp [account, List.foldl_append]

theorem account_prefix (w : List Bool → ℝ) (v : List Bool) : (account w v).1 = v := by
  induction v using List.reverseRecOn with
  | nil => rfl
  | append_singleton v b ih => simp [capitalStep, ih]

@[simp] theorem capital_nil (w : List Bool → ℝ) : capital w [] = 1 := rfl

theorem capital_snoc (w : List Bool → ℝ) (v : List Bool) (b : Bool) :
    capital w (v ++ [b]) = capital w v * (1 + (answerSign b : ℝ) * w v) := by
  simp [capital, capitalStep, account_prefix]

theorem factor_nonneg {w : ℝ} (hw : |w| ≤ 1) (b : Bool) :
    0 ≤ 1 + (answerSign b : ℝ) * w := by
  obtain ⟨hl, hu⟩ := abs_le.mp hw
  cases b <;> norm_num [answerSign] <;> linarith

theorem capital_nonneg (w : List Bool → ℝ) (hw : ∀ v, |w v| ≤ 1) (v : List Bool) :
    0 ≤ capital w v := by
  induction v using List.reverseRecOn with
  | nil => norm_num
  | append_singleton v b ih =>
    rw [capital_snoc]
    exact mul_nonneg ih (factor_nonneg (hw v) b)

theorem capital_fair (w : List Bool → ℝ) (v : List Bool) :
    capital w (v ++ [false]) + capital w (v ++ [true]) = 2 * capital w v := by
  simp only [capital_snoc, answerSign_false, answerSign_true, Rat.cast_neg, Rat.cast_one]
  ring

/-- The fair capital process induced by a schedule of wager fractions bounded by one. -/
noncomputable def process (w : List Bool → ℝ) (hw : ∀ v, |w v| ≤ 1) : CapitalProcess where
  value := capital w
  initial := capital_nil w
  nonneg := capital_nonneg w hw
  fair := capital_fair w

/-- `true` selects histories whose next bit is conditionally fair. -/
noncomputable def fairWager (select : List Bool → Bool) (w : List Bool → ℝ) (v : List Bool) : ℝ :=
  if select v then w v else 0

/-- The original wager on forced answers and zero on fair answers. -/
noncomputable def forcedWager (select : List Bool → Bool) (w : List Bool → ℝ) (v : List Bool) : ℝ :=
  if select v then 0 else w v

/-- The magnitude of the original wager on forced answers and zero on fair answers. -/
noncomputable def forcedAmount (select : List Bool → Bool) (w : List Bool → ℝ)
    (v : List Bool) : ℝ := if select v then 0 else |w v|

theorem fairWager_bound (select : List Bool → Bool) (w : List Bool → ℝ)
    (hw : ∀ v, |w v| ≤ 1) (v : List Bool) : |fairWager select w v| ≤ 1 := by
  cases h : select v <;> simp [fairWager, h, hw]

theorem forcedWager_bound (select : List Bool → Bool) (w : List Bool → ℝ)
    (hw : ∀ v, |w v| ≤ 1) (v : List Bool) : |forcedWager select w v| ≤ 1 := by
  cases h : select v <;> simp [forcedWager, h, hw]

@[simp] theorem abs_forcedWager (select : List Bool → Bool) (w : List Bool → ℝ) (v : List Bool) :
    |forcedWager select w v| = forcedAmount select w v := by
  cases h : select v <;> simp [forcedWager, forcedAmount, h]

theorem forcedAmount_nonneg (select : List Bool → Bool) (w : List Bool → ℝ) (v : List Bool) :
    0 ≤ forcedAmount select w v := by
  cases h : select v <;> simp [forcedAmount, h]

/-- The condition consumed from the affine probability calculation.  It is an
identity of actual transcript-cylinder probabilities under the input law. -/
def FairLaw (μ : Measure Cantor) (π : ScanRule) (select : List Bool → Bool) : Prop :=
  ∀ v, select v = true → ∀ b : Bool,
    μ (event π (v ++ [b])) = (1 / 2 : ℝ≥0∞) * μ (event π v)

/-- Capital-weighted mass is conserved when refining each transcript cylinder. -/
def WeightedBalance (μ : Measure Cantor) (π : ScanRule) (d : CapitalProcess) : Prop :=
  ∀ v, ENNReal.ofReal (d.value (v ++ [false])) * μ (event π (v ++ [false])) +
      ENNReal.ofReal (d.value (v ++ [true])) * μ (event π (v ++ [true])) =
    ENNReal.ofReal (d.value v) * μ (event π v)

theorem fair_process_weightedBalance (μ : Measure Cantor) (π : ScanRule)
    (select : List Bool → Bool) (w : List Bool → ℝ) (hw : ∀ v, |w v| ≤ 1)
    (hfair : FairLaw μ π select) :
    WeightedBalance μ π (process (fairWager select w) (fairWager_bound select w hw)) := by
  let d := process (fairWager select w) (fairWager_bound select w hw)
  change WeightedBalance μ π d
  intro v
  cases hs : select v with
  | false =>
    have hchild (b : Bool) : d.value (v ++ [b]) = d.value v := by
      change capital (fairWager select w) (v ++ [b]) = capital (fairWager select w) v
      simp [capital_snoc, fairWager, hs]
    rw [hchild, hchild, ← mul_add, measure_event_children]
  | true =>
    rw [hfair v hs false, hfair v hs true, ← add_mul,
      ← ENNReal.ofReal_add (d.nonneg _) (d.nonneg _), d.fair,
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num only [ENNReal.ofReal_ofNat]
    calc
      2 * ENNReal.ofReal (d.value v) * ((1 / 2 : ℝ≥0∞) * μ (event π v)) =
          ENNReal.ofReal (d.value v) * μ (event π v) * (2 * (1 / 2)) := by ac_rfl
      _ = _ := by
        rw [one_div, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), mul_one]

/-- Finite-tree maximal inequality under a nonuniform input law. -/
theorem finiteHit_bound (μ : Measure Cantor) (π : ScanRule) (d : CapitalProcess)
    (hbalance : WeightedBalance μ π d) (a : ℝ) (v : List Bool) (n : ℕ) :
    ENNReal.ofReal a * μ (d.finiteHit π a v n) ≤ ENNReal.ofReal (d.value v) * μ (event π v) := by
  induction n generalizing v with
  | zero =>
    by_cases h : a < d.value v
    · simp only [CapitalProcess.finiteHit, ite_eq_left h, event]
      gcongr
    · simp [CapitalProcess.finiteHit, h]
  | succ n ih =>
    by_cases h : a < d.value v
    · simp only [CapitalProcess.finiteHit, ite_eq_left h, event]
      gcongr
    · rw [CapitalProcess.finiteHit, ite_eq_right h]
      calc
        _ ≤ ENNReal.ofReal a * (μ (d.finiteHit π a (v ++ [false]) n) +
            μ (d.finiteHit π a (v ++ [true]) n)) := by
          gcongr
          exact measure_union_le _ _
        _ = _ := mul_add _ _ _
        _ ≤ _ := add_le_add (ih _) (ih _)
        _ = _ := hbalance v

theorem measure_exceeds_pow_le (μ : Measure Cantor) [IsProbabilityMeasure μ]
    (π : ScanRule) (d : CapitalProcess) (hbalance : WeightedBalance μ π d) (m : ℕ) :
    μ (d.exceeds π ((2 : ℝ) ^ m)) ≤ (1 / 2 : ℝ≥0∞) ^ m := by
  rw [d.exceeds_eq_iUnion_finiteHit, (d.finiteHit_mono π ((2 : ℝ) ^ m) []).measure_iUnion]
  apply iSup_le
  intro n
  have h := finiteHit_bound μ π d hbalance ((2 : ℝ)^m) [] n
  simp only [d.initial, ENNReal.ofReal_one, event_nil, measure_univ, mul_one,
    ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_ofNat] at h
  have hc : (1 / 2 : ℝ≥0∞)^m * (2 : ℝ≥0∞)^m = 1 := by
    rw [← mul_pow, one_div, ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_pow]
  calc
    _ = (1 / 2 : ℝ≥0∞)^m *
        ((2 : ℝ≥0∞)^m * μ (d.finiteHit π ((2 : ℝ)^m) [] n)) := by
      rw [← mul_assoc, hc, one_mul]
    _ ≤ (1 / 2 : ℝ≥0∞)^m * 1 := by gcongr
    _ = _ := mul_one _

/-- The weighted maximal inequality implies almost-sure boundedness directly;
no martingale convergence theorem is needed. -/
theorem ae_bounded_of_weightedBalance (μ : Measure Cantor) [IsProbabilityMeasure μ]
    (π : ScanRule) (d : CapitalProcess) (hbalance : WeightedBalance μ π d) :
    ∀ᵐ X ∂μ, ∃ B : ℝ, ∀ n, d.value (π.transcript X n) ≤ B := by
  rw [ae_iff]
  let Bad : Set Cantor := {X | ¬∃ B : ℝ, ∀ n, d.value (π.transcript X n) ≤ B}
  have hbound (m : ℕ) : μ Bad ≤ (1 / 2 : ℝ≥0∞)^m := by
    apply (measure_mono (show Bad ⊆ d.exceeds π ((2 : ℝ)^m) from ?_)).trans
      (measure_exceeds_pow_le μ π d hbalance m)
    intro X hX
    by_contra h
    apply hX
    refine ⟨(2 : ℝ)^m, fun n => ?_⟩
    exact le_of_not_gt (fun hn => h ⟨n, hn⟩)
  have hzero : μ Bad ≤ 0 :=
    le_of_tendsto_of_tendsto tendsto_const_nhds
      (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (1 / 2 : ℝ≥0∞) < 1))
      (Filter.Eventually.of_forall hbound)
  exact le_antisymm hzero bot_le

/-- The full capital is the product of the fair-only and forced-only accounts. -/
theorem capital_eq_fair_mul_forced (select : List Bool → Bool) (w : List Bool → ℝ)
    (v : List Bool) :
    capital w v = capital (fairWager select w) v * capital (forcedWager select w) v := by
  induction v using List.reverseRecOn with
  | nil => simp
  | append_singleton v b ih =>
    simp only [capital_snoc, ih]
    cases hs : select v <;> simp [fairWager, forcedWager, hs] <;> ring

theorem factor_le_exp_abs (w : ℝ) (b : Bool) :
    1 + (answerSign b : ℝ) * w ≤ Real.exp |w| := by
  calc
    _ ≤ |w| + 1 := by
      cases b <;> norm_num [answerSign] <;> linarith [le_abs_self w, neg_le_abs w]
    _ ≤ _ := Real.add_one_le_exp _

/-- A multiplicative account is bounded by the exponential of its finite
absolute-wager sum. -/
theorem capital_le_exp_sum (w : List Bool → ℝ) (hw : ∀ v, |w v| ≤ 1)
    (π : ScanRule) (X : Cantor) (n : ℕ) :
    capital w (π.transcript X n) ≤
      Real.exp (∑ t ∈ Finset.range n, |w (π.transcript X t)|) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [ScanRule.transcript_succ, capital_snoc, Finset.sum_range_succ, Real.exp_add]
    exact mul_le_mul ih (factor_le_exp_abs _ _)
      (factor_nonneg (hw _) _) (Real.exp_pos _).le

/-- Fair-step capital is almost surely bounded under the actual input law.
The other steps are skipped, without making any assumption about their answer law. -/
theorem ae_bounded_fair_capital (μ : Measure Cantor) [IsProbabilityMeasure μ]
    (π : ScanRule) (select : List Bool → Bool) (w : List Bool → ℝ)
    (hw : ∀ v, |w v| ≤ 1) (hfair : FairLaw μ π select) :
    ∀ᵐ X ∂μ, ∃ B : ℝ, ∀ n, capital (fairWager select w) (π.transcript X n) ≤ B :=
  ae_bounded_of_weightedBalance μ π _ (fair_process_weightedBalance μ π select w hw hfair)

/-- The main fair/forced criterion.  Fairness of selected histories and almost-sure
summability of all other absolute wagers imply bounded total capital almost surely.
These hypotheses must be established for the intended block product law. -/
theorem ae_bounded_capital (μ : Measure Cantor) [IsProbabilityMeasure μ]
    (π : ScanRule) (select : List Bool → Bool) (w : List Bool → ℝ)
    (hw : ∀ v, |w v| ≤ (1 / 2 : ℝ)) (hfair : FairLaw μ π select)
    (hforced : ∀ᵐ X ∂μ, Summable (fun n => forcedAmount select w (π.transcript X n))) :
    ∀ᵐ X ∂μ, ∃ B : ℝ, ∀ n, capital w (π.transcript X n) ≤ B := by
  have hw' (v : List Bool) : |w v| ≤ 1 := (hw v).trans (by norm_num)
  filter_upwards [ae_bounded_fair_capital μ π select w hw' hfair, hforced]
    with X hF hsum
  obtain ⟨B, hB⟩ := hF
  let A := ∑' n, forcedAmount select w (π.transcript X n)
  refine ⟨max 0 B * Real.exp A, fun n => ?_⟩
  have hsum_le : (∑ t ∈ Finset.range n, forcedAmount select w (π.transcript X t)) ≤ A :=
    hsum.sum_le_tsum _ (fun _ _ => forcedAmount_nonneg _ _ _)
  have hG : capital (forcedWager select w) (π.transcript X n) ≤ Real.exp A := by
    calc
      _ ≤ Real.exp (∑ t ∈ Finset.range n,
          forcedAmount select w (π.transcript X t)) := by
        simpa only [abs_forcedWager] using
          capital_le_exp_sum (forcedWager select w) (forcedWager_bound select w hw') π X n
      _ ≤ _ := Real.exp_le_exp.mpr hsum_le
  rw [capital_eq_fair_mul_forced select]
  exact mul_le_mul ((hB n).trans (le_max_right _ _)) hG
    (capital_nonneg _ (forcedWager_bound select w hw') _) (le_max_left _ _)

/-- Reconstructing a capital process from its own wagers recovers the original
values, including branches whose capital reaches zero. -/
theorem capital_wager_eq (d : CapitalProcess) (v : List Bool) :
    capital d.wager v = d.value v := by
  induction v using List.reverseRecOn with
  | nil => simp [d.initial]
  | append_singleton v b ih =>
    rw [capital_snoc, ih]
    by_cases hz : d.value v = 0
    · rw [d.successor_eq_zero v hz b, hz]
      simp
    · have hp : 0 < d.value v := lt_of_le_of_ne (d.nonneg v) (Ne.symm hz)
      rw [d.update v hp b]
      cases b <;> simp [answerSign]

/-- The criterion applied directly to an existing fair capital process. -/
theorem ae_bounded_process (μ : Measure Cantor) [IsProbabilityMeasure μ]
    (π : ScanRule) (select : List Bool → Bool) (d : CapitalProcess)
    (hw : ∀ v, |d.wager v| ≤ (1 / 2 : ℝ)) (hfair : FairLaw μ π select)
    (hforced : ∀ᵐ X ∂μ,
      Summable (fun n => forcedAmount select d.wager (π.transcript X n))) :
    ∀ᵐ X ∂μ, ∃ B : ℝ, ∀ n, d.value (π.transcript X n) ≤ B := by
  simpa only [capital_wager_eq] using ae_bounded_capital μ π select d.wager hw hfair hforced

end Klr.FairForced

namespace Klr

open MeasureTheory

/-- A strategy fails almost surely when its selected steps are fair and its
remaining absolute wagers are almost surely summable. -/
theorem BettingStrategy.ae_not_succeeds_of_fair_forced (s : BettingStrategy)
    (μ : Measure Cantor) [IsProbabilityMeasure μ] (select : List Bool → Bool)
    (hw : ∀ v, |s.capital.wager v| ≤ (1 / 2 : ℝ))
    (hfair : FairForced.FairLaw μ s.scan select)
    (hforced : ∀ᵐ X ∂μ,
      Summable (fun n => FairForced.forcedAmount select s.capital.wager (s.scan.transcript X n))) :
    ∀ᵐ X ∂μ, ¬ s.Succeeds X := by
  filter_upwards [FairForced.ae_bounded_process μ s.scan select s.capital hw hfair hforced]
    with X hX
  obtain ⟨B, hB⟩ := hX
  intro hs
  obtain ⟨n, hn⟩ := hs B
  exact (not_lt_of_ge (hB n)) hn

end Klr
