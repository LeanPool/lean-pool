/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

-- Modified for Lean Pool.

module

public import LeanPool.KLRandomness.PartialBetting
public import LeanPool.KLRandomness.ComputableRational
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Capital preservation by the partial-strategy scheduler

Each parity simulator places exactly the source bets on its active parity and
has zero wager on every other query.  Its capital at the stage corresponding to
source stage `n` is therefore the product of the source returns on that parity.
The two parity products multiply to the original capital, so an unbounded
source capital makes at least one total simulator unbounded.
-/

@[expose] public section

namespace Klr.PartialBetting

open Klr.RationalComputability

/-- Decode and legalize a rational wager.  On an already legal source wager
the clipping has no effect. -/
def fraction (a : Action) : ℚ :=
  max (-1) (min 1 ((a.2.1 : ℚ) / (a.2.2 : ℚ)))

theorem neg_one_le_fraction (a : Action) : -1 ≤ fraction a := le_max_left _ _

theorem fraction_le_one (a : Action) : fraction a ≤ 1 := by
  exact max_le (by norm_num) (min_le_left _ _)

theorem fraction_eq_of_legal (a : Action)
    (h : |(a.2.1 : ℚ) / (a.2.2 : ℚ)| ≤ 1) :
    fraction a = (a.2.1 : ℚ) / (a.2.2 : ℚ) := by
  obtain ⟨hl, hu⟩ := abs_le.mp h
  simp [fraction, min_eq_right hu, max_eq_right hl]

/-- The actual stake.  Cached actions and inactive queries have zero wager. -/
def wager (c : Nat.Partrec.Code) (side : Bool) (s : State) : ℚ :=
  match approximate c s.1 s.2.2 with
  | none => 0
  | some a => match lookup a.1 s.2.1 with
    | some _ => 0
    | none => if a.1.bodd = side then fraction a else 0

theorem wager_bounds (c : Nat.Partrec.Code) (side : Bool) (s : State) :
    -1 ≤ wager c side s ∧ wager c side s ≤ 1 := by
  unfold wager
  split
  · norm_num
  · split
    · norm_num
    · split
      · exact ⟨neg_one_le_fraction _, fraction_le_one _⟩
      · norm_num

/-- The multiplicative capital return from one binary wager. -/
def factor (w : ℚ) (b : Bool) : ℚ := 1 + (if b then 1 else -1) * w

theorem factor_nonneg {w : ℚ} (hw : -1 ≤ w ∧ w ≤ 1) (b : Bool) :
    0 ≤ factor w b := by
  cases b <;> simp [factor] <;> linarith

theorem factor_false_add_true (w : ℚ) : factor w false + factor w true = 2 := by
  simp only [factor, Bool.false_eq_true, ite_false, ite_true]
  ring

/-- Advance the simulation and update the rational capital for one answer. -/
def accountStep (c : Nat.Partrec.Code) (side : Bool)
    (p : State × ℚ) (b : Bool) : State × ℚ :=
  (advance c side p.1 b, p.2 * factor (wager c side p.1) b)

/-- The simulation state and capital after a finite answer transcript. -/
def account (c : Nat.Partrec.Code) (side : Bool) (v : List Bool) : State × ℚ :=
  v.foldl (accountStep c side) (initial, 1)

/-- Exact rational capital of the selected parity simulator. -/
def rationalCapital (c : Nat.Partrec.Code) (side : Bool) (v : List Bool) : ℚ :=
  (account c side v).2

@[simp] theorem account_snoc (c : Nat.Partrec.Code) (side : Bool)
    (v : List Bool) (b : Bool) :
    account c side (v ++ [b]) = accountStep c side (account c side v) b := by
  simp [account, List.foldl_append]

theorem account_state (c : Nat.Partrec.Code) (side : Bool) (v : List Bool) :
    (account c side v).1 = state c side v := by
  induction v using List.reverseRecOn with
  | nil => rfl
  | append_singleton v b ih => simp [accountStep, ih]

@[simp] theorem rationalCapital_nil (c : Nat.Partrec.Code) (side : Bool) :
    rationalCapital c side [] = 1 := rfl

theorem rationalCapital_snoc (c : Nat.Partrec.Code) (side : Bool)
    (v : List Bool) (b : Bool) :
    rationalCapital c side (v ++ [b]) =
      rationalCapital c side v * factor (wager c side (state c side v)) b := by
  simp [rationalCapital, accountStep, account_state]

theorem rationalCapital_nonneg (c : Nat.Partrec.Code) (side : Bool) (v : List Bool) :
    0 ≤ rationalCapital c side v := by
  induction v using List.reverseRecOn with
  | nil => norm_num
  | append_singleton v b ih =>
    rw [rationalCapital_snoc]
    exact mul_nonneg ih (factor_nonneg (wager_bounds c side _) b)

theorem rationalCapital_fair (c : Nat.Partrec.Code) (side : Bool) (v : List Bool) :
    rationalCapital c side (v ++ [false]) + rationalCapital c side (v ++ [true]) =
      2 * rationalCapital c side v := by
  rw [rationalCapital_snoc, rationalCapital_snoc, ← mul_add, factor_false_add_true]
  ring

/-- The total simulator's nonnegative fair capital process. -/
def capital (c : Nat.Partrec.Code) (side : Bool) : CapitalProcess where
  value v := (rationalCapital c side v : ℝ)
  initial := by simp
  nonneg v := Rat.cast_nonneg.mpr (rationalCapital_nonneg c side v)
  fair v := by exact_mod_cast rationalCapital_fair c side v

/-- Rational capital along the actual simulator run. -/
def runCapital (c : Nat.Partrec.Code) (side : Bool) (X : Cantor) (n : ℕ) : ℚ :=
  rationalCapital c side ((scan c side).transcript X n)

@[simp] theorem runCapital_zero (c : Nat.Partrec.Code) (side : Bool) (X : Cantor) :
    runCapital c side X 0 = 1 := rfl

theorem runCapital_succ (c : Nat.Partrec.Code) (side : Bool) (X : Cantor) (n : ℕ) :
    runCapital c side X (n + 1) = runCapital c side X n *
      factor (wager c side (run c side X n)) (X (query c side (run c side X n))) := by
  simp only [runCapital, ScanRule.transcript_succ, rationalCapital_snoc]
  rfl

/-- The source return factor on the chosen parity and one on the other parity. -/
def selectedFactor (side : Bool) (a : Action) (b : Bool) : ℚ :=
  if a.1.bodd = side then factor (fraction a) b else 1

theorem selectedFactor_nonneg (side : Bool) (a : Action) (b : Bool) :
    0 ≤ selectedFactor side a b := by
  unfold selectedFactor
  split
  · exact factor_nonneg ⟨neg_one_le_fraction _, fraction_le_one _⟩ _
  · norm_num

theorem selectedFactor_mul (a : Action) (b : Bool) :
    selectedFactor false a b * selectedFactor true a b = factor (fraction a) b := by
  unfold selectedFactor
  cases a.1.bodd <;> simp

theorem ready_factor (c : Nat.Partrec.Code) (side : Bool) (X : Cantor) (s : State)
    (hcovered : ActiveCovered side s) {a : Action}
    (ha : approximate c s.1 s.2.2 = some a)
    (hfresh : ∀ d, (a.1, d) ∉ s.1) :
    factor (wager c side s) (X (query c side s)) = selectedFactor side a (X a.1) := by
  by_cases hs : a.1.bodd = side
  · have hl : lookup a.1 s.2.1 = none := by
      apply (lookup_eq_none_iff _ _).mpr
      intro b hb
      obtain ⟨d, hd⟩ := hcovered _ _ hb hs
      exact hfresh d hd
    simp [wager, query, ha, hl, selectedFactor, hs]
  · cases hl : lookup a.1 s.2.1 <;>
      simp [wager, query, ha, hl, selectedFactor, hs, factor]

/-- A source step is completed with exactly its active-parity capital factor.
Waiting and replay add no capital changes. -/
theorem completes_next_capital (c : Nat.Partrec.Code) (side : Bool) (X : Cantor)
    (n budget : ℕ) {a : Action}
    (h : approximate c (run c side X n).1 ((run c side X n).2.2 + budget) = some a)
    (hfresh : ∀ d, (a.1, d) ∉ (run c side X n).1) :
    ∃ m, n < m ∧
      (run c side X m).1 = (run c side X n).1 ++ [(a.1, X a.1)] ∧
      runCapital c side X m = runCapital c side X n * selectedFactor side a (X a.1) := by
  induction budget generalizing n with
  | zero =>
    have ha : approximate c (run c side X n).1 (run c side X n).2.2 = some a := by
      simpa using h
    refine ⟨n + 1, by omega, ?_, ?_⟩
    · rw [run_succ]
      exact advance_original_ready c side X _ (run_cache_correct c side X n) ha
    · rw [runCapital_succ]
      exact congrArg (fun z => runCapital c side X n * z)
        (ready_factor c side X _ (activeCovered_state c side _) ha hfresh)
  | succ budget ih =>
    cases hp : approximate c (run c side X n).1 (run c side X n).2.2 with
    | none =>
      have hw : run c side X (n + 1) =
          ((run c side X n).1,
            (query c side (run c side X n), X (query c side (run c side X n))) ::
              (run c side X n).2.1,
            (run c side X n).2.2 + 1) := by
        rw [run_succ]
        simp [advance, hp]
      have hn : approximate c (run c side X (n + 1)).1
          ((run c side X (n + 1)).2.2 + budget) = some a := by
        simpa only [hw, Nat.add_assoc, Nat.add_comm 1 budget] using h
      have hfn : ∀ d, (a.1, d) ∉ (run c side X (n + 1)).1 := by
        simpa only [hw] using hfresh
      have hc : runCapital c side X (n + 1) = runCapital c side X n := by
        simp [runCapital_succ, wager, hp, factor]
      obtain ⟨m, hm, hnext, hcap⟩ := ih (n + 1) hn hfn
      exact ⟨m, by omega, by simpa only [hw] using hnext, by simpa only [hc] using hcap⟩
    | some b =>
      have hab := approximate_unique c _ hp h
      subst b
      refine ⟨n + 1, by omega, ?_, ?_⟩
      · rw [run_succ]
        exact advance_original_ready c side X _ (run_cache_correct c side X n) hp
      · rw [runCapital_succ]
        exact congrArg (fun z => runCapital c side X n * z)
          (ready_factor c side X _ (activeCovered_state c side _) hp hfresh)

/-- The product of all source return factors through the given time. -/
def sourceCapital {c : Nat.Partrec.Code} {X : Cantor} (r : SourceRun c X) (n : ℕ) : ℚ :=
  ∏ i ∈ Finset.range n, factor (fraction (r.action i)) (X (r.action i).1)

/-- The product of the source return factors on positions of the given parity. -/
def parityCapital {c : Nat.Partrec.Code} {X : Cantor}
    (side : Bool) (r : SourceRun c X) (n : ℕ) : ℚ :=
  ∏ i ∈ Finset.range n, selectedFactor side (r.action i) (X (r.action i).1)

@[simp] theorem parityCapital_zero {c : Nat.Partrec.Code} {X : Cantor}
    (side : Bool) (r : SourceRun c X) : parityCapital side r 0 = 1 := by
  simp [parityCapital]

theorem parityCapital_succ {c : Nat.Partrec.Code} {X : Cantor}
    (side : Bool) (r : SourceRun c X) (n : ℕ) :
    parityCapital side r (n + 1) = parityCapital side r n *
      selectedFactor side (r.action n) (X (r.action n).1) := by
  simp [parityCapital, Finset.prod_range_succ]

theorem parityCapital_nonneg {c : Nat.Partrec.Code} {X : Cantor}
    (side : Bool) (r : SourceRun c X) (n : ℕ) : 0 ≤ parityCapital side r n :=
  Finset.prod_nonneg fun _ _ => selectedFactor_nonneg _ _ _

theorem sourceCapital_eq_mul {c : Nat.Partrec.Code} {X : Cantor}
    (r : SourceRun c X) (n : ℕ) :
    sourceCapital r n = parityCapital false r n * parityCapital true r n := by
  simp only [sourceCapital, parityCapital, ← Finset.prod_mul_distrib, selectedFactor_mul]

theorem source_fresh {c : Nat.Partrec.Code} {X : Cantor}
    (r : SourceRun c X) (n : ℕ) (b : Bool) :
    ((r.action n).1, b) ∉ sourceAssignment r.action X n := by
  intro h
  obtain ⟨i, hi, he⟩ := List.mem_map.mp h
  have hi' := List.mem_range.mp hi
  have hpos : (r.action i).1 = (r.action n).1 := congrArg (fun p : ℕ × Bool => p.1) he
  have he' : i = n := r.fresh hpos
  omega

/-- Exact capital simulation, at a possibly much later genuine-query stage.
Both the assignment and the capital agree with the corresponding parity run. -/
theorem reaches_source_capital (c : Nat.Partrec.Code) (side : Bool) (X : Cantor)
    (r : SourceRun c X) (n : ℕ) :
    ∃ m, (run c side X m).1 = sourceAssignment r.action X n ∧
      runCapital c side X m = parityCapital side r n := by
  induction n with
  | zero => exact ⟨0, rfl, by simp⟩
  | succ n ih =>
    obtain ⟨m, hm, hcap⟩ := ih
    obtain ⟨t, ht⟩ := r.halts n
    have ha : approximate c (run c side X m).1 ((run c side X m).2.2 + t) =
        some (r.action n) := by
      rw [hm]
      exact approximate_mono c _ (Nat.le_add_left t _) ht
    have hfresh : ∀ d, ((r.action n).1, d) ∉ (run c side X m).1 := by
      simpa only [hm] using source_fresh r n
    obtain ⟨j, _, hj, hjcap⟩ := completes_next_capital c side X m t ha hfresh
    refine ⟨j, by simpa [hm] using hj, ?_⟩
    simpa [hcap, parityCapital_succ] using hjcap

/-- Unbounded capital for an infinite run of a partial rational program. -/
def SourceRun.Succeeds {c : Nat.Partrec.Code} {X : Cantor} (r : SourceRun c X) : Prop :=
  ∀ bound : ℝ, ∃ n, bound < (sourceCapital r n : ℝ)

theorem unbounded_parity {c : Nat.Partrec.Code} {X : Cantor}
    (r : SourceRun c X) (hr : r.Succeeds) :
    (∀ bound : ℝ, ∃ n, bound < (parityCapital false r n : ℝ)) ∨
    (∀ bound : ℝ, ∃ n, bound < (parityCapital true r n : ℝ)) := by
  by_contra! h
  obtain ⟨⟨A, hA⟩, ⟨B, hB⟩⟩ := h
  obtain ⟨n, hn⟩ := hr (max 0 A * max 0 B)
  have hprod : (parityCapital false r n : ℝ) * (parityCapital true r n : ℝ) ≤
      max 0 A * max 0 B := by
    apply mul_le_mul ((hA n).trans (le_max_right _ _)) ((hB n).trans (le_max_right _ _))
    · exact_mod_cast parityCapital_nonneg true r n
    · exact le_max_left _ _
  have heq : (sourceCapital r n : ℝ) =
      (parityCapital false r n : ℝ) * (parityCapital true r n : ℝ) := by
    exact_mod_cast sourceCapital_eq_mul r n
  rw [← heq] at hprod
  exact (not_lt_of_ge hprod) hn

/-- The two fixed total schedulers cover the success of every infinite fresh
rational-wager run of the source program. -/
theorem unbounded_simulator {c : Nat.Partrec.Code} {X : Cantor}
    (r : SourceRun c X) (hr : r.Succeeds) :
    ∃ side : Bool, ∀ bound : ℝ, ∃ n, bound < (runCapital c side X n : ℝ) := by
  obtain h | h := unbounded_parity r hr
  · refine ⟨false, fun bound => ?_⟩
    obtain ⟨n, hn⟩ := h bound
    obtain ⟨m, _, hm⟩ := reaches_source_capital c false X r n
    exact ⟨m, by simpa only [hm] using hn⟩
  · refine ⟨true, fun bound => ?_⟩
    obtain ⟨n, hn⟩ := h bound
    obtain ⟨m, _, hm⟩ := reaches_source_capital c true X r n
    exact ⟨m, by simpa only [hm] using hn⟩

theorem primrec_fraction : Primrec fraction :=
  primrec_rat_max.comp (Primrec.const (-1))
    (primrec_rat_min.comp (Primrec.const 1)
      (primrec_rat_div.comp (primrec_rat_intCast.comp (Primrec.fst.comp Primrec.snd))
        (primrec_rat_natCast.comp (Primrec.snd.comp Primrec.snd))))

theorem primrec_wager (c : Nat.Partrec.Code) (side : Bool) : Primrec (wager c side) := by
  have hplan : Primrec (fun s : State => approximate c s.1 s.2.2) :=
    (primrec_approximate c).comp Primrec.fst (Primrec.snd.comp Primrec.snd)
  have hbet : Primrec (fun p : State × Action =>
      if p.2.1.bodd = side then fraction p.2 else 0) :=
    Primrec.ite (Primrec.eq.comp
      (Primrec.nat_bodd.comp (Primrec.fst.comp Primrec.snd)) (Primrec.const side))
      (primrec_fraction.comp Primrec.snd) (Primrec.const 0)
  have hready : Primrec (fun p : State × Action =>
      match lookup p.2.1 p.1.2.1 with
      | some _ => 0
      | none => if p.2.1.bodd = side then fraction p.2 else 0) := by
    apply (Primrec.option_casesOn
      (primrec_lookup.comp (Primrec.fst.comp Primrec.snd)
        (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)))
      hbet (Primrec.const 0).to₂).of_eq
    intro p
    cases lookup p.2.1 p.1.2.1 <;> rfl
  apply (Primrec.option_casesOn hplan (Primrec.const 0) hready.to₂).of_eq
  intro s
  unfold wager
  cases approximate c s.1 s.2.2 <;> rfl

theorem primrec_factor : Primrec₂ factor :=
  primrec_rat_add.comp (Primrec.const 1)
    (primrec_rat_mul.comp ((Primrec.dom_bool fun b => if b then (1 : ℚ) else -1).comp
      Primrec.snd) Primrec.fst)

theorem primrec_accountStep (c : Nat.Partrec.Code) (side : Bool) :
    Primrec₂ (accountStep c side) :=
  ((primrec_advance c side).comp (Primrec.fst.comp Primrec.fst) Primrec.snd).pair
    (primrec_rat_mul.comp (Primrec.snd.comp Primrec.fst)
      (primrec_factor.comp ((primrec_wager c side).comp (Primrec.fst.comp Primrec.fst))
        Primrec.snd))

theorem primrec_account (c : Nat.Partrec.Code) (side : Bool) :
    Primrec (account c side) :=
  Primrec.list_foldl Primrec.id (Primrec.const (initial, (1 : ℚ)))
    ((primrec_accountStep c side).comp (Primrec.fst.comp Primrec.snd)
      (Primrec.snd.comp Primrec.snd)).to₂

theorem primrec_rationalCapital (c : Nat.Partrec.Code) (side : Bool) :
    Primrec (rationalCapital c side) :=
  Primrec.snd.comp (primrec_account c side)

/-- The totalized strategy in the repository's original computable-real
interface.  Its query and its rational capital are both primitive recursive. -/
def strategy (c : Nat.Partrec.Code) (side : Bool) : BettingStrategy where
  scan := scan c side
  capital := capital c side
  computable_capital := computableRealCapital_of_rat (primrec_rationalCapital c side).to_comp

/-- Merkle's two-simulator reduction for partial rational-wager programs.
The pair of total primitive-recursive simulators depends only on the program,
and covers its success on every input admitting an infinite fresh source run. -/
theorem two_total_strategies_cover {c : Nat.Partrec.Code} {X : Cantor}
    (r : SourceRun c X) (hr : r.Succeeds) :
    (strategy c false).Succeeds X ∨ (strategy c true).Succeeds X := by
  obtain ⟨side, h⟩ := unbounded_simulator r hr
  have hs : (strategy c side).Succeeds X := h
  cases side
  · exact Or.inl hs
  · exact Or.inr hs

/-- Total KL randomness rules out every successful infinite fresh run of a
partial rational-wager program. -/
theorem no_partial_rational_success {X : Cantor} (hX : KolmogorovLovelandRandom X)
    {c : Nat.Partrec.Code} (r : SourceRun c X) : ¬ r.Succeeds := by
  intro hr
  rcases two_total_strategies_cover r hr with h | h
  · exact hX (strategy c false) h
  · exact hX (strategy c true) h

end Klr.PartialBetting
