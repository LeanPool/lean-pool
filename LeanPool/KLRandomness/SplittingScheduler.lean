/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

-- Modified for Lean Pool.

module

public import LeanPool.KLRandomness.PartialBettingCapital
public import LeanPool.KLRandomness.EffectiveNormalization
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Scheduling finite-oracle rational bets on the two coordinate halves

The scheduler reads an initial segment of each half. While the next target
bet is not ready, it reads the next oracle bit with zero wager. A ready bet
reads the next target bit. Thus every query is fresh and eventual readiness
ensures that every target bit is eventually read. The existing partial-program
totalization theorem converts success of this explicit run into failure of KL
randomness.
-/

@[expose] public section

namespace Klr.SplittingScheduler

open RationalComputability

/-- Position of the next bit in the parity subsequence on which the program wagers. -/
def targetPos (side : Bool) (n : ℕ) : ℕ := 2 * n + if side then 1 else 0
/-- Position of the next bit in the parity subsequence used as an oracle. -/
def oraclePos (side : Bool) (n : ℕ) : ℕ := 2 * n + if side then 0 else 1

/-- `side = false` bets on the even half and uses the odd half as oracle. -/
def target (side : Bool) (X : Cantor) : Cantor := fun n => X (targetPos side n)
/-- The half of the input used as the oracle. -/
def oracle (side : Bool) (X : Cantor) : Cantor := fun n => X (oraclePos side n)

/-- The cached oracle prefix, target prefix and current capital. -/
abbrev State := List Bool × (List Bool × ℚ)

/-- The state with empty prefixes and initial capital one. -/
def initial : State := ([], [], 1)

/-- Read the next target bit if the readiness test passes, or the next oracle bit otherwise. -/
def query (side : Bool) (ready : List Bool → ℕ → Bool) (s : State) : ℕ :=
  bif ready s.1 s.2.1.length then targetPos side s.2.1.length else oraclePos side s.1.length

/-- The fraction staked on a target query, with no stake on an oracle query. -/
def requested (ready : List Bool → ℕ → Bool) (bet : List Bool → List Bool → ℚ)
    (s : State) : ℚ :=
  bif ready s.1 s.2.1.length then bet s.1 s.2.1 / s.2.2 else 0

/-- The next query position and encoded rational wager. -/
def action (side : Bool) (ready : List Bool → ℕ → Bool)
    (bet : List Bool → List Bool → ℚ) (s : State) : PartialBetting.Action :=
  (query side ready s, (requested ready bet s).num, (requested ready bet s).den)

/-- Update the appropriate cached prefix and capital after an answer. -/
def advance (side : Bool) (ready : List Bool → ℕ → Bool)
    (bet : List Bool → List Bool → ℚ) (s : State) (d : Bool) : State :=
  let capital := s.2.2 * PartialBetting.factor (PartialBetting.fraction (action side ready bet s)) d
  bif ready s.1 s.2.1.length then (s.1, s.2.1 ++ [d], capital)
    else (s.1 ++ [d], s.2.1, capital)

theorem advance_capital (side : Bool) (ready : List Bool → ℕ → Bool)
    (bet : List Bool → List Bool → ℚ) (s : State) (d : Bool) :
    (advance side ready bet s d).2.2 =
      s.2.2 * PartialBetting.factor (PartialBetting.fraction (action side ready bet s)) d := by
  unfold advance
  cases ready s.1 s.2.1.length <;> rfl

theorem fraction_action (side : Bool) (ready : List Bool → ℕ → Bool)
    (bet : List Bool → List Bool → ℚ) (s : State) (h : |requested ready bet s| ≤ 1) :
    PartialBetting.fraction (action side ready bet s) = requested ready bet s := by
  have hr := PartialBetting.fraction_eq_of_legal (action side ready bet s)
    (by simpa only [action, Rat.num_div_den] using h)
  simpa only [action, Rat.num_div_den] using hr

/-- Replay a finite answer string, with a bounded recursion on its length. -/
def stateAux (side : Bool) (ready : List Bool → ℕ → Bool)
    (bet : List Bool → List Bool → ℚ) (v : List Bool) : ℕ → State
  | 0 => initial
  | n + 1 => advance side ready bet (stateAux side ready bet v n) (v.getD n false)

/-- Replay the scheduler along the given finite sequence of answers. -/
def state (side : Bool) (ready : List Bool → ℕ → Bool)
    (bet : List Bool → List Bool → ℚ) (v : List Bool) : State :=
  stateAux side ready bet v v.length

theorem stateAux_congr (side : Bool) (ready : List Bool → ℕ → Bool)
    (bet : List Bool → List Bool → ℚ) (v w : List Bool) (n : ℕ)
    (h : ∀ i < n, v.getD i false = w.getD i false) :
    stateAux side ready bet v n = stateAux side ready bet w n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [stateAux, stateAux, ih (fun i hi => h i (by omega)), h n (by omega)]

@[simp] theorem state_nil (side : Bool) (ready : List Bool → ℕ → Bool)
    (bet : List Bool → List Bool → ℚ) : state side ready bet [] = initial := rfl

theorem state_snoc (side : Bool) (ready : List Bool → ℕ → Bool)
    (bet : List Bool → List Bool → ℚ) (v : List Bool) (d : Bool) :
    state side ready bet (v ++ [d]) = advance side ready bet (state side ready bet v) d := by
  unfold state
  rw [List.length_append, List.length_singleton, stateAux]
  have h := stateAux_congr side ready bet (v ++ [d]) v v.length (by
    intro i hi
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi])
  rw [h]
  simp [List.getD_eq_getElem?_getD]

theorem computable_query (side : Bool) {ready : List Bool → ℕ → Bool}
    (hr : Computable₂ ready) : Computable (query side ready) := by
  have ho : Computable (fun s : State => s.1.length) :=
    Computable.list_length.comp Computable.fst
  have ht : Computable (fun s : State => s.2.1.length) :=
    Computable.list_length.comp (Computable.fst.comp Computable.snd)
  have hc := hr.comp Computable.fst ht
  exact Computable.cond hc
    (Primrec.nat_add.to_comp.comp (Primrec.nat_mul.to_comp.comp (Computable.const 2) ht)
      (Computable.const (if side then 1 else 0)))
    (Primrec.nat_add.to_comp.comp (Primrec.nat_mul.to_comp.comp (Computable.const 2) ho)
      (Computable.const (if side then 0 else 1)))

theorem computable_requested {ready : List Bool → ℕ → Bool}
    {bet : List Bool → List Bool → ℚ} (hr : Computable₂ ready) (hb : Computable₂ bet) :
    Computable (requested ready bet) := by
  have ht : Computable (fun s : State => s.2.1) := Computable.fst.comp Computable.snd
  exact Computable.cond (hr.comp Computable.fst (Computable.list_length.comp ht))
    (primrec_rat_div.to_comp.comp (hb.comp Computable.fst ht)
      (Computable.snd.comp Computable.snd)) (Computable.const 0)

theorem computable_action (side : Bool) {ready : List Bool → ℕ → Bool}
    {bet : List Bool → List Bool → ℚ} (hr : Computable₂ ready) (hb : Computable₂ bet) :
    Computable (action side ready bet) :=
  (computable_query side hr).pair
    ((primrec_rat_num.to_comp.comp (computable_requested hr hb)).pair
      (primrec_rat_den.to_comp.comp (computable_requested hr hb)))

theorem computable_advance (side : Bool) {ready : List Bool → ℕ → Bool}
    {bet : List Bool → List Bool → ℚ} (hr : Computable₂ ready) (hb : Computable₂ bet) :
    Computable₂ (advance side ready bet) := by
  have ho : Computable (fun p : State × Bool => p.1.1) :=
    Computable.fst.comp Computable.fst
  have ht : Computable (fun p : State × Bool => p.1.2.1) :=
    Computable.fst.comp (Computable.snd.comp Computable.fst)
  have hq : Computable (fun p : State × Bool => p.1.2.2) :=
    Computable.snd.comp (Computable.snd.comp Computable.fst)
  have ha : Computable (fun p : State × Bool => action side ready bet p.1) :=
    (computable_action side hr hb).comp Computable.fst
  have hf := PartialBetting.primrec_factor.to_comp.comp
    (PartialBetting.primrec_fraction.to_comp.comp ha) Computable.snd
  have hcapital := primrec_rat_mul.to_comp.comp hq hf
  exact Computable.cond (hr.comp ho (Computable.list_length.comp ht))
    (ho.pair ((Computable.list_concat.comp ht Computable.snd).pair hcapital))
    ((Computable.list_concat.comp ho Computable.snd).pair (ht.pair hcapital))

theorem computable_state (side : Bool) {ready : List Bool → ℕ → Bool}
    {bet : List Bool → List Bool → ℚ} (hr : Computable₂ ready) (hb : Computable₂ bet) :
    Computable (state side ready bet) := by
  have hs : Computable₂ (fun v : List Bool => fun p : ℕ × State =>
      advance side ready bet p.2 (v.getD p.1 false)) :=
    ((computable_advance side hr hb).comp (Computable.snd.comp Computable.snd)
      ((Primrec.list_getD false).to_comp.comp Computable.fst
        (Computable.fst.comp Computable.snd))).to₂
  apply (Computable.nat_rec Computable.list_length (Computable.const initial) hs).of_eq
  intro v
  change (Nat.rec initial (fun n s => advance side ready bet s (v.getD n false)) v.length) =
    stateAux side ready bet v v.length
  generalize v.length = n
  induction n with
  | zero => rfl
  | succ n ih => simp only [stateAux, ih]

/-- The exact sequence of source states on the actual input. -/
def run (side : Bool) (ready : List Bool → ℕ → Bool)
    (bet : List Bool → List Bool → ℚ) (X : Cantor) : ℕ → State
  | 0 => initial
  | n + 1 => advance side ready bet (run side ready bet X n)
      (X (query side ready (run side ready bet X n)))

private theorem inputPrefix_succ (X : Cantor) (n : ℕ) :
    ScanRule.inputPrefix X (n + 1) = ScanRule.inputPrefix X n ++ [X n] := by
  simp [ScanRule.inputPrefix, List.range_succ]

theorem run_prefixes (side : Bool) (ready : List Bool → ℕ → Bool)
    (bet : List Bool → List Bool → ℚ) (X : Cantor) (n : ℕ) :
    (run side ready bet X n).1 =
      ScanRule.inputPrefix (oracle side X) (run side ready bet X n).1.length ∧
    (run side ready bet X n).2.1 =
      ScanRule.inputPrefix (target side X) (run side ready bet X n).2.1.length := by
  induction n with
  | zero => exact ⟨rfl, rfl⟩
  | succ n ih =>
    cases hr : ready (run side ready bet X n).1 (run side ready bet X n).2.1.length
    · simp only [run, advance, query, hr, Bool.cond_false]
      constructor
      · simpa only [List.length_append, List.length_singleton, inputPrefix_succ, oracle] using
          congrArg (fun v => v ++ [X (oraclePos side (run side ready bet X n).1.length)]) ih.1
      · exact ih.2
    · simp only [run, advance, query, hr, Bool.cond_true]
      constructor
      · exact ih.1
      · simpa only [List.length_append, List.length_singleton, inputPrefix_succ, target] using
          congrArg (fun v => v ++ [X (targetPos side (run side ready bet X n).2.1.length)]) ih.2

theorem oracle_length_mono (side : Bool) (ready : List Bool → ℕ → Bool)
    (bet : List Bool → List Bool → ℚ) (X : Cantor) :
    Monotone (fun n => (run side ready bet X n).1.length) := by
  apply monotone_nat_of_le_succ
  intro n
  simp only [run, advance]
  cases ready (run side ready bet X n).1 (run side ready bet X n).2.1.length <;> simp

theorem target_length_mono (side : Bool) (ready : List Bool → ℕ → Bool)
    (bet : List Bool → List Bool → ℚ) (X : Cantor) :
    Monotone (fun n => (run side ready bet X n).2.1.length) := by
  apply monotone_nat_of_le_succ
  intro n
  simp only [run, advance]
  cases ready (run side ready bet X n).1 (run side ready bet X n).2.1.length <;> simp

theorem query_ne_of_lt (side : Bool) (ready : List Bool → ℕ → Bool)
    (bet : List Bool → List Bool → ℚ) (X : Cantor) {m n : ℕ} (hmn : m < n) :
    query side ready (run side ready bet X m) ≠ query side ready (run side ready bet X n) := by
  have ho := oracle_length_mono side ready bet X (show m + 1 ≤ n by omega)
  have ht := target_length_mono side ready bet X (show m + 1 ≤ n by omega)
  cases hm : ready (run side ready bet X m).1 (run side ready bet X m).2.1.length <;>
    cases hn : ready (run side ready bet X n).1 (run side ready bet X n).2.1.length <;>
    simp only [run, advance, hm, Bool.cond_false, Bool.cond_true,
      List.length_append, List.length_singleton] at ho ht <;>
    simp only [query, hm, hn, Bool.cond_false, Bool.cond_true, targetPos, oraclePos] <;>
    cases side <;> simp only [Bool.false_eq_true, ite_false, ite_true] at * <;> omega

theorem query_injective (side : Bool) (ready : List Bool → ℕ → Bool)
    (bet : List Bool → List Bool → ℚ) (X : Cantor) :
    Function.Injective (fun n => query side ready (run side ready bet X n)) := by
  intro m n h
  rcases lt_trichotomy m n with hmn | rfl | hnm
  · exact False.elim (query_ne_of_lt side ready bet X hmn h)
  · rfl
  · exact False.elim (query_ne_of_lt side ready bet X hnm h.symm)

/-- Every finite prefix of the target half is eventually completed. -/
theorem reaches_target_length (side : Bool) (ready : List Bool → ℕ → Bool)
    (bet : List Bool → List Bool → ℚ) (X : Cantor)
    (hready : ∀ n, ∃ K, ∀ m, K ≤ m →
      ready (ScanRule.inputPrefix (oracle side X) m) n = true) (n : ℕ) :
    ∃ t, (run side ready bet X t).2.1.length = n := by
  have next (t : ℕ) : ∃ u, (run side ready bet X u).2.1.length =
      (run side ready bet X t).2.1.length + 1 := by
    let k := (run side ready bet X t).2.1.length
    obtain ⟨K, hK⟩ := hready k
    have progress : ∀ d t, (run side ready bet X t).2.1.length = k →
        K ≤ (run side ready bet X t).1.length + d →
        ∃ u, (run side ready bet X u).2.1.length = k + 1 := by
      intro d
      induction d with
      | zero =>
        intro t ht hbound
        have hr : ready (run side ready bet X t).1 (run side ready bet X t).2.1.length = true := by
          rw [(run_prefixes side ready bet X t).1, ht]
          exact hK _ (by simpa using hbound)
        refine ⟨t + 1, ?_⟩
        simp only [run, advance, hr, Bool.cond_true, List.length_append, List.length_singleton]
        omega
      | succ d ih =>
        intro t ht hbound
        cases hr : ready (run side ready bet X t).1 (run side ready bet X t).2.1.length
        · apply ih (t + 1)
          · simpa only [run, advance, hr, Bool.cond_false] using ht
          · simpa only [run, advance, hr, Bool.cond_false,
              List.length_append, List.length_singleton, Nat.add_assoc,
              Nat.add_comm 1 d] using hbound
        · refine ⟨t + 1, ?_⟩
          simp only [run, advance, hr, Bool.cond_true, List.length_append, List.length_singleton]
          omega
    exact progress K t rfl (by omega)
  induction n with
  | zero => exact ⟨0, rfl⟩
  | succ n ih =>
    obtain ⟨t, ht⟩ := ih
    obtain ⟨u, hu⟩ := next t
    exact ⟨u, by simpa only [ht] using hu⟩

theorem state_answers_eq_run (side : Bool) (ready : List Bool → ℕ → Bool)
    (bet : List Bool → List Bool → ℚ) (X : Cantor) (n : ℕ) :
    state side ready bet
      (ScanRule.inputPrefix (fun i => X (query side ready (run side ready bet X i))) n) =
      run side ready bet X n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [inputPrefix_succ, state_snoc, ih]; rfl

/-- Compile the scheduler and obtain an infinite fresh run on every input. -/
theorem exists_sourceRun (side : Bool) {ready : List Bool → ℕ → Bool}
    {bet : List Bool → List Bool → ℚ} (hr : Computable₂ ready) (hb : Computable₂ bet)
    (X : Cantor) :
    ∃ c : Nat.Partrec.Code, ∃ r : PartialBetting.SourceRun c X,
      (∀ n, r.action n = action side ready bet (run side ready bet X n)) ∧
      ∀ n, PartialBetting.sourceCapital r n = (run side ready bet X n).2.2 := by
  have hf : Computable (fun v => action side ready bet (state side ready bet v)) :=
    (computable_action side hr hb).comp (computable_state side hr hb)
  obtain ⟨c, hc⟩ := PartialBetting.exists_partialAction _ hf.partrec
  let a : ℕ → PartialBetting.Action := fun n => action side ready bet (run side ready bet X n)
  have hanswers (n : ℕ) :
      (PartialBetting.sourceAssignment a X n).map Prod.snd =
        ScanRule.inputPrefix (fun i => X (query side ready (run side ready bet X i))) n := by
    simp [PartialBetting.sourceAssignment, ScanRule.inputPrefix, List.map_map, a, action]
  let r : PartialBetting.SourceRun c X :=
    { action := a
      halts := fun n => (PartialBetting.approximate_complete c _ _).mp (by
        rw [hanswers, hc]
        change a n ∈ Part.some (action side ready bet (state side ready bet
          (ScanRule.inputPrefix (fun i => X (query side ready (run side ready bet X i))) n)))
        rw [state_answers_eq_run]
        exact Part.mem_some _)
      fresh := query_injective side ready bet X }
  refine ⟨c, r, fun _ => rfl, ?_⟩
  intro n
  induction n with
  | zero => simp [PartialBetting.sourceCapital, run, initial]
  | succ n ih =>
    change (∏ i ∈ Finset.range (n + 1), PartialBetting.factor
      (PartialBetting.fraction (r.action i)) (X (r.action i).1)) = _
    rw [Finset.prod_range_succ]
    change PartialBetting.sourceCapital r n * _ = _
    rw [ih]
    rw [run, advance_capital]
    rfl

/-- Along the actual input, certified additive stakes reproduce the desired capital exactly. -/
theorem run_capital_eq (side : Bool) (ready : List Bool → ℕ → Bool)
    (bet : List Bool → List Bool → ℚ) (X : Cantor) (Q q : List Bool → ℚ)
    (hinit : Q [] = 1) (hpos : ∀ v, 0 < Q v) (hlegal : ∀ v, |q v| ≤ Q v)
    (hstep : ∀ v d, Q (v ++ [d]) = Q v + answerSign d * q v)
    (hbet : ∀ m n, ready (ScanRule.inputPrefix (oracle side X) m) n = true →
      bet (ScanRule.inputPrefix (oracle side X) m) (ScanRule.inputPrefix (target side X) n) =
        q (ScanRule.inputPrefix (target side X) n)) (n : ℕ) :
    (run side ready bet X n).2.2 = Q (run side ready bet X n).2.1 := by
  induction n with
  | zero => exact hinit.symm
  | succ n ih =>
    let s := run side ready bet X n
    have hO : s.1 = ScanRule.inputPrefix (oracle side X) s.1.length :=
      (run_prefixes side ready bet X n).1
    have hT : s.2.1 = ScanRule.inputPrefix (target side X) s.2.1.length :=
      (run_prefixes side ready bet X n).2
    cases hr : ready s.1 s.2.1.length
    · have hw : requested ready bet s = 0 := by simp [requested, hr]
      have hf : PartialBetting.fraction (action side ready bet s) = 0 := by
        rw [fraction_action side ready bet s (by rw [hw]; norm_num), hw]
      change (advance side ready bet s (X (query side ready s))).2.2 =
        Q (advance side ready bet s (X (query side ready s))).2.1
      simp only [advance, hr, Bool.cond_false, hf, PartialBetting.factor,
        mul_zero, add_zero, mul_one]
      exact ih
    · have hb : bet s.1 s.2.1 = q s.2.1 := by
        have hh := hbet s.1.length s.2.1.length (by simpa only [← hO] using hr)
        simpa only [← hO, ← hT] using hh
      have hqpos := hpos s.2.1
      have hqlegal : |q s.2.1 / Q s.2.1| ≤ 1 := by
        rw [abs_div, abs_of_pos hqpos]
        exact (div_le_one hqpos).mpr (hlegal s.2.1)
      have hw : requested ready bet s = q s.2.1 / Q s.2.1 := by
        simp only [requested, hr, Bool.cond_true, hb]
        exact congrArg (fun t => q s.2.1 / t) ih
      have hf : PartialBetting.fraction (action side ready bet s) = q s.2.1 / Q s.2.1 := by
        rw [fraction_action side ready bet s (by rwa [hw]), hw]
      change (advance side ready bet s (X (query side ready s))).2.2 =
        Q (advance side ready bet s (X (query side ready s))).2.1
      simp only [advance, hr, Bool.cond_true, hf]
      rw [hstep]
      change s.2.2 * (1 + answerSign (X (query side ready s)) * (q s.2.1 / Q s.2.1)) = _
      rw [ih]
      field_simp [ne_of_gt hqpos]
      ring

/-- A computable finite-oracle scheduler for a positive unbounded rational capital
contradicts KL randomness in the repository's existing total-strategy convention. -/
theorem not_kolmogorovLovelandRandom_of_bets (side : Bool)
    {ready : List Bool → ℕ → Bool} {bet : List Bool → List Bool → ℚ}
    (hr : Computable₂ ready) (hb : Computable₂ bet) (X : Cantor) (Q q : List Bool → ℚ)
    (hinit : Q [] = 1) (hpos : ∀ v, 0 < Q v) (hlegal : ∀ v, |q v| ≤ Q v)
    (hstep : ∀ v d, Q (v ++ [d]) = Q v + answerSign d * q v)
    (hready : ∀ n, ∃ K, ∀ m, K ≤ m →
      ready (ScanRule.inputPrefix (oracle side X) m) n = true)
    (hbet : ∀ m n, ready (ScanRule.inputPrefix (oracle side X) m) n = true →
      bet (ScanRule.inputPrefix (oracle side X) m) (ScanRule.inputPrefix (target side X) n) =
        q (ScanRule.inputPrefix (target side X) n))
    (hunbounded : ∀ bound : ℝ, ∃ n,
      bound < (Q (ScanRule.inputPrefix (target side X) n) : ℝ)) :
    ¬KolmogorovLovelandRandom X := by
  intro hX
  obtain ⟨c, r, _, hcapital⟩ := exists_sourceRun side hr hb X
  apply PartialBetting.no_partial_rational_success hX r
  intro bound
  obtain ⟨n, hn⟩ := hunbounded bound
  obtain ⟨t, ht⟩ := reaches_target_length side ready bet X hready n
  refine ⟨t, ?_⟩
  rw [hcapital, run_capital_eq side ready bet X Q q hinit hpos hlegal hstep hbet,
    (run_prefixes side ready bet X t).2, ht]
  exact hn

end Klr.SplittingScheduler
