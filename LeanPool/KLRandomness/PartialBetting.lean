/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

-- Modified for Lean Pool.

module

public import LeanPool.KLRandomness.Betting
public import Mathlib.Computability.PartrecCode
public import Mathlib.Computability.Primrec.List
public import Mathlib.Data.Nat.Bits

/-!
# A total fresh-query scheduler for partial KL programs

A partial program receives the previously completed answers and returns a query
position and a rational wager.  The scheduler spends one bounded-computation
stage per outward query.  While waiting, it reads a fresh position in the parity
on which it never wagers.  Previously read answers are cached: if the simulated
program subsequently requests one, that answer is replayed without a second
query.  Each outward query is fresh, including when the program diverges.

The even/odd splitting argument is Merkle's totalization construction, described
in Bienvenu's thesis, Remark 1.7.7.  The cached-answer replay is made explicit
here because a nonmonotonic scan is not allowed to read a position twice.
-/

@[expose] public section

namespace Klr.PartialBetting

/-- A program output: position, signed numerator, and natural denominator.
The wager is clipped to `[-1,1]` so every program code defines legal bets. -/
abbrev Action := ℕ × (ℤ × ℕ)

/-- A finite assignment, recorded in the order in which its answers were read. -/
abbrev Assignment := List (ℕ × Bool)

/-- Completed simulated queries, actual observed queries, and a computation
budget for the next simulated action.  The actual observations are cached in
reverse order; the simulated assignment is in chronological order. -/
abbrev State := Assignment × (Assignment × ℕ)

/-- The scheduler state before any queries or program evaluation. -/
def initial : State := ([], [], 0)

/-- The ordinary partial recursive action described by a program code. -/
def partialAction (c : Nat.Partrec.Code) (v : List Bool) : Part Action :=
  (c.eval (Encodable.encode v)).map (Denumerable.ofNat Action)

theorem exists_partialAction (f : List Bool → Part Action) (hf : Partrec f) :
    ∃ c : Nat.Partrec.Code, ∀ v, partialAction c v = f v := by
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.mp hf
  refine ⟨c, fun v => ?_⟩
  have hdecode : Denumerable.ofNat Action ∘ Encodable.encode = @id Action := by
    funext a
    exact Denumerable.ofNat_encode a
  simp only [partialAction, hc, Encodable.encodek, Part.coe_some, Part.bind_some,
    Part.map_map, hdecode]
  exact Part.map_id' (fun _ => rfl) _

/-- Run the source program for a bounded time on the cached answer transcript. -/
def approximate (c : Nat.Partrec.Code) (v : Assignment) (t : ℕ) : Option Action :=
  (c.evaln t (Encodable.encode (v.map Prod.snd))).map (Denumerable.ofNat Action)

theorem approximate_complete (c : Nat.Partrec.Code) (v : Assignment) (a : Action) :
    a ∈ partialAction c (v.map Prod.snd) ↔ ∃ t, approximate c v t = some a := by
  rw [partialAction, Part.mem_map_iff]
  constructor
  · rintro ⟨k, hk, rfl⟩
    obtain ⟨t, ht⟩ := Nat.Partrec.Code.evaln_complete.mp hk
    exact ⟨t, Option.map_eq_some_iff.mpr ⟨k, ht, rfl⟩⟩
  · rintro ⟨t, ht⟩
    obtain ⟨k, hk, ha⟩ := Option.map_eq_some_iff.mp ht
    exact ⟨k, Nat.Partrec.Code.evaln_sound hk, ha⟩

theorem approximate_mono (c : Nat.Partrec.Code) (v : Assignment)
    {s t : ℕ} {a : Action} (hst : s ≤ t) (h : approximate c v s = some a) :
    approximate c v t = some a := by
  obtain ⟨k, hk, rfl⟩ := Option.map_eq_some_iff.mp h
  exact Option.map_eq_some_iff.mpr
    ⟨k, Nat.Partrec.Code.evaln_mono hst hk, rfl⟩

theorem approximate_unique (c : Nat.Partrec.Code) (v : Assignment)
    {s t : ℕ} {a b : Action} (ha : approximate c v s = some a)
    (hb : approximate c v t = some b) : a = b := by
  have ha' := approximate_mono c v (Nat.le_max_left s t) ha
  have hb' := approximate_mono c v (Nat.le_max_right s t) hb
  exact Option.some.inj (ha'.symm.trans hb')

/-- Look up an already observed answer. -/
def lookup (q : ℕ) : Assignment → Option Bool
  | [] => none
  | (p, b) :: xs => if q = p then some b else lookup q xs

@[simp] theorem lookup_nil (q : ℕ) : lookup q [] = none := rfl

@[simp] theorem lookup_cons (q p : ℕ) (b : Bool) (xs : Assignment) :
    lookup q ((p, b) :: xs) = if q = p then some b else lookup q xs := rfl

theorem lookup_eq_none_iff (q : ℕ) (xs : Assignment) :
    lookup q xs = none ↔ ∀ b, (q, b) ∉ xs := by
  induction xs with
  | nil => simp
  | cons p xs ih =>
    rcases p with ⟨p, b⟩
    by_cases h : q = p
    · subst p
      constructor
      · intro h
        simp at h
      · intro h
        exact False.elim (h b (by simp))
    · simp [h, ih]

theorem mem_of_lookup_eq_some {q : ℕ} {b : Bool} {xs : Assignment}
    (h : lookup q xs = some b) : (q, b) ∈ xs := by
  induction xs with
  | nil => simp at h
  | cons p xs ih =>
    rcases p with ⟨p, d⟩
    by_cases hp : q = p
    · simp [hp] at h
      subst p
      subst d
      simp
    · simp only [lookup_cons, hp, ite_false] at h
      exact List.mem_cons_of_mem _ (ih h)

/-- A convenient strict upper bound on every coordinate in an assignment. -/
def bound : Assignment → ℕ
  | [] => 0
  | (q, _) :: xs => q + bound xs + 1

theorem lt_bound_of_mem {q : ℕ} {b : Bool} {xs : Assignment}
    (h : (q, b) ∈ xs) : q < bound xs := by
  induction xs with
  | nil => simp at h
  | cons p xs ih =>
    rcases p with ⟨p, d⟩
    simp only [List.mem_cons, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | h
    · simp [bound]
    · have := ih h
      simp only [bound]
      omega

/-- `side = false` means wagering only at even coordinates. -/
def filler (side : Bool) (xs : Assignment) : ℕ :=
  2 * bound xs + if side then 0 else 1

@[simp] theorem bodd_filler (side : Bool) (xs : Assignment) :
    (filler side xs).bodd = !side := by
  cases side <;> simp [filler]

theorem filler_not_mem (side : Bool) (xs : Assignment) (b : Bool) :
    (filler side xs, b) ∉ xs := by
  intro h
  have := lt_bound_of_mem h
  cases side <;> simp only [filler, Bool.false_eq_true, ite_false, ite_true] at this <;>
    omega

/-- The next genuine query.  A ready action is queried only if its answer is
not already cached; all other cases consume a fresh inactive coordinate. -/
def query (c : Nat.Partrec.Code) (side : Bool) (s : State) : ℕ :=
  match approximate c s.1 s.2.2 with
  | none => filler side s.2.1
  | some a => match lookup a.1 s.2.1 with
    | none => a.1
    | some _ => filler side s.2.1

/-- Consume one outward answer and perform at most one simulated action. -/
def advance (c : Nat.Partrec.Code) (side : Bool) (s : State) (b : Bool) : State :=
  let observed := (query c side s, b) :: s.2.1
  match approximate c s.1 s.2.2 with
  | none => (s.1, observed, s.2.2 + 1)
  | some a => (s.1 ++ [(a.1, (lookup a.1 s.2.1).getD b)], observed, 0)

/-- The scheduler state after processing a finite transcript of actual answers. -/
def state (c : Nat.Partrec.Code) (side : Bool) (v : List Bool) : State :=
  v.foldl (advance c side) initial

@[simp] theorem state_nil (c : Nat.Partrec.Code) (side : Bool) :
    state c side [] = initial := rfl

@[simp] theorem state_snoc (c : Nat.Partrec.Code) (side : Bool)
    (v : List Bool) (b : Bool) :
    state c side (v ++ [b]) = advance c side (state c side v) b := by
  simp [state, List.foldl_append]

@[simp] theorem advance_observed (c : Nat.Partrec.Code) (side : Bool)
    (s : State) (b : Bool) :
    (advance c side s b).2.1 = (query c side s, b) :: s.2.1 := by
  simp only [advance]
  split <;> rfl

theorem query_not_mem (c : Nat.Partrec.Code) (side : Bool)
    (s : State) (b : Bool) : (query c side s, b) ∉ s.2.1 := by
  unfold query
  split
  · exact filler_not_mem side _ b
  · split
    · exact (lookup_eq_none_iff _ _).mp ‹_› b
    · exact filler_not_mem side _ b

theorem previous_query_mem (c : Nat.Partrec.Code) (side : Bool)
    (v : List Bool) (n : ℕ) (hn : n < v.length) :
    ∃ b, (query c side (state c side (v.take n)), b) ∈ (state c side v).2.1 := by
  induction v using List.reverseRecOn with
  | nil => simp at hn
  | append_singleton v b ih =>
    simp only [List.length_append, List.length_singleton] at hn
    rw [state_snoc, advance_observed]
    rcases lt_or_eq_of_le (Nat.le_of_lt_succ hn) with h | rfl
    · obtain ⟨d, hd⟩ := ih h
      exact ⟨d, List.mem_cons_of_mem _ (by simpa [List.take_append_of_le_length h.le] using hd)⟩
    · exact ⟨b, by simp⟩

theorem primrec_approximate (c : Nat.Partrec.Code) : Primrec₂ (approximate c) := by
  have hv : Primrec (fun p : Assignment × ℕ => p.1.map Prod.snd) :=
    Primrec.list_map Primrec.fst (Primrec.snd.comp Primrec.snd).to₂
  exact (Primrec.option_map
    (Nat.Partrec.Code.primrec_evaln.comp
      ((Primrec.snd.pair (Primrec.const c)).pair (Primrec.encode.comp hv)))
    ((Primrec.ofNat Action).comp Primrec.snd).to₂).to₂

theorem primrec_lookup : Primrec₂ lookup := by
  have h := Primrec.list_foldr (β := ℕ × Bool) (σ := Option Bool)
    (α := ℕ × Assignment) Primrec.snd (Primrec.const none)
    (Primrec.ite
      (Primrec.eq.comp (Primrec.fst.comp Primrec.fst)
        (Primrec.fst.comp (Primrec.fst.comp Primrec.snd)))
      (Primrec.option_some.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.snd)))
      (Primrec.snd.comp Primrec.snd)).to₂
  apply h.of_eq
  rintro ⟨q, xs⟩
  induction xs with
  | nil => rfl
  | cons p xs ih => simp [lookup, ih]

theorem primrec_bound : Primrec bound := by
  have h := Primrec.list_foldr (β := ℕ × Bool) (σ := ℕ)
    (α := Assignment) Primrec.id (Primrec.const 0)
    (Primrec.succ.comp (Primrec.nat_add.comp
      (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd))).to₂
  apply h.of_eq
  intro xs
  induction xs with
  | nil => rfl
  | cons p xs ih =>
    dsimp only at ih
    simp only [bound]
    exact congrArg (fun n => p.1 + n + 1) ih

theorem primrec_filler (side : Bool) : Primrec (filler side) :=
  Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2) primrec_bound)
    (Primrec.const (if side then 0 else 1))

theorem primrec_query (c : Nat.Partrec.Code) (side : Bool) :
    Primrec (query c side) := by
  have hplan : Primrec (fun s : State => approximate c s.1 s.2.2) :=
    (primrec_approximate c).comp Primrec.fst (Primrec.snd.comp Primrec.snd)
  have hfill : Primrec (fun s : State => filler side s.2.1) :=
    (primrec_filler side).comp (Primrec.fst.comp Primrec.snd)
  have hready : Primrec (fun p : State × Action =>
      match lookup p.2.1 p.1.2.1 with
      | none => p.2.1
      | some _ => filler side p.1.2.1) :=
    by
    apply (Primrec.option_casesOn
      (primrec_lookup.comp (Primrec.fst.comp Primrec.snd)
        (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)))
      (Primrec.fst.comp Primrec.snd)
      (hfill.comp (Primrec.fst.comp Primrec.fst)).to₂).of_eq
    intro p
    cases lookup p.2.1 p.1.2.1 <;> rfl
  apply (Primrec.option_casesOn hplan hfill hready.to₂).of_eq
  intro s
  unfold query
  cases approximate c s.1 s.2.2 <;> rfl

theorem primrec_advance (c : Nat.Partrec.Code) (side : Bool) :
    Primrec₂ (advance c side) := by
  have hquery : Primrec (fun p : State × Bool => query c side p.1) :=
    (primrec_query c side).comp Primrec.fst
  have hcache : Primrec (fun p : State × Bool =>
      (query c side p.1, p.2) :: p.1.2.1) :=
    Primrec.list_cons.comp (hquery.pair Primrec.snd)
      (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
  have hplan : Primrec (fun p : State × Bool => approximate c p.1.1 p.1.2.2) :=
    (primrec_approximate c).comp (Primrec.fst.comp Primrec.fst)
      (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
  have hwait : Primrec (fun p : State × Bool =>
      (p.1.1, (query c side p.1, p.2) :: p.1.2.1, p.1.2.2 + 1)) :=
    (Primrec.fst.comp Primrec.fst).pair
      (hcache.pair (Primrec.succ.comp
        (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))))
  have hanswer : Primrec (fun p : (State × Bool) × Action =>
      (lookup p.2.1 p.1.1.2.1).getD p.1.2) :=
    Primrec.option_getD.comp
      (primrec_lookup.comp (Primrec.fst.comp Primrec.snd)
        (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))))
      (Primrec.snd.comp Primrec.fst)
  have hready : Primrec (fun p : (State × Bool) × Action =>
      (p.1.1.1 ++ [(p.2.1, (lookup p.2.1 p.1.1.2.1).getD p.1.2)],
        (query c side p.1.1, p.1.2) :: p.1.1.2.1, 0)) :=
    (Primrec.list_concat.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
      ((Primrec.fst.comp Primrec.snd).pair hanswer)).pair
      ((hcache.comp Primrec.fst).pair (Primrec.const 0))
  apply (Primrec.option_casesOn hplan hwait hready.to₂).of_eq
  intro p
  unfold advance
  cases approximate c p.1.1 p.1.2.2 <;> rfl

theorem primrec_state (c : Nat.Partrec.Code) (side : Bool) :
    Primrec (state c side) :=
  Primrec.list_foldl Primrec.id (Primrec.const initial)
    ((primrec_advance c side).comp (Primrec.fst.comp Primrec.snd)
      (Primrec.snd.comp Primrec.snd)).to₂

/-- The simulator's scan is total, primitive recursive, and fresh on every
transcript, whether or not the partial program halts. -/
def scan (c : Nat.Partrec.Code) (side : Bool) : ScanRule where
  query v := query c side (state c side v)
  computable_query := ((primrec_query c side).comp (primrec_state c side)).to_comp
  fresh v n hn := by
    obtain ⟨b, hb⟩ := previous_query_mem c side v n hn
    intro h
    rw [h] at hb
    exact query_not_mem c side (state c side v) b hb

/-- Every active observation has already been supplied to the simulated
program.  Inactive filler observations need not have been supplied yet. -/
def ActiveCovered (side : Bool) (s : State) : Prop :=
  ∀ q b, (q, b) ∈ s.2.1 → q.bodd = side → ∃ d, (q, d) ∈ s.1

theorem mem_original_advance (c : Nat.Partrec.Code) (side : Bool)
    (s : State) (b : Bool) {p : ℕ × Bool} (hp : p ∈ s.1) :
    p ∈ (advance c side s b).1 := by
  unfold advance
  split
  · exact hp
  · exact List.mem_append_left _ hp

theorem active_query_ready (c : Nat.Partrec.Code) (side : Bool) (s : State)
    (hactive : (query c side s).bodd = side) :
    ∃ a, approximate c s.1 s.2.2 = some a ∧
      lookup a.1 s.2.1 = none ∧ query c side s = a.1 := by
  cases hp : approximate c s.1 s.2.2 with
  | none =>
    simp [query, hp] at hactive
  | some a =>
    cases hl : lookup a.1 s.2.1 with
    | none => exact ⟨a, rfl, hl, by simp [query, hp, hl]⟩
    | some d =>
      simp [query, hp, hl] at hactive

theorem activeCovered_advance (c : Nat.Partrec.Code) (side : Bool)
    (s : State) (b : Bool) (h : ActiveCovered side s) :
    ActiveCovered side (advance c side s b) := by
  intro q d hmem hactive
  rw [advance_observed] at hmem
  rcases List.mem_cons.mp hmem with heq | hmem
  · have hq : q = query c side s := congrArg Prod.fst heq
    subst q
    obtain ⟨a, ha, hl, hq⟩ := active_query_ready c side s hactive
    refine ⟨b, ?_⟩
    simp [advance, ha, hl, hq]
  · obtain ⟨e, he⟩ := h q d hmem hactive
    exact ⟨e, mem_original_advance c side s b he⟩

theorem activeCovered_state (c : Nat.Partrec.Code) (side : Bool) (v : List Bool) :
    ActiveCovered side (state c side v) := by
  induction v using List.reverseRecOn with
  | nil => simp [state, initial, ActiveCovered]
  | append_singleton v b ih =>
    rw [state_snoc]
    exact activeCovered_advance c side _ b ih

/-- The concrete simulator state after `n` genuine observations of `X`. -/
def run (c : Nat.Partrec.Code) (side : Bool) (X : Cantor) (n : ℕ) : State :=
  state c side ((scan c side).transcript X n)

@[simp] theorem run_zero (c : Nat.Partrec.Code) (side : Bool) (X : Cantor) :
    run c side X 0 = initial := rfl

theorem run_succ (c : Nat.Partrec.Code) (side : Bool) (X : Cantor) (n : ℕ) :
    run c side X (n + 1) =
      advance c side (run c side X n) (X (query c side (run c side X n))) := by
  simp only [run, ScanRule.transcript_succ, state_snoc]
  rfl

/-- All cached answers are the actual input bits. -/
theorem run_cache_correct (c : Nat.Partrec.Code) (side : Bool) (X : Cantor)
    (n : ℕ) : ∀ q b, (q, b) ∈ (run c side X n).2.1 → b = X q := by
  induction n with
  | zero => simp [initial]
  | succ n ih =>
    intro q b h
    rw [run_succ, advance_observed] at h
    rcases List.mem_cons.mp h with heq | h
    · exact (congrArg Prod.snd heq).trans (congrArg X (congrArg Prod.fst heq).symm)
    · exact ih q b h

theorem advance_original_ready (c : Nat.Partrec.Code) (side : Bool) (X : Cantor)
    (s : State) (hcache : ∀ q b, (q, b) ∈ s.2.1 → b = X q)
    {a : Action} (ha : approximate c s.1 s.2.2 = some a) :
    (advance c side s (X (query c side s))).1 = s.1 ++ [(a.1, X a.1)] := by
  cases hl : lookup a.1 s.2.1 with
  | none => simp [advance, query, ha, hl]
  | some b =>
    have hb := hcache a.1 b (mem_of_lookup_eq_some hl)
    simp [advance, ha, hl, hb]

/-- A completed partial computation is eventually acted upon.  This theorem
allows arbitrarily long waits, cached-answer replay, and arbitrary intervening
inactive observations. -/
theorem completes_next (c : Nat.Partrec.Code) (side : Bool) (X : Cantor)
    (n budget : ℕ) {a : Action}
    (h : approximate c (run c side X n).1 ((run c side X n).2.2 + budget) = some a) :
    ∃ m, n < m ∧ (run c side X m).1 = (run c side X n).1 ++ [(a.1, X a.1)] := by
  induction budget generalizing n with
  | zero =>
    have ha : approximate c (run c side X n).1 (run c side X n).2.2 = some a := by
      simpa using h
    refine ⟨n + 1, by omega, ?_⟩
    rw [run_succ]
    exact advance_original_ready c side X _ (run_cache_correct c side X n) ha
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
      obtain ⟨m, hm, hnext⟩ := ih (n + 1) hn
      exact ⟨m, by omega, by simpa only [hw] using hnext⟩
    | some b =>
      have hab := approximate_unique c _ hp h
      subst b
      refine ⟨n + 1, by omega, ?_⟩
      rw [run_succ]
      exact advance_original_ready c side X _ (run_cache_correct c side X n) hp

/-- The first `n` assignments of a proposed source run. -/
def sourceAssignment (a : ℕ → Action) (X : Cantor) (n : ℕ) : Assignment :=
  (List.range n).map fun i => ((a i).1, X (a i).1)

@[simp] theorem sourceAssignment_zero (a : ℕ → Action) (X : Cantor) :
    sourceAssignment a X 0 = [] := rfl

@[simp] theorem sourceAssignment_succ (a : ℕ → Action) (X : Cantor) (n : ℕ) :
    sourceAssignment a X (n + 1) = sourceAssignment a X n ++ [((a n).1, X (a n).1)] := by
  simp [sourceAssignment, List.range_succ]

/-- An infinite fresh run of a partial rational betting program on an input.
The program need not halt away from this input. -/
structure SourceRun (c : Nat.Partrec.Code) (X : Cantor) where
  /-- The successive query positions and rational wagers of this source run. -/
  action : ℕ → Action
  halts : ∀ n, ∃ t, approximate c (sourceAssignment action X n) t = some (action n)
  fresh : Function.Injective (fun n => (action n).1)

/-- Every finite stage of an infinite source run is reached by each of the
two total simulators.  Thus divergence on other inputs causes no difficulty. -/
theorem reaches_source_stage (c : Nat.Partrec.Code) (side : Bool) (X : Cantor)
    (r : SourceRun c X) (n : ℕ) :
    ∃ m, (run c side X m).1 = sourceAssignment r.action X n := by
  induction n with
  | zero => exact ⟨0, rfl⟩
  | succ n ih =>
    obtain ⟨m, hm⟩ := ih
    obtain ⟨t, ht⟩ := r.halts n
    have ha : approximate c (run c side X m).1 ((run c side X m).2.2 + t) =
        some (r.action n) := by
      rw [hm]
      exact approximate_mono c _ (Nat.le_add_left t _) ht
    obtain ⟨j, _, hj⟩ := completes_next c side X m t ha
    exact ⟨j, by simpa [hm] using hj⟩

end Klr.PartialBetting
