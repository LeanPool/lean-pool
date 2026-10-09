/-
Copyright (c) 2026 Pure Nock formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pure Nock formalization contributors
-/

module

public import LeanPool.PureNock.Verb

/-!
# Evaluation traces

`Def:eval_trace`–`Thm:deterministic_Trace` (`main.tex:1114–1157`).
-/

@[expose] public section

namespace Nock
namespace Verb

/-! ### Trace, consistency, completeness (`Def:eval_trace`, `main.tex:1114–1127`) -/

-- main.tex:1118  (`Nock(tᵢ, tᵢ₊₁) = 0`)
/-- **`Def:eval_trace`** (`main.tex:1118`).
    Consistent step: `Nock(tᵢ, tᵢ₊₁) = 0`. -/
def Step (a b : Verb) : Prop := next a = some b

/-- The transition relation is deterministic: `next` is a function. -/
theorem Step.det {a b b' : Verb} (h : Step a b) (h' : Step a b') : b = b' :=
  Option.some.inj (h.symm.trans h')

-- main.tex:1115–1118  (consistent evaluation trace)
/-- **`Def:eval_trace`** (`main.tex:1114–1127`).
    Consistent: `∀ i ∈ [n], Nock(tᵢ, tᵢ₊₁) = 0`. -/
def Consistent : List Verb → Prop
  | []              => True
  | [_]             => True
  | a :: b :: rest  => Step a b ∧ Consistent (b :: rest)

-- main.tex:1122  (complete: `tₙ` terminal or null)
/-- **`Def:eval_trace`** (`main.tex:1114–1127`).
    Complete: `tₙ` is in terminal state or null. -/
def Complete (T : List Verb) : Prop := ∃ v, T.getLast? = some v ∧ next v = none

-- main.tex:1115–1118  (`t₀ = F` with consistency)
/-- **`Def:eval_trace`** (`main.tex:1114–1127`).
    Consistent trace of `F`: `t₀ = F` and `∀ i ∈ [n], Nock(tᵢ, tᵢ₊₁) = 0`. -/
def TraceOf (F : Verb) (T : List Verb) : Prop := T.head? = some F ∧ Consistent T

-- main.tex:1126  (continuation)
/-- **`Def:eval_trace`** (`main.tex:1114–1127`).
    If `c ∈ T(F)`, `c` is a continuation (of `F`). -/
def Continuation (F c : Verb) : Prop := ∃ T, TraceOf F T ∧ c ∈ T

-- main.tex:1123  (valid)
/-- **`Def:eval_trace`** (`main.tex:1114–1127`).
    Valid: `T` complete and `tₙ` is not null. -/
def Valid (F : Verb) : Prop :=
  ∃ T v, TraceOf F T ∧ T.getLast? = some v ∧ next v = none ∧ isTerminal v = true

-- main.tex:1124  (invalid)
/-- **`Def:eval_trace`** (`main.tex:1114–1127`).
    Invalid: `T` complete and `tₙ` is null. -/
def Invalid (F : Verb) : Prop :=
  ∃ T v, TraceOf F T ∧ T.getLast? = some v ∧ next v = none ∧ isTerminal v = false

-- main.tex:1130–1134  (Def:Nock)
/-- **`Def:Nock`** (`main.tex:1130–1134`).
    `F` terminates (is finite) if `F ∈ NockVM^Λ := {F | ∃ complete T=(t₀,…,tₙ) s.t. t₀=F, λ≤Λ}`. -/
def Finite (F : Verb) : Prop := ∃ T, TraceOf F T ∧ Complete T

-- main.tex:1147  (`FiniteTransitions^Λ`)
/-- **`FiniteTransitions^Λ`** (`main.tex:1147`).
    `FiniteTransitions^Λ := {F | F is a continuation of a finite verb and λ ≤ Λ}`. -/
def FiniteTransition (F : Verb) : Prop :=
  ∃ (F0 : Verb) (T : List Verb), TraceOf F0 T ∧ Complete T ∧ F ∈ T

/-! ### Small list helpers (Lean core only) -/

private theorem head?_some_mem {F : Verb} {T : List Verb}
    (h : T.head? = some F) : F ∈ T := by
  cases T with
  | nil => simp at h
  | cons a t =>
      simp only [List.head?_cons, Option.some.injEq] at h
      subst h; simp

private theorem getLast?_cons₂ (x y : Verb) (t : List Verb) :
    (x :: y :: t).getLast? = (y :: t).getLast? := by
  simp [List.getLast?_cons_cons]

/-- Any element of a consistent trace begins a consistent *suffix* with the same last verb. -/
private theorem consistent_suffix_of_mem {F : Verb} :
    ∀ (T : List Verb), Consistent T → F ∈ T →
      ∃ S, S.head? = some F ∧ Consistent S ∧ S.getLast? = T.getLast? := by
  intro T
  induction T with
  | nil => intro _ hmem; simp at hmem
  | cons a t iht =>
      cases t with
      | nil =>
          intro hc hmem
          simp only [List.mem_singleton] at hmem
          subst hmem
          exact ⟨[F], by simp, hc, rfl⟩
      | cons b t' =>
          intro hc hmem
          obtain ⟨hab, hrest⟩ := hc
          rcases List.mem_cons.1 hmem with hFa | hmem'
          · subst hFa
            exact ⟨F :: b :: t', by simp, ⟨hab, hrest⟩, rfl⟩
          · obtain ⟨S, hS1, hS2, hS3⟩ := iht hrest hmem'
            exact ⟨S, hS1, hS2, hS3.trans (getLast?_cons₂ a b t').symm⟩

/-! ### `Lem:domain` (`main.tex:1141–1142`) -/

-- main.tex:1141–1142  (Lem:domain)
/-- **`Lem:domain`** (`main.tex:1141–1142`).
    Let `c` be a continuation not followed by a null operator in a consistent evaluation
    trace. Then `map(c, getIndex(c)) ∈ D(V)`. -/
theorem domain {c t : Verb} (h : Step c t) :
    ∃ i sub, getIndex c = some i ∧ map i c = some sub ∧ inDomain sub = true := by
  unfold Step next at h
  split at h
  · simp at h
  · rename_i i hg
    split at h
    · simp at h
    · rename_i sub hm
      split at h
      · rename_i hd
        exact ⟨i, sub, hg, hm, hd⟩
      · simp at h

/-! ### `lemma:equiv_continuations` (`main.tex:1150–1153`) -/

-- main.tex:1150–1153  (NockVM^Λ ≡ FiniteTransitions^Λ)
/-- **`lemma:equiv_continuations`** (`main.tex:1150–1153`).
    `NockVM^Λ ≡ FiniteTransitions^Λ`. -/
theorem equiv_continuations (F : Verb) : Finite F ↔ FiniteTransition F := by
  constructor
  · rintro ⟨T, hTof, hComp⟩
    exact ⟨F, T, hTof, hComp, head?_some_mem hTof.1⟩
  · rintro ⟨F0, T, hTof, ⟨v, hlast, hnext⟩, hmem⟩
    obtain ⟨S, hS1, hS2, hS3⟩ := consistent_suffix_of_mem T hTof.2 hmem
    exact ⟨S, ⟨hS1, hS2⟩, ⟨v, hS3.trans hlast, hnext⟩⟩

/-! ### `Thm:deterministic_Trace` (`main.tex:1156–1157`) -/

/-- Inductive core of determinism: `Step` is functional, so equal heads and lengths force equality. -/
theorem trace_unique (T1 : List Verb) : ∀ (T2 : List Verb),
    Consistent T1 → Consistent T2 → T1.head? = T2.head? → T1.length = T2.length → T1 = T2 := by
  induction T1 with
  | nil =>
      intro T2 _ _ _ hl
      cases T2 with
      | nil => rfl
      | cons _ _ => simp at hl
  | cons a t1 ih =>
      intro T2 h1 h2 hh hl
      cases T2 with
      | nil => simp at hl
      | cons c t2 =>
          have hac : a = c := by
            simp only [List.head?_cons, Option.some.injEq] at hh; exact hh
          subst hac
          cases t1 with
          | nil =>
              cases t2 with
              | nil => rfl
              | cons _ _ => simp at hl
          | cons b t1' =>
              cases t2 with
              | nil => simp at hl
              | cons d t2' =>
                  simp only [Consistent] at h1 h2
                  obtain ⟨hab, hbt⟩ := h1
                  obtain ⟨had, hdt⟩ := h2
                  have hbd : b = d := Step.det hab had
                  subst hbd
                  have hrec : (b :: t1') = (b :: t2') :=
                    ih (b :: t2') hbt hdt (by simp)
                      (by simp only [List.length_cons] at hl ⊢; omega)
                  exact congrArg (a :: ·) hrec

-- main.tex:1156–1157  (Thm:deterministic_Trace — functional form)
/-- **`Thm:deterministic_Trace`** (`main.tex:1156–1157`).
    If `map` enforces a strict ordering on finite verbs, then for every finite verb `F` and
    integer `n`, there exists at most one consistent evaluation trace of size `n` for `F`. -/
theorem deterministic_Trace {F : Verb} {n : Nat} {T1 T2 : List Verb}
    (h1 : TraceOf F T1) (h2 : TraceOf F T2)
    (hn1 : T1.length = n + 1) (hn2 : T2.length = n + 1) : T1 = T2 :=
  trace_unique T1 T2 h1.2 h2.2 (h1.1.trans h2.1.symm) (by omega)

/-! ### Conditional deterministic-trace theorem (`main.tex:1156–1157`) -/

/-- Consistency of a trace with respect to an arbitrary transition relation `R`
    (`Consistent` is the special case `R = Step`). -/
def ConsistentR (R : Verb → Verb → Prop) : List Verb → Prop
  | []             => True
  | [_]            => True
  | a :: b :: rest => R a b ∧ ConsistentR R (b :: rest)

/-- Trace uniqueness for **any deterministic** transition relation.  Determinism of the
    relation is the only hypothesis; this is the inductive core shared by the functional and
    the strict-order forms. -/
theorem trace_unique_of_det {R : Verb → Verb → Prop}
    (hdet : ∀ {a b b' : Verb}, R a b → R a b' → b = b') :
    ∀ (T1 T2 : List Verb), ConsistentR R T1 → ConsistentR R T2 →
      T1.head? = T2.head? → T1.length = T2.length → T1 = T2 := by
  intro T1
  induction T1 with
  | nil =>
      intro T2 _ _ _ hl
      cases T2 with
      | nil => rfl
      | cons _ _ => simp at hl
  | cons a t1 ih =>
      intro T2 h1 h2 hh hl
      cases T2 with
      | nil => simp at hl
      | cons c t2 =>
          have hac : a = c := by
            simp only [List.head?_cons, Option.some.injEq] at hh; exact hh
          subst hac
          cases t1 with
          | nil =>
              cases t2 with
              | nil => rfl
              | cons _ _ => simp at hl
          | cons b t1' =>
              cases t2 with
              | nil => simp at hl
              | cons d t2' =>
                  simp only [ConsistentR] at h1 h2
                  obtain ⟨hab, hbt⟩ := h1
                  obtain ⟨had, hdt⟩ := h2
                  have hbd : b = d := hdet hab had
                  subst hbd
                  have hrec : (b :: t1') = (b :: t2') :=
                    ih (b :: t2') hbt hdt (by simp)
                      (by simp only [List.length_cons] at hl ⊢; omega)
                  exact congrArg (a :: ·) hrec

/-- A trace w.r.t. an arbitrary transition relation `R` (generalizing `TraceOf`). -/
def TraceOfR (R : Verb → Verb → Prop) (F : Verb) (T : List Verb) : Prop :=
  T.head? = some F ∧ ConsistentR R T

-- main.tex:1156–1157  (Thm:deterministic_Trace — conditional form)
/-- **`Thm:deterministic_Trace`** (`main.tex:1156–1157`).
    If `map` enforces a strict ordering on finite verbs, then for every finite verb `F` and
    integer `n`, there exists at most one consistent evaluation trace of size `n` for `F`. -/
theorem selStep_deterministic_Trace {lt : Nat → Nat → Prop} (hs : StrictSelect lt)
    {F : Verb} {n : Nat} {T1 T2 : List Verb}
    (h1 : TraceOfR (SelStep lt) F T1) (h2 : TraceOfR (SelStep lt) F T2)
    (hn1 : T1.length = n + 1) (hn2 : T2.length = n + 1) : T1 = T2 :=
  trace_unique_of_det (R := SelStep lt)
    (fun {a b b'} (hab : SelStep lt a b) (hab' : SelStep lt a b') => SelStep.det hs hab hab')
    T1 T2 h1.2 h2.2 (h1.1.trans h2.1.symm) (by omega)

/-- The concrete consistency (`Consistent`, via `next`) is exactly `SelStep dfsLt`
    consistency, because `next` realizes the DFS selection step (`next_eq_some_iff`). -/
theorem consistent_iff_selStep : ∀ (T : List Verb),
    Consistent T ↔ ConsistentR (SelStep dfsLt) T
  | []             => Iff.rfl
  | [_]            => Iff.rfl
  | a :: b :: rest => by
      simp only [Consistent, ConsistentR]
      exact and_congr next_eq_some_iff (consistent_iff_selStep (b :: rest))

-- main.tex:1156–1157  (Thm:deterministic_Trace — DFS instance)
/-- **`Thm:deterministic_Trace`** (`main.tex:1156–1157`).
    If `map` enforces a strict ordering on finite verbs, then for every finite verb `F` and
    integer `n`, there exists at most one consistent evaluation trace of size `n` for `F`. -/
theorem deterministic_Trace_strict {F : Verb} {n : Nat} {T1 T2 : List Verb}
    (h1 : TraceOf F T1) (h2 : TraceOf F T2)
    (hn1 : T1.length = n + 1) (hn2 : T2.length = n + 1) : T1 = T2 :=
  selStep_deterministic_Trace strictSelect_dfs
    ⟨h1.1, (consistent_iff_selStep T1).1 h1.2⟩
    ⟨h2.1, (consistent_iff_selStep T2).1 h2.2⟩ hn1 hn2

/-! ### Corollary: valid and invalid verbs are finite (`main.tex:1137–1138`) -/

-- main.tex:1137–1138  (Corr)
/-- **`Corr`** (`main.tex:1137–1138`).
    All valid and invalid verbs are finite. -/
theorem finite_of_valid {F : Verb} (h : Valid F) : Finite F := by
  obtain ⟨T, v, hT, hl, hn, _⟩ := h
  exact ⟨T, hT, v, hl, hn⟩

-- main.tex:1137–1138  (Corr)
/-- **`Corr`** (`main.tex:1137–1138`).
    All valid and invalid verbs are finite. -/
theorem finite_of_invalid {F : Verb} (h : Invalid F) : Finite F := by
  obtain ⟨T, v, hT, hl, hn, _⟩ := h
  exact ⟨T, hT, v, hl, hn⟩

-- main.tex:1137–1138  (Corr)
/-- **`Corr`** (`main.tex:1137–1138`).
    All valid and invalid verbs are finite. -/
theorem finite_of_valid_or_invalid {F : Verb} (h : Valid F ∨ Invalid F) : Finite F :=
  h.elim finite_of_valid finite_of_invalid

/-! ### Size bound `λ ≤ Λ` on paper languages (`main.tex:1130–1147`) -/

-- main.tex:1164  (`λ = len(n) = |d|`)
/-- The paper's length `λ` of a verb: the number of leaves of its noun. -/
def size (F : Verb) : Nat := F.leaves

-- main.tex:1130–1134  (`NockVM^Λ`)
/-- **`Def:Nock`** (`main.tex:1130–1134`).
    `NockVM^Λ := {F ∈ V^λ | ∃ complete T with t₀=F, and λ ≤ Λ}`. -/
def FiniteΛ (Λ : Nat) (F : Verb) : Prop := Finite F ∧ size F ≤ Λ

-- main.tex:1147  (`FiniteTransitions^Λ`)
/-- **`FiniteTransitions^Λ`** (`main.tex:1147`).
    `FiniteTransitions^Λ := {F | F is a continuation of a finite verb and λ ≤ Λ}`. -/
def FiniteTransitionΛ (Λ : Nat) (F : Verb) : Prop := FiniteTransition F ∧ size F ≤ Λ

-- main.tex:1150–1153  (`NockVM^Λ ≡ FiniteTransitions^Λ`)
/-- **`lemma:equiv_continuations`** (`main.tex:1150–1153`).
    `NockVM^Λ ≡ FiniteTransitions^Λ`. -/
theorem equiv_continuationsΛ (Λ : Nat) (F : Verb) : FiniteΛ Λ F ↔ FiniteTransitionΛ Λ F :=
  and_congr (equiv_continuations F) Iff.rfl

/-! ### `NockProgram^Λ` / `NockValidProgram^Λ` (`main.tex:1090–1149`) -/

-- main.tex:1090–1098  (Def:NockProgram)
/-- **`Def:NockProgram`** (`main.tex:1090–1098`).
    `F = *[subject, formula]` with subject, formula terminal; `NockProgram^Λ := {F | λ ≤ Λ}`. -/
def IsNockProgram (Λ : Nat) (F : Verb) : Prop :=
  (∃ subject formula, F = .node .star subject formula
      ∧ isTerminal subject = true ∧ isTerminal formula = true)
    ∧ size F ≤ Λ

-- main.tex:1145  (`NockValidProgram^Λ := {F ∈ NockProgram^Λ | F is a valid verb}`)
/-- **`F ∈ NockValidProgram^Λ`** (main.tex:1145): a Nock program that is a *valid* verb. -/
def NockValidProgramΛ (Λ : Nat) (F : Verb) : Prop := IsNockProgram Λ F ∧ Valid F

/-- Subset of verb-languages (`⊆`): every verb in `P` is in `Q`. -/
def SubLang (P Q : Verb → Prop) : Prop := ∀ ⦃F⦄, P F → Q F

/-- **Strict inclusion of verb-languages (`⊊`)**: `P ⊆ Q` together with a witness in `Q ∖ P`.
    This is exactly the meaning of the set-theoretic `⊊` (proper subset = subset + a strictly
    separating element), spelled out at the predicate level. -/
def SSubLang (P Q : Verb → Prop) : Prop := SubLang P Q ∧ ∃ F, Q F ∧ ¬ P F

/-- A terminal leaf is finite: its one-element trace `[leaf n]` is complete. -/
theorem finite_leaf (n : Nat) : Finite (.leaf n) :=
  ⟨[.leaf n], ⟨rfl, trivial⟩, .leaf n, rfl, next_none_of_terminal rfl⟩

-- main.tex:1145  (`NockValidProgram^Λ ⊊ NockVM^Λ`)
/-- **Strict inclusion (main.tex:1145).**  `NockValidProgram^Λ ⊊ NockVM^Λ`: every valid program
    is finite of length `≤ Λ` (`⊆`, via `finite_of_valid`), and the containment is *strict* —
    e.g. the terminal leaf `0` is a finite verb of length `1 ≤ Λ` that is **not** a Nock program
    (it is not of the form `*[subject, formula]`; main.tex:1145 "not all elements of `NockVM^Λ`
    are actually programs").  The side condition `1 ≤ Λ` is *necessary*: for `Λ = 0` both
    languages are empty (every verb has `≥ 1` leaf), so `∅ ⊊ ∅` fails; the paper's `⊊` is meant
    for the non-degenerate range. -/
theorem nockValidProgram_ssubset_nockVM {Λ : Nat} (hΛ : 1 ≤ Λ) :
    SSubLang (NockValidProgramΛ Λ) (FiniteΛ Λ) := by
  refine ⟨?_, .leaf 0, ⟨finite_leaf 0, ?_⟩, ?_⟩
  · intro F hF
    exact ⟨finite_of_valid hF.2, hF.1.2⟩
  · show size (.leaf 0) ≤ Λ
    simpa [size, leaves] using hΛ
  · rintro ⟨⟨⟨s, f, hEq, _, _⟩, _⟩, _⟩
    simp at hEq

/-! ### `NockVMROM^Λ` at the verb level (main.tex:1160) -/

-- main.tex:1160  (a single consistent ROM transition)
/-- A single `NockVMROM` step (`next` restricted to exclude `OP₁₀`). -/
def StepROM (a b : Verb) : Prop := nextROM a = some b

/-- Every ROM step is a Nock step (`nextROM ⊆ next`; main.tex:1160). -/
theorem step_of_stepROM {a b : Verb} (h : StepROM a b) : Step a b := next_of_nextROM h

-- main.tex:1160  (ROM completeness: `tₙ` has no ROM successor)
/-- A trace is **ROM-complete** iff its last verb has no `nextROM`-successor. -/
def CompleteROM (T : List Verb) : Prop := ∃ v, T.getLast? = some v ∧ nextROM v = none

-- main.tex:1160  (a consistent ROM trace of `F`)
/-- `T` is a consistent ROM trace of `F` (uses `StepROM` for consistency). -/
def TraceOfROM (F : Verb) (T : List Verb) : Prop := T.head? = some F ∧ ConsistentR StepROM T

/-- Every consistent ROM trace is a consistent Nock trace (ROM steps are Nock steps). -/
theorem consistent_of_consistentROM : ∀ (T : List Verb), ConsistentR StepROM T → Consistent T
  | [],            _ => trivial
  | [_],           _ => trivial
  | _ :: _ :: rest, h => ⟨step_of_stepROM h.1, consistent_of_consistentROM (_ :: rest) h.2⟩

/-- Every ROM trace of `F` is a Nock trace of `F`. -/
theorem traceOf_of_traceOfROM {F : Verb} {T : List Verb} (h : TraceOfROM F T) : TraceOf F T :=
  ⟨h.1, consistent_of_consistentROM T h.2⟩

-- main.tex:1160  (`NockVMROM`: verbs with a complete ROM trace)
/-- `F` is **ROM-finite** (`F ∈ NockVMROM`): it has a complete ROM trace. -/
def FiniteROM (F : Verb) : Prop := ∃ T, TraceOfROM F T ∧ CompleteROM T

-- main.tex:1160 + 1130-1133  (`NockVMROM^Λ`: ROM-finite verbs of length `λ ≤ Λ`)
/-- `F ∈ NockVMROM^Λ`: ROM-finite *and* of length `λ ≤ Λ` (Def:Nock without `OP₁₀`). -/
def FiniteROMΛ (Λ : Nat) (F : Verb) : Prop := FiniteROM F ∧ size F ≤ Λ

-- main.tex:1123,1160  (a ROM-*valid* verb: ROM-complete trace ending in terminal state)
/-- `F` is **ROM-valid**: it has a complete ROM trace ending in a terminal (non-crash) verb. -/
def ValidROM (F : Verb) : Prop :=
  ∃ T v, TraceOfROM F T ∧ T.getLast? = some v ∧ nextROM v = none ∧ isTerminal v = true

/-- **ROM-valid ⇒ finite.**  A verb that terminates in a terminal state using only ROM steps
    is Nock-finite: its ROM trace is a Nock trace (`traceOf_of_traceOfROM`), and its terminal
    last verb has no Nock successor either (`next_none_of_terminal`), so the trace is
    Nock-complete. -/
theorem finite_of_validROM {F : Verb} (h : ValidROM F) : Finite F := by
  obtain ⟨T, v, hT, hl, _, hterm⟩ := h
  exact ⟨T, traceOf_of_traceOfROM hT, v, hl, next_none_of_terminal hterm⟩

/-! ### The two-verb checker `Nock` matches `Step` (App A, main.tex:1639) -/

-- main.tex:1118,1639  (`Nock(tᵢ,tᵢ₊₁)=0` ⟺ `Step` ∨ crash: the checker is 1-1 with `Step`)
/-- **`Nock` checker ⟺ trace consistency (`Step`) + crash.**  `NockCheck a b = true` (paper's
    accept `0`, main.tex:1118) iff `b` is a `Step`-successor of `a` (`Step a v`, i.e. a
    consistent transition `Nock(a,v)=0`) or `a` crashes and `b = ⊥` (`b = none`).  This is the
    genuine biconditional making the two-verb checker 1-1 with the forward semantics `Step`
    plus the crash branch (defeq to `Verb.nockCheck_eq_true_iff`, since `Step a v := next a =
    some v`). -/
theorem nockCheck_iff_step {a : Verb} {b : Option Verb} :
    NockCheck a b = true ↔ (∃ v, b = some v ∧ Step a v) ∨ (b = none ∧ Crashes a) :=
  nockCheck_eq_true_iff

/-! ### Verifiable crash ⟺ the paper's ⊥ (`Invalid`, `main.tex:1124`)

`Nock.Verb.eval` reports a three-way `Outcome`; a `crash` result is tied here to the paper's
program-level ⊥: the *evaluated* program `v` is `Invalid` — its trace is complete and ends at a
stuck, non-terminal state (`main.tex:1124`).  Soundness (`eval_crash_invalid`), completeness
(`eval_crash_complete`), and their biconditional (`eval_crash_iff_invalid`) pin `eval`'s crash to
exactly that object; `eval_crash_checked` further exhibits the reached ⊥ state and its
`NockCheck`-accepted crash edge. -/

-- main.tex:1114–1127  (a crash trace: consistent, ending stuck non-terminal, length = fuel)
/-- If `S` is a consistent trace of `u` (head `u`, `Consistent S`) whose last state `w` is a stuck
    non-terminal (`next w = none`, `¬terminal`), then `eval` reports a `crash` at fuel `S.length`. -/
theorem crash_of_trace :
    ∀ (S : List Verb) (u w : Verb),
      S.head? = some u → Consistent S → S.getLast? = some w →
      next w = none → isTerminal w = false → eval S.length u = .crash
  | [], u, w, h, _, _, _, _ => by simp at h
  | [a], u, w, hh, _, hl, hnext, hnt => by
      simp only [List.head?_cons, Option.some.injEq] at hh
      simp only [List.getLast?_singleton, Option.some.injEq] at hl
      subst hh; subst hl
      show eval 1 a = .crash
      rw [eval_succ, hnext, haltOutcome_crash hnt]
  | a :: b :: rest, u, w, hh, hc, hl, hnext, hnt => by
      simp only [List.head?_cons, Option.some.injEq] at hh
      subst hh
      obtain ⟨hstep, hcrest⟩ := hc
      have hlrest : (b :: rest).getLast? = some w := by
        rw [List.getLast?_cons_cons] at hl; exact hl
      have ih := crash_of_trace (b :: rest) b w rfl hcrest hlrest hnext hnt
      show eval ((b :: rest).length + 1) a = .crash
      rw [eval_succ, (hstep : next a = some b)]
      exact ih

-- main.tex:1124  (`Invalid`: complete trace ending in the null state ⊥)
/-- **Crash soundness (program-tied).**  A `crash` reported by `eval` for the program `v` means `v`
    is `Invalid`: its evaluation trace is complete and ends at a stuck non-terminal — the paper's ⊥
    (`main.tex:1124`).  Unlike a bare "some crashing verb exists", the witness is the trace *of `v`*. -/
theorem eval_crash_invalid {n : Nat} {v : Verb} (h : eval n v = .crash) : Invalid v := by
  induction n generalizing v with
  | zero => simp [eval] at h
  | succ n ih =>
      rw [eval_succ] at h
      cases hnv : next v with
      | some v' =>
          simp only [hnv] at h
          obtain ⟨T, w, hTr, hlast, hnext, hnt⟩ := ih h
          refine ⟨v :: T, w, ?_, ?_, hnext, hnt⟩
          · refine ⟨rfl, ?_⟩
            obtain ⟨hhead, hcons⟩ := hTr
            cases T with
            | nil => simp at hhead
            | cons a t =>
                simp only [List.head?_cons, Option.some.injEq] at hhead
                subst hhead
                exact ⟨hnv, hcons⟩
          · obtain ⟨hhead, _⟩ := hTr
            cases T with
            | nil => simp at hhead
            | cons a t => simp [List.getLast?_cons_cons] at hlast ⊢; exact hlast
      | none =>
          simp only [hnv, haltOutcome] at h
          have hnt : v.isTerminal = false := by
            by_cases ht : v.isTerminal
            · rw [if_pos ht] at h; exact Outcome.noConfusion h
            · simpa using ht
          exact ⟨[v], v, ⟨rfl, trivial⟩, rfl, hnv, hnt⟩

-- main.tex:1124  (converse: every `Invalid` program is reported as a crash)
/-- **Crash completeness.**  Every `Invalid` program (complete trace ending stuck non-terminal,
    `main.tex:1124`) is eventually reported as a `crash` by `eval` — at fuel = its trace length. -/
theorem eval_crash_complete {v : Verb} (h : Invalid v) : ∃ n, eval n v = .crash := by
  obtain ⟨T, w, ⟨hhead, hcons⟩, hlast, hnext, hnt⟩ := h
  exact ⟨T.length, crash_of_trace T v w hhead hcons hlast hnext hnt⟩

-- main.tex:1124  (`eval` crash ⟺ the paper's ⊥ object)
/-- **Verifiable crash ⟺ ⊥.**  `eval` crashes on `v` (at some fuel) iff `v` is `Invalid` — the
    clean soundness/completeness biconditional at the paper's ⊥ (`main.tex:1124`). -/
theorem eval_crash_iff_invalid {v : Verb} : (∃ n, eval n v = .crash) ↔ Invalid v :=
  ⟨fun ⟨_, h⟩ => eval_crash_invalid h, eval_crash_complete⟩

-- main.tex:1124,1642  (the reached ⊥ state passes the transition checker)
/-- **The reported crash is a checked ⊥ (program-tied).**  A `crash` for `v` exhibits the trace of
    `v` reaching a state `w` that genuinely `Crashes` and whose ⊥-edge is accepted by the two-verb
    checker (`NockCheck w none = true`) — verifiability tied to the *evaluated* program. -/
theorem eval_crash_checked {n : Nat} {v : Verb} (h : eval n v = .crash) :
    ∃ T w, TraceOf v T ∧ T.getLast? = some w ∧ Crashes w ∧ NockCheck w none = true := by
  obtain ⟨T, w, hTr, hlast, hnext, hnt⟩ := eval_crash_invalid h
  have hgi : getIndex w ≠ none := fun hg =>
    absurd (getIndex_none_iff_terminal.mp hg) (by simp [hnt])
  have hcr : Crashes w := ⟨hgi, hnext⟩
  exact ⟨T, w, hTr, hlast, hcr, nockCheck_eq_true_iff.mpr (Or.inr ⟨rfl, hcr⟩)⟩

end Verb
end Nock
