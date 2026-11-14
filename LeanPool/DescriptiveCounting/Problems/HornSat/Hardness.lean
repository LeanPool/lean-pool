/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
module

public import LeanPool.DescriptiveCounting.ClauseDischarge
public import LeanPool.DescriptiveCounting.Problems.HornSat.Defs
public import Mathlib.Data.Fintype.Lattice
import all LeanPool.DescriptiveCounting.ClauseDischarge
import all LeanPool.DescriptiveCounting.Padding

/-!
# Hardness of HORN-SAT: the Horn discharge

Every SO-Horn definable problem admits an ordered first-order reduction to
HORN-SAT (`DescriptiveComplexity.hornSat_hard_of_sigmaSOHornDefinable`): the
machine-free P-hardness statement, one level below the Cook–Levin discharge of
`DescriptiveComplexity.Problems.Sat.Hardness` and in the same style.

It is *simpler* than Cook–Levin, and this is the whole point of the Horn
fragment. The Tseitin translation of an arbitrary first-order kernel has to
name every subformula by an auxiliary *gate* variable, and the gate clauses it
emits are not Horn. Here nothing has to be named: a Horn program
(`DescriptiveComplexity.HornProgram`) is already a conjunction of clauses, its
first-order guards mention the input vocabulary only – so they are *evaluated*
in the input structure rather than encoded – and each clause instance
translates to one propositional clause with at most one positive literal.

Given a block `B`, a number `k` of universally quantified first-order variables
and a program `prog`, the reduction interprets, inside an ordered input
structure `A`:

* propositional variables: one per relation variable `i` of `B` and per
  `B.arity i`-tuple over `A`, canonically padded
  (`DescriptiveComplexity.Padding`) to the common dimension
  `DescriptiveComplexity.clauseDim`;
* clauses: one per clause `c` of the program and per `k`-tuple over `A`
  *satisfying the guard of `c`* – the guard is an input-vocabulary formula, so
  “the guard holds” is literally what the defining formula of `satIsClause`
  says;
* literals: the head atom of `c` occurs positively and its body atoms occur
  negatively, at the canonically padded tuples of their arguments.

A clause of the program with no head (a goal clause) yields a purely negative
propositional clause, and one with a head yields exactly one positive literal:
the interpreted structure is always Horn
(`DescriptiveComplexity.horn_atMostOnePositive`), which is what makes the reduction land
in HORN-SAT rather than merely in SAT.

The correctness proof (`DescriptiveComplexity.horn_satisfiable_iff`) reads in both
directions through the canonical padding: an assignment `ρ` of the block gives
the truth value `ρ i (pref x)` of the propositional variable `(i, x)`, and
conversely a satisfying truth assignment `ν` gives the assignment
`ρ i ā := ν (i, pad ā)`.
-/

@[expose] public section

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

section Discharge

variable {L : Language.{0, 0}} {B : SOBlock} {k : ℕ}

/-! ### Tags and clause access

The dimension, the tags and the two generic defining formulas are shared with
the Krom discharge; they live in `DescriptiveComplexity.ClauseDischarge`. -/

/-- The tags of the Horn interpretation: the generic clausal tags at the
program's number of clauses. -/
abbrev HornTag (prog : HornProgram (L.sum Language.order) B k) : Type :=
  ClauseTag prog.length B

/-- The `c`-th clause of the program. -/
abbrev clauseAt (prog : HornProgram (L.sum Language.order) B k) (c : Fin prog.length) :
    HornClause (L.sum Language.order) B k :=
  prog[(c : ℕ)]'c.isLt

/-! ### The defining formulas -/

section Formulas

variable {γ : Type}

open Classical in
/-- The defining formula of a positive occurrence: the head atom of the
clause, when it is an atom of the relation variable `i`. -/
noncomputable def headOccF (c : HornClause (L.sum Language.order) B k) (i : B.ι)
    (u x : Fin (clauseDim B k) → γ) : (L.sum Language.order).Formula γ :=
  c.head.elim ⊥ fun a => if a.idx = i then atomOccF a u x else ⊥

open Classical in
/-- The defining formula of a negative occurrence: any body atom of the
clause that is an atom of the relation variable `i`. -/
noncomputable def bodyOccF (c : HornClause (L.sum Language.order) B k) (i : B.ι)
    (u x : Fin (clauseDim B k) → γ) : (L.sum Language.order).Formula γ :=
  listSup (c.body.map fun a => if a.idx = i then atomOccF a u x else ⊥)

/-! #### Realization of the defining formulas -/

variable {A : Type} [L.Structure A] [LinearOrder A] {v : γ → A}

private theorem realize_headOccF {c : HornClause (L.sum Language.order) B k} {i : B.ι}
    {u x : Fin (clauseDim B k) → γ} :
    (headOccF c i u x).Realize v ↔
      ∃ a ∈ c.head, a.idx = i ∧
        PadTup (atomIdx a) (fun j => v (u j)) fun j => v (x j) := by
  classical
  rw [headOccF]
  cases hh : c.head with
  | none =>
    rw [Option.elim_none]
    refine iff_of_false id ?_
    rintro ⟨a, ha, -⟩
    simp at ha
  | some a =>
    rw [Option.elim_some]
    by_cases hi : a.idx = i
    · rw [ite_eq_left hi, realize_atomOccF]
      refine ⟨fun h => ⟨a, rfl, hi, h⟩, ?_⟩
      rintro ⟨a', ha', -, h⟩
      have hae := Option.mem_def.mp ha'
      rw [Option.some.injEq] at hae
      subst hae
      exact h
    · rw [ite_eq_right hi]
      refine iff_of_false id ?_
      rintro ⟨a', ha', hi', -⟩
      have hae := Option.mem_def.mp ha'
      rw [Option.some.injEq] at hae
      subst hae
      exact hi hi'

private theorem realize_bodyOccF {c : HornClause (L.sum Language.order) B k} {i : B.ι}
    {u x : Fin (clauseDim B k) → γ} :
    (bodyOccF c i u x).Realize v ↔
      ∃ a ∈ c.body, a.idx = i ∧
        PadTup (atomIdx a) (fun j => v (u j)) fun j => v (x j) := by
  classical
  rw [bodyOccF, realize_listSup]
  constructor
  · rintro ⟨ψ, hψmem, hψ⟩
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hψmem
    by_cases hi : a.idx = i
    · rw [ite_eq_left hi, realize_atomOccF] at hψ
      exact ⟨a, ha, hi, hψ⟩
    · rw [ite_eq_right hi] at hψ
      exact hψ.elim
  · rintro ⟨a, ha, hi, hpad⟩
    refine ⟨_, List.mem_map.mpr ⟨a, ha, rfl⟩, ?_⟩
    rw [ite_eq_left hi, realize_atomOccF]
    exact hpad

end Formulas

/-- The Horn interpretation: the CNF instance of the propositional translation
of the program, defined inside the ordered input structure. -/
noncomputable def hornInterp (prog : HornProgram (L.sum Language.order) B k) :
    FOInterpretation (L.sum Language.order) Language.sat (HornTag prog) (clauseDim B k) where
  relFormula {n} R :=
    match n, R with
    | _, .isClause => fun t =>
        match t 0 with
        | Sum.inl (Sum.inl c) =>
            guardF (clauseAt prog c).guard (fun j => ((0 : Fin 1), j)) ⊓
              canonF k fun j => ((0 : Fin 1), j)
        | _ => ⊥
    | _, .posIn => fun t =>
        match t 0, t 1 with
        | Sum.inl (Sum.inl c), Sum.inl (Sum.inr i) =>
            headOccF (clauseAt prog c) i (fun j => ((0 : Fin 2), j)) fun j => ((1 : Fin 2), j)
        | _, _ => ⊥
    | _, .negIn => fun t =>
        match t 0, t 1 with
        | Sum.inl (Sum.inl c), Sum.inl (Sum.inr i) =>
            bodyOccF (clauseAt prog c) i (fun j => ((0 : Fin 2), j)) fun j => ((1 : Fin 2), j)
        | _, _ => ⊥

/-! ### Characterization of the interpreted relations

Every statement below is the corresponding realization lemma read through
`DescriptiveComplexity.FOInterpretation.relMap_map`; the tag combinations that are not
listed have `⊥` as defining formula, so the corresponding relation is empty. -/

section Characterizations

variable {A : Type} [L.Structure A] [LinearOrder A]
variable {prog : HornProgram (L.sum Language.order) B k}

/-- **The clause elements**: one per clause of the program and per canonically
padded tuple satisfying that clause's guard. -/
private theorem horn_isClause_cl (c : Fin prog.length) (w : Fin (clauseDim B k) → A) :
    RelMap (M := (hornInterp prog).Map A) satIsClause ![(clTag c, w)] ↔
      (clauseAt prog c).guard.Realize (fun j => w (Fin.castLE le_clauseDim j)) ∧ Canon k w := by
  rw [FOInterpretation.relMap_map]
  exact Formula.realize_inf.trans (and_congr realize_guardF realize_canonF)

/-- Elements carrying a variable tag are not clauses. -/
private theorem horn_not_isClause_var (i : B.ι) (w : Fin (clauseDim B k) → A) :
    ¬RelMap (M := (hornInterp prog).Map A) satIsClause ![(varTag i, w)] :=
  id

/-- Elements carrying the junk tag are not clauses. -/
private theorem horn_not_isClause_junk (w : Fin (clauseDim B k) → A) :
    ¬RelMap (M := (hornInterp prog).Map A) satIsClause
      ![((Sum.inr () : HornTag prog), w)] :=
  id

/-- **The positive literals**: the head atom of the clause, at the canonically
padded tuple of its arguments. -/
private theorem horn_posIn_cl_var (c : Fin prog.length) (i : B.ι)
    (u x : Fin (clauseDim B k) → A) :
    RelMap (M := (hornInterp prog).Map A) satPosIn ![(clTag c, u), (varTag i, x)] ↔
      ∃ a ∈ (clauseAt prog c).head, a.idx = i ∧ PadTup (atomIdx a) u x := by
  rw [FOInterpretation.relMap_map]
  exact realize_headOccF

/-- **The negative literals**: any body atom of the clause, at the canonically
padded tuple of its arguments. -/
private theorem horn_negIn_cl_var (c : Fin prog.length) (i : B.ι)
    (u x : Fin (clauseDim B k) → A) :
    RelMap (M := (hornInterp prog).Map A) satNegIn ![(clTag c, u), (varTag i, x)] ↔
      ∃ a ∈ (clauseAt prog c).body, a.idx = i ∧ PadTup (atomIdx a) u x := by
  rw [FOInterpretation.relMap_map]
  exact realize_bodyOccF

end Characterizations

/-! ### The interpreted structure is Horn, and correct -/

section Correctness

variable {A : Type} [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A]
variable (prog : HornProgram (L.sum Language.order) B k)

/-- **The interpretation always lands in HORN-SAT**: a clause of the program
has at most one head atom, and canonical padding makes the element encoding it
unique, so every interpreted clause has at most one positive literal. -/
theorem horn_atMostOnePositive : AtMostOnePositive ((hornInterp prog).Map A) := by
  obtain ⟨a₀, ha₀⟩ : ∃ a₀ : A, IsBot a₀ := Finite.exists_min (id : A → A)
  rintro ⟨tc, u⟩ ⟨tx, x⟩ ⟨ty, y⟩ hc hx hy
  rcases tc with (c | i) | ⟨⟩
  · rcases tx with (c' | i') | ⟨⟩ <;> try exact hx.elim
    rcases ty with (c'' | i'') | ⟨⟩ <;> try exact hy.elim
    obtain ⟨a, ha, hai, hpx⟩ := (horn_posIn_cl_var c i' u x).mp hx
    obtain ⟨a', ha', hai', hpy⟩ := (horn_posIn_cl_var c i'' u y).mp hy
    have hae : (clauseAt prog c).head = some a := Option.mem_def.mp ha
    have hae' : (clauseAt prog c).head = some a' := Option.mem_def.mp ha'
    rw [hae, Option.some.injEq] at hae'
    subst hae'
    subst hai
    subst hai'
    rw [eq_pad_of_padTup ha₀ hpx, eq_pad_of_padTup ha₀ hpy]
  · exact absurd hc (horn_not_isClause_var i u)
  · exact absurd hc (horn_not_isClause_junk u)

/-- **Correctness of the Horn discharge**: the program has a satisfying
assignment iff the interpreted CNF is satisfiable. -/
theorem horn_satisfiable_iff :
    (∃ ρ : B.Assignment A, prog.Holds ρ) ↔ Satisfiable ((hornInterp prog).Map A) := by
  obtain ⟨a₀, ha₀⟩ : ∃ a₀ : A, IsBot a₀ := Finite.exists_min (id : A → A)
  constructor
  · rintro ⟨ρ, hρ⟩
    refine ⟨fun z =>
      match z with
      | (Sum.inl (Sum.inr i), y) => ρ i (pref (arity_le_clauseDim (k := k) i) y)
      | _ => False, ?_⟩
    rintro ⟨tc, u⟩ hc
    rcases tc with (c | i) | ⟨⟩
    · obtain ⟨hguard, -⟩ := (horn_isClause_cl c u).mp hc
      -- the truth value of the propositional variable encoding an atom
      have hval : ∀ a : SOAtom B k,
          ρ a.idx (pref (arity_le_clauseDim (k := k) a.idx) (pad a₀ fun j => u (atomIdx a j))) ↔
            a.Holds ρ fun j => u (Fin.castLE le_clauseDim j) := by
        intro a
        rw [pref_pad]
        exact Iff.rfl
      by_cases hbody : ∀ a ∈ (clauseAt prog c).body,
          a.Holds ρ fun j => u (Fin.castLE le_clauseDim j)
      · -- every body atom is true, so the head atom is, and it occurs positively
        have hhead := hρ (fun j => u (Fin.castLE le_clauseDim j)) (clauseAt prog c)
          (List.getElem_mem c.isLt) ⟨hguard, hbody⟩
        rw [HornClause.HeadHolds] at hhead
        cases hh : (clauseAt prog c).head with
        | none =>
          rw [hh, Option.elim_none] at hhead
          exact hhead.elim
        | some a =>
          rw [hh, Option.elim_some] at hhead
          refine ⟨((varTag a.idx : HornTag prog), pad a₀ fun j => u (atomIdx a j)),
            Or.inl ⟨?_, ?_⟩⟩
          · exact (horn_posIn_cl_var c a.idx u _).mpr
              ⟨a, hh, rfl, padTup_pad ha₀ _ u⟩
          · exact (hval a).mpr hhead
      · -- some body atom is false, and it occurs negatively
        push Not at hbody
        obtain ⟨a, ha, hfalse⟩ := hbody
        refine ⟨((varTag a.idx : HornTag prog), pad a₀ fun j => u (atomIdx a j)),
          Or.inr ⟨?_, ?_⟩⟩
        · exact (horn_negIn_cl_var c a.idx u _).mpr ⟨a, ha, rfl, padTup_pad ha₀ _ u⟩
        · exact fun h => hfalse ((hval a).mp h)
    · exact absurd hc (horn_not_isClause_var i u)
    · exact absurd hc (horn_not_isClause_junk u)
  · rintro ⟨ν, hν⟩
    refine ⟨fun i ā => ν ((varTag i : HornTag prog), pad a₀ ā), fun v c hc => ?_⟩
    obtain ⟨n, hn, hci⟩ := List.getElem_of_mem hc
    subst hci
    intro hpre
    have hcl : RelMap (M := (hornInterp prog).Map A) satIsClause
        ![((clTag ⟨n, hn⟩ : HornTag prog), pad a₀ v)] := by
      refine (horn_isClause_cl ⟨n, hn⟩ (pad a₀ v)).mpr ⟨?_, canon_pad ha₀ k v⟩
      rw [show (fun j => pad (D := clauseDim B k) a₀ v (Fin.castLE le_clauseDim j)) = v from
        pref_pad a₀ le_clauseDim v]
      exact hpre.1
    obtain ⟨⟨tx, x⟩, hx⟩ := hν _ hcl
    -- the element encoding an atom is the canonical padding of its arguments
    have hatom : ∀ a : SOAtom B k, PadTup (atomIdx a) (pad a₀ v) x →
        x = pad a₀ fun j => v (a.args j) := by
      intro a hpad
      rw [eq_pad_of_padTup ha₀ hpad]
      exact congrArg (pad a₀) (funext fun j => congrFun (pref_pad a₀ le_clauseDim v) (a.args j))
    rcases tx with (c' | i') | ⟨⟩
    · rcases hx with ⟨h, -⟩ | ⟨h, -⟩ <;> exact h.elim
    · rcases hx with ⟨hpos, hval⟩ | ⟨hneg, hval⟩
      · obtain ⟨a, ha, hai, hpad⟩ := (horn_posIn_cl_var ⟨n, hn⟩ i' (pad a₀ v) x).mp hpos
        have hae : (clauseAt prog ⟨n, hn⟩).head = some a := Option.mem_def.mp ha
        subst hai
        rw [hatom a hpad] at hval
        unfold HornClause.HeadHolds
        rw [hae]
        exact hval
      · obtain ⟨a, ha, hai, hpad⟩ := (horn_negIn_cl_var ⟨n, hn⟩ i' (pad a₀ v) x).mp hneg
        subst hai
        rw [hatom a hpad] at hval
        exact absurd (hpre.2 a ha) hval
    · rcases hx with ⟨h, -⟩ | ⟨h, -⟩ <;> exact h.elim

/-- The program has a satisfying assignment iff the interpreted CNF is a
yes-instance of HORN-SAT. -/
theorem horn_hornSatisfiable_iff :
    (∃ ρ : B.Assignment A, prog.Holds ρ) ↔ HornSatisfiable ((hornInterp prog).Map A) := by
  rw [HornSatisfiable, and_iff_right (horn_atMostOnePositive prog)]
  exact horn_satisfiable_iff prog

end Correctness

/-- **The generic Horn reduction**: an ordered first-order reduction to
HORN-SAT from any problem defined, on nonempty finite structures, by an
existential second-order sentence with a Horn kernel. -/
noncomputable def hornReduction [L.IsRelational]
    (prog : HornProgram (L.sum Language.order) B k) (Q : DecisionProblem L)
    (hQ : ∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A],
      Q A ↔ ∃ ρ : B.Assignment A, prog.Holds ρ) : Q ≤ᶠᵒ[≤] HORNSAT where
  Tag := HornTag prog
  dim := clauseDim B k
  toInterpretation := hornInterp prog
  correct A _ _ _ _ := (hQ A).trans (horn_hornSatisfiable_iff prog)

end Discharge

/-- **P-hardness of HORN-SAT, machine-free**: every SO-Horn definable problem
admits an ordered first-order reduction to HORN-SAT. This is the Horn analogue
of the Cook–Levin discharge `DescriptiveComplexity.sat_hard_of_sigmaSODefinable`, one
level below it. -/
theorem hornSat_hard_of_sigmaSOHornDefinable :
    ∀ {L : Language.{0, 0}} [L.IsRelational] (Q : DecisionProblem L),
      SigmaSOHornDefinable Q → Nonempty (Q ≤ᶠᵒ[≤] HORNSAT) := by
  rintro L _ Q ⟨B, k, prog, hprog⟩
  exact ⟨hornReduction prog Q hprog⟩

end DescriptiveComplexity
