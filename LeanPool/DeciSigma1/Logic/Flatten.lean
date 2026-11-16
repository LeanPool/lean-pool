/-
Copyright (c) 2026 Yaoyu Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaoyu Zhao
-/

module

public import LeanPool.DeciSigma1.Logic.Syntax
public import Mathlib.Tactic.ToAdditive
import Mathlib.Data.List.Basic
public import Mathlib.Tactic.Attr.Core
import Mathlib.Tactic.Finiteness.Attr
public import Mathlib.Tactic.Basic
public import Mathlib.Tactic.ToDual

/-! Ported to Lean Pool’s module system and pinned Lean and Mathlib.

 # Disjunctive normal form and flattening of clauses

A quantifier-free formula is equivalent to a disjunction of conjunctive clauses, each a conjunction
of inequalities `s ≤ t` and negated inequalities `¬ s ≤ t` (`QuantifierFreeFormula.holds_iff_dnf`).
A clause is realizable in a class of values exactly when a disjunctive entailment between flat
constraints fails (`ConjunctiveClause.realizable_iff_not_disjEntailsIn`): every subterm of the
clause receives a fresh name, flat constraints define each name from the names of its immediate
subterms, the inequalities become flat inequalities between names, and the negated inequalities
become the queries `x_i ≤ y_i` of the entailment. With no negated inequality the query family is
empty, and the entailment fails exactly when the flat constraints are satisfiable.

The flat constraint language is a parameter: a `Flattening` provides the literals, their
satisfaction, the literal `x ≤ y`, the subterms of a term, and the literals that define the name of
a term.

## Main declarations

- `ConjunctiveClause`, `ConjunctiveClause.Holds`: conjunctions of inequalities and negated
  inequalities.
- `QuantifierFreeFormula.dnf`, `QuantifierFreeFormula.holds_iff_dnf`: the disjunctive normal form.
- `Flattening`: a flat constraint language adequate for naming subterms.
- `Flattening.DisjEntailsIn`: disjunctive entailment between flat constraints in a class.
- `ConjunctiveClause.constraints`, `ConjunctiveClause.queries`: the flat constraints and queries of
  a clause.
- `ConjunctiveClause.realizable_iff_not_disjEntailsIn`: a clause is realizable exactly when its
  constraints do not entail the disjunction of its queries.
-/

@[expose] public section


namespace DeciSigma1.Logic

variable {T : Type → Type} {D V : Type} {I : Interpretation T D}

/-! ## Disjunctive normal form -/

/-- A clause: a conjunction of inequalities `s ≤ t` (`positive`) and negated inequalities
`¬ s ≤ t` (`negative`). -/
structure ConjunctiveClause (T : Type → Type) (V : Type) where
  /-- The inequalities. -/
  positive : List (T V × T V)
  /-- The negated inequalities. -/
  negative : List (T V × T V)

/-- Truth of a clause when its variables have the values `ρ`. -/
def ConjunctiveClause.Holds (I : Interpretation T D) (ρ : V → D) (c : ConjunctiveClause T V) :
    Prop :=
  (∀ p ∈ c.positive, I.le (I.eval ρ p.1) (I.eval ρ p.2)) ∧
  (∀ p ∈ c.negative, ¬ I.le (I.eval ρ p.1) (I.eval ρ p.2))

/-- The conjunction of two clauses. -/
def ConjunctiveClause.append (c d : ConjunctiveClause T V) : ConjunctiveClause T V :=
  ⟨c.positive ++ d.positive, c.negative ++ d.negative⟩

@[simp] theorem ConjunctiveClause.holds_append (ρ : V → D) (c d : ConjunctiveClause T V) :
    (c.append d).Holds I ρ ↔ c.Holds I ρ ∧ d.Holds I ρ := by
  simp only [Holds, append, List.mem_append, or_imp, forall_and]
  tauto

/-- The conjunction of two disjunctions of clauses, as a disjunction of clauses. -/
def ConjunctiveClause.cross (cs ds : List (ConjunctiveClause T V)) : List (ConjunctiveClause T V) :=
  cs.flatMap fun c => ds.map c.append

theorem ConjunctiveClause.exists_holds_cross (ρ : V → D) (cs ds : List (ConjunctiveClause T V)) :
    (∃ c ∈ cross cs ds, c.Holds I ρ) ↔ (∃ c ∈ cs, c.Holds I ρ) ∧ (∃ d ∈ ds, d.Holds I ρ) := by
  simp only [cross, List.mem_flatMap, List.mem_map]
  aesop

/-- The disjunctive normal form of `φ` for `b = true` and of `¬ φ` for `b = false`. -/
def QuantifierFreeFormula.dnfWithPolarity :
    QuantifierFreeFormula T V → Bool → List (ConjunctiveClause T V)
  | .le s t, true => [⟨[(s, t)], []⟩]
  | .le s t, false => [⟨[], [(s, t)]⟩]
  | .tt, true | .ff, false => [⟨[], []⟩]
  | .tt, false | .ff, true => []
  | .not φ, b => φ.dnfWithPolarity (!b)
  | .and φ ψ, true => ConjunctiveClause.cross (φ.dnfWithPolarity true) (ψ.dnfWithPolarity true)
  | .or φ ψ, false => ConjunctiveClause.cross (φ.dnfWithPolarity false) (ψ.dnfWithPolarity false)
  | .and φ ψ, false => φ.dnfWithPolarity false ++ ψ.dnfWithPolarity false
  | .or φ ψ, true => φ.dnfWithPolarity true ++ ψ.dnfWithPolarity true

theorem QuantifierFreeFormula.holds_iff_dnfWithPolarity (φ : QuantifierFreeFormula T V) (ρ : V → D)
    (b : Bool) :
    (if b then φ.Holds I ρ else ¬ φ.Holds I ρ) ↔ ∃ c ∈ φ.dnfWithPolarity b, c.Holds I ρ := by
  induction φ generalizing b with
  | le s t => cases b <;> simp [dnfWithPolarity, Holds, ConjunctiveClause.Holds]
  | tt => cases b <;> simp [dnfWithPolarity, Holds, ConjunctiveClause.Holds]
  | ff => cases b <;> simp [dnfWithPolarity, Holds, ConjunctiveClause.Holds]
  | not φ ih =>
    cases b
    · simpa [dnfWithPolarity, Holds] using ih true
    · simpa [dnfWithPolarity, Holds] using ih false
  | and φ ψ ihφ ihψ =>
    cases b <;> simp [dnfWithPolarity, Holds, ConjunctiveClause.exists_holds_cross, or_and_right,
      exists_or, ← ihφ, ← ihψ]
    tauto
  | or φ ψ ihφ ihψ =>
    cases b <;> simp [dnfWithPolarity, Holds, ConjunctiveClause.exists_holds_cross, or_and_right,
      exists_or, ← ihφ, ← ihψ]

/-- The disjunctive normal form of a quantifier-free formula. -/
def QuantifierFreeFormula.dnf (φ : QuantifierFreeFormula T V) :
    List (ConjunctiveClause T V) := φ.dnfWithPolarity true

/-- A quantifier-free formula holds exactly when some clause of its disjunctive normal form
holds. -/
theorem QuantifierFreeFormula.holds_iff_dnf (φ : QuantifierFreeFormula T V) (ρ : V → D) :
    φ.Holds I ρ ↔ ∃ c ∈ φ.dnf, c.Holds I ρ :=
  φ.holds_iff_dnfWithPolarity ρ true

/-! ## Flattening -/

/-- A flat constraint language for the interpretation `I`, adequate for naming subterms: flat
literals over variables `W` with their satisfaction, the literal `x ≤ y`, the subterms of a
term, and for each term `t` the literals `defs var name t` that define `name t` from the names
of the immediate subterms of `t`, where `var` names the variables. -/
structure Flattening (I : Interpretation T D) where
  /-- Flat literals with variables in `W`. -/
  Lit : Type → Type
  /-- Satisfaction of a flat literal by an assignment. -/
  Holds {W : Type} : (W → D) → Lit W → Prop
  /-- The flat literal `x ≤ y`. -/
  leLit {W : Type} : W → W → Lit W
  holds_leLit {W : Type} (σ : W → D) (x y : W) : Holds σ (leLit x y) ↔ I.le (σ x) (σ y)
  /-- The subterms of a term, including the term itself. -/
  subterms {V : Type} : T V → List (T V)
  mem_subterms {V : Type} (t : T V) : t ∈ subterms t
  subterms_trans {V : Type} {s t u : T V} : s ∈ subterms t → u ∈ subterms s → u ∈ subterms t
  /-- A term without variables, which names the values not used by a clause. -/
  bot {V : Type} : T V
  /-- Literals defining `name t`, given the names `var v` of the variables and `name s` of the
  other subterms of `t`. -/
  defs {V W : Type} : (V → W) → (T V → W) → T V → List (Lit W)
  /-- If every subterm is named by its value, the defining literals hold. -/
  holds_defs {V W : Type} (var : V → W) (name : T V → W) (σ : W → D) (t : T V) :
    (∀ s ∈ subterms t, σ (name s) = I.eval (σ ∘ var) s) → ∀ l ∈ defs var name t, Holds σ l
  /-- If the defining literals of all subterms hold, `t` is named by its value. -/
  eval_of_holds_defs {V W : Type} (var : V → W) (name : T V → W) (σ : W → D) (t : T V) :
    (∀ s ∈ subterms t, ∀ l ∈ defs var name s, Holds σ l) → σ (name t) = I.eval (σ ∘ var) t

namespace Flattening

variable (F : Flattening I)

/-- Disjunctive entailment between flat constraints over the class `C`: every assignment with
values in `C` that satisfies `Γ` satisfies one of the inequalities `x_i ≤ y_i` with
`q i = (x_i, y_i)`. -/
def DisjEntailsIn {W : Type} {k : ℕ} (C : D → Prop) (Γ : List (F.Lit W))
    (q : Fin k → W × W) : Prop :=
  ∀ σ : W → D, (∀ w, C (σ w)) → (∀ l ∈ Γ, F.Holds σ l) → ∃ i, I.le (σ (q i).1) (σ (q i).2)

end Flattening

namespace ConjunctiveClause

variable (F : Flattening I) {m : ℕ} (c : ConjunctiveClause T (Fin m))

/-- The subterms of the terms of a clause. -/
def terms : List (T (Fin m)) :=
  (c.positive ++ c.negative).flatMap fun p => F.subterms p.1 ++ F.subterms p.2

theorem mem_terms {p : T (Fin m) × T (Fin m)} (hp : p ∈ c.positive ∨ p ∈ c.negative) :
    p.1 ∈ c.terms F ∧ p.2 ∈ c.terms F := by
  constructor <;> refine List.mem_flatMap.mpr ⟨p, List.mem_append.mpr hp, ?_⟩ <;>
    simp [F.mem_subterms]

theorem mem_terms_of_mem_subterms {s t : T (Fin m)} (ht : t ∈ c.terms F)
    (hs : s ∈ F.subterms t) : s ∈ c.terms F := by
  obtain ⟨p, hp, ht⟩ := List.mem_flatMap.mp ht
  refine List.mem_flatMap.mpr ⟨p, hp, ?_⟩
  rcases List.mem_append.mp ht with ht | ht
  · exact List.mem_append_left _ (F.subterms_trans ht hs)
  · exact List.mem_append_right _ (F.subterms_trans ht hs)

/-- The flat variables of a clause: its own variables and one name for each of its subterms,
with one spare name. -/
abbrev Names : Type := Fin m ⊕ Fin ((c.terms F).length + 1)

/-- The assignment that gives every name the value of the term it names. -/
def extend (ρ : Fin m → D) : c.Names F → D :=
  Sum.elim ρ fun i => I.eval ρ (((c.terms F)[i.val]?).getD F.bot)

theorem extend_closed {C : D → Prop} (hC : I.TermClosed C) {ρ : Fin m → D} (hρ : ∀ v, C (ρ v)) :
    ∀ w, C (c.extend F ρ w)
  | .inl v => hρ v
  | .inr _ => hC ρ _ hρ

variable [DecidableEq (T (Fin m))]

/-- The name of a term: its position in `terms`; terms outside `terms` share the spare
name. -/
def name (t : T (Fin m)) : c.Names F :=
  .inr ⟨(c.terms F).idxOf t, Nat.lt_succ_of_le List.idxOf_le_length⟩

/-- The flat constraints of a clause: the definitions of the names of its subterms and its
inequalities between names. -/
def constraints : List (F.Lit (c.Names F)) :=
  (c.terms F).flatMap (F.defs .inl (c.name F)) ++
    c.positive.map fun p => F.leLit (c.name F p.1) (c.name F p.2)

/-- The queries of a clause: one inequality between names for each negated inequality. -/
def queries (i : Fin c.negative.length) : c.Names F × c.Names F :=
  (c.name F c.negative[i].1, c.name F c.negative[i].2)

theorem extend_name (ρ : Fin m → D) {t : T (Fin m)} (ht : t ∈ c.terms F) :
    c.extend F ρ (c.name F t) = I.eval ρ t := by
  simp [extend, name, List.getElem?_idxOf, ht]

theorem holds_constraints_extend {ρ : Fin m → D} (hρ : c.Holds I ρ) :
    ∀ l ∈ c.constraints F, F.Holds (c.extend F ρ) l := by
  intro l hl
  rcases List.mem_append.mp hl with hl | hl
  · obtain ⟨t, ht, hl⟩ := List.mem_flatMap.mp hl
    exact F.holds_defs _ _ _ t
      (fun s hs => c.extend_name F ρ (c.mem_terms_of_mem_subterms F ht hs)) l hl
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hl
    have h := c.mem_terms F (Or.inl hp)
    rw [F.holds_leLit, c.extend_name F ρ h.1, c.extend_name F ρ h.2]
    exact hρ.1 p hp

theorem eq_eval_of_holds_constraints {σ : c.Names F → D}
    (hσ : ∀ l ∈ c.constraints F, F.Holds σ l) {t : T (Fin m)} (ht : t ∈ c.terms F) :
    σ (c.name F t) = I.eval (σ ∘ .inl) t :=
  F.eval_of_holds_defs _ _ σ t fun s hs l hl =>
    hσ l (List.mem_append_left _
      (List.mem_flatMap.mpr ⟨s, c.mem_terms_of_mem_subterms F ht hs, hl⟩))

/-- A clause is realizable in a closed class `C` if and only if its flat constraints do not
entail the disjunction of its queries over `C`. -/
theorem realizable_iff_not_disjEntailsIn {C : D → Prop} (hC : I.TermClosed C) :
    (∃ ρ : Fin m → D, (∀ v, C (ρ v)) ∧ c.Holds I ρ) ↔
      ¬ F.DisjEntailsIn C (c.constraints F) (c.queries F) := by
  simp only [Flattening.DisjEntailsIn, not_forall, not_exists]
  constructor
  · rintro ⟨ρ, hCρ, hρ⟩
    refine ⟨c.extend F ρ, c.extend_closed F hC hCρ, c.holds_constraints_extend F hρ, ?_⟩
    intro i
    have h := c.mem_terms F (p := c.negative[i]) (Or.inr (List.getElem_mem i.isLt))
    change ¬ I.le (c.extend F ρ (c.name F c.negative[i].1))
      (c.extend F ρ (c.name F c.negative[i].2))
    rw [c.extend_name F ρ h.1, c.extend_name F ρ h.2]
    exact hρ.2 _ (List.getElem_mem i.isLt)
  · rintro ⟨σ, hCσ, hσ, hq⟩
    refine ⟨σ ∘ .inl, fun v => hCσ _, ?_, ?_⟩
    · intro p hp
      have h := c.mem_terms F (Or.inl hp)
      have hl := hσ _ (List.mem_append_right _ (List.mem_map.mpr ⟨p, hp, rfl⟩))
      rwa [F.holds_leLit, c.eq_eval_of_holds_constraints F hσ h.1,
        c.eq_eval_of_holds_constraints F hσ h.2] at hl
    · intro p hp
      obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hp
      have h := c.mem_terms F (Or.inr (List.getElem_mem hi))
      have hl : ¬ I.le (σ (c.name F c.negative[i].1)) (σ (c.name F c.negative[i].2)) :=
        hq ⟨i, hi⟩
      rwa [c.eq_eval_of_holds_constraints F hσ h.1,
        c.eq_eval_of_holds_constraints F hσ h.2] at hl

end ConjunctiveClause

end DeciSigma1.Logic
