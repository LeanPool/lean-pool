/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
module

public import LeanPool.DescriptiveCounting.Syntax
import LeanPool.DescriptiveCounting.Vocabulary
public import LeanPool.DescriptiveCounting.Hierarchy

/-!
# SAT: propositional satisfiability

The problem SAT, as a decision problem on first-order structures. A CNF
formula is a `FirstOrder.Language.sat`-structure: elements are clauses and
propositional variables, `satIsClause c` distinguishes the clauses, and
`satPosIn c x` / `satNegIn c x` say that the literal `x` / `¬x` occurs in
clause `c`. `DescriptiveComplexity.Satisfiable` is the usual satisfiability, and
`DescriptiveComplexity.SAT` the bundled decision problem.

SAT is the archetypical NP-complete problem: this is the Cook–Levin theorem
([Cook 1971][cook1971complexity]; [Levin 1973][levin1973universal];
`DescriptiveComplexity.SAT_NP_complete`, in `DescriptiveComplexity.Problems.Sat.Hardness`). With
NP *defined* as existential-second-order definability
(`DescriptiveComplexity.Hierarchy`), its membership half is the theorem
`DescriptiveComplexity.sat_sigmaSODefinable` proved here – “there is a truth assignment
making every clause true” – and its hardness half is the machine-free,
Dahlhaus-style ([Dahlhaus 1983][dahlhaus1983reduction]) generic reduction
`DescriptiveComplexity.sat_hard_of_sigmaSODefinable`
of `DescriptiveComplexity.Problems.Sat.Hardness`. Other problems' NP-completeness
proofs derive from it through first-order reductions; see e.g.,
`DescriptiveComplexity.Problems.ThreeColorability`.
-/

@[expose] public section

/- The language of CNF instances lives in Mathlib's `FirstOrder.Language`
namespace, next to `Language.graph` and `Language.order` – a project-local
`Language` namespace would shadow Mathlib's under `open Language`. -/
namespace FirstOrder

namespace Language

/-- The relational language of CNF instances: a unary predicate singling out
clauses, and two binary predicates for positive and negative occurrences of a
variable in a clause. -/
fo_language sat with sat where
  /-- `isClause c`: the element `c` is a clause. -/
  isClause : 1
  /-- `posIn c x`: the variable `x` occurs positively in the clause `c`. -/
  posIn : 2
  /-- `negIn c x`: the variable `x` occurs negatively in the clause `c`. -/
  negIn : 2

end Language

end FirstOrder

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

section Sat

variable (A : Type) [Language.sat.Structure A]

/-- A `Language.sat`-structure is satisfiable if some assignment of truth
values to its elements makes every clause contain a true literal. (Elements
that are not variables of the CNF formula may be assigned arbitrarily; they are
harmless since no clause mentions them.) -/
def Satisfiable : Prop :=
  ∃ ν : A → Prop, ∀ c : A, RelMap satIsClause ![c] →
    ∃ x : A, (RelMap satPosIn ![c, x] ∧ ν x) ∨ (RelMap satNegIn ![c, x] ∧ ¬ν x)

/-- The element `x` is a variable of the CNF formula: it occurs, positively or
negatively, in some clause. The decision problem does not need the notion –
an element in no clause is harmless – but everything that *counts* assignments
does, and so does any reduction that must not give such an element a truth
value to choose. -/
def SatOccurs (x : A) : Prop :=
  ∃ c : A, RelMap satIsClause ![c] ∧ (RelMap satPosIn ![c, x] ∨ RelMap satNegIn ![c, x])

end Sat

section Iso

private theorem satisfiable_of_iso {A B : Type} [Language.sat.Structure A]
    [Language.sat.Structure B] (e : A ≃[Language.sat] B) (h : Satisfiable A) :
    Satisfiable B := by
  obtain ⟨ν, hν⟩ := h
  refine ⟨fun b => ν (e.symm b), fun c hc => ?_⟩
  obtain ⟨x, hx⟩ := hν (e.symm c) ((relMap_equiv₁ e.symm satIsClause c).mp hc)
  refine ⟨e x, ?_⟩
  rcases hx with ⟨hp, hT⟩ | ⟨hn, hT⟩
  · refine Or.inl ⟨?_, by simpa using hT⟩
    simpa using (relMap_equiv₂ e satPosIn (e.symm c) x).mp hp
  · refine Or.inr ⟨?_, by simpa using hT⟩
    simpa using (relMap_equiv₂ e satNegIn (e.symm c) x).mp hn

/-- Satisfiability is isomorphism-invariant. -/
theorem satisfiable_iso {A B : Type} [Language.sat.Structure A] [Language.sat.Structure B]
    (e : A ≃[Language.sat] B) : Satisfiable A ↔ Satisfiable B :=
  ⟨satisfiable_of_iso e, satisfiable_of_iso e.symm⟩

end Iso

/-- SAT, as a problem on `Language.sat`-structures. -/
def SAT : DecisionProblem Language.sat where
  Holds := fun A inst => @Satisfiable A inst
  iso_invariant := fun e => satisfiable_iso e

/-! ### SAT is existential second-order definable

SAT is `Σ₁`-definable in the sense of `DescriptiveComplexity.SecondOrder` – “there
exists a truth assignment (a unary relation) making every clause true”, the
inner part being first-order. Since NP is *defined* as `Σ₁`-definability,
this is the membership half of the Cook–Levin theorem. -/

section SigmaOne

open SOBlock

/-- The single existential block of the `Σ₁` definition of SAT: one unary
relation variable, the truth assignment. -/
def satAssignBlock : SOBlock where
  ι := Unit
  arity := fun _ => 1

/-- The symbol of the truth-assignment relation variable. -/
def satNuSym : satAssignBlock.lang.Relations 1 := ⟨(), rfl⟩

/-- The vocabulary of the kernel: CNF instances together with the
truth-assignment relation variable. -/
abbrev satSOLang : Language := Language.sat.sum satAssignBlock.lang

/-- The symbol for “is a clause” in the kernel's vocabulary. -/
abbrev kIsClSym : satSOLang.Relations 1 := Sum.inl satIsClause

/-- The symbol for “occurs positively in” in the kernel's vocabulary. -/
abbrev kPosSym : satSOLang.Relations 2 := Sum.inl satPosIn

/-- The symbol for “occurs negatively in” in the kernel's vocabulary. -/
abbrev kNegSym : satSOLang.Relations 2 := Sum.inl satNegIn

/-- The truth-assignment symbol in the kernel's vocabulary. -/
abbrev kNuSym : satSOLang.Relations 1 := Sum.inr satNuSym

/-- The first-order kernel of the `Σ₁` definition of SAT: every clause
contains a true literal. The universally quantified variable is the clause,
the existentially quantified one the literal's variable. -/
noncomputable def satKernel : satSOLang.Sentence :=
  fo% ∀ c, kIsClSym(c) →
    ∃ x, (kPosSym(c, x) ∧ kNuSym(x)) ∨ (kNegSym(c, x) ∧ ¬ kNuSym(x))

/-- Realization of the kernel under an assignment of the truth-assignment
variable: every clause contains a true literal. (Reused by the membership
proof of HORN-SAT, whose kernel is this one conjoined with the first-order
Horn condition.) -/
theorem realize_satKernel {A : Type} [Language.sat.Structure A]
    (ρ : satAssignBlock.Assignment A) :
    (@Sentence.Realize satSOLang A
        (@sumStructure _ _ A _ (satAssignBlock.structure ρ)) satKernel) ↔
      ∀ c : A, RelMap satIsClause ![c] → ∃ x : A,
        (RelMap satPosIn ![c, x] ∧ ρ satNuSym.1 fun _ => x) ∨
          (RelMap satNegIn ![c, x] ∧ ¬ρ satNuSym.1 fun _ => x) := by
  let := satAssignBlock.structure ρ
  have hsub : ∀ (w : Fin 1 → A),
      RelMap (L := satSOLang) (M := A) kNuSym w ↔ ρ satNuSym.1 fun _ => w 0 := by
    intro w
    change ρ satNuSym.1 _ ↔ ρ satNuSym.1 _
    exact iff_of_eq (congrArg _ (funext fun j => congrArg w (Subsingleton.elim _ _)))
  rw [satKernel]
  simp only [Sentence.Realize, Formula.realize_iAlls, Formula.realize_imp,
    Formula.realize_iExs, Formula.realize_sup, Formula.realize_inf, Formula.realize_not,
    Formula.realize_rel₁, Formula.realize_rel₂, Term.realize_var, Sum.elim_inr, Sum.elim_inl,
    Language.relMap_sumInl, hsub]
  constructor
  · intro h c hc
    obtain ⟨x, hx⟩ := h (fun _ => c) hc
    rcases hx with ⟨hp, hT⟩ | ⟨hn, hT⟩
    · exact ⟨x 0, Or.inl ⟨hp, hT⟩⟩
    · exact ⟨x 0, Or.inr ⟨hn, hT⟩⟩
  · intro h i hc
    obtain ⟨x, hx⟩ := h (i 0) hc
    rcases hx with ⟨hp, hT⟩ | ⟨hn, hT⟩
    · exact ⟨fun _ => x, Or.inl ⟨hp, hT⟩⟩
    · exact ⟨fun _ => x, Or.inr ⟨hn, hT⟩⟩

/-- **SAT is `Σ₁`-definable**: satisfiability of a CNF structure is expressed
by existentially quantifying a truth assignment and checking, in first-order
logic, that every clause contains a true literal.
Registered in the Lax archive as
[`Lax904597.CookLevin.sat_sigmaSODefinable`](https://laxarchive.org/lax-904597/Lax904597.CookLevin.html#s-Lax904597.CookLevin.sat_sigmaSODefinable). -/
theorem sat_sigmaSODefinable : SigmaSODefinable 1 SAT := by
  refine ⟨[satAssignBlock], rfl, satKernel, ?_⟩
  intro A _ _ _
  constructor
  · rintro ⟨ν, hν⟩
    exact ⟨fun _ x => ν (x ⟨0, Nat.one_pos⟩),
      (realize_satKernel _).mpr fun c hc => hν c hc⟩
  · rintro ⟨ρ, hρ⟩
    exact ⟨fun a => ρ satNuSym.1 fun _ => a, fun c hc => (realize_satKernel ρ).mp hρ c hc⟩

end SigmaOne

end DescriptiveComplexity
