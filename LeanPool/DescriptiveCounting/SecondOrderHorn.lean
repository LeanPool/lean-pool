/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
module

public import LeanPool.DescriptiveCounting.SecondOrder
import all LeanPool.DescriptiveCounting.SecondOrder

/-!
# SO-Horn: existential second-order logic with a Horn kernel

The fragment SO-Horn of Grädel ([Grädel 1992][gradel1992capturing]): existential
second-order sentences whose first-order kernel is a conjunction of *Horn
clauses* in the quantified relation variables. On ordered structures SO-Horn
captures polynomial time – the Horn kernel is exactly what makes the guessed
relations *determined* rather than merely guessed, since a satisfiable Horn
formula has a least model, computable by unit propagation.

## The kernel, as data

The Horn condition constrains only the occurrences of the *second-order*
variables: a clause is

```
guard(x) ∧ R₁(x) ∧ … ∧ Rₙ(x) → R₀(x)   (or → ⊥)
```

where `guard` is an arbitrary first-order formula over the *input* vocabulary
alone (in the definability notion below, over its ordered expansion). Rather
than carve this shape out of `FirstOrder.Language.BoundedFormula` with a
syntactic predicate, the kernel is represented here *as data*: a
`DescriptiveComplexity.HornClause` bundles its guard, the list of its body atoms and its
optional head atom, and a `DescriptiveComplexity.HornProgram` is a list of clauses
sharing `k` universally quantified first-order variables. This is Grädel's
clausal normal form, and it is what a reduction consuming an SO-Horn definition
needs to see: the discharge of `DescriptiveComplexity.Problems.HornSat.Hardness` reads the
clause list directly, and emits one propositional Horn clause per clause and
per instantiation of the `k` variables.

`DescriptiveComplexity.SigmaSOHornDefinable` is the resulting definability notion,
the SO-Horn analogue of `DescriptiveComplexity.SigmaSODefinable`; it is closed under
(ordered) first-order reductions by
`DescriptiveComplexity.SecondOrderHornPull`, which is what makes it a
`DescriptiveComplexity.ComplexityClass` – the class `DescriptiveComplexity.PTIME` of
`DescriptiveComplexity.Hierarchy`.
-/

@[expose] public section

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### Horn programs -/

/-- A Horn clause over the input vocabulary `L` and the block `B`, with `k`
universally quantified first-order variables: an arbitrary first-order guard
over `L` and a list of second-order body atoms imply the head atom – or `⊥`,
when the head is `none` (a *goal* clause). -/
structure HornClause (L : Language.{0, 0}) (B : SOBlock) (k : ℕ) where
  /-- The first-order guard, over the input vocabulary alone. -/
  guard : L.Formula (Fin k)
  /-- The body: second-order atoms, all of them positive. -/
  body : List (SOAtom B k)
  /-- The head: a second-order atom, or `none` for a goal clause. -/
  head : Option (SOAtom B k)

/-- An SO-Horn kernel, as data: a finite conjunction of Horn clauses, each
implicitly universally quantified over the same `k` first-order variables. -/
abbrev HornProgram (L : Language.{0, 0}) (B : SOBlock) (k : ℕ) : Type :=
  List (HornClause L B k)

/-! ### Semantics -/

section Semantics

variable {L : Language.{0, 0}} {B : SOBlock} {k : ℕ} {A : Type} [L.Structure A]

/-- The truth value of the head of a clause: `False` for a goal clause. -/
def HornClause.HeadHolds (c : HornClause L B k) (ρ : B.Assignment A)
    (v : Fin k → A) : Prop :=
  c.head.elim False fun h => h.Holds ρ v

/-- A Horn clause holds at a valuation when its guard and all its body atoms
force its head. -/
def HornClause.Holds (c : HornClause L B k) (ρ : B.Assignment A) (v : Fin k → A) :
    Prop :=
  (c.guard.Realize v ∧ ∀ a ∈ c.body, a.Holds ρ v) → c.HeadHolds ρ v

/-- An assignment satisfies a program when every clause holds at every
valuation of the universally quantified variables. -/
def HornProgram.Holds (prog : HornProgram L B k) (ρ : B.Assignment A) : Prop :=
  ∀ v : Fin k → A, ∀ c ∈ prog, c.Holds ρ v

end Semantics

/-! ### Isomorphism-invariance -/

section Iso

variable {L : Language.{0, 0}} {B : SOBlock} {k : ℕ} {M N : Type}
variable [L.Structure M] [L.Structure N]

theorem HornClause.holds_equiv (e : M ≃[L] N) (c : HornClause L B k)
    (ρ : B.Assignment M) (v : Fin k → M) :
    c.Holds (B.mapAssign e.toEquiv ρ) (fun j => e (v j)) ↔ c.Holds ρ v := by
  have hhead : c.HeadHolds (B.mapAssign e.toEquiv ρ) (fun j => e (v j)) ↔
      c.HeadHolds ρ v := by
    rw [HornClause.HeadHolds, HornClause.HeadHolds]
    cases c.head with
    | none => exact Iff.rfl
    | some a => exact a.holds_equiv e ρ v
  refine imp_congr (and_congr ?_ ?_) hhead
  · exact StrongHomClass.realize_formula e c.guard
  · exact forall_congr' fun a => imp_congr Iff.rfl (a.holds_equiv e ρ v)

theorem HornProgram.holds_equiv (e : M ≃[L] N) (prog : HornProgram L B k)
    (ρ : B.Assignment M) : prog.Holds (B.mapAssign e.toEquiv ρ) ↔ prog.Holds ρ := by
  constructor
  · intro h v c hc
    exact (c.holds_equiv e ρ v).mp (h (fun j => e (v j)) c hc)
  · intro h v c hc
    have := (c.holds_equiv e ρ fun j => e.symm (v j)).mpr
      (h (fun j => e.symm (v j)) c hc)
    simpa using this

/-- **Horn satisfiability is isomorphism-invariant**: a program has a
satisfying assignment on one structure iff it has one on any isomorphic
structure. -/
private theorem exists_holds_equiv (e : M ≃[L] N) (prog : HornProgram L B k) :
    (∃ ρ : B.Assignment M, prog.Holds ρ) ↔ ∃ ρ : B.Assignment N, prog.Holds ρ := by
  constructor
  · rintro ⟨ρ, hρ⟩
    exact ⟨B.mapAssign e.toEquiv ρ, (prog.holds_equiv e ρ).mpr hρ⟩
  · rintro ⟨ρ, hρ⟩
    refine ⟨B.mapAssign e.toEquiv.symm ρ, ?_⟩
    have hkey : B.mapAssign e.toEquiv (B.mapAssign e.toEquiv.symm ρ) = ρ := by
      funext i x
      rw [SOBlock.mapAssign, SOBlock.mapAssign]
      exact congrArg _ (funext fun j => e.toEquiv.apply_symm_apply _)
    rw [← prog.holds_equiv e (B.mapAssign e.toEquiv.symm ρ), hkey]
    exact hρ

end Iso

/-! ### SO-Horn definability -/

variable {L : Language.{0, 0}}

/-- A decision problem is *SO-Horn definable* if, on nonempty finite *ordered*
structures, it is defined by an existential second-order sentence with a Horn
kernel: there is a block of relation variables and a Horn program over the
ordered expansion of the vocabulary such that the yes-instances are exactly
the structures admitting a satisfying assignment.

This is the SO-Horn analogue of `DescriptiveComplexity.SigmaSODefinable`; a single
block suffices, since existential second-order quantifiers merge.

The guards live over `L.sum Language.order`, and the equivalence is required
for *every* linear order on `A`, exactly as in
`DescriptiveComplexity.OrderedFOReduction`: since the problem itself does not see the
order, this is order-invariant SO-Horn definability. The order is not a
convenience here – it is the setting of Grädel's capture theorem, it is what
lets a Horn program traverse an unbounded conjunction along the order, and it
is forced by closure under ordered first-order reductions
(`DescriptiveComplexity.SigmaSOHornDefinable.of_orderedReduction`), which pull the
lexicographic order of the interpreted universe back into the guards. Nor can
the order be guessed away, as it is for the existential logics and – see
`DescriptiveComplexity.sotcDefinable_iff_free` – for SO(TC): a Horn kernel
cannot state that a guessed relation is total, two positive literals in one
clause not being Horn. -/
def SigmaSOHornDefinable [L.IsRelational] (P : DecisionProblem L) : Prop :=
  ∃ (B : SOBlock) (k : ℕ) (prog : HornProgram (L.sum Language.order) B k),
    ∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A],
      P A ↔ ∃ ρ : B.Assignment A, prog.Holds ρ

/-- SO-Horn definability only depends on the finite instances of a problem. -/
theorem sigmaSOHornDefinable_congr [L.IsRelational] {P Q : DecisionProblem L}
    (h : ∀ (A : Type) [L.Structure A] [Finite A], P A ↔ Q A) :
    SigmaSOHornDefinable P ↔ SigmaSOHornDefinable Q := by
  constructor <;> rintro ⟨B, k, prog, hprog⟩ <;> refine ⟨B, k, prog, ?_⟩ <;>
    intro A _ _ _ _
  · exact (h A).symm.trans (hprog A)
  · exact (h A).trans (hprog A)

end DescriptiveComplexity
