/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
module

public import LeanPool.DescriptiveCounting.Relativized

/-!
# Abstract complexity classes, the polynomial hierarchy, and NP-completeness

Complexity classes are introduced *abstractly*: a `ComplexityClass` assigns to
decision problems (over any relational vocabulary) a membership predicate and a
hardness predicate, and is required to be closed under (ordered) first-order
reductions – membership downward (`P ≤ᶠᵒ Q` and `Q ∈ 𝒞` give `P ∈ 𝒞`),
hardness upward (`P ≤ᶠᵒ Q` and `P` `𝒞`-hard give `Q` `𝒞`-hard). Since FO
reductions are computable in AC⁰ ⊆ LOGSPACE ⊆ PTIME, every class from
LOGSPACE up is closed in this sense, so this is a mild requirement. Note that
closure must be part of the *definition* of a complexity class rather than an
axiom quantified over all classes: arbitrary collections of problems need not
be closed, and the quantified axiom would be inconsistent.

This file also defines the complement of a decision problem
(`DecisionProblem.compl`, notation `Pᶜ`), and the observation that a reduction
complements: the same interpretation reduces `Pᶜ` to `Qᶜ`
(`DescriptiveComplexity.FOReduction.compl`).

The polynomial hierarchy itself – `DescriptiveComplexity.SigmaP`/`DescriptiveComplexity.PiP`, with
levels `k ≥ 1` *defined* by second-order quantifier alternation and level 0
polynomial time – lives in `DescriptiveComplexity.Hierarchy`; the Cook–Levin
theorem ([Cook 1971][cook1971complexity]; [Levin 1973][levin1973universal]) lives
with the problem SAT in `DescriptiveComplexity.Problems.Sat`, and
completeness theorems for other problems in their files under
`DescriptiveComplexity/Problems/` (e.g., `DescriptiveComplexity.threeCol_NP_complete` in
`DescriptiveComplexity.Problems.ThreeColorability`).
-/

@[expose] public section

namespace DescriptiveComplexity

open FirstOrder

open Language

/-- An abstract complexity class: a collection of decision problems (its
`Mem`bership predicate) together with a `Hard`ness predicate, closed under
(ordered) first-order reductions. Both predicates are left completely
abstract; the closure requirements are sound for every class containing
LOGSPACE, since (ordered) FO reductions are computable in AC⁰.

Hardness is a field of its own rather than a function of `Mem`. The classes of
this library take it to be cofinal hardness for their own members – equivalent
to “every member reduces to `P`” (`DescriptiveComplexity.cofinalHard_iff`) – and
are built by `DescriptiveComplexity.ComplexityClass.ofMem`, which supplies both
that reading of `Hard` and the three closure proofs it needs; keeping the field
abstract leaves room for the two that read hardness differently
(`DescriptiveComplexity.ComplexityClass.empty`, `DescriptiveComplexity.PH`). -/
structure ComplexityClass where
  /-- The problems belonging to the class. Use the notation `P ∈ 𝒞`. -/
  Mem : ∀ {L : Language.{0, 0}} [L.IsRelational], DecisionProblem L → Prop
  /-- The problems every problem of the class reduces to (“`𝒞`-hard”). -/
  Hard : ∀ {L : Language.{0, 0}} [L.IsRelational], DecisionProblem L → Prop
  /-- Membership travels backward along FO reductions. -/
  mem_of_foReduction : ∀ {L L' : Language.{0, 0}} [L.IsRelational] [L'.IsRelational]
    {P : DecisionProblem L} {Q : DecisionProblem L'}, (P ≤ᶠᵒ Q) → Mem Q → Mem P
  /-- Hardness travels forward along FO reductions. -/
  hard_of_foReduction : ∀ {L L' : Language.{0, 0}} [L.IsRelational] [L'.IsRelational]
    {P : DecisionProblem L} {Q : DecisionProblem L'}, (P ≤ᶠᵒ Q) → Hard P → Hard Q
  /-- Membership travels backward along ordered FO reductions. -/
  mem_of_orderedReduction : ∀ {L L' : Language.{0, 0}} [L.IsRelational] [L'.IsRelational]
    {P : DecisionProblem L} {Q : DecisionProblem L'}, (P ≤ᶠᵒ[≤] Q) → Mem Q → Mem P
  /-- Hardness travels forward along ordered FO reductions. -/
  hard_of_orderedReduction : ∀ {L L' : Language.{0, 0}} [L.IsRelational] [L'.IsRelational]
    {P : DecisionProblem L} {Q : DecisionProblem L'}, (P ≤ᶠᵒ[≤] Q) → Hard P → Hard Q
  /-- Hardness travels forward along relativized ordered FO reductions – the
  reductions with a definable target universe, needed for spanning problems. -/
  hard_of_relOrderedReduction : ∀ {L L' : Language.{0, 0}} [L.IsRelational] [L'.IsRelational]
    {P : DecisionProblem L} {Q : DecisionProblem L'}, (P ≤ʳᶠᵒ[≤] Q) → Hard P → Hard Q
  /-- Complexity classes speak about *finite* instances only: membership does
  not depend on the behavior of a problem on infinite structures. -/
  mem_congr_finite : ∀ {L : Language.{0, 0}} [L.IsRelational] {P Q : DecisionProblem L},
    (∀ (A : Type) [L.Structure A] [Finite A], P A ↔ Q A) → (Mem P ↔ Mem Q)
  /-- Hardness, too, only depends on the finite instances of a problem. -/
  hard_congr_finite : ∀ {L : Language.{0, 0}} [L.IsRelational] {P Q : DecisionProblem L},
    (∀ (A : Type) [L.Structure A] [Finite A], P A ↔ Q A) → (Hard P ↔ Hard Q)

/-- `P ∈ 𝒞`: the problem `P` belongs to the complexity class `𝒞`. (This
overloads the `∈` notation; the `Membership` class cannot be used here since
the element type `DecisionProblem L` is not determined by `ComplexityClass`.) -/
scoped notation:50 P:51 " ∈ " C:51 => ComplexityClass.Mem C P

namespace ComplexityClass

/-- Two complexity classes with the same members and the same hard problems
are equal: the remaining fields are proofs. -/
theorem ext {C₁ C₂ : ComplexityClass}
    (hMem : ∀ {L : Language.{0, 0}} [L.IsRelational] (P : DecisionProblem L),
      C₁.Mem P ↔ C₂.Mem P)
    (hHard : ∀ {L : Language.{0, 0}} [L.IsRelational] (P : DecisionProblem L),
      C₁.Hard P ↔ C₂.Hard P) :
    C₁ = C₂ := by
  obtain ⟨M₁, H₁, _, _, _, _, _, _, _⟩ := C₁
  obtain ⟨M₂, H₂, _, _, _, _, _, _, _⟩ := C₂
  have hM : @M₁ = @M₂ := by
    funext L inst P
    exact propext (hMem P)
  have hH : @H₁ = @H₂ := by
    funext L inst P
    exact propext (hHard P)
  subst hM
  subst hH
  rfl

/-- The empty complexity class: no members, and every problem vacuously hard
(there is nothing that would have to reduce to it). It stands for a level of a
hierarchy that has no logical characterization. -/
private def empty : ComplexityClass where
  Mem _ := False
  Hard _ := True
  mem_of_foReduction _ h := h
  hard_of_foReduction _ _ := trivial
  mem_of_orderedReduction _ h := h
  hard_of_orderedReduction _ _ := trivial
  hard_of_relOrderedReduction _ _ := trivial
  mem_congr_finite _ := Iff.rfl
  hard_congr_finite _ := Iff.rfl

/-- Inclusion of complexity classes. -/
instance : HasSubset ComplexityClass :=
  ⟨fun C D => ∀ ⦃L : Language.{0, 0}⦄ [L.IsRelational] ⦃P : DecisionProblem L⦄,
    C.Mem P → D.Mem P⟩

variable (C : ComplexityClass) {L : Language.{0, 0}} [L.IsRelational]

/-- A problem is complete for a class if it belongs to it and is hard for
it. -/
def Complete (P : DecisionProblem L) : Prop :=
  P ∈ C ∧ C.Hard P

theorem Complete.mem {P : DecisionProblem L} (h : C.Complete P) : P ∈ C := h.1

theorem Complete.hard {P : DecisionProblem L} (h : C.Complete P) : C.Hard P := h.2

end ComplexityClass

/-- The complement of a decision problem: its yes-instances are the
no-instances of `P`. -/
protected def DecisionProblem.compl {L : Language.{0, 0}} [L.IsRelational]
    (P : DecisionProblem L) :
    DecisionProblem L where
  Holds := fun A inst => ¬@DecisionProblem.Holds L _ P A inst
  iso_invariant := fun e => not_congr (P.iso_invariant e)

instance {L : Language.{0, 0}} [L.IsRelational] : Compl (DecisionProblem L) :=
  ⟨DecisionProblem.compl⟩

@[simp]
theorem DecisionProblem.compl_compl {L : Language.{0, 0}} [L.IsRelational]
    (P : DecisionProblem L) :
    Pᶜᶜ = P :=
  DecisionProblem.ext fun _ _ => not_not

/-- **Reductions complement**: the very same interpretation reduces `Pᶜ` to
`Qᶜ`, since the correctness of a reduction is an equivalence. This is what
turns a hardness discharge for a `Σ`-level into one for the dual `Π`-level;
see `DescriptiveComplexity.taut_hard_of_piSODefinable`. -/
def FOReduction.compl {L L' : Language.{0, 0}} [L.IsRelational] [L'.IsRelational]
    {P : DecisionProblem L} {Q : DecisionProblem L'} (f : P ≤ᶠᵒ Q) : Pᶜ ≤ᶠᵒ Qᶜ :=
  letI := f.tagFinite
  letI := f.tagNonempty
  { Tag := f.Tag
    dim := f.dim
    toInterpretation := f.toInterpretation
    correct := fun A _ _ _ => not_congr (f.correct A) }

@[inherit_doc FOReduction.compl]
def OrderedFOReduction.compl {L L' : Language.{0, 0}} [L.IsRelational] [L'.IsRelational]
    {P : DecisionProblem L} {Q : DecisionProblem L'} (f : P ≤ᶠᵒ[≤] Q) : Pᶜ ≤ᶠᵒ[≤] Qᶜ :=
  letI := f.tagFinite
  letI := f.tagNonempty
  { Tag := f.Tag
    dim := f.dim
    toInterpretation := f.toInterpretation
    correct := fun A _ _ _ _ => not_congr (f.correct A) }

end DescriptiveComplexity
