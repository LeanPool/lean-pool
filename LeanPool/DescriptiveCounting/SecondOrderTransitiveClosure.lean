/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
module

public import LeanPool.DescriptiveCounting.SecondOrder

/-!
# SO(TC): second-order logic with transitive closure

The logic that captures polynomial space on ordered structures ([Immerman
1999][immerman1999descriptive], ch. 10): a transitive closure taken not over
tuples of *elements*, as in `DescriptiveComplexity.TransitiveClosure`, but over
tuples of *relations*. A state of the walk is an assignment of relations to a
second-order quantifier block, so a structure of size `n` has `2^(n^a)` states
and a walk through them is a computation of exponentially many steps – each one
first-order, hence cheap – on a polynomial amount of remembered information.
That is exactly the resource PSPACE measures.

## Why no fragment of plain SO would do

`DescriptiveComplexity.SigmaSODefinable` and its levels give the polynomial
hierarchy, and plain second-order logic gives `PH` as a whole
([Fagin 1974][fagin1974generalized]; [Stockmeyer
1976][stockmeyer1976polynomial]), so no fragment of plain SO can define PSPACE
without collapsing PH. Some iteration operator is unavoidable, and the
transitive closure is the cheapest one: it needs no positivity condition, no
stage or inflationary machinery, and no syntax of its own.

## The operator as data

As in `DescriptiveComplexity.TransitiveClosure` (and for the same reasons – not
touching Mathlib's `FirstOrder.Language.BoundedFormula`), the operator lives at
the Lean level. A `DescriptiveComplexity.SOTCSpec` bundles

* a second-order quantifier block `B`, whose assignments are the *states* of
  the walk;
* a `step` **sentence** over the base vocabulary expanded by the order and by
  *two* copies of the block – the current state and the next one;
* `src` and `tgt` sentences over one copy of the block.

Reachability itself is `Relation.ReflTransGen`, and a structure is accepted
when some `tgt` state is reachable from some `src` state
(`DescriptiveComplexity.SOTCSpec.Accepts`). A single application of `TC` in front
of a first-order matrix is taken as the definition, exactly as a single
existential block is taken as the definition of `Σ₁`-definability.

## No modes, no tuples

`DescriptiveComplexity.TCSpec` carries a finite *mode* beside its tuple of elements,
because a tuple of elements cannot hold finite data on a one-element universe.
Here nothing of the sort is needed: a relation variable of arity `0` *is* a
bit, so finite control is already inside a block, and a relation variable of
arity `1` holding a singleton is an element register. A state is therefore a
bare `DescriptiveComplexity.SOBlock.Assignment` and the walk carries no extra
components – which also makes the pullback of a specification through an
interpretation (`DescriptiveComplexity.SecondOrderTransitiveClosurePull`) purely a
matter of pulling the block back.

## What this file contains

The semantics (`DescriptiveComplexity.SOTCSpec.Step`,
`DescriptiveComplexity.SOTCSpec.Reach`, `DescriptiveComplexity.SOTCSpec.Accepts`),
its isomorphism-invariance, the transfer of acceptance along a bijection of
states (`DescriptiveComplexity.SOTCSpec.accepts_congr`, the workhorse of the
pullback), and the definability notion
`DescriptiveComplexity.SOTCDefinable`. The class `DescriptiveComplexity.PSPACE`
itself is built on top of it in `DescriptiveComplexity.PSpace`, once closure
under reductions is available.
-/

@[expose] public section

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}}

/-! ### Expanding a structure by one or two copies of a block -/

section Expand

/-- `FirstOrder.Language.StrongHomClass.realize_sentence` with the two structures
passed explicitly rather than by instance search. The structures a walk is read
against are built from block assignments (`DescriptiveComplexity.SOBlock.structure₁`,
`DescriptiveComplexity.SOBlock.structure₂`) and are never instances, so every
transport in this file and in
`DescriptiveComplexity.SecondOrderTransitiveClosurePull` goes through this form. -/
theorem realize_sentence_of_equiv {L' : Language.{0, 0}} {M N : Type}
    {instM : L'.Structure M} {instN : L'.Structure N}
    (e : @Language.Equiv L' M N instM instN) (φ : L'.Sentence) :
    @Sentence.Realize L' M instM φ ↔ @Sentence.Realize L' N instN φ :=
  letI := instM
  letI := instN
  StrongHomClass.realize_sentence e φ

/-- The structure over `L` expanded by one copy of a block's vocabulary,
interpreted by an assignment. -/
@[instance_reducible]
def SOBlock.structure₁ (B : SOBlock) {A : Type} [inst : L.Structure A]
    (ρ : B.Assignment A) : (L.sum B.lang).Structure A :=
  @sumStructure L B.lang A inst (B.structure ρ)

/-- The structure over `L` expanded by *two* copies of a block's vocabulary –
the current state and the next one – interpreted by two assignments. -/
@[instance_reducible]
def SOBlock.structure₂ (B : SOBlock) {A : Type} [inst : L.Structure A]
    (ρ σ : B.Assignment A) : ((L.sum B.lang).sum B.lang).Structure A :=
  @sumStructure (L.sum B.lang) B.lang A (B.structure₁ ρ) (B.structure σ)

/-- `DescriptiveComplexity.SOBlock.extendEquiv` with the two structures passed
explicitly rather than by instance search, for the same reason as
`DescriptiveComplexity.realize_sentence_of_equiv`: the layers a walk is read
against are block expansions, which are not instances. -/
def SOBlock.extendEquiv' (B : SOBlock) {L' : Language.{0, 0}} {M N : Type}
    {instM : L'.Structure M} {instN : L'.Structure N}
    (e : @Language.Equiv L' M N instM instN) (ρ : B.Assignment M) :
    @Language.Equiv (L'.sum B.lang) M N (B.structure₁ ρ)
      (B.structure₁ (B.mapAssign e.toEquiv ρ)) :=
  letI := instM
  letI := instN
  B.extendEquiv e ρ

/-- Transport of block assignments along an equivalence of universes, as an
equivalence: the states of the walk are in bijection with the states of the
transported walk. -/
def SOBlock.assignEquiv (B : SOBlock) {A A' : Type} (e : A ≃ A') :
    B.Assignment A ≃ B.Assignment A' where
  toFun := B.mapAssign e
  invFun := B.mapAssign e.symm
  left_inv ρ := by
    funext i x
    exact congrArg (ρ i) (funext fun j => e.symm_apply_apply (x j))
  right_inv ρ := by
    funext i x
    exact congrArg (ρ i) (funext fun j => e.apply_symm_apply (x j))

@[simp]
theorem SOBlock.assignEquiv_apply (B : SOBlock) {A A' : Type} (e : A ≃ A')
    (ρ : B.Assignment A) : B.assignEquiv e ρ = B.mapAssign e ρ :=
  rfl

/-- An `L`-isomorphism extends to `L` expanded by two copies of a block, the
two assignments being transported. -/
def SOBlock.extendEquiv₂ (B : SOBlock) {A A' : Type} [L.Structure A] [L.Structure A']
    (e : A ≃[L] A') (ρ σ : B.Assignment A) :
    @Language.Equiv ((L.sum B.lang).sum B.lang) A A'
      (B.structure₂ ρ σ) (B.structure₂ (B.mapAssign e.toEquiv ρ) (B.mapAssign e.toEquiv σ)) :=
  letI := B.structure₁ (L := L) ρ
  letI := B.structure₁ (L := L) (B.mapAssign e.toEquiv ρ)
  B.extendEquiv (B.extendEquiv e ρ) σ

end Expand

/-! ### Specifications -/

/-- A single-`TC` definition over a second-order block: the states of the walk
are the assignments of the block `B`, and the transition, source and target
conditions are first-order sentences over the base vocabulary expanded by the
order and by copies of the block. The transition sentence sees two copies –
the current state and the next one.

The order is visible to all three sentences, as the ordered setting of the
capture theorem allows; the problem itself does not see it (see
`DescriptiveComplexity.SOTCDefinable`). -/
structure SOTCSpec (L : Language.{0, 0}) : Type 1 where
  /-- The block whose assignments are the states of the walk. -/
  B : SOBlock
  /-- The transition sentence, over two copies of the block: the current state
  reads the first copy, the next state the second. -/
  step : (((L.sum Language.order).sum B.lang).sum B.lang).Sentence
  /-- The sentence defining the admissible starting states. -/
  src : ((L.sum Language.order).sum B.lang).Sentence
  /-- The sentence defining the accepting states. -/
  tgt : ((L.sum Language.order).sum B.lang).Sentence

namespace SOTCSpec

section Semantics

variable (spec : SOTCSpec L) {A : Type} [L.Structure A] [LinearOrder A]

variable (A) in
/-- A state of the walk: an assignment of the block. -/
abbrev State : Type := spec.B.Assignment A

/-- One step of the walk: the transition sentence, read with the current state
in the first copy of the block and the next state in the second. -/
def Step (ρ σ : spec.State A) : Prop :=
  @Sentence.Realize _ A (spec.B.structure₂ (L := L.sum Language.order) ρ σ) spec.step

/-- Reachability in the walk: the reflexive-transitive closure of
`DescriptiveComplexity.SOTCSpec.Step`. -/
abbrev Reach : spec.State A → spec.State A → Prop :=
  Relation.ReflTransGen spec.Step

/-- A state is a starting state when it satisfies the source sentence. -/
def IsSrc (ρ : spec.State A) : Prop :=
  @Sentence.Realize _ A (spec.B.structure₁ (L := L.sum Language.order) ρ) spec.src

/-- A state is accepting when it satisfies the target sentence. -/
def IsTgt (ρ : spec.State A) : Prop :=
  @Sentence.Realize _ A (spec.B.structure₁ (L := L.sum Language.order) ρ) spec.tgt

variable (A) in
/-- The structure is accepted: some accepting state is reachable from some
starting state. -/
def Accepts : Prop :=
  ∃ ρ σ : spec.State A, spec.IsSrc ρ ∧ spec.IsTgt σ ∧ spec.Reach ρ σ

end Semantics

/-! ### Transfer along a bijection of states

Acceptance only depends on the walk up to a bijection of its states. Stated for
two specifications over two vocabularies, since the pullback through an
interpretation relates a specification over the base structure to one over the
interpreted structure. -/

section Transfer

variable {L' : Language.{0, 0}} {spec₁ : SOTCSpec L} {spec₂ : SOTCSpec L'}
  {A B : Type} [L.Structure A] [LinearOrder A] [L'.Structure B] [LinearOrder B]

private theorem reach_map (e : spec₁.State A ≃ spec₂.State B)
    (hstep : ∀ ρ σ, spec₁.Step ρ σ ↔ spec₂.Step (e ρ) (e σ)) {ρ σ : spec₁.State A}
    (h : spec₁.Reach ρ σ) : spec₂.Reach (e ρ) (e σ) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail c d _ hcd ih => exact ih.tail ((hstep c d).mp hcd)

/-- **Acceptance transfers along a bijection of states** carrying steps to
steps and endpoints to endpoints. -/
theorem accepts_congr (e : spec₁.State A ≃ spec₂.State B)
    (hstep : ∀ ρ σ, spec₁.Step ρ σ ↔ spec₂.Step (e ρ) (e σ))
    (hsrc : ∀ ρ, spec₁.IsSrc ρ ↔ spec₂.IsSrc (e ρ))
    (htgt : ∀ ρ, spec₁.IsTgt ρ ↔ spec₂.IsTgt (e ρ)) :
    spec₁.Accepts A ↔ spec₂.Accepts B := by
  have hstep' : ∀ ρ σ, spec₂.Step ρ σ ↔ spec₁.Step (e.symm ρ) (e.symm σ) := by
    intro ρ σ
    rw [hstep (e.symm ρ) (e.symm σ), e.apply_symm_apply, e.apply_symm_apply]
  constructor
  · rintro ⟨ρ, σ, hρ, hσ, h⟩
    exact ⟨e ρ, e σ, (hsrc ρ).mp hρ, (htgt σ).mp hσ, reach_map e hstep h⟩
  · rintro ⟨ρ, σ, hρ, hσ, h⟩
    refine ⟨e.symm ρ, e.symm σ, ?_, ?_, reach_map e.symm hstep' h⟩
    · rw [hsrc, e.apply_symm_apply]
      exact hρ
    · rw [htgt, e.apply_symm_apply]
      exact hσ

end Transfer

/-! ### Isomorphism-invariance -/

section Iso

variable (spec : SOTCSpec L) {A A' : Type} [L.Structure A] [LinearOrder A]
variable [L.Structure A'] [LinearOrder A']

/-- One step is preserved by an isomorphism of the ordered expansions, the
states being transported. -/
private theorem step_equiv (e : A ≃[L.sum Language.order] A') (ρ σ : spec.State A) :
    spec.Step ρ σ ↔ spec.Step (spec.B.mapAssign e.toEquiv ρ) (spec.B.mapAssign e.toEquiv σ) :=
  realize_sentence_of_equiv (spec.B.extendEquiv₂ e ρ σ) spec.step

/-- Starting states are preserved by an isomorphism of the ordered
expansions. -/
private theorem isSrc_equiv (e : A ≃[L.sum Language.order] A') (ρ : spec.State A) :
    spec.IsSrc ρ ↔ spec.IsSrc (spec.B.mapAssign e.toEquiv ρ) :=
  realize_sentence_of_equiv (spec.B.extendEquiv e ρ) spec.src

/-- Accepting states are preserved by an isomorphism of the ordered
expansions. -/
private theorem isTgt_equiv (e : A ≃[L.sum Language.order] A') (ρ : spec.State A) :
    spec.IsTgt ρ ↔ spec.IsTgt (spec.B.mapAssign e.toEquiv ρ) :=
  realize_sentence_of_equiv (spec.B.extendEquiv e ρ) spec.tgt

/-- **Acceptance is isomorphism-invariant** (for isomorphisms of the ordered
expansions, the order being visible to the sentences). -/
private theorem accepts_equiv (e : A ≃[L.sum Language.order] A') :
    spec.Accepts A ↔ spec.Accepts A' :=
  accepts_congr (spec.B.assignEquiv e.toEquiv) (spec.step_equiv e) (spec.isSrc_equiv e)
    (spec.isTgt_equiv e)

end Iso

end SOTCSpec

/-! ### SO(TC) definability -/

/-- A decision problem is *SO(TC) definable* if, on nonempty finite *ordered*
structures, it is defined by a single transitive closure over the assignments
of a second-order quantifier block: there is a `DescriptiveComplexity.SOTCSpec`
whose accepting states are reachable from its starting states exactly on the
yes-instances.

As for `DescriptiveComplexity.TCDefinable` and the clausal fragments, the
equivalence is required for *every* linear order on the universe, so this is
order-invariant SO(TC) definability: the problem itself does not see the order,
while the three sentences may. Unlike those, however, SO(TC) does not *need* the
order: a walk can guess it into its own state, so this notion coincides with the
order-free `DescriptiveComplexity.SOTCDefinableFree`
(`DescriptiveComplexity.sotcDefinable_iff_free`, in
`DescriptiveComplexity.SecondOrderTransitiveClosureFree`). -/
def SOTCDefinable [L.IsRelational] (P : DecisionProblem L) : Prop :=
  ∃ spec : SOTCSpec L,
    ∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A],
      P A ↔ spec.Accepts A

/-- SO(TC) definability only depends on the finite instances of a problem.
Registered in the Lax archive as
[`Lax134656.PSPACEClosure.PSPACE_mem_congr_finite`](https://laxarchive.org/lax-134656/Lax134656.PSPACEClosure.html#s-Lax134656.PSPACEClosure.PSPACE_mem_congr_finite). -/
theorem sotcDefinable_congr [L.IsRelational] {P Q : DecisionProblem L}
    (h : ∀ (A : Type) [L.Structure A] [Finite A], P A ↔ Q A) :
    SOTCDefinable P ↔ SOTCDefinable Q := by
  constructor <;> rintro ⟨spec, hspec⟩ <;> refine ⟨spec, ?_⟩ <;> intro A _ _ _ _
  · exact (h A).symm.trans (hspec A)
  · exact (h A).trans (hspec A)

end DescriptiveComplexity
