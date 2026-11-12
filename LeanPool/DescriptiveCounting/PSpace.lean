/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
module

public import LeanPool.DescriptiveCounting.SecondOrderTransitiveClosurePull
public import LeanPool.DescriptiveCounting.Hierarchy

/-!
# PSPACE, by second-order transitive closure

**The class PSPACE**: the problems definable in SO(TC), second-order logic with
a transitive closure taken over assignments of a relation block
(`DescriptiveComplexity.SOTCDefinable`), which captures polynomial space on ordered
structures ([Immerman 1999][immerman1999descriptive], ch. 10). This is the same
move as defining `PTIME` by the Horn fragment, `NL` by the Krom fragment and
`NP` by `Σ₁`-definability: the class is a *definition*, not an axiom, and it is
a bona fide `DescriptiveComplexity.ComplexityClass` because SO(TC) definability is
closed under (ordered) first-order reductions – the block and the three
sentences all survive the pullback, see
`DescriptiveComplexity.SecondOrderTransitiveClosurePull`.

## Why the states are relations

An SO(TC) walk remembers an assignment of relations, i.e., `n^a` bits on a
universe of size `n`, and may take exponentially many steps to reach its
target. That is precisely a polynomially space-bounded computation: the
configuration is the remembered assignment, and the (first-order) transition
sentence is one step of the machine. Immerman's capture theorem is the
statement that nothing is lost either way; here, as everywhere in this library,
the logic is taken as the definition of the class and the capture theorem is a
statement about machines, to be proved against a machine model rather than
assumed (see `DescriptiveComplexity.Machines`).

## What is *not* free here

* **PSPACE = coPSPACE** is not the definitional duality that gives `PiP k` from
  `SigmaP k`: the complement of an SO(TC) definable problem is not *obviously*
  SO(TC) definable. It is a genuine theorem, and it is proved – downstream, in
  `DescriptiveComplexity.PSpaceCompl`, once QSAT is available: every SO(TC)
  definable problem reduces to QSAT, complementing a reduction is free, and the
  walk that decides QSAT is deterministic, so reading its answer the other way
  round decides the complement.
* **PH ⊆ PSPACE** is not a syntactic inclusion either: a `Σₖ` sentence is not a
  walk. It too is proved downstream, in `DescriptiveComplexity.PSpaceHierarchy`,
  by alternating that complement with the other closure property of SO(TC) – a
  walk can guess a block into its own state and never touch it again – along the
  quantifier prefix. What *is* immediate here is the bottom of the tower,
  `NP ⊆ PSPACE` (`DescriptiveComplexity.NP_subset_PSPACE`): an existential block
  is a walk that guesses its state in one step and then stops, so
  `Σ₁`-definability is SO(TC) definability with an empty transition relation.
  Everything below NP follows by composition.
-/

@[expose] public section

namespace DescriptiveComplexity

open FirstOrder

open Language

variable {L : Language.{0, 0}}

/-- **The class PSPACE**: the problems definable in SO(TC), second-order logic
with a transitive closure over assignments of a relation block, which captures
polynomial space on ordered structures ([Immerman
1999][immerman1999descriptive]).

Hardness is stated cofinally, exactly as for the other classes of this library
(`DescriptiveComplexity.CofinalHard`), which is the usual notion,
`DescriptiveComplexity.hard_PSPACE_iff`. -/
noncomputable def PSPACE : ComplexityClass :=
  .ofMem (fun P => SOTCDefinable P)
    (fun f h => h.of_foReduction f)
    (fun f h => h.of_orderedReduction f)
    (fun h => sotcDefinable_congr h)

/-- Membership in PSPACE is exactly SO(TC) definability, by definition. -/
private theorem mem_PSPACE_iff
    [L.IsRelational] (P : DecisionProblem L) : P ∈ PSPACE ↔ SOTCDefinable P :=
  Iff.rfl

/-- PSPACE-hardness is the usual notion: every SO(TC) definable problem
reduces to `P`. -/
private theorem hard_PSPACE_iff [L.IsRelational] (P : DecisionProblem L) :
    PSPACE.Hard P ↔
      ∀ {L'' : Language.{0, 0}} [L''.IsRelational] (Q : DecisionProblem L''),
        SOTCDefinable Q → Nonempty (Q ≤ʳᶠᵒ[≤] P) :=
  cofinalHard_iff _ P

/-- A problem is PSPACE-hard as soon as every SO(TC) definable problem reduces
to it; the discharge shape shared by every PSPACE-hardness proof of the
catalog. -/
theorem PSPACE_hard_of_sotcDefinable [L.IsRelational] (P : DecisionProblem L)
    (h : ∀ {L'' : Language.{0, 0}} [L''.IsRelational] (Q : DecisionProblem L''),
      SOTCDefinable Q → Nonempty (Q ≤ʳᶠᵒ[≤] P)) : PSPACE.Hard P :=
  (hard_PSPACE_iff P).mpr h

/-- coPSPACE, the complement class of PSPACE. That it coincides with PSPACE
(Savitch) is *not* proved here (see the module docstring). -/
noncomputable abbrev coPSPACE : ComplexityClass := PSPACE.compl

/-! ### `NP ⊆ PSPACE`: an existential block is a one-step walk

A `Σ₁` definition `∃ R. φ(R)` is the SO(TC) specification whose states are the
assignments of the block, whose transition relation is *empty*, and whose
starting and accepting states are both the ones satisfying `φ`. Its walks are
the one-state walks, so it accepts exactly when some assignment satisfies `φ`.

The only work is that an SO(TC) specification's sentences live over the
*ordered* expansion of the vocabulary, so the kernel has to be moved along the
language map that inserts the order symbol. -/

section SigmaOne

/-- The language map inserting the order vocabulary underneath a block
expansion: the kernel of a `Σ₁` definition, which does not see the order, read
as a sentence of the vocabulary an SO(TC) specification uses. -/
def blockOrderLift (L : Language.{0, 0}) (B : SOBlock) :
    (L.sum B.lang) →ᴸ ((L.sum Language.order).sum B.lang) :=
  LHom.sumMap LHom.sumInl (LHom.id B.lang)

variable {A : Type} [L.Structure A] [LinearOrder A] (B : SOBlock) (ρ : B.Assignment A)

/-- Inserting the order symbol does not change how anything is interpreted. -/
private theorem blockOrderLift_isExpansionOn :
    @LHom.IsExpansionOn _ _ (blockOrderLift L B) A
      (B.structure₁ (L := L) ρ) (B.structure₁ (L := L.sum Language.order) ρ) := by
  let := B.structure₁ (L := L) ρ
  let := B.structure₁ (L := L.sum Language.order) ρ
  refine ⟨fun {n} f x => ?_, fun {n} r x => ?_⟩
  · cases f with
    | inl g => rfl
    | inr g => exact g.elim
  · cases r with
    | inl s => rfl
    | inr s => rfl

/-- The lifted kernel realizes over the ordered expansion exactly as the
original kernel realizes over the base expansion. -/
private theorem realize_blockOrderLift (φ : (L.sum B.lang).Sentence) :
    @Sentence.Realize _ A (B.structure₁ (L := L.sum Language.order) ρ)
        ((blockOrderLift L B).onSentence φ) ↔
      @Sentence.Realize _ A (B.structure₁ (L := L) ρ) φ :=
  letI := B.structure₁ (L := L) ρ
  letI := B.structure₁ (L := L.sum Language.order) ρ
  haveI := blockOrderLift_isExpansionOn (L := L) B ρ
  LHom.realize_onSentence (M := A) (blockOrderLift L B) φ

variable (L) in
/-- The specification of a `Σ₁` definition: the states are the assignments of
the block, there are no transitions, and the accepting states are the ones
satisfying the kernel. -/
def sigmaOneSpec (B : SOBlock) (φ : (L.sum B.lang).Sentence) : SOTCSpec L where
  B := B
  step := ⊥
  src := (blockOrderLift L B).onSentence φ
  tgt := (blockOrderLift L B).onSentence φ

/-- The one-step walk of a `Σ₁` definition accepts exactly when the kernel is
satisfiable in the block. -/
private theorem sigmaOneSpec_accepts_iff (φ : (L.sum B.lang).Sentence) :
    (sigmaOneSpec L B φ).Accepts A ↔
      ∃ ρ : B.Assignment A, @Sentence.Realize _ A (B.structure₁ (L := L) ρ) φ := by
  have hstep : ∀ ρ σ : B.Assignment A, ¬(sigmaOneSpec L B φ).Step ρ σ := fun _ _ h => h
  constructor
  · rintro ⟨ρ, σ, hρ, -, -⟩
    exact ⟨ρ, (realize_blockOrderLift B ρ φ).mp hρ⟩
  · rintro ⟨ρ, hρ⟩
    exact ⟨ρ, ρ, (realize_blockOrderLift B ρ φ).mpr hρ,
      (realize_blockOrderLift B ρ φ).mpr hρ, Relation.ReflTransGen.refl⟩

/-- **Every `Σ₁`-definable problem is SO(TC) definable**: guess the block in
the state, take no step. -/
private theorem SOTCDefinable.of_sigmaSODefinable [L.IsRelational] {P : DecisionProblem L}
    (h : SigmaSODefinable 1 P) : SOTCDefinable P := by
  obtain ⟨Bs, hlen, φ, hφ⟩ := h
  match Bs, hlen with
  | [B], _ =>
    refine ⟨sigmaOneSpec L B φ, ?_⟩
    intro A _ _ _ _
    exact (hφ A).trans (sigmaOneSpec_accepts_iff B φ).symm

end SigmaOne

/-- **`NP ⊆ PSPACE`**: NP is `Σ₁`-definability (Fagin) and PSPACE is SO(TC)
definability, and an existential block is a walk that guesses its state and
stops.
Registered in the Lax archive as
[`Lax134656.HierarchyInPSPACE.NP_subset_PSPACE`](https://laxarchive.org/lax-134656/Lax134656.HierarchyInPSPACE.html#s-Lax134656.HierarchyInPSPACE.NP_subset_PSPACE). -/
theorem NP_subset_PSPACE : NP ⊆ PSPACE :=
  fun _ _ _ h => SOTCDefinable.of_sigmaSODefinable h

end DescriptiveComplexity
