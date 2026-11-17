/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
module

public import LeanPool.DescriptiveCounting.FixedPointInflationary
public import LeanPool.DescriptiveCounting.RelComposition
public import LeanPool.DescriptiveCounting.SecondOrderLift

/-!
# FO(LFP) reductions: the polynomial-time reductions of a machine-free library

A first-order reduction (`DescriptiveComplexity.FOReduction` and its ordered
and relativized variants) is computable in AC⁰; the textbook notion of
reduction for the classes from PTIME up is the *polynomial-time* one. In a
library without machines, a polynomial-time reduction is an interpretation
whose defining formulas belong to a logic capturing PTIME: Immerman's
**FO(LFP) reductions** ([Immerman 1999][immerman1999descriptive], ch. 3). This
file defines them, and embeds every first-order reduction notion of the library
into them – the statement that a first-order reduction is in particular a
polynomial-time one.

## The notion

A `DescriptiveComplexity.LFPInterpretation` is a relativized first-order
interpretation (`DescriptiveComplexity.RelFOInterpretation`) whose formulas
may read, beside the symbols of the base structure, the relations computed by a
simultaneous inflationary induction over it (`DescriptiveComplexity.StepDef`,
the library's normal form for FO(≤, IFP) = FO(LFP) = PTIME on ordered
structures). The induction is computed once, its value expands the base
structure (`DescriptiveComplexity.LFPInterpretation.expStructure`), and the
interpretation is read over the expansion. This is the clausal normal form
Immerman's reductions take: one fixed point, then first-order formulas.

Two design points.

* **The base vocabulary is a parameter.** An `LFPInterpretation L L'` reads an
  induction over `L` itself; the ordered reduction notion instantiates `L` with
  the ordered expansion `L.sum Language.order`. Keeping the base free is what
  lets the closure theorems be proved once, by an induction on quantifier
  blocks, and specialized to the ordered reading at the end.
* **The interpretation is relativized** (it carries a domain formula). The
  library's hardness travels along relativized reductions `≤ʳᶠᵒ[≤]`, and a
  relativized reduction cannot be turned into a whole-universe one – junk
  points cannot be dropped – so a polynomial-time notion that did not carry a
  domain formula would not contain the library's own hardness. Classically a
  polynomial-time reduction may output an instance of any size, and the domain
  formula is what stands for that freedom here.

`DescriptiveComplexity.LFPReduction P Q`, notation `P ≤ˡᶠᵖ Q`, is an ordered
`LFPInterpretation` mapping yes-instances exactly to yes-instances, for every
linear order on the input – order-invariance, exactly as for
`DescriptiveComplexity.OrderedFOReduction`.

## The embeddings

`DescriptiveComplexity.RelOrderedFOReduction.toLFP` (and the two variants
`OrderedFOReduction.toLFP`, `FOReduction.toLFP`) read a first-order reduction
as an FO(LFP) reduction with no induction at all: **every first-order reduction
is a polynomial-time reduction**. The converse fails, and provably so:
`DescriptiveComplexity.exists_lfpReduction_not_orderedReduction`
(`DescriptiveComplexity.FixedPointReductionStrict`) exhibits a target to which
EVEN reduces in FO(LFP) but not in FO(≤).

## What is proved elsewhere

* transitivity, `DescriptiveComplexity.LFPReduction.trans`
  (`DescriptiveComplexity.FixedPointReductionComposition`);
* closure of PTIME, NP and coNP under `≤ˡᶠᵖ`, and hardness stated with it –
  implied by the library's own hardness
  (`DescriptiveComplexity.FixedPointReductionClosure`).
-/

@[expose] public section

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### Lifting a relativized interpretation along a vocabulary map of its source -/

section LiftSource

variable {L₀ L₁ L' : Language.{0, 0}} {Tag : Type} {dim : ℕ}

/-- A relativized interpretation read over a larger source vocabulary: every
formula is transported along the vocabulary map. -/
def RelFOInterpretation.liftSource (φ : L₀ →ᴸ L₁) (I : RelFOInterpretation L₀ L' Tag dim) :
    RelFOInterpretation L₁ L' Tag dim where
  relFormula R t := φ.onFormula (I.relFormula R t)
  domFormula t := φ.onFormula (I.domFormula t)

variable (φ : L₀ →ᴸ L₁) (I : RelFOInterpretation L₀ L' Tag dim)
variable {A : Type} {inst₀ : L₀.Structure A} {inst₁ : L₁.Structure A}

theorem RelFOInterpretation.realize_liftSource_domFormula
    (hexp : @LHom.IsExpansionOn _ _ φ A inst₀ inst₁) (t : Tag) (w : Fin dim → A) :
    (@Formula.Realize _ A inst₁ _ ((I.liftSource φ).domFormula t) w) ↔
      @Formula.Realize _ A inst₀ _ (I.domFormula t) w :=
  letI := inst₀
  letI := inst₁
  letI := hexp
  LHom.realize_onFormula φ _

/-- On a structure that is an expansion along the vocabulary map, the lifted
interpretation produces the same structure as the original one: the identity
on tagged tuples is an isomorphism. -/
def RelFOInterpretation.liftSourceLEquiv [L'.IsRelational]
    (hexp : @LHom.IsExpansionOn _ _ φ A inst₀ inst₁) :
    @Language.Equiv L'
      (@RelFOInterpretation.MapRel L₁ L' Tag dim (I.liftSource φ) A inst₁)
      (@RelFOInterpretation.MapRel L₀ L' Tag dim I A inst₀)
      (@RelFOInterpretation.mapRelStructure L₁ L' Tag dim (I.liftSource φ) A inst₁ _)
      (@RelFOInterpretation.mapRelStructure L₀ L' Tag dim I A inst₀ _) :=
  letI := inst₀
  letI := inst₁
  letI := hexp
  { toEquiv := Equiv.subtypeEquiv (Equiv.refl _) fun x =>
      I.realize_liftSource_domFormula φ hexp x.1 x.2
    map_fun' := fun f => isEmptyElim f
    map_rel' := fun R x => by
      rw [RelFOInterpretation.relMap_mapRel, RelFOInterpretation.relMap_mapRel]
      exact (LHom.realize_onFormula φ _).symm }

end LiftSource

/-! ### The induction with no relation variables -/

/-- The simultaneous induction with no relation variables at all: its value is
the (unique) assignment of the trivial block, and its output is `⊤`. The
first-order reductions embed into the FO(LFP) ones through it. -/
def StepDef.trivialDef (L : Language.{0, 0}) : StepDef L where
  B := SOBlock.trivial
  step i := nomatch i
  out := ⊤

/-! ### Interpretations reading a fixed point -/

/-- An **FO(LFP) interpretation**: a relativized first-order interpretation
whose formulas may read the value of a simultaneous inflationary induction
over the base structure. The induction `ind` is computed first (its output
sentence is not read); the interpretation `toRel` is then read over the base
vocabulary expanded by the induction's relation variables.

Over an ordered base (`L := L₀.sum Language.order`) this is Immerman's
FO(LFP) reduction, the logical form of a polynomial-time reduction. -/
structure LFPInterpretation (L L' : Language.{0, 0}) (Tag : Type) (dim : ℕ) : Type 1 where
  /-- The induction whose value the formulas may read. -/
  ind : StepDef L
  /-- The interpretation, over the base vocabulary expanded by the block of
  the induction. -/
  toRel : RelFOInterpretation (L.sum ind.B.lang) L' Tag dim

namespace LFPInterpretation

variable {L L' : Language.{0, 0}} {Tag : Type} {dim : ℕ}
variable (I : LFPInterpretation L L' Tag dim) (A : Type) [L.Structure A]

/-- The base structure expanded by the value of the induction – the structure
the interpretation is read over. -/
@[instance_reducible]
def expStructure : (L.sum I.ind.B.lang).Structure A :=
  I.ind.B.structure₁ (L := L) (I.ind.inflLimit A)

/-- The universe of the interpreted structure: the tagged tuples in the
domain, the domain formula being read over the expanded structure. -/
protected def Map : Type :=
  letI := I.expStructure A
  I.toRel.MapRel A

/-- The `L'`-structure interpreted in `A`. -/
instance mapStructure [L'.IsRelational] : L'.Structure (I.Map A) :=
  letI := I.expStructure A
  RelFOInterpretation.mapRelStructure I.toRel A

theorem map_finite [Finite Tag] [Finite A] : Finite (I.Map A) :=
  letI := I.expStructure A
  I.toRel.mapRel_finite A

variable {A}

/-- FO(LFP) interpretations are functorial on isomorphisms: the value of the
induction transports along the isomorphism
(`DescriptiveComplexity.StepDef.inflLimit_map`), and a relativized
interpretation is functorial. -/
def mapLEquiv [L'.IsRelational] {M N : Type} [L.Structure M] [L.Structure N] (e : M ≃[L] N) :
    I.Map M ≃[L'] I.Map N := by
  letI := I.expStructure M
  letI := I.expStructure N
  have e₂ := I.ind.B.extendEquiv' (L' := L) e (I.ind.inflLimit M)
  rw [← I.ind.inflLimit_map e] at e₂
  exact I.toRel.mapRelLEquiv e₂

/-- The pullback of a decision problem along an FO(LFP) interpretation: the
structures the interpretation sends to yes-instances. -/
def pullProblem [L.IsRelational] [L'.IsRelational] (Q : DecisionProblem L') :
    DecisionProblem L where
  Holds A := Q (I.Map A)
  iso_invariant e := Q.iso_invariant (I.mapLEquiv e)

@[simp]
theorem pullProblem_apply [L.IsRelational] [L'.IsRelational] (Q : DecisionProblem L')
    (A : Type) [L.Structure A] : I.pullProblem Q A ↔ Q (I.Map A) :=
  Iff.rfl

end LFPInterpretation

/-! ### With no induction, an FO(LFP) interpretation is a relativized one -/

section NoInduction

variable {L L' : Language.{0, 0}} {Tag : Type} {dim : ℕ} [L'.IsRelational]

/-- A relativized interpretation, read as an FO(LFP) interpretation with the
trivial induction. -/
def RelFOInterpretation.toLFP (J : RelFOInterpretation L L' Tag dim) :
    LFPInterpretation L L' Tag dim :=
  ⟨StepDef.trivialDef L, J.liftSource LHom.sumInl⟩

/-- The FO(LFP) interpretation with the trivial induction produces exactly the
structure of the relativized interpretation it lifts. -/
def RelFOInterpretation.toLFPLEquiv (J : RelFOInterpretation L L' Tag dim) (A : Type)
    [instA : L.Structure A] : J.toLFP.Map A ≃[L'] J.MapRel A :=
  letI := J.toLFP.expStructure A
  J.liftSourceLEquiv LHom.sumInl (inst₀ := instA)
    (inst₁ := J.toLFP.expStructure A) ⟨fun _ _ => rfl, fun _ _ => rfl⟩

end NoInduction

/-! ### FO(LFP) reductions -/

variable {L L' : Language.{0, 0}}

/-- An **FO(LFP) reduction** from `P` to `Q` – a polynomial-time reduction,
in the logical form of [Immerman 1999][immerman1999descriptive]: an FO(LFP)
interpretation over the ordered expansion of the source vocabulary, mapping
yes-instances of `P` exactly to yes-instances of `Q`, for every finite linear
order on the input. As for `DescriptiveComplexity.OrderedFOReduction`, the
problem `P` does not see the order, so the reduction is order-invariant.

The interpretation is relativized, and the domain is required to be
inhabited, as in `DescriptiveComplexity.RelOrderedFOReduction`. -/
structure LFPReduction [L.IsRelational] [L'.IsRelational] (P : DecisionProblem L)
    (Q : DecisionProblem L') : Type 1 where
  /-- The tags used by the underlying interpretation. -/
  Tag : Type
  /-- Tags are finite, so that finite structures map to finite structures. -/
  [tagFinite : Finite Tag]
  /-- The dimension of the underlying interpretation. -/
  dim : ℕ
  /-- The underlying FO(LFP) interpretation, over the ordered expansion. -/
  toInterpretation : LFPInterpretation (L.sum Language.order) L' Tag dim
  /-- The interpreted structure is nonempty on nonempty finite ordered
  inputs. -/
  map_nonempty : ∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A],
    Nonempty (toInterpretation.Map A)
  /-- Yes-instances map exactly to yes-instances, whatever the linear order. -/
  correct : ∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A],
    P A ↔ Q (toInterpretation.Map A)

@[inherit_doc]
scoped notation:50 P:51 " ≤ˡᶠᵖ " Q:51 => LFPReduction P Q

namespace LFPReduction

variable [L.IsRelational] [L'.IsRelational] {P : DecisionProblem L} {Q : DecisionProblem L'}

/-- The same interpretation reduces `Pᶜ` to `Qᶜ`. -/
def compl (f : P ≤ˡᶠᵖ Q) : Pᶜ ≤ˡᶠᵖ Qᶜ :=
  letI := f.tagFinite
  { Tag := f.Tag
    dim := f.dim
    toInterpretation := f.toInterpretation
    map_nonempty := f.map_nonempty
    correct := fun A _ _ _ _ => not_congr (f.correct A) }

/-- An FO(LFP) reduction can be transported along an agreement of the source
problems on finite structures. -/
def congrSource {P' : DecisionProblem L}
    (h : ∀ (A : Type) [L.Structure A] [Finite A], P A ↔ P' A) (f : P ≤ˡᶠᵖ Q) :
    P' ≤ˡᶠᵖ Q :=
  letI := f.tagFinite
  { Tag := f.Tag
    dim := f.dim
    toInterpretation := f.toInterpretation
    map_nonempty := f.map_nonempty
    correct := fun A _ _ _ _ => (h A).symm.trans (f.correct A) }

end LFPReduction

/-! ### Every first-order reduction is an FO(LFP) reduction -/

section Embed

variable [L.IsRelational] [L'.IsRelational] {P : DecisionProblem L} {Q : DecisionProblem L'}

/-- **A relativized ordered FO reduction is an FO(LFP) reduction** with no
induction: the first-order reductions the library's hardness travels along
are in particular polynomial-time reductions. -/
def RelOrderedFOReduction.toLFP (f : P ≤ʳᶠᵒ[≤] Q) : P ≤ˡᶠᵖ Q :=
  letI := f.tagFinite
  { Tag := f.Tag
    dim := f.dim
    toInterpretation := f.toRelInterpretation.toLFP
    map_nonempty := fun A _ _ _ _ =>
      (f.mapRel_nonempty A).map (f.toRelInterpretation.toLFPLEquiv A).symm
    correct := fun A _ _ _ _ =>
      (f.correct A).trans (Q.iso_invariant (f.toRelInterpretation.toLFPLEquiv A)).symm }

/-- **An ordered FO reduction is an FO(LFP) reduction.** -/
def OrderedFOReduction.toLFP (f : P ≤ᶠᵒ[≤] Q) : P ≤ˡᶠᵖ Q :=
  f.toRel.toLFP

/-- **An FO reduction is an FO(LFP) reduction.** -/
noncomputable def FOReduction.toLFP (f : P ≤ᶠᵒ Q) : P ≤ˡᶠᵖ Q :=
  f.toOrdered.toRel.toLFP

end Embed

end DescriptiveComplexity
