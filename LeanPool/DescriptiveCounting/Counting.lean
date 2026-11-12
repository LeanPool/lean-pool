/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
module

public import LeanPool.DescriptiveCounting.OrderedComposition
import all LeanPool.DescriptiveCounting.Composition

/-!
# Counting problems and parsimonious reductions

A decision problem is an isomorphism-invariant *property* of finite structures;
a **counting problem** (`DescriptiveComplexity.CountingProblem`) is an
isomorphism-invariant *number* attached to them – the number of satisfying
assignments of a CNF formula, of proper colorings of a graph, of accepting runs
of a machine. Vocabularies, tagged interpretations and the invariance
discipline carry over unchanged from `DescriptiveComplexity.Interpretation`.

The reductions of this file are the **parsimonious** ones: a first-order
interpretation under which the two counts are *equal*,

* `DescriptiveComplexity.ParsimoniousReduction`, notation `C ≤ᵖ D`, over the bare
  vocabulary, and
* `DescriptiveComplexity.OrderedParsimoniousReduction`, notation `C ≤ᵖ[≤] D`, over
  the ordered expansion, the equation holding whatever the linear order.

They are `DescriptiveComplexity.FOReduction` and
`DescriptiveComplexity.OrderedFOReduction` with the equivalence of the `correct`
field replaced by an equation, and they compose for the same reason: the
composite interpretation is isomorphic to the twice-applied one, and a counting
problem does not distinguish isomorphic structures.

Every counting problem has a decision problem underneath, its **support**
(`DescriptiveComplexity.CountingProblem.support`): “is the count positive?”. A
parsimonious reduction between two counting problems is in particular a
first-order reduction between their supports
(`DescriptiveComplexity.ParsimoniousReduction.toFOReduction`), which is how
hardness results for counting problems yield hardness results for decision
problems.
-/

@[expose] public section

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

variable (L : Language.{0, 0})

/-- A counting problem in the sense of descriptive complexity: an
isomorphism-invariant natural number attached to every `L`-structure. As for
`DescriptiveComplexity.DecisionProblem`, only the values on finite structures are ever
read. -/
structure CountingProblem [L.IsRelational] where
  /-- The count: `C A` (through the function coercion) is the number attached
  to the structure `A`. -/
  Count : ∀ (A : Type) [L.Structure A], ℕ
  /-- Counting problems do not distinguish isomorphic structures. -/
  iso_invariant : ∀ {A B : Type} [L.Structure A] [L.Structure B],
    (A ≃[L] B) → Count A = Count B

namespace CountingProblem

variable {L} [L.IsRelational]

instance : CoeFun (CountingProblem L) fun _ => ∀ (A : Type) [L.Structure A], ℕ :=
  ⟨Count⟩

@[ext]
theorem ext {C D : CountingProblem L} (h : ∀ (A : Type) [L.Structure A], C A = D A) :
    C = D := by
  obtain ⟨c, hc⟩ := C
  obtain ⟨d, hd⟩ := D
  have : c = d := funext fun A => funext fun inst => h A
  subst this
  rfl

/-- The decision problem underneath a counting problem: is the count
positive? -/
def support (C : CountingProblem L) : DecisionProblem L where
  Holds := fun A inst => 0 < @Count L _ C A inst
  iso_invariant := fun e => by rw [C.iso_invariant e]

theorem support_iff (C : CountingProblem L) (A : Type) [L.Structure A] :
    C.support A ↔ 0 < C A :=
  Iff.rfl

end CountingProblem

variable {L} {L' : Language.{0, 0}}

/-! ### Reading an interpretation over a larger source vocabulary -/

section LiftSource

variable {L₀ L₁ : Language.{0, 0}} {Tag : Type} {dim : ℕ}

/-- An interpretation read over a larger source vocabulary: every defining
formula is transported along the vocabulary map. -/
def FOInterpretation.liftSource (Φ : L₀ →ᴸ L₁) (I : FOInterpretation L₀ L' Tag dim) :
    FOInterpretation L₁ L' Tag dim where
  relFormula R t := Φ.onFormula (I.relFormula R t)

/-- On a structure that is an expansion along the vocabulary map, the lifted
interpretation produces the same structure as the original one: the identity
on tagged tuples is an isomorphism. -/
def FOInterpretation.liftSourceLEquiv [L'.IsRelational] (Φ : L₀ →ᴸ L₁)
    (I : FOInterpretation L₀ L' Tag dim) (A : Type) [L₀.Structure A] [L₁.Structure A]
    [Φ.IsExpansionOn A] : (I.liftSource Φ).Map A ≃[L'] I.Map A where
  toEquiv := Equiv.refl _
  map_fun' := fun f => isEmptyElim f
  map_rel' := fun {n} R x => by
    rw [FOInterpretation.relMap_map, FOInterpretation.relMap_map]
    exact (LHom.realize_onFormula _ _).symm

end LiftSource

/-! ### Parsimonious reductions -/

/-- A *parsimonious* first-order reduction from the counting problem `C` to the
counting problem `D`: a first-order interpretation under which the two counts
agree. -/
structure ParsimoniousReduction [L.IsRelational] [L'.IsRelational] (C : CountingProblem L)
    (D : CountingProblem L') where
  /-- The tags (copies of `A^dim`) used by the underlying interpretation. -/
  Tag : Type
  /-- Tags are finite, so that finite structures map to finite structures. -/
  [tagFinite : Finite Tag]
  /-- Tags are nonempty, so that nonempty structures map to nonempty
  structures. -/
  [tagNonempty : Nonempty Tag]
  /-- The dimension of the underlying interpretation. -/
  dim : ℕ
  /-- The underlying first-order interpretation. -/
  toInterpretation : FOInterpretation L L' Tag dim
  /-- The counts agree, on the finite nonempty structures. -/
  correct : ∀ (A : Type) [L.Structure A] [Finite A] [Nonempty A],
    C A = D (toInterpretation.Map A)

@[inherit_doc]
scoped notation:50 C:51 " ≤ᵖ " D:51 => ParsimoniousReduction C D

/-- An *ordered* parsimonious reduction: a first-order interpretation over the
ordered expansion of the source vocabulary under which the two counts agree,
for every linear order of the (finite) input structure. -/
structure OrderedParsimoniousReduction [L.IsRelational] [L'.IsRelational]
    (C : CountingProblem L) (D : CountingProblem L') where
  /-- The tags (copies of `A^dim`) used by the underlying interpretation. -/
  Tag : Type
  /-- Tags are finite, so that finite structures map to finite structures. -/
  [tagFinite : Finite Tag]
  /-- Tags are nonempty, so that nonempty structures map to nonempty
  structures. -/
  [tagNonempty : Nonempty Tag]
  /-- The dimension of the underlying interpretation. -/
  dim : ℕ
  /-- The underlying first-order interpretation, over the ordered expansion. -/
  toInterpretation : FOInterpretation (L.sum Language.order) L' Tag dim
  /-- The counts agree, whatever the linear order. -/
  correct : ∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A],
    C A = D (toInterpretation.Map A)

@[inherit_doc]
scoped notation:50 C:51 " ≤ᵖ[≤] " D:51 => OrderedParsimoniousReduction C D

section Support

variable [L.IsRelational] [L'.IsRelational] {C : CountingProblem L} {D : CountingProblem L'}

/-- A parsimonious reduction is a first-order reduction between the supports:
equal counts are positive together. -/
def ParsimoniousReduction.toFOReduction (f : C ≤ᵖ D) : C.support ≤ᶠᵒ D.support :=
  letI := f.tagFinite
  letI := f.tagNonempty
  { Tag := f.Tag
    dim := f.dim
    toInterpretation := f.toInterpretation
    correct := fun A _ _ _ => by
      rw [CountingProblem.support_iff, CountingProblem.support_iff, f.correct A] }

/-- An ordered parsimonious reduction is an ordered first-order reduction
between the supports. -/
def OrderedParsimoniousReduction.toOrderedFOReduction (f : C ≤ᵖ[≤] D) :
    C.support ≤ᶠᵒ[≤] D.support :=
  letI := f.tagFinite
  letI := f.tagNonempty
  { Tag := f.Tag
    dim := f.dim
    toInterpretation := f.toInterpretation
    correct := fun A _ _ _ _ => by
      rw [CountingProblem.support_iff, CountingProblem.support_iff, f.correct A] }

end Support

/-! ### Reflexivity and transitivity -/

section Trans

variable {L₁ L₂ L₃ : Language.{0, 0}} [L₁.IsRelational] [L₂.IsRelational] [L₃.IsRelational]
variable {C : CountingProblem L₁} {D : CountingProblem L₂} {E : CountingProblem L₃}

/-- Every counting problem parsimoniously reduces to itself, via the identity
interpretation. -/
def ParsimoniousReduction.refl (C : CountingProblem L₁) : C ≤ᵖ C where
  Tag := Unit
  dim := 1
  toInterpretation := FOInterpretation.refl L₁
  correct A _ _ _ := (C.iso_invariant (FOInterpretation.reflLEquiv L₁ A)).symm

/-- **Transitivity of parsimonious reductions.** The composite interpretation
is only isomorphic to the twice-applied one, so the isomorphism-invariance
built into `DescriptiveComplexity.CountingProblem` concludes. -/
noncomputable def ParsimoniousReduction.trans (g : C ≤ᵖ D) (f : D ≤ᵖ E) : C ≤ᵖ E :=
  letI := f.tagFinite
  letI := g.tagFinite
  letI := f.tagNonempty
  letI := g.tagNonempty
  { Tag := f.Tag × (Fin f.dim → g.Tag)
    dim := f.dim * g.dim
    toInterpretation := f.toInterpretation.comp g.toInterpretation
    correct := fun A _ _ _ =>
      haveI := g.toInterpretation.map_nonempty (A := A)
      haveI := g.toInterpretation.map_finite A
      ((g.correct A).trans (f.correct (g.toInterpretation.Map A))).trans
        (E.iso_invariant (f.toInterpretation.compLEquiv g.toInterpretation A)).symm }

/-- **Transitivity of ordered parsimonious reductions.** The intermediate
structure is ordered by the lexicographic order on tagged tuples, which is
first-order definable from the order of the input. -/
noncomputable def OrderedParsimoniousReduction.trans (g : C ≤ᵖ[≤] D) (f : D ≤ᵖ[≤] E) :
    C ≤ᵖ[≤] E :=
  letI := g.tagFinite
  letI := f.tagFinite
  letI := g.tagNonempty
  letI := f.tagNonempty
  letI : LinearOrder g.Tag := finiteLinearOrder g.Tag
  { Tag := f.Tag × (Fin f.dim → g.Tag)
    dim := f.dim * g.dim
    toInterpretation := f.toInterpretation.comp g.toInterpretation.ordExtend
    correct := fun A _ _ _ _ => by
      let := g.toInterpretation.mapLinearOrder A
      have : Finite (g.toInterpretation.Map A) := g.toInterpretation.map_finite A
      have : Nonempty (g.toInterpretation.Map A) := g.toInterpretation.map_nonempty A
      have h1 := g.correct A
      have h2 := f.correct (g.toInterpretation.Map A)
      have e1 := g.toInterpretation.ordExtendLEquiv A
      have e2 := f.toInterpretation.mapLEquiv e1
      have e3 := f.toInterpretation.compLEquiv g.toInterpretation.ordExtend A
      exact (h1.trans h2).trans (E.iso_invariant (e2.comp e3)).symm }

/-- A parsimonious reduction is in particular an ordered one: lift its defining
formulas to the ordered expansion, where they ignore the order. -/
noncomputable def ParsimoniousReduction.toOrdered (g : C ≤ᵖ D) : C ≤ᵖ[≤] D :=
  letI := g.tagFinite
  letI := g.tagNonempty
  { Tag := g.Tag
    dim := g.dim
    toInterpretation :=
      { relFormula := fun R t => LHom.sumInl.onFormula (g.toInterpretation.relFormula R t) }
    correct := fun A _ _ _ _ => by
      refine (g.correct A).trans (D.iso_invariant ?_)
      exact
        { toEquiv := Equiv.refl _
          map_fun' := fun f => isEmptyElim f
          map_rel' := fun {n} R x => by
            rw [FOInterpretation.relMap_map, FOInterpretation.relMap_map]
            exact LHom.realize_onFormula _ _ } }

/-- Mixed transitivity: an ordered parsimonious reduction followed by a plain
one. -/
noncomputable def OrderedParsimoniousReduction.transParsimonious (g : C ≤ᵖ[≤] D) (f : D ≤ᵖ E) :
    C ≤ᵖ[≤] E :=
  g.trans f.toOrdered

/-- Mixed transitivity: a plain parsimonious reduction followed by an ordered
one. -/
noncomputable def ParsimoniousReduction.transOrdered (g : C ≤ᵖ D) (f : D ≤ᵖ[≤] E) :
    C ≤ᵖ[≤] E :=
  g.toOrdered.trans f

/-- `Trans` instance for parsimonious reductions, enabling `calc` chains. -/
noncomputable instance :
    Trans (α := CountingProblem L₁) (β := CountingProblem L₂) (γ := CountingProblem L₃)
      ParsimoniousReduction ParsimoniousReduction ParsimoniousReduction where
  trans g f := g.trans f

/-- `Trans` instance for ordered parsimonious reductions. -/
noncomputable instance :
    Trans (α := CountingProblem L₁) (β := CountingProblem L₂) (γ := CountingProblem L₃)
      OrderedParsimoniousReduction OrderedParsimoniousReduction
      OrderedParsimoniousReduction where
  trans g f := g.trans f

@[inherit_doc OrderedParsimoniousReduction.transParsimonious]
noncomputable instance :
    Trans (α := CountingProblem L₁) (β := CountingProblem L₂) (γ := CountingProblem L₃)
      OrderedParsimoniousReduction ParsimoniousReduction OrderedParsimoniousReduction where
  trans g f := g.transParsimonious f

@[inherit_doc ParsimoniousReduction.transOrdered]
noncomputable instance :
    Trans (α := CountingProblem L₁) (β := CountingProblem L₂) (γ := CountingProblem L₃)
      ParsimoniousReduction OrderedParsimoniousReduction OrderedParsimoniousReduction where
  trans g f := g.transOrdered f

/-- Replacing the source of an ordered parsimonious reduction by a counting
problem with the same values on finite structures. -/
def OrderedParsimoniousReduction.congrSource {C' : CountingProblem L₁}
    (h : ∀ (A : Type) [L₁.Structure A] [Finite A], C A = C' A) (g : C ≤ᵖ[≤] D) :
    C' ≤ᵖ[≤] D :=
  letI := g.tagFinite
  letI := g.tagNonempty
  { Tag := g.Tag
    dim := g.dim
    toInterpretation := g.toInterpretation
    correct := fun A _ _ _ _ => (h A).symm.trans (g.correct A) }

end Trans

end DescriptiveComplexity
