/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
module

public import LeanPool.DescriptiveCounting.Counting
public import LeanPool.DescriptiveCounting.RelComposition
import all LeanPool.DescriptiveCounting.Counting

/-!
# Relativized parsimonious reductions

The counting counterpart of `DescriptiveComplexity.RelOrderedFOReduction`: an ordered
parsimonious reduction through a *relativized* interpretation, whose target
universe is the definable subset a domain formula carves out of `Tag × A^dim`
(`DescriptiveComplexity.RelOrderedParsimoniousReduction`, notation `C ≤ʳᵖ[≤] D`).

It is needed for the same reason as on the decision side. A counting problem
whose solutions *span* the universe – the Hamilton circuits of a graph – cannot
be the target of an ordinary interpretation: the tagged tuples that stand for
nothing would each have to lie on every circuit. With a definable domain they
are simply not there.

* `DescriptiveComplexity.OrderedParsimoniousReduction.toRel`: an ordinary ordered
  parsimonious reduction is a relativized one, with domain `⊤`;
* `DescriptiveComplexity.RelOrderedParsimoniousReduction.trans`: transitivity, by the
  guarded composition of `DescriptiveComplexity.RelComposition`;
* `DescriptiveComplexity.RelOrderedParsimoniousReduction.toRelOrderedFOReduction`: it
  is a relativized reduction between the supports.

Parsimonious hardness for the counting classes of
`DescriptiveComplexity.Counting.Class` is hardness under these reductions, as hardness
for the decision classes is hardness under `≤ʳᶠᵒ[≤]`.
-/

@[expose] public section

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L L' : Language.{0, 0}}

/-- An ordered parsimonious reduction through a **relativized**
interpretation: the two counts agree, the target structure being carried by
the definable subset of `Tag × A^dim` that the domain formula carves out. -/
structure RelOrderedParsimoniousReduction [L.IsRelational] [L'.IsRelational]
    (C : CountingProblem L) (D : CountingProblem L') where
  /-- The tags used by the underlying interpretation. -/
  Tag : Type
  /-- Tags are finite, so that finite structures map to finite structures. -/
  [tagFinite : Finite Tag]
  /-- The dimension of the underlying interpretation. -/
  dim : ℕ
  /-- The underlying relativized interpretation, over the ordered expansion. -/
  toRelInterpretation : RelFOInterpretation (L.sum Language.order) L' Tag dim
  /-- The definable domain is inhabited. -/
  dom_nonempty : ∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A],
    ∃ (t : Tag) (w : Fin dim → A), (toRelInterpretation.domFormula t).Realize w
  /-- The counts agree, whatever the linear order. -/
  correct : ∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A],
    C A = D (toRelInterpretation.MapRel A)

@[inherit_doc]
scoped notation:50 C:51 " ≤ʳᵖ[≤] " D:51 => RelOrderedParsimoniousReduction C D

section Basic

variable [L.IsRelational] [L'.IsRelational] {C : CountingProblem L} {D : CountingProblem L'}

/-- The relativized universe of the output of a reduction is nonempty on
nonempty finite ordered inputs. -/
theorem RelOrderedParsimoniousReduction.mapRel_nonempty (f : C ≤ʳᵖ[≤] D) (A : Type)
    [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A] :
    Nonempty (f.toRelInterpretation.MapRel A) :=
  let ⟨t, w, h⟩ := f.dom_nonempty A
  ⟨⟨(t, w), h⟩⟩

/-- An ordinary ordered parsimonious reduction is a relativized one with `⊤`
domain. -/
def OrderedParsimoniousReduction.toRel (f : C ≤ᵖ[≤] D) : C ≤ʳᵖ[≤] D :=
  letI := f.tagFinite
  letI := f.tagNonempty
  { Tag := f.Tag
    dim := f.dim
    toRelInterpretation := f.toInterpretation.toRel
    dom_nonempty := fun A => ⟨Classical.arbitrary f.Tag, fun _ => Classical.arbitrary A,
      Formula.realize_top.mpr trivial⟩
    correct := fun A => (f.correct A).trans (D.iso_invariant (f.toInterpretation.toRelLEquiv A)) }

/-- A relativized parsimonious reduction is a relativized first-order reduction
between the supports: equal counts are positive together. -/
def RelOrderedParsimoniousReduction.toRelOrderedFOReduction (f : C ≤ʳᵖ[≤] D) :
    C.support ≤ʳᶠᵒ[≤] D.support :=
  letI := f.tagFinite
  { Tag := f.Tag
    dim := f.dim
    toRelInterpretation := f.toRelInterpretation
    dom_nonempty := f.dom_nonempty
    correct := fun A _ _ _ _ => by
      rw [CountingProblem.support_iff, CountingProblem.support_iff, f.correct A] }

/-- Replacing the source of a relativized parsimonious reduction by a counting
problem with the same values on finite structures. -/
def RelOrderedParsimoniousReduction.congrSource {C' : CountingProblem L}
    (h : ∀ (A : Type) [L.Structure A] [Finite A], C A = C' A) (g : C ≤ʳᵖ[≤] D) :
    C' ≤ʳᵖ[≤] D :=
  letI := g.tagFinite
  { Tag := g.Tag
    dim := g.dim
    toRelInterpretation := g.toRelInterpretation
    dom_nonempty := g.dom_nonempty
    correct := fun A => (h A).symm.trans (g.correct A) }

/-- Replacing the target of a relativized parsimonious reduction by a counting
problem with the same values on finite structures. -/
def RelOrderedParsimoniousReduction.congrTarget {D' : CountingProblem L'}
    (h : ∀ (A : Type) [L'.Structure A] [Finite A], D A = D' A) (g : C ≤ʳᵖ[≤] D) :
    C ≤ʳᵖ[≤] D' :=
  letI := g.tagFinite
  { Tag := g.Tag
    dim := g.dim
    toRelInterpretation := g.toRelInterpretation
    dom_nonempty := g.dom_nonempty
    correct := fun A _ _ _ _ =>
      haveI := g.toRelInterpretation.mapRel_finite A
      (g.correct A).trans (h (g.toRelInterpretation.MapRel A)) }

end Basic

section Trans

variable {L₁ L₂ L₃ : Language.{0, 0}} [L₁.IsRelational] [L₂.IsRelational] [L₃.IsRelational]
variable {C : CountingProblem L₁} {D : CountingProblem L₂} {E : CountingProblem L₃}

/-- **Transitivity of relativized parsimonious reductions.** The intermediate
definable structure is ordered by the lexicographic order on tagged tuples,
restricted to the domain. -/
noncomputable def RelOrderedParsimoniousReduction.trans (g : C ≤ʳᵖ[≤] D) (f : D ≤ʳᵖ[≤] E) :
    C ≤ʳᵖ[≤] E :=
  letI := g.tagFinite
  letI := f.tagFinite
  letI : LinearOrder g.Tag := finiteLinearOrder g.Tag
  { Tag := f.Tag × (Fin f.dim → g.Tag)
    dim := f.dim * g.dim
    toRelInterpretation := f.toRelInterpretation.compRel g.toRelInterpretation.ordExtendRel
    dom_nonempty := fun A _ _ _ _ => by
      let := g.toRelInterpretation.mapRelLinearOrder A
      have : Finite (g.toRelInterpretation.MapRel A) := g.toRelInterpretation.mapRel_finite A
      have : Nonempty (g.toRelInterpretation.MapRel A) := g.mapRel_nonempty A
      have e1 := g.toRelInterpretation.ordExtendRelLEquiv A
      have e2 := f.toRelInterpretation.mapRelLEquiv e1
      have e3 := f.toRelInterpretation.compLEquivRel g.toRelInterpretation.ordExtendRel (A := A)
      obtain ⟨y⟩ := f.mapRel_nonempty (g.toRelInterpretation.MapRel A)
      obtain ⟨⟨t, w⟩, hw⟩ := (e2.comp e3).symm y
      exact ⟨t, w, hw⟩
    correct := fun A _ _ _ _ => by
      let := g.toRelInterpretation.mapRelLinearOrder A
      have : Finite (g.toRelInterpretation.MapRel A) := g.toRelInterpretation.mapRel_finite A
      have : Nonempty (g.toRelInterpretation.MapRel A) := g.mapRel_nonempty A
      have h1 := g.correct A
      have h2 := f.correct (g.toRelInterpretation.MapRel A)
      have e1 := g.toRelInterpretation.ordExtendRelLEquiv A
      have e2 := f.toRelInterpretation.mapRelLEquiv e1
      have e3 := f.toRelInterpretation.compLEquivRel g.toRelInterpretation.ordExtendRel (A := A)
      exact (h1.trans h2).trans (E.iso_invariant (e2.comp e3)).symm }

end Trans

end DescriptiveComplexity
