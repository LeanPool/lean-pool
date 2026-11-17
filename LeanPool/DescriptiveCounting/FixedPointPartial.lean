/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
module

public import LeanPool.DescriptiveCounting.FixedPointInflationary
import all LeanPool.DescriptiveCounting.FixedPointStep
import all LeanPool.DescriptiveCounting.SecondOrderPull

/-!
# FO(PFP): first-order logic with a partial fixed point

The partial fixed-point logic ([Abiteboul–Vianu 1989][abiteboul1989fixpoint];
[Ebbinghaus–Flum 1995][ebbinghaus1995finite], ch. 7): iterate the step
formulas of a `DescriptiveComplexity.StepDef` by *replacement* – each stage is
one application of the step formulas to the previous one – and read the
output at the first stable stage, if the iteration stabilizes at all.

## The divergence convention

`DescriptiveComplexity.StepDef.PFPHolds` requires convergence: a diverging
iteration makes the definition *false*, whatever the output sentence. The
textbook semantics instead assigns a diverging iteration the empty relations
and reads the output there; the two readings are compared precisely by
`DescriptiveComplexity.StepDef.realize_pfpValue_iff` – they agree unless the
iteration diverges *and* the output holds at the empty assignment. The
convergence-requiring convention is chosen deliberately:

* it is what makes the translation to SO(TC) direct
  (`DescriptiveComplexity.FixedPointPartialSpace`): acceptance of the walk
  *is* «some stable stage satisfying the output is reachable», with no
  divergence detection – on unordered structures, none is available;
* every definition in the textbook semantics whose output fails on the empty
  assignment means the same thing here, and conversely a definition of this
  file is read in the textbook semantics by guarding its output with «the
  state is a fixed point of the step» – the guard is first-order
  (`DescriptiveComplexity.StepDef.isFixedPtF` in
  `DescriptiveComplexity.FixedPointPartialSpace`), and it fails at the empty
  assignment of a diverging iteration, since a diverging iteration's empty
  *start* is not a fixed point.

As for IFP, there is an ordered notion (`DescriptiveComplexity.PFPDefinable`,
the setting of the capture theorem FO(≤, PFP) = PSPACE) and an order-free one
(`DescriptiveComplexity.PFPDefinableFree`, the right-hand side of the
Abiteboul–Vianu theorem), and the two must not be conflated.

## Inflation is a special case

`DescriptiveComplexity.StepDef.inflate` disjoins each variable's own atom
onto its step formula, making the *partial* iteration of the modified
definition the *inflationary* iteration of the original one. Since an
inflationary iteration always converges on finite structures, FO(IFP) is
contained in FO(PFP) (`DescriptiveComplexity.IFPDefinable.pfpDefinable`,
`DescriptiveComplexity.IFPDefinableFree.pfpDefinableFree`) – the easy
inclusion of Abiteboul–Vianu, in both its ordered and order-free forms.

## Closure properties

Same story as for IFP: closed under (ordered) first-order reductions by the
transport lemmas of `DescriptiveComplexity.FixedPointStep`
(`DescriptiveComplexity.PFPDefinable.of_orderedReduction`,
`DescriptiveComplexity.PFPDefinableFree.of_foReduction`). Closure under
complement is *not* by negating the output – divergence makes both a
definition and its output-negation false – but follows on ordered structures
from the capture theorem (`DescriptiveComplexity.FixedPointPartialSpace`)
and `PSPACE = coPSPACE`.
-/

@[expose] public section

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

open Function (IsFixedPt)

variable {L : Language.{0, 0}}

namespace StepDef

/-! ### The value of a partial definition -/

/-- The value of a simultaneous induction read partially: some stage is a
fixed point of the step and satisfies the output sentence. All stable stages
are equal (`DescriptiveComplexity.StepDef.partStage_eq_of_isFixedPt`), so
this says exactly «the iteration converges and its limit satisfies the
output» – see the module docstring for the divergence convention. -/
def PFPHolds (d : StepDef L) (A : Type) [L.Structure A] : Prop :=
  ∃ n, IsFixedPt d.next (d.partStage A n) ∧
    @Sentence.Realize _ A (d.B.structure₁ (L := L) (d.partStage A n)) d.out

/-- The partial iteration converges: some stage is a fixed point of the
step. -/
def PFPConverges (d : StepDef L) (A : Type) [L.Structure A] : Prop :=
  ∃ n, IsFixedPt d.next (d.partStage A n)

/-- A definition whose value is read converges. -/
theorem PFPHolds.converges {d : StepDef L} {A : Type} [L.Structure A]
    (h : d.PFPHolds A) : d.PFPConverges A :=
  ⟨h.choose, h.choose_spec.1⟩

open Classical in
/-- **The first stage that does not move**: convergence is witnessed by a
*least* index. That is what a machine testing «this stage and the next
agree» at each round stops at, and what makes its earlier rounds' tests
fail. -/
theorem exists_least_stable (d : StepDef L) (A : Type) [L.Structure A]
    (h : d.PFPConverges A) :
    ∃ N, d.partStage A N = d.partStage A (N + 1) ∧
      ∀ n, n < N → d.partStage A n ≠ d.partStage A (n + 1) := by
  have hex : ∃ n, d.partStage A n = d.partStage A (n + 1) := by
    obtain ⟨n, hn⟩ := h
    exact ⟨n, by rw [d.partStage_succ, hn]⟩
  exact ⟨Nat.find hex, Nat.find_spec hex, fun n hn => Nat.find_min hex hn⟩

open Classical in
/-- The textbook value of the partial iteration: the stable stage if the
iteration converges, the empty assignment otherwise. Only used to relate the
two divergence conventions (`DescriptiveComplexity.StepDef.realize_pfpValue_iff`);
the semantics of the logic is `DescriptiveComplexity.StepDef.PFPHolds`. -/
noncomputable def pfpValue (d : StepDef L) (A : Type) [L.Structure A] :
    d.B.Assignment A :=
  if h : d.PFPConverges A then d.partStage A h.choose else d.B.botAssign A

/-- **The two divergence conventions, compared**: the textbook reading – the
output at `DescriptiveComplexity.StepDef.pfpValue` – differs from
`DescriptiveComplexity.StepDef.PFPHolds` exactly on a diverging iteration
whose output holds at the empty assignment. -/
theorem realize_pfpValue_iff (d : StepDef L) (A : Type) [L.Structure A] :
    (@Sentence.Realize _ A (d.B.structure₁ (L := L) (d.pfpValue A)) d.out) ↔
      d.PFPHolds A ∨ (¬d.PFPConverges A ∧
        @Sentence.Realize _ A (d.B.structure₁ (L := L) (d.B.botAssign A)) d.out) := by
  by_cases h : d.PFPConverges A
  · rw [pfpValue, dite_eq_left h]
    constructor
    · intro hout
      exact Or.inl ⟨h.choose, h.choose_spec, hout⟩
    · rintro (⟨n, hn, hout⟩ | ⟨hdiv, -⟩)
      · rwa [d.partStage_eq_of_isFixedPt h.choose_spec hn]
      · exact absurd h hdiv
  · rw [pfpValue, dite_eq_right h]
    constructor
    · intro hout
      exact Or.inr ⟨h, hout⟩
    · rintro (⟨n, hn, -⟩ | ⟨-, hout⟩)
      · exact absurd ⟨n, hn⟩ h
      · exact hout

/-- The value of a partial definition is isomorphism-invariant. -/
private theorem pfpHolds_equiv (d : StepDef L) {M N : Type} [L.Structure M] [L.Structure N]
    (e : M ≃[L] N) : d.PFPHolds M ↔ d.PFPHolds N := by
  refine exists_congr fun n => ?_
  rw [d.partStage_map e n]
  refine and_congr (d.isFixedPt_next_map_iff e _).symm ?_
  exact realize_sentence_of_equiv
    (d.B.extendEquiv' (L' := L) e (d.partStage M n)) d.out

end StepDef

/-! ### Definability, ordered and order-free -/

/-- A decision problem is *order-free FO(PFP) definable* if, on nonempty
finite structures, it is the value of a simultaneous induction over its own
vocabulary, read partially. This is the unordered notion on the fixed-point
side of the Abiteboul–Vianu theorem. -/
def PFPDefinableFree [L.IsRelational] (P : DecisionProblem L) : Prop :=
  ∃ d : StepDef L, ∀ (A : Type) [L.Structure A] [Finite A] [Nonempty A],
    P A ↔ d.PFPHolds A

/-- A decision problem is *FO(≤, PFP) definable* if, on nonempty finite
ordered structures, it is the value of a simultaneous induction over the
ordered expansion of its vocabulary, read partially – for every linear order,
the problem itself never seeing it. This is the setting of the capture
theorem FO(≤, PFP) = PSPACE
(`DescriptiveComplexity.FixedPointPartialSpace`). -/
def PFPDefinable [L.IsRelational] (P : DecisionProblem L) : Prop :=
  ∃ d : StepDef (L.sum Language.order),
    ∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A],
      P A ↔ d.PFPHolds A

/-- Order-free FO(PFP) definability only depends on the finite instances of a
problem. -/
private theorem pfpDefinableFree_congr [L.IsRelational] {P Q : DecisionProblem L}
    (h : ∀ (A : Type) [L.Structure A] [Finite A], P A ↔ Q A) :
    PFPDefinableFree P ↔ PFPDefinableFree Q := by
  constructor <;> rintro ⟨d, hd⟩ <;> refine ⟨d, ?_⟩ <;> intro A _ _ _
  · exact (h A).symm.trans (hd A)
  · exact (h A).trans (hd A)

/-- FO(≤, PFP) definability only depends on the finite instances of a
problem.
Registered in the Lax archive as
[`Lax134656.PartialFixedPointClosure.pfpDefinable_congr_finite`](https://laxarchive.org/lax-134656/Lax134656.PartialFixedPointClosure.html#s-Lax134656.PartialFixedPointClosure.pfpDefinable_congr_finite). -/
theorem pfpDefinable_congr [L.IsRelational] {P Q : DecisionProblem L}
    (h : ∀ (A : Type) [L.Structure A] [Finite A], P A ↔ Q A) :
    PFPDefinable P ↔ PFPDefinable Q := by
  constructor <;> rintro ⟨d, hd⟩ <;> refine ⟨d, ?_⟩ <;> intro A _ _ _ _
  · exact (h A).symm.trans (hd A)
  · exact (h A).trans (hd A)

/-! ### Closure under reductions -/

section Closure

variable {L₁ L₂ : Language.{0, 0}} [L₁.IsRelational] [L₂.IsRelational]
variable {P : DecisionProblem L₁} {Q : DecisionProblem L₂}

/-- **Order-free FO(PFP) definability is closed under first-order
reductions**: the partial stages commute with the pullback of the block
(`DescriptiveComplexity.StepDef.partStage_pull`), being a fixed point is
insensitive to the pullback
(`DescriptiveComplexity.StepDef.isFixedPt_next_pull_iff`), and the output
sentence pulls back through the extended interpretation. -/
theorem PFPDefinableFree.of_foReduction (f : P ≤ᶠᵒ Q) (h : PFPDefinableFree Q) :
    PFPDefinableFree P := by
  obtain ⟨d, hd⟩ := h
  let := f.tagFinite
  let := f.tagNonempty
  refine ⟨d.pull f.toInterpretation, ?_⟩
  intro A _ _ _
  have := f.toInterpretation.map_finite A
  have := f.toInterpretation.map_nonempty A
  refine (f.correct A).trans ((hd (f.toInterpretation.Map A)).trans ?_)
  rw [StepDef.PFPHolds, StepDef.PFPHolds]
  refine exists_congr fun n => ?_
  rw [StepDef.partStage_pull f.toInterpretation d A n]
  refine and_congr (StepDef.isFixedPt_next_pull_iff f.toInterpretation d _).symm ?_
  let := (d.B.pull f.Tag f.dim).structure
    (d.B.pullAssign (d.partStage (f.toInterpretation.Map A) n))
  have htrans := realize_sentence_of_equiv
    (f.toInterpretation.extendSOEquiv d.B A (d.partStage (f.toInterpretation.Map A) n))
    d.out
  have hpull := (f.toInterpretation.extendSO d.B).realize_pullSentence d.out A
  exact (hpull.trans htrans).symm

/-- **FO(≤, PFP) definability is closed under ordered first-order
reductions**, by the same route as for IFP
(`DescriptiveComplexity.IFPDefinable.of_orderedReduction`), stage by
stage.
Registered in the Lax archive as
[`Lax134656.PartialFixedPointClosure.pfpDefinable_of_orderedReduction`](https://laxarchive.org/lax-134656/Lax134656.PartialFixedPointClosure.html#s-Lax134656.PartialFixedPointClosure.pfpDefinable_of_orderedReduction). -/
theorem PFPDefinable.of_orderedReduction (f : P ≤ᶠᵒ[≤] Q) (h : PFPDefinable Q) :
    PFPDefinable P := by
  obtain ⟨d, hd⟩ := h
  let := f.tagFinite
  let := f.tagNonempty
  let : LinearOrder f.Tag := finiteLinearOrder f.Tag
  refine ⟨d.pull f.toInterpretation.ordExtend, ?_⟩
  intro A _ _ _ _
  let := f.toInterpretation.mapLinearOrder A
  have := f.toInterpretation.map_finite A
  have := f.toInterpretation.map_nonempty A
  refine (f.correct A).trans ((hd (f.toInterpretation.Map A)).trans ?_)
  rw [StepDef.PFPHolds, StepDef.PFPHolds]
  refine exists_congr fun n => ?_
  rw [d.partStage_map (f.toInterpretation.ordExtendLEquiv A) n,
    StepDef.partStage_pull f.toInterpretation.ordExtend d A n]
  refine and_congr ((d.isFixedPt_next_map_iff (f.toInterpretation.ordExtendLEquiv A)
    _).trans (StepDef.isFixedPt_next_pull_iff f.toInterpretation.ordExtend d _).symm) ?_
  let := (d.B.pull f.Tag f.dim).structure
    (d.B.pullAssign (d.partStage (f.toInterpretation.ordExtend.Map A) n))
  have e₁ := f.toInterpretation.ordExtend.extendSOEquiv d.B A
    (d.partStage (f.toInterpretation.ordExtend.Map A) n)
  have e₂ := d.B.extendEquiv (f.toInterpretation.ordExtendLEquiv A)
    (d.partStage (f.toInterpretation.ordExtend.Map A) n)
  let : ((L₂.sum Language.order).sum d.B.lang).Structure
      ((f.toInterpretation.ordExtend.extendSO d.B).Map A) :=
    FOInterpretation.mapStructure (f.toInterpretation.ordExtend.extendSO d.B) A
  let : ((L₂.sum Language.order).sum d.B.lang).Structure
      (f.toInterpretation.ordExtend.Map A) :=
    @sumStructure (L₂.sum Language.order) d.B.lang (f.toInterpretation.ordExtend.Map A)
      (FOInterpretation.mapStructure f.toInterpretation.ordExtend A)
      (d.B.structure (d.partStage (f.toInterpretation.ordExtend.Map A) n))
  let : ((L₂.sum Language.order).sum d.B.lang).Structure (f.toInterpretation.Map A) :=
    @sumStructure (L₂.sum Language.order) d.B.lang (f.toInterpretation.Map A) _
      (d.B.structure (d.B.mapAssign (f.toInterpretation.ordExtendLEquiv A).toEquiv
        (d.partStage (f.toInterpretation.ordExtend.Map A) n)))
  have hout := StrongHomClass.realize_sentence
    (L := (L₂.sum Language.order).sum d.B.lang) (e₂.comp e₁) d.out
  have hpull := (f.toInterpretation.ordExtend.extendSO d.B).realize_pullSentence d.out A
  exact hout.symm.trans hpull.symm

/-- FO(≤, PFP) definability is closed under plain first-order reductions,
which are in particular ordered ones.
Registered in the Lax archive as
[`Lax134656.PartialFixedPointClosure.pfpDefinable_of_foReduction`](https://laxarchive.org/lax-134656/Lax134656.PartialFixedPointClosure.html#s-Lax134656.PartialFixedPointClosure.pfpDefinable_of_foReduction). -/
theorem PFPDefinable.of_foReduction (f : P ≤ᶠᵒ Q) (h : PFPDefinable Q) :
    PFPDefinable P :=
  h.of_orderedReduction f.toOrdered

end Closure

/-! ### FO(IFP) is contained in FO(PFP) -/

section Inflate

variable {L : Language.{0, 0}}

/-- The inflationary reading of a simultaneous induction, as a partial one:
disjoin each variable's own atom onto its step formula, so that one partial
step of the result is one *inflationary* step of the original. -/
noncomputable def StepDef.inflate (d : StepDef L) : StepDef L where
  B := d.B
  step := fun i =>
    Relations.formula (varInSym L d.B i) (fun j => Term.var j) ⊔ d.step i
  out := d.out

private theorem realize_inflate_step (d : StepDef L) {A : Type} [L.Structure A]
    (ρ : d.B.Assignment A) (i : d.B.ι) (x : Fin (d.B.arity i) → A) :
    (@Formula.Realize _ A (d.B.structure₁ (L := L) ρ) _
      (((varInSym L d.B i).formula fun j => Term.var j) ⊔ d.step i) x) ↔
      ρ i x ∨ d.next ρ i x := by
  let := d.B.structure₁ (L := L) ρ
  rw [Formula.realize_sup, Formula.realize_rel]
  exact Iff.rfl

/-- One partial step of the inflated induction is one inflationary step of
the original. -/
theorem StepDef.next_inflate (d : StepDef L) {A : Type} [L.Structure A]
    (ρ : d.B.Assignment A) : d.inflate.next ρ = d.inflStep ρ := by
  funext i x
  exact propext (realize_inflate_step d ρ i x)

/-- The partial stages of the inflated induction are the inflationary stages
of the original. -/
private theorem StepDef.partStage_inflate (d : StepDef L) (A : Type) [L.Structure A] (n : ℕ) :
    d.inflate.partStage A n = d.inflStage A n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [d.inflate.partStage_succ, d.inflStage_succ, ih, d.next_inflate]

/-- On a finite structure the inflated induction converges to the
inflationary limit, so its partial value is the inflationary value. -/
private theorem StepDef.pfpHolds_inflate (d : StepDef L) (A : Type) [L.Structure A]
    [Finite A] : d.inflate.PFPHolds A ↔ d.IFPHolds A := by
  constructor
  · rintro ⟨n, hn, hout⟩
    rw [d.partStage_inflate A n] at hn hout
    have hfix : IsFixedPt d.inflStep (d.inflStage A n) :=
      (d.next_inflate (d.inflStage A n)).symm.trans hn
    have hlim : d.inflLimit A = d.inflStage A n := by
      funext i x
      refine propext ⟨?_, fun h => ⟨n, h⟩⟩
      rintro ⟨m, hm⟩
      rcases le_total m n with hle | hle
      · exact d.inflStage_le_of_le hle i x hm
      · have hst : d.inflStage A m = d.inflStage A n :=
          iterate_eq_of_isFixedPt hfix hle
        rwa [hst] at hm
    rw [StepDef.IFPHolds, hlim]
    exact hout
  · intro hout
    refine ⟨Nat.card (BAtom d.B A), ?_, ?_⟩
    · rw [d.partStage_inflate A]
      exact (d.next_inflate _).trans (d.isFixedPt_inflStep_card A)
    · rw [d.partStage_inflate A, ← d.inflLimit_eq_stage_card A]
      exact hout

/-- **Order-free FO(IFP) is contained in order-free FO(PFP)**: inflate the
induction. The easy inclusion of the Abiteboul–Vianu theorem.
Registered in the Lax archive as
[`Lax134656.InflationaryInPartial.ifpDefinableFree_pfpDefinableFree`](https://laxarchive.org/lax-134656/Lax134656.InflationaryInPartial.html#s-Lax134656.InflationaryInPartial.ifpDefinableFree_pfpDefinableFree). -/
theorem IFPDefinableFree.pfpDefinableFree [L.IsRelational] {P : DecisionProblem L}
    (h : IFPDefinableFree P) : PFPDefinableFree P := by
  obtain ⟨d, hd⟩ := h
  refine ⟨d.inflate, ?_⟩
  intro A _ _ _
  exact (hd A).trans (d.pfpHolds_inflate A).symm

/-- **FO(≤, IFP) is contained in FO(≤, PFP)**: inflate the induction.
Registered in the Lax archive as
[`Lax134656.InflationaryInPartial.ifpDefinable_pfpDefinable`](https://laxarchive.org/lax-134656/Lax134656.InflationaryInPartial.html#s-Lax134656.InflationaryInPartial.ifpDefinable_pfpDefinable). -/
theorem IFPDefinable.pfpDefinable [L.IsRelational] {P : DecisionProblem L}
    (h : IFPDefinable P) : PFPDefinable P := by
  obtain ⟨d, hd⟩ := h
  refine ⟨d.inflate, ?_⟩
  intro A _ _ _ _
  exact (hd A).trans (d.pfpHolds_inflate A).symm

end Inflate

end DescriptiveComplexity
