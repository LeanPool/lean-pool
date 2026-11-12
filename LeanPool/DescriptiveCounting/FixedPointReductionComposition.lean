/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
module

public import LeanPool.DescriptiveCounting.FixedPointReduction
public import LeanPool.DescriptiveCounting.FixedPointStratify
public import LeanPool.DescriptiveCounting.FixedPointStepRel
import all LeanPool.DescriptiveCounting.FixedPointReduction
import all LeanPool.DescriptiveCounting.FixedPointStepRel
import all LeanPool.DescriptiveCounting.FixedPointStratify

/-!
# Composition of FO(LFP) reductions

Transitivity of `P ≤ˡᶠᵖ Q` (`DescriptiveComplexity.LFPReduction.trans`), the
FO(LFP) analogue of `DescriptiveComplexity.RelOrderedFOReduction.trans`. It is
what makes `≤ˡᶠᵖ` a reduction *order*, and what the hardness notion of
`DescriptiveComplexity.FixedPointReductionClosure` consumes.

## Why this is a theorem and not bookkeeping

Composing two first-order interpretations pulls the outer formulas back through
the inner one. Here the outer formulas may also read *the outer induction*, run
over the interpreted structure, so composition has to say that a fixed point
computed on the interpreted structure is computed by an induction on the base –
after the inner induction, whose value the inner interpretation reads. Nothing
about that is formal: it is the substitution property of the logic, and the
statement classically known as “FO(LFP) reductions compose”.

Three constructions already in the library supply the three halves:

* the outer induction pulls back through the inner (relativized)
  interpretation, `DescriptiveComplexity.StepDef.pullRel`, giving an induction
  over the base *expanded by the inner induction's block*;
* two inductions run one after the other are one induction,
  `DescriptiveComplexity.StepDef.stratify` – whose gate fires exactly when the
  first has converged, so the composite's limit has the inner limit and the
  pulled outer limit as its two parts
  (`DescriptiveComplexity.StepDef.strat1Assign_inflLimit`,
  `DescriptiveComplexity.StepDef.strat2Assign_inflLimit`);
* the interpretations compose, with the guarded pullback that a definable
  domain requires, `DescriptiveComplexity.RelFOInterpretation.compRel`.

`DescriptiveComplexity.LFPInterpretation.compLEquiv` assembles them: the
composite interpretation produces the twice-interpreted structure.

## The order of the intermediate structure

As for `DescriptiveComplexity.OrderedFOReduction.trans`, the outer reduction's
formulas mention the order of the intermediate structure, which the inner
interpretation does not produce. The fix is the same – the lexicographic order
on tagged tuples – with one twist: the inner interpretation's *source* is the
base expanded by its own induction's block, so the lexicographic formula has to
be read there. `DescriptiveComplexity.RelFOInterpretation.ordExtendSrc` is the
order extension along an arbitrary vocabulary map of the source, of which
`DescriptiveComplexity.RelFOInterpretation.ordExtendRel` is the identity case.
-/

@[expose] public section

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### The order extension, over a larger source vocabulary -/

section OrdExtendSrc

variable {L₁ Lsrc L₂ : Language.{0, 0}} [L₂.IsRelational]
variable {T : Type} [LinearOrder T] {d : ℕ}

/-- Extension of a relativized interpretation with the lexicographic order on
tagged tuples, the comparison formula being read through a vocabulary map of
the *source*: this is `DescriptiveComplexity.RelFOInterpretation.ordExtendRel`
where the source is not the ordered expansion itself but an expansion of it,
as happens when the interpretation reads an induction over the ordered base. -/
noncomputable def RelFOInterpretation.ordExtendSrc (φ : (L₁.sum Language.order) →ᴸ Lsrc)
    (I : RelFOInterpretation Lsrc L₂ T d) :
    RelFOInterpretation Lsrc (L₂.sum Language.order) T d where
  relFormula {n} R :=
    match n, R with
    | _, Sum.inl r => I.relFormula r
    | _, Sum.inr .le => fun t => φ.onFormula (lexLeF L₁ d (t 0) (t 1))
  domFormula := I.domFormula

variable (φ : (L₁.sum Language.order) →ᴸ Lsrc) (I : RelFOInterpretation Lsrc L₂ T d)
variable {A : Type} [L₁.Structure A] [LinearOrder A] (instS : Lsrc.Structure A)

/-- The lexicographic linear order on the interpreted universe of an
interpretation with an arbitrary source vocabulary: as
`DescriptiveComplexity.RelFOInterpretation.mapRelLinearOrder`, of which this is
the generalization the composition needs. -/
@[instance_reducible]
noncomputable def RelFOInterpretation.mapRelLinearOrderSrc :
    LinearOrder (@RelFOInterpretation.MapRel Lsrc L₂ T d I A instS) :=
  letI := instS
  letI := tagTupleOrder (Tag := T) (d := d) (A := A)
  LinearOrder.lift' (Subtype.val : I.MapRel A → T × (Fin d → A)) Subtype.val_injective

/-- The order-extended interpretation produces exactly the interpreted
structure equipped with the lexicographic order, restricted to the domain. -/
noncomputable def RelFOInterpretation.ordExtendSrcLEquiv
    (hexp : @LHom.IsExpansionOn _ _ φ A (sumOrderStructure L₁ A) instS) :
    @Language.Equiv (L₂.sum Language.order)
      (@RelFOInterpretation.MapRel Lsrc _ T d (I.ordExtendSrc φ) A instS)
      (@RelFOInterpretation.MapRel Lsrc _ T d I A instS)
      (@RelFOInterpretation.mapRelStructure Lsrc _ T d (I.ordExtendSrc φ) A instS _)
      (letI := instS
       letI := I.mapRelLinearOrderSrc instS
       sumOrderStructure L₂ (I.MapRel A)) :=
  letI := instS
  letI := I.mapRelLinearOrderSrc instS
  letI := hexp
  { toEquiv := Equiv.refl _
    map_fun' := fun f => isEmptyElim f
    map_rel' := fun {n} R x => by
      cases R with
      | inl r => exact Iff.rfl
      | inr r =>
        cases r with
        | le =>
          exact (((LHom.realize_onFormula φ _).trans
            (realize_lexLeF (L := L₁) (A := A) (Tag := T) (d := d)
              (t₁ := (x 0).1.1) (t₂ := (x 1).1.1)
              (v := fun p => (x p.1).1.2 p.2))).trans
            (tagTupleLe_iff_le (x 0).1 (x 1).1)).symm }

end OrdExtendSrc

/-! ### Composition of FO(LFP) interpretations -/

section Comp

variable {L₁ L₂ L₃ : Language.{0, 0}} [L₂.IsRelational] [L₃.IsRelational]
variable {Tag₁ Tag₂ : Type} [Finite Tag₁] {d₁ d₂ : ℕ}

/-- **The composite of two FO(LFP) interpretations**: the two inductions are
stratified – the inner one first, then the outer one pulled back through the
inner interpretation – and the two interpretations compose with the guarded
pullback, read over the stratified block. -/
noncomputable def LFPInterpretation.comp (J : LFPInterpretation L₂ L₃ Tag₂ d₂)
    (I : LFPInterpretation L₁ L₂ Tag₁ d₁) :
    LFPInterpretation L₁ L₃ (Tag₂ × (Fin d₂ → Tag₁)) (d₂ * d₁) where
  ind := I.ind.stratify (J.ind.pullRel I.toRel)
  toRel :=
    (J.toRel.compRel (I.toRel.extendSORel J.ind.B)).liftSource
      (strat2LHom L₁ I.ind.B (J.ind.pullRel I.toRel).B)

variable (J : LFPInterpretation L₂ L₃ Tag₂ d₂) (I : LFPInterpretation L₁ L₂ Tag₁ d₁)
variable (A : Type) [L₁.Structure A] [Finite A]

/-- **The composite interpretation produces the twice-interpreted structure.**
This is the substitution property of FO(LFP): what the composite computes in
one induction and one layer of formulas is what the two interpretations
compute in sequence. -/
noncomputable def LFPInterpretation.compLEquiv :
    (J.comp I).Map A ≃[L₃] J.Map (I.Map A) := by
  letI := I.expStructure A
  -- the composite limit splits into the inner limit and the pulled outer limit
  have h1 : strat1Assign ((J.comp I).ind.inflLimit A) = I.ind.inflLimit A :=
    I.ind.strat1Assign_inflLimit (J.ind.pullRel I.toRel)
  have h2 : strat2Assign ((J.comp I).ind.inflLimit A) =
      J.ind.B.pullAssignRel I.toRel (J.ind.inflLimit (I.Map A)) := by
    refine Eq.trans (I.ind.strat2Assign_inflLimit (J.ind.pullRel I.toRel)) ?_
    exact StepDef.inflLimit_pullRel J.ind I.toRel
  -- the composite structure, read through the stratified block
  have hexp := strat2LHom_isExpansionOn (L := L₁) ((J.comp I).ind.inflLimit A)
  rw [h1, h2] at hexp
  letI : ((L₁.sum I.ind.B.lang).sum (J.ind.B.pull Tag₁ d₁).lang).Structure A :=
    @SOBlock.structure₁ (L₁.sum I.ind.B.lang) (J.ind.B.pull Tag₁ d₁) A (I.expStructure A)
      (J.ind.B.pullAssignRel I.toRel (J.ind.inflLimit (I.Map A)))
  letI : (L₂.sum J.ind.B.lang).Structure (I.toRel.MapRel A) := J.expStructure (I.Map A)
  exact ((J.toRel.mapRelLEquiv (I.toRel.extendSORelEquiv J.ind.B A
        (J.ind.inflLimit (I.Map A)))).comp
      ((J.toRel.compLEquivRel (I.toRel.extendSORel J.ind.B)).comp
        ((J.toRel.compRel (I.toRel.extendSORel J.ind.B)).liftSourceLEquiv
          (strat2LHom L₁ I.ind.B (J.ind.pullRel I.toRel).B) hexp)))

end Comp

/-! ### The order of the interpreted structure -/

section OrdExtend

variable {L₁ L₂ : Language.{0, 0}} [L₂.IsRelational] {T : Type} [LinearOrder T] {d : ℕ}
variable (I : LFPInterpretation (L₁.sum Language.order) L₂ T d)

/-- Extension of an FO(LFP) interpretation over an ordered base to one whose
target carries the order vocabulary, interpreted by the lexicographic order on
tagged tuples. The induction is unchanged; the comparison formula is read over
the base expanded by its block. -/
noncomputable def LFPInterpretation.ordExtend :
    LFPInterpretation (L₁.sum Language.order) (L₂.sum Language.order) T d where
  ind := I.ind
  toRel := I.toRel.ordExtendSrc LHom.sumInl

variable (A : Type) [L₁.Structure A] [LinearOrder A]

/-- The lexicographic linear order on the universe interpreted by an FO(LFP)
interpretation. -/
@[instance_reducible]
noncomputable def LFPInterpretation.mapLinearOrder : LinearOrder (I.Map A) :=
  I.toRel.mapRelLinearOrderSrc (I.expStructure A)

/-- The order-extended interpretation produces exactly the interpreted
structure equipped with the lexicographic order. -/
noncomputable def LFPInterpretation.ordExtendLEquiv :
    @Language.Equiv (L₂.sum Language.order) (I.ordExtend.Map A) (I.Map A)
      (LFPInterpretation.mapStructure I.ordExtend A)
      (letI := I.mapLinearOrder A; sumOrderStructure L₂ (I.Map A)) :=
  letI := I.expStructure A
  I.toRel.ordExtendSrcLEquiv LHom.sumInl (I.expStructure A) ⟨fun _ _ => rfl, fun _ _ => rfl⟩

end OrdExtend

/-! ### Transitivity -/

section Trans

variable {L₁ L₂ L₃ : Language.{0, 0}} [L₁.IsRelational] [L₂.IsRelational] [L₃.IsRelational]
variable {P : DecisionProblem L₁} {Q : DecisionProblem L₂} {R : DecisionProblem L₃}

/-- **Transitivity of FO(LFP) reductions**: if `P ≤ˡᶠᵖ Q` and `Q ≤ˡᶠᵖ R`, then
`P ≤ˡᶠᵖ R`. The two inductions are stratified into one, the interpretations
compose, and the intermediate structure is ordered lexicographically – the same
three ingredients as `DescriptiveComplexity.RelOrderedFOReduction.trans`, plus
the stratification that is this notion's own. -/
noncomputable def LFPReduction.trans (g : P ≤ˡᶠᵖ Q) (f : Q ≤ˡᶠᵖ R) : P ≤ˡᶠᵖ R :=
  letI := g.tagFinite
  letI := f.tagFinite
  letI : LinearOrder g.Tag := finiteLinearOrder g.Tag
  { Tag := f.Tag × (Fin f.dim → g.Tag)
    dim := f.dim * g.dim
    toInterpretation := f.toInterpretation.comp g.toInterpretation.ordExtend
    map_nonempty := fun A _ _ _ _ => by
      let := g.toInterpretation.mapLinearOrder A
      have : Finite (g.toInterpretation.Map A) := g.toInterpretation.map_finite A
      have := g.map_nonempty A
      have e₁ := g.toInterpretation.ordExtendLEquiv A
      have e₂ := f.toInterpretation.mapLEquiv e₁
      have e₃ := f.toInterpretation.compLEquiv g.toInterpretation.ordExtend A
      exact (f.map_nonempty (g.toInterpretation.Map A)).map (e₂.comp e₃).symm
    correct := fun A _ _ _ _ => by
      let := g.toInterpretation.mapLinearOrder A
      have : Finite (g.toInterpretation.Map A) := g.toInterpretation.map_finite A
      have := g.map_nonempty A
      have h1 := g.correct A
      have h2 := f.correct (g.toInterpretation.Map A)
      have e₁ := g.toInterpretation.ordExtendLEquiv A
      have e₂ := f.toInterpretation.mapLEquiv e₁
      have e₃ := f.toInterpretation.compLEquiv g.toInterpretation.ordExtend A
      exact (h1.trans h2).trans (R.iso_invariant (e₂.comp e₃)).symm }

/-- `Trans` instance for FO(LFP) reductions, enabling `calc` chains. -/
noncomputable instance :
    Trans (α := DecisionProblem L₁) (β := DecisionProblem L₂) (γ := DecisionProblem L₃)
      LFPReduction LFPReduction LFPReduction where
  trans g f := g.trans f

end Trans

end DescriptiveComplexity
