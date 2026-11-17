/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
module

public import LeanPool.DescriptiveCounting.FixedPointStep
import all LeanPool.DescriptiveCounting.FixedPoint
import all LeanPool.DescriptiveCounting.FixedPointStep
import all LeanPool.DescriptiveCounting.Padding
import all LeanPool.DescriptiveCounting.SecondOrderPull

/-!
# FO(IFP): first-order logic with an inflationary fixed point

The inflationary fixed-point logic ([Gurevich–Shelah
1986][gurevich1986fixed]; [Abiteboul–Vianu 1989][abiteboul1989fixpoint];
[Ebbinghaus–Flum 1995][ebbinghaus1995finite], ch. 7): iterate the step
formulas of a `DescriptiveComplexity.StepDef` *inflationarily* – each stage
accumulates what the step formulas derive on top of the previous stage – and
read the output sentence at the limit. No positivity is required of the step
formulas: inflation makes the iteration monotone whatever they are, which is
the whole point of the logic.

Two definability notions result, and keeping them distinct is the entire
subject of the Abiteboul–Vianu theorem:

* `DescriptiveComplexity.IFPDefinableFree` – over the bare vocabulary, on
  unordered structures;
* `DescriptiveComplexity.IFPDefinable` – over the vocabulary expanded by an
  order, required for every linear order on the universe, the problem itself
  never seeing it. This is the setting of the capture theorem
  FO(≤, IFP) = PTIME (`DescriptiveComplexity.FixedPointInflationaryLFP`).

For SO(TC) the corresponding two notions coincide
(`DescriptiveComplexity.sotcDefinable_iff_free`): a walk can guess an order
into its state. Here they must *not* be conflated – an inflationary induction
cannot manufacture an order (its stages are isomorphism-invariant, so on a
bare set of `n` elements nothing asymmetric is ever derived), and the gap
between the two notions is precisely what makes the unordered
Abiteboul–Vianu theorem (`DescriptiveComplexity.AbiteboulVianu`) a theorem
about `P = PSPACE` rather than a triviality.

## Relation to FO(LFP), and why Gurevich–Shelah is not needed

`DescriptiveComplexity.LFPDefinable.ifpDefinable` embeds FO(LFP) into ordered
FO(IFP): the rules of a Horn program, read as one simultaneous step
(`DescriptiveComplexity.hornStepF`), form a `StepDef` whose inflationary
stages are exactly the derivation stages `DescriptiveComplexity.derivesIn`
(`DescriptiveComplexity.inflStage_toStepDef`). The converse translation –
FO(≤, IFP) back into FO(LFP), hence the capture of PTIME – is
`DescriptiveComplexity.FixedPointInflationaryLFP`.

This library states the Abiteboul–Vianu theorem for IFP versus PFP, as in
Abiteboul and Vianu's original form. The classical statement for *least*
fixed points on unordered structures needs Gurevich–Shelah (order-free
LFP = IFP, by stage comparison) on top; phrasing the theorem with IFP makes
that machinery unnecessary, a design decision, not an omission.

## Closure properties

FO(IFP) definability is closed under complement by construction
(`DescriptiveComplexity.IFPDefinable.compl` – negate the output), and under
(ordered) first-order reductions
(`DescriptiveComplexity.IFPDefinableFree.of_foReduction`,
`DescriptiveComplexity.IFPDefinable.of_orderedReduction`): the stages commute
with the pullback of the block (`DescriptiveComplexity.StepDef.inflStage_pull`)
and the output sentence pulls back through the extended interpretation,
exactly as for FO(LFP). The notion is class-worthy in the sense of
`DescriptiveComplexity.ComplexityClass`.
-/

@[expose] public section

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}}

namespace StepDef

/-! ### The value of an inflationary definition -/

/-- The value of a simultaneous induction read inflationarily: the output
sentence, at the limit of the inflationary iteration. -/
def IFPHolds (d : StepDef L) (A : Type) [L.Structure A] : Prop :=
  @Sentence.Realize _ A (d.B.structure₁ (L := L) (d.inflLimit A)) d.out

/-- Negating the output complements the defined property: FO(IFP) is closed
under complement *by construction*, being a logic rather than a fragment. -/
private def not (d : StepDef L) : StepDef L :=
  { B := d.B, step := d.step, out := ∼d.out }

private theorem ifpHolds_not (d : StepDef L) (A : Type) [L.Structure A] :
    d.not.IFPHolds A ↔ ¬d.IFPHolds A :=
  Iff.rfl

/-- The value of an inflationary definition is isomorphism-invariant. -/
private theorem ifpHolds_equiv (d : StepDef L) {M N : Type} [L.Structure M] [L.Structure N]
    (e : M ≃[L] N) : d.IFPHolds M ↔ d.IFPHolds N := by
  rw [IFPHolds, IFPHolds, d.inflLimit_map e]
  exact realize_sentence_of_equiv (d.B.extendEquiv' (L' := L) e (d.inflLimit M)) d.out

end StepDef

/-! ### Definability, ordered and order-free -/

/-- A decision problem is *order-free FO(IFP) definable* if, on nonempty
finite structures, it is the value of a simultaneous induction over its own
vocabulary, read inflationarily. This is the unordered notion the
Abiteboul–Vianu theorem is about; the capture theorem for PTIME instead uses
the ordered `DescriptiveComplexity.IFPDefinable`. -/
def IFPDefinableFree [L.IsRelational] (P : DecisionProblem L) : Prop :=
  ∃ d : StepDef L, ∀ (A : Type) [L.Structure A] [Finite A] [Nonempty A],
    P A ↔ d.IFPHolds A

/-- A decision problem is *FO(≤, IFP) definable* if, on nonempty finite
ordered structures, it is the value of a simultaneous induction over the
ordered expansion of its vocabulary, read inflationarily. As everywhere in
this library, the equivalence is required for every linear order, so the
notion is order-invariant: the formulas see the order, the problem does
not. -/
def IFPDefinable [L.IsRelational] (P : DecisionProblem L) : Prop :=
  ∃ d : StepDef (L.sum Language.order),
    ∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A],
      P A ↔ d.IFPHolds A

/-- Order-free FO(IFP) definability only depends on the finite instances of a
problem. -/
theorem ifpDefinableFree_congr [L.IsRelational] {P Q : DecisionProblem L}
    (h : ∀ (A : Type) [L.Structure A] [Finite A], P A ↔ Q A) :
    IFPDefinableFree P ↔ IFPDefinableFree Q := by
  constructor <;> rintro ⟨d, hd⟩ <;> refine ⟨d, ?_⟩ <;> intro A _ _ _
  · exact (h A).symm.trans (hd A)
  · exact (h A).trans (hd A)

/-- FO(≤, IFP) definability only depends on the finite instances of a
problem. -/
private theorem ifpDefinable_congr [L.IsRelational] {P Q : DecisionProblem L}
    (h : ∀ (A : Type) [L.Structure A] [Finite A], P A ↔ Q A) :
    IFPDefinable P ↔ IFPDefinable Q := by
  constructor <;> rintro ⟨d, hd⟩ <;> refine ⟨d, ?_⟩ <;> intro A _ _ _ _
  · exact (h A).symm.trans (hd A)
  · exact (h A).trans (hd A)

/-- **Order-free FO(IFP) definability is closed under complement**: negate the
output formula. -/
theorem IFPDefinableFree.compl [L.IsRelational] {P : DecisionProblem L}
    (h : IFPDefinableFree P) : IFPDefinableFree Pᶜ := by
  obtain ⟨d, hd⟩ := h
  refine ⟨d.not, ?_⟩
  intro A _ _ _
  exact (not_congr (hd A)).trans (d.ifpHolds_not A).symm

/-- **FO(≤, IFP) definability is closed under complement**: negate the output
formula. -/
theorem IFPDefinable.compl [L.IsRelational] {P : DecisionProblem L}
    (h : IFPDefinable P) : IFPDefinable Pᶜ := by
  obtain ⟨d, hd⟩ := h
  refine ⟨d.not, ?_⟩
  intro A _ _ _ _
  exact (not_congr (hd A)).trans (d.ifpHolds_not A).symm

/-! ### Closure under reductions -/

section Closure

variable {L₁ L₂ : Language.{0, 0}} [L₁.IsRelational] [L₂.IsRelational]
variable {P : DecisionProblem L₁} {Q : DecisionProblem L₂}

/-- **Order-free FO(IFP) definability is closed under first-order
reductions**: pull the induction back through the interpretation
(`DescriptiveComplexity.StepDef.pull`); the inflationary limit commutes with
the pullback (`DescriptiveComplexity.StepDef.inflLimit_pull`) and the output
sentence pulls back through the extended interpretation. -/
theorem IFPDefinableFree.of_foReduction (f : P ≤ᶠᵒ Q) (h : IFPDefinableFree Q) :
    IFPDefinableFree P := by
  obtain ⟨d, hd⟩ := h
  let := f.tagFinite
  let := f.tagNonempty
  refine ⟨d.pull f.toInterpretation, ?_⟩
  intro A _ _ _
  have := f.toInterpretation.map_finite A
  have := f.toInterpretation.map_nonempty A
  refine (f.correct A).trans ((hd (f.toInterpretation.Map A)).trans ?_)
  rw [StepDef.IFPHolds, StepDef.IFPHolds,
    StepDef.inflLimit_pull f.toInterpretation d A]
  let := (d.B.pull f.Tag f.dim).structure
    (d.B.pullAssign (d.inflLimit (f.toInterpretation.Map A)))
  have htrans := realize_sentence_of_equiv
    (f.toInterpretation.extendSOEquiv d.B A (d.inflLimit (f.toInterpretation.Map A))) d.out
  have hpull := (f.toInterpretation.extendSO d.B).realize_pullSentence d.out A
  exact (hpull.trans htrans).symm

/-- **FO(≤, IFP) definability is closed under ordered first-order
reductions.** The induction pulls back through the order-extended
interpretation; the two readings of the interpreted ordered structure are
identified by `DescriptiveComplexity.FOInterpretation.ordExtendLEquiv`, along
which the inflationary limit transports
(`DescriptiveComplexity.StepDef.inflLimit_map`). -/
theorem IFPDefinable.of_orderedReduction (f : P ≤ᶠᵒ[≤] Q) (h : IFPDefinable Q) :
    IFPDefinable P := by
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
  rw [StepDef.IFPHolds, StepDef.IFPHolds,
    StepDef.inflLimit_pull f.toInterpretation.ordExtend d A]
  let := (d.B.pull f.Tag f.dim).structure
    (d.B.pullAssign (d.inflLimit (f.toInterpretation.ordExtend.Map A)))
  have e₁ := f.toInterpretation.ordExtend.extendSOEquiv d.B A
    (d.inflLimit (f.toInterpretation.ordExtend.Map A))
  have e₂ := d.B.extendEquiv (f.toInterpretation.ordExtendLEquiv A)
    (d.inflLimit (f.toInterpretation.ordExtend.Map A))
  rw [← d.inflLimit_map (f.toInterpretation.ordExtendLEquiv A)] at e₂
  let : ((L₂.sum Language.order).sum d.B.lang).Structure
      ((f.toInterpretation.ordExtend.extendSO d.B).Map A) :=
    FOInterpretation.mapStructure (f.toInterpretation.ordExtend.extendSO d.B) A
  let : ((L₂.sum Language.order).sum d.B.lang).Structure
      (f.toInterpretation.ordExtend.Map A) :=
    @sumStructure (L₂.sum Language.order) d.B.lang (f.toInterpretation.ordExtend.Map A)
      (FOInterpretation.mapStructure f.toInterpretation.ordExtend A)
      (d.B.structure (d.inflLimit (f.toInterpretation.ordExtend.Map A)))
  let : ((L₂.sum Language.order).sum d.B.lang).Structure (f.toInterpretation.Map A) :=
    @sumStructure (L₂.sum Language.order) d.B.lang (f.toInterpretation.Map A) _
      (d.B.structure (d.inflLimit (f.toInterpretation.Map A)))
  have hout := StrongHomClass.realize_sentence
    (L := (L₂.sum Language.order).sum d.B.lang) (e₂.comp e₁) d.out
  have hpull := (f.toInterpretation.ordExtend.extendSO d.B).realize_pullSentence d.out A
  exact (hpull.trans hout).symm

/-- FO(≤, IFP) definability is closed under plain first-order reductions,
which are in particular ordered ones. -/
theorem IFPDefinable.of_foReduction (f : P ≤ᶠᵒ Q) (h : IFPDefinable Q) :
    IFPDefinable P :=
  h.of_orderedReduction f.toOrdered

end Closure

/-! ### Horn rules as one simultaneous inflationary step

The rules of an FO(LFP) definition, read as a single simultaneous step: the
step formula of the variable `i` says that some rule with head `i` fires –
its guard holds and its body atoms are in the current stage – with the head's
arguments instantiated at the free variables. Iterated inflationarily, the
stages are exactly the derivation stages `DescriptiveComplexity.derivesIn`,
so the limit is the least fixed point and FO(LFP) embeds into FO(≤, IFP)
(`DescriptiveComplexity.LFPDefinable.ifpDefinable`). The step formulas
produced here are *positive* in the block – inflation just does not care. -/

section Horn

variable {B : SOBlock} {k : ℕ}

/-- The relation symbol of a block variable, in the expanded vocabulary
`L.sum B.lang` (the generic-`L` sibling of
`DescriptiveComplexity.varOutSym`). -/
abbrev varInSym (L : Language.{0, 0}) (B : SOBlock) (i : B.ι) :
    (L.sum B.lang).Relations (B.arity i) :=
  Sum.inr (varSym B i)

/-- A second-order body atom, as a formula over the expanded vocabulary; its
arguments are read from the rule-variable component. -/
noncomputable def bodyAtomF (b : SOAtom B k) {n : ℕ} :
    (L.sum B.lang).Formula (Fin n ⊕ Fin k) :=
  Relations.formula (varInSym L B b.idx) fun j => Term.var (Sum.inr (b.args j))

/-- A guard, transported to the expanded vocabulary, over head-argument and
rule variables. -/
noncomputable def guardStepF (φ : L.Formula (Fin k)) {n : ℕ} :
    (L.sum B.lang).Formula (Fin n ⊕ Fin k) :=
  (LHom.sumInl.onFormula φ).relabel Sum.inr

open Classical in
/-- The contribution of one rule to the step formula of the variable `i`:
the rule's head is about `i`, its arguments are the free variables, its guard
holds, and its body atoms are in the current stage. -/
noncomputable def ruleStepF (c : HornClause L B k) (i : B.ι) :
    (L.sum B.lang).Formula (Fin (B.arity i) ⊕ Fin k) :=
  c.head.elim ⊥ fun a =>
    if h : a.idx = i then
      (Formula.iInf fun j : Fin (B.arity i) =>
        Term.equal (Term.var (Sum.inl j))
          (Term.var (Sum.inr (a.args (Fin.cast (congrArg B.arity h.symm) j))))) ⊓
        guardStepF c.guard ⊓ listInf (c.body.map (bodyAtomF (n := B.arity i)))
    else ⊥

/-- The step formula of the variable `i` induced by a list of rules: some
rule with head `i` fires, for some values of the rule variables. -/
noncomputable def hornStepF (rules : List (HornClause L B k)) (i : B.ι) :
    (L.sum B.lang).Formula (Fin (B.arity i)) :=
  Formula.iExs (Fin k) (listSup (rules.map fun c => ruleStepF c i))

section Realize

variable {A : Type} [L.Structure A] (ρ : B.Assignment A)

private theorem realize_bodyAtomF (b : SOAtom B k) {n : ℕ} (w : Fin n ⊕ Fin k → A) :
    (@Formula.Realize _ A (B.structure₁ (L := L) ρ) _ (bodyAtomF b) w) ↔
      b.Holds ρ fun q => w (Sum.inr q) := by
  let := B.structure₁ (L := L) ρ
  rw [bodyAtomF, Formula.realize_rel]
  exact Iff.rfl

private theorem realize_guardStepF (φ : L.Formula (Fin k)) {n : ℕ} (w : Fin n ⊕ Fin k → A) :
    (@Formula.Realize _ A (B.structure₁ (L := L) ρ) _ (guardStepF (B := B) φ) w) ↔
      φ.Realize fun q => w (Sum.inr q) := by
  let := B.structure₁ (L := L) ρ
  rw [guardStepF, Formula.realize_relabel, LHom.realize_onFormula]
  rfl

/-- **The step formula induced by a list of rules realizes as one round of
rule application** (`DescriptiveComplexity.stepDerives`). -/
private theorem realize_hornStepF (rules : List (HornClause L B k)) (i : B.ι)
    (x : Fin (B.arity i) → A) :
    (@Formula.Realize _ A (B.structure₁ (L := L) ρ) _ (hornStepF rules i) x) ↔
      stepDerives rules (fun q => ρ q.1 q.2) (⟨i, x⟩ : BAtom B A) := by
  classical
  let := B.structure₁ (L := L) ρ
  rw [hornStepF, Formula.realize_iExs]
  constructor
  · rintro ⟨v, hv⟩
    rw [realize_listSup] at hv
    obtain ⟨ψ, hψmem, hψ⟩ := hv
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hψmem
    cases hh : c.head with
    | none =>
      rw [ruleStepF, hh, Option.elim_none, Formula.realize_bot] at hψ
      exact hψ.elim
    | some a =>
      rw [ruleStepF, hh, Option.elim_some] at hψ
      by_cases hidx : a.idx = i
      · rw [dite_eq_left hidx] at hψ
        rw [Formula.realize_inf, Formula.realize_inf, Formula.realize_iInf] at hψ
        obtain ⟨⟨heqs, hguard⟩, hbody⟩ := hψ
        subst hidx
        refine ⟨c, hc, a, hh, v, ?_, ?_, ?_⟩
        · refine congrArg (Sigma.mk a.idx) (funext fun j => ?_)
          have hj := heqs j
          rw [Formula.realize_equal] at hj
          simpa using hj
        · exact (realize_guardStepF ρ c.guard _).mp hguard
        · intro b hb
          rw [realize_listInf] at hbody
          exact (realize_bodyAtomF ρ b _).mp
            (hbody _ (List.mem_map_of_mem hb))
      · rw [dite_eq_right hidx, Formula.realize_bot] at hψ
        exact hψ.elim
  · rintro ⟨c, hc, a, hh, v, heq, hguard, hbody⟩
    refine ⟨v, ?_⟩
    rw [realize_listSup]
    refine ⟨ruleStepF c i, List.mem_map_of_mem hc, ?_⟩
    have hidx : i = a.idx := congrArg Sigma.fst heq
    subst hidx
    injection heq with _ hargs
    rw [ruleStepF, hh, Option.elim_some, dite_eq_left rfl]
    rw [Formula.realize_inf, Formula.realize_inf, Formula.realize_iInf]
    refine ⟨⟨fun j => ?_, ?_⟩, ?_⟩
    · rw [Formula.realize_equal]
      simpa using congrFun hargs j
    · exact (realize_guardStepF ρ c.guard _).mpr hguard
    · rw [realize_listInf]
      rintro ψ hψ
      obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hψ
      exact (realize_bodyAtomF ρ b _).mpr (hbody b hb)

end Realize

end Horn

/-! ### FO(LFP) embeds into FO(≤, IFP) -/

section OfLFP

variable {L : Language.{0, 0}}

/-- The simultaneous induction induced by an FO(LFP) definition: same block,
the rules read as one simultaneous step, same output. -/
noncomputable def LFPDef.toStepDef (d : LFPDef L) : StepDef (L.sum Language.order) where
  B := d.B
  step := fun i => hornStepF d.rules i
  out := d.out

/-- The inflationary stages of the induced induction are the derivation
stages of the rules. -/
theorem inflStage_toStepDef (d : LFPDef L) (A : Type) [L.Structure A] [LinearOrder A]
    (n : ℕ) :
    d.toStepDef.inflStage A n =
      fun i x => derivesIn d.rules n (⟨i, x⟩ : BAtom d.B A) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    funext i x
    rw [d.toStepDef.inflStage_succ]
    refine propext (or_congr (iff_of_eq (congrFun (congrFun ih i) x)) ?_)
    rw [ih]
    exact realize_hornStepF (fun i x => derivesIn d.rules n ⟨i, x⟩) d.rules i x

/-- The value of the induced inflationary iteration is the least fixed point
of the rules. -/
theorem inflLimit_toStepDef (d : LFPDef L) (A : Type) [L.Structure A] [LinearOrder A] :
    d.toStepDef.inflLimit A = lfpAssign d.rules := by
  funext i x
  refine propext ?_
  change (∃ n, d.toStepDef.inflStage A n i x) ↔ Derives d.rules ⟨i, x⟩
  rw [derives_iff_derivesIn]
  exact exists_congr fun n => iff_of_eq (congrFun (congrFun (inflStage_toStepDef d A n) i) x)

/-- **Every FO(LFP) definition is an FO(≤, IFP) definition**: read the rules
as one simultaneous step; inflation iterates them to their least fixed point,
and the output survives unchanged. (The converse, closing the circle back
into FO(LFP), is `DescriptiveComplexity.FixedPointInflationaryLFP`.)
Registered in the Lax archive as
[`Lax535992.InflationaryIsLeastFixedPoint.lfpDefinable_ifpDefinable`](https://laxarchive.org/lax-535992/Lax535992.InflationaryIsLeastFixedPoint.html#s-Lax535992.InflationaryIsLeastFixedPoint.lfpDefinable_ifpDefinable). -/
theorem LFPDefinable.ifpDefinable [L.IsRelational] {P : DecisionProblem L}
    (h : LFPDefinable P) :
    IFPDefinable P := by
  obtain ⟨d, hd⟩ := h
  refine ⟨d.toStepDef, ?_⟩
  intro A _ _ _ _
  refine (hd A).trans ?_
  rw [LFPDef.Holds, StepDef.IFPHolds, inflLimit_toStepDef]
  exact Iff.rfl

end OfLFP

end DescriptiveComplexity
