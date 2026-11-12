/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
module

public import LeanPool.DescriptiveCounting.FixedPointInflationaryLFP
import LeanPool.DescriptiveCounting.FixedPointOrderTransfer
import LeanPool.DescriptiveCounting.SecondOrderMerge
import LeanPool.DescriptiveCounting.Problems.HornSat
import all LeanPool.DescriptiveCounting.FixedPointInflationary
import all LeanPool.DescriptiveCounting.FixedPointOrderTransfer
import all LeanPool.DescriptiveCounting.FixedPointStep
import all LeanPool.DescriptiveCounting.SecondOrderMerge

/-!
# Eliminating an induction from a second-order definition

**The theorem**: a problem defined by a `Σ₁` sentence read over a structure
*expanded by the value of an inflationary induction* is `Σ₁` definable outright
(`DescriptiveComplexity.sigmaSODefinable_of_ifpExpand`). Since an induction is
exactly what an FO(LFP) reduction may consult, this is what closes NP under
FO(LFP) reductions (`DescriptiveComplexity.FixedPointReductionClosure`).

## The argument, and why no fixed-point certificate is built

The direct route – guess the value of the induction inside the existential
block and have the kernel check it – founders on the check: the inflationary
value is *not* characterized by being a fixed point (the step formulas are not
monotone, so a fixed point need not contain it), and pinning it down needs the
whole stage sequence, which is the construction of
`DescriptiveComplexity.FixedPointInflationaryLFP` all over again.

The route taken instead pays nothing, by pushing the induction *inside* the
guess:

* the guessed relations are made part of the vocabulary. Over that larger
  vocabulary, “the induction's value satisfies the kernel” is a problem defined
  by an induction with a first-order output – order-free FO(IFP) definable, so
  in PTIME, so (`DescriptiveComplexity.PTIME_subset_NP`) `Σ₁` definable, with
  no induction left;
* two consecutive existential blocks – the original guess and the one that
  replaces the induction – merge into one
  (`DescriptiveComplexity.sigmaSODefinable_exBlock`), which is what keeps the
  result at `Σ₁` rather than at `Σ₂`.

The two supporting constructions are of the kind that has to exist once: an
induction read over a larger vocabulary computes the same value
(`DescriptiveComplexity.StepDef.ifpHolds_liftLang`), and expanding by two
blocks in either order is the same structure
(`DescriptiveComplexity.swapExpand`).
-/

@[expose] public section

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

/-! ### Expanding by two blocks, in either order -/

section Swap

variable (L : Language.{0, 0}) (B C : SOBlock)

/-- Swapping two block expansions: the same symbols, read in the other
association. -/
private def swapExpand : (L.sum B.lang).sum C.lang →ᴸ (L.sum C.lang).sum B.lang where
  onFunction := fun {_} f =>
    match f with
    | .inl (.inl g) => .inl (.inl g)
    | .inl (.inr g) => isEmptyElim g
    | .inr g => isEmptyElim g
  onRelation := fun {_} r =>
    match r with
    | .inl (.inl s) => .inl (.inl s)
    | .inl (.inr s) => .inr s
    | .inr s => .inl (.inr s)

variable {L B C} {A : Type}

/-- The swap is an expansion: expanding by `B` then by `C` interprets every
symbol as expanding by `C` then by `B` does. -/
private theorem swapExpand_isExpansionOn (instL : L.Structure A) (ρ : B.Assignment A)
    (μ : C.Assignment A) :
    @LHom.IsExpansionOn _ _ (swapExpand L B C) A
      (@SOBlock.structure₁ (L.sum B.lang) C A (B.structure₁ (L := L) ρ) μ)
      (@SOBlock.structure₁ (L.sum C.lang) B A (C.structure₁ (L := L) μ) ρ) := by
  let := instL
  let := B.structure ρ
  let := C.structure μ
  refine ⟨fun {n} f x => ?_, fun {n} r x => ?_⟩
  · rcases f with (g | g) | g
    · rfl
    · exact isEmptyElim g
    · exact isEmptyElim g
  · rcases r with (s | s) | s
    · rfl
    · rfl
    · rfl

/-- Realization across the swap. -/
private theorem realize_swapExpand (instL : L.Structure A) (ρ : B.Assignment A)
    (μ : C.Assignment A) (φ : ((L.sum B.lang).sum C.lang).Sentence) :
    (@Sentence.Realize _ A
      (@SOBlock.structure₁ (L.sum C.lang) B A (C.structure₁ (L := L) μ) ρ)
      ((swapExpand L B C).onSentence φ)) ↔
      @Sentence.Realize _ A
        (@SOBlock.structure₁ (L.sum B.lang) C A (B.structure₁ (L := L) ρ) μ) φ := by
  let := instL
  let := @SOBlock.structure₁ (L.sum B.lang) C A (B.structure₁ (L := L) ρ) μ
  let := @SOBlock.structure₁ (L.sum C.lang) B A (C.structure₁ (L := L) μ) ρ
  have := swapExpand_isExpansionOn instL ρ μ
  exact LHom.realize_onSentence (M := A) (φ := swapExpand L B C) (ψ := φ)

end Swap

/-! ### An induction read over a larger vocabulary -/

namespace StepDef

variable {L L' : Language.{0, 0}} (φ : L →ᴸ L') (d : StepDef L)

/-- A simultaneous induction read over a larger vocabulary: the step formulas
and the output are transported along the vocabulary map, which they use only
through the symbols they already mention. This generalizes
`DescriptiveComplexity.StepDef.liftOrder`, the case of the ordered
expansion. -/
noncomputable def liftLang : StepDef L' where
  B := d.B
  step := fun i => (φ.sumMap (LHom.id d.B.lang)).onFormula (d.step i)
  out := (φ.sumMap (LHom.id d.B.lang)).onSentence d.out

variable {A : Type} (instL : L.Structure A) (instL' : L'.Structure A)
variable (hexp : @LHom.IsExpansionOn _ _ φ A instL instL')

include hexp in
theorem realize_liftLang {α : Type} (ρ : d.B.Assignment A)
    (ψ : (L.sum d.B.lang).Formula α) (v : α → A) :
    (@Formula.Realize _ A (@SOBlock.structure₁ L' d.B A instL' ρ) _
      ((φ.sumMap (LHom.id d.B.lang)).onFormula ψ) v) ↔
      @Formula.Realize _ A (@SOBlock.structure₁ L d.B A instL ρ) _ ψ v := by
  let := instL
  let := instL'
  let := hexp
  let := @SOBlock.structure₁ L d.B A instL ρ
  let := @SOBlock.structure₁ L' d.B A instL' ρ
  exact LHom.realize_onFormula (φ := φ.sumMap (LHom.id d.B.lang)) ψ

include hexp in
theorem next_liftLang (ρ : d.B.Assignment A) :
    @StepDef.next L' (d.liftLang φ) A instL' ρ = @StepDef.next L d A instL ρ := by
  funext i x
  exact propext (d.realize_liftLang φ instL instL' hexp ρ (d.step i) x)

include hexp in
theorem inflStage_liftLang (n : ℕ) :
    @StepDef.inflStage L' (d.liftLang φ) A instL' n = @StepDef.inflStage L d A instL n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    funext i x
    rw [@StepDef.inflStage_succ L' (d.liftLang φ) A instL' n,
      @StepDef.inflStage_succ L d A instL n, ih]
    refine propext (or_congr Iff.rfl ?_)
    exact iff_of_eq (congrFun (congrFun
      (d.next_liftLang φ instL instL' hexp (@StepDef.inflStage L d A instL n)) i) x)

include hexp in
/-- **An induction computes the same value over a larger vocabulary.** -/
theorem inflLimit_liftLang :
    @StepDef.inflLimit L' (d.liftLang φ) A instL' = @StepDef.inflLimit L d A instL := by
  funext i x
  exact propext (exists_congr fun n => iff_of_eq
    (congrFun (congrFun (d.inflStage_liftLang φ instL instL' hexp n) i) x))

include hexp in
/-- The inflationary value of the lifted induction is the original one. -/
theorem ifpHolds_liftLang :
    (@StepDef.IFPHolds L' (d.liftLang φ) A instL') ↔ @StepDef.IFPHolds L d A instL := by
  rw [StepDef.IFPHolds, StepDef.IFPHolds, d.inflLimit_liftLang φ instL instL' hexp]
  exact d.realize_liftLang φ instL instL' hexp _ d.out default

end StepDef

/-! ### Two existential blocks are one -/

section ExBlock

variable {L : Language.{0, 0}} [L.IsRelational]

/-- **An existential guess over an expanded vocabulary stays in `Σ₁`**: if `S`,
a problem over the vocabulary expanded by a block `C`, is `Σ₁` definable, then
so is “some assignment of `C` makes `S` hold”. The two existential blocks merge
into one (`DescriptiveComplexity.SOBlock.cons`), which is what keeps the level
at `Σ₁`. -/
theorem sigmaSODefinable_exBlock {C : SOBlock} {S : DecisionProblem (L.sum C.lang)}
    (hS : SigmaSODefinable 1 S) {P : DecisionProblem L}
    (hP : ∀ (A : Type) [_instA : L.Structure A] [Finite A] [Nonempty A],
      P A ↔ ∃ ρ : C.Assignment A,
        @DecisionProblem.Holds _ _ S A (C.structure₁ (L := L) ρ)) :
    SigmaSODefinable 1 P := by
  obtain ⟨Bs, hlen, ψ, hψ⟩ := hS
  obtain ⟨D, rfl⟩ := List.length_eq_one_iff.mp hlen
  refine ⟨[SOBlock.cons C D], rfl, (mergeStep L C D).onSentence ψ, ?_⟩
  intro A instA _ _
  have key : ∀ (ρ : C.Assignment A) (μ : D.Assignment A),
      (@Sentence.Realize _ A
          (@SOBlock.structure₁ L (SOBlock.cons C D) A instA (consAssign ρ μ))
          ((mergeStep L C D).onSentence ψ)) ↔
        @Sentence.Realize _ A
          (@SOBlock.structure₁ (L.sum C.lang) D A (C.structure₁ (L := L) ρ) μ) ψ := by
    intro ρ μ
    let := instA
    let := C.structure ρ
    let := D.structure μ
    let := (SOBlock.cons C D).structure (consAssign ρ μ)
    have := mergeStep_isExpansionOn L instA C D ρ μ
    exact LHom.realize_onSentence (M := A) (φ := mergeStep L C D) (ψ := ψ)
  refine (hP A).trans ⟨?_, ?_⟩
  · rintro ⟨ρ, hρ⟩
    let := C.structure₁ (L := L) ρ
    obtain ⟨μ, hμ⟩ := (hψ A).mp hρ
    exact ⟨consAssign ρ μ, (key ρ μ).mpr hμ⟩
  · rintro ⟨π, hπ⟩
    refine ⟨fun i => π (Sum.inl i), ?_⟩
    let := C.structure₁ (L := L) (fun i => π (Sum.inl i))
    refine (hψ A).mpr ⟨fun i => π (Sum.inr i), ?_⟩
    refine (key (fun i => π (Sum.inl i)) (fun i => π (Sum.inr i))).mp ?_
    have hcons : consAssign (fun i => π (Sum.inl i)) (fun i => π (Sum.inr i)) = π := by
      funext i
      cases i with
      | inl i => rfl
      | inr i => rfl
    rwa [hcons]

end ExBlock

/-! ### Eliminating the induction -/

section Expand

variable {L : Language.{0, 0}} [L.IsRelational]

/-- **A `Σ₁` definition read over the value of an induction is a `Σ₁`
definition.** If `S` – a problem over the vocabulary expanded by the relation
variables of a simultaneous induction `d` – is `Σ₁` definable, then so is the
problem “`S` holds of the structure expanded by the value of `d`”.

This is the substitution property NP needs: the FO(LFP) relations an FO(LFP)
reduction consults can be removed from a `Σ₁` definition, at no cost in
quantifier alternation. -/
theorem sigmaSODefinable_of_ifpExpand (d : StepDef L) {S : DecisionProblem (L.sum d.B.lang)}
    (hS : SigmaSODefinable 1 S) {P : DecisionProblem L}
    (hP : ∀ (A : Type) [_instA : L.Structure A] [Finite A] [Nonempty A],
      P A ↔ @DecisionProblem.Holds _ _ S A (d.B.structure₁ (L := L) (d.inflLimit A))) :
    SigmaSODefinable 1 P := by
  obtain ⟨Bs, hlen, φ, hφ⟩ := hS
  obtain ⟨C, rfl⟩ := List.length_eq_one_iff.mp hlen
  -- the induction, read over the vocabulary expanded by the guessed block, with
  -- the kernel as its output: an induction with a first-order output, hence in
  -- PTIME
  let dC : StepDef (L.sum C.lang) :=
    { B := (d.liftLang (LHom.sumInl (L' := C.lang))).B
      step := (d.liftLang (LHom.sumInl (L' := C.lang))).step
      out := (swapExpand L d.B C).onSentence φ }
  have hexpC : ∀ (A : Type) (instA : L.Structure A) (μ : C.Assignment A),
      @LHom.IsExpansionOn L (L.sum C.lang) (LHom.sumInl (L' := C.lang)) A instA
        (@SOBlock.structure₁ L C A instA μ) := by
    intro A instA μ
    let := instA
    let := C.structure μ
    infer_instance
  have hlim : ∀ (A : Type) (instA : L.Structure A) (μ : C.Assignment A),
      @StepDef.inflLimit (L.sum C.lang) dC A
          (@SOBlock.structure₁ L C A instA μ) = @StepDef.inflLimit L d A instA :=
    fun A instA μ => d.inflLimit_liftLang (LHom.sumInl (L' := C.lang)) instA
      (@SOBlock.structure₁ L C A instA μ) (hexpC A instA μ)
  let R : DecisionProblem (L.sum C.lang) :=
    { Holds := fun A inst => @StepDef.IFPHolds (L.sum C.lang) dC A inst
      iso_invariant := fun {M N} instM instN e =>
        @StepDef.ifpHolds_equiv (L.sum C.lang) dC M N instM instN e }
  have hRfree : IFPDefinableFree R := ⟨dC, fun A _ _ _ => Iff.rfl⟩
  have hRsigma : SigmaSODefinable 1 R :=
    PTIME_subset_NP ((ifpDefinable_iff_mem_PTIME R).mp hRfree.ifpDefinable)
  refine sigmaSODefinable_exBlock (C := C) (S := R) hRsigma ?_
  intro A instA _ _
  have hR : ∀ μ : C.Assignment A,
      (@DecisionProblem.Holds _ _ R A (@SOBlock.structure₁ L C A instA μ)) ↔
        @Sentence.Realize _ A
          (@SOBlock.structure₁ (L.sum d.B.lang) C A
            (@SOBlock.structure₁ L d.B A instA (@StepDef.inflLimit L d A instA)) μ) φ := by
    intro μ
    change (@StepDef.IFPHolds (L.sum C.lang) dC A (@SOBlock.structure₁ L C A instA μ)) ↔ _
    rw [StepDef.IFPHolds, hlim A instA μ]
    exact realize_swapExpand instA (@StepDef.inflLimit L d A instA) μ φ
  refine (hP A).trans (Iff.trans ?_ (exists_congr fun μ => (hR μ).symm))
  exact @hφ A (@SOBlock.structure₁ L d.B A instA (@StepDef.inflLimit L d A instA)) _ _

end Expand

end DescriptiveComplexity
