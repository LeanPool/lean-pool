/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
module

import LeanPool.DescriptiveCounting.FixedPointExpand
public import LeanPool.DescriptiveCounting.FixedPointReductionComposition
import LeanPool.DescriptiveCounting.SecondOrderRelPull
import all LeanPool.DescriptiveCounting.Composition
import all LeanPool.DescriptiveCounting.FixedPointInflationary
import all LeanPool.DescriptiveCounting.FixedPointReduction
import all LeanPool.DescriptiveCounting.FixedPointReductionComposition

/-!
# The classes are closed under FO(LFP) reductions

Membership in PTIME, in NP and in coNP travels backward along an FO(LFP)
reduction (`DescriptiveComplexity.mem_PTIME_of_lfpReduction`,
`DescriptiveComplexity.mem_NP_of_lfpReduction`,
`DescriptiveComplexity.mem_coNP_of_lfpReduction`), exactly as it does along a
first-order one. This is what makes `≤ˡᶠᵖ` a usable reduction notion for these
classes rather than a definition with no theorems: without it, “`P` reduces to a
problem of the class” would say nothing about `P`.

The three proofs are different, and the difference is the point.

* **PTIME** is closed because the logic is: the reduction's induction and the
  membership's induction *stratify* into one
  (`DescriptiveComplexity.StepDef.stratify`), after the latter is pulled back
  through the interpretation. Nothing is guessed.
* **NP** is closed because an induction can be eliminated from a `Σ₁`
  definition (`DescriptiveComplexity.sigmaSODefinable_of_ifpExpand`), the
  quantifier block that replaces it merging with the one already there.
* **coNP** is closed by complementation – a reduction complements
  (`DescriptiveComplexity.LFPReduction.compl`) – which is cheaper than
  redoing the argument with a universal block.

Above the first level nothing is claimed here. The same argument would put an
extra existential block *innermost* in a `Σₖ` prefix, which merges with the
innermost block only when that block is existential; the even levels would need
the dual elimination, through `DescriptiveComplexity.PTIME_subset_coNP`, and the
vocabulary bookkeeping of a block inserted in the middle of a prefix. PSPACE is
open here for a sharper reason: FO(PFP) has no stratification theorem, the
partial iteration not being monotone.

## Hardness

`DescriptiveComplexity.CofinalHardLFP` is hardness stated with `≤ˡᶠᵖ` in place
of `≤ʳᶠᵒ[≤]`, and `DescriptiveComplexity.CofinalHard.toLFP` says that a hard
problem in the library's sense is hard in this weaker one – the expected
implication, since a first-order reduction is an FO(LFP) reduction. Note the
direction: hardness under a *larger* class of reductions is a *weaker*
statement, so every completeness theorem of the catalog implies its
polynomial-time-reduction reading, and none of them is superseded by it.
-/

@[expose] public section

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L₁ L₂ : Language.{0, 0}}

/-! ### The definable domain is inhabited, as a sentence -/

section DomNonempty

variable {Tag : Type} [Finite Tag] {dim : ℕ}

open Classical in
/-- “Some tagged tuple is in the domain”, as a first-order sentence of the
source vocabulary: the disjunction over the (finitely many) tags of the
existential closure of the domain formula. -/
private noncomputable def RelFOInterpretation.domNonemptyS
    (I : RelFOInterpretation L₁ L₂ Tag dim) : L₁.Sentence :=
  letI : Fintype Tag := Fintype.ofFinite Tag
  Formula.iSup fun t : Tag => ((I.domFormula t).relabel Sum.inr).iExs (Fin dim)

private theorem RelFOInterpretation.realize_domNonemptyS (I : RelFOInterpretation L₁ L₂ Tag dim)
    (A : Type) [L₁.Structure A] :
    A ⊨ I.domNonemptyS ↔ Nonempty (I.MapRel A) := by
  classical
  let : Fintype Tag := Fintype.ofFinite Tag
  rw [RelFOInterpretation.domNonemptyS]
  simp only [Sentence.Realize, Formula.realize_iSup, Formula.realize_iExs,
    Formula.realize_relabel]
  constructor
  · rintro ⟨t, w, hw⟩
    exact ⟨⟨(t, w), by simpa using hw⟩⟩
  · rintro ⟨⟨⟨t, w⟩, hw⟩⟩
    exact ⟨t, w, by simpa using hw⟩

end DomNonempty

/-! ### Polynomial time -/

section PTime

variable [L₁.IsRelational] [L₂.IsRelational] {P : DecisionProblem L₁} {Q : DecisionProblem L₂}

/-- **FO(≤, IFP) definability is closed under FO(LFP) reductions**: the
reduction's induction and the definition's induction stratify into one, the
latter pulled back through the (order-extended) interpretation. -/
theorem IFPDefinable.of_lfpReduction (f : P ≤ˡᶠᵖ Q) (h : IFPDefinable Q) :
    IFPDefinable P := by
  obtain ⟨d, hd⟩ := h
  let := f.tagFinite
  let : LinearOrder f.Tag := finiteLinearOrder f.Tag
  set I := f.toInterpretation with hI
  refine ⟨I.ind.stratify (d.pullRel I.ordExtend.toRel), ?_⟩
  intro A _ _ _ _
  let := I.mapLinearOrder A
  have : Finite (I.Map A) := I.map_finite A
  have : Nonempty (I.Map A) := f.map_nonempty A
  refine (f.correct A).trans ((hd (I.Map A)).trans ?_)
  -- the stratified induction computes the pulled one over the expanded structure
  have hstrat := I.ind.ifpHolds_stratify (A := A) (d.pullRel I.ordExtend.toRel)
  refine Iff.trans ?_ hstrat.symm
  -- and the pulled one is the original, read on the order-extended universe
  let : ((L₁.sum Language.order).sum I.ordExtend.ind.B.lang).Structure A :=
    I.ordExtend.expStructure A
  have hpull := StepDef.ifpHolds_pullRel (A := A) d I.ordExtend.toRel
  refine Iff.trans ?_ hpull.symm
  exact (@StepDef.ifpHolds_equiv (L₂.sum Language.order) d (I.ordExtend.Map A) (I.Map A)
    (LFPInterpretation.mapStructure I.ordExtend A)
    (letI := I.mapLinearOrder A; sumOrderStructure L₂ (I.Map A))
    (I.ordExtendLEquiv A)).symm

/-- **PTIME is closed under FO(LFP) reductions**: a problem reducing to a
polynomial-time problem by a polynomial-time reduction is polynomial time. -/
theorem mem_PTIME_of_lfpReduction (f : P ≤ˡᶠᵖ Q) (h : Q ∈ PTIME) : P ∈ PTIME :=
  (ifpDefinable_iff_mem_PTIME P).mp
    (((ifpDefinable_iff_mem_PTIME Q).mpr h).of_lfpReduction f)

end PTime

/-! ### NP, and coNP by complementation -/

section NP

variable [L₁.IsRelational] [L₂.IsRelational] {P : DecisionProblem L₁} {Q : DecisionProblem L₂}

/-- **`Σ₁`-definability is closed under FO(LFP) reductions.** The membership
sentence is pulled back through the interpretation, over the base structure
expanded by the reduction's induction
(`DescriptiveComplexity.sorealize_pullRelSO`); the induction is then eliminated
from the pulled definition
(`DescriptiveComplexity.sigmaSODefinable_of_ifpExpand`), and the order the
reduction uses is re-quantified inside the block
(`DescriptiveComplexity.sigmaSODefinable_of_orderPull`). -/
private theorem SigmaSODefinable.of_lfpReduction (f : P ≤ˡᶠᵖ Q) (h : SigmaSODefinable 1 Q) :
    SigmaSODefinable 1 P := by
  obtain ⟨Bs, hlen, φ, hφ⟩ := h
  let := f.tagFinite
  set I := f.toInterpretation with hI
  -- the target problem, pulled back through the interpretation alone: a problem
  -- over the base vocabulary expanded by the reduction's induction
  let S : DecisionProblem ((L₁.sum Language.order).sum I.ind.B.lang) :=
    { Holds := fun A' inst =>
        Nonempty (@RelFOInterpretation.MapRel _ _ _ _ I.toRel A' inst) ∧
          Q (@RelFOInterpretation.MapRel _ _ _ _ I.toRel A' inst)
      iso_invariant := fun {M N} instM instN e =>
        and_congr ⟨fun hne => hne.map (I.toRel.mapRelLEquiv e),
            fun hne => hne.map (I.toRel.mapRelLEquiv e.symm)⟩
          (Q.iso_invariant (I.toRel.mapRelLEquiv e)) }
  have hS : SigmaSODefinable 1 S := by
    refine ⟨pullBlocks f.Tag f.dim Bs, by simpa [pullBlocks] using hlen,
      (soLangEmbed (pullBlocks f.Tag f.dim Bs) _).onSentence I.toRel.domNonemptyS ⊓
        pullRelSO Bs _ L₂ I.toRel φ, ?_⟩
    intro A' _ _ _
    rw [sorealize_inf_embed (pullBlocks f.Tag f.dim Bs) _ A' _ _ _ true,
      I.toRel.realize_domNonemptyS A']
    refine and_congr_right fun hne => ?_
    have : Finite (I.toRel.MapRel A') := I.toRel.mapRel_finite A'
    exact (hφ (I.toRel.MapRel A')).trans (sorealize_pullRelSO I.toRel A' Bs φ true)
  -- the induction is eliminated from that definition
  have hP' : SigmaSODefinable 1
      ({ Holds := fun A _ => Nonempty (I.Map A) ∧ Q (I.Map A)
         iso_invariant := fun {M N} instM instN e =>
           and_congr ⟨fun hne => hne.map (I.mapLEquiv e),
               fun hne => hne.map (I.mapLEquiv e.symm)⟩
             (Q.iso_invariant (I.mapLEquiv e)) } : DecisionProblem (L₁.sum Language.order)) :=
    sigmaSODefinable_of_ifpExpand I.ind hS fun A _ _ _ => Iff.rfl
  -- and the order is re-quantified inside the block
  obtain ⟨Cs, hlen', χ, hχ⟩ := hP'
  obtain ⟨C, rfl⟩ := List.length_eq_one_iff.mp hlen'
  refine sigmaSODefinable_of_orderPull [C] rfl χ ?_
  intro A _ _ _
  have key : ∀ lo : LinearOrder A,
      (letI := lo
       P A ↔ SORealize (L₁.sum Language.order) A [C] χ true) := by
    intro lo
    let := lo
    have : Finite (I.Map A) := I.map_finite A
    have hne : Nonempty (I.Map A) := f.map_nonempty A
    refine (f.correct A).trans (Iff.trans ?_ (hχ A))
    exact ⟨fun hQ => ⟨hne, hQ⟩, fun h => h.2⟩
  exact ⟨fun hP => ⟨finiteLinearOrder A, (key _).mp hP⟩, fun ⟨lo, h⟩ => (key lo).mpr h⟩

/-- **NP is closed under FO(LFP) reductions**: a problem reducing to an NP
problem by a polynomial-time reduction is in NP. -/
theorem mem_NP_of_lfpReduction (f : P ≤ˡᶠᵖ Q) (h : Q ∈ NP) : P ∈ NP :=
  SigmaSODefinable.of_lfpReduction f h

/-- **coNP is closed under FO(LFP) reductions**, by complementation: the same
interpretation reduces the complements. -/
theorem mem_coNP_of_lfpReduction (f : P ≤ˡᶠᵖ Q) (h : Q ∈ coNP) : P ∈ coNP :=
  (mem_piP_iff 1 P).mpr (mem_NP_of_lfpReduction f.compl ((mem_piP_iff 1 Q).mp h))

/-- `Π₁`-definability is closed under FO(LFP) reductions – the same statement
as `DescriptiveComplexity.mem_coNP_of_lfpReduction`, at the level of the
logic. -/
private theorem PiSODefinable.of_lfpReduction (f : P ≤ˡᶠᵖ Q) (h : PiSODefinable 1 Q) :
    PiSODefinable 1 P :=
  (piSODefinable_iff_compl 1 P).mpr
    (SigmaSODefinable.of_lfpReduction f.compl ((piSODefinable_iff_compl 1 Q).mp h))

end NP

/-! ### Membership under relativized first-order reductions

The same three classes are closed under the *relativized* first-order
reductions `≤ʳᶠᵒ[≤]` – the notion all of this library's hardness travels along.
Only the hardness half of that closure was available before
(`DescriptiveComplexity.ComplexityClass.hard_of_relOrderedReduction`); the
membership half is these three theorems, and they are corollaries of the
pullback of `DescriptiveComplexity.SecondOrderRelPull` and of
`DescriptiveComplexity.IFPDefinable.of_relOrderedReduction`. (What is still
missing is the corresponding *field* of
`DescriptiveComplexity.ComplexityClass`, which every class literal of the
library would have to supply.) -/

section RelOrdered

variable [L₁.IsRelational] [L₂.IsRelational] {P : DecisionProblem L₁} {Q : DecisionProblem L₂}

/-- **PTIME is closed under relativized ordered reductions.**
Registered in the Lax archive as
[`Lax535992.PTIMEClosure.PTIME_mem_of_relOrderedReduction`](https://laxarchive.org/lax-535992/Lax535992.PTIMEClosure.html#s-Lax535992.PTIMEClosure.PTIME_mem_of_relOrderedReduction). -/
theorem mem_PTIME_of_relOrderedReduction (f : P ≤ʳᶠᵒ[≤] Q) (h : Q ∈ PTIME) : P ∈ PTIME :=
  (ifpDefinable_iff_mem_PTIME P).mp
    (((ifpDefinable_iff_mem_PTIME Q).mpr h).of_relOrderedReduction f)

/-- **NP is closed under relativized ordered reductions.** -/
private theorem mem_NP_of_relOrderedReduction (f : P ≤ʳᶠᵒ[≤] Q) (h : Q ∈ NP) : P ∈ NP :=
  SigmaSODefinable.of_relOrderedReduction f h

/-- **coNP is closed under relativized ordered reductions.** -/
theorem mem_coNP_of_relOrderedReduction (f : P ≤ʳᶠᵒ[≤] Q) (h : Q ∈ coNP) : P ∈ coNP :=
  PiSODefinable.of_relOrderedReduction f h

end RelOrdered

/-! ### Hardness under FO(LFP) reductions -/

section Hardness

variable {L : Language.{0, 0}} [L.IsRelational]

/-- Hardness for a collection of problems under **FO(LFP) reductions**, stated
cofinally as `DescriptiveComplexity.CofinalHard` is: every problem of the
collection FO(LFP)-reduces to every problem that `P` FO(LFP)-reduces to.

Hardness under a wider class of reductions is a weaker statement, so this is
implied by the library's own hardness (`DescriptiveComplexity.CofinalHard.toLFP`)
and does not replace it. -/
def CofinalHardLFP (Mem : ∀ {L₀ : Language.{0, 0}} [L₀.IsRelational], DecisionProblem L₀ → Prop)
    (P : DecisionProblem L) : Prop :=
  ∀ {L' : Language.{0, 0}} [L'.IsRelational] (S : DecisionProblem L'),
    Nonempty (P ≤ˡᶠᵖ S) →
      ∀ {L'' : Language.{0, 0}} [L''.IsRelational] (Q : DecisionProblem L''),
        Mem Q → Nonempty (Q ≤ˡᶠᵖ S)

/-- **Hardness under FO(LFP) reductions is the usual notion**: every problem of
the collection reduces to `P` itself. -/
private theorem cofinalHardLFP_iff
    (Mem : ∀ {L₀ : Language.{0, 0}} [L₀.IsRelational], DecisionProblem L₀ → Prop)
    (P : DecisionProblem L) :
    CofinalHardLFP Mem P ↔
      ∀ {L'' : Language.{0, 0}} [L''.IsRelational] (Q : DecisionProblem L''),
        Mem Q → Nonempty (Q ≤ˡᶠᵖ P) := by
  constructor
  · intro h L'' _ Q hQ
    exact h P ⟨(FOReduction.refl P).toLFP⟩ Q hQ
  · intro h L' _ S hS L'' _ Q hQ
    exact ⟨(h Q hQ).some.trans hS.some⟩

/-- **Hardness travels forward along FO(LFP) reductions.** -/
theorem CofinalHardLFP.of_lfpReduction
    {Mem : ∀ {L₀ : Language.{0, 0}} [L₀.IsRelational], DecisionProblem L₀ → Prop}
    {L' : Language.{0, 0}} [L'.IsRelational] {P : DecisionProblem L} {Q : DecisionProblem L'}
    (f : P ≤ˡᶠᵖ Q) (hP : CofinalHardLFP Mem P) : CofinalHardLFP Mem Q := by
  intro L'' _ S hQS L₀ _ R hR
  exact hP S (hQS.map fun g => f.trans g) R hR

/-- **A problem hard for a collection under first-order reductions is hard for
it under FO(LFP) reductions**: every first-order reduction is an FO(LFP)
reduction. -/
theorem CofinalHard.toLFP
    {Mem : ∀ {L₀ : Language.{0, 0}} [L₀.IsRelational], DecisionProblem L₀ → Prop}
    {P : DecisionProblem L} (h : CofinalHard Mem P) : CofinalHardLFP Mem P := by
  intro L' _ S hPS L'' _ Q hQ
  exact ((cofinalHard_iff Mem P).mp h Q hQ).map fun g => g.toLFP.trans hPS.some

/-- **A `𝒞`-hard problem of a class of this library is hard under FO(LFP)
reductions.** Reading a completeness theorem of the catalog with
polynomial-time reductions in place of first-order ones is this corollary. -/
theorem ComplexityClass.hard_lfp_of_hard {C : ComplexityClass} {P : DecisionProblem L}
    (hC : ∀ {L' : Language.{0, 0}} [L'.IsRelational] (R : DecisionProblem L'),
      C.Hard R ↔ CofinalHard C.Mem R) (h : C.Hard P) : CofinalHardLFP C.Mem P :=
  CofinalHard.toLFP ((hC P).mp h)

end Hardness

end DescriptiveComplexity
