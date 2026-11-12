/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
module

public import LeanPool.DescriptiveCounting.FixedPointStepRel
import all LeanPool.DescriptiveCounting.FixedPointStepRel
import all LeanPool.DescriptiveCounting.SecondOrderNewPull

/-!
# Second-order definability pulls back through a relativized interpretation

`DescriptiveComplexity.SecondOrderPull` pulls an alternating second-order
sentence back through an interpretation whose universe is *all* tagged tuples.
This file does the same for an interpretation with a **definable domain**
(`DescriptiveComplexity.RelFOInterpretation`), and concludes that the levels of
the polynomial hierarchy are closed under relativized ordered reductions
(`DescriptiveComplexity.SigmaSODefinable.of_relOrderedReduction`,
`DescriptiveComplexity.PiSODefinable.of_relOrderedReduction`) – the membership
half of the closure whose hardness half `DescriptiveComplexity.Relativized`
supplies.

## Why the transfer of assignments is a retraction, not a bijection

Over the whole universe, assignments of a block on the interpreted structure
and assignments of the pulled block on the base structure correspond
bijectively (`DescriptiveComplexity.SOBlock.pullAssign`,
`DescriptiveComplexity.SOBlock.mergeAssign`). Over a definable domain they do
not: a pulled relation may hold of tuples that are not points of the target at
all, and no condition on the target's assignment says anything about them.

What survives is a **retraction**: reading a guessed pulled assignment back on
the domain (`DescriptiveComplexity.SOBlock.readAssignRel`) undoes the transfer
of a target assignment (`DescriptiveComplexity.SOBlock.pullAssignRel`), i.e.,
`readAssignRel ∘ pullAssignRel = id`
(`DescriptiveComplexity.SOBlock.readAssignRel_pullAssignRel`). That is enough
for a quantifier of *either* polarity: an existential guess is transported
forward and read back, a universal one is instantiated at the read-back
assignment. The off-domain junk a guess may carry is never looked at, since
every atom the kernel evaluates sits at points of the domain.
-/

@[expose] public section

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L₁ L₂ : Language.{0, 0}}

/-! ### Reading a pulled assignment back on the definable domain -/

section ReadBack

variable {Tag : Type} [Finite Tag] {dm : ℕ} {B : SOBlock} {A : Type} [L₁.Structure A]

/-- Reading an assignment of the pulled block back as an assignment of the
original block on the definable domain: a tuple of domain points is packed
into its tags and its coordinates. Off-domain tuples are simply not looked
at. -/
def SOBlock.readAssignRel (B : SOBlock) (I : RelFOInterpretation L₁ L₂ Tag dm)
    (σ : (B.pull Tag dm).Assignment A) : B.Assignment (I.MapRel A) :=
  fun i y => σ ⟨i, fun k => (y k).1.1⟩
    fun m => (y (finProdFinEquiv.symm m).1).1.2 (finProdFinEquiv.symm m).2

/-- The read-back of a pulled assignment at a tuple whose components are
known. -/
theorem SOBlock.readAssignRel_iff (B : SOBlock) (I : RelFOInterpretation L₁ L₂ Tag dm)
    (σ : (B.pull Tag dm).Assignment A) {i : B.ι} (y : Fin (B.arity i) → I.MapRel A) :
    B.readAssignRel I σ i y ↔
      σ ⟨i, fun k => (y k).1.1⟩ fun m =>
        (y (finProdFinEquiv.symm m).1).1.2 (finProdFinEquiv.symm m).2 :=
  Iff.rfl

/-- **The transfer of assignments is a retraction**: reading a transferred
assignment back on the domain returns it unchanged. (The other composite is
*not* the identity – a guessed pulled assignment may hold of tuples that are
not points of the domain.) -/
theorem SOBlock.readAssignRel_pullAssignRel (B : SOBlock)
    (I : RelFOInterpretation L₁ L₂ Tag dm) (ρ : B.Assignment (I.MapRel A)) :
    B.readAssignRel I (B.pullAssignRel I ρ) = ρ := by
  funext i y
  refine propext ?_
  have hcoord : ∀ (k : Fin (B.arity i)) (j : Fin dm),
      (y (finProdFinEquiv.symm (finProdFinEquiv (k, j))).1).1.2
          (finProdFinEquiv.symm (finProdFinEquiv (k, j))).2 = (y k).1.2 j :=
    fun k j => congrArg (fun z : Fin (B.arity i) × Fin dm => (y z.1).1.2 z.2)
      (Equiv.symm_apply_apply finProdFinEquiv (k, j))
  have hy : ∀ k, (y k).1 = ((y k).1.1,
      fun j => (y (finProdFinEquiv.symm (finProdFinEquiv (k, j))).1).1.2
        (finProdFinEquiv.symm (finProdFinEquiv (k, j))).2) :=
    fun k => congrArg (Prod.mk (y k).1.1) (funext fun j => (hcoord k j).symm)
  exact B.pullAssignRel_iff I ρ y hy

end ReadBack

/-! ### The extended interpretation, at an arbitrary pulled assignment -/

section ExtendAny

variable {Tag : Type} [Finite Tag] {dm : ℕ} [L₂.IsRelational]

/-- Interpreting through the extension of a relativized interpretation along a
block, at an **arbitrary** assignment of the pulled block: the block is read on
the domain through `DescriptiveComplexity.SOBlock.readAssignRel`. This is
`DescriptiveComplexity.RelFOInterpretation.extendSORelEquiv` with the
assumption that the assignment is transferred from the target dropped – which
is what a *guessed* assignment cannot be assumed to be. -/
noncomputable def RelFOInterpretation.extendSORelEquivAny
    (I : RelFOInterpretation L₁ L₂ Tag dm) (B : SOBlock) (A : Type) [L₁.Structure A]
    (σ : (B.pull Tag dm).Assignment A) :
    @Language.Equiv (L₂.sum B.lang)
      (letI := (B.pull Tag dm).structure σ
       (I.extendSORel B).MapRel A)
      (I.MapRel A)
      (letI := (B.pull Tag dm).structure σ
       RelFOInterpretation.mapRelStructure (I.extendSORel B) A)
      (@sumStructure L₂ B.lang (I.MapRel A) (RelFOInterpretation.mapRelStructure I A)
        (B.structure (B.readAssignRel I σ))) :=
  letI := (B.pull Tag dm).structure σ
  letI := B.structure (B.readAssignRel I σ)
  { toEquiv := extendSORelPointEquiv I B A σ
    map_fun' := fun f => isEmptyElim f
    map_rel' := fun {n} R x => by
      cases R with
      | inl r =>
        exact (LHom.realize_onFormula LHom.sumInl
          (I.relFormula r fun i => (x i).1.1)).symm
      | inr r => exact Iff.rfl }

end ExtendAny

/-! ### Pulling back an alternating second-order sentence -/

section PullRelSO

variable {Tag : Type} {dm : ℕ} [Finite Tag]

/-- The pullback of a sentence over the block expansion of the target
language, through a relativized interpretation: pull each block, then pull the
first-order kernel through the (iteratively extended) interpretation, with the
guarded pullback the definable domain requires. -/
noncomputable def pullRelSO :
    ∀ (Bs : List SOBlock) (L₁ L₂ : Language.{0, 0}) [L₂.IsRelational]
      (_I : RelFOInterpretation L₁ L₂ Tag dm),
      (soLang L₂ Bs).Sentence → (soLang L₁ (pullBlocks Tag dm Bs)).Sentence
  | [], _, _, _, I, φ => I.pullRelSentence φ
  | B :: Bs, L₁, L₂, _, I, φ =>
      pullRelSO Bs (L₁.sum (B.pull Tag dm).lang) (L₂.sum B.lang) (I.extendSORel B) φ

private theorem sorealize_pullRelSO_aux :
    ∀ (Bs : List SOBlock) (L₁ L₂ : Language.{0, 0}) (instRel : L₂.IsRelational)
      (I : RelFOInterpretation L₁ L₂ Tag dm) (A : Type) (instA : L₁.Structure A)
      (φ : (soLang L₂ Bs).Sentence) (pol : Bool),
      @SORealize L₂ (I.MapRel A)
          (@RelFOInterpretation.mapRelStructure L₁ L₂ Tag dm I A instA instRel) Bs φ pol ↔
        @SORealize L₁ A instA (pullBlocks Tag dm Bs)
          (@pullRelSO Tag dm _ Bs L₁ L₂ instRel I φ) pol := by
  intro Bs
  induction Bs with
  | nil =>
    intro L₁ L₂ instRel I A instA φ pol
    exact (I.realize_pullRelSentence φ A).symm
  | cons B Bs ih =>
    intro L₁ L₂ instRel I A instA φ pol
    let := instA
    have key : ∀ σ : (B.pull Tag dm).Assignment A,
        (@SORealize (L₂.sum B.lang) (I.MapRel A)
            (@sumStructure L₂ B.lang (I.MapRel A)
              (RelFOInterpretation.mapRelStructure I A)
              (B.structure (B.readAssignRel I σ))) Bs φ (!pol) ↔
          @SORealize (L₁.sum (B.pull Tag dm).lang) A
            (@sumStructure L₁ (B.pull Tag dm).lang A instA ((B.pull Tag dm).structure σ))
            (pullBlocks Tag dm Bs)
            (@pullRelSO Tag dm _ Bs (L₁.sum (B.pull Tag dm).lang) (L₂.sum B.lang) _
              (I.extendSORel B) φ) (!pol)) := by
      intro σ
      let := (B.pull Tag dm).structure σ
      refine Iff.trans (Iff.symm (@sorealize_iso (L₂.sum B.lang)
        ((I.extendSORel B).MapRel A) (I.MapRel A)
        (RelFOInterpretation.mapRelStructure (I.extendSORel B) A)
        (@sumStructure L₂ B.lang (I.MapRel A)
          (RelFOInterpretation.mapRelStructure I A)
          (B.structure (B.readAssignRel I σ)))
        (I.extendSORelEquivAny B A σ) Bs φ (!pol))) ?_
      exact ih (L₁.sum (B.pull Tag dm).lang) (L₂.sum B.lang) inferInstance
        (I.extendSORel B) A
        (@sumStructure L₁ (B.pull Tag dm).lang A instA ((B.pull Tag dm).structure σ))
        φ (!pol)
    cases pol with
    | true =>
      change (∃ ρ : B.Assignment (I.MapRel A),
          @SORealize (L₂.sum B.lang) (I.MapRel A)
            (@sumStructure L₂ B.lang (I.MapRel A)
              (RelFOInterpretation.mapRelStructure I A) (B.structure ρ)) Bs φ false) ↔
        ∃ σ : (B.pull Tag dm).Assignment A,
          @SORealize (L₁.sum (B.pull Tag dm).lang) A
            (@sumStructure L₁ (B.pull Tag dm).lang A instA ((B.pull Tag dm).structure σ))
            (pullBlocks Tag dm Bs)
            (@pullRelSO Tag dm _ Bs (L₁.sum (B.pull Tag dm).lang) (L₂.sum B.lang) _
              (I.extendSORel B) φ) false
      constructor
      · rintro ⟨ρ, h⟩
        refine ⟨B.pullAssignRel I ρ, (key (B.pullAssignRel I ρ)).mp ?_⟩
        rwa [B.readAssignRel_pullAssignRel I ρ]
      · rintro ⟨σ, h⟩
        exact ⟨B.readAssignRel I σ, (key σ).mpr h⟩
    | false =>
      change (∀ ρ : B.Assignment (I.MapRel A),
          @SORealize (L₂.sum B.lang) (I.MapRel A)
            (@sumStructure L₂ B.lang (I.MapRel A)
              (RelFOInterpretation.mapRelStructure I A) (B.structure ρ)) Bs φ true) ↔
        ∀ σ : (B.pull Tag dm).Assignment A,
          @SORealize (L₁.sum (B.pull Tag dm).lang) A
            (@sumStructure L₁ (B.pull Tag dm).lang A instA ((B.pull Tag dm).structure σ))
            (pullBlocks Tag dm Bs)
            (@pullRelSO Tag dm _ Bs (L₁.sum (B.pull Tag dm).lang) (L₂.sum B.lang) _
              (I.extendSORel B) φ) true
      constructor
      · intro h σ
        exact (key σ).mp (h (B.readAssignRel I σ))
      · intro h ρ
        have hσ := (key (B.pullAssignRel I ρ)).mpr (h (B.pullAssignRel I ρ))
        rwa [B.readAssignRel_pullAssignRel I ρ] at hσ

/-- **Pulling second-order satisfaction back through a relativized
interpretation**: alternating second-order satisfaction in the interpreted
structure – whose universe is the definable domain – coincides with
satisfaction of the pulled sentence, over the pulled blocks, in the base
structure. -/
theorem sorealize_pullRelSO [instRel : L₂.IsRelational]
    (I : RelFOInterpretation L₁ L₂ Tag dm) (A : Type) [L₁.Structure A]
    (Bs : List SOBlock) (φ : (soLang L₂ Bs).Sentence) (pol : Bool) :
    SORealize L₂ (I.MapRel A) Bs φ pol ↔
      SORealize L₁ A (pullBlocks Tag dm Bs) (pullRelSO Bs L₁ L₂ I φ) pol :=
  sorealize_pullRelSO_aux Bs L₁ L₂ instRel I A _ φ pol

end PullRelSO

/-! ### Closure of the hierarchy under relativized ordered reductions -/

section Closure

variable [L₁.IsRelational] [L₂.IsRelational] {P : DecisionProblem L₁} {Q : DecisionProblem L₂}
variable {k : ℕ}

/-- **`Σₖ₊₁`-definability is closed under relativized ordered reductions.**
The blocks pull back with the retraction of assignments above, and the order of
the source is re-quantified inside the first block
(`DescriptiveComplexity.sigmaSODefinable_of_orderPull`), exactly as for
non-relativized ordered reductions. -/
theorem SigmaSODefinable.of_relOrderedReduction (f : P ≤ʳᶠᵒ[≤] Q)
    (h : SigmaSODefinable (k + 1) Q) : SigmaSODefinable (k + 1) P := by
  obtain ⟨Bs, hk, φ, hφ⟩ := h
  let := f.tagFinite
  refine sigmaSODefinable_of_orderPull (pullBlocks f.Tag f.dim Bs)
    (by simpa [pullBlocks] using hk) (pullRelSO Bs (L₁.sum Language.order) L₂
      f.toRelInterpretation φ) ?_
  intro A _ _ _
  have key : ∀ lo : LinearOrder A,
      (letI := lo
       P A ↔ SORealize (L₁.sum Language.order) A (pullBlocks f.Tag f.dim Bs)
        (pullRelSO Bs (L₁.sum Language.order) L₂ f.toRelInterpretation φ) true) := by
    intro lo
    let := lo
    have : Finite (f.toRelInterpretation.MapRel A) := f.toRelInterpretation.mapRel_finite A
    have : Nonempty (f.toRelInterpretation.MapRel A) := f.mapRel_nonempty A
    exact (f.correct A).trans ((hφ (f.toRelInterpretation.MapRel A)).trans
      (sorealize_pullRelSO f.toRelInterpretation A Bs φ true))
  exact ⟨fun hP => ⟨finiteLinearOrder A, (key _).mp hP⟩, fun ⟨lo, h⟩ => (key lo).mpr h⟩

/-- **`Πₖ₊₁`-definability is closed under relativized ordered reductions.** -/
theorem PiSODefinable.of_relOrderedReduction (f : P ≤ʳᶠᵒ[≤] Q)
    (h : PiSODefinable (k + 1) Q) : PiSODefinable (k + 1) P := by
  obtain ⟨Bs, hk, φ, hφ⟩ := h
  let := f.tagFinite
  refine piSODefinable_of_orderPull (pullBlocks f.Tag f.dim Bs)
    (by simpa [pullBlocks] using hk) (pullRelSO Bs (L₁.sum Language.order) L₂
      f.toRelInterpretation φ) ?_
  intro A _ _ _
  have key : ∀ lo : LinearOrder A,
      (letI := lo
       P A ↔ SORealize (L₁.sum Language.order) A (pullBlocks f.Tag f.dim Bs)
        (pullRelSO Bs (L₁.sum Language.order) L₂ f.toRelInterpretation φ) false) := by
    intro lo
    let := lo
    have : Finite (f.toRelInterpretation.MapRel A) := f.toRelInterpretation.mapRel_finite A
    have : Nonempty (f.toRelInterpretation.MapRel A) := f.mapRel_nonempty A
    exact (f.correct A).trans ((hφ (f.toRelInterpretation.MapRel A)).trans
      (sorealize_pullRelSO f.toRelInterpretation A Bs φ false))
  exact ⟨fun hP lo => (key lo).mp hP, fun h => (key (finiteLinearOrder A)).mpr (h _)⟩

end Closure

end DescriptiveComplexity
