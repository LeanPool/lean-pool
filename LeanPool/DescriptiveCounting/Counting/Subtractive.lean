/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
module

public import LeanPool.DescriptiveCounting.Counting.RelClosure
import all LeanPool.DescriptiveCounting.Counting.SharpP
import all LeanPool.DescriptiveCounting.SecondOrderPull

/-!
# Subtractive reductions

The reductions of [Durand, Hermann, Kolaitis 2005][durand2005subtractive],
which sit between the parsimonious reductions and the one-call reductions of
`DescriptiveComplexity.Counting.Reduction`, and under which `#P` is closed.

A **strong subtractive reduction** from `C` to `D`
(`DescriptiveComplexity.StrongSubtractiveReduction`) draws two instances of
`D`, the *subtrahend* and the *minuend*, such that the solutions of the first
are among those of the second and

`C A = D (minuend A) - D (subtrahend A)`.

The condition on solutions is what keeps the difference inside `#P`, and it is
about solutions, not counts. So `D` comes with a *presentation*: a second-order
block and a first-order kernel whose witnesses it counts
(`DescriptiveComplexity.StrongSubtractiveReduction.present`), which plays the
part of the relation `B` in the paper's `#·B`. The two interpretations share
their tags and their dimension, so the two instances have the same universe,
ordered the same way, and a witness of one can be compared with a witness of
the other (`DescriptiveComplexity.FOInterpretation.WitAt`).

Strong subtractive reductions do not compose, and a **subtractive reduction**
`C ≤ˢ D` (`DescriptiveComplexity.SubtractiveReducible`) is a finite chain of
steps, as in the paper. Two departures from it, both forced:

* a step is a strong subtractive reduction *or a parsimonious reduction*, in
  its most general form, relativized and ordered. The paper obtains the second
  as the special case of the first whose subtrahend has no solution, which
  needs the target to have such an instance, definably; admitting the step
  directly asks for nothing;
* the target of a strong step is presented by a first-order kernel, hence is
  itself in `#P`. The paper's relations are arbitrary, which is what lets it
  speak of the classes above `#P`; the library has no such classes yet.

`#P` is closed under subtractive reductions
(`DescriptiveComplexity.SharpPDefinable.of_subtractive`, Theorem 3.3 of the
paper): the witnesses of the minuend that are not witnesses of the subtrahend
are the witnesses of one kernel, the conjunction of the pulled kernel of the
first with the negated pulled kernel of the second. So this is the widest
notion of the library under which the class is closed, and the plain words go
to it, as on the decision side they go to reductions the classes are closed
under: `DescriptiveComplexity.CountingClass.Hard` and
`DescriptiveComplexity.CountingClass.Complete` are hardness and completeness
under subtractive reductions. Parsimonious hardness and completeness imply
them (`DescriptiveComplexity.hard_sharpP_of_parsimoniousHard`,
`DescriptiveComplexity.complete_sharpP_of_parsimoniousComplete`).
-/

@[expose] public section

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L L' : Language.{0, 0}}

/-! ### Witnesses at an interpreted instance -/

section WitAt

variable [L'.IsRelational] {Tag : Type} [LinearOrder Tag] {dim : ℕ}

/-- The assignment `ρ` is a witness of the kernel `φ` at the instance drawn by
the interpretation `I`, ordered lexicographically. The universe of that
instance is `Tag × A ^ dim` whatever `I` is, so the witnesses at two
interpretations with the same tags and dimension are comparable. -/
def FOInterpretation.WitAt (I : FOInterpretation (L.sum Language.order) L' Tag dim)
    (B : SOBlock) (φ : ((L'.sum Language.order).sum B.lang).Sentence) (A : Type)
    [L.Structure A] [LinearOrder A] (ρ : B.Assignment (Tag × (Fin dim → A))) : Prop :=
  @Sentence.Realize ((L'.sum Language.order).sum B.lang) (I.ordExtend.Map A)
    (@sumStructure (L'.sum Language.order) B.lang (I.ordExtend.Map A)
      (FOInterpretation.mapStructure I.ordExtend A) (B.structure ρ)) φ

variable [Finite Tag] (I : FOInterpretation (L.sum Language.order) L' Tag dim)
  (B : SOBlock) (φ : ((L'.sum Language.order).sum B.lang).Sentence)
  (A : Type) [L.Structure A] [LinearOrder A]

/-- A witness at an interpreted instance is a witness of the pulled kernel, at
the pulled assignment. -/
theorem FOInterpretation.witAt_iff_pull (ρ : B.Assignment (Tag × (Fin dim → A))) :
    I.WitAt B φ A ρ ↔
      @Sentence.Realize ((L.sum Language.order).sum (B.pull Tag dim).lang) A
        (@sumStructure (L.sum Language.order) (B.pull Tag dim).lang A _
          ((B.pull Tag dim).structure (B.pullAssign ρ)))
        ((I.ordExtend.extendSO B).pullSentence φ) := by
  let := (B.pull Tag dim).structure (B.pullAssign ρ)
  exact (@StrongHomClass.realize_sentence ((L'.sum Language.order).sum B.lang)
      ((I.ordExtend.extendSO B).Map A) (I.ordExtend.Map A)
      (FOInterpretation.mapStructure (I.ordExtend.extendSO B) A)
      (@sumStructure (L'.sum Language.order) B.lang (I.ordExtend.Map A)
        (I.ordExtend.mapStructure A) (B.structure ρ)) _ _ _
      (I.ordExtend.extendSOEquiv B A ρ) φ).symm.trans
    ((I.ordExtend.extendSO B).realize_pullSentence φ A).symm

omit [Finite Tag] in
/-- The witness count of the kernel at the interpreted instance, ordered
lexicographically, is the number of witnesses there. -/
theorem FOInterpretation.witnessCount_map_eq_card :
    @witnessCount (L'.sum Language.order) B φ (I.Map A)
        (letI := I.mapLinearOrder A; sumOrderStructure L' (I.Map A)) =
      Nat.card {ρ : B.Assignment (Tag × (Fin dim → A)) // I.WitAt B φ A ρ} := by
  let := I.mapLinearOrder A
  exact (witnessCount_iso B φ (I.ordExtendLEquiv A)).symm

omit [Finite Tag] in
/-- A witness of an order-free kernel at an interpreted instance: the order of
the instance plays no part. -/
private theorem FOInterpretation.witAt_orderFreeKernel (ψ : (L'.sum B.lang).Sentence)
    (ρ : B.Assignment (Tag × (Fin dim → A))) :
    I.WitAt B (orderFreeKernel B ψ) A ρ ↔
      @Sentence.Realize (L'.sum B.lang) (I.Map A)
        (@sumStructure L' B.lang (I.Map A) (I.mapStructure A) (B.structure ρ)) ψ := by
  let s₁ : (L'.sum B.lang).Structure (I.ordExtend.Map A) :=
    @sumStructure L' B.lang (I.Map A) (I.mapStructure A) (B.structure ρ)
  let s₂ : ((L'.sum Language.order).sum B.lang).Structure (I.ordExtend.Map A) :=
    @sumStructure (L'.sum Language.order) B.lang (I.ordExtend.Map A)
      (FOInterpretation.mapStructure I.ordExtend A) (B.structure ρ)
  have : @LHom.IsExpansionOn _ _ (LHom.sumMap (LHom.sumInl : L' →ᴸ L'.sum Language.order)
      (LHom.id B.lang)) (I.ordExtend.Map A) s₁ s₂ :=
    @LHom.IsExpansionOn.mk _ _ _ _ s₁ s₂ (fun f _ => isEmptyElim f)
      (fun r _ => by cases r <;> rfl)
  exact @LHom.realize_onSentence _ _ (I.ordExtend.Map A) s₁ s₂
    (LHom.sumMap (LHom.sumInl : L' →ᴸ L'.sum Language.order) (LHom.id B.lang)) this ψ

end WitAt

/-- The witness count of an order-free kernel, lifted to the ordered expansion,
is its witness count. -/
private theorem witnessCount_orderFreeKernel (B : SOBlock) (φ : (L.sum B.lang).Sentence) (A : Type)
    [L.Structure A] [LinearOrder A] :
    witnessCount B (orderFreeKernel B φ) A = witnessCount B φ A := by
  refine Nat.card_congr (Equiv.subtypeEquiv (Equiv.refl _) fun ρ => ?_)
  let := B.structure ρ
  have : (LHom.sumMap (LHom.sumInl : L →ᴸ L.sum Language.order)
      (LHom.id B.lang)).IsExpansionOn A :=
    ⟨fun f _ => by cases f <;> rfl, fun r _ => by cases r <;> rfl⟩
  exact LHom.realize_onSentence A (LHom.sumMap (LHom.sumInl : L →ᴸ L.sum Language.order)
    (LHom.id B.lang)) φ

/-! ### Strong subtractive reductions -/

/-- A **strong subtractive reduction**: the target is presented as the witness
count of a kernel, two interpretations with the same tags and dimension draw a
subtrahend and a minuend, every witness at the first is a witness at the
second, and the count of the source is the difference of the two counts. -/
structure StrongSubtractiveReduction [L.IsRelational] [L'.IsRelational]
    (C : CountingProblem L) (D : CountingProblem L') where
  /-- The tags used by the two interpretations. -/
  Tag : Type
  /-- Tags are finite, so that finite structures map to finite structures. -/
  [tagFinite : Finite Tag]
  /-- Tags are nonempty, so that nonempty structures map to nonempty ones. -/
  [tagNonempty : Nonempty Tag]
  /-- Tags are linearly ordered: the order of the drawn instances is the
  lexicographic one. -/
  [tagOrder : LinearOrder Tag]
  /-- The dimension of the two interpretations. -/
  dim : ℕ
  /-- The second-order block of the presentation of the target. -/
  block : SOBlock
  /-- The first-order kernel of the presentation of the target. -/
  kernel : ((L'.sum Language.order).sum block.lang).Sentence
  /-- The target counts the witnesses of its presentation, whatever the linear
  order. -/
  present : ∀ (A : Type) [L'.Structure A] [LinearOrder A] [Finite A] [Nonempty A],
    D A = witnessCount block kernel A
  /-- The interpretation drawing the subtrahend. -/
  subtrahend : FOInterpretation (L.sum Language.order) L' Tag dim
  /-- The interpretation drawing the minuend. -/
  minuend : FOInterpretation (L.sum Language.order) L' Tag dim
  /-- Every witness at the subtrahend is a witness at the minuend. -/
  witness_le : ∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A]
    (ρ : block.Assignment (Tag × (Fin dim → A))),
    subtrahend.WitAt block kernel A ρ → minuend.WitAt block kernel A ρ
  /-- The count of the source and the count at the subtrahend add up to the
  count at the minuend. -/
  correct : ∀ (A : Type) [L.Structure A] [LinearOrder A] [Finite A] [Nonempty A],
    C A + D (subtrahend.Map A) = D (minuend.Map A)

section Closure

variable [L.IsRelational] [L'.IsRelational] {C : CountingProblem L} {D : CountingProblem L'}

/-- With the witnesses of one predicate among those of another, the witnesses
of the second that are not witnesses of the first make up the difference. -/
private theorem card_diff_add_card {α : Type} [Finite α] {P Q : α → Prop} (h : ∀ a, P a → Q a) :
    Nat.card {a // Q a ∧ ¬P a} + Nat.card {a // P a} = Nat.card {a // Q a} := by
  classical
  have e : {a // Q a ∧ ¬P a} ⊕ {a // P a} ≃ {a // Q a} :=
    { toFun := Sum.elim (fun a => ⟨a.1, a.2.1⟩) fun a => ⟨a.1, h a.1 a.2⟩
      invFun := fun a => if hP : P a.1 then Sum.inr ⟨a.1, hP⟩ else Sum.inl ⟨a.1, a.2, hP⟩
      left_inv := by
        rintro (⟨a, h1, h2⟩ | ⟨a, h1⟩)
        · simp [h2]
        · simp [h1]
      right_inv := fun a => by
        by_cases hP : P a.1 <;> simp [hP] }
  rw [← Nat.card_sum, Nat.card_congr e]

/-- **The source of a strong subtractive reduction is in `#P`**: it counts the
witnesses at the minuend that are not witnesses at the subtrahend, and those
are the witnesses of one kernel. -/
theorem SharpPDefinable.of_strongSubtractive (f : StrongSubtractiveReduction C D) :
    SharpPDefinable C := by
  let := f.tagFinite
  let := f.tagNonempty
  let := f.tagOrder
  refine ⟨f.block.pull f.Tag f.dim,
    (f.minuend.ordExtend.extendSO f.block).pullSentence f.kernel ⊓
      ∼((f.subtrahend.ordExtend.extendSO f.block).pullSentence f.kernel), ?_⟩
  intro A _ _ _ _
  have cnt : ∀ I : FOInterpretation (L.sum Language.order) L' f.Tag f.dim,
      D (I.Map A) = Nat.card {ρ : f.block.Assignment (f.Tag × (Fin f.dim → A)) //
        I.WitAt f.block f.kernel A ρ} := by
    intro I
    let := I.mapLinearOrder A
    have : Finite (I.Map A) := I.map_finite A
    have : Nonempty (I.Map A) := I.map_nonempty A
    rw [f.present (I.Map A)]
    exact I.witnessCount_map_eq_card f.block f.kernel A
  have hc := f.correct A
  rw [cnt f.subtrahend, cnt f.minuend, ← card_diff_add_card (f.witness_le A)] at hc
  rw [Nat.add_right_cancel hc]
  refine Nat.card_congr (Equiv.subtypeEquiv (f.block.pullAssignEquiv f.Tag f.dim A) fun ρ => ?_)
  have h1 := f.minuend.witAt_iff_pull f.block f.kernel A ρ
  have h2 := f.subtrahend.witAt_iff_pull f.block f.kernel A ρ
  let := (f.block.pull f.Tag f.dim).structure (f.block.pullAssign ρ)
  rw [Sentence.Realize, Formula.realize_inf, Formula.realize_not]
  exact and_congr h1 (not_congr h2)

end Closure

/-! ### Subtractive reductions -/

/-- **Subtractive reducibility**, `C ≤ˢ D`: a finite chain of steps, each a
strong subtractive reduction or a relativized ordered parsimonious
reduction. -/
inductive SubtractiveReducible : ∀ {L L' : Language.{0, 0}} [L.IsRelational] [L'.IsRelational],
    CountingProblem L → CountingProblem L' → Prop
  /-- The empty chain. -/
  | refl {L : Language.{0, 0}} [L.IsRelational] (C : CountingProblem L) :
      SubtractiveReducible C C
  /-- A strong subtractive step, then a chain. -/
  | strong {L₁ L₂ L₃ : Language.{0, 0}} [L₁.IsRelational] [L₂.IsRelational]
      [L₃.IsRelational] {C : CountingProblem L₁} {D : CountingProblem L₂}
      {E : CountingProblem L₃} (f : StrongSubtractiveReduction C D)
      (h : SubtractiveReducible D E) : SubtractiveReducible C E
  /-- A parsimonious step, then a chain. -/
  | parsimonious {L₁ L₂ L₃ : Language.{0, 0}} [L₁.IsRelational] [L₂.IsRelational]
      [L₃.IsRelational] {C : CountingProblem L₁} {D : CountingProblem L₂}
      {E : CountingProblem L₃} (f : C ≤ʳᵖ[≤] D)
      (h : SubtractiveReducible D E) : SubtractiveReducible C E

@[inherit_doc]
scoped notation:50 C:51 " ≤ˢ " D:51 => SubtractiveReducible C D

section Reducible

variable {L₁ L₂ L₃ : Language.{0, 0}} [L₁.IsRelational] [L₂.IsRelational] [L₃.IsRelational]
variable {C : CountingProblem L₁} {D : CountingProblem L₂} {E : CountingProblem L₃}

/-- A strong subtractive reduction is a subtractive reduction. -/
theorem StrongSubtractiveReduction.subtractiveReducible
    (f : StrongSubtractiveReduction C D) :
    C ≤ˢ D :=
  .strong f (.refl D)

/-- A relativized parsimonious reduction is a subtractive reduction. -/
theorem RelOrderedParsimoniousReduction.subtractiveReducible (f : C ≤ʳᵖ[≤] D) : C ≤ˢ D :=
  .parsimonious f (.refl D)

/-- An ordered parsimonious reduction is a subtractive reduction. -/
private theorem OrderedParsimoniousReduction.subtractiveReducible (f : C ≤ᵖ[≤] D) : C ≤ˢ D :=
  f.toRel.subtractiveReducible

/-- A parsimonious reduction is a subtractive reduction. -/
private theorem ParsimoniousReduction.subtractiveReducible (f : C ≤ᵖ D) : C ≤ˢ D :=
  f.toOrdered.subtractiveReducible

/-- **Subtractive reducibility is transitive** (Proposition 3.2 of the paper):
chains concatenate. -/
theorem SubtractiveReducible.trans (h₁ : C ≤ˢ D) (h₂ : D ≤ˢ E) : C ≤ˢ E := by
  induction h₁ with
  | refl _ => exact h₂
  | strong f _ ih => exact .strong f (ih h₂)
  | parsimonious f _ ih => exact .parsimonious f (ih h₂)

/-- **`#P` is closed under subtractive reductions** (Theorem 3.3 of
[Durand, Hermann, Kolaitis 2005][durand2005subtractive]). -/
theorem SharpPDefinable.of_subtractive (h : C ≤ˢ D) (hD : SharpPDefinable D) :
    SharpPDefinable C := by
  induction h with
  | refl _ => exact hD
  | strong f _ _ => exact .of_strongSubtractive f
  | parsimonious f _ ih => exact (ih hD).of_relOrderedParsimonious f

end Reducible

/-! ### Hardness and completeness -/

namespace CountingClass

variable (K : CountingClass) {L L' : Language.{0, 0}} [L.IsRelational] [L'.IsRelational]

/-- A counting problem is **hard** for a class when every problem of the class
reduces to it by a subtractive reduction. -/
def Hard (C : CountingProblem L) : Prop :=
  ∀ {L'' : Language.{0, 0}} [L''.IsRelational] (D : CountingProblem L''), D ∈ K → D ≤ˢ C

/-- A counting problem is **complete** for a class when it belongs to it and
is hard for it, under subtractive reductions. -/
def Complete (C : CountingProblem L) : Prop :=
  C ∈ K ∧ K.Hard C

variable {K}

theorem Complete.mem {C : CountingProblem L} (h : K.Complete C) : C ∈ K := h.1

theorem Complete.hard {C : CountingProblem L} (h : K.Complete C) : K.Hard C := h.2

/-- Hardness travels forward along subtractive reductions. -/
theorem Hard.of_subtractive {C : CountingProblem L} {D : CountingProblem L'}
    (f : C ≤ˢ D) (hC : K.Hard C) : K.Hard D :=
  fun E hE => (hC E hE).trans f

end CountingClass

/-- **Membership in `#P` travels backward along subtractive reductions.** -/
theorem mem_sharpP_of_subtractive [L.IsRelational] [L'.IsRelational] {C : CountingProblem L}
    {D : CountingProblem L'} (h : C ≤ˢ D) (hD : D ∈ SharpP) : C ∈ SharpP :=
  SharpPDefinable.of_subtractive h hD

/-- **Parsimonious `#P`-hardness implies `#P`-hardness**: a relativized
parsimonious reduction is a subtractive reduction. -/
theorem hard_sharpP_of_parsimoniousHard [L.IsRelational] {C : CountingProblem L}
    (h : SharpP.ParsimoniousHard C) : SharpP.Hard C :=
  fun D hD => (h D hD).some.subtractiveReducible

/-- A parsimoniously `#P`-complete problem is `#P`-complete. -/
theorem complete_sharpP_of_parsimoniousComplete [L.IsRelational] {C : CountingProblem L}
    (h : SharpP.ParsimoniousComplete C) : SharpP.Complete C :=
  ⟨h.1, hard_sharpP_of_parsimoniousHard h.2⟩

end DescriptiveComplexity
