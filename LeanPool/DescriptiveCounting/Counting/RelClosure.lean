/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
module

public import LeanPool.DescriptiveCounting.Counting.Class
public import LeanPool.DescriptiveCounting.SecondOrderRelPull
import all LeanPool.DescriptiveCounting.SecondOrderNewPull
import all LeanPool.DescriptiveCounting.SecondOrderRelPull

/-!
# `#P` is closed under relativized parsimonious reductions

Membership in `#P` travels backward along the relativized reductions
`C ≤ʳᵖ[≤] D`, those whose target universe is a definable set of tagged tuples
(`DescriptiveComplexity.SharpPDefinable.of_relOrderedParsimonious`). With the
hardness half, which holds by definition, this makes the relativized
reductions reductions of the class in the full sense.

## From a retraction to a bijection

`DescriptiveComplexity.SecondOrderRelPull` pulls a second-order sentence back
through a relativized interpretation, and observes that the transfer of
assignments is only a retraction: a relation variable of the pulled block
ranges over *all* tagged tuples, and may hold of tuples that are not points of
the target. That is harmless for deciding, and fatal for counting, every
assignment of the target being counted once per way of filling in the tuples
outside the domain.

The repair is one conjunct in the kernel,
`DescriptiveComplexity.supportSentence`: every pulled relation variable holds
only of tuples all of whose points are in the domain. On such *supported*
assignments the read-back is injective
(`DescriptiveComplexity.SOBlock.pullAssignRel_readAssignRel`), so the witnesses
of the kernel in the target are, bijectively, the supported witnesses of the
pulled kernel in the source (`DescriptiveComplexity.witnessCount_mapRel`).
-/

@[expose] public section

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L₁ L₂ : Language.{0, 0}}

/-! ### Supported assignments -/

section Supported

variable {Tag : Type} [Finite Tag] {dm : ℕ} {A : Type} [L₁.Structure A]

/-- An assignment of the pulled block is **supported** by the domain of a
relativized interpretation when each of its relations holds only of tuples all
of whose points are in the domain. -/
def SOBlock.Supported (B : SOBlock) (J : RelFOInterpretation L₁ L₂ Tag dm)
    (σ : (B.pull Tag dm).Assignment A) : Prop :=
  ∀ (p : Σ i : B.ι, Fin (B.arity i) → Tag) (x : Fin (B.arity p.1 * dm) → A), σ p x →
    ∀ k : Fin (B.arity p.1), (J.domFormula (p.2 k)).Realize fun j => x (finProdFinEquiv (k, j))

/-- A transferred assignment is supported. -/
theorem SOBlock.supported_pullAssignRel (B : SOBlock) (J : RelFOInterpretation L₁ L₂ Tag dm)
    (ρ : B.Assignment (J.MapRel A)) : B.Supported J (B.pullAssignRel J ρ) :=
  fun _ _ h k => h.1 k

/-- **On supported assignments the read-back is injective**: transferring the
read-back of a supported assignment returns it. -/
theorem SOBlock.pullAssignRel_readAssignRel (B : SOBlock)
    (J : RelFOInterpretation L₁ L₂ Tag dm) {σ : (B.pull Tag dm).Assignment A}
    (hσ : B.Supported J σ) : B.pullAssignRel J (B.readAssignRel J σ) = σ := by
  funext p x
  obtain ⟨i, τ⟩ := p
  have hx : (fun m : Fin (B.arity i * dm) =>
      x (finProdFinEquiv ((finProdFinEquiv.symm m).1, (finProdFinEquiv.symm m).2))) = x :=
    funext fun m => congrArg x (finProdFinEquiv.apply_symm_apply m)
  refine propext ⟨?_, fun h => ⟨hσ ⟨i, τ⟩ x h, ?_⟩⟩
  · rintro ⟨_, h⟩
    have h' : σ ⟨i, τ⟩ fun m : Fin (B.arity i * dm) =>
        x (finProdFinEquiv ((finProdFinEquiv.symm m).1, (finProdFinEquiv.symm m).2)) := h
    rwa [hx] at h'
  · change σ ⟨i, τ⟩ fun m : Fin (B.arity i * dm) =>
      x (finProdFinEquiv ((finProdFinEquiv.symm m).1, (finProdFinEquiv.symm m).2))
    rw [hx]
    exact h

/-- Realization of a finite conjunction of formulas. -/
private theorem realize_iInf' {L : Language.{0, 0}} {M : Type} [L.Structure M] {α β : Type}
    [Finite β] (f : β → L.Formula α) (v : α → M) :
    (Formula.iInf f).Realize v ↔ ∀ b, (f b).Realize v :=
  BoundedFormula.realize_iInf

/-- The sentence saying that the assignment of the pulled block is supported:
for each relation variable, at each tuple it holds of, every point of the tuple
satisfies the domain formula of its tag. -/
noncomputable def supportSentence (J : RelFOInterpretation L₁ L₂ Tag dm) (B : SOBlock) :
    (L₁.sum (B.pull Tag dm).lang).Sentence :=
  Formula.iInf fun p : Σ i : B.ι, Fin (B.arity i) → Tag =>
    Formula.iAlls (Fin (B.arity p.1 * dm))
      (((Relations.formula
            (Sum.inr ⟨p, rfl⟩ : (L₁.sum (B.pull Tag dm).lang).Relations (B.arity p.1 * dm))
            fun m => Term.var m).imp
          (Formula.iInf fun k : Fin (B.arity p.1) =>
            (LHom.sumInl.onFormula (J.domFormula (p.2 k))).relabel
              fun j => finProdFinEquiv (k, j))).relabel Sum.inr)

private theorem realize_supportSentence (J : RelFOInterpretation L₁ L₂ Tag dm) (B : SOBlock)
    (σ : (B.pull Tag dm).Assignment A) :
    @Sentence.Realize (L₁.sum (B.pull Tag dm).lang) A
        (@sumStructure L₁ (B.pull Tag dm).lang A _ ((B.pull Tag dm).structure σ))
        (supportSentence J B) ↔ B.Supported J σ := by
  let := (B.pull Tag dm).structure σ
  rw [supportSentence, Sentence.Realize, realize_iInf']
  refine forall_congr' fun p => ?_
  rw [Formula.realize_iAlls]
  refine forall_congr' fun x => ?_
  rw [Formula.realize_relabel, Formula.realize_imp, realize_iInf']
  refine imp_congr ?_ (forall_congr' fun k => ?_)
  · exact Formula.realize_rel.trans Iff.rfl
  · exact Formula.realize_relabel.trans ((LHom.realize_onFormula _ _).trans Iff.rfl)

end Supported

/-! ### Witness counts through a relativized interpretation -/

section Count

variable {Tag : Type} [Finite Tag] {dm : ℕ} [L₂.IsRelational]

/-- A pulled kernel holds at an assignment of the pulled block exactly when
the kernel holds, in the interpreted structure, at its read-back. -/
private theorem RelFOInterpretation.realize_pullRelSentence_iff_read
    (J : RelFOInterpretation L₁ L₂ Tag dm) (B : SOBlock) (φ : (L₂.sum B.lang).Sentence)
    (A : Type) [L₁.Structure A] (σ : (B.pull Tag dm).Assignment A) :
    @Sentence.Realize (L₁.sum (B.pull Tag dm).lang) A
        (@sumStructure L₁ (B.pull Tag dm).lang A _ ((B.pull Tag dm).structure σ))
        ((J.extendSORel B).pullRelSentence φ) ↔
      @Sentence.Realize (L₂.sum B.lang) (J.MapRel A)
        (@sumStructure L₂ B.lang (J.MapRel A) (RelFOInterpretation.mapRelStructure J A)
          (B.structure (B.readAssignRel J σ))) φ := by
  let := (B.pull Tag dm).structure σ
  exact ((J.extendSORel B).realize_pullRelSentence φ A).trans
    (@StrongHomClass.realize_sentence (L₂.sum B.lang) ((J.extendSORel B).MapRel A) (J.MapRel A)
      (RelFOInterpretation.mapRelStructure (J.extendSORel B) A)
      (@sumStructure L₂ B.lang (J.MapRel A) (RelFOInterpretation.mapRelStructure J A)
        (B.structure (B.readAssignRel J σ))) _ _ _
      (J.extendSORelEquivAny B A σ) φ)

/-- **Pulling a witness count back through a relativized interpretation**: the
witnesses of a kernel in the definable structure are, bijectively, the
supported witnesses of the pulled kernel in the base structure. -/
theorem witnessCount_mapRel (J : RelFOInterpretation L₁ L₂ Tag dm) (B : SOBlock)
    (φ : (L₂.sum B.lang).Sentence) (A : Type) [L₁.Structure A] :
    witnessCount B φ (J.MapRel A) =
      witnessCount (B.pull Tag dm)
        ((J.extendSORel B).pullRelSentence φ ⊓ supportSentence J B) A := by
  have key : ∀ σ : (B.pull Tag dm).Assignment A,
      @Sentence.Realize (L₁.sum (B.pull Tag dm).lang) A
          (@sumStructure L₁ (B.pull Tag dm).lang A _ ((B.pull Tag dm).structure σ))
          ((J.extendSORel B).pullRelSentence φ ⊓ supportSentence J B) ↔
        @Sentence.Realize (L₂.sum B.lang) (J.MapRel A)
            (@sumStructure L₂ B.lang (J.MapRel A) (RelFOInterpretation.mapRelStructure J A)
              (B.structure (B.readAssignRel J σ))) φ ∧ B.Supported J σ := by
    intro σ
    have h1 := J.realize_pullRelSentence_iff_read B φ A σ
    have h2 := realize_supportSentence J B σ
    let := (B.pull Tag dm).structure σ
    rw [Sentence.Realize, Formula.realize_inf]
    exact and_congr h1 h2
  exact Nat.card_congr
    { toFun := fun ρ => ⟨B.pullAssignRel J ρ.1, (key _).mpr
        ⟨(B.readAssignRel_pullAssignRel J ρ.1).symm ▸ ρ.2, B.supported_pullAssignRel J ρ.1⟩⟩
      invFun := fun σ => ⟨B.readAssignRel J σ.1, ((key σ.1).mp σ.2).1⟩
      left_inv := fun ρ => Subtype.ext (B.readAssignRel_pullAssignRel J ρ.1)
      right_inv := fun σ => Subtype.ext (B.pullAssignRel_readAssignRel J ((key σ.1).mp σ.2).2) }

end Count

/-! ### Closure -/

section Closure

variable {L L' : Language.{0, 0}} [L.IsRelational] [L'.IsRelational]
  {C : CountingProblem L} {D : CountingProblem L'}

/-- **`#P`-definability is closed under relativized ordered parsimonious
reductions.**
Registered in the Lax archive as
[`Lax366625.SharpPClosure.SharpP_mem_of_relOrderedParsimonious`](https://laxarchive.org/lax-366625/Lax366625.SharpPClosure.html#s-Lax366625.SharpPClosure.SharpP_mem_of_relOrderedParsimonious). -/
theorem SharpPDefinable.of_relOrderedParsimonious (f : C ≤ʳᵖ[≤] D) (h : SharpPDefinable D) :
    SharpPDefinable C := by
  obtain ⟨B, φ, hφ⟩ := h
  let := f.tagFinite
  let : LinearOrder f.Tag := finiteLinearOrder f.Tag
  refine ⟨B.pull f.Tag f.dim,
    (f.toRelInterpretation.ordExtendRel.extendSORel B).pullRelSentence φ ⊓
      supportSentence f.toRelInterpretation.ordExtendRel B, ?_⟩
  intro A _ _ _ _
  let := f.toRelInterpretation.mapRelLinearOrder A
  have : Finite (f.toRelInterpretation.MapRel A) := f.toRelInterpretation.mapRel_finite A
  have : Nonempty (f.toRelInterpretation.MapRel A) := f.mapRel_nonempty A
  rw [f.correct A, hφ (f.toRelInterpretation.MapRel A),
    ← witnessCount_mapRel f.toRelInterpretation.ordExtendRel B φ A]
  exact (witnessCount_iso B φ (f.toRelInterpretation.ordExtendRelLEquiv A)).symm

/-- **Membership in `#P` travels backward along relativized ordered
parsimonious reductions.** -/
private theorem mem_sharpP_of_relOrderedParsimonious
    (f : C ≤ʳᵖ[≤] D) (h : D ∈ SharpP) : C ∈ SharpP :=
  SharpPDefinable.of_relOrderedParsimonious f h

end Closure

end DescriptiveComplexity
