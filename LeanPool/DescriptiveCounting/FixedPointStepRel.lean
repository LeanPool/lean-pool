/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
module

public import LeanPool.DescriptiveCounting.FixedPointPartialSpace
public import LeanPool.DescriptiveCounting.SecondOrderNewPull
import all LeanPool.DescriptiveCounting.FixedPointInflationary
import all LeanPool.DescriptiveCounting.FixedPointPartial
import all LeanPool.DescriptiveCounting.FixedPointStep
import all LeanPool.DescriptiveCounting.SecondOrderNewPull

/-!
# Pulling a simultaneous induction through a relativized interpretation

The transport lemmas of `DescriptiveComplexity.FixedPointStep`, redone for
interpretations with a *definable domain*
(`DescriptiveComplexity.RelFOInterpretation`) – and with them, **closure of
membership under relativized ordered reductions** `≤ʳᶠᵒ[≤]`
(`DescriptiveComplexity.IFPDefinable.of_relOrderedReduction`,
`DescriptiveComplexity.PFPDefinable.of_relOrderedReduction`).

Why the fixed-point logics need it when the second-order ones did not: all the
library's hardness travels along relativized reductions (they are what a
*spanning* target problem requires), so bringing a problem of a class *back*
from a complete problem – `PSPACE ⊆ FO(≤, PFP)` via the machine problem in
`DescriptiveComplexity.FixedPointPartialMachine` – crosses a relativized
reduction in the membership direction. For the second-order classes membership
was always a direct sentence, and the crossing never happened.

## The construction

Everything mirrors the plain pullback (`DescriptiveComplexity.StepDef.pull`),
with the domain threaded through:

* the interpretation extends along a block with its domain unchanged
  (`DescriptiveComplexity.RelFOInterpretation.extendSORel`);
* an assignment of the block on the definable universe transfers to an
  assignment of the pulled block that holds *only in-domain* tuples
  (`DescriptiveComplexity.SOBlock.pullAssignRel`) – the transfer is injective
  (`DescriptiveComplexity.SOBlock.pullAssignRel_injective`), which is what
  carries fixed-point-ness back and forth for a *deterministic* iteration,
  where the existential-only transfer of
  `DescriptiveComplexity.SecondOrderNewPull` would not suffice;
* the step formula of a pulled variable is the guarded pullback of the
  original step (`DescriptiveComplexity.guardPullRel`, from
  `DescriptiveComplexity.RelFOInterpretation.pullRel`) *gated by the domain
  formulas of its arguments* (`DescriptiveComplexity.domGateF`), so that
  off-domain tuples are never derived and the stages stay in the image of the
  transfer;
* one application of the pulled step is the transfer of one application of
  the original (`DescriptiveComplexity.StepDef.next_pullRel`), whence the
  stages, limits, and values correspond
  (`DescriptiveComplexity.StepDef.ifpHolds_pullRel`,
  `DescriptiveComplexity.StepDef.pfpHolds_pullRel`).
-/

@[expose] public section

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

open Function (IsFixedPt)

variable {L₁ L₂ : Language.{0, 0}} [L₂.IsRelational] {Tag : Type} [Finite Tag] {dm : ℕ}

/-! ### Extending a relativized interpretation along a block -/

/-- Extension of a relativized interpretation along a second-order quantifier
block: the underlying interpretation extends as
`DescriptiveComplexity.FOInterpretation.extendSO`, and the domain formula is
unchanged (lifted to the expanded source vocabulary, which it does not
use). -/
def RelFOInterpretation.extendSORel (I : RelFOInterpretation L₁ L₂ Tag dm)
    (B : SOBlock) :
    RelFOInterpretation (L₁.sum (B.pull Tag dm).lang) (L₂.sum B.lang) Tag dm where
  toFOInterpretation := I.toFOInterpretation.extendSO B
  domFormula := fun t => LHom.sumInl.onFormula (I.domFormula t)

/-! ### Transferring assignments -/

/-- Transfer of an assignment on the definable universe to an assignment of
the pulled block: a pulled tuple is in the transferred relation when all its
argument points lie in the domain *and* the packed tuple is in the original
relation. Off-domain tuples are never held – which keeps the transfer
injective. -/
def SOBlock.pullAssignRel (B : SOBlock) (I : RelFOInterpretation L₁ L₂ Tag dm)
    {A : Type} [L₁.Structure A] (ρ : B.Assignment (I.MapRel A)) :
    (B.pull Tag dm).Assignment A :=
  fun p x =>
    ∃ h : ∀ k, (I.domFormula (p.2 k)).Realize fun j => x (finProdFinEquiv (k, j)),
      ρ p.1 fun k => ⟨(p.2 k, fun j => x (finProdFinEquiv (k, j))), h k⟩

omit [L₂.IsRelational] in
/-- The workhorse characterization of the transfer: reading it at a tuple of
points whose components are known is reading the original assignment at those
points. -/
theorem SOBlock.pullAssignRel_iff (B : SOBlock) (I : RelFOInterpretation L₁ L₂ Tag dm)
    {A : Type} [L₁.Structure A] (ρ : B.Assignment (I.MapRel A)) {i : B.ι}
    {τ : Fin (B.arity i) → Tag} {x : Fin (B.arity i * dm) → A}
    (y : Fin (B.arity i) → I.MapRel A)
    (hy : ∀ k, (y k).1 = (τ k, fun j => x (finProdFinEquiv (k, j)))) :
    B.pullAssignRel I ρ ⟨i, τ⟩ x ↔ ρ i y := by
  constructor
  · rintro ⟨h, hρ⟩
    have hfun : (fun k => (⟨(τ k, fun j => x (finProdFinEquiv (k, j))), h k⟩ :
        I.MapRel A)) = y :=
      funext fun k => Subtype.ext (hy k).symm
    rwa [hfun] at hρ
  · intro hρ
    have h : ∀ k, (I.domFormula (τ k)).Realize fun j => x (finProdFinEquiv (k, j)) := by
      intro k
      have h2 := (y k).2
      rw [hy k] at h2
      exact h2
    refine ⟨h, ?_⟩
    have hfun : (fun k => (⟨(τ k, fun j => x (finProdFinEquiv (k, j))), h k⟩ :
        I.MapRel A)) = y :=
      funext fun k => Subtype.ext (hy k).symm
    rwa [hfun]

omit [L₂.IsRelational] in
/-- Transferring the empty assignment gives the empty assignment. -/
theorem SOBlock.pullAssignRel_botAssign (B : SOBlock)
    (I : RelFOInterpretation L₁ L₂ Tag dm) {A : Type} [L₁.Structure A] :
    B.pullAssignRel I (B.botAssign (I.MapRel A)) = (B.pull Tag dm).botAssign A := by
  funext p x
  refine propext ⟨?_, False.elim⟩
  rintro ⟨hdom, h⟩
  exact h

omit [L₂.IsRelational] in
/-- The transfer of assignments to the definable universe is injective: the
original assignment is read back off the transferred one at the packed
tuples. -/
theorem SOBlock.pullAssignRel_injective (B : SOBlock)
    (I : RelFOInterpretation L₁ L₂ Tag dm) {A : Type} [L₁.Structure A] :
    Function.Injective (B.pullAssignRel I (A := A)) := by
  intro ρ ρ' h
  funext i y
  have key := congrFun (congrFun h ⟨i, fun k => (y k).1.1⟩)
    fun m => (y (finProdFinEquiv.symm m).1).1.2 (finProdFinEquiv.symm m).2
  have hcoord : ∀ (k : Fin (B.arity i)) (j : Fin dm),
      (y (finProdFinEquiv.symm (finProdFinEquiv (k, j))).1).1.2
        (finProdFinEquiv.symm (finProdFinEquiv (k, j))).2 = (y k).1.2 j :=
    fun k j => congrArg (fun z : Fin (B.arity i) × Fin dm => (y z.1).1.2 z.2)
      (Equiv.symm_apply_apply finProdFinEquiv (k, j))
  have hy : ∀ k, (y k).1 = ((y k).1.1,
      fun j => (y (finProdFinEquiv.symm (finProdFinEquiv (k, j))).1).1.2
        (finProdFinEquiv.symm (finProdFinEquiv (k, j))).2) :=
    fun k => congrArg (Prod.mk (y k).1.1) (funext fun j => (hcoord k j).symm)
  refine propext ⟨fun hρ => ?_, fun hρ => ?_⟩
  · exact (B.pullAssignRel_iff I ρ' y hy).mp
      (key ▸ (B.pullAssignRel_iff I ρ y hy).mpr hρ)
  · exact (B.pullAssignRel_iff I ρ y hy).mp
      (key ▸ (B.pullAssignRel_iff I ρ' y hy).mpr hρ)

/-! ### The gated pullback of the step formulas -/

/-- The domain gate of a pulled variable: all its argument points lie in the
definable domain. -/
noncomputable def domGateF (I : RelFOInterpretation L₁ L₂ Tag dm) (B : SOBlock)
    (p : (B.pull Tag dm).ι) :
    (L₁.sum (B.pull Tag dm).lang).Formula (Fin (B.arity p.1 * dm)) :=
  Formula.iInf fun k : Fin (B.arity p.1) =>
    LHom.sumInl.onFormula ((I.domFormula (p.2 k)).relabel fun j => finProdFinEquiv (k, j))

omit [L₂.IsRelational] in
theorem realize_domGateF (I : RelFOInterpretation L₁ L₂ Tag dm) (B : SOBlock)
    (p : (B.pull Tag dm).ι) {A : Type} [L₁.Structure A]
    (σ : (B.pull Tag dm).Assignment A) (x : Fin (B.arity p.1 * dm) → A) :
    (@Formula.Realize _ A ((B.pull Tag dm).structure₁ (L := L₁) σ) _ (domGateF I B p) x) ↔
      ∀ k, (I.domFormula (p.2 k)).Realize fun j => x (finProdFinEquiv (k, j)) := by
  let := (B.pull Tag dm).structure σ
  rw [domGateF, Formula.realize_iInf]
  refine forall_congr' fun k => ?_
  rw [LHom.realize_onFormula, Formula.realize_relabel]
  exact Iff.rfl

/-- The guarded pullback of a formula on `k` free variables, at a static tag
assignment: the relativized sibling of `DescriptiveComplexity.guardPull`. -/
noncomputable def guardPullRel {L₃ L₄ : Language.{0, 0}} [L₄.IsRelational]
    (J : RelFOInterpretation L₃ L₄ Tag dm) {k : ℕ} (φ : L₄.Formula (Fin k))
    (t : Fin k → Tag) : L₃.Formula (Fin (k * dm)) :=
  (J.pullRel (φ : L₄.BoundedFormula (Fin k) 0) (Sum.elim t finZeroElim)).relabel
    fun p => finProdFinEquiv (Sum.elim id finZeroElim p.1, p.2)

private theorem realize_guardPullRel {L₃ L₄ : Language.{0, 0}} [L₄.IsRelational]
    (J : RelFOInterpretation L₃ L₄ Tag dm) {A : Type} [L₃.Structure A] {k : ℕ}
    (φ : L₄.Formula (Fin k)) (t : Fin k → Tag) (w : Fin (k * dm) → A)
    (hw : ∀ q, (J.domFormula (t q)).Realize fun j => w (finProdFinEquiv (q, j))) :
    (guardPullRel J φ t).Realize w ↔
      φ.Realize (M := J.MapRel A)
        fun q => ⟨(t q, fun j => w (finProdFinEquiv (q, j))), hw q⟩ := by
  have hv : ∀ b : Fin k ⊕ Fin 0,
      (J.domFormula (Sum.elim t finZeroElim b)).Realize fun j =>
        (w ∘ fun p : (Fin k ⊕ Fin 0) × Fin dm =>
          finProdFinEquiv (Sum.elim id finZeroElim p.1, p.2)) (b, j) := by
    rintro (q | z)
    · exact hw q
    · exact z.elim0
  rw [guardPullRel, Formula.realize_relabel,
    J.realize_pullRel (φ : L₄.BoundedFormula (Fin k) 0) (Sum.elim t finZeroElim) _ hv]
  exact iff_of_eq (congrArg₂
    (fun a b => BoundedFormula.Realize (M := J.MapRel A)
      (φ : L₄.BoundedFormula (Fin k) 0) a b)
    (funext fun q => rfl) (Subsingleton.elim _ _))

/-! ### The extended structure equivalence -/

omit [L₂.IsRelational] in
/-- The domain formula of the extended relativized interpretation means the
original domain formula. -/
theorem realize_extendSORel_domFormula (I : RelFOInterpretation L₁ L₂ Tag dm)
    (B : SOBlock) {A : Type} [L₁.Structure A] (σ : (B.pull Tag dm).Assignment A)
    (t : Tag) (w : Fin dm → A) :
    (@Formula.Realize _ A ((B.pull Tag dm).structure₁ (L := L₁) σ) _
      ((I.extendSORel B).domFormula t) w) ↔ (I.domFormula t).Realize w := by
  let := (B.pull Tag dm).structure σ
  exact LHom.realize_onFormula LHom.sumInl (I.domFormula t)

/-- Points of the extended relativized universe are points of the original
one: the two subtypes are cut out by equivalent conditions. -/
noncomputable def extendSORelPointEquiv (I : RelFOInterpretation L₁ L₂ Tag dm)
    (B : SOBlock) (A : Type) [L₁.Structure A] (σ : (B.pull Tag dm).Assignment A) :
    (letI := (B.pull Tag dm).structure σ
     (I.extendSORel B).MapRel A) ≃ I.MapRel A :=
  letI := (B.pull Tag dm).structure σ
  Equiv.subtypeEquiv (Equiv.refl _) fun a =>
    realize_extendSORel_domFormula I B σ a.1 a.2

/-- Interpreting through the extended relativized interpretation agrees with
expanding the definable universe by the block: repackaging the points is an
isomorphism over the expanded target language, the block being read through
the transfer on one side and directly on the other (the relativized sibling
of `DescriptiveComplexity.FOInterpretation.extendSOEquiv`). -/
noncomputable def RelFOInterpretation.extendSORelEquiv
    (I : RelFOInterpretation L₁ L₂ Tag dm) (B : SOBlock) (A : Type) [L₁.Structure A]
    (ρ : B.Assignment (I.MapRel A)) :
    @Language.Equiv (L₂.sum B.lang)
      (letI := (B.pull Tag dm).structure (B.pullAssignRel I ρ)
       (I.extendSORel B).MapRel A)
      (I.MapRel A)
      (letI := (B.pull Tag dm).structure (B.pullAssignRel I ρ)
       RelFOInterpretation.mapRelStructure (I.extendSORel B) A)
      (@sumStructure L₂ B.lang (I.MapRel A) (RelFOInterpretation.mapRelStructure I A)
        (B.structure ρ)) :=
  letI := (B.pull Tag dm).structure (B.pullAssignRel I ρ)
  letI := B.structure ρ
  { toEquiv := extendSORelPointEquiv I B A (B.pullAssignRel I ρ)
    map_fun' := fun f => isEmptyElim f
    map_rel' := fun {n} R x => by
      cases R with
      | inl r =>
        exact (LHom.realize_onFormula LHom.sumInl
          (I.relFormula r fun i => (x i).1.1)).symm
      | inr r =>
        have hcoord : ∀ (k : Fin (B.arity r.1)) (j : Fin dm),
            (x (Fin.cast r.2 (finProdFinEquiv.symm (finProdFinEquiv (k, j))).1)).1.2
              (finProdFinEquiv.symm (finProdFinEquiv (k, j))).2 =
              (x (Fin.cast r.2 k)).1.2 j :=
          fun k j => congrArg
            (fun z : Fin (B.arity r.1) × Fin dm => (x (Fin.cast r.2 z.1)).1.2 z.2)
            (Equiv.symm_apply_apply finProdFinEquiv (k, j))
        have hy : ∀ k : Fin (B.arity r.1),
            ((extendSORelPointEquiv I B A (B.pullAssignRel I ρ))
                (x (Fin.cast r.2 k))).1 =
              ((x (Fin.cast r.2 k)).1.1,
                fun j =>
                  (x (Fin.cast r.2 (finProdFinEquiv.symm (finProdFinEquiv (k, j))).1)).1.2
                    (finProdFinEquiv.symm (finProdFinEquiv (k, j))).2) :=
          fun k => congrArg (Prod.mk (x (Fin.cast r.2 k)).1.1)
            (funext fun j => (hcoord k j).symm)
        exact (B.pullAssignRel_iff I ρ
          (fun k => (extendSORelPointEquiv I B A (B.pullAssignRel I ρ))
            (x (Fin.cast r.2 k))) hy).symm }

/-! ### The pulled induction and its stages -/

namespace StepDef

variable (dd : StepDef L₂) (I : RelFOInterpretation L₁ L₂ Tag dm)

/-- The pullback of a simultaneous induction through a *relativized*
interpretation: the block is pulled back variable by variable, the step
formula of a pulled variable is the guarded pullback of the original step
gated by the domain formulas of its arguments, and the output is the guarded
pullback of the original output. -/
noncomputable def pullRel : StepDef L₁ where
  B := dd.B.pull Tag dm
  step := fun p =>
    domGateF I dd.B p ⊓ guardPullRel (I.extendSORel dd.B) (dd.step p.1) p.2
  out := (I.extendSORel dd.B).pullRelSentence dd.out

variable {A : Type} [L₁.Structure A]

/-- **One application of the pulled step formulas is the transfer of one
application of the original ones.** -/
theorem next_pullRel (ρ : dd.B.Assignment (I.MapRel A)) :
    (dd.pullRel I).next (dd.B.pullAssignRel I ρ) =
      dd.B.pullAssignRel I (dd.next (A := I.MapRel A) ρ) := by
  funext p x
  let := (dd.B.pull Tag dm).structure (dd.B.pullAssignRel I ρ)
  have hsplit : (@Formula.Realize _ A ((dd.B.pull Tag dm).structure₁ (L := L₁)
        (dd.B.pullAssignRel I ρ)) _
        (domGateF I dd.B p ⊓ guardPullRel (I.extendSORel dd.B) (dd.step p.1) p.2) x) ↔
      ((@Formula.Realize _ A ((dd.B.pull Tag dm).structure₁ (L := L₁)
          (dd.B.pullAssignRel I ρ)) _ (domGateF I dd.B p) x) ∧
        (@Formula.Realize _ A ((dd.B.pull Tag dm).structure₁ (L := L₁)
          (dd.B.pullAssignRel I ρ)) _
          (guardPullRel (I.extendSORel dd.B) (dd.step p.1) p.2) x)) :=
    Formula.realize_inf
  refine propext (hsplit.trans ?_)
  constructor
  · rintro ⟨hdom', hstep⟩
    have hdom := (realize_domGateF I dd.B p _ x).mp hdom'
    have hdomE : ∀ q, ((I.extendSORel dd.B).domFormula (p.2 q)).Realize
        fun j => x (finProdFinEquiv (q, j)) := fun q =>
      (realize_extendSORel_domFormula I dd.B (dd.B.pullAssignRel I ρ) (p.2 q) _).mpr
        (hdom q)
    have h1 := (realize_guardPullRel (I.extendSORel dd.B) (dd.step p.1) p.2 x
      hdomE).mp hstep
    have h2 := (realize_formula_of_equiv (I.extendSORelEquiv dd.B A ρ) (dd.step p.1)
      (fun q => ⟨(p.2 q, fun j => x (finProdFinEquiv (q, j))), hdomE q⟩)).mpr h1
    exact (dd.B.pullAssignRel_iff I (dd.next ρ) (τ := p.2) (x := x)
      (fun q => (I.extendSORelEquiv dd.B A ρ)
        ⟨(p.2 q, fun j => x (finProdFinEquiv (q, j))), hdomE q⟩)
      (fun q => rfl)).mpr h2
  · rintro ⟨hdom, hρ⟩
    have hdomE : ∀ q, ((I.extendSORel dd.B).domFormula (p.2 q)).Realize
        fun j => x (finProdFinEquiv (q, j)) := fun q =>
      (realize_extendSORel_domFormula I dd.B (dd.B.pullAssignRel I ρ) (p.2 q) _).mpr
        (hdom q)
    refine ⟨(realize_domGateF I dd.B p _ x).mpr hdom, ?_⟩
    refine (realize_guardPullRel (I.extendSORel dd.B) (dd.step p.1) p.2 x hdomE).mpr ?_
    refine (realize_formula_of_equiv (I.extendSORelEquiv dd.B A ρ) (dd.step p.1)
      (fun q => ⟨(p.2 q, fun j => x (finProdFinEquiv (q, j))), hdomE q⟩)).mp ?_
    exact (dd.B.pullAssignRel_iff I (dd.next ρ) (τ := p.2) (x := x)
      (fun q => (I.extendSORelEquiv dd.B A ρ)
        ⟨(p.2 q, fun j => x (finProdFinEquiv (q, j))), hdomE q⟩)
      (fun q => rfl)).mp ⟨hdom, hρ⟩

/-- The partial stages of the relativized pullback are the transfers of the
original stages. -/
private theorem partStage_pullRel (n : ℕ) :
    (dd.pullRel I).partStage A n =
      dd.B.pullAssignRel I (dd.partStage (I.MapRel A) n) := by
  induction n with
  | zero => exact (dd.B.pullAssignRel_botAssign I).symm
  | succ n ih =>
    rw [(dd.pullRel I).partStage_succ, dd.partStage_succ, ih, next_pullRel]

/-- The inflationary step commutes with the transfer. -/
private theorem inflStep_pullRel (ρ : dd.B.Assignment (I.MapRel A)) :
    (dd.pullRel I).inflStep (dd.B.pullAssignRel I ρ) =
      dd.B.pullAssignRel I (dd.inflStep (A := I.MapRel A) ρ) := by
  funext p x
  have hnext := congrFun (congrFun (next_pullRel dd I ρ) p) x
  refine propext ?_
  constructor
  · rintro (⟨h, hp⟩ | hq)
    · exact ⟨h, Or.inl hp⟩
    · obtain ⟨h, hq'⟩ := hnext ▸ hq
      exact ⟨h, Or.inr hq'⟩
  · rintro ⟨h, hp | hq⟩
    · exact Or.inl ⟨h, hp⟩
    · exact Or.inr (hnext.symm ▸ (⟨h, hq⟩ :
        dd.B.pullAssignRel I (dd.next (A := I.MapRel A) ρ) p x))

/-- The inflationary stages of the relativized pullback are the transfers of
the original stages. -/
private theorem inflStage_pullRel (n : ℕ) :
    (dd.pullRel I).inflStage A n =
      dd.B.pullAssignRel I (dd.inflStage (I.MapRel A) n) := by
  induction n with
  | zero => exact (dd.B.pullAssignRel_botAssign I).symm
  | succ n ih =>
    rw [(dd.pullRel I).inflStage_succ, dd.inflStage_succ, ih, inflStep_pullRel]

/-- The value of the pulled inflationary iteration is the transfer of the
original value. -/
theorem inflLimit_pullRel :
    (dd.pullRel I).inflLimit A = dd.B.pullAssignRel I (dd.inflLimit (I.MapRel A)) := by
  funext p x
  refine propext ?_
  have hstage : ∀ n, (dd.pullRel I).inflStage A n p x ↔
      dd.B.pullAssignRel I (dd.inflStage (I.MapRel A) n) p x :=
    fun n => iff_of_eq (congrFun (congrFun (inflStage_pullRel dd I n) p) x)
  constructor
  · rintro ⟨n, hn⟩
    obtain ⟨h, hρ⟩ := (hstage n).mp hn
    exact ⟨h, ⟨n, hρ⟩⟩
  · rintro ⟨h, n, hρ⟩
    exact ⟨n, (hstage n).mpr ⟨h, hρ⟩⟩

/-- Being a fixed point of the step is insensitive to the transfer. -/
private theorem isFixedPt_next_pullRel_iff (ρ : dd.B.Assignment (I.MapRel A)) :
    IsFixedPt (dd.pullRel I).next (dd.B.pullAssignRel I ρ) ↔
      IsFixedPt (dd.next (A := I.MapRel A)) ρ :=
  ⟨fun h => dd.B.pullAssignRel_injective I ((next_pullRel dd I ρ).symm.trans h),
    fun h => (next_pullRel dd I ρ).trans (congrArg _ h)⟩

/-- The value of the pulled inflationary definition is the value of the
original one on the definable universe. -/
theorem ifpHolds_pullRel : (dd.pullRel I).IFPHolds A ↔ dd.IFPHolds (I.MapRel A) := by
  rw [IFPHolds, IFPHolds, inflLimit_pullRel dd I]
  let := (dd.B.pull Tag dm).structure (dd.B.pullAssignRel I (dd.inflLimit (I.MapRel A)))
  have hpull := (I.extendSORel dd.B).realize_pullRelSentence dd.out A
  have htrans := realize_sentence_of_equiv
    (I.extendSORelEquiv dd.B A (dd.inflLimit (I.MapRel A))) dd.out
  exact hpull.trans htrans

/-- The value of the pulled partial definition is the value of the original
one on the definable universe. -/
theorem pfpHolds_pullRel : (dd.pullRel I).PFPHolds A ↔ dd.PFPHolds (I.MapRel A) := by
  rw [PFPHolds, PFPHolds]
  refine exists_congr fun n => ?_
  rw [partStage_pullRel dd I n]
  refine and_congr (isFixedPt_next_pullRel_iff dd I _) ?_
  let := (dd.B.pull Tag dm).structure
    (dd.B.pullAssignRel I (dd.partStage (I.MapRel A) n))
  have hpull := (I.extendSORel dd.B).realize_pullRelSentence dd.out A
  have htrans := realize_sentence_of_equiv
    (I.extendSORelEquiv dd.B A (dd.partStage (I.MapRel A) n)) dd.out
  exact hpull.trans htrans

end StepDef

/-! ### Closure under relativized ordered reductions -/

section Closure

variable [L₁.IsRelational] {P : DecisionProblem L₁} {Q : DecisionProblem L₂}

/-- **FO(≤, IFP) definability is closed under relativized ordered
reductions**: the induction pulls back through the order-extended relativized
interpretation, whose universe – the definable domain with the restricted
lexicographic order – is identified with the ordered domain by
`DescriptiveComplexity.RelFOInterpretation.ordExtendRelLEquiv`. -/
theorem IFPDefinable.of_relOrderedReduction (f : P ≤ʳᶠᵒ[≤] Q) (h : IFPDefinable Q) :
    IFPDefinable P := by
  obtain ⟨d, hd⟩ := h
  let := f.tagFinite
  let : LinearOrder f.Tag := finiteLinearOrder f.Tag
  refine ⟨d.pullRel f.toRelInterpretation.ordExtendRel, ?_⟩
  intro A _ _ _ _
  let := f.toRelInterpretation.mapRelLinearOrder A
  have : Finite (f.toRelInterpretation.MapRel A) := f.toRelInterpretation.mapRel_finite A
  have : Nonempty (f.toRelInterpretation.MapRel A) := f.mapRel_nonempty A
  refine (f.correct A).trans ((hd (f.toRelInterpretation.MapRel A)).trans ?_)
  refine Iff.trans ?_
    (StepDef.ifpHolds_pullRel d f.toRelInterpretation.ordExtendRel).symm
  exact (@StepDef.ifpHolds_equiv (L₂.sum Language.order) d
    (f.toRelInterpretation.ordExtendRel.MapRel A) (f.toRelInterpretation.MapRel A)
    (RelFOInterpretation.mapRelStructure f.toRelInterpretation.ordExtendRel A)
    (letI := f.toRelInterpretation.mapRelLinearOrder A
     sumOrderStructure L₂ (f.toRelInterpretation.MapRel A))
    (f.toRelInterpretation.ordExtendRelLEquiv A)).symm

/-- **FO(≤, PFP) definability is closed under relativized ordered
reductions.**
Registered in the Lax archive as
[`Lax134656.PartialFixedPointClosure.pfpDefinable_of_relOrderedReduction`](https://laxarchive.org/lax-134656/Lax134656.PartialFixedPointClosure.html#s-Lax134656.PartialFixedPointClosure.pfpDefinable_of_relOrderedReduction). -/
theorem PFPDefinable.of_relOrderedReduction (f : P ≤ʳᶠᵒ[≤] Q) (h : PFPDefinable Q) :
    PFPDefinable P := by
  obtain ⟨d, hd⟩ := h
  let := f.tagFinite
  let : LinearOrder f.Tag := finiteLinearOrder f.Tag
  refine ⟨d.pullRel f.toRelInterpretation.ordExtendRel, ?_⟩
  intro A _ _ _ _
  let := f.toRelInterpretation.mapRelLinearOrder A
  have : Finite (f.toRelInterpretation.MapRel A) := f.toRelInterpretation.mapRel_finite A
  have : Nonempty (f.toRelInterpretation.MapRel A) := f.mapRel_nonempty A
  refine (f.correct A).trans ((hd (f.toRelInterpretation.MapRel A)).trans ?_)
  refine Iff.trans ?_
    (StepDef.pfpHolds_pullRel d f.toRelInterpretation.ordExtendRel).symm
  exact (@StepDef.pfpHolds_equiv (L₂.sum Language.order) d
    (f.toRelInterpretation.ordExtendRel.MapRel A) (f.toRelInterpretation.MapRel A)
    (RelFOInterpretation.mapRelStructure f.toRelInterpretation.ordExtendRel A)
    (letI := f.toRelInterpretation.mapRelLinearOrder A
     sumOrderStructure L₂ (f.toRelInterpretation.MapRel A))
    (f.toRelInterpretation.ordExtendRelLEquiv A)).symm

end Closure

end DescriptiveComplexity
