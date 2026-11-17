/-
Copyright (c) 2026 Pierre Senellart. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre Senellart
-/
module

public import LeanPool.DescriptiveCounting.FixedPointPartial
import Mathlib.Tactic.FinCases
import all LeanPool.DescriptiveCounting.FixedPointInflationary
import all LeanPool.DescriptiveCounting.FixedPointPartial
import all LeanPool.DescriptiveCounting.FixedPointStep

/-!
# Order relativization: moving the order between the instance and the vocabulary

The ordered fixed-point definability notions
(`DescriptiveComplexity.IFPDefinable`, `DescriptiveComplexity.PFPDefinable`)
quantify over every linear order on the universe of an `L`-structure; the
order-free notions over the *ordered expansion* `L.sum Language.order` instead
see the order as one more relation of the instance. This file proves the two
readings interchangeable, the bookkeeping the unordered Abiteboul–Vianu
theorem (`DescriptiveComplexity.AbiteboulVianu`) threads its right-to-left
direction through:

* `DescriptiveComplexity.DecisionProblem.withOrder` – the problem «the order
  symbol is a linear order, and `P` holds on the `L`-reduct», over
  `L.sum Language.order`;
* `DescriptiveComplexity.ifpDefinable_iff_ifpDefinableFree_withOrder` and
  `DescriptiveComplexity.pfpDefinable_iff_pfpDefinableFree_withOrder` – `P` is
  FO(≤, IFP) (resp. FO(≤, PFP)) definable exactly when `P.withOrder` is
  *order-free* FO(IFP) (resp. FO(PFP)) definable.

Left to right, the induction is reused as is and its output is guarded by the
first-order sentence «the order symbol is a linear order»
(`DescriptiveComplexity.leLinearS`, via
`DescriptiveComplexity.StepDef.guardOut`); on an instance whose order symbol
does satisfy the guard, the promoted order
(`DescriptiveComplexity.LeLinearOn.linearOrder`) rebuilds the ordered
instance, identical to the given one through the identity isomorphism
(`DescriptiveComplexity.relMapIffEquiv`). Right to left is immediate: an
ordered `L`-structure *is* an instance of the expansion whose order symbol is
a linear order (`DescriptiveComplexity.sumOrderStructure`).
-/

@[expose] public section

namespace DescriptiveComplexity

open FirstOrder

open Language Structure

variable {L : Language.{0, 0}}

/-! ### Identity isomorphisms between structures with the same relations -/

/-- Two structures over a relational vocabulary interpreting every relation
symbol equivalently are isomorphic through the identity map. -/
def relMapIffEquiv [L.IsRelational] {A : Type} (inst inst' : L.Structure A)
    (h : ∀ {n : ℕ} (r : L.Relations n) (x : Fin n → A),
      @RelMap L A inst n r x ↔ @RelMap L A inst' n r x) :
    @Language.Equiv L A A inst inst' :=
  @Language.Equiv.mk L A A inst inst' (Equiv.refl A)
    (fun {_} f _ => isEmptyElim f) (fun {_} r x => (h r x).symm)

/-- An isomorphism over an expanded vocabulary is an isomorphism of the
reducts. -/
def reductSumInlEquiv {L' : Language.{0, 0}} {A B : Type}
    [instA : (L.sum L').Structure A] [instB : (L.sum L').Structure B]
    (e : A ≃[L.sum L'] B) :
    @Language.Equiv L A B ((LHom.sumInl : L →ᴸ L.sum L').reduct A)
      ((LHom.sumInl : L →ᴸ L.sum L').reduct B) :=
  @Language.Equiv.mk L A B ((LHom.sumInl : L →ᴸ L.sum L').reduct A)
    ((LHom.sumInl : L →ᴸ L.sum L').reduct B) e.toEquiv
    (fun {_} f x => e.map_fun' (Sum.inl f) x)
    (fun {_} r x => e.map_rel' (Sum.inl r) x)

/-! ### «The order symbol is a linear order» -/

section LeLinear

variable (L)

/-- The interpretation of the order symbol of the ordered expansion is a
linear order: reflexive, transitive, antisymmetric and total. This is the
guard under which a structure over `L.sum Language.order` is an ordered
`L`-structure. -/
def LeLinearOn (A : Type) [(L.sum Language.order).Structure A] : Prop :=
  Std.Refl (fun x y : A =>
    RelMap (leSymb : (L.sum Language.order).Relations 2) ![x, y]) ∧
  IsTrans A (fun x y : A =>
    RelMap (leSymb : (L.sum Language.order).Relations 2) ![x, y]) ∧
  Std.Antisymm (fun x y : A =>
    RelMap (leSymb : (L.sum Language.order).Relations 2) ![x, y]) ∧
  Std.Total (fun x y : A =>
    RelMap (leSymb : (L.sum Language.order).Relations 2) ![x, y])

/-- The guard sentence «the order symbol is a linear order», over the ordered
expansion. -/
def leLinearS : (L.sum Language.order).Sentence :=
  (leSymb : (L.sum Language.order).Relations 2).reflexive ⊓
    ((leSymb : (L.sum Language.order).Relations 2).transitive ⊓
      ((leSymb : (L.sum Language.order).Relations 2).antisymmetric ⊓
        (leSymb : (L.sum Language.order).Relations 2).total))

/-- Realization of the guard sentence: the order symbol is a linear order. -/
private theorem realize_leLinearS (A : Type) [(L.sum Language.order).Structure A] :
    A ⊨ leLinearS L ↔ LeLinearOn L A := by
  have hsplit : A ⊨ leLinearS L ↔
      (A ⊨ (leSymb : (L.sum Language.order).Relations 2).reflexive ∧
        (A ⊨ (leSymb : (L.sum Language.order).Relations 2).transitive ∧
          (A ⊨ (leSymb : (L.sum Language.order).Relations 2).antisymmetric ∧
            A ⊨ (leSymb : (L.sum Language.order).Relations 2).total))) :=
    Formula.realize_inf.trans (and_congr Iff.rfl
      (Formula.realize_inf.trans (and_congr Iff.rfl Formula.realize_inf)))
  rw [hsplit, Relations.realize_reflexive, Relations.realize_transitive,
    Relations.realize_antisymmetric, Relations.realize_total]
  exact Iff.rfl

variable {L}

/-- Promoting a linear order symbol to a linear order on the universe
(decidability by choice). -/
@[instance_reducible]
noncomputable def LeLinearOn.linearOrder {A : Type}
    [(L.sum Language.order).Structure A] (h : LeLinearOn L A) : LinearOrder A where
  le x y := RelMap (leSymb : (L.sum Language.order).Relations 2) ![x, y]
  le_refl := h.1.refl
  le_trans := h.2.1.trans
  le_antisymm := h.2.2.1.antisymm
  le_total := h.2.2.2.total
  toDecidableLE := fun _ _ => Classical.propDecidable _

/-- The guard transports along an isomorphism over the ordered expansion. -/
theorem LeLinearOn.equiv {A B : Type} [(L.sum Language.order).Structure A]
    [(L.sum Language.order).Structure B] (e : A ≃[L.sum Language.order] B)
    (h : LeLinearOn L A) : LeLinearOn L B := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hrel : ∀ a a' : A,
      RelMap (leSymb : (L.sum Language.order).Relations 2) ![a, a'] ↔
        RelMap (leSymb : (L.sum Language.order).Relations 2) ![e a, e a'] :=
    fun a a' => relMap_equiv₂ e leSymb a a'
  have hsurj : Function.Surjective e := EquivLike.surjective e
  refine ⟨⟨fun b => ?_⟩, ⟨fun b b' b'' hbb' hb'b'' => ?_⟩,
    ⟨fun b b' hbb' hb'b => ?_⟩, ⟨fun b b' => ?_⟩⟩
  · obtain ⟨a, rfl⟩ := hsurj b
    exact (hrel a a).mp (h1.refl a)
  · obtain ⟨a, rfl⟩ := hsurj b
    obtain ⟨a', rfl⟩ := hsurj b'
    obtain ⟨a'', rfl⟩ := hsurj b''
    exact (hrel a a'').mp
      (h2.trans a a' a'' ((hrel a a').mpr hbb') ((hrel a' a'').mpr hb'b''))
  · obtain ⟨a, rfl⟩ := hsurj b
    obtain ⟨a', rfl⟩ := hsurj b'
    exact congrArg _ (h3.antisymm a a' ((hrel a a').mpr hbb') ((hrel a' a).mpr hb'b))
  · obtain ⟨a, rfl⟩ := hsurj b
    obtain ⟨a', rfl⟩ := hsurj b'
    rcases h4.total a a' with hc | hc
    · exact Or.inl ((hrel a a').mp hc)
    · exact Or.inr ((hrel a' a).mp hc)

end LeLinear

/-! ### The problem, moved to the ordered expansion -/

section WithOrder

variable [L.IsRelational] (P : DecisionProblem L)

theorem withOrder_iso_invariant {A B : Type}
    [instA : (L.sum Language.order).Structure A]
    [instB : (L.sum Language.order).Structure B] (e : A ≃[L.sum Language.order] B) :
    (LeLinearOn L A ∧
        (letI := (LHom.sumInl : L →ᴸ L.sum Language.order).reduct A; P A)) ↔
      (LeLinearOn L B ∧
        (letI := (LHom.sumInl : L →ᴸ L.sum Language.order).reduct B; P B)) :=
  and_congr ⟨fun h => h.equiv e, fun h => h.equiv e.symm⟩
    (@DecisionProblem.iso_invariant L _ P A B
      ((LHom.sumInl : L →ᴸ L.sum Language.order).reduct A)
      ((LHom.sumInl : L →ᴸ L.sum Language.order).reduct B) (reductSumInlEquiv e))

/-- «The order symbol is a linear order, and `P` holds on the `L`-reduct»:
the problem `P`, moved to the ordered expansion of its vocabulary with the
order now part of the instance. The order-relativized problem through which
definability quantified over all linear orders
(`DescriptiveComplexity.IFPDefinable`, `DescriptiveComplexity.PFPDefinable`)
is compared with order-free definability over the expansion. -/
def DecisionProblem.withOrder : DecisionProblem (L.sum Language.order) where
  Holds A _ := LeLinearOn L A ∧
    (letI := (LHom.sumInl : L →ᴸ L.sum Language.order).reduct A; P A)
  iso_invariant e := withOrder_iso_invariant P e

end WithOrder

/-! ### Guarding the output of an induction -/

namespace StepDef

variable {L' : Language.{0, 0}} (d : StepDef L') (χ : L'.Sentence)

/-- Guard the output of a simultaneous induction by a sentence over the base
vocabulary: same block, same step formulas, the output conjoined with the
guard. -/
private def guardOut : StepDef L' where
  B := d.B
  step := d.step
  out := LHom.sumInl.onSentence χ ⊓ d.out

variable {A : Type} [L'.Structure A]

private theorem realize_guardOut_out (ρ : d.B.Assignment A) :
    (@Sentence.Realize _ A (d.B.structure₁ (L := L') ρ) (d.guardOut χ).out) ↔
      (A ⊨ χ ∧ @Sentence.Realize _ A (d.B.structure₁ (L := L') ρ) d.out) := by
  let := d.B.structure₁ (L := L') ρ
  refine Formula.realize_inf.trans (and_congr ?_ Iff.rfl)
  exact (LHom.sumInl : L' →ᴸ L'.sum d.B.lang).realize_onSentence (M := A) χ

variable (A) in
/-- The inflationary value of the guarded induction: the guard holds and the
original value does. -/
private theorem ifpHolds_guardOut : (d.guardOut χ).IFPHolds A ↔ (A ⊨ χ ∧ d.IFPHolds A) :=
  realize_guardOut_out d χ (d.inflLimit A)

variable (A) in
/-- The partial value of the guarded induction: the guard holds and the
original value does. -/
private theorem pfpHolds_guardOut : (d.guardOut χ).PFPHolds A ↔ (A ⊨ χ ∧ d.PFPHolds A) := by
  constructor
  · rintro ⟨n, hfix, hout⟩
    obtain ⟨hχ, hout'⟩ := (realize_guardOut_out d χ (d.partStage A n)).mp hout
    exact ⟨hχ, n, hfix, hout'⟩
  · rintro ⟨hχ, n, hfix, hout⟩
    exact ⟨n, hfix, (realize_guardOut_out d χ (d.partStage A n)).mpr ⟨hχ, hout⟩⟩

end StepDef

/-! ### The transfer -/

section Transfer

variable [L.IsRelational] (P : DecisionProblem L)

private theorem vecEta₂ {A : Type} (x : Fin 2 → A) : ![x 0, x 1] = x := by
  funext j
  fin_cases j <;> simp

/-- The ordered instance rebuilt from a structure over the expansion whose
order symbol is a linear order is the given instance, through the identity
isomorphism. -/
noncomputable def rebuildEquiv {A : Type}
    [inst : (L.sum Language.order).Structure A]
    (h : LeLinearOn L A) :
    @Language.Equiv (L.sum Language.order) A A
      (letI := (LHom.sumInl : L →ᴸ L.sum Language.order).reduct A
       letI := h.linearOrder
       sumOrderStructure L A) inst :=
  letI := (LHom.sumInl : L →ᴸ L.sum Language.order).reduct A
  letI := h.linearOrder
  relMapIffEquiv (sumOrderStructure L A) inst fun {n} r x => by
    cases r with
    | inl s => exact Iff.rfl
    | inr s =>
      cases s with
      | le =>
        exact iff_of_eq
          (congrArg (@RelMap (L.sum Language.order) A inst 2 (Sum.inr orderRel.le))
            (vecEta₂ x))

/-- **Order relativization, inflationary case**: `P` is FO(≤, IFP) definable
exactly when its ordered relativization
(`DescriptiveComplexity.DecisionProblem.withOrder`) is *order-free* FO(IFP)
definable. -/
theorem ifpDefinable_iff_ifpDefinableFree_withOrder :
    IFPDefinable P ↔ IFPDefinableFree P.withOrder := by
  constructor
  · rintro ⟨d, hd⟩
    refine ⟨d.guardOut (leLinearS L), ?_⟩
    intro A inst _ _
    rw [d.ifpHolds_guardOut (leLinearS L) A, realize_leLinearS L A]
    refine and_congr_right fun h => ?_
    let := (LHom.sumInl : L →ᴸ L.sum Language.order).reduct A
    let := h.linearOrder
    exact (hd A).trans
      (@StepDef.ifpHolds_equiv (L.sum Language.order) d A A (sumOrderStructure L A)
        inst (rebuildEquiv h))
  · rintro ⟨d, hd⟩
    refine ⟨d, ?_⟩
    intro A instL lo _ _
    refine Iff.trans ?_ (hd A)
    have hlin : LeLinearOn L A :=
      ⟨⟨fun a => le_refl a⟩, ⟨fun a b c hab hbc => le_trans hab hbc⟩,
        ⟨fun a b hab hba => le_antisymm hab hba⟩, ⟨fun a b => le_total a b⟩⟩
    have hP : (letI := (LHom.sumInl : L →ᴸ L.sum Language.order).reduct A; P A) ↔ P A :=
      @DecisionProblem.iso_invariant L _ P A A
        ((LHom.sumInl : L →ᴸ L.sum Language.order).reduct A) instL
        (relMapIffEquiv _ instL fun r x => Iff.rfl)
    exact ⟨fun hp => ⟨hlin, hP.mpr hp⟩, fun hw => hP.mp hw.2⟩

/-- **Order relativization, partial case**: `P` is FO(≤, PFP) definable
exactly when its ordered relativization
(`DescriptiveComplexity.DecisionProblem.withOrder`) is *order-free* FO(PFP)
definable. -/
theorem pfpDefinable_iff_pfpDefinableFree_withOrder :
    PFPDefinable P ↔ PFPDefinableFree P.withOrder := by
  constructor
  · rintro ⟨d, hd⟩
    refine ⟨d.guardOut (leLinearS L), ?_⟩
    intro A inst _ _
    rw [d.pfpHolds_guardOut (leLinearS L) A, realize_leLinearS L A]
    refine and_congr_right fun h => ?_
    let := (LHom.sumInl : L →ᴸ L.sum Language.order).reduct A
    let := h.linearOrder
    exact (hd A).trans
      (@StepDef.pfpHolds_equiv (L.sum Language.order) d A A (sumOrderStructure L A)
        inst (rebuildEquiv h))
  · rintro ⟨d, hd⟩
    refine ⟨d, ?_⟩
    intro A instL lo _ _
    refine Iff.trans ?_ (hd A)
    have hlin : LeLinearOn L A :=
      ⟨⟨fun a => le_refl a⟩, ⟨fun a b c hab hbc => le_trans hab hbc⟩,
        ⟨fun a b hab hba => le_antisymm hab hba⟩, ⟨fun a b => le_total a b⟩⟩
    have hP : (letI := (LHom.sumInl : L →ᴸ L.sum Language.order).reduct A; P A) ↔ P A :=
      @DecisionProblem.iso_invariant L _ P A A
        ((LHom.sumInl : L →ᴸ L.sum Language.order).reduct A) instL
        (relMapIffEquiv _ instL fun r x => Iff.rfl)
    exact ⟨fun hp => ⟨hlin, hP.mpr hp⟩, fun hw => hP.mp hw.2⟩

end Transfer

/-! ### Order-free definability implies ordered definability -/

namespace StepDef

variable (d : StepDef L)

/-- A simultaneous induction over the base vocabulary, read over the ordered
expansion: the formulas ignore the order symbol. -/
noncomputable def liftOrder : StepDef (L.sum Language.order) where
  B := d.B
  step := fun i =>
    (LHom.sumMap (LHom.sumInl (L' := Language.order))
      (LHom.id d.B.lang)).onFormula (d.step i)
  out :=
    (LHom.sumMap (LHom.sumInl (L' := Language.order))
      (LHom.id d.B.lang)).onSentence d.out

variable {A : Type} [L.Structure A] [LinearOrder A]

private theorem realize_liftOrder {α : Type} (ρ : d.B.Assignment A)
    (φ : (L.sum d.B.lang).Formula α) (v : α → A) :
    (@Formula.Realize _ A
      (@SOBlock.structure₁ (L.sum Language.order) d.B A
        (sumOrderStructure L A) ρ) _
      ((LHom.sumMap (LHom.sumInl (L' := Language.order))
        (LHom.id d.B.lang)).onFormula φ) v) ↔
      @Formula.Realize _ A (d.B.structure₁ (L := L) ρ) _ φ v := by
  let := d.B.structure₁ (L := L) ρ
  let := @SOBlock.structure₁ (L.sum Language.order) d.B A
    (sumOrderStructure L A) ρ
  exact LHom.realize_onFormula
    (φ := LHom.sumMap (LHom.sumInl (L' := Language.order)) (LHom.id d.B.lang)) φ

private theorem next_liftOrder (ρ : d.B.Assignment A) :
    @StepDef.next (L.sum Language.order) d.liftOrder A (sumOrderStructure L A) ρ =
      d.next ρ := by
  funext i x
  exact propext (d.realize_liftOrder ρ (d.step i) x)

private theorem inflStage_liftOrder (n : ℕ) :
    @StepDef.inflStage (L.sum Language.order) d.liftOrder A
        (sumOrderStructure L A) n = d.inflStage A n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    funext i x
    rw [@StepDef.inflStage_succ (L.sum Language.order) d.liftOrder A
      (sumOrderStructure L A) n, d.inflStage_succ, ih]
    refine propext (or_congr Iff.rfl ?_)
    exact iff_of_eq (congrFun (congrFun (d.next_liftOrder (d.inflStage A n)) i) x)

private theorem partStage_liftOrder (n : ℕ) :
    @StepDef.partStage (L.sum Language.order) d.liftOrder A
        (sumOrderStructure L A) n = d.partStage A n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [@StepDef.partStage_succ (L.sum Language.order) d.liftOrder A
      (sumOrderStructure L A) n, d.partStage_succ, ih]
    exact d.next_liftOrder (d.partStage A n)

/-- The inflationary value of the lifted induction is the original one. -/
private theorem ifpHolds_liftOrder :
    (@StepDef.IFPHolds (L.sum Language.order) d.liftOrder A
        (sumOrderStructure L A)) ↔ d.IFPHolds A := by
  have hlim : @StepDef.inflLimit (L.sum Language.order) d.liftOrder A
      (sumOrderStructure L A) = d.inflLimit A := by
    funext i x
    exact propext (exists_congr fun n => iff_of_eq
      (congrFun (congrFun (d.inflStage_liftOrder n) i) x))
  rw [StepDef.IFPHolds, StepDef.IFPHolds, hlim]
  exact d.realize_liftOrder (d.inflLimit A) d.out default

/-- The partial value of the lifted induction is the original one. -/
private theorem pfpHolds_liftOrder :
    (@StepDef.PFPHolds (L.sum Language.order) d.liftOrder A
        (sumOrderStructure L A)) ↔ d.PFPHolds A := by
  refine exists_congr fun n => ?_
  rw [d.partStage_liftOrder n]
  exact and_congr
    ⟨fun h => (d.next_liftOrder (d.partStage A n)).symm.trans h,
      fun h => (d.next_liftOrder (d.partStage A n)).trans h⟩
    (d.realize_liftOrder (d.partStage A n) d.out default)

end StepDef

/-- **Order-free FO(IFP) definability implies ordered definability**: the
induction ignores the order.
Registered in the Lax archive as
[`Lax134656.InflationaryInPartial.ifpDefinableFree_ifpDefinable`](https://laxarchive.org/lax-134656/Lax134656.InflationaryInPartial.html#s-Lax134656.InflationaryInPartial.ifpDefinableFree_ifpDefinable). -/
theorem IFPDefinableFree.ifpDefinable [L.IsRelational] {P : DecisionProblem L}
    (h : IFPDefinableFree P) : IFPDefinable P := by
  obtain ⟨d, hd⟩ := h
  refine ⟨d.liftOrder, ?_⟩
  intro A _ _ _ _
  exact (hd A).trans (d.ifpHolds_liftOrder).symm

/-- **Order-free FO(PFP) definability implies ordered definability**: the
induction ignores the order.
Registered in the Lax archive as
[`Lax134656.InflationaryInPartial.pfpDefinableFree_pfpDefinable`](https://laxarchive.org/lax-134656/Lax134656.InflationaryInPartial.html#s-Lax134656.InflationaryInPartial.pfpDefinableFree_pfpDefinable). -/
theorem PFPDefinableFree.pfpDefinable [L.IsRelational] {P : DecisionProblem L}
    (h : PFPDefinableFree P) : PFPDefinable P := by
  obtain ⟨d, hd⟩ := h
  refine ⟨d.liftOrder, ?_⟩
  intro A _ _ _ _
  exact (hd A).trans (d.pfpHolds_liftOrder).symm

end DescriptiveComplexity
