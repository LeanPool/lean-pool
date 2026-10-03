/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NFStandard.Basic
public import LeanPool.NFWeakPartition.NFCompactLeafEndpoints

/-! NF weak partition development: NFStandard.HailperinModel. -/


public section

namespace NFChoice.Foundation.NFStandard

open scoped Fol
open NFChoice.Foundation.ExactLiteralTrial
open NFChoice.SemanticCore
open NFChoice.SemanticCore.Lowering
open NFChoice.ReplaySupport
open NFChoice.Compiler.NFCompactLeafEndpoints

/-! This file packages the eleven literal Hailperin axioms as ordinary operations
on an arbitrary model.  All operations are Skolem choices from the actual
axioms; their API exposes only extensional membership laws.
-/


/-- The intrinsic formula underlying any literal axiom holds in its model. -/
theorem formulaHolds_literal_axiom {S : Fol.Structure LNF}
    (hH : Fol.all_realize_sentence S LiteralHailperinNF) (name : HailperinAxiomName) :
    FormulaHolds S DVec.nil (literalAxiomSyntax name) :=
  (formulaHolds_toFlypitch DVec.nil (literalAxiomSyntax name)).2
    (realizes_literal_axiom hH name)

/-- Raw semantic content of `ax-nin`. -/
theorem exists_nin {S : Fol.Structure LNF}
    (hH : Fol.all_realize_sentence S LiteralHailperinNF) (x y : S) :
    ∃ a : S, ∀ z : S, Mem S z a ↔ ¬(Mem S z x ∧ Mem S z y) :=
  by
  have h := formulaHolds_literal_axiom hH .axNin
  simpa [literalAxiomSyntax, literalAxNin, FormulaHolds, lookup, DVec.nth] using h x y

/-- A selected NAND set supplied by `ax-nin`. -/
@[expose]
noncomputable def nin {S : Fol.Structure LNF}
    (hH : Fol.all_realize_sentence S LiteralHailperinNF) (x y : S) : S :=
  Classical.choose (exists_nin hH x y)

@[simp]
theorem mem_nin {S : Fol.Structure LNF}
    (hH : Fol.all_realize_sentence S LiteralHailperinNF) (x y z : S) :
    Mem S z (nin hH x y) ↔ ¬(Mem S z x ∧ Mem S z y) :=
  Classical.choose_spec (exists_nin hH x y) z

/-- Raw semantic content of `ax-sn`. -/
theorem exists_singleton {S : Fol.Structure LNF}
    (hH : Fol.all_realize_sentence S LiteralHailperinNF) (x : S) :
    ∃ a : S, ∀ z : S, Mem S z a ↔ z = x :=
  by
  have h := formulaHolds_literal_axiom hH .axSn
  simpa [literalAxiomSyntax, literalAxSn, FormulaHolds, lookup, DVec.nth] using h x

/-- A selected singleton supplied by `ax-sn`. -/
@[expose]
noncomputable def singleton {S : Fol.Structure LNF}
    (hH : Fol.all_realize_sentence S LiteralHailperinNF) (x : S) : S :=
  Classical.choose (exists_singleton hH x)

@[simp]
theorem mem_singleton {S : Fol.Structure LNF}
    (hH : Fol.all_realize_sentence S LiteralHailperinNF) (x z : S) :
    Mem S z (singleton hH x) ↔ z = x :=
  Classical.choose_spec (exists_singleton hH x) z

/-- Complement, derived from NAND. -/
@[expose]
noncomputable def complement {S : Fol.Structure LNF}
    (hH : Fol.all_realize_sentence S LiteralHailperinNF) (x : S) : S :=
  nin hH x x

@[simp]
theorem mem_complement {S : Fol.Structure LNF}
    (hH : Fol.all_realize_sentence S LiteralHailperinNF) (x z : S) :
    Mem S z (complement hH x) ↔ ¬Mem S z x := by simp [complement]

/-- Binary union, derived by De Morgan from NAND. -/
@[expose]
noncomputable def union {S : Fol.Structure LNF}
    (hH : Fol.all_realize_sentence S LiteralHailperinNF) (x y : S) : S :=
  nin hH (complement hH x) (complement hH y)

@[simp]
theorem mem_union {S : Fol.Structure LNF}
    (hH : Fol.all_realize_sentence S LiteralHailperinNF) (x y z : S) :
    Mem S z (union hH x y) ↔ Mem S z x ∨ Mem S z y :=
  by
  simp [union]
  tauto

/-- Unordered pair, derived as the union of two selected singletons. -/
@[expose]
noncomputable def unorderedPair {S : Fol.Structure LNF}
    (hH : Fol.all_realize_sentence S LiteralHailperinNF) (x y : S) : S :=
  union hH (singleton hH x) (singleton hH y)

@[simp]
theorem mem_unorderedPair {S : Fol.Structure LNF}
    (hH : Fol.all_realize_sentence S LiteralHailperinNF) (x y z : S) :
    Mem S z (unorderedPair hH x y) ↔ z = x ∨ z = y := by simp [unorderedPair]

/-- The selected Kuratowski ordered pair. -/
@[expose]
noncomputable def kPair {S : Fol.Structure LNF}
    (hH : Fol.all_realize_sentence S LiteralHailperinNF) (x y : S) : S :=
  unorderedPair hH (singleton hH x) (unorderedPair hH x y)

@[simp]
theorem mem_kPair {S : Fol.Structure LNF}
    (hH : Fol.all_realize_sentence S LiteralHailperinNF) (x y z : S) :
    Mem S z (kPair hH x y) ↔ z = singleton hH x ∨ z = unorderedPair hH x y := by
  simp [kPair]

/-- An element of the carrier extensionally represents a literal class. -/
@[expose]
def RepresentsLiteral {S : Fol.Structure LNF} {n : Nat} (xs : DVec S n)
    (A : LiteralClass n) (a : S) : Prop :=
  ∀ z : S,
    Mem S z a ↔ NFChoice.Compiler.NFCompactLeafSemanticAdapters.LiteralClassSem xs A z

theorem representsLiteral_unique {S : Fol.Structure LNF} {n : Nat} (hExt : Extensional S)
    {xs : DVec S n} {A : LiteralClass n} {a b : S} (ha : RepresentsLiteral xs A a)
    (hb : RepresentsLiteral xs A b) : a = b :=
  hExt a b (fun z => (ha z).trans (hb z).symm)

@[simp]
theorem representsLiteral_setVar {S : Fol.Structure LNF} {n : Nat} (xs : DVec S n)
    (i : Fin n) : RepresentsLiteral xs (.setVar i) (lookup xs i) :=
  by
  intro z
  rfl

theorem representsLiteral_singleton {S : Fol.Structure LNF} {n : Nat}
    (hH : Fol.all_realize_sentence S LiteralHailperinNF) {xs : DVec S n}
    {A : LiteralClass n} {a : S} (ha : RepresentsLiteral xs A a) :
    RepresentsLiteral xs (.singleton A) (singleton hH a) :=
  by
  intro z
  rw [mem_singleton]
  change z = a ↔ RepresentsLiteral xs A z
  constructor
  · rintro rfl
    exact ha
  · intro hz
    exact representsLiteral_unique (extensional_of_literal_model hH) hz ha

theorem representsLiteral_unorderedPair {S : Fol.Structure LNF} {n : Nat}
    (hH : Fol.all_realize_sentence S LiteralHailperinNF) {xs : DVec S n}
    {A B : LiteralClass n} {a b : S} (ha : RepresentsLiteral xs A a)
    (hb : RepresentsLiteral xs B b) :
    RepresentsLiteral xs (.unorderedPair A B) (unorderedPair hH a b) :=
  by
  intro z
  rw [mem_unorderedPair]
  change z = a ∨ z = b ↔ RepresentsLiteral xs A z ∨ RepresentsLiteral xs B z
  constructor
  · rintro (rfl | rfl)
    · exact Or.inl ha
    · exact Or.inr hb
  · rintro (hz | hz)
    · exact Or.inl (representsLiteral_unique (extensional_of_literal_model hH) hz ha)
    · exact Or.inr (representsLiteral_unique (extensional_of_literal_model hH) hz hb)

theorem representsLiteral_kPair {S : Fol.Structure LNF} {n : Nat}
    (hH : Fol.all_realize_sentence S LiteralHailperinNF) {xs : DVec S n}
    {A B : LiteralClass n} {a b : S} (ha : RepresentsLiteral xs A a)
    (hb : RepresentsLiteral xs B b) : RepresentsLiteral xs (.kPair A B) (kPair hH a b) :=
  by
  have hsa := representsLiteral_singleton hH ha
  have hab := representsLiteral_unorderedPair hH ha hb
  intro z
  rw [mem_kPair]
  change
    z = singleton hH a ∨ z = unorderedPair hH a b ↔
      RepresentsLiteral xs (.singleton A) z ∨ RepresentsLiteral xs (.unorderedPair A B) z
  constructor
  · rintro (rfl | rfl)
    · exact Or.inl hsa
    · exact Or.inr hab
  · rintro (hz | hz)
    · exact Or.inl (representsLiteral_unique (extensional_of_literal_model hH) hz hsa)
    · exact Or.inr (representsLiteral_unique (extensional_of_literal_model hH) hz hab)

/-- A literal set-equality formula identifies the canonical representative. -/
theorem formulaHolds_setEqClass_iff_eq {S : Fol.Structure LNF} {n : Nat}
    (hH : Fol.all_realize_sentence S LiteralHailperinNF) (xs : DVec S n) (r : Fin n)
    (A : LiteralClass n) (a : S) (ha : RepresentsLiteral xs A a) :
    FormulaHolds S xs (LiteralClass.setEqClass r A) ↔ lookup xs r = a :=
  by
  rw [formulaHolds_setEqClass]
  constructor
  · intro hr
    exact
      (extensional_of_literal_model hH) (lookup xs r) a
        (fun z => (hr z).trans (ha z).symm)
  · rintro rfl
    exact ha

/-- A literal class-membership formula is membership of its canonical representative. -/
theorem formulaHolds_classMemSet_iff_mem {S : Fol.Structure LNF} {n : Nat}
    (hH : Fol.all_realize_sentence S LiteralHailperinNF) (xs : DVec S n)
    (A : LiteralClass n) (r : Fin n) (a : S) (ha : RepresentsLiteral xs A a) :
    FormulaHolds S xs (LiteralClass.classMemSet A r) ↔ Mem S a (lookup xs r) :=
  by
  rw [formulaHolds_classMemSet]
  constructor
  · rintro ⟨p, hp, hpr⟩
    have hpa : p = a := representsLiteral_unique (extensional_of_literal_model hH) hp ha
    simpa [hpa] using hpr
  · intro har
    exact ⟨a, ha, har⟩

@[simp]
theorem formulaHolds_literalKPair_iff {S : Fol.Structure LNF} {n : Nat}
    (hH : Fol.all_realize_sentence S LiteralHailperinNF) (xs : DVec S n)
    (ip ia ib : Fin n) :
    FormulaHolds S xs (literalKPair ip ia ib) ↔
      lookup xs ip = kPair hH (lookup xs ia) (lookup xs ib) :=
  by
  apply formulaHolds_setEqClass_iff_eq hH
  exact
    representsLiteral_kPair hH (representsLiteral_setVar xs ia)
      (representsLiteral_setVar xs ib)

@[simp]
theorem formulaHolds_literalPairMem_iff {S : Fol.Structure LNF} {n : Nat}
    (hH : Fol.all_realize_sentence S LiteralHailperinNF) (xs : DVec S n)
    (ia ib ir : Fin n) :
    FormulaHolds S xs (literalPairMem ia ib ir) ↔
      Mem S (kPair hH (lookup xs ia) (lookup xs ib)) (lookup xs ir) :=
  by
  apply formulaHolds_classMemSet_iff_mem hH
  exact
    representsLiteral_kPair hH (representsLiteral_setVar xs ia)
      (representsLiteral_setVar xs ib)

@[simp]
theorem formulaHolds_literalSingletonPairMem_iff {S : Fol.Structure LNF} {n : Nat}
    (hH : Fol.all_realize_sentence S LiteralHailperinNF) (xs : DVec S n)
    (ia ib ir : Fin n) :
    FormulaHolds S xs (literalSingletonPairMem ia ib ir) ↔
      Mem S (kPair hH (singleton hH (lookup xs ia)) (singleton hH (lookup xs ib)))
        (lookup xs ir) :=
  by
  apply formulaHolds_classMemSet_iff_mem hH
  exact
    representsLiteral_kPair hH
      (representsLiteral_singleton hH (representsLiteral_setVar xs ia))
      (representsLiteral_singleton hH (representsLiteral_setVar xs ib))

@[simp]
theorem formulaHolds_literalInsertedPairMem_iff {S : Fol.Structure LNF} {n : Nat}
    (hH : Fol.all_realize_sentence S LiteralHailperinNF) (xs : DVec S n)
    (iz iw it ir : Fin n) :
    FormulaHolds S xs (literalInsertedPairMem iz iw it ir) ↔
      Mem S
        (kPair hH (singleton hH (singleton hH (lookup xs iz)))
          (kPair hH (lookup xs iw) (lookup xs it)))
        (lookup xs ir) :=
  by
  apply formulaHolds_classMemSet_iff_mem hH
  exact
    representsLiteral_kPair hH
      (representsLiteral_singleton hH
        (representsLiteral_singleton hH (representsLiteral_setVar xs iz)))
      (representsLiteral_kPair hH (representsLiteral_setVar xs iw)
        (representsLiteral_setVar xs it))

@[simp]
theorem formulaHolds_literalPairSingletonSecondMem_iff {S : Fol.Structure LNF} {n : Nat}
    (hH : Fol.all_realize_sentence S LiteralHailperinNF) (xs : DVec S n)
    (ia iz ir : Fin n) :
    FormulaHolds S xs (literalPairSingletonSecondMem ia iz ir) ↔
      Mem S (kPair hH (lookup xs ia) (singleton hH (lookup xs iz))) (lookup xs ir) :=
  by
  apply formulaHolds_classMemSet_iff_mem hH
  exact
    representsLiteral_kPair hH (representsLiteral_setVar xs ia)
      (representsLiteral_singleton hH (representsLiteral_setVar xs iz))

/-! ### Skolem witnesses for the remaining Hailperin axioms -/


theorem exists_xp {S : Fol.Structure LNF}
    (hH : Fol.all_realize_sentence S LiteralHailperinNF) (x : S) :
    ∃ y : S, ∀ z : S, Mem S z y ↔ ∃ w t : S, z = kPair hH w t ∧ Mem S t x :=
  by
  have h := formulaHolds_literal_axiom hH .axXp
  simpa [literalAxiomSyntax, literalAxXp, FormulaHolds, lookup, DVec.nth,
    formulaHolds_literalKPair_iff hH] using h x

theorem exists_cnv {S : Fol.Structure LNF}
    (hH : Fol.all_realize_sentence S LiteralHailperinNF) (x : S) :
    ∃ y : S, ∀ z w : S, Mem S (kPair hH z w) y ↔ Mem S (kPair hH w z) x :=
  by
  have h := formulaHolds_literal_axiom hH .axCnv
  simpa [literalAxiomSyntax, literalAxCnv, FormulaHolds, lookup, DVec.nth,
    formulaHolds_literalPairMem_iff hH] using h x

theorem exists_oneC {S : Fol.Structure LNF}
    (hH : Fol.all_realize_sentence S LiteralHailperinNF) :
    ∃ x : S, ∀ y : S, Mem S y x ↔ ∃ z : S, ∀ w : S, Mem S w y ↔ w = z :=
  by
  have h := formulaHolds_literal_axiom hH .ax1c
  simpa [literalAxiomSyntax, literalAx1c, Formula.isSomeSingleton, Formula.singleton,
    FormulaHolds, lookup, DVec.nth] using h

theorem exists_sset {S : Fol.Structure LNF}
    (hH : Fol.all_realize_sentence S LiteralHailperinNF) :
    ∃ x : S, ∀ y z : S, Mem S (kPair hH y z) x ↔ ∀ w : S, Mem S w y → Mem S w z :=
  by
  have h := formulaHolds_literal_axiom hH .axSset
  simpa [literalAxiomSyntax, literalAxSset, Formula.subset, FormulaHolds, lookup,
    DVec.nth, formulaHolds_literalPairMem_iff hH] using h

theorem exists_si {S : Fol.Structure LNF}
    (hH : Fol.all_realize_sentence S LiteralHailperinNF) (x : S) :
    ∃ y : S,
      ∀ z w : S,
        Mem S (kPair hH (singleton hH z) (singleton hH w)) y ↔ Mem S (kPair hH z w) x :=
  by
  have h := formulaHolds_literal_axiom hH .axSi
  simpa [literalAxiomSyntax, literalAxSi, FormulaHolds, lookup, DVec.nth,
    formulaHolds_literalSingletonPairMem_iff hH, formulaHolds_literalPairMem_iff hH] using
    h x

theorem exists_ins2 {S : Fol.Structure LNF}
    (hH : Fol.all_realize_sentence S LiteralHailperinNF) (x : S) :
    ∃ y : S,
      ∀ z w t : S,
        Mem S (kPair hH (singleton hH (singleton hH z)) (kPair hH w t)) y ↔
          Mem S (kPair hH z t) x :=
  by
  have h := formulaHolds_literal_axiom hH .axIns2
  simpa [literalAxiomSyntax, literalAxIns2, FormulaHolds, lookup, DVec.nth,
    formulaHolds_literalInsertedPairMem_iff hH, formulaHolds_literalPairMem_iff hH] using
    h x

theorem exists_ins3 {S : Fol.Structure LNF}
    (hH : Fol.all_realize_sentence S LiteralHailperinNF) (x : S) :
    ∃ y : S,
      ∀ z w t : S,
        Mem S (kPair hH (singleton hH (singleton hH z)) (kPair hH w t)) y ↔
          Mem S (kPair hH z w) x :=
  by
  have h := formulaHolds_literal_axiom hH .axIns3
  simpa [literalAxiomSyntax, literalAxIns3, FormulaHolds, lookup, DVec.nth,
    formulaHolds_literalInsertedPairMem_iff hH, formulaHolds_literalPairMem_iff hH] using
    h x

theorem exists_typeLower {S : Fol.Structure LNF}
    (hH : Fol.all_realize_sentence S LiteralHailperinNF) (x : S) :
    ∃ y : S, ∀ z : S, Mem S z y ↔ ∀ w : S, Mem S (kPair hH w (singleton hH z)) x :=
  by
  have h := formulaHolds_literal_axiom hH .axTypeLower
  simpa [literalAxiomSyntax, literalAxTypeLower, FormulaHolds, lookup, DVec.nth,
    formulaHolds_literalPairSingletonSecondMem_iff hH] using h x

/-- Cartesian-product/range constructor selected from `ax-xp`. -/
@[expose]
noncomputable def xp {S : Fol.Structure LNF}
    (hH : Fol.all_realize_sentence S LiteralHailperinNF) (x : S) : S :=
  Classical.choose (exists_xp hH x)

@[simp]
theorem mem_xp {S : Fol.Structure LNF}
    (hH : Fol.all_realize_sentence S LiteralHailperinNF) (x z : S) :
    Mem S z (xp hH x) ↔ ∃ w t : S, z = kPair hH w t ∧ Mem S t x :=
  Classical.choose_spec (exists_xp hH x) z

/-- Converse-relation constructor selected from `ax-cnv`. -/
@[expose]
noncomputable def cnv {S : Fol.Structure LNF}
    (hH : Fol.all_realize_sentence S LiteralHailperinNF) (x : S) : S :=
  Classical.choose (exists_cnv hH x)

@[simp]
theorem mem_cnv {S : Fol.Structure LNF}
    (hH : Fol.all_realize_sentence S LiteralHailperinNF) (x z w : S) :
    Mem S (kPair hH z w) (cnv hH x) ↔ Mem S (kPair hH w z) x :=
  Classical.choose_spec (exists_cnv hH x) z w

/-- The set of all singleton sets selected from `ax-1c`. -/
@[expose]
noncomputable def oneC {S : Fol.Structure LNF}
    (hH : Fol.all_realize_sentence S LiteralHailperinNF) : S :=
  Classical.choose (exists_oneC hH)

@[simp]
theorem mem_oneC {S : Fol.Structure LNF}
    (hH : Fol.all_realize_sentence S LiteralHailperinNF) (y : S) :
    Mem S y (oneC hH) ↔ ∃ z : S, ∀ w : S, Mem S w y ↔ w = z :=
  Classical.choose_spec (exists_oneC hH) y

/-- The subset relation selected from `ax-sset`. -/
@[expose]
noncomputable def sset {S : Fol.Structure LNF}
    (hH : Fol.all_realize_sentence S LiteralHailperinNF) : S :=
  Classical.choose (exists_sset hH)

@[simp]
theorem mem_sset {S : Fol.Structure LNF}
    (hH : Fol.all_realize_sentence S LiteralHailperinNF) (y z : S) :
    Mem S (kPair hH y z) (sset hH) ↔ ∀ w : S, Mem S w y → Mem S w z :=
  Classical.choose_spec (exists_sset hH) y z

/-- Singleton-image relation transformer selected from `ax-si`. -/
@[expose]
noncomputable def si {S : Fol.Structure LNF}
    (hH : Fol.all_realize_sentence S LiteralHailperinNF) (x : S) : S :=
  Classical.choose (exists_si hH x)

@[simp]
theorem mem_si {S : Fol.Structure LNF}
    (hH : Fol.all_realize_sentence S LiteralHailperinNF) (x z w : S) :
    Mem S (kPair hH (singleton hH z) (singleton hH w)) (si hH x) ↔
      Mem S (kPair hH z w) x :=
  Classical.choose_spec (exists_si hH x) z w

/-- Second inserted-pair transformer selected from `ax-ins2`. -/
@[expose]
noncomputable def ins2 {S : Fol.Structure LNF}
    (hH : Fol.all_realize_sentence S LiteralHailperinNF) (x : S) : S :=
  Classical.choose (exists_ins2 hH x)

@[simp]
theorem mem_ins2 {S : Fol.Structure LNF}
    (hH : Fol.all_realize_sentence S LiteralHailperinNF) (x z w t : S) :
    Mem S (kPair hH (singleton hH (singleton hH z)) (kPair hH w t)) (ins2 hH x) ↔
      Mem S (kPair hH z t) x :=
  Classical.choose_spec (exists_ins2 hH x) z w t

/-- Third inserted-pair transformer selected from `ax-ins3`. -/
@[expose]
noncomputable def ins3 {S : Fol.Structure LNF}
    (hH : Fol.all_realize_sentence S LiteralHailperinNF) (x : S) : S :=
  Classical.choose (exists_ins3 hH x)

@[simp]
theorem mem_ins3 {S : Fol.Structure LNF}
    (hH : Fol.all_realize_sentence S LiteralHailperinNF) (x z w t : S) :
    Mem S (kPair hH (singleton hH (singleton hH z)) (kPair hH w t)) (ins3 hH x) ↔
      Mem S (kPair hH z w) x :=
  Classical.choose_spec (exists_ins3 hH x) z w t

/-- Type-lowering transformer selected from `ax-typlower`. -/
@[expose]
noncomputable def typeLower {S : Fol.Structure LNF}
    (hH : Fol.all_realize_sentence S LiteralHailperinNF) (x : S) : S :=
  Classical.choose (exists_typeLower hH x)

@[simp]
theorem mem_typeLower {S : Fol.Structure LNF}
    (hH : Fol.all_realize_sentence S LiteralHailperinNF) (x z : S) :
    Mem S z (typeLower hH x) ↔ ∀ w : S, Mem S (kPair hH w (singleton hH z)) x :=
  Classical.choose_spec (exists_typeLower hH x) z

/-! ### A reusable bundled kernel -/


/-- All semantic operations supplied by Hailperin's finite basis, detached from
the syntactic theory after extraction.  The equations on the four derived
constructors record that no additional choices were made for them.
-/
structure HailperinModel (S : Fol.Structure LNF) where
  extensional : Extensional S
  nin : S → S → S
  mem_nin : ∀ x y z, Mem S z (nin x y) ↔ ¬(Mem S z x ∧ Mem S z y)
  singleton : S → S
  mem_singleton : ∀ x z, Mem S z (singleton x) ↔ z = x
  complement : S → S
  complement_eq : ∀ x, complement x = nin x x
  mem_complement : ∀ x z, Mem S z (complement x) ↔ ¬Mem S z x
  union : S → S → S
  union_eq : ∀ x y, union x y = nin (complement x) (complement y)
  mem_union : ∀ x y z, Mem S z (union x y) ↔ Mem S z x ∨ Mem S z y
  unorderedPair : S → S → S
  unorderedPair_eq : ∀ x y, unorderedPair x y = union (singleton x) (singleton y)
  mem_unorderedPair : ∀ x y z, Mem S z (unorderedPair x y) ↔ z = x ∨ z = y
  kPair : S → S → S
  kPair_eq : ∀ x y, kPair x y = unorderedPair (singleton x) (unorderedPair x y)
  mem_kPair : ∀ x y z, Mem S z (kPair x y) ↔ z = singleton x ∨ z = unorderedPair x y
  xp : S → S
  mem_xp : ∀ x z, Mem S z (xp x) ↔ ∃ w t, z = kPair w t ∧ Mem S t x
  cnv : S → S
  mem_cnv : ∀ x z w, Mem S (kPair z w) (cnv x) ↔ Mem S (kPair w z) x
  oneC : S
  mem_oneC : ∀ y, Mem S y oneC ↔ ∃ z, ∀ w, Mem S w y ↔ w = z
  sset : S
  mem_sset : ∀ y z, Mem S (kPair y z) sset ↔ ∀ w, Mem S w y → Mem S w z
  si : S → S
  mem_si : ∀ x z w, Mem S (kPair (singleton z) (singleton w)) (si x) ↔ Mem S (kPair z w) x
  ins2 : S → S
  mem_ins2 :
    ∀ x z w t,
      Mem S (kPair (singleton (singleton z)) (kPair w t)) (ins2 x) ↔ Mem S (kPair z t) x
  ins3 : S → S
  mem_ins3 :
    ∀ x z w t,
      Mem S (kPair (singleton (singleton z)) (kPair w t)) (ins3 x) ↔ Mem S (kPair z w) x
  typeLower : S → S
  mem_typeLower : ∀ x z, Mem S z (typeLower x) ↔ ∀ w, Mem S (kPair w (singleton z)) x

/-- Extract the complete semantic Skolem kernel from a literal Hailperin model. -/
@[expose]
noncomputable def HailperinModel.ofLiteralModel {S : Fol.Structure LNF}
    (hH : Fol.all_realize_sentence S LiteralHailperinNF) : HailperinModel S
    where
  extensional := extensional_of_literal_model hH
  nin := NFChoice.Foundation.NFStandard.nin hH
  mem_nin := fun x y z => NFChoice.Foundation.NFStandard.mem_nin hH x y z
  singleton := NFChoice.Foundation.NFStandard.singleton hH
  mem_singleton := fun x z => NFChoice.Foundation.NFStandard.mem_singleton hH x z
  complement := NFChoice.Foundation.NFStandard.complement hH
  complement_eq := fun _ => rfl
  mem_complement := fun x z => NFChoice.Foundation.NFStandard.mem_complement hH x z
  union := NFChoice.Foundation.NFStandard.union hH
  union_eq := fun _ _ => rfl
  mem_union := fun x y z => NFChoice.Foundation.NFStandard.mem_union hH x y z
  unorderedPair := NFChoice.Foundation.NFStandard.unorderedPair hH
  unorderedPair_eq := fun _ _ => rfl
  mem_unorderedPair := fun x y z =>
    NFChoice.Foundation.NFStandard.mem_unorderedPair hH x y z
  kPair := NFChoice.Foundation.NFStandard.kPair hH
  kPair_eq := fun _ _ => rfl
  mem_kPair := fun x y z => NFChoice.Foundation.NFStandard.mem_kPair hH x y z
  xp := NFChoice.Foundation.NFStandard.xp hH
  mem_xp := fun x z => NFChoice.Foundation.NFStandard.mem_xp hH x z
  cnv := NFChoice.Foundation.NFStandard.cnv hH
  mem_cnv := fun x z w => NFChoice.Foundation.NFStandard.mem_cnv hH x z w
  oneC := NFChoice.Foundation.NFStandard.oneC hH
  mem_oneC := fun y => NFChoice.Foundation.NFStandard.mem_oneC hH y
  sset := NFChoice.Foundation.NFStandard.sset hH
  mem_sset := fun y z => NFChoice.Foundation.NFStandard.mem_sset hH y z
  si := NFChoice.Foundation.NFStandard.si hH
  mem_si := fun x z w => NFChoice.Foundation.NFStandard.mem_si hH x z w
  ins2 := NFChoice.Foundation.NFStandard.ins2 hH
  mem_ins2 := fun x z w t => NFChoice.Foundation.NFStandard.mem_ins2 hH x z w t
  ins3 := NFChoice.Foundation.NFStandard.ins3 hH
  mem_ins3 := fun x z w t => NFChoice.Foundation.NFStandard.mem_ins3 hH x z w t
  typeLower := NFChoice.Foundation.NFStandard.typeLower hH
  mem_typeLower := fun x z => NFChoice.Foundation.NFStandard.mem_typeLower hH x z


end NFChoice.Foundation.NFStandard
