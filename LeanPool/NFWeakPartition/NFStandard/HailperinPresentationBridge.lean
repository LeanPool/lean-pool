/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NFStandard.HailperinModel
public import LeanPool.NFWeakPartition.NFStandard.TheoryEquivalence

/-! NF weak partition development: NFStandard.HailperinPresentationBridge. -/


public section

namespace NFChoice.Foundation.NFStandard

open scoped Fol
open NFChoice.Foundation.ExactLiteralTrial
open NFChoice.SemanticCore
open NFChoice.SemanticCore.Lowering
open NFChoice.Compiler.NFCompactLeafSemanticAdapters
open NFChoice.Compiler.NFCompactLeafEndpoints

/-! The original foundation file expands class constructors by introducing
intermediate set representatives.  The exact-literal presentation expands the
same constructors extensionally.  The two presentations are equivalent in an
extensional structure once singleton and unordered-pair representatives are
available.  Those representatives are supplied in either presentation by
`ax-sn` and `ax-nin`.
-/


/-- The small common kernel needed to compare the two presentations. -/
structure PresentationKernel (S : Fol.Structure LNF) where
  extensional : Extensional S
  /-- The singleton operation of this NF model presentation. -/
  singleton : S → S
  mem_singleton : ∀ x z, Mem S z (singleton x) ↔ z = x
  /-- The unordered Pair operation of this NF model presentation. -/
  unorderedPair : S → S → S
  mem_unorderedPair : ∀ x y z, Mem S z (unorderedPair x y) ↔ z = x ∨ z = y
  /-- The k Pair operation of this NF model presentation. -/
  kPair : S → S → S
  kPair_eq : ∀ x y, kPair x y = unorderedPair (singleton x) (unorderedPair x y)
  mem_kPair : ∀ x y z, Mem S z (kPair x y) ↔ z = singleton x ∨ z = unorderedPair x y

namespace PresentationKernel

variable {S : Fol.Structure LNF} (K : PresentationKernel S)

/-! ### The existential-intermediate presentation -/


theorem formulaHolds_singleton_iff {n : Nat} (xs : DVec S n) (is ia : Fin n) :
    FormulaHolds S xs (Formula.singleton is ia) ↔
      lookup xs is = K.singleton (lookup xs ia) :=
  by
  simp only [Formula.singleton, FormulaHolds, formulaHolds_biimp, lookup_cons_zero,
    lookup_cons_succ]
  change (∀ z : S, Mem S z (lookup xs is) ↔ z = lookup xs ia) ↔ _
  constructor
  · intro h
    exact K.extensional _ _ (fun z => (h z).trans (K.mem_singleton _ z).symm)
  · intro h
    rw [h]
    exact K.mem_singleton _

theorem formulaHolds_unorderedPair_iff {n : Nat} (xs : DVec S n) (ip ia ib : Fin n) :
    FormulaHolds S xs (Formula.unorderedPair ip ia ib) ↔
      lookup xs ip = K.unorderedPair (lookup xs ia) (lookup xs ib) :=
  by
  simp only [Formula.unorderedPair, FormulaHolds, formulaHolds_biimp, Formula.disj,
    Formula.neg, lookup_cons_zero, lookup_cons_succ]
  constructor
  · intro h
    apply K.extensional
    intro z
    have hdisj :
      ((z = lookup xs ia → False) → z = lookup xs ib) ↔
        z = lookup xs ia ∨ z = lookup xs ib :=
      by tauto
    exact (h z).trans (hdisj.trans (K.mem_unorderedPair _ _ z).symm)
  · intro h
    rw [h]
    intro z
    rw [K.mem_unorderedPair]
    tauto

theorem formulaHolds_isKPair_iff {n : Nat} (xs : DVec S n) (ip ia ib : Fin n) :
    FormulaHolds S xs (Formula.isKPair ip ia ib) ↔
      lookup xs ip = K.kPair (lookup xs ia) (lookup xs ib) :=
  by
  simp only [Formula.isKPair, formulaHolds_ex, formulaHolds_conj,
    K.formulaHolds_singleton_iff, K.formulaHolds_unorderedPair_iff, lookup_cons_zero,
    lookup_cons_succ]
  simp [K.kPair_eq, lookup, DVec.nth]

theorem formulaHolds_equalKPair_iff {n : Nat} (xs : DVec S n) (iz ia ib : Fin n) :
    FormulaHolds S xs (Formula.equalKPair iz ia ib) ↔
      lookup xs iz = K.kPair (lookup xs ia) (lookup xs ib) :=
  by simp [Formula.equalKPair, K.formulaHolds_isKPair_iff, FormulaHolds, lookup, DVec.nth]

theorem formulaHolds_pairMem_iff {n : Nat} (xs : DVec S n) (ia ib ir : Fin n) :
    FormulaHolds S xs (Formula.pairMem ia ib ir) ↔
      Mem S (K.kPair (lookup xs ia) (lookup xs ib)) (lookup xs ir) :=
  by simp [Formula.pairMem, K.formulaHolds_isKPair_iff, FormulaHolds, lookup, DVec.nth]

theorem formulaHolds_doubleSingleton_iff {n : Nat} (xs : DVec S n) (id ia : Fin n) :
    FormulaHolds S xs (Formula.doubleSingleton id ia) ↔
      lookup xs id = K.singleton (K.singleton (lookup xs ia)) :=
  by simp [Formula.doubleSingleton, K.formulaHolds_singleton_iff, lookup, DVec.nth]

theorem formulaHolds_singletonPairMem_iff {n : Nat} (xs : DVec S n) (ia ib ir : Fin n) :
    FormulaHolds S xs (Formula.singletonPairMem ia ib ir) ↔
      Mem S (K.kPair (K.singleton (lookup xs ia)) (K.singleton (lookup xs ib)))
        (lookup xs ir) :=
  by
  simp [Formula.singletonPairMem, K.formulaHolds_singleton_iff,
    K.formulaHolds_pairMem_iff, lookup, DVec.nth]

theorem formulaHolds_insertedPairMem_iff {n : Nat} (xs : DVec S n) (iz iw it ir : Fin n) :
    FormulaHolds S xs (Formula.insertedPairMem iz iw it ir) ↔
      Mem S
        (K.kPair (K.singleton (K.singleton (lookup xs iz)))
          (K.kPair (lookup xs iw) (lookup xs it)))
        (lookup xs ir) :=
  by
  simp [Formula.insertedPairMem, K.formulaHolds_doubleSingleton_iff,
    K.formulaHolds_isKPair_iff, K.formulaHolds_pairMem_iff, lookup, DVec.nth]

theorem formulaHolds_pairSingletonSecondMem_iff {n : Nat} (xs : DVec S n)
    (ia iz ir : Fin n) :
    FormulaHolds S xs (Formula.pairSingletonSecondMem ia iz ir) ↔
      Mem S (K.kPair (lookup xs ia) (K.singleton (lookup xs iz))) (lookup xs ir) :=
  by
  simp [Formula.pairSingletonSecondMem, K.formulaHolds_singleton_iff,
    K.formulaHolds_pairMem_iff, lookup, DVec.nth]

/-! ### The exact-literal presentation -/


theorem representsLiteral_singleton_ofKernel {n : Nat} {xs : DVec S n}
    {A : LiteralClass n} {a : S} (ha : RepresentsLiteral xs A a) :
    RepresentsLiteral xs (.singleton A) (K.singleton a) :=
  by
  intro z
  rw [K.mem_singleton]
  change z = a ↔ RepresentsLiteral xs A z
  constructor
  · rintro rfl
    exact ha
  · intro hz
    exact K.extensional _ _ (fun u => (hz u).trans (ha u).symm)

theorem representsLiteral_unorderedPair_ofKernel {n : Nat} {xs : DVec S n}
    {A B : LiteralClass n} {a b : S} (ha : RepresentsLiteral xs A a)
    (hb : RepresentsLiteral xs B b) :
    RepresentsLiteral xs (.unorderedPair A B) (K.unorderedPair a b) :=
  by
  intro z
  rw [K.mem_unorderedPair]
  change z = a ∨ z = b ↔ RepresentsLiteral xs A z ∨ RepresentsLiteral xs B z
  constructor
  · rintro (rfl | rfl)
    · exact Or.inl ha
    · exact Or.inr hb
  · rintro (hz | hz)
    · exact Or.inl (K.extensional _ _ (fun u => (hz u).trans (ha u).symm))
    · exact Or.inr (K.extensional _ _ (fun u => (hz u).trans (hb u).symm))

theorem representsLiteral_kPair_ofKernel {n : Nat} {xs : DVec S n} {A B : LiteralClass n}
    {a b : S} (ha : RepresentsLiteral xs A a) (hb : RepresentsLiteral xs B b) :
    RepresentsLiteral xs (.kPair A B) (K.kPair a b) :=
  by
  have hsa := K.representsLiteral_singleton_ofKernel ha
  have hab := K.representsLiteral_unorderedPair_ofKernel ha hb
  intro z
  rw [K.mem_kPair]
  change
    z = K.singleton a ∨ z = K.unorderedPair a b ↔
      RepresentsLiteral xs (.singleton A) z ∨ RepresentsLiteral xs (.unorderedPair A B) z
  constructor
  · rintro (rfl | rfl)
    · exact Or.inl hsa
    · exact Or.inr hab
  · rintro (hz | hz)
    · exact Or.inl (K.extensional _ _ (fun u => (hz u).trans (hsa u).symm))
    · exact Or.inr (K.extensional _ _ (fun u => (hz u).trans (hab u).symm))

theorem formulaHolds_setEqClass_iff_eq_ofKernel (K : PresentationKernel S) {n : Nat}
    (xs : DVec S n) (r : Fin n) (A : LiteralClass n) (a : S)
    (ha : RepresentsLiteral xs A a) :
    FormulaHolds S xs (LiteralClass.setEqClass r A) ↔ lookup xs r = a :=
  by
  rw [formulaHolds_setEqClass]
  constructor
  · intro hr
    exact K.extensional _ _ (fun z => (hr z).trans (ha z).symm)
  · rintro rfl
    exact ha

theorem formulaHolds_classMemSet_iff_mem_ofKernel (K : PresentationKernel S) {n : Nat}
    (xs : DVec S n) (A : LiteralClass n) (r : Fin n) (a : S)
    (ha : RepresentsLiteral xs A a) :
    FormulaHolds S xs (LiteralClass.classMemSet A r) ↔ Mem S a (lookup xs r) :=
  by
  rw [formulaHolds_classMemSet]
  constructor
  · rintro ⟨p, hp, hpr⟩
    have hpa : p = a := K.extensional _ _ (fun z => (hp z).trans (ha z).symm)
    simpa [hpa] using hpr
  · intro har
    exact ⟨a, ha, har⟩

theorem formulaHolds_literalKPair_iff_kernel {n : Nat} (xs : DVec S n)
    (ip ia ib : Fin n) :
    FormulaHolds S xs (literalKPair ip ia ib) ↔
      lookup xs ip = K.kPair (lookup xs ia) (lookup xs ib) :=
  by
  apply K.formulaHolds_setEqClass_iff_eq_ofKernel
  exact
    K.representsLiteral_kPair_ofKernel (representsLiteral_setVar xs ia)
      (representsLiteral_setVar xs ib)

theorem formulaHolds_literalPairMem_iff_kernel {n : Nat} (xs : DVec S n)
    (ia ib ir : Fin n) :
    FormulaHolds S xs (literalPairMem ia ib ir) ↔
      Mem S (K.kPair (lookup xs ia) (lookup xs ib)) (lookup xs ir) :=
  by
  apply K.formulaHolds_classMemSet_iff_mem_ofKernel
  exact
    K.representsLiteral_kPair_ofKernel (representsLiteral_setVar xs ia)
      (representsLiteral_setVar xs ib)

theorem formulaHolds_literalSingletonPairMem_iff_kernel {n : Nat} (xs : DVec S n)
    (ia ib ir : Fin n) :
    FormulaHolds S xs (literalSingletonPairMem ia ib ir) ↔
      Mem S (K.kPair (K.singleton (lookup xs ia)) (K.singleton (lookup xs ib)))
        (lookup xs ir) :=
  by
  apply K.formulaHolds_classMemSet_iff_mem_ofKernel
  exact
    K.representsLiteral_kPair_ofKernel
      (K.representsLiteral_singleton_ofKernel (representsLiteral_setVar xs ia))
      (K.representsLiteral_singleton_ofKernel (representsLiteral_setVar xs ib))

theorem formulaHolds_literalInsertedPairMem_iff_kernel {n : Nat} (xs : DVec S n)
    (iz iw it ir : Fin n) :
    FormulaHolds S xs (literalInsertedPairMem iz iw it ir) ↔
      Mem S
        (K.kPair (K.singleton (K.singleton (lookup xs iz)))
          (K.kPair (lookup xs iw) (lookup xs it)))
        (lookup xs ir) :=
  by
  apply K.formulaHolds_classMemSet_iff_mem_ofKernel
  exact
    K.representsLiteral_kPair_ofKernel
      (K.representsLiteral_singleton_ofKernel
        (K.representsLiteral_singleton_ofKernel (representsLiteral_setVar xs iz)))
      (K.representsLiteral_kPair_ofKernel (representsLiteral_setVar xs iw)
        (representsLiteral_setVar xs it))

theorem formulaHolds_literalPairSingletonSecondMem_iff_kernel {n : Nat} (xs : DVec S n)
    (ia iz ir : Fin n) :
    FormulaHolds S xs (literalPairSingletonSecondMem ia iz ir) ↔
      Mem S (K.kPair (lookup xs ia) (K.singleton (lookup xs iz))) (lookup xs ir) :=
  by
  apply K.formulaHolds_classMemSet_iff_mem_ofKernel
  exact
    K.representsLiteral_kPair_ofKernel (representsLiteral_setVar xs ia)
      (K.representsLiteral_singleton_ofKernel (representsLiteral_setVar xs iz))

end PresentationKernel

/-! ### Extracting the common kernel from the original presentation -/


/-- Realize a named axiom from the original foundation theory. -/
theorem realizes_foundation_axiom {S : Fol.Structure LNF}
    (hH : Fol.allRealizeSentence S HailperinNF) (name : HailperinAxiomName) :
    Fol.realizeSentence S (axiomFormula name) :=
  hH (axiom_mem_HailperinNF name)

/-- Intrinsic semantic form of an original foundation axiom. -/
theorem formulaHolds_foundation_axiom {S : Fol.Structure LNF}
    (hH : Fol.allRealizeSentence S HailperinNF) (name : HailperinAxiomName) :
    FormulaHolds S DVec.nil (axiomSyntax name) :=
  (formulaHolds_toFlypitch DVec.nil (axiomSyntax name)).2
    (realizes_foundation_axiom hH name)

theorem foundation_model_extensional {S : Fol.Structure LNF}
    (hH : Fol.allRealizeSentence S HailperinNF) : Extensional S :=
  (extensional_iff_foundation_axExt S).2 (realizes_foundation_axiom hH .axExt)

theorem foundation_exists_nin {S : Fol.Structure LNF}
    (hH : Fol.allRealizeSentence S HailperinNF) (x y : S) :
    ∃ a : S, ∀ z : S, Mem S z a ↔ ¬(Mem S z x ∧ Mem S z y) :=
  by
  have h := formulaHolds_foundation_axiom hH .axNin
  simpa [axiomSyntax, axNin, FormulaHolds, lookup, DVec.nth] using h x y

/-- Standard-NF model or stratification construction identified upstream as `foundationNin`. -/
@[expose]
noncomputable def foundationNin {S : Fol.Structure LNF}
    (hH : Fol.allRealizeSentence S HailperinNF) (x y : S) : S :=
  Classical.choose (foundation_exists_nin hH x y)

@[simp]
theorem mem_foundationNin {S : Fol.Structure LNF}
    (hH : Fol.allRealizeSentence S HailperinNF) (x y z : S) :
    Mem S z (foundationNin hH x y) ↔ ¬(Mem S z x ∧ Mem S z y) :=
  Classical.choose_spec (foundation_exists_nin hH x y) z

theorem foundation_exists_singleton {S : Fol.Structure LNF}
    (hH : Fol.allRealizeSentence S HailperinNF) (x : S) :
    ∃ a : S, ∀ z : S, Mem S z a ↔ z = x :=
  by
  have h := formulaHolds_foundation_axiom hH .axSn
  simpa [axiomSyntax, axSn, FormulaHolds, lookup, DVec.nth] using h x

/-- Standard-NF model or stratification construction identified upstream as
`foundationSingleton`.
-/
@[expose]
noncomputable def foundationSingleton {S : Fol.Structure LNF}
    (hH : Fol.allRealizeSentence S HailperinNF) (x : S) : S :=
  Classical.choose (foundation_exists_singleton hH x)

@[simp]
theorem mem_foundationSingleton {S : Fol.Structure LNF}
    (hH : Fol.allRealizeSentence S HailperinNF) (x z : S) :
    Mem S z (foundationSingleton hH x) ↔ z = x :=
  Classical.choose_spec (foundation_exists_singleton hH x) z

/-- Standard-NF model or stratification construction identified upstream as
`foundationComplement`.
-/
@[expose]
noncomputable def foundationComplement {S : Fol.Structure LNF}
    (hH : Fol.allRealizeSentence S HailperinNF) (x : S) : S :=
  foundationNin hH x x

@[simp]
theorem mem_foundationComplement {S : Fol.Structure LNF}
    (hH : Fol.allRealizeSentence S HailperinNF) (x z : S) :
    Mem S z (foundationComplement hH x) ↔ ¬Mem S z x := by simp [foundationComplement]

/-- Standard-NF model or stratification construction identified upstream as `foundationUnion`. -/
@[expose]
noncomputable def foundationUnion {S : Fol.Structure LNF}
    (hH : Fol.allRealizeSentence S HailperinNF) (x y : S) : S :=
  foundationNin hH (foundationComplement hH x) (foundationComplement hH y)

@[simp]
theorem mem_foundationUnion {S : Fol.Structure LNF}
    (hH : Fol.allRealizeSentence S HailperinNF) (x y z : S) :
    Mem S z (foundationUnion hH x y) ↔ Mem S z x ∨ Mem S z y :=
  by
  simp [foundationUnion]
  tauto

/-- Standard-NF model or stratification construction identified upstream as
`foundationUnorderedPair`.
-/
@[expose]
noncomputable def foundationUnorderedPair {S : Fol.Structure LNF}
    (hH : Fol.allRealizeSentence S HailperinNF) (x y : S) : S :=
  foundationUnion hH (foundationSingleton hH x) (foundationSingleton hH y)

@[simp]
theorem mem_foundationUnorderedPair {S : Fol.Structure LNF}
    (hH : Fol.allRealizeSentence S HailperinNF) (x y z : S) :
    Mem S z (foundationUnorderedPair hH x y) ↔ z = x ∨ z = y := by
  simp [foundationUnorderedPair]

/-- Standard-NF model or stratification construction identified upstream as `foundationKPair`. -/
@[expose]
noncomputable def foundationKPair {S : Fol.Structure LNF}
    (hH : Fol.allRealizeSentence S HailperinNF) (x y : S) : S :=
  foundationUnorderedPair hH (foundationSingleton hH x) (foundationUnorderedPair hH x y)

@[simp]
theorem mem_foundationKPair {S : Fol.Structure LNF}
    (hH : Fol.allRealizeSentence S HailperinNF) (x y z : S) :
    Mem S z (foundationKPair hH x y) ↔
      z = foundationSingleton hH x ∨ z = foundationUnorderedPair hH x y :=
  by simp [foundationKPair]

/-- Standard-NF model or stratification construction identified upstream as
`PresentationKernel.ofFoundationModel`.
-/
@[expose]
noncomputable def PresentationKernel.ofFoundationModel {S : Fol.Structure LNF}
    (hH : Fol.allRealizeSentence S HailperinNF) : PresentationKernel S
    where
  extensional := foundation_model_extensional hH
  singleton := foundationSingleton hH
  mem_singleton := mem_foundationSingleton hH
  unorderedPair := foundationUnorderedPair hH
  mem_unorderedPair := mem_foundationUnorderedPair hH
  kPair := foundationKPair hH
  kPair_eq := fun _ _ => rfl
  mem_kPair := mem_foundationKPair hH

/-- Standard-NF model or stratification construction identified upstream as
`PresentationKernel.ofLiteralModel`.
-/
@[expose]
noncomputable def PresentationKernel.ofLiteralModel {S : Fol.Structure LNF}
    (hH : Fol.allRealizeSentence S LiteralHailperinNF) : PresentationKernel S :=
  by
  let H := HailperinModel.ofLiteralModel hH
  exact
    { extensional := H.extensional
      singleton := H.singleton
      mem_singleton := H.mem_singleton
      unorderedPair := H.unorderedPair
      mem_unorderedPair := H.mem_unorderedPair
      kPair := H.kPair
      kPair_eq := H.kPair_eq
      mem_kPair := H.mem_kPair }

/-! ### Axiom-by-axiom and theory-level equivalence -/


/-- Each named original axiom has the same semantics as its literal expansion. -/
theorem formulaHolds_axiomSyntax_iff_literal {S : Fol.Structure LNF}
    (K : PresentationKernel S) (name : HailperinAxiomName) :
    FormulaHolds S DVec.nil (axiomSyntax name) ↔
      FormulaHolds S DVec.nil (literalAxiomSyntax name) :=
  by
  cases name <;>
    simp [axiomSyntax, literalAxiomSyntax, axExt, axNin, axXp, axCnv, ax1c, axSset, axSi,
      axIns2, axIns3, axTypeLower, axSn, literalAxExt, literalAxNin, literalAxXp,
      literalAxCnv, literalAx1c, literalAxSset, literalAxSi, literalAxIns2, literalAxIns3,
      literalAxTypeLower, literalAxSn, FormulaHolds, K.formulaHolds_equalKPair_iff,
      K.formulaHolds_pairMem_iff, K.formulaHolds_singletonPairMem_iff,
      K.formulaHolds_insertedPairMem_iff, K.formulaHolds_pairSingletonSecondMem_iff,
      K.formulaHolds_literalKPair_iff_kernel, K.formulaHolds_literalPairMem_iff_kernel,
      K.formulaHolds_literalSingletonPairMem_iff_kernel,
      K.formulaHolds_literalInsertedPairMem_iff_kernel,
      K.formulaHolds_literalPairSingletonSecondMem_iff_kernel]

/-- Every model of the original presentation is a model of the literal one. -/
theorem foundationModel_to_literalModel {S : Fol.Structure LNF}
    (hH : Fol.allRealizeSentence S HailperinNF) :
    Fol.allRealizeSentence S LiteralHailperinNF :=
  by
  intro f hf
  rcases hf with ⟨name, rfl⟩
  apply (formulaHolds_toFlypitch DVec.nil (literalAxiomSyntax name)).1
  exact
    (formulaHolds_axiomSyntax_iff_literal (PresentationKernel.ofFoundationModel hH) name).1
      (formulaHolds_foundation_axiom hH name)

/-- Every model of the literal presentation is a model of the original one. -/
theorem literalModel_to_foundationModel {S : Fol.Structure LNF}
    (hH : Fol.allRealizeSentence S LiteralHailperinNF) :
    Fol.allRealizeSentence S HailperinNF :=
  by
  intro f hf
  rcases hf with ⟨name, rfl⟩
  apply (formulaHolds_toFlypitch DVec.nil (axiomSyntax name)).1
  exact
    (formulaHolds_axiomSyntax_iff_literal (PresentationKernel.ofLiteralModel hH) name).2
      (formulaHolds_literal_axiom hH name)

/-- The two finite Hailperin presentations have exactly the same models. -/
theorem hailperinPresentation_models_iff (S : Fol.Structure LNF) :
    Fol.allRealizeSentence S HailperinNF ↔
      Fol.allRealizeSentence S LiteralHailperinNF :=
  ⟨foundationModel_to_literalModel, literalModel_to_foundationModel⟩

/-- Hence the two presentations have exactly the same formal consequences. -/
theorem hailperinPresentation_deductivelyEquivalent :
    DeductivelyEquivalent HailperinNF LiteralHailperinNF :=
  deductivelyEquivalent_of_models_iff hailperinPresentation_models_iff


end NFChoice.Foundation.NFStandard
