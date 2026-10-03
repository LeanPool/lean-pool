/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NFStandard.Basic
public import LeanPool.NFWeakPartition.NFCompactLeafEndpoints
public import Mathlib.Data.Fin.VecNotation

/-! NF weak partition development: NFStandard.ToHailperin. -/


public section

namespace NFChoice.Foundation.NFStandard

open scoped Fol
open NFChoice.Foundation.ExactLiteralTrial
open NFChoice.SemanticCore
open NFChoice.SemanticCore.Lowering
open NFChoice.Compiler.NFCompactLeafSemanticAdapters
open NFChoice.Compiler.NFCompactLeafEndpoints

/-! This file proves the finite, semantic half of the equivalence between the
ordinary NF axioms and Hailperin's eleven-axiom presentation.  The class
notation in the literal Hailperin sentences is extensional notation, so the
only substantive shared construction is the usual Kuratowski ordered pair.
-/


section Constructors

variable {S : Fol.Structure LNF} (hNF : Fol.all_realize_sentence S NF)

/-- The stratified predicate defining a singleton with one parameter. -/
@[expose]
def singletonPred : Formula 2 :=
  .equal 0 1

theorem singletonPred_stratified : singletonPred.Stratified :=
  by
  refine ⟨fun _ => 0, ?_⟩
  rfl

/-- The stratified predicate defining an unordered pair with two parameters. -/
@[expose]
def unorderedPairPred : Formula 3 :=
  Formula.disj (.equal 0 1) (.equal 0 2)

theorem unorderedPairPred_stratified : unorderedPairPred.Stratified :=
  by
  refine ⟨fun _ => 0, ?_⟩
  simp [unorderedPairPred, Formula.disj, Formula.neg, Formula.StratifiedBy]

/-- A chosen singleton supplied by NF comprehension. -/
@[expose]
noncomputable def singletonObj (a : S) : S :=
  Classical.choose
    (nf_comprehension hNF singletonPred singletonPred_stratified (DVec.cons a DVec.nil))

@[simp]
theorem mem_singletonObj (a z : S) : Mem S z (singletonObj hNF a) ↔ z = a := by
  exact
    (Classical.choose_spec
      (nf_comprehension hNF singletonPred singletonPred_stratified (DVec.cons a DVec.nil)) z)

/-- A chosen unordered pair supplied by NF comprehension. -/
@[expose]
noncomputable def unorderedPairObj (a b : S) : S :=
  Classical.choose
    (nf_comprehension hNF unorderedPairPred unorderedPairPred_stratified
      (DVec.cons a (DVec.cons b DVec.nil)))

@[simp]
theorem mem_unorderedPairObj (a b z : S) :
    Mem S z (unorderedPairObj hNF a b) ↔ z = a ∨ z = b := by
  simpa [unorderedPairObj, unorderedPairPred, FormulaHolds, lookup, DVec.nth,
    NFChoice.Compiler.NFCompactLeafSemanticAdapters.formulaHolds_disj] using
    (Classical.choose_spec (nf_comprehension hNF unorderedPairPred unorderedPairPred_stratified
        (DVec.cons a (DVec.cons b DVec.nil))) z)

/-- The Kuratowski ordered pair `{{a},{a,b}}`. -/
@[expose]
noncomputable def kPairObj (a b : S) : S :=
  unorderedPairObj hNF (singletonObj hNF a) (unorderedPairObj hNF a b)

@[simp]
theorem mem_kPairObj (a b z : S) :
    Mem S z (kPairObj hNF a b) ↔ z = singletonObj hNF a ∨ z = unorderedPairObj hNF a b :=
  by exact mem_unorderedPairObj hNF _ _ _

theorem singletonObj_injective : Function.Injective (singletonObj hNF) :=
  by
  intro a b hab
  have ha : Mem S a (singletonObj hNF b) :=
    by
    rw [← hab]
    simp
  simpa using ha

theorem unorderedPairObj_eq_iff (a b c d : S) :
    unorderedPairObj hNF a b = unorderedPairObj hNF c d ↔
      (a = c ∧ b = d) ∨ (a = d ∧ b = c) :=
  by
  constructor
  · intro h
    have hset : ({ a, b } : Set S) = { c, d } :=
      by
      ext z
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      rw [← mem_unorderedPairObj hNF a b z, ← mem_unorderedPairObj hNF c d z, h]
    exact Set.pair_eq_pair_iff.mp hset
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rfl
    · apply nf_extensional hNF
      intro z
      simp [or_comm]

theorem singletonObj_eq_unorderedPairObj_iff (a b c : S) :
    singletonObj hNF a = unorderedPairObj hNF b c ↔ b = a ∧ c = a :=
  by
  constructor
  · intro h
    constructor
    · have hb : Mem S b (singletonObj hNF a) :=
        by
        rw [h]
        simp
      simpa using hb
    · have hc : Mem S c (singletonObj hNF a) :=
        by
        rw [h]
        simp
      simpa using hc
  · rintro ⟨rfl, rfl⟩
    apply nf_extensional hNF
    intro z
    simp

theorem kPairObj_injective {a b c d : S} (h : kPairObj hNF a b = kPairObj hNF c d) :
    a = c ∧ b = d :=
  by
  have hout :=
    (unorderedPairObj_eq_iff hNF (singletonObj hNF a) (unorderedPairObj hNF a b)
          (singletonObj hNF c) (unorderedPairObj hNF c d)).mp
      h
  rcases hout with hdirect | hcross
  · rcases hdirect with ⟨hs, hp⟩
    have hac : a = c := singletonObj_injective hNF hs
    rcases (unorderedPairObj_eq_iff hNF a b c d).mp hp with hp' | hp'
    · exact hp'
    · rcases hp' with ⟨had, hbc⟩
      exact ⟨hac, hbc.trans (hac.symm.trans had)⟩
  · rcases hcross with ⟨hs, hp⟩
    have hcd : c = a ∧ d = a := (singletonObj_eq_unorderedPairObj_iff hNF a c d).mp hs
    have hab : a = c ∧ b = c :=
      (singletonObj_eq_unorderedPairObj_iff hNF c a b).mp hp.symm
    exact ⟨hab.1, hab.2.trans (hcd.1.trans hcd.2.symm)⟩

end Constructors

section LiteralClasses

variable {S : Fol.Structure LNF} (hNF : Fol.all_realize_sentence S NF)

/-- The actual set denoted by an exact literal class expression in an NF model. -/
@[expose]
noncomputable def evalLiteralClass {n : Nat} (xs : DVec S n) : LiteralClass n → S
  | .setVar i => lookup xs i
  | .singleton A => singletonObj hNF (evalLiteralClass xs A)
  | .unorderedPair A B =>
    unorderedPairObj hNF (evalLiteralClass xs A) (evalLiteralClass xs B)
  | .kPair A B => kPairObj hNF (evalLiteralClass xs A) (evalLiteralClass xs B)

/-- Literal class semantics is membership in its canonically represented set. -/
theorem literalClassSem_iff_mem_eval {n : Nat} (xs : DVec S n) (A : LiteralClass n)
    (z : S) : LiteralClassSem xs A z ↔ Mem S z (evalLiteralClass hNF xs A) := by
  induction A generalizing z with
  | setVar i => rfl
  | singleton A
    ih =>
    simp only [LiteralClassSem, evalLiteralClass, mem_singletonObj]
    constructor
    · intro hz
      apply nf_extensional hNF
      intro u
      exact (hz u).trans (ih u)
    · intro hza
      subst z
      intro u
      exact (ih u).symm
  | unorderedPair A B ihA
    ihB =>
    simp only [LiteralClassSem, evalLiteralClass, mem_unorderedPairObj]
    constructor
    · rintro (hz | hz)
      · left
        apply nf_extensional hNF
        intro u
        exact (hz u).trans (ihA u)
      · right
        apply nf_extensional hNF
        intro u
        exact (hz u).trans (ihB u)
    · rintro (rfl | rfl)
      · left
        intro u
        exact (ihA u).symm
      · right
        intro u
        exact (ihB u).symm
  | kPair A B ihA
    ihB =>
    simp only [LiteralClassSem, evalLiteralClass, mem_kPairObj]
    have repA :
      ∀ u : S,
        (∀ e : S, Mem S e u ↔ LiteralClassSem xs A e) ↔ u = evalLiteralClass hNF xs A :=
      by
      intro u
      constructor
      · intro hu
        apply nf_extensional hNF
        intro e
        exact (hu e).trans (ihA e)
      · rintro rfl
        intro e
        exact (ihA e).symm
    have repB :
      ∀ u : S,
        (∀ e : S, Mem S e u ↔ LiteralClassSem xs B e) ↔ u = evalLiteralClass hNF xs B :=
      by
      intro u
      constructor
      · intro hu
        apply nf_extensional hNF
        intro e
        exact (hu e).trans (ihB e)
      · rintro rfl
        intro e
        exact (ihB e).symm
    constructor
    · rintro (hz | hz)
      · left
        apply nf_extensional hNF
        intro u
        exact (hz u).trans ((repA u).trans (mem_singletonObj hNF _ _).symm)
      · right
        apply nf_extensional hNF
        intro u
        exact
          (hz u).trans
            ((or_congr (repA u) (repB u)).trans (mem_unorderedPairObj hNF _ _ _).symm)
    · rintro (rfl | rfl)
      · left
        intro u
        exact (mem_singletonObj hNF _ _).trans (repA u).symm
      · right
        intro u
        exact
          (mem_unorderedPairObj hNF _ _ _).trans (or_congr (repA u).symm (repB u).symm)

theorem formulaHolds_setEqClass_iff {n : Nat} (xs : DVec S n) (r : Fin n)
    (A : LiteralClass n) :
    FormulaHolds S xs (LiteralClass.setEqClass r A) ↔
      lookup xs r = evalLiteralClass hNF xs A :=
  by
  rw [formulaHolds_setEqClass]
  constructor
  · intro hr
    apply nf_extensional hNF
    intro z
    exact (hr z).trans (literalClassSem_iff_mem_eval hNF xs A z)
  · intro h z
    rw [h]
    exact (literalClassSem_iff_mem_eval hNF xs A z).symm

theorem formulaHolds_classMemSet_iff {n : Nat} (xs : DVec S n) (A : LiteralClass n)
    (r : Fin n) :
    FormulaHolds S xs (LiteralClass.classMemSet A r) ↔
      Mem S (evalLiteralClass hNF xs A) (lookup xs r) :=
  by
  rw [formulaHolds_classMemSet]
  constructor
  · rintro ⟨p, hp, hpr⟩
    have hpe : p = evalLiteralClass hNF xs A :=
      by
      apply nf_extensional hNF
      intro z
      exact (hp z).trans (literalClassSem_iff_mem_eval hNF xs A z)
    simpa [hpe] using hpr
  · intro h
    refine ⟨evalLiteralClass hNF xs A, ?_, h⟩
    intro z
    exact (literalClassSem_iff_mem_eval hNF xs A z).symm

end LiteralClasses

section StratificationSupport

theorem stratifiedBy_conj_iff {n : Nat} (ty : Fin n → Int) (p q : Formula n) :
    Formula.StratifiedBy ty (Formula.conj p q) ↔
      Formula.StratifiedBy ty p ∧ Formula.StratifiedBy ty q :=
  by simp [Formula.conj, Formula.neg, Formula.StratifiedBy]

theorem stratifiedBy_disj_iff {n : Nat} (ty : Fin n → Int) (p q : Formula n) :
    Formula.StratifiedBy ty (Formula.disj p q) ↔
      Formula.StratifiedBy ty p ∧ Formula.StratifiedBy ty q :=
  by simp [Formula.disj, Formula.neg, Formula.StratifiedBy]

theorem stratifiedBy_biimp_iff {n : Nat} (ty : Fin n → Int) (p q : Formula n) :
    Formula.StratifiedBy ty (Formula.biimp p q) ↔
      Formula.StratifiedBy ty p ∧ Formula.StratifiedBy ty q :=
  by
  simp [Formula.biimp, stratifiedBy_conj_iff, Formula.StratifiedBy]
  tauto

theorem stratifiedBy_ex_iff {n : Nat} (ty : Fin n → Int) (p : Formula (n + 1)) :
    Formula.StratifiedBy ty (Formula.ex p) ↔
      ∃ k : Int, Formula.StratifiedBy (Fin.cases k ty) p :=
  by simp [Formula.ex, Formula.neg, Formula.StratifiedBy]

theorem stratifiedBy_renameVars {n m : Nat} (rho : Fin n → Fin m) (smallTy : Fin n → Int)
    (largeTy : Fin m → Int) (hTy : ∀ i, largeTy (rho i) = smallTy i) (p : Formula n)
    (hp : Formula.StratifiedBy smallTy p) :
    Formula.StratifiedBy largeTy (ExactLiteralTrial.Formula.renameVars rho p) := by
  induction p generalizing m largeTy with
  | falsum => trivial
  | equal i j =>
    simpa [ExactLiteralTrial.Formula.renameVars, Formula.StratifiedBy, hTy i, hTy j] using
      hp
  | mem i j =>
    simpa [ExactLiteralTrial.Formula.renameVars, Formula.StratifiedBy, hTy i, hTy j] using
      hp
  | imp p q ihp ihq =>
    constructor
    · apply ihp
      · exact hTy
      · exact hp.1
    · apply ihq
      · exact hTy
      · exact hp.2
  | all p ih =>
    rcases hp with ⟨k, hp⟩
    refine ⟨k, ?_⟩
    apply
      ih (Fin.cases 0 (fun i => Fin.succ (rho i))) (Fin.cases k smallTy)
        (Fin.cases k largeTy)
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · rfl
      · exact hTy j
    · exact hp

theorem stratifiedBy_liftClassPredicate {n : Nat} (ty : Fin n → Int)
    (memberTy representedTy : Int) (p : Formula (n + 1))
    (hp : Formula.StratifiedBy (Fin.cases memberTy ty) p) :
    Formula.StratifiedBy (Fin.cases memberTy (Fin.cases representedTy ty))
      (ExactLiteralTrial.Formula.liftClassPredicate p) :=
  by
  apply
    stratifiedBy_renameVars (Fin.cases 0 (fun i => Fin.succ (Fin.succ i)))
      (Fin.cases memberTy ty)
  · intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · rfl
  · exact hp

theorem stratifiedBy_eqCandidateToPredicate {n : Nat} (ty : Fin n → Int) (memberTy : Int)
    (p : Formula (n + 1)) (hp : Formula.StratifiedBy (Fin.cases memberTy ty) p) :
    Formula.StratifiedBy (Fin.cases (memberTy + 1) ty)
      (ExactLiteralTrial.Formula.eqCandidateToPredicate p) :=
  by
  simp only [ExactLiteralTrial.Formula.eqCandidateToPredicate, Formula.StratifiedBy]
  refine ⟨memberTy, ?_⟩
  rw [stratifiedBy_biimp_iff]
  constructor
  · change memberTy + 1 = memberTy + 1
    rfl
  · exact stratifiedBy_liftClassPredicate ty memberTy (memberTy + 1) p hp

namespace LiteralClass

/-- A literal class is typed by the type of one of its members. -/
inductive Typed {n : Nat} (ty : Fin n → Int) : LiteralClass n → Int → Prop
  | setVar (i : Fin n) (k : Int) (h : ty i = k + 1) : Typed ty (.setVar i) k
  |
  singleton {A : LiteralClass n} {k : Int} :
    Typed ty A k → Typed ty (.singleton A) (k + 1)
  |
  unorderedPair {A B : LiteralClass n} {k : Int} :
    Typed ty A k → Typed ty B k → Typed ty (.unorderedPair A B) (k + 1)
  |
  kPair {A B : LiteralClass n} {k : Int} :
    Typed ty A k → Typed ty B k → Typed ty (.kPair A B) (k + 2)

theorem membership_stratifiedBy {n : Nat} {ty : Fin n → Int} {A : LiteralClass n}
    {k : Int} (hA : Typed ty A k) :
    Formula.StratifiedBy (Fin.cases k ty) (ExactLiteralTrial.LiteralClass.membership A) :=
  by
  induction hA with
  | setVar i k h =>
    simpa [ExactLiteralTrial.LiteralClass.membership, Formula.StratifiedBy] using h
  | singleton h ih =>
    simpa only [ExactLiteralTrial.LiteralClass.membership] using
      (stratifiedBy_eqCandidateToPredicate ty _ _ ih)
  | unorderedPair hA hB ihA
    ihB =>
    simp only [ExactLiteralTrial.LiteralClass.membership]
    rw [stratifiedBy_disj_iff]
    exact
      ⟨stratifiedBy_eqCandidateToPredicate ty _ _ ihA,
        stratifiedBy_eqCandidateToPredicate ty _ _ ihB⟩
  | kPair hA hB ihA
    ihB =>
    simp only [ExactLiteralTrial.LiteralClass.membership]
    rw [stratifiedBy_disj_iff]
    constructor
    · have h1 := stratifiedBy_eqCandidateToPredicate ty _ _ ihA
      have h2 := stratifiedBy_eqCandidateToPredicate ty _ _ h1
      simpa only [Int.add_assoc, show (1 : Int) + 1 = 2 from rfl] using h2
    · have h1 := stratifiedBy_eqCandidateToPredicate ty _ _ ihA
      have h2 := stratifiedBy_eqCandidateToPredicate ty _ _ ihB
      have hp := (stratifiedBy_disj_iff _ _ _).2 ⟨h1, h2⟩
      have hout := stratifiedBy_eqCandidateToPredicate ty _ _ hp
      simpa only [Int.add_assoc, show (1 : Int) + 1 = 2 from rfl] using hout

theorem classEq_stratifiedBy {n : Nat} {ty : Fin n → Int} {A B : LiteralClass n} {k : Int}
    (hA : Typed ty A k) (hB : Typed ty B k) :
    Formula.StratifiedBy ty (ExactLiteralTrial.LiteralClass.classEq A B) :=
  by
  simp only [ExactLiteralTrial.LiteralClass.classEq, Formula.StratifiedBy]
  refine ⟨k, ?_⟩
  rw [stratifiedBy_biimp_iff]
  exact ⟨membership_stratifiedBy hA, membership_stratifiedBy hB⟩

theorem setEqClass_stratifiedBy {n : Nat} {ty : Fin n → Int} {x : Fin n}
    {A : LiteralClass n} {k : Int} (hx : ty x = k + 1) (hA : Typed ty A k) :
    Formula.StratifiedBy ty (ExactLiteralTrial.LiteralClass.setEqClass x A) :=
  classEq_stratifiedBy (.setVar x k hx) hA

theorem classMemSet_stratifiedBy {n : Nat} {ty : Fin n → Int} {A : LiteralClass n}
    {r : Fin n} {k : Int} (hA : Typed ty A k) (hr : ty r = k + 2) :
    Formula.StratifiedBy ty (ExactLiteralTrial.LiteralClass.classMemSet A r) :=
  by
  simp only [ExactLiteralTrial.LiteralClass.classMemSet]
  rw [stratifiedBy_ex_iff]
  refine ⟨k + 1, ?_⟩
  rw [stratifiedBy_conj_iff]
  constructor
  · exact stratifiedBy_eqCandidateToPredicate ty k _ (membership_stratifiedBy hA)
  · simpa [Formula.StratifiedBy, Int.add_assoc, show (1 : Int) + 1 = 2 from rfl] using hr

end LiteralClass

end StratificationSupport

section ComprehensionPredicates

/-! Strong unary predicates whose comprehension sets witness the eleven axioms. -/


@[expose]
def ninPred : Formula 3 :=
  Formula.neg (Formula.conj (.mem 0 2) (.mem 0 1))

@[expose]
def xpPred : Formula 2 :=
  Formula.ex (Formula.ex (Formula.conj (literalKPair 2 1 0) (.mem 0 3)))

@[expose]
def oneCPred : Formula 1 :=
  Formula.isSomeSingleton 0

@[expose]
def cnvPred : Formula 2 :=
  Formula.ex (Formula.ex (Formula.conj (literalKPair 2 1 0) (literalPairMem 0 1 3)))

@[expose]
def ssetPred : Formula 1 :=
  Formula.ex (Formula.ex (Formula.conj (literalKPair 2 1 0) (Formula.subset 1 0)))

@[expose]
def siPred : Formula 2 :=
  Formula.ex
    (Formula.ex (Formula.conj (LiteralClass.setEqClass 2
          (.kPair (.singleton (.setVar 1)) (.singleton (.setVar 0)))) (literalPairMem 1 0 3)))

@[expose]
def ins2Pred : Formula 2 :=
  Formula.ex
    (Formula.ex (Formula.ex (Formula.conj (LiteralClass.setEqClass 3
            (.kPair (.singleton (.singleton (.setVar 2))) (.kPair (.setVar 1) (.setVar 0))))
          (literalPairMem 2 0 4))))

@[expose]
def ins3Pred : Formula 2 :=
  Formula.ex
    (Formula.ex (Formula.ex (Formula.conj (LiteralClass.setEqClass 3
            (.kPair (.singleton (.singleton (.setVar 2))) (.kPair (.setVar 1) (.setVar 0))))
          (literalPairMem 2 1 4))))

@[expose]
def typeLowerPred : Formula 2 :=
  .all (literalPairSingletonSecondMem 0 1 2)

theorem ninPred_stratified : ninPred.Stratified :=
  by
  refine ⟨![0, 1, 1], ?_⟩
  simp [ninPred, Formula.StratifiedBy, Formula.neg, Formula.conj]

theorem oneCPred_stratified : oneCPred.Stratified :=
  by
  refine ⟨![1], ?_⟩
  simp only [oneCPred, Formula.isSomeSingleton, Formula.ex, Formula.neg, Nat.reduceAdd,
    Formula.singleton, Formula.biimp, Formula.conj, Fin.isValue, Fin.succ_zero_eq_one,
    Fin.succ_one_eq_two, Formula.stratifiedBy_imp, Formula.StratifiedBy, Fin.cases_zero,
    and_true]
  refine ⟨0, 0, ?_⟩
  decide

theorem xpPred_stratified : xpPred.Stratified :=
  by
  refine ⟨![2, 1], ?_⟩
  simp only [xpPred, stratifiedBy_ex_iff]
  refine ⟨0, 0, ?_⟩
  rw [stratifiedBy_conj_iff]
  constructor
  · apply LiteralClass.setEqClass_stratifiedBy (k := (1 : Int))
    · decide
    · exact
        LiteralClass.Typed.kPair (.setVar 1 (-1) (by decide)) (.setVar 0 (-1) (by decide))
  · change (1 : Int) = 0 + 1
    rfl

theorem cnvPred_stratified : cnvPred.Stratified :=
  by
  refine ⟨![2, 3], ?_⟩
  simp only [cnvPred, stratifiedBy_ex_iff]
  refine ⟨0, 0, ?_⟩
  rw [stratifiedBy_conj_iff]
  constructor
  · apply LiteralClass.setEqClass_stratifiedBy (k := (1 : Int))
    · decide
    · exact
        LiteralClass.Typed.kPair (.setVar 1 (-1) (by decide)) (.setVar 0 (-1) (by decide))
  · apply LiteralClass.classMemSet_stratifiedBy (k := (1 : Int))
    · exact
        LiteralClass.Typed.kPair (.setVar 0 (-1) (by decide)) (.setVar 1 (-1) (by decide))
    · decide

theorem ssetPred_stratified : ssetPred.Stratified :=
  by
  refine ⟨![3], ?_⟩
  simp only [ssetPred, stratifiedBy_ex_iff]
  refine ⟨1, 1, ?_⟩
  rw [stratifiedBy_conj_iff]
  constructor
  · apply LiteralClass.setEqClass_stratifiedBy (k := (2 : Int))
    · decide
    · exact LiteralClass.Typed.kPair (.setVar 1 0 (by decide)) (.setVar 0 0 (by decide))
  · simp only [Formula.subset, Formula.StratifiedBy]
    refine ⟨0, ?_⟩
    constructor <;> change (1 : Int) = 0 + 1 <;> rfl

theorem siPred_stratified : siPred.Stratified :=
  by
  refine ⟨![3, 3], ?_⟩
  simp only [siPred, stratifiedBy_ex_iff]
  refine ⟨0, 0, ?_⟩
  rw [stratifiedBy_conj_iff]
  constructor
  · apply LiteralClass.setEqClass_stratifiedBy (k := (2 : Int))
    · decide
    · exact
        LiteralClass.Typed.kPair
          (LiteralClass.Typed.singleton (.setVar 1 (-1) (by decide)))
          (LiteralClass.Typed.singleton (.setVar 0 (-1) (by decide)))
  · apply LiteralClass.classMemSet_stratifiedBy (k := (1 : Int))
    · exact
        LiteralClass.Typed.kPair (.setVar 1 (-1) (by decide)) (.setVar 0 (-1) (by decide))
    · decide

theorem ins2Pred_stratified : ins2Pred.Stratified :=
  by
  refine ⟨![4, 3], ?_⟩
  simp only [ins2Pred, stratifiedBy_ex_iff]
  refine ⟨0, 0, 0, ?_⟩
  rw [stratifiedBy_conj_iff]
  constructor
  · apply LiteralClass.setEqClass_stratifiedBy (k := (3 : Int))
    · decide
    · exact
        LiteralClass.Typed.kPair
          (LiteralClass.Typed.singleton
            (LiteralClass.Typed.singleton (.setVar 2 (-1) (by decide))))
          (LiteralClass.Typed.kPair (.setVar 1 (-1) (by decide)) (.setVar 0 (-1) (by decide)))
  · apply LiteralClass.classMemSet_stratifiedBy (k := (1 : Int))
    · exact
        LiteralClass.Typed.kPair (.setVar 2 (-1) (by decide)) (.setVar 0 (-1) (by decide))
    · decide

theorem ins3Pred_stratified : ins3Pred.Stratified :=
  by
  refine ⟨![4, 3], ?_⟩
  simp only [ins3Pred, stratifiedBy_ex_iff]
  refine ⟨0, 0, 0, ?_⟩
  rw [stratifiedBy_conj_iff]
  constructor
  · apply LiteralClass.setEqClass_stratifiedBy (k := (3 : Int))
    · decide
    · exact
        LiteralClass.Typed.kPair
          (LiteralClass.Typed.singleton
            (LiteralClass.Typed.singleton (.setVar 2 (-1) (by decide))))
          (LiteralClass.Typed.kPair (.setVar 1 (-1) (by decide)) (.setVar 0 (-1) (by decide)))
  · apply LiteralClass.classMemSet_stratifiedBy (k := (1 : Int))
    · exact
        LiteralClass.Typed.kPair (.setVar 2 (-1) (by decide)) (.setVar 1 (-1) (by decide))
    · decide

theorem typeLowerPred_stratified : typeLowerPred.Stratified :=
  by
  refine ⟨![0, 4], ?_⟩
  simp only [typeLowerPred, Formula.StratifiedBy]
  refine ⟨1, ?_⟩
  apply LiteralClass.classMemSet_stratifiedBy (k := (2 : Int))
  · exact
      LiteralClass.Typed.kPair (.setVar 0 0 (by decide))
        (LiteralClass.Typed.singleton (.setVar 1 (-1) (by decide)))
  · decide

end ComprehensionPredicates

section Satisfaction

variable {S : Fol.Structure LNF} (hNF : Fol.all_realize_sentence S NF)

/-- A named choice of the set delivered by an NF comprehension instance. -/
@[expose]
noncomputable def comprehensionObj {n : Nat} (p : Formula (n + 1)) (hp : p.Stratified)
    (xs : DVec S n) : S :=
  Classical.choose (nf_comprehension hNF p hp xs)

@[simp]
theorem mem_comprehensionObj {n : Nat} (p : Formula (n + 1)) (hp : p.Stratified)
    (xs : DVec S n) (z : S) :
    Mem S z (comprehensionObj hNF p hp xs) ↔ FormulaHolds S (DVec.cons z xs) p :=
  Classical.choose_spec (nf_comprehension hNF p hp xs) z

theorem realizes_literalAxSn (hNF : Fol.all_realize_sentence S NF) :
    Fol.realize_sentence S (literalAxiomFormula .axSn) :=
  by
  rw [literalAxiomFormula, literalAxiomSyntax]
  change Fol.realize_bounded_formula DVec.nil (Formula.toFlypitch literalAxSn) DVec.nil
  rw [← formulaHolds_toFlypitch DVec.nil literalAxSn]
  simp only [literalAxSn, FormulaHolds, formulaHolds_ex, formulaHolds_biimp]
  intro x
  refine ⟨singletonObj hNF x, ?_⟩
  intro z
  simp [lookup, DVec.nth]

theorem realizes_literalAxNin (hNF : Fol.all_realize_sentence S NF) :
    Fol.realize_sentence S (literalAxiomFormula .axNin) :=
  by
  rw [literalAxiomFormula, literalAxiomSyntax]
  change Fol.realize_bounded_formula DVec.nil (Formula.toFlypitch literalAxNin) DVec.nil
  rw [← formulaHolds_toFlypitch DVec.nil literalAxNin]
  simp only [literalAxNin, FormulaHolds, formulaHolds_ex, formulaHolds_biimp]
  intro x y
  refine
    ⟨comprehensionObj hNF ninPred ninPred_stratified (DVec.cons y (DVec.cons x DVec.nil)),
      ?_⟩
  intro z
  simp only [lookup, DVec.nth]
  rw [mem_comprehensionObj]
  simp [ninPred, FormulaHolds, lookup, DVec.nth]

theorem realizes_literalAx1c (hNF : Fol.all_realize_sentence S NF) :
    Fol.realize_sentence S (literalAxiomFormula .ax1c) :=
  by
  rw [literalAxiomFormula, literalAxiomSyntax]
  change Fol.realize_bounded_formula DVec.nil (Formula.toFlypitch literalAx1c) DVec.nil
  rw [← formulaHolds_toFlypitch DVec.nil literalAx1c]
  simp only [literalAx1c, formulaHolds_ex, FormulaHolds, formulaHolds_biimp]
  refine ⟨comprehensionObj hNF oneCPred oneCPred_stratified DVec.nil, ?_⟩
  intro y
  simp only [lookup, DVec.nth]
  rw [mem_comprehensionObj]
  simp [oneCPred, Formula.isSomeSingleton, Formula.singleton, FormulaHolds, lookup,
    DVec.nth]

theorem realizes_literalAxXp (hNF : Fol.all_realize_sentence S NF) :
    Fol.realize_sentence S (literalAxiomFormula .axXp) :=
  by
  rw [literalAxiomFormula, literalAxiomSyntax]
  change Fol.realize_bounded_formula DVec.nil (Formula.toFlypitch literalAxXp) DVec.nil
  rw [← formulaHolds_toFlypitch DVec.nil literalAxXp]
  simp only [literalAxXp, FormulaHolds, formulaHolds_ex, formulaHolds_biimp]
  intro x
  refine ⟨comprehensionObj hNF xpPred xpPred_stratified (DVec.cons x DVec.nil), ?_⟩
  intro z
  simp only [lookup, DVec.nth]
  rw [mem_comprehensionObj]
  simp [xpPred, literalKPair, FormulaHolds, formulaHolds_ex, formulaHolds_conj,
    formulaHolds_setEqClass_iff hNF, evalLiteralClass, kPairObj, lookup, DVec.nth]

theorem realizes_literalAxExt (hNF : Fol.all_realize_sentence S NF) :
    Fol.realize_sentence S (literalAxiomFormula .axExt) :=
  hNF extensionality_mem_NF

theorem realizes_literalAxTypeLower (hNF : Fol.all_realize_sentence S NF) :
    Fol.realize_sentence S (literalAxiomFormula .axTypeLower) :=
  by
  rw [literalAxiomFormula, literalAxiomSyntax]
  change
    Fol.realize_bounded_formula DVec.nil (Formula.toFlypitch literalAxTypeLower) DVec.nil
  rw [← formulaHolds_toFlypitch DVec.nil literalAxTypeLower]
  simp only [literalAxTypeLower, FormulaHolds, formulaHolds_ex, formulaHolds_biimp]
  intro x
  refine
    ⟨comprehensionObj hNF typeLowerPred typeLowerPred_stratified (DVec.cons x DVec.nil),
      ?_⟩
  intro z
  simp only [lookup, DVec.nth]
  rw [mem_comprehensionObj]
  simp [typeLowerPred, literalPairSingletonSecondMem, FormulaHolds,
    formulaHolds_classMemSet_iff hNF, evalLiteralClass, kPairObj, lookup, DVec.nth]

theorem realizes_literalAxCnv (hNF : Fol.all_realize_sentence S NF) :
    Fol.realize_sentence S (literalAxiomFormula .axCnv) :=
  by
  rw [literalAxiomFormula, literalAxiomSyntax]
  change Fol.realize_bounded_formula DVec.nil (Formula.toFlypitch literalAxCnv) DVec.nil
  rw [← formulaHolds_toFlypitch DVec.nil literalAxCnv]
  simp only [literalAxCnv, FormulaHolds, formulaHolds_ex, formulaHolds_biimp]
  intro x
  let y := comprehensionObj hNF cnvPred cnvPred_stratified (DVec.cons x DVec.nil)
  refine ⟨y, ?_⟩
  intro z w
  simp only [literalPairMem, formulaHolds_classMemSet_iff hNF, evalLiteralClass, lookup,
    DVec.nth]
  rw [show y = comprehensionObj hNF cnvPred cnvPred_stratified (DVec.cons x DVec.nil) by
      rfl,
    mem_comprehensionObj]
  simp only [cnvPred, formulaHolds_ex, formulaHolds_conj]
  simp only [Nat.reduceAdd, literalKPair, Fin.isValue, formulaHolds_setEqClass_iff hNF,
    lookup, DVec.nth, evalLiteralClass, literalPairMem, formulaHolds_classMemSet_iff hNF]
  constructor
  · rintro ⟨z', w', hp, hm⟩
    rcases kPairObj_injective hNF hp with ⟨rfl, rfl⟩
    exact hm
  · intro hm
    exact ⟨z, w, rfl, hm⟩

theorem realizes_literalAxSset (hNF : Fol.all_realize_sentence S NF) :
    Fol.realize_sentence S (literalAxiomFormula .axSset) :=
  by
  rw [literalAxiomFormula, literalAxiomSyntax]
  change Fol.realize_bounded_formula DVec.nil (Formula.toFlypitch literalAxSset) DVec.nil
  rw [← formulaHolds_toFlypitch DVec.nil literalAxSset]
  simp only [literalAxSset, FormulaHolds, formulaHolds_ex, formulaHolds_biimp]
  let r := comprehensionObj hNF ssetPred ssetPred_stratified DVec.nil
  refine ⟨r, ?_⟩
  intro a b
  simp only [literalPairMem, formulaHolds_classMemSet_iff hNF, evalLiteralClass, lookup,
    DVec.nth]
  change Mem S (kPairObj hNF a b) r ↔ ∀ z : S, Mem S z a → Mem S z b
  rw [show r = comprehensionObj hNF ssetPred ssetPred_stratified DVec.nil by rfl,
    mem_comprehensionObj]
  simp only [ssetPred, formulaHolds_ex, formulaHolds_conj]
  simp only [Nat.reduceAdd, literalKPair, Fin.isValue, formulaHolds_setEqClass_iff hNF,
    lookup, DVec.nth, evalLiteralClass, Formula.subset, Fin.succ_one_eq_two,
    Fin.succ_zero_eq_one]
  constructor
  · rintro ⟨a', b', hp, hs⟩
    rcases kPairObj_injective hNF hp with ⟨rfl, rfl⟩
    exact hs
  · intro hs
    exact ⟨a, b, rfl, hs⟩

theorem realizes_literalAxSi (hNF : Fol.all_realize_sentence S NF) :
    Fol.realize_sentence S (literalAxiomFormula .axSi) :=
  by
  rw [literalAxiomFormula, literalAxiomSyntax]
  change Fol.realize_bounded_formula DVec.nil (Formula.toFlypitch literalAxSi) DVec.nil
  rw [← formulaHolds_toFlypitch DVec.nil literalAxSi]
  simp only [literalAxSi, FormulaHolds, formulaHolds_ex, formulaHolds_biimp]
  intro x
  let y := comprehensionObj hNF siPred siPred_stratified (DVec.cons x DVec.nil)
  refine ⟨y, ?_⟩
  intro z w
  simp only [literalSingletonPairMem, literalPairMem, formulaHolds_classMemSet_iff hNF,
    evalLiteralClass, lookup, DVec.nth]
  rw [show y = comprehensionObj hNF siPred siPred_stratified (DVec.cons x DVec.nil) by
      rfl,
    mem_comprehensionObj]
  simp only [siPred, formulaHolds_ex, formulaHolds_conj]
  simp only [Nat.reduceAdd, Fin.isValue, formulaHolds_setEqClass_iff hNF, lookup,
    DVec.nth, evalLiteralClass, literalPairMem, formulaHolds_classMemSet_iff hNF]
  constructor
  · rintro ⟨z', w', hp, hm⟩
    rcases kPairObj_injective hNF hp with ⟨hz, hw⟩
    have hzz : z = z' := singletonObj_injective hNF hz
    have hww : w = w' := singletonObj_injective hNF hw
    simpa [hzz, hww] using hm
  · intro hm
    exact ⟨z, w, rfl, hm⟩

theorem realizes_literalAxIns2 (hNF : Fol.all_realize_sentence S NF) :
    Fol.realize_sentence S (literalAxiomFormula .axIns2) :=
  by
  rw [literalAxiomFormula, literalAxiomSyntax]
  change Fol.realize_bounded_formula DVec.nil (Formula.toFlypitch literalAxIns2) DVec.nil
  rw [← formulaHolds_toFlypitch DVec.nil literalAxIns2]
  simp only [literalAxIns2, FormulaHolds, formulaHolds_ex, formulaHolds_biimp]
  intro x
  let y := comprehensionObj hNF ins2Pred ins2Pred_stratified (DVec.cons x DVec.nil)
  refine ⟨y, ?_⟩
  intro z w t
  simp only [literalInsertedPairMem, literalPairMem, formulaHolds_classMemSet_iff hNF,
    evalLiteralClass, lookup, DVec.nth]
  rw [show y = comprehensionObj hNF ins2Pred ins2Pred_stratified (DVec.cons x DVec.nil) by
      rfl,
    mem_comprehensionObj]
  simp only [ins2Pred, formulaHolds_ex, formulaHolds_conj]
  simp only [Nat.reduceAdd, Fin.isValue, formulaHolds_setEqClass_iff hNF, lookup,
    DVec.nth, evalLiteralClass, literalPairMem, formulaHolds_classMemSet_iff hNF]
  constructor
  · rintro ⟨z', w', t', hp, hm⟩
    rcases kPairObj_injective hNF hp with ⟨hzz, hwt⟩
    have hz1 := singletonObj_injective hNF hzz
    have hzz' : z = z' := singletonObj_injective hNF hz1
    rcases kPairObj_injective hNF hwt with ⟨hww, htt⟩
    simpa [hzz', hww, htt] using hm
  · intro hm
    exact ⟨z, w, t, rfl, hm⟩

theorem realizes_literalAxIns3 (hNF : Fol.all_realize_sentence S NF) :
    Fol.realize_sentence S (literalAxiomFormula .axIns3) :=
  by
  rw [literalAxiomFormula, literalAxiomSyntax]
  change Fol.realize_bounded_formula DVec.nil (Formula.toFlypitch literalAxIns3) DVec.nil
  rw [← formulaHolds_toFlypitch DVec.nil literalAxIns3]
  simp only [literalAxIns3, FormulaHolds, formulaHolds_ex, formulaHolds_biimp]
  intro x
  let y := comprehensionObj hNF ins3Pred ins3Pred_stratified (DVec.cons x DVec.nil)
  refine ⟨y, ?_⟩
  intro z w t
  simp only [literalInsertedPairMem, literalPairMem, formulaHolds_classMemSet_iff hNF,
    evalLiteralClass, lookup, DVec.nth]
  rw [show y = comprehensionObj hNF ins3Pred ins3Pred_stratified (DVec.cons x DVec.nil) by
      rfl,
    mem_comprehensionObj]
  simp only [ins3Pred, formulaHolds_ex, formulaHolds_conj]
  simp only [Nat.reduceAdd, Fin.isValue, formulaHolds_setEqClass_iff hNF, lookup,
    DVec.nth, evalLiteralClass, literalPairMem, formulaHolds_classMemSet_iff hNF,
    exists_and_right]
  constructor
  · rintro ⟨z', w', ⟨t', hp⟩, hm⟩
    rcases kPairObj_injective hNF hp with ⟨hzz, hwt⟩
    have hz1 := singletonObj_injective hNF hzz
    have hzz' : z = z' := singletonObj_injective hNF hz1
    rcases kPairObj_injective hNF hwt with ⟨hww, htt⟩
    simpa [hzz', hww, htt] using hm
  · intro hm
    exact ⟨z, w, ⟨t, rfl⟩, hm⟩

/-- Every model of ordinary NF satisfies all eleven literal Hailperin axioms. -/
theorem nf_models_literalHailperin (hNF : Fol.all_realize_sentence S NF) :
    Fol.all_realize_sentence S LiteralHailperinNF :=
  by
  intro f hf
  rcases hf with ⟨name, rfl⟩
  cases name with
  | axExt => exact realizes_literalAxExt hNF
  | axNin => exact realizes_literalAxNin hNF
  | axXp => exact realizes_literalAxXp hNF
  | axCnv => exact realizes_literalAxCnv hNF
  | ax1c => exact realizes_literalAx1c hNF
  | axSset => exact realizes_literalAxSset hNF
  | axSi => exact realizes_literalAxSi hNF
  | axIns2 => exact realizes_literalAxIns2 hNF
  | axIns3 => exact realizes_literalAxIns3 hNF
  | axTypeLower => exact realizes_literalAxTypeLower hNF
  | axSn => exact realizes_literalAxSn hNF

end Satisfaction


end NFChoice.Foundation.NFStandard
