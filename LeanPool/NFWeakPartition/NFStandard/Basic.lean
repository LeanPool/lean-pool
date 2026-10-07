/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.SemanticCore.Lowering

/-! NF weak partition development: NFStandard.Basic. -/


public section

namespace NFChoice.Foundation

open scoped Fol

namespace Formula

/-! The usual graph-theoretic stratification condition for the language of NF.
An equality edge preserves type and a membership edge raises type by one.
At a binder, the newly bound de Bruijn variable (index zero) may be assigned
an arbitrary integer type.
-/


/-- A type assignment certifies the ordinary NF stratification of a formula. -/
@[expose]
def StratifiedBy {n : Nat} (ty : Fin n → Int) : Formula n → Prop
  | .falsum => True
  | .equal x y => ty x = ty y
  | .mem x y => ty y = ty x + 1
  | .imp p q => StratifiedBy ty p ∧ StratifiedBy ty q
  | .all p => ∃ k : Int, StratifiedBy (Fin.cases k ty) p

/-- A formula is stratified when it admits an integer type assignment. -/
@[expose]
def Stratified {n : Nat} (p : Formula n) : Prop :=
  ∃ ty : Fin n → Int, StratifiedBy ty p

/-- A first-class stratification certificate, useful to schema enumerators. -/
abbrev Stratification {n : Nat} (p : Formula n) :=
  { ty : Fin n → Int // StratifiedBy ty p }

@[simp]
theorem stratifiedBy_falsum {n : Nat} (ty : Fin n → Int) :
    StratifiedBy ty (.falsum : Formula n) :=
  trivial

@[simp]
theorem stratifiedBy_equal {n : Nat} (ty : Fin n → Int) (x y : Fin n) :
    StratifiedBy ty (.equal x y) ↔ ty x = ty y :=
  Iff.rfl

@[simp]
theorem stratifiedBy_mem {n : Nat} (ty : Fin n → Int) (x y : Fin n) :
    StratifiedBy ty (.mem x y) ↔ ty y = ty x + 1 :=
  Iff.rfl

@[simp]
theorem stratifiedBy_imp {n : Nat} (ty : Fin n → Int) (p q : Formula n) :
    StratifiedBy ty (.imp p q) ↔ StratifiedBy ty p ∧ StratifiedBy ty q :=
  Iff.rfl

@[simp]
theorem stratifiedBy_all {n : Nat} (ty : Fin n → Int) (p : Formula (n + 1)) :
    StratifiedBy ty (.all p) ↔ ∃ k : Int, StratifiedBy (Fin.cases k ty) p :=
  Iff.rfl

@[simp]
theorem stratified_neg_iff {n : Nat} (p : Formula n) :
    Stratified (neg p) ↔ Stratified p := by simp [Stratified, neg]

@[simp]
theorem stratified_imp_iff {n : Nat} (p q : Formula n) :
    Stratified (.imp p q) ↔ ∃ ty : Fin n → Int, StratifiedBy ty p ∧ StratifiedBy ty q :=
  Iff.rfl

@[simp]
theorem stratified_conj_iff {n : Nat} (p q : Formula n) :
    Stratified (conj p q) ↔ ∃ ty : Fin n → Int, StratifiedBy ty p ∧ StratifiedBy ty q :=
  by simp [conj, Stratified, neg]

@[simp]
theorem stratified_disj_iff {n : Nat} (p q : Formula n) :
    Stratified (disj p q) ↔ ∃ ty : Fin n → Int, StratifiedBy ty p ∧ StratifiedBy ty q :=
  by simp [disj, Stratified, neg]

@[simp]
theorem stratified_biimp_iff {n : Nat} (p q : Formula n) :
    Stratified (biimp p q) ↔ ∃ ty : Fin n → Int, StratifiedBy ty p ∧ StratifiedBy ty q :=
  by
  constructor
  · rintro ⟨ty, h⟩
    refine ⟨ty, ?_⟩
    simp only [biimp, conj, neg, StratifiedBy] at h
    tauto
  · rintro ⟨ty, hp, hq⟩
    refine ⟨ty, ?_⟩
    simp only [biimp, conj, neg, StratifiedBy]
    tauto

@[simp]
theorem stratified_all_iff {n : Nat} (p : Formula (n + 1)) :
    Stratified (.all p) ↔ Stratified p :=
  by
  constructor
  · rintro ⟨ty, k, hp⟩
    exact ⟨Fin.cases k ty, hp⟩
  · rintro ⟨u, hp⟩
    let ty : Fin n → Int := fun i => u (Fin.succ i)
    have hu : Fin.cases (u 0) ty = u := by
      funext i
      exact Fin.cases rfl (fun _ => rfl) i
    refine ⟨ty, u 0, ?_⟩
    rw [hu]
    exact hp

@[simp]
theorem stratified_ex_iff {n : Nat} (p : Formula (n + 1)) :
    Stratified (ex p) ↔ Stratified p := by simp [ex]

theorem Stratified.imp {n : Nat} {p q : Formula n} {ty : Fin n → Int}
    (hp : StratifiedBy ty p) (hq : StratifiedBy ty q) : Stratified (.imp p q) :=
  ⟨ty, hp, hq⟩

theorem Stratified.neg {n : Nat} {p : Formula n} (hp : Stratified p) :
    Stratified (neg p) :=
  (stratified_neg_iff p).2 hp

theorem Stratified.conj {n : Nat} {p q : Formula n} {ty : Fin n → Int}
    (hp : StratifiedBy ty p) (hq : StratifiedBy ty q) : Stratified (conj p q) :=
  (stratified_conj_iff p q).2 ⟨ty, hp, hq⟩

theorem Stratified.disj {n : Nat} {p q : Formula n} {ty : Fin n → Int}
    (hp : StratifiedBy ty p) (hq : StratifiedBy ty q) : Stratified (disj p q) :=
  (stratified_disj_iff p q).2 ⟨ty, hp, hq⟩

theorem Stratified.biimp {n : Nat} {p q : Formula n} {ty : Fin n → Int}
    (hp : StratifiedBy ty p) (hq : StratifiedBy ty q) : Stratified (biimp p q) :=
  (stratified_biimp_iff p q).2 ⟨ty, hp, hq⟩

theorem Stratified.all {n : Nat} {p : Formula (n + 1)} (hp : Stratified p) :
    Stratified (.all p) :=
  (stratified_all_iff p).2 hp

theorem Stratified.ex {n : Nat} {p : Formula (n + 1)} (hp : Stratified p) :
    Stratified (ex p) :=
  (stratified_ex_iff p).2 hp

/-- Universally close all free de Bruijn variables of an intrinsic formula. -/
@[expose]
def closeAll {n : Nat} (p : Formula n) : Fol.sentence LNF :=
  Fol.bdAlls n p.toFlypitch

end Formula

namespace NFStandard

open ExactLiteralTrial

/-- The open formula saying that some set has exactly the extension defined by `p`. -/
@[expose]
def comprehensionBody {n : Nat} (p : Formula (n + 1)) : Formula n :=
  Formula.ex (ExactLiteralTrial.Formula.eqCandidateToPredicate p)

/-- The universally closed comprehension axiom associated with `p`. -/
@[expose]
def comprehensionInstance {n : Nat} (p : Formula (n + 1)) : Fol.sentence LNF :=
  Formula.closeAll (comprehensionBody p)

/-- The ordinary NF stratified-comprehension schema. -/
@[expose]
def StratifiedComprehension : Fol.SentTheory LNF :=
  {f |
    ∃ (n : Nat) (p : Formula (n + 1)), Formula.Stratified p ∧ f = comprehensionInstance p}

@[simp]
theorem mem_stratifiedComprehension_iff (f : Fol.sentence LNF) :
    f ∈ StratifiedComprehension ↔
      ∃ (n : Nat) (p : Formula (n + 1)),
        Formula.Stratified p ∧ f = comprehensionInstance p :=
  Iff.rfl

theorem comprehensionInstance_mem {n : Nat} (p : Formula (n + 1))
    (hp : Formula.Stratified p) : comprehensionInstance p ∈ StratifiedComprehension :=
  ⟨n, p, hp, rfl⟩

end NFStandard

/-- Standard NF: extensionality plus every stratified comprehension instance. -/
abbrev NF : Fol.SentTheory LNF :=
  Set.insert (ExactLiteralTrial.literalAxiomFormula .axExt)
    NFStandard.StratifiedComprehension

namespace NFStandard

@[simp]
theorem extensionality_mem_NF : ExactLiteralTrial.literalAxiomFormula .axExt ∈ NF :=
  Set.mem_insert _ _

@[simp]
theorem comprehensionInstance_mem_NF {n : Nat} (p : Formula (n + 1))
    (hp : Formula.Stratified p) : comprehensionInstance p ∈ NF :=
  Set.mem_insert_of_mem _ (comprehensionInstance_mem p hp)

open NFChoice.SemanticCore

/-- Renaming intrinsic free variables agrees with renaming their valuation. -/
theorem formulaHolds_renameVars :
    ∀ {S : Fol.Structure LNF} {n m : Nat} (rho : Fin n → Fin m) (xs : DVec S m)
      (ys : DVec S n),
      (∀ i, Lowering.lookup xs (rho i) = Lowering.lookup ys i) →
        ∀ p : Formula n,
          Lowering.FormulaHolds S xs (ExactLiteralTrial.Formula.renameVars rho p) ↔
            Lowering.FormulaHolds S ys p
  | _, _, _, _, _, _, _, .falsum => Iff.rfl
  | _, _, _, rho, xs, ys, hlookup, .equal x y =>
    by
    simp only [ExactLiteralTrial.Formula.renameVars, Lowering.FormulaHolds]
    rw [hlookup x, hlookup y]
  | _, _, _, rho, xs, ys, hlookup, .mem x y =>
    by
    simp only [ExactLiteralTrial.Formula.renameVars, Lowering.FormulaHolds]
    rw [hlookup x, hlookup y]
  | _, _, _, rho, xs, ys, hlookup, .imp p q =>
    by
    simp only [ExactLiteralTrial.Formula.renameVars, Lowering.FormulaHolds]
    exact
      Iff.imp (formulaHolds_renameVars rho xs ys hlookup p)
        (formulaHolds_renameVars rho xs ys hlookup q)
  | _, _, _, rho, xs, ys, hlookup, .all p =>
    by
    simp only [ExactLiteralTrial.Formula.renameVars, Lowering.FormulaHolds]
    apply forall_congr'
    intro a
    apply
      formulaHolds_renameVars (Fin.cases 0 (fun i => Fin.succ (rho i))) (DVec.cons a xs)
        (DVec.cons a ys)
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · simp [hlookup]

/--
The inserted ambient set variable is semantically ignored by a lifted class predicate. -/
@[simp]
theorem formulaHolds_liftClassPredicate {S : Fol.Structure LNF} {n : Nat} (xs : DVec S n)
    (a z : S) (p : Formula (n + 1)) :
    Lowering.FormulaHolds S (DVec.cons z (DVec.cons a xs))
        (ExactLiteralTrial.Formula.liftClassPredicate p) ↔
      Lowering.FormulaHolds S (DVec.cons z xs) p :=
  by
  apply
    formulaHolds_renameVars (Fin.cases 0 (fun i => Fin.succ (Fin.succ i)))
      (DVec.cons z (DVec.cons a xs)) (DVec.cons z xs)
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp
  · simp

/-- Direct semantics of the set-representative formula used by comprehension. -/
@[simp]
theorem formulaHolds_eqCandidateToPredicate {S : Fol.Structure LNF} {n : Nat}
    (xs : DVec S n) (a : S) (p : Formula (n + 1)) :
    Lowering.FormulaHolds S (DVec.cons a xs)
        (ExactLiteralTrial.Formula.eqCandidateToPredicate p) ↔
      ∀ z : S, Mem S z a ↔ Lowering.FormulaHolds S (DVec.cons z xs) p :=
  by
  have lookup_one (z : S) :
    Lowering.lookup (DVec.cons z (DVec.cons a xs)) (1 : Fin (n + 2)) = a := by
    exact
      (Lowering.lookup_cons_succ z (DVec.cons a xs) (0 : Fin (n + 1))).trans
        (Lowering.lookup_cons_zero a xs)
  simp [ExactLiteralTrial.Formula.eqCandidateToPredicate, Lowering.FormulaHolds,
    lookup_one]

/-- Every model of `NF` is extensional. -/
theorem nf_extensional {S : Fol.Structure LNF} (hNF : Fol.allRealizeSentence S NF) :
    Extensional S :=
  (extensional_iff_literal_axExt S).2 (hNF extensionality_mem_NF)

/-- A model of `NF` realizes each certified closed comprehension instance. -/
theorem nf_realizes_comprehensionInstance {S : Fol.Structure LNF}
    (hNF : Fol.allRealizeSentence S NF) {n : Nat} (p : Formula (n + 1))
    (hp : Formula.Stratified p) : Fol.realizeSentence S (comprehensionInstance p) :=
  hNF (comprehensionInstance_mem_NF p hp)

/-- Semantic elimination rule for standard stratified comprehension. -/
theorem nf_comprehension {S : Fol.Structure LNF} (hNF : Fol.allRealizeSentence S NF)
    {n : Nat} (p : Formula (n + 1)) (hp : Formula.Stratified p) (xs : DVec S n) :
    ∃ a : S, ∀ z : S, Mem S z a ↔ Lowering.FormulaHolds S (DVec.cons z xs) p :=
  by
  have hclosed := nf_realizes_comprehensionInstance hNF p hp
  have hall :
    ∀ ys : DVec S n,
      Fol.realizeBoundedFormula ys (Formula.toFlypitch (comprehensionBody p))
        DVec.nil :=
    by
    apply (Fol.realize_sentence_bd_alls).1
    simpa [comprehensionInstance, Formula.closeAll] using hclosed
  have hbody : Lowering.FormulaHolds S xs (comprehensionBody p) :=
    (Lowering.formulaHolds_toFlypitch xs (comprehensionBody p)).2 (hall xs)
  rcases (Lowering.formulaHolds_ex).1 hbody with ⟨a, ha⟩
  exact ⟨a, (formulaHolds_eqCandidateToPredicate xs a p).1 ha⟩

end NFStandard

end NFChoice.Foundation
