/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NFChoiceFoundation.Basic

/-! NF weak partition development: exact_literal_trial.NFChoiceExactLiteral. -/


public section

namespace NFChoice.Foundation.ExactLiteralTrial

open scoped Fol

/-! This append-only trial gives the literal class-elimination boundary for the
eleven finite NF axioms.  In particular, a class expression is represented by
its unary membership predicate.  Nested class constructors are *not* replaced
by existential assertions that their values are sets.

For example, the exact predicate saying that the set `p` is the Kuratowski
class pair `<<a,b>>` is

```
forall u, u in p <-> (u = {a} or u = {a,b}),
```

where both displayed class equalities are themselves expanded extensionally.
This differs from asserting the existence of sets `s = {a}` and `q = {a,b}`.
-/


namespace Formula

/-- Rename every free de Bruijn variable in the small formula language. -/
@[expose]
def renameVars {n m : Nat} (rho : Fin n → Fin m) : Formula n → Formula m
  | .falsum => .falsum
  | .equal x y => .equal (rho x) (rho y)
  | .mem x y => .mem (rho x) (rho y)
  | .imp p q => .imp (renameVars rho p) (renameVars rho q)
  | .all p => .all (renameVars (Fin.cases 0 (fun i => Fin.succ (rho i))) p)

/-- Insert a new ambient variable at index one while retaining index zero as the
membership candidate of a unary class predicate.
-/
@[expose]
def liftClassPredicate {n : Nat} (p : Formula (n + 1)) : Formula (n + 2) :=
  renameVars (Fin.cases 0 (fun i => Fin.succ (Fin.succ i))) p

/-- In context `[x, ambient...]`, assert that the set variable `x` is extensionally
equal to the class whose unary membership predicate is `p`.
-/
@[expose]
def eqCandidateToPredicate {n : Nat} (p : Formula (n + 1)) : Formula (n + 1) :=
  .all (Formula.biimp (.mem 0 1) (liftClassPredicate p))

end Formula

/-- The class constructors occurring in the eleven source axioms. -/
inductive LiteralClass : Nat → Type
  | setVar : Fin n → LiteralClass n
  | singleton : LiteralClass n → LiteralClass n
  | unorderedPair : LiteralClass n → LiteralClass n → LiteralClass n
  | kPair : LiteralClass n → LiteralClass n → LiteralClass n

namespace LiteralClass

/-- The unary membership predicate of a class expression.  Its index zero is the
candidate member; the `n` ambient set variables occupy indices one onward.
-/
@[expose]
def membership : {n : Nat} → LiteralClass n → Formula (n + 1)
  | _, .setVar a => .mem 0 (Fin.succ a)
  | _, .singleton A => Formula.eqCandidateToPredicate (membership A)
  | _, .unorderedPair A B =>
    Formula.disj (Formula.eqCandidateToPredicate (membership A))
      (Formula.eqCandidateToPredicate (membership B))
  | _, .kPair A B =>
    let memA := membership A
    let memB := membership B
    let memSingletonA := Formula.eqCandidateToPredicate memA
    let memPairAB :=
      Formula.disj (Formula.eqCandidateToPredicate memA)
        (Formula.eqCandidateToPredicate memB)
    Formula.disj (Formula.eqCandidateToPredicate memSingletonA)
      (Formula.eqCandidateToPredicate memPairAB)

/-- Literal `df-cleq`: extensional equality of two class expressions. -/
@[expose]
def classEq {n : Nat} (A B : LiteralClass n) : Formula n :=
  .all (Formula.biimp (membership A) (membership B))

/-- Extensional equality of a set variable and a class expression. -/
@[expose]
def setEqClass {n : Nat} (x : Fin n) (A : LiteralClass n) : Formula n :=
  classEq (.setVar x) A

/-- Literal `df-clel` when the right side is a set variable:
`A e. r <-> exists x, (x = A and x e. r)`.
-/
@[expose]
def classMemSet {n : Nat} (A : LiteralClass n) (r : Fin n) : Formula n :=
  Formula.ex
    (Formula.conj (Formula.eqCandidateToPredicate (membership A)) (.mem 0 (Fin.succ r)))

end LiteralClass

open LiteralClass

/-! Exact relational readings of the source class constructors. -/


@[expose]
def literalSingleton {n : Nat} (s a : Fin n) : Formula n :=
  setEqClass s (.singleton (.setVar a))

@[expose]
def literalUnorderedPair {n : Nat} (p a b : Fin n) : Formula n :=
  setEqClass p (.unorderedPair (.setVar a) (.setVar b))

@[expose]
def literalKPair {n : Nat} (p a b : Fin n) : Formula n :=
  setEqClass p (.kPair (.setVar a) (.setVar b))

@[expose]
def literalPairMem {n : Nat} (a b r : Fin n) : Formula n :=
  classMemSet (.kPair (.setVar a) (.setVar b)) r

@[expose]
def literalDoubleSingleton {n : Nat} (d a : Fin n) : Formula n :=
  setEqClass d (.singleton (.singleton (.setVar a)))

@[expose]
def literalSingletonPairMem {n : Nat} (a b r : Fin n) : Formula n :=
  classMemSet (.kPair (.singleton (.setVar a)) (.singleton (.setVar b))) r

@[expose]
def literalInsertedPairMem {n : Nat} (z w t r : Fin n) : Formula n :=
  classMemSet
    (.kPair (.singleton (.singleton (.setVar z))) (.kPair (.setVar w) (.setVar t))) r

@[expose]
def literalPairSingletonSecondMem {n : Nat} (a z r : Fin n) : Formula n :=
  classMemSet (.kPair (.setVar a) (.singleton (.setVar z))) r

/-! The following are the universal closures of the source token strings.  Every
constructor-bearing subexpression is interpreted by `LiteralClass.membership`,
so the output contains only logical equality and the sole membership relation.
-/


/-- `ax-ext`: `( A. z ( z e. x <-> z e. y ) -> x = y )`. -/
@[expose]
def literalAxExt : Sentence :=
  .all (.all (.imp (.all (Formula.biimp (.mem 0 2) (.mem 0 1))) (.equal 1 0)))

/-- `ax-nin`: the source anti-conjunction (NAND) axiom. -/
@[expose]
def literalAxNin : Sentence :=
  .all
    (.all (Formula.ex (.all
          (Formula.biimp (.mem 0 1) (Formula.neg (Formula.conj (.mem 0 3) (.mem 0 2)))))))

/-- `ax-xp`: `E. y A. z (z e. y <-> E. w E. t (z = <<w,t>> /\ t e. x))`. -/
@[expose]
def literalAxXp : Sentence :=
  .all
    (Formula.ex (.all (Formula.biimp (.mem 0 1)
          (Formula.ex (Formula.ex (Formula.conj (literalKPair 2 1 0) (.mem 0 4)))))))

/-- `ax-cnv`: `E. y A. z A. w (<<z,w>> e. y <-> <<w,z>> e. x)`. -/
@[expose]
def literalAxCnv : Sentence :=
  .all
    (Formula.ex (.all (.all (Formula.biimp (literalPairMem 1 0 2) (literalPairMem 0 1 3)))))

/-- `ax-1c`: `E. x A. y (y e. x <-> E. z A. w (w e. y <-> w = z))`. -/
@[expose]
def literalAx1c : Sentence :=
  Formula.ex (.all (Formula.biimp (.mem 0 1) (Formula.isSomeSingleton 0)))

/-- `ax-sset`: `E. x A. y A. z (<<y,z>> e. x <-> A. w(w e. y -> w e. z))`. -/
@[expose]
def literalAxSset : Sentence :=
  Formula.ex (.all (.all (Formula.biimp (literalPairMem 1 0 2) (Formula.subset 1 0))))

/-- `ax-si`: `E. y A. z A. w (<<{z},{w}>> e. y <-> <<z,w>> e. x)`. -/
@[expose]
def literalAxSi : Sentence :=
  .all
    (Formula.ex (.all
        (.all (Formula.biimp (literalSingletonPairMem 1 0 2) (literalPairMem 1 0 3)))))

/-- `ax-ins2`: the inserted-pair biconditional ending in `<<z,t>> e. x`. -/
@[expose]
def literalAxIns2 : Sentence :=
  .all
    (Formula.ex (.all (.all (.all
            (Formula.biimp (literalInsertedPairMem 2 1 0 3) (literalPairMem 2 0 4))))))

/-- `ax-ins3`: the inserted-pair biconditional ending in `<<z,w>> e. x`. -/
@[expose]
def literalAxIns3 : Sentence :=
  .all
    (Formula.ex (.all (.all (.all
            (Formula.biimp (literalInsertedPairMem 2 1 0 3) (literalPairMem 2 1 4))))))

/-- `ax-typlower`: `E. y A. z (z e. y <-> A. w <<w,{z}>> e. x)`. -/
@[expose]
def literalAxTypeLower : Sentence :=
  .all
    (Formula.ex (.all (Formula.biimp (.mem 0 1) (.all (literalPairSingletonSecondMem 0 1 3)))))

/-- `ax-sn`: `E. y A. z (z e. y <-> z = x)`. -/
@[expose]
def literalAxSn : Sentence :=
  .all (Formula.ex (.all (Formula.biimp (.mem 0 1) (.equal 0 2))))

/-! Token-by-token equations, deliberately proved by reduction only. -/


theorem axExt_source_equation :
    literalAxExt =
      .all (.all (.imp (.all (Formula.biimp (.mem 0 2) (.mem 0 1))) (.equal 1 0))) :=
  rfl

theorem axNin_source_equation :
    literalAxNin =
      .all
        (.all (Formula.ex (.all (Formula.biimp (.mem 0 1)
                (Formula.neg (Formula.conj (.mem 0 3) (.mem 0 2))))))) :=
  rfl

theorem axXp_source_equation :
    literalAxXp =
      .all
        (Formula.ex (.all (Formula.biimp (.mem 0 1) (Formula.ex
                (Formula.ex (Formula.conj (literalKPair 2 1 0) (.mem 0 4))))))) :=
  rfl

theorem axCnv_source_equation :
    literalAxCnv =
      .all
        (Formula.ex
          (.all (.all (Formula.biimp (literalPairMem 1 0 2) (literalPairMem 0 1 3))))) :=
  rfl

theorem ax1c_source_equation :
    literalAx1c =
      Formula.ex (.all (Formula.biimp (.mem 0 1) (Formula.isSomeSingleton 0))) :=
  rfl

theorem axSset_source_equation :
    literalAxSset =
      Formula.ex
        (.all (.all (Formula.biimp (literalPairMem 1 0 2) (Formula.subset 1 0)))) :=
  rfl

theorem axSi_source_equation :
    literalAxSi =
      .all
        (Formula.ex (.all (.all
              (Formula.biimp (literalSingletonPairMem 1 0 2) (literalPairMem 1 0 3))))) :=
  rfl

theorem axIns2_source_equation :
    literalAxIns2 =
      .all
        (Formula.ex (.all (.all (.all (Formula.biimp (literalInsertedPairMem 2 1 0 3)
                  (literalPairMem 2 0 4)))))) :=
  rfl

theorem axIns3_source_equation :
    literalAxIns3 =
      .all
        (Formula.ex (.all (.all (.all (Formula.biimp (literalInsertedPairMem 2 1 0 3)
                  (literalPairMem 2 1 4)))))) :=
  rfl

theorem axTypeLower_source_equation :
    literalAxTypeLower =
      .all
        (Formula.ex (.all
            (Formula.biimp (.mem 0 1) (.all (literalPairSingletonSecondMem 0 1 3))))) :=
  rfl

theorem axSn_source_equation :
    literalAxSn = .all (Formula.ex (.all (Formula.biimp (.mem 0 1) (.equal 0 2)))) :=
  rfl

/-- Literal sentence data, indexed by the exact eleven source labels. -/
@[expose]
def literalAxiomSyntax : HailperinAxiomName → Sentence
  | .axExt => literalAxExt
  | .axNin => literalAxNin
  | .axXp => literalAxXp
  | .axCnv => literalAxCnv
  | .ax1c => literalAx1c
  | .axSset => literalAxSset
  | .axSi => literalAxSi
  | .axIns2 => literalAxIns2
  | .axIns3 => literalAxIns3
  | .axTypeLower => literalAxTypeLower
  | .axSn => literalAxSn

@[expose]
def literalAxiomFormula (name : HailperinAxiomName) : Fol.sentence LNF :=
  Formula.toFlypitch (literalAxiomSyntax name)

abbrev LiteralHailperinNF : Fol.SentTheory LNF :=
  Set.range literalAxiomFormula

theorem literalAxiom_mem (name : HailperinAxiomName) :
    literalAxiomFormula name ∈ LiteralHailperinNF :=
  ⟨name, rfl⟩

abbrev LiteralSourceNFProvesNotChoiceTarget (sourceChoiceNF : Fol.sentence LNF) : Prop :=
  LiteralHailperinNF ⊢ₛ' (Fol.bd_not sourceChoiceNF)


end NFChoice.Foundation.ExactLiteralTrial
