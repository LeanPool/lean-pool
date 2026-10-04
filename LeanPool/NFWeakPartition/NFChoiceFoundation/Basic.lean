/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Flypitch4.Completeness

/-! NF weak partition development: NFChoiceFoundation.Basic. -/


public section

namespace NFChoice.Foundation

open scoped Fol

/-! This file fixes the trusted first-order boundary for the NF choice experiment.
There are no nonlogical function symbols and membership is the sole
nonlogical predicate. Equality is Flypitch's logical equality.
-/


/-- The only nonlogical relation symbol of the language of NF. -/
inductive LNFRelation : Nat → Type
  | mem : LNFRelation 2

/-- The membership-only first-order language used for NF. -/
@[expose]
def LNF : Fol.Language where
  functions := fun _ => Empty
  relations := LNFRelation

/-! `Formula n` is a small intrinsically scoped front end. Its variables are
de Bruijn indices in `Fin n`. It has exactly Flypitch's primitive logical
constructors, specialized to the membership-only language.
-/


/-- Intrinsically scoped membership-only first-order formulas. -/
inductive Formula : Nat → Type
  | falsum : Formula n
  | equal : Fin n → Fin n → Formula n
  | mem : Fin n → Fin n → Formula n
  | imp : Formula n → Formula n → Formula n
  | all : Formula (n + 1) → Formula n

/-- A closed membership-only formula. -/
abbrev Sentence :=
  Formula 0

namespace Formula

/-- Negation, with falsity and implication as primitives. -/
@[expose]
def neg {n : Nat} (p : Formula n) : Formula n :=
  .imp p .falsum

/-- Classical conjunction in Flypitch's primitive basis. -/
@[expose]
def conj {n : Nat} (p q : Formula n) : Formula n :=
  neg (.imp p (neg q))

/-- Classical disjunction in Flypitch's primitive basis. -/
@[expose]
def disj {n : Nat} (p q : Formula n) : Formula n :=
  .imp (neg p) q

/-- Biconditional. -/
@[expose]
def biimp {n : Nat} (p q : Formula n) : Formula n :=
  conj (.imp p q) (.imp q p)

/-- Existential quantification, defined from universal quantification. -/
@[expose]
def ex {n : Nat} (p : Formula (n + 1)) : Formula n :=
  neg (.all (neg p))

/-- Apply the sole binary relation symbol to two bounded variables. -/
@[expose]
def memToFlypitch {n : Nat} (x y : Fol.boundedTerm LNF n) : Fol.boundedFormula LNF n :=
  Fol.bd_apprel (Fol.bd_apprel (Fol.bd_rel LNFRelation.mem) x) y

/-- Translate the small front end into Flypitch's bounded syntax. -/
@[expose]
def toFlypitch : {n : Nat} → Formula n → Fol.boundedFormula LNF n
  | _, .falsum => Fol.bd_falsum
  | _, .equal x y => Fol.bd_equal (Fol.bd_var x) (Fol.bd_var y)
  | _, .mem x y => memToFlypitch (Fol.bd_var x) (Fol.bd_var y)
  | _, .imp p q => Fol.bd_imp (toFlypitch p) (toFlypitch q)
  | _, .all p => Fol.bd_all (toFlypitch p)

/-- `s` is the singleton of `a`. -/
@[expose]
def singleton {n : Nat} (s a : Fin n) : Formula n :=
  .all (biimp (.mem 0 (Fin.succ s)) (.equal 0 (Fin.succ a)))

/-- `p` is the unordered pair of `a` and `b`. -/
@[expose]
def unorderedPair {n : Nat} (p a b : Fin n) : Formula n :=
  .all
    (biimp (.mem 0 (Fin.succ p)) (disj (.equal 0 (Fin.succ a)) (.equal 0 (Fin.succ b))))

/-- `a` is a subset of `b`. -/
@[expose]
def subset {n : Nat} (a b : Fin n) : Formula n :=
  .all (.imp (.mem 0 (Fin.succ a)) (.mem 0 (Fin.succ b)))

/-- `a` has an element. -/
@[expose]
def nonempty {n : Nat} (a : Fin n) : Formula n :=
  ex (.mem 0 (Fin.succ a))

/-- `y` is a singleton (of some object). -/
@[expose]
def isSomeSingleton {n : Nat} (y : Fin n) : Formula n :=
  ex (singleton (Fin.succ y) 0)

/-- `p` is the Kuratowski ordered pair of `a` and `b`. -/
@[expose]
def isKPair {n : Nat} (p a b : Fin n) : Formula n :=
  ex
    (ex (conj (singleton 1 (Fin.succ (Fin.succ a)))
        (conj (unorderedPair 0 (Fin.succ (Fin.succ a)) (Fin.succ (Fin.succ b)))
          (unorderedPair (Fin.succ (Fin.succ p)) 1 0))))

/-- `z` is the Kuratowski ordered pair of `a` and `b`. -/
@[expose]
def equalKPair {n : Nat} (z a b : Fin n) : Formula n :=
  ex (conj (isKPair 0 (Fin.succ a) (Fin.succ b)) (.equal (Fin.succ z) 0))

/-- The Kuratowski ordered pair of `a` and `b` belongs to `r`. -/
@[expose]
def pairMem {n : Nat} (a b r : Fin n) : Formula n :=
  ex (conj (isKPair 0 (Fin.succ a) (Fin.succ b)) (.mem 0 (Fin.succ r)))

/-- `d` is the double singleton of `a`. -/
@[expose]
def doubleSingleton {n : Nat} (d a : Fin n) : Formula n :=
  ex (conj (singleton 0 (Fin.succ a)) (singleton (Fin.succ d) 0))

/-- The ordered pair of the singletons of `a` and `b` belongs to `r`. -/
@[expose]
def singletonPairMem {n : Nat} (a b r : Fin n) : Formula n :=
  ex
    (ex (conj (singleton 1 (Fin.succ (Fin.succ a))) (conj (singleton 0 (Fin.succ (Fin.succ b)))
          (pairMem 1 0 (Fin.succ (Fin.succ r))))))

/-- `<< {{z}}, <<w,t>> >>` belongs to `r`. -/
@[expose]
def insertedPairMem {n : Nat} (z w t r : Fin n) : Formula n :=
  ex
    (ex (conj (doubleSingleton 1 (Fin.succ (Fin.succ z)))
        (conj (isKPair 0 (Fin.succ (Fin.succ w)) (Fin.succ (Fin.succ t)))
          (pairMem 1 0 (Fin.succ (Fin.succ r))))))

/-- The ordered pair of `a` and the singleton of `z` belongs to `r`. -/
@[expose]
def pairSingletonSecondMem {n : Nat} (a z r : Fin n) : Formula n :=
  ex (conj (singleton 0 (Fin.succ z)) (pairMem (Fin.succ a) 0 (Fin.succ r)))

/-! The direct first-order well-order predicate used in `ChoiceNF`. -/


/-- Proof-translation construction identified upstream as `reflexiveOn`. -/
@[expose]
def reflexiveOn {n : Nat} (r a : Fin n) : Formula n :=
  .all (.imp (.mem 0 (Fin.succ a)) (pairMem 0 0 (Fin.succ r)))

/-- Proof-translation construction identified upstream as `transitiveOn`. -/
@[expose]
def transitiveOn {n : Nat} (r a : Fin n) : Formula n :=
  .all
    (.imp (.mem 0 (Fin.succ a)) (.all (.imp (.mem 0 (Fin.succ (Fin.succ a))) (.all
            (.imp (.mem 0 (Fin.succ (Fin.succ (Fin.succ a)))) (.imp
                (conj (pairMem 2 1 (Fin.succ (Fin.succ (Fin.succ r))))
                  (pairMem 1 0 (Fin.succ (Fin.succ (Fin.succ r)))))
                (pairMem 2 0 (Fin.succ (Fin.succ (Fin.succ r))))))))))

/-- Proof-translation construction identified upstream as `antisymmetricOn`. -/
@[expose]
def antisymmetricOn {n : Nat} (r a : Fin n) : Formula n :=
  .all
    (.imp (.mem 0 (Fin.succ a)) (.all (.imp (.mem 0 (Fin.succ (Fin.succ a))) (.imp
            (conj (pairMem 1 0 (Fin.succ (Fin.succ r))) (pairMem 0 1 (Fin.succ (Fin.succ r))))
            (.equal 1 0)))))

/-- Proof-translation construction identified upstream as `connectedOn`. -/
@[expose]
def connectedOn {n : Nat} (r a : Fin n) : Formula n :=
  .all
    (.imp (.mem 0 (Fin.succ a)) (.all (.imp (.mem 0 (Fin.succ (Fin.succ a)))
          (disj (pairMem 1 0 (Fin.succ (Fin.succ r))) (pairMem 0 1 (Fin.succ (Fin.succ r)))))))

/-- Proof-translation construction identified upstream as `foundedOn`. -/
@[expose]
def foundedOn {n : Nat} (r a : Fin n) : Formula n :=
  .all
    (.imp (conj (subset 0 (Fin.succ a)) (nonempty 0)) (ex (conj (.mem 0 1) (.all
            (.imp (.mem 0 2)
              (.imp (pairMem 0 1 (Fin.succ (Fin.succ (Fin.succ r)))) (.equal 0 1)))))))

/-- `r` well-orders `a`, matching the order/foundation conventions of `df-we`. -/
@[expose]
def wellOrders {n : Nat} (r a : Fin n) : Formula n :=
  conj (reflexiveOn r a)
    (conj (transitiveOn r a)
      (conj (antisymmetricOn r a) (conj (connectedOn r a) (foundedOn r a))))

end Formula

/-! The eleven closed NF axioms below are the `nf.mm` source axioms `ax-ext`,
`ax-nin`, `ax-xp`, `ax-cnv`, `ax-1c`, `ax-sset`, `ax-si`, `ax-ins2`,
`ax-ins3`, `ax-typlower`, and `ax-sn`. Set-builder notation, singletons,
and ordered pairs are expanded into equality and membership.
-/


/-- Proof-translation construction identified upstream as `axExt`. -/
@[expose]
def axExt : Sentence :=
  .all (.all (.imp (.all (Formula.biimp (.mem 0 2) (.mem 0 1))) (.equal 1 0)))

/-- Proof-translation construction identified upstream as `axNin`. -/
@[expose]
def axNin : Sentence :=
  .all
    (.all (Formula.ex (.all
          (Formula.biimp (.mem 0 1) (Formula.neg (Formula.conj (.mem 0 3) (.mem 0 2)))))))

/-- Proof-translation construction identified upstream as `axXp`. -/
@[expose]
def axXp : Sentence :=
  .all
    (Formula.ex (.all (Formula.biimp (.mem 0 1) (Formula.ex
            (Formula.ex (Formula.conj (Formula.equalKPair 2 1 0) (.mem 0 4)))))))

/-- Proof-translation construction identified upstream as `axCnv`. -/
@[expose]
def axCnv : Sentence :=
  .all
    (Formula.ex (.all (.all (Formula.biimp (Formula.pairMem 1 0 2) (Formula.pairMem 0 1 3)))))

/-- Proof-translation construction identified upstream as `ax1c`. -/
@[expose]
def ax1c : Sentence :=
  Formula.ex (.all (Formula.biimp (.mem 0 1) (Formula.isSomeSingleton 0)))

/-- Proof-translation construction identified upstream as `axSset`. -/
@[expose]
def axSset : Sentence :=
  Formula.ex (.all (.all (Formula.biimp (Formula.pairMem 1 0 2) (Formula.subset 1 0))))

/-- Proof-translation construction identified upstream as `axSi`. -/
@[expose]
def axSi : Sentence :=
  .all
    (Formula.ex (.all
        (.all (Formula.biimp (Formula.singletonPairMem 1 0 2) (Formula.pairMem 1 0 3)))))

/-- Proof-translation construction identified upstream as `axIns2`. -/
@[expose]
def axIns2 : Sentence :=
  .all
    (Formula.ex (.all (.all (.all
            (Formula.biimp (Formula.insertedPairMem 2 1 0 3) (Formula.pairMem 2 0 4))))))

/-- Proof-translation construction identified upstream as `axIns3`. -/
@[expose]
def axIns3 : Sentence :=
  .all
    (Formula.ex (.all (.all (.all
            (Formula.biimp (Formula.insertedPairMem 2 1 0 3) (Formula.pairMem 2 1 4))))))

/-- Proof-translation construction identified upstream as `axTypeLower`. -/
@[expose]
def axTypeLower : Sentence :=
  .all
    (Formula.ex (.all (Formula.biimp (.mem 0 1) (.all (Formula.pairSingletonSecondMem 0 1 3)))))

/-- The singleton-existence axiom added to Metamath's Hailperin-derived NF basis.
Metamath credits contributor SF on 12 January 2015; it identifies this as an addition
missing from Hailperin's presentation. See <https://us.metamath.org/nfeuni/ax-sn.html>.
-/
@[expose]
def axSn : Sentence :=
  .all (Formula.ex (.all (Formula.biimp (.mem 0 1) (.equal 0 2))))

/-- The exact eleven source labels in the finite NF basis. -/
inductive HailperinAxiomName
  | axExt
  | axNin
  | axXp
  | axCnv
  | ax1c
  | axSset
  | axSi
  | axIns2
  | axIns3
  | axTypeLower
  | axSn
  deriving DecidableEq, Repr

/-- The closed membership-only sentence named by each source axiom. -/
@[expose]
def axiomSyntax : HailperinAxiomName → Sentence
  | .axExt => axExt
  | .axNin => axNin
  | .axXp => axXp
  | .axCnv => axCnv
  | .ax1c => ax1c
  | .axSset => axSset
  | .axSi => axSi
  | .axIns2 => axIns2
  | .axIns3 => axIns3
  | .axTypeLower => axTypeLower
  | .axSn => axSn

/-- The Flypitch sentence corresponding to a named NF axiom. -/
@[expose]
def axiomFormula (name : HailperinAxiomName) : Fol.sentence LNF :=
  Formula.toFlypitch (axiomSyntax name)

/-- The eleven-sentence Metamath Hailperin-derived NF presentation, including `axSn`. -/
abbrev HailperinNF : Fol.SentTheory LNF :=
  Set.range axiomFormula

/-- Every named axiom belongs to the finite theory. -/
theorem axiom_mem_HailperinNF (name : HailperinAxiomName) :
    axiomFormula name ∈ HailperinNF :=
  ⟨name, rfl⟩

/-- A direct membership-only statement that every set admits a well-order. -/
@[expose]
def ChoiceNFSyntax : Sentence :=
  .all (Formula.ex (Formula.wellOrders 0 1))

/-- The choice sentence at the Flypitch boundary. -/
@[expose]
def ChoiceNF : Fol.sentence LNF :=
  Formula.toFlypitch ChoiceNFSyntax

/-- The target interface for an exact source-generated choice sentence. A generated
module supplies its concrete `SourceChoiceNF`; this foundation does not identify
that sentence with the direct comparison sentence `ChoiceNF`.
-/
abbrev SourceNFProvesNotChoiceTarget (SourceChoiceNF : Fol.sentence LNF) : Prop :=
  HailperinNF ⊢ₛ' (Fol.bdNot SourceChoiceNF)

/-- The comparison target for the direct every-set-is-well-orderable sentence. -/
abbrev DirectNFProvesNotChoiceTarget : Prop :=
  SourceNFProvesNotChoiceTarget ChoiceNF

/-- Completeness specialized to any exact source-generated choice sentence. -/
theorem source_not_choice_completeness_bridge (SourceChoiceNF : Fol.sentence LNF) :
    (HailperinNF ⊢ₛ' (Fol.bdNot SourceChoiceNF)) ↔
      Fol.ssatisfied HailperinNF (Fol.bdNot SourceChoiceNF) :=
  Fol.completeness HailperinNF (Fol.bdNot SourceChoiceNF)

/-- The exact syntactic/semantic bridge supplied by Gödel completeness. -/
theorem NF_not_choice_completeness_bridge :
    (HailperinNF ⊢ₛ' (Fol.bdNot ChoiceNF)) ↔
      Fol.ssatisfied HailperinNF (Fol.bdNot ChoiceNF) :=
  source_not_choice_completeness_bridge ChoiceNF

end NFChoice.Foundation
