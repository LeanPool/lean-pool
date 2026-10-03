/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.SemanticCore.LiteralFoundation

/-! NF weak partition development: SemanticCore.Lowering. -/


public section

namespace NFChoice.SemanticCore.Lowering

open NFChoice.Foundation

/-- Read a bounded valuation at a `Fin` index. -/
@[expose]
def lookup {S : Type _} {n : Nat} (xs : DVec S n) (i : Fin n) : S :=
  xs.nth i.1 i.2

@[simp]
theorem lookup_cons_zero {S : Type _} {n : Nat} (a : S) (xs : DVec S n) :
    lookup (DVec.cons a xs) 0 = a := by simp [lookup, DVec.nth]

@[simp]
theorem lookup_cons_succ {S : Type _} {n : Nat} (a : S) (xs : DVec S n) (i : Fin n) :
    lookup (DVec.cons a xs) (Fin.succ i) = lookup xs i := by simp [lookup, DVec.nth]

/-- Shift an environment under one newly introduced de Bruijn binder. -/
@[expose]
def liftRho {n : Nat} (rho : Var → Fin n) : Var → Fin (n + 1) := fun x => Fin.succ (rho x)

/-- Shift an environment and bind nominal name `x` at de Bruijn index zero. -/
@[expose]
def bindRho {n : Nat} (rho : Var → Fin n) (x : Var) : Var → Fin (n + 1) :=
  Function.update (liftRho rho) x 0

mutual
  /-- Lower class membership-at-a-candidate to the literal membership language. -/
  @[expose]
  def lowerClassPred {n : Nat} (rho : Var → Fin n) (candidate : Fin n) : Class → Formula n
    | .cv x => .mem candidate (rho x)
    | .cab x p => lowerWff (Function.update rho x candidate) p
  /-- Compositional lowering of the nominal core to intrinsically scoped FOL. -/
  @[expose]
  def lowerWff {n : Nat} (rho : Var → Fin n) : Wff → Formula n
    | .falsum => .falsum
    | .imp p q => .imp (lowerWff rho p) (lowerWff rho q)
    | .all x p => .all (lowerWff (bindRho rho x) p)
    | .objEq x y => .equal (rho x) (rho y)
    | .objMem x y => .mem (rho x) (rho y)
    | .classEq A B =>
      .all
        (Formula.biimp (lowerClassPred (liftRho rho) 0 A) (lowerClassPred (liftRho rho) 0 B))
    | .classMem A B =>
      Formula.ex
        (Formula.conj
          (.all (Formula.biimp (.mem 0 1) (lowerClassPred (liftRho (liftRho rho)) 0 A)))
          (lowerClassPred (liftRho rho) 0 B))
end

/-- Direct semantics of the small intrinsically scoped formula front end. -/
@[expose]
def FormulaHolds (S : Fol.Structure LNF) : {n : Nat} → DVec S n → Formula n → Prop
  | _, _, .falsum => False
  | _, xs, .equal x y => lookup xs x = lookup xs y
  | _, xs, .mem x y => Mem S (lookup xs x) (lookup xs y)
  | _, xs, .imp p q => FormulaHolds S xs p → FormulaHolds S xs q
  | _, xs, .all p => ∀ a : S, FormulaHolds S (DVec.cons a xs) p

@[simp]
theorem formulaHolds_neg {S : Fol.Structure LNF} {n : Nat} {xs : DVec S n}
    {p : Formula n} : FormulaHolds S xs (Formula.neg p) ↔ ¬FormulaHolds S xs p :=
  Iff.rfl

@[simp]
theorem formulaHolds_conj {S : Fol.Structure LNF} {n : Nat} {xs : DVec S n}
    {p q : Formula n} :
    FormulaHolds S xs (Formula.conj p q) ↔ FormulaHolds S xs p ∧ FormulaHolds S xs q :=
  by
  simp only [Formula.conj, Formula.neg, FormulaHolds]
  tauto

@[simp]
theorem formulaHolds_biimp {S : Fol.Structure LNF} {n : Nat} {xs : DVec S n}
    {p q : Formula n} :
    FormulaHolds S xs (Formula.biimp p q) ↔ (FormulaHolds S xs p ↔ FormulaHolds S xs q) :=
  by
  simp only [Formula.biimp, formulaHolds_conj, FormulaHolds]
  tauto

@[simp]
theorem formulaHolds_ex {S : Fol.Structure LNF} {n : Nat} {xs : DVec S n}
    {p : Formula (n + 1)} :
    FormulaHolds S xs (Formula.ex p) ↔ ∃ a : S, FormulaHolds S (DVec.cons a xs) p :=
  by
  simp only [Formula.ex, Formula.neg, FormulaHolds]
  constructor
  · intro h
    by_contra hn
    apply h
    intro a ha
    exact hn ⟨a, ha⟩
  · rintro ⟨a, ha⟩ h
    exact h a ha

mutual
  /-- Semantic correctness of class-predicate lowering. -/
  theorem lowerClassPred_sound {S : Fol.Structure LNF} {n : Nat} (rho : Var → Fin n)
      (xs : DVec S n) (v : Var → S) (hrho : ∀ x, lookup xs (rho x) = v x)
      (candidate : Fin n) (A : Class) :
      Class.Holds S v A (lookup xs candidate) ↔
        FormulaHolds S xs (lowerClassPred rho candidate A) :=
    by
    cases A with
    | cv x =>
      simp only [Class.Holds, lowerClassPred, FormulaHolds]
      rw [hrho x]
    | cab x p =>
      simp only [Class.Holds, lowerClassPred]
      apply
        lowerWff_sound (Function.update rho x candidate) xs
          (update v x (lookup xs candidate))
      intro y
      by_cases hyx : y = x
      · subst y
        simp [update]
      · simp [Function.update, update, hyx, hrho]
  /-- Semantic correctness of nominal-wff lowering. -/
  theorem lowerWff_sound {S : Fol.Structure LNF} {n : Nat} (rho : Var → Fin n)
      (xs : DVec S n) (v : Var → S) (hrho : ∀ x, lookup xs (rho x) = v x) (p : Wff) :
      Wff.Holds S v p ↔ FormulaHolds S xs (lowerWff rho p) := by
    cases p with
    | falsum => rfl
    | imp p q =>
      simp only [Wff.Holds, lowerWff, FormulaHolds]
      exact Iff.imp (lowerWff_sound rho xs v hrho p) (lowerWff_sound rho xs v hrho q)
    | all x p =>
      simp only [Wff.Holds, lowerWff, FormulaHolds]
      apply forall_congr'
      intro a
      apply lowerWff_sound (bindRho rho x) (DVec.cons a xs) (update v x a)
      intro y
      by_cases hyx : y = x
      · subst y
        simp [bindRho, update]
      · simp [bindRho, liftRho, Function.update, update, hyx, hrho]
    | objEq x y =>
      simp only [Wff.Holds, lowerWff, FormulaHolds]
      rw [hrho x, hrho y]
    | objMem x y =>
      simp only [Wff.Holds, lowerWff, FormulaHolds]
      rw [hrho x, hrho y]
    | classEq A
      B =>
      simp only [Wff.Holds, lowerWff, FormulaHolds, formulaHolds_biimp]
      apply forall_congr'
      intro a
      have hA :=
        lowerClassPred_sound (liftRho rho) (DVec.cons a xs) v
          (fun x => by simp [liftRho, hrho]) 0 A
      have hB :=
        lowerClassPred_sound (liftRho rho) (DVec.cons a xs) v
          (fun x => by simp [liftRho, hrho]) 0 B
      simp only [lookup_cons_zero] at hA hB
      tauto
    | classMem A
      B =>
      simp only [Wff.Holds, lowerWff, formulaHolds_ex, formulaHolds_conj, FormulaHolds,
        formulaHolds_biimp]
      apply exists_congr
      intro a
      apply and_congr
      · apply forall_congr'
        intro z
        have hA :=
          lowerClassPred_sound (liftRho (liftRho rho)) (DVec.cons z (DVec.cons a xs)) v
            (fun x => by simp [liftRho, hrho]) 0 A
        simp only [lookup_cons_zero] at hA
        tauto
      · have hB :=
          lowerClassPred_sound (liftRho rho) (DVec.cons a xs) v
            (fun x => by simp [liftRho, hrho]) 0 B
        simpa using hB
end

/-- The direct front-end semantics agrees with Flypitch realization. -/
theorem formulaHolds_toFlypitch :
    ∀ {S : Fol.Structure LNF} {n : Nat} (xs : DVec S n) (p : Formula n),
      FormulaHolds S xs p ↔ Fol.realize_bounded_formula xs (Formula.toFlypitch p) DVec.nil
  | _, _, _, .falsum => Iff.rfl
  | _, _, _, .equal _ _ => Iff.rfl
  | _, _, _, .mem _ _ => Iff.rfl
  | _, _, xs, .imp p q =>
    by
    simp only [FormulaHolds, Formula.toFlypitch, Fol.realize_bounded_formula]
    exact Iff.imp (formulaHolds_toFlypitch xs p) (formulaHolds_toFlypitch xs q)
  | _, _, xs, .all p =>
    by
    simp only [FormulaHolds, Formula.toFlypitch, Fol.realize_bounded_formula]
    apply forall_congr'
    intro a
    exact formulaHolds_toFlypitch (DVec.cons a xs) p

/-- End-to-end correctness of nominal lowering at the Flypitch boundary. -/
theorem lowerWff_realize_iff {S : Fol.Structure LNF} {n : Nat} (rho : Var → Fin n)
    (xs : DVec S n) (v : Var → S) (hrho : ∀ x, lookup xs (rho x) = v x) (p : Wff) :
    Wff.Holds S v p ↔
      Fol.realize_bounded_formula xs (Formula.toFlypitch (lowerWff rho p)) DVec.nil :=
  (lowerWff_sound rho xs v hrho p).trans (formulaHolds_toFlypitch xs (lowerWff rho p))

end NFChoice.SemanticCore.Lowering
