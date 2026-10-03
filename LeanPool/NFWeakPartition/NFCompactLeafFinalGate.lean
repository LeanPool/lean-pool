/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NFCompactLeafEndpoints

/-! NF weak partition development: NFCompactLeafFinalGate. -/


public section

namespace NFChoice.Compiler.NFCompactLeafFinalGate

open scoped Fol
open NFChoice.Foundation
open NFChoice.Foundation.ExactLiteralTrial
open NFChoice.SemanticCore
open NFChoice.SemanticCore.Lowering
open NFChoice.Compiler.CompactSourceSyntax
open NFChoice.Compiler.NFCompactLeafEndpoints

theorem holds_xp_rhs {S : Fol.Structure LNF} (hExt : Extensional S) (v : Var → S)
    (x y z w t : Var) (hxw : x ≠ w) (hxt : x ≠ t) (_hyw : y ≠ w) (_hyt : y ≠ t)
    (hzw : z ≠ w) (hzt : z ≠ t) (hwt : w ≠ t) :
    Wff.Holds S v
        (syn_wex w (syn_wex t
            (syn_wa (.classEq (.cv z) (syn_copk (.cv w) (.cv t))) (.objMem t x)))) ↔
      FormulaHolds S (DVec.cons (v z) (DVec.cons (v y) (DVec.cons (v x) DVec.nil)))
        (Formula.ex (Formula.ex (Formula.conj (literalKPair 2 1 0) (.mem 0 4)))) :=
  by
  change
    Wff.Holds S v
        (Wff.ex w (Wff.ex t
            (Wff.conj (.classEq (.cv z) (syn_copk (.cv w) (.cv t))) (.objMem t x)))) ↔
      _
  simp only [Wff.holds_ex, formulaHolds_ex]
  apply exists_congr
  intro W
  apply exists_congr
  intro T
  simp only [Wff.holds_conj, formulaHolds_conj]
  apply and_congr
  · apply
      holds_literalKPair hExt (update (update v w W) t T)
        (DVec.cons T
          (DVec.cons W (DVec.cons (v z) (DVec.cons (v y) (DVec.cons (v x) DVec.nil)))))
        z w t 2 1 0
    · simp only [ne_eq, hzt, not_false_eq_true, update_noteq, hzw, Nat.reduceAdd,
        Fin.isValue]
      change v z = v z
      rfl
    · simp only [ne_eq, hwt, not_false_eq_true, update_noteq, update_same, Nat.reduceAdd,
        Fin.isValue]
      change W = W
      rfl
    · simp
  · simp only [Wff.Holds, update_same, ne_eq, hxt, not_false_eq_true, update_noteq, hxw,
      FormulaHolds, Nat.reduceAdd, Fin.isValue, lookup_cons_zero]
    change Mem S T (v x) ↔ Mem S T (v x)
    rfl

theorem axXpCompact {S : Fol.Structure LNF}
    (hNF : Fol.all_realize_sentence S LiteralHailperinNF) (x y z w t : Var) (hxy : x ≠ y)
    (hxz : x ≠ z) (hxw : x ≠ w) (hxt : x ≠ t) (hyz : y ≠ z) (hyw : y ≠ w) (hyt : y ≠ t)
    (hzw : z ≠ w) (hzt : z ≠ t) (hwt : w ≠ t) :
    Wff.Valid S
      (syn_wex y (.all z (syn_wb (.objMem z y) (syn_wex w (syn_wex t
                (syn_wa (.classEq (.cv z) (syn_copk (.cv w) (.cv t))) (.objMem t x))))))) :=
  by
  have hExt := NFChoice.ReplaySupport.extensional_of_literal_model hNF
  have hLit : FormulaHolds S DVec.nil literalAxXp :=
    (formulaHolds_toFlypitch DVec.nil literalAxXp).2
      (NFChoice.ReplaySupport.realizes_literal_axiom hNF .axXp)
  intro v
  apply Wff.holds_ex.mpr
  rcases formulaHolds_ex.mp (hLit (v x)) with ⟨Y, hY⟩
  refine ⟨Y, ?_⟩
  intro Z
  apply Wff.holds_biimp.mpr
  have hiff := formulaHolds_biimp.mp (hY Z)
  calc
    Wff.Holds S (update (update v y Y) z Z) (.objMem z y) ↔
        FormulaHolds S (DVec.cons Z (DVec.cons Y (DVec.cons (v x) DVec.nil)))
          (.mem 0 1) :=
      by
      simp only [Wff.Holds, update_same, ne_eq, hyz, not_false_eq_true, update_noteq,
        FormulaHolds, Nat.reduceAdd, Fin.isValue, lookup_cons_zero]
      change Mem S Z Y ↔ Mem S Z Y
      rfl
    _ ↔
        FormulaHolds S (DVec.cons Z (DVec.cons Y (DVec.cons (v x) DVec.nil)))
          (Formula.ex (Formula.ex (Formula.conj (literalKPair 2 1 0) (.mem 0 4)))) :=
      hiff
    _ ↔
        Wff.Holds S (update (update v y Y) z Z)
          (syn_wex w (syn_wex t
              (syn_wa (.classEq (.cv z) (syn_copk (.cv w) (.cv t))) (.objMem t x)))) :=
      by
      symm
      simpa [update_noteq, hxy, hxz, hyz] using
        (holds_xp_rhs hExt (update (update v y Y) z Z) x y z w t hxw hxt hyw hyt hzw hzt hwt)

theorem axCnvCompact {S : Fol.Structure LNF}
    (hNF : Fol.all_realize_sentence S LiteralHailperinNF) (x y z w : Var) (hxy : x ≠ y)
    (hxz : x ≠ z) (hxw : x ≠ w) (hyz : y ≠ z) (hyw : y ≠ w) (hzw : z ≠ w) :
    Wff.Valid S
      (syn_wex y (.all z (.all w (syn_wb (.classMem (syn_copk (.cv z) (.cv w)) (.cv y))
              (.classMem (syn_copk (.cv w) (.cv z)) (.cv x)))))) :=
  by
  have hExt := NFChoice.ReplaySupport.extensional_of_literal_model hNF
  have hLit : FormulaHolds S DVec.nil literalAxCnv :=
    (formulaHolds_toFlypitch DVec.nil literalAxCnv).2
      (NFChoice.ReplaySupport.realizes_literal_axiom hNF .axCnv)
  intro v
  apply Wff.holds_ex.mpr
  rcases formulaHolds_ex.mp (hLit (v x)) with ⟨Y, hY⟩
  refine ⟨Y, ?_⟩
  intro Z W
  apply Wff.holds_biimp.mpr
  have hiff := formulaHolds_biimp.mp (hY Z W)
  let v' := update (update (update v y Y) z Z) w W
  let xs := DVec.cons W (DVec.cons Z (DVec.cons Y (DVec.cons (v x) DVec.nil)))
  have hz : v' z = lookup xs (1 : Fin 4) :=
    by
    simp only [ne_eq, hzw, not_false_eq_true, update_noteq, update_same, Nat.reduceAdd,
      Fin.isValue, v', xs]
    change Z = Z
    rfl
  have hw : v' w = lookup xs (0 : Fin 4) := by simp [v', xs]
  have hy : v' y = lookup xs (2 : Fin 4) :=
    by
    simp only [ne_eq, hyw, not_false_eq_true, update_noteq, hyz, update_same,
      Nat.reduceAdd, Fin.isValue, v', xs]
    change Y = Y
    rfl
  have hx : v' x = lookup xs (3 : Fin 4) :=
    by
    simp only [ne_eq, hxw, not_false_eq_true, update_noteq, hxz, hxy, Nat.reduceAdd,
      Fin.isValue, v', xs]
    change v x = v x
    rfl
  calc
    Wff.Holds S v' (.classMem (syn_copk (.cv z) (.cv w)) (.cv y)) ↔
        FormulaHolds S xs (literalPairMem 1 0 2) :=
      holds_literalPairMem hExt v' xs z w y 1 0 2 hz hw hy
    _ ↔ FormulaHolds S xs (literalPairMem 0 1 3) := by simpa [xs] using hiff
    _ ↔ Wff.Holds S v' (.classMem (syn_copk (.cv w) (.cv z)) (.cv x)) :=
      (holds_literalPairMem hExt v' xs w z x 0 1 3 hw hz hx).symm

theorem holds_literalSubset {S : Fol.Structure LNF} {n : Nat} (v : Var → S)
    (xs : DVec S n) (y z w : Var) (iy iz : Fin n) (hy : v y = lookup xs iy)
    (hz : v z = lookup xs iz) (hyw : y ≠ w) (hzw : z ≠ w) :
    Wff.Holds S v (.all w (.imp (.objMem w y) (.objMem w z))) ↔
      FormulaHolds S xs (Formula.subset iy iz) :=
  by
  simp only [Wff.Holds, Formula.subset, FormulaHolds]
  apply forall_congr'
  intro a
  simp only [lookup_cons_zero, lookup_cons_succ]
  rw [show update v w a y = lookup xs iy by simpa [update_noteq, hyw] using hy]
  rw [show update v w a z = lookup xs iz by simpa [update_noteq, hzw] using hz]
  simp [update_same]

theorem axSsetCompact {S : Fol.Structure LNF}
    (hNF : Fol.all_realize_sentence S LiteralHailperinNF) (x y z w : Var) (hxy : x ≠ y)
    (hxz : x ≠ z) (_hxw : x ≠ w) (hyz : y ≠ z) (hyw : y ≠ w) (hzw : z ≠ w) :
    Wff.Valid S
      (syn_wex x (.all y (.all z (syn_wb (.classMem (syn_copk (.cv y) (.cv z)) (.cv x))
              (.all w (.imp (.objMem w y) (.objMem w z))))))) :=
  by
  have hExt := NFChoice.ReplaySupport.extensional_of_literal_model hNF
  have hLit : FormulaHolds S DVec.nil literalAxSset :=
    (formulaHolds_toFlypitch DVec.nil literalAxSset).2
      (NFChoice.ReplaySupport.realizes_literal_axiom hNF .axSset)
  intro v
  apply Wff.holds_ex.mpr
  rcases formulaHolds_ex.mp hLit with ⟨X, hX⟩
  refine ⟨X, ?_⟩
  intro Y Z
  apply Wff.holds_biimp.mpr
  have hiff := formulaHolds_biimp.mp (hX Y Z)
  let v' := update (update (update v x X) y Y) z Z
  let xs := DVec.cons Z (DVec.cons Y (DVec.cons X DVec.nil))
  have hz : v' z = lookup xs (0 : Fin 3) := by simp [v', xs]
  have hy : v' y = lookup xs (1 : Fin 3) :=
    by
    simp only [ne_eq, hyz, not_false_eq_true, update_noteq, update_same, Nat.reduceAdd,
      Fin.isValue, v', xs]
    change Y = Y
    rfl
  have hx : v' x = lookup xs (2 : Fin 3) :=
    by
    simp only [ne_eq, hxz, not_false_eq_true, update_noteq, hxy, update_same,
      Nat.reduceAdd, Fin.isValue, v', xs]
    change X = X
    rfl
  calc
    Wff.Holds S v' (.classMem (syn_copk (.cv y) (.cv z)) (.cv x)) ↔
        FormulaHolds S xs (literalPairMem 1 0 2) :=
      holds_literalPairMem hExt v' xs y z x 1 0 2 hy hz hx
    _ ↔ FormulaHolds S xs (Formula.subset 1 0) := by simpa [xs] using hiff
    _ ↔ Wff.Holds S v' (.all w (.imp (.objMem w y) (.objMem w z))) :=
      (holds_literalSubset v' xs y z w 1 0 hy hz hyw hzw).symm

theorem axSiCompact {S : Fol.Structure LNF}
    (hNF : Fol.all_realize_sentence S LiteralHailperinNF) (x y z w : Var) (hxy : x ≠ y)
    (hxz : x ≠ z) (hxw : x ≠ w) (hyz : y ≠ z) (hyw : y ≠ w) (hzw : z ≠ w) :
    Wff.Valid S
      (syn_wex y (.all z (.all w
            (syn_wb (.classMem (syn_copk (syn_csn (.cv z)) (syn_csn (.cv w))) (.cv y))
              (.classMem (syn_copk (.cv z) (.cv w)) (.cv x)))))) :=
  by
  have hExt := NFChoice.ReplaySupport.extensional_of_literal_model hNF
  have hLit : FormulaHolds S DVec.nil literalAxSi :=
    (formulaHolds_toFlypitch DVec.nil literalAxSi).2
      (NFChoice.ReplaySupport.realizes_literal_axiom hNF .axSi)
  intro v
  apply Wff.holds_ex.mpr
  rcases formulaHolds_ex.mp (hLit (v x)) with ⟨Y, hY⟩
  refine ⟨Y, ?_⟩
  intro Z W
  apply Wff.holds_biimp.mpr
  have hiff := formulaHolds_biimp.mp (hY Z W)
  let v' := update (update (update v y Y) z Z) w W
  let xs := DVec.cons W (DVec.cons Z (DVec.cons Y (DVec.cons (v x) DVec.nil)))
  have hz : v' z = lookup xs (1 : Fin 4) :=
    by
    simp only [ne_eq, hzw, not_false_eq_true, update_noteq, update_same, Nat.reduceAdd,
      Fin.isValue, v', xs]
    change Z = Z
    rfl
  have hw : v' w = lookup xs (0 : Fin 4) := by simp [v', xs]
  have hy : v' y = lookup xs (2 : Fin 4) :=
    by
    simp only [ne_eq, hyw, not_false_eq_true, update_noteq, hyz, update_same,
      Nat.reduceAdd, Fin.isValue, v', xs]
    change Y = Y
    rfl
  have hx : v' x = lookup xs (3 : Fin 4) :=
    by
    simp only [ne_eq, hxw, not_false_eq_true, update_noteq, hxz, hxy, Nat.reduceAdd,
      Fin.isValue, v', xs]
    change v x = v x
    rfl
  calc
    Wff.Holds S v' (.classMem (syn_copk (syn_csn (.cv z)) (syn_csn (.cv w))) (.cv y)) ↔
        FormulaHolds S xs (literalSingletonPairMem 1 0 2) :=
      holds_literalSingletonPairMem hExt v' xs z w y 1 0 2 hz hw hy
    _ ↔ FormulaHolds S xs (literalPairMem 1 0 3) := by simpa [xs] using hiff
    _ ↔ Wff.Holds S v' (.classMem (syn_copk (.cv z) (.cv w)) (.cv x)) :=
      (holds_literalPairMem hExt v' xs z w x 1 0 3 hz hw hx).symm

theorem axIns2Compact {S : Fol.Structure LNF}
    (hNF : Fol.all_realize_sentence S LiteralHailperinNF) (x y z w t : Var) (hxy : x ≠ y)
    (hxz : x ≠ z) (hxw : x ≠ w) (hxt : x ≠ t) (hyz : y ≠ z) (hyw : y ≠ w) (hyt : y ≠ t)
    (hzw : z ≠ w) (hzt : z ≠ t) (hwt : w ≠ t) :
    Wff.Valid S
      (syn_wex y (.all z (.all w (.all t (syn_wb (.classMem
                  (syn_copk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv w) (.cv t))) (.cv y))
                (.classMem (syn_copk (.cv z) (.cv t)) (.cv x))))))) :=
  by
  have hExt := NFChoice.ReplaySupport.extensional_of_literal_model hNF
  have hLit : FormulaHolds S DVec.nil literalAxIns2 :=
    (formulaHolds_toFlypitch DVec.nil literalAxIns2).2
      (NFChoice.ReplaySupport.realizes_literal_axiom hNF .axIns2)
  intro v
  apply Wff.holds_ex.mpr
  rcases formulaHolds_ex.mp (hLit (v x)) with ⟨Y, hY⟩
  refine ⟨Y, ?_⟩
  intro Z W T
  apply Wff.holds_biimp.mpr
  have hiff := formulaHolds_biimp.mp (hY Z W T)
  let v' := update (update (update (update v y Y) z Z) w W) t T
  let xs :=
    DVec.cons T (DVec.cons W (DVec.cons Z (DVec.cons Y (DVec.cons (v x) DVec.nil))))
  have ht : v' t = lookup xs (0 : Fin 5) := by simp [v', xs]
  have hw : v' w = lookup xs (1 : Fin 5) :=
    by
    simp only [ne_eq, hwt, not_false_eq_true, update_noteq, update_same, Nat.reduceAdd,
      Fin.isValue, v', xs]
    change W = W
    rfl
  have hz : v' z = lookup xs (2 : Fin 5) :=
    by
    simp only [ne_eq, hzt, not_false_eq_true, update_noteq, hzw, update_same,
      Nat.reduceAdd, Fin.isValue, v', xs]
    change Z = Z
    rfl
  have hy : v' y = lookup xs (3 : Fin 5) :=
    by
    simp only [ne_eq, hyt, not_false_eq_true, update_noteq, hyw, hyz, update_same,
      Nat.reduceAdd, Fin.isValue, v', xs]
    change Y = Y
    rfl
  have hx : v' x = lookup xs (4 : Fin 5) :=
    by
    simp only [ne_eq, hxt, not_false_eq_true, update_noteq, hxw, hxz, hxy, Nat.reduceAdd,
      Fin.isValue, v', xs]
    change v x = v x
    rfl
  calc
    Wff.Holds S v'
          (.classMem (syn_copk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv w) (.cv t)))
            (.cv y)) ↔
        FormulaHolds S xs (literalInsertedPairMem 2 1 0 3) :=
      holds_literalInsertedPairMem hExt v' xs z w t y 2 1 0 3 hz hw ht hy
    _ ↔ FormulaHolds S xs (literalPairMem 2 0 4) := by simpa [xs] using hiff
    _ ↔ Wff.Holds S v' (.classMem (syn_copk (.cv z) (.cv t)) (.cv x)) :=
      (holds_literalPairMem hExt v' xs z t x 2 0 4 hz ht hx).symm

theorem axIns3Compact {S : Fol.Structure LNF}
    (hNF : Fol.all_realize_sentence S LiteralHailperinNF) (x y z w t : Var) (hxy : x ≠ y)
    (hxz : x ≠ z) (hxw : x ≠ w) (hxt : x ≠ t) (hyz : y ≠ z) (hyw : y ≠ w) (hyt : y ≠ t)
    (hzw : z ≠ w) (hzt : z ≠ t) (hwt : w ≠ t) :
    Wff.Valid S
      (syn_wex y (.all z (.all w (.all t (syn_wb (.classMem
                  (syn_copk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv w) (.cv t))) (.cv y))
                (.classMem (syn_copk (.cv z) (.cv w)) (.cv x))))))) :=
  by
  have hExt := NFChoice.ReplaySupport.extensional_of_literal_model hNF
  have hLit : FormulaHolds S DVec.nil literalAxIns3 :=
    (formulaHolds_toFlypitch DVec.nil literalAxIns3).2
      (NFChoice.ReplaySupport.realizes_literal_axiom hNF .axIns3)
  intro v
  apply Wff.holds_ex.mpr
  rcases formulaHolds_ex.mp (hLit (v x)) with ⟨Y, hY⟩
  refine ⟨Y, ?_⟩
  intro Z W T
  apply Wff.holds_biimp.mpr
  have hiff := formulaHolds_biimp.mp (hY Z W T)
  let v' := update (update (update (update v y Y) z Z) w W) t T
  let xs :=
    DVec.cons T (DVec.cons W (DVec.cons Z (DVec.cons Y (DVec.cons (v x) DVec.nil))))
  have ht : v' t = lookup xs (0 : Fin 5) := by simp [v', xs]
  have hw : v' w = lookup xs (1 : Fin 5) :=
    by
    simp only [ne_eq, hwt, not_false_eq_true, update_noteq, update_same, Nat.reduceAdd,
      Fin.isValue, v', xs]
    change W = W
    rfl
  have hz : v' z = lookup xs (2 : Fin 5) :=
    by
    simp only [ne_eq, hzt, not_false_eq_true, update_noteq, hzw, update_same,
      Nat.reduceAdd, Fin.isValue, v', xs]
    change Z = Z
    rfl
  have hy : v' y = lookup xs (3 : Fin 5) :=
    by
    simp only [ne_eq, hyt, not_false_eq_true, update_noteq, hyw, hyz, update_same,
      Nat.reduceAdd, Fin.isValue, v', xs]
    change Y = Y
    rfl
  have hx : v' x = lookup xs (4 : Fin 5) :=
    by
    simp only [ne_eq, hxt, not_false_eq_true, update_noteq, hxw, hxz, hxy, Nat.reduceAdd,
      Fin.isValue, v', xs]
    change v x = v x
    rfl
  calc
    Wff.Holds S v'
          (.classMem (syn_copk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv w) (.cv t)))
            (.cv y)) ↔
        FormulaHolds S xs (literalInsertedPairMem 2 1 0 3) :=
      holds_literalInsertedPairMem hExt v' xs z w t y 2 1 0 3 hz hw ht hy
    _ ↔ FormulaHolds S xs (literalPairMem 2 1 4) := by simpa [xs] using hiff
    _ ↔ Wff.Holds S v' (.classMem (syn_copk (.cv z) (.cv w)) (.cv x)) :=
      (holds_literalPairMem hExt v' xs z w x 2 1 4 hz hw hx).symm

theorem holds_typlower_rhs {S : Fol.Structure LNF} (hExt : Extensional S) (v : Var → S)
    (x y z w : Var) (hxw : x ≠ w) (hzw : z ≠ w) :
    Wff.Holds S v (.all w (.classMem (syn_copk (.cv w) (syn_csn (.cv z))) (.cv x))) ↔
      FormulaHolds S (DVec.cons (v z) (DVec.cons (v y) (DVec.cons (v x) DVec.nil)))
        (.all (literalPairSingletonSecondMem 0 1 3)) :=
  by
  simp only [Wff.Holds, FormulaHolds]
  apply forall_congr'
  intro W
  apply
    holds_literalPairSingletonSecondMem hExt (update v w W)
      (DVec.cons W (DVec.cons (v z) (DVec.cons (v y) (DVec.cons (v x) DVec.nil)))) w z x 0
      1 3
  · simp
  · simp only [ne_eq, hzw, not_false_eq_true, update_noteq, Nat.reduceAdd, Fin.isValue]
    change v z = v z
    rfl
  · simp only [ne_eq, hxw, not_false_eq_true, update_noteq, Nat.reduceAdd, Fin.isValue]
    change v x = v x
    rfl

theorem axTypeLowerCompact {S : Fol.Structure LNF}
    (hNF : Fol.all_realize_sentence S LiteralHailperinNF) (x y z w : Var) (hxy : x ≠ y)
    (hxz : x ≠ z) (hxw : x ≠ w) (hyz : y ≠ z) (_hyw : y ≠ w) (hzw : z ≠ w) :
    Wff.Valid S
      (syn_wex y (.all z (syn_wb (.objMem z y)
            (.all w (.classMem (syn_copk (.cv w) (syn_csn (.cv z))) (.cv x)))))) :=
  by
  have hExt := NFChoice.ReplaySupport.extensional_of_literal_model hNF
  have hLit : FormulaHolds S DVec.nil literalAxTypeLower :=
    (formulaHolds_toFlypitch DVec.nil literalAxTypeLower).2
      (NFChoice.ReplaySupport.realizes_literal_axiom hNF .axTypeLower)
  intro v
  apply Wff.holds_ex.mpr
  rcases formulaHolds_ex.mp (hLit (v x)) with ⟨Y, hY⟩
  refine ⟨Y, ?_⟩
  intro Z
  apply Wff.holds_biimp.mpr
  have hiff := formulaHolds_biimp.mp (hY Z)
  let v' := update (update v y Y) z Z
  let xs := DVec.cons Z (DVec.cons Y (DVec.cons (v x) DVec.nil))
  calc
    Wff.Holds S v' (.objMem z y) ↔ FormulaHolds S xs (.mem 0 1) :=
      by
      simp only [Wff.Holds, update_same, ne_eq, hyz, not_false_eq_true, update_noteq,
        FormulaHolds, Nat.reduceAdd, Fin.isValue, lookup_cons_zero, v', xs]
      change Mem S Z Y ↔ Mem S Z Y
      rfl
    _ ↔ FormulaHolds S xs (.all (literalPairSingletonSecondMem 0 1 3)) := by
      simpa [xs] using hiff
    _ ↔
        Wff.Holds S v'
          (.all w (.classMem (syn_copk (.cv w) (syn_csn (.cv z))) (.cv x))) :=
      by
      symm
      simpa [v', xs, update_noteq, hxy, hxz, hyz] using
        (holds_typlower_rhs hExt v' x y z w hxw hzw)


end NFChoice.Compiler.NFCompactLeafFinalGate
