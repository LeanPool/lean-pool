/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.CompactSyntaxFV

/-! NF weak partition development: CoreFVSimp. -/


public section

namespace NFChoice.Compiler.CoreFVSimp

open NFChoice.Foundation
open NFChoice.SemanticCore

/-! Shallow, nonrecursive simplification equations for semantic FV support. -/


@[simp]
theorem fv_class_cv (x : Var) : (Class.cv x).fv = ({ x } : Finset Var) := by rfl

@[simp]
theorem fv_class_cab (x : Var) (p : Wff) : (Class.cab x p).fv = p.fv.erase x := by rfl

@[simp]
theorem fv_wff_falsum : Wff.falsum.fv = (∅ : Finset Var) := by rfl

@[simp]
theorem fv_wff_imp (p q : Wff) : (Wff.imp p q).fv = p.fv ∪ q.fv := by rfl

@[simp]
theorem fv_wff_all (x : Var) (p : Wff) : (Wff.all x p).fv = p.fv.erase x := by rfl

@[simp]
theorem fv_wff_objEq (x y : Var) : (Wff.objEq x y).fv = ({ x, y } : Finset Var) := by rfl

@[simp]
theorem fv_wff_objMem (x y : Var) : (Wff.objMem x y).fv = ({ x, y } : Finset Var) := by
  rfl

@[simp]
theorem fv_wff_classEq (A B : Class) : (Wff.classEq A B).fv = A.fv ∪ B.fv := by rfl

@[simp]
theorem fv_wff_classMem (A B : Class) : (Wff.classMem A B).fv = A.fv ∪ B.fv := by rfl

@[simp]
theorem fv_wff_neg (p : Wff) : (Wff.neg p).fv = p.fv :=
  by
  ext u
  simp [Wff.neg, Wff.fv]

@[simp]
theorem fv_wff_conj (p q : Wff) : (Wff.conj p q).fv = p.fv ∪ q.fv :=
  by
  ext u
  simp [Wff.conj, Wff.neg, Wff.fv]

@[simp]
theorem fv_wff_disj (p q : Wff) : (Wff.disj p q).fv = p.fv ∪ q.fv :=
  by
  ext u
  simp [Wff.disj, Wff.neg, Wff.fv]

@[simp]
theorem fv_wff_biimp (p q : Wff) : (Wff.biimp p q).fv = p.fv ∪ q.fv :=
  by
  ext u
  simp [Wff.biimp, Wff.conj, Wff.neg, Wff.fv]
  tauto

@[simp]
theorem fv_wff_ex (x : Var) (p : Wff) : (Wff.ex x p).fv = p.fv.erase x :=
  by
  ext u
  simp [Wff.ex, Wff.neg, Wff.fv]


end NFChoice.Compiler.CoreFVSimp
