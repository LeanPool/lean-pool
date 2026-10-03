/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C090C001Block005

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C090C001Part020`. -/


section

namespace NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

open scoped Fol
open NFChoice.Foundation
open NFChoice.Foundation.ExactLiteralTrial
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax
open NFChoice.Compiler.CompactSyntaxFVExplicit
open NFChoice.Compiler.WPPCompactSyntaxFVExplicit
open NFChoice.Compiler.CoreFVSimp
open NFChoice.DefinitionLeaves.AlphaFocusedSupport
open NFChoice.DefinitionLeaves.AlphaFocusedFV
open NFChoice.DirectNominalPrf
open NFChoice.DirectNominalPrf.Nominal

theorem nb090_support_mem_0635 (h : Var) :
    (nb090_alpha_dummy_427 h) ∈
      (((syn_ccompl (Class.cab (nb090_alpha_dummy_583 h)
              (syn_wrex (nb090_alpha_dummy_584 h) (Class.cv (nb090_alpha_dummy_428 h))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_583 h))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_584 h)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb090_alpha_dummy_583 h)
              (syn_wrex (nb090_alpha_dummy_584 h) (Class.cv (nb090_alpha_dummy_427 h))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_583 h))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_584 h)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090_alpha_dummy_427 h) ≠ (nb090_alpha_dummy_583 h) from (by
          unfold nb090_alpha_dummy_583;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0634 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090_alpha_dummy_427 h) ≠ (nb090_alpha_dummy_584 h) from (by
            unfold nb090_alpha_dummy_584;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0634 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0636 (A : Class) :
    (nb090_alpha_dummy_424 A) ∈
      (((Class.cab (nb090_alpha_dummy_581 A)
            (syn_wrex (nb090_alpha_dummy_582 A) (Class.cv (nb090_alpha_dummy_424 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_581 A))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_582 A)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_581 A)
            (syn_wrex (nb090_alpha_dummy_582 A) (Class.cv (nb090_alpha_dummy_424 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_581 A))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_582 A)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090_alpha_dummy_424 A) ≠ (nb090_alpha_dummy_581 A) from (by
          unfold nb090_alpha_dummy_581;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0632 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090_alpha_dummy_424 A) ≠ (nb090_alpha_dummy_582 A) from (by
            unfold nb090_alpha_dummy_582;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0632 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0637 (h : Var) :
    (nb090_alpha_dummy_427 h) ∈
      (((Class.cab (nb090_alpha_dummy_583 h)
            (syn_wrex (nb090_alpha_dummy_584 h) (Class.cv (nb090_alpha_dummy_427 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_583 h))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_584 h)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_583 h)
            (syn_wrex (nb090_alpha_dummy_584 h) (Class.cv (nb090_alpha_dummy_427 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_583 h))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_584 h)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090_alpha_dummy_427 h) ≠ (nb090_alpha_dummy_583 h) from (by
          unfold nb090_alpha_dummy_583;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0634 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090_alpha_dummy_427 h) ≠ (nb090_alpha_dummy_584 h) from (by
            unfold nb090_alpha_dummy_584;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0634 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0638 (A : Class) :
    (nb090_alpha_dummy_582 A) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_582 A))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0639 (h : Var) :
    (nb090_alpha_dummy_584 h) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_584 h))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0640 (A : Class) :
    (nb090_alpha_dummy_582 A) ∈
      (((syn_cphi (Class.cv (nb090_alpha_dummy_582 A)))).fv ∪
        ((syn_cphi (Class.cv (nb090_alpha_dummy_582 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0641 (h : Var) :
    (nb090_alpha_dummy_584 h) ∈
      (((syn_cphi (Class.cv (nb090_alpha_dummy_584 h)))).fv ∪
        ((syn_cphi (Class.cv (nb090_alpha_dummy_584 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0642 (A : Class) :
    (nb090_alpha_dummy_001 A) ∈
      (((Class.cv (nb090_alpha_dummy_000 A))).fv ∪
              ((syn_cfv (syn_c1st) (Class.cv (nb090_alpha_dummy_001 A)))).fv ∪
            ((syn_cfv (syn_c1st) (Class.cv (nb090_alpha_dummy_002 A)))).fv ∪
          ((syn_cfv (syn_c2nd) (Class.cv (nb090_alpha_dummy_001 A)))).fv ∪
        ((syn_cfv (syn_c2nd) (Class.cv (nb090_alpha_dummy_002 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_cfv]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0643 (v : Var) (u : Var) (h : Var) :
    u ∈
      (((Class.cv h)).fv ∪ ((syn_cfv (syn_c1st) (Class.cv u))).fv ∪
            ((syn_cfv (syn_c1st) (Class.cv v))).fv ∪ ((syn_cfv (syn_c2nd) (Class.cv u))).fv ∪
        ((syn_cfv (syn_c2nd) (Class.cv v))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_cfv]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0644 (A : Class) :
    (nb090_alpha_dummy_041 A) ∈
      (((Class.cv (nb090_alpha_dummy_041 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_042 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0645 (A : Class) :
    (nb090_alpha_dummy_041 A) ∈
      (((syn_ccompl (Class.cab (nb090_alpha_dummy_617 A)
              (syn_wrex (nb090_alpha_dummy_618 A) (Class.cv (nb090_alpha_dummy_041 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_617 A))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_618 A)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb090_alpha_dummy_617 A)
              (syn_wrex (nb090_alpha_dummy_618 A) (Class.cv (nb090_alpha_dummy_042 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_617 A))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_618 A)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090_alpha_dummy_041 A) ≠ (nb090_alpha_dummy_617 A) from (by
          unfold nb090_alpha_dummy_617;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0644 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090_alpha_dummy_041 A) ≠ (nb090_alpha_dummy_618 A) from (by
            unfold nb090_alpha_dummy_618;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0644 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0646 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_043 v u h) ∈
      (((Class.cv (nb090_alpha_dummy_043 v u h))).fv ∪
        ((Class.cv (nb090_alpha_dummy_044 v u h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0647 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_043 v u h) ∈
      (((syn_ccompl (Class.cab (nb090_alpha_dummy_619 v u h)
              (syn_wrex (nb090_alpha_dummy_620 v u h) (Class.cv (nb090_alpha_dummy_043 v u h))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_619 v u h))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_620 v u h)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb090_alpha_dummy_619 v u h) (syn_wrex (nb090_alpha_dummy_620 v u h)
                (Class.cv (nb090_alpha_dummy_044 v u h))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_619 v u h))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_620 v u h)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090_alpha_dummy_043 v u h) ≠ (nb090_alpha_dummy_619 v u h) from (by
          unfold nb090_alpha_dummy_619;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0646 v u h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090_alpha_dummy_043 v u h) ≠ (nb090_alpha_dummy_620 v u h) from (by
            unfold nb090_alpha_dummy_620;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0646 v u h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0648 (A : Class) :
    (nb090_alpha_dummy_041 A) ∈
      (((Class.cab (nb090_alpha_dummy_617 A)
            (syn_wrex (nb090_alpha_dummy_618 A) (Class.cv (nb090_alpha_dummy_041 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_617 A))
                (syn_cphi (Class.cv (nb090_alpha_dummy_618 A))))))).fv ∪
        ((Class.cab (nb090_alpha_dummy_617 A)
            (syn_wrex (nb090_alpha_dummy_618 A) (Class.cv (nb090_alpha_dummy_041 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_617 A))
                (syn_cphi (Class.cv (nb090_alpha_dummy_618 A))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090_alpha_dummy_041 A) ≠ (nb090_alpha_dummy_617 A) from (by
          unfold nb090_alpha_dummy_617;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0644 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090_alpha_dummy_041 A) ≠ (nb090_alpha_dummy_618 A) from (by
            unfold nb090_alpha_dummy_618;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0644 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0649 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_043 v u h) ∈
      (((Class.cab (nb090_alpha_dummy_619 v u h) (syn_wrex (nb090_alpha_dummy_620 v u h)
              (Class.cv (nb090_alpha_dummy_043 v u h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_619 v u h))
                (syn_cphi (Class.cv (nb090_alpha_dummy_620 v u h))))))).fv ∪
        ((Class.cab (nb090_alpha_dummy_619 v u h) (syn_wrex (nb090_alpha_dummy_620 v u h)
              (Class.cv (nb090_alpha_dummy_043 v u h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_619 v u h))
                (syn_cphi (Class.cv (nb090_alpha_dummy_620 v u h))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090_alpha_dummy_043 v u h) ≠ (nb090_alpha_dummy_619 v u h) from (by
          unfold nb090_alpha_dummy_619;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0646 v u h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090_alpha_dummy_043 v u h) ≠ (nb090_alpha_dummy_620 v u h) from (by
            unfold nb090_alpha_dummy_620;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0646 v u h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0650 (A : Class) :
    (nb090_alpha_dummy_618 A) ∈ (((Class.cv (nb090_alpha_dummy_618 A))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0651 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_620 v u h) ∈ (((Class.cv (nb090_alpha_dummy_620 v u h))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0652 (A : Class) :
    (nb090_alpha_dummy_625 A) ∈
      (((Wff.classMem (Class.cv (nb090_alpha_dummy_625 A)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb090_alpha_dummy_625 A)) (syn_c1c))).fv ∪
        ((Class.cv (nb090_alpha_dummy_625 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_wff_classMem]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0653 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_627 v u h) ∈
      (((Wff.classMem (Class.cv (nb090_alpha_dummy_627 v u h)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb090_alpha_dummy_627 v u h)) (syn_c1c))).fv ∪
        ((Class.cv (nb090_alpha_dummy_627 v u h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_wff_classMem]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0654 (A : Class) :
    (nb090_alpha_dummy_625 A) ∈
      (((Class.cv (nb090_alpha_dummy_625 A))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0655 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_627 v u h) ∈
      (((Class.cv (nb090_alpha_dummy_627 v u h))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0656 (A : Class) :
    (nb090_alpha_dummy_632 A) ∈
      (((syn_cnin (Class.cv (nb090_alpha_dummy_632 A))
            (Class.cv (nb090_alpha_dummy_633 A)))).fv ∪
        ((syn_cnin (Class.cv (nb090_alpha_dummy_632 A))
            (Class.cv (nb090_alpha_dummy_633 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0657 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_635 v u h) ∈
      (((syn_cnin (Class.cv (nb090_alpha_dummy_635 v u h))
            (Class.cv (nb090_alpha_dummy_636 v u h)))).fv ∪
        ((syn_cnin (Class.cv (nb090_alpha_dummy_635 v u h))
            (Class.cv (nb090_alpha_dummy_636 v u h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0658 (A : Class) :
    (nb090_alpha_dummy_632 A) ∈
      (((Class.cv (nb090_alpha_dummy_632 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_633 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0659 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_635 v u h) ∈
      (((Class.cv (nb090_alpha_dummy_635 v u h))).fv ∪
        ((Class.cv (nb090_alpha_dummy_636 v u h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0660 (A : Class) :
    (nb090_alpha_dummy_633 A) ∈
      (((syn_cnin (Class.cv (nb090_alpha_dummy_632 A))
            (Class.cv (nb090_alpha_dummy_633 A)))).fv ∪
        ((syn_cnin (Class.cv (nb090_alpha_dummy_632 A))
            (Class.cv (nb090_alpha_dummy_633 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0661 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_636 v u h) ∈
      (((syn_cnin (Class.cv (nb090_alpha_dummy_635 v u h))
            (Class.cv (nb090_alpha_dummy_636 v u h)))).fv ∪
        ((syn_cnin (Class.cv (nb090_alpha_dummy_635 v u h))
            (Class.cv (nb090_alpha_dummy_636 v u h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0662 (A : Class) :
    (nb090_alpha_dummy_633 A) ∈
      (((Class.cv (nb090_alpha_dummy_632 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_633 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0663 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_636 v u h) ∈
      (((Class.cv (nb090_alpha_dummy_635 v u h))).fv ∪
        ((Class.cv (nb090_alpha_dummy_636 v u h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0664 (A : Class) :
    (nb090_alpha_dummy_632 A) ∈
      (((syn_ccompl (Class.cv (nb090_alpha_dummy_632 A)))).fv ∪
        ((syn_ccompl (Class.cv (nb090_alpha_dummy_633 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0665 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_635 v u h) ∈
      (((syn_ccompl (Class.cv (nb090_alpha_dummy_635 v u h)))).fv ∪
        ((syn_ccompl (Class.cv (nb090_alpha_dummy_636 v u h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0666 (A : Class) :
    (nb090_alpha_dummy_632 A) ∈
      (((Class.cv (nb090_alpha_dummy_632 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_632 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0667 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_635 v u h) ∈
      (((Class.cv (nb090_alpha_dummy_635 v u h))).fv ∪
        ((Class.cv (nb090_alpha_dummy_635 v u h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0668 (A : Class) :
    (nb090_alpha_dummy_633 A) ∈
      (((syn_ccompl (Class.cv (nb090_alpha_dummy_632 A)))).fv ∪
        ((syn_ccompl (Class.cv (nb090_alpha_dummy_633 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0669 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_636 v u h) ∈
      (((syn_ccompl (Class.cv (nb090_alpha_dummy_635 v u h)))).fv ∪
        ((syn_ccompl (Class.cv (nb090_alpha_dummy_636 v u h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0670 (A : Class) :
    (nb090_alpha_dummy_633 A) ∈
      (((Class.cv (nb090_alpha_dummy_633 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_633 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0671 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_636 v u h) ∈
      (((Class.cv (nb090_alpha_dummy_636 v u h))).fv ∪
        ((Class.cv (nb090_alpha_dummy_636 v u h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0672 (A : Class) :
    (nb090_alpha_dummy_042 A) ∈
      (((Class.cv (nb090_alpha_dummy_041 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_042 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0673 (A : Class) :
    (nb090_alpha_dummy_042 A) ∈
      (((syn_ccompl (Class.cab (nb090_alpha_dummy_617 A)
              (syn_wrex (nb090_alpha_dummy_618 A) (Class.cv (nb090_alpha_dummy_041 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_617 A))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_618 A)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb090_alpha_dummy_617 A)
              (syn_wrex (nb090_alpha_dummy_618 A) (Class.cv (nb090_alpha_dummy_042 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_617 A))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_618 A)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090_alpha_dummy_042 A) ≠ (nb090_alpha_dummy_617 A) from (by
          unfold nb090_alpha_dummy_617;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0672 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090_alpha_dummy_042 A) ≠ (nb090_alpha_dummy_618 A) from (by
            unfold nb090_alpha_dummy_618;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0672 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0674 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_044 v u h) ∈
      (((Class.cv (nb090_alpha_dummy_043 v u h))).fv ∪
        ((Class.cv (nb090_alpha_dummy_044 v u h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0675 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_044 v u h) ∈
      (((syn_ccompl (Class.cab (nb090_alpha_dummy_619 v u h)
              (syn_wrex (nb090_alpha_dummy_620 v u h) (Class.cv (nb090_alpha_dummy_043 v u h))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_619 v u h))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_620 v u h)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb090_alpha_dummy_619 v u h) (syn_wrex (nb090_alpha_dummy_620 v u h)
                (Class.cv (nb090_alpha_dummy_044 v u h))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_619 v u h))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_620 v u h)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090_alpha_dummy_044 v u h) ≠ (nb090_alpha_dummy_619 v u h) from (by
          unfold nb090_alpha_dummy_619;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0674 v u h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090_alpha_dummy_044 v u h) ≠ (nb090_alpha_dummy_620 v u h) from (by
            unfold nb090_alpha_dummy_620;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0674 v u h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0676 (A : Class) :
    (nb090_alpha_dummy_042 A) ∈
      (((Class.cab (nb090_alpha_dummy_617 A)
            (syn_wrex (nb090_alpha_dummy_618 A) (Class.cv (nb090_alpha_dummy_042 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_617 A))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_618 A)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_617 A)
            (syn_wrex (nb090_alpha_dummy_618 A) (Class.cv (nb090_alpha_dummy_042 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_617 A))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_618 A)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090_alpha_dummy_042 A) ≠ (nb090_alpha_dummy_617 A) from (by
          unfold nb090_alpha_dummy_617;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0672 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090_alpha_dummy_042 A) ≠ (nb090_alpha_dummy_618 A) from (by
            unfold nb090_alpha_dummy_618;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0672 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0677 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_044 v u h) ∈
      (((Class.cab (nb090_alpha_dummy_619 v u h) (syn_wrex (nb090_alpha_dummy_620 v u h)
              (Class.cv (nb090_alpha_dummy_044 v u h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_619 v u h))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_620 v u h)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_619 v u h)
            (syn_wrex (nb090_alpha_dummy_620 v u h) (Class.cv (nb090_alpha_dummy_044 v u h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_619 v u h))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_620 v u h)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090_alpha_dummy_044 v u h) ≠ (nb090_alpha_dummy_619 v u h) from (by
          unfold nb090_alpha_dummy_619;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0674 v u h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090_alpha_dummy_044 v u h) ≠ (nb090_alpha_dummy_620 v u h) from (by
            unfold nb090_alpha_dummy_620;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0674 v u h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0678 (A : Class) :
    (nb090_alpha_dummy_618 A) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_618 A))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0679 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_620 v u h) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_620 v u h))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0680 (A : Class) :
    (nb090_alpha_dummy_618 A) ∈
      (((syn_cphi (Class.cv (nb090_alpha_dummy_618 A)))).fv ∪
        ((syn_cphi (Class.cv (nb090_alpha_dummy_618 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0681 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_620 v u h) ∈
      (((syn_cphi (Class.cv (nb090_alpha_dummy_620 v u h)))).fv ∪
        ((syn_cphi (Class.cv (nb090_alpha_dummy_620 v u h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0682 (A : Class) :
    (nb090_alpha_dummy_001 A) ∈
      (((syn_c1st)).fv ∪ ((Class.cv (nb090_alpha_dummy_001 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0683 (A : Class) :
    (nb090_alpha_dummy_001 A) ∈
      (({(nb090_alpha_dummy_653 A)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb090_alpha_dummy_001 A)) (syn_c1st)
            (Class.cv (nb090_alpha_dummy_653 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_wbr]
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0684 (A : Class) :
    (nb090_alpha_dummy_001 A) ∈
      (((Class.cab (nb090_alpha_dummy_655 A) (Wff.classEq (Class.cab (nb090_alpha_dummy_653 A)
              (syn_wbr (Class.cv (nb090_alpha_dummy_001 A)) (syn_c1st)
                (Class.cv (nb090_alpha_dummy_653 A))))
            (syn_csn (Class.cv (nb090_alpha_dummy_655 A)))))).fv) :=
  by
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090_alpha_dummy_001 A) ≠ (nb090_alpha_dummy_655 A) from (by
          unfold nb090_alpha_dummy_655;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0683 A) 0))))
  · rw [fv_wff_classEq]
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cab]
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090_alpha_dummy_001 A) ≠ (nb090_alpha_dummy_653 A) from (by
            unfold nb090_alpha_dummy_653;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0682 A) 0))))
    · rw [fv_syn_wbr]
      with_reducible rw [Finset.mem_union]
      left
      with_reducible rw [Finset.mem_union]
      left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0685 (u : Var) : u ∈ (((syn_c1st)).fv ∪ ((Class.cv u)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0686 (u : Var) :
    u ∈
      (({(nb090_alpha_dummy_654 u)} : Finset Var) ∪
        ((syn_wbr (Class.cv u) (syn_c1st) (Class.cv (nb090_alpha_dummy_654 u)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_wbr]
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0687 (u : Var) :
    u ∈
      (((Class.cab (nb090_alpha_dummy_656 u) (Wff.classEq (Class.cab (nb090_alpha_dummy_654 u)
              (syn_wbr (Class.cv u) (syn_c1st) (Class.cv (nb090_alpha_dummy_654 u))))
            (syn_csn (Class.cv (nb090_alpha_dummy_656 u)))))).fv) :=
  by
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show u ≠ (nb090_alpha_dummy_656 u) from (by
          unfold nb090_alpha_dummy_656;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0686 u) 0))))
  · rw [fv_wff_classEq]
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cab]
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show u ≠ (nb090_alpha_dummy_654 u) from (by
            unfold nb090_alpha_dummy_654;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0685 u) 0))))
    · rw [fv_syn_wbr]
      with_reducible rw [Finset.mem_union]
      left
      with_reducible rw [Finset.mem_union]
      left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0688 (A : Class) :
    (nb090_alpha_dummy_001 A) ∈
      (((Class.cv (nb090_alpha_dummy_001 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_653 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0689 (A : Class) :
    (nb090_alpha_dummy_001 A) ∈
      (((syn_ccompl (Class.cab (nb090_alpha_dummy_661 A)
              (syn_wrex (nb090_alpha_dummy_662 A) (Class.cv (nb090_alpha_dummy_001 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_661 A))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_662 A)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb090_alpha_dummy_661 A)
              (syn_wrex (nb090_alpha_dummy_662 A) (Class.cv (nb090_alpha_dummy_653 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_661 A))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_662 A)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090_alpha_dummy_001 A) ≠ (nb090_alpha_dummy_661 A) from (by
          unfold nb090_alpha_dummy_661;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0688 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090_alpha_dummy_001 A) ≠ (nb090_alpha_dummy_662 A) from (by
            unfold nb090_alpha_dummy_662;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0688 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0690 (u : Var) :
    u ∈ (((Class.cv u)).fv ∪ ((Class.cv (nb090_alpha_dummy_654 u))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0691 (u : Var) :
    u ∈
      (((syn_ccompl (Class.cab (nb090_alpha_dummy_663 u)
              (syn_wrex (nb090_alpha_dummy_664 u) (Class.cv u)
                (Wff.classEq (Class.cv (nb090_alpha_dummy_663 u))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_664 u)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb090_alpha_dummy_663 u)
              (syn_wrex (nb090_alpha_dummy_664 u) (Class.cv (nb090_alpha_dummy_654 u))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_663 u))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_664 u)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show u ≠ (nb090_alpha_dummy_663 u) from (by
          unfold nb090_alpha_dummy_663;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0690 u) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show u ≠ (nb090_alpha_dummy_664 u) from (by
            unfold nb090_alpha_dummy_664;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0690 u) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0692 (A : Class) :
    (nb090_alpha_dummy_001 A) ∈
      (((Class.cab (nb090_alpha_dummy_661 A)
            (syn_wrex (nb090_alpha_dummy_662 A) (Class.cv (nb090_alpha_dummy_001 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_661 A))
                (syn_cphi (Class.cv (nb090_alpha_dummy_662 A))))))).fv ∪
        ((Class.cab (nb090_alpha_dummy_661 A)
            (syn_wrex (nb090_alpha_dummy_662 A) (Class.cv (nb090_alpha_dummy_001 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_661 A))
                (syn_cphi (Class.cv (nb090_alpha_dummy_662 A))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090_alpha_dummy_001 A) ≠ (nb090_alpha_dummy_661 A) from (by
          unfold nb090_alpha_dummy_661;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0688 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090_alpha_dummy_001 A) ≠ (nb090_alpha_dummy_662 A) from (by
            unfold nb090_alpha_dummy_662;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0688 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0693 (u : Var) :
    u ∈
      (((Class.cab (nb090_alpha_dummy_663 u) (syn_wrex (nb090_alpha_dummy_664 u) (Class.cv u)
              (Wff.classEq (Class.cv (nb090_alpha_dummy_663 u))
                (syn_cphi (Class.cv (nb090_alpha_dummy_664 u))))))).fv ∪
        ((Class.cab (nb090_alpha_dummy_663 u) (syn_wrex (nb090_alpha_dummy_664 u) (Class.cv u)
              (Wff.classEq (Class.cv (nb090_alpha_dummy_663 u))
                (syn_cphi (Class.cv (nb090_alpha_dummy_664 u))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show u ≠ (nb090_alpha_dummy_663 u) from (by
          unfold nb090_alpha_dummy_663;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0690 u) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show u ≠ (nb090_alpha_dummy_664 u) from (by
            unfold nb090_alpha_dummy_664;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0690 u) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0694 (A : Class) :
    (nb090_alpha_dummy_662 A) ∈ (((Class.cv (nb090_alpha_dummy_662 A))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0695 (u : Var) :
    (nb090_alpha_dummy_664 u) ∈ (((Class.cv (nb090_alpha_dummy_664 u))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0696 (A : Class) :
    (nb090_alpha_dummy_669 A) ∈
      (((Wff.classMem (Class.cv (nb090_alpha_dummy_669 A)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb090_alpha_dummy_669 A)) (syn_c1c))).fv ∪
        ((Class.cv (nb090_alpha_dummy_669 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_wff_classMem]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0697 (u : Var) :
    (nb090_alpha_dummy_671 u) ∈
      (((Wff.classMem (Class.cv (nb090_alpha_dummy_671 u)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb090_alpha_dummy_671 u)) (syn_c1c))).fv ∪
        ((Class.cv (nb090_alpha_dummy_671 u))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_wff_classMem]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0698 (A : Class) :
    (nb090_alpha_dummy_669 A) ∈
      (((Class.cv (nb090_alpha_dummy_669 A))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0699 (u : Var) :
    (nb090_alpha_dummy_671 u) ∈
      (((Class.cv (nb090_alpha_dummy_671 u))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0700 (A : Class) :
    (nb090_alpha_dummy_676 A) ∈
      (((syn_cnin (Class.cv (nb090_alpha_dummy_676 A))
            (Class.cv (nb090_alpha_dummy_677 A)))).fv ∪
        ((syn_cnin (Class.cv (nb090_alpha_dummy_676 A))
            (Class.cv (nb090_alpha_dummy_677 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0701 (u : Var) :
    (nb090_alpha_dummy_679 u) ∈
      (((syn_cnin (Class.cv (nb090_alpha_dummy_679 u))
            (Class.cv (nb090_alpha_dummy_680 u)))).fv ∪
        ((syn_cnin (Class.cv (nb090_alpha_dummy_679 u))
            (Class.cv (nb090_alpha_dummy_680 u)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0702 (A : Class) :
    (nb090_alpha_dummy_676 A) ∈
      (((Class.cv (nb090_alpha_dummy_676 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_677 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0703 (u : Var) :
    (nb090_alpha_dummy_679 u) ∈
      (((Class.cv (nb090_alpha_dummy_679 u))).fv ∪ ((Class.cv (nb090_alpha_dummy_680 u))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0704 (A : Class) :
    (nb090_alpha_dummy_677 A) ∈
      (((syn_cnin (Class.cv (nb090_alpha_dummy_676 A))
            (Class.cv (nb090_alpha_dummy_677 A)))).fv ∪
        ((syn_cnin (Class.cv (nb090_alpha_dummy_676 A))
            (Class.cv (nb090_alpha_dummy_677 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0705 (u : Var) :
    (nb090_alpha_dummy_680 u) ∈
      (((syn_cnin (Class.cv (nb090_alpha_dummy_679 u))
            (Class.cv (nb090_alpha_dummy_680 u)))).fv ∪
        ((syn_cnin (Class.cv (nb090_alpha_dummy_679 u))
            (Class.cv (nb090_alpha_dummy_680 u)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0706 (A : Class) :
    (nb090_alpha_dummy_677 A) ∈
      (((Class.cv (nb090_alpha_dummy_676 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_677 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0707 (u : Var) :
    (nb090_alpha_dummy_680 u) ∈
      (((Class.cv (nb090_alpha_dummy_679 u))).fv ∪ ((Class.cv (nb090_alpha_dummy_680 u))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0708 (A : Class) :
    (nb090_alpha_dummy_676 A) ∈
      (((syn_ccompl (Class.cv (nb090_alpha_dummy_676 A)))).fv ∪
        ((syn_ccompl (Class.cv (nb090_alpha_dummy_677 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0709 (u : Var) :
    (nb090_alpha_dummy_679 u) ∈
      (((syn_ccompl (Class.cv (nb090_alpha_dummy_679 u)))).fv ∪
        ((syn_ccompl (Class.cv (nb090_alpha_dummy_680 u)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0710 (A : Class) :
    (nb090_alpha_dummy_676 A) ∈
      (((Class.cv (nb090_alpha_dummy_676 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_676 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0711 (u : Var) :
    (nb090_alpha_dummy_679 u) ∈
      (((Class.cv (nb090_alpha_dummy_679 u))).fv ∪ ((Class.cv (nb090_alpha_dummy_679 u))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0712 (A : Class) :
    (nb090_alpha_dummy_677 A) ∈
      (((syn_ccompl (Class.cv (nb090_alpha_dummy_676 A)))).fv ∪
        ((syn_ccompl (Class.cv (nb090_alpha_dummy_677 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0713 (u : Var) :
    (nb090_alpha_dummy_680 u) ∈
      (((syn_ccompl (Class.cv (nb090_alpha_dummy_679 u)))).fv ∪
        ((syn_ccompl (Class.cv (nb090_alpha_dummy_680 u)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0714 (A : Class) :
    (nb090_alpha_dummy_677 A) ∈
      (((Class.cv (nb090_alpha_dummy_677 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_677 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0715 (u : Var) :
    (nb090_alpha_dummy_680 u) ∈
      (((Class.cv (nb090_alpha_dummy_680 u))).fv ∪ ((Class.cv (nb090_alpha_dummy_680 u))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0716 (A : Class) :
    (nb090_alpha_dummy_653 A) ∈
      (((Class.cv (nb090_alpha_dummy_001 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_653 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0717 (A : Class) :
    (nb090_alpha_dummy_653 A) ∈
      (((syn_ccompl (Class.cab (nb090_alpha_dummy_661 A)
              (syn_wrex (nb090_alpha_dummy_662 A) (Class.cv (nb090_alpha_dummy_001 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_661 A))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_662 A)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb090_alpha_dummy_661 A)
              (syn_wrex (nb090_alpha_dummy_662 A) (Class.cv (nb090_alpha_dummy_653 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_661 A))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_662 A)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090_alpha_dummy_653 A) ≠ (nb090_alpha_dummy_661 A) from (by
          unfold nb090_alpha_dummy_661;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0716 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090_alpha_dummy_653 A) ≠ (nb090_alpha_dummy_662 A) from (by
            unfold nb090_alpha_dummy_662;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0716 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0718 (u : Var) :
    (nb090_alpha_dummy_654 u) ∈
      (((Class.cv u)).fv ∪ ((Class.cv (nb090_alpha_dummy_654 u))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0719 (u : Var) :
    (nb090_alpha_dummy_654 u) ∈
      (((syn_ccompl (Class.cab (nb090_alpha_dummy_663 u)
              (syn_wrex (nb090_alpha_dummy_664 u) (Class.cv u)
                (Wff.classEq (Class.cv (nb090_alpha_dummy_663 u))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_664 u)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb090_alpha_dummy_663 u)
              (syn_wrex (nb090_alpha_dummy_664 u) (Class.cv (nb090_alpha_dummy_654 u))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_663 u))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_664 u)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090_alpha_dummy_654 u) ≠ (nb090_alpha_dummy_663 u) from (by
          unfold nb090_alpha_dummy_663;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0718 u) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090_alpha_dummy_654 u) ≠ (nb090_alpha_dummy_664 u) from (by
            unfold nb090_alpha_dummy_664;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0718 u) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0720 (A : Class) :
    (nb090_alpha_dummy_653 A) ∈
      (((Class.cab (nb090_alpha_dummy_661 A)
            (syn_wrex (nb090_alpha_dummy_662 A) (Class.cv (nb090_alpha_dummy_653 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_661 A))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_662 A)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_661 A)
            (syn_wrex (nb090_alpha_dummy_662 A) (Class.cv (nb090_alpha_dummy_653 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_661 A))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_662 A)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090_alpha_dummy_653 A) ≠ (nb090_alpha_dummy_661 A) from (by
          unfold nb090_alpha_dummy_661;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0716 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090_alpha_dummy_653 A) ≠ (nb090_alpha_dummy_662 A) from (by
            unfold nb090_alpha_dummy_662;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0716 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0721 (u : Var) :
    (nb090_alpha_dummy_654 u) ∈
      (((Class.cab (nb090_alpha_dummy_663 u)
            (syn_wrex (nb090_alpha_dummy_664 u) (Class.cv (nb090_alpha_dummy_654 u))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_663 u))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_664 u)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_663 u)
            (syn_wrex (nb090_alpha_dummy_664 u) (Class.cv (nb090_alpha_dummy_654 u))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_663 u))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_664 u)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090_alpha_dummy_654 u) ≠ (nb090_alpha_dummy_663 u) from (by
          unfold nb090_alpha_dummy_663;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0718 u) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090_alpha_dummy_654 u) ≠ (nb090_alpha_dummy_664 u) from (by
            unfold nb090_alpha_dummy_664;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0718 u) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0722 (A : Class) :
    (nb090_alpha_dummy_662 A) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_662 A))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0723 (u : Var) :
    (nb090_alpha_dummy_664 u) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_664 u))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0724 (A : Class) :
    (nb090_alpha_dummy_662 A) ∈
      (((syn_cphi (Class.cv (nb090_alpha_dummy_662 A)))).fv ∪
        ((syn_cphi (Class.cv (nb090_alpha_dummy_662 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0725 (u : Var) :
    (nb090_alpha_dummy_664 u) ∈
      (((syn_cphi (Class.cv (nb090_alpha_dummy_664 u)))).fv ∪
        ((syn_cphi (Class.cv (nb090_alpha_dummy_664 u)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0726 (A : Class) :
    (nb090_alpha_dummy_655 A) ∈ (((Class.cv (nb090_alpha_dummy_655 A))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0727 (u : Var) :
    (nb090_alpha_dummy_656 u) ∈ (((Class.cv (nb090_alpha_dummy_656 u))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0728 (A : Class) :
    (nb090_alpha_dummy_041 A) ∈
      (((syn_cfv (Class.cv (nb090_alpha_dummy_000 A))
            (Class.cv (nb090_alpha_dummy_041 A)))).fv ∪
        ((syn_cfv (Class.cv (nb090_alpha_dummy_000 A))
            (Class.cv (nb090_alpha_dummy_042 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cfv]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0729 (A : Class) :
    (nb090_alpha_dummy_041 A) ∈
      (((syn_ccompl (Class.cab (nb090_alpha_dummy_699 A) (syn_wrex (nb090_alpha_dummy_700 A)
                (syn_cfv (Class.cv (nb090_alpha_dummy_000 A))
                  (Class.cv (nb090_alpha_dummy_041 A)))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_699 A))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_700 A)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb090_alpha_dummy_699 A) (syn_wrex (nb090_alpha_dummy_700 A)
                (syn_cfv (Class.cv (nb090_alpha_dummy_000 A))
                  (Class.cv (nb090_alpha_dummy_042 A)))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_699 A))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_700 A)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090_alpha_dummy_041 A) ≠ (nb090_alpha_dummy_699 A) from (by
          unfold nb090_alpha_dummy_699;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0728 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090_alpha_dummy_041 A) ≠ (nb090_alpha_dummy_700 A) from (by
            unfold nb090_alpha_dummy_700;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0728 A) 1))))
    · rw [fv_syn_cfv]
      with_reducible rw [Finset.mem_union]
      left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0730 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_043 v u h) ∈
      (((syn_cfv (Class.cv h) (Class.cv (nb090_alpha_dummy_043 v u h)))).fv ∪
        ((syn_cfv (Class.cv h) (Class.cv (nb090_alpha_dummy_044 v u h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cfv]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0731 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_043 v u h) ∈
      (((syn_ccompl (Class.cab (nb090_alpha_dummy_701 v u h)
              (syn_wrex (nb090_alpha_dummy_702 v u h)
                (syn_cfv (Class.cv h) (Class.cv (nb090_alpha_dummy_043 v u h)))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_701 v u h))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_702 v u h)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb090_alpha_dummy_701 v u h) (syn_wrex (nb090_alpha_dummy_702 v u h)
                (syn_cfv (Class.cv h) (Class.cv (nb090_alpha_dummy_044 v u h)))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_701 v u h))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_702 v u h)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090_alpha_dummy_043 v u h) ≠ (nb090_alpha_dummy_701 v u h) from (by
          unfold nb090_alpha_dummy_701;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0730 v u h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090_alpha_dummy_043 v u h) ≠ (nb090_alpha_dummy_702 v u h) from (by
            unfold nb090_alpha_dummy_702;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0730 v u h) 1))))
    · rw [fv_syn_cfv]
      with_reducible rw [Finset.mem_union]
      left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0732 (A : Class) :
    (nb090_alpha_dummy_041 A) ∈
      (((Class.cab (nb090_alpha_dummy_699 A) (syn_wrex (nb090_alpha_dummy_700 A)
              (syn_cfv (Class.cv (nb090_alpha_dummy_000 A))
                (Class.cv (nb090_alpha_dummy_041 A)))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_699 A))
                (syn_cphi (Class.cv (nb090_alpha_dummy_700 A))))))).fv ∪
        ((Class.cab (nb090_alpha_dummy_699 A) (syn_wrex (nb090_alpha_dummy_700 A)
              (syn_cfv (Class.cv (nb090_alpha_dummy_000 A))
                (Class.cv (nb090_alpha_dummy_041 A)))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_699 A))
                (syn_cphi (Class.cv (nb090_alpha_dummy_700 A))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090_alpha_dummy_041 A) ≠ (nb090_alpha_dummy_699 A) from (by
          unfold nb090_alpha_dummy_699;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0728 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090_alpha_dummy_041 A) ≠ (nb090_alpha_dummy_700 A) from (by
            unfold nb090_alpha_dummy_700;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0728 A) 1))))
    · rw [fv_syn_cfv]
      with_reducible rw [Finset.mem_union]
      left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0733 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_043 v u h) ∈
      (((Class.cab (nb090_alpha_dummy_701 v u h) (syn_wrex (nb090_alpha_dummy_702 v u h)
              (syn_cfv (Class.cv h) (Class.cv (nb090_alpha_dummy_043 v u h)))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_701 v u h))
                (syn_cphi (Class.cv (nb090_alpha_dummy_702 v u h))))))).fv ∪
        ((Class.cab (nb090_alpha_dummy_701 v u h) (syn_wrex (nb090_alpha_dummy_702 v u h)
              (syn_cfv (Class.cv h) (Class.cv (nb090_alpha_dummy_043 v u h)))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_701 v u h))
                (syn_cphi (Class.cv (nb090_alpha_dummy_702 v u h))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090_alpha_dummy_043 v u h) ≠ (nb090_alpha_dummy_701 v u h) from (by
          unfold nb090_alpha_dummy_701;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0730 v u h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090_alpha_dummy_043 v u h) ≠ (nb090_alpha_dummy_702 v u h) from (by
            unfold nb090_alpha_dummy_702;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0730 v u h) 1))))
    · rw [fv_syn_cfv]
      with_reducible rw [Finset.mem_union]
      left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0734 (A : Class) :
    (nb090_alpha_dummy_041 A) ∈
      (((Class.cv (nb090_alpha_dummy_000 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_041 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0735 (A : Class) :
    (nb090_alpha_dummy_041 A) ∈
      (({(nb090_alpha_dummy_707 A)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb090_alpha_dummy_041 A)) (Class.cv (nb090_alpha_dummy_000 A))
            (Class.cv (nb090_alpha_dummy_707 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_wbr]
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0736 (A : Class) :
    (nb090_alpha_dummy_041 A) ∈
      (((Class.cab (nb090_alpha_dummy_709 A) (Wff.classEq (Class.cab (nb090_alpha_dummy_707 A)
              (syn_wbr (Class.cv (nb090_alpha_dummy_041 A)) (Class.cv (nb090_alpha_dummy_000 A))
                (Class.cv (nb090_alpha_dummy_707 A))))
            (syn_csn (Class.cv (nb090_alpha_dummy_709 A)))))).fv) :=
  by
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090_alpha_dummy_041 A) ≠ (nb090_alpha_dummy_709 A) from (by
          unfold nb090_alpha_dummy_709;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0735 A) 0))))
  · rw [fv_wff_classEq]
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cab]
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090_alpha_dummy_041 A) ≠ (nb090_alpha_dummy_707 A) from (by
            unfold nb090_alpha_dummy_707;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0734 A) 0))))
    · rw [fv_syn_wbr]
      with_reducible rw [Finset.mem_union]
      left
      with_reducible rw [Finset.mem_union]
      left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0737 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_043 v u h) ∈
      (((Class.cv h)).fv ∪ ((Class.cv (nb090_alpha_dummy_043 v u h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0738 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_043 v u h) ∈
      (({(nb090_alpha_dummy_708 v u h)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb090_alpha_dummy_043 v u h)) (Class.cv h)
            (Class.cv (nb090_alpha_dummy_708 v u h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_wbr]
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0739 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_043 v u h) ∈
      (((Class.cab (nb090_alpha_dummy_710 v u h) (Wff.classEq
            (Class.cab (nb090_alpha_dummy_708 v u h)
              (syn_wbr (Class.cv (nb090_alpha_dummy_043 v u h)) (Class.cv h)
                (Class.cv (nb090_alpha_dummy_708 v u h))))
            (syn_csn (Class.cv (nb090_alpha_dummy_710 v u h)))))).fv) :=
  by
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090_alpha_dummy_043 v u h) ≠ (nb090_alpha_dummy_710 v u h) from (by
          unfold nb090_alpha_dummy_710;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0738 v u h) 0))))
  · rw [fv_wff_classEq]
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cab]
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090_alpha_dummy_043 v u h) ≠ (nb090_alpha_dummy_708 v u h) from (by
            unfold nb090_alpha_dummy_708;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0737 v u h) 0))))
    · rw [fv_syn_wbr]
      with_reducible rw [Finset.mem_union]
      left
      with_reducible rw [Finset.mem_union]
      left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0740 (A : Class) :
    (nb090_alpha_dummy_041 A) ∈
      (((Class.cv (nb090_alpha_dummy_041 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_707 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0741 (A : Class) :
    (nb090_alpha_dummy_041 A) ∈
      (((syn_ccompl (Class.cab (nb090_alpha_dummy_715 A)
              (syn_wrex (nb090_alpha_dummy_716 A) (Class.cv (nb090_alpha_dummy_041 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_715 A))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_716 A)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb090_alpha_dummy_715 A)
              (syn_wrex (nb090_alpha_dummy_716 A) (Class.cv (nb090_alpha_dummy_707 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_715 A))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_716 A)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090_alpha_dummy_041 A) ≠ (nb090_alpha_dummy_715 A) from (by
          unfold nb090_alpha_dummy_715;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0740 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090_alpha_dummy_041 A) ≠ (nb090_alpha_dummy_716 A) from (by
            unfold nb090_alpha_dummy_716;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0740 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0742 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_043 v u h) ∈
      (((Class.cv (nb090_alpha_dummy_043 v u h))).fv ∪
        ((Class.cv (nb090_alpha_dummy_708 v u h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0743 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_043 v u h) ∈
      (((syn_ccompl (Class.cab (nb090_alpha_dummy_717 v u h)
              (syn_wrex (nb090_alpha_dummy_718 v u h) (Class.cv (nb090_alpha_dummy_043 v u h))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_717 v u h))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_718 v u h)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb090_alpha_dummy_717 v u h) (syn_wrex (nb090_alpha_dummy_718 v u h)
                (Class.cv (nb090_alpha_dummy_708 v u h))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_717 v u h))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_718 v u h)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090_alpha_dummy_043 v u h) ≠ (nb090_alpha_dummy_717 v u h) from (by
          unfold nb090_alpha_dummy_717;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0742 v u h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090_alpha_dummy_043 v u h) ≠ (nb090_alpha_dummy_718 v u h) from (by
            unfold nb090_alpha_dummy_718;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0742 v u h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0744 (A : Class) :
    (nb090_alpha_dummy_041 A) ∈
      (((Class.cab (nb090_alpha_dummy_715 A)
            (syn_wrex (nb090_alpha_dummy_716 A) (Class.cv (nb090_alpha_dummy_041 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_715 A))
                (syn_cphi (Class.cv (nb090_alpha_dummy_716 A))))))).fv ∪
        ((Class.cab (nb090_alpha_dummy_715 A)
            (syn_wrex (nb090_alpha_dummy_716 A) (Class.cv (nb090_alpha_dummy_041 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_715 A))
                (syn_cphi (Class.cv (nb090_alpha_dummy_716 A))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090_alpha_dummy_041 A) ≠ (nb090_alpha_dummy_715 A) from (by
          unfold nb090_alpha_dummy_715;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0740 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090_alpha_dummy_041 A) ≠ (nb090_alpha_dummy_716 A) from (by
            unfold nb090_alpha_dummy_716;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0740 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0745 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_043 v u h) ∈
      (((Class.cab (nb090_alpha_dummy_717 v u h) (syn_wrex (nb090_alpha_dummy_718 v u h)
              (Class.cv (nb090_alpha_dummy_043 v u h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_717 v u h))
                (syn_cphi (Class.cv (nb090_alpha_dummy_718 v u h))))))).fv ∪
        ((Class.cab (nb090_alpha_dummy_717 v u h) (syn_wrex (nb090_alpha_dummy_718 v u h)
              (Class.cv (nb090_alpha_dummy_043 v u h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_717 v u h))
                (syn_cphi (Class.cv (nb090_alpha_dummy_718 v u h))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090_alpha_dummy_043 v u h) ≠ (nb090_alpha_dummy_717 v u h) from (by
          unfold nb090_alpha_dummy_717;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0742 v u h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090_alpha_dummy_043 v u h) ≠ (nb090_alpha_dummy_718 v u h) from (by
            unfold nb090_alpha_dummy_718;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0742 v u h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0746 (A : Class) :
    (nb090_alpha_dummy_716 A) ∈ (((Class.cv (nb090_alpha_dummy_716 A))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0747 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_718 v u h) ∈ (((Class.cv (nb090_alpha_dummy_718 v u h))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0748 (A : Class) :
    (nb090_alpha_dummy_723 A) ∈
      (((Wff.classMem (Class.cv (nb090_alpha_dummy_723 A)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb090_alpha_dummy_723 A)) (syn_c1c))).fv ∪
        ((Class.cv (nb090_alpha_dummy_723 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_wff_classMem]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0749 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_725 v u h) ∈
      (((Wff.classMem (Class.cv (nb090_alpha_dummy_725 v u h)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb090_alpha_dummy_725 v u h)) (syn_c1c))).fv ∪
        ((Class.cv (nb090_alpha_dummy_725 v u h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_wff_classMem]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0750 (A : Class) :
    (nb090_alpha_dummy_723 A) ∈
      (((Class.cv (nb090_alpha_dummy_723 A))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0751 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_725 v u h) ∈
      (((Class.cv (nb090_alpha_dummy_725 v u h))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0752 (A : Class) :
    (nb090_alpha_dummy_730 A) ∈
      (((syn_cnin (Class.cv (nb090_alpha_dummy_730 A))
            (Class.cv (nb090_alpha_dummy_731 A)))).fv ∪
        ((syn_cnin (Class.cv (nb090_alpha_dummy_730 A))
            (Class.cv (nb090_alpha_dummy_731 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0753 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_733 v u h) ∈
      (((syn_cnin (Class.cv (nb090_alpha_dummy_733 v u h))
            (Class.cv (nb090_alpha_dummy_734 v u h)))).fv ∪
        ((syn_cnin (Class.cv (nb090_alpha_dummy_733 v u h))
            (Class.cv (nb090_alpha_dummy_734 v u h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0754 (A : Class) :
    (nb090_alpha_dummy_730 A) ∈
      (((Class.cv (nb090_alpha_dummy_730 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_731 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0755 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_733 v u h) ∈
      (((Class.cv (nb090_alpha_dummy_733 v u h))).fv ∪
        ((Class.cv (nb090_alpha_dummy_734 v u h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0756 (A : Class) :
    (nb090_alpha_dummy_731 A) ∈
      (((syn_cnin (Class.cv (nb090_alpha_dummy_730 A))
            (Class.cv (nb090_alpha_dummy_731 A)))).fv ∪
        ((syn_cnin (Class.cv (nb090_alpha_dummy_730 A))
            (Class.cv (nb090_alpha_dummy_731 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0757 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_734 v u h) ∈
      (((syn_cnin (Class.cv (nb090_alpha_dummy_733 v u h))
            (Class.cv (nb090_alpha_dummy_734 v u h)))).fv ∪
        ((syn_cnin (Class.cv (nb090_alpha_dummy_733 v u h))
            (Class.cv (nb090_alpha_dummy_734 v u h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0758 (A : Class) :
    (nb090_alpha_dummy_731 A) ∈
      (((Class.cv (nb090_alpha_dummy_730 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_731 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0759 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_734 v u h) ∈
      (((Class.cv (nb090_alpha_dummy_733 v u h))).fv ∪
        ((Class.cv (nb090_alpha_dummy_734 v u h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C090C001Part021`. -/


section

namespace NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

open scoped Fol
open NFChoice.Foundation
open NFChoice.Foundation.ExactLiteralTrial
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax
open NFChoice.Compiler.CompactSyntaxFVExplicit
open NFChoice.Compiler.WPPCompactSyntaxFVExplicit
open NFChoice.Compiler.CoreFVSimp
open NFChoice.DefinitionLeaves.AlphaFocusedSupport
open NFChoice.DefinitionLeaves.AlphaFocusedFV
open NFChoice.DirectNominalPrf
open NFChoice.DirectNominalPrf.Nominal

theorem nb090_support_mem_0760 (A : Class) :
    (nb090_alpha_dummy_730 A) ∈
      (((syn_ccompl (Class.cv (nb090_alpha_dummy_730 A)))).fv ∪
        ((syn_ccompl (Class.cv (nb090_alpha_dummy_731 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0761 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_733 v u h) ∈
      (((syn_ccompl (Class.cv (nb090_alpha_dummy_733 v u h)))).fv ∪
        ((syn_ccompl (Class.cv (nb090_alpha_dummy_734 v u h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0762 (A : Class) :
    (nb090_alpha_dummy_730 A) ∈
      (((Class.cv (nb090_alpha_dummy_730 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_730 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0763 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_733 v u h) ∈
      (((Class.cv (nb090_alpha_dummy_733 v u h))).fv ∪
        ((Class.cv (nb090_alpha_dummy_733 v u h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0764 (A : Class) :
    (nb090_alpha_dummy_731 A) ∈
      (((syn_ccompl (Class.cv (nb090_alpha_dummy_730 A)))).fv ∪
        ((syn_ccompl (Class.cv (nb090_alpha_dummy_731 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0765 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_734 v u h) ∈
      (((syn_ccompl (Class.cv (nb090_alpha_dummy_733 v u h)))).fv ∪
        ((syn_ccompl (Class.cv (nb090_alpha_dummy_734 v u h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0766 (A : Class) :
    (nb090_alpha_dummy_731 A) ∈
      (((Class.cv (nb090_alpha_dummy_731 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_731 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0767 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_734 v u h) ∈
      (((Class.cv (nb090_alpha_dummy_734 v u h))).fv ∪
        ((Class.cv (nb090_alpha_dummy_734 v u h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0768 (A : Class) :
    (nb090_alpha_dummy_707 A) ∈
      (((Class.cv (nb090_alpha_dummy_041 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_707 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0769 (A : Class) :
    (nb090_alpha_dummy_707 A) ∈
      (((syn_ccompl (Class.cab (nb090_alpha_dummy_715 A)
              (syn_wrex (nb090_alpha_dummy_716 A) (Class.cv (nb090_alpha_dummy_041 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_715 A))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_716 A)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb090_alpha_dummy_715 A)
              (syn_wrex (nb090_alpha_dummy_716 A) (Class.cv (nb090_alpha_dummy_707 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_715 A))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_716 A)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090_alpha_dummy_707 A) ≠ (nb090_alpha_dummy_715 A) from (by
          unfold nb090_alpha_dummy_715;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0768 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090_alpha_dummy_707 A) ≠ (nb090_alpha_dummy_716 A) from (by
            unfold nb090_alpha_dummy_716;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0768 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0770 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_708 v u h) ∈
      (((Class.cv (nb090_alpha_dummy_043 v u h))).fv ∪
        ((Class.cv (nb090_alpha_dummy_708 v u h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0771 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_708 v u h) ∈
      (((syn_ccompl (Class.cab (nb090_alpha_dummy_717 v u h)
              (syn_wrex (nb090_alpha_dummy_718 v u h) (Class.cv (nb090_alpha_dummy_043 v u h))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_717 v u h))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_718 v u h)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb090_alpha_dummy_717 v u h) (syn_wrex (nb090_alpha_dummy_718 v u h)
                (Class.cv (nb090_alpha_dummy_708 v u h))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_717 v u h))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_718 v u h)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090_alpha_dummy_708 v u h) ≠ (nb090_alpha_dummy_717 v u h) from (by
          unfold nb090_alpha_dummy_717;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0770 v u h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090_alpha_dummy_708 v u h) ≠ (nb090_alpha_dummy_718 v u h) from (by
            unfold nb090_alpha_dummy_718;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0770 v u h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0772 (A : Class) :
    (nb090_alpha_dummy_707 A) ∈
      (((Class.cab (nb090_alpha_dummy_715 A)
            (syn_wrex (nb090_alpha_dummy_716 A) (Class.cv (nb090_alpha_dummy_707 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_715 A))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_716 A)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_715 A)
            (syn_wrex (nb090_alpha_dummy_716 A) (Class.cv (nb090_alpha_dummy_707 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_715 A))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_716 A)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090_alpha_dummy_707 A) ≠ (nb090_alpha_dummy_715 A) from (by
          unfold nb090_alpha_dummy_715;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0768 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090_alpha_dummy_707 A) ≠ (nb090_alpha_dummy_716 A) from (by
            unfold nb090_alpha_dummy_716;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0768 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0773 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_708 v u h) ∈
      (((Class.cab (nb090_alpha_dummy_717 v u h) (syn_wrex (nb090_alpha_dummy_718 v u h)
              (Class.cv (nb090_alpha_dummy_708 v u h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_717 v u h))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_718 v u h)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_717 v u h)
            (syn_wrex (nb090_alpha_dummy_718 v u h) (Class.cv (nb090_alpha_dummy_708 v u h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_717 v u h))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_718 v u h)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090_alpha_dummy_708 v u h) ≠ (nb090_alpha_dummy_717 v u h) from (by
          unfold nb090_alpha_dummy_717;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0770 v u h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090_alpha_dummy_708 v u h) ≠ (nb090_alpha_dummy_718 v u h) from (by
            unfold nb090_alpha_dummy_718;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0770 v u h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0774 (A : Class) :
    (nb090_alpha_dummy_716 A) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_716 A))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0775 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_718 v u h) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_718 v u h))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0776 (A : Class) :
    (nb090_alpha_dummy_716 A) ∈
      (((syn_cphi (Class.cv (nb090_alpha_dummy_716 A)))).fv ∪
        ((syn_cphi (Class.cv (nb090_alpha_dummy_716 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0777 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_718 v u h) ∈
      (((syn_cphi (Class.cv (nb090_alpha_dummy_718 v u h)))).fv ∪
        ((syn_cphi (Class.cv (nb090_alpha_dummy_718 v u h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0778 (A : Class) :
    (nb090_alpha_dummy_000 A) ∈
      (((Class.cv (nb090_alpha_dummy_000 A))).fv ∪
              ((syn_cfv (syn_c1st) (Class.cv (nb090_alpha_dummy_001 A)))).fv ∪
            ((syn_cfv (syn_c1st) (Class.cv (nb090_alpha_dummy_002 A)))).fv ∪
          ((syn_cfv (syn_c2nd) (Class.cv (nb090_alpha_dummy_001 A)))).fv ∪
        ((syn_cfv (syn_c2nd) (Class.cv (nb090_alpha_dummy_002 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0779 (v : Var) (u : Var) (h : Var) :
    h ∈
      (((Class.cv h)).fv ∪ ((syn_cfv (syn_c1st) (Class.cv u))).fv ∪
            ((syn_cfv (syn_c1st) (Class.cv v))).fv ∪ ((syn_cfv (syn_c2nd) (Class.cv u))).fv ∪
        ((syn_cfv (syn_c2nd) (Class.cv v))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0780 (A : Class) :
    (nb090_alpha_dummy_000 A) ∈
      (((syn_cfv (Class.cv (nb090_alpha_dummy_000 A))
            (Class.cv (nb090_alpha_dummy_041 A)))).fv ∪
        ((syn_cfv (Class.cv (nb090_alpha_dummy_000 A))
            (Class.cv (nb090_alpha_dummy_042 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cfv]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0781 (A : Class) :
    (nb090_alpha_dummy_000 A) ∈
      (((syn_ccompl (Class.cab (nb090_alpha_dummy_699 A) (syn_wrex (nb090_alpha_dummy_700 A)
                (syn_cfv (Class.cv (nb090_alpha_dummy_000 A))
                  (Class.cv (nb090_alpha_dummy_041 A)))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_699 A))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_700 A)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb090_alpha_dummy_699 A) (syn_wrex (nb090_alpha_dummy_700 A)
                (syn_cfv (Class.cv (nb090_alpha_dummy_000 A))
                  (Class.cv (nb090_alpha_dummy_042 A)))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_699 A))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_700 A)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090_alpha_dummy_000 A) ≠ (nb090_alpha_dummy_699 A) from (by
          unfold nb090_alpha_dummy_699;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0780 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090_alpha_dummy_000 A) ≠ (nb090_alpha_dummy_700 A) from (by
            unfold nb090_alpha_dummy_700;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0780 A) 1))))
    · rw [fv_syn_cfv]
      with_reducible rw [Finset.mem_union]
      right
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0782 (v : Var) (u : Var) (h : Var) :
    h ∈
      (((syn_cfv (Class.cv h) (Class.cv (nb090_alpha_dummy_043 v u h)))).fv ∪
        ((syn_cfv (Class.cv h) (Class.cv (nb090_alpha_dummy_044 v u h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cfv]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0783 (v : Var) (u : Var) (h : Var) :
    h ∈
      (((syn_ccompl (Class.cab (nb090_alpha_dummy_701 v u h)
              (syn_wrex (nb090_alpha_dummy_702 v u h)
                (syn_cfv (Class.cv h) (Class.cv (nb090_alpha_dummy_043 v u h)))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_701 v u h))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_702 v u h)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb090_alpha_dummy_701 v u h) (syn_wrex (nb090_alpha_dummy_702 v u h)
                (syn_cfv (Class.cv h) (Class.cv (nb090_alpha_dummy_044 v u h)))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_701 v u h))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_702 v u h)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show h ≠ (nb090_alpha_dummy_701 v u h) from (by
          unfold nb090_alpha_dummy_701;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0782 v u h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show h ≠ (nb090_alpha_dummy_702 v u h) from (by
            unfold nb090_alpha_dummy_702;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0782 v u h) 1))))
    · rw [fv_syn_cfv]
      with_reducible rw [Finset.mem_union]
      right
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0784 (A : Class) :
    (nb090_alpha_dummy_000 A) ∈
      (((Class.cab (nb090_alpha_dummy_699 A) (syn_wrex (nb090_alpha_dummy_700 A)
              (syn_cfv (Class.cv (nb090_alpha_dummy_000 A))
                (Class.cv (nb090_alpha_dummy_041 A)))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_699 A))
                (syn_cphi (Class.cv (nb090_alpha_dummy_700 A))))))).fv ∪
        ((Class.cab (nb090_alpha_dummy_699 A) (syn_wrex (nb090_alpha_dummy_700 A)
              (syn_cfv (Class.cv (nb090_alpha_dummy_000 A))
                (Class.cv (nb090_alpha_dummy_041 A)))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_699 A))
                (syn_cphi (Class.cv (nb090_alpha_dummy_700 A))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090_alpha_dummy_000 A) ≠ (nb090_alpha_dummy_699 A) from (by
          unfold nb090_alpha_dummy_699;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0780 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090_alpha_dummy_000 A) ≠ (nb090_alpha_dummy_700 A) from (by
            unfold nb090_alpha_dummy_700;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0780 A) 1))))
    · rw [fv_syn_cfv]
      with_reducible rw [Finset.mem_union]
      right
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0785 (v : Var) (u : Var) (h : Var) :
    h ∈
      (((Class.cab (nb090_alpha_dummy_701 v u h) (syn_wrex (nb090_alpha_dummy_702 v u h)
              (syn_cfv (Class.cv h) (Class.cv (nb090_alpha_dummy_043 v u h)))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_701 v u h))
                (syn_cphi (Class.cv (nb090_alpha_dummy_702 v u h))))))).fv ∪
        ((Class.cab (nb090_alpha_dummy_701 v u h) (syn_wrex (nb090_alpha_dummy_702 v u h)
              (syn_cfv (Class.cv h) (Class.cv (nb090_alpha_dummy_043 v u h)))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_701 v u h))
                (syn_cphi (Class.cv (nb090_alpha_dummy_702 v u h))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show h ≠ (nb090_alpha_dummy_701 v u h) from (by
          unfold nb090_alpha_dummy_701;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0782 v u h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show h ≠ (nb090_alpha_dummy_702 v u h) from (by
            unfold nb090_alpha_dummy_702;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0782 v u h) 1))))
    · rw [fv_syn_cfv]
      with_reducible rw [Finset.mem_union]
      right
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0786 (A : Class) :
    (nb090_alpha_dummy_000 A) ∈
      (((Class.cv (nb090_alpha_dummy_000 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_041 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0787 (A : Class) :
    (nb090_alpha_dummy_000 A) ∈
      (({(nb090_alpha_dummy_707 A)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb090_alpha_dummy_041 A)) (Class.cv (nb090_alpha_dummy_000 A))
            (Class.cv (nb090_alpha_dummy_707 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_wbr]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0788 (A : Class) :
    (nb090_alpha_dummy_000 A) ∈
      (((Class.cab (nb090_alpha_dummy_709 A) (Wff.classEq (Class.cab (nb090_alpha_dummy_707 A)
              (syn_wbr (Class.cv (nb090_alpha_dummy_041 A)) (Class.cv (nb090_alpha_dummy_000 A))
                (Class.cv (nb090_alpha_dummy_707 A))))
            (syn_csn (Class.cv (nb090_alpha_dummy_709 A)))))).fv) :=
  by
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090_alpha_dummy_000 A) ≠ (nb090_alpha_dummy_709 A) from (by
          unfold nb090_alpha_dummy_709;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0787 A) 0))))
  · rw [fv_wff_classEq]
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cab]
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090_alpha_dummy_000 A) ≠ (nb090_alpha_dummy_707 A) from (by
            unfold nb090_alpha_dummy_707;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0786 A) 0))))
    · rw [fv_syn_wbr]
      with_reducible rw [Finset.mem_union]
      right
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0789 (v : Var) (u : Var) (h : Var) :
    h ∈ (((Class.cv h)).fv ∪ ((Class.cv (nb090_alpha_dummy_043 v u h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0790 (v : Var) (u : Var) (h : Var) :
    h ∈
      (({(nb090_alpha_dummy_708 v u h)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb090_alpha_dummy_043 v u h)) (Class.cv h)
            (Class.cv (nb090_alpha_dummy_708 v u h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_wbr]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0791 (v : Var) (u : Var) (h : Var) :
    h ∈
      (((Class.cab (nb090_alpha_dummy_710 v u h) (Wff.classEq
            (Class.cab (nb090_alpha_dummy_708 v u h)
              (syn_wbr (Class.cv (nb090_alpha_dummy_043 v u h)) (Class.cv h)
                (Class.cv (nb090_alpha_dummy_708 v u h))))
            (syn_csn (Class.cv (nb090_alpha_dummy_710 v u h)))))).fv) :=
  by
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show h ≠ (nb090_alpha_dummy_710 v u h) from (by
          unfold nb090_alpha_dummy_710;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0790 v u h) 0))))
  · rw [fv_wff_classEq]
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cab]
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show h ≠ (nb090_alpha_dummy_708 v u h) from (by
            unfold nb090_alpha_dummy_708;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0789 v u h) 0))))
    · rw [fv_syn_wbr]
      with_reducible rw [Finset.mem_union]
      right
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0792 (A : Class) :
    (nb090_alpha_dummy_709 A) ∈ (((Class.cv (nb090_alpha_dummy_709 A))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0793 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_710 v u h) ∈ (((Class.cv (nb090_alpha_dummy_710 v u h))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0794 (A : Class) :
    (nb090_alpha_dummy_700 A) ∈ (((Class.cv (nb090_alpha_dummy_700 A))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0795 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_702 v u h) ∈ (((Class.cv (nb090_alpha_dummy_702 v u h))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0796 (A : Class) :
    (nb090_alpha_dummy_753 A) ∈
      (((Wff.classMem (Class.cv (nb090_alpha_dummy_753 A)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb090_alpha_dummy_753 A)) (syn_c1c))).fv ∪
        ((Class.cv (nb090_alpha_dummy_753 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_wff_classMem]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0797 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_755 v u h) ∈
      (((Wff.classMem (Class.cv (nb090_alpha_dummy_755 v u h)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb090_alpha_dummy_755 v u h)) (syn_c1c))).fv ∪
        ((Class.cv (nb090_alpha_dummy_755 v u h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_wff_classMem]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0798 (A : Class) :
    (nb090_alpha_dummy_753 A) ∈
      (((Class.cv (nb090_alpha_dummy_753 A))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0799 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_755 v u h) ∈
      (((Class.cv (nb090_alpha_dummy_755 v u h))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0800 (A : Class) :
    (nb090_alpha_dummy_760 A) ∈
      (((syn_cnin (Class.cv (nb090_alpha_dummy_760 A))
            (Class.cv (nb090_alpha_dummy_761 A)))).fv ∪
        ((syn_cnin (Class.cv (nb090_alpha_dummy_760 A))
            (Class.cv (nb090_alpha_dummy_761 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0801 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_763 v u h) ∈
      (((syn_cnin (Class.cv (nb090_alpha_dummy_763 v u h))
            (Class.cv (nb090_alpha_dummy_764 v u h)))).fv ∪
        ((syn_cnin (Class.cv (nb090_alpha_dummy_763 v u h))
            (Class.cv (nb090_alpha_dummy_764 v u h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0802 (A : Class) :
    (nb090_alpha_dummy_760 A) ∈
      (((Class.cv (nb090_alpha_dummy_760 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_761 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0803 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_763 v u h) ∈
      (((Class.cv (nb090_alpha_dummy_763 v u h))).fv ∪
        ((Class.cv (nb090_alpha_dummy_764 v u h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0804 (A : Class) :
    (nb090_alpha_dummy_761 A) ∈
      (((syn_cnin (Class.cv (nb090_alpha_dummy_760 A))
            (Class.cv (nb090_alpha_dummy_761 A)))).fv ∪
        ((syn_cnin (Class.cv (nb090_alpha_dummy_760 A))
            (Class.cv (nb090_alpha_dummy_761 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0805 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_764 v u h) ∈
      (((syn_cnin (Class.cv (nb090_alpha_dummy_763 v u h))
            (Class.cv (nb090_alpha_dummy_764 v u h)))).fv ∪
        ((syn_cnin (Class.cv (nb090_alpha_dummy_763 v u h))
            (Class.cv (nb090_alpha_dummy_764 v u h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0806 (A : Class) :
    (nb090_alpha_dummy_761 A) ∈
      (((Class.cv (nb090_alpha_dummy_760 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_761 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0807 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_764 v u h) ∈
      (((Class.cv (nb090_alpha_dummy_763 v u h))).fv ∪
        ((Class.cv (nb090_alpha_dummy_764 v u h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0808 (A : Class) :
    (nb090_alpha_dummy_760 A) ∈
      (((syn_ccompl (Class.cv (nb090_alpha_dummy_760 A)))).fv ∪
        ((syn_ccompl (Class.cv (nb090_alpha_dummy_761 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0809 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_763 v u h) ∈
      (((syn_ccompl (Class.cv (nb090_alpha_dummy_763 v u h)))).fv ∪
        ((syn_ccompl (Class.cv (nb090_alpha_dummy_764 v u h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0810 (A : Class) :
    (nb090_alpha_dummy_760 A) ∈
      (((Class.cv (nb090_alpha_dummy_760 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_760 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0811 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_763 v u h) ∈
      (((Class.cv (nb090_alpha_dummy_763 v u h))).fv ∪
        ((Class.cv (nb090_alpha_dummy_763 v u h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0812 (A : Class) :
    (nb090_alpha_dummy_761 A) ∈
      (((syn_ccompl (Class.cv (nb090_alpha_dummy_760 A)))).fv ∪
        ((syn_ccompl (Class.cv (nb090_alpha_dummy_761 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0813 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_764 v u h) ∈
      (((syn_ccompl (Class.cv (nb090_alpha_dummy_763 v u h)))).fv ∪
        ((syn_ccompl (Class.cv (nb090_alpha_dummy_764 v u h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0814 (A : Class) :
    (nb090_alpha_dummy_761 A) ∈
      (((Class.cv (nb090_alpha_dummy_761 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_761 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0815 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_764 v u h) ∈
      (((Class.cv (nb090_alpha_dummy_764 v u h))).fv ∪
        ((Class.cv (nb090_alpha_dummy_764 v u h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0816 (A : Class) :
    (nb090_alpha_dummy_042 A) ∈
      (((syn_cfv (Class.cv (nb090_alpha_dummy_000 A))
            (Class.cv (nb090_alpha_dummy_041 A)))).fv ∪
        ((syn_cfv (Class.cv (nb090_alpha_dummy_000 A))
            (Class.cv (nb090_alpha_dummy_042 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_cfv]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0817 (A : Class) :
    (nb090_alpha_dummy_042 A) ∈
      (((syn_ccompl (Class.cab (nb090_alpha_dummy_699 A) (syn_wrex (nb090_alpha_dummy_700 A)
                (syn_cfv (Class.cv (nb090_alpha_dummy_000 A))
                  (Class.cv (nb090_alpha_dummy_041 A)))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_699 A))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_700 A)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb090_alpha_dummy_699 A) (syn_wrex (nb090_alpha_dummy_700 A)
                (syn_cfv (Class.cv (nb090_alpha_dummy_000 A))
                  (Class.cv (nb090_alpha_dummy_042 A)))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_699 A))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_700 A)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090_alpha_dummy_042 A) ≠ (nb090_alpha_dummy_699 A) from (by
          unfold nb090_alpha_dummy_699;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0816 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090_alpha_dummy_042 A) ≠ (nb090_alpha_dummy_700 A) from (by
            unfold nb090_alpha_dummy_700;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0816 A) 1))))
    · rw [fv_syn_cfv]
      with_reducible rw [Finset.mem_union]
      left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0818 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_044 v u h) ∈
      (((syn_cfv (Class.cv h) (Class.cv (nb090_alpha_dummy_043 v u h)))).fv ∪
        ((syn_cfv (Class.cv h) (Class.cv (nb090_alpha_dummy_044 v u h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_cfv]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0819 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_044 v u h) ∈
      (((syn_ccompl (Class.cab (nb090_alpha_dummy_701 v u h)
              (syn_wrex (nb090_alpha_dummy_702 v u h)
                (syn_cfv (Class.cv h) (Class.cv (nb090_alpha_dummy_043 v u h)))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_701 v u h))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_702 v u h)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb090_alpha_dummy_701 v u h) (syn_wrex (nb090_alpha_dummy_702 v u h)
                (syn_cfv (Class.cv h) (Class.cv (nb090_alpha_dummy_044 v u h)))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_701 v u h))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_702 v u h)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090_alpha_dummy_044 v u h) ≠ (nb090_alpha_dummy_701 v u h) from (by
          unfold nb090_alpha_dummy_701;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0818 v u h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090_alpha_dummy_044 v u h) ≠ (nb090_alpha_dummy_702 v u h) from (by
            unfold nb090_alpha_dummy_702;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0818 v u h) 1))))
    · rw [fv_syn_cfv]
      with_reducible rw [Finset.mem_union]
      left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0820 (A : Class) :
    (nb090_alpha_dummy_042 A) ∈
      (((Class.cab (nb090_alpha_dummy_699 A) (syn_wrex (nb090_alpha_dummy_700 A)
              (syn_cfv (Class.cv (nb090_alpha_dummy_000 A))
                (Class.cv (nb090_alpha_dummy_042 A)))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_699 A))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_700 A)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_699 A)
            (syn_wrex (nb090_alpha_dummy_700 A) (syn_cfv (Class.cv (nb090_alpha_dummy_000 A))
                (Class.cv (nb090_alpha_dummy_042 A)))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_699 A))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_700 A)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090_alpha_dummy_042 A) ≠ (nb090_alpha_dummy_699 A) from (by
          unfold nb090_alpha_dummy_699;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0816 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090_alpha_dummy_042 A) ≠ (nb090_alpha_dummy_700 A) from (by
            unfold nb090_alpha_dummy_700;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0816 A) 1))))
    · rw [fv_syn_cfv]
      with_reducible rw [Finset.mem_union]
      left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0821 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_044 v u h) ∈
      (((Class.cab (nb090_alpha_dummy_701 v u h) (syn_wrex (nb090_alpha_dummy_702 v u h)
              (syn_cfv (Class.cv h) (Class.cv (nb090_alpha_dummy_044 v u h)))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_701 v u h))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_702 v u h)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_701 v u h)
            (syn_wrex (nb090_alpha_dummy_702 v u h)
              (syn_cfv (Class.cv h) (Class.cv (nb090_alpha_dummy_044 v u h)))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_701 v u h))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_702 v u h)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090_alpha_dummy_044 v u h) ≠ (nb090_alpha_dummy_701 v u h) from (by
          unfold nb090_alpha_dummy_701;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0818 v u h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090_alpha_dummy_044 v u h) ≠ (nb090_alpha_dummy_702 v u h) from (by
            unfold nb090_alpha_dummy_702;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0818 v u h) 1))))
    · rw [fv_syn_cfv]
      with_reducible rw [Finset.mem_union]
      left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0822 (A : Class) :
    (nb090_alpha_dummy_042 A) ∈
      (((Class.cv (nb090_alpha_dummy_000 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_042 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0823 (A : Class) :
    (nb090_alpha_dummy_042 A) ∈
      (({(nb090_alpha_dummy_777 A)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb090_alpha_dummy_042 A)) (Class.cv (nb090_alpha_dummy_000 A))
            (Class.cv (nb090_alpha_dummy_777 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_wbr]
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0824 (A : Class) :
    (nb090_alpha_dummy_042 A) ∈
      (((Class.cab (nb090_alpha_dummy_779 A) (Wff.classEq (Class.cab (nb090_alpha_dummy_777 A)
              (syn_wbr (Class.cv (nb090_alpha_dummy_042 A)) (Class.cv (nb090_alpha_dummy_000 A))
                (Class.cv (nb090_alpha_dummy_777 A))))
            (syn_csn (Class.cv (nb090_alpha_dummy_779 A)))))).fv) :=
  by
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090_alpha_dummy_042 A) ≠ (nb090_alpha_dummy_779 A) from (by
          unfold nb090_alpha_dummy_779;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0823 A) 0))))
  · rw [fv_wff_classEq]
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cab]
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090_alpha_dummy_042 A) ≠ (nb090_alpha_dummy_777 A) from (by
            unfold nb090_alpha_dummy_777;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0822 A) 0))))
    · rw [fv_syn_wbr]
      with_reducible rw [Finset.mem_union]
      left
      with_reducible rw [Finset.mem_union]
      left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0825 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_044 v u h) ∈
      (((Class.cv h)).fv ∪ ((Class.cv (nb090_alpha_dummy_044 v u h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0826 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_044 v u h) ∈
      (({(nb090_alpha_dummy_778 v u h)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb090_alpha_dummy_044 v u h)) (Class.cv h)
            (Class.cv (nb090_alpha_dummy_778 v u h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_wbr]
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0827 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_044 v u h) ∈
      (((Class.cab (nb090_alpha_dummy_780 v u h) (Wff.classEq
            (Class.cab (nb090_alpha_dummy_778 v u h)
              (syn_wbr (Class.cv (nb090_alpha_dummy_044 v u h)) (Class.cv h)
                (Class.cv (nb090_alpha_dummy_778 v u h))))
            (syn_csn (Class.cv (nb090_alpha_dummy_780 v u h)))))).fv) :=
  by
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090_alpha_dummy_044 v u h) ≠ (nb090_alpha_dummy_780 v u h) from (by
          unfold nb090_alpha_dummy_780;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0826 v u h) 0))))
  · rw [fv_wff_classEq]
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cab]
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090_alpha_dummy_044 v u h) ≠ (nb090_alpha_dummy_778 v u h) from (by
            unfold nb090_alpha_dummy_778;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0825 v u h) 0))))
    · rw [fv_syn_wbr]
      with_reducible rw [Finset.mem_union]
      left
      with_reducible rw [Finset.mem_union]
      left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0828 (A : Class) :
    (nb090_alpha_dummy_042 A) ∈
      (((Class.cv (nb090_alpha_dummy_042 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_777 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0829 (A : Class) :
    (nb090_alpha_dummy_042 A) ∈
      (((syn_ccompl (Class.cab (nb090_alpha_dummy_785 A)
              (syn_wrex (nb090_alpha_dummy_786 A) (Class.cv (nb090_alpha_dummy_042 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_785 A))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_786 A)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb090_alpha_dummy_785 A)
              (syn_wrex (nb090_alpha_dummy_786 A) (Class.cv (nb090_alpha_dummy_777 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_785 A))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_786 A)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090_alpha_dummy_042 A) ≠ (nb090_alpha_dummy_785 A) from (by
          unfold nb090_alpha_dummy_785;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0828 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090_alpha_dummy_042 A) ≠ (nb090_alpha_dummy_786 A) from (by
            unfold nb090_alpha_dummy_786;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0828 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0830 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_044 v u h) ∈
      (((Class.cv (nb090_alpha_dummy_044 v u h))).fv ∪
        ((Class.cv (nb090_alpha_dummy_778 v u h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0831 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_044 v u h) ∈
      (((syn_ccompl (Class.cab (nb090_alpha_dummy_787 v u h)
              (syn_wrex (nb090_alpha_dummy_788 v u h) (Class.cv (nb090_alpha_dummy_044 v u h))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_787 v u h))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_788 v u h)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb090_alpha_dummy_787 v u h) (syn_wrex (nb090_alpha_dummy_788 v u h)
                (Class.cv (nb090_alpha_dummy_778 v u h))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_787 v u h))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_788 v u h)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090_alpha_dummy_044 v u h) ≠ (nb090_alpha_dummy_787 v u h) from (by
          unfold nb090_alpha_dummy_787;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0830 v u h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090_alpha_dummy_044 v u h) ≠ (nb090_alpha_dummy_788 v u h) from (by
            unfold nb090_alpha_dummy_788;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0830 v u h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0832 (A : Class) :
    (nb090_alpha_dummy_042 A) ∈
      (((Class.cab (nb090_alpha_dummy_785 A)
            (syn_wrex (nb090_alpha_dummy_786 A) (Class.cv (nb090_alpha_dummy_042 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_785 A))
                (syn_cphi (Class.cv (nb090_alpha_dummy_786 A))))))).fv ∪
        ((Class.cab (nb090_alpha_dummy_785 A)
            (syn_wrex (nb090_alpha_dummy_786 A) (Class.cv (nb090_alpha_dummy_042 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_785 A))
                (syn_cphi (Class.cv (nb090_alpha_dummy_786 A))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090_alpha_dummy_042 A) ≠ (nb090_alpha_dummy_785 A) from (by
          unfold nb090_alpha_dummy_785;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0828 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090_alpha_dummy_042 A) ≠ (nb090_alpha_dummy_786 A) from (by
            unfold nb090_alpha_dummy_786;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0828 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0833 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_044 v u h) ∈
      (((Class.cab (nb090_alpha_dummy_787 v u h) (syn_wrex (nb090_alpha_dummy_788 v u h)
              (Class.cv (nb090_alpha_dummy_044 v u h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_787 v u h))
                (syn_cphi (Class.cv (nb090_alpha_dummy_788 v u h))))))).fv ∪
        ((Class.cab (nb090_alpha_dummy_787 v u h) (syn_wrex (nb090_alpha_dummy_788 v u h)
              (Class.cv (nb090_alpha_dummy_044 v u h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_787 v u h))
                (syn_cphi (Class.cv (nb090_alpha_dummy_788 v u h))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090_alpha_dummy_044 v u h) ≠ (nb090_alpha_dummy_787 v u h) from (by
          unfold nb090_alpha_dummy_787;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0830 v u h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090_alpha_dummy_044 v u h) ≠ (nb090_alpha_dummy_788 v u h) from (by
            unfold nb090_alpha_dummy_788;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0830 v u h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0834 (A : Class) :
    (nb090_alpha_dummy_786 A) ∈ (((Class.cv (nb090_alpha_dummy_786 A))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0835 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_788 v u h) ∈ (((Class.cv (nb090_alpha_dummy_788 v u h))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0836 (A : Class) :
    (nb090_alpha_dummy_793 A) ∈
      (((Wff.classMem (Class.cv (nb090_alpha_dummy_793 A)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb090_alpha_dummy_793 A)) (syn_c1c))).fv ∪
        ((Class.cv (nb090_alpha_dummy_793 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_wff_classMem]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0837 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_795 v u h) ∈
      (((Wff.classMem (Class.cv (nb090_alpha_dummy_795 v u h)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb090_alpha_dummy_795 v u h)) (syn_c1c))).fv ∪
        ((Class.cv (nb090_alpha_dummy_795 v u h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_wff_classMem]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0838 (A : Class) :
    (nb090_alpha_dummy_793 A) ∈
      (((Class.cv (nb090_alpha_dummy_793 A))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0839 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_795 v u h) ∈
      (((Class.cv (nb090_alpha_dummy_795 v u h))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0840 (A : Class) :
    (nb090_alpha_dummy_800 A) ∈
      (((syn_cnin (Class.cv (nb090_alpha_dummy_800 A))
            (Class.cv (nb090_alpha_dummy_801 A)))).fv ∪
        ((syn_cnin (Class.cv (nb090_alpha_dummy_800 A))
            (Class.cv (nb090_alpha_dummy_801 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0841 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_803 v u h) ∈
      (((syn_cnin (Class.cv (nb090_alpha_dummy_803 v u h))
            (Class.cv (nb090_alpha_dummy_804 v u h)))).fv ∪
        ((syn_cnin (Class.cv (nb090_alpha_dummy_803 v u h))
            (Class.cv (nb090_alpha_dummy_804 v u h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0842 (A : Class) :
    (nb090_alpha_dummy_800 A) ∈
      (((Class.cv (nb090_alpha_dummy_800 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_801 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0843 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_803 v u h) ∈
      (((Class.cv (nb090_alpha_dummy_803 v u h))).fv ∪
        ((Class.cv (nb090_alpha_dummy_804 v u h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0844 (A : Class) :
    (nb090_alpha_dummy_801 A) ∈
      (((syn_cnin (Class.cv (nb090_alpha_dummy_800 A))
            (Class.cv (nb090_alpha_dummy_801 A)))).fv ∪
        ((syn_cnin (Class.cv (nb090_alpha_dummy_800 A))
            (Class.cv (nb090_alpha_dummy_801 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0845 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_804 v u h) ∈
      (((syn_cnin (Class.cv (nb090_alpha_dummy_803 v u h))
            (Class.cv (nb090_alpha_dummy_804 v u h)))).fv ∪
        ((syn_cnin (Class.cv (nb090_alpha_dummy_803 v u h))
            (Class.cv (nb090_alpha_dummy_804 v u h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0846 (A : Class) :
    (nb090_alpha_dummy_801 A) ∈
      (((Class.cv (nb090_alpha_dummy_800 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_801 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0847 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_804 v u h) ∈
      (((Class.cv (nb090_alpha_dummy_803 v u h))).fv ∪
        ((Class.cv (nb090_alpha_dummy_804 v u h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0848 (A : Class) :
    (nb090_alpha_dummy_800 A) ∈
      (((syn_ccompl (Class.cv (nb090_alpha_dummy_800 A)))).fv ∪
        ((syn_ccompl (Class.cv (nb090_alpha_dummy_801 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0849 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_803 v u h) ∈
      (((syn_ccompl (Class.cv (nb090_alpha_dummy_803 v u h)))).fv ∪
        ((syn_ccompl (Class.cv (nb090_alpha_dummy_804 v u h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0850 (A : Class) :
    (nb090_alpha_dummy_800 A) ∈
      (((Class.cv (nb090_alpha_dummy_800 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_800 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0851 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_803 v u h) ∈
      (((Class.cv (nb090_alpha_dummy_803 v u h))).fv ∪
        ((Class.cv (nb090_alpha_dummy_803 v u h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0852 (A : Class) :
    (nb090_alpha_dummy_801 A) ∈
      (((syn_ccompl (Class.cv (nb090_alpha_dummy_800 A)))).fv ∪
        ((syn_ccompl (Class.cv (nb090_alpha_dummy_801 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0853 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_804 v u h) ∈
      (((syn_ccompl (Class.cv (nb090_alpha_dummy_803 v u h)))).fv ∪
        ((syn_ccompl (Class.cv (nb090_alpha_dummy_804 v u h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0854 (A : Class) :
    (nb090_alpha_dummy_801 A) ∈
      (((Class.cv (nb090_alpha_dummy_801 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_801 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0855 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_804 v u h) ∈
      (((Class.cv (nb090_alpha_dummy_804 v u h))).fv ∪
        ((Class.cv (nb090_alpha_dummy_804 v u h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0856 (A : Class) :
    (nb090_alpha_dummy_777 A) ∈
      (((Class.cv (nb090_alpha_dummy_042 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_777 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0857 (A : Class) :
    (nb090_alpha_dummy_777 A) ∈
      (((syn_ccompl (Class.cab (nb090_alpha_dummy_785 A)
              (syn_wrex (nb090_alpha_dummy_786 A) (Class.cv (nb090_alpha_dummy_042 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_785 A))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_786 A)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb090_alpha_dummy_785 A)
              (syn_wrex (nb090_alpha_dummy_786 A) (Class.cv (nb090_alpha_dummy_777 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_785 A))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_786 A)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090_alpha_dummy_777 A) ≠ (nb090_alpha_dummy_785 A) from (by
          unfold nb090_alpha_dummy_785;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0856 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090_alpha_dummy_777 A) ≠ (nb090_alpha_dummy_786 A) from (by
            unfold nb090_alpha_dummy_786;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0856 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0858 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_778 v u h) ∈
      (((Class.cv (nb090_alpha_dummy_044 v u h))).fv ∪
        ((Class.cv (nb090_alpha_dummy_778 v u h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0859 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_778 v u h) ∈
      (((syn_ccompl (Class.cab (nb090_alpha_dummy_787 v u h)
              (syn_wrex (nb090_alpha_dummy_788 v u h) (Class.cv (nb090_alpha_dummy_044 v u h))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_787 v u h))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_788 v u h)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb090_alpha_dummy_787 v u h) (syn_wrex (nb090_alpha_dummy_788 v u h)
                (Class.cv (nb090_alpha_dummy_778 v u h))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_787 v u h))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_788 v u h)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090_alpha_dummy_778 v u h) ≠ (nb090_alpha_dummy_787 v u h) from (by
          unfold nb090_alpha_dummy_787;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0858 v u h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090_alpha_dummy_778 v u h) ≠ (nb090_alpha_dummy_788 v u h) from (by
            unfold nb090_alpha_dummy_788;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0858 v u h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0860 (A : Class) :
    (nb090_alpha_dummy_777 A) ∈
      (((Class.cab (nb090_alpha_dummy_785 A)
            (syn_wrex (nb090_alpha_dummy_786 A) (Class.cv (nb090_alpha_dummy_777 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_785 A))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_786 A)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_785 A)
            (syn_wrex (nb090_alpha_dummy_786 A) (Class.cv (nb090_alpha_dummy_777 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_785 A))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_786 A)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090_alpha_dummy_777 A) ≠ (nb090_alpha_dummy_785 A) from (by
          unfold nb090_alpha_dummy_785;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0856 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090_alpha_dummy_777 A) ≠ (nb090_alpha_dummy_786 A) from (by
            unfold nb090_alpha_dummy_786;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0856 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0861 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_778 v u h) ∈
      (((Class.cab (nb090_alpha_dummy_787 v u h) (syn_wrex (nb090_alpha_dummy_788 v u h)
              (Class.cv (nb090_alpha_dummy_778 v u h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_787 v u h))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_788 v u h)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_787 v u h)
            (syn_wrex (nb090_alpha_dummy_788 v u h) (Class.cv (nb090_alpha_dummy_778 v u h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_787 v u h))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_788 v u h)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090_alpha_dummy_778 v u h) ≠ (nb090_alpha_dummy_787 v u h) from (by
          unfold nb090_alpha_dummy_787;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0858 v u h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090_alpha_dummy_778 v u h) ≠ (nb090_alpha_dummy_788 v u h) from (by
            unfold nb090_alpha_dummy_788;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0858 v u h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0862 (A : Class) :
    (nb090_alpha_dummy_786 A) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_786 A))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0863 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_788 v u h) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_788 v u h))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0864 (A : Class) :
    (nb090_alpha_dummy_786 A) ∈
      (((syn_cphi (Class.cv (nb090_alpha_dummy_786 A)))).fv ∪
        ((syn_cphi (Class.cv (nb090_alpha_dummy_786 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0865 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_788 v u h) ∈
      (((syn_cphi (Class.cv (nb090_alpha_dummy_788 v u h)))).fv ∪
        ((syn_cphi (Class.cv (nb090_alpha_dummy_788 v u h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0866 (A : Class) :
    (nb090_alpha_dummy_000 A) ∈
      (((Class.cab (nb090_alpha_dummy_699 A) (syn_wrex (nb090_alpha_dummy_700 A)
              (syn_cfv (Class.cv (nb090_alpha_dummy_000 A))
                (Class.cv (nb090_alpha_dummy_042 A)))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_699 A))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_700 A)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_699 A)
            (syn_wrex (nb090_alpha_dummy_700 A) (syn_cfv (Class.cv (nb090_alpha_dummy_000 A))
                (Class.cv (nb090_alpha_dummy_042 A)))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_699 A))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_700 A)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090_alpha_dummy_000 A) ≠ (nb090_alpha_dummy_699 A) from (by
          unfold nb090_alpha_dummy_699;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0780 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090_alpha_dummy_000 A) ≠ (nb090_alpha_dummy_700 A) from (by
            unfold nb090_alpha_dummy_700;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0780 A) 1))))
    · rw [fv_syn_cfv]
      with_reducible rw [Finset.mem_union]
      right
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0867 (v : Var) (u : Var) (h : Var) :
    h ∈
      (((Class.cab (nb090_alpha_dummy_701 v u h) (syn_wrex (nb090_alpha_dummy_702 v u h)
              (syn_cfv (Class.cv h) (Class.cv (nb090_alpha_dummy_044 v u h)))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_701 v u h))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_702 v u h)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_701 v u h)
            (syn_wrex (nb090_alpha_dummy_702 v u h)
              (syn_cfv (Class.cv h) (Class.cv (nb090_alpha_dummy_044 v u h)))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_701 v u h))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_702 v u h)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show h ≠ (nb090_alpha_dummy_701 v u h) from (by
          unfold nb090_alpha_dummy_701;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0782 v u h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show h ≠ (nb090_alpha_dummy_702 v u h) from (by
            unfold nb090_alpha_dummy_702;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0782 v u h) 1))))
    · rw [fv_syn_cfv]
      with_reducible rw [Finset.mem_union]
      right
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0868 (A : Class) :
    (nb090_alpha_dummy_000 A) ∈
      (((Class.cv (nb090_alpha_dummy_000 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_042 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0869 (A : Class) :
    (nb090_alpha_dummy_000 A) ∈
      (({(nb090_alpha_dummy_777 A)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb090_alpha_dummy_042 A)) (Class.cv (nb090_alpha_dummy_000 A))
            (Class.cv (nb090_alpha_dummy_777 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_wbr]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0870 (A : Class) :
    (nb090_alpha_dummy_000 A) ∈
      (((Class.cab (nb090_alpha_dummy_779 A) (Wff.classEq (Class.cab (nb090_alpha_dummy_777 A)
              (syn_wbr (Class.cv (nb090_alpha_dummy_042 A)) (Class.cv (nb090_alpha_dummy_000 A))
                (Class.cv (nb090_alpha_dummy_777 A))))
            (syn_csn (Class.cv (nb090_alpha_dummy_779 A)))))).fv) :=
  by
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090_alpha_dummy_000 A) ≠ (nb090_alpha_dummy_779 A) from (by
          unfold nb090_alpha_dummy_779;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0869 A) 0))))
  · rw [fv_wff_classEq]
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cab]
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090_alpha_dummy_000 A) ≠ (nb090_alpha_dummy_777 A) from (by
            unfold nb090_alpha_dummy_777;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0868 A) 0))))
    · rw [fv_syn_wbr]
      with_reducible rw [Finset.mem_union]
      right
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0871 (v : Var) (u : Var) (h : Var) :
    h ∈ (((Class.cv h)).fv ∪ ((Class.cv (nb090_alpha_dummy_044 v u h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0872 (v : Var) (u : Var) (h : Var) :
    h ∈
      (({(nb090_alpha_dummy_778 v u h)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb090_alpha_dummy_044 v u h)) (Class.cv h)
            (Class.cv (nb090_alpha_dummy_778 v u h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_wbr]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0873 (v : Var) (u : Var) (h : Var) :
    h ∈
      (((Class.cab (nb090_alpha_dummy_780 v u h) (Wff.classEq
            (Class.cab (nb090_alpha_dummy_778 v u h)
              (syn_wbr (Class.cv (nb090_alpha_dummy_044 v u h)) (Class.cv h)
                (Class.cv (nb090_alpha_dummy_778 v u h))))
            (syn_csn (Class.cv (nb090_alpha_dummy_780 v u h)))))).fv) :=
  by
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show h ≠ (nb090_alpha_dummy_780 v u h) from (by
          unfold nb090_alpha_dummy_780;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0872 v u h) 0))))
  · rw [fv_wff_classEq]
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cab]
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show h ≠ (nb090_alpha_dummy_778 v u h) from (by
            unfold nb090_alpha_dummy_778;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0871 v u h) 0))))
    · rw [fv_syn_wbr]
      with_reducible rw [Finset.mem_union]
      right
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0874 (A : Class) :
    (nb090_alpha_dummy_779 A) ∈ (((Class.cv (nb090_alpha_dummy_779 A))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0875 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_780 v u h) ∈ (((Class.cv (nb090_alpha_dummy_780 v u h))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0876 (A : Class) :
    (nb090_alpha_dummy_700 A) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_700 A))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0877 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_702 v u h) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_702 v u h))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0878 (A : Class) :
    (nb090_alpha_dummy_700 A) ∈
      (((syn_cphi (Class.cv (nb090_alpha_dummy_700 A)))).fv ∪
        ((syn_cphi (Class.cv (nb090_alpha_dummy_700 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0879 (v : Var) (u : Var) (h : Var) :
    (nb090_alpha_dummy_702 v u h) ∈
      (((syn_cphi (Class.cv (nb090_alpha_dummy_702 v u h)))).fv ∪
        ((syn_cphi (Class.cv (nb090_alpha_dummy_702 v u h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0880 (A : Class) :
    (nb090_alpha_dummy_002 A) ∈
      (((Class.cv (nb090_alpha_dummy_000 A))).fv ∪
              ((syn_cfv (syn_c1st) (Class.cv (nb090_alpha_dummy_001 A)))).fv ∪
            ((syn_cfv (syn_c1st) (Class.cv (nb090_alpha_dummy_002 A)))).fv ∪
          ((syn_cfv (syn_c2nd) (Class.cv (nb090_alpha_dummy_001 A)))).fv ∪
        ((syn_cfv (syn_c2nd) (Class.cv (nb090_alpha_dummy_002 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_cfv]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0881 (v : Var) (u : Var) (h : Var) :
    v ∈
      (((Class.cv h)).fv ∪ ((syn_cfv (syn_c1st) (Class.cv u))).fv ∪
            ((syn_cfv (syn_c1st) (Class.cv v))).fv ∪ ((syn_cfv (syn_c2nd) (Class.cv u))).fv ∪
        ((syn_cfv (syn_c2nd) (Class.cv v))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_cfv]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0882 (A : Class) :
    (nb090_alpha_dummy_002 A) ∈
      (((syn_c1st)).fv ∪ ((Class.cv (nb090_alpha_dummy_002 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0883 (A : Class) :
    (nb090_alpha_dummy_002 A) ∈
      (({(nb090_alpha_dummy_827 A)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb090_alpha_dummy_002 A)) (syn_c1st)
            (Class.cv (nb090_alpha_dummy_827 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_wbr]
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0884 (A : Class) :
    (nb090_alpha_dummy_002 A) ∈
      (((Class.cab (nb090_alpha_dummy_829 A) (Wff.classEq (Class.cab (nb090_alpha_dummy_827 A)
              (syn_wbr (Class.cv (nb090_alpha_dummy_002 A)) (syn_c1st)
                (Class.cv (nb090_alpha_dummy_827 A))))
            (syn_csn (Class.cv (nb090_alpha_dummy_829 A)))))).fv) :=
  by
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090_alpha_dummy_002 A) ≠ (nb090_alpha_dummy_829 A) from (by
          unfold nb090_alpha_dummy_829;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0883 A) 0))))
  · rw [fv_wff_classEq]
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cab]
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090_alpha_dummy_002 A) ≠ (nb090_alpha_dummy_827 A) from (by
            unfold nb090_alpha_dummy_827;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0882 A) 0))))
    · rw [fv_syn_wbr]
      with_reducible rw [Finset.mem_union]
      left
      with_reducible rw [Finset.mem_union]
      left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C090C001Part022`. -/


section

namespace NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

open scoped Fol
open NFChoice.Foundation
open NFChoice.Foundation.ExactLiteralTrial
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax
open NFChoice.Compiler.CompactSyntaxFVExplicit
open NFChoice.Compiler.WPPCompactSyntaxFVExplicit
open NFChoice.Compiler.CoreFVSimp
open NFChoice.DefinitionLeaves.AlphaFocusedSupport
open NFChoice.DefinitionLeaves.AlphaFocusedFV
open NFChoice.DirectNominalPrf
open NFChoice.DirectNominalPrf.Nominal

theorem nb090_support_mem_0885 (v : Var) : v ∈ (((syn_c1st)).fv ∪ ((Class.cv v)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0886 (v : Var) :
    v ∈
      (({(nb090_alpha_dummy_828 v)} : Finset Var) ∪
        ((syn_wbr (Class.cv v) (syn_c1st) (Class.cv (nb090_alpha_dummy_828 v)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_wbr]
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0887 (v : Var) :
    v ∈
      (((Class.cab (nb090_alpha_dummy_830 v) (Wff.classEq (Class.cab (nb090_alpha_dummy_828 v)
              (syn_wbr (Class.cv v) (syn_c1st) (Class.cv (nb090_alpha_dummy_828 v))))
            (syn_csn (Class.cv (nb090_alpha_dummy_830 v)))))).fv) :=
  by
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show v ≠ (nb090_alpha_dummy_830 v) from (by
          unfold nb090_alpha_dummy_830;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0886 v) 0))))
  · rw [fv_wff_classEq]
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cab]
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show v ≠ (nb090_alpha_dummy_828 v) from (by
            unfold nb090_alpha_dummy_828;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0885 v) 0))))
    · rw [fv_syn_wbr]
      with_reducible rw [Finset.mem_union]
      left
      with_reducible rw [Finset.mem_union]
      left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0888 (A : Class) :
    (nb090_alpha_dummy_002 A) ∈
      (((Class.cv (nb090_alpha_dummy_002 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_827 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0889 (A : Class) :
    (nb090_alpha_dummy_002 A) ∈
      (((syn_ccompl (Class.cab (nb090_alpha_dummy_835 A)
              (syn_wrex (nb090_alpha_dummy_836 A) (Class.cv (nb090_alpha_dummy_002 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_835 A))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_836 A)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb090_alpha_dummy_835 A)
              (syn_wrex (nb090_alpha_dummy_836 A) (Class.cv (nb090_alpha_dummy_827 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_835 A))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_836 A)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090_alpha_dummy_002 A) ≠ (nb090_alpha_dummy_835 A) from (by
          unfold nb090_alpha_dummy_835;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0888 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090_alpha_dummy_002 A) ≠ (nb090_alpha_dummy_836 A) from (by
            unfold nb090_alpha_dummy_836;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0888 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0890 (v : Var) :
    v ∈ (((Class.cv v)).fv ∪ ((Class.cv (nb090_alpha_dummy_828 v))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0891 (v : Var) :
    v ∈
      (((syn_ccompl (Class.cab (nb090_alpha_dummy_837 v)
              (syn_wrex (nb090_alpha_dummy_838 v) (Class.cv v)
                (Wff.classEq (Class.cv (nb090_alpha_dummy_837 v))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_838 v)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb090_alpha_dummy_837 v)
              (syn_wrex (nb090_alpha_dummy_838 v) (Class.cv (nb090_alpha_dummy_828 v))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_837 v))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_838 v)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show v ≠ (nb090_alpha_dummy_837 v) from (by
          unfold nb090_alpha_dummy_837;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0890 v) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show v ≠ (nb090_alpha_dummy_838 v) from (by
            unfold nb090_alpha_dummy_838;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0890 v) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0892 (A : Class) :
    (nb090_alpha_dummy_002 A) ∈
      (((Class.cab (nb090_alpha_dummy_835 A)
            (syn_wrex (nb090_alpha_dummy_836 A) (Class.cv (nb090_alpha_dummy_002 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_835 A))
                (syn_cphi (Class.cv (nb090_alpha_dummy_836 A))))))).fv ∪
        ((Class.cab (nb090_alpha_dummy_835 A)
            (syn_wrex (nb090_alpha_dummy_836 A) (Class.cv (nb090_alpha_dummy_002 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_835 A))
                (syn_cphi (Class.cv (nb090_alpha_dummy_836 A))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090_alpha_dummy_002 A) ≠ (nb090_alpha_dummy_835 A) from (by
          unfold nb090_alpha_dummy_835;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0888 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090_alpha_dummy_002 A) ≠ (nb090_alpha_dummy_836 A) from (by
            unfold nb090_alpha_dummy_836;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0888 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0893 (v : Var) :
    v ∈
      (((Class.cab (nb090_alpha_dummy_837 v) (syn_wrex (nb090_alpha_dummy_838 v) (Class.cv v)
              (Wff.classEq (Class.cv (nb090_alpha_dummy_837 v))
                (syn_cphi (Class.cv (nb090_alpha_dummy_838 v))))))).fv ∪
        ((Class.cab (nb090_alpha_dummy_837 v) (syn_wrex (nb090_alpha_dummy_838 v) (Class.cv v)
              (Wff.classEq (Class.cv (nb090_alpha_dummy_837 v))
                (syn_cphi (Class.cv (nb090_alpha_dummy_838 v))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show v ≠ (nb090_alpha_dummy_837 v) from (by
          unfold nb090_alpha_dummy_837;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0890 v) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show v ≠ (nb090_alpha_dummy_838 v) from (by
            unfold nb090_alpha_dummy_838;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0890 v) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0894 (A : Class) :
    (nb090_alpha_dummy_836 A) ∈ (((Class.cv (nb090_alpha_dummy_836 A))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0895 (v : Var) :
    (nb090_alpha_dummy_838 v) ∈ (((Class.cv (nb090_alpha_dummy_838 v))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0896 (A : Class) :
    (nb090_alpha_dummy_843 A) ∈
      (((Wff.classMem (Class.cv (nb090_alpha_dummy_843 A)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb090_alpha_dummy_843 A)) (syn_c1c))).fv ∪
        ((Class.cv (nb090_alpha_dummy_843 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_wff_classMem]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0897 (v : Var) :
    (nb090_alpha_dummy_845 v) ∈
      (((Wff.classMem (Class.cv (nb090_alpha_dummy_845 v)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb090_alpha_dummy_845 v)) (syn_c1c))).fv ∪
        ((Class.cv (nb090_alpha_dummy_845 v))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_wff_classMem]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0898 (A : Class) :
    (nb090_alpha_dummy_843 A) ∈
      (((Class.cv (nb090_alpha_dummy_843 A))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0899 (v : Var) :
    (nb090_alpha_dummy_845 v) ∈
      (((Class.cv (nb090_alpha_dummy_845 v))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0900 (A : Class) :
    (nb090_alpha_dummy_850 A) ∈
      (((syn_cnin (Class.cv (nb090_alpha_dummy_850 A))
            (Class.cv (nb090_alpha_dummy_851 A)))).fv ∪
        ((syn_cnin (Class.cv (nb090_alpha_dummy_850 A))
            (Class.cv (nb090_alpha_dummy_851 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0901 (v : Var) :
    (nb090_alpha_dummy_853 v) ∈
      (((syn_cnin (Class.cv (nb090_alpha_dummy_853 v))
            (Class.cv (nb090_alpha_dummy_854 v)))).fv ∪
        ((syn_cnin (Class.cv (nb090_alpha_dummy_853 v))
            (Class.cv (nb090_alpha_dummy_854 v)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0902 (A : Class) :
    (nb090_alpha_dummy_850 A) ∈
      (((Class.cv (nb090_alpha_dummy_850 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_851 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0903 (v : Var) :
    (nb090_alpha_dummy_853 v) ∈
      (((Class.cv (nb090_alpha_dummy_853 v))).fv ∪ ((Class.cv (nb090_alpha_dummy_854 v))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0904 (A : Class) :
    (nb090_alpha_dummy_851 A) ∈
      (((syn_cnin (Class.cv (nb090_alpha_dummy_850 A))
            (Class.cv (nb090_alpha_dummy_851 A)))).fv ∪
        ((syn_cnin (Class.cv (nb090_alpha_dummy_850 A))
            (Class.cv (nb090_alpha_dummy_851 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0905 (v : Var) :
    (nb090_alpha_dummy_854 v) ∈
      (((syn_cnin (Class.cv (nb090_alpha_dummy_853 v))
            (Class.cv (nb090_alpha_dummy_854 v)))).fv ∪
        ((syn_cnin (Class.cv (nb090_alpha_dummy_853 v))
            (Class.cv (nb090_alpha_dummy_854 v)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0906 (A : Class) :
    (nb090_alpha_dummy_851 A) ∈
      (((Class.cv (nb090_alpha_dummy_850 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_851 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0907 (v : Var) :
    (nb090_alpha_dummy_854 v) ∈
      (((Class.cv (nb090_alpha_dummy_853 v))).fv ∪ ((Class.cv (nb090_alpha_dummy_854 v))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0908 (A : Class) :
    (nb090_alpha_dummy_850 A) ∈
      (((syn_ccompl (Class.cv (nb090_alpha_dummy_850 A)))).fv ∪
        ((syn_ccompl (Class.cv (nb090_alpha_dummy_851 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0909 (v : Var) :
    (nb090_alpha_dummy_853 v) ∈
      (((syn_ccompl (Class.cv (nb090_alpha_dummy_853 v)))).fv ∪
        ((syn_ccompl (Class.cv (nb090_alpha_dummy_854 v)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0910 (A : Class) :
    (nb090_alpha_dummy_850 A) ∈
      (((Class.cv (nb090_alpha_dummy_850 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_850 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0911 (v : Var) :
    (nb090_alpha_dummy_853 v) ∈
      (((Class.cv (nb090_alpha_dummy_853 v))).fv ∪ ((Class.cv (nb090_alpha_dummy_853 v))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0912 (A : Class) :
    (nb090_alpha_dummy_851 A) ∈
      (((syn_ccompl (Class.cv (nb090_alpha_dummy_850 A)))).fv ∪
        ((syn_ccompl (Class.cv (nb090_alpha_dummy_851 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0913 (v : Var) :
    (nb090_alpha_dummy_854 v) ∈
      (((syn_ccompl (Class.cv (nb090_alpha_dummy_853 v)))).fv ∪
        ((syn_ccompl (Class.cv (nb090_alpha_dummy_854 v)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0914 (A : Class) :
    (nb090_alpha_dummy_851 A) ∈
      (((Class.cv (nb090_alpha_dummy_851 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_851 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0915 (v : Var) :
    (nb090_alpha_dummy_854 v) ∈
      (((Class.cv (nb090_alpha_dummy_854 v))).fv ∪ ((Class.cv (nb090_alpha_dummy_854 v))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0916 (A : Class) :
    (nb090_alpha_dummy_827 A) ∈
      (((Class.cv (nb090_alpha_dummy_002 A))).fv ∪ ((Class.cv (nb090_alpha_dummy_827 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0917 (A : Class) :
    (nb090_alpha_dummy_827 A) ∈
      (((syn_ccompl (Class.cab (nb090_alpha_dummy_835 A)
              (syn_wrex (nb090_alpha_dummy_836 A) (Class.cv (nb090_alpha_dummy_002 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_835 A))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_836 A)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb090_alpha_dummy_835 A)
              (syn_wrex (nb090_alpha_dummy_836 A) (Class.cv (nb090_alpha_dummy_827 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_835 A))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_836 A)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090_alpha_dummy_827 A) ≠ (nb090_alpha_dummy_835 A) from (by
          unfold nb090_alpha_dummy_835;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0916 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090_alpha_dummy_827 A) ≠ (nb090_alpha_dummy_836 A) from (by
            unfold nb090_alpha_dummy_836;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0916 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0918 (v : Var) :
    (nb090_alpha_dummy_828 v) ∈
      (((Class.cv v)).fv ∪ ((Class.cv (nb090_alpha_dummy_828 v))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0919 (v : Var) :
    (nb090_alpha_dummy_828 v) ∈
      (((syn_ccompl (Class.cab (nb090_alpha_dummy_837 v)
              (syn_wrex (nb090_alpha_dummy_838 v) (Class.cv v)
                (Wff.classEq (Class.cv (nb090_alpha_dummy_837 v))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_838 v)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb090_alpha_dummy_837 v)
              (syn_wrex (nb090_alpha_dummy_838 v) (Class.cv (nb090_alpha_dummy_828 v))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_837 v))
                  (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_838 v)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090_alpha_dummy_828 v) ≠ (nb090_alpha_dummy_837 v) from (by
          unfold nb090_alpha_dummy_837;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0918 v) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090_alpha_dummy_828 v) ≠ (nb090_alpha_dummy_838 v) from (by
            unfold nb090_alpha_dummy_838;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0918 v) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0920 (A : Class) :
    (nb090_alpha_dummy_827 A) ∈
      (((Class.cab (nb090_alpha_dummy_835 A)
            (syn_wrex (nb090_alpha_dummy_836 A) (Class.cv (nb090_alpha_dummy_827 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_835 A))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_836 A)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_835 A)
            (syn_wrex (nb090_alpha_dummy_836 A) (Class.cv (nb090_alpha_dummy_827 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_835 A))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_836 A)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090_alpha_dummy_827 A) ≠ (nb090_alpha_dummy_835 A) from (by
          unfold nb090_alpha_dummy_835;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0916 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090_alpha_dummy_827 A) ≠ (nb090_alpha_dummy_836 A) from (by
            unfold nb090_alpha_dummy_836;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0916 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0921 (v : Var) :
    (nb090_alpha_dummy_828 v) ∈
      (((Class.cab (nb090_alpha_dummy_837 v)
            (syn_wrex (nb090_alpha_dummy_838 v) (Class.cv (nb090_alpha_dummy_828 v))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_837 v))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_838 v)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb090_alpha_dummy_837 v)
            (syn_wrex (nb090_alpha_dummy_838 v) (Class.cv (nb090_alpha_dummy_828 v))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_837 v))
                (syn_cun (syn_cphi (Class.cv (nb090_alpha_dummy_838 v)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090_alpha_dummy_828 v) ≠ (nb090_alpha_dummy_837 v) from (by
          unfold nb090_alpha_dummy_837;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0918 v) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090_alpha_dummy_828 v) ≠ (nb090_alpha_dummy_838 v) from (by
            unfold nb090_alpha_dummy_838;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0918 v) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0922 (A : Class) :
    (nb090_alpha_dummy_836 A) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_836 A))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0923 (v : Var) :
    (nb090_alpha_dummy_838 v) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb090_alpha_dummy_838 v))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0924 (A : Class) :
    (nb090_alpha_dummy_836 A) ∈
      (((syn_cphi (Class.cv (nb090_alpha_dummy_836 A)))).fv ∪
        ((syn_cphi (Class.cv (nb090_alpha_dummy_836 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0925 (v : Var) :
    (nb090_alpha_dummy_838 v) ∈
      (((syn_cphi (Class.cv (nb090_alpha_dummy_838 v)))).fv ∪
        ((syn_cphi (Class.cv (nb090_alpha_dummy_838 v)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0926 (A : Class) :
    (nb090_alpha_dummy_829 A) ∈ (((Class.cv (nb090_alpha_dummy_829 A))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0927 (v : Var) :
    (nb090_alpha_dummy_830 v) ∈ (((Class.cv (nb090_alpha_dummy_830 v))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_compact_fv_empty_0020 (A : Class) :
    (nb090_alpha_dummy_002 A) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb090_compact_fv_empty_0021 (v : Var) : v ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb090_compact_fv_empty_0022 (A : Class) :
    (nb090_alpha_dummy_001 A) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb090_compact_fv_empty_0023 (u : Var) : u ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb090_compact_fv_empty_0024 (A : Class) :
    (nb090_alpha_dummy_003 A) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb090_compact_fv_empty_0025 (v : Var) (u : Var) (A : Class) (h : Var) :
    (nb090_alpha_dummy_004 v u A h) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
