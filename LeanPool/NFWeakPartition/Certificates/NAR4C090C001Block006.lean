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
    (nb090AlphaDummy427 h) ∈
      (((synCcompl (Class.cab (nb090AlphaDummy583 h)
              (synWrex (nb090AlphaDummy584 h) (Class.cv (nb090AlphaDummy428 h))
                (Wff.classEq (Class.cv (nb090AlphaDummy583 h))
                  (synCphi (Class.cv (nb090AlphaDummy584 h)))))))).fv ∪ ((synCcompl
            (Class.cab (nb090AlphaDummy583 h)
              (synWrex (nb090AlphaDummy584 h) (Class.cv (nb090AlphaDummy427 h))
                (Wff.classEq (Class.cv (nb090AlphaDummy583 h))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy584 h)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090AlphaDummy427 h) ≠ (nb090AlphaDummy583 h) from (by
          unfold nb090AlphaDummy583;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0634 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090AlphaDummy427 h) ≠ (nb090AlphaDummy584 h) from (by
            unfold nb090AlphaDummy584;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0634 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0636 (A : Class) :
    (nb090AlphaDummy424 A) ∈
      (((Class.cab (nb090AlphaDummy581 A)
            (synWrex (nb090AlphaDummy582 A) (Class.cv (nb090AlphaDummy424 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy581 A))
                (synCun (synCphi (Class.cv (nb090AlphaDummy582 A)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb090AlphaDummy581 A)
            (synWrex (nb090AlphaDummy582 A) (Class.cv (nb090AlphaDummy424 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy581 A))
                (synCun (synCphi (Class.cv (nb090AlphaDummy582 A)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090AlphaDummy424 A) ≠ (nb090AlphaDummy581 A) from (by
          unfold nb090AlphaDummy581;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0632 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090AlphaDummy424 A) ≠ (nb090AlphaDummy582 A) from (by
            unfold nb090AlphaDummy582;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0632 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0637 (h : Var) :
    (nb090AlphaDummy427 h) ∈
      (((Class.cab (nb090AlphaDummy583 h)
            (synWrex (nb090AlphaDummy584 h) (Class.cv (nb090AlphaDummy427 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy583 h))
                (synCun (synCphi (Class.cv (nb090AlphaDummy584 h)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb090AlphaDummy583 h)
            (synWrex (nb090AlphaDummy584 h) (Class.cv (nb090AlphaDummy427 h))
              (Wff.classEq (Class.cv (nb090AlphaDummy583 h))
                (synCun (synCphi (Class.cv (nb090AlphaDummy584 h)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090AlphaDummy427 h) ≠ (nb090AlphaDummy583 h) from (by
          unfold nb090AlphaDummy583;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0634 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090AlphaDummy427 h) ≠ (nb090AlphaDummy584 h) from (by
            unfold nb090AlphaDummy584;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0634 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0638 (A : Class) :
    (nb090AlphaDummy582 A) ∈
      (((synCcompl (synCphi (Class.cv (nb090AlphaDummy582 A))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0639 (h : Var) :
    (nb090AlphaDummy584 h) ∈
      (((synCcompl (synCphi (Class.cv (nb090AlphaDummy584 h))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0640 (A : Class) :
    (nb090AlphaDummy582 A) ∈
      (((synCphi (Class.cv (nb090AlphaDummy582 A)))).fv ∪
        ((synCphi (Class.cv (nb090AlphaDummy582 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0641 (h : Var) :
    (nb090AlphaDummy584 h) ∈
      (((synCphi (Class.cv (nb090AlphaDummy584 h)))).fv ∪
        ((synCphi (Class.cv (nb090AlphaDummy584 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0642 (A : Class) :
    (nb090AlphaDummy001 A) ∈
      (((Class.cv (nb090AlphaDummy000 A))).fv ∪
              ((synCfv (synC1st) (Class.cv (nb090AlphaDummy001 A)))).fv ∪
            ((synCfv (synC1st) (Class.cv (nb090AlphaDummy002 A)))).fv ∪
          ((synCfv (synC2nd) (Class.cv (nb090AlphaDummy001 A)))).fv ∪
        ((synCfv (synC2nd) (Class.cv (nb090AlphaDummy002 A)))).fv) :=
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
      (((Class.cv h)).fv ∪ ((synCfv (synC1st) (Class.cv u))).fv ∪
            ((synCfv (synC1st) (Class.cv v))).fv ∪ ((synCfv (synC2nd) (Class.cv u))).fv ∪
        ((synCfv (synC2nd) (Class.cv v))).fv) :=
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
    (nb090AlphaDummy041 A) ∈
      (((Class.cv (nb090AlphaDummy041 A))).fv ∪ ((Class.cv (nb090AlphaDummy042 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0645 (A : Class) :
    (nb090AlphaDummy041 A) ∈
      (((synCcompl (Class.cab (nb090AlphaDummy617 A)
              (synWrex (nb090AlphaDummy618 A) (Class.cv (nb090AlphaDummy041 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy617 A))
                  (synCphi (Class.cv (nb090AlphaDummy618 A)))))))).fv ∪ ((synCcompl
            (Class.cab (nb090AlphaDummy617 A)
              (synWrex (nb090AlphaDummy618 A) (Class.cv (nb090AlphaDummy042 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy617 A))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy618 A)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090AlphaDummy041 A) ≠ (nb090AlphaDummy617 A) from (by
          unfold nb090AlphaDummy617;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0644 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090AlphaDummy041 A) ≠ (nb090AlphaDummy618 A) from (by
            unfold nb090AlphaDummy618;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0644 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0646 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy043 v u h) ∈
      (((Class.cv (nb090AlphaDummy043 v u h))).fv ∪
        ((Class.cv (nb090AlphaDummy044 v u h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0647 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy043 v u h) ∈
      (((synCcompl (Class.cab (nb090AlphaDummy619 v u h)
              (synWrex (nb090AlphaDummy620 v u h) (Class.cv (nb090AlphaDummy043 v u h))
                (Wff.classEq (Class.cv (nb090AlphaDummy619 v u h))
                  (synCphi (Class.cv (nb090AlphaDummy620 v u h)))))))).fv ∪ ((synCcompl
            (Class.cab (nb090AlphaDummy619 v u h) (synWrex (nb090AlphaDummy620 v u h)
                (Class.cv (nb090AlphaDummy044 v u h))
                (Wff.classEq (Class.cv (nb090AlphaDummy619 v u h))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy620 v u h)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090AlphaDummy043 v u h) ≠ (nb090AlphaDummy619 v u h) from (by
          unfold nb090AlphaDummy619;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0646 v u h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090AlphaDummy043 v u h) ≠ (nb090AlphaDummy620 v u h) from (by
            unfold nb090AlphaDummy620;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0646 v u h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0648 (A : Class) :
    (nb090AlphaDummy041 A) ∈
      (((Class.cab (nb090AlphaDummy617 A)
            (synWrex (nb090AlphaDummy618 A) (Class.cv (nb090AlphaDummy041 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy617 A))
                (synCphi (Class.cv (nb090AlphaDummy618 A))))))).fv ∪
        ((Class.cab (nb090AlphaDummy617 A)
            (synWrex (nb090AlphaDummy618 A) (Class.cv (nb090AlphaDummy041 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy617 A))
                (synCphi (Class.cv (nb090AlphaDummy618 A))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090AlphaDummy041 A) ≠ (nb090AlphaDummy617 A) from (by
          unfold nb090AlphaDummy617;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0644 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090AlphaDummy041 A) ≠ (nb090AlphaDummy618 A) from (by
            unfold nb090AlphaDummy618;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0644 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0649 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy043 v u h) ∈
      (((Class.cab (nb090AlphaDummy619 v u h) (synWrex (nb090AlphaDummy620 v u h)
              (Class.cv (nb090AlphaDummy043 v u h))
              (Wff.classEq (Class.cv (nb090AlphaDummy619 v u h))
                (synCphi (Class.cv (nb090AlphaDummy620 v u h))))))).fv ∪
        ((Class.cab (nb090AlphaDummy619 v u h) (synWrex (nb090AlphaDummy620 v u h)
              (Class.cv (nb090AlphaDummy043 v u h))
              (Wff.classEq (Class.cv (nb090AlphaDummy619 v u h))
                (synCphi (Class.cv (nb090AlphaDummy620 v u h))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090AlphaDummy043 v u h) ≠ (nb090AlphaDummy619 v u h) from (by
          unfold nb090AlphaDummy619;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0646 v u h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090AlphaDummy043 v u h) ≠ (nb090AlphaDummy620 v u h) from (by
            unfold nb090AlphaDummy620;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0646 v u h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0650 (A : Class) :
    (nb090AlphaDummy618 A) ∈ (((Class.cv (nb090AlphaDummy618 A))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0651 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy620 v u h) ∈ (((Class.cv (nb090AlphaDummy620 v u h))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0652 (A : Class) :
    (nb090AlphaDummy625 A) ∈
      (((Wff.classMem (Class.cv (nb090AlphaDummy625 A)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb090AlphaDummy625 A)) (synC1c))).fv ∪
        ((Class.cv (nb090AlphaDummy625 A))).fv) :=
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
    (nb090AlphaDummy627 v u h) ∈
      (((Wff.classMem (Class.cv (nb090AlphaDummy627 v u h)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb090AlphaDummy627 v u h)) (synC1c))).fv ∪
        ((Class.cv (nb090AlphaDummy627 v u h))).fv) :=
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
    (nb090AlphaDummy625 A) ∈
      (((Class.cv (nb090AlphaDummy625 A))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0655 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy627 v u h) ∈
      (((Class.cv (nb090AlphaDummy627 v u h))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0656 (A : Class) :
    (nb090AlphaDummy632 A) ∈
      (((synCnin (Class.cv (nb090AlphaDummy632 A))
            (Class.cv (nb090AlphaDummy633 A)))).fv ∪
        ((synCnin (Class.cv (nb090AlphaDummy632 A))
            (Class.cv (nb090AlphaDummy633 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0657 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy635 v u h) ∈
      (((synCnin (Class.cv (nb090AlphaDummy635 v u h))
            (Class.cv (nb090AlphaDummy636 v u h)))).fv ∪
        ((synCnin (Class.cv (nb090AlphaDummy635 v u h))
            (Class.cv (nb090AlphaDummy636 v u h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0658 (A : Class) :
    (nb090AlphaDummy632 A) ∈
      (((Class.cv (nb090AlphaDummy632 A))).fv ∪ ((Class.cv (nb090AlphaDummy633 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0659 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy635 v u h) ∈
      (((Class.cv (nb090AlphaDummy635 v u h))).fv ∪
        ((Class.cv (nb090AlphaDummy636 v u h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0660 (A : Class) :
    (nb090AlphaDummy633 A) ∈
      (((synCnin (Class.cv (nb090AlphaDummy632 A))
            (Class.cv (nb090AlphaDummy633 A)))).fv ∪
        ((synCnin (Class.cv (nb090AlphaDummy632 A))
            (Class.cv (nb090AlphaDummy633 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0661 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy636 v u h) ∈
      (((synCnin (Class.cv (nb090AlphaDummy635 v u h))
            (Class.cv (nb090AlphaDummy636 v u h)))).fv ∪
        ((synCnin (Class.cv (nb090AlphaDummy635 v u h))
            (Class.cv (nb090AlphaDummy636 v u h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0662 (A : Class) :
    (nb090AlphaDummy633 A) ∈
      (((Class.cv (nb090AlphaDummy632 A))).fv ∪ ((Class.cv (nb090AlphaDummy633 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0663 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy636 v u h) ∈
      (((Class.cv (nb090AlphaDummy635 v u h))).fv ∪
        ((Class.cv (nb090AlphaDummy636 v u h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0664 (A : Class) :
    (nb090AlphaDummy632 A) ∈
      (((synCcompl (Class.cv (nb090AlphaDummy632 A)))).fv ∪
        ((synCcompl (Class.cv (nb090AlphaDummy633 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0665 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy635 v u h) ∈
      (((synCcompl (Class.cv (nb090AlphaDummy635 v u h)))).fv ∪
        ((synCcompl (Class.cv (nb090AlphaDummy636 v u h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0666 (A : Class) :
    (nb090AlphaDummy632 A) ∈
      (((Class.cv (nb090AlphaDummy632 A))).fv ∪ ((Class.cv (nb090AlphaDummy632 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0667 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy635 v u h) ∈
      (((Class.cv (nb090AlphaDummy635 v u h))).fv ∪
        ((Class.cv (nb090AlphaDummy635 v u h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0668 (A : Class) :
    (nb090AlphaDummy633 A) ∈
      (((synCcompl (Class.cv (nb090AlphaDummy632 A)))).fv ∪
        ((synCcompl (Class.cv (nb090AlphaDummy633 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0669 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy636 v u h) ∈
      (((synCcompl (Class.cv (nb090AlphaDummy635 v u h)))).fv ∪
        ((synCcompl (Class.cv (nb090AlphaDummy636 v u h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0670 (A : Class) :
    (nb090AlphaDummy633 A) ∈
      (((Class.cv (nb090AlphaDummy633 A))).fv ∪ ((Class.cv (nb090AlphaDummy633 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0671 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy636 v u h) ∈
      (((Class.cv (nb090AlphaDummy636 v u h))).fv ∪
        ((Class.cv (nb090AlphaDummy636 v u h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0672 (A : Class) :
    (nb090AlphaDummy042 A) ∈
      (((Class.cv (nb090AlphaDummy041 A))).fv ∪ ((Class.cv (nb090AlphaDummy042 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0673 (A : Class) :
    (nb090AlphaDummy042 A) ∈
      (((synCcompl (Class.cab (nb090AlphaDummy617 A)
              (synWrex (nb090AlphaDummy618 A) (Class.cv (nb090AlphaDummy041 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy617 A))
                  (synCphi (Class.cv (nb090AlphaDummy618 A)))))))).fv ∪ ((synCcompl
            (Class.cab (nb090AlphaDummy617 A)
              (synWrex (nb090AlphaDummy618 A) (Class.cv (nb090AlphaDummy042 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy617 A))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy618 A)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090AlphaDummy042 A) ≠ (nb090AlphaDummy617 A) from (by
          unfold nb090AlphaDummy617;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0672 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090AlphaDummy042 A) ≠ (nb090AlphaDummy618 A) from (by
            unfold nb090AlphaDummy618;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0672 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0674 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy044 v u h) ∈
      (((Class.cv (nb090AlphaDummy043 v u h))).fv ∪
        ((Class.cv (nb090AlphaDummy044 v u h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0675 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy044 v u h) ∈
      (((synCcompl (Class.cab (nb090AlphaDummy619 v u h)
              (synWrex (nb090AlphaDummy620 v u h) (Class.cv (nb090AlphaDummy043 v u h))
                (Wff.classEq (Class.cv (nb090AlphaDummy619 v u h))
                  (synCphi (Class.cv (nb090AlphaDummy620 v u h)))))))).fv ∪ ((synCcompl
            (Class.cab (nb090AlphaDummy619 v u h) (synWrex (nb090AlphaDummy620 v u h)
                (Class.cv (nb090AlphaDummy044 v u h))
                (Wff.classEq (Class.cv (nb090AlphaDummy619 v u h))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy620 v u h)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090AlphaDummy044 v u h) ≠ (nb090AlphaDummy619 v u h) from (by
          unfold nb090AlphaDummy619;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0674 v u h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090AlphaDummy044 v u h) ≠ (nb090AlphaDummy620 v u h) from (by
            unfold nb090AlphaDummy620;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0674 v u h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0676 (A : Class) :
    (nb090AlphaDummy042 A) ∈
      (((Class.cab (nb090AlphaDummy617 A)
            (synWrex (nb090AlphaDummy618 A) (Class.cv (nb090AlphaDummy042 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy617 A))
                (synCun (synCphi (Class.cv (nb090AlphaDummy618 A)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb090AlphaDummy617 A)
            (synWrex (nb090AlphaDummy618 A) (Class.cv (nb090AlphaDummy042 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy617 A))
                (synCun (synCphi (Class.cv (nb090AlphaDummy618 A)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090AlphaDummy042 A) ≠ (nb090AlphaDummy617 A) from (by
          unfold nb090AlphaDummy617;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0672 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090AlphaDummy042 A) ≠ (nb090AlphaDummy618 A) from (by
            unfold nb090AlphaDummy618;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0672 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0677 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy044 v u h) ∈
      (((Class.cab (nb090AlphaDummy619 v u h) (synWrex (nb090AlphaDummy620 v u h)
              (Class.cv (nb090AlphaDummy044 v u h))
              (Wff.classEq (Class.cv (nb090AlphaDummy619 v u h))
                (synCun (synCphi (Class.cv (nb090AlphaDummy620 v u h)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb090AlphaDummy619 v u h)
            (synWrex (nb090AlphaDummy620 v u h) (Class.cv (nb090AlphaDummy044 v u h))
              (Wff.classEq (Class.cv (nb090AlphaDummy619 v u h))
                (synCun (synCphi (Class.cv (nb090AlphaDummy620 v u h)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090AlphaDummy044 v u h) ≠ (nb090AlphaDummy619 v u h) from (by
          unfold nb090AlphaDummy619;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0674 v u h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090AlphaDummy044 v u h) ≠ (nb090AlphaDummy620 v u h) from (by
            unfold nb090AlphaDummy620;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0674 v u h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0678 (A : Class) :
    (nb090AlphaDummy618 A) ∈
      (((synCcompl (synCphi (Class.cv (nb090AlphaDummy618 A))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0679 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy620 v u h) ∈
      (((synCcompl (synCphi (Class.cv (nb090AlphaDummy620 v u h))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0680 (A : Class) :
    (nb090AlphaDummy618 A) ∈
      (((synCphi (Class.cv (nb090AlphaDummy618 A)))).fv ∪
        ((synCphi (Class.cv (nb090AlphaDummy618 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0681 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy620 v u h) ∈
      (((synCphi (Class.cv (nb090AlphaDummy620 v u h)))).fv ∪
        ((synCphi (Class.cv (nb090AlphaDummy620 v u h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0682 (A : Class) :
    (nb090AlphaDummy001 A) ∈
      (((synC1st)).fv ∪ ((Class.cv (nb090AlphaDummy001 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0683 (A : Class) :
    (nb090AlphaDummy001 A) ∈
      (({(nb090AlphaDummy653 A)} : Finset Var) ∪
        ((synWbr (Class.cv (nb090AlphaDummy001 A)) (synC1st)
            (Class.cv (nb090AlphaDummy653 A)))).fv) :=
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
    (nb090AlphaDummy001 A) ∈
      (((Class.cab (nb090AlphaDummy655 A) (Wff.classEq (Class.cab (nb090AlphaDummy653 A)
              (synWbr (Class.cv (nb090AlphaDummy001 A)) (synC1st)
                (Class.cv (nb090AlphaDummy653 A))))
            (synCsn (Class.cv (nb090AlphaDummy655 A)))))).fv) :=
  by
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090AlphaDummy001 A) ≠ (nb090AlphaDummy655 A) from (by
          unfold nb090AlphaDummy655;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0683 A) 0))))
  · rw [fv_wff_classEq]
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cab]
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090AlphaDummy001 A) ≠ (nb090AlphaDummy653 A) from (by
            unfold nb090AlphaDummy653;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0682 A) 0))))
    · rw [fv_syn_wbr]
      with_reducible rw [Finset.mem_union]
      left
      with_reducible rw [Finset.mem_union]
      left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0685 (u : Var) : u ∈ (((synC1st)).fv ∪ ((Class.cv u)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0686 (u : Var) :
    u ∈
      (({(nb090AlphaDummy654 u)} : Finset Var) ∪
        ((synWbr (Class.cv u) (synC1st) (Class.cv (nb090AlphaDummy654 u)))).fv) :=
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
      (((Class.cab (nb090AlphaDummy656 u) (Wff.classEq (Class.cab (nb090AlphaDummy654 u)
              (synWbr (Class.cv u) (synC1st) (Class.cv (nb090AlphaDummy654 u))))
            (synCsn (Class.cv (nb090AlphaDummy656 u)))))).fv) :=
  by
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show u ≠ (nb090AlphaDummy656 u) from (by
          unfold nb090AlphaDummy656;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0686 u) 0))))
  · rw [fv_wff_classEq]
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cab]
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show u ≠ (nb090AlphaDummy654 u) from (by
            unfold nb090AlphaDummy654;
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
    (nb090AlphaDummy001 A) ∈
      (((Class.cv (nb090AlphaDummy001 A))).fv ∪ ((Class.cv (nb090AlphaDummy653 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0689 (A : Class) :
    (nb090AlphaDummy001 A) ∈
      (((synCcompl (Class.cab (nb090AlphaDummy661 A)
              (synWrex (nb090AlphaDummy662 A) (Class.cv (nb090AlphaDummy001 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy661 A))
                  (synCphi (Class.cv (nb090AlphaDummy662 A)))))))).fv ∪ ((synCcompl
            (Class.cab (nb090AlphaDummy661 A)
              (synWrex (nb090AlphaDummy662 A) (Class.cv (nb090AlphaDummy653 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy661 A))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy662 A)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090AlphaDummy001 A) ≠ (nb090AlphaDummy661 A) from (by
          unfold nb090AlphaDummy661;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0688 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090AlphaDummy001 A) ≠ (nb090AlphaDummy662 A) from (by
            unfold nb090AlphaDummy662;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0688 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0690 (u : Var) :
    u ∈ (((Class.cv u)).fv ∪ ((Class.cv (nb090AlphaDummy654 u))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0691 (u : Var) :
    u ∈
      (((synCcompl (Class.cab (nb090AlphaDummy663 u)
              (synWrex (nb090AlphaDummy664 u) (Class.cv u)
                (Wff.classEq (Class.cv (nb090AlphaDummy663 u))
                  (synCphi (Class.cv (nb090AlphaDummy664 u)))))))).fv ∪ ((synCcompl
            (Class.cab (nb090AlphaDummy663 u)
              (synWrex (nb090AlphaDummy664 u) (Class.cv (nb090AlphaDummy654 u))
                (Wff.classEq (Class.cv (nb090AlphaDummy663 u))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy664 u)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show u ≠ (nb090AlphaDummy663 u) from (by
          unfold nb090AlphaDummy663;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0690 u) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show u ≠ (nb090AlphaDummy664 u) from (by
            unfold nb090AlphaDummy664;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0690 u) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0692 (A : Class) :
    (nb090AlphaDummy001 A) ∈
      (((Class.cab (nb090AlphaDummy661 A)
            (synWrex (nb090AlphaDummy662 A) (Class.cv (nb090AlphaDummy001 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy661 A))
                (synCphi (Class.cv (nb090AlphaDummy662 A))))))).fv ∪
        ((Class.cab (nb090AlphaDummy661 A)
            (synWrex (nb090AlphaDummy662 A) (Class.cv (nb090AlphaDummy001 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy661 A))
                (synCphi (Class.cv (nb090AlphaDummy662 A))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090AlphaDummy001 A) ≠ (nb090AlphaDummy661 A) from (by
          unfold nb090AlphaDummy661;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0688 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090AlphaDummy001 A) ≠ (nb090AlphaDummy662 A) from (by
            unfold nb090AlphaDummy662;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0688 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0693 (u : Var) :
    u ∈
      (((Class.cab (nb090AlphaDummy663 u) (synWrex (nb090AlphaDummy664 u) (Class.cv u)
              (Wff.classEq (Class.cv (nb090AlphaDummy663 u))
                (synCphi (Class.cv (nb090AlphaDummy664 u))))))).fv ∪
        ((Class.cab (nb090AlphaDummy663 u) (synWrex (nb090AlphaDummy664 u) (Class.cv u)
              (Wff.classEq (Class.cv (nb090AlphaDummy663 u))
                (synCphi (Class.cv (nb090AlphaDummy664 u))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show u ≠ (nb090AlphaDummy663 u) from (by
          unfold nb090AlphaDummy663;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0690 u) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show u ≠ (nb090AlphaDummy664 u) from (by
            unfold nb090AlphaDummy664;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0690 u) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0694 (A : Class) :
    (nb090AlphaDummy662 A) ∈ (((Class.cv (nb090AlphaDummy662 A))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0695 (u : Var) :
    (nb090AlphaDummy664 u) ∈ (((Class.cv (nb090AlphaDummy664 u))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0696 (A : Class) :
    (nb090AlphaDummy669 A) ∈
      (((Wff.classMem (Class.cv (nb090AlphaDummy669 A)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb090AlphaDummy669 A)) (synC1c))).fv ∪
        ((Class.cv (nb090AlphaDummy669 A))).fv) :=
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
    (nb090AlphaDummy671 u) ∈
      (((Wff.classMem (Class.cv (nb090AlphaDummy671 u)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb090AlphaDummy671 u)) (synC1c))).fv ∪
        ((Class.cv (nb090AlphaDummy671 u))).fv) :=
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
    (nb090AlphaDummy669 A) ∈
      (((Class.cv (nb090AlphaDummy669 A))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0699 (u : Var) :
    (nb090AlphaDummy671 u) ∈
      (((Class.cv (nb090AlphaDummy671 u))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0700 (A : Class) :
    (nb090AlphaDummy676 A) ∈
      (((synCnin (Class.cv (nb090AlphaDummy676 A))
            (Class.cv (nb090AlphaDummy677 A)))).fv ∪
        ((synCnin (Class.cv (nb090AlphaDummy676 A))
            (Class.cv (nb090AlphaDummy677 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0701 (u : Var) :
    (nb090AlphaDummy679 u) ∈
      (((synCnin (Class.cv (nb090AlphaDummy679 u))
            (Class.cv (nb090AlphaDummy680 u)))).fv ∪
        ((synCnin (Class.cv (nb090AlphaDummy679 u))
            (Class.cv (nb090AlphaDummy680 u)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0702 (A : Class) :
    (nb090AlphaDummy676 A) ∈
      (((Class.cv (nb090AlphaDummy676 A))).fv ∪ ((Class.cv (nb090AlphaDummy677 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0703 (u : Var) :
    (nb090AlphaDummy679 u) ∈
      (((Class.cv (nb090AlphaDummy679 u))).fv ∪ ((Class.cv (nb090AlphaDummy680 u))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0704 (A : Class) :
    (nb090AlphaDummy677 A) ∈
      (((synCnin (Class.cv (nb090AlphaDummy676 A))
            (Class.cv (nb090AlphaDummy677 A)))).fv ∪
        ((synCnin (Class.cv (nb090AlphaDummy676 A))
            (Class.cv (nb090AlphaDummy677 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0705 (u : Var) :
    (nb090AlphaDummy680 u) ∈
      (((synCnin (Class.cv (nb090AlphaDummy679 u))
            (Class.cv (nb090AlphaDummy680 u)))).fv ∪
        ((synCnin (Class.cv (nb090AlphaDummy679 u))
            (Class.cv (nb090AlphaDummy680 u)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0706 (A : Class) :
    (nb090AlphaDummy677 A) ∈
      (((Class.cv (nb090AlphaDummy676 A))).fv ∪ ((Class.cv (nb090AlphaDummy677 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0707 (u : Var) :
    (nb090AlphaDummy680 u) ∈
      (((Class.cv (nb090AlphaDummy679 u))).fv ∪ ((Class.cv (nb090AlphaDummy680 u))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0708 (A : Class) :
    (nb090AlphaDummy676 A) ∈
      (((synCcompl (Class.cv (nb090AlphaDummy676 A)))).fv ∪
        ((synCcompl (Class.cv (nb090AlphaDummy677 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0709 (u : Var) :
    (nb090AlphaDummy679 u) ∈
      (((synCcompl (Class.cv (nb090AlphaDummy679 u)))).fv ∪
        ((synCcompl (Class.cv (nb090AlphaDummy680 u)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0710 (A : Class) :
    (nb090AlphaDummy676 A) ∈
      (((Class.cv (nb090AlphaDummy676 A))).fv ∪ ((Class.cv (nb090AlphaDummy676 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0711 (u : Var) :
    (nb090AlphaDummy679 u) ∈
      (((Class.cv (nb090AlphaDummy679 u))).fv ∪ ((Class.cv (nb090AlphaDummy679 u))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0712 (A : Class) :
    (nb090AlphaDummy677 A) ∈
      (((synCcompl (Class.cv (nb090AlphaDummy676 A)))).fv ∪
        ((synCcompl (Class.cv (nb090AlphaDummy677 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0713 (u : Var) :
    (nb090AlphaDummy680 u) ∈
      (((synCcompl (Class.cv (nb090AlphaDummy679 u)))).fv ∪
        ((synCcompl (Class.cv (nb090AlphaDummy680 u)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0714 (A : Class) :
    (nb090AlphaDummy677 A) ∈
      (((Class.cv (nb090AlphaDummy677 A))).fv ∪ ((Class.cv (nb090AlphaDummy677 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0715 (u : Var) :
    (nb090AlphaDummy680 u) ∈
      (((Class.cv (nb090AlphaDummy680 u))).fv ∪ ((Class.cv (nb090AlphaDummy680 u))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0716 (A : Class) :
    (nb090AlphaDummy653 A) ∈
      (((Class.cv (nb090AlphaDummy001 A))).fv ∪ ((Class.cv (nb090AlphaDummy653 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0717 (A : Class) :
    (nb090AlphaDummy653 A) ∈
      (((synCcompl (Class.cab (nb090AlphaDummy661 A)
              (synWrex (nb090AlphaDummy662 A) (Class.cv (nb090AlphaDummy001 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy661 A))
                  (synCphi (Class.cv (nb090AlphaDummy662 A)))))))).fv ∪ ((synCcompl
            (Class.cab (nb090AlphaDummy661 A)
              (synWrex (nb090AlphaDummy662 A) (Class.cv (nb090AlphaDummy653 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy661 A))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy662 A)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090AlphaDummy653 A) ≠ (nb090AlphaDummy661 A) from (by
          unfold nb090AlphaDummy661;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0716 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090AlphaDummy653 A) ≠ (nb090AlphaDummy662 A) from (by
            unfold nb090AlphaDummy662;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0716 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0718 (u : Var) :
    (nb090AlphaDummy654 u) ∈
      (((Class.cv u)).fv ∪ ((Class.cv (nb090AlphaDummy654 u))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0719 (u : Var) :
    (nb090AlphaDummy654 u) ∈
      (((synCcompl (Class.cab (nb090AlphaDummy663 u)
              (synWrex (nb090AlphaDummy664 u) (Class.cv u)
                (Wff.classEq (Class.cv (nb090AlphaDummy663 u))
                  (synCphi (Class.cv (nb090AlphaDummy664 u)))))))).fv ∪ ((synCcompl
            (Class.cab (nb090AlphaDummy663 u)
              (synWrex (nb090AlphaDummy664 u) (Class.cv (nb090AlphaDummy654 u))
                (Wff.classEq (Class.cv (nb090AlphaDummy663 u))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy664 u)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090AlphaDummy654 u) ≠ (nb090AlphaDummy663 u) from (by
          unfold nb090AlphaDummy663;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0718 u) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090AlphaDummy654 u) ≠ (nb090AlphaDummy664 u) from (by
            unfold nb090AlphaDummy664;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0718 u) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0720 (A : Class) :
    (nb090AlphaDummy653 A) ∈
      (((Class.cab (nb090AlphaDummy661 A)
            (synWrex (nb090AlphaDummy662 A) (Class.cv (nb090AlphaDummy653 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy661 A))
                (synCun (synCphi (Class.cv (nb090AlphaDummy662 A)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb090AlphaDummy661 A)
            (synWrex (nb090AlphaDummy662 A) (Class.cv (nb090AlphaDummy653 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy661 A))
                (synCun (synCphi (Class.cv (nb090AlphaDummy662 A)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090AlphaDummy653 A) ≠ (nb090AlphaDummy661 A) from (by
          unfold nb090AlphaDummy661;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0716 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090AlphaDummy653 A) ≠ (nb090AlphaDummy662 A) from (by
            unfold nb090AlphaDummy662;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0716 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0721 (u : Var) :
    (nb090AlphaDummy654 u) ∈
      (((Class.cab (nb090AlphaDummy663 u)
            (synWrex (nb090AlphaDummy664 u) (Class.cv (nb090AlphaDummy654 u))
              (Wff.classEq (Class.cv (nb090AlphaDummy663 u))
                (synCun (synCphi (Class.cv (nb090AlphaDummy664 u)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb090AlphaDummy663 u)
            (synWrex (nb090AlphaDummy664 u) (Class.cv (nb090AlphaDummy654 u))
              (Wff.classEq (Class.cv (nb090AlphaDummy663 u))
                (synCun (synCphi (Class.cv (nb090AlphaDummy664 u)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090AlphaDummy654 u) ≠ (nb090AlphaDummy663 u) from (by
          unfold nb090AlphaDummy663;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0718 u) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090AlphaDummy654 u) ≠ (nb090AlphaDummy664 u) from (by
            unfold nb090AlphaDummy664;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0718 u) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0722 (A : Class) :
    (nb090AlphaDummy662 A) ∈
      (((synCcompl (synCphi (Class.cv (nb090AlphaDummy662 A))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0723 (u : Var) :
    (nb090AlphaDummy664 u) ∈
      (((synCcompl (synCphi (Class.cv (nb090AlphaDummy664 u))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0724 (A : Class) :
    (nb090AlphaDummy662 A) ∈
      (((synCphi (Class.cv (nb090AlphaDummy662 A)))).fv ∪
        ((synCphi (Class.cv (nb090AlphaDummy662 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0725 (u : Var) :
    (nb090AlphaDummy664 u) ∈
      (((synCphi (Class.cv (nb090AlphaDummy664 u)))).fv ∪
        ((synCphi (Class.cv (nb090AlphaDummy664 u)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0726 (A : Class) :
    (nb090AlphaDummy655 A) ∈ (((Class.cv (nb090AlphaDummy655 A))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0727 (u : Var) :
    (nb090AlphaDummy656 u) ∈ (((Class.cv (nb090AlphaDummy656 u))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0728 (A : Class) :
    (nb090AlphaDummy041 A) ∈
      (((synCfv (Class.cv (nb090AlphaDummy000 A))
            (Class.cv (nb090AlphaDummy041 A)))).fv ∪
        ((synCfv (Class.cv (nb090AlphaDummy000 A))
            (Class.cv (nb090AlphaDummy042 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cfv]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0729 (A : Class) :
    (nb090AlphaDummy041 A) ∈
      (((synCcompl (Class.cab (nb090AlphaDummy699 A) (synWrex (nb090AlphaDummy700 A)
                (synCfv (Class.cv (nb090AlphaDummy000 A))
                  (Class.cv (nb090AlphaDummy041 A)))
                (Wff.classEq (Class.cv (nb090AlphaDummy699 A))
                  (synCphi (Class.cv (nb090AlphaDummy700 A)))))))).fv ∪ ((synCcompl
            (Class.cab (nb090AlphaDummy699 A) (synWrex (nb090AlphaDummy700 A)
                (synCfv (Class.cv (nb090AlphaDummy000 A))
                  (Class.cv (nb090AlphaDummy042 A)))
                (Wff.classEq (Class.cv (nb090AlphaDummy699 A))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy700 A)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090AlphaDummy041 A) ≠ (nb090AlphaDummy699 A) from (by
          unfold nb090AlphaDummy699;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0728 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090AlphaDummy041 A) ≠ (nb090AlphaDummy700 A) from (by
            unfold nb090AlphaDummy700;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0728 A) 1))))
    · rw [fv_syn_cfv]
      with_reducible rw [Finset.mem_union]
      left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0730 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy043 v u h) ∈
      (((synCfv (Class.cv h) (Class.cv (nb090AlphaDummy043 v u h)))).fv ∪
        ((synCfv (Class.cv h) (Class.cv (nb090AlphaDummy044 v u h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cfv]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0731 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy043 v u h) ∈
      (((synCcompl (Class.cab (nb090AlphaDummy701 v u h)
              (synWrex (nb090AlphaDummy702 v u h)
                (synCfv (Class.cv h) (Class.cv (nb090AlphaDummy043 v u h)))
                (Wff.classEq (Class.cv (nb090AlphaDummy701 v u h))
                  (synCphi (Class.cv (nb090AlphaDummy702 v u h)))))))).fv ∪ ((synCcompl
            (Class.cab (nb090AlphaDummy701 v u h) (synWrex (nb090AlphaDummy702 v u h)
                (synCfv (Class.cv h) (Class.cv (nb090AlphaDummy044 v u h)))
                (Wff.classEq (Class.cv (nb090AlphaDummy701 v u h))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy702 v u h)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090AlphaDummy043 v u h) ≠ (nb090AlphaDummy701 v u h) from (by
          unfold nb090AlphaDummy701;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0730 v u h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090AlphaDummy043 v u h) ≠ (nb090AlphaDummy702 v u h) from (by
            unfold nb090AlphaDummy702;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0730 v u h) 1))))
    · rw [fv_syn_cfv]
      with_reducible rw [Finset.mem_union]
      left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0732 (A : Class) :
    (nb090AlphaDummy041 A) ∈
      (((Class.cab (nb090AlphaDummy699 A) (synWrex (nb090AlphaDummy700 A)
              (synCfv (Class.cv (nb090AlphaDummy000 A))
                (Class.cv (nb090AlphaDummy041 A)))
              (Wff.classEq (Class.cv (nb090AlphaDummy699 A))
                (synCphi (Class.cv (nb090AlphaDummy700 A))))))).fv ∪
        ((Class.cab (nb090AlphaDummy699 A) (synWrex (nb090AlphaDummy700 A)
              (synCfv (Class.cv (nb090AlphaDummy000 A))
                (Class.cv (nb090AlphaDummy041 A)))
              (Wff.classEq (Class.cv (nb090AlphaDummy699 A))
                (synCphi (Class.cv (nb090AlphaDummy700 A))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090AlphaDummy041 A) ≠ (nb090AlphaDummy699 A) from (by
          unfold nb090AlphaDummy699;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0728 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090AlphaDummy041 A) ≠ (nb090AlphaDummy700 A) from (by
            unfold nb090AlphaDummy700;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0728 A) 1))))
    · rw [fv_syn_cfv]
      with_reducible rw [Finset.mem_union]
      left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0733 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy043 v u h) ∈
      (((Class.cab (nb090AlphaDummy701 v u h) (synWrex (nb090AlphaDummy702 v u h)
              (synCfv (Class.cv h) (Class.cv (nb090AlphaDummy043 v u h)))
              (Wff.classEq (Class.cv (nb090AlphaDummy701 v u h))
                (synCphi (Class.cv (nb090AlphaDummy702 v u h))))))).fv ∪
        ((Class.cab (nb090AlphaDummy701 v u h) (synWrex (nb090AlphaDummy702 v u h)
              (synCfv (Class.cv h) (Class.cv (nb090AlphaDummy043 v u h)))
              (Wff.classEq (Class.cv (nb090AlphaDummy701 v u h))
                (synCphi (Class.cv (nb090AlphaDummy702 v u h))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090AlphaDummy043 v u h) ≠ (nb090AlphaDummy701 v u h) from (by
          unfold nb090AlphaDummy701;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0730 v u h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090AlphaDummy043 v u h) ≠ (nb090AlphaDummy702 v u h) from (by
            unfold nb090AlphaDummy702;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0730 v u h) 1))))
    · rw [fv_syn_cfv]
      with_reducible rw [Finset.mem_union]
      left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0734 (A : Class) :
    (nb090AlphaDummy041 A) ∈
      (((Class.cv (nb090AlphaDummy000 A))).fv ∪ ((Class.cv (nb090AlphaDummy041 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0735 (A : Class) :
    (nb090AlphaDummy041 A) ∈
      (({(nb090AlphaDummy707 A)} : Finset Var) ∪
        ((synWbr (Class.cv (nb090AlphaDummy041 A)) (Class.cv (nb090AlphaDummy000 A))
            (Class.cv (nb090AlphaDummy707 A)))).fv) :=
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
    (nb090AlphaDummy041 A) ∈
      (((Class.cab (nb090AlphaDummy709 A) (Wff.classEq (Class.cab (nb090AlphaDummy707 A)
              (synWbr (Class.cv (nb090AlphaDummy041 A)) (Class.cv (nb090AlphaDummy000 A))
                (Class.cv (nb090AlphaDummy707 A))))
            (synCsn (Class.cv (nb090AlphaDummy709 A)))))).fv) :=
  by
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090AlphaDummy041 A) ≠ (nb090AlphaDummy709 A) from (by
          unfold nb090AlphaDummy709;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0735 A) 0))))
  · rw [fv_wff_classEq]
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cab]
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090AlphaDummy041 A) ≠ (nb090AlphaDummy707 A) from (by
            unfold nb090AlphaDummy707;
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
    (nb090AlphaDummy043 v u h) ∈
      (((Class.cv h)).fv ∪ ((Class.cv (nb090AlphaDummy043 v u h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0738 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy043 v u h) ∈
      (({(nb090AlphaDummy708 v u h)} : Finset Var) ∪
        ((synWbr (Class.cv (nb090AlphaDummy043 v u h)) (Class.cv h)
            (Class.cv (nb090AlphaDummy708 v u h)))).fv) :=
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
    (nb090AlphaDummy043 v u h) ∈
      (((Class.cab (nb090AlphaDummy710 v u h) (Wff.classEq
            (Class.cab (nb090AlphaDummy708 v u h)
              (synWbr (Class.cv (nb090AlphaDummy043 v u h)) (Class.cv h)
                (Class.cv (nb090AlphaDummy708 v u h))))
            (synCsn (Class.cv (nb090AlphaDummy710 v u h)))))).fv) :=
  by
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090AlphaDummy043 v u h) ≠ (nb090AlphaDummy710 v u h) from (by
          unfold nb090AlphaDummy710;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0738 v u h) 0))))
  · rw [fv_wff_classEq]
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cab]
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090AlphaDummy043 v u h) ≠ (nb090AlphaDummy708 v u h) from (by
            unfold nb090AlphaDummy708;
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
    (nb090AlphaDummy041 A) ∈
      (((Class.cv (nb090AlphaDummy041 A))).fv ∪ ((Class.cv (nb090AlphaDummy707 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0741 (A : Class) :
    (nb090AlphaDummy041 A) ∈
      (((synCcompl (Class.cab (nb090AlphaDummy715 A)
              (synWrex (nb090AlphaDummy716 A) (Class.cv (nb090AlphaDummy041 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy715 A))
                  (synCphi (Class.cv (nb090AlphaDummy716 A)))))))).fv ∪ ((synCcompl
            (Class.cab (nb090AlphaDummy715 A)
              (synWrex (nb090AlphaDummy716 A) (Class.cv (nb090AlphaDummy707 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy715 A))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy716 A)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090AlphaDummy041 A) ≠ (nb090AlphaDummy715 A) from (by
          unfold nb090AlphaDummy715;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0740 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090AlphaDummy041 A) ≠ (nb090AlphaDummy716 A) from (by
            unfold nb090AlphaDummy716;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0740 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0742 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy043 v u h) ∈
      (((Class.cv (nb090AlphaDummy043 v u h))).fv ∪
        ((Class.cv (nb090AlphaDummy708 v u h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0743 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy043 v u h) ∈
      (((synCcompl (Class.cab (nb090AlphaDummy717 v u h)
              (synWrex (nb090AlphaDummy718 v u h) (Class.cv (nb090AlphaDummy043 v u h))
                (Wff.classEq (Class.cv (nb090AlphaDummy717 v u h))
                  (synCphi (Class.cv (nb090AlphaDummy718 v u h)))))))).fv ∪ ((synCcompl
            (Class.cab (nb090AlphaDummy717 v u h) (synWrex (nb090AlphaDummy718 v u h)
                (Class.cv (nb090AlphaDummy708 v u h))
                (Wff.classEq (Class.cv (nb090AlphaDummy717 v u h))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy718 v u h)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090AlphaDummy043 v u h) ≠ (nb090AlphaDummy717 v u h) from (by
          unfold nb090AlphaDummy717;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0742 v u h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090AlphaDummy043 v u h) ≠ (nb090AlphaDummy718 v u h) from (by
            unfold nb090AlphaDummy718;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0742 v u h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0744 (A : Class) :
    (nb090AlphaDummy041 A) ∈
      (((Class.cab (nb090AlphaDummy715 A)
            (synWrex (nb090AlphaDummy716 A) (Class.cv (nb090AlphaDummy041 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy715 A))
                (synCphi (Class.cv (nb090AlphaDummy716 A))))))).fv ∪
        ((Class.cab (nb090AlphaDummy715 A)
            (synWrex (nb090AlphaDummy716 A) (Class.cv (nb090AlphaDummy041 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy715 A))
                (synCphi (Class.cv (nb090AlphaDummy716 A))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090AlphaDummy041 A) ≠ (nb090AlphaDummy715 A) from (by
          unfold nb090AlphaDummy715;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0740 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090AlphaDummy041 A) ≠ (nb090AlphaDummy716 A) from (by
            unfold nb090AlphaDummy716;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0740 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0745 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy043 v u h) ∈
      (((Class.cab (nb090AlphaDummy717 v u h) (synWrex (nb090AlphaDummy718 v u h)
              (Class.cv (nb090AlphaDummy043 v u h))
              (Wff.classEq (Class.cv (nb090AlphaDummy717 v u h))
                (synCphi (Class.cv (nb090AlphaDummy718 v u h))))))).fv ∪
        ((Class.cab (nb090AlphaDummy717 v u h) (synWrex (nb090AlphaDummy718 v u h)
              (Class.cv (nb090AlphaDummy043 v u h))
              (Wff.classEq (Class.cv (nb090AlphaDummy717 v u h))
                (synCphi (Class.cv (nb090AlphaDummy718 v u h))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090AlphaDummy043 v u h) ≠ (nb090AlphaDummy717 v u h) from (by
          unfold nb090AlphaDummy717;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0742 v u h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090AlphaDummy043 v u h) ≠ (nb090AlphaDummy718 v u h) from (by
            unfold nb090AlphaDummy718;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0742 v u h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0746 (A : Class) :
    (nb090AlphaDummy716 A) ∈ (((Class.cv (nb090AlphaDummy716 A))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0747 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy718 v u h) ∈ (((Class.cv (nb090AlphaDummy718 v u h))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0748 (A : Class) :
    (nb090AlphaDummy723 A) ∈
      (((Wff.classMem (Class.cv (nb090AlphaDummy723 A)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb090AlphaDummy723 A)) (synC1c))).fv ∪
        ((Class.cv (nb090AlphaDummy723 A))).fv) :=
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
    (nb090AlphaDummy725 v u h) ∈
      (((Wff.classMem (Class.cv (nb090AlphaDummy725 v u h)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb090AlphaDummy725 v u h)) (synC1c))).fv ∪
        ((Class.cv (nb090AlphaDummy725 v u h))).fv) :=
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
    (nb090AlphaDummy723 A) ∈
      (((Class.cv (nb090AlphaDummy723 A))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0751 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy725 v u h) ∈
      (((Class.cv (nb090AlphaDummy725 v u h))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0752 (A : Class) :
    (nb090AlphaDummy730 A) ∈
      (((synCnin (Class.cv (nb090AlphaDummy730 A))
            (Class.cv (nb090AlphaDummy731 A)))).fv ∪
        ((synCnin (Class.cv (nb090AlphaDummy730 A))
            (Class.cv (nb090AlphaDummy731 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0753 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy733 v u h) ∈
      (((synCnin (Class.cv (nb090AlphaDummy733 v u h))
            (Class.cv (nb090AlphaDummy734 v u h)))).fv ∪
        ((synCnin (Class.cv (nb090AlphaDummy733 v u h))
            (Class.cv (nb090AlphaDummy734 v u h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0754 (A : Class) :
    (nb090AlphaDummy730 A) ∈
      (((Class.cv (nb090AlphaDummy730 A))).fv ∪ ((Class.cv (nb090AlphaDummy731 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0755 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy733 v u h) ∈
      (((Class.cv (nb090AlphaDummy733 v u h))).fv ∪
        ((Class.cv (nb090AlphaDummy734 v u h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0756 (A : Class) :
    (nb090AlphaDummy731 A) ∈
      (((synCnin (Class.cv (nb090AlphaDummy730 A))
            (Class.cv (nb090AlphaDummy731 A)))).fv ∪
        ((synCnin (Class.cv (nb090AlphaDummy730 A))
            (Class.cv (nb090AlphaDummy731 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0757 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy734 v u h) ∈
      (((synCnin (Class.cv (nb090AlphaDummy733 v u h))
            (Class.cv (nb090AlphaDummy734 v u h)))).fv ∪
        ((synCnin (Class.cv (nb090AlphaDummy733 v u h))
            (Class.cv (nb090AlphaDummy734 v u h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0758 (A : Class) :
    (nb090AlphaDummy731 A) ∈
      (((Class.cv (nb090AlphaDummy730 A))).fv ∪ ((Class.cv (nb090AlphaDummy731 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0759 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy734 v u h) ∈
      (((Class.cv (nb090AlphaDummy733 v u h))).fv ∪
        ((Class.cv (nb090AlphaDummy734 v u h))).fv) :=
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
    (nb090AlphaDummy730 A) ∈
      (((synCcompl (Class.cv (nb090AlphaDummy730 A)))).fv ∪
        ((synCcompl (Class.cv (nb090AlphaDummy731 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0761 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy733 v u h) ∈
      (((synCcompl (Class.cv (nb090AlphaDummy733 v u h)))).fv ∪
        ((synCcompl (Class.cv (nb090AlphaDummy734 v u h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0762 (A : Class) :
    (nb090AlphaDummy730 A) ∈
      (((Class.cv (nb090AlphaDummy730 A))).fv ∪ ((Class.cv (nb090AlphaDummy730 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0763 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy733 v u h) ∈
      (((Class.cv (nb090AlphaDummy733 v u h))).fv ∪
        ((Class.cv (nb090AlphaDummy733 v u h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0764 (A : Class) :
    (nb090AlphaDummy731 A) ∈
      (((synCcompl (Class.cv (nb090AlphaDummy730 A)))).fv ∪
        ((synCcompl (Class.cv (nb090AlphaDummy731 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0765 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy734 v u h) ∈
      (((synCcompl (Class.cv (nb090AlphaDummy733 v u h)))).fv ∪
        ((synCcompl (Class.cv (nb090AlphaDummy734 v u h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0766 (A : Class) :
    (nb090AlphaDummy731 A) ∈
      (((Class.cv (nb090AlphaDummy731 A))).fv ∪ ((Class.cv (nb090AlphaDummy731 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0767 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy734 v u h) ∈
      (((Class.cv (nb090AlphaDummy734 v u h))).fv ∪
        ((Class.cv (nb090AlphaDummy734 v u h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0768 (A : Class) :
    (nb090AlphaDummy707 A) ∈
      (((Class.cv (nb090AlphaDummy041 A))).fv ∪ ((Class.cv (nb090AlphaDummy707 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0769 (A : Class) :
    (nb090AlphaDummy707 A) ∈
      (((synCcompl (Class.cab (nb090AlphaDummy715 A)
              (synWrex (nb090AlphaDummy716 A) (Class.cv (nb090AlphaDummy041 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy715 A))
                  (synCphi (Class.cv (nb090AlphaDummy716 A)))))))).fv ∪ ((synCcompl
            (Class.cab (nb090AlphaDummy715 A)
              (synWrex (nb090AlphaDummy716 A) (Class.cv (nb090AlphaDummy707 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy715 A))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy716 A)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090AlphaDummy707 A) ≠ (nb090AlphaDummy715 A) from (by
          unfold nb090AlphaDummy715;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0768 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090AlphaDummy707 A) ≠ (nb090AlphaDummy716 A) from (by
            unfold nb090AlphaDummy716;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0768 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0770 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy708 v u h) ∈
      (((Class.cv (nb090AlphaDummy043 v u h))).fv ∪
        ((Class.cv (nb090AlphaDummy708 v u h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0771 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy708 v u h) ∈
      (((synCcompl (Class.cab (nb090AlphaDummy717 v u h)
              (synWrex (nb090AlphaDummy718 v u h) (Class.cv (nb090AlphaDummy043 v u h))
                (Wff.classEq (Class.cv (nb090AlphaDummy717 v u h))
                  (synCphi (Class.cv (nb090AlphaDummy718 v u h)))))))).fv ∪ ((synCcompl
            (Class.cab (nb090AlphaDummy717 v u h) (synWrex (nb090AlphaDummy718 v u h)
                (Class.cv (nb090AlphaDummy708 v u h))
                (Wff.classEq (Class.cv (nb090AlphaDummy717 v u h))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy718 v u h)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090AlphaDummy708 v u h) ≠ (nb090AlphaDummy717 v u h) from (by
          unfold nb090AlphaDummy717;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0770 v u h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090AlphaDummy708 v u h) ≠ (nb090AlphaDummy718 v u h) from (by
            unfold nb090AlphaDummy718;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0770 v u h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0772 (A : Class) :
    (nb090AlphaDummy707 A) ∈
      (((Class.cab (nb090AlphaDummy715 A)
            (synWrex (nb090AlphaDummy716 A) (Class.cv (nb090AlphaDummy707 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy715 A))
                (synCun (synCphi (Class.cv (nb090AlphaDummy716 A)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb090AlphaDummy715 A)
            (synWrex (nb090AlphaDummy716 A) (Class.cv (nb090AlphaDummy707 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy715 A))
                (synCun (synCphi (Class.cv (nb090AlphaDummy716 A)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090AlphaDummy707 A) ≠ (nb090AlphaDummy715 A) from (by
          unfold nb090AlphaDummy715;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0768 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090AlphaDummy707 A) ≠ (nb090AlphaDummy716 A) from (by
            unfold nb090AlphaDummy716;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0768 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0773 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy708 v u h) ∈
      (((Class.cab (nb090AlphaDummy717 v u h) (synWrex (nb090AlphaDummy718 v u h)
              (Class.cv (nb090AlphaDummy708 v u h))
              (Wff.classEq (Class.cv (nb090AlphaDummy717 v u h))
                (synCun (synCphi (Class.cv (nb090AlphaDummy718 v u h)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb090AlphaDummy717 v u h)
            (synWrex (nb090AlphaDummy718 v u h) (Class.cv (nb090AlphaDummy708 v u h))
              (Wff.classEq (Class.cv (nb090AlphaDummy717 v u h))
                (synCun (synCphi (Class.cv (nb090AlphaDummy718 v u h)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090AlphaDummy708 v u h) ≠ (nb090AlphaDummy717 v u h) from (by
          unfold nb090AlphaDummy717;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0770 v u h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090AlphaDummy708 v u h) ≠ (nb090AlphaDummy718 v u h) from (by
            unfold nb090AlphaDummy718;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0770 v u h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0774 (A : Class) :
    (nb090AlphaDummy716 A) ∈
      (((synCcompl (synCphi (Class.cv (nb090AlphaDummy716 A))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0775 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy718 v u h) ∈
      (((synCcompl (synCphi (Class.cv (nb090AlphaDummy718 v u h))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0776 (A : Class) :
    (nb090AlphaDummy716 A) ∈
      (((synCphi (Class.cv (nb090AlphaDummy716 A)))).fv ∪
        ((synCphi (Class.cv (nb090AlphaDummy716 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0777 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy718 v u h) ∈
      (((synCphi (Class.cv (nb090AlphaDummy718 v u h)))).fv ∪
        ((synCphi (Class.cv (nb090AlphaDummy718 v u h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0778 (A : Class) :
    (nb090AlphaDummy000 A) ∈
      (((Class.cv (nb090AlphaDummy000 A))).fv ∪
              ((synCfv (synC1st) (Class.cv (nb090AlphaDummy001 A)))).fv ∪
            ((synCfv (synC1st) (Class.cv (nb090AlphaDummy002 A)))).fv ∪
          ((synCfv (synC2nd) (Class.cv (nb090AlphaDummy001 A)))).fv ∪
        ((synCfv (synC2nd) (Class.cv (nb090AlphaDummy002 A)))).fv) :=
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
      (((Class.cv h)).fv ∪ ((synCfv (synC1st) (Class.cv u))).fv ∪
            ((synCfv (synC1st) (Class.cv v))).fv ∪ ((synCfv (synC2nd) (Class.cv u))).fv ∪
        ((synCfv (synC2nd) (Class.cv v))).fv) :=
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
    (nb090AlphaDummy000 A) ∈
      (((synCfv (Class.cv (nb090AlphaDummy000 A))
            (Class.cv (nb090AlphaDummy041 A)))).fv ∪
        ((synCfv (Class.cv (nb090AlphaDummy000 A))
            (Class.cv (nb090AlphaDummy042 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cfv]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0781 (A : Class) :
    (nb090AlphaDummy000 A) ∈
      (((synCcompl (Class.cab (nb090AlphaDummy699 A) (synWrex (nb090AlphaDummy700 A)
                (synCfv (Class.cv (nb090AlphaDummy000 A))
                  (Class.cv (nb090AlphaDummy041 A)))
                (Wff.classEq (Class.cv (nb090AlphaDummy699 A))
                  (synCphi (Class.cv (nb090AlphaDummy700 A)))))))).fv ∪ ((synCcompl
            (Class.cab (nb090AlphaDummy699 A) (synWrex (nb090AlphaDummy700 A)
                (synCfv (Class.cv (nb090AlphaDummy000 A))
                  (Class.cv (nb090AlphaDummy042 A)))
                (Wff.classEq (Class.cv (nb090AlphaDummy699 A))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy700 A)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090AlphaDummy000 A) ≠ (nb090AlphaDummy699 A) from (by
          unfold nb090AlphaDummy699;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0780 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090AlphaDummy000 A) ≠ (nb090AlphaDummy700 A) from (by
            unfold nb090AlphaDummy700;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0780 A) 1))))
    · rw [fv_syn_cfv]
      with_reducible rw [Finset.mem_union]
      right
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0782 (v : Var) (u : Var) (h : Var) :
    h ∈
      (((synCfv (Class.cv h) (Class.cv (nb090AlphaDummy043 v u h)))).fv ∪
        ((synCfv (Class.cv h) (Class.cv (nb090AlphaDummy044 v u h)))).fv) :=
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
      (((synCcompl (Class.cab (nb090AlphaDummy701 v u h)
              (synWrex (nb090AlphaDummy702 v u h)
                (synCfv (Class.cv h) (Class.cv (nb090AlphaDummy043 v u h)))
                (Wff.classEq (Class.cv (nb090AlphaDummy701 v u h))
                  (synCphi (Class.cv (nb090AlphaDummy702 v u h)))))))).fv ∪ ((synCcompl
            (Class.cab (nb090AlphaDummy701 v u h) (synWrex (nb090AlphaDummy702 v u h)
                (synCfv (Class.cv h) (Class.cv (nb090AlphaDummy044 v u h)))
                (Wff.classEq (Class.cv (nb090AlphaDummy701 v u h))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy702 v u h)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show h ≠ (nb090AlphaDummy701 v u h) from (by
          unfold nb090AlphaDummy701;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0782 v u h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show h ≠ (nb090AlphaDummy702 v u h) from (by
            unfold nb090AlphaDummy702;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0782 v u h) 1))))
    · rw [fv_syn_cfv]
      with_reducible rw [Finset.mem_union]
      right
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0784 (A : Class) :
    (nb090AlphaDummy000 A) ∈
      (((Class.cab (nb090AlphaDummy699 A) (synWrex (nb090AlphaDummy700 A)
              (synCfv (Class.cv (nb090AlphaDummy000 A))
                (Class.cv (nb090AlphaDummy041 A)))
              (Wff.classEq (Class.cv (nb090AlphaDummy699 A))
                (synCphi (Class.cv (nb090AlphaDummy700 A))))))).fv ∪
        ((Class.cab (nb090AlphaDummy699 A) (synWrex (nb090AlphaDummy700 A)
              (synCfv (Class.cv (nb090AlphaDummy000 A))
                (Class.cv (nb090AlphaDummy041 A)))
              (Wff.classEq (Class.cv (nb090AlphaDummy699 A))
                (synCphi (Class.cv (nb090AlphaDummy700 A))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090AlphaDummy000 A) ≠ (nb090AlphaDummy699 A) from (by
          unfold nb090AlphaDummy699;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0780 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090AlphaDummy000 A) ≠ (nb090AlphaDummy700 A) from (by
            unfold nb090AlphaDummy700;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0780 A) 1))))
    · rw [fv_syn_cfv]
      with_reducible rw [Finset.mem_union]
      right
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0785 (v : Var) (u : Var) (h : Var) :
    h ∈
      (((Class.cab (nb090AlphaDummy701 v u h) (synWrex (nb090AlphaDummy702 v u h)
              (synCfv (Class.cv h) (Class.cv (nb090AlphaDummy043 v u h)))
              (Wff.classEq (Class.cv (nb090AlphaDummy701 v u h))
                (synCphi (Class.cv (nb090AlphaDummy702 v u h))))))).fv ∪
        ((Class.cab (nb090AlphaDummy701 v u h) (synWrex (nb090AlphaDummy702 v u h)
              (synCfv (Class.cv h) (Class.cv (nb090AlphaDummy043 v u h)))
              (Wff.classEq (Class.cv (nb090AlphaDummy701 v u h))
                (synCphi (Class.cv (nb090AlphaDummy702 v u h))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show h ≠ (nb090AlphaDummy701 v u h) from (by
          unfold nb090AlphaDummy701;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0782 v u h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show h ≠ (nb090AlphaDummy702 v u h) from (by
            unfold nb090AlphaDummy702;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0782 v u h) 1))))
    · rw [fv_syn_cfv]
      with_reducible rw [Finset.mem_union]
      right
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0786 (A : Class) :
    (nb090AlphaDummy000 A) ∈
      (((Class.cv (nb090AlphaDummy000 A))).fv ∪ ((Class.cv (nb090AlphaDummy041 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0787 (A : Class) :
    (nb090AlphaDummy000 A) ∈
      (({(nb090AlphaDummy707 A)} : Finset Var) ∪
        ((synWbr (Class.cv (nb090AlphaDummy041 A)) (Class.cv (nb090AlphaDummy000 A))
            (Class.cv (nb090AlphaDummy707 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_wbr]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0788 (A : Class) :
    (nb090AlphaDummy000 A) ∈
      (((Class.cab (nb090AlphaDummy709 A) (Wff.classEq (Class.cab (nb090AlphaDummy707 A)
              (synWbr (Class.cv (nb090AlphaDummy041 A)) (Class.cv (nb090AlphaDummy000 A))
                (Class.cv (nb090AlphaDummy707 A))))
            (synCsn (Class.cv (nb090AlphaDummy709 A)))))).fv) :=
  by
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090AlphaDummy000 A) ≠ (nb090AlphaDummy709 A) from (by
          unfold nb090AlphaDummy709;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0787 A) 0))))
  · rw [fv_wff_classEq]
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cab]
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090AlphaDummy000 A) ≠ (nb090AlphaDummy707 A) from (by
            unfold nb090AlphaDummy707;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0786 A) 0))))
    · rw [fv_syn_wbr]
      with_reducible rw [Finset.mem_union]
      right
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0789 (v : Var) (u : Var) (h : Var) :
    h ∈ (((Class.cv h)).fv ∪ ((Class.cv (nb090AlphaDummy043 v u h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0790 (v : Var) (u : Var) (h : Var) :
    h ∈
      (({(nb090AlphaDummy708 v u h)} : Finset Var) ∪
        ((synWbr (Class.cv (nb090AlphaDummy043 v u h)) (Class.cv h)
            (Class.cv (nb090AlphaDummy708 v u h)))).fv) :=
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
      (((Class.cab (nb090AlphaDummy710 v u h) (Wff.classEq
            (Class.cab (nb090AlphaDummy708 v u h)
              (synWbr (Class.cv (nb090AlphaDummy043 v u h)) (Class.cv h)
                (Class.cv (nb090AlphaDummy708 v u h))))
            (synCsn (Class.cv (nb090AlphaDummy710 v u h)))))).fv) :=
  by
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show h ≠ (nb090AlphaDummy710 v u h) from (by
          unfold nb090AlphaDummy710;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0790 v u h) 0))))
  · rw [fv_wff_classEq]
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cab]
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show h ≠ (nb090AlphaDummy708 v u h) from (by
            unfold nb090AlphaDummy708;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0789 v u h) 0))))
    · rw [fv_syn_wbr]
      with_reducible rw [Finset.mem_union]
      right
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0792 (A : Class) :
    (nb090AlphaDummy709 A) ∈ (((Class.cv (nb090AlphaDummy709 A))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0793 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy710 v u h) ∈ (((Class.cv (nb090AlphaDummy710 v u h))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0794 (A : Class) :
    (nb090AlphaDummy700 A) ∈ (((Class.cv (nb090AlphaDummy700 A))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0795 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy702 v u h) ∈ (((Class.cv (nb090AlphaDummy702 v u h))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0796 (A : Class) :
    (nb090AlphaDummy753 A) ∈
      (((Wff.classMem (Class.cv (nb090AlphaDummy753 A)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb090AlphaDummy753 A)) (synC1c))).fv ∪
        ((Class.cv (nb090AlphaDummy753 A))).fv) :=
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
    (nb090AlphaDummy755 v u h) ∈
      (((Wff.classMem (Class.cv (nb090AlphaDummy755 v u h)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb090AlphaDummy755 v u h)) (synC1c))).fv ∪
        ((Class.cv (nb090AlphaDummy755 v u h))).fv) :=
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
    (nb090AlphaDummy753 A) ∈
      (((Class.cv (nb090AlphaDummy753 A))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0799 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy755 v u h) ∈
      (((Class.cv (nb090AlphaDummy755 v u h))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0800 (A : Class) :
    (nb090AlphaDummy760 A) ∈
      (((synCnin (Class.cv (nb090AlphaDummy760 A))
            (Class.cv (nb090AlphaDummy761 A)))).fv ∪
        ((synCnin (Class.cv (nb090AlphaDummy760 A))
            (Class.cv (nb090AlphaDummy761 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0801 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy763 v u h) ∈
      (((synCnin (Class.cv (nb090AlphaDummy763 v u h))
            (Class.cv (nb090AlphaDummy764 v u h)))).fv ∪
        ((synCnin (Class.cv (nb090AlphaDummy763 v u h))
            (Class.cv (nb090AlphaDummy764 v u h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0802 (A : Class) :
    (nb090AlphaDummy760 A) ∈
      (((Class.cv (nb090AlphaDummy760 A))).fv ∪ ((Class.cv (nb090AlphaDummy761 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0803 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy763 v u h) ∈
      (((Class.cv (nb090AlphaDummy763 v u h))).fv ∪
        ((Class.cv (nb090AlphaDummy764 v u h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0804 (A : Class) :
    (nb090AlphaDummy761 A) ∈
      (((synCnin (Class.cv (nb090AlphaDummy760 A))
            (Class.cv (nb090AlphaDummy761 A)))).fv ∪
        ((synCnin (Class.cv (nb090AlphaDummy760 A))
            (Class.cv (nb090AlphaDummy761 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0805 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy764 v u h) ∈
      (((synCnin (Class.cv (nb090AlphaDummy763 v u h))
            (Class.cv (nb090AlphaDummy764 v u h)))).fv ∪
        ((synCnin (Class.cv (nb090AlphaDummy763 v u h))
            (Class.cv (nb090AlphaDummy764 v u h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0806 (A : Class) :
    (nb090AlphaDummy761 A) ∈
      (((Class.cv (nb090AlphaDummy760 A))).fv ∪ ((Class.cv (nb090AlphaDummy761 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0807 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy764 v u h) ∈
      (((Class.cv (nb090AlphaDummy763 v u h))).fv ∪
        ((Class.cv (nb090AlphaDummy764 v u h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0808 (A : Class) :
    (nb090AlphaDummy760 A) ∈
      (((synCcompl (Class.cv (nb090AlphaDummy760 A)))).fv ∪
        ((synCcompl (Class.cv (nb090AlphaDummy761 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0809 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy763 v u h) ∈
      (((synCcompl (Class.cv (nb090AlphaDummy763 v u h)))).fv ∪
        ((synCcompl (Class.cv (nb090AlphaDummy764 v u h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0810 (A : Class) :
    (nb090AlphaDummy760 A) ∈
      (((Class.cv (nb090AlphaDummy760 A))).fv ∪ ((Class.cv (nb090AlphaDummy760 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0811 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy763 v u h) ∈
      (((Class.cv (nb090AlphaDummy763 v u h))).fv ∪
        ((Class.cv (nb090AlphaDummy763 v u h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0812 (A : Class) :
    (nb090AlphaDummy761 A) ∈
      (((synCcompl (Class.cv (nb090AlphaDummy760 A)))).fv ∪
        ((synCcompl (Class.cv (nb090AlphaDummy761 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0813 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy764 v u h) ∈
      (((synCcompl (Class.cv (nb090AlphaDummy763 v u h)))).fv ∪
        ((synCcompl (Class.cv (nb090AlphaDummy764 v u h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0814 (A : Class) :
    (nb090AlphaDummy761 A) ∈
      (((Class.cv (nb090AlphaDummy761 A))).fv ∪ ((Class.cv (nb090AlphaDummy761 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0815 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy764 v u h) ∈
      (((Class.cv (nb090AlphaDummy764 v u h))).fv ∪
        ((Class.cv (nb090AlphaDummy764 v u h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0816 (A : Class) :
    (nb090AlphaDummy042 A) ∈
      (((synCfv (Class.cv (nb090AlphaDummy000 A))
            (Class.cv (nb090AlphaDummy041 A)))).fv ∪
        ((synCfv (Class.cv (nb090AlphaDummy000 A))
            (Class.cv (nb090AlphaDummy042 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_cfv]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0817 (A : Class) :
    (nb090AlphaDummy042 A) ∈
      (((synCcompl (Class.cab (nb090AlphaDummy699 A) (synWrex (nb090AlphaDummy700 A)
                (synCfv (Class.cv (nb090AlphaDummy000 A))
                  (Class.cv (nb090AlphaDummy041 A)))
                (Wff.classEq (Class.cv (nb090AlphaDummy699 A))
                  (synCphi (Class.cv (nb090AlphaDummy700 A)))))))).fv ∪ ((synCcompl
            (Class.cab (nb090AlphaDummy699 A) (synWrex (nb090AlphaDummy700 A)
                (synCfv (Class.cv (nb090AlphaDummy000 A))
                  (Class.cv (nb090AlphaDummy042 A)))
                (Wff.classEq (Class.cv (nb090AlphaDummy699 A))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy700 A)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090AlphaDummy042 A) ≠ (nb090AlphaDummy699 A) from (by
          unfold nb090AlphaDummy699;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0816 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090AlphaDummy042 A) ≠ (nb090AlphaDummy700 A) from (by
            unfold nb090AlphaDummy700;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0816 A) 1))))
    · rw [fv_syn_cfv]
      with_reducible rw [Finset.mem_union]
      left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0818 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy044 v u h) ∈
      (((synCfv (Class.cv h) (Class.cv (nb090AlphaDummy043 v u h)))).fv ∪
        ((synCfv (Class.cv h) (Class.cv (nb090AlphaDummy044 v u h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_cfv]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0819 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy044 v u h) ∈
      (((synCcompl (Class.cab (nb090AlphaDummy701 v u h)
              (synWrex (nb090AlphaDummy702 v u h)
                (synCfv (Class.cv h) (Class.cv (nb090AlphaDummy043 v u h)))
                (Wff.classEq (Class.cv (nb090AlphaDummy701 v u h))
                  (synCphi (Class.cv (nb090AlphaDummy702 v u h)))))))).fv ∪ ((synCcompl
            (Class.cab (nb090AlphaDummy701 v u h) (synWrex (nb090AlphaDummy702 v u h)
                (synCfv (Class.cv h) (Class.cv (nb090AlphaDummy044 v u h)))
                (Wff.classEq (Class.cv (nb090AlphaDummy701 v u h))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy702 v u h)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090AlphaDummy044 v u h) ≠ (nb090AlphaDummy701 v u h) from (by
          unfold nb090AlphaDummy701;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0818 v u h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090AlphaDummy044 v u h) ≠ (nb090AlphaDummy702 v u h) from (by
            unfold nb090AlphaDummy702;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0818 v u h) 1))))
    · rw [fv_syn_cfv]
      with_reducible rw [Finset.mem_union]
      left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0820 (A : Class) :
    (nb090AlphaDummy042 A) ∈
      (((Class.cab (nb090AlphaDummy699 A) (synWrex (nb090AlphaDummy700 A)
              (synCfv (Class.cv (nb090AlphaDummy000 A))
                (Class.cv (nb090AlphaDummy042 A)))
              (Wff.classEq (Class.cv (nb090AlphaDummy699 A))
                (synCun (synCphi (Class.cv (nb090AlphaDummy700 A)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb090AlphaDummy699 A)
            (synWrex (nb090AlphaDummy700 A) (synCfv (Class.cv (nb090AlphaDummy000 A))
                (Class.cv (nb090AlphaDummy042 A)))
              (Wff.classEq (Class.cv (nb090AlphaDummy699 A))
                (synCun (synCphi (Class.cv (nb090AlphaDummy700 A)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090AlphaDummy042 A) ≠ (nb090AlphaDummy699 A) from (by
          unfold nb090AlphaDummy699;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0816 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090AlphaDummy042 A) ≠ (nb090AlphaDummy700 A) from (by
            unfold nb090AlphaDummy700;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0816 A) 1))))
    · rw [fv_syn_cfv]
      with_reducible rw [Finset.mem_union]
      left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0821 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy044 v u h) ∈
      (((Class.cab (nb090AlphaDummy701 v u h) (synWrex (nb090AlphaDummy702 v u h)
              (synCfv (Class.cv h) (Class.cv (nb090AlphaDummy044 v u h)))
              (Wff.classEq (Class.cv (nb090AlphaDummy701 v u h))
                (synCun (synCphi (Class.cv (nb090AlphaDummy702 v u h)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb090AlphaDummy701 v u h)
            (synWrex (nb090AlphaDummy702 v u h)
              (synCfv (Class.cv h) (Class.cv (nb090AlphaDummy044 v u h)))
              (Wff.classEq (Class.cv (nb090AlphaDummy701 v u h))
                (synCun (synCphi (Class.cv (nb090AlphaDummy702 v u h)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090AlphaDummy044 v u h) ≠ (nb090AlphaDummy701 v u h) from (by
          unfold nb090AlphaDummy701;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0818 v u h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090AlphaDummy044 v u h) ≠ (nb090AlphaDummy702 v u h) from (by
            unfold nb090AlphaDummy702;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0818 v u h) 1))))
    · rw [fv_syn_cfv]
      with_reducible rw [Finset.mem_union]
      left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0822 (A : Class) :
    (nb090AlphaDummy042 A) ∈
      (((Class.cv (nb090AlphaDummy000 A))).fv ∪ ((Class.cv (nb090AlphaDummy042 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0823 (A : Class) :
    (nb090AlphaDummy042 A) ∈
      (({(nb090AlphaDummy777 A)} : Finset Var) ∪
        ((synWbr (Class.cv (nb090AlphaDummy042 A)) (Class.cv (nb090AlphaDummy000 A))
            (Class.cv (nb090AlphaDummy777 A)))).fv) :=
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
    (nb090AlphaDummy042 A) ∈
      (((Class.cab (nb090AlphaDummy779 A) (Wff.classEq (Class.cab (nb090AlphaDummy777 A)
              (synWbr (Class.cv (nb090AlphaDummy042 A)) (Class.cv (nb090AlphaDummy000 A))
                (Class.cv (nb090AlphaDummy777 A))))
            (synCsn (Class.cv (nb090AlphaDummy779 A)))))).fv) :=
  by
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090AlphaDummy042 A) ≠ (nb090AlphaDummy779 A) from (by
          unfold nb090AlphaDummy779;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0823 A) 0))))
  · rw [fv_wff_classEq]
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cab]
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090AlphaDummy042 A) ≠ (nb090AlphaDummy777 A) from (by
            unfold nb090AlphaDummy777;
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
    (nb090AlphaDummy044 v u h) ∈
      (((Class.cv h)).fv ∪ ((Class.cv (nb090AlphaDummy044 v u h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0826 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy044 v u h) ∈
      (({(nb090AlphaDummy778 v u h)} : Finset Var) ∪
        ((synWbr (Class.cv (nb090AlphaDummy044 v u h)) (Class.cv h)
            (Class.cv (nb090AlphaDummy778 v u h)))).fv) :=
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
    (nb090AlphaDummy044 v u h) ∈
      (((Class.cab (nb090AlphaDummy780 v u h) (Wff.classEq
            (Class.cab (nb090AlphaDummy778 v u h)
              (synWbr (Class.cv (nb090AlphaDummy044 v u h)) (Class.cv h)
                (Class.cv (nb090AlphaDummy778 v u h))))
            (synCsn (Class.cv (nb090AlphaDummy780 v u h)))))).fv) :=
  by
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090AlphaDummy044 v u h) ≠ (nb090AlphaDummy780 v u h) from (by
          unfold nb090AlphaDummy780;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0826 v u h) 0))))
  · rw [fv_wff_classEq]
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cab]
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090AlphaDummy044 v u h) ≠ (nb090AlphaDummy778 v u h) from (by
            unfold nb090AlphaDummy778;
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
    (nb090AlphaDummy042 A) ∈
      (((Class.cv (nb090AlphaDummy042 A))).fv ∪ ((Class.cv (nb090AlphaDummy777 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0829 (A : Class) :
    (nb090AlphaDummy042 A) ∈
      (((synCcompl (Class.cab (nb090AlphaDummy785 A)
              (synWrex (nb090AlphaDummy786 A) (Class.cv (nb090AlphaDummy042 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy785 A))
                  (synCphi (Class.cv (nb090AlphaDummy786 A)))))))).fv ∪ ((synCcompl
            (Class.cab (nb090AlphaDummy785 A)
              (synWrex (nb090AlphaDummy786 A) (Class.cv (nb090AlphaDummy777 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy785 A))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy786 A)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090AlphaDummy042 A) ≠ (nb090AlphaDummy785 A) from (by
          unfold nb090AlphaDummy785;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0828 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090AlphaDummy042 A) ≠ (nb090AlphaDummy786 A) from (by
            unfold nb090AlphaDummy786;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0828 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0830 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy044 v u h) ∈
      (((Class.cv (nb090AlphaDummy044 v u h))).fv ∪
        ((Class.cv (nb090AlphaDummy778 v u h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0831 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy044 v u h) ∈
      (((synCcompl (Class.cab (nb090AlphaDummy787 v u h)
              (synWrex (nb090AlphaDummy788 v u h) (Class.cv (nb090AlphaDummy044 v u h))
                (Wff.classEq (Class.cv (nb090AlphaDummy787 v u h))
                  (synCphi (Class.cv (nb090AlphaDummy788 v u h)))))))).fv ∪ ((synCcompl
            (Class.cab (nb090AlphaDummy787 v u h) (synWrex (nb090AlphaDummy788 v u h)
                (Class.cv (nb090AlphaDummy778 v u h))
                (Wff.classEq (Class.cv (nb090AlphaDummy787 v u h))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy788 v u h)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090AlphaDummy044 v u h) ≠ (nb090AlphaDummy787 v u h) from (by
          unfold nb090AlphaDummy787;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0830 v u h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090AlphaDummy044 v u h) ≠ (nb090AlphaDummy788 v u h) from (by
            unfold nb090AlphaDummy788;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0830 v u h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0832 (A : Class) :
    (nb090AlphaDummy042 A) ∈
      (((Class.cab (nb090AlphaDummy785 A)
            (synWrex (nb090AlphaDummy786 A) (Class.cv (nb090AlphaDummy042 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy785 A))
                (synCphi (Class.cv (nb090AlphaDummy786 A))))))).fv ∪
        ((Class.cab (nb090AlphaDummy785 A)
            (synWrex (nb090AlphaDummy786 A) (Class.cv (nb090AlphaDummy042 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy785 A))
                (synCphi (Class.cv (nb090AlphaDummy786 A))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090AlphaDummy042 A) ≠ (nb090AlphaDummy785 A) from (by
          unfold nb090AlphaDummy785;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0828 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090AlphaDummy042 A) ≠ (nb090AlphaDummy786 A) from (by
            unfold nb090AlphaDummy786;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0828 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0833 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy044 v u h) ∈
      (((Class.cab (nb090AlphaDummy787 v u h) (synWrex (nb090AlphaDummy788 v u h)
              (Class.cv (nb090AlphaDummy044 v u h))
              (Wff.classEq (Class.cv (nb090AlphaDummy787 v u h))
                (synCphi (Class.cv (nb090AlphaDummy788 v u h))))))).fv ∪
        ((Class.cab (nb090AlphaDummy787 v u h) (synWrex (nb090AlphaDummy788 v u h)
              (Class.cv (nb090AlphaDummy044 v u h))
              (Wff.classEq (Class.cv (nb090AlphaDummy787 v u h))
                (synCphi (Class.cv (nb090AlphaDummy788 v u h))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090AlphaDummy044 v u h) ≠ (nb090AlphaDummy787 v u h) from (by
          unfold nb090AlphaDummy787;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0830 v u h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090AlphaDummy044 v u h) ≠ (nb090AlphaDummy788 v u h) from (by
            unfold nb090AlphaDummy788;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0830 v u h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0834 (A : Class) :
    (nb090AlphaDummy786 A) ∈ (((Class.cv (nb090AlphaDummy786 A))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0835 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy788 v u h) ∈ (((Class.cv (nb090AlphaDummy788 v u h))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0836 (A : Class) :
    (nb090AlphaDummy793 A) ∈
      (((Wff.classMem (Class.cv (nb090AlphaDummy793 A)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb090AlphaDummy793 A)) (synC1c))).fv ∪
        ((Class.cv (nb090AlphaDummy793 A))).fv) :=
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
    (nb090AlphaDummy795 v u h) ∈
      (((Wff.classMem (Class.cv (nb090AlphaDummy795 v u h)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb090AlphaDummy795 v u h)) (synC1c))).fv ∪
        ((Class.cv (nb090AlphaDummy795 v u h))).fv) :=
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
    (nb090AlphaDummy793 A) ∈
      (((Class.cv (nb090AlphaDummy793 A))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0839 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy795 v u h) ∈
      (((Class.cv (nb090AlphaDummy795 v u h))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0840 (A : Class) :
    (nb090AlphaDummy800 A) ∈
      (((synCnin (Class.cv (nb090AlphaDummy800 A))
            (Class.cv (nb090AlphaDummy801 A)))).fv ∪
        ((synCnin (Class.cv (nb090AlphaDummy800 A))
            (Class.cv (nb090AlphaDummy801 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0841 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy803 v u h) ∈
      (((synCnin (Class.cv (nb090AlphaDummy803 v u h))
            (Class.cv (nb090AlphaDummy804 v u h)))).fv ∪
        ((synCnin (Class.cv (nb090AlphaDummy803 v u h))
            (Class.cv (nb090AlphaDummy804 v u h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0842 (A : Class) :
    (nb090AlphaDummy800 A) ∈
      (((Class.cv (nb090AlphaDummy800 A))).fv ∪ ((Class.cv (nb090AlphaDummy801 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0843 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy803 v u h) ∈
      (((Class.cv (nb090AlphaDummy803 v u h))).fv ∪
        ((Class.cv (nb090AlphaDummy804 v u h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0844 (A : Class) :
    (nb090AlphaDummy801 A) ∈
      (((synCnin (Class.cv (nb090AlphaDummy800 A))
            (Class.cv (nb090AlphaDummy801 A)))).fv ∪
        ((synCnin (Class.cv (nb090AlphaDummy800 A))
            (Class.cv (nb090AlphaDummy801 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0845 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy804 v u h) ∈
      (((synCnin (Class.cv (nb090AlphaDummy803 v u h))
            (Class.cv (nb090AlphaDummy804 v u h)))).fv ∪
        ((synCnin (Class.cv (nb090AlphaDummy803 v u h))
            (Class.cv (nb090AlphaDummy804 v u h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0846 (A : Class) :
    (nb090AlphaDummy801 A) ∈
      (((Class.cv (nb090AlphaDummy800 A))).fv ∪ ((Class.cv (nb090AlphaDummy801 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0847 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy804 v u h) ∈
      (((Class.cv (nb090AlphaDummy803 v u h))).fv ∪
        ((Class.cv (nb090AlphaDummy804 v u h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0848 (A : Class) :
    (nb090AlphaDummy800 A) ∈
      (((synCcompl (Class.cv (nb090AlphaDummy800 A)))).fv ∪
        ((synCcompl (Class.cv (nb090AlphaDummy801 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0849 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy803 v u h) ∈
      (((synCcompl (Class.cv (nb090AlphaDummy803 v u h)))).fv ∪
        ((synCcompl (Class.cv (nb090AlphaDummy804 v u h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0850 (A : Class) :
    (nb090AlphaDummy800 A) ∈
      (((Class.cv (nb090AlphaDummy800 A))).fv ∪ ((Class.cv (nb090AlphaDummy800 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0851 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy803 v u h) ∈
      (((Class.cv (nb090AlphaDummy803 v u h))).fv ∪
        ((Class.cv (nb090AlphaDummy803 v u h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0852 (A : Class) :
    (nb090AlphaDummy801 A) ∈
      (((synCcompl (Class.cv (nb090AlphaDummy800 A)))).fv ∪
        ((synCcompl (Class.cv (nb090AlphaDummy801 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0853 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy804 v u h) ∈
      (((synCcompl (Class.cv (nb090AlphaDummy803 v u h)))).fv ∪
        ((synCcompl (Class.cv (nb090AlphaDummy804 v u h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0854 (A : Class) :
    (nb090AlphaDummy801 A) ∈
      (((Class.cv (nb090AlphaDummy801 A))).fv ∪ ((Class.cv (nb090AlphaDummy801 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0855 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy804 v u h) ∈
      (((Class.cv (nb090AlphaDummy804 v u h))).fv ∪
        ((Class.cv (nb090AlphaDummy804 v u h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0856 (A : Class) :
    (nb090AlphaDummy777 A) ∈
      (((Class.cv (nb090AlphaDummy042 A))).fv ∪ ((Class.cv (nb090AlphaDummy777 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0857 (A : Class) :
    (nb090AlphaDummy777 A) ∈
      (((synCcompl (Class.cab (nb090AlphaDummy785 A)
              (synWrex (nb090AlphaDummy786 A) (Class.cv (nb090AlphaDummy042 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy785 A))
                  (synCphi (Class.cv (nb090AlphaDummy786 A)))))))).fv ∪ ((synCcompl
            (Class.cab (nb090AlphaDummy785 A)
              (synWrex (nb090AlphaDummy786 A) (Class.cv (nb090AlphaDummy777 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy785 A))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy786 A)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090AlphaDummy777 A) ≠ (nb090AlphaDummy785 A) from (by
          unfold nb090AlphaDummy785;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0856 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090AlphaDummy777 A) ≠ (nb090AlphaDummy786 A) from (by
            unfold nb090AlphaDummy786;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0856 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0858 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy778 v u h) ∈
      (((Class.cv (nb090AlphaDummy044 v u h))).fv ∪
        ((Class.cv (nb090AlphaDummy778 v u h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0859 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy778 v u h) ∈
      (((synCcompl (Class.cab (nb090AlphaDummy787 v u h)
              (synWrex (nb090AlphaDummy788 v u h) (Class.cv (nb090AlphaDummy044 v u h))
                (Wff.classEq (Class.cv (nb090AlphaDummy787 v u h))
                  (synCphi (Class.cv (nb090AlphaDummy788 v u h)))))))).fv ∪ ((synCcompl
            (Class.cab (nb090AlphaDummy787 v u h) (synWrex (nb090AlphaDummy788 v u h)
                (Class.cv (nb090AlphaDummy778 v u h))
                (Wff.classEq (Class.cv (nb090AlphaDummy787 v u h))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy788 v u h)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090AlphaDummy778 v u h) ≠ (nb090AlphaDummy787 v u h) from (by
          unfold nb090AlphaDummy787;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0858 v u h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090AlphaDummy778 v u h) ≠ (nb090AlphaDummy788 v u h) from (by
            unfold nb090AlphaDummy788;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0858 v u h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0860 (A : Class) :
    (nb090AlphaDummy777 A) ∈
      (((Class.cab (nb090AlphaDummy785 A)
            (synWrex (nb090AlphaDummy786 A) (Class.cv (nb090AlphaDummy777 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy785 A))
                (synCun (synCphi (Class.cv (nb090AlphaDummy786 A)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb090AlphaDummy785 A)
            (synWrex (nb090AlphaDummy786 A) (Class.cv (nb090AlphaDummy777 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy785 A))
                (synCun (synCphi (Class.cv (nb090AlphaDummy786 A)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090AlphaDummy777 A) ≠ (nb090AlphaDummy785 A) from (by
          unfold nb090AlphaDummy785;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0856 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090AlphaDummy777 A) ≠ (nb090AlphaDummy786 A) from (by
            unfold nb090AlphaDummy786;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0856 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0861 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy778 v u h) ∈
      (((Class.cab (nb090AlphaDummy787 v u h) (synWrex (nb090AlphaDummy788 v u h)
              (Class.cv (nb090AlphaDummy778 v u h))
              (Wff.classEq (Class.cv (nb090AlphaDummy787 v u h))
                (synCun (synCphi (Class.cv (nb090AlphaDummy788 v u h)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb090AlphaDummy787 v u h)
            (synWrex (nb090AlphaDummy788 v u h) (Class.cv (nb090AlphaDummy778 v u h))
              (Wff.classEq (Class.cv (nb090AlphaDummy787 v u h))
                (synCun (synCphi (Class.cv (nb090AlphaDummy788 v u h)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090AlphaDummy778 v u h) ≠ (nb090AlphaDummy787 v u h) from (by
          unfold nb090AlphaDummy787;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0858 v u h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090AlphaDummy778 v u h) ≠ (nb090AlphaDummy788 v u h) from (by
            unfold nb090AlphaDummy788;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0858 v u h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0862 (A : Class) :
    (nb090AlphaDummy786 A) ∈
      (((synCcompl (synCphi (Class.cv (nb090AlphaDummy786 A))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0863 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy788 v u h) ∈
      (((synCcompl (synCphi (Class.cv (nb090AlphaDummy788 v u h))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0864 (A : Class) :
    (nb090AlphaDummy786 A) ∈
      (((synCphi (Class.cv (nb090AlphaDummy786 A)))).fv ∪
        ((synCphi (Class.cv (nb090AlphaDummy786 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0865 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy788 v u h) ∈
      (((synCphi (Class.cv (nb090AlphaDummy788 v u h)))).fv ∪
        ((synCphi (Class.cv (nb090AlphaDummy788 v u h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0866 (A : Class) :
    (nb090AlphaDummy000 A) ∈
      (((Class.cab (nb090AlphaDummy699 A) (synWrex (nb090AlphaDummy700 A)
              (synCfv (Class.cv (nb090AlphaDummy000 A))
                (Class.cv (nb090AlphaDummy042 A)))
              (Wff.classEq (Class.cv (nb090AlphaDummy699 A))
                (synCun (synCphi (Class.cv (nb090AlphaDummy700 A)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb090AlphaDummy699 A)
            (synWrex (nb090AlphaDummy700 A) (synCfv (Class.cv (nb090AlphaDummy000 A))
                (Class.cv (nb090AlphaDummy042 A)))
              (Wff.classEq (Class.cv (nb090AlphaDummy699 A))
                (synCun (synCphi (Class.cv (nb090AlphaDummy700 A)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090AlphaDummy000 A) ≠ (nb090AlphaDummy699 A) from (by
          unfold nb090AlphaDummy699;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0780 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090AlphaDummy000 A) ≠ (nb090AlphaDummy700 A) from (by
            unfold nb090AlphaDummy700;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0780 A) 1))))
    · rw [fv_syn_cfv]
      with_reducible rw [Finset.mem_union]
      right
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0867 (v : Var) (u : Var) (h : Var) :
    h ∈
      (((Class.cab (nb090AlphaDummy701 v u h) (synWrex (nb090AlphaDummy702 v u h)
              (synCfv (Class.cv h) (Class.cv (nb090AlphaDummy044 v u h)))
              (Wff.classEq (Class.cv (nb090AlphaDummy701 v u h))
                (synCun (synCphi (Class.cv (nb090AlphaDummy702 v u h)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb090AlphaDummy701 v u h)
            (synWrex (nb090AlphaDummy702 v u h)
              (synCfv (Class.cv h) (Class.cv (nb090AlphaDummy044 v u h)))
              (Wff.classEq (Class.cv (nb090AlphaDummy701 v u h))
                (synCun (synCphi (Class.cv (nb090AlphaDummy702 v u h)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show h ≠ (nb090AlphaDummy701 v u h) from (by
          unfold nb090AlphaDummy701;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0782 v u h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show h ≠ (nb090AlphaDummy702 v u h) from (by
            unfold nb090AlphaDummy702;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0782 v u h) 1))))
    · rw [fv_syn_cfv]
      with_reducible rw [Finset.mem_union]
      right
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0868 (A : Class) :
    (nb090AlphaDummy000 A) ∈
      (((Class.cv (nb090AlphaDummy000 A))).fv ∪ ((Class.cv (nb090AlphaDummy042 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0869 (A : Class) :
    (nb090AlphaDummy000 A) ∈
      (({(nb090AlphaDummy777 A)} : Finset Var) ∪
        ((synWbr (Class.cv (nb090AlphaDummy042 A)) (Class.cv (nb090AlphaDummy000 A))
            (Class.cv (nb090AlphaDummy777 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_wbr]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0870 (A : Class) :
    (nb090AlphaDummy000 A) ∈
      (((Class.cab (nb090AlphaDummy779 A) (Wff.classEq (Class.cab (nb090AlphaDummy777 A)
              (synWbr (Class.cv (nb090AlphaDummy042 A)) (Class.cv (nb090AlphaDummy000 A))
                (Class.cv (nb090AlphaDummy777 A))))
            (synCsn (Class.cv (nb090AlphaDummy779 A)))))).fv) :=
  by
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090AlphaDummy000 A) ≠ (nb090AlphaDummy779 A) from (by
          unfold nb090AlphaDummy779;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0869 A) 0))))
  · rw [fv_wff_classEq]
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cab]
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090AlphaDummy000 A) ≠ (nb090AlphaDummy777 A) from (by
            unfold nb090AlphaDummy777;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0868 A) 0))))
    · rw [fv_syn_wbr]
      with_reducible rw [Finset.mem_union]
      right
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0871 (v : Var) (u : Var) (h : Var) :
    h ∈ (((Class.cv h)).fv ∪ ((Class.cv (nb090AlphaDummy044 v u h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0872 (v : Var) (u : Var) (h : Var) :
    h ∈
      (({(nb090AlphaDummy778 v u h)} : Finset Var) ∪
        ((synWbr (Class.cv (nb090AlphaDummy044 v u h)) (Class.cv h)
            (Class.cv (nb090AlphaDummy778 v u h)))).fv) :=
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
      (((Class.cab (nb090AlphaDummy780 v u h) (Wff.classEq
            (Class.cab (nb090AlphaDummy778 v u h)
              (synWbr (Class.cv (nb090AlphaDummy044 v u h)) (Class.cv h)
                (Class.cv (nb090AlphaDummy778 v u h))))
            (synCsn (Class.cv (nb090AlphaDummy780 v u h)))))).fv) :=
  by
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show h ≠ (nb090AlphaDummy780 v u h) from (by
          unfold nb090AlphaDummy780;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0872 v u h) 0))))
  · rw [fv_wff_classEq]
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cab]
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show h ≠ (nb090AlphaDummy778 v u h) from (by
            unfold nb090AlphaDummy778;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0871 v u h) 0))))
    · rw [fv_syn_wbr]
      with_reducible rw [Finset.mem_union]
      right
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0874 (A : Class) :
    (nb090AlphaDummy779 A) ∈ (((Class.cv (nb090AlphaDummy779 A))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0875 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy780 v u h) ∈ (((Class.cv (nb090AlphaDummy780 v u h))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0876 (A : Class) :
    (nb090AlphaDummy700 A) ∈
      (((synCcompl (synCphi (Class.cv (nb090AlphaDummy700 A))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0877 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy702 v u h) ∈
      (((synCcompl (synCphi (Class.cv (nb090AlphaDummy702 v u h))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0878 (A : Class) :
    (nb090AlphaDummy700 A) ∈
      (((synCphi (Class.cv (nb090AlphaDummy700 A)))).fv ∪
        ((synCphi (Class.cv (nb090AlphaDummy700 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0879 (v : Var) (u : Var) (h : Var) :
    (nb090AlphaDummy702 v u h) ∈
      (((synCphi (Class.cv (nb090AlphaDummy702 v u h)))).fv ∪
        ((synCphi (Class.cv (nb090AlphaDummy702 v u h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0880 (A : Class) :
    (nb090AlphaDummy002 A) ∈
      (((Class.cv (nb090AlphaDummy000 A))).fv ∪
              ((synCfv (synC1st) (Class.cv (nb090AlphaDummy001 A)))).fv ∪
            ((synCfv (synC1st) (Class.cv (nb090AlphaDummy002 A)))).fv ∪
          ((synCfv (synC2nd) (Class.cv (nb090AlphaDummy001 A)))).fv ∪
        ((synCfv (synC2nd) (Class.cv (nb090AlphaDummy002 A)))).fv) :=
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
      (((Class.cv h)).fv ∪ ((synCfv (synC1st) (Class.cv u))).fv ∪
            ((synCfv (synC1st) (Class.cv v))).fv ∪ ((synCfv (synC2nd) (Class.cv u))).fv ∪
        ((synCfv (synC2nd) (Class.cv v))).fv) :=
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
    (nb090AlphaDummy002 A) ∈
      (((synC1st)).fv ∪ ((Class.cv (nb090AlphaDummy002 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0883 (A : Class) :
    (nb090AlphaDummy002 A) ∈
      (({(nb090AlphaDummy827 A)} : Finset Var) ∪
        ((synWbr (Class.cv (nb090AlphaDummy002 A)) (synC1st)
            (Class.cv (nb090AlphaDummy827 A)))).fv) :=
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
    (nb090AlphaDummy002 A) ∈
      (((Class.cab (nb090AlphaDummy829 A) (Wff.classEq (Class.cab (nb090AlphaDummy827 A)
              (synWbr (Class.cv (nb090AlphaDummy002 A)) (synC1st)
                (Class.cv (nb090AlphaDummy827 A))))
            (synCsn (Class.cv (nb090AlphaDummy829 A)))))).fv) :=
  by
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090AlphaDummy002 A) ≠ (nb090AlphaDummy829 A) from (by
          unfold nb090AlphaDummy829;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0883 A) 0))))
  · rw [fv_wff_classEq]
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cab]
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090AlphaDummy002 A) ≠ (nb090AlphaDummy827 A) from (by
            unfold nb090AlphaDummy827;
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

theorem nb090_support_mem_0885 (v : Var) : v ∈ (((synC1st)).fv ∪ ((Class.cv v)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0886 (v : Var) :
    v ∈
      (({(nb090AlphaDummy828 v)} : Finset Var) ∪
        ((synWbr (Class.cv v) (synC1st) (Class.cv (nb090AlphaDummy828 v)))).fv) :=
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
      (((Class.cab (nb090AlphaDummy830 v) (Wff.classEq (Class.cab (nb090AlphaDummy828 v)
              (synWbr (Class.cv v) (synC1st) (Class.cv (nb090AlphaDummy828 v))))
            (synCsn (Class.cv (nb090AlphaDummy830 v)))))).fv) :=
  by
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show v ≠ (nb090AlphaDummy830 v) from (by
          unfold nb090AlphaDummy830;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0886 v) 0))))
  · rw [fv_wff_classEq]
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cab]
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show v ≠ (nb090AlphaDummy828 v) from (by
            unfold nb090AlphaDummy828;
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
    (nb090AlphaDummy002 A) ∈
      (((Class.cv (nb090AlphaDummy002 A))).fv ∪ ((Class.cv (nb090AlphaDummy827 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0889 (A : Class) :
    (nb090AlphaDummy002 A) ∈
      (((synCcompl (Class.cab (nb090AlphaDummy835 A)
              (synWrex (nb090AlphaDummy836 A) (Class.cv (nb090AlphaDummy002 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy835 A))
                  (synCphi (Class.cv (nb090AlphaDummy836 A)))))))).fv ∪ ((synCcompl
            (Class.cab (nb090AlphaDummy835 A)
              (synWrex (nb090AlphaDummy836 A) (Class.cv (nb090AlphaDummy827 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy835 A))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy836 A)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090AlphaDummy002 A) ≠ (nb090AlphaDummy835 A) from (by
          unfold nb090AlphaDummy835;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0888 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090AlphaDummy002 A) ≠ (nb090AlphaDummy836 A) from (by
            unfold nb090AlphaDummy836;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0888 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0890 (v : Var) :
    v ∈ (((Class.cv v)).fv ∪ ((Class.cv (nb090AlphaDummy828 v))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0891 (v : Var) :
    v ∈
      (((synCcompl (Class.cab (nb090AlphaDummy837 v)
              (synWrex (nb090AlphaDummy838 v) (Class.cv v)
                (Wff.classEq (Class.cv (nb090AlphaDummy837 v))
                  (synCphi (Class.cv (nb090AlphaDummy838 v)))))))).fv ∪ ((synCcompl
            (Class.cab (nb090AlphaDummy837 v)
              (synWrex (nb090AlphaDummy838 v) (Class.cv (nb090AlphaDummy828 v))
                (Wff.classEq (Class.cv (nb090AlphaDummy837 v))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy838 v)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show v ≠ (nb090AlphaDummy837 v) from (by
          unfold nb090AlphaDummy837;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0890 v) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show v ≠ (nb090AlphaDummy838 v) from (by
            unfold nb090AlphaDummy838;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0890 v) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0892 (A : Class) :
    (nb090AlphaDummy002 A) ∈
      (((Class.cab (nb090AlphaDummy835 A)
            (synWrex (nb090AlphaDummy836 A) (Class.cv (nb090AlphaDummy002 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy835 A))
                (synCphi (Class.cv (nb090AlphaDummy836 A))))))).fv ∪
        ((Class.cab (nb090AlphaDummy835 A)
            (synWrex (nb090AlphaDummy836 A) (Class.cv (nb090AlphaDummy002 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy835 A))
                (synCphi (Class.cv (nb090AlphaDummy836 A))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090AlphaDummy002 A) ≠ (nb090AlphaDummy835 A) from (by
          unfold nb090AlphaDummy835;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0888 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090AlphaDummy002 A) ≠ (nb090AlphaDummy836 A) from (by
            unfold nb090AlphaDummy836;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0888 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0893 (v : Var) :
    v ∈
      (((Class.cab (nb090AlphaDummy837 v) (synWrex (nb090AlphaDummy838 v) (Class.cv v)
              (Wff.classEq (Class.cv (nb090AlphaDummy837 v))
                (synCphi (Class.cv (nb090AlphaDummy838 v))))))).fv ∪
        ((Class.cab (nb090AlphaDummy837 v) (synWrex (nb090AlphaDummy838 v) (Class.cv v)
              (Wff.classEq (Class.cv (nb090AlphaDummy837 v))
                (synCphi (Class.cv (nb090AlphaDummy838 v))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show v ≠ (nb090AlphaDummy837 v) from (by
          unfold nb090AlphaDummy837;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0890 v) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show v ≠ (nb090AlphaDummy838 v) from (by
            unfold nb090AlphaDummy838;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0890 v) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0894 (A : Class) :
    (nb090AlphaDummy836 A) ∈ (((Class.cv (nb090AlphaDummy836 A))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0895 (v : Var) :
    (nb090AlphaDummy838 v) ∈ (((Class.cv (nb090AlphaDummy838 v))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0896 (A : Class) :
    (nb090AlphaDummy843 A) ∈
      (((Wff.classMem (Class.cv (nb090AlphaDummy843 A)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb090AlphaDummy843 A)) (synC1c))).fv ∪
        ((Class.cv (nb090AlphaDummy843 A))).fv) :=
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
    (nb090AlphaDummy845 v) ∈
      (((Wff.classMem (Class.cv (nb090AlphaDummy845 v)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb090AlphaDummy845 v)) (synC1c))).fv ∪
        ((Class.cv (nb090AlphaDummy845 v))).fv) :=
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
    (nb090AlphaDummy843 A) ∈
      (((Class.cv (nb090AlphaDummy843 A))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0899 (v : Var) :
    (nb090AlphaDummy845 v) ∈
      (((Class.cv (nb090AlphaDummy845 v))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0900 (A : Class) :
    (nb090AlphaDummy850 A) ∈
      (((synCnin (Class.cv (nb090AlphaDummy850 A))
            (Class.cv (nb090AlphaDummy851 A)))).fv ∪
        ((synCnin (Class.cv (nb090AlphaDummy850 A))
            (Class.cv (nb090AlphaDummy851 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0901 (v : Var) :
    (nb090AlphaDummy853 v) ∈
      (((synCnin (Class.cv (nb090AlphaDummy853 v))
            (Class.cv (nb090AlphaDummy854 v)))).fv ∪
        ((synCnin (Class.cv (nb090AlphaDummy853 v))
            (Class.cv (nb090AlphaDummy854 v)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0902 (A : Class) :
    (nb090AlphaDummy850 A) ∈
      (((Class.cv (nb090AlphaDummy850 A))).fv ∪ ((Class.cv (nb090AlphaDummy851 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0903 (v : Var) :
    (nb090AlphaDummy853 v) ∈
      (((Class.cv (nb090AlphaDummy853 v))).fv ∪ ((Class.cv (nb090AlphaDummy854 v))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0904 (A : Class) :
    (nb090AlphaDummy851 A) ∈
      (((synCnin (Class.cv (nb090AlphaDummy850 A))
            (Class.cv (nb090AlphaDummy851 A)))).fv ∪
        ((synCnin (Class.cv (nb090AlphaDummy850 A))
            (Class.cv (nb090AlphaDummy851 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0905 (v : Var) :
    (nb090AlphaDummy854 v) ∈
      (((synCnin (Class.cv (nb090AlphaDummy853 v))
            (Class.cv (nb090AlphaDummy854 v)))).fv ∪
        ((synCnin (Class.cv (nb090AlphaDummy853 v))
            (Class.cv (nb090AlphaDummy854 v)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0906 (A : Class) :
    (nb090AlphaDummy851 A) ∈
      (((Class.cv (nb090AlphaDummy850 A))).fv ∪ ((Class.cv (nb090AlphaDummy851 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0907 (v : Var) :
    (nb090AlphaDummy854 v) ∈
      (((Class.cv (nb090AlphaDummy853 v))).fv ∪ ((Class.cv (nb090AlphaDummy854 v))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0908 (A : Class) :
    (nb090AlphaDummy850 A) ∈
      (((synCcompl (Class.cv (nb090AlphaDummy850 A)))).fv ∪
        ((synCcompl (Class.cv (nb090AlphaDummy851 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0909 (v : Var) :
    (nb090AlphaDummy853 v) ∈
      (((synCcompl (Class.cv (nb090AlphaDummy853 v)))).fv ∪
        ((synCcompl (Class.cv (nb090AlphaDummy854 v)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0910 (A : Class) :
    (nb090AlphaDummy850 A) ∈
      (((Class.cv (nb090AlphaDummy850 A))).fv ∪ ((Class.cv (nb090AlphaDummy850 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0911 (v : Var) :
    (nb090AlphaDummy853 v) ∈
      (((Class.cv (nb090AlphaDummy853 v))).fv ∪ ((Class.cv (nb090AlphaDummy853 v))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0912 (A : Class) :
    (nb090AlphaDummy851 A) ∈
      (((synCcompl (Class.cv (nb090AlphaDummy850 A)))).fv ∪
        ((synCcompl (Class.cv (nb090AlphaDummy851 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0913 (v : Var) :
    (nb090AlphaDummy854 v) ∈
      (((synCcompl (Class.cv (nb090AlphaDummy853 v)))).fv ∪
        ((synCcompl (Class.cv (nb090AlphaDummy854 v)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0914 (A : Class) :
    (nb090AlphaDummy851 A) ∈
      (((Class.cv (nb090AlphaDummy851 A))).fv ∪ ((Class.cv (nb090AlphaDummy851 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0915 (v : Var) :
    (nb090AlphaDummy854 v) ∈
      (((Class.cv (nb090AlphaDummy854 v))).fv ∪ ((Class.cv (nb090AlphaDummy854 v))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0916 (A : Class) :
    (nb090AlphaDummy827 A) ∈
      (((Class.cv (nb090AlphaDummy002 A))).fv ∪ ((Class.cv (nb090AlphaDummy827 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0917 (A : Class) :
    (nb090AlphaDummy827 A) ∈
      (((synCcompl (Class.cab (nb090AlphaDummy835 A)
              (synWrex (nb090AlphaDummy836 A) (Class.cv (nb090AlphaDummy002 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy835 A))
                  (synCphi (Class.cv (nb090AlphaDummy836 A)))))))).fv ∪ ((synCcompl
            (Class.cab (nb090AlphaDummy835 A)
              (synWrex (nb090AlphaDummy836 A) (Class.cv (nb090AlphaDummy827 A))
                (Wff.classEq (Class.cv (nb090AlphaDummy835 A))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy836 A)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090AlphaDummy827 A) ≠ (nb090AlphaDummy835 A) from (by
          unfold nb090AlphaDummy835;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0916 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090AlphaDummy827 A) ≠ (nb090AlphaDummy836 A) from (by
            unfold nb090AlphaDummy836;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0916 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0918 (v : Var) :
    (nb090AlphaDummy828 v) ∈
      (((Class.cv v)).fv ∪ ((Class.cv (nb090AlphaDummy828 v))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0919 (v : Var) :
    (nb090AlphaDummy828 v) ∈
      (((synCcompl (Class.cab (nb090AlphaDummy837 v)
              (synWrex (nb090AlphaDummy838 v) (Class.cv v)
                (Wff.classEq (Class.cv (nb090AlphaDummy837 v))
                  (synCphi (Class.cv (nb090AlphaDummy838 v)))))))).fv ∪ ((synCcompl
            (Class.cab (nb090AlphaDummy837 v)
              (synWrex (nb090AlphaDummy838 v) (Class.cv (nb090AlphaDummy828 v))
                (Wff.classEq (Class.cv (nb090AlphaDummy837 v))
                  (synCun (synCphi (Class.cv (nb090AlphaDummy838 v)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090AlphaDummy828 v) ≠ (nb090AlphaDummy837 v) from (by
          unfold nb090AlphaDummy837;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0918 v) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090AlphaDummy828 v) ≠ (nb090AlphaDummy838 v) from (by
            unfold nb090AlphaDummy838;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0918 v) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0920 (A : Class) :
    (nb090AlphaDummy827 A) ∈
      (((Class.cab (nb090AlphaDummy835 A)
            (synWrex (nb090AlphaDummy836 A) (Class.cv (nb090AlphaDummy827 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy835 A))
                (synCun (synCphi (Class.cv (nb090AlphaDummy836 A)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb090AlphaDummy835 A)
            (synWrex (nb090AlphaDummy836 A) (Class.cv (nb090AlphaDummy827 A))
              (Wff.classEq (Class.cv (nb090AlphaDummy835 A))
                (synCun (synCphi (Class.cv (nb090AlphaDummy836 A)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090AlphaDummy827 A) ≠ (nb090AlphaDummy835 A) from (by
          unfold nb090AlphaDummy835;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0916 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090AlphaDummy827 A) ≠ (nb090AlphaDummy836 A) from (by
            unfold nb090AlphaDummy836;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0916 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0921 (v : Var) :
    (nb090AlphaDummy828 v) ∈
      (((Class.cab (nb090AlphaDummy837 v)
            (synWrex (nb090AlphaDummy838 v) (Class.cv (nb090AlphaDummy828 v))
              (Wff.classEq (Class.cv (nb090AlphaDummy837 v))
                (synCun (synCphi (Class.cv (nb090AlphaDummy838 v)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb090AlphaDummy837 v)
            (synWrex (nb090AlphaDummy838 v) (Class.cv (nb090AlphaDummy828 v))
              (Wff.classEq (Class.cv (nb090AlphaDummy837 v))
                (synCun (synCphi (Class.cv (nb090AlphaDummy838 v)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb090AlphaDummy828 v) ≠ (nb090AlphaDummy837 v) from (by
          unfold nb090AlphaDummy837;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0918 v) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb090AlphaDummy828 v) ≠ (nb090AlphaDummy838 v) from (by
            unfold nb090AlphaDummy838;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0918 v) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb090_support_mem_0922 (A : Class) :
    (nb090AlphaDummy836 A) ∈
      (((synCcompl (synCphi (Class.cv (nb090AlphaDummy836 A))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0923 (v : Var) :
    (nb090AlphaDummy838 v) ∈
      (((synCcompl (synCphi (Class.cv (nb090AlphaDummy838 v))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0924 (A : Class) :
    (nb090AlphaDummy836 A) ∈
      (((synCphi (Class.cv (nb090AlphaDummy836 A)))).fv ∪
        ((synCphi (Class.cv (nb090AlphaDummy836 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0925 (v : Var) :
    (nb090AlphaDummy838 v) ∈
      (((synCphi (Class.cv (nb090AlphaDummy838 v)))).fv ∪
        ((synCphi (Class.cv (nb090AlphaDummy838 v)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0926 (A : Class) :
    (nb090AlphaDummy829 A) ∈ (((Class.cv (nb090AlphaDummy829 A))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_support_mem_0927 (v : Var) :
    (nb090AlphaDummy830 v) ∈ (((Class.cv (nb090AlphaDummy830 v))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb090_compact_fv_empty_0020 (A : Class) :
    (nb090AlphaDummy002 A) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb090_compact_fv_empty_0021 (v : Var) : v ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb090_compact_fv_empty_0022 (A : Class) :
    (nb090AlphaDummy001 A) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb090_compact_fv_empty_0023 (u : Var) : u ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb090_compact_fv_empty_0024 (A : Class) :
    (nb090AlphaDummy003 A) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb090_compact_fv_empty_0025 (v : Var) (u : Var) (A : Class) (h : Var) :
    (nb090AlphaDummy004 v u A h) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
