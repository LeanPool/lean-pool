/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C068C001Block002

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C068C001Part010`. -/


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

theorem nb068_support_mem_0076 (f : Var) :
    (nb068AlphaDummy049 f) ∈
      (((Class.cv (nb068AlphaDummy048 f))).fv ∪ ((Class.cv (nb068AlphaDummy049 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0077 (f : Var) :
    (nb068AlphaDummy049 f) ∈
      (((synCcompl (Class.cab (nb068AlphaDummy055 f)
              (synWrex (nb068AlphaDummy056 f) (Class.cv (nb068AlphaDummy048 f))
                (Wff.classEq (Class.cv (nb068AlphaDummy055 f))
                  (synCphi (Class.cv (nb068AlphaDummy056 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb068AlphaDummy055 f)
              (synWrex (nb068AlphaDummy056 f) (Class.cv (nb068AlphaDummy049 f))
                (Wff.classEq (Class.cv (nb068AlphaDummy055 f))
                  (synCun (synCphi (Class.cv (nb068AlphaDummy056 f)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068AlphaDummy049 f) ≠ (nb068AlphaDummy055 f) from (by
          unfold nb068AlphaDummy055;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0076 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068AlphaDummy049 f) ≠ (nb068AlphaDummy056 f) from (by
            unfold nb068AlphaDummy056;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0076 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0078 :
    (nb068AlphaDummy046) ∈
      (((Class.cab (nb068AlphaDummy053)
            (synWrex (nb068AlphaDummy054) (Class.cv (nb068AlphaDummy046))
              (Wff.classEq (Class.cv (nb068AlphaDummy053))
                (synCun (synCphi (Class.cv (nb068AlphaDummy054)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb068AlphaDummy053)
            (synWrex (nb068AlphaDummy054) (Class.cv (nb068AlphaDummy046))
              (Wff.classEq (Class.cv (nb068AlphaDummy053))
                (synCun (synCphi (Class.cv (nb068AlphaDummy054)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068AlphaDummy046) ≠ (nb068AlphaDummy053) from (by
          unfold nb068AlphaDummy053;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0074) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068AlphaDummy046) ≠ (nb068AlphaDummy054) from (by
            unfold nb068AlphaDummy054;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0074) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0079 (f : Var) :
    (nb068AlphaDummy049 f) ∈
      (((Class.cab (nb068AlphaDummy055 f)
            (synWrex (nb068AlphaDummy056 f) (Class.cv (nb068AlphaDummy049 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy055 f))
                (synCun (synCphi (Class.cv (nb068AlphaDummy056 f)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb068AlphaDummy055 f)
            (synWrex (nb068AlphaDummy056 f) (Class.cv (nb068AlphaDummy049 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy055 f))
                (synCun (synCphi (Class.cv (nb068AlphaDummy056 f)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068AlphaDummy049 f) ≠ (nb068AlphaDummy055 f) from (by
          unfold nb068AlphaDummy055;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0076 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068AlphaDummy049 f) ≠ (nb068AlphaDummy056 f) from (by
            unfold nb068AlphaDummy056;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0076 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0080 :
    (nb068AlphaDummy054) ∈
      (((synCcompl (synCphi (Class.cv (nb068AlphaDummy054))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0081 (f : Var) :
    (nb068AlphaDummy056 f) ∈
      (((synCcompl (synCphi (Class.cv (nb068AlphaDummy056 f))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0082 :
    (nb068AlphaDummy054) ∈
      (((synCphi (Class.cv (nb068AlphaDummy054)))).fv ∪
        ((synCphi (Class.cv (nb068AlphaDummy054)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0083 (f : Var) :
    (nb068AlphaDummy056 f) ∈
      (((synCphi (Class.cv (nb068AlphaDummy056 f)))).fv ∪
        ((synCphi (Class.cv (nb068AlphaDummy056 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0084 :
    (nb068AlphaDummy045) ∈
      (((Class.cv (nb068AlphaDummy045))).fv ∪ ((Class.cv (nb068AlphaDummy047))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0085 :
    (nb068AlphaDummy045) ∈
      (((synCcompl (Class.cab (nb068AlphaDummy089)
              (synWrex (nb068AlphaDummy090) (Class.cv (nb068AlphaDummy045))
                (Wff.classEq (Class.cv (nb068AlphaDummy089))
                  (synCphi (Class.cv (nb068AlphaDummy090)))))))).fv ∪ ((synCcompl
            (Class.cab (nb068AlphaDummy089)
              (synWrex (nb068AlphaDummy090) (Class.cv (nb068AlphaDummy047))
                (Wff.classEq (Class.cv (nb068AlphaDummy089))
                  (synCun (synCphi (Class.cv (nb068AlphaDummy090)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068AlphaDummy045) ≠ (nb068AlphaDummy089) from (by
          unfold nb068AlphaDummy089;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0084) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068AlphaDummy045) ≠ (nb068AlphaDummy090) from (by
            unfold nb068AlphaDummy090;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0084) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0086 (f : Var) :
    (nb068AlphaDummy048 f) ∈
      (((Class.cv (nb068AlphaDummy048 f))).fv ∪ ((Class.cv (nb068AlphaDummy050 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0087 (f : Var) :
    (nb068AlphaDummy048 f) ∈
      (((synCcompl (Class.cab (nb068AlphaDummy091 f)
              (synWrex (nb068AlphaDummy092 f) (Class.cv (nb068AlphaDummy048 f))
                (Wff.classEq (Class.cv (nb068AlphaDummy091 f))
                  (synCphi (Class.cv (nb068AlphaDummy092 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb068AlphaDummy091 f)
              (synWrex (nb068AlphaDummy092 f) (Class.cv (nb068AlphaDummy050 f))
                (Wff.classEq (Class.cv (nb068AlphaDummy091 f))
                  (synCun (synCphi (Class.cv (nb068AlphaDummy092 f)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068AlphaDummy048 f) ≠ (nb068AlphaDummy091 f) from (by
          unfold nb068AlphaDummy091;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0086 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068AlphaDummy048 f) ≠ (nb068AlphaDummy092 f) from (by
            unfold nb068AlphaDummy092;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0086 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0088 :
    (nb068AlphaDummy045) ∈
      (((Class.cab (nb068AlphaDummy089)
            (synWrex (nb068AlphaDummy090) (Class.cv (nb068AlphaDummy045))
              (Wff.classEq (Class.cv (nb068AlphaDummy089))
                (synCphi (Class.cv (nb068AlphaDummy090))))))).fv ∪
        ((Class.cab (nb068AlphaDummy089)
            (synWrex (nb068AlphaDummy090) (Class.cv (nb068AlphaDummy045))
              (Wff.classEq (Class.cv (nb068AlphaDummy089))
                (synCphi (Class.cv (nb068AlphaDummy090))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068AlphaDummy045) ≠ (nb068AlphaDummy089) from (by
          unfold nb068AlphaDummy089;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0084) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068AlphaDummy045) ≠ (nb068AlphaDummy090) from (by
            unfold nb068AlphaDummy090;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0084) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0089 (f : Var) :
    (nb068AlphaDummy048 f) ∈
      (((Class.cab (nb068AlphaDummy091 f)
            (synWrex (nb068AlphaDummy092 f) (Class.cv (nb068AlphaDummy048 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy091 f))
                (synCphi (Class.cv (nb068AlphaDummy092 f))))))).fv ∪
        ((Class.cab (nb068AlphaDummy091 f)
            (synWrex (nb068AlphaDummy092 f) (Class.cv (nb068AlphaDummy048 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy091 f))
                (synCphi (Class.cv (nb068AlphaDummy092 f))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068AlphaDummy048 f) ≠ (nb068AlphaDummy091 f) from (by
          unfold nb068AlphaDummy091;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0086 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068AlphaDummy048 f) ≠ (nb068AlphaDummy092 f) from (by
            unfold nb068AlphaDummy092;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0086 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0090 :
    (nb068AlphaDummy090) ∈ (((Class.cv (nb068AlphaDummy090))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0091 (f : Var) :
    (nb068AlphaDummy092 f) ∈ (((Class.cv (nb068AlphaDummy092 f))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0092 :
    (nb068AlphaDummy097) ∈
      (((Wff.classMem (Class.cv (nb068AlphaDummy097)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb068AlphaDummy097)) (synC1c))).fv ∪
        ((Class.cv (nb068AlphaDummy097))).fv) :=
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

theorem nb068_support_mem_0093 (f : Var) :
    (nb068AlphaDummy099 f) ∈
      (((Wff.classMem (Class.cv (nb068AlphaDummy099 f)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb068AlphaDummy099 f)) (synC1c))).fv ∪
        ((Class.cv (nb068AlphaDummy099 f))).fv) :=
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

theorem nb068_support_mem_0094 :
    (nb068AlphaDummy097) ∈
      (((Class.cv (nb068AlphaDummy097))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0095 (f : Var) :
    (nb068AlphaDummy099 f) ∈
      (((Class.cv (nb068AlphaDummy099 f))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0096 :
    (nb068AlphaDummy104) ∈
      (((synCnin (Class.cv (nb068AlphaDummy104)) (Class.cv (nb068AlphaDummy105)))).fv ∪
        ((synCnin (Class.cv (nb068AlphaDummy104))
            (Class.cv (nb068AlphaDummy105)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0097 (f : Var) :
    (nb068AlphaDummy107 f) ∈
      (((synCnin (Class.cv (nb068AlphaDummy107 f))
            (Class.cv (nb068AlphaDummy108 f)))).fv ∪
        ((synCnin (Class.cv (nb068AlphaDummy107 f))
            (Class.cv (nb068AlphaDummy108 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0098 :
    (nb068AlphaDummy104) ∈
      (((Class.cv (nb068AlphaDummy104))).fv ∪ ((Class.cv (nb068AlphaDummy105))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0099 (f : Var) :
    (nb068AlphaDummy107 f) ∈
      (((Class.cv (nb068AlphaDummy107 f))).fv ∪ ((Class.cv (nb068AlphaDummy108 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0100 :
    (nb068AlphaDummy105) ∈
      (((synCnin (Class.cv (nb068AlphaDummy104)) (Class.cv (nb068AlphaDummy105)))).fv ∪
        ((synCnin (Class.cv (nb068AlphaDummy104))
            (Class.cv (nb068AlphaDummy105)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0101 (f : Var) :
    (nb068AlphaDummy108 f) ∈
      (((synCnin (Class.cv (nb068AlphaDummy107 f))
            (Class.cv (nb068AlphaDummy108 f)))).fv ∪
        ((synCnin (Class.cv (nb068AlphaDummy107 f))
            (Class.cv (nb068AlphaDummy108 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0102 :
    (nb068AlphaDummy105) ∈
      (((Class.cv (nb068AlphaDummy104))).fv ∪ ((Class.cv (nb068AlphaDummy105))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0103 (f : Var) :
    (nb068AlphaDummy108 f) ∈
      (((Class.cv (nb068AlphaDummy107 f))).fv ∪ ((Class.cv (nb068AlphaDummy108 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0104 :
    (nb068AlphaDummy104) ∈
      (((synCcompl (Class.cv (nb068AlphaDummy104)))).fv ∪
        ((synCcompl (Class.cv (nb068AlphaDummy105)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0105 (f : Var) :
    (nb068AlphaDummy107 f) ∈
      (((synCcompl (Class.cv (nb068AlphaDummy107 f)))).fv ∪
        ((synCcompl (Class.cv (nb068AlphaDummy108 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0106 :
    (nb068AlphaDummy104) ∈
      (((Class.cv (nb068AlphaDummy104))).fv ∪ ((Class.cv (nb068AlphaDummy104))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0107 (f : Var) :
    (nb068AlphaDummy107 f) ∈
      (((Class.cv (nb068AlphaDummy107 f))).fv ∪ ((Class.cv (nb068AlphaDummy107 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0108 :
    (nb068AlphaDummy105) ∈
      (((synCcompl (Class.cv (nb068AlphaDummy104)))).fv ∪
        ((synCcompl (Class.cv (nb068AlphaDummy105)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0109 (f : Var) :
    (nb068AlphaDummy108 f) ∈
      (((synCcompl (Class.cv (nb068AlphaDummy107 f)))).fv ∪
        ((synCcompl (Class.cv (nb068AlphaDummy108 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0110 :
    (nb068AlphaDummy105) ∈
      (((Class.cv (nb068AlphaDummy105))).fv ∪ ((Class.cv (nb068AlphaDummy105))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0111 (f : Var) :
    (nb068AlphaDummy108 f) ∈
      (((Class.cv (nb068AlphaDummy108 f))).fv ∪ ((Class.cv (nb068AlphaDummy108 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0112 :
    (nb068AlphaDummy047) ∈
      (((Class.cv (nb068AlphaDummy045))).fv ∪ ((Class.cv (nb068AlphaDummy047))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0113 :
    (nb068AlphaDummy047) ∈
      (((synCcompl (Class.cab (nb068AlphaDummy089)
              (synWrex (nb068AlphaDummy090) (Class.cv (nb068AlphaDummy045))
                (Wff.classEq (Class.cv (nb068AlphaDummy089))
                  (synCphi (Class.cv (nb068AlphaDummy090)))))))).fv ∪ ((synCcompl
            (Class.cab (nb068AlphaDummy089)
              (synWrex (nb068AlphaDummy090) (Class.cv (nb068AlphaDummy047))
                (Wff.classEq (Class.cv (nb068AlphaDummy089))
                  (synCun (synCphi (Class.cv (nb068AlphaDummy090)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068AlphaDummy047) ≠ (nb068AlphaDummy089) from (by
          unfold nb068AlphaDummy089;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0112) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068AlphaDummy047) ≠ (nb068AlphaDummy090) from (by
            unfold nb068AlphaDummy090;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0112) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0114 (f : Var) :
    (nb068AlphaDummy050 f) ∈
      (((Class.cv (nb068AlphaDummy048 f))).fv ∪ ((Class.cv (nb068AlphaDummy050 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0115 (f : Var) :
    (nb068AlphaDummy050 f) ∈
      (((synCcompl (Class.cab (nb068AlphaDummy091 f)
              (synWrex (nb068AlphaDummy092 f) (Class.cv (nb068AlphaDummy048 f))
                (Wff.classEq (Class.cv (nb068AlphaDummy091 f))
                  (synCphi (Class.cv (nb068AlphaDummy092 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb068AlphaDummy091 f)
              (synWrex (nb068AlphaDummy092 f) (Class.cv (nb068AlphaDummy050 f))
                (Wff.classEq (Class.cv (nb068AlphaDummy091 f))
                  (synCun (synCphi (Class.cv (nb068AlphaDummy092 f)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068AlphaDummy050 f) ≠ (nb068AlphaDummy091 f) from (by
          unfold nb068AlphaDummy091;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0114 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068AlphaDummy050 f) ≠ (nb068AlphaDummy092 f) from (by
            unfold nb068AlphaDummy092;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0114 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0116 :
    (nb068AlphaDummy047) ∈
      (((Class.cab (nb068AlphaDummy089)
            (synWrex (nb068AlphaDummy090) (Class.cv (nb068AlphaDummy047))
              (Wff.classEq (Class.cv (nb068AlphaDummy089))
                (synCun (synCphi (Class.cv (nb068AlphaDummy090)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb068AlphaDummy089)
            (synWrex (nb068AlphaDummy090) (Class.cv (nb068AlphaDummy047))
              (Wff.classEq (Class.cv (nb068AlphaDummy089))
                (synCun (synCphi (Class.cv (nb068AlphaDummy090)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068AlphaDummy047) ≠ (nb068AlphaDummy089) from (by
          unfold nb068AlphaDummy089;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0112) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068AlphaDummy047) ≠ (nb068AlphaDummy090) from (by
            unfold nb068AlphaDummy090;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0112) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0117 (f : Var) :
    (nb068AlphaDummy050 f) ∈
      (((Class.cab (nb068AlphaDummy091 f)
            (synWrex (nb068AlphaDummy092 f) (Class.cv (nb068AlphaDummy050 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy091 f))
                (synCun (synCphi (Class.cv (nb068AlphaDummy092 f)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb068AlphaDummy091 f)
            (synWrex (nb068AlphaDummy092 f) (Class.cv (nb068AlphaDummy050 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy091 f))
                (synCun (synCphi (Class.cv (nb068AlphaDummy092 f)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068AlphaDummy050 f) ≠ (nb068AlphaDummy091 f) from (by
          unfold nb068AlphaDummy091;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0114 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068AlphaDummy050 f) ≠ (nb068AlphaDummy092 f) from (by
            unfold nb068AlphaDummy092;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0114 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0118 :
    (nb068AlphaDummy090) ∈
      (((synCcompl (synCphi (Class.cv (nb068AlphaDummy090))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0119 (f : Var) :
    (nb068AlphaDummy092 f) ∈
      (((synCcompl (synCphi (Class.cv (nb068AlphaDummy092 f))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0120 :
    (nb068AlphaDummy090) ∈
      (((synCphi (Class.cv (nb068AlphaDummy090)))).fv ∪
        ((synCphi (Class.cv (nb068AlphaDummy090)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0121 (f : Var) :
    (nb068AlphaDummy092 f) ∈
      (((synCphi (Class.cv (nb068AlphaDummy092 f)))).fv ∪
        ((synCphi (Class.cv (nb068AlphaDummy092 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0122 :
    (nb068AlphaDummy125) ∈
      (({(nb068AlphaDummy125)} : Finset Var) ∪ ({(nb068AlphaDummy126)} : Finset Var) ∪
        ((synWbr (Class.cv (nb068AlphaDummy126)) (Class.cv (nb068AlphaDummy000))
            (Class.cv (nb068AlphaDummy125)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0123 (f : Var) :
    (nb068AlphaDummy127 f) ∈
      (({(nb068AlphaDummy127 f)} : Finset Var) ∪ ({(nb068AlphaDummy128 f)} : Finset Var) ∪
        ((synWbr (Class.cv (nb068AlphaDummy128 f)) (Class.cv f)
            (Class.cv (nb068AlphaDummy127 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0124 :
    (nb068AlphaDummy126) ∈
      (({(nb068AlphaDummy125)} : Finset Var) ∪ ({(nb068AlphaDummy126)} : Finset Var) ∪
        ((synWbr (Class.cv (nb068AlphaDummy126)) (Class.cv (nb068AlphaDummy000))
            (Class.cv (nb068AlphaDummy125)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0125 (f : Var) :
    (nb068AlphaDummy128 f) ∈
      (({(nb068AlphaDummy127 f)} : Finset Var) ∪ ({(nb068AlphaDummy128 f)} : Finset Var) ∪
        ((synWbr (Class.cv (nb068AlphaDummy128 f)) (Class.cv f)
            (Class.cv (nb068AlphaDummy127 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0126 :
    (nb068AlphaDummy125) ∈
      (((Class.cv (nb068AlphaDummy125))).fv ∪ ((Class.cv (nb068AlphaDummy126))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0127 :
    (nb068AlphaDummy125) ∈
      (((synCcompl (Class.cab (nb068AlphaDummy131)
              (synWrex (nb068AlphaDummy132) (Class.cv (nb068AlphaDummy125))
                (Wff.classEq (Class.cv (nb068AlphaDummy131))
                  (synCphi (Class.cv (nb068AlphaDummy132)))))))).fv ∪ ((synCcompl
            (Class.cab (nb068AlphaDummy131)
              (synWrex (nb068AlphaDummy132) (Class.cv (nb068AlphaDummy126))
                (Wff.classEq (Class.cv (nb068AlphaDummy131))
                  (synCun (synCphi (Class.cv (nb068AlphaDummy132)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068AlphaDummy125) ≠ (nb068AlphaDummy131) from (by
          unfold nb068AlphaDummy131;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0126) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068AlphaDummy125) ≠ (nb068AlphaDummy132) from (by
            unfold nb068AlphaDummy132;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0126) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0128 (f : Var) :
    (nb068AlphaDummy127 f) ∈
      (((Class.cv (nb068AlphaDummy127 f))).fv ∪ ((Class.cv (nb068AlphaDummy128 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0129 (f : Var) :
    (nb068AlphaDummy127 f) ∈
      (((synCcompl (Class.cab (nb068AlphaDummy133 f)
              (synWrex (nb068AlphaDummy134 f) (Class.cv (nb068AlphaDummy127 f))
                (Wff.classEq (Class.cv (nb068AlphaDummy133 f))
                  (synCphi (Class.cv (nb068AlphaDummy134 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb068AlphaDummy133 f)
              (synWrex (nb068AlphaDummy134 f) (Class.cv (nb068AlphaDummy128 f))
                (Wff.classEq (Class.cv (nb068AlphaDummy133 f))
                  (synCun (synCphi (Class.cv (nb068AlphaDummy134 f)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068AlphaDummy127 f) ≠ (nb068AlphaDummy133 f) from (by
          unfold nb068AlphaDummy133;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0128 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068AlphaDummy127 f) ≠ (nb068AlphaDummy134 f) from (by
            unfold nb068AlphaDummy134;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0128 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0130 :
    (nb068AlphaDummy125) ∈
      (((Class.cab (nb068AlphaDummy131)
            (synWrex (nb068AlphaDummy132) (Class.cv (nb068AlphaDummy125))
              (Wff.classEq (Class.cv (nb068AlphaDummy131))
                (synCphi (Class.cv (nb068AlphaDummy132))))))).fv ∪
        ((Class.cab (nb068AlphaDummy131)
            (synWrex (nb068AlphaDummy132) (Class.cv (nb068AlphaDummy125))
              (Wff.classEq (Class.cv (nb068AlphaDummy131))
                (synCphi (Class.cv (nb068AlphaDummy132))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068AlphaDummy125) ≠ (nb068AlphaDummy131) from (by
          unfold nb068AlphaDummy131;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0126) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068AlphaDummy125) ≠ (nb068AlphaDummy132) from (by
            unfold nb068AlphaDummy132;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0126) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0131 (f : Var) :
    (nb068AlphaDummy127 f) ∈
      (((Class.cab (nb068AlphaDummy133 f)
            (synWrex (nb068AlphaDummy134 f) (Class.cv (nb068AlphaDummy127 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy133 f))
                (synCphi (Class.cv (nb068AlphaDummy134 f))))))).fv ∪
        ((Class.cab (nb068AlphaDummy133 f)
            (synWrex (nb068AlphaDummy134 f) (Class.cv (nb068AlphaDummy127 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy133 f))
                (synCphi (Class.cv (nb068AlphaDummy134 f))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068AlphaDummy127 f) ≠ (nb068AlphaDummy133 f) from (by
          unfold nb068AlphaDummy133;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0128 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068AlphaDummy127 f) ≠ (nb068AlphaDummy134 f) from (by
            unfold nb068AlphaDummy134;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0128 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0132 :
    (nb068AlphaDummy132) ∈ (((Class.cv (nb068AlphaDummy132))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0133 (f : Var) :
    (nb068AlphaDummy134 f) ∈ (((Class.cv (nb068AlphaDummy134 f))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0134 :
    (nb068AlphaDummy139) ∈
      (((Wff.classMem (Class.cv (nb068AlphaDummy139)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb068AlphaDummy139)) (synC1c))).fv ∪
        ((Class.cv (nb068AlphaDummy139))).fv) :=
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

theorem nb068_support_mem_0135 (f : Var) :
    (nb068AlphaDummy141 f) ∈
      (((Wff.classMem (Class.cv (nb068AlphaDummy141 f)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb068AlphaDummy141 f)) (synC1c))).fv ∪
        ((Class.cv (nb068AlphaDummy141 f))).fv) :=
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

theorem nb068_support_mem_0136 :
    (nb068AlphaDummy139) ∈
      (((Class.cv (nb068AlphaDummy139))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0137 (f : Var) :
    (nb068AlphaDummy141 f) ∈
      (((Class.cv (nb068AlphaDummy141 f))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0138 :
    (nb068AlphaDummy146) ∈
      (((synCnin (Class.cv (nb068AlphaDummy146)) (Class.cv (nb068AlphaDummy147)))).fv ∪
        ((synCnin (Class.cv (nb068AlphaDummy146))
            (Class.cv (nb068AlphaDummy147)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0139 (f : Var) :
    (nb068AlphaDummy149 f) ∈
      (((synCnin (Class.cv (nb068AlphaDummy149 f))
            (Class.cv (nb068AlphaDummy150 f)))).fv ∪
        ((synCnin (Class.cv (nb068AlphaDummy149 f))
            (Class.cv (nb068AlphaDummy150 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0140 :
    (nb068AlphaDummy146) ∈
      (((Class.cv (nb068AlphaDummy146))).fv ∪ ((Class.cv (nb068AlphaDummy147))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0141 (f : Var) :
    (nb068AlphaDummy149 f) ∈
      (((Class.cv (nb068AlphaDummy149 f))).fv ∪ ((Class.cv (nb068AlphaDummy150 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0142 :
    (nb068AlphaDummy147) ∈
      (((synCnin (Class.cv (nb068AlphaDummy146)) (Class.cv (nb068AlphaDummy147)))).fv ∪
        ((synCnin (Class.cv (nb068AlphaDummy146))
            (Class.cv (nb068AlphaDummy147)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0143 (f : Var) :
    (nb068AlphaDummy150 f) ∈
      (((synCnin (Class.cv (nb068AlphaDummy149 f))
            (Class.cv (nb068AlphaDummy150 f)))).fv ∪
        ((synCnin (Class.cv (nb068AlphaDummy149 f))
            (Class.cv (nb068AlphaDummy150 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0144 :
    (nb068AlphaDummy147) ∈
      (((Class.cv (nb068AlphaDummy146))).fv ∪ ((Class.cv (nb068AlphaDummy147))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0145 (f : Var) :
    (nb068AlphaDummy150 f) ∈
      (((Class.cv (nb068AlphaDummy149 f))).fv ∪ ((Class.cv (nb068AlphaDummy150 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0146 :
    (nb068AlphaDummy146) ∈
      (((synCcompl (Class.cv (nb068AlphaDummy146)))).fv ∪
        ((synCcompl (Class.cv (nb068AlphaDummy147)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0147 (f : Var) :
    (nb068AlphaDummy149 f) ∈
      (((synCcompl (Class.cv (nb068AlphaDummy149 f)))).fv ∪
        ((synCcompl (Class.cv (nb068AlphaDummy150 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0148 :
    (nb068AlphaDummy146) ∈
      (((Class.cv (nb068AlphaDummy146))).fv ∪ ((Class.cv (nb068AlphaDummy146))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0149 (f : Var) :
    (nb068AlphaDummy149 f) ∈
      (((Class.cv (nb068AlphaDummy149 f))).fv ∪ ((Class.cv (nb068AlphaDummy149 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0150 :
    (nb068AlphaDummy147) ∈
      (((synCcompl (Class.cv (nb068AlphaDummy146)))).fv ∪
        ((synCcompl (Class.cv (nb068AlphaDummy147)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0151 (f : Var) :
    (nb068AlphaDummy150 f) ∈
      (((synCcompl (Class.cv (nb068AlphaDummy149 f)))).fv ∪
        ((synCcompl (Class.cv (nb068AlphaDummy150 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0152 :
    (nb068AlphaDummy147) ∈
      (((Class.cv (nb068AlphaDummy147))).fv ∪ ((Class.cv (nb068AlphaDummy147))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0153 (f : Var) :
    (nb068AlphaDummy150 f) ∈
      (((Class.cv (nb068AlphaDummy150 f))).fv ∪ ((Class.cv (nb068AlphaDummy150 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0154 :
    (nb068AlphaDummy126) ∈
      (((Class.cv (nb068AlphaDummy125))).fv ∪ ((Class.cv (nb068AlphaDummy126))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0155 :
    (nb068AlphaDummy126) ∈
      (((synCcompl (Class.cab (nb068AlphaDummy131)
              (synWrex (nb068AlphaDummy132) (Class.cv (nb068AlphaDummy125))
                (Wff.classEq (Class.cv (nb068AlphaDummy131))
                  (synCphi (Class.cv (nb068AlphaDummy132)))))))).fv ∪ ((synCcompl
            (Class.cab (nb068AlphaDummy131)
              (synWrex (nb068AlphaDummy132) (Class.cv (nb068AlphaDummy126))
                (Wff.classEq (Class.cv (nb068AlphaDummy131))
                  (synCun (synCphi (Class.cv (nb068AlphaDummy132)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068AlphaDummy126) ≠ (nb068AlphaDummy131) from (by
          unfold nb068AlphaDummy131;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0154) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068AlphaDummy126) ≠ (nb068AlphaDummy132) from (by
            unfold nb068AlphaDummy132;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0154) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0156 (f : Var) :
    (nb068AlphaDummy128 f) ∈
      (((Class.cv (nb068AlphaDummy127 f))).fv ∪ ((Class.cv (nb068AlphaDummy128 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0157 (f : Var) :
    (nb068AlphaDummy128 f) ∈
      (((synCcompl (Class.cab (nb068AlphaDummy133 f)
              (synWrex (nb068AlphaDummy134 f) (Class.cv (nb068AlphaDummy127 f))
                (Wff.classEq (Class.cv (nb068AlphaDummy133 f))
                  (synCphi (Class.cv (nb068AlphaDummy134 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb068AlphaDummy133 f)
              (synWrex (nb068AlphaDummy134 f) (Class.cv (nb068AlphaDummy128 f))
                (Wff.classEq (Class.cv (nb068AlphaDummy133 f))
                  (synCun (synCphi (Class.cv (nb068AlphaDummy134 f)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068AlphaDummy128 f) ≠ (nb068AlphaDummy133 f) from (by
          unfold nb068AlphaDummy133;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0156 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068AlphaDummy128 f) ≠ (nb068AlphaDummy134 f) from (by
            unfold nb068AlphaDummy134;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0156 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0158 :
    (nb068AlphaDummy126) ∈
      (((Class.cab (nb068AlphaDummy131)
            (synWrex (nb068AlphaDummy132) (Class.cv (nb068AlphaDummy126))
              (Wff.classEq (Class.cv (nb068AlphaDummy131))
                (synCun (synCphi (Class.cv (nb068AlphaDummy132)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb068AlphaDummy131)
            (synWrex (nb068AlphaDummy132) (Class.cv (nb068AlphaDummy126))
              (Wff.classEq (Class.cv (nb068AlphaDummy131))
                (synCun (synCphi (Class.cv (nb068AlphaDummy132)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068AlphaDummy126) ≠ (nb068AlphaDummy131) from (by
          unfold nb068AlphaDummy131;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0154) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068AlphaDummy126) ≠ (nb068AlphaDummy132) from (by
            unfold nb068AlphaDummy132;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0154) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0159 (f : Var) :
    (nb068AlphaDummy128 f) ∈
      (((Class.cab (nb068AlphaDummy133 f)
            (synWrex (nb068AlphaDummy134 f) (Class.cv (nb068AlphaDummy128 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy133 f))
                (synCun (synCphi (Class.cv (nb068AlphaDummy134 f)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb068AlphaDummy133 f)
            (synWrex (nb068AlphaDummy134 f) (Class.cv (nb068AlphaDummy128 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy133 f))
                (synCun (synCphi (Class.cv (nb068AlphaDummy134 f)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068AlphaDummy128 f) ≠ (nb068AlphaDummy133 f) from (by
          unfold nb068AlphaDummy133;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0156 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068AlphaDummy128 f) ≠ (nb068AlphaDummy134 f) from (by
            unfold nb068AlphaDummy134;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0156 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0160 :
    (nb068AlphaDummy132) ∈
      (((synCcompl (synCphi (Class.cv (nb068AlphaDummy132))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0161 (f : Var) :
    (nb068AlphaDummy134 f) ∈
      (((synCcompl (synCphi (Class.cv (nb068AlphaDummy134 f))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0162 :
    (nb068AlphaDummy132) ∈
      (((synCphi (Class.cv (nb068AlphaDummy132)))).fv ∪
        ((synCphi (Class.cv (nb068AlphaDummy132)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0163 (f : Var) :
    (nb068AlphaDummy134 f) ∈
      (((synCphi (Class.cv (nb068AlphaDummy134 f)))).fv ∪
        ((synCphi (Class.cv (nb068AlphaDummy134 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0164 :
    (nb068AlphaDummy126) ∈
      (((Class.cv (nb068AlphaDummy126))).fv ∪ ((Class.cv (nb068AlphaDummy125))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0165 :
    (nb068AlphaDummy126) ∈
      (((synCcompl (Class.cab (nb068AlphaDummy167)
              (synWrex (nb068AlphaDummy168) (Class.cv (nb068AlphaDummy126))
                (Wff.classEq (Class.cv (nb068AlphaDummy167))
                  (synCphi (Class.cv (nb068AlphaDummy168)))))))).fv ∪ ((synCcompl
            (Class.cab (nb068AlphaDummy167)
              (synWrex (nb068AlphaDummy168) (Class.cv (nb068AlphaDummy125))
                (Wff.classEq (Class.cv (nb068AlphaDummy167))
                  (synCun (synCphi (Class.cv (nb068AlphaDummy168)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068AlphaDummy126) ≠ (nb068AlphaDummy167) from (by
          unfold nb068AlphaDummy167;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0164) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068AlphaDummy126) ≠ (nb068AlphaDummy168) from (by
            unfold nb068AlphaDummy168;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0164) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0166 (f : Var) :
    (nb068AlphaDummy128 f) ∈
      (((Class.cv (nb068AlphaDummy128 f))).fv ∪ ((Class.cv (nb068AlphaDummy127 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0167 (f : Var) :
    (nb068AlphaDummy128 f) ∈
      (((synCcompl (Class.cab (nb068AlphaDummy169 f)
              (synWrex (nb068AlphaDummy170 f) (Class.cv (nb068AlphaDummy128 f))
                (Wff.classEq (Class.cv (nb068AlphaDummy169 f))
                  (synCphi (Class.cv (nb068AlphaDummy170 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb068AlphaDummy169 f)
              (synWrex (nb068AlphaDummy170 f) (Class.cv (nb068AlphaDummy127 f))
                (Wff.classEq (Class.cv (nb068AlphaDummy169 f))
                  (synCun (synCphi (Class.cv (nb068AlphaDummy170 f)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068AlphaDummy128 f) ≠ (nb068AlphaDummy169 f) from (by
          unfold nb068AlphaDummy169;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0166 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068AlphaDummy128 f) ≠ (nb068AlphaDummy170 f) from (by
            unfold nb068AlphaDummy170;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0166 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0168 :
    (nb068AlphaDummy126) ∈
      (((Class.cab (nb068AlphaDummy167)
            (synWrex (nb068AlphaDummy168) (Class.cv (nb068AlphaDummy126))
              (Wff.classEq (Class.cv (nb068AlphaDummy167))
                (synCphi (Class.cv (nb068AlphaDummy168))))))).fv ∪
        ((Class.cab (nb068AlphaDummy167)
            (synWrex (nb068AlphaDummy168) (Class.cv (nb068AlphaDummy126))
              (Wff.classEq (Class.cv (nb068AlphaDummy167))
                (synCphi (Class.cv (nb068AlphaDummy168))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068AlphaDummy126) ≠ (nb068AlphaDummy167) from (by
          unfold nb068AlphaDummy167;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0164) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068AlphaDummy126) ≠ (nb068AlphaDummy168) from (by
            unfold nb068AlphaDummy168;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0164) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0169 (f : Var) :
    (nb068AlphaDummy128 f) ∈
      (((Class.cab (nb068AlphaDummy169 f)
            (synWrex (nb068AlphaDummy170 f) (Class.cv (nb068AlphaDummy128 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy169 f))
                (synCphi (Class.cv (nb068AlphaDummy170 f))))))).fv ∪
        ((Class.cab (nb068AlphaDummy169 f)
            (synWrex (nb068AlphaDummy170 f) (Class.cv (nb068AlphaDummy128 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy169 f))
                (synCphi (Class.cv (nb068AlphaDummy170 f))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068AlphaDummy128 f) ≠ (nb068AlphaDummy169 f) from (by
          unfold nb068AlphaDummy169;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0166 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068AlphaDummy128 f) ≠ (nb068AlphaDummy170 f) from (by
            unfold nb068AlphaDummy170;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0166 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0170 :
    (nb068AlphaDummy168) ∈ (((Class.cv (nb068AlphaDummy168))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0171 (f : Var) :
    (nb068AlphaDummy170 f) ∈ (((Class.cv (nb068AlphaDummy170 f))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0172 :
    (nb068AlphaDummy175) ∈
      (((Wff.classMem (Class.cv (nb068AlphaDummy175)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb068AlphaDummy175)) (synC1c))).fv ∪
        ((Class.cv (nb068AlphaDummy175))).fv) :=
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

theorem nb068_support_mem_0173 (f : Var) :
    (nb068AlphaDummy177 f) ∈
      (((Wff.classMem (Class.cv (nb068AlphaDummy177 f)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb068AlphaDummy177 f)) (synC1c))).fv ∪
        ((Class.cv (nb068AlphaDummy177 f))).fv) :=
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

theorem nb068_support_mem_0174 :
    (nb068AlphaDummy175) ∈
      (((Class.cv (nb068AlphaDummy175))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0175 (f : Var) :
    (nb068AlphaDummy177 f) ∈
      (((Class.cv (nb068AlphaDummy177 f))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0176 :
    (nb068AlphaDummy182) ∈
      (((synCnin (Class.cv (nb068AlphaDummy182)) (Class.cv (nb068AlphaDummy183)))).fv ∪
        ((synCnin (Class.cv (nb068AlphaDummy182))
            (Class.cv (nb068AlphaDummy183)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0177 (f : Var) :
    (nb068AlphaDummy185 f) ∈
      (((synCnin (Class.cv (nb068AlphaDummy185 f))
            (Class.cv (nb068AlphaDummy186 f)))).fv ∪
        ((synCnin (Class.cv (nb068AlphaDummy185 f))
            (Class.cv (nb068AlphaDummy186 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0178 :
    (nb068AlphaDummy182) ∈
      (((Class.cv (nb068AlphaDummy182))).fv ∪ ((Class.cv (nb068AlphaDummy183))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0179 (f : Var) :
    (nb068AlphaDummy185 f) ∈
      (((Class.cv (nb068AlphaDummy185 f))).fv ∪ ((Class.cv (nb068AlphaDummy186 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0180 :
    (nb068AlphaDummy183) ∈
      (((synCnin (Class.cv (nb068AlphaDummy182)) (Class.cv (nb068AlphaDummy183)))).fv ∪
        ((synCnin (Class.cv (nb068AlphaDummy182))
            (Class.cv (nb068AlphaDummy183)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0181 (f : Var) :
    (nb068AlphaDummy186 f) ∈
      (((synCnin (Class.cv (nb068AlphaDummy185 f))
            (Class.cv (nb068AlphaDummy186 f)))).fv ∪
        ((synCnin (Class.cv (nb068AlphaDummy185 f))
            (Class.cv (nb068AlphaDummy186 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0182 :
    (nb068AlphaDummy183) ∈
      (((Class.cv (nb068AlphaDummy182))).fv ∪ ((Class.cv (nb068AlphaDummy183))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0183 (f : Var) :
    (nb068AlphaDummy186 f) ∈
      (((Class.cv (nb068AlphaDummy185 f))).fv ∪ ((Class.cv (nb068AlphaDummy186 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0184 :
    (nb068AlphaDummy182) ∈
      (((synCcompl (Class.cv (nb068AlphaDummy182)))).fv ∪
        ((synCcompl (Class.cv (nb068AlphaDummy183)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0185 (f : Var) :
    (nb068AlphaDummy185 f) ∈
      (((synCcompl (Class.cv (nb068AlphaDummy185 f)))).fv ∪
        ((synCcompl (Class.cv (nb068AlphaDummy186 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0186 :
    (nb068AlphaDummy182) ∈
      (((Class.cv (nb068AlphaDummy182))).fv ∪ ((Class.cv (nb068AlphaDummy182))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0187 (f : Var) :
    (nb068AlphaDummy185 f) ∈
      (((Class.cv (nb068AlphaDummy185 f))).fv ∪ ((Class.cv (nb068AlphaDummy185 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0188 :
    (nb068AlphaDummy183) ∈
      (((synCcompl (Class.cv (nb068AlphaDummy182)))).fv ∪
        ((synCcompl (Class.cv (nb068AlphaDummy183)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0189 (f : Var) :
    (nb068AlphaDummy186 f) ∈
      (((synCcompl (Class.cv (nb068AlphaDummy185 f)))).fv ∪
        ((synCcompl (Class.cv (nb068AlphaDummy186 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0190 :
    (nb068AlphaDummy183) ∈
      (((Class.cv (nb068AlphaDummy183))).fv ∪ ((Class.cv (nb068AlphaDummy183))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0191 (f : Var) :
    (nb068AlphaDummy186 f) ∈
      (((Class.cv (nb068AlphaDummy186 f))).fv ∪ ((Class.cv (nb068AlphaDummy186 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0192 :
    (nb068AlphaDummy125) ∈
      (((Class.cv (nb068AlphaDummy126))).fv ∪ ((Class.cv (nb068AlphaDummy125))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0193 :
    (nb068AlphaDummy125) ∈
      (((synCcompl (Class.cab (nb068AlphaDummy167)
              (synWrex (nb068AlphaDummy168) (Class.cv (nb068AlphaDummy126))
                (Wff.classEq (Class.cv (nb068AlphaDummy167))
                  (synCphi (Class.cv (nb068AlphaDummy168)))))))).fv ∪ ((synCcompl
            (Class.cab (nb068AlphaDummy167)
              (synWrex (nb068AlphaDummy168) (Class.cv (nb068AlphaDummy125))
                (Wff.classEq (Class.cv (nb068AlphaDummy167))
                  (synCun (synCphi (Class.cv (nb068AlphaDummy168)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068AlphaDummy125) ≠ (nb068AlphaDummy167) from (by
          unfold nb068AlphaDummy167;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0192) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068AlphaDummy125) ≠ (nb068AlphaDummy168) from (by
            unfold nb068AlphaDummy168;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0192) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0194 (f : Var) :
    (nb068AlphaDummy127 f) ∈
      (((Class.cv (nb068AlphaDummy128 f))).fv ∪ ((Class.cv (nb068AlphaDummy127 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0195 (f : Var) :
    (nb068AlphaDummy127 f) ∈
      (((synCcompl (Class.cab (nb068AlphaDummy169 f)
              (synWrex (nb068AlphaDummy170 f) (Class.cv (nb068AlphaDummy128 f))
                (Wff.classEq (Class.cv (nb068AlphaDummy169 f))
                  (synCphi (Class.cv (nb068AlphaDummy170 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb068AlphaDummy169 f)
              (synWrex (nb068AlphaDummy170 f) (Class.cv (nb068AlphaDummy127 f))
                (Wff.classEq (Class.cv (nb068AlphaDummy169 f))
                  (synCun (synCphi (Class.cv (nb068AlphaDummy170 f)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068AlphaDummy127 f) ≠ (nb068AlphaDummy169 f) from (by
          unfold nb068AlphaDummy169;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0194 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068AlphaDummy127 f) ≠ (nb068AlphaDummy170 f) from (by
            unfold nb068AlphaDummy170;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0194 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0196 :
    (nb068AlphaDummy125) ∈
      (((Class.cab (nb068AlphaDummy167)
            (synWrex (nb068AlphaDummy168) (Class.cv (nb068AlphaDummy125))
              (Wff.classEq (Class.cv (nb068AlphaDummy167))
                (synCun (synCphi (Class.cv (nb068AlphaDummy168)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb068AlphaDummy167)
            (synWrex (nb068AlphaDummy168) (Class.cv (nb068AlphaDummy125))
              (Wff.classEq (Class.cv (nb068AlphaDummy167))
                (synCun (synCphi (Class.cv (nb068AlphaDummy168)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068AlphaDummy125) ≠ (nb068AlphaDummy167) from (by
          unfold nb068AlphaDummy167;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0192) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068AlphaDummy125) ≠ (nb068AlphaDummy168) from (by
            unfold nb068AlphaDummy168;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0192) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0197 (f : Var) :
    (nb068AlphaDummy127 f) ∈
      (((Class.cab (nb068AlphaDummy169 f)
            (synWrex (nb068AlphaDummy170 f) (Class.cv (nb068AlphaDummy127 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy169 f))
                (synCun (synCphi (Class.cv (nb068AlphaDummy170 f)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb068AlphaDummy169 f)
            (synWrex (nb068AlphaDummy170 f) (Class.cv (nb068AlphaDummy127 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy169 f))
                (synCun (synCphi (Class.cv (nb068AlphaDummy170 f)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068AlphaDummy127 f) ≠ (nb068AlphaDummy169 f) from (by
          unfold nb068AlphaDummy169;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0194 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068AlphaDummy127 f) ≠ (nb068AlphaDummy170 f) from (by
            unfold nb068AlphaDummy170;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0194 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0198 :
    (nb068AlphaDummy168) ∈
      (((synCcompl (synCphi (Class.cv (nb068AlphaDummy168))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0199 (f : Var) :
    (nb068AlphaDummy170 f) ∈
      (((synCcompl (synCphi (Class.cv (nb068AlphaDummy170 f))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0200 :
    (nb068AlphaDummy168) ∈
      (((synCphi (Class.cv (nb068AlphaDummy168)))).fv ∪
        ((synCphi (Class.cv (nb068AlphaDummy168)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0201 (f : Var) :
    (nb068AlphaDummy170 f) ∈
      (((synCphi (Class.cv (nb068AlphaDummy170 f)))).fv ∪
        ((synCphi (Class.cv (nb068AlphaDummy170 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0202 :
    (nb068AlphaDummy000) ∈
      (((synCnin (synCcom (Class.cv (nb068AlphaDummy000))
              (synCcnv (Class.cv (nb068AlphaDummy000)))) (synCid))).fv ∪ ((synCnin
            (synCcom (Class.cv (nb068AlphaDummy000))
              (synCcnv (Class.cv (nb068AlphaDummy000)))) (synCid))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccom]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0203 (f : Var) :
    f ∈
      (((synCnin (synCcom (Class.cv f) (synCcnv (Class.cv f))) (synCid))).fv ∪
        ((synCnin (synCcom (Class.cv f) (synCcnv (Class.cv f))) (synCid))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccom]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0204 :
    (nb068AlphaDummy000) ∈
      (((synCcom (Class.cv (nb068AlphaDummy000))
            (synCcnv (Class.cv (nb068AlphaDummy000))))).fv ∪ ((synCid)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccom]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0205 (f : Var) :
    f ∈ (((synCcom (Class.cv f) (synCcnv (Class.cv f)))).fv ∪ ((synCid)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccom]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0206 :
    (nb068AlphaDummy000) ∈
      (((Class.cv (nb068AlphaDummy000))).fv ∪
        ((synCcnv (Class.cv (nb068AlphaDummy000)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0207 :
    (nb068AlphaDummy000) ∈
      (({(nb068AlphaDummy045)} : Finset Var) ∪ ({(nb068AlphaDummy046)} : Finset Var) ∪
        ((synWex (nb068AlphaDummy047) (synWa (synWbr (Class.cv (nb068AlphaDummy045))
                (synCcnv (Class.cv (nb068AlphaDummy000)))
                (Class.cv (nb068AlphaDummy047))) (synWbr (Class.cv (nb068AlphaDummy047))
                (Class.cv (nb068AlphaDummy000)) (Class.cv (nb068AlphaDummy046)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_wex]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068AlphaDummy000) ≠ (nb068AlphaDummy047) from (by
          unfold nb068AlphaDummy047;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0206) 2))))
  · rw [fv_syn_wa]
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_syn_wbr]
    with_reducible rw [Finset.mem_union]
    right
    rw [fv_syn_ccnv]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _

theorem nb068_support_mem_0208 (f : Var) :
    f ∈ (((Class.cv f)).fv ∪ ((synCcnv (Class.cv f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0209 (f : Var) :
    f ∈
      (({(nb068AlphaDummy048 f)} : Finset Var) ∪ ({(nb068AlphaDummy049 f)} : Finset Var) ∪
        ((synWex (nb068AlphaDummy050 f) (synWa
              (synWbr (Class.cv (nb068AlphaDummy048 f)) (synCcnv (Class.cv f))
                (Class.cv (nb068AlphaDummy050 f)))
              (synWbr (Class.cv (nb068AlphaDummy050 f)) (Class.cv f)
                (Class.cv (nb068AlphaDummy049 f)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_wex]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show f ≠ (nb068AlphaDummy050 f) from (by
          unfold nb068AlphaDummy050;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0208 f) 2))))
  · rw [fv_syn_wa]
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_syn_wbr]
    with_reducible rw [Finset.mem_union]
    right
    rw [fv_syn_ccnv]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _

theorem nb068_support_mem_0210 :
    (nb068AlphaDummy000) ∈
      (({(nb068AlphaDummy125)} : Finset Var) ∪ ({(nb068AlphaDummy126)} : Finset Var) ∪
        ((synWbr (Class.cv (nb068AlphaDummy126)) (Class.cv (nb068AlphaDummy000))
            (Class.cv (nb068AlphaDummy125)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_wbr]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0211 (f : Var) :
    f ∈
      (({(nb068AlphaDummy127 f)} : Finset Var) ∪ ({(nb068AlphaDummy128 f)} : Finset Var) ∪
        ((synWbr (Class.cv (nb068AlphaDummy128 f)) (Class.cv f)
            (Class.cv (nb068AlphaDummy127 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_wbr]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0212 :
    (nb068AlphaDummy000) ∈ (((Class.cv (nb068AlphaDummy000))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0213 (f : Var) : f ∈ (((Class.cv f)).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0214 :
    (nb068AlphaDummy047) ∈
      (((Class.cv (nb068AlphaDummy047))).fv ∪ ((Class.cv (nb068AlphaDummy046))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C068C001Part011`. -/


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

theorem nb068_support_mem_0215 :
    (nb068AlphaDummy047) ∈
      (((synCcompl (Class.cab (nb068AlphaDummy203)
              (synWrex (nb068AlphaDummy204) (Class.cv (nb068AlphaDummy047))
                (Wff.classEq (Class.cv (nb068AlphaDummy203))
                  (synCphi (Class.cv (nb068AlphaDummy204)))))))).fv ∪ ((synCcompl
            (Class.cab (nb068AlphaDummy203)
              (synWrex (nb068AlphaDummy204) (Class.cv (nb068AlphaDummy046))
                (Wff.classEq (Class.cv (nb068AlphaDummy203))
                  (synCun (synCphi (Class.cv (nb068AlphaDummy204)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068AlphaDummy047) ≠ (nb068AlphaDummy203) from (by
          unfold nb068AlphaDummy203;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0214) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068AlphaDummy047) ≠ (nb068AlphaDummy204) from (by
            unfold nb068AlphaDummy204;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0214) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0216 (f : Var) :
    (nb068AlphaDummy050 f) ∈
      (((Class.cv (nb068AlphaDummy050 f))).fv ∪ ((Class.cv (nb068AlphaDummy049 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0217 (f : Var) :
    (nb068AlphaDummy050 f) ∈
      (((synCcompl (Class.cab (nb068AlphaDummy205 f)
              (synWrex (nb068AlphaDummy206 f) (Class.cv (nb068AlphaDummy050 f))
                (Wff.classEq (Class.cv (nb068AlphaDummy205 f))
                  (synCphi (Class.cv (nb068AlphaDummy206 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb068AlphaDummy205 f)
              (synWrex (nb068AlphaDummy206 f) (Class.cv (nb068AlphaDummy049 f))
                (Wff.classEq (Class.cv (nb068AlphaDummy205 f))
                  (synCun (synCphi (Class.cv (nb068AlphaDummy206 f)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068AlphaDummy050 f) ≠ (nb068AlphaDummy205 f) from (by
          unfold nb068AlphaDummy205;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0216 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068AlphaDummy050 f) ≠ (nb068AlphaDummy206 f) from (by
            unfold nb068AlphaDummy206;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0216 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0218 :
    (nb068AlphaDummy047) ∈
      (((Class.cab (nb068AlphaDummy203)
            (synWrex (nb068AlphaDummy204) (Class.cv (nb068AlphaDummy047))
              (Wff.classEq (Class.cv (nb068AlphaDummy203))
                (synCphi (Class.cv (nb068AlphaDummy204))))))).fv ∪
        ((Class.cab (nb068AlphaDummy203)
            (synWrex (nb068AlphaDummy204) (Class.cv (nb068AlphaDummy047))
              (Wff.classEq (Class.cv (nb068AlphaDummy203))
                (synCphi (Class.cv (nb068AlphaDummy204))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068AlphaDummy047) ≠ (nb068AlphaDummy203) from (by
          unfold nb068AlphaDummy203;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0214) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068AlphaDummy047) ≠ (nb068AlphaDummy204) from (by
            unfold nb068AlphaDummy204;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0214) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0219 (f : Var) :
    (nb068AlphaDummy050 f) ∈
      (((Class.cab (nb068AlphaDummy205 f)
            (synWrex (nb068AlphaDummy206 f) (Class.cv (nb068AlphaDummy050 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy205 f))
                (synCphi (Class.cv (nb068AlphaDummy206 f))))))).fv ∪
        ((Class.cab (nb068AlphaDummy205 f)
            (synWrex (nb068AlphaDummy206 f) (Class.cv (nb068AlphaDummy050 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy205 f))
                (synCphi (Class.cv (nb068AlphaDummy206 f))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068AlphaDummy050 f) ≠ (nb068AlphaDummy205 f) from (by
          unfold nb068AlphaDummy205;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0216 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068AlphaDummy050 f) ≠ (nb068AlphaDummy206 f) from (by
            unfold nb068AlphaDummy206;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0216 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0220 :
    (nb068AlphaDummy204) ∈ (((Class.cv (nb068AlphaDummy204))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0221 (f : Var) :
    (nb068AlphaDummy206 f) ∈ (((Class.cv (nb068AlphaDummy206 f))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0222 :
    (nb068AlphaDummy211) ∈
      (((Wff.classMem (Class.cv (nb068AlphaDummy211)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb068AlphaDummy211)) (synC1c))).fv ∪
        ((Class.cv (nb068AlphaDummy211))).fv) :=
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

theorem nb068_support_mem_0223 (f : Var) :
    (nb068AlphaDummy213 f) ∈
      (((Wff.classMem (Class.cv (nb068AlphaDummy213 f)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb068AlphaDummy213 f)) (synC1c))).fv ∪
        ((Class.cv (nb068AlphaDummy213 f))).fv) :=
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

theorem nb068_support_mem_0224 :
    (nb068AlphaDummy211) ∈
      (((Class.cv (nb068AlphaDummy211))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0225 (f : Var) :
    (nb068AlphaDummy213 f) ∈
      (((Class.cv (nb068AlphaDummy213 f))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0226 :
    (nb068AlphaDummy218) ∈
      (((synCnin (Class.cv (nb068AlphaDummy218)) (Class.cv (nb068AlphaDummy219)))).fv ∪
        ((synCnin (Class.cv (nb068AlphaDummy218))
            (Class.cv (nb068AlphaDummy219)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0227 (f : Var) :
    (nb068AlphaDummy221 f) ∈
      (((synCnin (Class.cv (nb068AlphaDummy221 f))
            (Class.cv (nb068AlphaDummy222 f)))).fv ∪
        ((synCnin (Class.cv (nb068AlphaDummy221 f))
            (Class.cv (nb068AlphaDummy222 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0228 :
    (nb068AlphaDummy218) ∈
      (((Class.cv (nb068AlphaDummy218))).fv ∪ ((Class.cv (nb068AlphaDummy219))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0229 (f : Var) :
    (nb068AlphaDummy221 f) ∈
      (((Class.cv (nb068AlphaDummy221 f))).fv ∪ ((Class.cv (nb068AlphaDummy222 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0230 :
    (nb068AlphaDummy219) ∈
      (((synCnin (Class.cv (nb068AlphaDummy218)) (Class.cv (nb068AlphaDummy219)))).fv ∪
        ((synCnin (Class.cv (nb068AlphaDummy218))
            (Class.cv (nb068AlphaDummy219)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0231 (f : Var) :
    (nb068AlphaDummy222 f) ∈
      (((synCnin (Class.cv (nb068AlphaDummy221 f))
            (Class.cv (nb068AlphaDummy222 f)))).fv ∪
        ((synCnin (Class.cv (nb068AlphaDummy221 f))
            (Class.cv (nb068AlphaDummy222 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0232 :
    (nb068AlphaDummy219) ∈
      (((Class.cv (nb068AlphaDummy218))).fv ∪ ((Class.cv (nb068AlphaDummy219))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0233 (f : Var) :
    (nb068AlphaDummy222 f) ∈
      (((Class.cv (nb068AlphaDummy221 f))).fv ∪ ((Class.cv (nb068AlphaDummy222 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0234 :
    (nb068AlphaDummy218) ∈
      (((synCcompl (Class.cv (nb068AlphaDummy218)))).fv ∪
        ((synCcompl (Class.cv (nb068AlphaDummy219)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0235 (f : Var) :
    (nb068AlphaDummy221 f) ∈
      (((synCcompl (Class.cv (nb068AlphaDummy221 f)))).fv ∪
        ((synCcompl (Class.cv (nb068AlphaDummy222 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0236 :
    (nb068AlphaDummy218) ∈
      (((Class.cv (nb068AlphaDummy218))).fv ∪ ((Class.cv (nb068AlphaDummy218))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0237 (f : Var) :
    (nb068AlphaDummy221 f) ∈
      (((Class.cv (nb068AlphaDummy221 f))).fv ∪ ((Class.cv (nb068AlphaDummy221 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0238 :
    (nb068AlphaDummy219) ∈
      (((synCcompl (Class.cv (nb068AlphaDummy218)))).fv ∪
        ((synCcompl (Class.cv (nb068AlphaDummy219)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0239 (f : Var) :
    (nb068AlphaDummy222 f) ∈
      (((synCcompl (Class.cv (nb068AlphaDummy221 f)))).fv ∪
        ((synCcompl (Class.cv (nb068AlphaDummy222 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0240 :
    (nb068AlphaDummy219) ∈
      (((Class.cv (nb068AlphaDummy219))).fv ∪ ((Class.cv (nb068AlphaDummy219))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0241 (f : Var) :
    (nb068AlphaDummy222 f) ∈
      (((Class.cv (nb068AlphaDummy222 f))).fv ∪ ((Class.cv (nb068AlphaDummy222 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0242 :
    (nb068AlphaDummy046) ∈
      (((Class.cv (nb068AlphaDummy047))).fv ∪ ((Class.cv (nb068AlphaDummy046))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0243 :
    (nb068AlphaDummy046) ∈
      (((synCcompl (Class.cab (nb068AlphaDummy203)
              (synWrex (nb068AlphaDummy204) (Class.cv (nb068AlphaDummy047))
                (Wff.classEq (Class.cv (nb068AlphaDummy203))
                  (synCphi (Class.cv (nb068AlphaDummy204)))))))).fv ∪ ((synCcompl
            (Class.cab (nb068AlphaDummy203)
              (synWrex (nb068AlphaDummy204) (Class.cv (nb068AlphaDummy046))
                (Wff.classEq (Class.cv (nb068AlphaDummy203))
                  (synCun (synCphi (Class.cv (nb068AlphaDummy204)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068AlphaDummy046) ≠ (nb068AlphaDummy203) from (by
          unfold nb068AlphaDummy203;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0242) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068AlphaDummy046) ≠ (nb068AlphaDummy204) from (by
            unfold nb068AlphaDummy204;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0242) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0244 (f : Var) :
    (nb068AlphaDummy049 f) ∈
      (((Class.cv (nb068AlphaDummy050 f))).fv ∪ ((Class.cv (nb068AlphaDummy049 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0245 (f : Var) :
    (nb068AlphaDummy049 f) ∈
      (((synCcompl (Class.cab (nb068AlphaDummy205 f)
              (synWrex (nb068AlphaDummy206 f) (Class.cv (nb068AlphaDummy050 f))
                (Wff.classEq (Class.cv (nb068AlphaDummy205 f))
                  (synCphi (Class.cv (nb068AlphaDummy206 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb068AlphaDummy205 f)
              (synWrex (nb068AlphaDummy206 f) (Class.cv (nb068AlphaDummy049 f))
                (Wff.classEq (Class.cv (nb068AlphaDummy205 f))
                  (synCun (synCphi (Class.cv (nb068AlphaDummy206 f)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068AlphaDummy049 f) ≠ (nb068AlphaDummy205 f) from (by
          unfold nb068AlphaDummy205;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0244 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068AlphaDummy049 f) ≠ (nb068AlphaDummy206 f) from (by
            unfold nb068AlphaDummy206;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0244 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0246 :
    (nb068AlphaDummy046) ∈
      (((Class.cab (nb068AlphaDummy203)
            (synWrex (nb068AlphaDummy204) (Class.cv (nb068AlphaDummy046))
              (Wff.classEq (Class.cv (nb068AlphaDummy203))
                (synCun (synCphi (Class.cv (nb068AlphaDummy204)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb068AlphaDummy203)
            (synWrex (nb068AlphaDummy204) (Class.cv (nb068AlphaDummy046))
              (Wff.classEq (Class.cv (nb068AlphaDummy203))
                (synCun (synCphi (Class.cv (nb068AlphaDummy204)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068AlphaDummy046) ≠ (nb068AlphaDummy203) from (by
          unfold nb068AlphaDummy203;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0242) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068AlphaDummy046) ≠ (nb068AlphaDummy204) from (by
            unfold nb068AlphaDummy204;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0242) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0247 (f : Var) :
    (nb068AlphaDummy049 f) ∈
      (((Class.cab (nb068AlphaDummy205 f)
            (synWrex (nb068AlphaDummy206 f) (Class.cv (nb068AlphaDummy049 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy205 f))
                (synCun (synCphi (Class.cv (nb068AlphaDummy206 f)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb068AlphaDummy205 f)
            (synWrex (nb068AlphaDummy206 f) (Class.cv (nb068AlphaDummy049 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy205 f))
                (synCun (synCphi (Class.cv (nb068AlphaDummy206 f)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068AlphaDummy049 f) ≠ (nb068AlphaDummy205 f) from (by
          unfold nb068AlphaDummy205;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0244 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068AlphaDummy049 f) ≠ (nb068AlphaDummy206 f) from (by
            unfold nb068AlphaDummy206;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0244 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0248 :
    (nb068AlphaDummy204) ∈
      (((synCcompl (synCphi (Class.cv (nb068AlphaDummy204))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0249 (f : Var) :
    (nb068AlphaDummy206 f) ∈
      (((synCcompl (synCphi (Class.cv (nb068AlphaDummy206 f))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0250 :
    (nb068AlphaDummy204) ∈
      (((synCphi (Class.cv (nb068AlphaDummy204)))).fv ∪
        ((synCphi (Class.cv (nb068AlphaDummy204)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0251 (f : Var) :
    (nb068AlphaDummy206 f) ∈
      (((synCphi (Class.cv (nb068AlphaDummy206 f)))).fv ∪
        ((synCphi (Class.cv (nb068AlphaDummy206 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0252 :
    (nb068AlphaDummy240) ∈
      (((Class.cv (nb068AlphaDummy240))).fv ∪ ((Class.cv (nb068AlphaDummy239))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0253 :
    (nb068AlphaDummy240) ∈
      (((synCcompl (Class.cab (nb068AlphaDummy243)
              (synWrex (nb068AlphaDummy244) (Class.cv (nb068AlphaDummy240))
                (Wff.classEq (Class.cv (nb068AlphaDummy243))
                  (synCphi (Class.cv (nb068AlphaDummy244)))))))).fv ∪ ((synCcompl
            (Class.cab (nb068AlphaDummy243)
              (synWrex (nb068AlphaDummy244) (Class.cv (nb068AlphaDummy239))
                (Wff.classEq (Class.cv (nb068AlphaDummy243))
                  (synCun (synCphi (Class.cv (nb068AlphaDummy244)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068AlphaDummy240) ≠ (nb068AlphaDummy243) from (by
          unfold nb068AlphaDummy243;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0252) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068AlphaDummy240) ≠ (nb068AlphaDummy244) from (by
            unfold nb068AlphaDummy244;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0252) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0254 (f : Var) :
    (nb068AlphaDummy242 f) ∈
      (((Class.cv (nb068AlphaDummy242 f))).fv ∪ ((Class.cv (nb068AlphaDummy241 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0255 (f : Var) :
    (nb068AlphaDummy242 f) ∈
      (((synCcompl (Class.cab (nb068AlphaDummy245 f)
              (synWrex (nb068AlphaDummy246 f) (Class.cv (nb068AlphaDummy242 f))
                (Wff.classEq (Class.cv (nb068AlphaDummy245 f))
                  (synCphi (Class.cv (nb068AlphaDummy246 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb068AlphaDummy245 f)
              (synWrex (nb068AlphaDummy246 f) (Class.cv (nb068AlphaDummy241 f))
                (Wff.classEq (Class.cv (nb068AlphaDummy245 f))
                  (synCun (synCphi (Class.cv (nb068AlphaDummy246 f)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068AlphaDummy242 f) ≠ (nb068AlphaDummy245 f) from (by
          unfold nb068AlphaDummy245;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0254 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068AlphaDummy242 f) ≠ (nb068AlphaDummy246 f) from (by
            unfold nb068AlphaDummy246;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0254 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0256 :
    (nb068AlphaDummy240) ∈
      (((Class.cab (nb068AlphaDummy243)
            (synWrex (nb068AlphaDummy244) (Class.cv (nb068AlphaDummy240))
              (Wff.classEq (Class.cv (nb068AlphaDummy243))
                (synCphi (Class.cv (nb068AlphaDummy244))))))).fv ∪
        ((Class.cab (nb068AlphaDummy243)
            (synWrex (nb068AlphaDummy244) (Class.cv (nb068AlphaDummy240))
              (Wff.classEq (Class.cv (nb068AlphaDummy243))
                (synCphi (Class.cv (nb068AlphaDummy244))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068AlphaDummy240) ≠ (nb068AlphaDummy243) from (by
          unfold nb068AlphaDummy243;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0252) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068AlphaDummy240) ≠ (nb068AlphaDummy244) from (by
            unfold nb068AlphaDummy244;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0252) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0257 (f : Var) :
    (nb068AlphaDummy242 f) ∈
      (((Class.cab (nb068AlphaDummy245 f)
            (synWrex (nb068AlphaDummy246 f) (Class.cv (nb068AlphaDummy242 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy245 f))
                (synCphi (Class.cv (nb068AlphaDummy246 f))))))).fv ∪
        ((Class.cab (nb068AlphaDummy245 f)
            (synWrex (nb068AlphaDummy246 f) (Class.cv (nb068AlphaDummy242 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy245 f))
                (synCphi (Class.cv (nb068AlphaDummy246 f))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068AlphaDummy242 f) ≠ (nb068AlphaDummy245 f) from (by
          unfold nb068AlphaDummy245;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0254 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068AlphaDummy242 f) ≠ (nb068AlphaDummy246 f) from (by
            unfold nb068AlphaDummy246;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0254 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0258 :
    (nb068AlphaDummy244) ∈ (((Class.cv (nb068AlphaDummy244))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0259 (f : Var) :
    (nb068AlphaDummy246 f) ∈ (((Class.cv (nb068AlphaDummy246 f))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0260 :
    (nb068AlphaDummy251) ∈
      (((Wff.classMem (Class.cv (nb068AlphaDummy251)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb068AlphaDummy251)) (synC1c))).fv ∪
        ((Class.cv (nb068AlphaDummy251))).fv) :=
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

theorem nb068_support_mem_0261 (f : Var) :
    (nb068AlphaDummy253 f) ∈
      (((Wff.classMem (Class.cv (nb068AlphaDummy253 f)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb068AlphaDummy253 f)) (synC1c))).fv ∪
        ((Class.cv (nb068AlphaDummy253 f))).fv) :=
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

theorem nb068_support_mem_0262 :
    (nb068AlphaDummy251) ∈
      (((Class.cv (nb068AlphaDummy251))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0263 (f : Var) :
    (nb068AlphaDummy253 f) ∈
      (((Class.cv (nb068AlphaDummy253 f))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0264 :
    (nb068AlphaDummy258) ∈
      (((synCnin (Class.cv (nb068AlphaDummy258)) (Class.cv (nb068AlphaDummy259)))).fv ∪
        ((synCnin (Class.cv (nb068AlphaDummy258))
            (Class.cv (nb068AlphaDummy259)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0265 (f : Var) :
    (nb068AlphaDummy261 f) ∈
      (((synCnin (Class.cv (nb068AlphaDummy261 f))
            (Class.cv (nb068AlphaDummy262 f)))).fv ∪
        ((synCnin (Class.cv (nb068AlphaDummy261 f))
            (Class.cv (nb068AlphaDummy262 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0266 :
    (nb068AlphaDummy258) ∈
      (((Class.cv (nb068AlphaDummy258))).fv ∪ ((Class.cv (nb068AlphaDummy259))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0267 (f : Var) :
    (nb068AlphaDummy261 f) ∈
      (((Class.cv (nb068AlphaDummy261 f))).fv ∪ ((Class.cv (nb068AlphaDummy262 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0268 :
    (nb068AlphaDummy259) ∈
      (((synCnin (Class.cv (nb068AlphaDummy258)) (Class.cv (nb068AlphaDummy259)))).fv ∪
        ((synCnin (Class.cv (nb068AlphaDummy258))
            (Class.cv (nb068AlphaDummy259)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0269 (f : Var) :
    (nb068AlphaDummy262 f) ∈
      (((synCnin (Class.cv (nb068AlphaDummy261 f))
            (Class.cv (nb068AlphaDummy262 f)))).fv ∪
        ((synCnin (Class.cv (nb068AlphaDummy261 f))
            (Class.cv (nb068AlphaDummy262 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0270 :
    (nb068AlphaDummy259) ∈
      (((Class.cv (nb068AlphaDummy258))).fv ∪ ((Class.cv (nb068AlphaDummy259))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0271 (f : Var) :
    (nb068AlphaDummy262 f) ∈
      (((Class.cv (nb068AlphaDummy261 f))).fv ∪ ((Class.cv (nb068AlphaDummy262 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0272 :
    (nb068AlphaDummy258) ∈
      (((synCcompl (Class.cv (nb068AlphaDummy258)))).fv ∪
        ((synCcompl (Class.cv (nb068AlphaDummy259)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0273 (f : Var) :
    (nb068AlphaDummy261 f) ∈
      (((synCcompl (Class.cv (nb068AlphaDummy261 f)))).fv ∪
        ((synCcompl (Class.cv (nb068AlphaDummy262 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0274 :
    (nb068AlphaDummy258) ∈
      (((Class.cv (nb068AlphaDummy258))).fv ∪ ((Class.cv (nb068AlphaDummy258))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0275 (f : Var) :
    (nb068AlphaDummy261 f) ∈
      (((Class.cv (nb068AlphaDummy261 f))).fv ∪ ((Class.cv (nb068AlphaDummy261 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0276 :
    (nb068AlphaDummy259) ∈
      (((synCcompl (Class.cv (nb068AlphaDummy258)))).fv ∪
        ((synCcompl (Class.cv (nb068AlphaDummy259)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0277 (f : Var) :
    (nb068AlphaDummy262 f) ∈
      (((synCcompl (Class.cv (nb068AlphaDummy261 f)))).fv ∪
        ((synCcompl (Class.cv (nb068AlphaDummy262 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0278 :
    (nb068AlphaDummy259) ∈
      (((Class.cv (nb068AlphaDummy259))).fv ∪ ((Class.cv (nb068AlphaDummy259))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0279 (f : Var) :
    (nb068AlphaDummy262 f) ∈
      (((Class.cv (nb068AlphaDummy262 f))).fv ∪ ((Class.cv (nb068AlphaDummy262 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0280 :
    (nb068AlphaDummy239) ∈
      (((Class.cv (nb068AlphaDummy240))).fv ∪ ((Class.cv (nb068AlphaDummy239))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0281 :
    (nb068AlphaDummy239) ∈
      (((synCcompl (Class.cab (nb068AlphaDummy243)
              (synWrex (nb068AlphaDummy244) (Class.cv (nb068AlphaDummy240))
                (Wff.classEq (Class.cv (nb068AlphaDummy243))
                  (synCphi (Class.cv (nb068AlphaDummy244)))))))).fv ∪ ((synCcompl
            (Class.cab (nb068AlphaDummy243)
              (synWrex (nb068AlphaDummy244) (Class.cv (nb068AlphaDummy239))
                (Wff.classEq (Class.cv (nb068AlphaDummy243))
                  (synCun (synCphi (Class.cv (nb068AlphaDummy244)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068AlphaDummy239) ≠ (nb068AlphaDummy243) from (by
          unfold nb068AlphaDummy243;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0280) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068AlphaDummy239) ≠ (nb068AlphaDummy244) from (by
            unfold nb068AlphaDummy244;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0280) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0282 (f : Var) :
    (nb068AlphaDummy241 f) ∈
      (((Class.cv (nb068AlphaDummy242 f))).fv ∪ ((Class.cv (nb068AlphaDummy241 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0283 (f : Var) :
    (nb068AlphaDummy241 f) ∈
      (((synCcompl (Class.cab (nb068AlphaDummy245 f)
              (synWrex (nb068AlphaDummy246 f) (Class.cv (nb068AlphaDummy242 f))
                (Wff.classEq (Class.cv (nb068AlphaDummy245 f))
                  (synCphi (Class.cv (nb068AlphaDummy246 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb068AlphaDummy245 f)
              (synWrex (nb068AlphaDummy246 f) (Class.cv (nb068AlphaDummy241 f))
                (Wff.classEq (Class.cv (nb068AlphaDummy245 f))
                  (synCun (synCphi (Class.cv (nb068AlphaDummy246 f)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068AlphaDummy241 f) ≠ (nb068AlphaDummy245 f) from (by
          unfold nb068AlphaDummy245;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0282 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068AlphaDummy241 f) ≠ (nb068AlphaDummy246 f) from (by
            unfold nb068AlphaDummy246;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0282 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0284 :
    (nb068AlphaDummy239) ∈
      (((Class.cab (nb068AlphaDummy243)
            (synWrex (nb068AlphaDummy244) (Class.cv (nb068AlphaDummy239))
              (Wff.classEq (Class.cv (nb068AlphaDummy243))
                (synCun (synCphi (Class.cv (nb068AlphaDummy244)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb068AlphaDummy243)
            (synWrex (nb068AlphaDummy244) (Class.cv (nb068AlphaDummy239))
              (Wff.classEq (Class.cv (nb068AlphaDummy243))
                (synCun (synCphi (Class.cv (nb068AlphaDummy244)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068AlphaDummy239) ≠ (nb068AlphaDummy243) from (by
          unfold nb068AlphaDummy243;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0280) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068AlphaDummy239) ≠ (nb068AlphaDummy244) from (by
            unfold nb068AlphaDummy244;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0280) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0285 (f : Var) :
    (nb068AlphaDummy241 f) ∈
      (((Class.cab (nb068AlphaDummy245 f)
            (synWrex (nb068AlphaDummy246 f) (Class.cv (nb068AlphaDummy241 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy245 f))
                (synCun (synCphi (Class.cv (nb068AlphaDummy246 f)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb068AlphaDummy245 f)
            (synWrex (nb068AlphaDummy246 f) (Class.cv (nb068AlphaDummy241 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy245 f))
                (synCun (synCphi (Class.cv (nb068AlphaDummy246 f)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068AlphaDummy241 f) ≠ (nb068AlphaDummy245 f) from (by
          unfold nb068AlphaDummy245;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0282 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068AlphaDummy241 f) ≠ (nb068AlphaDummy246 f) from (by
            unfold nb068AlphaDummy246;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0282 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0286 :
    (nb068AlphaDummy244) ∈
      (((synCcompl (synCphi (Class.cv (nb068AlphaDummy244))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0287 (f : Var) :
    (nb068AlphaDummy246 f) ∈
      (((synCcompl (synCphi (Class.cv (nb068AlphaDummy246 f))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0288 :
    (nb068AlphaDummy244) ∈
      (((synCphi (Class.cv (nb068AlphaDummy244)))).fv ∪
        ((synCphi (Class.cv (nb068AlphaDummy244)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0289 (f : Var) :
    (nb068AlphaDummy246 f) ∈
      (((synCphi (Class.cv (nb068AlphaDummy246 f)))).fv ∪
        ((synCphi (Class.cv (nb068AlphaDummy246 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0290 :
    (nb068AlphaDummy000) ∈
      (((synCcnv (Class.cv (nb068AlphaDummy000)))).fv ∪ ((synCvv)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccnv]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0291 (f : Var) :
    f ∈ (((synCcnv (Class.cv f))).fv ∪ ((synCvv)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccnv]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0292 :
    (nb068AlphaDummy284) ∈
      (((Class.cv (nb068AlphaDummy284))).fv ∪ ((Class.cv (nb068AlphaDummy283))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0293 :
    (nb068AlphaDummy284) ∈
      (((synCcompl (Class.cab (nb068AlphaDummy287)
              (synWrex (nb068AlphaDummy288) (Class.cv (nb068AlphaDummy284))
                (Wff.classEq (Class.cv (nb068AlphaDummy287))
                  (synCphi (Class.cv (nb068AlphaDummy288)))))))).fv ∪ ((synCcompl
            (Class.cab (nb068AlphaDummy287)
              (synWrex (nb068AlphaDummy288) (Class.cv (nb068AlphaDummy283))
                (Wff.classEq (Class.cv (nb068AlphaDummy287))
                  (synCun (synCphi (Class.cv (nb068AlphaDummy288)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068AlphaDummy284) ≠ (nb068AlphaDummy287) from (by
          unfold nb068AlphaDummy287;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0292) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068AlphaDummy284) ≠ (nb068AlphaDummy288) from (by
            unfold nb068AlphaDummy288;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0292) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0294 (f : Var) :
    (nb068AlphaDummy286 f) ∈
      (((Class.cv (nb068AlphaDummy286 f))).fv ∪ ((Class.cv (nb068AlphaDummy285 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0295 (f : Var) :
    (nb068AlphaDummy286 f) ∈
      (((synCcompl (Class.cab (nb068AlphaDummy289 f)
              (synWrex (nb068AlphaDummy290 f) (Class.cv (nb068AlphaDummy286 f))
                (Wff.classEq (Class.cv (nb068AlphaDummy289 f))
                  (synCphi (Class.cv (nb068AlphaDummy290 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb068AlphaDummy289 f)
              (synWrex (nb068AlphaDummy290 f) (Class.cv (nb068AlphaDummy285 f))
                (Wff.classEq (Class.cv (nb068AlphaDummy289 f))
                  (synCun (synCphi (Class.cv (nb068AlphaDummy290 f)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068AlphaDummy286 f) ≠ (nb068AlphaDummy289 f) from (by
          unfold nb068AlphaDummy289;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0294 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068AlphaDummy286 f) ≠ (nb068AlphaDummy290 f) from (by
            unfold nb068AlphaDummy290;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0294 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0296 :
    (nb068AlphaDummy284) ∈
      (((Class.cab (nb068AlphaDummy287)
            (synWrex (nb068AlphaDummy288) (Class.cv (nb068AlphaDummy284))
              (Wff.classEq (Class.cv (nb068AlphaDummy287))
                (synCphi (Class.cv (nb068AlphaDummy288))))))).fv ∪
        ((Class.cab (nb068AlphaDummy287)
            (synWrex (nb068AlphaDummy288) (Class.cv (nb068AlphaDummy284))
              (Wff.classEq (Class.cv (nb068AlphaDummy287))
                (synCphi (Class.cv (nb068AlphaDummy288))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068AlphaDummy284) ≠ (nb068AlphaDummy287) from (by
          unfold nb068AlphaDummy287;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0292) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068AlphaDummy284) ≠ (nb068AlphaDummy288) from (by
            unfold nb068AlphaDummy288;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0292) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0297 (f : Var) :
    (nb068AlphaDummy286 f) ∈
      (((Class.cab (nb068AlphaDummy289 f)
            (synWrex (nb068AlphaDummy290 f) (Class.cv (nb068AlphaDummy286 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy289 f))
                (synCphi (Class.cv (nb068AlphaDummy290 f))))))).fv ∪
        ((Class.cab (nb068AlphaDummy289 f)
            (synWrex (nb068AlphaDummy290 f) (Class.cv (nb068AlphaDummy286 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy289 f))
                (synCphi (Class.cv (nb068AlphaDummy290 f))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068AlphaDummy286 f) ≠ (nb068AlphaDummy289 f) from (by
          unfold nb068AlphaDummy289;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0294 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068AlphaDummy286 f) ≠ (nb068AlphaDummy290 f) from (by
            unfold nb068AlphaDummy290;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0294 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0298 :
    (nb068AlphaDummy288) ∈ (((Class.cv (nb068AlphaDummy288))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0299 (f : Var) :
    (nb068AlphaDummy290 f) ∈ (((Class.cv (nb068AlphaDummy290 f))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0300 :
    (nb068AlphaDummy295) ∈
      (((Wff.classMem (Class.cv (nb068AlphaDummy295)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb068AlphaDummy295)) (synC1c))).fv ∪
        ((Class.cv (nb068AlphaDummy295))).fv) :=
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

theorem nb068_support_mem_0301 (f : Var) :
    (nb068AlphaDummy297 f) ∈
      (((Wff.classMem (Class.cv (nb068AlphaDummy297 f)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb068AlphaDummy297 f)) (synC1c))).fv ∪
        ((Class.cv (nb068AlphaDummy297 f))).fv) :=
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

theorem nb068_support_mem_0302 :
    (nb068AlphaDummy295) ∈
      (((Class.cv (nb068AlphaDummy295))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0303 (f : Var) :
    (nb068AlphaDummy297 f) ∈
      (((Class.cv (nb068AlphaDummy297 f))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0304 :
    (nb068AlphaDummy302) ∈
      (((synCnin (Class.cv (nb068AlphaDummy302)) (Class.cv (nb068AlphaDummy303)))).fv ∪
        ((synCnin (Class.cv (nb068AlphaDummy302))
            (Class.cv (nb068AlphaDummy303)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0305 (f : Var) :
    (nb068AlphaDummy305 f) ∈
      (((synCnin (Class.cv (nb068AlphaDummy305 f))
            (Class.cv (nb068AlphaDummy306 f)))).fv ∪
        ((synCnin (Class.cv (nb068AlphaDummy305 f))
            (Class.cv (nb068AlphaDummy306 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0306 :
    (nb068AlphaDummy302) ∈
      (((Class.cv (nb068AlphaDummy302))).fv ∪ ((Class.cv (nb068AlphaDummy303))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0307 (f : Var) :
    (nb068AlphaDummy305 f) ∈
      (((Class.cv (nb068AlphaDummy305 f))).fv ∪ ((Class.cv (nb068AlphaDummy306 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0308 :
    (nb068AlphaDummy303) ∈
      (((synCnin (Class.cv (nb068AlphaDummy302)) (Class.cv (nb068AlphaDummy303)))).fv ∪
        ((synCnin (Class.cv (nb068AlphaDummy302))
            (Class.cv (nb068AlphaDummy303)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0309 (f : Var) :
    (nb068AlphaDummy306 f) ∈
      (((synCnin (Class.cv (nb068AlphaDummy305 f))
            (Class.cv (nb068AlphaDummy306 f)))).fv ∪
        ((synCnin (Class.cv (nb068AlphaDummy305 f))
            (Class.cv (nb068AlphaDummy306 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0310 :
    (nb068AlphaDummy303) ∈
      (((Class.cv (nb068AlphaDummy302))).fv ∪ ((Class.cv (nb068AlphaDummy303))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0311 (f : Var) :
    (nb068AlphaDummy306 f) ∈
      (((Class.cv (nb068AlphaDummy305 f))).fv ∪ ((Class.cv (nb068AlphaDummy306 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0312 :
    (nb068AlphaDummy302) ∈
      (((synCcompl (Class.cv (nb068AlphaDummy302)))).fv ∪
        ((synCcompl (Class.cv (nb068AlphaDummy303)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0313 (f : Var) :
    (nb068AlphaDummy305 f) ∈
      (((synCcompl (Class.cv (nb068AlphaDummy305 f)))).fv ∪
        ((synCcompl (Class.cv (nb068AlphaDummy306 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0314 :
    (nb068AlphaDummy302) ∈
      (((Class.cv (nb068AlphaDummy302))).fv ∪ ((Class.cv (nb068AlphaDummy302))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0315 (f : Var) :
    (nb068AlphaDummy305 f) ∈
      (((Class.cv (nb068AlphaDummy305 f))).fv ∪ ((Class.cv (nb068AlphaDummy305 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0316 :
    (nb068AlphaDummy303) ∈
      (((synCcompl (Class.cv (nb068AlphaDummy302)))).fv ∪
        ((synCcompl (Class.cv (nb068AlphaDummy303)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0317 (f : Var) :
    (nb068AlphaDummy306 f) ∈
      (((synCcompl (Class.cv (nb068AlphaDummy305 f)))).fv ∪
        ((synCcompl (Class.cv (nb068AlphaDummy306 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0318 :
    (nb068AlphaDummy303) ∈
      (((Class.cv (nb068AlphaDummy303))).fv ∪ ((Class.cv (nb068AlphaDummy303))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0319 (f : Var) :
    (nb068AlphaDummy306 f) ∈
      (((Class.cv (nb068AlphaDummy306 f))).fv ∪ ((Class.cv (nb068AlphaDummy306 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0320 :
    (nb068AlphaDummy283) ∈
      (((Class.cv (nb068AlphaDummy284))).fv ∪ ((Class.cv (nb068AlphaDummy283))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0321 :
    (nb068AlphaDummy283) ∈
      (((synCcompl (Class.cab (nb068AlphaDummy287)
              (synWrex (nb068AlphaDummy288) (Class.cv (nb068AlphaDummy284))
                (Wff.classEq (Class.cv (nb068AlphaDummy287))
                  (synCphi (Class.cv (nb068AlphaDummy288)))))))).fv ∪ ((synCcompl
            (Class.cab (nb068AlphaDummy287)
              (synWrex (nb068AlphaDummy288) (Class.cv (nb068AlphaDummy283))
                (Wff.classEq (Class.cv (nb068AlphaDummy287))
                  (synCun (synCphi (Class.cv (nb068AlphaDummy288)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068AlphaDummy283) ≠ (nb068AlphaDummy287) from (by
          unfold nb068AlphaDummy287;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0320) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068AlphaDummy283) ≠ (nb068AlphaDummy288) from (by
            unfold nb068AlphaDummy288;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0320) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0322 (f : Var) :
    (nb068AlphaDummy285 f) ∈
      (((Class.cv (nb068AlphaDummy286 f))).fv ∪ ((Class.cv (nb068AlphaDummy285 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0323 (f : Var) :
    (nb068AlphaDummy285 f) ∈
      (((synCcompl (Class.cab (nb068AlphaDummy289 f)
              (synWrex (nb068AlphaDummy290 f) (Class.cv (nb068AlphaDummy286 f))
                (Wff.classEq (Class.cv (nb068AlphaDummy289 f))
                  (synCphi (Class.cv (nb068AlphaDummy290 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb068AlphaDummy289 f)
              (synWrex (nb068AlphaDummy290 f) (Class.cv (nb068AlphaDummy285 f))
                (Wff.classEq (Class.cv (nb068AlphaDummy289 f))
                  (synCun (synCphi (Class.cv (nb068AlphaDummy290 f)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068AlphaDummy285 f) ≠ (nb068AlphaDummy289 f) from (by
          unfold nb068AlphaDummy289;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0322 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068AlphaDummy285 f) ≠ (nb068AlphaDummy290 f) from (by
            unfold nb068AlphaDummy290;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0322 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0324 :
    (nb068AlphaDummy283) ∈
      (((Class.cab (nb068AlphaDummy287)
            (synWrex (nb068AlphaDummy288) (Class.cv (nb068AlphaDummy283))
              (Wff.classEq (Class.cv (nb068AlphaDummy287))
                (synCun (synCphi (Class.cv (nb068AlphaDummy288)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb068AlphaDummy287)
            (synWrex (nb068AlphaDummy288) (Class.cv (nb068AlphaDummy283))
              (Wff.classEq (Class.cv (nb068AlphaDummy287))
                (synCun (synCphi (Class.cv (nb068AlphaDummy288)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068AlphaDummy283) ≠ (nb068AlphaDummy287) from (by
          unfold nb068AlphaDummy287;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0320) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068AlphaDummy283) ≠ (nb068AlphaDummy288) from (by
            unfold nb068AlphaDummy288;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0320) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0325 (f : Var) :
    (nb068AlphaDummy285 f) ∈
      (((Class.cab (nb068AlphaDummy289 f)
            (synWrex (nb068AlphaDummy290 f) (Class.cv (nb068AlphaDummy285 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy289 f))
                (synCun (synCphi (Class.cv (nb068AlphaDummy290 f)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb068AlphaDummy289 f)
            (synWrex (nb068AlphaDummy290 f) (Class.cv (nb068AlphaDummy285 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy289 f))
                (synCun (synCphi (Class.cv (nb068AlphaDummy290 f)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068AlphaDummy285 f) ≠ (nb068AlphaDummy289 f) from (by
          unfold nb068AlphaDummy289;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0322 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068AlphaDummy285 f) ≠ (nb068AlphaDummy290 f) from (by
            unfold nb068AlphaDummy290;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0322 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0326 :
    (nb068AlphaDummy288) ∈
      (((synCcompl (synCphi (Class.cv (nb068AlphaDummy288))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0327 (f : Var) :
    (nb068AlphaDummy290 f) ∈
      (((synCcompl (synCphi (Class.cv (nb068AlphaDummy290 f))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0328 :
    (nb068AlphaDummy288) ∈
      (((synCphi (Class.cv (nb068AlphaDummy288)))).fv ∪
        ((synCphi (Class.cv (nb068AlphaDummy288)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0329 (f : Var) :
    (nb068AlphaDummy290 f) ∈
      (((synCphi (Class.cv (nb068AlphaDummy290 f)))).fv ∪
        ((synCphi (Class.cv (nb068AlphaDummy290 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0330 :
    (nb068AlphaDummy000) ∈
      (((synCnin (synCrn (Class.cv (nb068AlphaDummy000)))
            (Class.cv (nb068AlphaDummy002)))).fv ∪
        ((synCnin (synCrn (Class.cv (nb068AlphaDummy000)))
            (Class.cv (nb068AlphaDummy002)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_crn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0331 (y : Var) (f : Var) :
    f ∈
      (((synCnin (synCrn (Class.cv f)) (Class.cv y))).fv ∪
        ((synCnin (synCrn (Class.cv f)) (Class.cv y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_crn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0332 :
    (nb068AlphaDummy000) ∈
      (((synCrn (Class.cv (nb068AlphaDummy000)))).fv ∪
        ((Class.cv (nb068AlphaDummy002))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_crn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0333 (y : Var) (f : Var) :
    f ∈ (((synCrn (Class.cv f))).fv ∪ ((Class.cv y)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_crn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0334 :
    (nb068AlphaDummy000) ∈
      (((Class.cv (nb068AlphaDummy000))).fv ∪ ((synCvv)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0335 (f : Var) : f ∈ (((Class.cv f)).fv ∪ ((synCvv)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0336 :
    (nb068AlphaDummy002) ∈
      (((synCnin (synCrn (Class.cv (nb068AlphaDummy000)))
            (Class.cv (nb068AlphaDummy002)))).fv ∪
        ((synCnin (synCrn (Class.cv (nb068AlphaDummy000)))
            (Class.cv (nb068AlphaDummy002)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0337 (y : Var) (f : Var) :
    y ∈
      (((synCnin (synCrn (Class.cv f)) (Class.cv y))).fv ∪
        ((synCnin (synCrn (Class.cv f)) (Class.cv y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0338 :
    (nb068AlphaDummy002) ∈
      (((synCrn (Class.cv (nb068AlphaDummy000)))).fv ∪
        ((Class.cv (nb068AlphaDummy002))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0339 (y : Var) (f : Var) :
    y ∈ (((synCrn (Class.cv f))).fv ∪ ((Class.cv y)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0340 :
    (nb068AlphaDummy327) ∈
      (({(nb068AlphaDummy327)} : Finset Var) ∪ ({(nb068AlphaDummy328)} : Finset Var) ∪
        ((synWex (nb068AlphaDummy329) (synWa (synWbr (Class.cv (nb068AlphaDummy327))
                (synCcnv (synCcnv (Class.cv (nb068AlphaDummy000))))
                (Class.cv (nb068AlphaDummy329))) (synWbr (Class.cv (nb068AlphaDummy329))
                (synCcnv (Class.cv (nb068AlphaDummy000)))
                (Class.cv (nb068AlphaDummy328)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0341 (f : Var) :
    (nb068AlphaDummy330 f) ∈
      (({(nb068AlphaDummy330 f)} : Finset Var) ∪ ({(nb068AlphaDummy331 f)} : Finset Var) ∪
        ((synWex (nb068AlphaDummy332 f) (synWa
              (synWbr (Class.cv (nb068AlphaDummy330 f))
                (synCcnv (synCcnv (Class.cv f))) (Class.cv (nb068AlphaDummy332 f)))
              (synWbr (Class.cv (nb068AlphaDummy332 f)) (synCcnv (Class.cv f))
                (Class.cv (nb068AlphaDummy331 f)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0342 :
    (nb068AlphaDummy328) ∈
      (({(nb068AlphaDummy327)} : Finset Var) ∪ ({(nb068AlphaDummy328)} : Finset Var) ∪
        ((synWex (nb068AlphaDummy329) (synWa (synWbr (Class.cv (nb068AlphaDummy327))
                (synCcnv (synCcnv (Class.cv (nb068AlphaDummy000))))
                (Class.cv (nb068AlphaDummy329))) (synWbr (Class.cv (nb068AlphaDummy329))
                (synCcnv (Class.cv (nb068AlphaDummy000)))
                (Class.cv (nb068AlphaDummy328)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0343 (f : Var) :
    (nb068AlphaDummy331 f) ∈
      (({(nb068AlphaDummy330 f)} : Finset Var) ∪ ({(nb068AlphaDummy331 f)} : Finset Var) ∪
        ((synWex (nb068AlphaDummy332 f) (synWa
              (synWbr (Class.cv (nb068AlphaDummy330 f))
                (synCcnv (synCcnv (Class.cv f))) (Class.cv (nb068AlphaDummy332 f)))
              (synWbr (Class.cv (nb068AlphaDummy332 f)) (synCcnv (Class.cv f))
                (Class.cv (nb068AlphaDummy331 f)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0344 :
    (nb068AlphaDummy327) ∈
      (((Class.cv (nb068AlphaDummy327))).fv ∪ ((Class.cv (nb068AlphaDummy328))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0345 :
    (nb068AlphaDummy327) ∈
      (((synCcompl (Class.cab (nb068AlphaDummy335)
              (synWrex (nb068AlphaDummy336) (Class.cv (nb068AlphaDummy327))
                (Wff.classEq (Class.cv (nb068AlphaDummy335))
                  (synCphi (Class.cv (nb068AlphaDummy336)))))))).fv ∪ ((synCcompl
            (Class.cab (nb068AlphaDummy335)
              (synWrex (nb068AlphaDummy336) (Class.cv (nb068AlphaDummy328))
                (Wff.classEq (Class.cv (nb068AlphaDummy335))
                  (synCun (synCphi (Class.cv (nb068AlphaDummy336)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068AlphaDummy327) ≠ (nb068AlphaDummy335) from (by
          unfold nb068AlphaDummy335;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0344) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068AlphaDummy327) ≠ (nb068AlphaDummy336) from (by
            unfold nb068AlphaDummy336;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0344) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0346 (f : Var) :
    (nb068AlphaDummy330 f) ∈
      (((Class.cv (nb068AlphaDummy330 f))).fv ∪ ((Class.cv (nb068AlphaDummy331 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0347 (f : Var) :
    (nb068AlphaDummy330 f) ∈
      (((synCcompl (Class.cab (nb068AlphaDummy337 f)
              (synWrex (nb068AlphaDummy338 f) (Class.cv (nb068AlphaDummy330 f))
                (Wff.classEq (Class.cv (nb068AlphaDummy337 f))
                  (synCphi (Class.cv (nb068AlphaDummy338 f)))))))).fv ∪ ((synCcompl
            (Class.cab (nb068AlphaDummy337 f)
              (synWrex (nb068AlphaDummy338 f) (Class.cv (nb068AlphaDummy331 f))
                (Wff.classEq (Class.cv (nb068AlphaDummy337 f))
                  (synCun (synCphi (Class.cv (nb068AlphaDummy338 f)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068AlphaDummy330 f) ≠ (nb068AlphaDummy337 f) from (by
          unfold nb068AlphaDummy337;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0346 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068AlphaDummy330 f) ≠ (nb068AlphaDummy338 f) from (by
            unfold nb068AlphaDummy338;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0346 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0348 :
    (nb068AlphaDummy327) ∈
      (((Class.cab (nb068AlphaDummy335)
            (synWrex (nb068AlphaDummy336) (Class.cv (nb068AlphaDummy327))
              (Wff.classEq (Class.cv (nb068AlphaDummy335))
                (synCphi (Class.cv (nb068AlphaDummy336))))))).fv ∪
        ((Class.cab (nb068AlphaDummy335)
            (synWrex (nb068AlphaDummy336) (Class.cv (nb068AlphaDummy327))
              (Wff.classEq (Class.cv (nb068AlphaDummy335))
                (synCphi (Class.cv (nb068AlphaDummy336))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068AlphaDummy327) ≠ (nb068AlphaDummy335) from (by
          unfold nb068AlphaDummy335;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0344) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068AlphaDummy327) ≠ (nb068AlphaDummy336) from (by
            unfold nb068AlphaDummy336;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0344) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0349 (f : Var) :
    (nb068AlphaDummy330 f) ∈
      (((Class.cab (nb068AlphaDummy337 f)
            (synWrex (nb068AlphaDummy338 f) (Class.cv (nb068AlphaDummy330 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy337 f))
                (synCphi (Class.cv (nb068AlphaDummy338 f))))))).fv ∪
        ((Class.cab (nb068AlphaDummy337 f)
            (synWrex (nb068AlphaDummy338 f) (Class.cv (nb068AlphaDummy330 f))
              (Wff.classEq (Class.cv (nb068AlphaDummy337 f))
                (synCphi (Class.cv (nb068AlphaDummy338 f))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb068AlphaDummy330 f) ≠ (nb068AlphaDummy337 f) from (by
          unfold nb068AlphaDummy337;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0346 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb068AlphaDummy330 f) ≠ (nb068AlphaDummy338 f) from (by
            unfold nb068AlphaDummy338;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb068_support_mem_0346 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb068_support_mem_0350 :
    (nb068AlphaDummy336) ∈ (((Class.cv (nb068AlphaDummy336))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0351 (f : Var) :
    (nb068AlphaDummy338 f) ∈ (((Class.cv (nb068AlphaDummy338 f))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0352 :
    (nb068AlphaDummy343) ∈
      (((Wff.classMem (Class.cv (nb068AlphaDummy343)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb068AlphaDummy343)) (synC1c))).fv ∪
        ((Class.cv (nb068AlphaDummy343))).fv) :=
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

theorem nb068_support_mem_0353 (f : Var) :
    (nb068AlphaDummy345 f) ∈
      (((Wff.classMem (Class.cv (nb068AlphaDummy345 f)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb068AlphaDummy345 f)) (synC1c))).fv ∪
        ((Class.cv (nb068AlphaDummy345 f))).fv) :=
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

theorem nb068_support_mem_0354 :
    (nb068AlphaDummy343) ∈
      (((Class.cv (nb068AlphaDummy343))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb068_support_mem_0355 (f : Var) :
    (nb068AlphaDummy345 f) ∈
      (((Class.cv (nb068AlphaDummy345 f))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
