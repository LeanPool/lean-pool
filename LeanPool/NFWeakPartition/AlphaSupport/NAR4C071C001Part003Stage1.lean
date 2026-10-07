/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C071C001Block001

/-! NF weak partition development: NAR4C071C001Part003. -/


public section


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

theorem nb071_support_mem_0054 :
    (nb071AlphaDummy065) ∈
      (((Class.cv (nb071AlphaDummy065))).fv ∪ ((Class.cv (nb071AlphaDummy042))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0055 (x : Var) :
    (nb071AlphaDummy066 x) ∈
      (((Class.cv (nb071AlphaDummy066 x))).fv ∪ ((Class.cv (nb071AlphaDummy044 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0056 :
    (nb071AlphaDummy042) ∈
      (((synCen)).fv ∪ ((synCsn (synCpw1 (Class.cv (nb071AlphaDummy042))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_csn]
  rw [fv_syn_cpw1]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0057 (x : Var) :
    (nb071AlphaDummy044 x) ∈
      (((synCen)).fv ∪ ((synCsn (synCpw1 (Class.cv (nb071AlphaDummy044 x))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_csn]
  rw [fv_syn_cpw1]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0058 :
    (nb071AlphaDummy042) ∈ (((synCpw1 (Class.cv (nb071AlphaDummy042)))).fv) :=
  by
  rw [fv_syn_cpw1]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0059 (x : Var) :
    (nb071AlphaDummy044 x) ∈ (((synCpw1 (Class.cv (nb071AlphaDummy044 x)))).fv) :=
  by
  rw [fv_syn_cpw1]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0060 :
    (nb071AlphaDummy042) ∈
      (((synCnin (synCpw (Class.cv (nb071AlphaDummy042))) (synC1c))).fv ∪
        ((synCnin (synCpw (Class.cv (nb071AlphaDummy042))) (synC1c))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cpw]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0061 (x : Var) :
    (nb071AlphaDummy044 x) ∈
      (((synCnin (synCpw (Class.cv (nb071AlphaDummy044 x))) (synC1c))).fv ∪
        ((synCnin (synCpw (Class.cv (nb071AlphaDummy044 x))) (synC1c))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cpw]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0062 :
    (nb071AlphaDummy042) ∈
      (((synCpw (Class.cv (nb071AlphaDummy042)))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cpw]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0063 (x : Var) :
    (nb071AlphaDummy044 x) ∈
      (((synCpw (Class.cv (nb071AlphaDummy044 x)))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cpw]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0064 :
    (nb071AlphaDummy042) ∈ (((Class.cv (nb071AlphaDummy042))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0065 (x : Var) :
    (nb071AlphaDummy044 x) ∈ (((Class.cv (nb071AlphaDummy044 x))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0066 :
    (nb071AlphaDummy042) ∈
      (((synCnin (Class.cv (nb071AlphaDummy065)) (Class.cv (nb071AlphaDummy042)))).fv ∪
        ((synCnin (Class.cv (nb071AlphaDummy065))
            (Class.cv (nb071AlphaDummy042)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0067 (x : Var) :
    (nb071AlphaDummy044 x) ∈
      (((synCnin (Class.cv (nb071AlphaDummy066 x))
            (Class.cv (nb071AlphaDummy044 x)))).fv ∪
        ((synCnin (Class.cv (nb071AlphaDummy066 x))
            (Class.cv (nb071AlphaDummy044 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0068 :
    (nb071AlphaDummy042) ∈
      (((Class.cv (nb071AlphaDummy065))).fv ∪ ((Class.cv (nb071AlphaDummy042))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0069 (x : Var) :
    (nb071AlphaDummy044 x) ∈
      (((Class.cv (nb071AlphaDummy066 x))).fv ∪ ((Class.cv (nb071AlphaDummy044 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0070 :
    (nb071AlphaDummy056) ∈
      (((Class.cv (nb071AlphaDummy056))).fv ∪ ((Class.cv (nb071AlphaDummy055))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0071 :
    (nb071AlphaDummy056) ∈
      (((synCcompl (Class.cab (nb071AlphaDummy071)
              (synWrex (nb071AlphaDummy072) (Class.cv (nb071AlphaDummy056))
                (Wff.classEq (Class.cv (nb071AlphaDummy071))
                  (synCphi (Class.cv (nb071AlphaDummy072)))))))).fv ∪ ((synCcompl
            (Class.cab (nb071AlphaDummy071)
              (synWrex (nb071AlphaDummy072) (Class.cv (nb071AlphaDummy055))
                (Wff.classEq (Class.cv (nb071AlphaDummy071))
                  (synCun (synCphi (Class.cv (nb071AlphaDummy072)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb071AlphaDummy056) ≠ (nb071AlphaDummy071) from (by
          unfold nb071AlphaDummy071;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0070) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb071AlphaDummy056) ≠ (nb071AlphaDummy072) from (by
            unfold nb071AlphaDummy072;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0070) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb071_support_mem_0072 (x : Var) :
    (nb071AlphaDummy058 x) ∈
      (((Class.cv (nb071AlphaDummy058 x))).fv ∪ ((Class.cv (nb071AlphaDummy057 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0073 (x : Var) :
    (nb071AlphaDummy058 x) ∈
      (((synCcompl (Class.cab (nb071AlphaDummy073 x)
              (synWrex (nb071AlphaDummy074 x) (Class.cv (nb071AlphaDummy058 x))
                (Wff.classEq (Class.cv (nb071AlphaDummy073 x))
                  (synCphi (Class.cv (nb071AlphaDummy074 x)))))))).fv ∪ ((synCcompl
            (Class.cab (nb071AlphaDummy073 x)
              (synWrex (nb071AlphaDummy074 x) (Class.cv (nb071AlphaDummy057 x))
                (Wff.classEq (Class.cv (nb071AlphaDummy073 x))
                  (synCun (synCphi (Class.cv (nb071AlphaDummy074 x)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb071AlphaDummy058 x) ≠ (nb071AlphaDummy073 x) from (by
          unfold nb071AlphaDummy073;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0072 x) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb071AlphaDummy058 x) ≠ (nb071AlphaDummy074 x) from (by
            unfold nb071AlphaDummy074;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0072 x) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb071_support_mem_0074 :
    (nb071AlphaDummy056) ∈
      (((Class.cab (nb071AlphaDummy071)
            (synWrex (nb071AlphaDummy072) (Class.cv (nb071AlphaDummy056))
              (Wff.classEq (Class.cv (nb071AlphaDummy071))
                (synCphi (Class.cv (nb071AlphaDummy072))))))).fv ∪
        ((Class.cab (nb071AlphaDummy071)
            (synWrex (nb071AlphaDummy072) (Class.cv (nb071AlphaDummy056))
              (Wff.classEq (Class.cv (nb071AlphaDummy071))
                (synCphi (Class.cv (nb071AlphaDummy072))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb071AlphaDummy056) ≠ (nb071AlphaDummy071) from (by
          unfold nb071AlphaDummy071;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0070) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb071AlphaDummy056) ≠ (nb071AlphaDummy072) from (by
            unfold nb071AlphaDummy072;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0070) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb071_support_mem_0075 (x : Var) :
    (nb071AlphaDummy058 x) ∈
      (((Class.cab (nb071AlphaDummy073 x)
            (synWrex (nb071AlphaDummy074 x) (Class.cv (nb071AlphaDummy058 x))
              (Wff.classEq (Class.cv (nb071AlphaDummy073 x))
                (synCphi (Class.cv (nb071AlphaDummy074 x))))))).fv ∪
        ((Class.cab (nb071AlphaDummy073 x)
            (synWrex (nb071AlphaDummy074 x) (Class.cv (nb071AlphaDummy058 x))
              (Wff.classEq (Class.cv (nb071AlphaDummy073 x))
                (synCphi (Class.cv (nb071AlphaDummy074 x))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb071AlphaDummy058 x) ≠ (nb071AlphaDummy073 x) from (by
          unfold nb071AlphaDummy073;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0072 x) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb071AlphaDummy058 x) ≠ (nb071AlphaDummy074 x) from (by
            unfold nb071AlphaDummy074;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0072 x) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb071_support_mem_0076 :
    (nb071AlphaDummy072) ∈ (((Class.cv (nb071AlphaDummy072))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0077 (x : Var) :
    (nb071AlphaDummy074 x) ∈ (((Class.cv (nb071AlphaDummy074 x))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0078 :
    (nb071AlphaDummy079) ∈
      (((Wff.classMem (Class.cv (nb071AlphaDummy079)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb071AlphaDummy079)) (synC1c))).fv ∪
        ((Class.cv (nb071AlphaDummy079))).fv) :=
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

theorem nb071_support_mem_0079 (x : Var) :
    (nb071AlphaDummy081 x) ∈
      (((Wff.classMem (Class.cv (nb071AlphaDummy081 x)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb071AlphaDummy081 x)) (synC1c))).fv ∪
        ((Class.cv (nb071AlphaDummy081 x))).fv) :=
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

theorem nb071_support_mem_0080 :
    (nb071AlphaDummy079) ∈
      (((Class.cv (nb071AlphaDummy079))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0081 (x : Var) :
    (nb071AlphaDummy081 x) ∈
      (((Class.cv (nb071AlphaDummy081 x))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0082 :
    (nb071AlphaDummy086) ∈
      (((synCnin (Class.cv (nb071AlphaDummy086)) (Class.cv (nb071AlphaDummy087)))).fv ∪
        ((synCnin (Class.cv (nb071AlphaDummy086))
            (Class.cv (nb071AlphaDummy087)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0083 (x : Var) :
    (nb071AlphaDummy089 x) ∈
      (((synCnin (Class.cv (nb071AlphaDummy089 x))
            (Class.cv (nb071AlphaDummy090 x)))).fv ∪
        ((synCnin (Class.cv (nb071AlphaDummy089 x))
            (Class.cv (nb071AlphaDummy090 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0084 :
    (nb071AlphaDummy086) ∈
      (((Class.cv (nb071AlphaDummy086))).fv ∪ ((Class.cv (nb071AlphaDummy087))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0085 (x : Var) :
    (nb071AlphaDummy089 x) ∈
      (((Class.cv (nb071AlphaDummy089 x))).fv ∪ ((Class.cv (nb071AlphaDummy090 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0086 :
    (nb071AlphaDummy087) ∈
      (((synCnin (Class.cv (nb071AlphaDummy086)) (Class.cv (nb071AlphaDummy087)))).fv ∪
        ((synCnin (Class.cv (nb071AlphaDummy086))
            (Class.cv (nb071AlphaDummy087)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0087 (x : Var) :
    (nb071AlphaDummy090 x) ∈
      (((synCnin (Class.cv (nb071AlphaDummy089 x))
            (Class.cv (nb071AlphaDummy090 x)))).fv ∪
        ((synCnin (Class.cv (nb071AlphaDummy089 x))
            (Class.cv (nb071AlphaDummy090 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0088 :
    (nb071AlphaDummy087) ∈
      (((Class.cv (nb071AlphaDummy086))).fv ∪ ((Class.cv (nb071AlphaDummy087))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0089 (x : Var) :
    (nb071AlphaDummy090 x) ∈
      (((Class.cv (nb071AlphaDummy089 x))).fv ∪ ((Class.cv (nb071AlphaDummy090 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0090 :
    (nb071AlphaDummy086) ∈
      (((synCcompl (Class.cv (nb071AlphaDummy086)))).fv ∪
        ((synCcompl (Class.cv (nb071AlphaDummy087)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0091 (x : Var) :
    (nb071AlphaDummy089 x) ∈
      (((synCcompl (Class.cv (nb071AlphaDummy089 x)))).fv ∪
        ((synCcompl (Class.cv (nb071AlphaDummy090 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0092 :
    (nb071AlphaDummy086) ∈
      (((Class.cv (nb071AlphaDummy086))).fv ∪ ((Class.cv (nb071AlphaDummy086))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0093 (x : Var) :
    (nb071AlphaDummy089 x) ∈
      (((Class.cv (nb071AlphaDummy089 x))).fv ∪ ((Class.cv (nb071AlphaDummy089 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0094 :
    (nb071AlphaDummy087) ∈
      (((synCcompl (Class.cv (nb071AlphaDummy086)))).fv ∪
        ((synCcompl (Class.cv (nb071AlphaDummy087)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0095 (x : Var) :
    (nb071AlphaDummy090 x) ∈
      (((synCcompl (Class.cv (nb071AlphaDummy089 x)))).fv ∪
        ((synCcompl (Class.cv (nb071AlphaDummy090 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0096 :
    (nb071AlphaDummy087) ∈
      (((Class.cv (nb071AlphaDummy087))).fv ∪ ((Class.cv (nb071AlphaDummy087))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0097 (x : Var) :
    (nb071AlphaDummy090 x) ∈
      (((Class.cv (nb071AlphaDummy090 x))).fv ∪ ((Class.cv (nb071AlphaDummy090 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0098 :
    (nb071AlphaDummy055) ∈
      (((Class.cv (nb071AlphaDummy056))).fv ∪ ((Class.cv (nb071AlphaDummy055))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0099 :
    (nb071AlphaDummy055) ∈
      (((synCcompl (Class.cab (nb071AlphaDummy071)
              (synWrex (nb071AlphaDummy072) (Class.cv (nb071AlphaDummy056))
                (Wff.classEq (Class.cv (nb071AlphaDummy071))
                  (synCphi (Class.cv (nb071AlphaDummy072)))))))).fv ∪ ((synCcompl
            (Class.cab (nb071AlphaDummy071)
              (synWrex (nb071AlphaDummy072) (Class.cv (nb071AlphaDummy055))
                (Wff.classEq (Class.cv (nb071AlphaDummy071))
                  (synCun (synCphi (Class.cv (nb071AlphaDummy072)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb071AlphaDummy055) ≠ (nb071AlphaDummy071) from (by
          unfold nb071AlphaDummy071;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0098) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb071AlphaDummy055) ≠ (nb071AlphaDummy072) from (by
            unfold nb071AlphaDummy072;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0098) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb071_support_mem_0100 (x : Var) :
    (nb071AlphaDummy057 x) ∈
      (((Class.cv (nb071AlphaDummy058 x))).fv ∪ ((Class.cv (nb071AlphaDummy057 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0101 (x : Var) :
    (nb071AlphaDummy057 x) ∈
      (((synCcompl (Class.cab (nb071AlphaDummy073 x)
              (synWrex (nb071AlphaDummy074 x) (Class.cv (nb071AlphaDummy058 x))
                (Wff.classEq (Class.cv (nb071AlphaDummy073 x))
                  (synCphi (Class.cv (nb071AlphaDummy074 x)))))))).fv ∪ ((synCcompl
            (Class.cab (nb071AlphaDummy073 x)
              (synWrex (nb071AlphaDummy074 x) (Class.cv (nb071AlphaDummy057 x))
                (Wff.classEq (Class.cv (nb071AlphaDummy073 x))
                  (synCun (synCphi (Class.cv (nb071AlphaDummy074 x)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb071AlphaDummy057 x) ≠ (nb071AlphaDummy073 x) from (by
          unfold nb071AlphaDummy073;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0100 x) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb071AlphaDummy057 x) ≠ (nb071AlphaDummy074 x) from (by
            unfold nb071AlphaDummy074;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0100 x) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb071_support_mem_0102 :
    (nb071AlphaDummy055) ∈
      (((Class.cab (nb071AlphaDummy071)
            (synWrex (nb071AlphaDummy072) (Class.cv (nb071AlphaDummy055))
              (Wff.classEq (Class.cv (nb071AlphaDummy071))
                (synCun (synCphi (Class.cv (nb071AlphaDummy072)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb071AlphaDummy071)
            (synWrex (nb071AlphaDummy072) (Class.cv (nb071AlphaDummy055))
              (Wff.classEq (Class.cv (nb071AlphaDummy071))
                (synCun (synCphi (Class.cv (nb071AlphaDummy072)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb071AlphaDummy055) ≠ (nb071AlphaDummy071) from (by
          unfold nb071AlphaDummy071;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0098) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb071AlphaDummy055) ≠ (nb071AlphaDummy072) from (by
            unfold nb071AlphaDummy072;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0098) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb071_support_mem_0103 (x : Var) :
    (nb071AlphaDummy057 x) ∈
      (((Class.cab (nb071AlphaDummy073 x)
            (synWrex (nb071AlphaDummy074 x) (Class.cv (nb071AlphaDummy057 x))
              (Wff.classEq (Class.cv (nb071AlphaDummy073 x))
                (synCun (synCphi (Class.cv (nb071AlphaDummy074 x)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb071AlphaDummy073 x)
            (synWrex (nb071AlphaDummy074 x) (Class.cv (nb071AlphaDummy057 x))
              (Wff.classEq (Class.cv (nb071AlphaDummy073 x))
                (synCun (synCphi (Class.cv (nb071AlphaDummy074 x)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb071AlphaDummy057 x) ≠ (nb071AlphaDummy073 x) from (by
          unfold nb071AlphaDummy073;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0100 x) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb071AlphaDummy057 x) ≠ (nb071AlphaDummy074 x) from (by
            unfold nb071AlphaDummy074;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0100 x) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb071_support_mem_0104 :
    (nb071AlphaDummy072) ∈
      (((synCcompl (synCphi (Class.cv (nb071AlphaDummy072))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0105 (x : Var) :
    (nb071AlphaDummy074 x) ∈
      (((synCcompl (synCphi (Class.cv (nb071AlphaDummy074 x))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0106 :
    (nb071AlphaDummy072) ∈
      (((synCphi (Class.cv (nb071AlphaDummy072)))).fv ∪
        ((synCphi (Class.cv (nb071AlphaDummy072)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0107 (x : Var) :
    (nb071AlphaDummy074 x) ∈
      (((synCphi (Class.cv (nb071AlphaDummy074 x)))).fv ∪
        ((synCphi (Class.cv (nb071AlphaDummy074 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0108 :
    (nb071AlphaDummy045) ∈ (((Class.cv (nb071AlphaDummy045))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0109 (x : Var) :
    (nb071AlphaDummy046 x) ∈ (((Class.cv (nb071AlphaDummy046 x))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_compact_fv_empty_0020 : (nb071AlphaDummy001) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb071_compact_fv_empty_0021 (x : Var) :
    (nb071AlphaDummy002 x) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb071_compact_fv_empty_0022 : (nb071AlphaDummy000) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb071_compact_fv_empty_0023 (x : Var) : x ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb071_compact_fv_empty_0024 : (nb071AlphaDummy003) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb071_compact_fv_empty_0025 (x : Var) :
    (nb071AlphaDummy004 x) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
