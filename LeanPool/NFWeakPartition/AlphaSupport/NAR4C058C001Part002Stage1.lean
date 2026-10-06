/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NAR4C058C001Part001

/-! NF weak partition development: NAR4C058C001Part002. -/


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

theorem nb058_support_mem_0028 :
    (nb058AlphaDummy020) ∈
      (((Class.cv (nb058AlphaDummy020))).fv ∪ ((Class.cv (nb058AlphaDummy020))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb058_support_mem_0029 (x : Var) :
    (nb058AlphaDummy023 x) ∈
      (((Class.cv (nb058AlphaDummy023 x))).fv ∪ ((Class.cv (nb058AlphaDummy023 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb058_support_mem_0030 :
    (nb058AlphaDummy021) ∈
      (((synCcompl (Class.cv (nb058AlphaDummy020)))).fv ∪
        ((synCcompl (Class.cv (nb058AlphaDummy021)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb058_support_mem_0031 (x : Var) :
    (nb058AlphaDummy024 x) ∈
      (((synCcompl (Class.cv (nb058AlphaDummy023 x)))).fv ∪
        ((synCcompl (Class.cv (nb058AlphaDummy024 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb058_support_mem_0032 :
    (nb058AlphaDummy021) ∈
      (((Class.cv (nb058AlphaDummy021))).fv ∪ ((Class.cv (nb058AlphaDummy021))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb058_support_mem_0033 (x : Var) :
    (nb058AlphaDummy024 x) ∈
      (((Class.cv (nb058AlphaDummy024 x))).fv ∪ ((Class.cv (nb058AlphaDummy024 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb058_support_mem_0034 :
    (nb058AlphaDummy001) ∈
      (((Class.cv (nb058AlphaDummy000))).fv ∪ ((Class.cv (nb058AlphaDummy001))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb058_support_mem_0035 :
    (nb058AlphaDummy001) ∈
      (((synCcompl (Class.cab (nb058AlphaDummy005)
              (synWrex (nb058AlphaDummy006) (Class.cv (nb058AlphaDummy000))
                (Wff.classEq (Class.cv (nb058AlphaDummy005))
                  (synCphi (Class.cv (nb058AlphaDummy006)))))))).fv ∪ ((synCcompl
            (Class.cab (nb058AlphaDummy005)
              (synWrex (nb058AlphaDummy006) (Class.cv (nb058AlphaDummy001))
                (Wff.classEq (Class.cv (nb058AlphaDummy005))
                  (synCun (synCphi (Class.cv (nb058AlphaDummy006)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0034) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0034) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb058_support_mem_0036 (x : Var) :
    (nb058AlphaDummy002 x) ∈
      (((Class.cv x)).fv ∪ ((Class.cv (nb058AlphaDummy002 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb058_support_mem_0037 (x : Var) :
    (nb058AlphaDummy002 x) ∈
      (((synCcompl (Class.cab (nb058AlphaDummy007 x)
              (synWrex (nb058AlphaDummy008 x) (Class.cv x)
                (Wff.classEq (Class.cv (nb058AlphaDummy007 x))
                  (synCphi (Class.cv (nb058AlphaDummy008 x)))))))).fv ∪ ((synCcompl
            (Class.cab (nb058AlphaDummy007 x)
              (synWrex (nb058AlphaDummy008 x) (Class.cv (nb058AlphaDummy002 x))
                (Wff.classEq (Class.cv (nb058AlphaDummy007 x))
                  (synCun (synCphi (Class.cv (nb058AlphaDummy008 x)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0036 x) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0036 x) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb058_support_mem_0038 :
    (nb058AlphaDummy001) ∈
      (((Class.cab (nb058AlphaDummy005)
            (synWrex (nb058AlphaDummy006) (Class.cv (nb058AlphaDummy001))
              (Wff.classEq (Class.cv (nb058AlphaDummy005))
                (synCun (synCphi (Class.cv (nb058AlphaDummy006)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb058AlphaDummy005)
            (synWrex (nb058AlphaDummy006) (Class.cv (nb058AlphaDummy001))
              (Wff.classEq (Class.cv (nb058AlphaDummy005))
                (synCun (synCphi (Class.cv (nb058AlphaDummy006)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0034) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0034) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb058_support_mem_0039 (x : Var) :
    (nb058AlphaDummy002 x) ∈
      (((Class.cab (nb058AlphaDummy007 x)
            (synWrex (nb058AlphaDummy008 x) (Class.cv (nb058AlphaDummy002 x))
              (Wff.classEq (Class.cv (nb058AlphaDummy007 x))
                (synCun (synCphi (Class.cv (nb058AlphaDummy008 x)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb058AlphaDummy007 x)
            (synWrex (nb058AlphaDummy008 x) (Class.cv (nb058AlphaDummy002 x))
              (Wff.classEq (Class.cv (nb058AlphaDummy007 x))
                (synCun (synCphi (Class.cv (nb058AlphaDummy008 x)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0036 x) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0036 x) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb058_support_mem_0040 :
    (nb058AlphaDummy006) ∈
      (((synCcompl (synCphi (Class.cv (nb058AlphaDummy006))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb058_support_mem_0041 (x : Var) :
    (nb058AlphaDummy008 x) ∈
      (((synCcompl (synCphi (Class.cv (nb058AlphaDummy008 x))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb058_support_mem_0042 :
    (nb058AlphaDummy006) ∈
      (((synCphi (Class.cv (nb058AlphaDummy006)))).fv ∪
        ((synCphi (Class.cv (nb058AlphaDummy006)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb058_support_mem_0043 (x : Var) :
    (nb058AlphaDummy008 x) ∈
      (((synCphi (Class.cv (nb058AlphaDummy008 x)))).fv ∪
        ((synCphi (Class.cv (nb058AlphaDummy008 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb058_support_mem_0044 :
    (nb058AlphaDummy045) ∈
      (((synCnin (Class.cv (nb058AlphaDummy045))
            (synCuni (Class.cv (nb058AlphaDummy000))))).fv ∪
        ((synCnin (Class.cv (nb058AlphaDummy045))
            (synCuni (Class.cv (nb058AlphaDummy000))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb058_support_mem_0045 (x : Var) :
    (nb058AlphaDummy046 x) ∈
      (((synCnin (Class.cv (nb058AlphaDummy046 x)) (synCuni (Class.cv x)))).fv ∪
        ((synCnin (Class.cv (nb058AlphaDummy046 x)) (synCuni (Class.cv x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb058_support_mem_0046 :
    (nb058AlphaDummy045) ∈
      (((Class.cv (nb058AlphaDummy045))).fv ∪
        ((synCuni (Class.cv (nb058AlphaDummy000)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb058_support_mem_0047 (x : Var) :
    (nb058AlphaDummy046 x) ∈
      (((Class.cv (nb058AlphaDummy046 x))).fv ∪ ((synCuni (Class.cv x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb058_support_mem_0048 :
    (nb058AlphaDummy000) ∈
      (((synCnin (synCpw (synCuni (Class.cv (nb058AlphaDummy000)))) (synC1c))).fv ∪
        ((synCnin (synCpw (synCuni (Class.cv (nb058AlphaDummy000)))) (synC1c))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cpw]
  rw [fv_syn_cuni]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb058_support_mem_0049 (x : Var) :
    x ∈
      (((synCnin (synCpw (synCuni (Class.cv x))) (synC1c))).fv ∪
        ((synCnin (synCpw (synCuni (Class.cv x))) (synC1c))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cpw]
  rw [fv_syn_cuni]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb058_support_mem_0050 :
    (nb058AlphaDummy000) ∈
      (((synCpw (synCuni (Class.cv (nb058AlphaDummy000))))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cpw]
  rw [fv_syn_cuni]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb058_support_mem_0051 (x : Var) :
    x ∈ (((synCpw (synCuni (Class.cv x)))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cpw]
  rw [fv_syn_cuni]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb058_support_mem_0052 :
    (nb058AlphaDummy000) ∈ (((synCuni (Class.cv (nb058AlphaDummy000)))).fv) :=
  by
  rw [fv_syn_cuni]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb058_support_mem_0053 (x : Var) : x ∈ (((synCuni (Class.cv x))).fv) :=
  by
  rw [fv_syn_cuni]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb058_support_mem_0054 :
    (nb058AlphaDummy000) ∈
      (((synCnin (Class.cv (nb058AlphaDummy045))
            (synCuni (Class.cv (nb058AlphaDummy000))))).fv ∪
        ((synCnin (Class.cv (nb058AlphaDummy045))
            (synCuni (Class.cv (nb058AlphaDummy000))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_cuni]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb058_support_mem_0055 (x : Var) :
    x ∈
      (((synCnin (Class.cv (nb058AlphaDummy046 x)) (synCuni (Class.cv x)))).fv ∪
        ((synCnin (Class.cv (nb058AlphaDummy046 x)) (synCuni (Class.cv x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_cuni]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb058_support_mem_0056 :
    (nb058AlphaDummy000) ∈
      (((Class.cv (nb058AlphaDummy045))).fv ∪
        ((synCuni (Class.cv (nb058AlphaDummy000)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_cuni]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb058_support_mem_0057 (x : Var) :
    x ∈ (((Class.cv (nb058AlphaDummy046 x))).fv ∪ ((synCuni (Class.cv x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_cuni]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb058_support_mem_0058 :
    (nb058AlphaDummy000) ∈ (((Class.cv (nb058AlphaDummy000))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb058_support_mem_0059 (x : Var) : x ∈ (((Class.cv x)).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
