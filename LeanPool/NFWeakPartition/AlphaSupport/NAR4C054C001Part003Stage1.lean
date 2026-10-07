/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C054C001Block001

/-! NF weak partition development: NAR4C054C001Part003. -/


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

theorem nb054_support_mem_0079 (x : Var) (y : Var) :
    (nb054AlphaDummy061 x y) ∈
      (((synCcompl (Class.cv (nb054AlphaDummy060 x y)))).fv ∪
        ((synCcompl (Class.cv (nb054AlphaDummy061 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb054_support_mem_0080 :
    (nb054AlphaDummy058) ∈
      (((Class.cv (nb054AlphaDummy058))).fv ∪ ((Class.cv (nb054AlphaDummy058))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb054_support_mem_0081 (x : Var) (y : Var) :
    (nb054AlphaDummy061 x y) ∈
      (((Class.cv (nb054AlphaDummy061 x y))).fv ∪
        ((Class.cv (nb054AlphaDummy061 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb054_support_mem_0082 :
    (nb054AlphaDummy002) ∈
      (((synCop (Class.cv (nb054AlphaDummy000)) (Class.cv (nb054AlphaDummy001)))).fv ∪
        ((Class.cv (nb054AlphaDummy002))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb054_support_mem_0083 :
    (nb054AlphaDummy002) ∈
      (((synCcompl (Class.cab (nb054AlphaDummy006) (synWrex (nb054AlphaDummy007)
                (synCop (Class.cv (nb054AlphaDummy000)) (Class.cv (nb054AlphaDummy001)))
                (Wff.classEq (Class.cv (nb054AlphaDummy006))
                  (synCphi (Class.cv (nb054AlphaDummy007)))))))).fv ∪ ((synCcompl
            (Class.cab (nb054AlphaDummy006)
              (synWrex (nb054AlphaDummy007) (Class.cv (nb054AlphaDummy002))
                (Wff.classEq (Class.cv (nb054AlphaDummy006))
                  (synCun (synCphi (Class.cv (nb054AlphaDummy007)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0082) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0082) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb054_support_mem_0084 (x : Var) (y : Var) :
    (nb054AlphaDummy003 x y) ∈
      (((synCop (Class.cv x) (Class.cv y))).fv ∪
        ((Class.cv (nb054AlphaDummy003 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb054_support_mem_0085 (x : Var) (y : Var) :
    (nb054AlphaDummy003 x y) ∈
      (((synCcompl (Class.cab (nb054AlphaDummy008 x y)
              (synWrex (nb054AlphaDummy009 x y) (synCop (Class.cv x) (Class.cv y))
                (Wff.classEq (Class.cv (nb054AlphaDummy008 x y))
                  (synCphi (Class.cv (nb054AlphaDummy009 x y)))))))).fv ∪ ((synCcompl
            (Class.cab (nb054AlphaDummy008 x y)
              (synWrex (nb054AlphaDummy009 x y) (Class.cv (nb054AlphaDummy003 x y))
                (Wff.classEq (Class.cv (nb054AlphaDummy008 x y))
                  (synCun (synCphi (Class.cv (nb054AlphaDummy009 x y)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible
    refine
      Finset.mem_union_right (a := (nb054AlphaDummy003 x y)) (t := ((synCcompl
            (Class.cab (nb054AlphaDummy008 x y)
              (synWrex (nb054AlphaDummy009 x y) (Class.cv (nb054AlphaDummy003 x y))
                (Wff.classEq (Class.cv (nb054AlphaDummy008 x y))
                  (synCun (synCphi (Class.cv (nb054AlphaDummy009 x y)))
                    (synCsn (synC0c)))))))).fv)
        ((synCcompl (Class.cab (nb054AlphaDummy008 x y)
              (synWrex (nb054AlphaDummy009 x y) (synCop (Class.cv x) (Class.cv y))
                (Wff.classEq (Class.cv (nb054AlphaDummy008 x y))
                  (synCphi (Class.cv (nb054AlphaDummy009 x y)))))))).fv
        ?_
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0084 x y) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0084 x y) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb054_support_mem_0086 :
    (nb054AlphaDummy002) ∈
      (((Class.cab (nb054AlphaDummy006)
            (synWrex (nb054AlphaDummy007) (Class.cv (nb054AlphaDummy002))
              (Wff.classEq (Class.cv (nb054AlphaDummy006))
                (synCun (synCphi (Class.cv (nb054AlphaDummy007)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb054AlphaDummy006)
            (synWrex (nb054AlphaDummy007) (Class.cv (nb054AlphaDummy002))
              (Wff.classEq (Class.cv (nb054AlphaDummy006))
                (synCun (synCphi (Class.cv (nb054AlphaDummy007)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0082) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0082) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb054_support_mem_0087 (x : Var) (y : Var) :
    (nb054AlphaDummy003 x y) ∈
      (((Class.cab (nb054AlphaDummy008 x y)
            (synWrex (nb054AlphaDummy009 x y) (Class.cv (nb054AlphaDummy003 x y))
              (Wff.classEq (Class.cv (nb054AlphaDummy008 x y))
                (synCun (synCphi (Class.cv (nb054AlphaDummy009 x y)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb054AlphaDummy008 x y)
            (synWrex (nb054AlphaDummy009 x y) (Class.cv (nb054AlphaDummy003 x y))
              (Wff.classEq (Class.cv (nb054AlphaDummy008 x y))
                (synCun (synCphi (Class.cv (nb054AlphaDummy009 x y)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0084 x y) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0084 x y) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb054_support_mem_0088 :
    (nb054AlphaDummy007) ∈
      (((synCcompl (synCphi (Class.cv (nb054AlphaDummy007))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb054_support_mem_0089 (x : Var) (y : Var) :
    (nb054AlphaDummy009 x y) ∈
      (((synCcompl (synCphi (Class.cv (nb054AlphaDummy009 x y))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb054_support_mem_0090 :
    (nb054AlphaDummy007) ∈
      (((synCphi (Class.cv (nb054AlphaDummy007)))).fv ∪
        ((synCphi (Class.cv (nb054AlphaDummy007)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb054_support_mem_0091 (x : Var) (y : Var) :
    (nb054AlphaDummy009 x y) ∈
      (((synCphi (Class.cv (nb054AlphaDummy009 x y)))).fv ∪
        ((synCphi (Class.cv (nb054AlphaDummy009 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb054_support_mem_0092 :
    (nb054AlphaDummy015) ∈
      (((synCnin (Class.cv (nb054AlphaDummy015)) (Class.cv (nb054AlphaDummy078)))).fv ∪
        ((synCnin (Class.cv (nb054AlphaDummy015))
            (Class.cv (nb054AlphaDummy078)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb054_support_mem_0093 (x : Var) (y : Var) :
    (nb054AlphaDummy017 x y) ∈
      (((synCnin (Class.cv (nb054AlphaDummy017 x y))
            (Class.cv (nb054AlphaDummy079 x y)))).fv ∪
        ((synCnin (Class.cv (nb054AlphaDummy017 x y))
            (Class.cv (nb054AlphaDummy079 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb054_support_mem_0094 :
    (nb054AlphaDummy015) ∈
      (((Class.cv (nb054AlphaDummy015))).fv ∪ ((Class.cv (nb054AlphaDummy078))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb054_support_mem_0095 (x : Var) (y : Var) :
    (nb054AlphaDummy017 x y) ∈
      (((Class.cv (nb054AlphaDummy017 x y))).fv ∪
        ((Class.cv (nb054AlphaDummy079 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb054_support_mem_0096 :
    (nb054AlphaDummy078) ∈
      (((synCnin (Class.cv (nb054AlphaDummy015)) (Class.cv (nb054AlphaDummy078)))).fv ∪
        ((synCnin (Class.cv (nb054AlphaDummy015))
            (Class.cv (nb054AlphaDummy078)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb054_support_mem_0097 (x : Var) (y : Var) :
    (nb054AlphaDummy079 x y) ∈
      (((synCnin (Class.cv (nb054AlphaDummy017 x y))
            (Class.cv (nb054AlphaDummy079 x y)))).fv ∪
        ((synCnin (Class.cv (nb054AlphaDummy017 x y))
            (Class.cv (nb054AlphaDummy079 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb054_support_mem_0098 :
    (nb054AlphaDummy078) ∈
      (((Class.cv (nb054AlphaDummy015))).fv ∪ ((Class.cv (nb054AlphaDummy078))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb054_support_mem_0099 (x : Var) (y : Var) :
    (nb054AlphaDummy079 x y) ∈
      (((Class.cv (nb054AlphaDummy017 x y))).fv ∪
        ((Class.cv (nb054AlphaDummy079 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb054_support_mem_0100 :
    (nb054AlphaDummy015) ∈
      (((synCcompl (Class.cv (nb054AlphaDummy015)))).fv ∪
        ((synCcompl (Class.cv (nb054AlphaDummy078)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb054_support_mem_0101 (x : Var) (y : Var) :
    (nb054AlphaDummy017 x y) ∈
      (((synCcompl (Class.cv (nb054AlphaDummy017 x y)))).fv ∪
        ((synCcompl (Class.cv (nb054AlphaDummy079 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb054_support_mem_0102 :
    (nb054AlphaDummy015) ∈
      (((Class.cv (nb054AlphaDummy015))).fv ∪ ((Class.cv (nb054AlphaDummy015))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb054_support_mem_0103 (x : Var) (y : Var) :
    (nb054AlphaDummy017 x y) ∈
      (((Class.cv (nb054AlphaDummy017 x y))).fv ∪
        ((Class.cv (nb054AlphaDummy017 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb054_support_mem_0104 :
    (nb054AlphaDummy078) ∈
      (((synCcompl (Class.cv (nb054AlphaDummy015)))).fv ∪
        ((synCcompl (Class.cv (nb054AlphaDummy078)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb054_support_mem_0105 (x : Var) (y : Var) :
    (nb054AlphaDummy079 x y) ∈
      (((synCcompl (Class.cv (nb054AlphaDummy017 x y)))).fv ∪
        ((synCcompl (Class.cv (nb054AlphaDummy079 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb054_support_mem_0106 :
    (nb054AlphaDummy078) ∈
      (((Class.cv (nb054AlphaDummy078))).fv ∪ ((Class.cv (nb054AlphaDummy078))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb054_support_mem_0107 (x : Var) (y : Var) :
    (nb054AlphaDummy079 x y) ∈
      (((Class.cv (nb054AlphaDummy079 x y))).fv ∪
        ((Class.cv (nb054AlphaDummy079 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
