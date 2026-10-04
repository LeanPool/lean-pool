/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C052C001Block001

/-! NF weak partition development: NAR4C052C001Part003. -/


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

theorem nb052_support_mem_0087 (x : Var) (y : Var) :
    (nb052AlphaDummy003 x y) ∈
      (((Class.cab (nb052AlphaDummy008 x y)
            (synWrex (nb052AlphaDummy009 x y) (Class.cv (nb052AlphaDummy003 x y))
              (Wff.classEq (Class.cv (nb052AlphaDummy008 x y))
                (synCun (synCphi (Class.cv (nb052AlphaDummy009 x y)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb052AlphaDummy008 x y)
            (synWrex (nb052AlphaDummy009 x y) (Class.cv (nb052AlphaDummy003 x y))
              (Wff.classEq (Class.cv (nb052AlphaDummy008 x y))
                (synCun (synCphi (Class.cv (nb052AlphaDummy009 x y)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb052_support_mem_0084 x y) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb052_support_mem_0084 x y) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb052_support_mem_0088 :
    (nb052AlphaDummy007) ∈
      (((synCcompl (synCphi (Class.cv (nb052AlphaDummy007))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb052_support_mem_0089 (x : Var) (y : Var) :
    (nb052AlphaDummy009 x y) ∈
      (((synCcompl (synCphi (Class.cv (nb052AlphaDummy009 x y))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb052_support_mem_0090 :
    (nb052AlphaDummy007) ∈
      (((synCphi (Class.cv (nb052AlphaDummy007)))).fv ∪
        ((synCphi (Class.cv (nb052AlphaDummy007)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb052_support_mem_0091 (x : Var) (y : Var) :
    (nb052AlphaDummy009 x y) ∈
      (((synCphi (Class.cv (nb052AlphaDummy009 x y)))).fv ∪
        ((synCphi (Class.cv (nb052AlphaDummy009 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb052_support_mem_0092 :
    (nb052AlphaDummy000) ∈
      (((synCcompl (Class.cv (nb052AlphaDummy000)))).fv ∪
        ((synCcompl (Class.cv (nb052AlphaDummy001)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb052_support_mem_0093 (x : Var) (y : Var) :
    x ∈ (((synCcompl (Class.cv x))).fv ∪ ((synCcompl (Class.cv y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb052_support_mem_0094 :
    (nb052AlphaDummy000) ∈
      (((Class.cv (nb052AlphaDummy000))).fv ∪ ((Class.cv (nb052AlphaDummy000))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb052_support_mem_0095 (x : Var) : x ∈ (((Class.cv x)).fv ∪ ((Class.cv x)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb052_support_mem_0096 :
    (nb052AlphaDummy001) ∈
      (((synCcompl (Class.cv (nb052AlphaDummy000)))).fv ∪
        ((synCcompl (Class.cv (nb052AlphaDummy001)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb052_support_mem_0097 (x : Var) (y : Var) :
    y ∈ (((synCcompl (Class.cv x))).fv ∪ ((synCcompl (Class.cv y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb052_support_mem_0098 :
    (nb052AlphaDummy001) ∈
      (((Class.cv (nb052AlphaDummy001))).fv ∪ ((Class.cv (nb052AlphaDummy001))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb052_support_mem_0099 (y : Var) : y ∈ (((Class.cv y)).fv ∪ ((Class.cv y)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
