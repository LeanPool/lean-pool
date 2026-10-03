/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NAR4H5C095M3Part007

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `AlphaSupport.NAR4H5C095M3Part008Stage1`. -/


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

theorem nb095_support_mem_0725 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_695 x u D R S_cls f E) ∈
      (((Class.cv (nb095_alpha_dummy_695 x u D R S_cls f E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_695 x u D R S_cls f E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0726 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_693 D R S_cls E) ∈
      (((syn_ccompl (Class.cv (nb095_alpha_dummy_692 D R S_cls E)))).fv ∪
        ((syn_ccompl (Class.cv (nb095_alpha_dummy_693 D R S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0727 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_696 x u D R S_cls f E) ∈
      (((syn_ccompl (Class.cv (nb095_alpha_dummy_695 x u D R S_cls f E)))).fv ∪
        ((syn_ccompl (Class.cv (nb095_alpha_dummy_696 x u D R S_cls f E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0728 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_693 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_693 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_693 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0729 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_696 x u D R S_cls f E) ∈
      (((Class.cv (nb095_alpha_dummy_696 x u D R S_cls f E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_696 x u D R S_cls f E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0730 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_669 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_003 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_669 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0731 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_669 D R S_cls E) ∈
      (((syn_ccompl (Class.cab (nb095_alpha_dummy_677 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_678 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_003 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_677 D R S_cls E))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_678 D R S_cls E)))))))).fv ∪
        ((syn_ccompl (Class.cab (nb095_alpha_dummy_677 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_678 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_669 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_677 D R S_cls E))
                  (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_678 D R S_cls E)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095_alpha_dummy_669 D R S_cls E) ≠ (nb095_alpha_dummy_677 D R S_cls E) from (by
          unfold nb095_alpha_dummy_677;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0730 D R S_cls E) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095_alpha_dummy_669 D R S_cls E) ≠ (nb095_alpha_dummy_678 D R S_cls E) from (by
            unfold nb095_alpha_dummy_678;
            with_reducible
              exact
                (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0730 D R S_cls E) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0732 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_670 x u D R S_cls f E) ∈
      (((Class.cv (nb095_alpha_dummy_005 x u D R S_cls f E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_670 x u D R S_cls f E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0733 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_670 x u D R S_cls f E) ∈
      (((syn_ccompl (Class.cab (nb095_alpha_dummy_679 x u D R S_cls f E)
              (syn_wrex (nb095_alpha_dummy_680 x u D R S_cls f E)
                (Class.cv (nb095_alpha_dummy_005 x u D R S_cls f E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_679 x u D R S_cls f E)) (syn_cphi
                    (Class.cv (nb095_alpha_dummy_680 x u D R S_cls f E)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb095_alpha_dummy_679 x u D R S_cls f E)
              (syn_wrex (nb095_alpha_dummy_680 x u D R S_cls f E)
                (Class.cv (nb095_alpha_dummy_670 x u D R S_cls f E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_679 x u D R S_cls f E))
                  (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_680 x u D R S_cls f E)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095_alpha_dummy_670 x u D R S_cls f E) ≠
          (nb095_alpha_dummy_679 x u D R S_cls f E) from (by
          unfold nb095_alpha_dummy_679;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar (nb095_support_mem_0732 x u D R S_cls f E) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095_alpha_dummy_670 x u D R S_cls f E) ≠
            (nb095_alpha_dummy_680 x u D R S_cls f E) from (by
            unfold nb095_alpha_dummy_680;
            with_reducible
              exact
                (Nat.ne_of_lt
                  (mem_lt_freshVar (nb095_support_mem_0732 x u D R S_cls f E) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0734 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_669 D R S_cls E) ∈
      (((Class.cab (nb095_alpha_dummy_677 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_678 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_669 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_677 D R S_cls E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_678 D R S_cls E)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb095_alpha_dummy_677 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_678 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_669 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_677 D R S_cls E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_678 D R S_cls E)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095_alpha_dummy_669 D R S_cls E) ≠ (nb095_alpha_dummy_677 D R S_cls E) from (by
          unfold nb095_alpha_dummy_677;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0730 D R S_cls E) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095_alpha_dummy_669 D R S_cls E) ≠ (nb095_alpha_dummy_678 D R S_cls E) from (by
            unfold nb095_alpha_dummy_678;
            with_reducible
              exact
                (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0730 D R S_cls E) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0735 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_670 x u D R S_cls f E) ∈
      (((Class.cab (nb095_alpha_dummy_679 x u D R S_cls f E)
            (syn_wrex (nb095_alpha_dummy_680 x u D R S_cls f E)
              (Class.cv (nb095_alpha_dummy_670 x u D R S_cls f E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_679 x u D R S_cls f E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_680 x u D R S_cls f E)))
                  (syn_csn (syn_c0c))))))).fv ∪
        ((Class.cab (nb095_alpha_dummy_679 x u D R S_cls f E)
            (syn_wrex (nb095_alpha_dummy_680 x u D R S_cls f E)
              (Class.cv (nb095_alpha_dummy_670 x u D R S_cls f E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_679 x u D R S_cls f E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_680 x u D R S_cls f E)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095_alpha_dummy_670 x u D R S_cls f E) ≠
          (nb095_alpha_dummy_679 x u D R S_cls f E) from (by
          unfold nb095_alpha_dummy_679;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar (nb095_support_mem_0732 x u D R S_cls f E) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095_alpha_dummy_670 x u D R S_cls f E) ≠
            (nb095_alpha_dummy_680 x u D R S_cls f E) from (by
            unfold nb095_alpha_dummy_680;
            with_reducible
              exact
                (Nat.ne_of_lt
                  (mem_lt_freshVar (nb095_support_mem_0732 x u D R S_cls f E) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0736 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_678 D R S_cls E) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_678 D R S_cls E))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0737 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_680 x u D R S_cls f E) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_680 x u D R S_cls f E))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0738 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_678 D R S_cls E) ∈
      (((syn_cphi (Class.cv (nb095_alpha_dummy_678 D R S_cls E)))).fv ∪
        ((syn_cphi (Class.cv (nb095_alpha_dummy_678 D R S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0739 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_680 x u D R S_cls f E) ∈
      (((syn_cphi (Class.cv (nb095_alpha_dummy_680 x u D R S_cls f E)))).fv ∪
        ((syn_cphi (Class.cv (nb095_alpha_dummy_680 x u D R S_cls f E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0740 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_000 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_000 D R S_cls E))).fv ∪ ((syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                        (syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E))))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                        (syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E)))))))).fv ∪
            ((syn_cin S_cls (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                      (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E))))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                      (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E)))))))).fv ∪
          ((syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E)))))).fv ∪ ((syn_cin E
            (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
              (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E)))))).fv) :=
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

theorem nb095_support_mem_0741 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    f ∈
      (((Class.cv f)).fv ∪ ((syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (Class.cv x))))
                    (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                        (syn_csn (Class.cv x))))))).fv ∪ ((syn_cin S_cls (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid))) (syn_csn (Class.cv u))))
                  (syn_cin E (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                      (syn_csn (Class.cv u))))))).fv ∪ ((syn_cin D
              (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (Class.cv x))))).fv ∪
        ((syn_cin E (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
              (syn_csn (Class.cv u))))).fv) :=
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

theorem nb095_support_mem_0742 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_000 D R S_cls E) ∈
      (((syn_cfv (Class.cv (nb095_alpha_dummy_000 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_003 D R S_cls E)))).fv ∪
        ((syn_cfv (Class.cv (nb095_alpha_dummy_000 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_004 D R S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cfv]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0743 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_000 D R S_cls E) ∈
      (((syn_ccompl (Class.cab (nb095_alpha_dummy_661 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_662 D R S_cls E)
                (syn_cfv (Class.cv (nb095_alpha_dummy_000 D R S_cls E))
                  (Class.cv (nb095_alpha_dummy_003 D R S_cls E)))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_661 D R S_cls E))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_662 D R S_cls E)))))))).fv ∪
        ((syn_ccompl (Class.cab (nb095_alpha_dummy_661 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_662 D R S_cls E)
                (syn_cfv (Class.cv (nb095_alpha_dummy_000 D R S_cls E))
                  (Class.cv (nb095_alpha_dummy_004 D R S_cls E)))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_661 D R S_cls E))
                  (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_662 D R S_cls E)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095_alpha_dummy_000 D R S_cls E) ≠ (nb095_alpha_dummy_661 D R S_cls E) from (by
          unfold nb095_alpha_dummy_661;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0742 D R S_cls E) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095_alpha_dummy_000 D R S_cls E) ≠ (nb095_alpha_dummy_662 D R S_cls E) from (by
            unfold nb095_alpha_dummy_662;
            with_reducible
              exact
                (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0742 D R S_cls E) 1))))
    · rw [fv_syn_cfv]
      with_reducible rw [Finset.mem_union]
      right
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0744 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    f ∈
      (((syn_cfv (Class.cv f) (Class.cv (nb095_alpha_dummy_005 x u D R S_cls f E)))).fv ∪
        ((syn_cfv (Class.cv f) (Class.cv (nb095_alpha_dummy_006 x u D R S_cls f E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cfv]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0745 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    f ∈
      (((syn_ccompl (Class.cab (nb095_alpha_dummy_663 x u D R S_cls f E)
              (syn_wrex (nb095_alpha_dummy_664 x u D R S_cls f E) (syn_cfv (Class.cv f)
                  (Class.cv (nb095_alpha_dummy_005 x u D R S_cls f E)))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_663 x u D R S_cls f E)) (syn_cphi
                    (Class.cv (nb095_alpha_dummy_664 x u D R S_cls f E)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb095_alpha_dummy_663 x u D R S_cls f E)
              (syn_wrex (nb095_alpha_dummy_664 x u D R S_cls f E) (syn_cfv (Class.cv f)
                  (Class.cv (nb095_alpha_dummy_006 x u D R S_cls f E)))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_663 x u D R S_cls f E))
                  (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_664 x u D R S_cls f E)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show f ≠ (nb095_alpha_dummy_663 x u D R S_cls f E) from (by
          unfold nb095_alpha_dummy_663;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar (nb095_support_mem_0744 x u D R S_cls f E) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show f ≠ (nb095_alpha_dummy_664 x u D R S_cls f E) from (by
            unfold nb095_alpha_dummy_664;
            with_reducible
              exact
                (Nat.ne_of_lt
                  (mem_lt_freshVar (nb095_support_mem_0744 x u D R S_cls f E) 1))))
    · rw [fv_syn_cfv]
      with_reducible rw [Finset.mem_union]
      right
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0746 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_000 D R S_cls E) ∈
      (((Class.cab (nb095_alpha_dummy_661 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_662 D R S_cls E)
              (syn_cfv (Class.cv (nb095_alpha_dummy_000 D R S_cls E))
                (Class.cv (nb095_alpha_dummy_003 D R S_cls E)))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_661 D R S_cls E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_662 D R S_cls E))))))).fv ∪
        ((Class.cab (nb095_alpha_dummy_661 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_662 D R S_cls E)
              (syn_cfv (Class.cv (nb095_alpha_dummy_000 D R S_cls E))
                (Class.cv (nb095_alpha_dummy_003 D R S_cls E)))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_661 D R S_cls E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_662 D R S_cls E))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095_alpha_dummy_000 D R S_cls E) ≠ (nb095_alpha_dummy_661 D R S_cls E) from (by
          unfold nb095_alpha_dummy_661;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0742 D R S_cls E) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095_alpha_dummy_000 D R S_cls E) ≠ (nb095_alpha_dummy_662 D R S_cls E) from (by
            unfold nb095_alpha_dummy_662;
            with_reducible
              exact
                (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0742 D R S_cls E) 1))))
    · rw [fv_syn_cfv]
      with_reducible rw [Finset.mem_union]
      right
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0747 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    f ∈
      (((Class.cab (nb095_alpha_dummy_663 x u D R S_cls f E)
            (syn_wrex (nb095_alpha_dummy_664 x u D R S_cls f E)
              (syn_cfv (Class.cv f) (Class.cv (nb095_alpha_dummy_005 x u D R S_cls f E)))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_663 x u D R S_cls f E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_664 x u D R S_cls f E))))))).fv ∪
        ((Class.cab (nb095_alpha_dummy_663 x u D R S_cls f E)
            (syn_wrex (nb095_alpha_dummy_664 x u D R S_cls f E)
              (syn_cfv (Class.cv f) (Class.cv (nb095_alpha_dummy_005 x u D R S_cls f E)))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_663 x u D R S_cls f E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_664 x u D R S_cls f E))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show f ≠ (nb095_alpha_dummy_663 x u D R S_cls f E) from (by
          unfold nb095_alpha_dummy_663;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar (nb095_support_mem_0744 x u D R S_cls f E) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show f ≠ (nb095_alpha_dummy_664 x u D R S_cls f E) from (by
            unfold nb095_alpha_dummy_664;
            with_reducible
              exact
                (Nat.ne_of_lt
                  (mem_lt_freshVar (nb095_support_mem_0744 x u D R S_cls f E) 1))))
    · rw [fv_syn_cfv]
      with_reducible rw [Finset.mem_union]
      right
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0748 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_000 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_000 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_003 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0749 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_000 D R S_cls E) ∈
      (({(nb095_alpha_dummy_669 D R S_cls E)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb095_alpha_dummy_003 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_000 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_669 D R S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_wbr]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0750 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_000 D R S_cls E) ∈
      (((Class.cab (nb095_alpha_dummy_671 D R S_cls E) (Wff.classEq
            (Class.cab (nb095_alpha_dummy_669 D R S_cls E)
              (syn_wbr (Class.cv (nb095_alpha_dummy_003 D R S_cls E))
                (Class.cv (nb095_alpha_dummy_000 D R S_cls E))
                (Class.cv (nb095_alpha_dummy_669 D R S_cls E))))
            (syn_csn (Class.cv (nb095_alpha_dummy_671 D R S_cls E)))))).fv) :=
  by
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095_alpha_dummy_000 D R S_cls E) ≠ (nb095_alpha_dummy_671 D R S_cls E) from (by
          unfold nb095_alpha_dummy_671;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0749 D R S_cls E) 0))))
  · rw [fv_wff_classEq]
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cab]
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095_alpha_dummy_000 D R S_cls E) ≠ (nb095_alpha_dummy_669 D R S_cls E) from (by
            unfold nb095_alpha_dummy_669;
            with_reducible
              exact
                (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0748 D R S_cls E) 0))))
    · rw [fv_syn_wbr]
      with_reducible rw [Finset.mem_union]
      right
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0751 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    f ∈ (((Class.cv f)).fv ∪ ((Class.cv (nb095_alpha_dummy_005 x u D R S_cls f E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0752 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    f ∈
      (({(nb095_alpha_dummy_670 x u D R S_cls f E)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb095_alpha_dummy_005 x u D R S_cls f E)) (Class.cv f)
            (Class.cv (nb095_alpha_dummy_670 x u D R S_cls f E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_wbr]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0753 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    f ∈
      (((Class.cab (nb095_alpha_dummy_672 x u D R S_cls f E) (Wff.classEq
            (Class.cab (nb095_alpha_dummy_670 x u D R S_cls f E)
              (syn_wbr (Class.cv (nb095_alpha_dummy_005 x u D R S_cls f E)) (Class.cv f)
                (Class.cv (nb095_alpha_dummy_670 x u D R S_cls f E))))
            (syn_csn (Class.cv (nb095_alpha_dummy_672 x u D R S_cls f E)))))).fv) :=
  by
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show f ≠ (nb095_alpha_dummy_672 x u D R S_cls f E) from (by
          unfold nb095_alpha_dummy_672;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar (nb095_support_mem_0752 x u D R S_cls f E) 0))))
  · rw [fv_wff_classEq]
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cab]
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show f ≠ (nb095_alpha_dummy_670 x u D R S_cls f E) from (by
            unfold nb095_alpha_dummy_670;
            with_reducible
              exact
                (Nat.ne_of_lt
                  (mem_lt_freshVar (nb095_support_mem_0751 x u D R S_cls f E) 0))))
    · rw [fv_syn_wbr]
      with_reducible rw [Finset.mem_union]
      right
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0754 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_671 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_671 D R S_cls E))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0755 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_672 x u D R S_cls f E) ∈
      (((Class.cv (nb095_alpha_dummy_672 x u D R S_cls f E))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0756 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_662 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_662 D R S_cls E))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0757 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_664 x u D R S_cls f E) ∈
      (((Class.cv (nb095_alpha_dummy_664 x u D R S_cls f E))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0758 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_715 D R S_cls E) ∈
      (((Wff.classMem (Class.cv (nb095_alpha_dummy_715 D R S_cls E)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb095_alpha_dummy_715 D R S_cls E)) (syn_c1c))).fv ∪
        ((Class.cv (nb095_alpha_dummy_715 D R S_cls E))).fv) :=
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

theorem nb095_support_mem_0759 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_717 x u D R S_cls f E) ∈
      (((Wff.classMem (Class.cv (nb095_alpha_dummy_717 x u D R S_cls f E)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb095_alpha_dummy_717 x u D R S_cls f E)) (syn_c1c))).fv ∪
        ((Class.cv (nb095_alpha_dummy_717 x u D R S_cls f E))).fv) :=
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

theorem nb095_support_mem_0760 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_715 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_715 D R S_cls E))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0761 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_717 x u D R S_cls f E) ∈
      (((Class.cv (nb095_alpha_dummy_717 x u D R S_cls f E))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0762 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_722 D R S_cls E) ∈
      (((syn_cnin (Class.cv (nb095_alpha_dummy_722 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_723 D R S_cls E)))).fv ∪
        ((syn_cnin (Class.cv (nb095_alpha_dummy_722 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_723 D R S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0763 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_725 x u D R S_cls f E) ∈
      (((syn_cnin (Class.cv (nb095_alpha_dummy_725 x u D R S_cls f E))
            (Class.cv (nb095_alpha_dummy_726 x u D R S_cls f E)))).fv ∪
        ((syn_cnin (Class.cv (nb095_alpha_dummy_725 x u D R S_cls f E))
            (Class.cv (nb095_alpha_dummy_726 x u D R S_cls f E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0764 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_722 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_722 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_723 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0765 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_725 x u D R S_cls f E) ∈
      (((Class.cv (nb095_alpha_dummy_725 x u D R S_cls f E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_726 x u D R S_cls f E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0766 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_723 D R S_cls E) ∈
      (((syn_cnin (Class.cv (nb095_alpha_dummy_722 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_723 D R S_cls E)))).fv ∪
        ((syn_cnin (Class.cv (nb095_alpha_dummy_722 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_723 D R S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0767 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_726 x u D R S_cls f E) ∈
      (((syn_cnin (Class.cv (nb095_alpha_dummy_725 x u D R S_cls f E))
            (Class.cv (nb095_alpha_dummy_726 x u D R S_cls f E)))).fv ∪
        ((syn_cnin (Class.cv (nb095_alpha_dummy_725 x u D R S_cls f E))
            (Class.cv (nb095_alpha_dummy_726 x u D R S_cls f E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0768 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_723 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_722 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_723 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0769 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_726 x u D R S_cls f E) ∈
      (((Class.cv (nb095_alpha_dummy_725 x u D R S_cls f E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_726 x u D R S_cls f E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0770 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_722 D R S_cls E) ∈
      (((syn_ccompl (Class.cv (nb095_alpha_dummy_722 D R S_cls E)))).fv ∪
        ((syn_ccompl (Class.cv (nb095_alpha_dummy_723 D R S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0771 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_725 x u D R S_cls f E) ∈
      (((syn_ccompl (Class.cv (nb095_alpha_dummy_725 x u D R S_cls f E)))).fv ∪
        ((syn_ccompl (Class.cv (nb095_alpha_dummy_726 x u D R S_cls f E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0772 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_722 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_722 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_722 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0773 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_725 x u D R S_cls f E) ∈
      (((Class.cv (nb095_alpha_dummy_725 x u D R S_cls f E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_725 x u D R S_cls f E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0774 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_723 D R S_cls E) ∈
      (((syn_ccompl (Class.cv (nb095_alpha_dummy_722 D R S_cls E)))).fv ∪
        ((syn_ccompl (Class.cv (nb095_alpha_dummy_723 D R S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0775 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_726 x u D R S_cls f E) ∈
      (((syn_ccompl (Class.cv (nb095_alpha_dummy_725 x u D R S_cls f E)))).fv ∪
        ((syn_ccompl (Class.cv (nb095_alpha_dummy_726 x u D R S_cls f E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0776 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_723 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_723 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_723 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0777 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_726 x u D R S_cls f E) ∈
      (((Class.cv (nb095_alpha_dummy_726 x u D R S_cls f E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_726 x u D R S_cls f E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0778 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_004 D R S_cls E) ∈
      (((syn_cfv (Class.cv (nb095_alpha_dummy_000 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_003 D R S_cls E)))).fv ∪
        ((syn_cfv (Class.cv (nb095_alpha_dummy_000 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_004 D R S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_cfv]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0779 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_004 D R S_cls E) ∈
      (((syn_ccompl (Class.cab (nb095_alpha_dummy_661 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_662 D R S_cls E)
                (syn_cfv (Class.cv (nb095_alpha_dummy_000 D R S_cls E))
                  (Class.cv (nb095_alpha_dummy_003 D R S_cls E)))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_661 D R S_cls E))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_662 D R S_cls E)))))))).fv ∪
        ((syn_ccompl (Class.cab (nb095_alpha_dummy_661 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_662 D R S_cls E)
                (syn_cfv (Class.cv (nb095_alpha_dummy_000 D R S_cls E))
                  (Class.cv (nb095_alpha_dummy_004 D R S_cls E)))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_661 D R S_cls E))
                  (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_662 D R S_cls E)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095_alpha_dummy_004 D R S_cls E) ≠ (nb095_alpha_dummy_661 D R S_cls E) from (by
          unfold nb095_alpha_dummy_661;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0778 D R S_cls E) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095_alpha_dummy_004 D R S_cls E) ≠ (nb095_alpha_dummy_662 D R S_cls E) from (by
            unfold nb095_alpha_dummy_662;
            with_reducible
              exact
                (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0778 D R S_cls E) 1))))
    · rw [fv_syn_cfv]
      with_reducible rw [Finset.mem_union]
      left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0780 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_006 x u D R S_cls f E) ∈
      (((syn_cfv (Class.cv f) (Class.cv (nb095_alpha_dummy_005 x u D R S_cls f E)))).fv ∪
        ((syn_cfv (Class.cv f) (Class.cv (nb095_alpha_dummy_006 x u D R S_cls f E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_cfv]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0781 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_006 x u D R S_cls f E) ∈
      (((syn_ccompl (Class.cab (nb095_alpha_dummy_663 x u D R S_cls f E)
              (syn_wrex (nb095_alpha_dummy_664 x u D R S_cls f E) (syn_cfv (Class.cv f)
                  (Class.cv (nb095_alpha_dummy_005 x u D R S_cls f E)))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_663 x u D R S_cls f E)) (syn_cphi
                    (Class.cv (nb095_alpha_dummy_664 x u D R S_cls f E)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb095_alpha_dummy_663 x u D R S_cls f E)
              (syn_wrex (nb095_alpha_dummy_664 x u D R S_cls f E) (syn_cfv (Class.cv f)
                  (Class.cv (nb095_alpha_dummy_006 x u D R S_cls f E)))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_663 x u D R S_cls f E))
                  (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_664 x u D R S_cls f E)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095_alpha_dummy_006 x u D R S_cls f E) ≠
          (nb095_alpha_dummy_663 x u D R S_cls f E) from (by
          unfold nb095_alpha_dummy_663;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar (nb095_support_mem_0780 x u D R S_cls f E) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095_alpha_dummy_006 x u D R S_cls f E) ≠
            (nb095_alpha_dummy_664 x u D R S_cls f E) from (by
            unfold nb095_alpha_dummy_664;
            with_reducible
              exact
                (Nat.ne_of_lt
                  (mem_lt_freshVar (nb095_support_mem_0780 x u D R S_cls f E) 1))))
    · rw [fv_syn_cfv]
      with_reducible rw [Finset.mem_union]
      left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0782 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_004 D R S_cls E) ∈
      (((Class.cab (nb095_alpha_dummy_661 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_662 D R S_cls E)
              (syn_cfv (Class.cv (nb095_alpha_dummy_000 D R S_cls E))
                (Class.cv (nb095_alpha_dummy_004 D R S_cls E)))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_661 D R S_cls E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_662 D R S_cls E)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb095_alpha_dummy_661 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_662 D R S_cls E)
              (syn_cfv (Class.cv (nb095_alpha_dummy_000 D R S_cls E))
                (Class.cv (nb095_alpha_dummy_004 D R S_cls E)))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_661 D R S_cls E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_662 D R S_cls E)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095_alpha_dummy_004 D R S_cls E) ≠ (nb095_alpha_dummy_661 D R S_cls E) from (by
          unfold nb095_alpha_dummy_661;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0778 D R S_cls E) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095_alpha_dummy_004 D R S_cls E) ≠ (nb095_alpha_dummy_662 D R S_cls E) from (by
            unfold nb095_alpha_dummy_662;
            with_reducible
              exact
                (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0778 D R S_cls E) 1))))
    · rw [fv_syn_cfv]
      with_reducible rw [Finset.mem_union]
      left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0783 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_006 x u D R S_cls f E) ∈
      (((Class.cab (nb095_alpha_dummy_663 x u D R S_cls f E)
            (syn_wrex (nb095_alpha_dummy_664 x u D R S_cls f E)
              (syn_cfv (Class.cv f) (Class.cv (nb095_alpha_dummy_006 x u D R S_cls f E)))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_663 x u D R S_cls f E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_664 x u D R S_cls f E)))
                  (syn_csn (syn_c0c))))))).fv ∪
        ((Class.cab (nb095_alpha_dummy_663 x u D R S_cls f E)
            (syn_wrex (nb095_alpha_dummy_664 x u D R S_cls f E)
              (syn_cfv (Class.cv f) (Class.cv (nb095_alpha_dummy_006 x u D R S_cls f E)))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_663 x u D R S_cls f E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_664 x u D R S_cls f E)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095_alpha_dummy_006 x u D R S_cls f E) ≠
          (nb095_alpha_dummy_663 x u D R S_cls f E) from (by
          unfold nb095_alpha_dummy_663;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar (nb095_support_mem_0780 x u D R S_cls f E) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095_alpha_dummy_006 x u D R S_cls f E) ≠
            (nb095_alpha_dummy_664 x u D R S_cls f E) from (by
            unfold nb095_alpha_dummy_664;
            with_reducible
              exact
                (Nat.ne_of_lt
                  (mem_lt_freshVar (nb095_support_mem_0780 x u D R S_cls f E) 1))))
    · rw [fv_syn_cfv]
      with_reducible rw [Finset.mem_union]
      left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0784 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_004 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_000 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_004 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0785 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_004 D R S_cls E) ∈
      (({(nb095_alpha_dummy_739 D R S_cls E)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb095_alpha_dummy_004 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_000 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_739 D R S_cls E)))).fv) :=
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

theorem nb095_support_mem_0786 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_004 D R S_cls E) ∈
      (((Class.cab (nb095_alpha_dummy_741 D R S_cls E) (Wff.classEq
            (Class.cab (nb095_alpha_dummy_739 D R S_cls E)
              (syn_wbr (Class.cv (nb095_alpha_dummy_004 D R S_cls E))
                (Class.cv (nb095_alpha_dummy_000 D R S_cls E))
                (Class.cv (nb095_alpha_dummy_739 D R S_cls E))))
            (syn_csn (Class.cv (nb095_alpha_dummy_741 D R S_cls E)))))).fv) :=
  by
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095_alpha_dummy_004 D R S_cls E) ≠ (nb095_alpha_dummy_741 D R S_cls E) from (by
          unfold nb095_alpha_dummy_741;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0785 D R S_cls E) 0))))
  · rw [fv_wff_classEq]
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cab]
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095_alpha_dummy_004 D R S_cls E) ≠ (nb095_alpha_dummy_739 D R S_cls E) from (by
            unfold nb095_alpha_dummy_739;
            with_reducible
              exact
                (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0784 D R S_cls E) 0))))
    · rw [fv_syn_wbr]
      with_reducible rw [Finset.mem_union]
      left
      with_reducible rw [Finset.mem_union]
      left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0787 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_006 x u D R S_cls f E) ∈
      (((Class.cv f)).fv ∪ ((Class.cv (nb095_alpha_dummy_006 x u D R S_cls f E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0788 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_006 x u D R S_cls f E) ∈
      (({(nb095_alpha_dummy_740 x u D R S_cls f E)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb095_alpha_dummy_006 x u D R S_cls f E)) (Class.cv f)
            (Class.cv (nb095_alpha_dummy_740 x u D R S_cls f E)))).fv) :=
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

theorem nb095_support_mem_0789 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_006 x u D R S_cls f E) ∈
      (((Class.cab (nb095_alpha_dummy_742 x u D R S_cls f E) (Wff.classEq
            (Class.cab (nb095_alpha_dummy_740 x u D R S_cls f E)
              (syn_wbr (Class.cv (nb095_alpha_dummy_006 x u D R S_cls f E)) (Class.cv f)
                (Class.cv (nb095_alpha_dummy_740 x u D R S_cls f E))))
            (syn_csn (Class.cv (nb095_alpha_dummy_742 x u D R S_cls f E)))))).fv) :=
  by
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095_alpha_dummy_006 x u D R S_cls f E) ≠
          (nb095_alpha_dummy_742 x u D R S_cls f E) from (by
          unfold nb095_alpha_dummy_742;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar (nb095_support_mem_0788 x u D R S_cls f E) 0))))
  · rw [fv_wff_classEq]
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cab]
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095_alpha_dummy_006 x u D R S_cls f E) ≠
            (nb095_alpha_dummy_740 x u D R S_cls f E) from (by
            unfold nb095_alpha_dummy_740;
            with_reducible
              exact
                (Nat.ne_of_lt
                  (mem_lt_freshVar (nb095_support_mem_0787 x u D R S_cls f E) 0))))
    · rw [fv_syn_wbr]
      with_reducible rw [Finset.mem_union]
      left
      with_reducible rw [Finset.mem_union]
      left
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0790 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_004 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_004 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_739 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0791 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_004 D R S_cls E) ∈
      (((syn_ccompl (Class.cab (nb095_alpha_dummy_747 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_748 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_004 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_747 D R S_cls E))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_748 D R S_cls E)))))))).fv ∪
        ((syn_ccompl (Class.cab (nb095_alpha_dummy_747 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_748 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_739 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_747 D R S_cls E))
                  (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_748 D R S_cls E)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095_alpha_dummy_004 D R S_cls E) ≠ (nb095_alpha_dummy_747 D R S_cls E) from (by
          unfold nb095_alpha_dummy_747;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0790 D R S_cls E) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095_alpha_dummy_004 D R S_cls E) ≠ (nb095_alpha_dummy_748 D R S_cls E) from (by
            unfold nb095_alpha_dummy_748;
            with_reducible
              exact
                (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0790 D R S_cls E) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0792 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_006 x u D R S_cls f E) ∈
      (((Class.cv (nb095_alpha_dummy_006 x u D R S_cls f E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_740 x u D R S_cls f E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0793 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_006 x u D R S_cls f E) ∈
      (((syn_ccompl (Class.cab (nb095_alpha_dummy_749 x u D R S_cls f E)
              (syn_wrex (nb095_alpha_dummy_750 x u D R S_cls f E)
                (Class.cv (nb095_alpha_dummy_006 x u D R S_cls f E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_749 x u D R S_cls f E)) (syn_cphi
                    (Class.cv (nb095_alpha_dummy_750 x u D R S_cls f E)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb095_alpha_dummy_749 x u D R S_cls f E)
              (syn_wrex (nb095_alpha_dummy_750 x u D R S_cls f E)
                (Class.cv (nb095_alpha_dummy_740 x u D R S_cls f E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_749 x u D R S_cls f E))
                  (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_750 x u D R S_cls f E)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095_alpha_dummy_006 x u D R S_cls f E) ≠
          (nb095_alpha_dummy_749 x u D R S_cls f E) from (by
          unfold nb095_alpha_dummy_749;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar (nb095_support_mem_0792 x u D R S_cls f E) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095_alpha_dummy_006 x u D R S_cls f E) ≠
            (nb095_alpha_dummy_750 x u D R S_cls f E) from (by
            unfold nb095_alpha_dummy_750;
            with_reducible
              exact
                (Nat.ne_of_lt
                  (mem_lt_freshVar (nb095_support_mem_0792 x u D R S_cls f E) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0794 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_004 D R S_cls E) ∈
      (((Class.cab (nb095_alpha_dummy_747 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_748 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_004 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_747 D R S_cls E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_748 D R S_cls E))))))).fv ∪
        ((Class.cab (nb095_alpha_dummy_747 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_748 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_004 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_747 D R S_cls E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_748 D R S_cls E))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095_alpha_dummy_004 D R S_cls E) ≠ (nb095_alpha_dummy_747 D R S_cls E) from (by
          unfold nb095_alpha_dummy_747;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0790 D R S_cls E) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095_alpha_dummy_004 D R S_cls E) ≠ (nb095_alpha_dummy_748 D R S_cls E) from (by
            unfold nb095_alpha_dummy_748;
            with_reducible
              exact
                (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0790 D R S_cls E) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0795 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_006 x u D R S_cls f E) ∈
      (((Class.cab (nb095_alpha_dummy_749 x u D R S_cls f E)
            (syn_wrex (nb095_alpha_dummy_750 x u D R S_cls f E)
              (Class.cv (nb095_alpha_dummy_006 x u D R S_cls f E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_749 x u D R S_cls f E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_750 x u D R S_cls f E))))))).fv ∪
        ((Class.cab (nb095_alpha_dummy_749 x u D R S_cls f E)
            (syn_wrex (nb095_alpha_dummy_750 x u D R S_cls f E)
              (Class.cv (nb095_alpha_dummy_006 x u D R S_cls f E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_749 x u D R S_cls f E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_750 x u D R S_cls f E))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095_alpha_dummy_006 x u D R S_cls f E) ≠
          (nb095_alpha_dummy_749 x u D R S_cls f E) from (by
          unfold nb095_alpha_dummy_749;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar (nb095_support_mem_0792 x u D R S_cls f E) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095_alpha_dummy_006 x u D R S_cls f E) ≠
            (nb095_alpha_dummy_750 x u D R S_cls f E) from (by
            unfold nb095_alpha_dummy_750;
            with_reducible
              exact
                (Nat.ne_of_lt
                  (mem_lt_freshVar (nb095_support_mem_0792 x u D R S_cls f E) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0796 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_748 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_748 D R S_cls E))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0797 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_750 x u D R S_cls f E) ∈
      (((Class.cv (nb095_alpha_dummy_750 x u D R S_cls f E))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0798 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_755 D R S_cls E) ∈
      (((Wff.classMem (Class.cv (nb095_alpha_dummy_755 D R S_cls E)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb095_alpha_dummy_755 D R S_cls E)) (syn_c1c))).fv ∪
        ((Class.cv (nb095_alpha_dummy_755 D R S_cls E))).fv) :=
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

theorem nb095_support_mem_0799 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_757 x u D R S_cls f E) ∈
      (((Wff.classMem (Class.cv (nb095_alpha_dummy_757 x u D R S_cls f E)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb095_alpha_dummy_757 x u D R S_cls f E)) (syn_c1c))).fv ∪
        ((Class.cv (nb095_alpha_dummy_757 x u D R S_cls f E))).fv) :=
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

theorem nb095_support_mem_0800 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_755 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_755 D R S_cls E))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0801 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_757 x u D R S_cls f E) ∈
      (((Class.cv (nb095_alpha_dummy_757 x u D R S_cls f E))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0802 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_762 D R S_cls E) ∈
      (((syn_cnin (Class.cv (nb095_alpha_dummy_762 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_763 D R S_cls E)))).fv ∪
        ((syn_cnin (Class.cv (nb095_alpha_dummy_762 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_763 D R S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0803 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_765 x u D R S_cls f E) ∈
      (((syn_cnin (Class.cv (nb095_alpha_dummy_765 x u D R S_cls f E))
            (Class.cv (nb095_alpha_dummy_766 x u D R S_cls f E)))).fv ∪
        ((syn_cnin (Class.cv (nb095_alpha_dummy_765 x u D R S_cls f E))
            (Class.cv (nb095_alpha_dummy_766 x u D R S_cls f E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0804 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_762 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_762 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_763 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0805 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_765 x u D R S_cls f E) ∈
      (((Class.cv (nb095_alpha_dummy_765 x u D R S_cls f E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_766 x u D R S_cls f E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0806 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_763 D R S_cls E) ∈
      (((syn_cnin (Class.cv (nb095_alpha_dummy_762 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_763 D R S_cls E)))).fv ∪
        ((syn_cnin (Class.cv (nb095_alpha_dummy_762 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_763 D R S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0807 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_766 x u D R S_cls f E) ∈
      (((syn_cnin (Class.cv (nb095_alpha_dummy_765 x u D R S_cls f E))
            (Class.cv (nb095_alpha_dummy_766 x u D R S_cls f E)))).fv ∪
        ((syn_cnin (Class.cv (nb095_alpha_dummy_765 x u D R S_cls f E))
            (Class.cv (nb095_alpha_dummy_766 x u D R S_cls f E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0808 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_763 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_762 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_763 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0809 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_766 x u D R S_cls f E) ∈
      (((Class.cv (nb095_alpha_dummy_765 x u D R S_cls f E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_766 x u D R S_cls f E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0810 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_762 D R S_cls E) ∈
      (((syn_ccompl (Class.cv (nb095_alpha_dummy_762 D R S_cls E)))).fv ∪
        ((syn_ccompl (Class.cv (nb095_alpha_dummy_763 D R S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0811 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_765 x u D R S_cls f E) ∈
      (((syn_ccompl (Class.cv (nb095_alpha_dummy_765 x u D R S_cls f E)))).fv ∪
        ((syn_ccompl (Class.cv (nb095_alpha_dummy_766 x u D R S_cls f E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0812 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_762 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_762 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_762 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0813 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_765 x u D R S_cls f E) ∈
      (((Class.cv (nb095_alpha_dummy_765 x u D R S_cls f E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_765 x u D R S_cls f E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0814 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_763 D R S_cls E) ∈
      (((syn_ccompl (Class.cv (nb095_alpha_dummy_762 D R S_cls E)))).fv ∪
        ((syn_ccompl (Class.cv (nb095_alpha_dummy_763 D R S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0815 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_766 x u D R S_cls f E) ∈
      (((syn_ccompl (Class.cv (nb095_alpha_dummy_765 x u D R S_cls f E)))).fv ∪
        ((syn_ccompl (Class.cv (nb095_alpha_dummy_766 x u D R S_cls f E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0816 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_763 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_763 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_763 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0817 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_766 x u D R S_cls f E) ∈
      (((Class.cv (nb095_alpha_dummy_766 x u D R S_cls f E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_766 x u D R S_cls f E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0818 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_739 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_004 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_739 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0819 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_739 D R S_cls E) ∈
      (((syn_ccompl (Class.cab (nb095_alpha_dummy_747 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_748 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_004 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_747 D R S_cls E))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_748 D R S_cls E)))))))).fv ∪
        ((syn_ccompl (Class.cab (nb095_alpha_dummy_747 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_748 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_739 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_747 D R S_cls E))
                  (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_748 D R S_cls E)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095_alpha_dummy_739 D R S_cls E) ≠ (nb095_alpha_dummy_747 D R S_cls E) from (by
          unfold nb095_alpha_dummy_747;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0818 D R S_cls E) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095_alpha_dummy_739 D R S_cls E) ≠ (nb095_alpha_dummy_748 D R S_cls E) from (by
            unfold nb095_alpha_dummy_748;
            with_reducible
              exact
                (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0818 D R S_cls E) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0820 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_740 x u D R S_cls f E) ∈
      (((Class.cv (nb095_alpha_dummy_006 x u D R S_cls f E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_740 x u D R S_cls f E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0821 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_740 x u D R S_cls f E) ∈
      (((syn_ccompl (Class.cab (nb095_alpha_dummy_749 x u D R S_cls f E)
              (syn_wrex (nb095_alpha_dummy_750 x u D R S_cls f E)
                (Class.cv (nb095_alpha_dummy_006 x u D R S_cls f E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_749 x u D R S_cls f E)) (syn_cphi
                    (Class.cv (nb095_alpha_dummy_750 x u D R S_cls f E)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb095_alpha_dummy_749 x u D R S_cls f E)
              (syn_wrex (nb095_alpha_dummy_750 x u D R S_cls f E)
                (Class.cv (nb095_alpha_dummy_740 x u D R S_cls f E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_749 x u D R S_cls f E))
                  (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_750 x u D R S_cls f E)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095_alpha_dummy_740 x u D R S_cls f E) ≠
          (nb095_alpha_dummy_749 x u D R S_cls f E) from (by
          unfold nb095_alpha_dummy_749;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar (nb095_support_mem_0820 x u D R S_cls f E) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095_alpha_dummy_740 x u D R S_cls f E) ≠
            (nb095_alpha_dummy_750 x u D R S_cls f E) from (by
            unfold nb095_alpha_dummy_750;
            with_reducible
              exact
                (Nat.ne_of_lt
                  (mem_lt_freshVar (nb095_support_mem_0820 x u D R S_cls f E) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0822 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_739 D R S_cls E) ∈
      (((Class.cab (nb095_alpha_dummy_747 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_748 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_739 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_747 D R S_cls E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_748 D R S_cls E)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb095_alpha_dummy_747 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_748 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_739 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_747 D R S_cls E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_748 D R S_cls E)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095_alpha_dummy_739 D R S_cls E) ≠ (nb095_alpha_dummy_747 D R S_cls E) from (by
          unfold nb095_alpha_dummy_747;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0818 D R S_cls E) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095_alpha_dummy_739 D R S_cls E) ≠ (nb095_alpha_dummy_748 D R S_cls E) from (by
            unfold nb095_alpha_dummy_748;
            with_reducible
              exact
                (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0818 D R S_cls E) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0823 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_740 x u D R S_cls f E) ∈
      (((Class.cab (nb095_alpha_dummy_749 x u D R S_cls f E)
            (syn_wrex (nb095_alpha_dummy_750 x u D R S_cls f E)
              (Class.cv (nb095_alpha_dummy_740 x u D R S_cls f E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_749 x u D R S_cls f E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_750 x u D R S_cls f E)))
                  (syn_csn (syn_c0c))))))).fv ∪
        ((Class.cab (nb095_alpha_dummy_749 x u D R S_cls f E)
            (syn_wrex (nb095_alpha_dummy_750 x u D R S_cls f E)
              (Class.cv (nb095_alpha_dummy_740 x u D R S_cls f E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_749 x u D R S_cls f E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_750 x u D R S_cls f E)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095_alpha_dummy_740 x u D R S_cls f E) ≠
          (nb095_alpha_dummy_749 x u D R S_cls f E) from (by
          unfold nb095_alpha_dummy_749;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar (nb095_support_mem_0820 x u D R S_cls f E) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095_alpha_dummy_740 x u D R S_cls f E) ≠
            (nb095_alpha_dummy_750 x u D R S_cls f E) from (by
            unfold nb095_alpha_dummy_750;
            with_reducible
              exact
                (Nat.ne_of_lt
                  (mem_lt_freshVar (nb095_support_mem_0820 x u D R S_cls f E) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _


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

theorem nb095_support_mem_0824 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_748 D R S_cls E) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_748 D R S_cls E))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0825 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_750 x u D R S_cls f E) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_750 x u D R S_cls f E))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0826 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_748 D R S_cls E) ∈
      (((syn_cphi (Class.cv (nb095_alpha_dummy_748 D R S_cls E)))).fv ∪
        ((syn_cphi (Class.cv (nb095_alpha_dummy_748 D R S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0827 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_750 x u D R S_cls f E) ∈
      (((syn_cphi (Class.cv (nb095_alpha_dummy_750 x u D R S_cls f E)))).fv ∪
        ((syn_cphi (Class.cv (nb095_alpha_dummy_750 x u D R S_cls f E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0828 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_000 D R S_cls E) ∈
      (((Class.cab (nb095_alpha_dummy_661 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_662 D R S_cls E)
              (syn_cfv (Class.cv (nb095_alpha_dummy_000 D R S_cls E))
                (Class.cv (nb095_alpha_dummy_004 D R S_cls E)))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_661 D R S_cls E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_662 D R S_cls E)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb095_alpha_dummy_661 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_662 D R S_cls E)
              (syn_cfv (Class.cv (nb095_alpha_dummy_000 D R S_cls E))
                (Class.cv (nb095_alpha_dummy_004 D R S_cls E)))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_661 D R S_cls E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_662 D R S_cls E)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095_alpha_dummy_000 D R S_cls E) ≠ (nb095_alpha_dummy_661 D R S_cls E) from (by
          unfold nb095_alpha_dummy_661;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0742 D R S_cls E) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095_alpha_dummy_000 D R S_cls E) ≠ (nb095_alpha_dummy_662 D R S_cls E) from (by
            unfold nb095_alpha_dummy_662;
            with_reducible
              exact
                (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0742 D R S_cls E) 1))))
    · rw [fv_syn_cfv]
      with_reducible rw [Finset.mem_union]
      right
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0829 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    f ∈
      (((Class.cab (nb095_alpha_dummy_663 x u D R S_cls f E)
            (syn_wrex (nb095_alpha_dummy_664 x u D R S_cls f E)
              (syn_cfv (Class.cv f) (Class.cv (nb095_alpha_dummy_006 x u D R S_cls f E)))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_663 x u D R S_cls f E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_664 x u D R S_cls f E)))
                  (syn_csn (syn_c0c))))))).fv ∪
        ((Class.cab (nb095_alpha_dummy_663 x u D R S_cls f E)
            (syn_wrex (nb095_alpha_dummy_664 x u D R S_cls f E)
              (syn_cfv (Class.cv f) (Class.cv (nb095_alpha_dummy_006 x u D R S_cls f E)))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_663 x u D R S_cls f E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_664 x u D R S_cls f E)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show f ≠ (nb095_alpha_dummy_663 x u D R S_cls f E) from (by
          unfold nb095_alpha_dummy_663;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar (nb095_support_mem_0744 x u D R S_cls f E) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show f ≠ (nb095_alpha_dummy_664 x u D R S_cls f E) from (by
            unfold nb095_alpha_dummy_664;
            with_reducible
              exact
                (Nat.ne_of_lt
                  (mem_lt_freshVar (nb095_support_mem_0744 x u D R S_cls f E) 1))))
    · rw [fv_syn_cfv]
      with_reducible rw [Finset.mem_union]
      right
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0830 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_000 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_000 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_004 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0831 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_000 D R S_cls E) ∈
      (({(nb095_alpha_dummy_739 D R S_cls E)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb095_alpha_dummy_004 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_000 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_739 D R S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_wbr]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0832 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_000 D R S_cls E) ∈
      (((Class.cab (nb095_alpha_dummy_741 D R S_cls E) (Wff.classEq
            (Class.cab (nb095_alpha_dummy_739 D R S_cls E)
              (syn_wbr (Class.cv (nb095_alpha_dummy_004 D R S_cls E))
                (Class.cv (nb095_alpha_dummy_000 D R S_cls E))
                (Class.cv (nb095_alpha_dummy_739 D R S_cls E))))
            (syn_csn (Class.cv (nb095_alpha_dummy_741 D R S_cls E)))))).fv) :=
  by
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095_alpha_dummy_000 D R S_cls E) ≠ (nb095_alpha_dummy_741 D R S_cls E) from (by
          unfold nb095_alpha_dummy_741;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0831 D R S_cls E) 0))))
  · rw [fv_wff_classEq]
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cab]
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095_alpha_dummy_000 D R S_cls E) ≠ (nb095_alpha_dummy_739 D R S_cls E) from (by
            unfold nb095_alpha_dummy_739;
            with_reducible
              exact
                (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0830 D R S_cls E) 0))))
    · rw [fv_syn_wbr]
      with_reducible rw [Finset.mem_union]
      right
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0833 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    f ∈ (((Class.cv f)).fv ∪ ((Class.cv (nb095_alpha_dummy_006 x u D R S_cls f E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0834 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    f ∈
      (({(nb095_alpha_dummy_740 x u D R S_cls f E)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb095_alpha_dummy_006 x u D R S_cls f E)) (Class.cv f)
            (Class.cv (nb095_alpha_dummy_740 x u D R S_cls f E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_wbr]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0835 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    f ∈
      (((Class.cab (nb095_alpha_dummy_742 x u D R S_cls f E) (Wff.classEq
            (Class.cab (nb095_alpha_dummy_740 x u D R S_cls f E)
              (syn_wbr (Class.cv (nb095_alpha_dummy_006 x u D R S_cls f E)) (Class.cv f)
                (Class.cv (nb095_alpha_dummy_740 x u D R S_cls f E))))
            (syn_csn (Class.cv (nb095_alpha_dummy_742 x u D R S_cls f E)))))).fv) :=
  by
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show f ≠ (nb095_alpha_dummy_742 x u D R S_cls f E) from (by
          unfold nb095_alpha_dummy_742;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar (nb095_support_mem_0834 x u D R S_cls f E) 0))))
  · rw [fv_wff_classEq]
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_class_cab]
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show f ≠ (nb095_alpha_dummy_740 x u D R S_cls f E) from (by
            unfold nb095_alpha_dummy_740;
            with_reducible
              exact
                (Nat.ne_of_lt
                  (mem_lt_freshVar (nb095_support_mem_0833 x u D R S_cls f E) 0))))
    · rw [fv_syn_wbr]
      with_reducible rw [Finset.mem_union]
      right
      rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0836 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_741 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_741 D R S_cls E))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0837 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_742 x u D R S_cls f E) ∈
      (((Class.cv (nb095_alpha_dummy_742 x u D R S_cls f E))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0838 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_662 D R S_cls E) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_662 D R S_cls E))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0839 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_664 x u D R S_cls f E) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_664 x u D R S_cls f E))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0840 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_662 D R S_cls E) ∈
      (((syn_cphi (Class.cv (nb095_alpha_dummy_662 D R S_cls E)))).fv ∪
        ((syn_cphi (Class.cv (nb095_alpha_dummy_662 D R S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0841 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095_alpha_dummy_664 x u D R S_cls f E) ∈
      (((syn_cphi (Class.cv (nb095_alpha_dummy_664 x u D R S_cls f E)))).fv ∪
        ((syn_cphi (Class.cv (nb095_alpha_dummy_664 x u D R S_cls f E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0842 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_793 D R S_cls E) ∈
      (({(nb095_alpha_dummy_793 D R S_cls E)} : Finset Var) ∪
          ({(nb095_alpha_dummy_794 D R S_cls E)} : Finset Var) ∪ ((syn_wa
            (Wff.classMem (Class.cv (nb095_alpha_dummy_793 D R S_cls E)) (syn_cin E
                (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                  (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E))))))
            (Wff.classMem (Class.cv (nb095_alpha_dummy_794 D R S_cls E)) (syn_cin E
                (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                  (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0843 (u : Var) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_795 u S_cls E) ∈
      (({(nb095_alpha_dummy_795 u S_cls E)} : Finset Var) ∪
          ({(nb095_alpha_dummy_796 u S_cls E)} : Finset Var) ∪ ((syn_wa
            (Wff.classMem (Class.cv (nb095_alpha_dummy_795 u S_cls E)) (syn_cin E
                (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid))) (syn_csn (Class.cv u)))))
            (Wff.classMem (Class.cv (nb095_alpha_dummy_796 u S_cls E)) (syn_cin E
                (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                  (syn_csn (Class.cv u))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0844 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_794 D R S_cls E) ∈
      (({(nb095_alpha_dummy_793 D R S_cls E)} : Finset Var) ∪
          ({(nb095_alpha_dummy_794 D R S_cls E)} : Finset Var) ∪ ((syn_wa
            (Wff.classMem (Class.cv (nb095_alpha_dummy_793 D R S_cls E)) (syn_cin E
                (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                  (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E))))))
            (Wff.classMem (Class.cv (nb095_alpha_dummy_794 D R S_cls E)) (syn_cin E
                (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                  (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0845 (u : Var) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_796 u S_cls E) ∈
      (({(nb095_alpha_dummy_795 u S_cls E)} : Finset Var) ∪
          ({(nb095_alpha_dummy_796 u S_cls E)} : Finset Var) ∪ ((syn_wa
            (Wff.classMem (Class.cv (nb095_alpha_dummy_795 u S_cls E)) (syn_cin E
                (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid))) (syn_csn (Class.cv u)))))
            (Wff.classMem (Class.cv (nb095_alpha_dummy_796 u S_cls E)) (syn_cin E
                (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                  (syn_csn (Class.cv u))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0846 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_793 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_793 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_794 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0847 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_793 D R S_cls E) ∈
      (((syn_ccompl (Class.cab (nb095_alpha_dummy_799 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_800 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_793 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_799 D R S_cls E))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_800 D R S_cls E)))))))).fv ∪
        ((syn_ccompl (Class.cab (nb095_alpha_dummy_799 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_800 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_794 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_799 D R S_cls E))
                  (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_800 D R S_cls E)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095_alpha_dummy_793 D R S_cls E) ≠ (nb095_alpha_dummy_799 D R S_cls E) from (by
          unfold nb095_alpha_dummy_799;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0846 D R S_cls E) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095_alpha_dummy_793 D R S_cls E) ≠ (nb095_alpha_dummy_800 D R S_cls E) from (by
            unfold nb095_alpha_dummy_800;
            with_reducible
              exact
                (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0846 D R S_cls E) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0848 (u : Var) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_795 u S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_795 u S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_796 u S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0849 (u : Var) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_795 u S_cls E) ∈
      (((syn_ccompl (Class.cab (nb095_alpha_dummy_801 u S_cls E)
              (syn_wrex (nb095_alpha_dummy_802 u S_cls E)
                (Class.cv (nb095_alpha_dummy_795 u S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_801 u S_cls E))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_802 u S_cls E)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb095_alpha_dummy_801 u S_cls E)
              (syn_wrex (nb095_alpha_dummy_802 u S_cls E)
                (Class.cv (nb095_alpha_dummy_796 u S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_801 u S_cls E))
                  (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_802 u S_cls E)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095_alpha_dummy_795 u S_cls E) ≠ (nb095_alpha_dummy_801 u S_cls E) from (by
          unfold nb095_alpha_dummy_801;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0848 u S_cls E) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095_alpha_dummy_795 u S_cls E) ≠ (nb095_alpha_dummy_802 u S_cls E) from (by
            unfold nb095_alpha_dummy_802;
            with_reducible
              exact
                (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0848 u S_cls E) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0850 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_793 D R S_cls E) ∈
      (((Class.cab (nb095_alpha_dummy_799 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_800 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_793 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_799 D R S_cls E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_800 D R S_cls E))))))).fv ∪
        ((Class.cab (nb095_alpha_dummy_799 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_800 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_793 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_799 D R S_cls E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_800 D R S_cls E))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095_alpha_dummy_793 D R S_cls E) ≠ (nb095_alpha_dummy_799 D R S_cls E) from (by
          unfold nb095_alpha_dummy_799;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0846 D R S_cls E) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095_alpha_dummy_793 D R S_cls E) ≠ (nb095_alpha_dummy_800 D R S_cls E) from (by
            unfold nb095_alpha_dummy_800;
            with_reducible
              exact
                (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0846 D R S_cls E) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0851 (u : Var) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_795 u S_cls E) ∈
      (((Class.cab (nb095_alpha_dummy_801 u S_cls E) (syn_wrex (nb095_alpha_dummy_802 u S_cls E)
              (Class.cv (nb095_alpha_dummy_795 u S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_801 u S_cls E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_802 u S_cls E))))))).fv ∪
        ((Class.cab (nb095_alpha_dummy_801 u S_cls E)
            (syn_wrex (nb095_alpha_dummy_802 u S_cls E)
              (Class.cv (nb095_alpha_dummy_795 u S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_801 u S_cls E))
                (syn_cphi (Class.cv (nb095_alpha_dummy_802 u S_cls E))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095_alpha_dummy_795 u S_cls E) ≠ (nb095_alpha_dummy_801 u S_cls E) from (by
          unfold nb095_alpha_dummy_801;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0848 u S_cls E) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095_alpha_dummy_795 u S_cls E) ≠ (nb095_alpha_dummy_802 u S_cls E) from (by
            unfold nb095_alpha_dummy_802;
            with_reducible
              exact
                (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0848 u S_cls E) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0852 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_800 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_800 D R S_cls E))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0853 (u : Var) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_802 u S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_802 u S_cls E))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0854 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_807 D R S_cls E) ∈
      (((Wff.classMem (Class.cv (nb095_alpha_dummy_807 D R S_cls E)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb095_alpha_dummy_807 D R S_cls E)) (syn_c1c))).fv ∪
        ((Class.cv (nb095_alpha_dummy_807 D R S_cls E))).fv) :=
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

theorem nb095_support_mem_0855 (u : Var) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_809 u S_cls E) ∈
      (((Wff.classMem (Class.cv (nb095_alpha_dummy_809 u S_cls E)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb095_alpha_dummy_809 u S_cls E)) (syn_c1c))).fv ∪
        ((Class.cv (nb095_alpha_dummy_809 u S_cls E))).fv) :=
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

theorem nb095_support_mem_0856 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_807 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_807 D R S_cls E))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0857 (u : Var) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_809 u S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_809 u S_cls E))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0858 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_814 D R S_cls E) ∈
      (((syn_cnin (Class.cv (nb095_alpha_dummy_814 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_815 D R S_cls E)))).fv ∪
        ((syn_cnin (Class.cv (nb095_alpha_dummy_814 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_815 D R S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0859 (u : Var) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_817 u S_cls E) ∈
      (((syn_cnin (Class.cv (nb095_alpha_dummy_817 u S_cls E))
            (Class.cv (nb095_alpha_dummy_818 u S_cls E)))).fv ∪
        ((syn_cnin (Class.cv (nb095_alpha_dummy_817 u S_cls E))
            (Class.cv (nb095_alpha_dummy_818 u S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0860 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_814 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_814 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_815 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0861 (u : Var) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_817 u S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_817 u S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_818 u S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0862 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_815 D R S_cls E) ∈
      (((syn_cnin (Class.cv (nb095_alpha_dummy_814 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_815 D R S_cls E)))).fv ∪
        ((syn_cnin (Class.cv (nb095_alpha_dummy_814 D R S_cls E))
            (Class.cv (nb095_alpha_dummy_815 D R S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0863 (u : Var) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_818 u S_cls E) ∈
      (((syn_cnin (Class.cv (nb095_alpha_dummy_817 u S_cls E))
            (Class.cv (nb095_alpha_dummy_818 u S_cls E)))).fv ∪
        ((syn_cnin (Class.cv (nb095_alpha_dummy_817 u S_cls E))
            (Class.cv (nb095_alpha_dummy_818 u S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0864 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_815 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_814 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_815 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0865 (u : Var) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_818 u S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_817 u S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_818 u S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0866 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_814 D R S_cls E) ∈
      (((syn_ccompl (Class.cv (nb095_alpha_dummy_814 D R S_cls E)))).fv ∪
        ((syn_ccompl (Class.cv (nb095_alpha_dummy_815 D R S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0867 (u : Var) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_817 u S_cls E) ∈
      (((syn_ccompl (Class.cv (nb095_alpha_dummy_817 u S_cls E)))).fv ∪
        ((syn_ccompl (Class.cv (nb095_alpha_dummy_818 u S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0868 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_814 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_814 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_814 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0869 (u : Var) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_817 u S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_817 u S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_817 u S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0870 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_815 D R S_cls E) ∈
      (((syn_ccompl (Class.cv (nb095_alpha_dummy_814 D R S_cls E)))).fv ∪
        ((syn_ccompl (Class.cv (nb095_alpha_dummy_815 D R S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0871 (u : Var) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_818 u S_cls E) ∈
      (((syn_ccompl (Class.cv (nb095_alpha_dummy_817 u S_cls E)))).fv ∪
        ((syn_ccompl (Class.cv (nb095_alpha_dummy_818 u S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0872 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_815 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_815 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_815 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0873 (u : Var) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_818 u S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_818 u S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_818 u S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0874 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_794 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_793 D R S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_794 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0875 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_794 D R S_cls E) ∈
      (((syn_ccompl (Class.cab (nb095_alpha_dummy_799 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_800 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_793 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_799 D R S_cls E))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_800 D R S_cls E)))))))).fv ∪
        ((syn_ccompl (Class.cab (nb095_alpha_dummy_799 D R S_cls E)
              (syn_wrex (nb095_alpha_dummy_800 D R S_cls E)
                (Class.cv (nb095_alpha_dummy_794 D R S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_799 D R S_cls E))
                  (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_800 D R S_cls E)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095_alpha_dummy_794 D R S_cls E) ≠ (nb095_alpha_dummy_799 D R S_cls E) from (by
          unfold nb095_alpha_dummy_799;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0874 D R S_cls E) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095_alpha_dummy_794 D R S_cls E) ≠ (nb095_alpha_dummy_800 D R S_cls E) from (by
            unfold nb095_alpha_dummy_800;
            with_reducible
              exact
                (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0874 D R S_cls E) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0876 (u : Var) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_796 u S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_795 u S_cls E))).fv ∪
        ((Class.cv (nb095_alpha_dummy_796 u S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0877 (u : Var) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_796 u S_cls E) ∈
      (((syn_ccompl (Class.cab (nb095_alpha_dummy_801 u S_cls E)
              (syn_wrex (nb095_alpha_dummy_802 u S_cls E)
                (Class.cv (nb095_alpha_dummy_795 u S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_801 u S_cls E))
                  (syn_cphi (Class.cv (nb095_alpha_dummy_802 u S_cls E)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb095_alpha_dummy_801 u S_cls E)
              (syn_wrex (nb095_alpha_dummy_802 u S_cls E)
                (Class.cv (nb095_alpha_dummy_796 u S_cls E))
                (Wff.classEq (Class.cv (nb095_alpha_dummy_801 u S_cls E))
                  (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_802 u S_cls E)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095_alpha_dummy_796 u S_cls E) ≠ (nb095_alpha_dummy_801 u S_cls E) from (by
          unfold nb095_alpha_dummy_801;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0876 u S_cls E) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095_alpha_dummy_796 u S_cls E) ≠ (nb095_alpha_dummy_802 u S_cls E) from (by
            unfold nb095_alpha_dummy_802;
            with_reducible
              exact
                (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0876 u S_cls E) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0878 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_794 D R S_cls E) ∈
      (((Class.cab (nb095_alpha_dummy_799 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_800 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_794 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_799 D R S_cls E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_800 D R S_cls E)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb095_alpha_dummy_799 D R S_cls E)
            (syn_wrex (nb095_alpha_dummy_800 D R S_cls E)
              (Class.cv (nb095_alpha_dummy_794 D R S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_799 D R S_cls E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_800 D R S_cls E)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095_alpha_dummy_794 D R S_cls E) ≠ (nb095_alpha_dummy_799 D R S_cls E) from (by
          unfold nb095_alpha_dummy_799;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0874 D R S_cls E) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095_alpha_dummy_794 D R S_cls E) ≠ (nb095_alpha_dummy_800 D R S_cls E) from (by
            unfold nb095_alpha_dummy_800;
            with_reducible
              exact
                (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0874 D R S_cls E) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0879 (u : Var) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_796 u S_cls E) ∈
      (((Class.cab (nb095_alpha_dummy_801 u S_cls E) (syn_wrex (nb095_alpha_dummy_802 u S_cls E)
              (Class.cv (nb095_alpha_dummy_796 u S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_801 u S_cls E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_802 u S_cls E)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb095_alpha_dummy_801 u S_cls E)
            (syn_wrex (nb095_alpha_dummy_802 u S_cls E)
              (Class.cv (nb095_alpha_dummy_796 u S_cls E))
              (Wff.classEq (Class.cv (nb095_alpha_dummy_801 u S_cls E))
                (syn_cun (syn_cphi (Class.cv (nb095_alpha_dummy_802 u S_cls E)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095_alpha_dummy_796 u S_cls E) ≠ (nb095_alpha_dummy_801 u S_cls E) from (by
          unfold nb095_alpha_dummy_801;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0876 u S_cls E) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095_alpha_dummy_796 u S_cls E) ≠ (nb095_alpha_dummy_802 u S_cls E) from (by
            unfold nb095_alpha_dummy_802;
            with_reducible
              exact
                (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0876 u S_cls E) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0880 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_800 D R S_cls E) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_800 D R S_cls E))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0881 (u : Var) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_802 u S_cls E) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb095_alpha_dummy_802 u S_cls E))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0882 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_800 D R S_cls E) ∈
      (((syn_cphi (Class.cv (nb095_alpha_dummy_800 D R S_cls E)))).fv ∪
        ((syn_cphi (Class.cv (nb095_alpha_dummy_800 D R S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0883 (u : Var) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_802 u S_cls E) ∈
      (((syn_cphi (Class.cv (nb095_alpha_dummy_802 u S_cls E)))).fv ∪
        ((syn_cphi (Class.cv (nb095_alpha_dummy_802 u S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0884 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_001 D R S_cls E) ∈
      (((Class.cv (nb095_alpha_dummy_000 D R S_cls E))).fv ∪ ((syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                        (syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E))))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                        (syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E)))))))).fv ∪
            ((syn_cin S_cls (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                      (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E))))) (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                      (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E)))))))).fv ∪
          ((syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (Class.cv (nb095_alpha_dummy_002 D R S_cls E)))))).fv ∪ ((syn_cin E
            (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
              (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_cin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_cxp]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_cima]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_csn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0885 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    u ∈
      (((Class.cv f)).fv ∪ ((syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (Class.cv x))))
                    (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                        (syn_csn (Class.cv x))))))).fv ∪ ((syn_cin S_cls (syn_cxp (syn_cin E
                    (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid))) (syn_csn (Class.cv u))))
                  (syn_cin E (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                      (syn_csn (Class.cv u))))))).fv ∪ ((syn_cin D
              (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (Class.cv x))))).fv ∪
        ((syn_cin E (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
              (syn_csn (Class.cv u))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_cin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_cxp]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_cima]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_csn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0886 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_001 D R S_cls E) ∈
      (((syn_cnin S_cls (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                  (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E))))) (syn_cin E
                (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                  (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E)))))))).fv ∪
        ((syn_cnin S_cls (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                  (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E))))) (syn_cin E
                (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                  (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_cxp]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_cima]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_csn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0887 (u : Var) (S_cls : Class) (E : Class) :
    u ∈
      (((syn_cnin S_cls (syn_cxp (syn_cin E
                (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid))) (syn_csn (Class.cv u))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                  (syn_csn (Class.cv u))))))).fv ∪ ((syn_cnin S_cls (syn_cxp (syn_cin E
                (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid))) (syn_csn (Class.cv u))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                  (syn_csn (Class.cv u))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_cxp]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_cima]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_csn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0888 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_001 D R S_cls E) ∈
      ((S_cls).fv ∪ ((syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E))))) (syn_cin E
              (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_cxp]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_cima]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_csn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0889 (u : Var) (S_cls : Class) (E : Class) :
    u ∈
      ((S_cls).fv ∪ ((syn_cxp (syn_cin E
              (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid))) (syn_csn (Class.cv u))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                (syn_csn (Class.cv u)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_cxp]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_cima]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_csn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0890 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_001 D R S_cls E) ∈
      (({(nb095_alpha_dummy_793 D R S_cls E)} : Finset Var) ∪
          ({(nb095_alpha_dummy_794 D R S_cls E)} : Finset Var) ∪ ((syn_wa
            (Wff.classMem (Class.cv (nb095_alpha_dummy_793 D R S_cls E)) (syn_cin E
                (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                  (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E))))))
            (Wff.classMem (Class.cv (nb095_alpha_dummy_794 D R S_cls E)) (syn_cin E
                (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                  (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_wa]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_wff_classMem]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_cin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_cima]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_csn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0891 (u : Var) (S_cls : Class) (E : Class) :
    u ∈
      (({(nb095_alpha_dummy_795 u S_cls E)} : Finset Var) ∪
          ({(nb095_alpha_dummy_796 u S_cls E)} : Finset Var) ∪ ((syn_wa
            (Wff.classMem (Class.cv (nb095_alpha_dummy_795 u S_cls E)) (syn_cin E
                (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid))) (syn_csn (Class.cv u)))))
            (Wff.classMem (Class.cv (nb095_alpha_dummy_796 u S_cls E)) (syn_cin E
                (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
                  (syn_csn (Class.cv u))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_wa]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_wff_classMem]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_cin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_cima]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_csn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0892 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_001 D R S_cls E) ∈
      (((syn_cin E (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
              (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E)))))).fv ∪ ((syn_cin E
            (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
              (syn_csn (Class.cv (nb095_alpha_dummy_001 D R S_cls E)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_cima]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_csn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0893 (u : Var) (S_cls : Class) (E : Class) :
    u ∈
      (((syn_cin E
            (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid))) (syn_csn (Class.cv u))))).fv ∪
        ((syn_cin E (syn_cima (syn_ccnv (syn_cdif S_cls (syn_cid)))
              (syn_csn (Class.cv u))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_cima]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_csn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_focused_notmem_0000 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_002 D R S_cls E) ∉ D.fv :=
  by
  change freshVar ((R).fv ∪ (D).fv ∪ (S_cls).fv ∪ (E).fv) 2 ∉ D.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 2
      (fun _ hu =>
        Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (hu))))

theorem nb095_focused_notmem_0001 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_000 D R S_cls E) ∉ D.fv :=
  by
  change freshVar ((R).fv ∪ (D).fv ∪ (S_cls).fv ∪ (E).fv) 0 ∉ D.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun _ hu =>
        Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (hu))))

theorem nb095_compact_envfresh_0000 (x : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) (dv_D_f : f ∉ D.fv) (dv_D_x : x ∉ D.fv) :
    TEnvFresh
      [((nb095_alpha_dummy_002 D R S_cls E), x), ((nb095_alpha_dummy_000 D R S_cls E), f)]
      D.fv :=
  by
  exact
    (TEnvFresh.consFresh (nb095_alpha_dummy_002 D R S_cls E) x
      (nb095_focused_notmem_0000 D R S_cls E) dv_D_x
      (TEnvFresh.consFresh (nb095_alpha_dummy_000 D R S_cls E) f
        (nb095_focused_notmem_0001 D R S_cls E) dv_D_f (TEnvFresh.nil D.fv)))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `AlphaSupport.NAR4H5C095M3Part008Stage2`. -/


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

@[expose]
noncomputable def nb095_focused_refl_0000 (x : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) (dv_D_f : f ∉ D.fv) (dv_D_x : x ∉ D.fv) :
    TReflOn
      [((nb095_alpha_dummy_002 D R S_cls E), x), ((nb095_alpha_dummy_000 D R S_cls E), f)]
      D.fv :=
  TEnvFresh.reflOn (nb095_compact_envfresh_0000 x D R S_cls f E dv_D_f dv_D_x)

theorem nb095_focused_notmem_0002 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_001 D R S_cls E) ∉ E.fv :=
  by
  change freshVar ((R).fv ∪ (D).fv ∪ (S_cls).fv ∪ (E).fv) 1 ∉ E.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1
      (fun _ hu => Finset.mem_union_right _ (hu))

theorem nb095_focused_notmem_0003 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_002 D R S_cls E) ∉ E.fv :=
  by
  change freshVar ((R).fv ∪ (D).fv ∪ (S_cls).fv ∪ (E).fv) 2 ∉ E.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 2
      (fun _ hu => Finset.mem_union_right _ (hu))

theorem nb095_focused_notmem_0004 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_000 D R S_cls E) ∉ E.fv :=
  by
  change freshVar ((R).fv ∪ (D).fv ∪ (S_cls).fv ∪ (E).fv) 0 ∉ E.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun _ hu => Finset.mem_union_right _ (hu))

theorem nb095_compact_envfresh_0001 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) (dv_E_f : f ∉ E.fv) (dv_E_u : u ∉ E.fv)
    (dv_E_x : x ∉ E.fv) :
    TEnvFresh
      [((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)]
      E.fv :=
  by
  exact
    (TEnvFresh.consFresh (nb095_alpha_dummy_001 D R S_cls E) u
      (nb095_focused_notmem_0002 D R S_cls E) dv_E_u
      (TEnvFresh.consFresh (nb095_alpha_dummy_002 D R S_cls E) x
        (nb095_focused_notmem_0003 D R S_cls E) dv_E_x
        (TEnvFresh.consFresh (nb095_alpha_dummy_000 D R S_cls E) f
          (nb095_focused_notmem_0004 D R S_cls E) dv_E_f (TEnvFresh.nil E.fv))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `AlphaSupport.NAR4H5C095M3Part008Stage3`. -/


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

@[expose]
noncomputable def nb095_focused_refl_0001 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) (dv_E_f : f ∉ E.fv) (dv_E_u : u ∉ E.fv)
    (dv_E_x : x ∉ E.fv) :
    TReflOn
      [((nb095_alpha_dummy_001 D R S_cls E), u), ((nb095_alpha_dummy_002 D R S_cls E), x),
        ((nb095_alpha_dummy_000 D R S_cls E), f)]
      E.fv :=
  TEnvFresh.reflOn (nb095_compact_envfresh_0001 x u D R S_cls f E dv_E_f dv_E_u dv_E_x)

theorem nb095_compact_fv_empty_0026 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_009 D R S_cls E) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb095_compact_fv_empty_0027 (f : Var) :
    (nb095_alpha_dummy_010 f) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb095_compact_fv_empty_0028 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_007 D R S_cls E) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb095_compact_fv_empty_0029 (f : Var) :
    (nb095_alpha_dummy_008 f) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb095_compact_fv_empty_0030 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_001 D R S_cls E) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb095_compact_fv_empty_0031 (u : Var) : u ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb095_compact_fv_empty_0032 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_002 D R S_cls E) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb095_compact_fv_empty_0033 (x : Var) : x ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb095_compact_fv_empty_0034 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095_alpha_dummy_000 D R S_cls E) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb095_compact_fv_empty_0035 (f : Var) : f ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem


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


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
