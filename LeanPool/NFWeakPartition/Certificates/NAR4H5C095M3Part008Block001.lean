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
    (nb095AlphaDummy695 x u D R S_cls f E) ∈
      (((Class.cv (nb095AlphaDummy695 x u D R S_cls f E))).fv ∪
        ((Class.cv (nb095AlphaDummy695 x u D R S_cls f E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0726 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy693 D R S_cls E) ∈
      (((synCcompl (Class.cv (nb095AlphaDummy692 D R S_cls E)))).fv ∪
        ((synCcompl (Class.cv (nb095AlphaDummy693 D R S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0727 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095AlphaDummy696 x u D R S_cls f E) ∈
      (((synCcompl (Class.cv (nb095AlphaDummy695 x u D R S_cls f E)))).fv ∪
        ((synCcompl (Class.cv (nb095AlphaDummy696 x u D R S_cls f E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0728 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy693 D R S_cls E) ∈
      (((Class.cv (nb095AlphaDummy693 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy693 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0729 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095AlphaDummy696 x u D R S_cls f E) ∈
      (((Class.cv (nb095AlphaDummy696 x u D R S_cls f E))).fv ∪
        ((Class.cv (nb095AlphaDummy696 x u D R S_cls f E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0730 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy669 D R S_cls E) ∈
      (((Class.cv (nb095AlphaDummy003 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy669 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0731 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy669 D R S_cls E) ∈
      (((synCcompl (Class.cab (nb095AlphaDummy677 D R S_cls E)
              (synWrex (nb095AlphaDummy678 D R S_cls E)
                (Class.cv (nb095AlphaDummy003 D R S_cls E))
                (Wff.classEq (Class.cv (nb095AlphaDummy677 D R S_cls E))
                  (synCphi (Class.cv (nb095AlphaDummy678 D R S_cls E)))))))).fv ∪
        ((synCcompl (Class.cab (nb095AlphaDummy677 D R S_cls E)
              (synWrex (nb095AlphaDummy678 D R S_cls E)
                (Class.cv (nb095AlphaDummy669 D R S_cls E))
                (Wff.classEq (Class.cv (nb095AlphaDummy677 D R S_cls E))
                  (synCun (synCphi (Class.cv (nb095AlphaDummy678 D R S_cls E)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095AlphaDummy669 D R S_cls E) ≠ (nb095AlphaDummy677 D R S_cls E) from (by
          unfold nb095AlphaDummy677;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0730 D R S_cls E) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095AlphaDummy669 D R S_cls E) ≠ (nb095AlphaDummy678 D R S_cls E) from (by
            unfold nb095AlphaDummy678;
            with_reducible
              exact
                (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0730 D R S_cls E) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0732 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095AlphaDummy670 x u D R S_cls f E) ∈
      (((Class.cv (nb095AlphaDummy005 x u D R S_cls f E))).fv ∪
        ((Class.cv (nb095AlphaDummy670 x u D R S_cls f E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0733 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095AlphaDummy670 x u D R S_cls f E) ∈
      (((synCcompl (Class.cab (nb095AlphaDummy679 x u D R S_cls f E)
              (synWrex (nb095AlphaDummy680 x u D R S_cls f E)
                (Class.cv (nb095AlphaDummy005 x u D R S_cls f E))
                (Wff.classEq (Class.cv (nb095AlphaDummy679 x u D R S_cls f E)) (synCphi
                    (Class.cv (nb095AlphaDummy680 x u D R S_cls f E)))))))).fv ∪ ((synCcompl
            (Class.cab (nb095AlphaDummy679 x u D R S_cls f E)
              (synWrex (nb095AlphaDummy680 x u D R S_cls f E)
                (Class.cv (nb095AlphaDummy670 x u D R S_cls f E))
                (Wff.classEq (Class.cv (nb095AlphaDummy679 x u D R S_cls f E))
                  (synCun (synCphi (Class.cv (nb095AlphaDummy680 x u D R S_cls f E)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095AlphaDummy670 x u D R S_cls f E) ≠
          (nb095AlphaDummy679 x u D R S_cls f E) from (by
          unfold nb095AlphaDummy679;
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
        (show (nb095AlphaDummy670 x u D R S_cls f E) ≠
            (nb095AlphaDummy680 x u D R S_cls f E) from (by
            unfold nb095AlphaDummy680;
            with_reducible
              exact
                (Nat.ne_of_lt
                  (mem_lt_freshVar (nb095_support_mem_0732 x u D R S_cls f E) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0734 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy669 D R S_cls E) ∈
      (((Class.cab (nb095AlphaDummy677 D R S_cls E)
            (synWrex (nb095AlphaDummy678 D R S_cls E)
              (Class.cv (nb095AlphaDummy669 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy677 D R S_cls E))
                (synCun (synCphi (Class.cv (nb095AlphaDummy678 D R S_cls E)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb095AlphaDummy677 D R S_cls E)
            (synWrex (nb095AlphaDummy678 D R S_cls E)
              (Class.cv (nb095AlphaDummy669 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy677 D R S_cls E))
                (synCun (synCphi (Class.cv (nb095AlphaDummy678 D R S_cls E)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095AlphaDummy669 D R S_cls E) ≠ (nb095AlphaDummy677 D R S_cls E) from (by
          unfold nb095AlphaDummy677;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0730 D R S_cls E) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095AlphaDummy669 D R S_cls E) ≠ (nb095AlphaDummy678 D R S_cls E) from (by
            unfold nb095AlphaDummy678;
            with_reducible
              exact
                (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0730 D R S_cls E) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0735 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095AlphaDummy670 x u D R S_cls f E) ∈
      (((Class.cab (nb095AlphaDummy679 x u D R S_cls f E)
            (synWrex (nb095AlphaDummy680 x u D R S_cls f E)
              (Class.cv (nb095AlphaDummy670 x u D R S_cls f E))
              (Wff.classEq (Class.cv (nb095AlphaDummy679 x u D R S_cls f E))
                (synCun (synCphi (Class.cv (nb095AlphaDummy680 x u D R S_cls f E)))
                  (synCsn (synC0c))))))).fv ∪
        ((Class.cab (nb095AlphaDummy679 x u D R S_cls f E)
            (synWrex (nb095AlphaDummy680 x u D R S_cls f E)
              (Class.cv (nb095AlphaDummy670 x u D R S_cls f E))
              (Wff.classEq (Class.cv (nb095AlphaDummy679 x u D R S_cls f E))
                (synCun (synCphi (Class.cv (nb095AlphaDummy680 x u D R S_cls f E)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095AlphaDummy670 x u D R S_cls f E) ≠
          (nb095AlphaDummy679 x u D R S_cls f E) from (by
          unfold nb095AlphaDummy679;
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
        (show (nb095AlphaDummy670 x u D R S_cls f E) ≠
            (nb095AlphaDummy680 x u D R S_cls f E) from (by
            unfold nb095AlphaDummy680;
            with_reducible
              exact
                (Nat.ne_of_lt
                  (mem_lt_freshVar (nb095_support_mem_0732 x u D R S_cls f E) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0736 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy678 D R S_cls E) ∈
      (((synCcompl (synCphi (Class.cv (nb095AlphaDummy678 D R S_cls E))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0737 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095AlphaDummy680 x u D R S_cls f E) ∈
      (((synCcompl (synCphi (Class.cv (nb095AlphaDummy680 x u D R S_cls f E))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0738 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy678 D R S_cls E) ∈
      (((synCphi (Class.cv (nb095AlphaDummy678 D R S_cls E)))).fv ∪
        ((synCphi (Class.cv (nb095AlphaDummy678 D R S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0739 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095AlphaDummy680 x u D R S_cls f E) ∈
      (((synCphi (Class.cv (nb095AlphaDummy680 x u D R S_cls f E)))).fv ∪
        ((synCphi (Class.cv (nb095AlphaDummy680 x u D R S_cls f E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0740 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy000 D R S_cls E) ∈
      (((Class.cv (nb095AlphaDummy000 D R S_cls E))).fv ∪ ((synCin R (synCxp (synCin D
                      (synCima (synCcnv (synCdif R (synCid)))
                        (synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E))))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid)))
                        (synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E)))))))).fv ∪
            ((synCin S_cls (synCxp (synCin E (synCima (synCcnv (synCdif S_cls (synCid)))
                      (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E))))) (synCin E
                    (synCima (synCcnv (synCdif S_cls (synCid)))
                      (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E)))))))).fv ∪
          ((synCin D (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E)))))).fv ∪ ((synCin E
            (synCima (synCcnv (synCdif S_cls (synCid)))
              (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E)))))).fv) :=
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
      (((Class.cv f)).fv ∪ ((synCin R (synCxp (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (Class.cv x))))
                    (synCin D (synCima (synCcnv (synCdif R (synCid)))
                        (synCsn (Class.cv x))))))).fv ∪ ((synCin S_cls (synCxp (synCin E
                    (synCima (synCcnv (synCdif S_cls (synCid))) (synCsn (Class.cv u))))
                  (synCin E (synCima (synCcnv (synCdif S_cls (synCid)))
                      (synCsn (Class.cv u))))))).fv ∪ ((synCin D
              (synCima (synCcnv (synCdif R (synCid))) (synCsn (Class.cv x))))).fv ∪
        ((synCin E (synCima (synCcnv (synCdif S_cls (synCid)))
              (synCsn (Class.cv u))))).fv) :=
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
    (nb095AlphaDummy000 D R S_cls E) ∈
      (((synCfv (Class.cv (nb095AlphaDummy000 D R S_cls E))
            (Class.cv (nb095AlphaDummy003 D R S_cls E)))).fv ∪
        ((synCfv (Class.cv (nb095AlphaDummy000 D R S_cls E))
            (Class.cv (nb095AlphaDummy004 D R S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cfv]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0743 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy000 D R S_cls E) ∈
      (((synCcompl (Class.cab (nb095AlphaDummy661 D R S_cls E)
              (synWrex (nb095AlphaDummy662 D R S_cls E)
                (synCfv (Class.cv (nb095AlphaDummy000 D R S_cls E))
                  (Class.cv (nb095AlphaDummy003 D R S_cls E)))
                (Wff.classEq (Class.cv (nb095AlphaDummy661 D R S_cls E))
                  (synCphi (Class.cv (nb095AlphaDummy662 D R S_cls E)))))))).fv ∪
        ((synCcompl (Class.cab (nb095AlphaDummy661 D R S_cls E)
              (synWrex (nb095AlphaDummy662 D R S_cls E)
                (synCfv (Class.cv (nb095AlphaDummy000 D R S_cls E))
                  (Class.cv (nb095AlphaDummy004 D R S_cls E)))
                (Wff.classEq (Class.cv (nb095AlphaDummy661 D R S_cls E))
                  (synCun (synCphi (Class.cv (nb095AlphaDummy662 D R S_cls E)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095AlphaDummy000 D R S_cls E) ≠ (nb095AlphaDummy661 D R S_cls E) from (by
          unfold nb095AlphaDummy661;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0742 D R S_cls E) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095AlphaDummy000 D R S_cls E) ≠ (nb095AlphaDummy662 D R S_cls E) from (by
            unfold nb095AlphaDummy662;
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
      (((synCfv (Class.cv f) (Class.cv (nb095AlphaDummy005 x u D R S_cls f E)))).fv ∪
        ((synCfv (Class.cv f) (Class.cv (nb095AlphaDummy006 x u D R S_cls f E)))).fv) :=
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
      (((synCcompl (Class.cab (nb095AlphaDummy663 x u D R S_cls f E)
              (synWrex (nb095AlphaDummy664 x u D R S_cls f E) (synCfv (Class.cv f)
                  (Class.cv (nb095AlphaDummy005 x u D R S_cls f E)))
                (Wff.classEq (Class.cv (nb095AlphaDummy663 x u D R S_cls f E)) (synCphi
                    (Class.cv (nb095AlphaDummy664 x u D R S_cls f E)))))))).fv ∪ ((synCcompl
            (Class.cab (nb095AlphaDummy663 x u D R S_cls f E)
              (synWrex (nb095AlphaDummy664 x u D R S_cls f E) (synCfv (Class.cv f)
                  (Class.cv (nb095AlphaDummy006 x u D R S_cls f E)))
                (Wff.classEq (Class.cv (nb095AlphaDummy663 x u D R S_cls f E))
                  (synCun (synCphi (Class.cv (nb095AlphaDummy664 x u D R S_cls f E)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show f ≠ (nb095AlphaDummy663 x u D R S_cls f E) from (by
          unfold nb095AlphaDummy663;
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
        (show f ≠ (nb095AlphaDummy664 x u D R S_cls f E) from (by
            unfold nb095AlphaDummy664;
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
    (nb095AlphaDummy000 D R S_cls E) ∈
      (((Class.cab (nb095AlphaDummy661 D R S_cls E)
            (synWrex (nb095AlphaDummy662 D R S_cls E)
              (synCfv (Class.cv (nb095AlphaDummy000 D R S_cls E))
                (Class.cv (nb095AlphaDummy003 D R S_cls E)))
              (Wff.classEq (Class.cv (nb095AlphaDummy661 D R S_cls E))
                (synCphi (Class.cv (nb095AlphaDummy662 D R S_cls E))))))).fv ∪
        ((Class.cab (nb095AlphaDummy661 D R S_cls E)
            (synWrex (nb095AlphaDummy662 D R S_cls E)
              (synCfv (Class.cv (nb095AlphaDummy000 D R S_cls E))
                (Class.cv (nb095AlphaDummy003 D R S_cls E)))
              (Wff.classEq (Class.cv (nb095AlphaDummy661 D R S_cls E))
                (synCphi (Class.cv (nb095AlphaDummy662 D R S_cls E))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095AlphaDummy000 D R S_cls E) ≠ (nb095AlphaDummy661 D R S_cls E) from (by
          unfold nb095AlphaDummy661;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0742 D R S_cls E) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095AlphaDummy000 D R S_cls E) ≠ (nb095AlphaDummy662 D R S_cls E) from (by
            unfold nb095AlphaDummy662;
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
      (((Class.cab (nb095AlphaDummy663 x u D R S_cls f E)
            (synWrex (nb095AlphaDummy664 x u D R S_cls f E)
              (synCfv (Class.cv f) (Class.cv (nb095AlphaDummy005 x u D R S_cls f E)))
              (Wff.classEq (Class.cv (nb095AlphaDummy663 x u D R S_cls f E))
                (synCphi (Class.cv (nb095AlphaDummy664 x u D R S_cls f E))))))).fv ∪
        ((Class.cab (nb095AlphaDummy663 x u D R S_cls f E)
            (synWrex (nb095AlphaDummy664 x u D R S_cls f E)
              (synCfv (Class.cv f) (Class.cv (nb095AlphaDummy005 x u D R S_cls f E)))
              (Wff.classEq (Class.cv (nb095AlphaDummy663 x u D R S_cls f E))
                (synCphi (Class.cv (nb095AlphaDummy664 x u D R S_cls f E))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show f ≠ (nb095AlphaDummy663 x u D R S_cls f E) from (by
          unfold nb095AlphaDummy663;
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
        (show f ≠ (nb095AlphaDummy664 x u D R S_cls f E) from (by
            unfold nb095AlphaDummy664;
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
    (nb095AlphaDummy000 D R S_cls E) ∈
      (((Class.cv (nb095AlphaDummy000 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy003 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0749 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy000 D R S_cls E) ∈
      (({(nb095AlphaDummy669 D R S_cls E)} : Finset Var) ∪
        ((synWbr (Class.cv (nb095AlphaDummy003 D R S_cls E))
            (Class.cv (nb095AlphaDummy000 D R S_cls E))
            (Class.cv (nb095AlphaDummy669 D R S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_wbr]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0750 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy000 D R S_cls E) ∈
      (((Class.cab (nb095AlphaDummy671 D R S_cls E) (Wff.classEq
            (Class.cab (nb095AlphaDummy669 D R S_cls E)
              (synWbr (Class.cv (nb095AlphaDummy003 D R S_cls E))
                (Class.cv (nb095AlphaDummy000 D R S_cls E))
                (Class.cv (nb095AlphaDummy669 D R S_cls E))))
            (synCsn (Class.cv (nb095AlphaDummy671 D R S_cls E)))))).fv) :=
  by
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095AlphaDummy000 D R S_cls E) ≠ (nb095AlphaDummy671 D R S_cls E) from (by
          unfold nb095AlphaDummy671;
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
        (show (nb095AlphaDummy000 D R S_cls E) ≠ (nb095AlphaDummy669 D R S_cls E) from (by
            unfold nb095AlphaDummy669;
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
    f ∈ (((Class.cv f)).fv ∪ ((Class.cv (nb095AlphaDummy005 x u D R S_cls f E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0752 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    f ∈
      (({(nb095AlphaDummy670 x u D R S_cls f E)} : Finset Var) ∪
        ((synWbr (Class.cv (nb095AlphaDummy005 x u D R S_cls f E)) (Class.cv f)
            (Class.cv (nb095AlphaDummy670 x u D R S_cls f E)))).fv) :=
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
      (((Class.cab (nb095AlphaDummy672 x u D R S_cls f E) (Wff.classEq
            (Class.cab (nb095AlphaDummy670 x u D R S_cls f E)
              (synWbr (Class.cv (nb095AlphaDummy005 x u D R S_cls f E)) (Class.cv f)
                (Class.cv (nb095AlphaDummy670 x u D R S_cls f E))))
            (synCsn (Class.cv (nb095AlphaDummy672 x u D R S_cls f E)))))).fv) :=
  by
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show f ≠ (nb095AlphaDummy672 x u D R S_cls f E) from (by
          unfold nb095AlphaDummy672;
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
        (show f ≠ (nb095AlphaDummy670 x u D R S_cls f E) from (by
            unfold nb095AlphaDummy670;
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
    (nb095AlphaDummy671 D R S_cls E) ∈
      (((Class.cv (nb095AlphaDummy671 D R S_cls E))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0755 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095AlphaDummy672 x u D R S_cls f E) ∈
      (((Class.cv (nb095AlphaDummy672 x u D R S_cls f E))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0756 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy662 D R S_cls E) ∈
      (((Class.cv (nb095AlphaDummy662 D R S_cls E))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0757 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095AlphaDummy664 x u D R S_cls f E) ∈
      (((Class.cv (nb095AlphaDummy664 x u D R S_cls f E))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0758 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy715 D R S_cls E) ∈
      (((Wff.classMem (Class.cv (nb095AlphaDummy715 D R S_cls E)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb095AlphaDummy715 D R S_cls E)) (synC1c))).fv ∪
        ((Class.cv (nb095AlphaDummy715 D R S_cls E))).fv) :=
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
    (nb095AlphaDummy717 x u D R S_cls f E) ∈
      (((Wff.classMem (Class.cv (nb095AlphaDummy717 x u D R S_cls f E)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb095AlphaDummy717 x u D R S_cls f E)) (synC1c))).fv ∪
        ((Class.cv (nb095AlphaDummy717 x u D R S_cls f E))).fv) :=
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
    (nb095AlphaDummy715 D R S_cls E) ∈
      (((Class.cv (nb095AlphaDummy715 D R S_cls E))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0761 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095AlphaDummy717 x u D R S_cls f E) ∈
      (((Class.cv (nb095AlphaDummy717 x u D R S_cls f E))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0762 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy722 D R S_cls E) ∈
      (((synCnin (Class.cv (nb095AlphaDummy722 D R S_cls E))
            (Class.cv (nb095AlphaDummy723 D R S_cls E)))).fv ∪
        ((synCnin (Class.cv (nb095AlphaDummy722 D R S_cls E))
            (Class.cv (nb095AlphaDummy723 D R S_cls E)))).fv) :=
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
    (nb095AlphaDummy725 x u D R S_cls f E) ∈
      (((synCnin (Class.cv (nb095AlphaDummy725 x u D R S_cls f E))
            (Class.cv (nb095AlphaDummy726 x u D R S_cls f E)))).fv ∪
        ((synCnin (Class.cv (nb095AlphaDummy725 x u D R S_cls f E))
            (Class.cv (nb095AlphaDummy726 x u D R S_cls f E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0764 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy722 D R S_cls E) ∈
      (((Class.cv (nb095AlphaDummy722 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy723 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0765 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095AlphaDummy725 x u D R S_cls f E) ∈
      (((Class.cv (nb095AlphaDummy725 x u D R S_cls f E))).fv ∪
        ((Class.cv (nb095AlphaDummy726 x u D R S_cls f E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0766 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy723 D R S_cls E) ∈
      (((synCnin (Class.cv (nb095AlphaDummy722 D R S_cls E))
            (Class.cv (nb095AlphaDummy723 D R S_cls E)))).fv ∪
        ((synCnin (Class.cv (nb095AlphaDummy722 D R S_cls E))
            (Class.cv (nb095AlphaDummy723 D R S_cls E)))).fv) :=
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
    (nb095AlphaDummy726 x u D R S_cls f E) ∈
      (((synCnin (Class.cv (nb095AlphaDummy725 x u D R S_cls f E))
            (Class.cv (nb095AlphaDummy726 x u D R S_cls f E)))).fv ∪
        ((synCnin (Class.cv (nb095AlphaDummy725 x u D R S_cls f E))
            (Class.cv (nb095AlphaDummy726 x u D R S_cls f E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0768 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy723 D R S_cls E) ∈
      (((Class.cv (nb095AlphaDummy722 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy723 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0769 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095AlphaDummy726 x u D R S_cls f E) ∈
      (((Class.cv (nb095AlphaDummy725 x u D R S_cls f E))).fv ∪
        ((Class.cv (nb095AlphaDummy726 x u D R S_cls f E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0770 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy722 D R S_cls E) ∈
      (((synCcompl (Class.cv (nb095AlphaDummy722 D R S_cls E)))).fv ∪
        ((synCcompl (Class.cv (nb095AlphaDummy723 D R S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0771 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095AlphaDummy725 x u D R S_cls f E) ∈
      (((synCcompl (Class.cv (nb095AlphaDummy725 x u D R S_cls f E)))).fv ∪
        ((synCcompl (Class.cv (nb095AlphaDummy726 x u D R S_cls f E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0772 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy722 D R S_cls E) ∈
      (((Class.cv (nb095AlphaDummy722 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy722 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0773 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095AlphaDummy725 x u D R S_cls f E) ∈
      (((Class.cv (nb095AlphaDummy725 x u D R S_cls f E))).fv ∪
        ((Class.cv (nb095AlphaDummy725 x u D R S_cls f E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0774 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy723 D R S_cls E) ∈
      (((synCcompl (Class.cv (nb095AlphaDummy722 D R S_cls E)))).fv ∪
        ((synCcompl (Class.cv (nb095AlphaDummy723 D R S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0775 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095AlphaDummy726 x u D R S_cls f E) ∈
      (((synCcompl (Class.cv (nb095AlphaDummy725 x u D R S_cls f E)))).fv ∪
        ((synCcompl (Class.cv (nb095AlphaDummy726 x u D R S_cls f E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0776 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy723 D R S_cls E) ∈
      (((Class.cv (nb095AlphaDummy723 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy723 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0777 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095AlphaDummy726 x u D R S_cls f E) ∈
      (((Class.cv (nb095AlphaDummy726 x u D R S_cls f E))).fv ∪
        ((Class.cv (nb095AlphaDummy726 x u D R S_cls f E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0778 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy004 D R S_cls E) ∈
      (((synCfv (Class.cv (nb095AlphaDummy000 D R S_cls E))
            (Class.cv (nb095AlphaDummy003 D R S_cls E)))).fv ∪
        ((synCfv (Class.cv (nb095AlphaDummy000 D R S_cls E))
            (Class.cv (nb095AlphaDummy004 D R S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_cfv]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0779 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy004 D R S_cls E) ∈
      (((synCcompl (Class.cab (nb095AlphaDummy661 D R S_cls E)
              (synWrex (nb095AlphaDummy662 D R S_cls E)
                (synCfv (Class.cv (nb095AlphaDummy000 D R S_cls E))
                  (Class.cv (nb095AlphaDummy003 D R S_cls E)))
                (Wff.classEq (Class.cv (nb095AlphaDummy661 D R S_cls E))
                  (synCphi (Class.cv (nb095AlphaDummy662 D R S_cls E)))))))).fv ∪
        ((synCcompl (Class.cab (nb095AlphaDummy661 D R S_cls E)
              (synWrex (nb095AlphaDummy662 D R S_cls E)
                (synCfv (Class.cv (nb095AlphaDummy000 D R S_cls E))
                  (Class.cv (nb095AlphaDummy004 D R S_cls E)))
                (Wff.classEq (Class.cv (nb095AlphaDummy661 D R S_cls E))
                  (synCun (synCphi (Class.cv (nb095AlphaDummy662 D R S_cls E)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095AlphaDummy004 D R S_cls E) ≠ (nb095AlphaDummy661 D R S_cls E) from (by
          unfold nb095AlphaDummy661;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0778 D R S_cls E) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095AlphaDummy004 D R S_cls E) ≠ (nb095AlphaDummy662 D R S_cls E) from (by
            unfold nb095AlphaDummy662;
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
    (nb095AlphaDummy006 x u D R S_cls f E) ∈
      (((synCfv (Class.cv f) (Class.cv (nb095AlphaDummy005 x u D R S_cls f E)))).fv ∪
        ((synCfv (Class.cv f) (Class.cv (nb095AlphaDummy006 x u D R S_cls f E)))).fv) :=
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
    (nb095AlphaDummy006 x u D R S_cls f E) ∈
      (((synCcompl (Class.cab (nb095AlphaDummy663 x u D R S_cls f E)
              (synWrex (nb095AlphaDummy664 x u D R S_cls f E) (synCfv (Class.cv f)
                  (Class.cv (nb095AlphaDummy005 x u D R S_cls f E)))
                (Wff.classEq (Class.cv (nb095AlphaDummy663 x u D R S_cls f E)) (synCphi
                    (Class.cv (nb095AlphaDummy664 x u D R S_cls f E)))))))).fv ∪ ((synCcompl
            (Class.cab (nb095AlphaDummy663 x u D R S_cls f E)
              (synWrex (nb095AlphaDummy664 x u D R S_cls f E) (synCfv (Class.cv f)
                  (Class.cv (nb095AlphaDummy006 x u D R S_cls f E)))
                (Wff.classEq (Class.cv (nb095AlphaDummy663 x u D R S_cls f E))
                  (synCun (synCphi (Class.cv (nb095AlphaDummy664 x u D R S_cls f E)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095AlphaDummy006 x u D R S_cls f E) ≠
          (nb095AlphaDummy663 x u D R S_cls f E) from (by
          unfold nb095AlphaDummy663;
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
        (show (nb095AlphaDummy006 x u D R S_cls f E) ≠
            (nb095AlphaDummy664 x u D R S_cls f E) from (by
            unfold nb095AlphaDummy664;
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
    (nb095AlphaDummy004 D R S_cls E) ∈
      (((Class.cab (nb095AlphaDummy661 D R S_cls E)
            (synWrex (nb095AlphaDummy662 D R S_cls E)
              (synCfv (Class.cv (nb095AlphaDummy000 D R S_cls E))
                (Class.cv (nb095AlphaDummy004 D R S_cls E)))
              (Wff.classEq (Class.cv (nb095AlphaDummy661 D R S_cls E))
                (synCun (synCphi (Class.cv (nb095AlphaDummy662 D R S_cls E)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb095AlphaDummy661 D R S_cls E)
            (synWrex (nb095AlphaDummy662 D R S_cls E)
              (synCfv (Class.cv (nb095AlphaDummy000 D R S_cls E))
                (Class.cv (nb095AlphaDummy004 D R S_cls E)))
              (Wff.classEq (Class.cv (nb095AlphaDummy661 D R S_cls E))
                (synCun (synCphi (Class.cv (nb095AlphaDummy662 D R S_cls E)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095AlphaDummy004 D R S_cls E) ≠ (nb095AlphaDummy661 D R S_cls E) from (by
          unfold nb095AlphaDummy661;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0778 D R S_cls E) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095AlphaDummy004 D R S_cls E) ≠ (nb095AlphaDummy662 D R S_cls E) from (by
            unfold nb095AlphaDummy662;
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
    (nb095AlphaDummy006 x u D R S_cls f E) ∈
      (((Class.cab (nb095AlphaDummy663 x u D R S_cls f E)
            (synWrex (nb095AlphaDummy664 x u D R S_cls f E)
              (synCfv (Class.cv f) (Class.cv (nb095AlphaDummy006 x u D R S_cls f E)))
              (Wff.classEq (Class.cv (nb095AlphaDummy663 x u D R S_cls f E))
                (synCun (synCphi (Class.cv (nb095AlphaDummy664 x u D R S_cls f E)))
                  (synCsn (synC0c))))))).fv ∪
        ((Class.cab (nb095AlphaDummy663 x u D R S_cls f E)
            (synWrex (nb095AlphaDummy664 x u D R S_cls f E)
              (synCfv (Class.cv f) (Class.cv (nb095AlphaDummy006 x u D R S_cls f E)))
              (Wff.classEq (Class.cv (nb095AlphaDummy663 x u D R S_cls f E))
                (synCun (synCphi (Class.cv (nb095AlphaDummy664 x u D R S_cls f E)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095AlphaDummy006 x u D R S_cls f E) ≠
          (nb095AlphaDummy663 x u D R S_cls f E) from (by
          unfold nb095AlphaDummy663;
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
        (show (nb095AlphaDummy006 x u D R S_cls f E) ≠
            (nb095AlphaDummy664 x u D R S_cls f E) from (by
            unfold nb095AlphaDummy664;
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
    (nb095AlphaDummy004 D R S_cls E) ∈
      (((Class.cv (nb095AlphaDummy000 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy004 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0785 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy004 D R S_cls E) ∈
      (({(nb095AlphaDummy739 D R S_cls E)} : Finset Var) ∪
        ((synWbr (Class.cv (nb095AlphaDummy004 D R S_cls E))
            (Class.cv (nb095AlphaDummy000 D R S_cls E))
            (Class.cv (nb095AlphaDummy739 D R S_cls E)))).fv) :=
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
    (nb095AlphaDummy004 D R S_cls E) ∈
      (((Class.cab (nb095AlphaDummy741 D R S_cls E) (Wff.classEq
            (Class.cab (nb095AlphaDummy739 D R S_cls E)
              (synWbr (Class.cv (nb095AlphaDummy004 D R S_cls E))
                (Class.cv (nb095AlphaDummy000 D R S_cls E))
                (Class.cv (nb095AlphaDummy739 D R S_cls E))))
            (synCsn (Class.cv (nb095AlphaDummy741 D R S_cls E)))))).fv) :=
  by
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095AlphaDummy004 D R S_cls E) ≠ (nb095AlphaDummy741 D R S_cls E) from (by
          unfold nb095AlphaDummy741;
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
        (show (nb095AlphaDummy004 D R S_cls E) ≠ (nb095AlphaDummy739 D R S_cls E) from (by
            unfold nb095AlphaDummy739;
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
    (nb095AlphaDummy006 x u D R S_cls f E) ∈
      (((Class.cv f)).fv ∪ ((Class.cv (nb095AlphaDummy006 x u D R S_cls f E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0788 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095AlphaDummy006 x u D R S_cls f E) ∈
      (({(nb095AlphaDummy740 x u D R S_cls f E)} : Finset Var) ∪
        ((synWbr (Class.cv (nb095AlphaDummy006 x u D R S_cls f E)) (Class.cv f)
            (Class.cv (nb095AlphaDummy740 x u D R S_cls f E)))).fv) :=
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
    (nb095AlphaDummy006 x u D R S_cls f E) ∈
      (((Class.cab (nb095AlphaDummy742 x u D R S_cls f E) (Wff.classEq
            (Class.cab (nb095AlphaDummy740 x u D R S_cls f E)
              (synWbr (Class.cv (nb095AlphaDummy006 x u D R S_cls f E)) (Class.cv f)
                (Class.cv (nb095AlphaDummy740 x u D R S_cls f E))))
            (synCsn (Class.cv (nb095AlphaDummy742 x u D R S_cls f E)))))).fv) :=
  by
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095AlphaDummy006 x u D R S_cls f E) ≠
          (nb095AlphaDummy742 x u D R S_cls f E) from (by
          unfold nb095AlphaDummy742;
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
        (show (nb095AlphaDummy006 x u D R S_cls f E) ≠
            (nb095AlphaDummy740 x u D R S_cls f E) from (by
            unfold nb095AlphaDummy740;
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
    (nb095AlphaDummy004 D R S_cls E) ∈
      (((Class.cv (nb095AlphaDummy004 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy739 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0791 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy004 D R S_cls E) ∈
      (((synCcompl (Class.cab (nb095AlphaDummy747 D R S_cls E)
              (synWrex (nb095AlphaDummy748 D R S_cls E)
                (Class.cv (nb095AlphaDummy004 D R S_cls E))
                (Wff.classEq (Class.cv (nb095AlphaDummy747 D R S_cls E))
                  (synCphi (Class.cv (nb095AlphaDummy748 D R S_cls E)))))))).fv ∪
        ((synCcompl (Class.cab (nb095AlphaDummy747 D R S_cls E)
              (synWrex (nb095AlphaDummy748 D R S_cls E)
                (Class.cv (nb095AlphaDummy739 D R S_cls E))
                (Wff.classEq (Class.cv (nb095AlphaDummy747 D R S_cls E))
                  (synCun (synCphi (Class.cv (nb095AlphaDummy748 D R S_cls E)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095AlphaDummy004 D R S_cls E) ≠ (nb095AlphaDummy747 D R S_cls E) from (by
          unfold nb095AlphaDummy747;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0790 D R S_cls E) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095AlphaDummy004 D R S_cls E) ≠ (nb095AlphaDummy748 D R S_cls E) from (by
            unfold nb095AlphaDummy748;
            with_reducible
              exact
                (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0790 D R S_cls E) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0792 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095AlphaDummy006 x u D R S_cls f E) ∈
      (((Class.cv (nb095AlphaDummy006 x u D R S_cls f E))).fv ∪
        ((Class.cv (nb095AlphaDummy740 x u D R S_cls f E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0793 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095AlphaDummy006 x u D R S_cls f E) ∈
      (((synCcompl (Class.cab (nb095AlphaDummy749 x u D R S_cls f E)
              (synWrex (nb095AlphaDummy750 x u D R S_cls f E)
                (Class.cv (nb095AlphaDummy006 x u D R S_cls f E))
                (Wff.classEq (Class.cv (nb095AlphaDummy749 x u D R S_cls f E)) (synCphi
                    (Class.cv (nb095AlphaDummy750 x u D R S_cls f E)))))))).fv ∪ ((synCcompl
            (Class.cab (nb095AlphaDummy749 x u D R S_cls f E)
              (synWrex (nb095AlphaDummy750 x u D R S_cls f E)
                (Class.cv (nb095AlphaDummy740 x u D R S_cls f E))
                (Wff.classEq (Class.cv (nb095AlphaDummy749 x u D R S_cls f E))
                  (synCun (synCphi (Class.cv (nb095AlphaDummy750 x u D R S_cls f E)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095AlphaDummy006 x u D R S_cls f E) ≠
          (nb095AlphaDummy749 x u D R S_cls f E) from (by
          unfold nb095AlphaDummy749;
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
        (show (nb095AlphaDummy006 x u D R S_cls f E) ≠
            (nb095AlphaDummy750 x u D R S_cls f E) from (by
            unfold nb095AlphaDummy750;
            with_reducible
              exact
                (Nat.ne_of_lt
                  (mem_lt_freshVar (nb095_support_mem_0792 x u D R S_cls f E) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0794 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy004 D R S_cls E) ∈
      (((Class.cab (nb095AlphaDummy747 D R S_cls E)
            (synWrex (nb095AlphaDummy748 D R S_cls E)
              (Class.cv (nb095AlphaDummy004 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy747 D R S_cls E))
                (synCphi (Class.cv (nb095AlphaDummy748 D R S_cls E))))))).fv ∪
        ((Class.cab (nb095AlphaDummy747 D R S_cls E)
            (synWrex (nb095AlphaDummy748 D R S_cls E)
              (Class.cv (nb095AlphaDummy004 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy747 D R S_cls E))
                (synCphi (Class.cv (nb095AlphaDummy748 D R S_cls E))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095AlphaDummy004 D R S_cls E) ≠ (nb095AlphaDummy747 D R S_cls E) from (by
          unfold nb095AlphaDummy747;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0790 D R S_cls E) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095AlphaDummy004 D R S_cls E) ≠ (nb095AlphaDummy748 D R S_cls E) from (by
            unfold nb095AlphaDummy748;
            with_reducible
              exact
                (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0790 D R S_cls E) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0795 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095AlphaDummy006 x u D R S_cls f E) ∈
      (((Class.cab (nb095AlphaDummy749 x u D R S_cls f E)
            (synWrex (nb095AlphaDummy750 x u D R S_cls f E)
              (Class.cv (nb095AlphaDummy006 x u D R S_cls f E))
              (Wff.classEq (Class.cv (nb095AlphaDummy749 x u D R S_cls f E))
                (synCphi (Class.cv (nb095AlphaDummy750 x u D R S_cls f E))))))).fv ∪
        ((Class.cab (nb095AlphaDummy749 x u D R S_cls f E)
            (synWrex (nb095AlphaDummy750 x u D R S_cls f E)
              (Class.cv (nb095AlphaDummy006 x u D R S_cls f E))
              (Wff.classEq (Class.cv (nb095AlphaDummy749 x u D R S_cls f E))
                (synCphi (Class.cv (nb095AlphaDummy750 x u D R S_cls f E))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095AlphaDummy006 x u D R S_cls f E) ≠
          (nb095AlphaDummy749 x u D R S_cls f E) from (by
          unfold nb095AlphaDummy749;
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
        (show (nb095AlphaDummy006 x u D R S_cls f E) ≠
            (nb095AlphaDummy750 x u D R S_cls f E) from (by
            unfold nb095AlphaDummy750;
            with_reducible
              exact
                (Nat.ne_of_lt
                  (mem_lt_freshVar (nb095_support_mem_0792 x u D R S_cls f E) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0796 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy748 D R S_cls E) ∈
      (((Class.cv (nb095AlphaDummy748 D R S_cls E))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0797 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095AlphaDummy750 x u D R S_cls f E) ∈
      (((Class.cv (nb095AlphaDummy750 x u D R S_cls f E))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0798 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy755 D R S_cls E) ∈
      (((Wff.classMem (Class.cv (nb095AlphaDummy755 D R S_cls E)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb095AlphaDummy755 D R S_cls E)) (synC1c))).fv ∪
        ((Class.cv (nb095AlphaDummy755 D R S_cls E))).fv) :=
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
    (nb095AlphaDummy757 x u D R S_cls f E) ∈
      (((Wff.classMem (Class.cv (nb095AlphaDummy757 x u D R S_cls f E)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb095AlphaDummy757 x u D R S_cls f E)) (synC1c))).fv ∪
        ((Class.cv (nb095AlphaDummy757 x u D R S_cls f E))).fv) :=
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
    (nb095AlphaDummy755 D R S_cls E) ∈
      (((Class.cv (nb095AlphaDummy755 D R S_cls E))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0801 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095AlphaDummy757 x u D R S_cls f E) ∈
      (((Class.cv (nb095AlphaDummy757 x u D R S_cls f E))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0802 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy762 D R S_cls E) ∈
      (((synCnin (Class.cv (nb095AlphaDummy762 D R S_cls E))
            (Class.cv (nb095AlphaDummy763 D R S_cls E)))).fv ∪
        ((synCnin (Class.cv (nb095AlphaDummy762 D R S_cls E))
            (Class.cv (nb095AlphaDummy763 D R S_cls E)))).fv) :=
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
    (nb095AlphaDummy765 x u D R S_cls f E) ∈
      (((synCnin (Class.cv (nb095AlphaDummy765 x u D R S_cls f E))
            (Class.cv (nb095AlphaDummy766 x u D R S_cls f E)))).fv ∪
        ((synCnin (Class.cv (nb095AlphaDummy765 x u D R S_cls f E))
            (Class.cv (nb095AlphaDummy766 x u D R S_cls f E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0804 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy762 D R S_cls E) ∈
      (((Class.cv (nb095AlphaDummy762 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy763 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0805 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095AlphaDummy765 x u D R S_cls f E) ∈
      (((Class.cv (nb095AlphaDummy765 x u D R S_cls f E))).fv ∪
        ((Class.cv (nb095AlphaDummy766 x u D R S_cls f E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0806 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy763 D R S_cls E) ∈
      (((synCnin (Class.cv (nb095AlphaDummy762 D R S_cls E))
            (Class.cv (nb095AlphaDummy763 D R S_cls E)))).fv ∪
        ((synCnin (Class.cv (nb095AlphaDummy762 D R S_cls E))
            (Class.cv (nb095AlphaDummy763 D R S_cls E)))).fv) :=
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
    (nb095AlphaDummy766 x u D R S_cls f E) ∈
      (((synCnin (Class.cv (nb095AlphaDummy765 x u D R S_cls f E))
            (Class.cv (nb095AlphaDummy766 x u D R S_cls f E)))).fv ∪
        ((synCnin (Class.cv (nb095AlphaDummy765 x u D R S_cls f E))
            (Class.cv (nb095AlphaDummy766 x u D R S_cls f E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0808 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy763 D R S_cls E) ∈
      (((Class.cv (nb095AlphaDummy762 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy763 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0809 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095AlphaDummy766 x u D R S_cls f E) ∈
      (((Class.cv (nb095AlphaDummy765 x u D R S_cls f E))).fv ∪
        ((Class.cv (nb095AlphaDummy766 x u D R S_cls f E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0810 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy762 D R S_cls E) ∈
      (((synCcompl (Class.cv (nb095AlphaDummy762 D R S_cls E)))).fv ∪
        ((synCcompl (Class.cv (nb095AlphaDummy763 D R S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0811 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095AlphaDummy765 x u D R S_cls f E) ∈
      (((synCcompl (Class.cv (nb095AlphaDummy765 x u D R S_cls f E)))).fv ∪
        ((synCcompl (Class.cv (nb095AlphaDummy766 x u D R S_cls f E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0812 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy762 D R S_cls E) ∈
      (((Class.cv (nb095AlphaDummy762 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy762 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0813 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095AlphaDummy765 x u D R S_cls f E) ∈
      (((Class.cv (nb095AlphaDummy765 x u D R S_cls f E))).fv ∪
        ((Class.cv (nb095AlphaDummy765 x u D R S_cls f E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0814 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy763 D R S_cls E) ∈
      (((synCcompl (Class.cv (nb095AlphaDummy762 D R S_cls E)))).fv ∪
        ((synCcompl (Class.cv (nb095AlphaDummy763 D R S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0815 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095AlphaDummy766 x u D R S_cls f E) ∈
      (((synCcompl (Class.cv (nb095AlphaDummy765 x u D R S_cls f E)))).fv ∪
        ((synCcompl (Class.cv (nb095AlphaDummy766 x u D R S_cls f E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0816 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy763 D R S_cls E) ∈
      (((Class.cv (nb095AlphaDummy763 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy763 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0817 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095AlphaDummy766 x u D R S_cls f E) ∈
      (((Class.cv (nb095AlphaDummy766 x u D R S_cls f E))).fv ∪
        ((Class.cv (nb095AlphaDummy766 x u D R S_cls f E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0818 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy739 D R S_cls E) ∈
      (((Class.cv (nb095AlphaDummy004 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy739 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0819 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy739 D R S_cls E) ∈
      (((synCcompl (Class.cab (nb095AlphaDummy747 D R S_cls E)
              (synWrex (nb095AlphaDummy748 D R S_cls E)
                (Class.cv (nb095AlphaDummy004 D R S_cls E))
                (Wff.classEq (Class.cv (nb095AlphaDummy747 D R S_cls E))
                  (synCphi (Class.cv (nb095AlphaDummy748 D R S_cls E)))))))).fv ∪
        ((synCcompl (Class.cab (nb095AlphaDummy747 D R S_cls E)
              (synWrex (nb095AlphaDummy748 D R S_cls E)
                (Class.cv (nb095AlphaDummy739 D R S_cls E))
                (Wff.classEq (Class.cv (nb095AlphaDummy747 D R S_cls E))
                  (synCun (synCphi (Class.cv (nb095AlphaDummy748 D R S_cls E)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095AlphaDummy739 D R S_cls E) ≠ (nb095AlphaDummy747 D R S_cls E) from (by
          unfold nb095AlphaDummy747;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0818 D R S_cls E) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095AlphaDummy739 D R S_cls E) ≠ (nb095AlphaDummy748 D R S_cls E) from (by
            unfold nb095AlphaDummy748;
            with_reducible
              exact
                (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0818 D R S_cls E) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0820 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095AlphaDummy740 x u D R S_cls f E) ∈
      (((Class.cv (nb095AlphaDummy006 x u D R S_cls f E))).fv ∪
        ((Class.cv (nb095AlphaDummy740 x u D R S_cls f E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0821 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095AlphaDummy740 x u D R S_cls f E) ∈
      (((synCcompl (Class.cab (nb095AlphaDummy749 x u D R S_cls f E)
              (synWrex (nb095AlphaDummy750 x u D R S_cls f E)
                (Class.cv (nb095AlphaDummy006 x u D R S_cls f E))
                (Wff.classEq (Class.cv (nb095AlphaDummy749 x u D R S_cls f E)) (synCphi
                    (Class.cv (nb095AlphaDummy750 x u D R S_cls f E)))))))).fv ∪ ((synCcompl
            (Class.cab (nb095AlphaDummy749 x u D R S_cls f E)
              (synWrex (nb095AlphaDummy750 x u D R S_cls f E)
                (Class.cv (nb095AlphaDummy740 x u D R S_cls f E))
                (Wff.classEq (Class.cv (nb095AlphaDummy749 x u D R S_cls f E))
                  (synCun (synCphi (Class.cv (nb095AlphaDummy750 x u D R S_cls f E)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095AlphaDummy740 x u D R S_cls f E) ≠
          (nb095AlphaDummy749 x u D R S_cls f E) from (by
          unfold nb095AlphaDummy749;
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
        (show (nb095AlphaDummy740 x u D R S_cls f E) ≠
            (nb095AlphaDummy750 x u D R S_cls f E) from (by
            unfold nb095AlphaDummy750;
            with_reducible
              exact
                (Nat.ne_of_lt
                  (mem_lt_freshVar (nb095_support_mem_0820 x u D R S_cls f E) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0822 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy739 D R S_cls E) ∈
      (((Class.cab (nb095AlphaDummy747 D R S_cls E)
            (synWrex (nb095AlphaDummy748 D R S_cls E)
              (Class.cv (nb095AlphaDummy739 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy747 D R S_cls E))
                (synCun (synCphi (Class.cv (nb095AlphaDummy748 D R S_cls E)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb095AlphaDummy747 D R S_cls E)
            (synWrex (nb095AlphaDummy748 D R S_cls E)
              (Class.cv (nb095AlphaDummy739 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy747 D R S_cls E))
                (synCun (synCphi (Class.cv (nb095AlphaDummy748 D R S_cls E)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095AlphaDummy739 D R S_cls E) ≠ (nb095AlphaDummy747 D R S_cls E) from (by
          unfold nb095AlphaDummy747;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0818 D R S_cls E) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095AlphaDummy739 D R S_cls E) ≠ (nb095AlphaDummy748 D R S_cls E) from (by
            unfold nb095AlphaDummy748;
            with_reducible
              exact
                (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0818 D R S_cls E) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0823 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095AlphaDummy740 x u D R S_cls f E) ∈
      (((Class.cab (nb095AlphaDummy749 x u D R S_cls f E)
            (synWrex (nb095AlphaDummy750 x u D R S_cls f E)
              (Class.cv (nb095AlphaDummy740 x u D R S_cls f E))
              (Wff.classEq (Class.cv (nb095AlphaDummy749 x u D R S_cls f E))
                (synCun (synCphi (Class.cv (nb095AlphaDummy750 x u D R S_cls f E)))
                  (synCsn (synC0c))))))).fv ∪
        ((Class.cab (nb095AlphaDummy749 x u D R S_cls f E)
            (synWrex (nb095AlphaDummy750 x u D R S_cls f E)
              (Class.cv (nb095AlphaDummy740 x u D R S_cls f E))
              (Wff.classEq (Class.cv (nb095AlphaDummy749 x u D R S_cls f E))
                (synCun (synCphi (Class.cv (nb095AlphaDummy750 x u D R S_cls f E)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095AlphaDummy740 x u D R S_cls f E) ≠
          (nb095AlphaDummy749 x u D R S_cls f E) from (by
          unfold nb095AlphaDummy749;
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
        (show (nb095AlphaDummy740 x u D R S_cls f E) ≠
            (nb095AlphaDummy750 x u D R S_cls f E) from (by
            unfold nb095AlphaDummy750;
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
    (nb095AlphaDummy748 D R S_cls E) ∈
      (((synCcompl (synCphi (Class.cv (nb095AlphaDummy748 D R S_cls E))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0825 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095AlphaDummy750 x u D R S_cls f E) ∈
      (((synCcompl (synCphi (Class.cv (nb095AlphaDummy750 x u D R S_cls f E))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0826 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy748 D R S_cls E) ∈
      (((synCphi (Class.cv (nb095AlphaDummy748 D R S_cls E)))).fv ∪
        ((synCphi (Class.cv (nb095AlphaDummy748 D R S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0827 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095AlphaDummy750 x u D R S_cls f E) ∈
      (((synCphi (Class.cv (nb095AlphaDummy750 x u D R S_cls f E)))).fv ∪
        ((synCphi (Class.cv (nb095AlphaDummy750 x u D R S_cls f E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0828 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy000 D R S_cls E) ∈
      (((Class.cab (nb095AlphaDummy661 D R S_cls E)
            (synWrex (nb095AlphaDummy662 D R S_cls E)
              (synCfv (Class.cv (nb095AlphaDummy000 D R S_cls E))
                (Class.cv (nb095AlphaDummy004 D R S_cls E)))
              (Wff.classEq (Class.cv (nb095AlphaDummy661 D R S_cls E))
                (synCun (synCphi (Class.cv (nb095AlphaDummy662 D R S_cls E)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb095AlphaDummy661 D R S_cls E)
            (synWrex (nb095AlphaDummy662 D R S_cls E)
              (synCfv (Class.cv (nb095AlphaDummy000 D R S_cls E))
                (Class.cv (nb095AlphaDummy004 D R S_cls E)))
              (Wff.classEq (Class.cv (nb095AlphaDummy661 D R S_cls E))
                (synCun (synCphi (Class.cv (nb095AlphaDummy662 D R S_cls E)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095AlphaDummy000 D R S_cls E) ≠ (nb095AlphaDummy661 D R S_cls E) from (by
          unfold nb095AlphaDummy661;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0742 D R S_cls E) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095AlphaDummy000 D R S_cls E) ≠ (nb095AlphaDummy662 D R S_cls E) from (by
            unfold nb095AlphaDummy662;
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
      (((Class.cab (nb095AlphaDummy663 x u D R S_cls f E)
            (synWrex (nb095AlphaDummy664 x u D R S_cls f E)
              (synCfv (Class.cv f) (Class.cv (nb095AlphaDummy006 x u D R S_cls f E)))
              (Wff.classEq (Class.cv (nb095AlphaDummy663 x u D R S_cls f E))
                (synCun (synCphi (Class.cv (nb095AlphaDummy664 x u D R S_cls f E)))
                  (synCsn (synC0c))))))).fv ∪
        ((Class.cab (nb095AlphaDummy663 x u D R S_cls f E)
            (synWrex (nb095AlphaDummy664 x u D R S_cls f E)
              (synCfv (Class.cv f) (Class.cv (nb095AlphaDummy006 x u D R S_cls f E)))
              (Wff.classEq (Class.cv (nb095AlphaDummy663 x u D R S_cls f E))
                (synCun (synCphi (Class.cv (nb095AlphaDummy664 x u D R S_cls f E)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show f ≠ (nb095AlphaDummy663 x u D R S_cls f E) from (by
          unfold nb095AlphaDummy663;
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
        (show f ≠ (nb095AlphaDummy664 x u D R S_cls f E) from (by
            unfold nb095AlphaDummy664;
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
    (nb095AlphaDummy000 D R S_cls E) ∈
      (((Class.cv (nb095AlphaDummy000 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy004 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0831 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy000 D R S_cls E) ∈
      (({(nb095AlphaDummy739 D R S_cls E)} : Finset Var) ∪
        ((synWbr (Class.cv (nb095AlphaDummy004 D R S_cls E))
            (Class.cv (nb095AlphaDummy000 D R S_cls E))
            (Class.cv (nb095AlphaDummy739 D R S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_wbr]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0832 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy000 D R S_cls E) ∈
      (((Class.cab (nb095AlphaDummy741 D R S_cls E) (Wff.classEq
            (Class.cab (nb095AlphaDummy739 D R S_cls E)
              (synWbr (Class.cv (nb095AlphaDummy004 D R S_cls E))
                (Class.cv (nb095AlphaDummy000 D R S_cls E))
                (Class.cv (nb095AlphaDummy739 D R S_cls E))))
            (synCsn (Class.cv (nb095AlphaDummy741 D R S_cls E)))))).fv) :=
  by
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095AlphaDummy000 D R S_cls E) ≠ (nb095AlphaDummy741 D R S_cls E) from (by
          unfold nb095AlphaDummy741;
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
        (show (nb095AlphaDummy000 D R S_cls E) ≠ (nb095AlphaDummy739 D R S_cls E) from (by
            unfold nb095AlphaDummy739;
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
    f ∈ (((Class.cv f)).fv ∪ ((Class.cv (nb095AlphaDummy006 x u D R S_cls f E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0834 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    f ∈
      (({(nb095AlphaDummy740 x u D R S_cls f E)} : Finset Var) ∪
        ((synWbr (Class.cv (nb095AlphaDummy006 x u D R S_cls f E)) (Class.cv f)
            (Class.cv (nb095AlphaDummy740 x u D R S_cls f E)))).fv) :=
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
      (((Class.cab (nb095AlphaDummy742 x u D R S_cls f E) (Wff.classEq
            (Class.cab (nb095AlphaDummy740 x u D R S_cls f E)
              (synWbr (Class.cv (nb095AlphaDummy006 x u D R S_cls f E)) (Class.cv f)
                (Class.cv (nb095AlphaDummy740 x u D R S_cls f E))))
            (synCsn (Class.cv (nb095AlphaDummy742 x u D R S_cls f E)))))).fv) :=
  by
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show f ≠ (nb095AlphaDummy742 x u D R S_cls f E) from (by
          unfold nb095AlphaDummy742;
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
        (show f ≠ (nb095AlphaDummy740 x u D R S_cls f E) from (by
            unfold nb095AlphaDummy740;
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
    (nb095AlphaDummy741 D R S_cls E) ∈
      (((Class.cv (nb095AlphaDummy741 D R S_cls E))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0837 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095AlphaDummy742 x u D R S_cls f E) ∈
      (((Class.cv (nb095AlphaDummy742 x u D R S_cls f E))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0838 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy662 D R S_cls E) ∈
      (((synCcompl (synCphi (Class.cv (nb095AlphaDummy662 D R S_cls E))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0839 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095AlphaDummy664 x u D R S_cls f E) ∈
      (((synCcompl (synCphi (Class.cv (nb095AlphaDummy664 x u D R S_cls f E))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0840 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy662 D R S_cls E) ∈
      (((synCphi (Class.cv (nb095AlphaDummy662 D R S_cls E)))).fv ∪
        ((synCphi (Class.cv (nb095AlphaDummy662 D R S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0841 (x : Var) (u : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) :
    (nb095AlphaDummy664 x u D R S_cls f E) ∈
      (((synCphi (Class.cv (nb095AlphaDummy664 x u D R S_cls f E)))).fv ∪
        ((synCphi (Class.cv (nb095AlphaDummy664 x u D R S_cls f E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0842 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy793 D R S_cls E) ∈
      (({(nb095AlphaDummy793 D R S_cls E)} : Finset Var) ∪
          ({(nb095AlphaDummy794 D R S_cls E)} : Finset Var) ∪ ((synWa
            (Wff.classMem (Class.cv (nb095AlphaDummy793 D R S_cls E)) (synCin E
                (synCima (synCcnv (synCdif S_cls (synCid)))
                  (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E))))))
            (Wff.classMem (Class.cv (nb095AlphaDummy794 D R S_cls E)) (synCin E
                (synCima (synCcnv (synCdif S_cls (synCid)))
                  (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0843 (u : Var) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy795 u S_cls E) ∈
      (({(nb095AlphaDummy795 u S_cls E)} : Finset Var) ∪
          ({(nb095AlphaDummy796 u S_cls E)} : Finset Var) ∪ ((synWa
            (Wff.classMem (Class.cv (nb095AlphaDummy795 u S_cls E)) (synCin E
                (synCima (synCcnv (synCdif S_cls (synCid))) (synCsn (Class.cv u)))))
            (Wff.classMem (Class.cv (nb095AlphaDummy796 u S_cls E)) (synCin E
                (synCima (synCcnv (synCdif S_cls (synCid)))
                  (synCsn (Class.cv u))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0844 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy794 D R S_cls E) ∈
      (({(nb095AlphaDummy793 D R S_cls E)} : Finset Var) ∪
          ({(nb095AlphaDummy794 D R S_cls E)} : Finset Var) ∪ ((synWa
            (Wff.classMem (Class.cv (nb095AlphaDummy793 D R S_cls E)) (synCin E
                (synCima (synCcnv (synCdif S_cls (synCid)))
                  (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E))))))
            (Wff.classMem (Class.cv (nb095AlphaDummy794 D R S_cls E)) (synCin E
                (synCima (synCcnv (synCdif S_cls (synCid)))
                  (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0845 (u : Var) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy796 u S_cls E) ∈
      (({(nb095AlphaDummy795 u S_cls E)} : Finset Var) ∪
          ({(nb095AlphaDummy796 u S_cls E)} : Finset Var) ∪ ((synWa
            (Wff.classMem (Class.cv (nb095AlphaDummy795 u S_cls E)) (synCin E
                (synCima (synCcnv (synCdif S_cls (synCid))) (synCsn (Class.cv u)))))
            (Wff.classMem (Class.cv (nb095AlphaDummy796 u S_cls E)) (synCin E
                (synCima (synCcnv (synCdif S_cls (synCid)))
                  (synCsn (Class.cv u))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0846 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy793 D R S_cls E) ∈
      (((Class.cv (nb095AlphaDummy793 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy794 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0847 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy793 D R S_cls E) ∈
      (((synCcompl (Class.cab (nb095AlphaDummy799 D R S_cls E)
              (synWrex (nb095AlphaDummy800 D R S_cls E)
                (Class.cv (nb095AlphaDummy793 D R S_cls E))
                (Wff.classEq (Class.cv (nb095AlphaDummy799 D R S_cls E))
                  (synCphi (Class.cv (nb095AlphaDummy800 D R S_cls E)))))))).fv ∪
        ((synCcompl (Class.cab (nb095AlphaDummy799 D R S_cls E)
              (synWrex (nb095AlphaDummy800 D R S_cls E)
                (Class.cv (nb095AlphaDummy794 D R S_cls E))
                (Wff.classEq (Class.cv (nb095AlphaDummy799 D R S_cls E))
                  (synCun (synCphi (Class.cv (nb095AlphaDummy800 D R S_cls E)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095AlphaDummy793 D R S_cls E) ≠ (nb095AlphaDummy799 D R S_cls E) from (by
          unfold nb095AlphaDummy799;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0846 D R S_cls E) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095AlphaDummy793 D R S_cls E) ≠ (nb095AlphaDummy800 D R S_cls E) from (by
            unfold nb095AlphaDummy800;
            with_reducible
              exact
                (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0846 D R S_cls E) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0848 (u : Var) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy795 u S_cls E) ∈
      (((Class.cv (nb095AlphaDummy795 u S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy796 u S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0849 (u : Var) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy795 u S_cls E) ∈
      (((synCcompl (Class.cab (nb095AlphaDummy801 u S_cls E)
              (synWrex (nb095AlphaDummy802 u S_cls E)
                (Class.cv (nb095AlphaDummy795 u S_cls E))
                (Wff.classEq (Class.cv (nb095AlphaDummy801 u S_cls E))
                  (synCphi (Class.cv (nb095AlphaDummy802 u S_cls E)))))))).fv ∪ ((synCcompl
            (Class.cab (nb095AlphaDummy801 u S_cls E)
              (synWrex (nb095AlphaDummy802 u S_cls E)
                (Class.cv (nb095AlphaDummy796 u S_cls E))
                (Wff.classEq (Class.cv (nb095AlphaDummy801 u S_cls E))
                  (synCun (synCphi (Class.cv (nb095AlphaDummy802 u S_cls E)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095AlphaDummy795 u S_cls E) ≠ (nb095AlphaDummy801 u S_cls E) from (by
          unfold nb095AlphaDummy801;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0848 u S_cls E) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095AlphaDummy795 u S_cls E) ≠ (nb095AlphaDummy802 u S_cls E) from (by
            unfold nb095AlphaDummy802;
            with_reducible
              exact
                (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0848 u S_cls E) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0850 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy793 D R S_cls E) ∈
      (((Class.cab (nb095AlphaDummy799 D R S_cls E)
            (synWrex (nb095AlphaDummy800 D R S_cls E)
              (Class.cv (nb095AlphaDummy793 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy799 D R S_cls E))
                (synCphi (Class.cv (nb095AlphaDummy800 D R S_cls E))))))).fv ∪
        ((Class.cab (nb095AlphaDummy799 D R S_cls E)
            (synWrex (nb095AlphaDummy800 D R S_cls E)
              (Class.cv (nb095AlphaDummy793 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy799 D R S_cls E))
                (synCphi (Class.cv (nb095AlphaDummy800 D R S_cls E))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095AlphaDummy793 D R S_cls E) ≠ (nb095AlphaDummy799 D R S_cls E) from (by
          unfold nb095AlphaDummy799;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0846 D R S_cls E) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095AlphaDummy793 D R S_cls E) ≠ (nb095AlphaDummy800 D R S_cls E) from (by
            unfold nb095AlphaDummy800;
            with_reducible
              exact
                (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0846 D R S_cls E) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0851 (u : Var) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy795 u S_cls E) ∈
      (((Class.cab (nb095AlphaDummy801 u S_cls E) (synWrex (nb095AlphaDummy802 u S_cls E)
              (Class.cv (nb095AlphaDummy795 u S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy801 u S_cls E))
                (synCphi (Class.cv (nb095AlphaDummy802 u S_cls E))))))).fv ∪
        ((Class.cab (nb095AlphaDummy801 u S_cls E)
            (synWrex (nb095AlphaDummy802 u S_cls E)
              (Class.cv (nb095AlphaDummy795 u S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy801 u S_cls E))
                (synCphi (Class.cv (nb095AlphaDummy802 u S_cls E))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095AlphaDummy795 u S_cls E) ≠ (nb095AlphaDummy801 u S_cls E) from (by
          unfold nb095AlphaDummy801;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0848 u S_cls E) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095AlphaDummy795 u S_cls E) ≠ (nb095AlphaDummy802 u S_cls E) from (by
            unfold nb095AlphaDummy802;
            with_reducible
              exact
                (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0848 u S_cls E) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0852 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy800 D R S_cls E) ∈
      (((Class.cv (nb095AlphaDummy800 D R S_cls E))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0853 (u : Var) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy802 u S_cls E) ∈
      (((Class.cv (nb095AlphaDummy802 u S_cls E))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0854 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy807 D R S_cls E) ∈
      (((Wff.classMem (Class.cv (nb095AlphaDummy807 D R S_cls E)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb095AlphaDummy807 D R S_cls E)) (synC1c))).fv ∪
        ((Class.cv (nb095AlphaDummy807 D R S_cls E))).fv) :=
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
    (nb095AlphaDummy809 u S_cls E) ∈
      (((Wff.classMem (Class.cv (nb095AlphaDummy809 u S_cls E)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb095AlphaDummy809 u S_cls E)) (synC1c))).fv ∪
        ((Class.cv (nb095AlphaDummy809 u S_cls E))).fv) :=
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
    (nb095AlphaDummy807 D R S_cls E) ∈
      (((Class.cv (nb095AlphaDummy807 D R S_cls E))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0857 (u : Var) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy809 u S_cls E) ∈
      (((Class.cv (nb095AlphaDummy809 u S_cls E))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0858 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy814 D R S_cls E) ∈
      (((synCnin (Class.cv (nb095AlphaDummy814 D R S_cls E))
            (Class.cv (nb095AlphaDummy815 D R S_cls E)))).fv ∪
        ((synCnin (Class.cv (nb095AlphaDummy814 D R S_cls E))
            (Class.cv (nb095AlphaDummy815 D R S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0859 (u : Var) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy817 u S_cls E) ∈
      (((synCnin (Class.cv (nb095AlphaDummy817 u S_cls E))
            (Class.cv (nb095AlphaDummy818 u S_cls E)))).fv ∪
        ((synCnin (Class.cv (nb095AlphaDummy817 u S_cls E))
            (Class.cv (nb095AlphaDummy818 u S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0860 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy814 D R S_cls E) ∈
      (((Class.cv (nb095AlphaDummy814 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy815 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0861 (u : Var) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy817 u S_cls E) ∈
      (((Class.cv (nb095AlphaDummy817 u S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy818 u S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0862 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy815 D R S_cls E) ∈
      (((synCnin (Class.cv (nb095AlphaDummy814 D R S_cls E))
            (Class.cv (nb095AlphaDummy815 D R S_cls E)))).fv ∪
        ((synCnin (Class.cv (nb095AlphaDummy814 D R S_cls E))
            (Class.cv (nb095AlphaDummy815 D R S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0863 (u : Var) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy818 u S_cls E) ∈
      (((synCnin (Class.cv (nb095AlphaDummy817 u S_cls E))
            (Class.cv (nb095AlphaDummy818 u S_cls E)))).fv ∪
        ((synCnin (Class.cv (nb095AlphaDummy817 u S_cls E))
            (Class.cv (nb095AlphaDummy818 u S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0864 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy815 D R S_cls E) ∈
      (((Class.cv (nb095AlphaDummy814 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy815 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0865 (u : Var) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy818 u S_cls E) ∈
      (((Class.cv (nb095AlphaDummy817 u S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy818 u S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0866 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy814 D R S_cls E) ∈
      (((synCcompl (Class.cv (nb095AlphaDummy814 D R S_cls E)))).fv ∪
        ((synCcompl (Class.cv (nb095AlphaDummy815 D R S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0867 (u : Var) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy817 u S_cls E) ∈
      (((synCcompl (Class.cv (nb095AlphaDummy817 u S_cls E)))).fv ∪
        ((synCcompl (Class.cv (nb095AlphaDummy818 u S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0868 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy814 D R S_cls E) ∈
      (((Class.cv (nb095AlphaDummy814 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy814 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0869 (u : Var) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy817 u S_cls E) ∈
      (((Class.cv (nb095AlphaDummy817 u S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy817 u S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0870 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy815 D R S_cls E) ∈
      (((synCcompl (Class.cv (nb095AlphaDummy814 D R S_cls E)))).fv ∪
        ((synCcompl (Class.cv (nb095AlphaDummy815 D R S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0871 (u : Var) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy818 u S_cls E) ∈
      (((synCcompl (Class.cv (nb095AlphaDummy817 u S_cls E)))).fv ∪
        ((synCcompl (Class.cv (nb095AlphaDummy818 u S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0872 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy815 D R S_cls E) ∈
      (((Class.cv (nb095AlphaDummy815 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy815 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0873 (u : Var) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy818 u S_cls E) ∈
      (((Class.cv (nb095AlphaDummy818 u S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy818 u S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0874 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy794 D R S_cls E) ∈
      (((Class.cv (nb095AlphaDummy793 D R S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy794 D R S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0875 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy794 D R S_cls E) ∈
      (((synCcompl (Class.cab (nb095AlphaDummy799 D R S_cls E)
              (synWrex (nb095AlphaDummy800 D R S_cls E)
                (Class.cv (nb095AlphaDummy793 D R S_cls E))
                (Wff.classEq (Class.cv (nb095AlphaDummy799 D R S_cls E))
                  (synCphi (Class.cv (nb095AlphaDummy800 D R S_cls E)))))))).fv ∪
        ((synCcompl (Class.cab (nb095AlphaDummy799 D R S_cls E)
              (synWrex (nb095AlphaDummy800 D R S_cls E)
                (Class.cv (nb095AlphaDummy794 D R S_cls E))
                (Wff.classEq (Class.cv (nb095AlphaDummy799 D R S_cls E))
                  (synCun (synCphi (Class.cv (nb095AlphaDummy800 D R S_cls E)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095AlphaDummy794 D R S_cls E) ≠ (nb095AlphaDummy799 D R S_cls E) from (by
          unfold nb095AlphaDummy799;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0874 D R S_cls E) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095AlphaDummy794 D R S_cls E) ≠ (nb095AlphaDummy800 D R S_cls E) from (by
            unfold nb095AlphaDummy800;
            with_reducible
              exact
                (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0874 D R S_cls E) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0876 (u : Var) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy796 u S_cls E) ∈
      (((Class.cv (nb095AlphaDummy795 u S_cls E))).fv ∪
        ((Class.cv (nb095AlphaDummy796 u S_cls E))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0877 (u : Var) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy796 u S_cls E) ∈
      (((synCcompl (Class.cab (nb095AlphaDummy801 u S_cls E)
              (synWrex (nb095AlphaDummy802 u S_cls E)
                (Class.cv (nb095AlphaDummy795 u S_cls E))
                (Wff.classEq (Class.cv (nb095AlphaDummy801 u S_cls E))
                  (synCphi (Class.cv (nb095AlphaDummy802 u S_cls E)))))))).fv ∪ ((synCcompl
            (Class.cab (nb095AlphaDummy801 u S_cls E)
              (synWrex (nb095AlphaDummy802 u S_cls E)
                (Class.cv (nb095AlphaDummy796 u S_cls E))
                (Wff.classEq (Class.cv (nb095AlphaDummy801 u S_cls E))
                  (synCun (synCphi (Class.cv (nb095AlphaDummy802 u S_cls E)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095AlphaDummy796 u S_cls E) ≠ (nb095AlphaDummy801 u S_cls E) from (by
          unfold nb095AlphaDummy801;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0876 u S_cls E) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095AlphaDummy796 u S_cls E) ≠ (nb095AlphaDummy802 u S_cls E) from (by
            unfold nb095AlphaDummy802;
            with_reducible
              exact
                (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0876 u S_cls E) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0878 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy794 D R S_cls E) ∈
      (((Class.cab (nb095AlphaDummy799 D R S_cls E)
            (synWrex (nb095AlphaDummy800 D R S_cls E)
              (Class.cv (nb095AlphaDummy794 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy799 D R S_cls E))
                (synCun (synCphi (Class.cv (nb095AlphaDummy800 D R S_cls E)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb095AlphaDummy799 D R S_cls E)
            (synWrex (nb095AlphaDummy800 D R S_cls E)
              (Class.cv (nb095AlphaDummy794 D R S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy799 D R S_cls E))
                (synCun (synCphi (Class.cv (nb095AlphaDummy800 D R S_cls E)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095AlphaDummy794 D R S_cls E) ≠ (nb095AlphaDummy799 D R S_cls E) from (by
          unfold nb095AlphaDummy799;
          with_reducible
            exact
              (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0874 D R S_cls E) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095AlphaDummy794 D R S_cls E) ≠ (nb095AlphaDummy800 D R S_cls E) from (by
            unfold nb095AlphaDummy800;
            with_reducible
              exact
                (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0874 D R S_cls E) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0879 (u : Var) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy796 u S_cls E) ∈
      (((Class.cab (nb095AlphaDummy801 u S_cls E) (synWrex (nb095AlphaDummy802 u S_cls E)
              (Class.cv (nb095AlphaDummy796 u S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy801 u S_cls E))
                (synCun (synCphi (Class.cv (nb095AlphaDummy802 u S_cls E)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb095AlphaDummy801 u S_cls E)
            (synWrex (nb095AlphaDummy802 u S_cls E)
              (Class.cv (nb095AlphaDummy796 u S_cls E))
              (Wff.classEq (Class.cv (nb095AlphaDummy801 u S_cls E))
                (synCun (synCphi (Class.cv (nb095AlphaDummy802 u S_cls E)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb095AlphaDummy796 u S_cls E) ≠ (nb095AlphaDummy801 u S_cls E) from (by
          unfold nb095AlphaDummy801;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0876 u S_cls E) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb095AlphaDummy796 u S_cls E) ≠ (nb095AlphaDummy802 u S_cls E) from (by
            unfold nb095AlphaDummy802;
            with_reducible
              exact
                (Nat.ne_of_lt (mem_lt_freshVar (nb095_support_mem_0876 u S_cls E) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb095_support_mem_0880 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy800 D R S_cls E) ∈
      (((synCcompl (synCphi (Class.cv (nb095AlphaDummy800 D R S_cls E))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0881 (u : Var) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy802 u S_cls E) ∈
      (((synCcompl (synCphi (Class.cv (nb095AlphaDummy802 u S_cls E))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0882 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy800 D R S_cls E) ∈
      (((synCphi (Class.cv (nb095AlphaDummy800 D R S_cls E)))).fv ∪
        ((synCphi (Class.cv (nb095AlphaDummy800 D R S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0883 (u : Var) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy802 u S_cls E) ∈
      (((synCphi (Class.cv (nb095AlphaDummy802 u S_cls E)))).fv ∪
        ((synCphi (Class.cv (nb095AlphaDummy802 u S_cls E)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb095_support_mem_0884 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy001 D R S_cls E) ∈
      (((Class.cv (nb095AlphaDummy000 D R S_cls E))).fv ∪ ((synCin R (synCxp (synCin D
                      (synCima (synCcnv (synCdif R (synCid)))
                        (synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E))))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid)))
                        (synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E)))))))).fv ∪
            ((synCin S_cls (synCxp (synCin E (synCima (synCcnv (synCdif S_cls (synCid)))
                      (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E))))) (synCin E
                    (synCima (synCcnv (synCdif S_cls (synCid)))
                      (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E)))))))).fv ∪
          ((synCin D (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (Class.cv (nb095AlphaDummy002 D R S_cls E)))))).fv ∪ ((synCin E
            (synCima (synCcnv (synCdif S_cls (synCid)))
              (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E)))))).fv) :=
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
      (((Class.cv f)).fv ∪ ((synCin R (synCxp (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (Class.cv x))))
                    (synCin D (synCima (synCcnv (synCdif R (synCid)))
                        (synCsn (Class.cv x))))))).fv ∪ ((synCin S_cls (synCxp (synCin E
                    (synCima (synCcnv (synCdif S_cls (synCid))) (synCsn (Class.cv u))))
                  (synCin E (synCima (synCcnv (synCdif S_cls (synCid)))
                      (synCsn (Class.cv u))))))).fv ∪ ((synCin D
              (synCima (synCcnv (synCdif R (synCid))) (synCsn (Class.cv x))))).fv ∪
        ((synCin E (synCima (synCcnv (synCdif S_cls (synCid)))
              (synCsn (Class.cv u))))).fv) :=
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
    (nb095AlphaDummy001 D R S_cls E) ∈
      (((synCnin S_cls (synCxp (synCin E (synCima (synCcnv (synCdif S_cls (synCid)))
                  (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E))))) (synCin E
                (synCima (synCcnv (synCdif S_cls (synCid)))
                  (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E)))))))).fv ∪
        ((synCnin S_cls (synCxp (synCin E (synCima (synCcnv (synCdif S_cls (synCid)))
                  (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E))))) (synCin E
                (synCima (synCcnv (synCdif S_cls (synCid)))
                  (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E)))))))).fv) :=
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
      (((synCnin S_cls (synCxp (synCin E
                (synCima (synCcnv (synCdif S_cls (synCid))) (synCsn (Class.cv u))))
              (synCin E (synCima (synCcnv (synCdif S_cls (synCid)))
                  (synCsn (Class.cv u))))))).fv ∪ ((synCnin S_cls (synCxp (synCin E
                (synCima (synCcnv (synCdif S_cls (synCid))) (synCsn (Class.cv u))))
              (synCin E (synCima (synCcnv (synCdif S_cls (synCid)))
                  (synCsn (Class.cv u))))))).fv) :=
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
    (nb095AlphaDummy001 D R S_cls E) ∈
      ((S_cls).fv ∪ ((synCxp (synCin E (synCima (synCcnv (synCdif S_cls (synCid)))
                (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E))))) (synCin E
              (synCima (synCcnv (synCdif S_cls (synCid)))
                (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E))))))).fv) :=
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
      ((S_cls).fv ∪ ((synCxp (synCin E
              (synCima (synCcnv (synCdif S_cls (synCid))) (synCsn (Class.cv u))))
            (synCin E (synCima (synCcnv (synCdif S_cls (synCid)))
                (synCsn (Class.cv u)))))).fv) :=
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
    (nb095AlphaDummy001 D R S_cls E) ∈
      (({(nb095AlphaDummy793 D R S_cls E)} : Finset Var) ∪
          ({(nb095AlphaDummy794 D R S_cls E)} : Finset Var) ∪ ((synWa
            (Wff.classMem (Class.cv (nb095AlphaDummy793 D R S_cls E)) (synCin E
                (synCima (synCcnv (synCdif S_cls (synCid)))
                  (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E))))))
            (Wff.classMem (Class.cv (nb095AlphaDummy794 D R S_cls E)) (synCin E
                (synCima (synCcnv (synCdif S_cls (synCid)))
                  (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E)))))))).fv) :=
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
      (({(nb095AlphaDummy795 u S_cls E)} : Finset Var) ∪
          ({(nb095AlphaDummy796 u S_cls E)} : Finset Var) ∪ ((synWa
            (Wff.classMem (Class.cv (nb095AlphaDummy795 u S_cls E)) (synCin E
                (synCima (synCcnv (synCdif S_cls (synCid))) (synCsn (Class.cv u)))))
            (Wff.classMem (Class.cv (nb095AlphaDummy796 u S_cls E)) (synCin E
                (synCima (synCcnv (synCdif S_cls (synCid)))
                  (synCsn (Class.cv u))))))).fv) :=
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
    (nb095AlphaDummy001 D R S_cls E) ∈
      (((synCin E (synCima (synCcnv (synCdif S_cls (synCid)))
              (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E)))))).fv ∪ ((synCin E
            (synCima (synCcnv (synCdif S_cls (synCid)))
              (synCsn (Class.cv (nb095AlphaDummy001 D R S_cls E)))))).fv) :=
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
      (((synCin E
            (synCima (synCcnv (synCdif S_cls (synCid))) (synCsn (Class.cv u))))).fv ∪
        ((synCin E (synCima (synCcnv (synCdif S_cls (synCid)))
              (synCsn (Class.cv u))))).fv) :=
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
    (nb095AlphaDummy002 D R S_cls E) ∉ D.fv :=
  by
  change freshVar ((R).fv ∪ (D).fv ∪ (S_cls).fv ∪ (E).fv) 2 ∉ D.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 2
      (fun _ hu =>
        Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (hu))))

theorem nb095_focused_notmem_0001 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy000 D R S_cls E) ∉ D.fv :=
  by
  change freshVar ((R).fv ∪ (D).fv ∪ (S_cls).fv ∪ (E).fv) 0 ∉ D.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun _ hu =>
        Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (hu))))

theorem nb095_compact_envfresh_0000 (x : Var) (D : Class) (R : Class) (S_cls : Class)
    (f : Var) (E : Class) (dv_D_f : f ∉ D.fv) (dv_D_x : x ∉ D.fv) :
    TEnvFresh
      [((nb095AlphaDummy002 D R S_cls E), x), ((nb095AlphaDummy000 D R S_cls E), f)]
      D.fv :=
  by
  exact
    (TEnvFresh.consFresh (nb095AlphaDummy002 D R S_cls E) x
      (nb095_focused_notmem_0000 D R S_cls E) dv_D_x
      (TEnvFresh.consFresh (nb095AlphaDummy000 D R S_cls E) f
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

/-- Checked nominal proof certificate identified upstream as `nb095_focused_refl_0000`. -/
@[expose]
noncomputable def nb095FocusedRefl0000 (x : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) (dv_D_f : f ∉ D.fv) (dv_D_x : x ∉ D.fv) :
    TReflOn
      [((nb095AlphaDummy002 D R S_cls E), x), ((nb095AlphaDummy000 D R S_cls E), f)]
      D.fv :=
  TEnvFresh.reflOn (nb095_compact_envfresh_0000 x D R S_cls f E dv_D_f dv_D_x)

theorem nb095_focused_notmem_0002 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy001 D R S_cls E) ∉ E.fv :=
  by
  change freshVar ((R).fv ∪ (D).fv ∪ (S_cls).fv ∪ (E).fv) 1 ∉ E.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1
      (fun _ hu => Finset.mem_union_right _ (hu))

theorem nb095_focused_notmem_0003 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy002 D R S_cls E) ∉ E.fv :=
  by
  change freshVar ((R).fv ∪ (D).fv ∪ (S_cls).fv ∪ (E).fv) 2 ∉ E.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 2
      (fun _ hu => Finset.mem_union_right _ (hu))

theorem nb095_focused_notmem_0004 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy000 D R S_cls E) ∉ E.fv :=
  by
  change freshVar ((R).fv ∪ (D).fv ∪ (S_cls).fv ∪ (E).fv) 0 ∉ E.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun _ hu => Finset.mem_union_right _ (hu))

theorem nb095_compact_envfresh_0001 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) (dv_E_f : f ∉ E.fv) (dv_E_u : u ∉ E.fv)
    (dv_E_x : x ∉ E.fv) :
    TEnvFresh
      [((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)]
      E.fv :=
  by
  exact
    (TEnvFresh.consFresh (nb095AlphaDummy001 D R S_cls E) u
      (nb095_focused_notmem_0002 D R S_cls E) dv_E_u
      (TEnvFresh.consFresh (nb095AlphaDummy002 D R S_cls E) x
        (nb095_focused_notmem_0003 D R S_cls E) dv_E_x
        (TEnvFresh.consFresh (nb095AlphaDummy000 D R S_cls E) f
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

/-- Checked nominal proof certificate identified upstream as `nb095_focused_refl_0001`. -/
@[expose]
noncomputable def nb095FocusedRefl0001 (x : Var) (u : Var) (D : Class) (R : Class)
    (S_cls : Class) (f : Var) (E : Class) (dv_E_f : f ∉ E.fv) (dv_E_u : u ∉ E.fv)
    (dv_E_x : x ∉ E.fv) :
    TReflOn
      [((nb095AlphaDummy001 D R S_cls E), u), ((nb095AlphaDummy002 D R S_cls E), x),
        ((nb095AlphaDummy000 D R S_cls E), f)]
      E.fv :=
  TEnvFresh.reflOn (nb095_compact_envfresh_0001 x u D R S_cls f E dv_E_f dv_E_u dv_E_x)

theorem nb095_compact_fv_empty_0026 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy009 D R S_cls E) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb095_compact_fv_empty_0027 (f : Var) :
    (nb095AlphaDummy010 f) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb095_compact_fv_empty_0028 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy007 D R S_cls E) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb095_compact_fv_empty_0029 (f : Var) :
    (nb095AlphaDummy008 f) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb095_compact_fv_empty_0030 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy001 D R S_cls E) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb095_compact_fv_empty_0031 (u : Var) : u ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb095_compact_fv_empty_0032 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy002 D R S_cls E) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb095_compact_fv_empty_0033 (x : Var) : x ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb095_compact_fv_empty_0034 (D : Class) (R : Class) (S_cls : Class) (E : Class) :
    (nb095AlphaDummy000 D R S_cls E) ∉ (∅ : Finset Var) :=
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
