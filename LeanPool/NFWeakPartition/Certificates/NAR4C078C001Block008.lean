/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C078C001Block007

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C078C001Part028`. -/


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

theorem nb078_support_mem_0878 :
    (nb078AlphaDummy847) ∈
      (({(nb078AlphaDummy847)} : Finset Var) ∪ ({(nb078AlphaDummy848)} : Finset Var) ∪
        ((synWbr (Class.cv (nb078AlphaDummy848)) (Class.cv (nb078AlphaDummy002))
            (Class.cv (nb078AlphaDummy847)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0879 (h : Var) :
    (nb078AlphaDummy849 h) ∈
      (({(nb078AlphaDummy849 h)} : Finset Var) ∪ ({(nb078AlphaDummy850 h)} : Finset Var) ∪
        ((synWbr (Class.cv (nb078AlphaDummy850 h)) (Class.cv h)
            (Class.cv (nb078AlphaDummy849 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0880 :
    (nb078AlphaDummy848) ∈
      (({(nb078AlphaDummy847)} : Finset Var) ∪ ({(nb078AlphaDummy848)} : Finset Var) ∪
        ((synWbr (Class.cv (nb078AlphaDummy848)) (Class.cv (nb078AlphaDummy002))
            (Class.cv (nb078AlphaDummy847)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0881 (h : Var) :
    (nb078AlphaDummy850 h) ∈
      (({(nb078AlphaDummy849 h)} : Finset Var) ∪ ({(nb078AlphaDummy850 h)} : Finset Var) ∪
        ((synWbr (Class.cv (nb078AlphaDummy850 h)) (Class.cv h)
            (Class.cv (nb078AlphaDummy849 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0882 :
    (nb078AlphaDummy847) ∈
      (((Class.cv (nb078AlphaDummy847))).fv ∪ ((Class.cv (nb078AlphaDummy848))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0883 :
    (nb078AlphaDummy847) ∈
      (((synCcompl (Class.cab (nb078AlphaDummy853)
              (synWrex (nb078AlphaDummy854) (Class.cv (nb078AlphaDummy847))
                (Wff.classEq (Class.cv (nb078AlphaDummy853))
                  (synCphi (Class.cv (nb078AlphaDummy854)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy853)
              (synWrex (nb078AlphaDummy854) (Class.cv (nb078AlphaDummy848))
                (Wff.classEq (Class.cv (nb078AlphaDummy853))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy854)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy847) ≠ (nb078AlphaDummy853) from (by
          unfold nb078AlphaDummy853;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0882) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy847) ≠ (nb078AlphaDummy854) from (by
            unfold nb078AlphaDummy854;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0882) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0884 (h : Var) :
    (nb078AlphaDummy849 h) ∈
      (((Class.cv (nb078AlphaDummy849 h))).fv ∪ ((Class.cv (nb078AlphaDummy850 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0885 (h : Var) :
    (nb078AlphaDummy849 h) ∈
      (((synCcompl (Class.cab (nb078AlphaDummy855 h)
              (synWrex (nb078AlphaDummy856 h) (Class.cv (nb078AlphaDummy849 h))
                (Wff.classEq (Class.cv (nb078AlphaDummy855 h))
                  (synCphi (Class.cv (nb078AlphaDummy856 h)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy855 h)
              (synWrex (nb078AlphaDummy856 h) (Class.cv (nb078AlphaDummy850 h))
                (Wff.classEq (Class.cv (nb078AlphaDummy855 h))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy856 h)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy849 h) ≠ (nb078AlphaDummy855 h) from (by
          unfold nb078AlphaDummy855;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0884 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy849 h) ≠ (nb078AlphaDummy856 h) from (by
            unfold nb078AlphaDummy856;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0884 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0886 :
    (nb078AlphaDummy847) ∈
      (((Class.cab (nb078AlphaDummy853)
            (synWrex (nb078AlphaDummy854) (Class.cv (nb078AlphaDummy847))
              (Wff.classEq (Class.cv (nb078AlphaDummy853))
                (synCphi (Class.cv (nb078AlphaDummy854))))))).fv ∪
        ((Class.cab (nb078AlphaDummy853)
            (synWrex (nb078AlphaDummy854) (Class.cv (nb078AlphaDummy847))
              (Wff.classEq (Class.cv (nb078AlphaDummy853))
                (synCphi (Class.cv (nb078AlphaDummy854))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy847) ≠ (nb078AlphaDummy853) from (by
          unfold nb078AlphaDummy853;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0882) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy847) ≠ (nb078AlphaDummy854) from (by
            unfold nb078AlphaDummy854;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0882) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0887 (h : Var) :
    (nb078AlphaDummy849 h) ∈
      (((Class.cab (nb078AlphaDummy855 h)
            (synWrex (nb078AlphaDummy856 h) (Class.cv (nb078AlphaDummy849 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy855 h))
                (synCphi (Class.cv (nb078AlphaDummy856 h))))))).fv ∪
        ((Class.cab (nb078AlphaDummy855 h)
            (synWrex (nb078AlphaDummy856 h) (Class.cv (nb078AlphaDummy849 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy855 h))
                (synCphi (Class.cv (nb078AlphaDummy856 h))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy849 h) ≠ (nb078AlphaDummy855 h) from (by
          unfold nb078AlphaDummy855;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0884 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy849 h) ≠ (nb078AlphaDummy856 h) from (by
            unfold nb078AlphaDummy856;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0884 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0888 :
    (nb078AlphaDummy854) ∈ (((Class.cv (nb078AlphaDummy854))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0889 (h : Var) :
    (nb078AlphaDummy856 h) ∈ (((Class.cv (nb078AlphaDummy856 h))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0890 :
    (nb078AlphaDummy861) ∈
      (((Wff.classMem (Class.cv (nb078AlphaDummy861)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy861)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy861))).fv) :=
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

theorem nb078_support_mem_0891 (h : Var) :
    (nb078AlphaDummy863 h) ∈
      (((Wff.classMem (Class.cv (nb078AlphaDummy863 h)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy863 h)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy863 h))).fv) :=
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

theorem nb078_support_mem_0892 :
    (nb078AlphaDummy861) ∈
      (((Class.cv (nb078AlphaDummy861))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0893 (h : Var) :
    (nb078AlphaDummy863 h) ∈
      (((Class.cv (nb078AlphaDummy863 h))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0894 :
    (nb078AlphaDummy868) ∈
      (((synCnin (Class.cv (nb078AlphaDummy868)) (Class.cv (nb078AlphaDummy869)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy868))
            (Class.cv (nb078AlphaDummy869)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0895 (h : Var) :
    (nb078AlphaDummy871 h) ∈
      (((synCnin (Class.cv (nb078AlphaDummy871 h))
            (Class.cv (nb078AlphaDummy872 h)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy871 h))
            (Class.cv (nb078AlphaDummy872 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0896 :
    (nb078AlphaDummy868) ∈
      (((Class.cv (nb078AlphaDummy868))).fv ∪ ((Class.cv (nb078AlphaDummy869))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0897 (h : Var) :
    (nb078AlphaDummy871 h) ∈
      (((Class.cv (nb078AlphaDummy871 h))).fv ∪ ((Class.cv (nb078AlphaDummy872 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0898 :
    (nb078AlphaDummy869) ∈
      (((synCnin (Class.cv (nb078AlphaDummy868)) (Class.cv (nb078AlphaDummy869)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy868))
            (Class.cv (nb078AlphaDummy869)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0899 (h : Var) :
    (nb078AlphaDummy872 h) ∈
      (((synCnin (Class.cv (nb078AlphaDummy871 h))
            (Class.cv (nb078AlphaDummy872 h)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy871 h))
            (Class.cv (nb078AlphaDummy872 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0900 :
    (nb078AlphaDummy869) ∈
      (((Class.cv (nb078AlphaDummy868))).fv ∪ ((Class.cv (nb078AlphaDummy869))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0901 (h : Var) :
    (nb078AlphaDummy872 h) ∈
      (((Class.cv (nb078AlphaDummy871 h))).fv ∪ ((Class.cv (nb078AlphaDummy872 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0902 :
    (nb078AlphaDummy868) ∈
      (((synCcompl (Class.cv (nb078AlphaDummy868)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy869)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0903 (h : Var) :
    (nb078AlphaDummy871 h) ∈
      (((synCcompl (Class.cv (nb078AlphaDummy871 h)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy872 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0904 :
    (nb078AlphaDummy868) ∈
      (((Class.cv (nb078AlphaDummy868))).fv ∪ ((Class.cv (nb078AlphaDummy868))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0905 (h : Var) :
    (nb078AlphaDummy871 h) ∈
      (((Class.cv (nb078AlphaDummy871 h))).fv ∪ ((Class.cv (nb078AlphaDummy871 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0906 :
    (nb078AlphaDummy869) ∈
      (((synCcompl (Class.cv (nb078AlphaDummy868)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy869)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0907 (h : Var) :
    (nb078AlphaDummy872 h) ∈
      (((synCcompl (Class.cv (nb078AlphaDummy871 h)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy872 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0908 :
    (nb078AlphaDummy869) ∈
      (((Class.cv (nb078AlphaDummy869))).fv ∪ ((Class.cv (nb078AlphaDummy869))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0909 (h : Var) :
    (nb078AlphaDummy872 h) ∈
      (((Class.cv (nb078AlphaDummy872 h))).fv ∪ ((Class.cv (nb078AlphaDummy872 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0910 :
    (nb078AlphaDummy848) ∈
      (((Class.cv (nb078AlphaDummy847))).fv ∪ ((Class.cv (nb078AlphaDummy848))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0911 :
    (nb078AlphaDummy848) ∈
      (((synCcompl (Class.cab (nb078AlphaDummy853)
              (synWrex (nb078AlphaDummy854) (Class.cv (nb078AlphaDummy847))
                (Wff.classEq (Class.cv (nb078AlphaDummy853))
                  (synCphi (Class.cv (nb078AlphaDummy854)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy853)
              (synWrex (nb078AlphaDummy854) (Class.cv (nb078AlphaDummy848))
                (Wff.classEq (Class.cv (nb078AlphaDummy853))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy854)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy848) ≠ (nb078AlphaDummy853) from (by
          unfold nb078AlphaDummy853;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0910) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy848) ≠ (nb078AlphaDummy854) from (by
            unfold nb078AlphaDummy854;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0910) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0912 (h : Var) :
    (nb078AlphaDummy850 h) ∈
      (((Class.cv (nb078AlphaDummy849 h))).fv ∪ ((Class.cv (nb078AlphaDummy850 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0913 (h : Var) :
    (nb078AlphaDummy850 h) ∈
      (((synCcompl (Class.cab (nb078AlphaDummy855 h)
              (synWrex (nb078AlphaDummy856 h) (Class.cv (nb078AlphaDummy849 h))
                (Wff.classEq (Class.cv (nb078AlphaDummy855 h))
                  (synCphi (Class.cv (nb078AlphaDummy856 h)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy855 h)
              (synWrex (nb078AlphaDummy856 h) (Class.cv (nb078AlphaDummy850 h))
                (Wff.classEq (Class.cv (nb078AlphaDummy855 h))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy856 h)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy850 h) ≠ (nb078AlphaDummy855 h) from (by
          unfold nb078AlphaDummy855;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0912 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy850 h) ≠ (nb078AlphaDummy856 h) from (by
            unfold nb078AlphaDummy856;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0912 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0914 :
    (nb078AlphaDummy848) ∈
      (((Class.cab (nb078AlphaDummy853)
            (synWrex (nb078AlphaDummy854) (Class.cv (nb078AlphaDummy848))
              (Wff.classEq (Class.cv (nb078AlphaDummy853))
                (synCun (synCphi (Class.cv (nb078AlphaDummy854)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy853)
            (synWrex (nb078AlphaDummy854) (Class.cv (nb078AlphaDummy848))
              (Wff.classEq (Class.cv (nb078AlphaDummy853))
                (synCun (synCphi (Class.cv (nb078AlphaDummy854)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy848) ≠ (nb078AlphaDummy853) from (by
          unfold nb078AlphaDummy853;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0910) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy848) ≠ (nb078AlphaDummy854) from (by
            unfold nb078AlphaDummy854;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0910) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0915 (h : Var) :
    (nb078AlphaDummy850 h) ∈
      (((Class.cab (nb078AlphaDummy855 h)
            (synWrex (nb078AlphaDummy856 h) (Class.cv (nb078AlphaDummy850 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy855 h))
                (synCun (synCphi (Class.cv (nb078AlphaDummy856 h)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy855 h)
            (synWrex (nb078AlphaDummy856 h) (Class.cv (nb078AlphaDummy850 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy855 h))
                (synCun (synCphi (Class.cv (nb078AlphaDummy856 h)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy850 h) ≠ (nb078AlphaDummy855 h) from (by
          unfold nb078AlphaDummy855;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0912 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy850 h) ≠ (nb078AlphaDummy856 h) from (by
            unfold nb078AlphaDummy856;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0912 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0916 :
    (nb078AlphaDummy854) ∈
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy854))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0917 (h : Var) :
    (nb078AlphaDummy856 h) ∈
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy856 h))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0918 :
    (nb078AlphaDummy854) ∈
      (((synCphi (Class.cv (nb078AlphaDummy854)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy854)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0919 (h : Var) :
    (nb078AlphaDummy856 h) ∈
      (((synCphi (Class.cv (nb078AlphaDummy856 h)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy856 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0920 :
    (nb078AlphaDummy848) ∈
      (((Class.cv (nb078AlphaDummy848))).fv ∪ ((Class.cv (nb078AlphaDummy847))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0921 :
    (nb078AlphaDummy848) ∈
      (((synCcompl (Class.cab (nb078AlphaDummy889)
              (synWrex (nb078AlphaDummy890) (Class.cv (nb078AlphaDummy848))
                (Wff.classEq (Class.cv (nb078AlphaDummy889))
                  (synCphi (Class.cv (nb078AlphaDummy890)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy889)
              (synWrex (nb078AlphaDummy890) (Class.cv (nb078AlphaDummy847))
                (Wff.classEq (Class.cv (nb078AlphaDummy889))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy890)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy848) ≠ (nb078AlphaDummy889) from (by
          unfold nb078AlphaDummy889;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0920) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy848) ≠ (nb078AlphaDummy890) from (by
            unfold nb078AlphaDummy890;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0920) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0922 (h : Var) :
    (nb078AlphaDummy850 h) ∈
      (((Class.cv (nb078AlphaDummy850 h))).fv ∪ ((Class.cv (nb078AlphaDummy849 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0923 (h : Var) :
    (nb078AlphaDummy850 h) ∈
      (((synCcompl (Class.cab (nb078AlphaDummy891 h)
              (synWrex (nb078AlphaDummy892 h) (Class.cv (nb078AlphaDummy850 h))
                (Wff.classEq (Class.cv (nb078AlphaDummy891 h))
                  (synCphi (Class.cv (nb078AlphaDummy892 h)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy891 h)
              (synWrex (nb078AlphaDummy892 h) (Class.cv (nb078AlphaDummy849 h))
                (Wff.classEq (Class.cv (nb078AlphaDummy891 h))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy892 h)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy850 h) ≠ (nb078AlphaDummy891 h) from (by
          unfold nb078AlphaDummy891;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0922 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy850 h) ≠ (nb078AlphaDummy892 h) from (by
            unfold nb078AlphaDummy892;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0922 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0924 :
    (nb078AlphaDummy848) ∈
      (((Class.cab (nb078AlphaDummy889)
            (synWrex (nb078AlphaDummy890) (Class.cv (nb078AlphaDummy848))
              (Wff.classEq (Class.cv (nb078AlphaDummy889))
                (synCphi (Class.cv (nb078AlphaDummy890))))))).fv ∪
        ((Class.cab (nb078AlphaDummy889)
            (synWrex (nb078AlphaDummy890) (Class.cv (nb078AlphaDummy848))
              (Wff.classEq (Class.cv (nb078AlphaDummy889))
                (synCphi (Class.cv (nb078AlphaDummy890))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy848) ≠ (nb078AlphaDummy889) from (by
          unfold nb078AlphaDummy889;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0920) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy848) ≠ (nb078AlphaDummy890) from (by
            unfold nb078AlphaDummy890;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0920) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0925 (h : Var) :
    (nb078AlphaDummy850 h) ∈
      (((Class.cab (nb078AlphaDummy891 h)
            (synWrex (nb078AlphaDummy892 h) (Class.cv (nb078AlphaDummy850 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy891 h))
                (synCphi (Class.cv (nb078AlphaDummy892 h))))))).fv ∪
        ((Class.cab (nb078AlphaDummy891 h)
            (synWrex (nb078AlphaDummy892 h) (Class.cv (nb078AlphaDummy850 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy891 h))
                (synCphi (Class.cv (nb078AlphaDummy892 h))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy850 h) ≠ (nb078AlphaDummy891 h) from (by
          unfold nb078AlphaDummy891;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0922 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy850 h) ≠ (nb078AlphaDummy892 h) from (by
            unfold nb078AlphaDummy892;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0922 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0926 :
    (nb078AlphaDummy890) ∈ (((Class.cv (nb078AlphaDummy890))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0927 (h : Var) :
    (nb078AlphaDummy892 h) ∈ (((Class.cv (nb078AlphaDummy892 h))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0928 :
    (nb078AlphaDummy897) ∈
      (((Wff.classMem (Class.cv (nb078AlphaDummy897)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy897)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy897))).fv) :=
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

theorem nb078_support_mem_0929 (h : Var) :
    (nb078AlphaDummy899 h) ∈
      (((Wff.classMem (Class.cv (nb078AlphaDummy899 h)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy899 h)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy899 h))).fv) :=
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

theorem nb078_support_mem_0930 :
    (nb078AlphaDummy897) ∈
      (((Class.cv (nb078AlphaDummy897))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0931 (h : Var) :
    (nb078AlphaDummy899 h) ∈
      (((Class.cv (nb078AlphaDummy899 h))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0932 :
    (nb078AlphaDummy904) ∈
      (((synCnin (Class.cv (nb078AlphaDummy904)) (Class.cv (nb078AlphaDummy905)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy904))
            (Class.cv (nb078AlphaDummy905)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0933 (h : Var) :
    (nb078AlphaDummy907 h) ∈
      (((synCnin (Class.cv (nb078AlphaDummy907 h))
            (Class.cv (nb078AlphaDummy908 h)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy907 h))
            (Class.cv (nb078AlphaDummy908 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0934 :
    (nb078AlphaDummy904) ∈
      (((Class.cv (nb078AlphaDummy904))).fv ∪ ((Class.cv (nb078AlphaDummy905))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0935 (h : Var) :
    (nb078AlphaDummy907 h) ∈
      (((Class.cv (nb078AlphaDummy907 h))).fv ∪ ((Class.cv (nb078AlphaDummy908 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0936 :
    (nb078AlphaDummy905) ∈
      (((synCnin (Class.cv (nb078AlphaDummy904)) (Class.cv (nb078AlphaDummy905)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy904))
            (Class.cv (nb078AlphaDummy905)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0937 (h : Var) :
    (nb078AlphaDummy908 h) ∈
      (((synCnin (Class.cv (nb078AlphaDummy907 h))
            (Class.cv (nb078AlphaDummy908 h)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy907 h))
            (Class.cv (nb078AlphaDummy908 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0938 :
    (nb078AlphaDummy905) ∈
      (((Class.cv (nb078AlphaDummy904))).fv ∪ ((Class.cv (nb078AlphaDummy905))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0939 (h : Var) :
    (nb078AlphaDummy908 h) ∈
      (((Class.cv (nb078AlphaDummy907 h))).fv ∪ ((Class.cv (nb078AlphaDummy908 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0940 :
    (nb078AlphaDummy904) ∈
      (((synCcompl (Class.cv (nb078AlphaDummy904)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy905)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0941 (h : Var) :
    (nb078AlphaDummy907 h) ∈
      (((synCcompl (Class.cv (nb078AlphaDummy907 h)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy908 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0942 :
    (nb078AlphaDummy904) ∈
      (((Class.cv (nb078AlphaDummy904))).fv ∪ ((Class.cv (nb078AlphaDummy904))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0943 (h : Var) :
    (nb078AlphaDummy907 h) ∈
      (((Class.cv (nb078AlphaDummy907 h))).fv ∪ ((Class.cv (nb078AlphaDummy907 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0944 :
    (nb078AlphaDummy905) ∈
      (((synCcompl (Class.cv (nb078AlphaDummy904)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy905)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0945 (h : Var) :
    (nb078AlphaDummy908 h) ∈
      (((synCcompl (Class.cv (nb078AlphaDummy907 h)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy908 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0946 :
    (nb078AlphaDummy905) ∈
      (((Class.cv (nb078AlphaDummy905))).fv ∪ ((Class.cv (nb078AlphaDummy905))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0947 (h : Var) :
    (nb078AlphaDummy908 h) ∈
      (((Class.cv (nb078AlphaDummy908 h))).fv ∪ ((Class.cv (nb078AlphaDummy908 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0948 :
    (nb078AlphaDummy847) ∈
      (((Class.cv (nb078AlphaDummy848))).fv ∪ ((Class.cv (nb078AlphaDummy847))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0949 :
    (nb078AlphaDummy847) ∈
      (((synCcompl (Class.cab (nb078AlphaDummy889)
              (synWrex (nb078AlphaDummy890) (Class.cv (nb078AlphaDummy848))
                (Wff.classEq (Class.cv (nb078AlphaDummy889))
                  (synCphi (Class.cv (nb078AlphaDummy890)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy889)
              (synWrex (nb078AlphaDummy890) (Class.cv (nb078AlphaDummy847))
                (Wff.classEq (Class.cv (nb078AlphaDummy889))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy890)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy847) ≠ (nb078AlphaDummy889) from (by
          unfold nb078AlphaDummy889;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0948) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy847) ≠ (nb078AlphaDummy890) from (by
            unfold nb078AlphaDummy890;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0948) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0950 (h : Var) :
    (nb078AlphaDummy849 h) ∈
      (((Class.cv (nb078AlphaDummy850 h))).fv ∪ ((Class.cv (nb078AlphaDummy849 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0951 (h : Var) :
    (nb078AlphaDummy849 h) ∈
      (((synCcompl (Class.cab (nb078AlphaDummy891 h)
              (synWrex (nb078AlphaDummy892 h) (Class.cv (nb078AlphaDummy850 h))
                (Wff.classEq (Class.cv (nb078AlphaDummy891 h))
                  (synCphi (Class.cv (nb078AlphaDummy892 h)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy891 h)
              (synWrex (nb078AlphaDummy892 h) (Class.cv (nb078AlphaDummy849 h))
                (Wff.classEq (Class.cv (nb078AlphaDummy891 h))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy892 h)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy849 h) ≠ (nb078AlphaDummy891 h) from (by
          unfold nb078AlphaDummy891;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0950 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy849 h) ≠ (nb078AlphaDummy892 h) from (by
            unfold nb078AlphaDummy892;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0950 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0952 :
    (nb078AlphaDummy847) ∈
      (((Class.cab (nb078AlphaDummy889)
            (synWrex (nb078AlphaDummy890) (Class.cv (nb078AlphaDummy847))
              (Wff.classEq (Class.cv (nb078AlphaDummy889))
                (synCun (synCphi (Class.cv (nb078AlphaDummy890)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy889)
            (synWrex (nb078AlphaDummy890) (Class.cv (nb078AlphaDummy847))
              (Wff.classEq (Class.cv (nb078AlphaDummy889))
                (synCun (synCphi (Class.cv (nb078AlphaDummy890)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy847) ≠ (nb078AlphaDummy889) from (by
          unfold nb078AlphaDummy889;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0948) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy847) ≠ (nb078AlphaDummy890) from (by
            unfold nb078AlphaDummy890;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0948) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0953 (h : Var) :
    (nb078AlphaDummy849 h) ∈
      (((Class.cab (nb078AlphaDummy891 h)
            (synWrex (nb078AlphaDummy892 h) (Class.cv (nb078AlphaDummy849 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy891 h))
                (synCun (synCphi (Class.cv (nb078AlphaDummy892 h)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy891 h)
            (synWrex (nb078AlphaDummy892 h) (Class.cv (nb078AlphaDummy849 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy891 h))
                (synCun (synCphi (Class.cv (nb078AlphaDummy892 h)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy849 h) ≠ (nb078AlphaDummy891 h) from (by
          unfold nb078AlphaDummy891;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0950 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy849 h) ≠ (nb078AlphaDummy892 h) from (by
            unfold nb078AlphaDummy892;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0950 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0954 :
    (nb078AlphaDummy890) ∈
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy890))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0955 (h : Var) :
    (nb078AlphaDummy892 h) ∈
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy892 h))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0956 :
    (nb078AlphaDummy890) ∈
      (((synCphi (Class.cv (nb078AlphaDummy890)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy890)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0957 (h : Var) :
    (nb078AlphaDummy892 h) ∈
      (((synCphi (Class.cv (nb078AlphaDummy892 h)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy892 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0958 :
    (nb078AlphaDummy002) ∈
      (((synCnin (synCcom (Class.cv (nb078AlphaDummy002))
              (synCcnv (Class.cv (nb078AlphaDummy002)))) (synCid))).fv ∪ ((synCnin
            (synCcom (Class.cv (nb078AlphaDummy002))
              (synCcnv (Class.cv (nb078AlphaDummy002)))) (synCid))).fv) :=
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

theorem nb078_support_mem_0959 (h : Var) :
    h ∈
      (((synCnin (synCcom (Class.cv h) (synCcnv (Class.cv h))) (synCid))).fv ∪
        ((synCnin (synCcom (Class.cv h) (synCcnv (Class.cv h))) (synCid))).fv) :=
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

theorem nb078_support_mem_0960 :
    (nb078AlphaDummy002) ∈
      (((synCcom (Class.cv (nb078AlphaDummy002))
            (synCcnv (Class.cv (nb078AlphaDummy002))))).fv ∪ ((synCid)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccom]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0961 (h : Var) :
    h ∈ (((synCcom (Class.cv h) (synCcnv (Class.cv h)))).fv ∪ ((synCid)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccom]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0962 :
    (nb078AlphaDummy002) ∈
      (((Class.cv (nb078AlphaDummy002))).fv ∪
        ((synCcnv (Class.cv (nb078AlphaDummy002)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0963 :
    (nb078AlphaDummy002) ∈
      (({(nb078AlphaDummy767)} : Finset Var) ∪ ({(nb078AlphaDummy768)} : Finset Var) ∪
        ((synWex (nb078AlphaDummy769) (synWa (synWbr (Class.cv (nb078AlphaDummy767))
                (synCcnv (Class.cv (nb078AlphaDummy002)))
                (Class.cv (nb078AlphaDummy769))) (synWbr (Class.cv (nb078AlphaDummy769))
                (Class.cv (nb078AlphaDummy002)) (Class.cv (nb078AlphaDummy768)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_wex]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy002) ≠ (nb078AlphaDummy769) from (by
          unfold nb078AlphaDummy769;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0962) 2))))
  · rw [fv_syn_wa]
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_syn_wbr]
    with_reducible rw [Finset.mem_union]
    right
    rw [fv_syn_ccnv]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _

theorem nb078_support_mem_0964 (h : Var) :
    h ∈ (((Class.cv h)).fv ∪ ((synCcnv (Class.cv h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0965 (h : Var) :
    h ∈
      (({(nb078AlphaDummy770 h)} : Finset Var) ∪ ({(nb078AlphaDummy771 h)} : Finset Var) ∪
        ((synWex (nb078AlphaDummy772 h) (synWa
              (synWbr (Class.cv (nb078AlphaDummy770 h)) (synCcnv (Class.cv h))
                (Class.cv (nb078AlphaDummy772 h)))
              (synWbr (Class.cv (nb078AlphaDummy772 h)) (Class.cv h)
                (Class.cv (nb078AlphaDummy771 h)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_wex]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show h ≠ (nb078AlphaDummy772 h) from (by
          unfold nb078AlphaDummy772;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0964 h) 2))))
  · rw [fv_syn_wa]
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_syn_wbr]
    with_reducible rw [Finset.mem_union]
    right
    rw [fv_syn_ccnv]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _

theorem nb078_support_mem_0966 :
    (nb078AlphaDummy002) ∈
      (({(nb078AlphaDummy847)} : Finset Var) ∪ ({(nb078AlphaDummy848)} : Finset Var) ∪
        ((synWbr (Class.cv (nb078AlphaDummy848)) (Class.cv (nb078AlphaDummy002))
            (Class.cv (nb078AlphaDummy847)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_wbr]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0967 (h : Var) :
    h ∈
      (({(nb078AlphaDummy849 h)} : Finset Var) ∪ ({(nb078AlphaDummy850 h)} : Finset Var) ∪
        ((synWbr (Class.cv (nb078AlphaDummy850 h)) (Class.cv h)
            (Class.cv (nb078AlphaDummy849 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_wbr]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0968 :
    (nb078AlphaDummy002) ∈ (((Class.cv (nb078AlphaDummy002))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0969 (h : Var) : h ∈ (((Class.cv h)).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0970 :
    (nb078AlphaDummy769) ∈
      (((Class.cv (nb078AlphaDummy769))).fv ∪ ((Class.cv (nb078AlphaDummy768))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0971 :
    (nb078AlphaDummy769) ∈
      (((synCcompl (Class.cab (nb078AlphaDummy925)
              (synWrex (nb078AlphaDummy926) (Class.cv (nb078AlphaDummy769))
                (Wff.classEq (Class.cv (nb078AlphaDummy925))
                  (synCphi (Class.cv (nb078AlphaDummy926)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy925)
              (synWrex (nb078AlphaDummy926) (Class.cv (nb078AlphaDummy768))
                (Wff.classEq (Class.cv (nb078AlphaDummy925))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy926)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy769) ≠ (nb078AlphaDummy925) from (by
          unfold nb078AlphaDummy925;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0970) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy769) ≠ (nb078AlphaDummy926) from (by
            unfold nb078AlphaDummy926;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0970) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0972 (h : Var) :
    (nb078AlphaDummy772 h) ∈
      (((Class.cv (nb078AlphaDummy772 h))).fv ∪ ((Class.cv (nb078AlphaDummy771 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0973 (h : Var) :
    (nb078AlphaDummy772 h) ∈
      (((synCcompl (Class.cab (nb078AlphaDummy927 h)
              (synWrex (nb078AlphaDummy928 h) (Class.cv (nb078AlphaDummy772 h))
                (Wff.classEq (Class.cv (nb078AlphaDummy927 h))
                  (synCphi (Class.cv (nb078AlphaDummy928 h)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy927 h)
              (synWrex (nb078AlphaDummy928 h) (Class.cv (nb078AlphaDummy771 h))
                (Wff.classEq (Class.cv (nb078AlphaDummy927 h))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy928 h)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy772 h) ≠ (nb078AlphaDummy927 h) from (by
          unfold nb078AlphaDummy927;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0972 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy772 h) ≠ (nb078AlphaDummy928 h) from (by
            unfold nb078AlphaDummy928;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0972 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0974 :
    (nb078AlphaDummy769) ∈
      (((Class.cab (nb078AlphaDummy925)
            (synWrex (nb078AlphaDummy926) (Class.cv (nb078AlphaDummy769))
              (Wff.classEq (Class.cv (nb078AlphaDummy925))
                (synCphi (Class.cv (nb078AlphaDummy926))))))).fv ∪
        ((Class.cab (nb078AlphaDummy925)
            (synWrex (nb078AlphaDummy926) (Class.cv (nb078AlphaDummy769))
              (Wff.classEq (Class.cv (nb078AlphaDummy925))
                (synCphi (Class.cv (nb078AlphaDummy926))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy769) ≠ (nb078AlphaDummy925) from (by
          unfold nb078AlphaDummy925;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0970) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy769) ≠ (nb078AlphaDummy926) from (by
            unfold nb078AlphaDummy926;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0970) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0975 (h : Var) :
    (nb078AlphaDummy772 h) ∈
      (((Class.cab (nb078AlphaDummy927 h)
            (synWrex (nb078AlphaDummy928 h) (Class.cv (nb078AlphaDummy772 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy927 h))
                (synCphi (Class.cv (nb078AlphaDummy928 h))))))).fv ∪
        ((Class.cab (nb078AlphaDummy927 h)
            (synWrex (nb078AlphaDummy928 h) (Class.cv (nb078AlphaDummy772 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy927 h))
                (synCphi (Class.cv (nb078AlphaDummy928 h))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy772 h) ≠ (nb078AlphaDummy927 h) from (by
          unfold nb078AlphaDummy927;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0972 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy772 h) ≠ (nb078AlphaDummy928 h) from (by
            unfold nb078AlphaDummy928;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0972 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0976 :
    (nb078AlphaDummy926) ∈ (((Class.cv (nb078AlphaDummy926))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0977 (h : Var) :
    (nb078AlphaDummy928 h) ∈ (((Class.cv (nb078AlphaDummy928 h))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0978 :
    (nb078AlphaDummy933) ∈
      (((Wff.classMem (Class.cv (nb078AlphaDummy933)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy933)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy933))).fv) :=
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

theorem nb078_support_mem_0979 (h : Var) :
    (nb078AlphaDummy935 h) ∈
      (((Wff.classMem (Class.cv (nb078AlphaDummy935 h)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy935 h)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy935 h))).fv) :=
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

theorem nb078_support_mem_0980 :
    (nb078AlphaDummy933) ∈
      (((Class.cv (nb078AlphaDummy933))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0981 (h : Var) :
    (nb078AlphaDummy935 h) ∈
      (((Class.cv (nb078AlphaDummy935 h))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0982 :
    (nb078AlphaDummy940) ∈
      (((synCnin (Class.cv (nb078AlphaDummy940)) (Class.cv (nb078AlphaDummy941)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy940))
            (Class.cv (nb078AlphaDummy941)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0983 (h : Var) :
    (nb078AlphaDummy943 h) ∈
      (((synCnin (Class.cv (nb078AlphaDummy943 h))
            (Class.cv (nb078AlphaDummy944 h)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy943 h))
            (Class.cv (nb078AlphaDummy944 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0984 :
    (nb078AlphaDummy940) ∈
      (((Class.cv (nb078AlphaDummy940))).fv ∪ ((Class.cv (nb078AlphaDummy941))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0985 (h : Var) :
    (nb078AlphaDummy943 h) ∈
      (((Class.cv (nb078AlphaDummy943 h))).fv ∪ ((Class.cv (nb078AlphaDummy944 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0986 :
    (nb078AlphaDummy941) ∈
      (((synCnin (Class.cv (nb078AlphaDummy940)) (Class.cv (nb078AlphaDummy941)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy940))
            (Class.cv (nb078AlphaDummy941)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0987 (h : Var) :
    (nb078AlphaDummy944 h) ∈
      (((synCnin (Class.cv (nb078AlphaDummy943 h))
            (Class.cv (nb078AlphaDummy944 h)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy943 h))
            (Class.cv (nb078AlphaDummy944 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0988 :
    (nb078AlphaDummy941) ∈
      (((Class.cv (nb078AlphaDummy940))).fv ∪ ((Class.cv (nb078AlphaDummy941))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0989 (h : Var) :
    (nb078AlphaDummy944 h) ∈
      (((Class.cv (nb078AlphaDummy943 h))).fv ∪ ((Class.cv (nb078AlphaDummy944 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0990 :
    (nb078AlphaDummy940) ∈
      (((synCcompl (Class.cv (nb078AlphaDummy940)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy941)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0991 (h : Var) :
    (nb078AlphaDummy943 h) ∈
      (((synCcompl (Class.cv (nb078AlphaDummy943 h)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy944 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0992 :
    (nb078AlphaDummy940) ∈
      (((Class.cv (nb078AlphaDummy940))).fv ∪ ((Class.cv (nb078AlphaDummy940))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0993 (h : Var) :
    (nb078AlphaDummy943 h) ∈
      (((Class.cv (nb078AlphaDummy943 h))).fv ∪ ((Class.cv (nb078AlphaDummy943 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0994 :
    (nb078AlphaDummy941) ∈
      (((synCcompl (Class.cv (nb078AlphaDummy940)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy941)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0995 (h : Var) :
    (nb078AlphaDummy944 h) ∈
      (((synCcompl (Class.cv (nb078AlphaDummy943 h)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy944 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0996 :
    (nb078AlphaDummy941) ∈
      (((Class.cv (nb078AlphaDummy941))).fv ∪ ((Class.cv (nb078AlphaDummy941))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0997 (h : Var) :
    (nb078AlphaDummy944 h) ∈
      (((Class.cv (nb078AlphaDummy944 h))).fv ∪ ((Class.cv (nb078AlphaDummy944 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0998 :
    (nb078AlphaDummy768) ∈
      (((Class.cv (nb078AlphaDummy769))).fv ∪ ((Class.cv (nb078AlphaDummy768))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0999 :
    (nb078AlphaDummy768) ∈
      (((synCcompl (Class.cab (nb078AlphaDummy925)
              (synWrex (nb078AlphaDummy926) (Class.cv (nb078AlphaDummy769))
                (Wff.classEq (Class.cv (nb078AlphaDummy925))
                  (synCphi (Class.cv (nb078AlphaDummy926)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy925)
              (synWrex (nb078AlphaDummy926) (Class.cv (nb078AlphaDummy768))
                (Wff.classEq (Class.cv (nb078AlphaDummy925))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy926)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy768) ≠ (nb078AlphaDummy925) from (by
          unfold nb078AlphaDummy925;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0998) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy768) ≠ (nb078AlphaDummy926) from (by
            unfold nb078AlphaDummy926;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0998) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_1000 (h : Var) :
    (nb078AlphaDummy771 h) ∈
      (((Class.cv (nb078AlphaDummy772 h))).fv ∪ ((Class.cv (nb078AlphaDummy771 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1001 (h : Var) :
    (nb078AlphaDummy771 h) ∈
      (((synCcompl (Class.cab (nb078AlphaDummy927 h)
              (synWrex (nb078AlphaDummy928 h) (Class.cv (nb078AlphaDummy772 h))
                (Wff.classEq (Class.cv (nb078AlphaDummy927 h))
                  (synCphi (Class.cv (nb078AlphaDummy928 h)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy927 h)
              (synWrex (nb078AlphaDummy928 h) (Class.cv (nb078AlphaDummy771 h))
                (Wff.classEq (Class.cv (nb078AlphaDummy927 h))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy928 h)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy771 h) ≠ (nb078AlphaDummy927 h) from (by
          unfold nb078AlphaDummy927;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1000 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy771 h) ≠ (nb078AlphaDummy928 h) from (by
            unfold nb078AlphaDummy928;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1000 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_1002 :
    (nb078AlphaDummy768) ∈
      (((Class.cab (nb078AlphaDummy925)
            (synWrex (nb078AlphaDummy926) (Class.cv (nb078AlphaDummy768))
              (Wff.classEq (Class.cv (nb078AlphaDummy925))
                (synCun (synCphi (Class.cv (nb078AlphaDummy926)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy925)
            (synWrex (nb078AlphaDummy926) (Class.cv (nb078AlphaDummy768))
              (Wff.classEq (Class.cv (nb078AlphaDummy925))
                (synCun (synCphi (Class.cv (nb078AlphaDummy926)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy768) ≠ (nb078AlphaDummy925) from (by
          unfold nb078AlphaDummy925;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0998) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy768) ≠ (nb078AlphaDummy926) from (by
            unfold nb078AlphaDummy926;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0998) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_1003 (h : Var) :
    (nb078AlphaDummy771 h) ∈
      (((Class.cab (nb078AlphaDummy927 h)
            (synWrex (nb078AlphaDummy928 h) (Class.cv (nb078AlphaDummy771 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy927 h))
                (synCun (synCphi (Class.cv (nb078AlphaDummy928 h)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy927 h)
            (synWrex (nb078AlphaDummy928 h) (Class.cv (nb078AlphaDummy771 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy927 h))
                (synCun (synCphi (Class.cv (nb078AlphaDummy928 h)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy771 h) ≠ (nb078AlphaDummy927 h) from (by
          unfold nb078AlphaDummy927;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1000 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy771 h) ≠ (nb078AlphaDummy928 h) from (by
            unfold nb078AlphaDummy928;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1000 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_1004 :
    (nb078AlphaDummy926) ∈
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy926))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1005 (h : Var) :
    (nb078AlphaDummy928 h) ∈
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy928 h))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1006 :
    (nb078AlphaDummy926) ∈
      (((synCphi (Class.cv (nb078AlphaDummy926)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy926)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1007 (h : Var) :
    (nb078AlphaDummy928 h) ∈
      (((synCphi (Class.cv (nb078AlphaDummy928 h)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy928 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1008 :
    (nb078AlphaDummy962) ∈
      (((Class.cv (nb078AlphaDummy962))).fv ∪ ((Class.cv (nb078AlphaDummy961))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1009 :
    (nb078AlphaDummy962) ∈
      (((synCcompl (Class.cab (nb078AlphaDummy965)
              (synWrex (nb078AlphaDummy966) (Class.cv (nb078AlphaDummy962))
                (Wff.classEq (Class.cv (nb078AlphaDummy965))
                  (synCphi (Class.cv (nb078AlphaDummy966)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy965)
              (synWrex (nb078AlphaDummy966) (Class.cv (nb078AlphaDummy961))
                (Wff.classEq (Class.cv (nb078AlphaDummy965))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy966)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy962) ≠ (nb078AlphaDummy965) from (by
          unfold nb078AlphaDummy965;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1008) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy962) ≠ (nb078AlphaDummy966) from (by
            unfold nb078AlphaDummy966;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1008) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_1010 (h : Var) :
    (nb078AlphaDummy964 h) ∈
      (((Class.cv (nb078AlphaDummy964 h))).fv ∪ ((Class.cv (nb078AlphaDummy963 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1011 (h : Var) :
    (nb078AlphaDummy964 h) ∈
      (((synCcompl (Class.cab (nb078AlphaDummy967 h)
              (synWrex (nb078AlphaDummy968 h) (Class.cv (nb078AlphaDummy964 h))
                (Wff.classEq (Class.cv (nb078AlphaDummy967 h))
                  (synCphi (Class.cv (nb078AlphaDummy968 h)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy967 h)
              (synWrex (nb078AlphaDummy968 h) (Class.cv (nb078AlphaDummy963 h))
                (Wff.classEq (Class.cv (nb078AlphaDummy967 h))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy968 h)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy964 h) ≠ (nb078AlphaDummy967 h) from (by
          unfold nb078AlphaDummy967;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1010 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy964 h) ≠ (nb078AlphaDummy968 h) from (by
            unfold nb078AlphaDummy968;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1010 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_1012 :
    (nb078AlphaDummy962) ∈
      (((Class.cab (nb078AlphaDummy965)
            (synWrex (nb078AlphaDummy966) (Class.cv (nb078AlphaDummy962))
              (Wff.classEq (Class.cv (nb078AlphaDummy965))
                (synCphi (Class.cv (nb078AlphaDummy966))))))).fv ∪
        ((Class.cab (nb078AlphaDummy965)
            (synWrex (nb078AlphaDummy966) (Class.cv (nb078AlphaDummy962))
              (Wff.classEq (Class.cv (nb078AlphaDummy965))
                (synCphi (Class.cv (nb078AlphaDummy966))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy962) ≠ (nb078AlphaDummy965) from (by
          unfold nb078AlphaDummy965;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1008) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy962) ≠ (nb078AlphaDummy966) from (by
            unfold nb078AlphaDummy966;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1008) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_1013 (h : Var) :
    (nb078AlphaDummy964 h) ∈
      (((Class.cab (nb078AlphaDummy967 h)
            (synWrex (nb078AlphaDummy968 h) (Class.cv (nb078AlphaDummy964 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy967 h))
                (synCphi (Class.cv (nb078AlphaDummy968 h))))))).fv ∪
        ((Class.cab (nb078AlphaDummy967 h)
            (synWrex (nb078AlphaDummy968 h) (Class.cv (nb078AlphaDummy964 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy967 h))
                (synCphi (Class.cv (nb078AlphaDummy968 h))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy964 h) ≠ (nb078AlphaDummy967 h) from (by
          unfold nb078AlphaDummy967;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1010 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy964 h) ≠ (nb078AlphaDummy968 h) from (by
            unfold nb078AlphaDummy968;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1010 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_1014 :
    (nb078AlphaDummy966) ∈ (((Class.cv (nb078AlphaDummy966))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1015 (h : Var) :
    (nb078AlphaDummy968 h) ∈ (((Class.cv (nb078AlphaDummy968 h))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1016 :
    (nb078AlphaDummy973) ∈
      (((Wff.classMem (Class.cv (nb078AlphaDummy973)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy973)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy973))).fv) :=
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

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C078C001Part029`. -/


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

theorem nb078_support_mem_1017 (h : Var) :
    (nb078AlphaDummy975 h) ∈
      (((Wff.classMem (Class.cv (nb078AlphaDummy975 h)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy975 h)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy975 h))).fv) :=
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

theorem nb078_support_mem_1018 :
    (nb078AlphaDummy973) ∈
      (((Class.cv (nb078AlphaDummy973))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1019 (h : Var) :
    (nb078AlphaDummy975 h) ∈
      (((Class.cv (nb078AlphaDummy975 h))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1020 :
    (nb078AlphaDummy980) ∈
      (((synCnin (Class.cv (nb078AlphaDummy980)) (Class.cv (nb078AlphaDummy981)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy980))
            (Class.cv (nb078AlphaDummy981)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1021 (h : Var) :
    (nb078AlphaDummy983 h) ∈
      (((synCnin (Class.cv (nb078AlphaDummy983 h))
            (Class.cv (nb078AlphaDummy984 h)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy983 h))
            (Class.cv (nb078AlphaDummy984 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1022 :
    (nb078AlphaDummy980) ∈
      (((Class.cv (nb078AlphaDummy980))).fv ∪ ((Class.cv (nb078AlphaDummy981))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1023 (h : Var) :
    (nb078AlphaDummy983 h) ∈
      (((Class.cv (nb078AlphaDummy983 h))).fv ∪ ((Class.cv (nb078AlphaDummy984 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1024 :
    (nb078AlphaDummy981) ∈
      (((synCnin (Class.cv (nb078AlphaDummy980)) (Class.cv (nb078AlphaDummy981)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy980))
            (Class.cv (nb078AlphaDummy981)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1025 (h : Var) :
    (nb078AlphaDummy984 h) ∈
      (((synCnin (Class.cv (nb078AlphaDummy983 h))
            (Class.cv (nb078AlphaDummy984 h)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy983 h))
            (Class.cv (nb078AlphaDummy984 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1026 :
    (nb078AlphaDummy981) ∈
      (((Class.cv (nb078AlphaDummy980))).fv ∪ ((Class.cv (nb078AlphaDummy981))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1027 (h : Var) :
    (nb078AlphaDummy984 h) ∈
      (((Class.cv (nb078AlphaDummy983 h))).fv ∪ ((Class.cv (nb078AlphaDummy984 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1028 :
    (nb078AlphaDummy980) ∈
      (((synCcompl (Class.cv (nb078AlphaDummy980)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy981)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1029 (h : Var) :
    (nb078AlphaDummy983 h) ∈
      (((synCcompl (Class.cv (nb078AlphaDummy983 h)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy984 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1030 :
    (nb078AlphaDummy980) ∈
      (((Class.cv (nb078AlphaDummy980))).fv ∪ ((Class.cv (nb078AlphaDummy980))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1031 (h : Var) :
    (nb078AlphaDummy983 h) ∈
      (((Class.cv (nb078AlphaDummy983 h))).fv ∪ ((Class.cv (nb078AlphaDummy983 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1032 :
    (nb078AlphaDummy981) ∈
      (((synCcompl (Class.cv (nb078AlphaDummy980)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy981)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1033 (h : Var) :
    (nb078AlphaDummy984 h) ∈
      (((synCcompl (Class.cv (nb078AlphaDummy983 h)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy984 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1034 :
    (nb078AlphaDummy981) ∈
      (((Class.cv (nb078AlphaDummy981))).fv ∪ ((Class.cv (nb078AlphaDummy981))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1035 (h : Var) :
    (nb078AlphaDummy984 h) ∈
      (((Class.cv (nb078AlphaDummy984 h))).fv ∪ ((Class.cv (nb078AlphaDummy984 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1036 :
    (nb078AlphaDummy961) ∈
      (((Class.cv (nb078AlphaDummy962))).fv ∪ ((Class.cv (nb078AlphaDummy961))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1037 :
    (nb078AlphaDummy961) ∈
      (((synCcompl (Class.cab (nb078AlphaDummy965)
              (synWrex (nb078AlphaDummy966) (Class.cv (nb078AlphaDummy962))
                (Wff.classEq (Class.cv (nb078AlphaDummy965))
                  (synCphi (Class.cv (nb078AlphaDummy966)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy965)
              (synWrex (nb078AlphaDummy966) (Class.cv (nb078AlphaDummy961))
                (Wff.classEq (Class.cv (nb078AlphaDummy965))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy966)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy961) ≠ (nb078AlphaDummy965) from (by
          unfold nb078AlphaDummy965;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1036) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy961) ≠ (nb078AlphaDummy966) from (by
            unfold nb078AlphaDummy966;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1036) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_1038 (h : Var) :
    (nb078AlphaDummy963 h) ∈
      (((Class.cv (nb078AlphaDummy964 h))).fv ∪ ((Class.cv (nb078AlphaDummy963 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1039 (h : Var) :
    (nb078AlphaDummy963 h) ∈
      (((synCcompl (Class.cab (nb078AlphaDummy967 h)
              (synWrex (nb078AlphaDummy968 h) (Class.cv (nb078AlphaDummy964 h))
                (Wff.classEq (Class.cv (nb078AlphaDummy967 h))
                  (synCphi (Class.cv (nb078AlphaDummy968 h)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy967 h)
              (synWrex (nb078AlphaDummy968 h) (Class.cv (nb078AlphaDummy963 h))
                (Wff.classEq (Class.cv (nb078AlphaDummy967 h))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy968 h)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy963 h) ≠ (nb078AlphaDummy967 h) from (by
          unfold nb078AlphaDummy967;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1038 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy963 h) ≠ (nb078AlphaDummy968 h) from (by
            unfold nb078AlphaDummy968;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1038 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_1040 :
    (nb078AlphaDummy961) ∈
      (((Class.cab (nb078AlphaDummy965)
            (synWrex (nb078AlphaDummy966) (Class.cv (nb078AlphaDummy961))
              (Wff.classEq (Class.cv (nb078AlphaDummy965))
                (synCun (synCphi (Class.cv (nb078AlphaDummy966)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy965)
            (synWrex (nb078AlphaDummy966) (Class.cv (nb078AlphaDummy961))
              (Wff.classEq (Class.cv (nb078AlphaDummy965))
                (synCun (synCphi (Class.cv (nb078AlphaDummy966)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy961) ≠ (nb078AlphaDummy965) from (by
          unfold nb078AlphaDummy965;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1036) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy961) ≠ (nb078AlphaDummy966) from (by
            unfold nb078AlphaDummy966;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1036) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_1041 (h : Var) :
    (nb078AlphaDummy963 h) ∈
      (((Class.cab (nb078AlphaDummy967 h)
            (synWrex (nb078AlphaDummy968 h) (Class.cv (nb078AlphaDummy963 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy967 h))
                (synCun (synCphi (Class.cv (nb078AlphaDummy968 h)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy967 h)
            (synWrex (nb078AlphaDummy968 h) (Class.cv (nb078AlphaDummy963 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy967 h))
                (synCun (synCphi (Class.cv (nb078AlphaDummy968 h)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy963 h) ≠ (nb078AlphaDummy967 h) from (by
          unfold nb078AlphaDummy967;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1038 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy963 h) ≠ (nb078AlphaDummy968 h) from (by
            unfold nb078AlphaDummy968;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1038 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_1042 :
    (nb078AlphaDummy966) ∈
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy966))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1043 (h : Var) :
    (nb078AlphaDummy968 h) ∈
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy968 h))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1044 :
    (nb078AlphaDummy966) ∈
      (((synCphi (Class.cv (nb078AlphaDummy966)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy966)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1045 (h : Var) :
    (nb078AlphaDummy968 h) ∈
      (((synCphi (Class.cv (nb078AlphaDummy968 h)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy968 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1046 :
    (nb078AlphaDummy002) ∈
      (((synCcnv (Class.cv (nb078AlphaDummy002)))).fv ∪ ((synCvv)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccnv]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1047 (h : Var) :
    h ∈ (((synCcnv (Class.cv h))).fv ∪ ((synCvv)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccnv]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1048 :
    (nb078AlphaDummy1006) ∈
      (((Class.cv (nb078AlphaDummy1006))).fv ∪ ((Class.cv (nb078AlphaDummy1005))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1049 :
    (nb078AlphaDummy1006) ∈
      (((synCcompl (Class.cab (nb078AlphaDummy1009)
              (synWrex (nb078AlphaDummy1010) (Class.cv (nb078AlphaDummy1006))
                (Wff.classEq (Class.cv (nb078AlphaDummy1009))
                  (synCphi (Class.cv (nb078AlphaDummy1010)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy1009)
              (synWrex (nb078AlphaDummy1010) (Class.cv (nb078AlphaDummy1005))
                (Wff.classEq (Class.cv (nb078AlphaDummy1009))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy1010)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy1006) ≠ (nb078AlphaDummy1009) from (by
          unfold nb078AlphaDummy1009;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1048) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy1006) ≠ (nb078AlphaDummy1010) from (by
            unfold nb078AlphaDummy1010;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1048) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_1050 (h : Var) :
    (nb078AlphaDummy1008 h) ∈
      (((Class.cv (nb078AlphaDummy1008 h))).fv ∪
        ((Class.cv (nb078AlphaDummy1007 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1051 (h : Var) :
    (nb078AlphaDummy1008 h) ∈
      (((synCcompl (Class.cab (nb078AlphaDummy1011 h)
              (synWrex (nb078AlphaDummy1012 h) (Class.cv (nb078AlphaDummy1008 h))
                (Wff.classEq (Class.cv (nb078AlphaDummy1011 h))
                  (synCphi (Class.cv (nb078AlphaDummy1012 h)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy1011 h)
              (synWrex (nb078AlphaDummy1012 h) (Class.cv (nb078AlphaDummy1007 h))
                (Wff.classEq (Class.cv (nb078AlphaDummy1011 h))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy1012 h)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy1008 h) ≠ (nb078AlphaDummy1011 h) from (by
          unfold nb078AlphaDummy1011;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1050 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy1008 h) ≠ (nb078AlphaDummy1012 h) from (by
            unfold nb078AlphaDummy1012;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1050 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_1052 :
    (nb078AlphaDummy1006) ∈
      (((Class.cab (nb078AlphaDummy1009)
            (synWrex (nb078AlphaDummy1010) (Class.cv (nb078AlphaDummy1006))
              (Wff.classEq (Class.cv (nb078AlphaDummy1009))
                (synCphi (Class.cv (nb078AlphaDummy1010))))))).fv ∪
        ((Class.cab (nb078AlphaDummy1009)
            (synWrex (nb078AlphaDummy1010) (Class.cv (nb078AlphaDummy1006))
              (Wff.classEq (Class.cv (nb078AlphaDummy1009))
                (synCphi (Class.cv (nb078AlphaDummy1010))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy1006) ≠ (nb078AlphaDummy1009) from (by
          unfold nb078AlphaDummy1009;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1048) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy1006) ≠ (nb078AlphaDummy1010) from (by
            unfold nb078AlphaDummy1010;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1048) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_1053 (h : Var) :
    (nb078AlphaDummy1008 h) ∈
      (((Class.cab (nb078AlphaDummy1011 h)
            (synWrex (nb078AlphaDummy1012 h) (Class.cv (nb078AlphaDummy1008 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy1011 h))
                (synCphi (Class.cv (nb078AlphaDummy1012 h))))))).fv ∪
        ((Class.cab (nb078AlphaDummy1011 h)
            (synWrex (nb078AlphaDummy1012 h) (Class.cv (nb078AlphaDummy1008 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy1011 h))
                (synCphi (Class.cv (nb078AlphaDummy1012 h))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy1008 h) ≠ (nb078AlphaDummy1011 h) from (by
          unfold nb078AlphaDummy1011;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1050 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy1008 h) ≠ (nb078AlphaDummy1012 h) from (by
            unfold nb078AlphaDummy1012;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1050 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_1054 :
    (nb078AlphaDummy1010) ∈ (((Class.cv (nb078AlphaDummy1010))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1055 (h : Var) :
    (nb078AlphaDummy1012 h) ∈ (((Class.cv (nb078AlphaDummy1012 h))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1056 :
    (nb078AlphaDummy1017) ∈
      (((Wff.classMem (Class.cv (nb078AlphaDummy1017)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy1017)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy1017))).fv) :=
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

theorem nb078_support_mem_1057 (h : Var) :
    (nb078AlphaDummy1019 h) ∈
      (((Wff.classMem (Class.cv (nb078AlphaDummy1019 h)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy1019 h)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy1019 h))).fv) :=
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

theorem nb078_support_mem_1058 :
    (nb078AlphaDummy1017) ∈
      (((Class.cv (nb078AlphaDummy1017))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1059 (h : Var) :
    (nb078AlphaDummy1019 h) ∈
      (((Class.cv (nb078AlphaDummy1019 h))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1060 :
    (nb078AlphaDummy1024) ∈
      (((synCnin (Class.cv (nb078AlphaDummy1024)) (Class.cv (nb078AlphaDummy1025)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy1024))
            (Class.cv (nb078AlphaDummy1025)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1061 (h : Var) :
    (nb078AlphaDummy1027 h) ∈
      (((synCnin (Class.cv (nb078AlphaDummy1027 h))
            (Class.cv (nb078AlphaDummy1028 h)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy1027 h))
            (Class.cv (nb078AlphaDummy1028 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1062 :
    (nb078AlphaDummy1024) ∈
      (((Class.cv (nb078AlphaDummy1024))).fv ∪ ((Class.cv (nb078AlphaDummy1025))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1063 (h : Var) :
    (nb078AlphaDummy1027 h) ∈
      (((Class.cv (nb078AlphaDummy1027 h))).fv ∪
        ((Class.cv (nb078AlphaDummy1028 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1064 :
    (nb078AlphaDummy1025) ∈
      (((synCnin (Class.cv (nb078AlphaDummy1024)) (Class.cv (nb078AlphaDummy1025)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy1024))
            (Class.cv (nb078AlphaDummy1025)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1065 (h : Var) :
    (nb078AlphaDummy1028 h) ∈
      (((synCnin (Class.cv (nb078AlphaDummy1027 h))
            (Class.cv (nb078AlphaDummy1028 h)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy1027 h))
            (Class.cv (nb078AlphaDummy1028 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1066 :
    (nb078AlphaDummy1025) ∈
      (((Class.cv (nb078AlphaDummy1024))).fv ∪ ((Class.cv (nb078AlphaDummy1025))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1067 (h : Var) :
    (nb078AlphaDummy1028 h) ∈
      (((Class.cv (nb078AlphaDummy1027 h))).fv ∪
        ((Class.cv (nb078AlphaDummy1028 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1068 :
    (nb078AlphaDummy1024) ∈
      (((synCcompl (Class.cv (nb078AlphaDummy1024)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy1025)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1069 (h : Var) :
    (nb078AlphaDummy1027 h) ∈
      (((synCcompl (Class.cv (nb078AlphaDummy1027 h)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy1028 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1070 :
    (nb078AlphaDummy1024) ∈
      (((Class.cv (nb078AlphaDummy1024))).fv ∪ ((Class.cv (nb078AlphaDummy1024))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1071 (h : Var) :
    (nb078AlphaDummy1027 h) ∈
      (((Class.cv (nb078AlphaDummy1027 h))).fv ∪
        ((Class.cv (nb078AlphaDummy1027 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1072 :
    (nb078AlphaDummy1025) ∈
      (((synCcompl (Class.cv (nb078AlphaDummy1024)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy1025)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1073 (h : Var) :
    (nb078AlphaDummy1028 h) ∈
      (((synCcompl (Class.cv (nb078AlphaDummy1027 h)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy1028 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1074 :
    (nb078AlphaDummy1025) ∈
      (((Class.cv (nb078AlphaDummy1025))).fv ∪ ((Class.cv (nb078AlphaDummy1025))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1075 (h : Var) :
    (nb078AlphaDummy1028 h) ∈
      (((Class.cv (nb078AlphaDummy1028 h))).fv ∪
        ((Class.cv (nb078AlphaDummy1028 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1076 :
    (nb078AlphaDummy1005) ∈
      (((Class.cv (nb078AlphaDummy1006))).fv ∪ ((Class.cv (nb078AlphaDummy1005))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1077 :
    (nb078AlphaDummy1005) ∈
      (((synCcompl (Class.cab (nb078AlphaDummy1009)
              (synWrex (nb078AlphaDummy1010) (Class.cv (nb078AlphaDummy1006))
                (Wff.classEq (Class.cv (nb078AlphaDummy1009))
                  (synCphi (Class.cv (nb078AlphaDummy1010)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy1009)
              (synWrex (nb078AlphaDummy1010) (Class.cv (nb078AlphaDummy1005))
                (Wff.classEq (Class.cv (nb078AlphaDummy1009))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy1010)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy1005) ≠ (nb078AlphaDummy1009) from (by
          unfold nb078AlphaDummy1009;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1076) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy1005) ≠ (nb078AlphaDummy1010) from (by
            unfold nb078AlphaDummy1010;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1076) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_1078 (h : Var) :
    (nb078AlphaDummy1007 h) ∈
      (((Class.cv (nb078AlphaDummy1008 h))).fv ∪
        ((Class.cv (nb078AlphaDummy1007 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1079 (h : Var) :
    (nb078AlphaDummy1007 h) ∈
      (((synCcompl (Class.cab (nb078AlphaDummy1011 h)
              (synWrex (nb078AlphaDummy1012 h) (Class.cv (nb078AlphaDummy1008 h))
                (Wff.classEq (Class.cv (nb078AlphaDummy1011 h))
                  (synCphi (Class.cv (nb078AlphaDummy1012 h)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy1011 h)
              (synWrex (nb078AlphaDummy1012 h) (Class.cv (nb078AlphaDummy1007 h))
                (Wff.classEq (Class.cv (nb078AlphaDummy1011 h))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy1012 h)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy1007 h) ≠ (nb078AlphaDummy1011 h) from (by
          unfold nb078AlphaDummy1011;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1078 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy1007 h) ≠ (nb078AlphaDummy1012 h) from (by
            unfold nb078AlphaDummy1012;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1078 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_1080 :
    (nb078AlphaDummy1005) ∈
      (((Class.cab (nb078AlphaDummy1009)
            (synWrex (nb078AlphaDummy1010) (Class.cv (nb078AlphaDummy1005))
              (Wff.classEq (Class.cv (nb078AlphaDummy1009))
                (synCun (synCphi (Class.cv (nb078AlphaDummy1010)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy1009)
            (synWrex (nb078AlphaDummy1010) (Class.cv (nb078AlphaDummy1005))
              (Wff.classEq (Class.cv (nb078AlphaDummy1009))
                (synCun (synCphi (Class.cv (nb078AlphaDummy1010)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy1005) ≠ (nb078AlphaDummy1009) from (by
          unfold nb078AlphaDummy1009;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1076) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy1005) ≠ (nb078AlphaDummy1010) from (by
            unfold nb078AlphaDummy1010;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1076) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_1081 (h : Var) :
    (nb078AlphaDummy1007 h) ∈
      (((Class.cab (nb078AlphaDummy1011 h)
            (synWrex (nb078AlphaDummy1012 h) (Class.cv (nb078AlphaDummy1007 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy1011 h))
                (synCun (synCphi (Class.cv (nb078AlphaDummy1012 h)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy1011 h)
            (synWrex (nb078AlphaDummy1012 h) (Class.cv (nb078AlphaDummy1007 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy1011 h))
                (synCun (synCphi (Class.cv (nb078AlphaDummy1012 h)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy1007 h) ≠ (nb078AlphaDummy1011 h) from (by
          unfold nb078AlphaDummy1011;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1078 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy1007 h) ≠ (nb078AlphaDummy1012 h) from (by
            unfold nb078AlphaDummy1012;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1078 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_1082 :
    (nb078AlphaDummy1010) ∈
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy1010))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1083 (h : Var) :
    (nb078AlphaDummy1012 h) ∈
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy1012 h))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1084 :
    (nb078AlphaDummy1010) ∈
      (((synCphi (Class.cv (nb078AlphaDummy1010)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy1010)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1085 (h : Var) :
    (nb078AlphaDummy1012 h) ∈
      (((synCphi (Class.cv (nb078AlphaDummy1012 h)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy1012 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1086 :
    (nb078AlphaDummy002) ∈
      (((synCnin (synCrn (Class.cv (nb078AlphaDummy002)))
            (Class.cv (nb078AlphaDummy004)))).fv ∪
        ((synCnin (synCrn (Class.cv (nb078AlphaDummy002)))
            (Class.cv (nb078AlphaDummy004)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_crn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1087 (y : Var) (h : Var) :
    h ∈
      (((synCnin (synCrn (Class.cv h)) (Class.cv y))).fv ∪
        ((synCnin (synCrn (Class.cv h)) (Class.cv y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_crn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1088 :
    (nb078AlphaDummy002) ∈
      (((synCrn (Class.cv (nb078AlphaDummy002)))).fv ∪
        ((Class.cv (nb078AlphaDummy004))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_crn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1089 (y : Var) (h : Var) :
    h ∈ (((synCrn (Class.cv h))).fv ∪ ((Class.cv y)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_crn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1090 :
    (nb078AlphaDummy002) ∈
      (((Class.cv (nb078AlphaDummy002))).fv ∪ ((synCvv)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1091 (h : Var) : h ∈ (((Class.cv h)).fv ∪ ((synCvv)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1092 :
    (nb078AlphaDummy004) ∈
      (((synCnin (synCrn (Class.cv (nb078AlphaDummy002)))
            (Class.cv (nb078AlphaDummy004)))).fv ∪
        ((synCnin (synCrn (Class.cv (nb078AlphaDummy002)))
            (Class.cv (nb078AlphaDummy004)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1093 (y : Var) (h : Var) :
    y ∈
      (((synCnin (synCrn (Class.cv h)) (Class.cv y))).fv ∪
        ((synCnin (synCrn (Class.cv h)) (Class.cv y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1094 :
    (nb078AlphaDummy004) ∈
      (((synCrn (Class.cv (nb078AlphaDummy002)))).fv ∪
        ((Class.cv (nb078AlphaDummy004))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1095 (y : Var) (h : Var) :
    y ∈ (((synCrn (Class.cv h))).fv ∪ ((Class.cv y)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1096 :
    (nb078AlphaDummy1049) ∈
      (({(nb078AlphaDummy1049)} : Finset Var) ∪ ({(nb078AlphaDummy1050)} : Finset Var) ∪
        ((synWex (nb078AlphaDummy1051) (synWa (synWbr (Class.cv (nb078AlphaDummy1049))
                (synCcnv (synCcnv (Class.cv (nb078AlphaDummy002))))
                (Class.cv (nb078AlphaDummy1051)))
              (synWbr (Class.cv (nb078AlphaDummy1051))
                (synCcnv (Class.cv (nb078AlphaDummy002)))
                (Class.cv (nb078AlphaDummy1050)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1097 (h : Var) :
    (nb078AlphaDummy1052 h) ∈
      (({(nb078AlphaDummy1052 h)} : Finset Var) ∪
          ({(nb078AlphaDummy1053 h)} : Finset Var) ∪ ((synWex (nb078AlphaDummy1054 h)
            (synWa (synWbr (Class.cv (nb078AlphaDummy1052 h))
                (synCcnv (synCcnv (Class.cv h))) (Class.cv (nb078AlphaDummy1054 h)))
              (synWbr (Class.cv (nb078AlphaDummy1054 h)) (synCcnv (Class.cv h))
                (Class.cv (nb078AlphaDummy1053 h)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1098 :
    (nb078AlphaDummy1050) ∈
      (({(nb078AlphaDummy1049)} : Finset Var) ∪ ({(nb078AlphaDummy1050)} : Finset Var) ∪
        ((synWex (nb078AlphaDummy1051) (synWa (synWbr (Class.cv (nb078AlphaDummy1049))
                (synCcnv (synCcnv (Class.cv (nb078AlphaDummy002))))
                (Class.cv (nb078AlphaDummy1051)))
              (synWbr (Class.cv (nb078AlphaDummy1051))
                (synCcnv (Class.cv (nb078AlphaDummy002)))
                (Class.cv (nb078AlphaDummy1050)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1099 (h : Var) :
    (nb078AlphaDummy1053 h) ∈
      (({(nb078AlphaDummy1052 h)} : Finset Var) ∪
          ({(nb078AlphaDummy1053 h)} : Finset Var) ∪ ((synWex (nb078AlphaDummy1054 h)
            (synWa (synWbr (Class.cv (nb078AlphaDummy1052 h))
                (synCcnv (synCcnv (Class.cv h))) (Class.cv (nb078AlphaDummy1054 h)))
              (synWbr (Class.cv (nb078AlphaDummy1054 h)) (synCcnv (Class.cv h))
                (Class.cv (nb078AlphaDummy1053 h)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1100 :
    (nb078AlphaDummy1049) ∈
      (((Class.cv (nb078AlphaDummy1049))).fv ∪ ((Class.cv (nb078AlphaDummy1050))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1101 :
    (nb078AlphaDummy1049) ∈
      (((synCcompl (Class.cab (nb078AlphaDummy1057)
              (synWrex (nb078AlphaDummy1058) (Class.cv (nb078AlphaDummy1049))
                (Wff.classEq (Class.cv (nb078AlphaDummy1057))
                  (synCphi (Class.cv (nb078AlphaDummy1058)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy1057)
              (synWrex (nb078AlphaDummy1058) (Class.cv (nb078AlphaDummy1050))
                (Wff.classEq (Class.cv (nb078AlphaDummy1057))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy1058)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy1049) ≠ (nb078AlphaDummy1057) from (by
          unfold nb078AlphaDummy1057;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1100) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy1049) ≠ (nb078AlphaDummy1058) from (by
            unfold nb078AlphaDummy1058;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1100) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_1102 (h : Var) :
    (nb078AlphaDummy1052 h) ∈
      (((Class.cv (nb078AlphaDummy1052 h))).fv ∪
        ((Class.cv (nb078AlphaDummy1053 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1103 (h : Var) :
    (nb078AlphaDummy1052 h) ∈
      (((synCcompl (Class.cab (nb078AlphaDummy1059 h)
              (synWrex (nb078AlphaDummy1060 h) (Class.cv (nb078AlphaDummy1052 h))
                (Wff.classEq (Class.cv (nb078AlphaDummy1059 h))
                  (synCphi (Class.cv (nb078AlphaDummy1060 h)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy1059 h)
              (synWrex (nb078AlphaDummy1060 h) (Class.cv (nb078AlphaDummy1053 h))
                (Wff.classEq (Class.cv (nb078AlphaDummy1059 h))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy1060 h)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy1052 h) ≠ (nb078AlphaDummy1059 h) from (by
          unfold nb078AlphaDummy1059;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1102 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy1052 h) ≠ (nb078AlphaDummy1060 h) from (by
            unfold nb078AlphaDummy1060;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1102 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_1104 :
    (nb078AlphaDummy1049) ∈
      (((Class.cab (nb078AlphaDummy1057)
            (synWrex (nb078AlphaDummy1058) (Class.cv (nb078AlphaDummy1049))
              (Wff.classEq (Class.cv (nb078AlphaDummy1057))
                (synCphi (Class.cv (nb078AlphaDummy1058))))))).fv ∪
        ((Class.cab (nb078AlphaDummy1057)
            (synWrex (nb078AlphaDummy1058) (Class.cv (nb078AlphaDummy1049))
              (Wff.classEq (Class.cv (nb078AlphaDummy1057))
                (synCphi (Class.cv (nb078AlphaDummy1058))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy1049) ≠ (nb078AlphaDummy1057) from (by
          unfold nb078AlphaDummy1057;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1100) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy1049) ≠ (nb078AlphaDummy1058) from (by
            unfold nb078AlphaDummy1058;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1100) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_1105 (h : Var) :
    (nb078AlphaDummy1052 h) ∈
      (((Class.cab (nb078AlphaDummy1059 h)
            (synWrex (nb078AlphaDummy1060 h) (Class.cv (nb078AlphaDummy1052 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy1059 h))
                (synCphi (Class.cv (nb078AlphaDummy1060 h))))))).fv ∪
        ((Class.cab (nb078AlphaDummy1059 h)
            (synWrex (nb078AlphaDummy1060 h) (Class.cv (nb078AlphaDummy1052 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy1059 h))
                (synCphi (Class.cv (nb078AlphaDummy1060 h))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy1052 h) ≠ (nb078AlphaDummy1059 h) from (by
          unfold nb078AlphaDummy1059;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1102 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy1052 h) ≠ (nb078AlphaDummy1060 h) from (by
            unfold nb078AlphaDummy1060;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1102 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_1106 :
    (nb078AlphaDummy1058) ∈ (((Class.cv (nb078AlphaDummy1058))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1107 (h : Var) :
    (nb078AlphaDummy1060 h) ∈ (((Class.cv (nb078AlphaDummy1060 h))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1108 :
    (nb078AlphaDummy1065) ∈
      (((Wff.classMem (Class.cv (nb078AlphaDummy1065)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy1065)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy1065))).fv) :=
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

theorem nb078_support_mem_1109 (h : Var) :
    (nb078AlphaDummy1067 h) ∈
      (((Wff.classMem (Class.cv (nb078AlphaDummy1067 h)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy1067 h)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy1067 h))).fv) :=
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

theorem nb078_support_mem_1110 :
    (nb078AlphaDummy1065) ∈
      (((Class.cv (nb078AlphaDummy1065))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1111 (h : Var) :
    (nb078AlphaDummy1067 h) ∈
      (((Class.cv (nb078AlphaDummy1067 h))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1112 :
    (nb078AlphaDummy1072) ∈
      (((synCnin (Class.cv (nb078AlphaDummy1072)) (Class.cv (nb078AlphaDummy1073)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy1072))
            (Class.cv (nb078AlphaDummy1073)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1113 (h : Var) :
    (nb078AlphaDummy1075 h) ∈
      (((synCnin (Class.cv (nb078AlphaDummy1075 h))
            (Class.cv (nb078AlphaDummy1076 h)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy1075 h))
            (Class.cv (nb078AlphaDummy1076 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1114 :
    (nb078AlphaDummy1072) ∈
      (((Class.cv (nb078AlphaDummy1072))).fv ∪ ((Class.cv (nb078AlphaDummy1073))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1115 (h : Var) :
    (nb078AlphaDummy1075 h) ∈
      (((Class.cv (nb078AlphaDummy1075 h))).fv ∪
        ((Class.cv (nb078AlphaDummy1076 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1116 :
    (nb078AlphaDummy1073) ∈
      (((synCnin (Class.cv (nb078AlphaDummy1072)) (Class.cv (nb078AlphaDummy1073)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy1072))
            (Class.cv (nb078AlphaDummy1073)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1117 (h : Var) :
    (nb078AlphaDummy1076 h) ∈
      (((synCnin (Class.cv (nb078AlphaDummy1075 h))
            (Class.cv (nb078AlphaDummy1076 h)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy1075 h))
            (Class.cv (nb078AlphaDummy1076 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1118 :
    (nb078AlphaDummy1073) ∈
      (((Class.cv (nb078AlphaDummy1072))).fv ∪ ((Class.cv (nb078AlphaDummy1073))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1119 (h : Var) :
    (nb078AlphaDummy1076 h) ∈
      (((Class.cv (nb078AlphaDummy1075 h))).fv ∪
        ((Class.cv (nb078AlphaDummy1076 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1120 :
    (nb078AlphaDummy1072) ∈
      (((synCcompl (Class.cv (nb078AlphaDummy1072)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy1073)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1121 (h : Var) :
    (nb078AlphaDummy1075 h) ∈
      (((synCcompl (Class.cv (nb078AlphaDummy1075 h)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy1076 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1122 :
    (nb078AlphaDummy1072) ∈
      (((Class.cv (nb078AlphaDummy1072))).fv ∪ ((Class.cv (nb078AlphaDummy1072))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1123 (h : Var) :
    (nb078AlphaDummy1075 h) ∈
      (((Class.cv (nb078AlphaDummy1075 h))).fv ∪
        ((Class.cv (nb078AlphaDummy1075 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1124 :
    (nb078AlphaDummy1073) ∈
      (((synCcompl (Class.cv (nb078AlphaDummy1072)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy1073)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1125 (h : Var) :
    (nb078AlphaDummy1076 h) ∈
      (((synCcompl (Class.cv (nb078AlphaDummy1075 h)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy1076 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1126 :
    (nb078AlphaDummy1073) ∈
      (((Class.cv (nb078AlphaDummy1073))).fv ∪ ((Class.cv (nb078AlphaDummy1073))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1127 (h : Var) :
    (nb078AlphaDummy1076 h) ∈
      (((Class.cv (nb078AlphaDummy1076 h))).fv ∪
        ((Class.cv (nb078AlphaDummy1076 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1128 :
    (nb078AlphaDummy1050) ∈
      (((Class.cv (nb078AlphaDummy1049))).fv ∪ ((Class.cv (nb078AlphaDummy1050))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1129 :
    (nb078AlphaDummy1050) ∈
      (((synCcompl (Class.cab (nb078AlphaDummy1057)
              (synWrex (nb078AlphaDummy1058) (Class.cv (nb078AlphaDummy1049))
                (Wff.classEq (Class.cv (nb078AlphaDummy1057))
                  (synCphi (Class.cv (nb078AlphaDummy1058)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy1057)
              (synWrex (nb078AlphaDummy1058) (Class.cv (nb078AlphaDummy1050))
                (Wff.classEq (Class.cv (nb078AlphaDummy1057))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy1058)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy1050) ≠ (nb078AlphaDummy1057) from (by
          unfold nb078AlphaDummy1057;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1128) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy1050) ≠ (nb078AlphaDummy1058) from (by
            unfold nb078AlphaDummy1058;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1128) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_1130 (h : Var) :
    (nb078AlphaDummy1053 h) ∈
      (((Class.cv (nb078AlphaDummy1052 h))).fv ∪
        ((Class.cv (nb078AlphaDummy1053 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1131 (h : Var) :
    (nb078AlphaDummy1053 h) ∈
      (((synCcompl (Class.cab (nb078AlphaDummy1059 h)
              (synWrex (nb078AlphaDummy1060 h) (Class.cv (nb078AlphaDummy1052 h))
                (Wff.classEq (Class.cv (nb078AlphaDummy1059 h))
                  (synCphi (Class.cv (nb078AlphaDummy1060 h)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy1059 h)
              (synWrex (nb078AlphaDummy1060 h) (Class.cv (nb078AlphaDummy1053 h))
                (Wff.classEq (Class.cv (nb078AlphaDummy1059 h))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy1060 h)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy1053 h) ≠ (nb078AlphaDummy1059 h) from (by
          unfold nb078AlphaDummy1059;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1130 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy1053 h) ≠ (nb078AlphaDummy1060 h) from (by
            unfold nb078AlphaDummy1060;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1130 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_1132 :
    (nb078AlphaDummy1050) ∈
      (((Class.cab (nb078AlphaDummy1057)
            (synWrex (nb078AlphaDummy1058) (Class.cv (nb078AlphaDummy1050))
              (Wff.classEq (Class.cv (nb078AlphaDummy1057))
                (synCun (synCphi (Class.cv (nb078AlphaDummy1058)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy1057)
            (synWrex (nb078AlphaDummy1058) (Class.cv (nb078AlphaDummy1050))
              (Wff.classEq (Class.cv (nb078AlphaDummy1057))
                (synCun (synCphi (Class.cv (nb078AlphaDummy1058)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy1050) ≠ (nb078AlphaDummy1057) from (by
          unfold nb078AlphaDummy1057;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1128) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy1050) ≠ (nb078AlphaDummy1058) from (by
            unfold nb078AlphaDummy1058;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1128) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_1133 (h : Var) :
    (nb078AlphaDummy1053 h) ∈
      (((Class.cab (nb078AlphaDummy1059 h)
            (synWrex (nb078AlphaDummy1060 h) (Class.cv (nb078AlphaDummy1053 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy1059 h))
                (synCun (synCphi (Class.cv (nb078AlphaDummy1060 h)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy1059 h)
            (synWrex (nb078AlphaDummy1060 h) (Class.cv (nb078AlphaDummy1053 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy1059 h))
                (synCun (synCphi (Class.cv (nb078AlphaDummy1060 h)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy1053 h) ≠ (nb078AlphaDummy1059 h) from (by
          unfold nb078AlphaDummy1059;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1130 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy1053 h) ≠ (nb078AlphaDummy1060 h) from (by
            unfold nb078AlphaDummy1060;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1130 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_1134 :
    (nb078AlphaDummy1058) ∈
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy1058))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1135 (h : Var) :
    (nb078AlphaDummy1060 h) ∈
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy1060 h))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1136 :
    (nb078AlphaDummy1058) ∈
      (((synCphi (Class.cv (nb078AlphaDummy1058)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy1058)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1137 (h : Var) :
    (nb078AlphaDummy1060 h) ∈
      (((synCphi (Class.cv (nb078AlphaDummy1060 h)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy1060 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1138 :
    (nb078AlphaDummy1049) ∈
      (((Class.cv (nb078AlphaDummy1049))).fv ∪ ((Class.cv (nb078AlphaDummy1051))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1139 :
    (nb078AlphaDummy1049) ∈
      (((synCcompl (Class.cab (nb078AlphaDummy1093)
              (synWrex (nb078AlphaDummy1094) (Class.cv (nb078AlphaDummy1049))
                (Wff.classEq (Class.cv (nb078AlphaDummy1093))
                  (synCphi (Class.cv (nb078AlphaDummy1094)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy1093)
              (synWrex (nb078AlphaDummy1094) (Class.cv (nb078AlphaDummy1051))
                (Wff.classEq (Class.cv (nb078AlphaDummy1093))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy1094)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy1049) ≠ (nb078AlphaDummy1093) from (by
          unfold nb078AlphaDummy1093;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1138) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy1049) ≠ (nb078AlphaDummy1094) from (by
            unfold nb078AlphaDummy1094;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1138) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_1140 (h : Var) :
    (nb078AlphaDummy1052 h) ∈
      (((Class.cv (nb078AlphaDummy1052 h))).fv ∪
        ((Class.cv (nb078AlphaDummy1054 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1141 (h : Var) :
    (nb078AlphaDummy1052 h) ∈
      (((synCcompl (Class.cab (nb078AlphaDummy1095 h)
              (synWrex (nb078AlphaDummy1096 h) (Class.cv (nb078AlphaDummy1052 h))
                (Wff.classEq (Class.cv (nb078AlphaDummy1095 h))
                  (synCphi (Class.cv (nb078AlphaDummy1096 h)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy1095 h)
              (synWrex (nb078AlphaDummy1096 h) (Class.cv (nb078AlphaDummy1054 h))
                (Wff.classEq (Class.cv (nb078AlphaDummy1095 h))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy1096 h)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy1052 h) ≠ (nb078AlphaDummy1095 h) from (by
          unfold nb078AlphaDummy1095;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1140 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy1052 h) ≠ (nb078AlphaDummy1096 h) from (by
            unfold nb078AlphaDummy1096;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1140 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_1142 :
    (nb078AlphaDummy1049) ∈
      (((Class.cab (nb078AlphaDummy1093)
            (synWrex (nb078AlphaDummy1094) (Class.cv (nb078AlphaDummy1049))
              (Wff.classEq (Class.cv (nb078AlphaDummy1093))
                (synCphi (Class.cv (nb078AlphaDummy1094))))))).fv ∪
        ((Class.cab (nb078AlphaDummy1093)
            (synWrex (nb078AlphaDummy1094) (Class.cv (nb078AlphaDummy1049))
              (Wff.classEq (Class.cv (nb078AlphaDummy1093))
                (synCphi (Class.cv (nb078AlphaDummy1094))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy1049) ≠ (nb078AlphaDummy1093) from (by
          unfold nb078AlphaDummy1093;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1138) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy1049) ≠ (nb078AlphaDummy1094) from (by
            unfold nb078AlphaDummy1094;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1138) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_1143 (h : Var) :
    (nb078AlphaDummy1052 h) ∈
      (((Class.cab (nb078AlphaDummy1095 h)
            (synWrex (nb078AlphaDummy1096 h) (Class.cv (nb078AlphaDummy1052 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy1095 h))
                (synCphi (Class.cv (nb078AlphaDummy1096 h))))))).fv ∪
        ((Class.cab (nb078AlphaDummy1095 h)
            (synWrex (nb078AlphaDummy1096 h) (Class.cv (nb078AlphaDummy1052 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy1095 h))
                (synCphi (Class.cv (nb078AlphaDummy1096 h))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy1052 h) ≠ (nb078AlphaDummy1095 h) from (by
          unfold nb078AlphaDummy1095;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1140 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy1052 h) ≠ (nb078AlphaDummy1096 h) from (by
            unfold nb078AlphaDummy1096;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1140 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_1144 :
    (nb078AlphaDummy1094) ∈ (((Class.cv (nb078AlphaDummy1094))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1145 (h : Var) :
    (nb078AlphaDummy1096 h) ∈ (((Class.cv (nb078AlphaDummy1096 h))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1146 :
    (nb078AlphaDummy1101) ∈
      (((Wff.classMem (Class.cv (nb078AlphaDummy1101)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy1101)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy1101))).fv) :=
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

theorem nb078_support_mem_1147 (h : Var) :
    (nb078AlphaDummy1103 h) ∈
      (((Wff.classMem (Class.cv (nb078AlphaDummy1103 h)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy1103 h)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy1103 h))).fv) :=
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

theorem nb078_support_mem_1148 :
    (nb078AlphaDummy1101) ∈
      (((Class.cv (nb078AlphaDummy1101))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1149 (h : Var) :
    (nb078AlphaDummy1103 h) ∈
      (((Class.cv (nb078AlphaDummy1103 h))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1150 :
    (nb078AlphaDummy1108) ∈
      (((synCnin (Class.cv (nb078AlphaDummy1108)) (Class.cv (nb078AlphaDummy1109)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy1108))
            (Class.cv (nb078AlphaDummy1109)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1151 (h : Var) :
    (nb078AlphaDummy1111 h) ∈
      (((synCnin (Class.cv (nb078AlphaDummy1111 h))
            (Class.cv (nb078AlphaDummy1112 h)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy1111 h))
            (Class.cv (nb078AlphaDummy1112 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1152 :
    (nb078AlphaDummy1108) ∈
      (((Class.cv (nb078AlphaDummy1108))).fv ∪ ((Class.cv (nb078AlphaDummy1109))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1153 (h : Var) :
    (nb078AlphaDummy1111 h) ∈
      (((Class.cv (nb078AlphaDummy1111 h))).fv ∪
        ((Class.cv (nb078AlphaDummy1112 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1154 :
    (nb078AlphaDummy1109) ∈
      (((synCnin (Class.cv (nb078AlphaDummy1108)) (Class.cv (nb078AlphaDummy1109)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy1108))
            (Class.cv (nb078AlphaDummy1109)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1155 (h : Var) :
    (nb078AlphaDummy1112 h) ∈
      (((synCnin (Class.cv (nb078AlphaDummy1111 h))
            (Class.cv (nb078AlphaDummy1112 h)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy1111 h))
            (Class.cv (nb078AlphaDummy1112 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1156 :
    (nb078AlphaDummy1109) ∈
      (((Class.cv (nb078AlphaDummy1108))).fv ∪ ((Class.cv (nb078AlphaDummy1109))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1157 (h : Var) :
    (nb078AlphaDummy1112 h) ∈
      (((Class.cv (nb078AlphaDummy1111 h))).fv ∪
        ((Class.cv (nb078AlphaDummy1112 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1158 :
    (nb078AlphaDummy1108) ∈
      (((synCcompl (Class.cv (nb078AlphaDummy1108)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy1109)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1159 (h : Var) :
    (nb078AlphaDummy1111 h) ∈
      (((synCcompl (Class.cv (nb078AlphaDummy1111 h)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy1112 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1160 :
    (nb078AlphaDummy1108) ∈
      (((Class.cv (nb078AlphaDummy1108))).fv ∪ ((Class.cv (nb078AlphaDummy1108))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1161 (h : Var) :
    (nb078AlphaDummy1111 h) ∈
      (((Class.cv (nb078AlphaDummy1111 h))).fv ∪
        ((Class.cv (nb078AlphaDummy1111 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1162 :
    (nb078AlphaDummy1109) ∈
      (((synCcompl (Class.cv (nb078AlphaDummy1108)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy1109)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1163 (h : Var) :
    (nb078AlphaDummy1112 h) ∈
      (((synCcompl (Class.cv (nb078AlphaDummy1111 h)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy1112 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1164 :
    (nb078AlphaDummy1109) ∈
      (((Class.cv (nb078AlphaDummy1109))).fv ∪ ((Class.cv (nb078AlphaDummy1109))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
