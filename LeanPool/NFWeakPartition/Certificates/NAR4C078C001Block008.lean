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
    (nb078_alpha_dummy_847) ∈
      (({(nb078_alpha_dummy_847)} : Finset Var) ∪ ({(nb078_alpha_dummy_848)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb078_alpha_dummy_848)) (Class.cv (nb078_alpha_dummy_002))
            (Class.cv (nb078_alpha_dummy_847)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0879 (h : Var) :
    (nb078_alpha_dummy_849 h) ∈
      (({(nb078_alpha_dummy_849 h)} : Finset Var) ∪ ({(nb078_alpha_dummy_850 h)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb078_alpha_dummy_850 h)) (Class.cv h)
            (Class.cv (nb078_alpha_dummy_849 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0880 :
    (nb078_alpha_dummy_848) ∈
      (({(nb078_alpha_dummy_847)} : Finset Var) ∪ ({(nb078_alpha_dummy_848)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb078_alpha_dummy_848)) (Class.cv (nb078_alpha_dummy_002))
            (Class.cv (nb078_alpha_dummy_847)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0881 (h : Var) :
    (nb078_alpha_dummy_850 h) ∈
      (({(nb078_alpha_dummy_849 h)} : Finset Var) ∪ ({(nb078_alpha_dummy_850 h)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb078_alpha_dummy_850 h)) (Class.cv h)
            (Class.cv (nb078_alpha_dummy_849 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0882 :
    (nb078_alpha_dummy_847) ∈
      (((Class.cv (nb078_alpha_dummy_847))).fv ∪ ((Class.cv (nb078_alpha_dummy_848))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0883 :
    (nb078_alpha_dummy_847) ∈
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_853)
              (syn_wrex (nb078_alpha_dummy_854) (Class.cv (nb078_alpha_dummy_847))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_853))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_854)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_853)
              (syn_wrex (nb078_alpha_dummy_854) (Class.cv (nb078_alpha_dummy_848))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_853))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_854)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_847) ≠ (nb078_alpha_dummy_853) from (by
          unfold nb078_alpha_dummy_853;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0882) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_847) ≠ (nb078_alpha_dummy_854) from (by
            unfold nb078_alpha_dummy_854;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0882) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0884 (h : Var) :
    (nb078_alpha_dummy_849 h) ∈
      (((Class.cv (nb078_alpha_dummy_849 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_850 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0885 (h : Var) :
    (nb078_alpha_dummy_849 h) ∈
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_855 h)
              (syn_wrex (nb078_alpha_dummy_856 h) (Class.cv (nb078_alpha_dummy_849 h))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_855 h))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_856 h)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_855 h)
              (syn_wrex (nb078_alpha_dummy_856 h) (Class.cv (nb078_alpha_dummy_850 h))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_855 h))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_856 h)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_849 h) ≠ (nb078_alpha_dummy_855 h) from (by
          unfold nb078_alpha_dummy_855;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0884 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_849 h) ≠ (nb078_alpha_dummy_856 h) from (by
            unfold nb078_alpha_dummy_856;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0884 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0886 :
    (nb078_alpha_dummy_847) ∈
      (((Class.cab (nb078_alpha_dummy_853)
            (syn_wrex (nb078_alpha_dummy_854) (Class.cv (nb078_alpha_dummy_847))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_853))
                (syn_cphi (Class.cv (nb078_alpha_dummy_854))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_853)
            (syn_wrex (nb078_alpha_dummy_854) (Class.cv (nb078_alpha_dummy_847))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_853))
                (syn_cphi (Class.cv (nb078_alpha_dummy_854))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_847) ≠ (nb078_alpha_dummy_853) from (by
          unfold nb078_alpha_dummy_853;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0882) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_847) ≠ (nb078_alpha_dummy_854) from (by
            unfold nb078_alpha_dummy_854;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0882) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0887 (h : Var) :
    (nb078_alpha_dummy_849 h) ∈
      (((Class.cab (nb078_alpha_dummy_855 h)
            (syn_wrex (nb078_alpha_dummy_856 h) (Class.cv (nb078_alpha_dummy_849 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_855 h))
                (syn_cphi (Class.cv (nb078_alpha_dummy_856 h))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_855 h)
            (syn_wrex (nb078_alpha_dummy_856 h) (Class.cv (nb078_alpha_dummy_849 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_855 h))
                (syn_cphi (Class.cv (nb078_alpha_dummy_856 h))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_849 h) ≠ (nb078_alpha_dummy_855 h) from (by
          unfold nb078_alpha_dummy_855;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0884 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_849 h) ≠ (nb078_alpha_dummy_856 h) from (by
            unfold nb078_alpha_dummy_856;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0884 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0888 :
    (nb078_alpha_dummy_854) ∈ (((Class.cv (nb078_alpha_dummy_854))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0889 (h : Var) :
    (nb078_alpha_dummy_856 h) ∈ (((Class.cv (nb078_alpha_dummy_856 h))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0890 :
    (nb078_alpha_dummy_861) ∈
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_861)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_861)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_861))).fv) :=
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
    (nb078_alpha_dummy_863 h) ∈
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_863 h)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_863 h)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_863 h))).fv) :=
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
    (nb078_alpha_dummy_861) ∈
      (((Class.cv (nb078_alpha_dummy_861))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0893 (h : Var) :
    (nb078_alpha_dummy_863 h) ∈
      (((Class.cv (nb078_alpha_dummy_863 h))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0894 :
    (nb078_alpha_dummy_868) ∈
      (((syn_cnin (Class.cv (nb078_alpha_dummy_868)) (Class.cv (nb078_alpha_dummy_869)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_868))
            (Class.cv (nb078_alpha_dummy_869)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0895 (h : Var) :
    (nb078_alpha_dummy_871 h) ∈
      (((syn_cnin (Class.cv (nb078_alpha_dummy_871 h))
            (Class.cv (nb078_alpha_dummy_872 h)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_871 h))
            (Class.cv (nb078_alpha_dummy_872 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0896 :
    (nb078_alpha_dummy_868) ∈
      (((Class.cv (nb078_alpha_dummy_868))).fv ∪ ((Class.cv (nb078_alpha_dummy_869))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0897 (h : Var) :
    (nb078_alpha_dummy_871 h) ∈
      (((Class.cv (nb078_alpha_dummy_871 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_872 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0898 :
    (nb078_alpha_dummy_869) ∈
      (((syn_cnin (Class.cv (nb078_alpha_dummy_868)) (Class.cv (nb078_alpha_dummy_869)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_868))
            (Class.cv (nb078_alpha_dummy_869)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0899 (h : Var) :
    (nb078_alpha_dummy_872 h) ∈
      (((syn_cnin (Class.cv (nb078_alpha_dummy_871 h))
            (Class.cv (nb078_alpha_dummy_872 h)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_871 h))
            (Class.cv (nb078_alpha_dummy_872 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0900 :
    (nb078_alpha_dummy_869) ∈
      (((Class.cv (nb078_alpha_dummy_868))).fv ∪ ((Class.cv (nb078_alpha_dummy_869))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0901 (h : Var) :
    (nb078_alpha_dummy_872 h) ∈
      (((Class.cv (nb078_alpha_dummy_871 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_872 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0902 :
    (nb078_alpha_dummy_868) ∈
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_868)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_869)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0903 (h : Var) :
    (nb078_alpha_dummy_871 h) ∈
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_871 h)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_872 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0904 :
    (nb078_alpha_dummy_868) ∈
      (((Class.cv (nb078_alpha_dummy_868))).fv ∪ ((Class.cv (nb078_alpha_dummy_868))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0905 (h : Var) :
    (nb078_alpha_dummy_871 h) ∈
      (((Class.cv (nb078_alpha_dummy_871 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_871 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0906 :
    (nb078_alpha_dummy_869) ∈
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_868)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_869)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0907 (h : Var) :
    (nb078_alpha_dummy_872 h) ∈
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_871 h)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_872 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0908 :
    (nb078_alpha_dummy_869) ∈
      (((Class.cv (nb078_alpha_dummy_869))).fv ∪ ((Class.cv (nb078_alpha_dummy_869))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0909 (h : Var) :
    (nb078_alpha_dummy_872 h) ∈
      (((Class.cv (nb078_alpha_dummy_872 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_872 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0910 :
    (nb078_alpha_dummy_848) ∈
      (((Class.cv (nb078_alpha_dummy_847))).fv ∪ ((Class.cv (nb078_alpha_dummy_848))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0911 :
    (nb078_alpha_dummy_848) ∈
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_853)
              (syn_wrex (nb078_alpha_dummy_854) (Class.cv (nb078_alpha_dummy_847))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_853))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_854)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_853)
              (syn_wrex (nb078_alpha_dummy_854) (Class.cv (nb078_alpha_dummy_848))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_853))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_854)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_848) ≠ (nb078_alpha_dummy_853) from (by
          unfold nb078_alpha_dummy_853;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0910) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_848) ≠ (nb078_alpha_dummy_854) from (by
            unfold nb078_alpha_dummy_854;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0910) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0912 (h : Var) :
    (nb078_alpha_dummy_850 h) ∈
      (((Class.cv (nb078_alpha_dummy_849 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_850 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0913 (h : Var) :
    (nb078_alpha_dummy_850 h) ∈
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_855 h)
              (syn_wrex (nb078_alpha_dummy_856 h) (Class.cv (nb078_alpha_dummy_849 h))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_855 h))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_856 h)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_855 h)
              (syn_wrex (nb078_alpha_dummy_856 h) (Class.cv (nb078_alpha_dummy_850 h))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_855 h))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_856 h)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_850 h) ≠ (nb078_alpha_dummy_855 h) from (by
          unfold nb078_alpha_dummy_855;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0912 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_850 h) ≠ (nb078_alpha_dummy_856 h) from (by
            unfold nb078_alpha_dummy_856;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0912 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0914 :
    (nb078_alpha_dummy_848) ∈
      (((Class.cab (nb078_alpha_dummy_853)
            (syn_wrex (nb078_alpha_dummy_854) (Class.cv (nb078_alpha_dummy_848))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_853))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_854)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_853)
            (syn_wrex (nb078_alpha_dummy_854) (Class.cv (nb078_alpha_dummy_848))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_853))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_854)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_848) ≠ (nb078_alpha_dummy_853) from (by
          unfold nb078_alpha_dummy_853;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0910) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_848) ≠ (nb078_alpha_dummy_854) from (by
            unfold nb078_alpha_dummy_854;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0910) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0915 (h : Var) :
    (nb078_alpha_dummy_850 h) ∈
      (((Class.cab (nb078_alpha_dummy_855 h)
            (syn_wrex (nb078_alpha_dummy_856 h) (Class.cv (nb078_alpha_dummy_850 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_855 h))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_856 h)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_855 h)
            (syn_wrex (nb078_alpha_dummy_856 h) (Class.cv (nb078_alpha_dummy_850 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_855 h))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_856 h)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_850 h) ≠ (nb078_alpha_dummy_855 h) from (by
          unfold nb078_alpha_dummy_855;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0912 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_850 h) ≠ (nb078_alpha_dummy_856 h) from (by
            unfold nb078_alpha_dummy_856;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0912 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0916 :
    (nb078_alpha_dummy_854) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_854))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0917 (h : Var) :
    (nb078_alpha_dummy_856 h) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_856 h))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0918 :
    (nb078_alpha_dummy_854) ∈
      (((syn_cphi (Class.cv (nb078_alpha_dummy_854)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_854)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0919 (h : Var) :
    (nb078_alpha_dummy_856 h) ∈
      (((syn_cphi (Class.cv (nb078_alpha_dummy_856 h)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_856 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0920 :
    (nb078_alpha_dummy_848) ∈
      (((Class.cv (nb078_alpha_dummy_848))).fv ∪ ((Class.cv (nb078_alpha_dummy_847))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0921 :
    (nb078_alpha_dummy_848) ∈
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_889)
              (syn_wrex (nb078_alpha_dummy_890) (Class.cv (nb078_alpha_dummy_848))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_889))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_890)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_889)
              (syn_wrex (nb078_alpha_dummy_890) (Class.cv (nb078_alpha_dummy_847))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_889))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_890)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_848) ≠ (nb078_alpha_dummy_889) from (by
          unfold nb078_alpha_dummy_889;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0920) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_848) ≠ (nb078_alpha_dummy_890) from (by
            unfold nb078_alpha_dummy_890;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0920) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0922 (h : Var) :
    (nb078_alpha_dummy_850 h) ∈
      (((Class.cv (nb078_alpha_dummy_850 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_849 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0923 (h : Var) :
    (nb078_alpha_dummy_850 h) ∈
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_891 h)
              (syn_wrex (nb078_alpha_dummy_892 h) (Class.cv (nb078_alpha_dummy_850 h))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_891 h))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_892 h)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_891 h)
              (syn_wrex (nb078_alpha_dummy_892 h) (Class.cv (nb078_alpha_dummy_849 h))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_891 h))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_892 h)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_850 h) ≠ (nb078_alpha_dummy_891 h) from (by
          unfold nb078_alpha_dummy_891;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0922 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_850 h) ≠ (nb078_alpha_dummy_892 h) from (by
            unfold nb078_alpha_dummy_892;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0922 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0924 :
    (nb078_alpha_dummy_848) ∈
      (((Class.cab (nb078_alpha_dummy_889)
            (syn_wrex (nb078_alpha_dummy_890) (Class.cv (nb078_alpha_dummy_848))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_889))
                (syn_cphi (Class.cv (nb078_alpha_dummy_890))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_889)
            (syn_wrex (nb078_alpha_dummy_890) (Class.cv (nb078_alpha_dummy_848))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_889))
                (syn_cphi (Class.cv (nb078_alpha_dummy_890))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_848) ≠ (nb078_alpha_dummy_889) from (by
          unfold nb078_alpha_dummy_889;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0920) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_848) ≠ (nb078_alpha_dummy_890) from (by
            unfold nb078_alpha_dummy_890;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0920) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0925 (h : Var) :
    (nb078_alpha_dummy_850 h) ∈
      (((Class.cab (nb078_alpha_dummy_891 h)
            (syn_wrex (nb078_alpha_dummy_892 h) (Class.cv (nb078_alpha_dummy_850 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_891 h))
                (syn_cphi (Class.cv (nb078_alpha_dummy_892 h))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_891 h)
            (syn_wrex (nb078_alpha_dummy_892 h) (Class.cv (nb078_alpha_dummy_850 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_891 h))
                (syn_cphi (Class.cv (nb078_alpha_dummy_892 h))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_850 h) ≠ (nb078_alpha_dummy_891 h) from (by
          unfold nb078_alpha_dummy_891;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0922 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_850 h) ≠ (nb078_alpha_dummy_892 h) from (by
            unfold nb078_alpha_dummy_892;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0922 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0926 :
    (nb078_alpha_dummy_890) ∈ (((Class.cv (nb078_alpha_dummy_890))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0927 (h : Var) :
    (nb078_alpha_dummy_892 h) ∈ (((Class.cv (nb078_alpha_dummy_892 h))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0928 :
    (nb078_alpha_dummy_897) ∈
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_897)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_897)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_897))).fv) :=
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
    (nb078_alpha_dummy_899 h) ∈
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_899 h)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_899 h)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_899 h))).fv) :=
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
    (nb078_alpha_dummy_897) ∈
      (((Class.cv (nb078_alpha_dummy_897))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0931 (h : Var) :
    (nb078_alpha_dummy_899 h) ∈
      (((Class.cv (nb078_alpha_dummy_899 h))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0932 :
    (nb078_alpha_dummy_904) ∈
      (((syn_cnin (Class.cv (nb078_alpha_dummy_904)) (Class.cv (nb078_alpha_dummy_905)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_904))
            (Class.cv (nb078_alpha_dummy_905)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0933 (h : Var) :
    (nb078_alpha_dummy_907 h) ∈
      (((syn_cnin (Class.cv (nb078_alpha_dummy_907 h))
            (Class.cv (nb078_alpha_dummy_908 h)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_907 h))
            (Class.cv (nb078_alpha_dummy_908 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0934 :
    (nb078_alpha_dummy_904) ∈
      (((Class.cv (nb078_alpha_dummy_904))).fv ∪ ((Class.cv (nb078_alpha_dummy_905))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0935 (h : Var) :
    (nb078_alpha_dummy_907 h) ∈
      (((Class.cv (nb078_alpha_dummy_907 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_908 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0936 :
    (nb078_alpha_dummy_905) ∈
      (((syn_cnin (Class.cv (nb078_alpha_dummy_904)) (Class.cv (nb078_alpha_dummy_905)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_904))
            (Class.cv (nb078_alpha_dummy_905)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0937 (h : Var) :
    (nb078_alpha_dummy_908 h) ∈
      (((syn_cnin (Class.cv (nb078_alpha_dummy_907 h))
            (Class.cv (nb078_alpha_dummy_908 h)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_907 h))
            (Class.cv (nb078_alpha_dummy_908 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0938 :
    (nb078_alpha_dummy_905) ∈
      (((Class.cv (nb078_alpha_dummy_904))).fv ∪ ((Class.cv (nb078_alpha_dummy_905))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0939 (h : Var) :
    (nb078_alpha_dummy_908 h) ∈
      (((Class.cv (nb078_alpha_dummy_907 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_908 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0940 :
    (nb078_alpha_dummy_904) ∈
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_904)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_905)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0941 (h : Var) :
    (nb078_alpha_dummy_907 h) ∈
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_907 h)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_908 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0942 :
    (nb078_alpha_dummy_904) ∈
      (((Class.cv (nb078_alpha_dummy_904))).fv ∪ ((Class.cv (nb078_alpha_dummy_904))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0943 (h : Var) :
    (nb078_alpha_dummy_907 h) ∈
      (((Class.cv (nb078_alpha_dummy_907 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_907 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0944 :
    (nb078_alpha_dummy_905) ∈
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_904)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_905)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0945 (h : Var) :
    (nb078_alpha_dummy_908 h) ∈
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_907 h)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_908 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0946 :
    (nb078_alpha_dummy_905) ∈
      (((Class.cv (nb078_alpha_dummy_905))).fv ∪ ((Class.cv (nb078_alpha_dummy_905))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0947 (h : Var) :
    (nb078_alpha_dummy_908 h) ∈
      (((Class.cv (nb078_alpha_dummy_908 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_908 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0948 :
    (nb078_alpha_dummy_847) ∈
      (((Class.cv (nb078_alpha_dummy_848))).fv ∪ ((Class.cv (nb078_alpha_dummy_847))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0949 :
    (nb078_alpha_dummy_847) ∈
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_889)
              (syn_wrex (nb078_alpha_dummy_890) (Class.cv (nb078_alpha_dummy_848))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_889))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_890)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_889)
              (syn_wrex (nb078_alpha_dummy_890) (Class.cv (nb078_alpha_dummy_847))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_889))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_890)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_847) ≠ (nb078_alpha_dummy_889) from (by
          unfold nb078_alpha_dummy_889;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0948) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_847) ≠ (nb078_alpha_dummy_890) from (by
            unfold nb078_alpha_dummy_890;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0948) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0950 (h : Var) :
    (nb078_alpha_dummy_849 h) ∈
      (((Class.cv (nb078_alpha_dummy_850 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_849 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0951 (h : Var) :
    (nb078_alpha_dummy_849 h) ∈
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_891 h)
              (syn_wrex (nb078_alpha_dummy_892 h) (Class.cv (nb078_alpha_dummy_850 h))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_891 h))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_892 h)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_891 h)
              (syn_wrex (nb078_alpha_dummy_892 h) (Class.cv (nb078_alpha_dummy_849 h))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_891 h))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_892 h)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_849 h) ≠ (nb078_alpha_dummy_891 h) from (by
          unfold nb078_alpha_dummy_891;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0950 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_849 h) ≠ (nb078_alpha_dummy_892 h) from (by
            unfold nb078_alpha_dummy_892;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0950 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0952 :
    (nb078_alpha_dummy_847) ∈
      (((Class.cab (nb078_alpha_dummy_889)
            (syn_wrex (nb078_alpha_dummy_890) (Class.cv (nb078_alpha_dummy_847))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_889))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_890)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_889)
            (syn_wrex (nb078_alpha_dummy_890) (Class.cv (nb078_alpha_dummy_847))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_889))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_890)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_847) ≠ (nb078_alpha_dummy_889) from (by
          unfold nb078_alpha_dummy_889;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0948) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_847) ≠ (nb078_alpha_dummy_890) from (by
            unfold nb078_alpha_dummy_890;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0948) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0953 (h : Var) :
    (nb078_alpha_dummy_849 h) ∈
      (((Class.cab (nb078_alpha_dummy_891 h)
            (syn_wrex (nb078_alpha_dummy_892 h) (Class.cv (nb078_alpha_dummy_849 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_891 h))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_892 h)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_891 h)
            (syn_wrex (nb078_alpha_dummy_892 h) (Class.cv (nb078_alpha_dummy_849 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_891 h))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_892 h)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_849 h) ≠ (nb078_alpha_dummy_891 h) from (by
          unfold nb078_alpha_dummy_891;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0950 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_849 h) ≠ (nb078_alpha_dummy_892 h) from (by
            unfold nb078_alpha_dummy_892;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0950 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0954 :
    (nb078_alpha_dummy_890) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_890))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0955 (h : Var) :
    (nb078_alpha_dummy_892 h) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_892 h))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0956 :
    (nb078_alpha_dummy_890) ∈
      (((syn_cphi (Class.cv (nb078_alpha_dummy_890)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_890)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0957 (h : Var) :
    (nb078_alpha_dummy_892 h) ∈
      (((syn_cphi (Class.cv (nb078_alpha_dummy_892 h)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_892 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0958 :
    (nb078_alpha_dummy_002) ∈
      (((syn_cnin (syn_ccom (Class.cv (nb078_alpha_dummy_002))
              (syn_ccnv (Class.cv (nb078_alpha_dummy_002)))) (syn_cid))).fv ∪ ((syn_cnin
            (syn_ccom (Class.cv (nb078_alpha_dummy_002))
              (syn_ccnv (Class.cv (nb078_alpha_dummy_002)))) (syn_cid))).fv) :=
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
      (((syn_cnin (syn_ccom (Class.cv h) (syn_ccnv (Class.cv h))) (syn_cid))).fv ∪
        ((syn_cnin (syn_ccom (Class.cv h) (syn_ccnv (Class.cv h))) (syn_cid))).fv) :=
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
    (nb078_alpha_dummy_002) ∈
      (((syn_ccom (Class.cv (nb078_alpha_dummy_002))
            (syn_ccnv (Class.cv (nb078_alpha_dummy_002))))).fv ∪ ((syn_cid)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccom]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0961 (h : Var) :
    h ∈ (((syn_ccom (Class.cv h) (syn_ccnv (Class.cv h)))).fv ∪ ((syn_cid)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccom]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0962 :
    (nb078_alpha_dummy_002) ∈
      (((Class.cv (nb078_alpha_dummy_002))).fv ∪
        ((syn_ccnv (Class.cv (nb078_alpha_dummy_002)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0963 :
    (nb078_alpha_dummy_002) ∈
      (({(nb078_alpha_dummy_767)} : Finset Var) ∪ ({(nb078_alpha_dummy_768)} : Finset Var) ∪
        ((syn_wex (nb078_alpha_dummy_769) (syn_wa (syn_wbr (Class.cv (nb078_alpha_dummy_767))
                (syn_ccnv (Class.cv (nb078_alpha_dummy_002)))
                (Class.cv (nb078_alpha_dummy_769))) (syn_wbr (Class.cv (nb078_alpha_dummy_769))
                (Class.cv (nb078_alpha_dummy_002)) (Class.cv (nb078_alpha_dummy_768)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_wex]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_002) ≠ (nb078_alpha_dummy_769) from (by
          unfold nb078_alpha_dummy_769;
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
    h ∈ (((Class.cv h)).fv ∪ ((syn_ccnv (Class.cv h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0965 (h : Var) :
    h ∈
      (({(nb078_alpha_dummy_770 h)} : Finset Var) ∪ ({(nb078_alpha_dummy_771 h)} : Finset Var) ∪
        ((syn_wex (nb078_alpha_dummy_772 h) (syn_wa
              (syn_wbr (Class.cv (nb078_alpha_dummy_770 h)) (syn_ccnv (Class.cv h))
                (Class.cv (nb078_alpha_dummy_772 h)))
              (syn_wbr (Class.cv (nb078_alpha_dummy_772 h)) (Class.cv h)
                (Class.cv (nb078_alpha_dummy_771 h)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_wex]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show h ≠ (nb078_alpha_dummy_772 h) from (by
          unfold nb078_alpha_dummy_772;
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
    (nb078_alpha_dummy_002) ∈
      (({(nb078_alpha_dummy_847)} : Finset Var) ∪ ({(nb078_alpha_dummy_848)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb078_alpha_dummy_848)) (Class.cv (nb078_alpha_dummy_002))
            (Class.cv (nb078_alpha_dummy_847)))).fv) :=
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
      (({(nb078_alpha_dummy_849 h)} : Finset Var) ∪ ({(nb078_alpha_dummy_850 h)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb078_alpha_dummy_850 h)) (Class.cv h)
            (Class.cv (nb078_alpha_dummy_849 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_wbr]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0968 :
    (nb078_alpha_dummy_002) ∈ (((Class.cv (nb078_alpha_dummy_002))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0969 (h : Var) : h ∈ (((Class.cv h)).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0970 :
    (nb078_alpha_dummy_769) ∈
      (((Class.cv (nb078_alpha_dummy_769))).fv ∪ ((Class.cv (nb078_alpha_dummy_768))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0971 :
    (nb078_alpha_dummy_769) ∈
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_925)
              (syn_wrex (nb078_alpha_dummy_926) (Class.cv (nb078_alpha_dummy_769))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_925))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_926)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_925)
              (syn_wrex (nb078_alpha_dummy_926) (Class.cv (nb078_alpha_dummy_768))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_925))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_926)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_769) ≠ (nb078_alpha_dummy_925) from (by
          unfold nb078_alpha_dummy_925;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0970) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_769) ≠ (nb078_alpha_dummy_926) from (by
            unfold nb078_alpha_dummy_926;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0970) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0972 (h : Var) :
    (nb078_alpha_dummy_772 h) ∈
      (((Class.cv (nb078_alpha_dummy_772 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_771 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0973 (h : Var) :
    (nb078_alpha_dummy_772 h) ∈
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_927 h)
              (syn_wrex (nb078_alpha_dummy_928 h) (Class.cv (nb078_alpha_dummy_772 h))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_927 h))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_928 h)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_927 h)
              (syn_wrex (nb078_alpha_dummy_928 h) (Class.cv (nb078_alpha_dummy_771 h))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_927 h))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_928 h)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_772 h) ≠ (nb078_alpha_dummy_927 h) from (by
          unfold nb078_alpha_dummy_927;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0972 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_772 h) ≠ (nb078_alpha_dummy_928 h) from (by
            unfold nb078_alpha_dummy_928;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0972 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0974 :
    (nb078_alpha_dummy_769) ∈
      (((Class.cab (nb078_alpha_dummy_925)
            (syn_wrex (nb078_alpha_dummy_926) (Class.cv (nb078_alpha_dummy_769))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_925))
                (syn_cphi (Class.cv (nb078_alpha_dummy_926))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_925)
            (syn_wrex (nb078_alpha_dummy_926) (Class.cv (nb078_alpha_dummy_769))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_925))
                (syn_cphi (Class.cv (nb078_alpha_dummy_926))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_769) ≠ (nb078_alpha_dummy_925) from (by
          unfold nb078_alpha_dummy_925;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0970) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_769) ≠ (nb078_alpha_dummy_926) from (by
            unfold nb078_alpha_dummy_926;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0970) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0975 (h : Var) :
    (nb078_alpha_dummy_772 h) ∈
      (((Class.cab (nb078_alpha_dummy_927 h)
            (syn_wrex (nb078_alpha_dummy_928 h) (Class.cv (nb078_alpha_dummy_772 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_927 h))
                (syn_cphi (Class.cv (nb078_alpha_dummy_928 h))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_927 h)
            (syn_wrex (nb078_alpha_dummy_928 h) (Class.cv (nb078_alpha_dummy_772 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_927 h))
                (syn_cphi (Class.cv (nb078_alpha_dummy_928 h))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_772 h) ≠ (nb078_alpha_dummy_927 h) from (by
          unfold nb078_alpha_dummy_927;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0972 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_772 h) ≠ (nb078_alpha_dummy_928 h) from (by
            unfold nb078_alpha_dummy_928;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0972 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0976 :
    (nb078_alpha_dummy_926) ∈ (((Class.cv (nb078_alpha_dummy_926))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0977 (h : Var) :
    (nb078_alpha_dummy_928 h) ∈ (((Class.cv (nb078_alpha_dummy_928 h))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0978 :
    (nb078_alpha_dummy_933) ∈
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_933)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_933)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_933))).fv) :=
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
    (nb078_alpha_dummy_935 h) ∈
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_935 h)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_935 h)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_935 h))).fv) :=
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
    (nb078_alpha_dummy_933) ∈
      (((Class.cv (nb078_alpha_dummy_933))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0981 (h : Var) :
    (nb078_alpha_dummy_935 h) ∈
      (((Class.cv (nb078_alpha_dummy_935 h))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0982 :
    (nb078_alpha_dummy_940) ∈
      (((syn_cnin (Class.cv (nb078_alpha_dummy_940)) (Class.cv (nb078_alpha_dummy_941)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_940))
            (Class.cv (nb078_alpha_dummy_941)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0983 (h : Var) :
    (nb078_alpha_dummy_943 h) ∈
      (((syn_cnin (Class.cv (nb078_alpha_dummy_943 h))
            (Class.cv (nb078_alpha_dummy_944 h)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_943 h))
            (Class.cv (nb078_alpha_dummy_944 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0984 :
    (nb078_alpha_dummy_940) ∈
      (((Class.cv (nb078_alpha_dummy_940))).fv ∪ ((Class.cv (nb078_alpha_dummy_941))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0985 (h : Var) :
    (nb078_alpha_dummy_943 h) ∈
      (((Class.cv (nb078_alpha_dummy_943 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_944 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0986 :
    (nb078_alpha_dummy_941) ∈
      (((syn_cnin (Class.cv (nb078_alpha_dummy_940)) (Class.cv (nb078_alpha_dummy_941)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_940))
            (Class.cv (nb078_alpha_dummy_941)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0987 (h : Var) :
    (nb078_alpha_dummy_944 h) ∈
      (((syn_cnin (Class.cv (nb078_alpha_dummy_943 h))
            (Class.cv (nb078_alpha_dummy_944 h)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_943 h))
            (Class.cv (nb078_alpha_dummy_944 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0988 :
    (nb078_alpha_dummy_941) ∈
      (((Class.cv (nb078_alpha_dummy_940))).fv ∪ ((Class.cv (nb078_alpha_dummy_941))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0989 (h : Var) :
    (nb078_alpha_dummy_944 h) ∈
      (((Class.cv (nb078_alpha_dummy_943 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_944 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0990 :
    (nb078_alpha_dummy_940) ∈
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_940)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_941)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0991 (h : Var) :
    (nb078_alpha_dummy_943 h) ∈
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_943 h)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_944 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0992 :
    (nb078_alpha_dummy_940) ∈
      (((Class.cv (nb078_alpha_dummy_940))).fv ∪ ((Class.cv (nb078_alpha_dummy_940))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0993 (h : Var) :
    (nb078_alpha_dummy_943 h) ∈
      (((Class.cv (nb078_alpha_dummy_943 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_943 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0994 :
    (nb078_alpha_dummy_941) ∈
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_940)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_941)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0995 (h : Var) :
    (nb078_alpha_dummy_944 h) ∈
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_943 h)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_944 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0996 :
    (nb078_alpha_dummy_941) ∈
      (((Class.cv (nb078_alpha_dummy_941))).fv ∪ ((Class.cv (nb078_alpha_dummy_941))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0997 (h : Var) :
    (nb078_alpha_dummy_944 h) ∈
      (((Class.cv (nb078_alpha_dummy_944 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_944 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0998 :
    (nb078_alpha_dummy_768) ∈
      (((Class.cv (nb078_alpha_dummy_769))).fv ∪ ((Class.cv (nb078_alpha_dummy_768))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0999 :
    (nb078_alpha_dummy_768) ∈
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_925)
              (syn_wrex (nb078_alpha_dummy_926) (Class.cv (nb078_alpha_dummy_769))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_925))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_926)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_925)
              (syn_wrex (nb078_alpha_dummy_926) (Class.cv (nb078_alpha_dummy_768))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_925))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_926)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_768) ≠ (nb078_alpha_dummy_925) from (by
          unfold nb078_alpha_dummy_925;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0998) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_768) ≠ (nb078_alpha_dummy_926) from (by
            unfold nb078_alpha_dummy_926;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0998) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_1000 (h : Var) :
    (nb078_alpha_dummy_771 h) ∈
      (((Class.cv (nb078_alpha_dummy_772 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_771 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1001 (h : Var) :
    (nb078_alpha_dummy_771 h) ∈
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_927 h)
              (syn_wrex (nb078_alpha_dummy_928 h) (Class.cv (nb078_alpha_dummy_772 h))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_927 h))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_928 h)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_927 h)
              (syn_wrex (nb078_alpha_dummy_928 h) (Class.cv (nb078_alpha_dummy_771 h))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_927 h))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_928 h)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_771 h) ≠ (nb078_alpha_dummy_927 h) from (by
          unfold nb078_alpha_dummy_927;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1000 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_771 h) ≠ (nb078_alpha_dummy_928 h) from (by
            unfold nb078_alpha_dummy_928;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1000 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_1002 :
    (nb078_alpha_dummy_768) ∈
      (((Class.cab (nb078_alpha_dummy_925)
            (syn_wrex (nb078_alpha_dummy_926) (Class.cv (nb078_alpha_dummy_768))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_925))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_926)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_925)
            (syn_wrex (nb078_alpha_dummy_926) (Class.cv (nb078_alpha_dummy_768))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_925))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_926)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_768) ≠ (nb078_alpha_dummy_925) from (by
          unfold nb078_alpha_dummy_925;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0998) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_768) ≠ (nb078_alpha_dummy_926) from (by
            unfold nb078_alpha_dummy_926;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0998) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_1003 (h : Var) :
    (nb078_alpha_dummy_771 h) ∈
      (((Class.cab (nb078_alpha_dummy_927 h)
            (syn_wrex (nb078_alpha_dummy_928 h) (Class.cv (nb078_alpha_dummy_771 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_927 h))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_928 h)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_927 h)
            (syn_wrex (nb078_alpha_dummy_928 h) (Class.cv (nb078_alpha_dummy_771 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_927 h))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_928 h)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_771 h) ≠ (nb078_alpha_dummy_927 h) from (by
          unfold nb078_alpha_dummy_927;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1000 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_771 h) ≠ (nb078_alpha_dummy_928 h) from (by
            unfold nb078_alpha_dummy_928;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1000 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_1004 :
    (nb078_alpha_dummy_926) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_926))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1005 (h : Var) :
    (nb078_alpha_dummy_928 h) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_928 h))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1006 :
    (nb078_alpha_dummy_926) ∈
      (((syn_cphi (Class.cv (nb078_alpha_dummy_926)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_926)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1007 (h : Var) :
    (nb078_alpha_dummy_928 h) ∈
      (((syn_cphi (Class.cv (nb078_alpha_dummy_928 h)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_928 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1008 :
    (nb078_alpha_dummy_962) ∈
      (((Class.cv (nb078_alpha_dummy_962))).fv ∪ ((Class.cv (nb078_alpha_dummy_961))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1009 :
    (nb078_alpha_dummy_962) ∈
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_965)
              (syn_wrex (nb078_alpha_dummy_966) (Class.cv (nb078_alpha_dummy_962))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_965))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_966)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_965)
              (syn_wrex (nb078_alpha_dummy_966) (Class.cv (nb078_alpha_dummy_961))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_965))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_966)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_962) ≠ (nb078_alpha_dummy_965) from (by
          unfold nb078_alpha_dummy_965;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1008) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_962) ≠ (nb078_alpha_dummy_966) from (by
            unfold nb078_alpha_dummy_966;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1008) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_1010 (h : Var) :
    (nb078_alpha_dummy_964 h) ∈
      (((Class.cv (nb078_alpha_dummy_964 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_963 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1011 (h : Var) :
    (nb078_alpha_dummy_964 h) ∈
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_967 h)
              (syn_wrex (nb078_alpha_dummy_968 h) (Class.cv (nb078_alpha_dummy_964 h))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_967 h))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_968 h)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_967 h)
              (syn_wrex (nb078_alpha_dummy_968 h) (Class.cv (nb078_alpha_dummy_963 h))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_967 h))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_968 h)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_964 h) ≠ (nb078_alpha_dummy_967 h) from (by
          unfold nb078_alpha_dummy_967;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1010 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_964 h) ≠ (nb078_alpha_dummy_968 h) from (by
            unfold nb078_alpha_dummy_968;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1010 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_1012 :
    (nb078_alpha_dummy_962) ∈
      (((Class.cab (nb078_alpha_dummy_965)
            (syn_wrex (nb078_alpha_dummy_966) (Class.cv (nb078_alpha_dummy_962))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_965))
                (syn_cphi (Class.cv (nb078_alpha_dummy_966))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_965)
            (syn_wrex (nb078_alpha_dummy_966) (Class.cv (nb078_alpha_dummy_962))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_965))
                (syn_cphi (Class.cv (nb078_alpha_dummy_966))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_962) ≠ (nb078_alpha_dummy_965) from (by
          unfold nb078_alpha_dummy_965;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1008) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_962) ≠ (nb078_alpha_dummy_966) from (by
            unfold nb078_alpha_dummy_966;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1008) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_1013 (h : Var) :
    (nb078_alpha_dummy_964 h) ∈
      (((Class.cab (nb078_alpha_dummy_967 h)
            (syn_wrex (nb078_alpha_dummy_968 h) (Class.cv (nb078_alpha_dummy_964 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_967 h))
                (syn_cphi (Class.cv (nb078_alpha_dummy_968 h))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_967 h)
            (syn_wrex (nb078_alpha_dummy_968 h) (Class.cv (nb078_alpha_dummy_964 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_967 h))
                (syn_cphi (Class.cv (nb078_alpha_dummy_968 h))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_964 h) ≠ (nb078_alpha_dummy_967 h) from (by
          unfold nb078_alpha_dummy_967;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1010 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_964 h) ≠ (nb078_alpha_dummy_968 h) from (by
            unfold nb078_alpha_dummy_968;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1010 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_1014 :
    (nb078_alpha_dummy_966) ∈ (((Class.cv (nb078_alpha_dummy_966))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1015 (h : Var) :
    (nb078_alpha_dummy_968 h) ∈ (((Class.cv (nb078_alpha_dummy_968 h))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1016 :
    (nb078_alpha_dummy_973) ∈
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_973)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_973)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_973))).fv) :=
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
    (nb078_alpha_dummy_975 h) ∈
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_975 h)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_975 h)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_975 h))).fv) :=
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
    (nb078_alpha_dummy_973) ∈
      (((Class.cv (nb078_alpha_dummy_973))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1019 (h : Var) :
    (nb078_alpha_dummy_975 h) ∈
      (((Class.cv (nb078_alpha_dummy_975 h))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1020 :
    (nb078_alpha_dummy_980) ∈
      (((syn_cnin (Class.cv (nb078_alpha_dummy_980)) (Class.cv (nb078_alpha_dummy_981)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_980))
            (Class.cv (nb078_alpha_dummy_981)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1021 (h : Var) :
    (nb078_alpha_dummy_983 h) ∈
      (((syn_cnin (Class.cv (nb078_alpha_dummy_983 h))
            (Class.cv (nb078_alpha_dummy_984 h)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_983 h))
            (Class.cv (nb078_alpha_dummy_984 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1022 :
    (nb078_alpha_dummy_980) ∈
      (((Class.cv (nb078_alpha_dummy_980))).fv ∪ ((Class.cv (nb078_alpha_dummy_981))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1023 (h : Var) :
    (nb078_alpha_dummy_983 h) ∈
      (((Class.cv (nb078_alpha_dummy_983 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_984 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1024 :
    (nb078_alpha_dummy_981) ∈
      (((syn_cnin (Class.cv (nb078_alpha_dummy_980)) (Class.cv (nb078_alpha_dummy_981)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_980))
            (Class.cv (nb078_alpha_dummy_981)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1025 (h : Var) :
    (nb078_alpha_dummy_984 h) ∈
      (((syn_cnin (Class.cv (nb078_alpha_dummy_983 h))
            (Class.cv (nb078_alpha_dummy_984 h)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_983 h))
            (Class.cv (nb078_alpha_dummy_984 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1026 :
    (nb078_alpha_dummy_981) ∈
      (((Class.cv (nb078_alpha_dummy_980))).fv ∪ ((Class.cv (nb078_alpha_dummy_981))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1027 (h : Var) :
    (nb078_alpha_dummy_984 h) ∈
      (((Class.cv (nb078_alpha_dummy_983 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_984 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1028 :
    (nb078_alpha_dummy_980) ∈
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_980)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_981)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1029 (h : Var) :
    (nb078_alpha_dummy_983 h) ∈
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_983 h)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_984 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1030 :
    (nb078_alpha_dummy_980) ∈
      (((Class.cv (nb078_alpha_dummy_980))).fv ∪ ((Class.cv (nb078_alpha_dummy_980))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1031 (h : Var) :
    (nb078_alpha_dummy_983 h) ∈
      (((Class.cv (nb078_alpha_dummy_983 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_983 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1032 :
    (nb078_alpha_dummy_981) ∈
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_980)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_981)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1033 (h : Var) :
    (nb078_alpha_dummy_984 h) ∈
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_983 h)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_984 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1034 :
    (nb078_alpha_dummy_981) ∈
      (((Class.cv (nb078_alpha_dummy_981))).fv ∪ ((Class.cv (nb078_alpha_dummy_981))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1035 (h : Var) :
    (nb078_alpha_dummy_984 h) ∈
      (((Class.cv (nb078_alpha_dummy_984 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_984 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1036 :
    (nb078_alpha_dummy_961) ∈
      (((Class.cv (nb078_alpha_dummy_962))).fv ∪ ((Class.cv (nb078_alpha_dummy_961))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1037 :
    (nb078_alpha_dummy_961) ∈
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_965)
              (syn_wrex (nb078_alpha_dummy_966) (Class.cv (nb078_alpha_dummy_962))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_965))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_966)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_965)
              (syn_wrex (nb078_alpha_dummy_966) (Class.cv (nb078_alpha_dummy_961))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_965))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_966)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_961) ≠ (nb078_alpha_dummy_965) from (by
          unfold nb078_alpha_dummy_965;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1036) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_961) ≠ (nb078_alpha_dummy_966) from (by
            unfold nb078_alpha_dummy_966;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1036) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_1038 (h : Var) :
    (nb078_alpha_dummy_963 h) ∈
      (((Class.cv (nb078_alpha_dummy_964 h))).fv ∪ ((Class.cv (nb078_alpha_dummy_963 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1039 (h : Var) :
    (nb078_alpha_dummy_963 h) ∈
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_967 h)
              (syn_wrex (nb078_alpha_dummy_968 h) (Class.cv (nb078_alpha_dummy_964 h))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_967 h))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_968 h)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_967 h)
              (syn_wrex (nb078_alpha_dummy_968 h) (Class.cv (nb078_alpha_dummy_963 h))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_967 h))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_968 h)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_963 h) ≠ (nb078_alpha_dummy_967 h) from (by
          unfold nb078_alpha_dummy_967;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1038 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_963 h) ≠ (nb078_alpha_dummy_968 h) from (by
            unfold nb078_alpha_dummy_968;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1038 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_1040 :
    (nb078_alpha_dummy_961) ∈
      (((Class.cab (nb078_alpha_dummy_965)
            (syn_wrex (nb078_alpha_dummy_966) (Class.cv (nb078_alpha_dummy_961))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_965))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_966)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_965)
            (syn_wrex (nb078_alpha_dummy_966) (Class.cv (nb078_alpha_dummy_961))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_965))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_966)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_961) ≠ (nb078_alpha_dummy_965) from (by
          unfold nb078_alpha_dummy_965;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1036) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_961) ≠ (nb078_alpha_dummy_966) from (by
            unfold nb078_alpha_dummy_966;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1036) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_1041 (h : Var) :
    (nb078_alpha_dummy_963 h) ∈
      (((Class.cab (nb078_alpha_dummy_967 h)
            (syn_wrex (nb078_alpha_dummy_968 h) (Class.cv (nb078_alpha_dummy_963 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_967 h))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_968 h)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_967 h)
            (syn_wrex (nb078_alpha_dummy_968 h) (Class.cv (nb078_alpha_dummy_963 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_967 h))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_968 h)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_963 h) ≠ (nb078_alpha_dummy_967 h) from (by
          unfold nb078_alpha_dummy_967;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1038 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_963 h) ≠ (nb078_alpha_dummy_968 h) from (by
            unfold nb078_alpha_dummy_968;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1038 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_1042 :
    (nb078_alpha_dummy_966) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_966))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1043 (h : Var) :
    (nb078_alpha_dummy_968 h) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_968 h))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1044 :
    (nb078_alpha_dummy_966) ∈
      (((syn_cphi (Class.cv (nb078_alpha_dummy_966)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_966)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1045 (h : Var) :
    (nb078_alpha_dummy_968 h) ∈
      (((syn_cphi (Class.cv (nb078_alpha_dummy_968 h)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_968 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1046 :
    (nb078_alpha_dummy_002) ∈
      (((syn_ccnv (Class.cv (nb078_alpha_dummy_002)))).fv ∪ ((syn_cvv)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccnv]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1047 (h : Var) :
    h ∈ (((syn_ccnv (Class.cv h))).fv ∪ ((syn_cvv)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccnv]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1048 :
    (nb078_alpha_dummy_1006) ∈
      (((Class.cv (nb078_alpha_dummy_1006))).fv ∪ ((Class.cv (nb078_alpha_dummy_1005))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1049 :
    (nb078_alpha_dummy_1006) ∈
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_1009)
              (syn_wrex (nb078_alpha_dummy_1010) (Class.cv (nb078_alpha_dummy_1006))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_1009))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_1010)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_1009)
              (syn_wrex (nb078_alpha_dummy_1010) (Class.cv (nb078_alpha_dummy_1005))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_1009))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1010)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_1006) ≠ (nb078_alpha_dummy_1009) from (by
          unfold nb078_alpha_dummy_1009;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1048) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_1006) ≠ (nb078_alpha_dummy_1010) from (by
            unfold nb078_alpha_dummy_1010;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1048) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_1050 (h : Var) :
    (nb078_alpha_dummy_1008 h) ∈
      (((Class.cv (nb078_alpha_dummy_1008 h))).fv ∪
        ((Class.cv (nb078_alpha_dummy_1007 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1051 (h : Var) :
    (nb078_alpha_dummy_1008 h) ∈
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_1011 h)
              (syn_wrex (nb078_alpha_dummy_1012 h) (Class.cv (nb078_alpha_dummy_1008 h))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_1011 h))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_1012 h)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_1011 h)
              (syn_wrex (nb078_alpha_dummy_1012 h) (Class.cv (nb078_alpha_dummy_1007 h))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_1011 h))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1012 h)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_1008 h) ≠ (nb078_alpha_dummy_1011 h) from (by
          unfold nb078_alpha_dummy_1011;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1050 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_1008 h) ≠ (nb078_alpha_dummy_1012 h) from (by
            unfold nb078_alpha_dummy_1012;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1050 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_1052 :
    (nb078_alpha_dummy_1006) ∈
      (((Class.cab (nb078_alpha_dummy_1009)
            (syn_wrex (nb078_alpha_dummy_1010) (Class.cv (nb078_alpha_dummy_1006))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1009))
                (syn_cphi (Class.cv (nb078_alpha_dummy_1010))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_1009)
            (syn_wrex (nb078_alpha_dummy_1010) (Class.cv (nb078_alpha_dummy_1006))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1009))
                (syn_cphi (Class.cv (nb078_alpha_dummy_1010))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_1006) ≠ (nb078_alpha_dummy_1009) from (by
          unfold nb078_alpha_dummy_1009;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1048) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_1006) ≠ (nb078_alpha_dummy_1010) from (by
            unfold nb078_alpha_dummy_1010;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1048) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_1053 (h : Var) :
    (nb078_alpha_dummy_1008 h) ∈
      (((Class.cab (nb078_alpha_dummy_1011 h)
            (syn_wrex (nb078_alpha_dummy_1012 h) (Class.cv (nb078_alpha_dummy_1008 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1011 h))
                (syn_cphi (Class.cv (nb078_alpha_dummy_1012 h))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_1011 h)
            (syn_wrex (nb078_alpha_dummy_1012 h) (Class.cv (nb078_alpha_dummy_1008 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1011 h))
                (syn_cphi (Class.cv (nb078_alpha_dummy_1012 h))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_1008 h) ≠ (nb078_alpha_dummy_1011 h) from (by
          unfold nb078_alpha_dummy_1011;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1050 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_1008 h) ≠ (nb078_alpha_dummy_1012 h) from (by
            unfold nb078_alpha_dummy_1012;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1050 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_1054 :
    (nb078_alpha_dummy_1010) ∈ (((Class.cv (nb078_alpha_dummy_1010))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1055 (h : Var) :
    (nb078_alpha_dummy_1012 h) ∈ (((Class.cv (nb078_alpha_dummy_1012 h))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1056 :
    (nb078_alpha_dummy_1017) ∈
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_1017)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_1017)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_1017))).fv) :=
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
    (nb078_alpha_dummy_1019 h) ∈
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_1019 h)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_1019 h)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_1019 h))).fv) :=
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
    (nb078_alpha_dummy_1017) ∈
      (((Class.cv (nb078_alpha_dummy_1017))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1059 (h : Var) :
    (nb078_alpha_dummy_1019 h) ∈
      (((Class.cv (nb078_alpha_dummy_1019 h))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1060 :
    (nb078_alpha_dummy_1024) ∈
      (((syn_cnin (Class.cv (nb078_alpha_dummy_1024)) (Class.cv (nb078_alpha_dummy_1025)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_1024))
            (Class.cv (nb078_alpha_dummy_1025)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1061 (h : Var) :
    (nb078_alpha_dummy_1027 h) ∈
      (((syn_cnin (Class.cv (nb078_alpha_dummy_1027 h))
            (Class.cv (nb078_alpha_dummy_1028 h)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_1027 h))
            (Class.cv (nb078_alpha_dummy_1028 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1062 :
    (nb078_alpha_dummy_1024) ∈
      (((Class.cv (nb078_alpha_dummy_1024))).fv ∪ ((Class.cv (nb078_alpha_dummy_1025))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1063 (h : Var) :
    (nb078_alpha_dummy_1027 h) ∈
      (((Class.cv (nb078_alpha_dummy_1027 h))).fv ∪
        ((Class.cv (nb078_alpha_dummy_1028 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1064 :
    (nb078_alpha_dummy_1025) ∈
      (((syn_cnin (Class.cv (nb078_alpha_dummy_1024)) (Class.cv (nb078_alpha_dummy_1025)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_1024))
            (Class.cv (nb078_alpha_dummy_1025)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1065 (h : Var) :
    (nb078_alpha_dummy_1028 h) ∈
      (((syn_cnin (Class.cv (nb078_alpha_dummy_1027 h))
            (Class.cv (nb078_alpha_dummy_1028 h)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_1027 h))
            (Class.cv (nb078_alpha_dummy_1028 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1066 :
    (nb078_alpha_dummy_1025) ∈
      (((Class.cv (nb078_alpha_dummy_1024))).fv ∪ ((Class.cv (nb078_alpha_dummy_1025))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1067 (h : Var) :
    (nb078_alpha_dummy_1028 h) ∈
      (((Class.cv (nb078_alpha_dummy_1027 h))).fv ∪
        ((Class.cv (nb078_alpha_dummy_1028 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1068 :
    (nb078_alpha_dummy_1024) ∈
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_1024)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_1025)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1069 (h : Var) :
    (nb078_alpha_dummy_1027 h) ∈
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_1027 h)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_1028 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1070 :
    (nb078_alpha_dummy_1024) ∈
      (((Class.cv (nb078_alpha_dummy_1024))).fv ∪ ((Class.cv (nb078_alpha_dummy_1024))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1071 (h : Var) :
    (nb078_alpha_dummy_1027 h) ∈
      (((Class.cv (nb078_alpha_dummy_1027 h))).fv ∪
        ((Class.cv (nb078_alpha_dummy_1027 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1072 :
    (nb078_alpha_dummy_1025) ∈
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_1024)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_1025)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1073 (h : Var) :
    (nb078_alpha_dummy_1028 h) ∈
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_1027 h)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_1028 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1074 :
    (nb078_alpha_dummy_1025) ∈
      (((Class.cv (nb078_alpha_dummy_1025))).fv ∪ ((Class.cv (nb078_alpha_dummy_1025))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1075 (h : Var) :
    (nb078_alpha_dummy_1028 h) ∈
      (((Class.cv (nb078_alpha_dummy_1028 h))).fv ∪
        ((Class.cv (nb078_alpha_dummy_1028 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1076 :
    (nb078_alpha_dummy_1005) ∈
      (((Class.cv (nb078_alpha_dummy_1006))).fv ∪ ((Class.cv (nb078_alpha_dummy_1005))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1077 :
    (nb078_alpha_dummy_1005) ∈
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_1009)
              (syn_wrex (nb078_alpha_dummy_1010) (Class.cv (nb078_alpha_dummy_1006))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_1009))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_1010)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_1009)
              (syn_wrex (nb078_alpha_dummy_1010) (Class.cv (nb078_alpha_dummy_1005))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_1009))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1010)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_1005) ≠ (nb078_alpha_dummy_1009) from (by
          unfold nb078_alpha_dummy_1009;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1076) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_1005) ≠ (nb078_alpha_dummy_1010) from (by
            unfold nb078_alpha_dummy_1010;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1076) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_1078 (h : Var) :
    (nb078_alpha_dummy_1007 h) ∈
      (((Class.cv (nb078_alpha_dummy_1008 h))).fv ∪
        ((Class.cv (nb078_alpha_dummy_1007 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1079 (h : Var) :
    (nb078_alpha_dummy_1007 h) ∈
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_1011 h)
              (syn_wrex (nb078_alpha_dummy_1012 h) (Class.cv (nb078_alpha_dummy_1008 h))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_1011 h))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_1012 h)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_1011 h)
              (syn_wrex (nb078_alpha_dummy_1012 h) (Class.cv (nb078_alpha_dummy_1007 h))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_1011 h))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1012 h)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_1007 h) ≠ (nb078_alpha_dummy_1011 h) from (by
          unfold nb078_alpha_dummy_1011;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1078 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_1007 h) ≠ (nb078_alpha_dummy_1012 h) from (by
            unfold nb078_alpha_dummy_1012;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1078 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_1080 :
    (nb078_alpha_dummy_1005) ∈
      (((Class.cab (nb078_alpha_dummy_1009)
            (syn_wrex (nb078_alpha_dummy_1010) (Class.cv (nb078_alpha_dummy_1005))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1009))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1010)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_1009)
            (syn_wrex (nb078_alpha_dummy_1010) (Class.cv (nb078_alpha_dummy_1005))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1009))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1010)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_1005) ≠ (nb078_alpha_dummy_1009) from (by
          unfold nb078_alpha_dummy_1009;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1076) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_1005) ≠ (nb078_alpha_dummy_1010) from (by
            unfold nb078_alpha_dummy_1010;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1076) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_1081 (h : Var) :
    (nb078_alpha_dummy_1007 h) ∈
      (((Class.cab (nb078_alpha_dummy_1011 h)
            (syn_wrex (nb078_alpha_dummy_1012 h) (Class.cv (nb078_alpha_dummy_1007 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1011 h))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1012 h)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_1011 h)
            (syn_wrex (nb078_alpha_dummy_1012 h) (Class.cv (nb078_alpha_dummy_1007 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1011 h))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1012 h)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_1007 h) ≠ (nb078_alpha_dummy_1011 h) from (by
          unfold nb078_alpha_dummy_1011;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1078 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_1007 h) ≠ (nb078_alpha_dummy_1012 h) from (by
            unfold nb078_alpha_dummy_1012;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1078 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_1082 :
    (nb078_alpha_dummy_1010) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_1010))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1083 (h : Var) :
    (nb078_alpha_dummy_1012 h) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_1012 h))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1084 :
    (nb078_alpha_dummy_1010) ∈
      (((syn_cphi (Class.cv (nb078_alpha_dummy_1010)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_1010)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1085 (h : Var) :
    (nb078_alpha_dummy_1012 h) ∈
      (((syn_cphi (Class.cv (nb078_alpha_dummy_1012 h)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_1012 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1086 :
    (nb078_alpha_dummy_002) ∈
      (((syn_cnin (syn_crn (Class.cv (nb078_alpha_dummy_002)))
            (Class.cv (nb078_alpha_dummy_004)))).fv ∪
        ((syn_cnin (syn_crn (Class.cv (nb078_alpha_dummy_002)))
            (Class.cv (nb078_alpha_dummy_004)))).fv) :=
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
      (((syn_cnin (syn_crn (Class.cv h)) (Class.cv y))).fv ∪
        ((syn_cnin (syn_crn (Class.cv h)) (Class.cv y))).fv) :=
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
    (nb078_alpha_dummy_002) ∈
      (((syn_crn (Class.cv (nb078_alpha_dummy_002)))).fv ∪
        ((Class.cv (nb078_alpha_dummy_004))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_crn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1089 (y : Var) (h : Var) :
    h ∈ (((syn_crn (Class.cv h))).fv ∪ ((Class.cv y)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_crn]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1090 :
    (nb078_alpha_dummy_002) ∈
      (((Class.cv (nb078_alpha_dummy_002))).fv ∪ ((syn_cvv)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1091 (h : Var) : h ∈ (((Class.cv h)).fv ∪ ((syn_cvv)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1092 :
    (nb078_alpha_dummy_004) ∈
      (((syn_cnin (syn_crn (Class.cv (nb078_alpha_dummy_002)))
            (Class.cv (nb078_alpha_dummy_004)))).fv ∪
        ((syn_cnin (syn_crn (Class.cv (nb078_alpha_dummy_002)))
            (Class.cv (nb078_alpha_dummy_004)))).fv) :=
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
      (((syn_cnin (syn_crn (Class.cv h)) (Class.cv y))).fv ∪
        ((syn_cnin (syn_crn (Class.cv h)) (Class.cv y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1094 :
    (nb078_alpha_dummy_004) ∈
      (((syn_crn (Class.cv (nb078_alpha_dummy_002)))).fv ∪
        ((Class.cv (nb078_alpha_dummy_004))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1095 (y : Var) (h : Var) :
    y ∈ (((syn_crn (Class.cv h))).fv ∪ ((Class.cv y)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1096 :
    (nb078_alpha_dummy_1049) ∈
      (({(nb078_alpha_dummy_1049)} : Finset Var) ∪ ({(nb078_alpha_dummy_1050)} : Finset Var) ∪
        ((syn_wex (nb078_alpha_dummy_1051) (syn_wa (syn_wbr (Class.cv (nb078_alpha_dummy_1049))
                (syn_ccnv (syn_ccnv (Class.cv (nb078_alpha_dummy_002))))
                (Class.cv (nb078_alpha_dummy_1051)))
              (syn_wbr (Class.cv (nb078_alpha_dummy_1051))
                (syn_ccnv (Class.cv (nb078_alpha_dummy_002)))
                (Class.cv (nb078_alpha_dummy_1050)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1097 (h : Var) :
    (nb078_alpha_dummy_1052 h) ∈
      (({(nb078_alpha_dummy_1052 h)} : Finset Var) ∪
          ({(nb078_alpha_dummy_1053 h)} : Finset Var) ∪ ((syn_wex (nb078_alpha_dummy_1054 h)
            (syn_wa (syn_wbr (Class.cv (nb078_alpha_dummy_1052 h))
                (syn_ccnv (syn_ccnv (Class.cv h))) (Class.cv (nb078_alpha_dummy_1054 h)))
              (syn_wbr (Class.cv (nb078_alpha_dummy_1054 h)) (syn_ccnv (Class.cv h))
                (Class.cv (nb078_alpha_dummy_1053 h)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1098 :
    (nb078_alpha_dummy_1050) ∈
      (({(nb078_alpha_dummy_1049)} : Finset Var) ∪ ({(nb078_alpha_dummy_1050)} : Finset Var) ∪
        ((syn_wex (nb078_alpha_dummy_1051) (syn_wa (syn_wbr (Class.cv (nb078_alpha_dummy_1049))
                (syn_ccnv (syn_ccnv (Class.cv (nb078_alpha_dummy_002))))
                (Class.cv (nb078_alpha_dummy_1051)))
              (syn_wbr (Class.cv (nb078_alpha_dummy_1051))
                (syn_ccnv (Class.cv (nb078_alpha_dummy_002)))
                (Class.cv (nb078_alpha_dummy_1050)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1099 (h : Var) :
    (nb078_alpha_dummy_1053 h) ∈
      (({(nb078_alpha_dummy_1052 h)} : Finset Var) ∪
          ({(nb078_alpha_dummy_1053 h)} : Finset Var) ∪ ((syn_wex (nb078_alpha_dummy_1054 h)
            (syn_wa (syn_wbr (Class.cv (nb078_alpha_dummy_1052 h))
                (syn_ccnv (syn_ccnv (Class.cv h))) (Class.cv (nb078_alpha_dummy_1054 h)))
              (syn_wbr (Class.cv (nb078_alpha_dummy_1054 h)) (syn_ccnv (Class.cv h))
                (Class.cv (nb078_alpha_dummy_1053 h)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1100 :
    (nb078_alpha_dummy_1049) ∈
      (((Class.cv (nb078_alpha_dummy_1049))).fv ∪ ((Class.cv (nb078_alpha_dummy_1050))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1101 :
    (nb078_alpha_dummy_1049) ∈
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_1057)
              (syn_wrex (nb078_alpha_dummy_1058) (Class.cv (nb078_alpha_dummy_1049))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_1057))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_1058)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_1057)
              (syn_wrex (nb078_alpha_dummy_1058) (Class.cv (nb078_alpha_dummy_1050))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_1057))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1058)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_1049) ≠ (nb078_alpha_dummy_1057) from (by
          unfold nb078_alpha_dummy_1057;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1100) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_1049) ≠ (nb078_alpha_dummy_1058) from (by
            unfold nb078_alpha_dummy_1058;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1100) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_1102 (h : Var) :
    (nb078_alpha_dummy_1052 h) ∈
      (((Class.cv (nb078_alpha_dummy_1052 h))).fv ∪
        ((Class.cv (nb078_alpha_dummy_1053 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1103 (h : Var) :
    (nb078_alpha_dummy_1052 h) ∈
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_1059 h)
              (syn_wrex (nb078_alpha_dummy_1060 h) (Class.cv (nb078_alpha_dummy_1052 h))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_1059 h))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_1060 h)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_1059 h)
              (syn_wrex (nb078_alpha_dummy_1060 h) (Class.cv (nb078_alpha_dummy_1053 h))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_1059 h))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1060 h)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_1052 h) ≠ (nb078_alpha_dummy_1059 h) from (by
          unfold nb078_alpha_dummy_1059;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1102 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_1052 h) ≠ (nb078_alpha_dummy_1060 h) from (by
            unfold nb078_alpha_dummy_1060;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1102 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_1104 :
    (nb078_alpha_dummy_1049) ∈
      (((Class.cab (nb078_alpha_dummy_1057)
            (syn_wrex (nb078_alpha_dummy_1058) (Class.cv (nb078_alpha_dummy_1049))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1057))
                (syn_cphi (Class.cv (nb078_alpha_dummy_1058))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_1057)
            (syn_wrex (nb078_alpha_dummy_1058) (Class.cv (nb078_alpha_dummy_1049))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1057))
                (syn_cphi (Class.cv (nb078_alpha_dummy_1058))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_1049) ≠ (nb078_alpha_dummy_1057) from (by
          unfold nb078_alpha_dummy_1057;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1100) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_1049) ≠ (nb078_alpha_dummy_1058) from (by
            unfold nb078_alpha_dummy_1058;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1100) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_1105 (h : Var) :
    (nb078_alpha_dummy_1052 h) ∈
      (((Class.cab (nb078_alpha_dummy_1059 h)
            (syn_wrex (nb078_alpha_dummy_1060 h) (Class.cv (nb078_alpha_dummy_1052 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1059 h))
                (syn_cphi (Class.cv (nb078_alpha_dummy_1060 h))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_1059 h)
            (syn_wrex (nb078_alpha_dummy_1060 h) (Class.cv (nb078_alpha_dummy_1052 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1059 h))
                (syn_cphi (Class.cv (nb078_alpha_dummy_1060 h))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_1052 h) ≠ (nb078_alpha_dummy_1059 h) from (by
          unfold nb078_alpha_dummy_1059;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1102 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_1052 h) ≠ (nb078_alpha_dummy_1060 h) from (by
            unfold nb078_alpha_dummy_1060;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1102 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_1106 :
    (nb078_alpha_dummy_1058) ∈ (((Class.cv (nb078_alpha_dummy_1058))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1107 (h : Var) :
    (nb078_alpha_dummy_1060 h) ∈ (((Class.cv (nb078_alpha_dummy_1060 h))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1108 :
    (nb078_alpha_dummy_1065) ∈
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_1065)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_1065)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_1065))).fv) :=
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
    (nb078_alpha_dummy_1067 h) ∈
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_1067 h)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_1067 h)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_1067 h))).fv) :=
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
    (nb078_alpha_dummy_1065) ∈
      (((Class.cv (nb078_alpha_dummy_1065))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1111 (h : Var) :
    (nb078_alpha_dummy_1067 h) ∈
      (((Class.cv (nb078_alpha_dummy_1067 h))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1112 :
    (nb078_alpha_dummy_1072) ∈
      (((syn_cnin (Class.cv (nb078_alpha_dummy_1072)) (Class.cv (nb078_alpha_dummy_1073)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_1072))
            (Class.cv (nb078_alpha_dummy_1073)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1113 (h : Var) :
    (nb078_alpha_dummy_1075 h) ∈
      (((syn_cnin (Class.cv (nb078_alpha_dummy_1075 h))
            (Class.cv (nb078_alpha_dummy_1076 h)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_1075 h))
            (Class.cv (nb078_alpha_dummy_1076 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1114 :
    (nb078_alpha_dummy_1072) ∈
      (((Class.cv (nb078_alpha_dummy_1072))).fv ∪ ((Class.cv (nb078_alpha_dummy_1073))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1115 (h : Var) :
    (nb078_alpha_dummy_1075 h) ∈
      (((Class.cv (nb078_alpha_dummy_1075 h))).fv ∪
        ((Class.cv (nb078_alpha_dummy_1076 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1116 :
    (nb078_alpha_dummy_1073) ∈
      (((syn_cnin (Class.cv (nb078_alpha_dummy_1072)) (Class.cv (nb078_alpha_dummy_1073)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_1072))
            (Class.cv (nb078_alpha_dummy_1073)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1117 (h : Var) :
    (nb078_alpha_dummy_1076 h) ∈
      (((syn_cnin (Class.cv (nb078_alpha_dummy_1075 h))
            (Class.cv (nb078_alpha_dummy_1076 h)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_1075 h))
            (Class.cv (nb078_alpha_dummy_1076 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1118 :
    (nb078_alpha_dummy_1073) ∈
      (((Class.cv (nb078_alpha_dummy_1072))).fv ∪ ((Class.cv (nb078_alpha_dummy_1073))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1119 (h : Var) :
    (nb078_alpha_dummy_1076 h) ∈
      (((Class.cv (nb078_alpha_dummy_1075 h))).fv ∪
        ((Class.cv (nb078_alpha_dummy_1076 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1120 :
    (nb078_alpha_dummy_1072) ∈
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_1072)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_1073)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1121 (h : Var) :
    (nb078_alpha_dummy_1075 h) ∈
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_1075 h)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_1076 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1122 :
    (nb078_alpha_dummy_1072) ∈
      (((Class.cv (nb078_alpha_dummy_1072))).fv ∪ ((Class.cv (nb078_alpha_dummy_1072))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1123 (h : Var) :
    (nb078_alpha_dummy_1075 h) ∈
      (((Class.cv (nb078_alpha_dummy_1075 h))).fv ∪
        ((Class.cv (nb078_alpha_dummy_1075 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1124 :
    (nb078_alpha_dummy_1073) ∈
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_1072)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_1073)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1125 (h : Var) :
    (nb078_alpha_dummy_1076 h) ∈
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_1075 h)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_1076 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1126 :
    (nb078_alpha_dummy_1073) ∈
      (((Class.cv (nb078_alpha_dummy_1073))).fv ∪ ((Class.cv (nb078_alpha_dummy_1073))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1127 (h : Var) :
    (nb078_alpha_dummy_1076 h) ∈
      (((Class.cv (nb078_alpha_dummy_1076 h))).fv ∪
        ((Class.cv (nb078_alpha_dummy_1076 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1128 :
    (nb078_alpha_dummy_1050) ∈
      (((Class.cv (nb078_alpha_dummy_1049))).fv ∪ ((Class.cv (nb078_alpha_dummy_1050))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1129 :
    (nb078_alpha_dummy_1050) ∈
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_1057)
              (syn_wrex (nb078_alpha_dummy_1058) (Class.cv (nb078_alpha_dummy_1049))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_1057))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_1058)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_1057)
              (syn_wrex (nb078_alpha_dummy_1058) (Class.cv (nb078_alpha_dummy_1050))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_1057))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1058)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_1050) ≠ (nb078_alpha_dummy_1057) from (by
          unfold nb078_alpha_dummy_1057;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1128) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_1050) ≠ (nb078_alpha_dummy_1058) from (by
            unfold nb078_alpha_dummy_1058;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1128) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_1130 (h : Var) :
    (nb078_alpha_dummy_1053 h) ∈
      (((Class.cv (nb078_alpha_dummy_1052 h))).fv ∪
        ((Class.cv (nb078_alpha_dummy_1053 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1131 (h : Var) :
    (nb078_alpha_dummy_1053 h) ∈
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_1059 h)
              (syn_wrex (nb078_alpha_dummy_1060 h) (Class.cv (nb078_alpha_dummy_1052 h))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_1059 h))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_1060 h)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_1059 h)
              (syn_wrex (nb078_alpha_dummy_1060 h) (Class.cv (nb078_alpha_dummy_1053 h))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_1059 h))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1060 h)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_1053 h) ≠ (nb078_alpha_dummy_1059 h) from (by
          unfold nb078_alpha_dummy_1059;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1130 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_1053 h) ≠ (nb078_alpha_dummy_1060 h) from (by
            unfold nb078_alpha_dummy_1060;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1130 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_1132 :
    (nb078_alpha_dummy_1050) ∈
      (((Class.cab (nb078_alpha_dummy_1057)
            (syn_wrex (nb078_alpha_dummy_1058) (Class.cv (nb078_alpha_dummy_1050))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1057))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1058)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_1057)
            (syn_wrex (nb078_alpha_dummy_1058) (Class.cv (nb078_alpha_dummy_1050))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1057))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1058)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_1050) ≠ (nb078_alpha_dummy_1057) from (by
          unfold nb078_alpha_dummy_1057;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1128) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_1050) ≠ (nb078_alpha_dummy_1058) from (by
            unfold nb078_alpha_dummy_1058;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1128) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_1133 (h : Var) :
    (nb078_alpha_dummy_1053 h) ∈
      (((Class.cab (nb078_alpha_dummy_1059 h)
            (syn_wrex (nb078_alpha_dummy_1060 h) (Class.cv (nb078_alpha_dummy_1053 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1059 h))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1060 h)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_1059 h)
            (syn_wrex (nb078_alpha_dummy_1060 h) (Class.cv (nb078_alpha_dummy_1053 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1059 h))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1060 h)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_1053 h) ≠ (nb078_alpha_dummy_1059 h) from (by
          unfold nb078_alpha_dummy_1059;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1130 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_1053 h) ≠ (nb078_alpha_dummy_1060 h) from (by
            unfold nb078_alpha_dummy_1060;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1130 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_1134 :
    (nb078_alpha_dummy_1058) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_1058))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1135 (h : Var) :
    (nb078_alpha_dummy_1060 h) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_1060 h))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1136 :
    (nb078_alpha_dummy_1058) ∈
      (((syn_cphi (Class.cv (nb078_alpha_dummy_1058)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_1058)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1137 (h : Var) :
    (nb078_alpha_dummy_1060 h) ∈
      (((syn_cphi (Class.cv (nb078_alpha_dummy_1060 h)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_1060 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1138 :
    (nb078_alpha_dummy_1049) ∈
      (((Class.cv (nb078_alpha_dummy_1049))).fv ∪ ((Class.cv (nb078_alpha_dummy_1051))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1139 :
    (nb078_alpha_dummy_1049) ∈
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_1093)
              (syn_wrex (nb078_alpha_dummy_1094) (Class.cv (nb078_alpha_dummy_1049))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_1093))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_1094)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_1093)
              (syn_wrex (nb078_alpha_dummy_1094) (Class.cv (nb078_alpha_dummy_1051))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_1093))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1094)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_1049) ≠ (nb078_alpha_dummy_1093) from (by
          unfold nb078_alpha_dummy_1093;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1138) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_1049) ≠ (nb078_alpha_dummy_1094) from (by
            unfold nb078_alpha_dummy_1094;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1138) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_1140 (h : Var) :
    (nb078_alpha_dummy_1052 h) ∈
      (((Class.cv (nb078_alpha_dummy_1052 h))).fv ∪
        ((Class.cv (nb078_alpha_dummy_1054 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1141 (h : Var) :
    (nb078_alpha_dummy_1052 h) ∈
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_1095 h)
              (syn_wrex (nb078_alpha_dummy_1096 h) (Class.cv (nb078_alpha_dummy_1052 h))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_1095 h))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_1096 h)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_1095 h)
              (syn_wrex (nb078_alpha_dummy_1096 h) (Class.cv (nb078_alpha_dummy_1054 h))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_1095 h))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1096 h)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_1052 h) ≠ (nb078_alpha_dummy_1095 h) from (by
          unfold nb078_alpha_dummy_1095;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1140 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_1052 h) ≠ (nb078_alpha_dummy_1096 h) from (by
            unfold nb078_alpha_dummy_1096;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1140 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_1142 :
    (nb078_alpha_dummy_1049) ∈
      (((Class.cab (nb078_alpha_dummy_1093)
            (syn_wrex (nb078_alpha_dummy_1094) (Class.cv (nb078_alpha_dummy_1049))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1093))
                (syn_cphi (Class.cv (nb078_alpha_dummy_1094))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_1093)
            (syn_wrex (nb078_alpha_dummy_1094) (Class.cv (nb078_alpha_dummy_1049))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1093))
                (syn_cphi (Class.cv (nb078_alpha_dummy_1094))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_1049) ≠ (nb078_alpha_dummy_1093) from (by
          unfold nb078_alpha_dummy_1093;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1138) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_1049) ≠ (nb078_alpha_dummy_1094) from (by
            unfold nb078_alpha_dummy_1094;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1138) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_1143 (h : Var) :
    (nb078_alpha_dummy_1052 h) ∈
      (((Class.cab (nb078_alpha_dummy_1095 h)
            (syn_wrex (nb078_alpha_dummy_1096 h) (Class.cv (nb078_alpha_dummy_1052 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1095 h))
                (syn_cphi (Class.cv (nb078_alpha_dummy_1096 h))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_1095 h)
            (syn_wrex (nb078_alpha_dummy_1096 h) (Class.cv (nb078_alpha_dummy_1052 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1095 h))
                (syn_cphi (Class.cv (nb078_alpha_dummy_1096 h))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_1052 h) ≠ (nb078_alpha_dummy_1095 h) from (by
          unfold nb078_alpha_dummy_1095;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1140 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_1052 h) ≠ (nb078_alpha_dummy_1096 h) from (by
            unfold nb078_alpha_dummy_1096;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1140 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_1144 :
    (nb078_alpha_dummy_1094) ∈ (((Class.cv (nb078_alpha_dummy_1094))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1145 (h : Var) :
    (nb078_alpha_dummy_1096 h) ∈ (((Class.cv (nb078_alpha_dummy_1096 h))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1146 :
    (nb078_alpha_dummy_1101) ∈
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_1101)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_1101)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_1101))).fv) :=
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
    (nb078_alpha_dummy_1103 h) ∈
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_1103 h)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_1103 h)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_1103 h))).fv) :=
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
    (nb078_alpha_dummy_1101) ∈
      (((Class.cv (nb078_alpha_dummy_1101))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1149 (h : Var) :
    (nb078_alpha_dummy_1103 h) ∈
      (((Class.cv (nb078_alpha_dummy_1103 h))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1150 :
    (nb078_alpha_dummy_1108) ∈
      (((syn_cnin (Class.cv (nb078_alpha_dummy_1108)) (Class.cv (nb078_alpha_dummy_1109)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_1108))
            (Class.cv (nb078_alpha_dummy_1109)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1151 (h : Var) :
    (nb078_alpha_dummy_1111 h) ∈
      (((syn_cnin (Class.cv (nb078_alpha_dummy_1111 h))
            (Class.cv (nb078_alpha_dummy_1112 h)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_1111 h))
            (Class.cv (nb078_alpha_dummy_1112 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1152 :
    (nb078_alpha_dummy_1108) ∈
      (((Class.cv (nb078_alpha_dummy_1108))).fv ∪ ((Class.cv (nb078_alpha_dummy_1109))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1153 (h : Var) :
    (nb078_alpha_dummy_1111 h) ∈
      (((Class.cv (nb078_alpha_dummy_1111 h))).fv ∪
        ((Class.cv (nb078_alpha_dummy_1112 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1154 :
    (nb078_alpha_dummy_1109) ∈
      (((syn_cnin (Class.cv (nb078_alpha_dummy_1108)) (Class.cv (nb078_alpha_dummy_1109)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_1108))
            (Class.cv (nb078_alpha_dummy_1109)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1155 (h : Var) :
    (nb078_alpha_dummy_1112 h) ∈
      (((syn_cnin (Class.cv (nb078_alpha_dummy_1111 h))
            (Class.cv (nb078_alpha_dummy_1112 h)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_1111 h))
            (Class.cv (nb078_alpha_dummy_1112 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1156 :
    (nb078_alpha_dummy_1109) ∈
      (((Class.cv (nb078_alpha_dummy_1108))).fv ∪ ((Class.cv (nb078_alpha_dummy_1109))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1157 (h : Var) :
    (nb078_alpha_dummy_1112 h) ∈
      (((Class.cv (nb078_alpha_dummy_1111 h))).fv ∪
        ((Class.cv (nb078_alpha_dummy_1112 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1158 :
    (nb078_alpha_dummy_1108) ∈
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_1108)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_1109)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1159 (h : Var) :
    (nb078_alpha_dummy_1111 h) ∈
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_1111 h)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_1112 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1160 :
    (nb078_alpha_dummy_1108) ∈
      (((Class.cv (nb078_alpha_dummy_1108))).fv ∪ ((Class.cv (nb078_alpha_dummy_1108))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1161 (h : Var) :
    (nb078_alpha_dummy_1111 h) ∈
      (((Class.cv (nb078_alpha_dummy_1111 h))).fv ∪
        ((Class.cv (nb078_alpha_dummy_1111 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1162 :
    (nb078_alpha_dummy_1109) ∈
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_1108)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_1109)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1163 (h : Var) :
    (nb078_alpha_dummy_1112 h) ∈
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_1111 h)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_1112 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1164 :
    (nb078_alpha_dummy_1109) ∈
      (((Class.cv (nb078_alpha_dummy_1109))).fv ∪ ((Class.cv (nb078_alpha_dummy_1109))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
