/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C078C001Block004

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C078C001Part022`. -/


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

theorem nb078_support_mem_0033 :
    (nb078_alpha_dummy_010) ∈
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_017)
              (syn_wrex (nb078_alpha_dummy_018) (Class.cv (nb078_alpha_dummy_009))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_017))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_018)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_017)
              (syn_wrex (nb078_alpha_dummy_018) (Class.cv (nb078_alpha_dummy_010))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_017))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_018)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_010) ≠ (nb078_alpha_dummy_017) from (by
          unfold nb078_alpha_dummy_017;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0032) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_010) ≠ (nb078_alpha_dummy_018) from (by
            unfold nb078_alpha_dummy_018;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0032) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0034 (f : Var) :
    (nb078_alpha_dummy_013 f) ∈
      (((Class.cv (nb078_alpha_dummy_012 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_013 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0035 (f : Var) :
    (nb078_alpha_dummy_013 f) ∈
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_019 f)
              (syn_wrex (nb078_alpha_dummy_020 f) (Class.cv (nb078_alpha_dummy_012 f))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_019 f))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_020 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_019 f)
              (syn_wrex (nb078_alpha_dummy_020 f) (Class.cv (nb078_alpha_dummy_013 f))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_019 f))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_020 f)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_013 f) ≠ (nb078_alpha_dummy_019 f) from (by
          unfold nb078_alpha_dummy_019;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0034 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_013 f) ≠ (nb078_alpha_dummy_020 f) from (by
            unfold nb078_alpha_dummy_020;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0034 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0036 :
    (nb078_alpha_dummy_010) ∈
      (((Class.cab (nb078_alpha_dummy_017)
            (syn_wrex (nb078_alpha_dummy_018) (Class.cv (nb078_alpha_dummy_010))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_017))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_018)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_017)
            (syn_wrex (nb078_alpha_dummy_018) (Class.cv (nb078_alpha_dummy_010))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_017))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_018)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_010) ≠ (nb078_alpha_dummy_017) from (by
          unfold nb078_alpha_dummy_017;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0032) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_010) ≠ (nb078_alpha_dummy_018) from (by
            unfold nb078_alpha_dummy_018;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0032) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0037 (f : Var) :
    (nb078_alpha_dummy_013 f) ∈
      (((Class.cab (nb078_alpha_dummy_019 f)
            (syn_wrex (nb078_alpha_dummy_020 f) (Class.cv (nb078_alpha_dummy_013 f))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_019 f))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_020 f)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_019 f)
            (syn_wrex (nb078_alpha_dummy_020 f) (Class.cv (nb078_alpha_dummy_013 f))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_019 f))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_020 f)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_013 f) ≠ (nb078_alpha_dummy_019 f) from (by
          unfold nb078_alpha_dummy_019;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0034 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_013 f) ≠ (nb078_alpha_dummy_020 f) from (by
            unfold nb078_alpha_dummy_020;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0034 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0038 :
    (nb078_alpha_dummy_018) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_018))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0039 (f : Var) :
    (nb078_alpha_dummy_020 f) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_020 f))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0040 :
    (nb078_alpha_dummy_018) ∈
      (((syn_cphi (Class.cv (nb078_alpha_dummy_018)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_018)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0041 (f : Var) :
    (nb078_alpha_dummy_020 f) ∈
      (((syn_cphi (Class.cv (nb078_alpha_dummy_020 f)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_020 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0042 :
    (nb078_alpha_dummy_009) ∈
      (((Class.cv (nb078_alpha_dummy_009))).fv ∪ ((Class.cv (nb078_alpha_dummy_011))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0043 :
    (nb078_alpha_dummy_009) ∈
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_053)
              (syn_wrex (nb078_alpha_dummy_054) (Class.cv (nb078_alpha_dummy_009))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_053))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_054)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_053)
              (syn_wrex (nb078_alpha_dummy_054) (Class.cv (nb078_alpha_dummy_011))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_053))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_054)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_009) ≠ (nb078_alpha_dummy_053) from (by
          unfold nb078_alpha_dummy_053;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0042) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_009) ≠ (nb078_alpha_dummy_054) from (by
            unfold nb078_alpha_dummy_054;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0042) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0044 (f : Var) :
    (nb078_alpha_dummy_012 f) ∈
      (((Class.cv (nb078_alpha_dummy_012 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_014 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0045 (f : Var) :
    (nb078_alpha_dummy_012 f) ∈
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_055 f)
              (syn_wrex (nb078_alpha_dummy_056 f) (Class.cv (nb078_alpha_dummy_012 f))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_055 f))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_056 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_055 f)
              (syn_wrex (nb078_alpha_dummy_056 f) (Class.cv (nb078_alpha_dummy_014 f))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_055 f))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_056 f)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_012 f) ≠ (nb078_alpha_dummy_055 f) from (by
          unfold nb078_alpha_dummy_055;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0044 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_012 f) ≠ (nb078_alpha_dummy_056 f) from (by
            unfold nb078_alpha_dummy_056;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0044 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0046 :
    (nb078_alpha_dummy_009) ∈
      (((Class.cab (nb078_alpha_dummy_053)
            (syn_wrex (nb078_alpha_dummy_054) (Class.cv (nb078_alpha_dummy_009))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_053))
                (syn_cphi (Class.cv (nb078_alpha_dummy_054))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_053)
            (syn_wrex (nb078_alpha_dummy_054) (Class.cv (nb078_alpha_dummy_009))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_053))
                (syn_cphi (Class.cv (nb078_alpha_dummy_054))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_009) ≠ (nb078_alpha_dummy_053) from (by
          unfold nb078_alpha_dummy_053;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0042) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_009) ≠ (nb078_alpha_dummy_054) from (by
            unfold nb078_alpha_dummy_054;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0042) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0047 (f : Var) :
    (nb078_alpha_dummy_012 f) ∈
      (((Class.cab (nb078_alpha_dummy_055 f)
            (syn_wrex (nb078_alpha_dummy_056 f) (Class.cv (nb078_alpha_dummy_012 f))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_055 f))
                (syn_cphi (Class.cv (nb078_alpha_dummy_056 f))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_055 f)
            (syn_wrex (nb078_alpha_dummy_056 f) (Class.cv (nb078_alpha_dummy_012 f))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_055 f))
                (syn_cphi (Class.cv (nb078_alpha_dummy_056 f))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_012 f) ≠ (nb078_alpha_dummy_055 f) from (by
          unfold nb078_alpha_dummy_055;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0044 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_012 f) ≠ (nb078_alpha_dummy_056 f) from (by
            unfold nb078_alpha_dummy_056;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0044 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0048 :
    (nb078_alpha_dummy_054) ∈ (((Class.cv (nb078_alpha_dummy_054))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0049 (f : Var) :
    (nb078_alpha_dummy_056 f) ∈ (((Class.cv (nb078_alpha_dummy_056 f))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0050 :
    (nb078_alpha_dummy_061) ∈
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_061)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_061)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_061))).fv) :=
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

theorem nb078_support_mem_0051 (f : Var) :
    (nb078_alpha_dummy_063 f) ∈
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_063 f)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_063 f)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_063 f))).fv) :=
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

theorem nb078_support_mem_0052 :
    (nb078_alpha_dummy_061) ∈
      (((Class.cv (nb078_alpha_dummy_061))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0053 (f : Var) :
    (nb078_alpha_dummy_063 f) ∈
      (((Class.cv (nb078_alpha_dummy_063 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0054 :
    (nb078_alpha_dummy_068) ∈
      (((syn_cnin (Class.cv (nb078_alpha_dummy_068)) (Class.cv (nb078_alpha_dummy_069)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_068))
            (Class.cv (nb078_alpha_dummy_069)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0055 (f : Var) :
    (nb078_alpha_dummy_071 f) ∈
      (((syn_cnin (Class.cv (nb078_alpha_dummy_071 f))
            (Class.cv (nb078_alpha_dummy_072 f)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_071 f))
            (Class.cv (nb078_alpha_dummy_072 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0056 :
    (nb078_alpha_dummy_068) ∈
      (((Class.cv (nb078_alpha_dummy_068))).fv ∪ ((Class.cv (nb078_alpha_dummy_069))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0057 (f : Var) :
    (nb078_alpha_dummy_071 f) ∈
      (((Class.cv (nb078_alpha_dummy_071 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_072 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0058 :
    (nb078_alpha_dummy_069) ∈
      (((syn_cnin (Class.cv (nb078_alpha_dummy_068)) (Class.cv (nb078_alpha_dummy_069)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_068))
            (Class.cv (nb078_alpha_dummy_069)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0059 (f : Var) :
    (nb078_alpha_dummy_072 f) ∈
      (((syn_cnin (Class.cv (nb078_alpha_dummy_071 f))
            (Class.cv (nb078_alpha_dummy_072 f)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_071 f))
            (Class.cv (nb078_alpha_dummy_072 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0060 :
    (nb078_alpha_dummy_069) ∈
      (((Class.cv (nb078_alpha_dummy_068))).fv ∪ ((Class.cv (nb078_alpha_dummy_069))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0061 (f : Var) :
    (nb078_alpha_dummy_072 f) ∈
      (((Class.cv (nb078_alpha_dummy_071 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_072 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0062 :
    (nb078_alpha_dummy_068) ∈
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_068)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_069)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0063 (f : Var) :
    (nb078_alpha_dummy_071 f) ∈
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_071 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_072 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0064 :
    (nb078_alpha_dummy_068) ∈
      (((Class.cv (nb078_alpha_dummy_068))).fv ∪ ((Class.cv (nb078_alpha_dummy_068))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0065 (f : Var) :
    (nb078_alpha_dummy_071 f) ∈
      (((Class.cv (nb078_alpha_dummy_071 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_071 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0066 :
    (nb078_alpha_dummy_069) ∈
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_068)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_069)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0067 (f : Var) :
    (nb078_alpha_dummy_072 f) ∈
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_071 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_072 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0068 :
    (nb078_alpha_dummy_069) ∈
      (((Class.cv (nb078_alpha_dummy_069))).fv ∪ ((Class.cv (nb078_alpha_dummy_069))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0069 (f : Var) :
    (nb078_alpha_dummy_072 f) ∈
      (((Class.cv (nb078_alpha_dummy_072 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_072 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0070 :
    (nb078_alpha_dummy_011) ∈
      (((Class.cv (nb078_alpha_dummy_009))).fv ∪ ((Class.cv (nb078_alpha_dummy_011))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0071 :
    (nb078_alpha_dummy_011) ∈
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_053)
              (syn_wrex (nb078_alpha_dummy_054) (Class.cv (nb078_alpha_dummy_009))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_053))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_054)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_053)
              (syn_wrex (nb078_alpha_dummy_054) (Class.cv (nb078_alpha_dummy_011))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_053))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_054)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_011) ≠ (nb078_alpha_dummy_053) from (by
          unfold nb078_alpha_dummy_053;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0070) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_011) ≠ (nb078_alpha_dummy_054) from (by
            unfold nb078_alpha_dummy_054;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0070) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0072 (f : Var) :
    (nb078_alpha_dummy_014 f) ∈
      (((Class.cv (nb078_alpha_dummy_012 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_014 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0073 (f : Var) :
    (nb078_alpha_dummy_014 f) ∈
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_055 f)
              (syn_wrex (nb078_alpha_dummy_056 f) (Class.cv (nb078_alpha_dummy_012 f))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_055 f))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_056 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_055 f)
              (syn_wrex (nb078_alpha_dummy_056 f) (Class.cv (nb078_alpha_dummy_014 f))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_055 f))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_056 f)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_014 f) ≠ (nb078_alpha_dummy_055 f) from (by
          unfold nb078_alpha_dummy_055;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0072 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_014 f) ≠ (nb078_alpha_dummy_056 f) from (by
            unfold nb078_alpha_dummy_056;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0072 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0074 :
    (nb078_alpha_dummy_011) ∈
      (((Class.cab (nb078_alpha_dummy_053)
            (syn_wrex (nb078_alpha_dummy_054) (Class.cv (nb078_alpha_dummy_011))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_053))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_054)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_053)
            (syn_wrex (nb078_alpha_dummy_054) (Class.cv (nb078_alpha_dummy_011))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_053))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_054)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_011) ≠ (nb078_alpha_dummy_053) from (by
          unfold nb078_alpha_dummy_053;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0070) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_011) ≠ (nb078_alpha_dummy_054) from (by
            unfold nb078_alpha_dummy_054;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0070) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0075 (f : Var) :
    (nb078_alpha_dummy_014 f) ∈
      (((Class.cab (nb078_alpha_dummy_055 f)
            (syn_wrex (nb078_alpha_dummy_056 f) (Class.cv (nb078_alpha_dummy_014 f))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_055 f))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_056 f)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_055 f)
            (syn_wrex (nb078_alpha_dummy_056 f) (Class.cv (nb078_alpha_dummy_014 f))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_055 f))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_056 f)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_014 f) ≠ (nb078_alpha_dummy_055 f) from (by
          unfold nb078_alpha_dummy_055;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0072 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_014 f) ≠ (nb078_alpha_dummy_056 f) from (by
            unfold nb078_alpha_dummy_056;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0072 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0076 :
    (nb078_alpha_dummy_054) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_054))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0077 (f : Var) :
    (nb078_alpha_dummy_056 f) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_056 f))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0078 :
    (nb078_alpha_dummy_054) ∈
      (((syn_cphi (Class.cv (nb078_alpha_dummy_054)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_054)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0079 (f : Var) :
    (nb078_alpha_dummy_056 f) ∈
      (((syn_cphi (Class.cv (nb078_alpha_dummy_056 f)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_056 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0080 :
    (nb078_alpha_dummy_089) ∈
      (({(nb078_alpha_dummy_089)} : Finset Var) ∪ ({(nb078_alpha_dummy_090)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb078_alpha_dummy_090)) (Class.cv (nb078_alpha_dummy_000))
            (Class.cv (nb078_alpha_dummy_089)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0081 (f : Var) :
    (nb078_alpha_dummy_091 f) ∈
      (({(nb078_alpha_dummy_091 f)} : Finset Var) ∪ ({(nb078_alpha_dummy_092 f)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb078_alpha_dummy_092 f)) (Class.cv f)
            (Class.cv (nb078_alpha_dummy_091 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0082 :
    (nb078_alpha_dummy_090) ∈
      (({(nb078_alpha_dummy_089)} : Finset Var) ∪ ({(nb078_alpha_dummy_090)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb078_alpha_dummy_090)) (Class.cv (nb078_alpha_dummy_000))
            (Class.cv (nb078_alpha_dummy_089)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0083 (f : Var) :
    (nb078_alpha_dummy_092 f) ∈
      (({(nb078_alpha_dummy_091 f)} : Finset Var) ∪ ({(nb078_alpha_dummy_092 f)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb078_alpha_dummy_092 f)) (Class.cv f)
            (Class.cv (nb078_alpha_dummy_091 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0084 :
    (nb078_alpha_dummy_089) ∈
      (((Class.cv (nb078_alpha_dummy_089))).fv ∪ ((Class.cv (nb078_alpha_dummy_090))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0085 :
    (nb078_alpha_dummy_089) ∈
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_095)
              (syn_wrex (nb078_alpha_dummy_096) (Class.cv (nb078_alpha_dummy_089))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_095))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_096)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_095)
              (syn_wrex (nb078_alpha_dummy_096) (Class.cv (nb078_alpha_dummy_090))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_095))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_096)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_089) ≠ (nb078_alpha_dummy_095) from (by
          unfold nb078_alpha_dummy_095;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0084) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_089) ≠ (nb078_alpha_dummy_096) from (by
            unfold nb078_alpha_dummy_096;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0084) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0086 (f : Var) :
    (nb078_alpha_dummy_091 f) ∈
      (((Class.cv (nb078_alpha_dummy_091 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_092 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0087 (f : Var) :
    (nb078_alpha_dummy_091 f) ∈
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_097 f)
              (syn_wrex (nb078_alpha_dummy_098 f) (Class.cv (nb078_alpha_dummy_091 f))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_097 f))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_098 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_097 f)
              (syn_wrex (nb078_alpha_dummy_098 f) (Class.cv (nb078_alpha_dummy_092 f))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_097 f))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_098 f)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_091 f) ≠ (nb078_alpha_dummy_097 f) from (by
          unfold nb078_alpha_dummy_097;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0086 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_091 f) ≠ (nb078_alpha_dummy_098 f) from (by
            unfold nb078_alpha_dummy_098;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0086 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0088 :
    (nb078_alpha_dummy_089) ∈
      (((Class.cab (nb078_alpha_dummy_095)
            (syn_wrex (nb078_alpha_dummy_096) (Class.cv (nb078_alpha_dummy_089))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_095))
                (syn_cphi (Class.cv (nb078_alpha_dummy_096))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_095)
            (syn_wrex (nb078_alpha_dummy_096) (Class.cv (nb078_alpha_dummy_089))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_095))
                (syn_cphi (Class.cv (nb078_alpha_dummy_096))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_089) ≠ (nb078_alpha_dummy_095) from (by
          unfold nb078_alpha_dummy_095;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0084) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_089) ≠ (nb078_alpha_dummy_096) from (by
            unfold nb078_alpha_dummy_096;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0084) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0089 (f : Var) :
    (nb078_alpha_dummy_091 f) ∈
      (((Class.cab (nb078_alpha_dummy_097 f)
            (syn_wrex (nb078_alpha_dummy_098 f) (Class.cv (nb078_alpha_dummy_091 f))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_097 f))
                (syn_cphi (Class.cv (nb078_alpha_dummy_098 f))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_097 f)
            (syn_wrex (nb078_alpha_dummy_098 f) (Class.cv (nb078_alpha_dummy_091 f))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_097 f))
                (syn_cphi (Class.cv (nb078_alpha_dummy_098 f))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_091 f) ≠ (nb078_alpha_dummy_097 f) from (by
          unfold nb078_alpha_dummy_097;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0086 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_091 f) ≠ (nb078_alpha_dummy_098 f) from (by
            unfold nb078_alpha_dummy_098;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0086 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0090 :
    (nb078_alpha_dummy_096) ∈ (((Class.cv (nb078_alpha_dummy_096))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0091 (f : Var) :
    (nb078_alpha_dummy_098 f) ∈ (((Class.cv (nb078_alpha_dummy_098 f))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0092 :
    (nb078_alpha_dummy_103) ∈
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_103)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_103)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_103))).fv) :=
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

theorem nb078_support_mem_0093 (f : Var) :
    (nb078_alpha_dummy_105 f) ∈
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_105 f)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_105 f)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_105 f))).fv) :=
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

theorem nb078_support_mem_0094 :
    (nb078_alpha_dummy_103) ∈
      (((Class.cv (nb078_alpha_dummy_103))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0095 (f : Var) :
    (nb078_alpha_dummy_105 f) ∈
      (((Class.cv (nb078_alpha_dummy_105 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0096 :
    (nb078_alpha_dummy_110) ∈
      (((syn_cnin (Class.cv (nb078_alpha_dummy_110)) (Class.cv (nb078_alpha_dummy_111)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_110))
            (Class.cv (nb078_alpha_dummy_111)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0097 (f : Var) :
    (nb078_alpha_dummy_113 f) ∈
      (((syn_cnin (Class.cv (nb078_alpha_dummy_113 f))
            (Class.cv (nb078_alpha_dummy_114 f)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_113 f))
            (Class.cv (nb078_alpha_dummy_114 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0098 :
    (nb078_alpha_dummy_110) ∈
      (((Class.cv (nb078_alpha_dummy_110))).fv ∪ ((Class.cv (nb078_alpha_dummy_111))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0099 (f : Var) :
    (nb078_alpha_dummy_113 f) ∈
      (((Class.cv (nb078_alpha_dummy_113 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_114 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0100 :
    (nb078_alpha_dummy_111) ∈
      (((syn_cnin (Class.cv (nb078_alpha_dummy_110)) (Class.cv (nb078_alpha_dummy_111)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_110))
            (Class.cv (nb078_alpha_dummy_111)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0101 (f : Var) :
    (nb078_alpha_dummy_114 f) ∈
      (((syn_cnin (Class.cv (nb078_alpha_dummy_113 f))
            (Class.cv (nb078_alpha_dummy_114 f)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_113 f))
            (Class.cv (nb078_alpha_dummy_114 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0102 :
    (nb078_alpha_dummy_111) ∈
      (((Class.cv (nb078_alpha_dummy_110))).fv ∪ ((Class.cv (nb078_alpha_dummy_111))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0103 (f : Var) :
    (nb078_alpha_dummy_114 f) ∈
      (((Class.cv (nb078_alpha_dummy_113 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_114 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0104 :
    (nb078_alpha_dummy_110) ∈
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_110)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_111)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0105 (f : Var) :
    (nb078_alpha_dummy_113 f) ∈
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_113 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_114 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0106 :
    (nb078_alpha_dummy_110) ∈
      (((Class.cv (nb078_alpha_dummy_110))).fv ∪ ((Class.cv (nb078_alpha_dummy_110))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0107 (f : Var) :
    (nb078_alpha_dummy_113 f) ∈
      (((Class.cv (nb078_alpha_dummy_113 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_113 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0108 :
    (nb078_alpha_dummy_111) ∈
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_110)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_111)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0109 (f : Var) :
    (nb078_alpha_dummy_114 f) ∈
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_113 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_114 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0110 :
    (nb078_alpha_dummy_111) ∈
      (((Class.cv (nb078_alpha_dummy_111))).fv ∪ ((Class.cv (nb078_alpha_dummy_111))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0111 (f : Var) :
    (nb078_alpha_dummy_114 f) ∈
      (((Class.cv (nb078_alpha_dummy_114 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_114 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0112 :
    (nb078_alpha_dummy_090) ∈
      (((Class.cv (nb078_alpha_dummy_089))).fv ∪ ((Class.cv (nb078_alpha_dummy_090))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0113 :
    (nb078_alpha_dummy_090) ∈
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_095)
              (syn_wrex (nb078_alpha_dummy_096) (Class.cv (nb078_alpha_dummy_089))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_095))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_096)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_095)
              (syn_wrex (nb078_alpha_dummy_096) (Class.cv (nb078_alpha_dummy_090))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_095))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_096)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_090) ≠ (nb078_alpha_dummy_095) from (by
          unfold nb078_alpha_dummy_095;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0112) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_090) ≠ (nb078_alpha_dummy_096) from (by
            unfold nb078_alpha_dummy_096;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0112) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0114 (f : Var) :
    (nb078_alpha_dummy_092 f) ∈
      (((Class.cv (nb078_alpha_dummy_091 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_092 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0115 (f : Var) :
    (nb078_alpha_dummy_092 f) ∈
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_097 f)
              (syn_wrex (nb078_alpha_dummy_098 f) (Class.cv (nb078_alpha_dummy_091 f))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_097 f))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_098 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_097 f)
              (syn_wrex (nb078_alpha_dummy_098 f) (Class.cv (nb078_alpha_dummy_092 f))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_097 f))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_098 f)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_092 f) ≠ (nb078_alpha_dummy_097 f) from (by
          unfold nb078_alpha_dummy_097;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0114 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_092 f) ≠ (nb078_alpha_dummy_098 f) from (by
            unfold nb078_alpha_dummy_098;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0114 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0116 :
    (nb078_alpha_dummy_090) ∈
      (((Class.cab (nb078_alpha_dummy_095)
            (syn_wrex (nb078_alpha_dummy_096) (Class.cv (nb078_alpha_dummy_090))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_095))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_096)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_095)
            (syn_wrex (nb078_alpha_dummy_096) (Class.cv (nb078_alpha_dummy_090))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_095))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_096)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_090) ≠ (nb078_alpha_dummy_095) from (by
          unfold nb078_alpha_dummy_095;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0112) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_090) ≠ (nb078_alpha_dummy_096) from (by
            unfold nb078_alpha_dummy_096;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0112) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0117 (f : Var) :
    (nb078_alpha_dummy_092 f) ∈
      (((Class.cab (nb078_alpha_dummy_097 f)
            (syn_wrex (nb078_alpha_dummy_098 f) (Class.cv (nb078_alpha_dummy_092 f))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_097 f))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_098 f)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_097 f)
            (syn_wrex (nb078_alpha_dummy_098 f) (Class.cv (nb078_alpha_dummy_092 f))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_097 f))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_098 f)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_092 f) ≠ (nb078_alpha_dummy_097 f) from (by
          unfold nb078_alpha_dummy_097;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0114 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_092 f) ≠ (nb078_alpha_dummy_098 f) from (by
            unfold nb078_alpha_dummy_098;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0114 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0118 :
    (nb078_alpha_dummy_096) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_096))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0119 (f : Var) :
    (nb078_alpha_dummy_098 f) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_098 f))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0120 :
    (nb078_alpha_dummy_096) ∈
      (((syn_cphi (Class.cv (nb078_alpha_dummy_096)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_096)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0121 (f : Var) :
    (nb078_alpha_dummy_098 f) ∈
      (((syn_cphi (Class.cv (nb078_alpha_dummy_098 f)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_098 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0122 :
    (nb078_alpha_dummy_090) ∈
      (((Class.cv (nb078_alpha_dummy_090))).fv ∪ ((Class.cv (nb078_alpha_dummy_089))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0123 :
    (nb078_alpha_dummy_090) ∈
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_131)
              (syn_wrex (nb078_alpha_dummy_132) (Class.cv (nb078_alpha_dummy_090))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_131))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_132)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_131)
              (syn_wrex (nb078_alpha_dummy_132) (Class.cv (nb078_alpha_dummy_089))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_131))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_132)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_090) ≠ (nb078_alpha_dummy_131) from (by
          unfold nb078_alpha_dummy_131;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0122) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_090) ≠ (nb078_alpha_dummy_132) from (by
            unfold nb078_alpha_dummy_132;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0122) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0124 (f : Var) :
    (nb078_alpha_dummy_092 f) ∈
      (((Class.cv (nb078_alpha_dummy_092 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_091 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0125 (f : Var) :
    (nb078_alpha_dummy_092 f) ∈
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_133 f)
              (syn_wrex (nb078_alpha_dummy_134 f) (Class.cv (nb078_alpha_dummy_092 f))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_133 f))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_134 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_133 f)
              (syn_wrex (nb078_alpha_dummy_134 f) (Class.cv (nb078_alpha_dummy_091 f))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_133 f))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_134 f)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_092 f) ≠ (nb078_alpha_dummy_133 f) from (by
          unfold nb078_alpha_dummy_133;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0124 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_092 f) ≠ (nb078_alpha_dummy_134 f) from (by
            unfold nb078_alpha_dummy_134;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0124 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0126 :
    (nb078_alpha_dummy_090) ∈
      (((Class.cab (nb078_alpha_dummy_131)
            (syn_wrex (nb078_alpha_dummy_132) (Class.cv (nb078_alpha_dummy_090))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_131))
                (syn_cphi (Class.cv (nb078_alpha_dummy_132))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_131)
            (syn_wrex (nb078_alpha_dummy_132) (Class.cv (nb078_alpha_dummy_090))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_131))
                (syn_cphi (Class.cv (nb078_alpha_dummy_132))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_090) ≠ (nb078_alpha_dummy_131) from (by
          unfold nb078_alpha_dummy_131;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0122) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_090) ≠ (nb078_alpha_dummy_132) from (by
            unfold nb078_alpha_dummy_132;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0122) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0127 (f : Var) :
    (nb078_alpha_dummy_092 f) ∈
      (((Class.cab (nb078_alpha_dummy_133 f)
            (syn_wrex (nb078_alpha_dummy_134 f) (Class.cv (nb078_alpha_dummy_092 f))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_133 f))
                (syn_cphi (Class.cv (nb078_alpha_dummy_134 f))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_133 f)
            (syn_wrex (nb078_alpha_dummy_134 f) (Class.cv (nb078_alpha_dummy_092 f))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_133 f))
                (syn_cphi (Class.cv (nb078_alpha_dummy_134 f))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_092 f) ≠ (nb078_alpha_dummy_133 f) from (by
          unfold nb078_alpha_dummy_133;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0124 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_092 f) ≠ (nb078_alpha_dummy_134 f) from (by
            unfold nb078_alpha_dummy_134;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0124 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0128 :
    (nb078_alpha_dummy_132) ∈ (((Class.cv (nb078_alpha_dummy_132))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0129 (f : Var) :
    (nb078_alpha_dummy_134 f) ∈ (((Class.cv (nb078_alpha_dummy_134 f))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0130 :
    (nb078_alpha_dummy_139) ∈
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_139)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_139)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_139))).fv) :=
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

theorem nb078_support_mem_0131 (f : Var) :
    (nb078_alpha_dummy_141 f) ∈
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_141 f)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_141 f)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_141 f))).fv) :=
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

theorem nb078_support_mem_0132 :
    (nb078_alpha_dummy_139) ∈
      (((Class.cv (nb078_alpha_dummy_139))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0133 (f : Var) :
    (nb078_alpha_dummy_141 f) ∈
      (((Class.cv (nb078_alpha_dummy_141 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0134 :
    (nb078_alpha_dummy_146) ∈
      (((syn_cnin (Class.cv (nb078_alpha_dummy_146)) (Class.cv (nb078_alpha_dummy_147)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_146))
            (Class.cv (nb078_alpha_dummy_147)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0135 (f : Var) :
    (nb078_alpha_dummy_149 f) ∈
      (((syn_cnin (Class.cv (nb078_alpha_dummy_149 f))
            (Class.cv (nb078_alpha_dummy_150 f)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_149 f))
            (Class.cv (nb078_alpha_dummy_150 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0136 :
    (nb078_alpha_dummy_146) ∈
      (((Class.cv (nb078_alpha_dummy_146))).fv ∪ ((Class.cv (nb078_alpha_dummy_147))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0137 (f : Var) :
    (nb078_alpha_dummy_149 f) ∈
      (((Class.cv (nb078_alpha_dummy_149 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_150 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0138 :
    (nb078_alpha_dummy_147) ∈
      (((syn_cnin (Class.cv (nb078_alpha_dummy_146)) (Class.cv (nb078_alpha_dummy_147)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_146))
            (Class.cv (nb078_alpha_dummy_147)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0139 (f : Var) :
    (nb078_alpha_dummy_150 f) ∈
      (((syn_cnin (Class.cv (nb078_alpha_dummy_149 f))
            (Class.cv (nb078_alpha_dummy_150 f)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_149 f))
            (Class.cv (nb078_alpha_dummy_150 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0140 :
    (nb078_alpha_dummy_147) ∈
      (((Class.cv (nb078_alpha_dummy_146))).fv ∪ ((Class.cv (nb078_alpha_dummy_147))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0141 (f : Var) :
    (nb078_alpha_dummy_150 f) ∈
      (((Class.cv (nb078_alpha_dummy_149 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_150 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0142 :
    (nb078_alpha_dummy_146) ∈
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_146)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_147)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0143 (f : Var) :
    (nb078_alpha_dummy_149 f) ∈
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_149 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_150 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0144 :
    (nb078_alpha_dummy_146) ∈
      (((Class.cv (nb078_alpha_dummy_146))).fv ∪ ((Class.cv (nb078_alpha_dummy_146))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0145 (f : Var) :
    (nb078_alpha_dummy_149 f) ∈
      (((Class.cv (nb078_alpha_dummy_149 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_149 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0146 :
    (nb078_alpha_dummy_147) ∈
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_146)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_147)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0147 (f : Var) :
    (nb078_alpha_dummy_150 f) ∈
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_149 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_150 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0148 :
    (nb078_alpha_dummy_147) ∈
      (((Class.cv (nb078_alpha_dummy_147))).fv ∪ ((Class.cv (nb078_alpha_dummy_147))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0149 (f : Var) :
    (nb078_alpha_dummy_150 f) ∈
      (((Class.cv (nb078_alpha_dummy_150 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_150 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0150 :
    (nb078_alpha_dummy_089) ∈
      (((Class.cv (nb078_alpha_dummy_090))).fv ∪ ((Class.cv (nb078_alpha_dummy_089))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0151 :
    (nb078_alpha_dummy_089) ∈
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_131)
              (syn_wrex (nb078_alpha_dummy_132) (Class.cv (nb078_alpha_dummy_090))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_131))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_132)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_131)
              (syn_wrex (nb078_alpha_dummy_132) (Class.cv (nb078_alpha_dummy_089))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_131))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_132)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_089) ≠ (nb078_alpha_dummy_131) from (by
          unfold nb078_alpha_dummy_131;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0150) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_089) ≠ (nb078_alpha_dummy_132) from (by
            unfold nb078_alpha_dummy_132;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0150) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0152 (f : Var) :
    (nb078_alpha_dummy_091 f) ∈
      (((Class.cv (nb078_alpha_dummy_092 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_091 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0153 (f : Var) :
    (nb078_alpha_dummy_091 f) ∈
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_133 f)
              (syn_wrex (nb078_alpha_dummy_134 f) (Class.cv (nb078_alpha_dummy_092 f))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_133 f))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_134 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_133 f)
              (syn_wrex (nb078_alpha_dummy_134 f) (Class.cv (nb078_alpha_dummy_091 f))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_133 f))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_134 f)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_091 f) ≠ (nb078_alpha_dummy_133 f) from (by
          unfold nb078_alpha_dummy_133;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0152 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_091 f) ≠ (nb078_alpha_dummy_134 f) from (by
            unfold nb078_alpha_dummy_134;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0152 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0154 :
    (nb078_alpha_dummy_089) ∈
      (((Class.cab (nb078_alpha_dummy_131)
            (syn_wrex (nb078_alpha_dummy_132) (Class.cv (nb078_alpha_dummy_089))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_131))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_132)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_131)
            (syn_wrex (nb078_alpha_dummy_132) (Class.cv (nb078_alpha_dummy_089))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_131))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_132)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_089) ≠ (nb078_alpha_dummy_131) from (by
          unfold nb078_alpha_dummy_131;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0150) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_089) ≠ (nb078_alpha_dummy_132) from (by
            unfold nb078_alpha_dummy_132;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0150) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0155 (f : Var) :
    (nb078_alpha_dummy_091 f) ∈
      (((Class.cab (nb078_alpha_dummy_133 f)
            (syn_wrex (nb078_alpha_dummy_134 f) (Class.cv (nb078_alpha_dummy_091 f))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_133 f))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_134 f)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_133 f)
            (syn_wrex (nb078_alpha_dummy_134 f) (Class.cv (nb078_alpha_dummy_091 f))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_133 f))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_134 f)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_091 f) ≠ (nb078_alpha_dummy_133 f) from (by
          unfold nb078_alpha_dummy_133;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0152 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_091 f) ≠ (nb078_alpha_dummy_134 f) from (by
            unfold nb078_alpha_dummy_134;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0152 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0156 :
    (nb078_alpha_dummy_132) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_132))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0157 (f : Var) :
    (nb078_alpha_dummy_134 f) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_134 f))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0158 :
    (nb078_alpha_dummy_132) ∈
      (((syn_cphi (Class.cv (nb078_alpha_dummy_132)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_132)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0159 (f : Var) :
    (nb078_alpha_dummy_134 f) ∈
      (((syn_cphi (Class.cv (nb078_alpha_dummy_134 f)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_134 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0160 :
    (nb078_alpha_dummy_000) ∈
      (((syn_cnin (syn_ccom (Class.cv (nb078_alpha_dummy_000))
              (syn_ccnv (Class.cv (nb078_alpha_dummy_000)))) (syn_cid))).fv ∪ ((syn_cnin
            (syn_ccom (Class.cv (nb078_alpha_dummy_000))
              (syn_ccnv (Class.cv (nb078_alpha_dummy_000)))) (syn_cid))).fv) :=
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

theorem nb078_support_mem_0161 (f : Var) :
    f ∈
      (((syn_cnin (syn_ccom (Class.cv f) (syn_ccnv (Class.cv f))) (syn_cid))).fv ∪
        ((syn_cnin (syn_ccom (Class.cv f) (syn_ccnv (Class.cv f))) (syn_cid))).fv) :=
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

theorem nb078_support_mem_0162 :
    (nb078_alpha_dummy_000) ∈
      (((syn_ccom (Class.cv (nb078_alpha_dummy_000))
            (syn_ccnv (Class.cv (nb078_alpha_dummy_000))))).fv ∪ ((syn_cid)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccom]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0163 (f : Var) :
    f ∈ (((syn_ccom (Class.cv f) (syn_ccnv (Class.cv f)))).fv ∪ ((syn_cid)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccom]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0164 :
    (nb078_alpha_dummy_000) ∈
      (((Class.cv (nb078_alpha_dummy_000))).fv ∪
        ((syn_ccnv (Class.cv (nb078_alpha_dummy_000)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0165 :
    (nb078_alpha_dummy_000) ∈
      (({(nb078_alpha_dummy_009)} : Finset Var) ∪ ({(nb078_alpha_dummy_010)} : Finset Var) ∪
        ((syn_wex (nb078_alpha_dummy_011) (syn_wa (syn_wbr (Class.cv (nb078_alpha_dummy_009))
                (syn_ccnv (Class.cv (nb078_alpha_dummy_000)))
                (Class.cv (nb078_alpha_dummy_011))) (syn_wbr (Class.cv (nb078_alpha_dummy_011))
                (Class.cv (nb078_alpha_dummy_000)) (Class.cv (nb078_alpha_dummy_010)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_wex]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_000) ≠ (nb078_alpha_dummy_011) from (by
          unfold nb078_alpha_dummy_011;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0164) 2))))
  · rw [fv_syn_wa]
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_syn_wbr]
    with_reducible rw [Finset.mem_union]
    right
    rw [fv_syn_ccnv]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _

theorem nb078_support_mem_0166 (f : Var) :
    f ∈ (((Class.cv f)).fv ∪ ((syn_ccnv (Class.cv f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0167 (f : Var) :
    f ∈
      (({(nb078_alpha_dummy_012 f)} : Finset Var) ∪ ({(nb078_alpha_dummy_013 f)} : Finset Var) ∪
        ((syn_wex (nb078_alpha_dummy_014 f) (syn_wa
              (syn_wbr (Class.cv (nb078_alpha_dummy_012 f)) (syn_ccnv (Class.cv f))
                (Class.cv (nb078_alpha_dummy_014 f)))
              (syn_wbr (Class.cv (nb078_alpha_dummy_014 f)) (Class.cv f)
                (Class.cv (nb078_alpha_dummy_013 f)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_wex]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show f ≠ (nb078_alpha_dummy_014 f) from (by
          unfold nb078_alpha_dummy_014;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0166 f) 2))))
  · rw [fv_syn_wa]
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_syn_wbr]
    with_reducible rw [Finset.mem_union]
    right
    rw [fv_syn_ccnv]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _

theorem nb078_support_mem_0168 :
    (nb078_alpha_dummy_000) ∈
      (({(nb078_alpha_dummy_089)} : Finset Var) ∪ ({(nb078_alpha_dummy_090)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb078_alpha_dummy_090)) (Class.cv (nb078_alpha_dummy_000))
            (Class.cv (nb078_alpha_dummy_089)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_wbr]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0169 (f : Var) :
    f ∈
      (({(nb078_alpha_dummy_091 f)} : Finset Var) ∪ ({(nb078_alpha_dummy_092 f)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb078_alpha_dummy_092 f)) (Class.cv f)
            (Class.cv (nb078_alpha_dummy_091 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_wbr]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0170 :
    (nb078_alpha_dummy_000) ∈ (((Class.cv (nb078_alpha_dummy_000))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C078C001Part023`. -/


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

theorem nb078_support_mem_0171 (f : Var) : f ∈ (((Class.cv f)).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0172 :
    (nb078_alpha_dummy_011) ∈
      (((Class.cv (nb078_alpha_dummy_011))).fv ∪ ((Class.cv (nb078_alpha_dummy_010))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0173 :
    (nb078_alpha_dummy_011) ∈
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_167)
              (syn_wrex (nb078_alpha_dummy_168) (Class.cv (nb078_alpha_dummy_011))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_167))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_168)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_167)
              (syn_wrex (nb078_alpha_dummy_168) (Class.cv (nb078_alpha_dummy_010))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_167))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_168)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_011) ≠ (nb078_alpha_dummy_167) from (by
          unfold nb078_alpha_dummy_167;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0172) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_011) ≠ (nb078_alpha_dummy_168) from (by
            unfold nb078_alpha_dummy_168;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0172) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0174 (f : Var) :
    (nb078_alpha_dummy_014 f) ∈
      (((Class.cv (nb078_alpha_dummy_014 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_013 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0175 (f : Var) :
    (nb078_alpha_dummy_014 f) ∈
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_169 f)
              (syn_wrex (nb078_alpha_dummy_170 f) (Class.cv (nb078_alpha_dummy_014 f))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_169 f))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_170 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_169 f)
              (syn_wrex (nb078_alpha_dummy_170 f) (Class.cv (nb078_alpha_dummy_013 f))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_169 f))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_170 f)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_014 f) ≠ (nb078_alpha_dummy_169 f) from (by
          unfold nb078_alpha_dummy_169;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0174 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_014 f) ≠ (nb078_alpha_dummy_170 f) from (by
            unfold nb078_alpha_dummy_170;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0174 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0176 :
    (nb078_alpha_dummy_011) ∈
      (((Class.cab (nb078_alpha_dummy_167)
            (syn_wrex (nb078_alpha_dummy_168) (Class.cv (nb078_alpha_dummy_011))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_167))
                (syn_cphi (Class.cv (nb078_alpha_dummy_168))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_167)
            (syn_wrex (nb078_alpha_dummy_168) (Class.cv (nb078_alpha_dummy_011))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_167))
                (syn_cphi (Class.cv (nb078_alpha_dummy_168))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_011) ≠ (nb078_alpha_dummy_167) from (by
          unfold nb078_alpha_dummy_167;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0172) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_011) ≠ (nb078_alpha_dummy_168) from (by
            unfold nb078_alpha_dummy_168;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0172) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0177 (f : Var) :
    (nb078_alpha_dummy_014 f) ∈
      (((Class.cab (nb078_alpha_dummy_169 f)
            (syn_wrex (nb078_alpha_dummy_170 f) (Class.cv (nb078_alpha_dummy_014 f))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_169 f))
                (syn_cphi (Class.cv (nb078_alpha_dummy_170 f))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_169 f)
            (syn_wrex (nb078_alpha_dummy_170 f) (Class.cv (nb078_alpha_dummy_014 f))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_169 f))
                (syn_cphi (Class.cv (nb078_alpha_dummy_170 f))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_014 f) ≠ (nb078_alpha_dummy_169 f) from (by
          unfold nb078_alpha_dummy_169;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0174 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_014 f) ≠ (nb078_alpha_dummy_170 f) from (by
            unfold nb078_alpha_dummy_170;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0174 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0178 :
    (nb078_alpha_dummy_168) ∈ (((Class.cv (nb078_alpha_dummy_168))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0179 (f : Var) :
    (nb078_alpha_dummy_170 f) ∈ (((Class.cv (nb078_alpha_dummy_170 f))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0180 :
    (nb078_alpha_dummy_175) ∈
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_175)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_175)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_175))).fv) :=
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

theorem nb078_support_mem_0181 (f : Var) :
    (nb078_alpha_dummy_177 f) ∈
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_177 f)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_177 f)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_177 f))).fv) :=
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

theorem nb078_support_mem_0182 :
    (nb078_alpha_dummy_175) ∈
      (((Class.cv (nb078_alpha_dummy_175))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0183 (f : Var) :
    (nb078_alpha_dummy_177 f) ∈
      (((Class.cv (nb078_alpha_dummy_177 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0184 :
    (nb078_alpha_dummy_182) ∈
      (((syn_cnin (Class.cv (nb078_alpha_dummy_182)) (Class.cv (nb078_alpha_dummy_183)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_182))
            (Class.cv (nb078_alpha_dummy_183)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0185 (f : Var) :
    (nb078_alpha_dummy_185 f) ∈
      (((syn_cnin (Class.cv (nb078_alpha_dummy_185 f))
            (Class.cv (nb078_alpha_dummy_186 f)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_185 f))
            (Class.cv (nb078_alpha_dummy_186 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0186 :
    (nb078_alpha_dummy_182) ∈
      (((Class.cv (nb078_alpha_dummy_182))).fv ∪ ((Class.cv (nb078_alpha_dummy_183))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0187 (f : Var) :
    (nb078_alpha_dummy_185 f) ∈
      (((Class.cv (nb078_alpha_dummy_185 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_186 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0188 :
    (nb078_alpha_dummy_183) ∈
      (((syn_cnin (Class.cv (nb078_alpha_dummy_182)) (Class.cv (nb078_alpha_dummy_183)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_182))
            (Class.cv (nb078_alpha_dummy_183)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0189 (f : Var) :
    (nb078_alpha_dummy_186 f) ∈
      (((syn_cnin (Class.cv (nb078_alpha_dummy_185 f))
            (Class.cv (nb078_alpha_dummy_186 f)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_185 f))
            (Class.cv (nb078_alpha_dummy_186 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0190 :
    (nb078_alpha_dummy_183) ∈
      (((Class.cv (nb078_alpha_dummy_182))).fv ∪ ((Class.cv (nb078_alpha_dummy_183))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0191 (f : Var) :
    (nb078_alpha_dummy_186 f) ∈
      (((Class.cv (nb078_alpha_dummy_185 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_186 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0192 :
    (nb078_alpha_dummy_182) ∈
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_182)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_183)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0193 (f : Var) :
    (nb078_alpha_dummy_185 f) ∈
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_185 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_186 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0194 :
    (nb078_alpha_dummy_182) ∈
      (((Class.cv (nb078_alpha_dummy_182))).fv ∪ ((Class.cv (nb078_alpha_dummy_182))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0195 (f : Var) :
    (nb078_alpha_dummy_185 f) ∈
      (((Class.cv (nb078_alpha_dummy_185 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_185 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0196 :
    (nb078_alpha_dummy_183) ∈
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_182)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_183)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0197 (f : Var) :
    (nb078_alpha_dummy_186 f) ∈
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_185 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_186 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0198 :
    (nb078_alpha_dummy_183) ∈
      (((Class.cv (nb078_alpha_dummy_183))).fv ∪ ((Class.cv (nb078_alpha_dummy_183))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0199 (f : Var) :
    (nb078_alpha_dummy_186 f) ∈
      (((Class.cv (nb078_alpha_dummy_186 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_186 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0200 :
    (nb078_alpha_dummy_010) ∈
      (((Class.cv (nb078_alpha_dummy_011))).fv ∪ ((Class.cv (nb078_alpha_dummy_010))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0201 :
    (nb078_alpha_dummy_010) ∈
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_167)
              (syn_wrex (nb078_alpha_dummy_168) (Class.cv (nb078_alpha_dummy_011))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_167))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_168)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_167)
              (syn_wrex (nb078_alpha_dummy_168) (Class.cv (nb078_alpha_dummy_010))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_167))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_168)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_010) ≠ (nb078_alpha_dummy_167) from (by
          unfold nb078_alpha_dummy_167;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0200) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_010) ≠ (nb078_alpha_dummy_168) from (by
            unfold nb078_alpha_dummy_168;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0200) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0202 (f : Var) :
    (nb078_alpha_dummy_013 f) ∈
      (((Class.cv (nb078_alpha_dummy_014 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_013 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0203 (f : Var) :
    (nb078_alpha_dummy_013 f) ∈
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_169 f)
              (syn_wrex (nb078_alpha_dummy_170 f) (Class.cv (nb078_alpha_dummy_014 f))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_169 f))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_170 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_169 f)
              (syn_wrex (nb078_alpha_dummy_170 f) (Class.cv (nb078_alpha_dummy_013 f))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_169 f))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_170 f)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_013 f) ≠ (nb078_alpha_dummy_169 f) from (by
          unfold nb078_alpha_dummy_169;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0202 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_013 f) ≠ (nb078_alpha_dummy_170 f) from (by
            unfold nb078_alpha_dummy_170;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0202 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0204 :
    (nb078_alpha_dummy_010) ∈
      (((Class.cab (nb078_alpha_dummy_167)
            (syn_wrex (nb078_alpha_dummy_168) (Class.cv (nb078_alpha_dummy_010))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_167))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_168)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_167)
            (syn_wrex (nb078_alpha_dummy_168) (Class.cv (nb078_alpha_dummy_010))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_167))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_168)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_010) ≠ (nb078_alpha_dummy_167) from (by
          unfold nb078_alpha_dummy_167;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0200) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_010) ≠ (nb078_alpha_dummy_168) from (by
            unfold nb078_alpha_dummy_168;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0200) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0205 (f : Var) :
    (nb078_alpha_dummy_013 f) ∈
      (((Class.cab (nb078_alpha_dummy_169 f)
            (syn_wrex (nb078_alpha_dummy_170 f) (Class.cv (nb078_alpha_dummy_013 f))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_169 f))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_170 f)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_169 f)
            (syn_wrex (nb078_alpha_dummy_170 f) (Class.cv (nb078_alpha_dummy_013 f))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_169 f))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_170 f)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_013 f) ≠ (nb078_alpha_dummy_169 f) from (by
          unfold nb078_alpha_dummy_169;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0202 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_013 f) ≠ (nb078_alpha_dummy_170 f) from (by
            unfold nb078_alpha_dummy_170;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0202 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0206 :
    (nb078_alpha_dummy_168) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_168))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0207 (f : Var) :
    (nb078_alpha_dummy_170 f) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_170 f))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0208 :
    (nb078_alpha_dummy_168) ∈
      (((syn_cphi (Class.cv (nb078_alpha_dummy_168)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_168)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0209 (f : Var) :
    (nb078_alpha_dummy_170 f) ∈
      (((syn_cphi (Class.cv (nb078_alpha_dummy_170 f)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_170 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0210 :
    (nb078_alpha_dummy_204) ∈
      (((Class.cv (nb078_alpha_dummy_204))).fv ∪ ((Class.cv (nb078_alpha_dummy_203))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0211 :
    (nb078_alpha_dummy_204) ∈
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_207)
              (syn_wrex (nb078_alpha_dummy_208) (Class.cv (nb078_alpha_dummy_204))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_207))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_208)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_207)
              (syn_wrex (nb078_alpha_dummy_208) (Class.cv (nb078_alpha_dummy_203))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_207))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_208)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_204) ≠ (nb078_alpha_dummy_207) from (by
          unfold nb078_alpha_dummy_207;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0210) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_204) ≠ (nb078_alpha_dummy_208) from (by
            unfold nb078_alpha_dummy_208;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0210) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0212 (f : Var) :
    (nb078_alpha_dummy_206 f) ∈
      (((Class.cv (nb078_alpha_dummy_206 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_205 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0213 (f : Var) :
    (nb078_alpha_dummy_206 f) ∈
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_209 f)
              (syn_wrex (nb078_alpha_dummy_210 f) (Class.cv (nb078_alpha_dummy_206 f))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_209 f))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_210 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_209 f)
              (syn_wrex (nb078_alpha_dummy_210 f) (Class.cv (nb078_alpha_dummy_205 f))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_209 f))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_210 f)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_206 f) ≠ (nb078_alpha_dummy_209 f) from (by
          unfold nb078_alpha_dummy_209;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0212 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_206 f) ≠ (nb078_alpha_dummy_210 f) from (by
            unfold nb078_alpha_dummy_210;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0212 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0214 :
    (nb078_alpha_dummy_204) ∈
      (((Class.cab (nb078_alpha_dummy_207)
            (syn_wrex (nb078_alpha_dummy_208) (Class.cv (nb078_alpha_dummy_204))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_207))
                (syn_cphi (Class.cv (nb078_alpha_dummy_208))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_207)
            (syn_wrex (nb078_alpha_dummy_208) (Class.cv (nb078_alpha_dummy_204))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_207))
                (syn_cphi (Class.cv (nb078_alpha_dummy_208))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_204) ≠ (nb078_alpha_dummy_207) from (by
          unfold nb078_alpha_dummy_207;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0210) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_204) ≠ (nb078_alpha_dummy_208) from (by
            unfold nb078_alpha_dummy_208;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0210) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0215 (f : Var) :
    (nb078_alpha_dummy_206 f) ∈
      (((Class.cab (nb078_alpha_dummy_209 f)
            (syn_wrex (nb078_alpha_dummy_210 f) (Class.cv (nb078_alpha_dummy_206 f))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_209 f))
                (syn_cphi (Class.cv (nb078_alpha_dummy_210 f))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_209 f)
            (syn_wrex (nb078_alpha_dummy_210 f) (Class.cv (nb078_alpha_dummy_206 f))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_209 f))
                (syn_cphi (Class.cv (nb078_alpha_dummy_210 f))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_206 f) ≠ (nb078_alpha_dummy_209 f) from (by
          unfold nb078_alpha_dummy_209;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0212 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_206 f) ≠ (nb078_alpha_dummy_210 f) from (by
            unfold nb078_alpha_dummy_210;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0212 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0216 :
    (nb078_alpha_dummy_208) ∈ (((Class.cv (nb078_alpha_dummy_208))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0217 (f : Var) :
    (nb078_alpha_dummy_210 f) ∈ (((Class.cv (nb078_alpha_dummy_210 f))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0218 :
    (nb078_alpha_dummy_215) ∈
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_215)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_215)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_215))).fv) :=
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

theorem nb078_support_mem_0219 (f : Var) :
    (nb078_alpha_dummy_217 f) ∈
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_217 f)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_217 f)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_217 f))).fv) :=
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

theorem nb078_support_mem_0220 :
    (nb078_alpha_dummy_215) ∈
      (((Class.cv (nb078_alpha_dummy_215))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0221 (f : Var) :
    (nb078_alpha_dummy_217 f) ∈
      (((Class.cv (nb078_alpha_dummy_217 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0222 :
    (nb078_alpha_dummy_222) ∈
      (((syn_cnin (Class.cv (nb078_alpha_dummy_222)) (Class.cv (nb078_alpha_dummy_223)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_222))
            (Class.cv (nb078_alpha_dummy_223)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0223 (f : Var) :
    (nb078_alpha_dummy_225 f) ∈
      (((syn_cnin (Class.cv (nb078_alpha_dummy_225 f))
            (Class.cv (nb078_alpha_dummy_226 f)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_225 f))
            (Class.cv (nb078_alpha_dummy_226 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0224 :
    (nb078_alpha_dummy_222) ∈
      (((Class.cv (nb078_alpha_dummy_222))).fv ∪ ((Class.cv (nb078_alpha_dummy_223))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0225 (f : Var) :
    (nb078_alpha_dummy_225 f) ∈
      (((Class.cv (nb078_alpha_dummy_225 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_226 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0226 :
    (nb078_alpha_dummy_223) ∈
      (((syn_cnin (Class.cv (nb078_alpha_dummy_222)) (Class.cv (nb078_alpha_dummy_223)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_222))
            (Class.cv (nb078_alpha_dummy_223)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0227 (f : Var) :
    (nb078_alpha_dummy_226 f) ∈
      (((syn_cnin (Class.cv (nb078_alpha_dummy_225 f))
            (Class.cv (nb078_alpha_dummy_226 f)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_225 f))
            (Class.cv (nb078_alpha_dummy_226 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0228 :
    (nb078_alpha_dummy_223) ∈
      (((Class.cv (nb078_alpha_dummy_222))).fv ∪ ((Class.cv (nb078_alpha_dummy_223))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0229 (f : Var) :
    (nb078_alpha_dummy_226 f) ∈
      (((Class.cv (nb078_alpha_dummy_225 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_226 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0230 :
    (nb078_alpha_dummy_222) ∈
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_222)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_223)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0231 (f : Var) :
    (nb078_alpha_dummy_225 f) ∈
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_225 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_226 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0232 :
    (nb078_alpha_dummy_222) ∈
      (((Class.cv (nb078_alpha_dummy_222))).fv ∪ ((Class.cv (nb078_alpha_dummy_222))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0233 (f : Var) :
    (nb078_alpha_dummy_225 f) ∈
      (((Class.cv (nb078_alpha_dummy_225 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_225 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0234 :
    (nb078_alpha_dummy_223) ∈
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_222)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_223)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0235 (f : Var) :
    (nb078_alpha_dummy_226 f) ∈
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_225 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_226 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0236 :
    (nb078_alpha_dummy_223) ∈
      (((Class.cv (nb078_alpha_dummy_223))).fv ∪ ((Class.cv (nb078_alpha_dummy_223))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0237 (f : Var) :
    (nb078_alpha_dummy_226 f) ∈
      (((Class.cv (nb078_alpha_dummy_226 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_226 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0238 :
    (nb078_alpha_dummy_203) ∈
      (((Class.cv (nb078_alpha_dummy_204))).fv ∪ ((Class.cv (nb078_alpha_dummy_203))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0239 :
    (nb078_alpha_dummy_203) ∈
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_207)
              (syn_wrex (nb078_alpha_dummy_208) (Class.cv (nb078_alpha_dummy_204))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_207))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_208)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_207)
              (syn_wrex (nb078_alpha_dummy_208) (Class.cv (nb078_alpha_dummy_203))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_207))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_208)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_203) ≠ (nb078_alpha_dummy_207) from (by
          unfold nb078_alpha_dummy_207;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0238) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_203) ≠ (nb078_alpha_dummy_208) from (by
            unfold nb078_alpha_dummy_208;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0238) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0240 (f : Var) :
    (nb078_alpha_dummy_205 f) ∈
      (((Class.cv (nb078_alpha_dummy_206 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_205 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0241 (f : Var) :
    (nb078_alpha_dummy_205 f) ∈
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_209 f)
              (syn_wrex (nb078_alpha_dummy_210 f) (Class.cv (nb078_alpha_dummy_206 f))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_209 f))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_210 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_209 f)
              (syn_wrex (nb078_alpha_dummy_210 f) (Class.cv (nb078_alpha_dummy_205 f))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_209 f))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_210 f)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_205 f) ≠ (nb078_alpha_dummy_209 f) from (by
          unfold nb078_alpha_dummy_209;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0240 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_205 f) ≠ (nb078_alpha_dummy_210 f) from (by
            unfold nb078_alpha_dummy_210;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0240 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0242 :
    (nb078_alpha_dummy_203) ∈
      (((Class.cab (nb078_alpha_dummy_207)
            (syn_wrex (nb078_alpha_dummy_208) (Class.cv (nb078_alpha_dummy_203))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_207))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_208)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_207)
            (syn_wrex (nb078_alpha_dummy_208) (Class.cv (nb078_alpha_dummy_203))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_207))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_208)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_203) ≠ (nb078_alpha_dummy_207) from (by
          unfold nb078_alpha_dummy_207;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0238) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_203) ≠ (nb078_alpha_dummy_208) from (by
            unfold nb078_alpha_dummy_208;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0238) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0243 (f : Var) :
    (nb078_alpha_dummy_205 f) ∈
      (((Class.cab (nb078_alpha_dummy_209 f)
            (syn_wrex (nb078_alpha_dummy_210 f) (Class.cv (nb078_alpha_dummy_205 f))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_209 f))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_210 f)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_209 f)
            (syn_wrex (nb078_alpha_dummy_210 f) (Class.cv (nb078_alpha_dummy_205 f))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_209 f))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_210 f)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_205 f) ≠ (nb078_alpha_dummy_209 f) from (by
          unfold nb078_alpha_dummy_209;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0240 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_205 f) ≠ (nb078_alpha_dummy_210 f) from (by
            unfold nb078_alpha_dummy_210;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0240 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0244 :
    (nb078_alpha_dummy_208) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_208))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0245 (f : Var) :
    (nb078_alpha_dummy_210 f) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_210 f))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0246 :
    (nb078_alpha_dummy_208) ∈
      (((syn_cphi (Class.cv (nb078_alpha_dummy_208)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_208)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0247 (f : Var) :
    (nb078_alpha_dummy_210 f) ∈
      (((syn_cphi (Class.cv (nb078_alpha_dummy_210 f)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_210 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0248 :
    (nb078_alpha_dummy_000) ∈
      (((syn_ccnv (Class.cv (nb078_alpha_dummy_000)))).fv ∪ ((syn_cvv)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccnv]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0249 (f : Var) :
    f ∈ (((syn_ccnv (Class.cv f))).fv ∪ ((syn_cvv)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccnv]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0250 :
    (nb078_alpha_dummy_244) ∈
      (((Class.cv (nb078_alpha_dummy_244))).fv ∪ ((Class.cv (nb078_alpha_dummy_243))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0251 :
    (nb078_alpha_dummy_244) ∈
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_247)
              (syn_wrex (nb078_alpha_dummy_248) (Class.cv (nb078_alpha_dummy_244))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_247))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_248)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_247)
              (syn_wrex (nb078_alpha_dummy_248) (Class.cv (nb078_alpha_dummy_243))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_247))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_248)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_244) ≠ (nb078_alpha_dummy_247) from (by
          unfold nb078_alpha_dummy_247;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0250) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_244) ≠ (nb078_alpha_dummy_248) from (by
            unfold nb078_alpha_dummy_248;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0250) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0252 (f : Var) :
    (nb078_alpha_dummy_246 f) ∈
      (((Class.cv (nb078_alpha_dummy_246 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_245 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0253 (f : Var) :
    (nb078_alpha_dummy_246 f) ∈
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_249 f)
              (syn_wrex (nb078_alpha_dummy_250 f) (Class.cv (nb078_alpha_dummy_246 f))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_249 f))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_250 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_249 f)
              (syn_wrex (nb078_alpha_dummy_250 f) (Class.cv (nb078_alpha_dummy_245 f))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_249 f))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_250 f)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_246 f) ≠ (nb078_alpha_dummy_249 f) from (by
          unfold nb078_alpha_dummy_249;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0252 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_246 f) ≠ (nb078_alpha_dummy_250 f) from (by
            unfold nb078_alpha_dummy_250;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0252 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0254 :
    (nb078_alpha_dummy_244) ∈
      (((Class.cab (nb078_alpha_dummy_247)
            (syn_wrex (nb078_alpha_dummy_248) (Class.cv (nb078_alpha_dummy_244))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_247))
                (syn_cphi (Class.cv (nb078_alpha_dummy_248))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_247)
            (syn_wrex (nb078_alpha_dummy_248) (Class.cv (nb078_alpha_dummy_244))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_247))
                (syn_cphi (Class.cv (nb078_alpha_dummy_248))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_244) ≠ (nb078_alpha_dummy_247) from (by
          unfold nb078_alpha_dummy_247;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0250) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_244) ≠ (nb078_alpha_dummy_248) from (by
            unfold nb078_alpha_dummy_248;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0250) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0255 (f : Var) :
    (nb078_alpha_dummy_246 f) ∈
      (((Class.cab (nb078_alpha_dummy_249 f)
            (syn_wrex (nb078_alpha_dummy_250 f) (Class.cv (nb078_alpha_dummy_246 f))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_249 f))
                (syn_cphi (Class.cv (nb078_alpha_dummy_250 f))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_249 f)
            (syn_wrex (nb078_alpha_dummy_250 f) (Class.cv (nb078_alpha_dummy_246 f))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_249 f))
                (syn_cphi (Class.cv (nb078_alpha_dummy_250 f))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_246 f) ≠ (nb078_alpha_dummy_249 f) from (by
          unfold nb078_alpha_dummy_249;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0252 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_246 f) ≠ (nb078_alpha_dummy_250 f) from (by
            unfold nb078_alpha_dummy_250;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0252 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0256 :
    (nb078_alpha_dummy_248) ∈ (((Class.cv (nb078_alpha_dummy_248))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0257 (f : Var) :
    (nb078_alpha_dummy_250 f) ∈ (((Class.cv (nb078_alpha_dummy_250 f))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0258 :
    (nb078_alpha_dummy_255) ∈
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_255)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_255)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_255))).fv) :=
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

theorem nb078_support_mem_0259 (f : Var) :
    (nb078_alpha_dummy_257 f) ∈
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_257 f)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_257 f)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_257 f))).fv) :=
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

theorem nb078_support_mem_0260 :
    (nb078_alpha_dummy_255) ∈
      (((Class.cv (nb078_alpha_dummy_255))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0261 (f : Var) :
    (nb078_alpha_dummy_257 f) ∈
      (((Class.cv (nb078_alpha_dummy_257 f))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0262 :
    (nb078_alpha_dummy_262) ∈
      (((syn_cnin (Class.cv (nb078_alpha_dummy_262)) (Class.cv (nb078_alpha_dummy_263)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_262))
            (Class.cv (nb078_alpha_dummy_263)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0263 (f : Var) :
    (nb078_alpha_dummy_265 f) ∈
      (((syn_cnin (Class.cv (nb078_alpha_dummy_265 f))
            (Class.cv (nb078_alpha_dummy_266 f)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_265 f))
            (Class.cv (nb078_alpha_dummy_266 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0264 :
    (nb078_alpha_dummy_262) ∈
      (((Class.cv (nb078_alpha_dummy_262))).fv ∪ ((Class.cv (nb078_alpha_dummy_263))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0265 (f : Var) :
    (nb078_alpha_dummy_265 f) ∈
      (((Class.cv (nb078_alpha_dummy_265 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_266 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0266 :
    (nb078_alpha_dummy_263) ∈
      (((syn_cnin (Class.cv (nb078_alpha_dummy_262)) (Class.cv (nb078_alpha_dummy_263)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_262))
            (Class.cv (nb078_alpha_dummy_263)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0267 (f : Var) :
    (nb078_alpha_dummy_266 f) ∈
      (((syn_cnin (Class.cv (nb078_alpha_dummy_265 f))
            (Class.cv (nb078_alpha_dummy_266 f)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_265 f))
            (Class.cv (nb078_alpha_dummy_266 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0268 :
    (nb078_alpha_dummy_263) ∈
      (((Class.cv (nb078_alpha_dummy_262))).fv ∪ ((Class.cv (nb078_alpha_dummy_263))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0269 (f : Var) :
    (nb078_alpha_dummy_266 f) ∈
      (((Class.cv (nb078_alpha_dummy_265 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_266 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0270 :
    (nb078_alpha_dummy_262) ∈
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_262)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_263)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0271 (f : Var) :
    (nb078_alpha_dummy_265 f) ∈
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_265 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_266 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0272 :
    (nb078_alpha_dummy_262) ∈
      (((Class.cv (nb078_alpha_dummy_262))).fv ∪ ((Class.cv (nb078_alpha_dummy_262))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0273 (f : Var) :
    (nb078_alpha_dummy_265 f) ∈
      (((Class.cv (nb078_alpha_dummy_265 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_265 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0274 :
    (nb078_alpha_dummy_263) ∈
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_262)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_263)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0275 (f : Var) :
    (nb078_alpha_dummy_266 f) ∈
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_265 f)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_266 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0276 :
    (nb078_alpha_dummy_263) ∈
      (((Class.cv (nb078_alpha_dummy_263))).fv ∪ ((Class.cv (nb078_alpha_dummy_263))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0277 (f : Var) :
    (nb078_alpha_dummy_266 f) ∈
      (((Class.cv (nb078_alpha_dummy_266 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_266 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0278 :
    (nb078_alpha_dummy_243) ∈
      (((Class.cv (nb078_alpha_dummy_244))).fv ∪ ((Class.cv (nb078_alpha_dummy_243))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0279 :
    (nb078_alpha_dummy_243) ∈
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_247)
              (syn_wrex (nb078_alpha_dummy_248) (Class.cv (nb078_alpha_dummy_244))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_247))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_248)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_247)
              (syn_wrex (nb078_alpha_dummy_248) (Class.cv (nb078_alpha_dummy_243))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_247))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_248)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_243) ≠ (nb078_alpha_dummy_247) from (by
          unfold nb078_alpha_dummy_247;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0278) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_243) ≠ (nb078_alpha_dummy_248) from (by
            unfold nb078_alpha_dummy_248;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0278) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0280 (f : Var) :
    (nb078_alpha_dummy_245 f) ∈
      (((Class.cv (nb078_alpha_dummy_246 f))).fv ∪ ((Class.cv (nb078_alpha_dummy_245 f))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0281 (f : Var) :
    (nb078_alpha_dummy_245 f) ∈
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_249 f)
              (syn_wrex (nb078_alpha_dummy_250 f) (Class.cv (nb078_alpha_dummy_246 f))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_249 f))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_250 f)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_249 f)
              (syn_wrex (nb078_alpha_dummy_250 f) (Class.cv (nb078_alpha_dummy_245 f))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_249 f))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_250 f)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_245 f) ≠ (nb078_alpha_dummy_249 f) from (by
          unfold nb078_alpha_dummy_249;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0280 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_245 f) ≠ (nb078_alpha_dummy_250 f) from (by
            unfold nb078_alpha_dummy_250;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0280 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0282 :
    (nb078_alpha_dummy_243) ∈
      (((Class.cab (nb078_alpha_dummy_247)
            (syn_wrex (nb078_alpha_dummy_248) (Class.cv (nb078_alpha_dummy_243))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_247))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_248)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_247)
            (syn_wrex (nb078_alpha_dummy_248) (Class.cv (nb078_alpha_dummy_243))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_247))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_248)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_243) ≠ (nb078_alpha_dummy_247) from (by
          unfold nb078_alpha_dummy_247;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0278) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_243) ≠ (nb078_alpha_dummy_248) from (by
            unfold nb078_alpha_dummy_248;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0278) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0283 (f : Var) :
    (nb078_alpha_dummy_245 f) ∈
      (((Class.cab (nb078_alpha_dummy_249 f)
            (syn_wrex (nb078_alpha_dummy_250 f) (Class.cv (nb078_alpha_dummy_245 f))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_249 f))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_250 f)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_249 f)
            (syn_wrex (nb078_alpha_dummy_250 f) (Class.cv (nb078_alpha_dummy_245 f))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_249 f))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_250 f)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_245 f) ≠ (nb078_alpha_dummy_249 f) from (by
          unfold nb078_alpha_dummy_249;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0280 f) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_245 f) ≠ (nb078_alpha_dummy_250 f) from (by
            unfold nb078_alpha_dummy_250;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0280 f) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0284 :
    (nb078_alpha_dummy_248) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_248))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0285 (f : Var) :
    (nb078_alpha_dummy_250 f) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_250 f))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0286 :
    (nb078_alpha_dummy_248) ∈
      (((syn_cphi (Class.cv (nb078_alpha_dummy_248)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_248)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0287 (f : Var) :
    (nb078_alpha_dummy_250 f) ∈
      (((syn_cphi (Class.cv (nb078_alpha_dummy_250 f)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_250 f)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0288 :
    (nb078_alpha_dummy_000) ∈
      (((Class.cv (nb078_alpha_dummy_000))).fv ∪ ((syn_cvv)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0289 (f : Var) : f ∈ (((Class.cv f)).fv ∪ ((syn_cvv)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0290 :
    (nb078_alpha_dummy_287) ∈
      (({(nb078_alpha_dummy_287)} : Finset Var) ∪ ({(nb078_alpha_dummy_288)} : Finset Var) ∪
        ((syn_wex (nb078_alpha_dummy_289) (syn_wa (syn_wbr (Class.cv (nb078_alpha_dummy_287))
                (syn_ccnv (Class.cv (nb078_alpha_dummy_001)))
                (Class.cv (nb078_alpha_dummy_289))) (syn_wbr (Class.cv (nb078_alpha_dummy_289))
                (Class.cv (nb078_alpha_dummy_001)) (Class.cv (nb078_alpha_dummy_288)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0291 (g : Var) :
    (nb078_alpha_dummy_290 g) ∈
      (({(nb078_alpha_dummy_290 g)} : Finset Var) ∪ ({(nb078_alpha_dummy_291 g)} : Finset Var) ∪
        ((syn_wex (nb078_alpha_dummy_292 g) (syn_wa
              (syn_wbr (Class.cv (nb078_alpha_dummy_290 g)) (syn_ccnv (Class.cv g))
                (Class.cv (nb078_alpha_dummy_292 g)))
              (syn_wbr (Class.cv (nb078_alpha_dummy_292 g)) (Class.cv g)
                (Class.cv (nb078_alpha_dummy_291 g)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0292 :
    (nb078_alpha_dummy_288) ∈
      (({(nb078_alpha_dummy_287)} : Finset Var) ∪ ({(nb078_alpha_dummy_288)} : Finset Var) ∪
        ((syn_wex (nb078_alpha_dummy_289) (syn_wa (syn_wbr (Class.cv (nb078_alpha_dummy_287))
                (syn_ccnv (Class.cv (nb078_alpha_dummy_001)))
                (Class.cv (nb078_alpha_dummy_289))) (syn_wbr (Class.cv (nb078_alpha_dummy_289))
                (Class.cv (nb078_alpha_dummy_001)) (Class.cv (nb078_alpha_dummy_288)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0293 (g : Var) :
    (nb078_alpha_dummy_291 g) ∈
      (({(nb078_alpha_dummy_290 g)} : Finset Var) ∪ ({(nb078_alpha_dummy_291 g)} : Finset Var) ∪
        ((syn_wex (nb078_alpha_dummy_292 g) (syn_wa
              (syn_wbr (Class.cv (nb078_alpha_dummy_290 g)) (syn_ccnv (Class.cv g))
                (Class.cv (nb078_alpha_dummy_292 g)))
              (syn_wbr (Class.cv (nb078_alpha_dummy_292 g)) (Class.cv g)
                (Class.cv (nb078_alpha_dummy_291 g)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0294 :
    (nb078_alpha_dummy_287) ∈
      (((Class.cv (nb078_alpha_dummy_287))).fv ∪ ((Class.cv (nb078_alpha_dummy_288))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0295 :
    (nb078_alpha_dummy_287) ∈
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_295)
              (syn_wrex (nb078_alpha_dummy_296) (Class.cv (nb078_alpha_dummy_287))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_295))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_296)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_295)
              (syn_wrex (nb078_alpha_dummy_296) (Class.cv (nb078_alpha_dummy_288))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_295))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_296)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_287) ≠ (nb078_alpha_dummy_295) from (by
          unfold nb078_alpha_dummy_295;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0294) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_287) ≠ (nb078_alpha_dummy_296) from (by
            unfold nb078_alpha_dummy_296;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0294) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0296 (g : Var) :
    (nb078_alpha_dummy_290 g) ∈
      (((Class.cv (nb078_alpha_dummy_290 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_291 g))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0297 (g : Var) :
    (nb078_alpha_dummy_290 g) ∈
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_297 g)
              (syn_wrex (nb078_alpha_dummy_298 g) (Class.cv (nb078_alpha_dummy_290 g))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_297 g))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_298 g)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_297 g)
              (syn_wrex (nb078_alpha_dummy_298 g) (Class.cv (nb078_alpha_dummy_291 g))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_297 g))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_298 g)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_290 g) ≠ (nb078_alpha_dummy_297 g) from (by
          unfold nb078_alpha_dummy_297;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0296 g) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_290 g) ≠ (nb078_alpha_dummy_298 g) from (by
            unfold nb078_alpha_dummy_298;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0296 g) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0298 :
    (nb078_alpha_dummy_287) ∈
      (((Class.cab (nb078_alpha_dummy_295)
            (syn_wrex (nb078_alpha_dummy_296) (Class.cv (nb078_alpha_dummy_287))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_295))
                (syn_cphi (Class.cv (nb078_alpha_dummy_296))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_295)
            (syn_wrex (nb078_alpha_dummy_296) (Class.cv (nb078_alpha_dummy_287))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_295))
                (syn_cphi (Class.cv (nb078_alpha_dummy_296))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_287) ≠ (nb078_alpha_dummy_295) from (by
          unfold nb078_alpha_dummy_295;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0294) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_287) ≠ (nb078_alpha_dummy_296) from (by
            unfold nb078_alpha_dummy_296;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0294) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0299 (g : Var) :
    (nb078_alpha_dummy_290 g) ∈
      (((Class.cab (nb078_alpha_dummy_297 g)
            (syn_wrex (nb078_alpha_dummy_298 g) (Class.cv (nb078_alpha_dummy_290 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_297 g))
                (syn_cphi (Class.cv (nb078_alpha_dummy_298 g))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_297 g)
            (syn_wrex (nb078_alpha_dummy_298 g) (Class.cv (nb078_alpha_dummy_290 g))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_297 g))
                (syn_cphi (Class.cv (nb078_alpha_dummy_298 g))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_290 g) ≠ (nb078_alpha_dummy_297 g) from (by
          unfold nb078_alpha_dummy_297;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0296 g) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_290 g) ≠ (nb078_alpha_dummy_298 g) from (by
            unfold nb078_alpha_dummy_298;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0296 g) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_0300 :
    (nb078_alpha_dummy_296) ∈ (((Class.cv (nb078_alpha_dummy_296))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0301 (g : Var) :
    (nb078_alpha_dummy_298 g) ∈ (((Class.cv (nb078_alpha_dummy_298 g))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0302 :
    (nb078_alpha_dummy_303) ∈
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_303)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_303)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_303))).fv) :=
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

theorem nb078_support_mem_0303 (g : Var) :
    (nb078_alpha_dummy_305 g) ∈
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_305 g)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_305 g)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_305 g))).fv) :=
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

theorem nb078_support_mem_0304 :
    (nb078_alpha_dummy_303) ∈
      (((Class.cv (nb078_alpha_dummy_303))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0305 (g : Var) :
    (nb078_alpha_dummy_305 g) ∈
      (((Class.cv (nb078_alpha_dummy_305 g))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0306 :
    (nb078_alpha_dummy_310) ∈
      (((syn_cnin (Class.cv (nb078_alpha_dummy_310)) (Class.cv (nb078_alpha_dummy_311)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_310))
            (Class.cv (nb078_alpha_dummy_311)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0307 (g : Var) :
    (nb078_alpha_dummy_313 g) ∈
      (((syn_cnin (Class.cv (nb078_alpha_dummy_313 g))
            (Class.cv (nb078_alpha_dummy_314 g)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_313 g))
            (Class.cv (nb078_alpha_dummy_314 g)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0308 :
    (nb078_alpha_dummy_310) ∈
      (((Class.cv (nb078_alpha_dummy_310))).fv ∪ ((Class.cv (nb078_alpha_dummy_311))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0309 (g : Var) :
    (nb078_alpha_dummy_313 g) ∈
      (((Class.cv (nb078_alpha_dummy_313 g))).fv ∪ ((Class.cv (nb078_alpha_dummy_314 g))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0310 :
    (nb078_alpha_dummy_311) ∈
      (((syn_cnin (Class.cv (nb078_alpha_dummy_310)) (Class.cv (nb078_alpha_dummy_311)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_310))
            (Class.cv (nb078_alpha_dummy_311)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0311 (g : Var) :
    (nb078_alpha_dummy_314 g) ∈
      (((syn_cnin (Class.cv (nb078_alpha_dummy_313 g))
            (Class.cv (nb078_alpha_dummy_314 g)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_313 g))
            (Class.cv (nb078_alpha_dummy_314 g)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_0312 :
    (nb078_alpha_dummy_311) ∈
      (((Class.cv (nb078_alpha_dummy_310))).fv ∪ ((Class.cv (nb078_alpha_dummy_311))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
