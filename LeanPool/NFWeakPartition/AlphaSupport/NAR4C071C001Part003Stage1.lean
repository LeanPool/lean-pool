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
    (nb071_alpha_dummy_065) ∈
      (((Class.cv (nb071_alpha_dummy_065))).fv ∪ ((Class.cv (nb071_alpha_dummy_042))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0055 (x : Var) :
    (nb071_alpha_dummy_066 x) ∈
      (((Class.cv (nb071_alpha_dummy_066 x))).fv ∪ ((Class.cv (nb071_alpha_dummy_044 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0056 :
    (nb071_alpha_dummy_042) ∈
      (((syn_cen)).fv ∪ ((syn_csn (syn_cpw1 (Class.cv (nb071_alpha_dummy_042))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_csn]
  rw [fv_syn_cpw1]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0057 (x : Var) :
    (nb071_alpha_dummy_044 x) ∈
      (((syn_cen)).fv ∪ ((syn_csn (syn_cpw1 (Class.cv (nb071_alpha_dummy_044 x))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_csn]
  rw [fv_syn_cpw1]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0058 :
    (nb071_alpha_dummy_042) ∈ (((syn_cpw1 (Class.cv (nb071_alpha_dummy_042)))).fv) :=
  by
  rw [fv_syn_cpw1]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0059 (x : Var) :
    (nb071_alpha_dummy_044 x) ∈ (((syn_cpw1 (Class.cv (nb071_alpha_dummy_044 x)))).fv) :=
  by
  rw [fv_syn_cpw1]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0060 :
    (nb071_alpha_dummy_042) ∈
      (((syn_cnin (syn_cpw (Class.cv (nb071_alpha_dummy_042))) (syn_c1c))).fv ∪
        ((syn_cnin (syn_cpw (Class.cv (nb071_alpha_dummy_042))) (syn_c1c))).fv) :=
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
    (nb071_alpha_dummy_044 x) ∈
      (((syn_cnin (syn_cpw (Class.cv (nb071_alpha_dummy_044 x))) (syn_c1c))).fv ∪
        ((syn_cnin (syn_cpw (Class.cv (nb071_alpha_dummy_044 x))) (syn_c1c))).fv) :=
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
    (nb071_alpha_dummy_042) ∈
      (((syn_cpw (Class.cv (nb071_alpha_dummy_042)))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cpw]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0063 (x : Var) :
    (nb071_alpha_dummy_044 x) ∈
      (((syn_cpw (Class.cv (nb071_alpha_dummy_044 x)))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cpw]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0064 :
    (nb071_alpha_dummy_042) ∈ (((Class.cv (nb071_alpha_dummy_042))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0065 (x : Var) :
    (nb071_alpha_dummy_044 x) ∈ (((Class.cv (nb071_alpha_dummy_044 x))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0066 :
    (nb071_alpha_dummy_042) ∈
      (((syn_cnin (Class.cv (nb071_alpha_dummy_065)) (Class.cv (nb071_alpha_dummy_042)))).fv ∪
        ((syn_cnin (Class.cv (nb071_alpha_dummy_065))
            (Class.cv (nb071_alpha_dummy_042)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0067 (x : Var) :
    (nb071_alpha_dummy_044 x) ∈
      (((syn_cnin (Class.cv (nb071_alpha_dummy_066 x))
            (Class.cv (nb071_alpha_dummy_044 x)))).fv ∪
        ((syn_cnin (Class.cv (nb071_alpha_dummy_066 x))
            (Class.cv (nb071_alpha_dummy_044 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0068 :
    (nb071_alpha_dummy_042) ∈
      (((Class.cv (nb071_alpha_dummy_065))).fv ∪ ((Class.cv (nb071_alpha_dummy_042))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0069 (x : Var) :
    (nb071_alpha_dummy_044 x) ∈
      (((Class.cv (nb071_alpha_dummy_066 x))).fv ∪ ((Class.cv (nb071_alpha_dummy_044 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0070 :
    (nb071_alpha_dummy_056) ∈
      (((Class.cv (nb071_alpha_dummy_056))).fv ∪ ((Class.cv (nb071_alpha_dummy_055))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0071 :
    (nb071_alpha_dummy_056) ∈
      (((syn_ccompl (Class.cab (nb071_alpha_dummy_071)
              (syn_wrex (nb071_alpha_dummy_072) (Class.cv (nb071_alpha_dummy_056))
                (Wff.classEq (Class.cv (nb071_alpha_dummy_071))
                  (syn_cphi (Class.cv (nb071_alpha_dummy_072)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb071_alpha_dummy_071)
              (syn_wrex (nb071_alpha_dummy_072) (Class.cv (nb071_alpha_dummy_055))
                (Wff.classEq (Class.cv (nb071_alpha_dummy_071))
                  (syn_cun (syn_cphi (Class.cv (nb071_alpha_dummy_072)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb071_alpha_dummy_056) ≠ (nb071_alpha_dummy_071) from (by
          unfold nb071_alpha_dummy_071;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0070) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb071_alpha_dummy_056) ≠ (nb071_alpha_dummy_072) from (by
            unfold nb071_alpha_dummy_072;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0070) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb071_support_mem_0072 (x : Var) :
    (nb071_alpha_dummy_058 x) ∈
      (((Class.cv (nb071_alpha_dummy_058 x))).fv ∪ ((Class.cv (nb071_alpha_dummy_057 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0073 (x : Var) :
    (nb071_alpha_dummy_058 x) ∈
      (((syn_ccompl (Class.cab (nb071_alpha_dummy_073 x)
              (syn_wrex (nb071_alpha_dummy_074 x) (Class.cv (nb071_alpha_dummy_058 x))
                (Wff.classEq (Class.cv (nb071_alpha_dummy_073 x))
                  (syn_cphi (Class.cv (nb071_alpha_dummy_074 x)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb071_alpha_dummy_073 x)
              (syn_wrex (nb071_alpha_dummy_074 x) (Class.cv (nb071_alpha_dummy_057 x))
                (Wff.classEq (Class.cv (nb071_alpha_dummy_073 x))
                  (syn_cun (syn_cphi (Class.cv (nb071_alpha_dummy_074 x)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb071_alpha_dummy_058 x) ≠ (nb071_alpha_dummy_073 x) from (by
          unfold nb071_alpha_dummy_073;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0072 x) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb071_alpha_dummy_058 x) ≠ (nb071_alpha_dummy_074 x) from (by
            unfold nb071_alpha_dummy_074;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0072 x) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb071_support_mem_0074 :
    (nb071_alpha_dummy_056) ∈
      (((Class.cab (nb071_alpha_dummy_071)
            (syn_wrex (nb071_alpha_dummy_072) (Class.cv (nb071_alpha_dummy_056))
              (Wff.classEq (Class.cv (nb071_alpha_dummy_071))
                (syn_cphi (Class.cv (nb071_alpha_dummy_072))))))).fv ∪
        ((Class.cab (nb071_alpha_dummy_071)
            (syn_wrex (nb071_alpha_dummy_072) (Class.cv (nb071_alpha_dummy_056))
              (Wff.classEq (Class.cv (nb071_alpha_dummy_071))
                (syn_cphi (Class.cv (nb071_alpha_dummy_072))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb071_alpha_dummy_056) ≠ (nb071_alpha_dummy_071) from (by
          unfold nb071_alpha_dummy_071;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0070) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb071_alpha_dummy_056) ≠ (nb071_alpha_dummy_072) from (by
            unfold nb071_alpha_dummy_072;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0070) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb071_support_mem_0075 (x : Var) :
    (nb071_alpha_dummy_058 x) ∈
      (((Class.cab (nb071_alpha_dummy_073 x)
            (syn_wrex (nb071_alpha_dummy_074 x) (Class.cv (nb071_alpha_dummy_058 x))
              (Wff.classEq (Class.cv (nb071_alpha_dummy_073 x))
                (syn_cphi (Class.cv (nb071_alpha_dummy_074 x))))))).fv ∪
        ((Class.cab (nb071_alpha_dummy_073 x)
            (syn_wrex (nb071_alpha_dummy_074 x) (Class.cv (nb071_alpha_dummy_058 x))
              (Wff.classEq (Class.cv (nb071_alpha_dummy_073 x))
                (syn_cphi (Class.cv (nb071_alpha_dummy_074 x))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb071_alpha_dummy_058 x) ≠ (nb071_alpha_dummy_073 x) from (by
          unfold nb071_alpha_dummy_073;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0072 x) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb071_alpha_dummy_058 x) ≠ (nb071_alpha_dummy_074 x) from (by
            unfold nb071_alpha_dummy_074;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0072 x) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb071_support_mem_0076 :
    (nb071_alpha_dummy_072) ∈ (((Class.cv (nb071_alpha_dummy_072))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0077 (x : Var) :
    (nb071_alpha_dummy_074 x) ∈ (((Class.cv (nb071_alpha_dummy_074 x))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0078 :
    (nb071_alpha_dummy_079) ∈
      (((Wff.classMem (Class.cv (nb071_alpha_dummy_079)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb071_alpha_dummy_079)) (syn_c1c))).fv ∪
        ((Class.cv (nb071_alpha_dummy_079))).fv) :=
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
    (nb071_alpha_dummy_081 x) ∈
      (((Wff.classMem (Class.cv (nb071_alpha_dummy_081 x)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb071_alpha_dummy_081 x)) (syn_c1c))).fv ∪
        ((Class.cv (nb071_alpha_dummy_081 x))).fv) :=
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
    (nb071_alpha_dummy_079) ∈
      (((Class.cv (nb071_alpha_dummy_079))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0081 (x : Var) :
    (nb071_alpha_dummy_081 x) ∈
      (((Class.cv (nb071_alpha_dummy_081 x))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0082 :
    (nb071_alpha_dummy_086) ∈
      (((syn_cnin (Class.cv (nb071_alpha_dummy_086)) (Class.cv (nb071_alpha_dummy_087)))).fv ∪
        ((syn_cnin (Class.cv (nb071_alpha_dummy_086))
            (Class.cv (nb071_alpha_dummy_087)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0083 (x : Var) :
    (nb071_alpha_dummy_089 x) ∈
      (((syn_cnin (Class.cv (nb071_alpha_dummy_089 x))
            (Class.cv (nb071_alpha_dummy_090 x)))).fv ∪
        ((syn_cnin (Class.cv (nb071_alpha_dummy_089 x))
            (Class.cv (nb071_alpha_dummy_090 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0084 :
    (nb071_alpha_dummy_086) ∈
      (((Class.cv (nb071_alpha_dummy_086))).fv ∪ ((Class.cv (nb071_alpha_dummy_087))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0085 (x : Var) :
    (nb071_alpha_dummy_089 x) ∈
      (((Class.cv (nb071_alpha_dummy_089 x))).fv ∪ ((Class.cv (nb071_alpha_dummy_090 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0086 :
    (nb071_alpha_dummy_087) ∈
      (((syn_cnin (Class.cv (nb071_alpha_dummy_086)) (Class.cv (nb071_alpha_dummy_087)))).fv ∪
        ((syn_cnin (Class.cv (nb071_alpha_dummy_086))
            (Class.cv (nb071_alpha_dummy_087)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0087 (x : Var) :
    (nb071_alpha_dummy_090 x) ∈
      (((syn_cnin (Class.cv (nb071_alpha_dummy_089 x))
            (Class.cv (nb071_alpha_dummy_090 x)))).fv ∪
        ((syn_cnin (Class.cv (nb071_alpha_dummy_089 x))
            (Class.cv (nb071_alpha_dummy_090 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0088 :
    (nb071_alpha_dummy_087) ∈
      (((Class.cv (nb071_alpha_dummy_086))).fv ∪ ((Class.cv (nb071_alpha_dummy_087))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0089 (x : Var) :
    (nb071_alpha_dummy_090 x) ∈
      (((Class.cv (nb071_alpha_dummy_089 x))).fv ∪ ((Class.cv (nb071_alpha_dummy_090 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0090 :
    (nb071_alpha_dummy_086) ∈
      (((syn_ccompl (Class.cv (nb071_alpha_dummy_086)))).fv ∪
        ((syn_ccompl (Class.cv (nb071_alpha_dummy_087)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0091 (x : Var) :
    (nb071_alpha_dummy_089 x) ∈
      (((syn_ccompl (Class.cv (nb071_alpha_dummy_089 x)))).fv ∪
        ((syn_ccompl (Class.cv (nb071_alpha_dummy_090 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0092 :
    (nb071_alpha_dummy_086) ∈
      (((Class.cv (nb071_alpha_dummy_086))).fv ∪ ((Class.cv (nb071_alpha_dummy_086))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0093 (x : Var) :
    (nb071_alpha_dummy_089 x) ∈
      (((Class.cv (nb071_alpha_dummy_089 x))).fv ∪ ((Class.cv (nb071_alpha_dummy_089 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0094 :
    (nb071_alpha_dummy_087) ∈
      (((syn_ccompl (Class.cv (nb071_alpha_dummy_086)))).fv ∪
        ((syn_ccompl (Class.cv (nb071_alpha_dummy_087)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0095 (x : Var) :
    (nb071_alpha_dummy_090 x) ∈
      (((syn_ccompl (Class.cv (nb071_alpha_dummy_089 x)))).fv ∪
        ((syn_ccompl (Class.cv (nb071_alpha_dummy_090 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0096 :
    (nb071_alpha_dummy_087) ∈
      (((Class.cv (nb071_alpha_dummy_087))).fv ∪ ((Class.cv (nb071_alpha_dummy_087))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0097 (x : Var) :
    (nb071_alpha_dummy_090 x) ∈
      (((Class.cv (nb071_alpha_dummy_090 x))).fv ∪ ((Class.cv (nb071_alpha_dummy_090 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0098 :
    (nb071_alpha_dummy_055) ∈
      (((Class.cv (nb071_alpha_dummy_056))).fv ∪ ((Class.cv (nb071_alpha_dummy_055))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0099 :
    (nb071_alpha_dummy_055) ∈
      (((syn_ccompl (Class.cab (nb071_alpha_dummy_071)
              (syn_wrex (nb071_alpha_dummy_072) (Class.cv (nb071_alpha_dummy_056))
                (Wff.classEq (Class.cv (nb071_alpha_dummy_071))
                  (syn_cphi (Class.cv (nb071_alpha_dummy_072)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb071_alpha_dummy_071)
              (syn_wrex (nb071_alpha_dummy_072) (Class.cv (nb071_alpha_dummy_055))
                (Wff.classEq (Class.cv (nb071_alpha_dummy_071))
                  (syn_cun (syn_cphi (Class.cv (nb071_alpha_dummy_072)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb071_alpha_dummy_055) ≠ (nb071_alpha_dummy_071) from (by
          unfold nb071_alpha_dummy_071;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0098) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb071_alpha_dummy_055) ≠ (nb071_alpha_dummy_072) from (by
            unfold nb071_alpha_dummy_072;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0098) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb071_support_mem_0100 (x : Var) :
    (nb071_alpha_dummy_057 x) ∈
      (((Class.cv (nb071_alpha_dummy_058 x))).fv ∪ ((Class.cv (nb071_alpha_dummy_057 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0101 (x : Var) :
    (nb071_alpha_dummy_057 x) ∈
      (((syn_ccompl (Class.cab (nb071_alpha_dummy_073 x)
              (syn_wrex (nb071_alpha_dummy_074 x) (Class.cv (nb071_alpha_dummy_058 x))
                (Wff.classEq (Class.cv (nb071_alpha_dummy_073 x))
                  (syn_cphi (Class.cv (nb071_alpha_dummy_074 x)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb071_alpha_dummy_073 x)
              (syn_wrex (nb071_alpha_dummy_074 x) (Class.cv (nb071_alpha_dummy_057 x))
                (Wff.classEq (Class.cv (nb071_alpha_dummy_073 x))
                  (syn_cun (syn_cphi (Class.cv (nb071_alpha_dummy_074 x)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb071_alpha_dummy_057 x) ≠ (nb071_alpha_dummy_073 x) from (by
          unfold nb071_alpha_dummy_073;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0100 x) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb071_alpha_dummy_057 x) ≠ (nb071_alpha_dummy_074 x) from (by
            unfold nb071_alpha_dummy_074;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0100 x) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb071_support_mem_0102 :
    (nb071_alpha_dummy_055) ∈
      (((Class.cab (nb071_alpha_dummy_071)
            (syn_wrex (nb071_alpha_dummy_072) (Class.cv (nb071_alpha_dummy_055))
              (Wff.classEq (Class.cv (nb071_alpha_dummy_071))
                (syn_cun (syn_cphi (Class.cv (nb071_alpha_dummy_072)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb071_alpha_dummy_071)
            (syn_wrex (nb071_alpha_dummy_072) (Class.cv (nb071_alpha_dummy_055))
              (Wff.classEq (Class.cv (nb071_alpha_dummy_071))
                (syn_cun (syn_cphi (Class.cv (nb071_alpha_dummy_072)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb071_alpha_dummy_055) ≠ (nb071_alpha_dummy_071) from (by
          unfold nb071_alpha_dummy_071;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0098) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb071_alpha_dummy_055) ≠ (nb071_alpha_dummy_072) from (by
            unfold nb071_alpha_dummy_072;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0098) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb071_support_mem_0103 (x : Var) :
    (nb071_alpha_dummy_057 x) ∈
      (((Class.cab (nb071_alpha_dummy_073 x)
            (syn_wrex (nb071_alpha_dummy_074 x) (Class.cv (nb071_alpha_dummy_057 x))
              (Wff.classEq (Class.cv (nb071_alpha_dummy_073 x))
                (syn_cun (syn_cphi (Class.cv (nb071_alpha_dummy_074 x)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb071_alpha_dummy_073 x)
            (syn_wrex (nb071_alpha_dummy_074 x) (Class.cv (nb071_alpha_dummy_057 x))
              (Wff.classEq (Class.cv (nb071_alpha_dummy_073 x))
                (syn_cun (syn_cphi (Class.cv (nb071_alpha_dummy_074 x)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb071_alpha_dummy_057 x) ≠ (nb071_alpha_dummy_073 x) from (by
          unfold nb071_alpha_dummy_073;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0100 x) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb071_alpha_dummy_057 x) ≠ (nb071_alpha_dummy_074 x) from (by
            unfold nb071_alpha_dummy_074;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb071_support_mem_0100 x) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb071_support_mem_0104 :
    (nb071_alpha_dummy_072) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb071_alpha_dummy_072))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0105 (x : Var) :
    (nb071_alpha_dummy_074 x) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb071_alpha_dummy_074 x))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0106 :
    (nb071_alpha_dummy_072) ∈
      (((syn_cphi (Class.cv (nb071_alpha_dummy_072)))).fv ∪
        ((syn_cphi (Class.cv (nb071_alpha_dummy_072)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0107 (x : Var) :
    (nb071_alpha_dummy_074 x) ∈
      (((syn_cphi (Class.cv (nb071_alpha_dummy_074 x)))).fv ∪
        ((syn_cphi (Class.cv (nb071_alpha_dummy_074 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0108 :
    (nb071_alpha_dummy_045) ∈ (((Class.cv (nb071_alpha_dummy_045))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_support_mem_0109 (x : Var) :
    (nb071_alpha_dummy_046 x) ∈ (((Class.cv (nb071_alpha_dummy_046 x))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb071_compact_fv_empty_0020 : (nb071_alpha_dummy_001) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb071_compact_fv_empty_0021 (x : Var) :
    (nb071_alpha_dummy_002 x) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb071_compact_fv_empty_0022 : (nb071_alpha_dummy_000) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb071_compact_fv_empty_0023 (x : Var) : x ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb071_compact_fv_empty_0024 : (nb071_alpha_dummy_003) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb071_compact_fv_empty_0025 (x : Var) :
    (nb071_alpha_dummy_004 x) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
