/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NAR4H5C093M3Part001

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `AlphaSupport.NAR4H5C093M3Part002Stage1`. -/


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

theorem nb093_support_mem_0051 (r : Var) :
    r ∈ (((Class.cv r)).fv ∪ ((syn_ccompl (syn_ccnv (Class.cv r)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0052 (A : Class) :
    (nb093_alpha_dummy_058 A) ∈
      (({(nb093_alpha_dummy_058 A)} : Finset Var) ∪ ({(nb093_alpha_dummy_059 A)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb093_alpha_dummy_059 A)) (Class.cv (nb093_alpha_dummy_001 A))
            (Class.cv (nb093_alpha_dummy_058 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0053 (r : Var) :
    (nb093_alpha_dummy_060 r) ∈
      (({(nb093_alpha_dummy_060 r)} : Finset Var) ∪ ({(nb093_alpha_dummy_061 r)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb093_alpha_dummy_061 r)) (Class.cv r)
            (Class.cv (nb093_alpha_dummy_060 r)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0054 (A : Class) :
    (nb093_alpha_dummy_059 A) ∈
      (({(nb093_alpha_dummy_058 A)} : Finset Var) ∪ ({(nb093_alpha_dummy_059 A)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb093_alpha_dummy_059 A)) (Class.cv (nb093_alpha_dummy_001 A))
            (Class.cv (nb093_alpha_dummy_058 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0055 (r : Var) :
    (nb093_alpha_dummy_061 r) ∈
      (({(nb093_alpha_dummy_060 r)} : Finset Var) ∪ ({(nb093_alpha_dummy_061 r)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb093_alpha_dummy_061 r)) (Class.cv r)
            (Class.cv (nb093_alpha_dummy_060 r)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0056 (A : Class) :
    (nb093_alpha_dummy_058 A) ∈
      (((Class.cv (nb093_alpha_dummy_058 A))).fv ∪ ((Class.cv (nb093_alpha_dummy_059 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0057 (A : Class) :
    (nb093_alpha_dummy_058 A) ∈
      (((syn_ccompl (Class.cab (nb093_alpha_dummy_064 A)
              (syn_wrex (nb093_alpha_dummy_065 A) (Class.cv (nb093_alpha_dummy_058 A))
                (Wff.classEq (Class.cv (nb093_alpha_dummy_064 A))
                  (syn_cphi (Class.cv (nb093_alpha_dummy_065 A)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb093_alpha_dummy_064 A)
              (syn_wrex (nb093_alpha_dummy_065 A) (Class.cv (nb093_alpha_dummy_059 A))
                (Wff.classEq (Class.cv (nb093_alpha_dummy_064 A))
                  (syn_cun (syn_cphi (Class.cv (nb093_alpha_dummy_065 A)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb093_alpha_dummy_058 A) ≠ (nb093_alpha_dummy_064 A) from (by
          unfold nb093_alpha_dummy_064;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0056 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb093_alpha_dummy_058 A) ≠ (nb093_alpha_dummy_065 A) from (by
            unfold nb093_alpha_dummy_065;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0056 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb093_support_mem_0058 (r : Var) :
    (nb093_alpha_dummy_060 r) ∈
      (((Class.cv (nb093_alpha_dummy_060 r))).fv ∪ ((Class.cv (nb093_alpha_dummy_061 r))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0059 (r : Var) :
    (nb093_alpha_dummy_060 r) ∈
      (((syn_ccompl (Class.cab (nb093_alpha_dummy_066 r)
              (syn_wrex (nb093_alpha_dummy_067 r) (Class.cv (nb093_alpha_dummy_060 r))
                (Wff.classEq (Class.cv (nb093_alpha_dummy_066 r))
                  (syn_cphi (Class.cv (nb093_alpha_dummy_067 r)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb093_alpha_dummy_066 r)
              (syn_wrex (nb093_alpha_dummy_067 r) (Class.cv (nb093_alpha_dummy_061 r))
                (Wff.classEq (Class.cv (nb093_alpha_dummy_066 r))
                  (syn_cun (syn_cphi (Class.cv (nb093_alpha_dummy_067 r)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb093_alpha_dummy_060 r) ≠ (nb093_alpha_dummy_066 r) from (by
          unfold nb093_alpha_dummy_066;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0058 r) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb093_alpha_dummy_060 r) ≠ (nb093_alpha_dummy_067 r) from (by
            unfold nb093_alpha_dummy_067;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0058 r) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb093_support_mem_0060 (A : Class) :
    (nb093_alpha_dummy_058 A) ∈
      (((Class.cab (nb093_alpha_dummy_064 A)
            (syn_wrex (nb093_alpha_dummy_065 A) (Class.cv (nb093_alpha_dummy_058 A))
              (Wff.classEq (Class.cv (nb093_alpha_dummy_064 A))
                (syn_cphi (Class.cv (nb093_alpha_dummy_065 A))))))).fv ∪
        ((Class.cab (nb093_alpha_dummy_064 A)
            (syn_wrex (nb093_alpha_dummy_065 A) (Class.cv (nb093_alpha_dummy_058 A))
              (Wff.classEq (Class.cv (nb093_alpha_dummy_064 A))
                (syn_cphi (Class.cv (nb093_alpha_dummy_065 A))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb093_alpha_dummy_058 A) ≠ (nb093_alpha_dummy_064 A) from (by
          unfold nb093_alpha_dummy_064;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0056 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb093_alpha_dummy_058 A) ≠ (nb093_alpha_dummy_065 A) from (by
            unfold nb093_alpha_dummy_065;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0056 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb093_support_mem_0061 (r : Var) :
    (nb093_alpha_dummy_060 r) ∈
      (((Class.cab (nb093_alpha_dummy_066 r)
            (syn_wrex (nb093_alpha_dummy_067 r) (Class.cv (nb093_alpha_dummy_060 r))
              (Wff.classEq (Class.cv (nb093_alpha_dummy_066 r))
                (syn_cphi (Class.cv (nb093_alpha_dummy_067 r))))))).fv ∪
        ((Class.cab (nb093_alpha_dummy_066 r)
            (syn_wrex (nb093_alpha_dummy_067 r) (Class.cv (nb093_alpha_dummy_060 r))
              (Wff.classEq (Class.cv (nb093_alpha_dummy_066 r))
                (syn_cphi (Class.cv (nb093_alpha_dummy_067 r))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb093_alpha_dummy_060 r) ≠ (nb093_alpha_dummy_066 r) from (by
          unfold nb093_alpha_dummy_066;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0058 r) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb093_alpha_dummy_060 r) ≠ (nb093_alpha_dummy_067 r) from (by
            unfold nb093_alpha_dummy_067;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0058 r) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb093_support_mem_0062 (A : Class) :
    (nb093_alpha_dummy_065 A) ∈ (((Class.cv (nb093_alpha_dummy_065 A))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0063 (r : Var) :
    (nb093_alpha_dummy_067 r) ∈ (((Class.cv (nb093_alpha_dummy_067 r))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0064 (A : Class) :
    (nb093_alpha_dummy_072 A) ∈
      (((Wff.classMem (Class.cv (nb093_alpha_dummy_072 A)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb093_alpha_dummy_072 A)) (syn_c1c))).fv ∪
        ((Class.cv (nb093_alpha_dummy_072 A))).fv) :=
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

theorem nb093_support_mem_0065 (r : Var) :
    (nb093_alpha_dummy_074 r) ∈
      (((Wff.classMem (Class.cv (nb093_alpha_dummy_074 r)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb093_alpha_dummy_074 r)) (syn_c1c))).fv ∪
        ((Class.cv (nb093_alpha_dummy_074 r))).fv) :=
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

theorem nb093_support_mem_0066 (A : Class) :
    (nb093_alpha_dummy_072 A) ∈
      (((Class.cv (nb093_alpha_dummy_072 A))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0067 (r : Var) :
    (nb093_alpha_dummy_074 r) ∈
      (((Class.cv (nb093_alpha_dummy_074 r))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0068 (A : Class) :
    (nb093_alpha_dummy_079 A) ∈
      (((syn_cnin (Class.cv (nb093_alpha_dummy_079 A))
            (Class.cv (nb093_alpha_dummy_080 A)))).fv ∪
        ((syn_cnin (Class.cv (nb093_alpha_dummy_079 A))
            (Class.cv (nb093_alpha_dummy_080 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0069 (r : Var) :
    (nb093_alpha_dummy_082 r) ∈
      (((syn_cnin (Class.cv (nb093_alpha_dummy_082 r))
            (Class.cv (nb093_alpha_dummy_083 r)))).fv ∪
        ((syn_cnin (Class.cv (nb093_alpha_dummy_082 r))
            (Class.cv (nb093_alpha_dummy_083 r)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0070 (A : Class) :
    (nb093_alpha_dummy_079 A) ∈
      (((Class.cv (nb093_alpha_dummy_079 A))).fv ∪ ((Class.cv (nb093_alpha_dummy_080 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0071 (r : Var) :
    (nb093_alpha_dummy_082 r) ∈
      (((Class.cv (nb093_alpha_dummy_082 r))).fv ∪ ((Class.cv (nb093_alpha_dummy_083 r))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0072 (A : Class) :
    (nb093_alpha_dummy_080 A) ∈
      (((syn_cnin (Class.cv (nb093_alpha_dummy_079 A))
            (Class.cv (nb093_alpha_dummy_080 A)))).fv ∪
        ((syn_cnin (Class.cv (nb093_alpha_dummy_079 A))
            (Class.cv (nb093_alpha_dummy_080 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0073 (r : Var) :
    (nb093_alpha_dummy_083 r) ∈
      (((syn_cnin (Class.cv (nb093_alpha_dummy_082 r))
            (Class.cv (nb093_alpha_dummy_083 r)))).fv ∪
        ((syn_cnin (Class.cv (nb093_alpha_dummy_082 r))
            (Class.cv (nb093_alpha_dummy_083 r)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0074 (A : Class) :
    (nb093_alpha_dummy_080 A) ∈
      (((Class.cv (nb093_alpha_dummy_079 A))).fv ∪ ((Class.cv (nb093_alpha_dummy_080 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0075 (r : Var) :
    (nb093_alpha_dummy_083 r) ∈
      (((Class.cv (nb093_alpha_dummy_082 r))).fv ∪ ((Class.cv (nb093_alpha_dummy_083 r))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0076 (A : Class) :
    (nb093_alpha_dummy_079 A) ∈
      (((syn_ccompl (Class.cv (nb093_alpha_dummy_079 A)))).fv ∪
        ((syn_ccompl (Class.cv (nb093_alpha_dummy_080 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0077 (r : Var) :
    (nb093_alpha_dummy_082 r) ∈
      (((syn_ccompl (Class.cv (nb093_alpha_dummy_082 r)))).fv ∪
        ((syn_ccompl (Class.cv (nb093_alpha_dummy_083 r)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0078 (A : Class) :
    (nb093_alpha_dummy_079 A) ∈
      (((Class.cv (nb093_alpha_dummy_079 A))).fv ∪ ((Class.cv (nb093_alpha_dummy_079 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0079 (r : Var) :
    (nb093_alpha_dummy_082 r) ∈
      (((Class.cv (nb093_alpha_dummy_082 r))).fv ∪ ((Class.cv (nb093_alpha_dummy_082 r))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0080 (A : Class) :
    (nb093_alpha_dummy_080 A) ∈
      (((syn_ccompl (Class.cv (nb093_alpha_dummy_079 A)))).fv ∪
        ((syn_ccompl (Class.cv (nb093_alpha_dummy_080 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0081 (r : Var) :
    (nb093_alpha_dummy_083 r) ∈
      (((syn_ccompl (Class.cv (nb093_alpha_dummy_082 r)))).fv ∪
        ((syn_ccompl (Class.cv (nb093_alpha_dummy_083 r)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0082 (A : Class) :
    (nb093_alpha_dummy_080 A) ∈
      (((Class.cv (nb093_alpha_dummy_080 A))).fv ∪ ((Class.cv (nb093_alpha_dummy_080 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0083 (r : Var) :
    (nb093_alpha_dummy_083 r) ∈
      (((Class.cv (nb093_alpha_dummy_083 r))).fv ∪ ((Class.cv (nb093_alpha_dummy_083 r))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0084 (A : Class) :
    (nb093_alpha_dummy_059 A) ∈
      (((Class.cv (nb093_alpha_dummy_058 A))).fv ∪ ((Class.cv (nb093_alpha_dummy_059 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0085 (A : Class) :
    (nb093_alpha_dummy_059 A) ∈
      (((syn_ccompl (Class.cab (nb093_alpha_dummy_064 A)
              (syn_wrex (nb093_alpha_dummy_065 A) (Class.cv (nb093_alpha_dummy_058 A))
                (Wff.classEq (Class.cv (nb093_alpha_dummy_064 A))
                  (syn_cphi (Class.cv (nb093_alpha_dummy_065 A)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb093_alpha_dummy_064 A)
              (syn_wrex (nb093_alpha_dummy_065 A) (Class.cv (nb093_alpha_dummy_059 A))
                (Wff.classEq (Class.cv (nb093_alpha_dummy_064 A))
                  (syn_cun (syn_cphi (Class.cv (nb093_alpha_dummy_065 A)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb093_alpha_dummy_059 A) ≠ (nb093_alpha_dummy_064 A) from (by
          unfold nb093_alpha_dummy_064;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0084 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb093_alpha_dummy_059 A) ≠ (nb093_alpha_dummy_065 A) from (by
            unfold nb093_alpha_dummy_065;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0084 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb093_support_mem_0086 (r : Var) :
    (nb093_alpha_dummy_061 r) ∈
      (((Class.cv (nb093_alpha_dummy_060 r))).fv ∪ ((Class.cv (nb093_alpha_dummy_061 r))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0087 (r : Var) :
    (nb093_alpha_dummy_061 r) ∈
      (((syn_ccompl (Class.cab (nb093_alpha_dummy_066 r)
              (syn_wrex (nb093_alpha_dummy_067 r) (Class.cv (nb093_alpha_dummy_060 r))
                (Wff.classEq (Class.cv (nb093_alpha_dummy_066 r))
                  (syn_cphi (Class.cv (nb093_alpha_dummy_067 r)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb093_alpha_dummy_066 r)
              (syn_wrex (nb093_alpha_dummy_067 r) (Class.cv (nb093_alpha_dummy_061 r))
                (Wff.classEq (Class.cv (nb093_alpha_dummy_066 r))
                  (syn_cun (syn_cphi (Class.cv (nb093_alpha_dummy_067 r)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb093_alpha_dummy_061 r) ≠ (nb093_alpha_dummy_066 r) from (by
          unfold nb093_alpha_dummy_066;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0086 r) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb093_alpha_dummy_061 r) ≠ (nb093_alpha_dummy_067 r) from (by
            unfold nb093_alpha_dummy_067;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0086 r) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb093_support_mem_0088 (A : Class) :
    (nb093_alpha_dummy_059 A) ∈
      (((Class.cab (nb093_alpha_dummy_064 A)
            (syn_wrex (nb093_alpha_dummy_065 A) (Class.cv (nb093_alpha_dummy_059 A))
              (Wff.classEq (Class.cv (nb093_alpha_dummy_064 A))
                (syn_cun (syn_cphi (Class.cv (nb093_alpha_dummy_065 A)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb093_alpha_dummy_064 A)
            (syn_wrex (nb093_alpha_dummy_065 A) (Class.cv (nb093_alpha_dummy_059 A))
              (Wff.classEq (Class.cv (nb093_alpha_dummy_064 A))
                (syn_cun (syn_cphi (Class.cv (nb093_alpha_dummy_065 A)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb093_alpha_dummy_059 A) ≠ (nb093_alpha_dummy_064 A) from (by
          unfold nb093_alpha_dummy_064;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0084 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb093_alpha_dummy_059 A) ≠ (nb093_alpha_dummy_065 A) from (by
            unfold nb093_alpha_dummy_065;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0084 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb093_support_mem_0089 (r : Var) :
    (nb093_alpha_dummy_061 r) ∈
      (((Class.cab (nb093_alpha_dummy_066 r)
            (syn_wrex (nb093_alpha_dummy_067 r) (Class.cv (nb093_alpha_dummy_061 r))
              (Wff.classEq (Class.cv (nb093_alpha_dummy_066 r))
                (syn_cun (syn_cphi (Class.cv (nb093_alpha_dummy_067 r)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb093_alpha_dummy_066 r)
            (syn_wrex (nb093_alpha_dummy_067 r) (Class.cv (nb093_alpha_dummy_061 r))
              (Wff.classEq (Class.cv (nb093_alpha_dummy_066 r))
                (syn_cun (syn_cphi (Class.cv (nb093_alpha_dummy_067 r)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb093_alpha_dummy_061 r) ≠ (nb093_alpha_dummy_066 r) from (by
          unfold nb093_alpha_dummy_066;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0086 r) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb093_alpha_dummy_061 r) ≠ (nb093_alpha_dummy_067 r) from (by
            unfold nb093_alpha_dummy_067;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0086 r) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb093_support_mem_0090 (A : Class) :
    (nb093_alpha_dummy_065 A) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb093_alpha_dummy_065 A))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0091 (r : Var) :
    (nb093_alpha_dummy_067 r) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb093_alpha_dummy_067 r))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0092 (A : Class) :
    (nb093_alpha_dummy_065 A) ∈
      (((syn_cphi (Class.cv (nb093_alpha_dummy_065 A)))).fv ∪
        ((syn_cphi (Class.cv (nb093_alpha_dummy_065 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0093 (r : Var) :
    (nb093_alpha_dummy_067 r) ∈
      (((syn_cphi (Class.cv (nb093_alpha_dummy_067 r)))).fv ∪
        ((syn_cphi (Class.cv (nb093_alpha_dummy_067 r)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0094 (A : Class) :
    (nb093_alpha_dummy_059 A) ∈
      (((Class.cv (nb093_alpha_dummy_059 A))).fv ∪ ((Class.cv (nb093_alpha_dummy_058 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0095 (A : Class) :
    (nb093_alpha_dummy_059 A) ∈
      (((syn_ccompl (Class.cab (nb093_alpha_dummy_100 A)
              (syn_wrex (nb093_alpha_dummy_101 A) (Class.cv (nb093_alpha_dummy_059 A))
                (Wff.classEq (Class.cv (nb093_alpha_dummy_100 A))
                  (syn_cphi (Class.cv (nb093_alpha_dummy_101 A)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb093_alpha_dummy_100 A)
              (syn_wrex (nb093_alpha_dummy_101 A) (Class.cv (nb093_alpha_dummy_058 A))
                (Wff.classEq (Class.cv (nb093_alpha_dummy_100 A))
                  (syn_cun (syn_cphi (Class.cv (nb093_alpha_dummy_101 A)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb093_alpha_dummy_059 A) ≠ (nb093_alpha_dummy_100 A) from (by
          unfold nb093_alpha_dummy_100;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0094 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb093_alpha_dummy_059 A) ≠ (nb093_alpha_dummy_101 A) from (by
            unfold nb093_alpha_dummy_101;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0094 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb093_support_mem_0096 (r : Var) :
    (nb093_alpha_dummy_061 r) ∈
      (((Class.cv (nb093_alpha_dummy_061 r))).fv ∪ ((Class.cv (nb093_alpha_dummy_060 r))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0097 (r : Var) :
    (nb093_alpha_dummy_061 r) ∈
      (((syn_ccompl (Class.cab (nb093_alpha_dummy_102 r)
              (syn_wrex (nb093_alpha_dummy_103 r) (Class.cv (nb093_alpha_dummy_061 r))
                (Wff.classEq (Class.cv (nb093_alpha_dummy_102 r))
                  (syn_cphi (Class.cv (nb093_alpha_dummy_103 r)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb093_alpha_dummy_102 r)
              (syn_wrex (nb093_alpha_dummy_103 r) (Class.cv (nb093_alpha_dummy_060 r))
                (Wff.classEq (Class.cv (nb093_alpha_dummy_102 r))
                  (syn_cun (syn_cphi (Class.cv (nb093_alpha_dummy_103 r)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb093_alpha_dummy_061 r) ≠ (nb093_alpha_dummy_102 r) from (by
          unfold nb093_alpha_dummy_102;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0096 r) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb093_alpha_dummy_061 r) ≠ (nb093_alpha_dummy_103 r) from (by
            unfold nb093_alpha_dummy_103;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0096 r) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb093_support_mem_0098 (A : Class) :
    (nb093_alpha_dummy_059 A) ∈
      (((Class.cab (nb093_alpha_dummy_100 A)
            (syn_wrex (nb093_alpha_dummy_101 A) (Class.cv (nb093_alpha_dummy_059 A))
              (Wff.classEq (Class.cv (nb093_alpha_dummy_100 A))
                (syn_cphi (Class.cv (nb093_alpha_dummy_101 A))))))).fv ∪
        ((Class.cab (nb093_alpha_dummy_100 A)
            (syn_wrex (nb093_alpha_dummy_101 A) (Class.cv (nb093_alpha_dummy_059 A))
              (Wff.classEq (Class.cv (nb093_alpha_dummy_100 A))
                (syn_cphi (Class.cv (nb093_alpha_dummy_101 A))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb093_alpha_dummy_059 A) ≠ (nb093_alpha_dummy_100 A) from (by
          unfold nb093_alpha_dummy_100;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0094 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb093_alpha_dummy_059 A) ≠ (nb093_alpha_dummy_101 A) from (by
            unfold nb093_alpha_dummy_101;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0094 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb093_support_mem_0099 (r : Var) :
    (nb093_alpha_dummy_061 r) ∈
      (((Class.cab (nb093_alpha_dummy_102 r)
            (syn_wrex (nb093_alpha_dummy_103 r) (Class.cv (nb093_alpha_dummy_061 r))
              (Wff.classEq (Class.cv (nb093_alpha_dummy_102 r))
                (syn_cphi (Class.cv (nb093_alpha_dummy_103 r))))))).fv ∪
        ((Class.cab (nb093_alpha_dummy_102 r)
            (syn_wrex (nb093_alpha_dummy_103 r) (Class.cv (nb093_alpha_dummy_061 r))
              (Wff.classEq (Class.cv (nb093_alpha_dummy_102 r))
                (syn_cphi (Class.cv (nb093_alpha_dummy_103 r))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb093_alpha_dummy_061 r) ≠ (nb093_alpha_dummy_102 r) from (by
          unfold nb093_alpha_dummy_102;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0096 r) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb093_alpha_dummy_061 r) ≠ (nb093_alpha_dummy_103 r) from (by
            unfold nb093_alpha_dummy_103;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0096 r) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb093_support_mem_0100 (A : Class) :
    (nb093_alpha_dummy_101 A) ∈ (((Class.cv (nb093_alpha_dummy_101 A))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0101 (r : Var) :
    (nb093_alpha_dummy_103 r) ∈ (((Class.cv (nb093_alpha_dummy_103 r))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0102 (A : Class) :
    (nb093_alpha_dummy_108 A) ∈
      (((Wff.classMem (Class.cv (nb093_alpha_dummy_108 A)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb093_alpha_dummy_108 A)) (syn_c1c))).fv ∪
        ((Class.cv (nb093_alpha_dummy_108 A))).fv) :=
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

theorem nb093_support_mem_0103 (r : Var) :
    (nb093_alpha_dummy_110 r) ∈
      (((Wff.classMem (Class.cv (nb093_alpha_dummy_110 r)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb093_alpha_dummy_110 r)) (syn_c1c))).fv ∪
        ((Class.cv (nb093_alpha_dummy_110 r))).fv) :=
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

theorem nb093_support_mem_0104 (A : Class) :
    (nb093_alpha_dummy_108 A) ∈
      (((Class.cv (nb093_alpha_dummy_108 A))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0105 (r : Var) :
    (nb093_alpha_dummy_110 r) ∈
      (((Class.cv (nb093_alpha_dummy_110 r))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0106 (A : Class) :
    (nb093_alpha_dummy_115 A) ∈
      (((syn_cnin (Class.cv (nb093_alpha_dummy_115 A))
            (Class.cv (nb093_alpha_dummy_116 A)))).fv ∪
        ((syn_cnin (Class.cv (nb093_alpha_dummy_115 A))
            (Class.cv (nb093_alpha_dummy_116 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0107 (r : Var) :
    (nb093_alpha_dummy_118 r) ∈
      (((syn_cnin (Class.cv (nb093_alpha_dummy_118 r))
            (Class.cv (nb093_alpha_dummy_119 r)))).fv ∪
        ((syn_cnin (Class.cv (nb093_alpha_dummy_118 r))
            (Class.cv (nb093_alpha_dummy_119 r)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0108 (A : Class) :
    (nb093_alpha_dummy_115 A) ∈
      (((Class.cv (nb093_alpha_dummy_115 A))).fv ∪ ((Class.cv (nb093_alpha_dummy_116 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0109 (r : Var) :
    (nb093_alpha_dummy_118 r) ∈
      (((Class.cv (nb093_alpha_dummy_118 r))).fv ∪ ((Class.cv (nb093_alpha_dummy_119 r))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0110 (A : Class) :
    (nb093_alpha_dummy_116 A) ∈
      (((syn_cnin (Class.cv (nb093_alpha_dummy_115 A))
            (Class.cv (nb093_alpha_dummy_116 A)))).fv ∪
        ((syn_cnin (Class.cv (nb093_alpha_dummy_115 A))
            (Class.cv (nb093_alpha_dummy_116 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0111 (r : Var) :
    (nb093_alpha_dummy_119 r) ∈
      (((syn_cnin (Class.cv (nb093_alpha_dummy_118 r))
            (Class.cv (nb093_alpha_dummy_119 r)))).fv ∪
        ((syn_cnin (Class.cv (nb093_alpha_dummy_118 r))
            (Class.cv (nb093_alpha_dummy_119 r)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0112 (A : Class) :
    (nb093_alpha_dummy_116 A) ∈
      (((Class.cv (nb093_alpha_dummy_115 A))).fv ∪ ((Class.cv (nb093_alpha_dummy_116 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0113 (r : Var) :
    (nb093_alpha_dummy_119 r) ∈
      (((Class.cv (nb093_alpha_dummy_118 r))).fv ∪ ((Class.cv (nb093_alpha_dummy_119 r))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0114 (A : Class) :
    (nb093_alpha_dummy_115 A) ∈
      (((syn_ccompl (Class.cv (nb093_alpha_dummy_115 A)))).fv ∪
        ((syn_ccompl (Class.cv (nb093_alpha_dummy_116 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0115 (r : Var) :
    (nb093_alpha_dummy_118 r) ∈
      (((syn_ccompl (Class.cv (nb093_alpha_dummy_118 r)))).fv ∪
        ((syn_ccompl (Class.cv (nb093_alpha_dummy_119 r)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0116 (A : Class) :
    (nb093_alpha_dummy_115 A) ∈
      (((Class.cv (nb093_alpha_dummy_115 A))).fv ∪ ((Class.cv (nb093_alpha_dummy_115 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0117 (r : Var) :
    (nb093_alpha_dummy_118 r) ∈
      (((Class.cv (nb093_alpha_dummy_118 r))).fv ∪ ((Class.cv (nb093_alpha_dummy_118 r))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0118 (A : Class) :
    (nb093_alpha_dummy_116 A) ∈
      (((syn_ccompl (Class.cv (nb093_alpha_dummy_115 A)))).fv ∪
        ((syn_ccompl (Class.cv (nb093_alpha_dummy_116 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0119 (r : Var) :
    (nb093_alpha_dummy_119 r) ∈
      (((syn_ccompl (Class.cv (nb093_alpha_dummy_118 r)))).fv ∪
        ((syn_ccompl (Class.cv (nb093_alpha_dummy_119 r)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0120 (A : Class) :
    (nb093_alpha_dummy_116 A) ∈
      (((Class.cv (nb093_alpha_dummy_116 A))).fv ∪ ((Class.cv (nb093_alpha_dummy_116 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0121 (r : Var) :
    (nb093_alpha_dummy_119 r) ∈
      (((Class.cv (nb093_alpha_dummy_119 r))).fv ∪ ((Class.cv (nb093_alpha_dummy_119 r))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0122 (A : Class) :
    (nb093_alpha_dummy_058 A) ∈
      (((Class.cv (nb093_alpha_dummy_059 A))).fv ∪ ((Class.cv (nb093_alpha_dummy_058 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0123 (A : Class) :
    (nb093_alpha_dummy_058 A) ∈
      (((syn_ccompl (Class.cab (nb093_alpha_dummy_100 A)
              (syn_wrex (nb093_alpha_dummy_101 A) (Class.cv (nb093_alpha_dummy_059 A))
                (Wff.classEq (Class.cv (nb093_alpha_dummy_100 A))
                  (syn_cphi (Class.cv (nb093_alpha_dummy_101 A)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb093_alpha_dummy_100 A)
              (syn_wrex (nb093_alpha_dummy_101 A) (Class.cv (nb093_alpha_dummy_058 A))
                (Wff.classEq (Class.cv (nb093_alpha_dummy_100 A))
                  (syn_cun (syn_cphi (Class.cv (nb093_alpha_dummy_101 A)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb093_alpha_dummy_058 A) ≠ (nb093_alpha_dummy_100 A) from (by
          unfold nb093_alpha_dummy_100;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0122 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb093_alpha_dummy_058 A) ≠ (nb093_alpha_dummy_101 A) from (by
            unfold nb093_alpha_dummy_101;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0122 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb093_support_mem_0124 (r : Var) :
    (nb093_alpha_dummy_060 r) ∈
      (((Class.cv (nb093_alpha_dummy_061 r))).fv ∪ ((Class.cv (nb093_alpha_dummy_060 r))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0125 (r : Var) :
    (nb093_alpha_dummy_060 r) ∈
      (((syn_ccompl (Class.cab (nb093_alpha_dummy_102 r)
              (syn_wrex (nb093_alpha_dummy_103 r) (Class.cv (nb093_alpha_dummy_061 r))
                (Wff.classEq (Class.cv (nb093_alpha_dummy_102 r))
                  (syn_cphi (Class.cv (nb093_alpha_dummy_103 r)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb093_alpha_dummy_102 r)
              (syn_wrex (nb093_alpha_dummy_103 r) (Class.cv (nb093_alpha_dummy_060 r))
                (Wff.classEq (Class.cv (nb093_alpha_dummy_102 r))
                  (syn_cun (syn_cphi (Class.cv (nb093_alpha_dummy_103 r)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb093_alpha_dummy_060 r) ≠ (nb093_alpha_dummy_102 r) from (by
          unfold nb093_alpha_dummy_102;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0124 r) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb093_alpha_dummy_060 r) ≠ (nb093_alpha_dummy_103 r) from (by
            unfold nb093_alpha_dummy_103;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0124 r) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb093_support_mem_0126 (A : Class) :
    (nb093_alpha_dummy_058 A) ∈
      (((Class.cab (nb093_alpha_dummy_100 A)
            (syn_wrex (nb093_alpha_dummy_101 A) (Class.cv (nb093_alpha_dummy_058 A))
              (Wff.classEq (Class.cv (nb093_alpha_dummy_100 A))
                (syn_cun (syn_cphi (Class.cv (nb093_alpha_dummy_101 A)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb093_alpha_dummy_100 A)
            (syn_wrex (nb093_alpha_dummy_101 A) (Class.cv (nb093_alpha_dummy_058 A))
              (Wff.classEq (Class.cv (nb093_alpha_dummy_100 A))
                (syn_cun (syn_cphi (Class.cv (nb093_alpha_dummy_101 A)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb093_alpha_dummy_058 A) ≠ (nb093_alpha_dummy_100 A) from (by
          unfold nb093_alpha_dummy_100;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0122 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb093_alpha_dummy_058 A) ≠ (nb093_alpha_dummy_101 A) from (by
            unfold nb093_alpha_dummy_101;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0122 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb093_support_mem_0127 (r : Var) :
    (nb093_alpha_dummy_060 r) ∈
      (((Class.cab (nb093_alpha_dummy_102 r)
            (syn_wrex (nb093_alpha_dummy_103 r) (Class.cv (nb093_alpha_dummy_060 r))
              (Wff.classEq (Class.cv (nb093_alpha_dummy_102 r))
                (syn_cun (syn_cphi (Class.cv (nb093_alpha_dummy_103 r)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb093_alpha_dummy_102 r)
            (syn_wrex (nb093_alpha_dummy_103 r) (Class.cv (nb093_alpha_dummy_060 r))
              (Wff.classEq (Class.cv (nb093_alpha_dummy_102 r))
                (syn_cun (syn_cphi (Class.cv (nb093_alpha_dummy_103 r)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb093_alpha_dummy_060 r) ≠ (nb093_alpha_dummy_102 r) from (by
          unfold nb093_alpha_dummy_102;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0124 r) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb093_alpha_dummy_060 r) ≠ (nb093_alpha_dummy_103 r) from (by
            unfold nb093_alpha_dummy_103;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0124 r) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb093_support_mem_0128 (A : Class) :
    (nb093_alpha_dummy_101 A) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb093_alpha_dummy_101 A))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0129 (r : Var) :
    (nb093_alpha_dummy_103 r) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb093_alpha_dummy_103 r))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0130 (A : Class) :
    (nb093_alpha_dummy_101 A) ∈
      (((syn_cphi (Class.cv (nb093_alpha_dummy_101 A)))).fv ∪
        ((syn_cphi (Class.cv (nb093_alpha_dummy_101 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0131 (r : Var) :
    (nb093_alpha_dummy_103 r) ∈
      (((syn_cphi (Class.cv (nb093_alpha_dummy_103 r)))).fv ∪
        ((syn_cphi (Class.cv (nb093_alpha_dummy_103 r)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0132 (A : Class) :
    (nb093_alpha_dummy_001 A) ∈
      (((syn_ccnv (Class.cv (nb093_alpha_dummy_001 A)))).fv ∪
        ((syn_ccnv (Class.cv (nb093_alpha_dummy_001 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccnv]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0133 (r : Var) :
    r ∈ (((syn_ccnv (Class.cv r))).fv ∪ ((syn_ccnv (Class.cv r))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccnv]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0134 (A : Class) :
    (nb093_alpha_dummy_001 A) ∈
      (({(nb093_alpha_dummy_058 A)} : Finset Var) ∪ ({(nb093_alpha_dummy_059 A)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb093_alpha_dummy_059 A)) (Class.cv (nb093_alpha_dummy_001 A))
            (Class.cv (nb093_alpha_dummy_058 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_wbr]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0135 (r : Var) :
    r ∈
      (({(nb093_alpha_dummy_060 r)} : Finset Var) ∪ ({(nb093_alpha_dummy_061 r)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb093_alpha_dummy_061 r)) (Class.cv r)
            (Class.cv (nb093_alpha_dummy_060 r)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_wbr]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0136 (A : Class) :
    (nb093_alpha_dummy_001 A) ∈ (((Class.cv (nb093_alpha_dummy_001 A))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0137 (r : Var) : r ∈ (((Class.cv r)).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0138 (A : Class) :
    (nb093_alpha_dummy_045 A) ∈ (((Class.cv (nb093_alpha_dummy_045 A))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0139 (r : Var) (d : Var) :
    (nb093_alpha_dummy_047 r d) ∈ (((Class.cv (nb093_alpha_dummy_047 r d))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0140 (A : Class) :
    (nb093_alpha_dummy_136 A) ∈
      (((Wff.classMem (Class.cv (nb093_alpha_dummy_136 A)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb093_alpha_dummy_136 A)) (syn_c1c))).fv ∪
        ((Class.cv (nb093_alpha_dummy_136 A))).fv) :=
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

theorem nb093_support_mem_0141 (r : Var) (d : Var) :
    (nb093_alpha_dummy_138 r d) ∈
      (((Wff.classMem (Class.cv (nb093_alpha_dummy_138 r d)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb093_alpha_dummy_138 r d)) (syn_c1c))).fv ∪
        ((Class.cv (nb093_alpha_dummy_138 r d))).fv) :=
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

theorem nb093_support_mem_0142 (A : Class) :
    (nb093_alpha_dummy_136 A) ∈
      (((Class.cv (nb093_alpha_dummy_136 A))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0143 (r : Var) (d : Var) :
    (nb093_alpha_dummy_138 r d) ∈
      (((Class.cv (nb093_alpha_dummy_138 r d))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0144 (A : Class) :
    (nb093_alpha_dummy_143 A) ∈
      (((syn_cnin (Class.cv (nb093_alpha_dummy_143 A))
            (Class.cv (nb093_alpha_dummy_144 A)))).fv ∪
        ((syn_cnin (Class.cv (nb093_alpha_dummy_143 A))
            (Class.cv (nb093_alpha_dummy_144 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0145 (r : Var) (d : Var) :
    (nb093_alpha_dummy_146 r d) ∈
      (((syn_cnin (Class.cv (nb093_alpha_dummy_146 r d))
            (Class.cv (nb093_alpha_dummy_147 r d)))).fv ∪
        ((syn_cnin (Class.cv (nb093_alpha_dummy_146 r d))
            (Class.cv (nb093_alpha_dummy_147 r d)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0146 (A : Class) :
    (nb093_alpha_dummy_143 A) ∈
      (((Class.cv (nb093_alpha_dummy_143 A))).fv ∪ ((Class.cv (nb093_alpha_dummy_144 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0147 (r : Var) (d : Var) :
    (nb093_alpha_dummy_146 r d) ∈
      (((Class.cv (nb093_alpha_dummy_146 r d))).fv ∪
        ((Class.cv (nb093_alpha_dummy_147 r d))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0148 (A : Class) :
    (nb093_alpha_dummy_144 A) ∈
      (((syn_cnin (Class.cv (nb093_alpha_dummy_143 A))
            (Class.cv (nb093_alpha_dummy_144 A)))).fv ∪
        ((syn_cnin (Class.cv (nb093_alpha_dummy_143 A))
            (Class.cv (nb093_alpha_dummy_144 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0149 (r : Var) (d : Var) :
    (nb093_alpha_dummy_147 r d) ∈
      (((syn_cnin (Class.cv (nb093_alpha_dummy_146 r d))
            (Class.cv (nb093_alpha_dummy_147 r d)))).fv ∪
        ((syn_cnin (Class.cv (nb093_alpha_dummy_146 r d))
            (Class.cv (nb093_alpha_dummy_147 r d)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0150 (A : Class) :
    (nb093_alpha_dummy_144 A) ∈
      (((Class.cv (nb093_alpha_dummy_143 A))).fv ∪ ((Class.cv (nb093_alpha_dummy_144 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0151 (r : Var) (d : Var) :
    (nb093_alpha_dummy_147 r d) ∈
      (((Class.cv (nb093_alpha_dummy_146 r d))).fv ∪
        ((Class.cv (nb093_alpha_dummy_147 r d))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0152 (A : Class) :
    (nb093_alpha_dummy_143 A) ∈
      (((syn_ccompl (Class.cv (nb093_alpha_dummy_143 A)))).fv ∪
        ((syn_ccompl (Class.cv (nb093_alpha_dummy_144 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0153 (r : Var) (d : Var) :
    (nb093_alpha_dummy_146 r d) ∈
      (((syn_ccompl (Class.cv (nb093_alpha_dummy_146 r d)))).fv ∪
        ((syn_ccompl (Class.cv (nb093_alpha_dummy_147 r d)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0154 (A : Class) :
    (nb093_alpha_dummy_143 A) ∈
      (((Class.cv (nb093_alpha_dummy_143 A))).fv ∪ ((Class.cv (nb093_alpha_dummy_143 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0155 (r : Var) (d : Var) :
    (nb093_alpha_dummy_146 r d) ∈
      (((Class.cv (nb093_alpha_dummy_146 r d))).fv ∪
        ((Class.cv (nb093_alpha_dummy_146 r d))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0156 (A : Class) :
    (nb093_alpha_dummy_144 A) ∈
      (((syn_ccompl (Class.cv (nb093_alpha_dummy_143 A)))).fv ∪
        ((syn_ccompl (Class.cv (nb093_alpha_dummy_144 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0157 (r : Var) (d : Var) :
    (nb093_alpha_dummy_147 r d) ∈
      (((syn_ccompl (Class.cv (nb093_alpha_dummy_146 r d)))).fv ∪
        ((syn_ccompl (Class.cv (nb093_alpha_dummy_147 r d)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0158 (A : Class) :
    (nb093_alpha_dummy_144 A) ∈
      (((Class.cv (nb093_alpha_dummy_144 A))).fv ∪ ((Class.cv (nb093_alpha_dummy_144 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0159 (r : Var) (d : Var) :
    (nb093_alpha_dummy_147 r d) ∈
      (((Class.cv (nb093_alpha_dummy_147 r d))).fv ∪
        ((Class.cv (nb093_alpha_dummy_147 r d))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0160 (A : Class) :
    (nb093_alpha_dummy_000 A) ∈
      (((syn_cdif (Class.cv (nb093_alpha_dummy_001 A))
            (syn_ccnv (Class.cv (nb093_alpha_dummy_001 A))))).fv ∪
        ((Class.cv (nb093_alpha_dummy_000 A))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0161 (A : Class) :
    (nb093_alpha_dummy_000 A) ∈
      (((syn_ccompl (Class.cab (nb093_alpha_dummy_044 A) (syn_wrex (nb093_alpha_dummy_045 A)
                (syn_cdif (Class.cv (nb093_alpha_dummy_001 A))
                  (syn_ccnv (Class.cv (nb093_alpha_dummy_001 A))))
                (Wff.classEq (Class.cv (nb093_alpha_dummy_044 A))
                  (syn_cphi (Class.cv (nb093_alpha_dummy_045 A)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb093_alpha_dummy_044 A)
              (syn_wrex (nb093_alpha_dummy_045 A) (Class.cv (nb093_alpha_dummy_000 A))
                (Wff.classEq (Class.cv (nb093_alpha_dummy_044 A))
                  (syn_cun (syn_cphi (Class.cv (nb093_alpha_dummy_045 A)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb093_alpha_dummy_000 A) ≠ (nb093_alpha_dummy_044 A) from (by
          unfold nb093_alpha_dummy_044;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0160 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb093_alpha_dummy_000 A) ≠ (nb093_alpha_dummy_045 A) from (by
            unfold nb093_alpha_dummy_045;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0160 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb093_support_mem_0162 (r : Var) (d : Var) :
    d ∈ (((syn_cdif (Class.cv r) (syn_ccnv (Class.cv r)))).fv ∪ ((Class.cv d)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0163 (r : Var) (d : Var) :
    d ∈
      (((syn_ccompl (Class.cab (nb093_alpha_dummy_046 r d) (syn_wrex (nb093_alpha_dummy_047 r d)
                (syn_cdif (Class.cv r) (syn_ccnv (Class.cv r)))
                (Wff.classEq (Class.cv (nb093_alpha_dummy_046 r d))
                  (syn_cphi (Class.cv (nb093_alpha_dummy_047 r d)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb093_alpha_dummy_046 r d)
              (syn_wrex (nb093_alpha_dummy_047 r d) (Class.cv d)
                (Wff.classEq (Class.cv (nb093_alpha_dummy_046 r d))
                  (syn_cun (syn_cphi (Class.cv (nb093_alpha_dummy_047 r d)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show d ≠ (nb093_alpha_dummy_046 r d) from (by
          unfold nb093_alpha_dummy_046;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0162 r d) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show d ≠ (nb093_alpha_dummy_047 r d) from (by
            unfold nb093_alpha_dummy_047;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0162 r d) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb093_support_mem_0164 (A : Class) :
    (nb093_alpha_dummy_000 A) ∈
      (((Class.cab (nb093_alpha_dummy_044 A)
            (syn_wrex (nb093_alpha_dummy_045 A) (Class.cv (nb093_alpha_dummy_000 A))
              (Wff.classEq (Class.cv (nb093_alpha_dummy_044 A))
                (syn_cun (syn_cphi (Class.cv (nb093_alpha_dummy_045 A)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb093_alpha_dummy_044 A)
            (syn_wrex (nb093_alpha_dummy_045 A) (Class.cv (nb093_alpha_dummy_000 A))
              (Wff.classEq (Class.cv (nb093_alpha_dummy_044 A))
                (syn_cun (syn_cphi (Class.cv (nb093_alpha_dummy_045 A)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb093_alpha_dummy_000 A) ≠ (nb093_alpha_dummy_044 A) from (by
          unfold nb093_alpha_dummy_044;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0160 A) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb093_alpha_dummy_000 A) ≠ (nb093_alpha_dummy_045 A) from (by
            unfold nb093_alpha_dummy_045;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0160 A) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb093_support_mem_0165 (r : Var) (d : Var) :
    d ∈
      (((Class.cab (nb093_alpha_dummy_046 r d)
            (syn_wrex (nb093_alpha_dummy_047 r d) (Class.cv d)
              (Wff.classEq (Class.cv (nb093_alpha_dummy_046 r d))
                (syn_cun (syn_cphi (Class.cv (nb093_alpha_dummy_047 r d)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb093_alpha_dummy_046 r d)
            (syn_wrex (nb093_alpha_dummy_047 r d) (Class.cv d)
              (Wff.classEq (Class.cv (nb093_alpha_dummy_046 r d))
                (syn_cun (syn_cphi (Class.cv (nb093_alpha_dummy_047 r d)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show d ≠ (nb093_alpha_dummy_046 r d) from (by
          unfold nb093_alpha_dummy_046;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0162 r d) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show d ≠ (nb093_alpha_dummy_047 r d) from (by
            unfold nb093_alpha_dummy_047;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0162 r d) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb093_support_mem_0166 (A : Class) :
    (nb093_alpha_dummy_045 A) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb093_alpha_dummy_045 A))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0167 (r : Var) (d : Var) :
    (nb093_alpha_dummy_047 r d) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb093_alpha_dummy_047 r d))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0168 (A : Class) :
    (nb093_alpha_dummy_045 A) ∈
      (((syn_cphi (Class.cv (nb093_alpha_dummy_045 A)))).fv ∪
        ((syn_cphi (Class.cv (nb093_alpha_dummy_045 A)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_support_mem_0169 (r : Var) (d : Var) :
    (nb093_alpha_dummy_047 r d) ∈
      (((syn_cphi (Class.cv (nb093_alpha_dummy_047 r d)))).fv ∪
        ((syn_cphi (Class.cv (nb093_alpha_dummy_047 r d)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb093_focused_notmem_0000 (A : Class) : (nb093_alpha_dummy_004 A) ∉ A.fv :=
  by
  change
    freshVar
        (((syn_clntpc A)).fv ∪ ((syn_copab (nb093_alpha_dummy_001 A) (nb093_alpha_dummy_000 A)
              (syn_wbr (syn_cdif (Class.cv (nb093_alpha_dummy_001 A))
                  (syn_ccnv (Class.cv (nb093_alpha_dummy_001 A))))
                (syn_cfound) (Class.cv (nb093_alpha_dummy_000 A))))).fv)
        0 ∉
      A.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_clntpc A]
  exact hu

theorem nb093_wpp_notmem_0000 (A : Class) :
    (nb093_alpha_dummy_004 A) ∉ ((syn_clntpc A)).fv := by
  simpa only [nb093_alpha_dummy_004, fv_syn_clntpc] using (nb093_focused_notmem_0000 A)

theorem nb093_focused_notmem_0001 (A : Class) (r : Var) (d : Var) :
    (nb093_alpha_dummy_005 A r d) ∉ A.fv :=
  by
  change
    freshVar
        (((syn_clntpc A)).fv ∪ ((syn_copab r d
              (syn_wbr (syn_cdif (Class.cv r) (syn_ccnv (Class.cv r))) (syn_cfound)
                (Class.cv d)))).fv)
        0 ∉
      A.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_clntpc A]
  exact hu

theorem nb093_wpp_notmem_0001 (A : Class) (r : Var) (d : Var) :
    (nb093_alpha_dummy_005 A r d) ∉ ((syn_clntpc A)).fv := by
  simpa only [nb093_alpha_dummy_005, fv_syn_clntpc] using
    (nb093_focused_notmem_0001 A r d)

theorem nb093_focused_notmem_0002 (A : Class) : (nb093_alpha_dummy_002 A) ∉ A.fv :=
  by
  change
    freshVar
        (((syn_cnin (syn_clntpc A)
              (syn_copab (nb093_alpha_dummy_001 A) (nb093_alpha_dummy_000 A) (syn_wbr
                  (syn_cdif (Class.cv (nb093_alpha_dummy_001 A))
                    (syn_ccnv (Class.cv (nb093_alpha_dummy_001 A))))
                  (syn_cfound) (Class.cv (nb093_alpha_dummy_000 A)))))).fv ∪
          ((syn_cnin (syn_clntpc A)
              (syn_copab (nb093_alpha_dummy_001 A) (nb093_alpha_dummy_000 A) (syn_wbr
                  (syn_cdif (Class.cv (nb093_alpha_dummy_001 A))
                    (syn_ccnv (Class.cv (nb093_alpha_dummy_001 A))))
                  (syn_cfound) (Class.cv (nb093_alpha_dummy_000 A)))))).fv)
        0 ∉
      A.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_cnin (syn_clntpc A)
      (syn_copab (nb093_alpha_dummy_001 A) (nb093_alpha_dummy_000 A) (syn_wbr
          (syn_cdif (Class.cv (nb093_alpha_dummy_001 A))
            (syn_ccnv (Class.cv (nb093_alpha_dummy_001 A))))
          (syn_cfound) (Class.cv (nb093_alpha_dummy_000 A))))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_clntpc A]
  exact hu

theorem nb093_wpp_notmem_0002 (A : Class) :
    (nb093_alpha_dummy_002 A) ∉ ((syn_clntpc A)).fv := by
  simpa only [nb093_alpha_dummy_002, fv_syn_clntpc] using (nb093_focused_notmem_0002 A)

theorem nb093_focused_notmem_0003 (A : Class) (r : Var) (d : Var) :
    (nb093_alpha_dummy_003 A r d) ∉ A.fv :=
  by
  change
    freshVar
        (((syn_cnin (syn_clntpc A) (syn_copab r d
                (syn_wbr (syn_cdif (Class.cv r) (syn_ccnv (Class.cv r))) (syn_cfound)
                  (Class.cv d))))).fv ∪ ((syn_cnin (syn_clntpc A) (syn_copab r d
                (syn_wbr (syn_cdif (Class.cv r) (syn_ccnv (Class.cv r))) (syn_cfound)
                  (Class.cv d))))).fv)
        0 ∉
      A.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_cnin (syn_clntpc A)
      (syn_copab r d (syn_wbr (syn_cdif (Class.cv r) (syn_ccnv (Class.cv r))) (syn_cfound)
          (Class.cv d)))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_clntpc A]
  exact hu

theorem nb093_wpp_notmem_0003 (A : Class) (r : Var) (d : Var) :
    (nb093_alpha_dummy_003 A r d) ∉ ((syn_clntpc A)).fv := by
  simpa only [nb093_alpha_dummy_003, fv_syn_clntpc] using
    (nb093_focused_notmem_0003 A r d)

theorem nb093_compact_envfresh_0000 (A : Class) (r : Var) (d : Var) :
    TEnvFresh
      [((nb093_alpha_dummy_004 A), (nb093_alpha_dummy_005 A r d)),
        ((nb093_alpha_dummy_002 A), (nb093_alpha_dummy_003 A r d))]
      ((syn_clntpc A)).fv :=
  by
  exact
    (TEnvFresh.consFresh (nb093_alpha_dummy_004 A) (nb093_alpha_dummy_005 A r d)
      (nb093_wpp_notmem_0000 A) (nb093_wpp_notmem_0001 A r d)
      (TEnvFresh.consFresh (nb093_alpha_dummy_002 A) (nb093_alpha_dummy_003 A r d)
        (nb093_wpp_notmem_0002 A) (nb093_wpp_notmem_0003 A r d)
        (TEnvFresh.nil ((syn_clntpc A)).fv)))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `AlphaSupport.NAR4H5C093M3Part002Stage2`. -/


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
noncomputable def nb093_wpp_refl_0000 (A : Class) (r : Var) (d : Var) :
    TReflOn
      [((nb093_alpha_dummy_004 A), (nb093_alpha_dummy_005 A r d)),
        ((nb093_alpha_dummy_002 A), (nb093_alpha_dummy_003 A r d))]
      ((syn_clntpc A)).fv :=
  TEnvFresh.reflOn (nb093_compact_envfresh_0000 A r d)

theorem nb093_compact_fv_empty_0020 (A : Class) :
    (nb093_alpha_dummy_000 A) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb093_compact_fv_empty_0021 (d : Var) : d ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb093_compact_fv_empty_0022 (A : Class) :
    (nb093_alpha_dummy_001 A) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb093_compact_fv_empty_0023 (r : Var) : r ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb093_compact_fv_empty_0024 (A : Class) :
    (nb093_alpha_dummy_006 A) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb093_compact_fv_empty_0025 (r : Var) (d : Var) :
    (nb093_alpha_dummy_007 r d) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb093_compact_fv_empty_0026 (A : Class) :
    (nb093_alpha_dummy_004 A) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb093_compact_fv_empty_0027 (A : Class) (r : Var) (d : Var) :
    (nb093_alpha_dummy_005 A r d) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb093_compact_fv_empty_0028 (A : Class) :
    (nb093_alpha_dummy_002 A) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb093_compact_fv_empty_0029 (A : Class) (r : Var) (d : Var) :
    (nb093_alpha_dummy_003 A r d) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
