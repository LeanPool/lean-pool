/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NAR4H5C096M3Part001

/-! NF weak partition development: NAR4H5C096M3Part002. -/


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

theorem nb096_support_mem_0124 (D : Class) (R : Class) :
    (nb096_alpha_dummy_117 D R) ∈
      (((Class.cv (nb096_alpha_dummy_117 D R))).fv ∪
        ((Class.cv (nb096_alpha_dummy_117 D R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0125 (D : Class) (R : Class) (q : Var) :
    (nb096_alpha_dummy_120 D R q) ∈
      (((Class.cv (nb096_alpha_dummy_120 D R q))).fv ∪
        ((Class.cv (nb096_alpha_dummy_120 D R q))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0126 (D : Class) (R : Class) :
    (nb096_alpha_dummy_041 D R) ∈
      (((Class.cv (nb096_alpha_dummy_042 D R))).fv ∪
        ((Class.cv (nb096_alpha_dummy_041 D R))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0127 (D : Class) (R : Class) :
    (nb096_alpha_dummy_041 D R) ∈
      (((syn_ccompl (Class.cab (nb096_alpha_dummy_101 D R)
              (syn_wrex (nb096_alpha_dummy_102 D R) (Class.cv (nb096_alpha_dummy_042 D R))
                (Wff.classEq (Class.cv (nb096_alpha_dummy_101 D R))
                  (syn_cphi (Class.cv (nb096_alpha_dummy_102 D R)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb096_alpha_dummy_101 D R)
              (syn_wrex (nb096_alpha_dummy_102 D R) (Class.cv (nb096_alpha_dummy_041 D R))
                (Wff.classEq (Class.cv (nb096_alpha_dummy_101 D R))
                  (syn_cun (syn_cphi (Class.cv (nb096_alpha_dummy_102 D R)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb096_alpha_dummy_041 D R) ≠ (nb096_alpha_dummy_101 D R) from (by
          unfold nb096_alpha_dummy_101;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0126 D R) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb096_alpha_dummy_041 D R) ≠ (nb096_alpha_dummy_102 D R) from (by
            unfold nb096_alpha_dummy_102;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0126 D R) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb096_support_mem_0128 (D : Class) (R : Class) (q : Var) :
    (nb096_alpha_dummy_043 D R q) ∈
      (((Class.cv (nb096_alpha_dummy_044 D R q))).fv ∪
        ((Class.cv (nb096_alpha_dummy_043 D R q))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0129 (D : Class) (R : Class) (q : Var) :
    (nb096_alpha_dummy_043 D R q) ∈
      (((syn_ccompl (Class.cab (nb096_alpha_dummy_103 D R q)
              (syn_wrex (nb096_alpha_dummy_104 D R q) (Class.cv (nb096_alpha_dummy_044 D R q))
                (Wff.classEq (Class.cv (nb096_alpha_dummy_103 D R q))
                  (syn_cphi (Class.cv (nb096_alpha_dummy_104 D R q)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb096_alpha_dummy_103 D R q) (syn_wrex (nb096_alpha_dummy_104 D R q)
                (Class.cv (nb096_alpha_dummy_043 D R q))
                (Wff.classEq (Class.cv (nb096_alpha_dummy_103 D R q))
                  (syn_cun (syn_cphi (Class.cv (nb096_alpha_dummy_104 D R q)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb096_alpha_dummy_043 D R q) ≠ (nb096_alpha_dummy_103 D R q) from (by
          unfold nb096_alpha_dummy_103;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0128 D R q) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb096_alpha_dummy_043 D R q) ≠ (nb096_alpha_dummy_104 D R q) from (by
            unfold nb096_alpha_dummy_104;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0128 D R q) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb096_support_mem_0130 (D : Class) (R : Class) :
    (nb096_alpha_dummy_041 D R) ∈
      (((Class.cab (nb096_alpha_dummy_101 D R)
            (syn_wrex (nb096_alpha_dummy_102 D R) (Class.cv (nb096_alpha_dummy_041 D R))
              (Wff.classEq (Class.cv (nb096_alpha_dummy_101 D R))
                (syn_cun (syn_cphi (Class.cv (nb096_alpha_dummy_102 D R)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb096_alpha_dummy_101 D R)
            (syn_wrex (nb096_alpha_dummy_102 D R) (Class.cv (nb096_alpha_dummy_041 D R))
              (Wff.classEq (Class.cv (nb096_alpha_dummy_101 D R))
                (syn_cun (syn_cphi (Class.cv (nb096_alpha_dummy_102 D R)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb096_alpha_dummy_041 D R) ≠ (nb096_alpha_dummy_101 D R) from (by
          unfold nb096_alpha_dummy_101;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0126 D R) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb096_alpha_dummy_041 D R) ≠ (nb096_alpha_dummy_102 D R) from (by
            unfold nb096_alpha_dummy_102;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0126 D R) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb096_support_mem_0131 (D : Class) (R : Class) (q : Var) :
    (nb096_alpha_dummy_043 D R q) ∈
      (((Class.cab (nb096_alpha_dummy_103 D R q) (syn_wrex (nb096_alpha_dummy_104 D R q)
              (Class.cv (nb096_alpha_dummy_043 D R q))
              (Wff.classEq (Class.cv (nb096_alpha_dummy_103 D R q))
                (syn_cun (syn_cphi (Class.cv (nb096_alpha_dummy_104 D R q)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb096_alpha_dummy_103 D R q)
            (syn_wrex (nb096_alpha_dummy_104 D R q) (Class.cv (nb096_alpha_dummy_043 D R q))
              (Wff.classEq (Class.cv (nb096_alpha_dummy_103 D R q))
                (syn_cun (syn_cphi (Class.cv (nb096_alpha_dummy_104 D R q)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb096_alpha_dummy_043 D R q) ≠ (nb096_alpha_dummy_103 D R q) from (by
          unfold nb096_alpha_dummy_103;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0128 D R q) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb096_alpha_dummy_043 D R q) ≠ (nb096_alpha_dummy_104 D R q) from (by
            unfold nb096_alpha_dummy_104;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb096_support_mem_0128 D R q) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb096_support_mem_0132 (D : Class) (R : Class) :
    (nb096_alpha_dummy_102 D R) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb096_alpha_dummy_102 D R))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0133 (D : Class) (R : Class) (q : Var) :
    (nb096_alpha_dummy_104 D R q) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb096_alpha_dummy_104 D R q))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0134 (D : Class) (R : Class) :
    (nb096_alpha_dummy_102 D R) ∈
      (((syn_cphi (Class.cv (nb096_alpha_dummy_102 D R)))).fv ∪
        ((syn_cphi (Class.cv (nb096_alpha_dummy_102 D R)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_support_mem_0135 (D : Class) (R : Class) (q : Var) :
    (nb096_alpha_dummy_104 D R q) ∈
      (((syn_cphi (Class.cv (nb096_alpha_dummy_104 D R q)))).fv ∪
        ((syn_cphi (Class.cv (nb096_alpha_dummy_104 D R q)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb096_compact_fv_empty_0020 (D : Class) (R : Class) :
    (nb096_alpha_dummy_001 D R) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb096_compact_fv_empty_0021 (D : Class) (R : Class) (q : Var) :
    (nb096_alpha_dummy_002 D R q) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb096_compact_fv_empty_0022 (D : Class) (R : Class) :
    (nb096_alpha_dummy_000 D R) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb096_compact_fv_empty_0023 (q : Var) : q ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb096_compact_fv_empty_0024 (D : Class) (R : Class) :
    (nb096_alpha_dummy_003 D R) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb096_compact_fv_empty_0025 (D : Class) (R : Class) (q : Var) :
    (nb096_alpha_dummy_004 D R q) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
