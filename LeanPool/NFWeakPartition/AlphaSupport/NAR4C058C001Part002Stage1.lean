/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NAR4C058C001Part001

/-! NF weak partition development: NAR4C058C001Part002. -/


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

theorem nb058_support_mem_0028 :
    (nb058_alpha_dummy_020) ∈
      (((Class.cv (nb058_alpha_dummy_020))).fv ∪ ((Class.cv (nb058_alpha_dummy_020))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb058_support_mem_0029 (x : Var) :
    (nb058_alpha_dummy_023 x) ∈
      (((Class.cv (nb058_alpha_dummy_023 x))).fv ∪ ((Class.cv (nb058_alpha_dummy_023 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb058_support_mem_0030 :
    (nb058_alpha_dummy_021) ∈
      (((syn_ccompl (Class.cv (nb058_alpha_dummy_020)))).fv ∪
        ((syn_ccompl (Class.cv (nb058_alpha_dummy_021)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb058_support_mem_0031 (x : Var) :
    (nb058_alpha_dummy_024 x) ∈
      (((syn_ccompl (Class.cv (nb058_alpha_dummy_023 x)))).fv ∪
        ((syn_ccompl (Class.cv (nb058_alpha_dummy_024 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb058_support_mem_0032 :
    (nb058_alpha_dummy_021) ∈
      (((Class.cv (nb058_alpha_dummy_021))).fv ∪ ((Class.cv (nb058_alpha_dummy_021))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb058_support_mem_0033 (x : Var) :
    (nb058_alpha_dummy_024 x) ∈
      (((Class.cv (nb058_alpha_dummy_024 x))).fv ∪ ((Class.cv (nb058_alpha_dummy_024 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb058_support_mem_0034 :
    (nb058_alpha_dummy_001) ∈
      (((Class.cv (nb058_alpha_dummy_000))).fv ∪ ((Class.cv (nb058_alpha_dummy_001))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb058_support_mem_0035 :
    (nb058_alpha_dummy_001) ∈
      (((syn_ccompl (Class.cab (nb058_alpha_dummy_005)
              (syn_wrex (nb058_alpha_dummy_006) (Class.cv (nb058_alpha_dummy_000))
                (Wff.classEq (Class.cv (nb058_alpha_dummy_005))
                  (syn_cphi (Class.cv (nb058_alpha_dummy_006)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb058_alpha_dummy_005)
              (syn_wrex (nb058_alpha_dummy_006) (Class.cv (nb058_alpha_dummy_001))
                (Wff.classEq (Class.cv (nb058_alpha_dummy_005))
                  (syn_cun (syn_cphi (Class.cv (nb058_alpha_dummy_006)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0034) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0034) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb058_support_mem_0036 (x : Var) :
    (nb058_alpha_dummy_002 x) ∈
      (((Class.cv x)).fv ∪ ((Class.cv (nb058_alpha_dummy_002 x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb058_support_mem_0037 (x : Var) :
    (nb058_alpha_dummy_002 x) ∈
      (((syn_ccompl (Class.cab (nb058_alpha_dummy_007 x)
              (syn_wrex (nb058_alpha_dummy_008 x) (Class.cv x)
                (Wff.classEq (Class.cv (nb058_alpha_dummy_007 x))
                  (syn_cphi (Class.cv (nb058_alpha_dummy_008 x)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb058_alpha_dummy_007 x)
              (syn_wrex (nb058_alpha_dummy_008 x) (Class.cv (nb058_alpha_dummy_002 x))
                (Wff.classEq (Class.cv (nb058_alpha_dummy_007 x))
                  (syn_cun (syn_cphi (Class.cv (nb058_alpha_dummy_008 x)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0036 x) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0036 x) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb058_support_mem_0038 :
    (nb058_alpha_dummy_001) ∈
      (((Class.cab (nb058_alpha_dummy_005)
            (syn_wrex (nb058_alpha_dummy_006) (Class.cv (nb058_alpha_dummy_001))
              (Wff.classEq (Class.cv (nb058_alpha_dummy_005))
                (syn_cun (syn_cphi (Class.cv (nb058_alpha_dummy_006)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb058_alpha_dummy_005)
            (syn_wrex (nb058_alpha_dummy_006) (Class.cv (nb058_alpha_dummy_001))
              (Wff.classEq (Class.cv (nb058_alpha_dummy_005))
                (syn_cun (syn_cphi (Class.cv (nb058_alpha_dummy_006)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0034) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0034) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb058_support_mem_0039 (x : Var) :
    (nb058_alpha_dummy_002 x) ∈
      (((Class.cab (nb058_alpha_dummy_007 x)
            (syn_wrex (nb058_alpha_dummy_008 x) (Class.cv (nb058_alpha_dummy_002 x))
              (Wff.classEq (Class.cv (nb058_alpha_dummy_007 x))
                (syn_cun (syn_cphi (Class.cv (nb058_alpha_dummy_008 x)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb058_alpha_dummy_007 x)
            (syn_wrex (nb058_alpha_dummy_008 x) (Class.cv (nb058_alpha_dummy_002 x))
              (Wff.classEq (Class.cv (nb058_alpha_dummy_007 x))
                (syn_cun (syn_cphi (Class.cv (nb058_alpha_dummy_008 x)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0036 x) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb058_support_mem_0036 x) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb058_support_mem_0040 :
    (nb058_alpha_dummy_006) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb058_alpha_dummy_006))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb058_support_mem_0041 (x : Var) :
    (nb058_alpha_dummy_008 x) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb058_alpha_dummy_008 x))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb058_support_mem_0042 :
    (nb058_alpha_dummy_006) ∈
      (((syn_cphi (Class.cv (nb058_alpha_dummy_006)))).fv ∪
        ((syn_cphi (Class.cv (nb058_alpha_dummy_006)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb058_support_mem_0043 (x : Var) :
    (nb058_alpha_dummy_008 x) ∈
      (((syn_cphi (Class.cv (nb058_alpha_dummy_008 x)))).fv ∪
        ((syn_cphi (Class.cv (nb058_alpha_dummy_008 x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb058_support_mem_0044 :
    (nb058_alpha_dummy_045) ∈
      (((syn_cnin (Class.cv (nb058_alpha_dummy_045))
            (syn_cuni (Class.cv (nb058_alpha_dummy_000))))).fv ∪
        ((syn_cnin (Class.cv (nb058_alpha_dummy_045))
            (syn_cuni (Class.cv (nb058_alpha_dummy_000))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb058_support_mem_0045 (x : Var) :
    (nb058_alpha_dummy_046 x) ∈
      (((syn_cnin (Class.cv (nb058_alpha_dummy_046 x)) (syn_cuni (Class.cv x)))).fv ∪
        ((syn_cnin (Class.cv (nb058_alpha_dummy_046 x)) (syn_cuni (Class.cv x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb058_support_mem_0046 :
    (nb058_alpha_dummy_045) ∈
      (((Class.cv (nb058_alpha_dummy_045))).fv ∪
        ((syn_cuni (Class.cv (nb058_alpha_dummy_000)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb058_support_mem_0047 (x : Var) :
    (nb058_alpha_dummy_046 x) ∈
      (((Class.cv (nb058_alpha_dummy_046 x))).fv ∪ ((syn_cuni (Class.cv x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb058_support_mem_0048 :
    (nb058_alpha_dummy_000) ∈
      (((syn_cnin (syn_cpw (syn_cuni (Class.cv (nb058_alpha_dummy_000)))) (syn_c1c))).fv ∪
        ((syn_cnin (syn_cpw (syn_cuni (Class.cv (nb058_alpha_dummy_000)))) (syn_c1c))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cpw]
  rw [fv_syn_cuni]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb058_support_mem_0049 (x : Var) :
    x ∈
      (((syn_cnin (syn_cpw (syn_cuni (Class.cv x))) (syn_c1c))).fv ∪
        ((syn_cnin (syn_cpw (syn_cuni (Class.cv x))) (syn_c1c))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cpw]
  rw [fv_syn_cuni]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb058_support_mem_0050 :
    (nb058_alpha_dummy_000) ∈
      (((syn_cpw (syn_cuni (Class.cv (nb058_alpha_dummy_000))))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cpw]
  rw [fv_syn_cuni]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb058_support_mem_0051 (x : Var) :
    x ∈ (((syn_cpw (syn_cuni (Class.cv x)))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cpw]
  rw [fv_syn_cuni]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb058_support_mem_0052 :
    (nb058_alpha_dummy_000) ∈ (((syn_cuni (Class.cv (nb058_alpha_dummy_000)))).fv) :=
  by
  rw [fv_syn_cuni]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb058_support_mem_0053 (x : Var) : x ∈ (((syn_cuni (Class.cv x))).fv) :=
  by
  rw [fv_syn_cuni]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb058_support_mem_0054 :
    (nb058_alpha_dummy_000) ∈
      (((syn_cnin (Class.cv (nb058_alpha_dummy_045))
            (syn_cuni (Class.cv (nb058_alpha_dummy_000))))).fv ∪
        ((syn_cnin (Class.cv (nb058_alpha_dummy_045))
            (syn_cuni (Class.cv (nb058_alpha_dummy_000))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_cuni]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb058_support_mem_0055 (x : Var) :
    x ∈
      (((syn_cnin (Class.cv (nb058_alpha_dummy_046 x)) (syn_cuni (Class.cv x)))).fv ∪
        ((syn_cnin (Class.cv (nb058_alpha_dummy_046 x)) (syn_cuni (Class.cv x)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_cuni]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb058_support_mem_0056 :
    (nb058_alpha_dummy_000) ∈
      (((Class.cv (nb058_alpha_dummy_045))).fv ∪
        ((syn_cuni (Class.cv (nb058_alpha_dummy_000)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_cuni]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb058_support_mem_0057 (x : Var) :
    x ∈ (((Class.cv (nb058_alpha_dummy_046 x))).fv ∪ ((syn_cuni (Class.cv x))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_cuni]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb058_support_mem_0058 :
    (nb058_alpha_dummy_000) ∈ (((Class.cv (nb058_alpha_dummy_000))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb058_support_mem_0059 (x : Var) : x ∈ (((Class.cv x)).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
