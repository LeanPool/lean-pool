/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C054C001Block001

/-! NF weak partition development: NAR4C054C001Part003. -/


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

theorem nb054_support_mem_0079 (x : Var) (y : Var) :
    (nb054_alpha_dummy_061 x y) ∈
      (((syn_ccompl (Class.cv (nb054_alpha_dummy_060 x y)))).fv ∪
        ((syn_ccompl (Class.cv (nb054_alpha_dummy_061 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb054_support_mem_0080 :
    (nb054_alpha_dummy_058) ∈
      (((Class.cv (nb054_alpha_dummy_058))).fv ∪ ((Class.cv (nb054_alpha_dummy_058))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb054_support_mem_0081 (x : Var) (y : Var) :
    (nb054_alpha_dummy_061 x y) ∈
      (((Class.cv (nb054_alpha_dummy_061 x y))).fv ∪
        ((Class.cv (nb054_alpha_dummy_061 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb054_support_mem_0082 :
    (nb054_alpha_dummy_002) ∈
      (((syn_cop (Class.cv (nb054_alpha_dummy_000)) (Class.cv (nb054_alpha_dummy_001)))).fv ∪
        ((Class.cv (nb054_alpha_dummy_002))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb054_support_mem_0083 :
    (nb054_alpha_dummy_002) ∈
      (((syn_ccompl (Class.cab (nb054_alpha_dummy_006) (syn_wrex (nb054_alpha_dummy_007)
                (syn_cop (Class.cv (nb054_alpha_dummy_000)) (Class.cv (nb054_alpha_dummy_001)))
                (Wff.classEq (Class.cv (nb054_alpha_dummy_006))
                  (syn_cphi (Class.cv (nb054_alpha_dummy_007)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb054_alpha_dummy_006)
              (syn_wrex (nb054_alpha_dummy_007) (Class.cv (nb054_alpha_dummy_002))
                (Wff.classEq (Class.cv (nb054_alpha_dummy_006))
                  (syn_cun (syn_cphi (Class.cv (nb054_alpha_dummy_007)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0082) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0082) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb054_support_mem_0084 (x : Var) (y : Var) :
    (nb054_alpha_dummy_003 x y) ∈
      (((syn_cop (Class.cv x) (Class.cv y))).fv ∪
        ((Class.cv (nb054_alpha_dummy_003 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb054_support_mem_0085 (x : Var) (y : Var) :
    (nb054_alpha_dummy_003 x y) ∈
      (((syn_ccompl (Class.cab (nb054_alpha_dummy_008 x y)
              (syn_wrex (nb054_alpha_dummy_009 x y) (syn_cop (Class.cv x) (Class.cv y))
                (Wff.classEq (Class.cv (nb054_alpha_dummy_008 x y))
                  (syn_cphi (Class.cv (nb054_alpha_dummy_009 x y)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb054_alpha_dummy_008 x y)
              (syn_wrex (nb054_alpha_dummy_009 x y) (Class.cv (nb054_alpha_dummy_003 x y))
                (Wff.classEq (Class.cv (nb054_alpha_dummy_008 x y))
                  (syn_cun (syn_cphi (Class.cv (nb054_alpha_dummy_009 x y)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible
    refine
      Finset.mem_union_right (a := (nb054_alpha_dummy_003 x y)) (t := ((syn_ccompl
            (Class.cab (nb054_alpha_dummy_008 x y)
              (syn_wrex (nb054_alpha_dummy_009 x y) (Class.cv (nb054_alpha_dummy_003 x y))
                (Wff.classEq (Class.cv (nb054_alpha_dummy_008 x y))
                  (syn_cun (syn_cphi (Class.cv (nb054_alpha_dummy_009 x y)))
                    (syn_csn (syn_c0c)))))))).fv)
        ((syn_ccompl (Class.cab (nb054_alpha_dummy_008 x y)
              (syn_wrex (nb054_alpha_dummy_009 x y) (syn_cop (Class.cv x) (Class.cv y))
                (Wff.classEq (Class.cv (nb054_alpha_dummy_008 x y))
                  (syn_cphi (Class.cv (nb054_alpha_dummy_009 x y)))))))).fv
        ?_
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0084 x y) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0084 x y) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb054_support_mem_0086 :
    (nb054_alpha_dummy_002) ∈
      (((Class.cab (nb054_alpha_dummy_006)
            (syn_wrex (nb054_alpha_dummy_007) (Class.cv (nb054_alpha_dummy_002))
              (Wff.classEq (Class.cv (nb054_alpha_dummy_006))
                (syn_cun (syn_cphi (Class.cv (nb054_alpha_dummy_007)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb054_alpha_dummy_006)
            (syn_wrex (nb054_alpha_dummy_007) (Class.cv (nb054_alpha_dummy_002))
              (Wff.classEq (Class.cv (nb054_alpha_dummy_006))
                (syn_cun (syn_cphi (Class.cv (nb054_alpha_dummy_007)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0082) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0082) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb054_support_mem_0087 (x : Var) (y : Var) :
    (nb054_alpha_dummy_003 x y) ∈
      (((Class.cab (nb054_alpha_dummy_008 x y)
            (syn_wrex (nb054_alpha_dummy_009 x y) (Class.cv (nb054_alpha_dummy_003 x y))
              (Wff.classEq (Class.cv (nb054_alpha_dummy_008 x y))
                (syn_cun (syn_cphi (Class.cv (nb054_alpha_dummy_009 x y)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb054_alpha_dummy_008 x y)
            (syn_wrex (nb054_alpha_dummy_009 x y) (Class.cv (nb054_alpha_dummy_003 x y))
              (Wff.classEq (Class.cv (nb054_alpha_dummy_008 x y))
                (syn_cun (syn_cphi (Class.cv (nb054_alpha_dummy_009 x y)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0084 x y) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb054_support_mem_0084 x y) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb054_support_mem_0088 :
    (nb054_alpha_dummy_007) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb054_alpha_dummy_007))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb054_support_mem_0089 (x : Var) (y : Var) :
    (nb054_alpha_dummy_009 x y) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb054_alpha_dummy_009 x y))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb054_support_mem_0090 :
    (nb054_alpha_dummy_007) ∈
      (((syn_cphi (Class.cv (nb054_alpha_dummy_007)))).fv ∪
        ((syn_cphi (Class.cv (nb054_alpha_dummy_007)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb054_support_mem_0091 (x : Var) (y : Var) :
    (nb054_alpha_dummy_009 x y) ∈
      (((syn_cphi (Class.cv (nb054_alpha_dummy_009 x y)))).fv ∪
        ((syn_cphi (Class.cv (nb054_alpha_dummy_009 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb054_support_mem_0092 :
    (nb054_alpha_dummy_015) ∈
      (((syn_cnin (Class.cv (nb054_alpha_dummy_015)) (Class.cv (nb054_alpha_dummy_078)))).fv ∪
        ((syn_cnin (Class.cv (nb054_alpha_dummy_015))
            (Class.cv (nb054_alpha_dummy_078)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb054_support_mem_0093 (x : Var) (y : Var) :
    (nb054_alpha_dummy_017 x y) ∈
      (((syn_cnin (Class.cv (nb054_alpha_dummy_017 x y))
            (Class.cv (nb054_alpha_dummy_079 x y)))).fv ∪
        ((syn_cnin (Class.cv (nb054_alpha_dummy_017 x y))
            (Class.cv (nb054_alpha_dummy_079 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb054_support_mem_0094 :
    (nb054_alpha_dummy_015) ∈
      (((Class.cv (nb054_alpha_dummy_015))).fv ∪ ((Class.cv (nb054_alpha_dummy_078))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb054_support_mem_0095 (x : Var) (y : Var) :
    (nb054_alpha_dummy_017 x y) ∈
      (((Class.cv (nb054_alpha_dummy_017 x y))).fv ∪
        ((Class.cv (nb054_alpha_dummy_079 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb054_support_mem_0096 :
    (nb054_alpha_dummy_078) ∈
      (((syn_cnin (Class.cv (nb054_alpha_dummy_015)) (Class.cv (nb054_alpha_dummy_078)))).fv ∪
        ((syn_cnin (Class.cv (nb054_alpha_dummy_015))
            (Class.cv (nb054_alpha_dummy_078)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb054_support_mem_0097 (x : Var) (y : Var) :
    (nb054_alpha_dummy_079 x y) ∈
      (((syn_cnin (Class.cv (nb054_alpha_dummy_017 x y))
            (Class.cv (nb054_alpha_dummy_079 x y)))).fv ∪
        ((syn_cnin (Class.cv (nb054_alpha_dummy_017 x y))
            (Class.cv (nb054_alpha_dummy_079 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb054_support_mem_0098 :
    (nb054_alpha_dummy_078) ∈
      (((Class.cv (nb054_alpha_dummy_015))).fv ∪ ((Class.cv (nb054_alpha_dummy_078))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb054_support_mem_0099 (x : Var) (y : Var) :
    (nb054_alpha_dummy_079 x y) ∈
      (((Class.cv (nb054_alpha_dummy_017 x y))).fv ∪
        ((Class.cv (nb054_alpha_dummy_079 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb054_support_mem_0100 :
    (nb054_alpha_dummy_015) ∈
      (((syn_ccompl (Class.cv (nb054_alpha_dummy_015)))).fv ∪
        ((syn_ccompl (Class.cv (nb054_alpha_dummy_078)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb054_support_mem_0101 (x : Var) (y : Var) :
    (nb054_alpha_dummy_017 x y) ∈
      (((syn_ccompl (Class.cv (nb054_alpha_dummy_017 x y)))).fv ∪
        ((syn_ccompl (Class.cv (nb054_alpha_dummy_079 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb054_support_mem_0102 :
    (nb054_alpha_dummy_015) ∈
      (((Class.cv (nb054_alpha_dummy_015))).fv ∪ ((Class.cv (nb054_alpha_dummy_015))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb054_support_mem_0103 (x : Var) (y : Var) :
    (nb054_alpha_dummy_017 x y) ∈
      (((Class.cv (nb054_alpha_dummy_017 x y))).fv ∪
        ((Class.cv (nb054_alpha_dummy_017 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb054_support_mem_0104 :
    (nb054_alpha_dummy_078) ∈
      (((syn_ccompl (Class.cv (nb054_alpha_dummy_015)))).fv ∪
        ((syn_ccompl (Class.cv (nb054_alpha_dummy_078)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb054_support_mem_0105 (x : Var) (y : Var) :
    (nb054_alpha_dummy_079 x y) ∈
      (((syn_ccompl (Class.cv (nb054_alpha_dummy_017 x y)))).fv ∪
        ((syn_ccompl (Class.cv (nb054_alpha_dummy_079 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb054_support_mem_0106 :
    (nb054_alpha_dummy_078) ∈
      (((Class.cv (nb054_alpha_dummy_078))).fv ∪ ((Class.cv (nb054_alpha_dummy_078))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb054_support_mem_0107 (x : Var) (y : Var) :
    (nb054_alpha_dummy_079 x y) ∈
      (((Class.cv (nb054_alpha_dummy_079 x y))).fv ∪
        ((Class.cv (nb054_alpha_dummy_079 x y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
