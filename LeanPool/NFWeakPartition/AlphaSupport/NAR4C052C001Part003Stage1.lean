/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C052C001Block001

/-! NF weak partition development: NAR4C052C001Part003. -/


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

theorem nb052_support_mem_0087 (x : Var) (y : Var) :
    (nb052_alpha_dummy_003 x y) ∈
      (((Class.cab (nb052_alpha_dummy_008 x y)
            (syn_wrex (nb052_alpha_dummy_009 x y) (Class.cv (nb052_alpha_dummy_003 x y))
              (Wff.classEq (Class.cv (nb052_alpha_dummy_008 x y))
                (syn_cun (syn_cphi (Class.cv (nb052_alpha_dummy_009 x y)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb052_alpha_dummy_008 x y)
            (syn_wrex (nb052_alpha_dummy_009 x y) (Class.cv (nb052_alpha_dummy_003 x y))
              (Wff.classEq (Class.cv (nb052_alpha_dummy_008 x y))
                (syn_cun (syn_cphi (Class.cv (nb052_alpha_dummy_009 x y)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact (Nat.ne_of_lt (mem_lt_freshVar (nb052_support_mem_0084 x y) 0))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact (Nat.ne_of_lt (mem_lt_freshVar (nb052_support_mem_0084 x y) 1))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb052_support_mem_0088 :
    (nb052_alpha_dummy_007) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb052_alpha_dummy_007))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb052_support_mem_0089 (x : Var) (y : Var) :
    (nb052_alpha_dummy_009 x y) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb052_alpha_dummy_009 x y))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb052_support_mem_0090 :
    (nb052_alpha_dummy_007) ∈
      (((syn_cphi (Class.cv (nb052_alpha_dummy_007)))).fv ∪
        ((syn_cphi (Class.cv (nb052_alpha_dummy_007)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb052_support_mem_0091 (x : Var) (y : Var) :
    (nb052_alpha_dummy_009 x y) ∈
      (((syn_cphi (Class.cv (nb052_alpha_dummy_009 x y)))).fv ∪
        ((syn_cphi (Class.cv (nb052_alpha_dummy_009 x y)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb052_support_mem_0092 :
    (nb052_alpha_dummy_000) ∈
      (((syn_ccompl (Class.cv (nb052_alpha_dummy_000)))).fv ∪
        ((syn_ccompl (Class.cv (nb052_alpha_dummy_001)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb052_support_mem_0093 (x : Var) (y : Var) :
    x ∈ (((syn_ccompl (Class.cv x))).fv ∪ ((syn_ccompl (Class.cv y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb052_support_mem_0094 :
    (nb052_alpha_dummy_000) ∈
      (((Class.cv (nb052_alpha_dummy_000))).fv ∪ ((Class.cv (nb052_alpha_dummy_000))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb052_support_mem_0095 (x : Var) : x ∈ (((Class.cv x)).fv ∪ ((Class.cv x)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb052_support_mem_0096 :
    (nb052_alpha_dummy_001) ∈
      (((syn_ccompl (Class.cv (nb052_alpha_dummy_000)))).fv ∪
        ((syn_ccompl (Class.cv (nb052_alpha_dummy_001)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb052_support_mem_0097 (x : Var) (y : Var) :
    y ∈ (((syn_ccompl (Class.cv x))).fv ∪ ((syn_ccompl (Class.cv y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb052_support_mem_0098 :
    (nb052_alpha_dummy_001) ∈
      (((Class.cv (nb052_alpha_dummy_001))).fv ∪ ((Class.cv (nb052_alpha_dummy_001))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb052_support_mem_0099 (y : Var) : y ∈ (((Class.cv y)).fv ∪ ((Class.cv y)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
