/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NAR4C069C001Part001

/-! NF weak partition development: NAR4C069C001Part002. -/


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

theorem nb069_support_mem_0042 :
    (nb069_alpha_dummy_002) ∈
      (((syn_cnin (Class.cv (nb069_alpha_dummy_002)) (Class.cv (nb069_alpha_dummy_003)))).fv ∪
        ((syn_cnin (Class.cv (nb069_alpha_dummy_002))
            (Class.cv (nb069_alpha_dummy_003)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb069_support_mem_0043 (x : Var) (y : Var) :
    x ∈
      (((syn_cnin (Class.cv x) (Class.cv y))).fv ∪ ((syn_cnin (Class.cv x) (Class.cv y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb069_support_mem_0044 :
    (nb069_alpha_dummy_002) ∈
      (((Class.cv (nb069_alpha_dummy_002))).fv ∪ ((Class.cv (nb069_alpha_dummy_003))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb069_support_mem_0045 (x : Var) (y : Var) :
    x ∈ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb069_support_mem_0046 :
    (nb069_alpha_dummy_003) ∈
      (((syn_cnin (Class.cv (nb069_alpha_dummy_002)) (Class.cv (nb069_alpha_dummy_003)))).fv ∪
        ((syn_cnin (Class.cv (nb069_alpha_dummy_002))
            (Class.cv (nb069_alpha_dummy_003)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb069_support_mem_0047 (x : Var) (y : Var) :
    y ∈
      (((syn_cnin (Class.cv x) (Class.cv y))).fv ∪ ((syn_cnin (Class.cv x) (Class.cv y))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb069_support_mem_0048 :
    (nb069_alpha_dummy_003) ∈
      (((Class.cv (nb069_alpha_dummy_002))).fv ∪ ((Class.cv (nb069_alpha_dummy_003))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb069_support_mem_0049 (x : Var) (y : Var) :
    y ∈ (((Class.cv x)).fv ∪ ((Class.cv y)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
