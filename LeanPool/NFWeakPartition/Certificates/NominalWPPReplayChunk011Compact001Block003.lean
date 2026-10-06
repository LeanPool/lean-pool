/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NominalWPPReplayChunk011Compact001Block002

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NominalWPPReplayChunk011Compact001Part010`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_dfxp2`. -/
@[expose]
noncomputable def gDfxp2 (A : Class) (B : Class) :
    Nominal.NPrf
      (.classEq (synCxp A B) (synCin (synCima (synCcnv (synC1st)) A)
          (synCima (synCcnv (synC2nd)) B))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let z : Var := freshVar proofSupport 2
  let w : Var := freshVar proofSupport 3
  let v : Var := freshVar proofSupport 4
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (h))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (h))
  have fresh_z_not_B : z ∉ B.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x := Ne.symm fresh_x_ne_y
  have fresh_x_ne_z : x ≠ z :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_z_ne_x : z ≠ x := Ne.symm fresh_x_ne_z
  have fresh_x_ne_w : x ≠ w :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_w_ne_x : w ≠ x := Ne.symm fresh_x_ne_w
  have fresh_x_ne_v : x ≠ v :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 0) (j := 4) (by decide)
  have fresh_v_ne_x : v ≠ x := Ne.symm fresh_x_ne_v
  have fresh_y_ne_z : y ≠ z :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_z_ne_y : z ≠ y := Ne.symm fresh_y_ne_z
  have fresh_y_ne_w : y ≠ w :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_w_ne_y : w ≠ y := Ne.symm fresh_y_ne_w
  have fresh_y_ne_v : y ≠ v :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 1) (j := 4) (by decide)
  have fresh_v_ne_y : v ≠ y := Ne.symm fresh_y_ne_v
  have fresh_z_ne_w : z ≠ w :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_w_ne_z : w ≠ z := Ne.symm fresh_z_ne_w
  have fresh_z_ne_v : z ≠ v :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 2) (j := 4) (by decide)
  have fresh_v_ne_z : v ≠ z := Ne.symm fresh_z_ne_v
  have fresh_w_ne_v : w ≠ v :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 3) (j := 4) (by decide)
  have fresh_v_ne_w : v ≠ w := Ne.symm fresh_w_ne_v
  have dv_cache_0001 : v ∉ ((Wff.classEq (.cv x) (synCop (.cv y) (.cv w)))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union,
          Finset.mem_singleton, fresh_v_ne_x, fresh_v_ne_y, fresh_v_ne_w, or_false,
          not_false_eq_true])
  have dv_cache_0002 : w ∉ ((Wff.classEq (.cv x) (synCop (.cv v) (.cv z)))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union,
          Finset.mem_singleton, fresh_w_ne_x, fresh_w_ne_v, fresh_w_ne_z, or_false,
          not_false_eq_true])
  have dv_cache_0003 : w ∉ ((Class.cv z)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_w_ne_z, not_false_eq_true])
  have dv_cache_0004 : v ∉ ((Class.cv z)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_v_ne_z, not_false_eq_true])
  have dv_cache_0005 : w ∉ ((Class.cv y)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_w_ne_y, not_false_eq_true])
  have dv_cache_0006 : v ∉ ((Class.cv y)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_v_ne_y, not_false_eq_true])
  have dv_cache_0007 :
    w ∉
      ((synWa (.classEq (.cv x) (synCop (.cv y) (.cv z)))
          (.classEq (.cv x) (synCop (.cv y) (.cv z))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union,
          Finset.mem_singleton, fresh_w_ne_x, fresh_w_ne_y, fresh_w_ne_z, or_false,
          not_false_eq_true])
  have dv_cache_0008 :
    v ∉
      ((synWa (.classEq (.cv x) (synCop (.cv y) (.cv z)))
          (.classEq (.cv x) (synCop (.cv y) (.cv z))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union,
          Finset.mem_singleton, fresh_v_ne_x, fresh_v_ne_y, fresh_v_ne_z, or_false,
          not_false_eq_true])
  have dv_cache_0009 : w ≠ v :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (show w ≠ v from (by exact fresh_w_ne_v))
  have dv_cache_0010 : w ∉ ((Wff.classEq (.cv x) (synCop (.cv y) (.cv z)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union,
          Finset.mem_singleton, fresh_w_ne_x, fresh_w_ne_y, fresh_w_ne_z, or_false,
          not_false_eq_true])
  have dv_cache_0011 : v ∉ ((Wff.classEq (.cv x) (synCop (.cv y) (.cv z)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union,
          Finset.mem_singleton, fresh_v_ne_x, fresh_v_ne_y, fresh_v_ne_z, or_false,
          not_false_eq_true])
  have dv_cache_0012 : w ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_w_ne_x, not_false_eq_true])
  have dv_cache_0013 : v ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_v_ne_x, not_false_eq_true])
  have dv_cache_0014 : y ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_y_ne_x, not_false_eq_true])
  have dv_cache_0015 : z ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_z_ne_x, not_false_eq_true])
  have dv_cache_0016 : y ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_A, not_false_eq_true])
  have dv_cache_0017 : z ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_A, not_false_eq_true])
  have dv_cache_0018 : y ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_B, not_false_eq_true])
  have dv_cache_0019 : z ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_B, not_false_eq_true])
  have dv_cache_0020 : y ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019
    exact (show y ≠ z from (by exact fresh_y_ne_z))
  have dv_cache_0021 : y ∉ ((synCcnv (synC1st))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, compact_fv_not_mem_empty,
          not_false_eq_true])
  have dv_cache_0022 : z ∉ ((synCcnv (synC2nd))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, compact_fv_not_mem_empty,
          not_false_eq_true])
  have dv_cache_0023 : z ∉ ((synWbr (.cv y) (synCcnv (synC1st)) (.cv x))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_y, fresh_z_ne_x, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0024 : y ∉ ((synWbr (.cv z) (synCcnv (synC2nd)) (.cv x))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_z, fresh_y_ne_x, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0025 : x ∉ ((synCxp A B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, Finset.mem_union,
          fresh_x_not_A, fresh_x_not_B, or_false, not_false_eq_true])
  have dv_cache_0026 :
    x ∉
      ((synCin (synCima (synCcnv (synC1st)) A) (synCima (synCcnv (synC2nd)) B))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union,
          fresh_x_not_A, fresh_x_not_B, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have p0000 :=
    @gEeanv (.classEq (.cv x) (synCop (.cv y) (.cv w)))
      (.classEq (.cv x) (synCop (.cv v) (.cv z))) w v dv_cache_0001 dv_cache_0002
  have p0001 := @gVex z
  have p0002 := @gVex y
  have p0003 := @gOpeq2 (.cv w) (.cv z) (.cv y)
  have p0004_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq w z) (.classEq (synCop (.cv y) (.cv w)) (synCop (.cv y) (.cv z)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synCop synCun synCnin synWnan synWa synCcompl synWrex synWex
          synCphi
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0003
  have p0004 :=
    @gEqeq2d (.objEq w z) (synCop (.cv y) (.cv w)) (synCop (.cv y) (.cv z)) (.cv x)
      p0004_e00_recanon
  have p0005 := @gOpeq1 (.cv v) (.cv y) (.cv z)
  have p0006_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq v y) (.classEq (synCop (.cv v) (.cv z)) (synCop (.cv y) (.cv z)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synCop synCun synCnin synWnan synWa synCcompl synWrex synWex
          synCphi
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0005
  have p0006 :=
    @gEqeq2d (.objEq v y) (synCop (.cv v) (.cv z)) (synCop (.cv y) (.cv z)) (.cv x)
      p0006_e00_recanon
  have p0007 :=
    @gBi2anan9 (.objEq w z) (.classEq (.cv x) (synCop (.cv y) (.cv w)))
      (.classEq (.cv x) (synCop (.cv y) (.cv z))) (.objEq v y)
      (.classEq (.cv x) (synCop (.cv v) (.cv z)))
      (.classEq (.cv x) (synCop (.cv y) (.cv z))) p0004 p0006
  have p0008_e02_recanon :
    Nominal.NPrf
      (.imp (synWa (.classEq (.cv w) (.cv z)) (.classEq (.cv v) (.cv y))) (synWb
          (synWa (.classEq (.cv x) (synCop (.cv y) (.cv w)))
            (.classEq (.cv x) (synCop (.cv v) (.cv z))))
          (synWa (.classEq (.cv x) (synCop (.cv y) (.cv z)))
            (.classEq (.cv x) (synCop (.cv y) (.cv z)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWa synWb
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0007
  have p0008 :=
    @gSpc2ev
      (synWa (.classEq (.cv x) (synCop (.cv y) (.cv w)))
        (.classEq (.cv x) (synCop (.cv v) (.cv z))))
      (synWa (.classEq (.cv x) (synCop (.cv y) (.cv z)))
        (.classEq (.cv x) (synCop (.cv y) (.cv z))))
      w v (.cv z) (.cv y) dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
      dv_cache_0007 dv_cache_0008 dv_cache_0009 p0001 p0002 p0008_e02_recanon
  have p0009 :=
    @gAnidms (.classEq (.cv x) (synCop (.cv y) (.cv z)))
      (synWex w (synWex v (synWa (.classEq (.cv x) (synCop (.cv y) (.cv w)))
            (.classEq (.cv x) (synCop (.cv v) (.cv z))))))
      p0008
  have p0010 :=
    @gSimpl (.classEq (.cv x) (synCop (.cv y) (.cv w)))
      (.classEq (.cv x) (synCop (.cv v) (.cv z)))
  have p0011 := @gEqtr2 (.cv x) (synCop (.cv y) (.cv w)) (synCop (.cv v) (.cv z))
  have p0012 := @gOpth (.cv y) (.cv w) (.cv v) (.cv z)
  have p0013_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq w z) (.classEq (synCop (.cv y) (.cv w)) (synCop (.cv y) (.cv z)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synCop synCun synCnin synWnan synWa synCcompl synWrex synWex
          synCphi
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0003
  have p0013 :=
    @gAdantl (.objEq w z) (.classEq (synCop (.cv y) (.cv w)) (synCop (.cv y) (.cv z)))
      (.objEq y v) p0013_e00_recanon
  have p0014_e00_recanon :
    Nominal.NPrf
      (synWb (.classEq (synCop (.cv y) (.cv w)) (synCop (.cv v) (.cv z)))
        (synWa (.objEq y v) (.objEq w z))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCop synCun synCnin synWnan synWa synCcompl synWrex synWex
          synCphi
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0012
  have p0014 :=
    @gSylbi (.classEq (synCop (.cv y) (.cv w)) (synCop (.cv v) (.cv z)))
      (synWa (.objEq y v) (.objEq w z))
      (.classEq (synCop (.cv y) (.cv w)) (synCop (.cv y) (.cv z))) p0014_e00_recanon
      p0013
  have p0015 :=
    @gSyl
      (synWa (.classEq (.cv x) (synCop (.cv y) (.cv w)))
        (.classEq (.cv x) (synCop (.cv v) (.cv z))))
      (.classEq (synCop (.cv y) (.cv w)) (synCop (.cv v) (.cv z)))
      (.classEq (synCop (.cv y) (.cv w)) (synCop (.cv y) (.cv z))) p0011 p0014
  have p0016 :=
    @gEqtrd
      (synWa (.classEq (.cv x) (synCop (.cv y) (.cv w)))
        (.classEq (.cv x) (synCop (.cv v) (.cv z))))
      (.cv x) (synCop (.cv y) (.cv w)) (synCop (.cv y) (.cv z)) p0010 p0015
  have p0017 :=
    @gExlimivv
      (synWa (.classEq (.cv x) (synCop (.cv y) (.cv w)))
        (.classEq (.cv x) (synCop (.cv v) (.cv z))))
      (.classEq (.cv x) (synCop (.cv y) (.cv z))) w v dv_cache_0010 dv_cache_0011 p0016
  have p0018 :=
    @gImpbii (.classEq (.cv x) (synCop (.cv y) (.cv z)))
      (synWex w (synWex v (synWa (.classEq (.cv x) (synCop (.cv y) (.cv w)))
            (.classEq (.cv x) (synCop (.cv v) (.cv z))))))
      p0009 p0017
  have p0019 := @gBrcnv (.cv y) (.cv x) (synC1st)
  have p0020 := @gBr1st w (.cv x) (.cv y) dv_cache_0012 dv_cache_0005 p0002
  have p0021 :=
    @gBitri (synWbr (.cv y) (synCcnv (synC1st)) (.cv x))
      (synWbr (.cv x) (synC1st) (.cv y))
      (synWex w (.classEq (.cv x) (synCop (.cv y) (.cv w)))) p0019 p0020
  have p0022 := @gBrcnv (.cv z) (.cv x) (synC2nd)
  have p0023 := @gBr2nd v (.cv x) (.cv z) dv_cache_0013 dv_cache_0004 p0001
  have p0024 :=
    @gBitri (synWbr (.cv z) (synCcnv (synC2nd)) (.cv x))
      (synWbr (.cv x) (synC2nd) (.cv z))
      (synWex v (.classEq (.cv x) (synCop (.cv v) (.cv z)))) p0022 p0023
  have p0025 :=
    @gAnbi12i (synWbr (.cv y) (synCcnv (synC1st)) (.cv x))
      (synWex w (.classEq (.cv x) (synCop (.cv y) (.cv w))))
      (synWbr (.cv z) (synCcnv (synC2nd)) (.cv x))
      (synWex v (.classEq (.cv x) (synCop (.cv v) (.cv z)))) p0021 p0024
  have p0026 :=
    @gN3bitr4i
      (synWex w (synWex v (synWa (.classEq (.cv x) (synCop (.cv y) (.cv w)))
            (.classEq (.cv x) (synCop (.cv v) (.cv z))))))
      (synWa (synWex w (.classEq (.cv x) (synCop (.cv y) (.cv w))))
        (synWex v (.classEq (.cv x) (synCop (.cv v) (.cv z)))))
      (.classEq (.cv x) (synCop (.cv y) (.cv z)))
      (synWa (synWbr (.cv y) (synCcnv (synC1st)) (.cv x))
        (synWbr (.cv z) (synCcnv (synC2nd)) (.cv x)))
      p0000 p0018 p0025
  have p0027 :=
    @gN2rexbii (.classEq (.cv x) (synCop (.cv y) (.cv z)))
      (synWa (synWbr (.cv y) (synCcnv (synC1st)) (.cv x))
        (synWbr (.cv z) (synCcnv (synC2nd)) (.cv x)))
      y z A B p0026
  have p0028 :=
    @gElxp2 y z (.cv x) A B dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020
  have p0029 :=
    @gElima y (.cv x) (synCcnv (synC1st)) A dv_cache_0014 dv_cache_0021 dv_cache_0016
  have p0030 :=
    @gElima z (.cv x) (synCcnv (synC2nd)) B dv_cache_0015 dv_cache_0022 dv_cache_0019
  have p0031 :=
    @gAnbi12i (.classMem (.cv x) (synCima (synCcnv (synC1st)) A))
      (synWrex y A (synWbr (.cv y) (synCcnv (synC1st)) (.cv x)))
      (.classMem (.cv x) (synCima (synCcnv (synC2nd)) B))
      (synWrex z B (synWbr (.cv z) (synCcnv (synC2nd)) (.cv x))) p0029 p0030
  have p0032 :=
    @gElin (.cv x) (synCima (synCcnv (synC1st)) A) (synCima (synCcnv (synC2nd)) B)
  have p0033 :=
    @gReeanv (synWbr (.cv y) (synCcnv (synC1st)) (.cv x))
      (synWbr (.cv z) (synCcnv (synC2nd)) (.cv x)) y z A B dv_cache_0017 dv_cache_0018
      dv_cache_0023 dv_cache_0024 dv_cache_0020
  have p0034 :=
    @gN3bitr4i
      (synWa (.classMem (.cv x) (synCima (synCcnv (synC1st)) A))
        (.classMem (.cv x) (synCima (synCcnv (synC2nd)) B)))
      (synWa (synWrex y A (synWbr (.cv y) (synCcnv (synC1st)) (.cv x)))
        (synWrex z B (synWbr (.cv z) (synCcnv (synC2nd)) (.cv x))))
      (.classMem (.cv x)
        (synCin (synCima (synCcnv (synC1st)) A) (synCima (synCcnv (synC2nd)) B)))
      (synWrex y A (synWrex z B (synWa (synWbr (.cv y) (synCcnv (synC1st)) (.cv x))
            (synWbr (.cv z) (synCcnv (synC2nd)) (.cv x)))))
      p0031 p0032 p0033
  have p0035 :=
    @gN3bitr4i
      (synWrex y A (synWrex z B (.classEq (.cv x) (synCop (.cv y) (.cv z)))))
      (synWrex y A (synWrex z B (synWa (synWbr (.cv y) (synCcnv (synC1st)) (.cv x))
            (synWbr (.cv z) (synCcnv (synC2nd)) (.cv x)))))
      (.classMem (.cv x) (synCxp A B))
      (.classMem (.cv x)
        (synCin (synCima (synCcnv (synC1st)) A) (synCima (synCcnv (synC2nd)) B)))
      p0027 p0028 p0034
  have p0036 :=
    @gEqriv x (synCxp A B)
      (synCin (synCima (synCcnv (synC1st)) A) (synCima (synCcnv (synC2nd)) B))
      dv_cache_0025 dv_cache_0026 p0035
  exact p0036

/-- Checked nominal proof certificate identified upstream as `g_xpexg`. -/
@[expose]
noncomputable def gXpexg (A : Class) (B : Class) (V : Class) (W : Class) :
    Nominal.NPrf
      (.imp (synWa (.classMem A V) (.classMem B W)) (.classMem (synCxp A B) (synCvv))) :=
  by
  have p0000 := @gDfxp2 A B
  have p0001 := @gN1stex
  have p0002 := @gCnvex (synC1st) p0001
  have p0003 := @gImaexg (synCcnv (synC1st)) A (synCvv) V
  have p0004 :=
    @gMpan (.classMem (synCcnv (synC1st)) (synCvv)) (.classMem A V)
      (.classMem (synCima (synCcnv (synC1st)) A) (synCvv)) p0002 p0003
  have p0005 := @gN2ndex
  have p0006 := @gCnvex (synC2nd) p0005
  have p0007 := @gImaexg (synCcnv (synC2nd)) B (synCvv) W
  have p0008 :=
    @gMpan (.classMem (synCcnv (synC2nd)) (synCvv)) (.classMem B W)
      (.classMem (synCima (synCcnv (synC2nd)) B) (synCvv)) p0006 p0007
  have p0009 :=
    @gInexg (synCima (synCcnv (synC1st)) A) (synCima (synCcnv (synC2nd)) B)
      (synCvv) (synCvv)
  have p0010 :=
    @gSyl2an (.classMem A V) (.classMem (synCima (synCcnv (synC1st)) A) (synCvv))
      (.classMem (synCima (synCcnv (synC2nd)) B) (synCvv))
      (.classMem (synCin (synCima (synCcnv (synC1st)) A) (synCima (synCcnv (synC2nd)) B))
        (synCvv))
      (.classMem B W) p0004 p0008 p0009
  have p0011 :=
    @gSyl5eqel (synWa (.classMem A V) (.classMem B W)) (synCxp A B)
      (synCin (synCima (synCcnv (synC1st)) A) (synCima (synCcnv (synC2nd)) B))
      (synCvv) p0000 p0010
  exact p0011

/-- Checked nominal proof certificate identified upstream as `g_xpex`. -/
@[expose]
noncomputable def gXpex (A : Class) (B : Class)
    (hyp_xpex_1 : Nominal.NPrf (.classMem A (synCvv)))
    (hyp_xpex_2 : Nominal.NPrf (.classMem B (synCvv))) :
    Nominal.NPrf (.classMem (synCxp A B) (synCvv)) :=
  by
  have p0000 := @gXpexg A B (synCvv) (synCvv)
  have p0001 :=
    @gMp2an (.classMem A (synCvv)) (.classMem B (synCvv))
      (.classMem (synCxp A B) (synCvv)) hyp_xpex_1 hyp_xpex_2 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_resexg`. -/
@[expose]
noncomputable def gResexg (A : Class) (B : Class) (V : Class) (W : Class) :
    Nominal.NPrf
      (.imp (synWa (.classMem A V) (.classMem B W)) (.classMem (synCres A B) (synCvv))) :=
  by
  have p0000 := (Nominal.classEqRefl (synCres A B))
  have p0001 := @gVvex
  have p0002 := @gXpexg B (synCvv) W (synCvv)
  have p0003 :=
    @gMpan2 (.classMem B W) (.classMem (synCvv) (synCvv))
      (.classMem (synCxp B (synCvv)) (synCvv)) p0001 p0002
  have p0004 := @gInexg A (synCxp B (synCvv)) V (synCvv)
  have p0005 :=
    @gSylan2 (.classMem B W) (.classMem A V) (.classMem (synCxp B (synCvv)) (synCvv))
      (.classMem (synCin A (synCxp B (synCvv))) (synCvv)) p0003 p0004
  have p0006 :=
    @gSyl5eqel (synWa (.classMem A V) (.classMem B W)) (synCres A B)
      (synCin A (synCxp B (synCvv))) (synCvv) p0000 p0005
  exact p0006

/-- Checked nominal proof certificate identified upstream as `g_resex`. -/
@[expose]
noncomputable def gResex (A : Class) (B : Class)
    (hyp_resex_1 : Nominal.NPrf (.classMem A (synCvv)))
    (hyp_resex_2 : Nominal.NPrf (.classMem B (synCvv))) :
    Nominal.NPrf (.classMem (synCres A B) (synCvv)) :=
  by
  have p0000 := @gResexg A B (synCvv) (synCvv)
  have p0001 :=
    @gMp2an (.classMem A (synCvv)) (.classMem B (synCvv))
      (.classMem (synCres A B) (synCvv)) hyp_resex_1 hyp_resex_2 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_dffun2`. -/
@[expose]
noncomputable def gDffun2 (x : Var) (y : Var) (z : Var) (A : Class) (dv_A_x : x ∉ A.fv)
    (dv_A_y : y ∉ A.fv) (dv_A_z : z ∉ A.fv) (dv_x_y : x ≠ y) (dv_x_z : x ≠ z)
    (dv_y_z : y ≠ z) :
    Nominal.NPrf
      (synWb (synWfun A) (.all x (.all y (.all z
              (.imp (synWa (synWbr (.cv x) A (.cv y)) (synWbr (.cv x) A (.cv z)))
                (.objEq y z)))))) :=
  by
  have dv_cache_0001 : y ∉ ((synCcom A (synCcnv A))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, Finset.mem_union, dv_A_y,
          or_false, not_false_eq_true])
  have dv_cache_0002 : z ∉ ((synCcom A (synCcnv A))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, Finset.mem_union, dv_A_z,
          or_false, not_false_eq_true])
  have dv_cache_0003 : y ∉ ((synCid)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0004 : z ∉ ((synCid)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0005 : y ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show y ≠ z from (by exact dv_y_z))
  have dv_cache_0006 : x ∉ ((Class.cv y)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, dv_x_y,
          not_false_eq_true])
  have dv_cache_0007 : x ∉ ((Class.cv z)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, dv_x_z,
          not_false_eq_true])
  have dv_cache_0008 : x ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_x, not_false_eq_true])
  have dv_cache_0009 : x ∉ ((synCcnv A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, dv_A_x,
          not_false_eq_true])
  have dv_cache_0010 : x ∉ ((Wff.objEq y z)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_insert,
          Finset.mem_singleton, dv_x_y, dv_x_z, or_false, not_false_eq_true])
  have p0000 := (Nominal.biimpRefl (synWfun A))
  have p0001 :=
    @gSsrel y z (synCcom A (synCcnv A)) (synCid) dv_cache_0001 dv_cache_0002
      dv_cache_0003 dv_cache_0004 dv_cache_0005
  have p0002 :=
    @gOpelco x (.cv y) (.cv z) A (synCcnv A) dv_cache_0006 dv_cache_0007 dv_cache_0008
      dv_cache_0009
  have p0003 := @gBrcnv (.cv y) (.cv x) A
  have p0004 :=
    @gAnbi1i (synWbr (.cv y) (synCcnv A) (.cv x)) (synWbr (.cv x) A (.cv y))
      (synWbr (.cv x) A (.cv z)) p0003
  have p0005 :=
    @gExbii (synWa (synWbr (.cv y) (synCcnv A) (.cv x)) (synWbr (.cv x) A (.cv z)))
      (synWa (synWbr (.cv x) A (.cv y)) (synWbr (.cv x) A (.cv z))) x p0004
  have p0006 :=
    @gBitri (.classMem (synCop (.cv y) (.cv z)) (synCcom A (synCcnv A)))
      (synWex x (synWa (synWbr (.cv y) (synCcnv A) (.cv x)) (synWbr (.cv x) A (.cv z))))
      (synWex x (synWa (synWbr (.cv x) A (.cv y)) (synWbr (.cv x) A (.cv z)))) p0002
      p0005
  have p0007 := (Nominal.biimpRefl (synWbr (.cv y) (synCid) (.cv z)))
  have p0008 := @gVex z
  have p0009 := @gIdeq (.cv y) (.cv z) p0008
  have p0010_e01_recanon :
    Nominal.NPrf (synWb (synWbr (.cv y) (synCid) (.cv z)) (.objEq y z)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWbr synCop synCun synCnin synWnan synWa synCcompl synWrex
          synWex synCphi synCid synCopab
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0009
  have p0010 :=
    @gBitr3i (.classMem (synCop (.cv y) (.cv z)) (synCid))
      (synWbr (.cv y) (synCid) (.cv z)) (.objEq y z) p0007 p0010_e01_recanon
  have p0011 :=
    @gImbi12i (.classMem (synCop (.cv y) (.cv z)) (synCcom A (synCcnv A)))
      (synWex x (synWa (synWbr (.cv x) A (.cv y)) (synWbr (.cv x) A (.cv z))))
      (.classMem (synCop (.cv y) (.cv z)) (synCid)) (.objEq y z) p0006 p0010
  have p0012 :=
    @gN1923v (synWa (synWbr (.cv x) A (.cv y)) (synWbr (.cv x) A (.cv z)))
      (.objEq y z) x dv_cache_0010
  have p0013 :=
    @gBitr4i
      (.imp (.classMem (synCop (.cv y) (.cv z)) (synCcom A (synCcnv A)))
        (.classMem (synCop (.cv y) (.cv z)) (synCid)))
      (.imp (synWex x (synWa (synWbr (.cv x) A (.cv y)) (synWbr (.cv x) A (.cv z))))
        (.objEq y z))
      (.all x (.imp (synWa (synWbr (.cv x) A (.cv y)) (synWbr (.cv x) A (.cv z)))
          (.objEq y z)))
      p0011 p0012
  have p0014 :=
    @gN2albii
      (.imp (.classMem (synCop (.cv y) (.cv z)) (synCcom A (synCcnv A)))
        (.classMem (synCop (.cv y) (.cv z)) (synCid)))
      (.all x (.imp (synWa (synWbr (.cv x) A (.cv y)) (synWbr (.cv x) A (.cv z)))
          (.objEq y z)))
      y z p0013
  have p0015 :=
    @gAlrot3
      (.imp (synWa (synWbr (.cv x) A (.cv y)) (synWbr (.cv x) A (.cv z))) (.objEq y z))
      x y z
  have p0016 :=
    @gBitr4i
      (.all y (.all z (.imp (.classMem (synCop (.cv y) (.cv z)) (synCcom A (synCcnv A)))
            (.classMem (synCop (.cv y) (.cv z)) (synCid)))))
      (.all y (.all z (.all x
            (.imp (synWa (synWbr (.cv x) A (.cv y)) (synWbr (.cv x) A (.cv z)))
              (.objEq y z)))))
      (.all x (.all y (.all z
            (.imp (synWa (synWbr (.cv x) A (.cv y)) (synWbr (.cv x) A (.cv z)))
              (.objEq y z)))))
      p0014 p0015
  have p0017 :=
    @gN3bitri (synWfun A) (synWss (synCcom A (synCcnv A)) (synCid))
      (.all y (.all z (.imp (.classMem (synCop (.cv y) (.cv z)) (synCcom A (synCcnv A)))
            (.classMem (synCop (.cv y) (.cv z)) (synCid)))))
      (.all x (.all y (.all z
            (.imp (synWa (synWbr (.cv x) A (.cv y)) (synWbr (.cv x) A (.cv z)))
              (.objEq y z)))))
      p0000 p0001 p0016
  exact p0017

/-- Checked nominal proof certificate identified upstream as `g_dffun3`. -/
@[expose]
noncomputable def gDffun3 (x : Var) (y : Var) (z : Var) (A : Class) (dv_A_x : x ∉ A.fv)
    (dv_A_y : y ∉ A.fv) (dv_A_z : z ∉ A.fv) (dv_x_y : x ≠ y) (dv_x_z : x ≠ z)
    (dv_y_z : y ≠ z) :
    Nominal.NPrf
      (synWb (synWfun A)
        (.all x (synWex z (.all y (.imp (synWbr (.cv x) A (.cv y)) (.objEq y z)))))) :=
  by
  have dv_cache_0001 : x ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_x, not_false_eq_true])
  have dv_cache_0002 : y ∉ (A).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_y, not_false_eq_true])
  have dv_cache_0003 : z ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_z, not_false_eq_true])
  have dv_cache_0004 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show x ≠ y from (by exact dv_x_y))
  have dv_cache_0005 : x ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show x ≠ z from (by exact dv_x_z))
  have dv_cache_0006 : y ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show y ≠ z from (by exact dv_y_z))
  have dv_cache_0007 : z ∉ ((synWbr (.cv x) A (.cv y))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, (Ne.symm dv_x_z), (Ne.symm dv_y_z), dv_A_z, or_false,
          not_false_eq_true])
  have dv_cache_0008 : y ∉ ((synWbr (.cv x) A (.cv z))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, (Ne.symm dv_x_y), dv_y_z, dv_A_y, or_false,
          not_false_eq_true])
  have p0000 :=
    @gDffun2 x y z A dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006
  have p0001 := @gBreq2 (.cv y) (.cv z) (.cv x) A
  have p0002_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq y z) (synWb (synWbr (.cv x) A (.cv y)) (synWbr (.cv x) A (.cv z)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWbr synCop synCun synCnin synWnan synWa synCcompl synWrex
          synWex synCphi
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0001
  have p0002 :=
    @gMo4 (synWbr (.cv x) A (.cv y)) (synWbr (.cv x) A (.cv z)) y z dv_cache_0007
      dv_cache_0008 dv_cache_0006 p0002_e00_recanon
  have p0003 := @gNfv (synWbr (.cv x) A (.cv y)) z dv_cache_0007
  have p0004 := @gMo2 (synWbr (.cv x) A (.cv y)) y z dv_cache_0006 p0003
  have p0005 :=
    @gBitr3i
      (.all y (.all z (.imp (synWa (synWbr (.cv x) A (.cv y)) (synWbr (.cv x) A (.cv z)))
            (.objEq y z))))
      (synWmo y (synWbr (.cv x) A (.cv y)))
      (synWex z (.all y (.imp (synWbr (.cv x) A (.cv y)) (.objEq y z)))) p0002 p0004
  have p0006 :=
    @gAlbii
      (.all y (.all z (.imp (synWa (synWbr (.cv x) A (.cv y)) (synWbr (.cv x) A (.cv z)))
            (.objEq y z))))
      (synWex z (.all y (.imp (synWbr (.cv x) A (.cv y)) (.objEq y z)))) x p0005
  have p0007 :=
    @gBitri (synWfun A)
      (.all x (.all y (.all z
            (.imp (synWa (synWbr (.cv x) A (.cv y)) (synWbr (.cv x) A (.cv z)))
              (.objEq y z)))))
      (.all x (synWex z (.all y (.imp (synWbr (.cv x) A (.cv y)) (.objEq y z))))) p0000
      p0006
  exact p0007

/-- Checked nominal proof certificate identified upstream as `g_dffun4`. -/
@[expose]
noncomputable def gDffun4 (x : Var) (y : Var) (z : Var) (A : Class) (dv_A_x : x ∉ A.fv)
    (dv_A_y : y ∉ A.fv) (dv_A_z : z ∉ A.fv) (dv_x_y : x ≠ y) (dv_x_z : x ≠ z)
    (dv_y_z : y ≠ z) :
    Nominal.NPrf
      (synWb (synWfun A) (.all x (.all y (.all z (.imp
                (synWa (.classMem (synCop (.cv x) (.cv y)) A)
                  (.classMem (synCop (.cv x) (.cv z)) A)) (.objEq y z)))))) :=
  by
  have dv_cache_0001 : x ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_x, not_false_eq_true])
  have dv_cache_0002 : y ∉ (A).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_y, not_false_eq_true])
  have dv_cache_0003 : z ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_z, not_false_eq_true])
  have dv_cache_0004 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show x ≠ y from (by exact dv_x_y))
  have dv_cache_0005 : x ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show x ≠ z from (by exact dv_x_z))
  have dv_cache_0006 : y ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show y ≠ z from (by exact dv_y_z))
  have p0000 :=
    @gDffun2 x y z A dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006
  have p0001 := (Nominal.biimpRefl (synWbr (.cv x) A (.cv y)))
  have p0002 := (Nominal.biimpRefl (synWbr (.cv x) A (.cv z)))
  have p0003 :=
    @gAnbi12i (synWbr (.cv x) A (.cv y)) (.classMem (synCop (.cv x) (.cv y)) A)
      (synWbr (.cv x) A (.cv z)) (.classMem (synCop (.cv x) (.cv z)) A) p0001 p0002
  have p0004 :=
    @gImbi1i (synWa (synWbr (.cv x) A (.cv y)) (synWbr (.cv x) A (.cv z)))
      (synWa (.classMem (synCop (.cv x) (.cv y)) A) (.classMem (synCop (.cv x) (.cv z)) A))
      (.objEq y z) p0003
  have p0005 :=
    @gAlbii
      (.imp (synWa (synWbr (.cv x) A (.cv y)) (synWbr (.cv x) A (.cv z))) (.objEq y z))
      (.imp (synWa (.classMem (synCop (.cv x) (.cv y)) A)
          (.classMem (synCop (.cv x) (.cv z)) A)) (.objEq y z))
      z p0004
  have p0006 :=
    @gN2albii
      (.all z (.imp (synWa (synWbr (.cv x) A (.cv y)) (synWbr (.cv x) A (.cv z)))
          (.objEq y z)))
      (.all z (.imp (synWa (.classMem (synCop (.cv x) (.cv y)) A)
            (.classMem (synCop (.cv x) (.cv z)) A)) (.objEq y z)))
      x y p0005
  have p0007 :=
    @gBitri (synWfun A)
      (.all x (.all y (.all z
            (.imp (synWa (synWbr (.cv x) A (.cv y)) (synWbr (.cv x) A (.cv z)))
              (.objEq y z)))))
      (.all x (.all y (.all z (.imp (synWa (.classMem (synCop (.cv x) (.cv y)) A)
                (.classMem (synCop (.cv x) (.cv z)) A)) (.objEq y z)))))
      p0000 p0006
  exact p0007


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk011Compact001Part011`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_dffun6f`. -/
@[expose]
noncomputable def gDffun6f (x : Var) (y : Var) (A : Class) (dv_x_y : x ≠ y)
    (hyp_dffun6f_1 : Nominal.NPrf (synWnfc x A))
    (hyp_dffun6f_2 : Nominal.NPrf (synWnfc y A)) :
    Nominal.NPrf (synWb (synWfun A) (.all x (synWmo y (synWbr (.cv x) A (.cv y))))) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ A.fv
  let w : Var := freshVar proofSupport 0
  let v : Var := freshVar proofSupport 1
  let u : Var := freshVar proofSupport 2
  have fresh_w : w ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_w_ne_x : w ≠ x := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_x_ne_w : x ≠ w := Ne.symm fresh_w_ne_x
  have fresh_w_ne_y : w ≠ y := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_y_ne_w : y ≠ w := Ne.symm fresh_w_ne_y
  have fresh_w_not_A : w ∉ A.fv := by
    intro h
    exact fresh_w (Finset.mem_union_right _ (h))
  have fresh_v : v ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_v_ne_y : v ≠ y := by
    intro h
    exact
      fresh_v
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_y_ne_v : y ≠ v := Ne.symm fresh_v_ne_y
  have fresh_v_not_A : v ∉ A.fv := by
    intro h
    exact fresh_v (Finset.mem_union_right _ (h))
  have fresh_u : u ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_u_not_A : u ∉ A.fv := by
    intro h
    exact fresh_u (Finset.mem_union_right _ (h))
  have fresh_w_ne_v : w ≠ v :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_v_ne_w : v ≠ w := Ne.symm fresh_w_ne_v
  have fresh_w_ne_u : w ≠ u :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_u_ne_w : u ≠ w := Ne.symm fresh_w_ne_u
  have fresh_v_ne_u : v ≠ u :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_u_ne_v : u ≠ v := Ne.symm fresh_v_ne_u
  have dv_cache_0001 : w ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_w_not_A, not_false_eq_true])
  have dv_cache_0002 : v ∉ (A).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_v_not_A, not_false_eq_true])
  have dv_cache_0003 : u ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_u_not_A, not_false_eq_true])
  have dv_cache_0004 : w ≠ v :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show w ≠ v from (by exact fresh_w_ne_v))
  have dv_cache_0005 : w ≠ u :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show w ≠ u from (by exact fresh_w_ne_u))
  have dv_cache_0006 : v ≠ u :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show v ≠ u from (by exact fresh_v_ne_u))
  have dv_cache_0007 : y ∉ ((Class.cv w)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_y_ne_w, not_false_eq_true])
  have dv_cache_0008 : y ∉ ((Class.cv v)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_y_ne_v, not_false_eq_true])
  have dv_cache_0009 : v ∉ ((synWbr (.cv w) A (.cv y))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_v_ne_w, fresh_v_ne_y, fresh_v_not_A, or_false,
          not_false_eq_true])
  have dv_cache_0010 : u ∉ ((synWbr (.cv w) A (.cv v))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_u_ne_w, fresh_u_ne_v, fresh_u_not_A, or_false,
          not_false_eq_true])
  have dv_cache_0011 : x ∉ ((Class.cv w)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_x_ne_w, not_false_eq_true])
  have dv_cache_0012 : x ∉ ((Class.cv y)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, dv_x_y,
          not_false_eq_true])
  have dv_cache_0013 : w ∉ ((synWmo y (synWbr (.cv x) A (.cv y)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wmo,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_w_ne_x, fresh_w_ne_y, fresh_w_not_A, or_false,
          and_false, not_false_eq_true])
  have dv_cache_0014 : y ∉ ((Wff.objEq w x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_insert,
          Finset.mem_singleton, fresh_y_ne_w, (Ne.symm dv_x_y), or_false,
          not_false_eq_true])
  have p0000 :=
    @gDffun3 w v u A dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006
  have p0001 := @gNfcv y (.cv w) dv_cache_0007
  have p0002 := @gNfcv y (.cv v) dv_cache_0008
  have p0003 := @gNfbr y (.cv w) (.cv v) A p0001 hyp_dffun6f_2 p0002
  have p0004 := @gNfv (synWbr (.cv w) A (.cv y)) v dv_cache_0009
  have p0005 := @gBreq2 (.cv v) (.cv y) (.cv w) A
  have p0006_e02_recanon :
    Nominal.NPrf
      (.imp (.objEq v y) (synWb (synWbr (.cv w) A (.cv v)) (synWbr (.cv w) A (.cv y)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWbr synCop synCun synCnin synWnan synWa synCcompl synWrex
          synWex synCphi
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0005
  have p0006 :=
    @gCbvmo (synWbr (.cv w) A (.cv v)) (synWbr (.cv w) A (.cv y)) v y p0003 p0004
      p0006_e02_recanon
  have p0007 :=
    @gAlbii (synWmo v (synWbr (.cv w) A (.cv v)))
      (synWmo y (synWbr (.cv w) A (.cv y))) w p0006
  have p0008 := @gNfv (synWbr (.cv w) A (.cv v)) u dv_cache_0010
  have p0009 := @gMo2 (synWbr (.cv w) A (.cv v)) v u dv_cache_0006 p0008
  have p0010 :=
    @gAlbii (synWmo v (synWbr (.cv w) A (.cv v)))
      (synWex u (.all v (.imp (synWbr (.cv w) A (.cv v)) (.objEq v u)))) w p0009
  have p0011 := @gNfcv x (.cv w) dv_cache_0011
  have p0012 := @gNfcv x (.cv y) dv_cache_0012
  have p0013 := @gNfbr x (.cv w) (.cv y) A p0011 hyp_dffun6f_1 p0012
  have p0014 := @gNfmo (synWbr (.cv w) A (.cv y)) x y p0013
  have p0015 := @gNfv (synWmo y (synWbr (.cv x) A (.cv y))) w dv_cache_0013
  have p0016 := @gBreq1 (.cv w) (.cv x) (.cv y) A
  have p0017_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq w x) (synWb (synWbr (.cv w) A (.cv y)) (synWbr (.cv x) A (.cv y)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWbr synCop synCun synCnin synWnan synWa synCcompl synWrex
          synWex synCphi
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0016
  have p0017 :=
    @gMobidv (.objEq w x) (synWbr (.cv w) A (.cv y)) (synWbr (.cv x) A (.cv y)) y
      dv_cache_0014 p0017_e00_recanon
  have p0018 :=
    @gCbval (synWmo y (synWbr (.cv w) A (.cv y)))
      (synWmo y (synWbr (.cv x) A (.cv y))) w x p0014 p0015 p0017
  have p0019 :=
    @gN3bitr3ri (.all w (synWmo v (synWbr (.cv w) A (.cv v))))
      (.all w (synWmo y (synWbr (.cv w) A (.cv y))))
      (.all w (synWex u (.all v (.imp (synWbr (.cv w) A (.cv v)) (.objEq v u)))))
      (.all x (synWmo y (synWbr (.cv x) A (.cv y)))) p0007 p0010 p0018
  have p0020 :=
    @gBitr4i (synWfun A)
      (.all w (synWex u (.all v (.imp (synWbr (.cv w) A (.cv v)) (.objEq v u)))))
      (.all x (synWmo y (synWbr (.cv x) A (.cv y)))) p0000 p0019
  exact p0020

/-- Checked nominal proof certificate identified upstream as `g_dffun6`. -/
@[expose]
noncomputable def gDffun6 (x : Var) (y : Var) (F : Class) (dv_F_x : x ∉ F.fv)
    (dv_F_y : y ∉ F.fv) (dv_x_y : x ≠ y) :
    Nominal.NPrf (synWb (synWfun F) (.all x (synWmo y (synWbr (.cv x) F (.cv y))))) :=
  by
  have dv_cache_0001 : x ∉ (F).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_F_x, not_false_eq_true])
  have dv_cache_0002 : y ∉ (F).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_F_y, not_false_eq_true])
  have dv_cache_0003 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact (show x ≠ y from (by exact dv_x_y))
  have p0000 := @gNfcv x F dv_cache_0001
  have p0001 := @gNfcv y F dv_cache_0002
  have p0002 := @gDffun6f x y F dv_cache_0003 p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_funmo`. -/
@[expose]
noncomputable def gFunmo (y : Var) (A : Class) (F : Class) (dv_A_y : y ∉ A.fv)
    (dv_F_y : y ∉ F.fv) :
    Nominal.NPrf (.imp (synWfun F) (synWmo y (synWbr A F (.cv y)))) :=
  by
  let proofSupport : Finset Var := ({ y } : Finset Var) ∪ A.fv ∪ F.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_ne_y : x ≠ y := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_y_ne_x : y ≠ x := Ne.symm fresh_x_ne_y
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_F : x ∉ F.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have dv_cache_0001 : y ∉ ((Wff.classEq (.cv x) A)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_x, dv_A_y, or_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ (A).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_A, not_false_eq_true])
  have dv_cache_0003 : x ∉ ((synWmo y (synWbr A F (.cv y)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wmo,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_x_not_A, fresh_x_ne_y, fresh_x_not_F, or_false,
          and_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ (F).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_F, not_false_eq_true])
  have dv_cache_0005 : y ∉ (F).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_F_y, not_false_eq_true])
  have dv_cache_0006 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0007 : y ∉ ((Wff.classMem A (synCvv))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union, dv_A_y,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have p0000 := @gBrreldmex A (.cv y) F
  have p0001 := @gAncri (synWbr A F (.cv y)) (.classMem A (synCvv)) p0000
  have p0002 := Nominal.gen p0001 y
  have p0003 := @gBreq1 (.cv x) A (.cv y) F
  have p0004 :=
    @gMobidv (.classEq (.cv x) A) (synWbr (.cv x) F (.cv y)) (synWbr A F (.cv y)) y
      dv_cache_0001 p0003
  have p0005 :=
    @gSpcgv (synWmo y (synWbr (.cv x) F (.cv y))) (synWmo y (synWbr A F (.cv y))) x A
      (synCvv) dv_cache_0002 dv_cache_0003 p0004
  have p0006 :=
    @gCom12 (.classMem A (synCvv)) (.all x (synWmo y (synWbr (.cv x) F (.cv y))))
      (synWmo y (synWbr A F (.cv y))) p0005
  have p0007 := @gDffun6 x y F dv_cache_0004 dv_cache_0005 dv_cache_0006
  have p0008 := @gMoanimv (.classMem A (synCvv)) (synWbr A F (.cv y)) y dv_cache_0007
  have p0009 :=
    @gN3imtr4i (.all x (synWmo y (synWbr (.cv x) F (.cv y))))
      (.imp (.classMem A (synCvv)) (synWmo y (synWbr A F (.cv y)))) (synWfun F)
      (synWmo y (synWa (.classMem A (synCvv)) (synWbr A F (.cv y)))) p0006 p0007 p0008
  have p0010 :=
    @gMoim (synWbr A F (.cv y)) (synWa (.classMem A (synCvv)) (synWbr A F (.cv y))) y
  have p0011 :=
    @gMpsyl
      (.all y (.imp (synWbr A F (.cv y))
          (synWa (.classMem A (synCvv)) (synWbr A F (.cv y)))))
      (synWfun F) (synWmo y (synWa (.classMem A (synCvv)) (synWbr A F (.cv y))))
      (synWmo y (synWbr A F (.cv y))) p0002 p0009 p0010
  exact p0011

/-- Checked nominal proof certificate identified upstream as `g_funss`. -/
@[expose]
noncomputable def gFunss (A : Class) (B : Class) :
    Nominal.NPrf (.imp (synWss A B) (.imp (synWfun B) (synWfun A))) :=
  by
  have p0000 := @gCoss1 A B (synCcnv A)
  have p0001 := @gCnvss A B
  have p0002 := @gCoss2 (synCcnv A) (synCcnv B) B
  have p0003 :=
    @gSyl (synWss A B) (synWss (synCcnv A) (synCcnv B))
      (synWss (synCcom B (synCcnv A)) (synCcom B (synCcnv B))) p0001 p0002
  have p0004 :=
    @gSstrd (synWss A B) (synCcom A (synCcnv A)) (synCcom B (synCcnv A))
      (synCcom B (synCcnv B)) p0000 p0003
  have p0005 := @gSstr2 (synCcom A (synCcnv A)) (synCcom B (synCcnv B)) (synCid)
  have p0006 :=
    @gSyl (synWss A B) (synWss (synCcom A (synCcnv A)) (synCcom B (synCcnv B)))
      (.imp (synWss (synCcom B (synCcnv B)) (synCid))
        (synWss (synCcom A (synCcnv A)) (synCid)))
      p0004 p0005
  have p0007 := (Nominal.biimpRefl (synWfun B))
  have p0008 := (Nominal.biimpRefl (synWfun A))
  have p0009 :=
    @gN3imtr4g (synWss A B) (synWss (synCcom B (synCcnv B)) (synCid))
      (synWss (synCcom A (synCcnv A)) (synCid)) (synWfun B) (synWfun A) p0006 p0007
      p0008
  exact p0009

/-- Checked nominal proof certificate identified upstream as `g_funeq`. -/
@[expose]
noncomputable def gFuneq (A : Class) (B : Class) :
    Nominal.NPrf (.imp (.classEq A B) (synWb (synWfun A) (synWfun B))) :=
  by
  have p0000 := @gFunss B A
  have p0001 := @gFunss A B
  have p0002 :=
    @gAnim12i (synWss B A) (.imp (synWfun A) (synWfun B)) (synWss A B)
      (.imp (synWfun B) (synWfun A)) p0000 p0001
  have p0003 :=
    @gAncoms (synWss B A) (synWss A B)
      (synWa (.imp (synWfun A) (synWfun B)) (.imp (synWfun B) (synWfun A))) p0002
  have p0004 := @gEqss A B
  have p0005 := @gDfbi2 (synWfun A) (synWfun B)
  have p0006 :=
    @gN3imtr4i (synWa (synWss A B) (synWss B A))
      (synWa (.imp (synWfun A) (synWfun B)) (.imp (synWfun B) (synWfun A)))
      (.classEq A B) (synWb (synWfun A) (synWfun B)) p0003 p0004 p0005
  exact p0006

/-- Checked nominal proof certificate identified upstream as `g_funeqi`. -/
@[expose]
noncomputable def gFuneqi (A : Class) (B : Class)
    (hyp_funeqi_1 : Nominal.NPrf (.classEq A B)) :
    Nominal.NPrf (synWb (synWfun A) (synWfun B)) :=
  by
  have p0000 := @gFuneq A B
  have p0001 := Nominal.mp hyp_funeqi_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_funeqd`. -/
@[expose]
noncomputable def gFuneqd (ph : Wff) (A : Class) (B : Class)
    (hyp_funeqd_1 : Nominal.NPrf (.imp ph (.classEq A B))) :
    Nominal.NPrf (.imp ph (synWb (synWfun A) (synWfun B))) :=
  by
  have p0000 := @gFuneq A B
  have p0001 :=
    @gSyl ph (.classEq A B) (synWb (synWfun A) (synWfun B)) hyp_funeqd_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_funeu`. -/
@[expose]
noncomputable def gFuneu (y : Var) (A : Class) (B : Class) (F : Class)
    (dv_A_y : y ∉ A.fv) (dv_F_y : y ∉ F.fv) :
    Nominal.NPrf
      (.imp (synWa (synWfun F) (synWbr A F B)) (synWeu y (synWbr A F (.cv y)))) :=
  by
  have dv_cache_0001 : y ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_y, not_false_eq_true])
  have dv_cache_0002 : y ∉ (F).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_F_y, not_false_eq_true])
  have p0000 := @gBreldm A B F
  have p0001 := @gEldm y A F dv_cache_0001 dv_cache_0002
  have p0002 :=
    @gSylib (synWbr A F B) (.classMem A (synCdm F)) (synWex y (synWbr A F (.cv y)))
      p0000 p0001
  have p0003 :=
    @gAdantl (synWbr A F B) (synWex y (synWbr A F (.cv y))) (synWfun F) p0002
  have p0004 := @gFunmo y A F dv_cache_0001 dv_cache_0002
  have p0005 :=
    @gAdantr (synWfun F) (synWmo y (synWbr A F (.cv y))) (synWbr A F B) p0004
  have p0006 :=
    @gJca (synWa (synWfun F) (synWbr A F B)) (synWex y (synWbr A F (.cv y)))
      (synWmo y (synWbr A F (.cv y))) p0003 p0005
  have p0007 := @gEu5 (synWbr A F (.cv y)) y
  have p0008 :=
    @gSylibr (synWa (synWfun F) (synWbr A F B))
      (synWa (synWex y (synWbr A F (.cv y))) (synWmo y (synWbr A F (.cv y))))
      (synWeu y (synWbr A F (.cv y))) p0006 p0007
  exact p0008

/-- Checked nominal proof certificate identified upstream as `g_funeu2`. -/
@[expose]
noncomputable def gFuneu2 (y : Var) (A : Class) (B : Class) (F : Class)
    (dv_A_y : y ∉ A.fv) (dv_F_y : y ∉ F.fv) :
    Nominal.NPrf
      (.imp (synWa (synWfun F) (.classMem (synCop A B) F))
        (synWeu y (.classMem (synCop A (.cv y)) F))) :=
  by
  have dv_cache_0001 : y ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_y, not_false_eq_true])
  have dv_cache_0002 : y ∉ (F).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_F_y, not_false_eq_true])
  have p0000 := (Nominal.biimpRefl (synWbr A F B))
  have p0001 := @gFuneu y A B F dv_cache_0001 dv_cache_0002
  have p0002 := (Nominal.biimpRefl (synWbr A F (.cv y)))
  have p0003 := @gEubii (synWbr A F (.cv y)) (.classMem (synCop A (.cv y)) F) y p0002
  have p0004 :=
    @gSylib (synWa (synWfun F) (synWbr A F B)) (synWeu y (synWbr A F (.cv y)))
      (synWeu y (.classMem (synCop A (.cv y)) F)) p0001 p0003
  have p0005 :=
    @gSylan2br (.classMem (synCop A B) F) (synWfun F) (synWbr A F B)
      (synWeu y (.classMem (synCop A (.cv y)) F)) p0000 p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_funfn`. -/
@[expose]
noncomputable def gFunfn (A : Class) :
    Nominal.NPrf (synWb (synWfun A) (synWfn A (synCdm A))) :=
  by
  have p0000 := @gEqid (synCdm A)
  have p0001 := @gBiantru (.classEq (synCdm A) (synCdm A)) (synWfun A) p0000
  have p0002 := (Nominal.biimpRefl (synWfn A (synCdm A)))
  have p0003 :=
    @gBitr4i (synWfun A) (synWa (synWfun A) (.classEq (synCdm A) (synCdm A)))
      (synWfn A (synCdm A)) p0001 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_funi`. -/
@[expose]
noncomputable def gFuni : Nominal.NPrf (synWfun (synCid)) :=
  by
  have p0000 := @gCnvi
  have p0001 := @gCoeq2i (synCcnv (synCid)) (synCid) (synCid) p0000
  have p0002 := @gCoi1 (synCid)
  have p0003 :=
    @gEqtri (synCcom (synCid) (synCcnv (synCid))) (synCcom (synCid) (synCid))
      (synCid) p0001 p0002
  have p0004 := @gEqimssi (synCcom (synCid) (synCcnv (synCid))) (synCid) p0003
  have p0005 := (Nominal.biimpRefl (synWfun (synCid)))
  have p0006 :=
    @gMpbir (synWfun (synCid))
      (synWss (synCcom (synCid) (synCcnv (synCid))) (synCid)) p0004 p0005
  exact p0006

/-- Checked nominal proof certificate identified upstream as `g_funopab`. -/
@[expose]
noncomputable def gFunopab (ph : Wff) (x : Var) (y : Var) (dv_x_y : x ≠ y) :
    Nominal.NPrf (synWb (synWfun (synCopab x y ph)) (.all x (synWmo y ph))) :=
  by
  have dv_cache_0001 : x ≠ y := by exact (show x ≠ y from (by exact dv_x_y))
  have p0000 := @gNfopab1 ph x y
  have p0001 := @gNfopab2 ph x y
  have p0002 := @gDffun6f x y (synCopab x y ph) dv_cache_0001 p0000 p0001
  have p0003 := (Nominal.biimpRefl (synWbr (.cv x) (synCopab x y ph) (.cv y)))
  have p0004 := @gOpabid ph x y
  have p0005 :=
    @gBitri (synWbr (.cv x) (synCopab x y ph) (.cv y))
      (.classMem (synCop (.cv x) (.cv y)) (synCopab x y ph)) ph p0003 p0004
  have p0006 := @gMobii (synWbr (.cv x) (synCopab x y ph) (.cv y)) ph y p0005
  have p0007 :=
    @gAlbii (synWmo y (synWbr (.cv x) (synCopab x y ph) (.cv y))) (synWmo y ph) x
      p0006
  have p0008 :=
    @gBitri (synWfun (synCopab x y ph))
      (.all x (synWmo y (synWbr (.cv x) (synCopab x y ph) (.cv y))))
      (.all x (synWmo y ph)) p0002 p0007
  exact p0008

/-- Checked nominal proof certificate identified upstream as `g_funco`. -/
@[expose]
noncomputable def gFunco (F : Class) (G : Class) :
    Nominal.NPrf (.imp (synWa (synWfun F) (synWfun G)) (synWfun (synCcom F G))) :=
  by
  let proofSupport : Finset Var := F.fv ∪ G.fv
  let x : Var := freshVar proofSupport 0
  let z : Var := freshVar proofSupport 1
  let y : Var := freshVar proofSupport 2
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_F : x ∉ F.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_not_G : x ∉ G.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_z_not_F : z ∉ F.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (h))
  have fresh_z_not_G : z ∉ G.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_y_not_F : y ∉ F.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (h))
  have fresh_y_not_G : y ∉ G.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_x_ne_z : x ≠ z :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_z_ne_x : z ≠ x := Ne.symm fresh_x_ne_z
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_y_ne_x : y ≠ x := Ne.symm fresh_x_ne_y
  have fresh_z_ne_y : z ≠ y :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_y_ne_z : y ≠ z := Ne.symm fresh_z_ne_y
  have dv_cache_0001 : z ∉ ((Class.cv x)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_z_ne_x, not_false_eq_true])
  have dv_cache_0002 : z ∉ (G).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_G, not_false_eq_true])
  have dv_cache_0003 : y ∉ ((Class.cv z)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_y_ne_z, not_false_eq_true])
  have dv_cache_0004 : y ∉ (F).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_F, not_false_eq_true])
  have dv_cache_0005 : z ∉ ((synWfun F)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfun, fresh_z_not_F,
          not_false_eq_true])
  have dv_cache_0006 : y ∉ ((synWbr (.cv x) G (.cv z))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_x, fresh_y_ne_z, fresh_y_not_G, or_false,
          not_false_eq_true])
  have dv_cache_0007 : x ∉ ((synWa (synWfun F) (synWfun G))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfun, Finset.mem_union,
          fresh_x_not_F, fresh_x_not_G, or_false, not_false_eq_true])
  have dv_cache_0008 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0009 : x ∉ (F).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_F, not_false_eq_true])
  have dv_cache_0010 : z ∉ (F).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_F, not_false_eq_true])
  have dv_cache_0011 : x ∉ (G).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_G, not_false_eq_true])
  have dv_cache_0012 : y ∉ (G).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_G, not_false_eq_true])
  have dv_cache_0013 : x ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact (show x ≠ z from (by exact fresh_x_ne_z))
  have dv_cache_0014 : y ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact (show y ≠ z from (by exact fresh_y_ne_z))
  have p0000 := @gFunmo z (.cv x) G dv_cache_0001 dv_cache_0002
  have p0001 := @gFunmo y (.cv z) F dv_cache_0003 dv_cache_0004
  have p0002 :=
    @gAlrimiv (synWfun F) (synWmo y (synWbr (.cv z) F (.cv y))) z dv_cache_0005 p0001
  have p0003 :=
    @gMoexexv (synWbr (.cv x) G (.cv z)) (synWbr (.cv z) F (.cv y)) z y dv_cache_0006
  have p0004 :=
    @gSyl2anr (synWfun G) (synWmo z (synWbr (.cv x) G (.cv z)))
      (.all z (synWmo y (synWbr (.cv z) F (.cv y))))
      (synWmo y (synWex z (synWa (synWbr (.cv x) G (.cv z)) (synWbr (.cv z) F (.cv y)))))
      (synWfun F) p0000 p0002 p0003
  have p0005 :=
    @gAlrimiv (synWa (synWfun F) (synWfun G))
      (synWmo y (synWex z (synWa (synWbr (.cv x) G (.cv z)) (synWbr (.cv z) F (.cv y)))))
      x dv_cache_0007 p0004
  have p0006 :=
    @gFunopab
      (synWex z (synWa (synWbr (.cv x) G (.cv z)) (synWbr (.cv z) F (.cv y)))) x y
      dv_cache_0008
  have p0007 :=
    @gSylibr (synWa (synWfun F) (synWfun G))
      (.all x (synWmo y
          (synWex z (synWa (synWbr (.cv x) G (.cv z)) (synWbr (.cv z) F (.cv y))))))
      (synWfun (synCopab x y
          (synWex z (synWa (synWbr (.cv x) G (.cv z)) (synWbr (.cv z) F (.cv y))))))
      p0005 p0006
  have p0008 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfCo x y z F G
      dv_cache_0009 dv_cache_0004 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0002
      dv_cache_0008 dv_cache_0013 dv_cache_0014
  have p0009 :=
    @gFuneqi (synCcom F G)
      (synCopab x y
        (synWex z (synWa (synWbr (.cv x) G (.cv z)) (synWbr (.cv z) F (.cv y)))))
      p0008
  have p0010 :=
    @gSylibr (synWa (synWfun F) (synWfun G))
      (synWfun (synCopab x y
          (synWex z (synWa (synWbr (.cv x) G (.cv z)) (synWbr (.cv z) F (.cv y))))))
      (synWfun (synCcom F G)) p0007 p0009
  exact p0010

/-- Checked nominal proof certificate identified upstream as `g_funres`. -/
@[expose]
noncomputable def gFunres (A : Class) (F : Class) :
    Nominal.NPrf (.imp (synWfun F) (synWfun (synCres F A))) :=
  by
  have p0000 := @gResss F A
  have p0001 := @gFunss (synCres F A) F
  have p0002 := Nominal.mp p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_funssres`. -/
@[expose]
noncomputable def gFunssres (F : Class) (G : Class) :
    Nominal.NPrf
      (.imp (synWa (synWfun F) (synWss G F)) (.classEq (synCres F (synCdm G)) G)) :=
  by
  let proofSupport : Finset Var := F.fv ∪ G.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_F : x ∉ F.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_not_G : x ∉ G.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_F : y ∉ F.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (h))
  have fresh_y_not_G : y ∉ G.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x := Ne.symm fresh_x_ne_y
  have dv_cache_0001 : y ∉ ((Class.cv x)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_y_ne_x, not_false_eq_true])
  have dv_cache_0002 : y ∉ (F).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_F, not_false_eq_true])
  have dv_cache_0003 : y ∉ (G).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_G, not_false_eq_true])
  have dv_cache_0004 : y ∉ ((synWss G F)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, Finset.mem_union,
          fresh_y_not_G, fresh_y_not_F, or_false, not_false_eq_true])
  have dv_cache_0005 : x ∉ ((synCres F (synCdm G))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, Finset.mem_union,
          fresh_x_not_F, fresh_x_not_G, or_false, not_false_eq_true])
  have dv_cache_0006 : y ∉ ((synCres F (synCdm G))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, Finset.mem_union,
          fresh_y_not_F, fresh_y_not_G, or_false, not_false_eq_true])
  have dv_cache_0007 : x ∉ (G).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_G, not_false_eq_true])
  have dv_cache_0008 : x ∉ ((synWa (synWfun F) (synWss G F))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, Finset.mem_union,
          fresh_x_not_F, fresh_x_not_G, or_false, not_false_eq_true])
  have dv_cache_0009 : y ∉ ((synWa (synWfun F) (synWss G F))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, Finset.mem_union,
          fresh_y_not_F, fresh_y_not_G, or_false, not_false_eq_true])
  have dv_cache_0010 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have p0000 := @gSsel G F (synCop (.cv x) (.cv y))
  have p0001 :=
    @gAdantl (synWss G F)
      (.imp (.classMem (synCop (.cv x) (.cv y)) G) (.classMem (synCop (.cv x) (.cv y)) F))
      (synWfun F) p0000
  have p0002 := @gOpeldm (.cv x) (.cv y) G
  have p0003 :=
    @gA1i (.imp (.classMem (synCop (.cv x) (.cv y)) G) (.classMem (.cv x) (synCdm G)))
      (synWa (synWfun F) (synWss G F)) p0002
  have p0004 :=
    @gJcad (synWa (synWfun F) (synWss G F)) (.classMem (synCop (.cv x) (.cv y)) G)
      (.classMem (synCop (.cv x) (.cv y)) F) (.classMem (.cv x) (synCdm G)) p0001 p0003
  have p0005 := @gFuneu2 y (.cv x) (.cv y) F dv_cache_0001 dv_cache_0002
  have p0006 := @gEldm2 y (.cv x) G dv_cache_0001 dv_cache_0003
  have p0007 :=
    @gAncrd (synWss G F) (.classMem (synCop (.cv x) (.cv y)) G)
      (.classMem (synCop (.cv x) (.cv y)) F) p0000
  have p0008 :=
    @gEximdv (synWss G F) (.classMem (synCop (.cv x) (.cv y)) G)
      (synWa (.classMem (synCop (.cv x) (.cv y)) F) (.classMem (synCop (.cv x) (.cv y)) G))
      y dv_cache_0004 p0007
  have p0009 :=
    @gSyl5bi (.classMem (.cv x) (synCdm G))
      (synWex y (.classMem (synCop (.cv x) (.cv y)) G)) (synWss G F)
      (synWex y (synWa (.classMem (synCop (.cv x) (.cv y)) F)
          (.classMem (synCop (.cv x) (.cv y)) G)))
      p0006 p0008
  have p0010 :=
    @gImp (synWss G F) (.classMem (.cv x) (synCdm G))
      (synWex y (synWa (.classMem (synCop (.cv x) (.cv y)) F)
          (.classMem (synCop (.cv x) (.cv y)) G)))
      p0009
  have p0011 :=
    @gEupick (.classMem (synCop (.cv x) (.cv y)) F)
      (.classMem (synCop (.cv x) (.cv y)) G) y
  have p0012 :=
    @gSyl2an (synWa (synWfun F) (.classMem (synCop (.cv x) (.cv y)) F))
      (synWeu y (.classMem (synCop (.cv x) (.cv y)) F))
      (synWex y (synWa (.classMem (synCop (.cv x) (.cv y)) F)
          (.classMem (synCop (.cv x) (.cv y)) G)))
      (.imp (.classMem (synCop (.cv x) (.cv y)) F) (.classMem (synCop (.cv x) (.cv y)) G))
      (synWa (synWss G F) (.classMem (.cv x) (synCdm G))) p0005 p0010 p0011
  have p0013 :=
    @gExp43 (synWfun F) (.classMem (synCop (.cv x) (.cv y)) F) (synWss G F)
      (.classMem (.cv x) (synCdm G))
      (.imp (.classMem (synCop (.cv x) (.cv y)) F) (.classMem (synCop (.cv x) (.cv y)) G))
      p0012
  have p0014 :=
    @gCom23 (synWfun F) (.classMem (synCop (.cv x) (.cv y)) F) (synWss G F)
      (.imp (.classMem (.cv x) (synCdm G)) (.imp (.classMem (synCop (.cv x) (.cv y)) F)
          (.classMem (synCop (.cv x) (.cv y)) G)))
      p0013
  have p0015 :=
    @gImp (synWfun F) (synWss G F)
      (.imp (.classMem (synCop (.cv x) (.cv y)) F) (.imp (.classMem (.cv x) (synCdm G))
          (.imp (.classMem (synCop (.cv x) (.cv y)) F)
            (.classMem (synCop (.cv x) (.cv y)) G))))
      p0014
  have p0016 :=
    @gCom34 (synWa (synWfun F) (synWss G F)) (.classMem (synCop (.cv x) (.cv y)) F)
      (.classMem (.cv x) (synCdm G)) (.classMem (synCop (.cv x) (.cv y)) F)
      (.classMem (synCop (.cv x) (.cv y)) G) p0015
  have p0017 :=
    @gPm243d (synWa (synWfun F) (synWss G F)) (.classMem (synCop (.cv x) (.cv y)) F)
      (.imp (.classMem (.cv x) (synCdm G)) (.classMem (synCop (.cv x) (.cv y)) G)) p0016
  have p0018 :=
    @gImp3a (synWa (synWfun F) (synWss G F)) (.classMem (synCop (.cv x) (.cv y)) F)
      (.classMem (.cv x) (synCdm G)) (.classMem (synCop (.cv x) (.cv y)) G) p0017
  have p0019 :=
    @gImpbid (synWa (synWfun F) (synWss G F)) (.classMem (synCop (.cv x) (.cv y)) G)
      (synWa (.classMem (synCop (.cv x) (.cv y)) F) (.classMem (.cv x) (synCdm G)))
      p0004 p0018
  have p0020 := @gOpelres (.cv x) (.cv y) F (synCdm G)
  have p0021 :=
    @gSyl6rbbr (synWa (synWfun F) (synWss G F))
      (.classMem (synCop (.cv x) (.cv y)) G)
      (synWa (.classMem (synCop (.cv x) (.cv y)) F) (.classMem (.cv x) (synCdm G)))
      (.classMem (synCop (.cv x) (.cv y)) (synCres F (synCdm G))) p0019 p0020
  have p0022 :=
    @gEqrelrdv (synWa (synWfun F) (synWss G F)) x y (synCres F (synCdm G)) G
      dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0003 dv_cache_0008 dv_cache_0009
      dv_cache_0010 p0021
  exact p0022


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk011Compact001Part012`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_funun`. -/
@[expose]
noncomputable def gFunun (F : Class) (G : Class) :
    Nominal.NPrf
      (.imp (synWa (synWa (synWfun F) (synWfun G))
          (.classEq (synCin (synCdm F) (synCdm G)) (synC0))) (synWfun (synCun F G))) :=
  by
  let proofSupport : Finset Var := F.fv ∪ G.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let z : Var := freshVar proofSupport 2
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_F : x ∉ F.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_not_G : x ∉ G.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_F : y ∉ F.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (h))
  have fresh_y_not_G : y ∉ G.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_z_not_F : z ∉ F.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (h))
  have fresh_z_not_G : z ∉ G.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_x_ne_z : x ≠ z :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_y_ne_z : y ≠ z :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have dv_cache_0001 : x ∉ ((synCdm F)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, fresh_x_not_F,
          not_false_eq_true])
  have dv_cache_0002 : x ∉ ((synCdm G)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, fresh_x_not_G,
          not_false_eq_true])
  have dv_cache_0003 : x ∉ (F).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_F, not_false_eq_true])
  have dv_cache_0004 : y ∉ (F).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_F, not_false_eq_true])
  have dv_cache_0005 : z ∉ (F).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_F, not_false_eq_true])
  have dv_cache_0006 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0007 : x ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact (show x ≠ z from (by exact fresh_x_ne_z))
  have dv_cache_0008 : y ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact (show y ≠ z from (by exact fresh_y_ne_z))
  have dv_cache_0009 : x ∉ (G).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_G, not_false_eq_true])
  have dv_cache_0010 : y ∉ (G).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_G, not_false_eq_true])
  have dv_cache_0011 : z ∉ (G).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_G, not_false_eq_true])
  have dv_cache_0012 :
    z ∉
      ((synWa (synWa (synWfun F) (synWfun G))
          (.classEq (synCin (synCdm F) (synCdm G)) (synC0)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfun,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union,
          fresh_z_not_F, fresh_z_not_G, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0013 :
    x ∉
      ((synWa (synWa (synWfun F) (synWfun G))
          (.classEq (synCin (synCdm F) (synCdm G)) (synC0)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfun,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union,
          fresh_x_not_F, fresh_x_not_G, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0014 :
    y ∉
      ((synWa (synWa (synWfun F) (synWfun G))
          (.classEq (synCin (synCdm F) (synCdm G)) (synC0)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfun,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union,
          fresh_y_not_F, fresh_y_not_G, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0015 : x ∉ ((synCun F G)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, Finset.mem_union,
          fresh_x_not_F, fresh_x_not_G, or_false, not_false_eq_true])
  have dv_cache_0016 : y ∉ ((synCun F G)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, Finset.mem_union,
          fresh_y_not_F, fresh_y_not_G, or_false, not_false_eq_true])
  have dv_cache_0017 : z ∉ ((synCun F G)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, Finset.mem_union,
          fresh_z_not_F, fresh_z_not_G, or_false, not_false_eq_true])
  have p0000 := @gElun (synCop (.cv x) (.cv y)) F G
  have p0001 := @gElun (synCop (.cv x) (.cv z)) F G
  have p0002 :=
    @gAnbi12i (.classMem (synCop (.cv x) (.cv y)) (synCun F G))
      (synWo (.classMem (synCop (.cv x) (.cv y)) F) (.classMem (synCop (.cv x) (.cv y)) G))
      (.classMem (synCop (.cv x) (.cv z)) (synCun F G))
      (synWo (.classMem (synCop (.cv x) (.cv z)) F) (.classMem (synCop (.cv x) (.cv z)) G))
      p0000 p0001
  have p0003 :=
    @gAnddi (.classMem (synCop (.cv x) (.cv y)) F)
      (.classMem (synCop (.cv x) (.cv y)) G) (.classMem (synCop (.cv x) (.cv z)) F)
      (.classMem (synCop (.cv x) (.cv z)) G)
  have p0004 :=
    @gBitri
      (synWa (.classMem (synCop (.cv x) (.cv y)) (synCun F G))
        (.classMem (synCop (.cv x) (.cv z)) (synCun F G)))
      (synWa (synWo (.classMem (synCop (.cv x) (.cv y)) F)
          (.classMem (synCop (.cv x) (.cv y)) G))
        (synWo (.classMem (synCop (.cv x) (.cv z)) F)
          (.classMem (synCop (.cv x) (.cv z)) G)))
      (synWo (synWo (synWa (.classMem (synCop (.cv x) (.cv y)) F)
            (.classMem (synCop (.cv x) (.cv z)) F))
          (synWa (.classMem (synCop (.cv x) (.cv y)) F)
            (.classMem (synCop (.cv x) (.cv z)) G))) (synWo
          (synWa (.classMem (synCop (.cv x) (.cv y)) G)
            (.classMem (synCop (.cv x) (.cv z)) F))
          (synWa (.classMem (synCop (.cv x) (.cv y)) G)
            (.classMem (synCop (.cv x) (.cv z)) G))))
      p0002 p0003
  have p0005 :=
    @gSp (.imp (.classMem (.cv x) (synCdm F)) (.neg (.classMem (.cv x) (synCdm G)))) x
  have p0006 := @gDisj1 x (synCdm F) (synCdm G) dv_cache_0001 dv_cache_0002
  have p0007 := @gImnan (.classMem (.cv x) (synCdm F)) (.classMem (.cv x) (synCdm G))
  have p0008 :=
    @gBicomi
      (.imp (.classMem (.cv x) (synCdm F)) (.neg (.classMem (.cv x) (synCdm G))))
      (.neg (synWa (.classMem (.cv x) (synCdm F)) (.classMem (.cv x) (synCdm G))))
      p0007
  have p0009 :=
    @gN3imtr4i
      (.all x (.imp (.classMem (.cv x) (synCdm F)) (.neg (.classMem (.cv x) (synCdm G)))))
      (.imp (.classMem (.cv x) (synCdm F)) (.neg (.classMem (.cv x) (synCdm G))))
      (.classEq (synCin (synCdm F) (synCdm G)) (synC0))
      (.neg (synWa (.classMem (.cv x) (synCdm F)) (.classMem (.cv x) (synCdm G))))
      p0005 p0006 p0008
  have p0010 := @gOpeldm (.cv x) (.cv y) F
  have p0011 := @gOpeldm (.cv x) (.cv z) G
  have p0012 :=
    @gAnim12i (.classMem (synCop (.cv x) (.cv y)) F) (.classMem (.cv x) (synCdm F))
      (.classMem (synCop (.cv x) (.cv z)) G) (.classMem (.cv x) (synCdm G)) p0010 p0011
  have p0013 :=
    @gNsyl (.classEq (synCin (synCdm F) (synCdm G)) (synC0))
      (synWa (.classMem (.cv x) (synCdm F)) (.classMem (.cv x) (synCdm G)))
      (synWa (.classMem (synCop (.cv x) (.cv y)) F) (.classMem (synCop (.cv x) (.cv z)) G))
      p0009 p0012
  have p0014 :=
    @gOrel2
      (synWa (.classMem (synCop (.cv x) (.cv y)) F) (.classMem (synCop (.cv x) (.cv z)) G))
      (synWa (.classMem (synCop (.cv x) (.cv y)) F) (.classMem (synCop (.cv x) (.cv z)) F))
  have p0015 :=
    @gSyl (.classEq (synCin (synCdm F) (synCdm G)) (synC0))
      (.neg (synWa (.classMem (synCop (.cv x) (.cv y)) F)
          (.classMem (synCop (.cv x) (.cv z)) G)))
      (.imp (synWo (synWa (.classMem (synCop (.cv x) (.cv y)) F)
            (.classMem (synCop (.cv x) (.cv z)) F))
          (synWa (.classMem (synCop (.cv x) (.cv y)) F)
            (.classMem (synCop (.cv x) (.cv z)) G)))
        (synWa (.classMem (synCop (.cv x) (.cv y)) F)
          (.classMem (synCop (.cv x) (.cv z)) F)))
      p0013 p0014
  have p0016 :=
    @gSp (.imp (.classMem (.cv x) (synCdm G)) (.neg (.classMem (.cv x) (synCdm F)))) x
  have p0017 := @gIncom (synCdm F) (synCdm G)
  have p0018 :=
    @gEqeq1i (synCin (synCdm F) (synCdm G)) (synCin (synCdm G) (synCdm F)) (synC0)
      p0017
  have p0019 := @gDisj1 x (synCdm G) (synCdm F) dv_cache_0002 dv_cache_0001
  have p0020 :=
    @gBitri (.classEq (synCin (synCdm F) (synCdm G)) (synC0))
      (.classEq (synCin (synCdm G) (synCdm F)) (synC0))
      (.all x (.imp (.classMem (.cv x) (synCdm G)) (.neg (.classMem (.cv x) (synCdm F)))))
      p0018 p0019
  have p0021 := @gImnan (.classMem (.cv x) (synCdm G)) (.classMem (.cv x) (synCdm F))
  have p0022 :=
    @gBicomi
      (.imp (.classMem (.cv x) (synCdm G)) (.neg (.classMem (.cv x) (synCdm F))))
      (.neg (synWa (.classMem (.cv x) (synCdm G)) (.classMem (.cv x) (synCdm F))))
      p0021
  have p0023 :=
    @gN3imtr4i
      (.all x (.imp (.classMem (.cv x) (synCdm G)) (.neg (.classMem (.cv x) (synCdm F)))))
      (.imp (.classMem (.cv x) (synCdm G)) (.neg (.classMem (.cv x) (synCdm F))))
      (.classEq (synCin (synCdm F) (synCdm G)) (synC0))
      (.neg (synWa (.classMem (.cv x) (synCdm G)) (.classMem (.cv x) (synCdm F))))
      p0016 p0020 p0022
  have p0024 := @gOpeldm (.cv x) (.cv y) G
  have p0025 := @gOpeldm (.cv x) (.cv z) F
  have p0026 :=
    @gAnim12i (.classMem (synCop (.cv x) (.cv y)) G) (.classMem (.cv x) (synCdm G))
      (.classMem (synCop (.cv x) (.cv z)) F) (.classMem (.cv x) (synCdm F)) p0024 p0025
  have p0027 :=
    @gNsyl (.classEq (synCin (synCdm F) (synCdm G)) (synC0))
      (synWa (.classMem (.cv x) (synCdm G)) (.classMem (.cv x) (synCdm F)))
      (synWa (.classMem (synCop (.cv x) (.cv y)) G) (.classMem (synCop (.cv x) (.cv z)) F))
      p0023 p0026
  have p0028 :=
    @gOrel1
      (synWa (.classMem (synCop (.cv x) (.cv y)) G) (.classMem (synCop (.cv x) (.cv z)) F))
      (synWa (.classMem (synCop (.cv x) (.cv y)) G) (.classMem (synCop (.cv x) (.cv z)) G))
  have p0029 :=
    @gSyl (.classEq (synCin (synCdm F) (synCdm G)) (synC0))
      (.neg (synWa (.classMem (synCop (.cv x) (.cv y)) G)
          (.classMem (synCop (.cv x) (.cv z)) F)))
      (.imp (synWo (synWa (.classMem (synCop (.cv x) (.cv y)) G)
            (.classMem (synCop (.cv x) (.cv z)) F))
          (synWa (.classMem (synCop (.cv x) (.cv y)) G)
            (.classMem (synCop (.cv x) (.cv z)) G)))
        (synWa (.classMem (synCop (.cv x) (.cv y)) G)
          (.classMem (synCop (.cv x) (.cv z)) G)))
      p0027 p0028
  have p0030 :=
    @gOrim12d (.classEq (synCin (synCdm F) (synCdm G)) (synC0))
      (synWo (synWa (.classMem (synCop (.cv x) (.cv y)) F)
          (.classMem (synCop (.cv x) (.cv z)) F))
        (synWa (.classMem (synCop (.cv x) (.cv y)) F)
          (.classMem (synCop (.cv x) (.cv z)) G)))
      (synWa (.classMem (synCop (.cv x) (.cv y)) F) (.classMem (synCop (.cv x) (.cv z)) F))
      (synWo (synWa (.classMem (synCop (.cv x) (.cv y)) G)
          (.classMem (synCop (.cv x) (.cv z)) F))
        (synWa (.classMem (synCop (.cv x) (.cv y)) G)
          (.classMem (synCop (.cv x) (.cv z)) G)))
      (synWa (.classMem (synCop (.cv x) (.cv y)) G) (.classMem (synCop (.cv x) (.cv z)) G))
      p0015 p0029
  have p0031 :=
    @gSyl5bi
      (synWa (.classMem (synCop (.cv x) (.cv y)) (synCun F G))
        (.classMem (synCop (.cv x) (.cv z)) (synCun F G)))
      (synWo (synWo (synWa (.classMem (synCop (.cv x) (.cv y)) F)
            (.classMem (synCop (.cv x) (.cv z)) F))
          (synWa (.classMem (synCop (.cv x) (.cv y)) F)
            (.classMem (synCop (.cv x) (.cv z)) G))) (synWo
          (synWa (.classMem (synCop (.cv x) (.cv y)) G)
            (.classMem (synCop (.cv x) (.cv z)) F))
          (synWa (.classMem (synCop (.cv x) (.cv y)) G)
            (.classMem (synCop (.cv x) (.cv z)) G))))
      (.classEq (synCin (synCdm F) (synCdm G)) (synC0))
      (synWo (synWa (.classMem (synCop (.cv x) (.cv y)) F)
          (.classMem (synCop (.cv x) (.cv z)) F))
        (synWa (.classMem (synCop (.cv x) (.cv y)) G)
          (.classMem (synCop (.cv x) (.cv z)) G)))
      p0004 p0030
  have p0032 :=
    @gDffun4 x y z F dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
      dv_cache_0007 dv_cache_0008
  have p0033 :=
    @gBiimpi (synWfun F)
      (.all x (.all y (.all z (.imp (synWa (.classMem (synCop (.cv x) (.cv y)) F)
                (.classMem (synCop (.cv x) (.cv z)) F)) (.objEq y z)))))
      p0032
  have p0034 :=
    @gN1921bi (synWfun F)
      (.all y (.all z (.imp (synWa (.classMem (synCop (.cv x) (.cv y)) F)
              (.classMem (synCop (.cv x) (.cv z)) F)) (.objEq y z))))
      x p0033
  have p0035 :=
    @gN1921bbi (synWfun F)
      (.imp (synWa (.classMem (synCop (.cv x) (.cv y)) F)
          (.classMem (synCop (.cv x) (.cv z)) F)) (.objEq y z))
      y z p0034
  have p0036 :=
    @gDffun4 x y z G dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0006
      dv_cache_0007 dv_cache_0008
  have p0037 :=
    @gBiimpi (synWfun G)
      (.all x (.all y (.all z (.imp (synWa (.classMem (synCop (.cv x) (.cv y)) G)
                (.classMem (synCop (.cv x) (.cv z)) G)) (.objEq y z)))))
      p0036
  have p0038 :=
    @gN1921bi (synWfun G)
      (.all y (.all z (.imp (synWa (.classMem (synCop (.cv x) (.cv y)) G)
              (.classMem (synCop (.cv x) (.cv z)) G)) (.objEq y z))))
      x p0037
  have p0039 :=
    @gN1921bbi (synWfun G)
      (.imp (synWa (.classMem (synCop (.cv x) (.cv y)) G)
          (.classMem (synCop (.cv x) (.cv z)) G)) (.objEq y z))
      y z p0038
  have p0040 :=
    @gJaao (synWfun F)
      (synWa (.classMem (synCop (.cv x) (.cv y)) F) (.classMem (synCop (.cv x) (.cv z)) F))
      (.objEq y z) (synWfun G)
      (synWa (.classMem (synCop (.cv x) (.cv y)) G) (.classMem (synCop (.cv x) (.cv z)) G))
      p0035 p0039
  have p0041 :=
    @gSylan9r (.classEq (synCin (synCdm F) (synCdm G)) (synC0))
      (synWa (.classMem (synCop (.cv x) (.cv y)) (synCun F G))
        (.classMem (synCop (.cv x) (.cv z)) (synCun F G)))
      (synWo (synWa (.classMem (synCop (.cv x) (.cv y)) F)
          (.classMem (synCop (.cv x) (.cv z)) F))
        (synWa (.classMem (synCop (.cv x) (.cv y)) G)
          (.classMem (synCop (.cv x) (.cv z)) G)))
      (synWa (synWfun F) (synWfun G)) (.objEq y z) p0031 p0040
  have p0042 :=
    @gAlrimiv
      (synWa (synWa (synWfun F) (synWfun G))
        (.classEq (synCin (synCdm F) (synCdm G)) (synC0)))
      (.imp (synWa (.classMem (synCop (.cv x) (.cv y)) (synCun F G))
          (.classMem (synCop (.cv x) (.cv z)) (synCun F G))) (.objEq y z))
      z dv_cache_0012 p0041
  have p0043 :=
    @gAlrimivv
      (synWa (synWa (synWfun F) (synWfun G))
        (.classEq (synCin (synCdm F) (synCdm G)) (synC0)))
      (.all z (.imp (synWa (.classMem (synCop (.cv x) (.cv y)) (synCun F G))
            (.classMem (synCop (.cv x) (.cv z)) (synCun F G))) (.objEq y z)))
      x y dv_cache_0013 dv_cache_0014 p0042
  have p0044 :=
    @gDffun4 x y z (synCun F G) dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0006
      dv_cache_0007 dv_cache_0008
  have p0045 :=
    @gSylibr
      (synWa (synWa (synWfun F) (synWfun G))
        (.classEq (synCin (synCdm F) (synCdm G)) (synC0)))
      (.all x (.all y (.all z (.imp (synWa (.classMem (synCop (.cv x) (.cv y)) (synCun F G))
                (.classMem (synCop (.cv x) (.cv z)) (synCun F G))) (.objEq y z)))))
      (synWfun (synCun F G)) p0043 p0044
  exact p0045

/-- Checked nominal proof certificate identified upstream as `g_funsn`. -/
@[expose]
noncomputable def gFunsn (A : Class) (B : Class) :
    Nominal.NPrf (synWfun (synCsn (synCop A B))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (h))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x := Ne.symm fresh_x_ne_y
  have dv_cache_0001 : x ∉ ((synCsn (synCop A B))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union,
          fresh_x_not_A, fresh_x_not_B, or_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((synCsn (synCop A B))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union,
          fresh_y_not_A, fresh_y_not_B, or_false, not_false_eq_true])
  have dv_cache_0003 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0004 : y ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_B, not_false_eq_true])
  have dv_cache_0005 : y ∉ ((Wff.classEq (.cv x) A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_x, fresh_y_not_A, or_false, not_false_eq_true])
  have p0000 :=
    @gDffun6 x y (synCsn (synCop A B)) dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0001 := @gMoeq y B dv_cache_0004
  have p0002 := @gA1i (synWmo y (.classEq (.cv y) B)) (.classEq (.cv x) A) p0001
  have p0003 := (Nominal.biimpRefl (synWbr (.cv x) (synCsn (synCop A B)) (.cv y)))
  have p0004 := @gVex x
  have p0005 := @gVex y
  have p0006 := @gOpex (.cv x) (.cv y) p0004 p0005
  have p0007 := @gElsnc (synCop (.cv x) (.cv y)) (synCop A B) p0006
  have p0008 := @gOpth (.cv x) (.cv y) A B
  have p0009 :=
    @gBitri (.classMem (synCop (.cv x) (.cv y)) (synCsn (synCop A B)))
      (.classEq (synCop (.cv x) (.cv y)) (synCop A B))
      (synWa (.classEq (.cv x) A) (.classEq (.cv y) B)) p0007 p0008
  have p0010 :=
    @gBitri (synWbr (.cv x) (synCsn (synCop A B)) (.cv y))
      (.classMem (synCop (.cv x) (.cv y)) (synCsn (synCop A B)))
      (synWa (.classEq (.cv x) A) (.classEq (.cv y) B)) p0003 p0009
  have p0011 :=
    @gMobii (synWbr (.cv x) (synCsn (synCop A B)) (.cv y))
      (synWa (.classEq (.cv x) A) (.classEq (.cv y) B)) y p0010
  have p0012 := @gMoanimv (.classEq (.cv x) A) (.classEq (.cv y) B) y dv_cache_0005
  have p0013 :=
    @gBitri (synWmo y (synWbr (.cv x) (synCsn (synCop A B)) (.cv y)))
      (synWmo y (synWa (.classEq (.cv x) A) (.classEq (.cv y) B)))
      (.imp (.classEq (.cv x) A) (synWmo y (.classEq (.cv y) B))) p0011 p0012
  have p0014 :=
    @gMpbir (synWmo y (synWbr (.cv x) (synCsn (synCop A B)) (.cv y)))
      (.imp (.classEq (.cv x) A) (synWmo y (.classEq (.cv y) B))) p0002 p0013
  have p0015 :=
    @gMpgbir (synWfun (synCsn (synCop A B)))
      (synWmo y (synWbr (.cv x) (synCsn (synCop A B)) (.cv y))) x p0000 p0014
  exact p0015

/-- Checked nominal proof certificate identified upstream as `g_fnsn`. -/
@[expose]
noncomputable def gFnsn (A : Class) (B : Class)
    (_hyp_fnsn_1 : Nominal.NPrf (.classMem A (synCvv)))
    (hyp_fnsn_2 : Nominal.NPrf (.classMem B (synCvv))) :
    Nominal.NPrf (synWfn (synCsn (synCop A B)) (synCsn A)) :=
  by
  have p0000 := @gFunsn A B
  have p0001 := @gDmsnop A B hyp_fnsn_2
  have p0002 := (Nominal.biimpRefl (synWfn (synCsn (synCop A B)) (synCsn A)))
  have p0003 :=
    @gMpbir2an (synWfn (synCsn (synCop A B)) (synCsn A))
      (synWfun (synCsn (synCop A B)))
      (.classEq (synCdm (synCsn (synCop A B))) (synCsn A)) p0000 p0001 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_fun0`. -/
@[expose]
noncomputable def gFun0 : Nominal.NPrf (synWfun (synC0)) :=
  by
  have p0000 := @gCo01 (synCcnv (synC0))
  have p0001 := @gN0ss (synCid)
  have p0002 :=
    @gEqsstri (synCcom (synC0) (synCcnv (synC0))) (synC0) (synCid) p0000 p0001
  have p0003 := (Nominal.biimpRefl (synWfun (synC0)))
  have p0004 :=
    @gMpbir (synWfun (synC0))
      (synWss (synCcom (synC0) (synCcnv (synC0))) (synCid)) p0002 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_funcnv2`. -/
@[expose]
noncomputable def gFuncnv2 (x : Var) (y : Var) (A : Class) (dv_A_x : x ∉ A.fv)
    (dv_A_y : y ∉ A.fv) (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (synWb (synWfun (synCcnv A)) (.all y (synWmo x (synWbr (.cv x) A (.cv y))))) :=
  by
  have dv_cache_0001 : y ∉ ((synCcnv A)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, dv_A_y,
          not_false_eq_true])
  have dv_cache_0002 : x ∉ ((synCcnv A)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, dv_A_x,
          not_false_eq_true])
  have dv_cache_0003 : y ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact (show y ≠ x from (by exact Ne.symm dv_x_y))
  have p0000 := @gDffun6 y x (synCcnv A) dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0001 := @gBrcnv (.cv y) (.cv x) A
  have p0002 :=
    @gMobii (synWbr (.cv y) (synCcnv A) (.cv x)) (synWbr (.cv x) A (.cv y)) x p0001
  have p0003 :=
    @gAlbii (synWmo x (synWbr (.cv y) (synCcnv A) (.cv x)))
      (synWmo x (synWbr (.cv x) A (.cv y))) y p0002
  have p0004 :=
    @gBitri (synWfun (synCcnv A))
      (.all y (synWmo x (synWbr (.cv y) (synCcnv A) (.cv x))))
      (.all y (synWmo x (synWbr (.cv x) A (.cv y)))) p0000 p0003
  exact p0004


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk011Compact001Part013`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_fununi`. -/
@[expose]
noncomputable def gFununi (A : Class) (f : Var) (g : Var) (dv_A_f : f ∉ A.fv)
    (dv_A_g : g ∉ A.fv) (dv_f_g : f ≠ g) :
    Nominal.NPrf
      (.imp (synWral f A (synWa (synWfun (.cv f))
            (synWral g A (synWo (synWss (.cv f) (.cv g)) (synWss (.cv g) (.cv f))))))
        (synWfun (synCuni A))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ ({ f } : Finset Var) ∪ ({ g } : Finset Var)
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let z : Var := freshVar proofSupport 2
  let w : Var := freshVar proofSupport 3
  let v : Var := freshVar proofSupport 4
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_x_ne_f : x ≠ f := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_x_ne_g : x ≠ g := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_y_ne_f : y ≠ f := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_y_ne_g : y ≠ g := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_z_ne_f : z ≠ f := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_z_ne_g : z ≠ g := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_w : w ∉ proofSupport :=
    by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_w_not_A : w ∉ A.fv := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_w_ne_f : w ≠ f := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_f_ne_w : f ≠ w := Ne.symm fresh_w_ne_f
  have fresh_w_ne_g : w ≠ g := by
    intro h
    exact fresh_w (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_g_ne_w : g ≠ w := Ne.symm fresh_w_ne_g
  have fresh_v : v ∉ proofSupport :=
    by
    change freshVar proofSupport 4 ∉ proofSupport
    exact freshVar_not_mem proofSupport 4
  have fresh_v_not_A : v ∉ A.fv := by
    intro h
    exact fresh_v (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_v_ne_f : v ≠ f := by
    intro h
    exact
      fresh_v
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_f_ne_v : f ≠ v := Ne.symm fresh_v_ne_f
  have fresh_v_ne_g : v ≠ g := by
    intro h
    exact fresh_v (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_g_ne_v : g ≠ v := Ne.symm fresh_v_ne_g
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_x_ne_z : x ≠ z :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_x_ne_w : x ≠ w :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_w_ne_x : w ≠ x := Ne.symm fresh_x_ne_w
  have fresh_x_ne_v : x ≠ v :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 0) (j := 4) (by decide)
  have fresh_v_ne_x : v ≠ x := Ne.symm fresh_x_ne_v
  have fresh_y_ne_z : y ≠ z :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_y_ne_w : y ≠ w :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_w_ne_y : w ≠ y := Ne.symm fresh_y_ne_w
  have fresh_y_ne_v : y ≠ v :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 1) (j := 4) (by decide)
  have fresh_v_ne_y : v ≠ y := Ne.symm fresh_y_ne_v
  have fresh_z_ne_w : z ≠ w :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_w_ne_z : w ≠ z := Ne.symm fresh_z_ne_w
  have fresh_z_ne_v : z ≠ v :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 2) (j := 4) (by decide)
  have fresh_v_ne_z : v ≠ z := Ne.symm fresh_z_ne_v
  have fresh_w_ne_v : w ≠ v :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 3) (j := 4) (by decide)
  have fresh_v_ne_w : v ≠ w := Ne.symm fresh_w_ne_v
  have dv_cache_0001 : g ∉ ((synWfun (.cv f))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfun,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          (Ne.symm dv_f_g), not_false_eq_true])
  have dv_cache_0002 : x ∉ ((Class.cv v)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_x_ne_v, not_false_eq_true])
  have dv_cache_0003 : y ∉ ((Class.cv v)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_y_ne_v, not_false_eq_true])
  have dv_cache_0004 : z ∉ ((Class.cv v)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_z_ne_v, not_false_eq_true])
  have dv_cache_0005 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0006 : x ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show x ≠ z from (by exact fresh_x_ne_z))
  have dv_cache_0007 : y ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact (show y ≠ z from (by exact fresh_y_ne_z))
  have dv_cache_0008 : x ∉ ((Class.cv w)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_x_ne_w, not_false_eq_true])
  have dv_cache_0009 : y ∉ ((Class.cv w)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_y_ne_w, not_false_eq_true])
  have dv_cache_0010 : z ∉ ((Class.cv w)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_z_ne_w, not_false_eq_true])
  have dv_cache_0011 : f ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_f, not_false_eq_true])
  have dv_cache_0012 : w ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_w_not_A, not_false_eq_true])
  have dv_cache_0013 : v ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_v_not_A, not_false_eq_true])
  have dv_cache_0014 : g ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact
      (by
        have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_g, not_false_eq_true])
  have dv_cache_0015 :
    v ∉
      ((synWa (synWfun (.cv w))
          (synWo (synWss (.cv w) (.cv g)) (synWss (.cv g) (.cv w))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfun,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wo,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, Finset.mem_union,
          Finset.mem_singleton, fresh_v_ne_w, fresh_v_ne_g, or_false, not_false_eq_true])
  have dv_cache_0016 :
    f ∉
      ((synWa (synWfun (.cv w))
          (synWo (synWss (.cv w) (.cv g)) (synWss (.cv g) (.cv w))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfun,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wo,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, Finset.mem_union,
          Finset.mem_singleton, fresh_f_ne_w, dv_f_g, or_false, not_false_eq_true])
  have dv_cache_0017 :
    w ∉
      ((synWa (synWfun (.cv f))
          (synWo (synWss (.cv f) (.cv g)) (synWss (.cv g) (.cv f))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfun,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wo,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, Finset.mem_union,
          Finset.mem_singleton, fresh_w_ne_f, fresh_w_ne_g, or_false, not_false_eq_true])
  have dv_cache_0018 :
    g ∉
      ((synWa (synWfun (.cv w))
          (synWo (synWss (.cv w) (.cv v)) (synWss (.cv v) (.cv w))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact
      (by
        have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfun,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wo,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, Finset.mem_union,
          Finset.mem_singleton, fresh_g_ne_w, fresh_g_ne_v, or_false, not_false_eq_true])
  have dv_cache_0019 : f ≠ g :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018
    exact (show f ≠ g from (by exact dv_f_g))
  have dv_cache_0020 : g ≠ w :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019
    exact (show g ≠ w from (by exact fresh_g_ne_w))
  have dv_cache_0021 :
    v ∉
      ((synWa (synWfun (.cv f))
          (synWo (synWss (.cv w) (.cv f)) (synWss (.cv f) (.cv w))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfun,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wo,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, Finset.mem_union,
          Finset.mem_singleton, fresh_v_ne_f, fresh_v_ne_w, or_false, not_false_eq_true])
  have dv_cache_0022 :
    g ∉
      ((synWa (synWfun (.cv f))
          (synWo (synWss (.cv w) (.cv f)) (synWss (.cv f) (.cv w))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact
      (by
        have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfun,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wo,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, Finset.mem_union,
          Finset.mem_singleton, (Ne.symm dv_f_g), fresh_g_ne_w, or_false,
          not_false_eq_true])
  have dv_cache_0023 :
    f ∉
      ((synWa (synWfun (.cv v))
          (synWo (synWss (.cv w) (.cv v)) (synWss (.cv v) (.cv w))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfun,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wo,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, Finset.mem_union,
          Finset.mem_singleton, fresh_f_ne_v, fresh_f_ne_w, or_false, not_false_eq_true])
  have dv_cache_0024 : g ≠ f :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
    exact (show g ≠ f from (by exact Ne.symm dv_f_g))
  have dv_cache_0025 : f ≠ w :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024
    exact (show f ≠ w from (by exact fresh_f_ne_w))
  have dv_cache_0026 : w ∉ ((synCop (.cv x) (.cv y))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_w_ne_x, fresh_w_ne_y, or_false, not_false_eq_true])
  have dv_cache_0027 : v ∉ ((synCop (.cv x) (.cv z))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_v_ne_x, fresh_v_ne_z, or_false, not_false_eq_true])
  have dv_cache_0028 :
    v ∉
      ((synWa (.classMem (synCop (.cv x) (.cv y)) (.cv w)) (.classMem (.cv w) A))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_v_ne_x, fresh_v_ne_y, fresh_v_ne_w, fresh_v_not_A,
          or_false, not_false_eq_true])
  have dv_cache_0029 :
    w ∉
      ((synWa (.classMem (synCop (.cv x) (.cv z)) (.cv v)) (.classMem (.cv v) A))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_w_ne_x, fresh_w_ne_z, fresh_w_ne_v, fresh_w_not_A,
          or_false, not_false_eq_true])
  have dv_cache_0030 : v ∉ ((Wff.objEq y z)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_insert,
          Finset.mem_singleton, fresh_v_ne_y, fresh_v_ne_z, or_false, not_false_eq_true])
  have dv_cache_0031 : w ≠ v :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030
    exact (show w ≠ v from (by exact fresh_w_ne_v))
  have dv_cache_0032 : w ∉ ((Wff.objEq y z)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_insert,
          Finset.mem_singleton, fresh_w_ne_y, fresh_w_ne_z, or_false, not_false_eq_true])
  have dv_cache_0033 :
    z ∉
      ((synWral f A (synWral g A (synWa (synWfun (.cv f))
              (synWo (synWss (.cv f) (.cv g)) (synWss (.cv g) (.cv f))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfun,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wo,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_z_not_A, fresh_z_ne_f,
          fresh_z_ne_g, or_false, and_false, not_false_eq_true])
  have dv_cache_0034 :
    x ∉
      ((synWral f A (synWral g A (synWa (synWfun (.cv f))
              (synWo (synWss (.cv f) (.cv g)) (synWss (.cv g) (.cv f))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfun,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wo,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_x_not_A, fresh_x_ne_f,
          fresh_x_ne_g, or_false, and_false, not_false_eq_true])
  have dv_cache_0035 :
    y ∉
      ((synWral f A (synWral g A (synWa (synWfun (.cv f))
              (synWo (synWss (.cv f) (.cv g)) (synWss (.cv g) (.cv f))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfun,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wo,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_y_not_A, fresh_y_ne_f,
          fresh_y_ne_g, or_false, and_false, not_false_eq_true])
  have dv_cache_0036 : x ∉ ((synCuni A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, fresh_x_not_A,
          not_false_eq_true])
  have dv_cache_0037 : y ∉ ((synCuni A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, fresh_y_not_A,
          not_false_eq_true])
  have dv_cache_0038 : z ∉ ((synCuni A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, fresh_z_not_A,
          not_false_eq_true])
  have p0000 :=
    @gR1928av (synWfun (.cv f))
      (synWo (synWss (.cv f) (.cv g)) (synWss (.cv g) (.cv f))) g A dv_cache_0001
  have p0001 :=
    @gRalimi
      (synWa (synWfun (.cv f))
        (synWral g A (synWo (synWss (.cv f) (.cv g)) (synWss (.cv g) (.cv f)))))
      (synWral g A (synWa (synWfun (.cv f))
          (synWo (synWss (.cv f) (.cv g)) (synWss (.cv g) (.cv f)))))
      f A p0000
  have p0002 := @gSsel (.cv w) (.cv v) (synCop (.cv x) (.cv y))
  have p0003 :=
    @gAnim1d (synWss (.cv w) (.cv v)) (.classMem (synCop (.cv x) (.cv y)) (.cv w))
      (.classMem (synCop (.cv x) (.cv y)) (.cv v))
      (.classMem (synCop (.cv x) (.cv z)) (.cv v)) p0002
  have p0004 :=
    @gDffun4 x y z (.cv v) dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
  have p0005 :=
    @gSp
      (.imp (synWa (.classMem (synCop (.cv x) (.cv y)) (.cv v))
          (.classMem (synCop (.cv x) (.cv z)) (.cv v))) (.objEq y z))
      z
  have p0006 :=
    @gSps
      (.all z (.imp (synWa (.classMem (synCop (.cv x) (.cv y)) (.cv v))
            (.classMem (synCop (.cv x) (.cv z)) (.cv v))) (.objEq y z)))
      (.imp (synWa (.classMem (synCop (.cv x) (.cv y)) (.cv v))
          (.classMem (synCop (.cv x) (.cv z)) (.cv v))) (.objEq y z))
      y p0005
  have p0007 :=
    @gSps
      (.all y (.all z (.imp (synWa (.classMem (synCop (.cv x) (.cv y)) (.cv v))
              (.classMem (synCop (.cv x) (.cv z)) (.cv v))) (.objEq y z))))
      (.imp (synWa (.classMem (synCop (.cv x) (.cv y)) (.cv v))
          (.classMem (synCop (.cv x) (.cv z)) (.cv v))) (.objEq y z))
      x p0006
  have p0008 :=
    @gSylbi (synWfun (.cv v))
      (.all x (.all y (.all z (.imp (synWa (.classMem (synCop (.cv x) (.cv y)) (.cv v))
                (.classMem (synCop (.cv x) (.cv z)) (.cv v))) (.objEq y z)))))
      (.imp (synWa (.classMem (synCop (.cv x) (.cv y)) (.cv v))
          (.classMem (synCop (.cv x) (.cv z)) (.cv v))) (.objEq y z))
      p0004 p0007
  have p0009 :=
    @gSyl9r (synWss (.cv w) (.cv v))
      (synWa (.classMem (synCop (.cv x) (.cv y)) (.cv w))
        (.classMem (synCop (.cv x) (.cv z)) (.cv v)))
      (synWa (.classMem (synCop (.cv x) (.cv y)) (.cv v))
        (.classMem (synCop (.cv x) (.cv z)) (.cv v)))
      (synWfun (.cv v)) (.objEq y z) p0003 p0008
  have p0010 :=
    @gAdantl (synWfun (.cv v))
      (.imp (synWss (.cv w) (.cv v)) (.imp
          (synWa (.classMem (synCop (.cv x) (.cv y)) (.cv w))
            (.classMem (synCop (.cv x) (.cv z)) (.cv v))) (.objEq y z)))
      (synWfun (.cv w)) p0009
  have p0011 := @gSsel (.cv v) (.cv w) (synCop (.cv x) (.cv z))
  have p0012 :=
    @gAnim2d (synWss (.cv v) (.cv w)) (.classMem (synCop (.cv x) (.cv z)) (.cv v))
      (.classMem (synCop (.cv x) (.cv z)) (.cv w))
      (.classMem (synCop (.cv x) (.cv y)) (.cv w)) p0011
  have p0013 :=
    @gDffun4 x y z (.cv w) dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0005
      dv_cache_0006 dv_cache_0007
  have p0014 :=
    @gSp
      (.imp (synWa (.classMem (synCop (.cv x) (.cv y)) (.cv w))
          (.classMem (synCop (.cv x) (.cv z)) (.cv w))) (.objEq y z))
      z
  have p0015 :=
    @gSps
      (.all z (.imp (synWa (.classMem (synCop (.cv x) (.cv y)) (.cv w))
            (.classMem (synCop (.cv x) (.cv z)) (.cv w))) (.objEq y z)))
      (.imp (synWa (.classMem (synCop (.cv x) (.cv y)) (.cv w))
          (.classMem (synCop (.cv x) (.cv z)) (.cv w))) (.objEq y z))
      y p0014
  have p0016 :=
    @gSps
      (.all y (.all z (.imp (synWa (.classMem (synCop (.cv x) (.cv y)) (.cv w))
              (.classMem (synCop (.cv x) (.cv z)) (.cv w))) (.objEq y z))))
      (.imp (synWa (.classMem (synCop (.cv x) (.cv y)) (.cv w))
          (.classMem (synCop (.cv x) (.cv z)) (.cv w))) (.objEq y z))
      x p0015
  have p0017 :=
    @gSylbi (synWfun (.cv w))
      (.all x (.all y (.all z (.imp (synWa (.classMem (synCop (.cv x) (.cv y)) (.cv w))
                (.classMem (synCop (.cv x) (.cv z)) (.cv w))) (.objEq y z)))))
      (.imp (synWa (.classMem (synCop (.cv x) (.cv y)) (.cv w))
          (.classMem (synCop (.cv x) (.cv z)) (.cv w))) (.objEq y z))
      p0013 p0016
  have p0018 :=
    @gSyl9r (synWss (.cv v) (.cv w))
      (synWa (.classMem (synCop (.cv x) (.cv y)) (.cv w))
        (.classMem (synCop (.cv x) (.cv z)) (.cv v)))
      (synWa (.classMem (synCop (.cv x) (.cv y)) (.cv w))
        (.classMem (synCop (.cv x) (.cv z)) (.cv w)))
      (synWfun (.cv w)) (.objEq y z) p0012 p0017
  have p0019 :=
    @gAdantr (synWfun (.cv w))
      (.imp (synWss (.cv v) (.cv w)) (.imp
          (synWa (.classMem (synCop (.cv x) (.cv y)) (.cv w))
            (.classMem (synCop (.cv x) (.cv z)) (.cv v))) (.objEq y z)))
      (synWfun (.cv v)) p0018
  have p0020 :=
    @gJaod (synWa (synWfun (.cv w)) (synWfun (.cv v))) (synWss (.cv w) (.cv v))
      (.imp (synWa (.classMem (synCop (.cv x) (.cv y)) (.cv w))
          (.classMem (synCop (.cv x) (.cv z)) (.cv v))) (.objEq y z))
      (synWss (.cv v) (.cv w)) p0010 p0019
  have p0021 :=
    @gImp (synWa (synWfun (.cv w)) (synWfun (.cv v)))
      (synWo (synWss (.cv w) (.cv v)) (synWss (.cv v) (.cv w)))
      (.imp (synWa (.classMem (synCop (.cv x) (.cv y)) (.cv w))
          (.classMem (synCop (.cv x) (.cv z)) (.cv v))) (.objEq y z))
      p0020
  have p0022 :=
    @gRalimi
      (synWa (synWa (synWfun (.cv w)) (synWfun (.cv v)))
        (synWo (synWss (.cv w) (.cv v)) (synWss (.cv v) (.cv w))))
      (.imp (synWa (.classMem (synCop (.cv x) (.cv y)) (.cv w))
          (.classMem (synCop (.cv x) (.cv z)) (.cv v))) (.objEq y z))
      v A p0021
  have p0023 :=
    @gRalimi
      (synWral v A (synWa (synWa (synWfun (.cv w)) (synWfun (.cv v)))
          (synWo (synWss (.cv w) (.cv v)) (synWss (.cv v) (.cv w)))))
      (synWral v A (.imp (synWa (.classMem (synCop (.cv x) (.cv y)) (.cv w))
            (.classMem (synCop (.cv x) (.cv z)) (.cv v))) (.objEq y z)))
      w A p0022
  have p0024 := @gFuneq (.cv f) (.cv w)
  have p0025 := @gSseq1 (.cv f) (.cv w) (.cv g)
  have p0026 := @gSseq2 (.cv f) (.cv w) (.cv g)
  have p0027_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq f w) (synWb (synWss (.cv f) (.cv g)) (synWss (.cv w) (.cv g)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWss synCin synCcompl synCnin synWnan synWa
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0025
  have p0027_e01_recanon :
    Nominal.NPrf
      (.imp (.objEq f w) (synWb (synWss (.cv g) (.cv f)) (synWss (.cv g) (.cv w)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWss synCin synCcompl synCnin synWnan synWa
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0026
  have p0027 :=
    @gOrbi12d (.objEq f w) (synWss (.cv f) (.cv g)) (synWss (.cv w) (.cv g))
      (synWss (.cv g) (.cv f)) (synWss (.cv g) (.cv w)) p0027_e00_recanon
      p0027_e01_recanon
  have p0028_e00_recanon :
    Nominal.NPrf (.imp (.objEq f w) (synWb (synWfun (.cv f)) (synWfun (.cv w)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWfun synWss synCin synCcompl synCnin synWnan synWa
          synCcom synCopab synWex synCcnv synCid
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0024
  have p0028 :=
    @gAnbi12d (.objEq f w) (synWfun (.cv f)) (synWfun (.cv w))
      (synWo (synWss (.cv f) (.cv g)) (synWss (.cv g) (.cv f)))
      (synWo (synWss (.cv w) (.cv g)) (synWss (.cv g) (.cv w))) p0028_e00_recanon p0027
  have p0029 := @gSseq2 (.cv g) (.cv v) (.cv w)
  have p0030 := @gSseq1 (.cv g) (.cv v) (.cv w)
  have p0031_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq g v) (synWb (synWss (.cv w) (.cv g)) (synWss (.cv w) (.cv v)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWss synCin synCcompl synCnin synWnan synWa
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0029
  have p0031_e01_recanon :
    Nominal.NPrf
      (.imp (.objEq g v) (synWb (synWss (.cv g) (.cv w)) (synWss (.cv v) (.cv w)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWss synCin synCcompl synCnin synWnan synWa
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0030
  have p0031 :=
    @gOrbi12d (.objEq g v) (synWss (.cv w) (.cv g)) (synWss (.cv w) (.cv v))
      (synWss (.cv g) (.cv w)) (synWss (.cv v) (.cv w)) p0031_e00_recanon
      p0031_e01_recanon
  have p0032 :=
    @gAnbi2d (.objEq g v) (synWo (synWss (.cv w) (.cv g)) (synWss (.cv g) (.cv w)))
      (synWo (synWss (.cv w) (.cv v)) (synWss (.cv v) (.cv w))) (synWfun (.cv w))
      p0031
  have p0033 :=
    @gCbvral2v
      (synWa (synWfun (.cv f)) (synWo (synWss (.cv f) (.cv g)) (synWss (.cv g) (.cv f))))
      (synWa (synWfun (.cv w)) (synWo (synWss (.cv w) (.cv v)) (synWss (.cv v) (.cv w))))
      (synWa (synWfun (.cv w)) (synWo (synWss (.cv w) (.cv g)) (synWss (.cv g) (.cv w))))
      f g w v A A dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0011 dv_cache_0014
      dv_cache_0012 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019
      dv_cache_0020 p0028 p0032
  have p0034 :=
    @gRalcom
      (synWa (synWfun (.cv f)) (synWo (synWss (.cv f) (.cv g)) (synWss (.cv g) (.cv f))))
      f g A A dv_cache_0014 dv_cache_0011 dv_cache_0019
  have p0035 := @gOrcom (synWss (.cv f) (.cv g)) (synWss (.cv g) (.cv f))
  have p0036 := @gSseq1 (.cv g) (.cv w) (.cv f)
  have p0037 := @gSseq2 (.cv g) (.cv w) (.cv f)
  have p0038_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq g w) (synWb (synWss (.cv g) (.cv f)) (synWss (.cv w) (.cv f)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWss synCin synCcompl synCnin synWnan synWa
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0036
  have p0038_e01_recanon :
    Nominal.NPrf
      (.imp (.objEq g w) (synWb (synWss (.cv f) (.cv g)) (synWss (.cv f) (.cv w)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWss synCin synCcompl synCnin synWnan synWa
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0037
  have p0038 :=
    @gOrbi12d (.objEq g w) (synWss (.cv g) (.cv f)) (synWss (.cv w) (.cv f))
      (synWss (.cv f) (.cv g)) (synWss (.cv f) (.cv w)) p0038_e00_recanon
      p0038_e01_recanon
  have p0039 :=
    @gSyl5bb (synWo (synWss (.cv f) (.cv g)) (synWss (.cv g) (.cv f)))
      (synWo (synWss (.cv g) (.cv f)) (synWss (.cv f) (.cv g))) (.objEq g w)
      (synWo (synWss (.cv w) (.cv f)) (synWss (.cv f) (.cv w))) p0035 p0038
  have p0040 :=
    @gAnbi2d (.objEq g w) (synWo (synWss (.cv f) (.cv g)) (synWss (.cv g) (.cv f)))
      (synWo (synWss (.cv w) (.cv f)) (synWss (.cv f) (.cv w))) (synWfun (.cv f))
      p0039
  have p0041 := @gFuneq (.cv f) (.cv v)
  have p0042 := @gSseq2 (.cv f) (.cv v) (.cv w)
  have p0043 := @gSseq1 (.cv f) (.cv v) (.cv w)
  have p0044_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq f v) (synWb (synWss (.cv w) (.cv f)) (synWss (.cv w) (.cv v)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWss synCin synCcompl synCnin synWnan synWa
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0042
  have p0044_e01_recanon :
    Nominal.NPrf
      (.imp (.objEq f v) (synWb (synWss (.cv f) (.cv w)) (synWss (.cv v) (.cv w)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWss synCin synCcompl synCnin synWnan synWa
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0043
  have p0044 :=
    @gOrbi12d (.objEq f v) (synWss (.cv w) (.cv f)) (synWss (.cv w) (.cv v))
      (synWss (.cv f) (.cv w)) (synWss (.cv v) (.cv w)) p0044_e00_recanon
      p0044_e01_recanon
  have p0045_e00_recanon :
    Nominal.NPrf (.imp (.objEq f v) (synWb (synWfun (.cv f)) (synWfun (.cv v)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWfun synWss synCin synCcompl synCnin synWnan synWa
          synCcom synCopab synWex synCcnv synCid
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0041
  have p0045 :=
    @gAnbi12d (.objEq f v) (synWfun (.cv f)) (synWfun (.cv v))
      (synWo (synWss (.cv w) (.cv f)) (synWss (.cv f) (.cv w)))
      (synWo (synWss (.cv w) (.cv v)) (synWss (.cv v) (.cv w))) p0045_e00_recanon p0044
  have p0046 :=
    @gCbvral2v
      (synWa (synWfun (.cv f)) (synWo (synWss (.cv f) (.cv g)) (synWss (.cv g) (.cv f))))
      (synWa (synWfun (.cv v)) (synWo (synWss (.cv w) (.cv v)) (synWss (.cv v) (.cv w))))
      (synWa (synWfun (.cv f)) (synWo (synWss (.cv w) (.cv f)) (synWss (.cv f) (.cv w))))
      g f w v A A dv_cache_0014 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0011
      dv_cache_0012 dv_cache_0021 dv_cache_0022 dv_cache_0017 dv_cache_0023 dv_cache_0024
      dv_cache_0025 p0040 p0045
  have p0047 :=
    @gBitri
      (synWral f A (synWral g A (synWa (synWfun (.cv f))
            (synWo (synWss (.cv f) (.cv g)) (synWss (.cv g) (.cv f))))))
      (synWral g A (synWral f A (synWa (synWfun (.cv f))
            (synWo (synWss (.cv f) (.cv g)) (synWss (.cv g) (.cv f))))))
      (synWral w A (synWral v A (synWa (synWfun (.cv v))
            (synWo (synWss (.cv w) (.cv v)) (synWss (.cv v) (.cv w))))))
      p0034 p0046
  have p0048 :=
    @gAnbi12i
      (synWral f A (synWral g A (synWa (synWfun (.cv f))
            (synWo (synWss (.cv f) (.cv g)) (synWss (.cv g) (.cv f))))))
      (synWral w A (synWral v A (synWa (synWfun (.cv w))
            (synWo (synWss (.cv w) (.cv v)) (synWss (.cv v) (.cv w))))))
      (synWral f A (synWral g A (synWa (synWfun (.cv f))
            (synWo (synWss (.cv f) (.cv g)) (synWss (.cv g) (.cv f))))))
      (synWral w A (synWral v A (synWa (synWfun (.cv v))
            (synWo (synWss (.cv w) (.cv v)) (synWss (.cv v) (.cv w))))))
      p0033 p0047
  have p0049 :=
    @gAnidm
      (synWral f A (synWral g A (synWa (synWfun (.cv f))
            (synWo (synWss (.cv f) (.cv g)) (synWss (.cv g) (.cv f))))))
  have p0050 :=
    @gAnandir (synWfun (.cv w)) (synWfun (.cv v))
      (synWo (synWss (.cv w) (.cv v)) (synWss (.cv v) (.cv w)))
  have p0051 :=
    @gN2ralbii
      (synWa (synWa (synWfun (.cv w)) (synWfun (.cv v)))
        (synWo (synWss (.cv w) (.cv v)) (synWss (.cv v) (.cv w))))
      (synWa (synWa (synWfun (.cv w))
          (synWo (synWss (.cv w) (.cv v)) (synWss (.cv v) (.cv w))))
        (synWa (synWfun (.cv v))
          (synWo (synWss (.cv w) (.cv v)) (synWss (.cv v) (.cv w)))))
      w v A A p0050
  have p0052 :=
    @g_r19_26_2
      (synWa (synWfun (.cv w)) (synWo (synWss (.cv w) (.cv v)) (synWss (.cv v) (.cv w))))
      (synWa (synWfun (.cv v)) (synWo (synWss (.cv w) (.cv v)) (synWss (.cv v) (.cv w))))
      w v A A
  have p0053 :=
    @gBitr2i
      (synWral w A (synWral v A (synWa (synWa (synWfun (.cv w)) (synWfun (.cv v)))
            (synWo (synWss (.cv w) (.cv v)) (synWss (.cv v) (.cv w))))))
      (synWral w A (synWral v A (synWa (synWa (synWfun (.cv w))
              (synWo (synWss (.cv w) (.cv v)) (synWss (.cv v) (.cv w))))
            (synWa (synWfun (.cv v))
              (synWo (synWss (.cv w) (.cv v)) (synWss (.cv v) (.cv w)))))))
      (synWa (synWral w A (synWral v A (synWa (synWfun (.cv w))
              (synWo (synWss (.cv w) (.cv v)) (synWss (.cv v) (.cv w)))))) (synWral w A
          (synWral v A (synWa (synWfun (.cv v))
              (synWo (synWss (.cv w) (.cv v)) (synWss (.cv v) (.cv w)))))))
      p0051 p0052
  have p0054 :=
    @gN3bitr3i
      (synWa (synWral f A (synWral g A (synWa (synWfun (.cv f))
              (synWo (synWss (.cv f) (.cv g)) (synWss (.cv g) (.cv f)))))) (synWral f A
          (synWral g A (synWa (synWfun (.cv f))
              (synWo (synWss (.cv f) (.cv g)) (synWss (.cv g) (.cv f)))))))
      (synWa (synWral w A (synWral v A (synWa (synWfun (.cv w))
              (synWo (synWss (.cv w) (.cv v)) (synWss (.cv v) (.cv w)))))) (synWral w A
          (synWral v A (synWa (synWfun (.cv v))
              (synWo (synWss (.cv w) (.cv v)) (synWss (.cv v) (.cv w)))))))
      (synWral f A (synWral g A (synWa (synWfun (.cv f))
            (synWo (synWss (.cv f) (.cv g)) (synWss (.cv g) (.cv f))))))
      (synWral w A (synWral v A (synWa (synWa (synWfun (.cv w)) (synWfun (.cv v)))
            (synWo (synWss (.cv w) (.cv v)) (synWss (.cv v) (.cv w))))))
      p0048 p0049 p0053
  have p0055 := @gEluni w (synCop (.cv x) (.cv y)) A dv_cache_0026 dv_cache_0012
  have p0056 := @gEluni v (synCop (.cv x) (.cv z)) A dv_cache_0027 dv_cache_0013
  have p0057 :=
    @gAnbi12i (.classMem (synCop (.cv x) (.cv y)) (synCuni A))
      (synWex w (synWa (.classMem (synCop (.cv x) (.cv y)) (.cv w)) (.classMem (.cv w) A)))
      (.classMem (synCop (.cv x) (.cv z)) (synCuni A))
      (synWex v (synWa (.classMem (synCop (.cv x) (.cv z)) (.cv v)) (.classMem (.cv v) A)))
      p0055 p0056
  have p0058 :=
    @gEeanv (synWa (.classMem (synCop (.cv x) (.cv y)) (.cv w)) (.classMem (.cv w) A))
      (synWa (.classMem (synCop (.cv x) (.cv z)) (.cv v)) (.classMem (.cv v) A)) w v
      dv_cache_0028 dv_cache_0029
  have p0059 :=
    @gAn4 (.classMem (synCop (.cv x) (.cv y)) (.cv w)) (.classMem (.cv w) A)
      (.classMem (synCop (.cv x) (.cv z)) (.cv v)) (.classMem (.cv v) A)
  have p0060 :=
    @gAncom
      (synWa (.classMem (synCop (.cv x) (.cv y)) (.cv w))
        (.classMem (synCop (.cv x) (.cv z)) (.cv v)))
      (synWa (.classMem (.cv w) A) (.classMem (.cv v) A))
  have p0061 :=
    @gBitri
      (synWa (synWa (.classMem (synCop (.cv x) (.cv y)) (.cv w)) (.classMem (.cv w) A))
        (synWa (.classMem (synCop (.cv x) (.cv z)) (.cv v)) (.classMem (.cv v) A)))
      (synWa (synWa (.classMem (synCop (.cv x) (.cv y)) (.cv w))
          (.classMem (synCop (.cv x) (.cv z)) (.cv v)))
        (synWa (.classMem (.cv w) A) (.classMem (.cv v) A)))
      (synWa (synWa (.classMem (.cv w) A) (.classMem (.cv v) A))
        (synWa (.classMem (synCop (.cv x) (.cv y)) (.cv w))
          (.classMem (synCop (.cv x) (.cv z)) (.cv v))))
      p0059 p0060
  have p0062 :=
    @gN2exbii
      (synWa (synWa (.classMem (synCop (.cv x) (.cv y)) (.cv w)) (.classMem (.cv w) A))
        (synWa (.classMem (synCop (.cv x) (.cv z)) (.cv v)) (.classMem (.cv v) A)))
      (synWa (synWa (.classMem (.cv w) A) (.classMem (.cv v) A))
        (synWa (.classMem (synCop (.cv x) (.cv y)) (.cv w))
          (.classMem (synCop (.cv x) (.cv z)) (.cv v))))
      w v p0061
  have p0063 :=
    @gN3bitr2i
      (synWa (.classMem (synCop (.cv x) (.cv y)) (synCuni A))
        (.classMem (synCop (.cv x) (.cv z)) (synCuni A)))
      (synWa (synWex w
          (synWa (.classMem (synCop (.cv x) (.cv y)) (.cv w)) (.classMem (.cv w) A)))
        (synWex v
          (synWa (.classMem (synCop (.cv x) (.cv z)) (.cv v)) (.classMem (.cv v) A))))
      (synWex w (synWex v (synWa
            (synWa (.classMem (synCop (.cv x) (.cv y)) (.cv w)) (.classMem (.cv w) A))
            (synWa (.classMem (synCop (.cv x) (.cv z)) (.cv v)) (.classMem (.cv v) A)))))
      (synWex w (synWex v (synWa (synWa (.classMem (.cv w) A) (.classMem (.cv v) A))
            (synWa (.classMem (synCop (.cv x) (.cv y)) (.cv w))
              (.classMem (synCop (.cv x) (.cv z)) (.cv v))))))
      p0057 p0058 p0062
  have p0064 :=
    @gImbi1i
      (synWa (.classMem (synCop (.cv x) (.cv y)) (synCuni A))
        (.classMem (synCop (.cv x) (.cv z)) (synCuni A)))
      (synWex w (synWex v (synWa (synWa (.classMem (.cv w) A) (.classMem (.cv v) A))
            (synWa (.classMem (synCop (.cv x) (.cv y)) (.cv w))
              (.classMem (synCop (.cv x) (.cv z)) (.cv v))))))
      (.objEq y z) p0063
  have p0065 :=
    @gN1923v
      (synWa (synWa (.classMem (.cv w) A) (.classMem (.cv v) A))
        (synWa (.classMem (synCop (.cv x) (.cv y)) (.cv w))
          (.classMem (synCop (.cv x) (.cv z)) (.cv v))))
      (.objEq y z) v dv_cache_0030
  have p0066 :=
    @gAlbii
      (.all v (.imp (synWa (synWa (.classMem (.cv w) A) (.classMem (.cv v) A))
            (synWa (.classMem (synCop (.cv x) (.cv y)) (.cv w))
              (.classMem (synCop (.cv x) (.cv z)) (.cv v)))) (.objEq y z)))
      (.imp (synWex v (synWa (synWa (.classMem (.cv w) A) (.classMem (.cv v) A))
            (synWa (.classMem (synCop (.cv x) (.cv y)) (.cv w))
              (.classMem (synCop (.cv x) (.cv z)) (.cv v))))) (.objEq y z))
      w p0065
  have p0067 :=
    @gImpexp (synWa (.classMem (.cv w) A) (.classMem (.cv v) A))
      (synWa (.classMem (synCop (.cv x) (.cv y)) (.cv w))
        (.classMem (synCop (.cv x) (.cv z)) (.cv v)))
      (.objEq y z)
  have p0068 :=
    @gN2albii
      (.imp (synWa (synWa (.classMem (.cv w) A) (.classMem (.cv v) A))
          (synWa (.classMem (synCop (.cv x) (.cv y)) (.cv w))
            (.classMem (synCop (.cv x) (.cv z)) (.cv v)))) (.objEq y z))
      (.imp (synWa (.classMem (.cv w) A) (.classMem (.cv v) A)) (.imp
          (synWa (.classMem (synCop (.cv x) (.cv y)) (.cv w))
            (.classMem (synCop (.cv x) (.cv z)) (.cv v))) (.objEq y z)))
      w v p0067
  have p0069 :=
    @gR2al
      (.imp (synWa (.classMem (synCop (.cv x) (.cv y)) (.cv w))
          (.classMem (synCop (.cv x) (.cv z)) (.cv v))) (.objEq y z))
      w v A A dv_cache_0013 dv_cache_0031
  have p0070 :=
    @gBitr4i
      (.all w (.all v (.imp (synWa (synWa (.classMem (.cv w) A) (.classMem (.cv v) A))
              (synWa (.classMem (synCop (.cv x) (.cv y)) (.cv w))
                (.classMem (synCop (.cv x) (.cv z)) (.cv v)))) (.objEq y z))))
      (.all w (.all v (.imp (synWa (.classMem (.cv w) A) (.classMem (.cv v) A)) (.imp
              (synWa (.classMem (synCop (.cv x) (.cv y)) (.cv w))
                (.classMem (synCop (.cv x) (.cv z)) (.cv v))) (.objEq y z)))))
      (synWral w A (synWral v A (.imp (synWa (.classMem (synCop (.cv x) (.cv y)) (.cv w))
              (.classMem (synCop (.cv x) (.cv z)) (.cv v))) (.objEq y z))))
      p0068 p0069
  have p0071 :=
    @gN1923v
      (synWex v (synWa (synWa (.classMem (.cv w) A) (.classMem (.cv v) A))
          (synWa (.classMem (synCop (.cv x) (.cv y)) (.cv w))
            (.classMem (synCop (.cv x) (.cv z)) (.cv v)))))
      (.objEq y z) w dv_cache_0032
  have p0072 :=
    @gN3bitr3ri
      (.all w (.all v (.imp (synWa (synWa (.classMem (.cv w) A) (.classMem (.cv v) A))
              (synWa (.classMem (synCop (.cv x) (.cv y)) (.cv w))
                (.classMem (synCop (.cv x) (.cv z)) (.cv v)))) (.objEq y z))))
      (.all w (.imp (synWex v (synWa (synWa (.classMem (.cv w) A) (.classMem (.cv v) A))
              (synWa (.classMem (synCop (.cv x) (.cv y)) (.cv w))
                (.classMem (synCop (.cv x) (.cv z)) (.cv v))))) (.objEq y z)))
      (synWral w A (synWral v A (.imp (synWa (.classMem (synCop (.cv x) (.cv y)) (.cv w))
              (.classMem (synCop (.cv x) (.cv z)) (.cv v))) (.objEq y z))))
      (.imp (synWex w (synWex v (synWa (synWa (.classMem (.cv w) A) (.classMem (.cv v) A))
              (synWa (.classMem (synCop (.cv x) (.cv y)) (.cv w))
                (.classMem (synCop (.cv x) (.cv z)) (.cv v)))))) (.objEq y z))
      p0066 p0070 p0071
  have p0073 :=
    @gBitri
      (.imp (synWa (.classMem (synCop (.cv x) (.cv y)) (synCuni A))
          (.classMem (synCop (.cv x) (.cv z)) (synCuni A))) (.objEq y z))
      (.imp (synWex w (synWex v (synWa (synWa (.classMem (.cv w) A) (.classMem (.cv v) A))
              (synWa (.classMem (synCop (.cv x) (.cv y)) (.cv w))
                (.classMem (synCop (.cv x) (.cv z)) (.cv v)))))) (.objEq y z))
      (synWral w A (synWral v A (.imp (synWa (.classMem (synCop (.cv x) (.cv y)) (.cv w))
              (.classMem (synCop (.cv x) (.cv z)) (.cv v))) (.objEq y z))))
      p0064 p0072
  have p0074 :=
    @gN3imtr4i
      (synWral w A (synWral v A (synWa (synWa (synWfun (.cv w)) (synWfun (.cv v)))
            (synWo (synWss (.cv w) (.cv v)) (synWss (.cv v) (.cv w))))))
      (synWral w A (synWral v A (.imp (synWa (.classMem (synCop (.cv x) (.cv y)) (.cv w))
              (.classMem (synCop (.cv x) (.cv z)) (.cv v))) (.objEq y z))))
      (synWral f A (synWral g A (synWa (synWfun (.cv f))
            (synWo (synWss (.cv f) (.cv g)) (synWss (.cv g) (.cv f))))))
      (.imp (synWa (.classMem (synCop (.cv x) (.cv y)) (synCuni A))
          (.classMem (synCop (.cv x) (.cv z)) (synCuni A))) (.objEq y z))
      p0023 p0054 p0073
  have p0075 :=
    @gAlrimiv
      (synWral f A (synWral g A (synWa (synWfun (.cv f))
            (synWo (synWss (.cv f) (.cv g)) (synWss (.cv g) (.cv f))))))
      (.imp (synWa (.classMem (synCop (.cv x) (.cv y)) (synCuni A))
          (.classMem (synCop (.cv x) (.cv z)) (synCuni A))) (.objEq y z))
      z dv_cache_0033 p0074
  have p0076 :=
    @gAlrimivv
      (synWral f A (synWral g A (synWa (synWfun (.cv f))
            (synWo (synWss (.cv f) (.cv g)) (synWss (.cv g) (.cv f))))))
      (.all z (.imp (synWa (.classMem (synCop (.cv x) (.cv y)) (synCuni A))
            (.classMem (synCop (.cv x) (.cv z)) (synCuni A))) (.objEq y z)))
      x y dv_cache_0034 dv_cache_0035 p0075
  have p0077 :=
    @gSyl
      (synWral f A (synWa (synWfun (.cv f))
          (synWral g A (synWo (synWss (.cv f) (.cv g)) (synWss (.cv g) (.cv f))))))
      (synWral f A (synWral g A (synWa (synWfun (.cv f))
            (synWo (synWss (.cv f) (.cv g)) (synWss (.cv g) (.cv f))))))
      (.all x (.all y (.all z (.imp (synWa (.classMem (synCop (.cv x) (.cv y)) (synCuni A))
                (.classMem (synCop (.cv x) (.cv z)) (synCuni A))) (.objEq y z)))))
      p0001 p0076
  have p0078 :=
    @gDffun4 x y z (synCuni A) dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0005
      dv_cache_0006 dv_cache_0007
  have p0079 :=
    @gSylibr
      (synWral f A (synWa (synWfun (.cv f))
          (synWral g A (synWo (synWss (.cv f) (.cv g)) (synWss (.cv g) (.cv f))))))
      (.all x (.all y (.all z (.imp (synWa (.classMem (synCop (.cv x) (.cv y)) (synCuni A))
                (.classMem (synCop (.cv x) (.cv z)) (synCuni A))) (.objEq y z)))))
      (synWfun (synCuni A)) p0077 p0078
  exact p0079


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk011Compact001Part014`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_funcnvuni`. -/
@[expose]
noncomputable def gFuncnvuni (A : Class) (f : Var) (g : Var) (dv_A_f : f ∉ A.fv)
    (dv_A_g : g ∉ A.fv) (dv_f_g : f ≠ g) :
    Nominal.NPrf
      (.imp (synWral f A (synWa (synWfun (synCcnv (.cv f)))
            (synWral g A (synWo (synWss (.cv f) (.cv g)) (synWss (.cv g) (.cv f))))))
        (synWfun (synCcnv (synCuni A)))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ ({ f } : Finset Var) ∪ ({ g } : Finset Var)
  let y : Var := freshVar proofSupport 0
  let x : Var := freshVar proofSupport 1
  let z : Var := freshVar proofSupport 2
  let w : Var := freshVar proofSupport 3
  let v : Var := freshVar proofSupport 4
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_x_ne_g : x ≠ g := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_g_ne_x : g ≠ x := Ne.symm fresh_x_ne_g
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_z_ne_f : z ≠ f := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_z_ne_g : z ≠ g := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_w : w ∉ proofSupport :=
    by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_w_not_A : w ∉ A.fv := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_w_ne_g : w ≠ g := by
    intro h
    exact fresh_w (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_v : v ∉ proofSupport :=
    by
    change freshVar proofSupport 4 ∉ proofSupport
    exact freshVar_not_mem proofSupport 4
  have fresh_v_not_A : v ∉ A.fv := by
    intro h
    exact fresh_v (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_v_ne_f : v ≠ f := by
    intro h
    exact
      fresh_v
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_f_ne_v : f ≠ v := Ne.symm fresh_v_ne_f
  have fresh_v_ne_g : v ≠ g := by
    intro h
    exact fresh_v (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_g_ne_v : g ≠ v := Ne.symm fresh_v_ne_g
  have fresh_y_ne_x : y ≠ x :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_x_ne_y : x ≠ y := Ne.symm fresh_y_ne_x
  have fresh_y_ne_z : y ≠ z :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_z_ne_y : z ≠ y := Ne.symm fresh_y_ne_z
  have fresh_y_ne_w : y ≠ w :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_w_ne_y : w ≠ y := Ne.symm fresh_y_ne_w
  have fresh_x_ne_z : x ≠ z :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_z_ne_x : z ≠ x := Ne.symm fresh_x_ne_z
  have fresh_x_ne_w : x ≠ w :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_w_ne_x : w ≠ x := Ne.symm fresh_x_ne_w
  have fresh_x_ne_v : x ≠ v :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 1) (j := 4) (by decide)
  have fresh_v_ne_x : v ≠ x := Ne.symm fresh_x_ne_v
  have fresh_z_ne_w : z ≠ w :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_w_ne_z : w ≠ z := Ne.symm fresh_z_ne_w
  have fresh_z_ne_v : z ≠ v :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 2) (j := 4) (by decide)
  have fresh_v_ne_z : v ≠ z := Ne.symm fresh_z_ne_v
  have fresh_w_ne_v : w ≠ v :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 3) (j := 4) (by decide)
  have fresh_v_ne_w : v ≠ w := Ne.symm fresh_w_ne_v
  have dv_cache_0001 : x ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_A, not_false_eq_true])
  have dv_cache_0002 : v ∉ (A).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_v_not_A, not_false_eq_true])
  have dv_cache_0003 : v ∉ ((Wff.classEq (.cv z) (synCcnv (.cv x)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, Finset.mem_union,
          Finset.mem_singleton, fresh_v_ne_z, fresh_v_ne_x, or_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ ((Wff.classEq (.cv z) (synCcnv (.cv v)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_z, fresh_x_ne_v, or_false, not_false_eq_true])
  have dv_cache_0005 : g ∉ ((Wff.classEq (.cv f) (.cv v))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, (Ne.symm dv_f_g), fresh_g_ne_v, or_false,
          not_false_eq_true])
  have dv_cache_0006 : f ∉ ((Class.cv v)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_f_ne_v, not_false_eq_true])
  have dv_cache_0007 : f ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_f, not_false_eq_true])
  have dv_cache_0008 :
    f ∉
      ((synWa (synWfun (synCcnv (.cv v))) (synWral g A
            (synWo (synWss (.cv v) (.cv g)) (synWss (.cv g) (.cv v)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wo,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_f_ne_v, dv_A_f, dv_f_g, or_false,
          and_false, not_false_eq_true])
  have dv_cache_0009 : g ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_g_ne_x, not_false_eq_true])
  have dv_cache_0010 : g ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_g, not_false_eq_true])
  have dv_cache_0011 :
    g ∉ ((synWo (synWss (.cv v) (.cv x)) (synWss (.cv x) (.cv v)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wo,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_g_ne_v, fresh_g_ne_x, or_false, not_false_eq_true])
  have dv_cache_0012 :
    x ∉
      ((Wff.imp (.classEq (.cv z) (synCcnv (.cv v)))
          (synWo (synWss (.cv z) (.cv w)) (synWss (.cv w) (.cv z))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wo,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_z, fresh_x_ne_v, fresh_x_ne_w, or_false,
          not_false_eq_true])
  have dv_cache_0013 :
    x ∉
      ((synWral g A (synWo (synWss (.cv v) (.cv g)) (synWss (.cv g) (.cv v))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wo,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_x_not_A, fresh_x_ne_v, fresh_x_ne_g, or_false,
          and_false, not_false_eq_true])
  have dv_cache_0014 :
    w ∉
      ((synWral g A (synWo (synWss (.cv v) (.cv g)) (synWss (.cv g) (.cv v))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wo,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_w_not_A, fresh_w_ne_v, fresh_w_ne_g, or_false,
          and_false, not_false_eq_true])
  have dv_cache_0015 : w ∉ ((Wff.classEq (.cv z) (synCcnv (.cv v)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, Finset.mem_union,
          Finset.mem_singleton, fresh_w_ne_z, fresh_w_ne_v, or_false, not_false_eq_true])
  have dv_cache_0016 :
    v ∉
      ((synWa (synWfun (.cv z)) (.all w
            (.imp (synWrex x A (.classEq (.cv w) (synCcnv (.cv x))))
              (synWo (synWss (.cv z) (.cv w)) (synWss (.cv w) (.cv z))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfun,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_wff_all,
          NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wo,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_v_ne_z, fresh_v_not_A,
          fresh_v_ne_w, fresh_v_ne_x, or_false, and_false, not_false_eq_true])
  have dv_cache_0017 :
    v ∉
      ((synWral f A (synWa (synWfun (synCcnv (.cv f))) (synWral g A
              (synWo (synWss (.cv f) (.cv g)) (synWss (.cv g) (.cv f))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wo,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_v_not_A, fresh_v_ne_f,
          fresh_v_ne_g, or_false, and_false, not_false_eq_true])
  have dv_cache_0018 :
    z ∉
      ((synWral f A (synWa (synWfun (synCcnv (.cv f))) (synWral g A
              (synWo (synWss (.cv f) (.cv g)) (synWss (.cv g) (.cv f))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wo,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_z_not_A, fresh_z_ne_f,
          fresh_z_ne_g, or_false, and_false, not_false_eq_true])
  have dv_cache_0019 : x ∉ ((Wff.classEq (.cv y) (.cv z))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_y, fresh_x_ne_z, or_false, not_false_eq_true])
  have dv_cache_0020 : y ∉ ((Class.cv z)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_y_ne_z, not_false_eq_true])
  have dv_cache_0021 : y ∉ ((synWrex x A (.classEq (.cv z) (synCcnv (.cv x))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_y_not_A, fresh_y_ne_z,
          fresh_y_ne_x, or_false, and_false, not_false_eq_true])
  have dv_cache_0022 : x ∉ ((Wff.classEq (.cv y) (.cv w))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_y, fresh_x_ne_w, or_false, not_false_eq_true])
  have dv_cache_0023 : y ∉ ((synWrex x A (.classEq (.cv w) (synCcnv (.cv x))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_y_not_A, fresh_y_ne_w,
          fresh_y_ne_x, or_false, and_false, not_false_eq_true])
  have dv_cache_0024 : w ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
    exact (show w ≠ y from (by exact fresh_w_ne_y))
  have dv_cache_0025 :
    z ∉ ((Class.cab y (synWrex x A (.classEq (.cv y) (synCcnv (.cv x)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cab,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_z_not_A, fresh_z_ne_y,
          fresh_z_ne_x, or_false, and_false, not_false_eq_true])
  have dv_cache_0026 :
    w ∉ ((Class.cab y (synWrex x A (.classEq (.cv y) (synCcnv (.cv x)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cab,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_w_not_A, fresh_w_ne_y,
          fresh_w_ne_x, or_false, and_false, not_false_eq_true])
  have dv_cache_0027 : z ≠ w :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026
    exact (show z ≠ w from (by exact fresh_z_ne_w))
  have dv_cache_0028 : y ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_A, not_false_eq_true])
  have dv_cache_0029 : y ∉ ((synCcnv (.cv x))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_y_ne_x,
          not_false_eq_true])
  have dv_cache_0030 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have p0000 := @gCnveq (.cv x) (.cv v)
  have p0001 :=
    @gEqeq2d (.classEq (.cv x) (.cv v)) (synCcnv (.cv x)) (synCcnv (.cv v)) (.cv z)
      p0000
  have p0002_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq x v) (synWb (.classEq (.cv z) (synCcnv (.cv x)))
          (.classEq (.cv z) (synCcnv (.cv v))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCcnv synCopab synWex synWbr synCop synCun synCnin synWnan
          synWa synCcompl synWrex synCphi
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0001
  have p0002 :=
    @gCbvrexv (.classEq (.cv z) (synCcnv (.cv x))) (.classEq (.cv z) (synCcnv (.cv v)))
      x v A dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 p0002_e00_recanon
  have p0003 := @gCnveq (.cv f) (.cv v)
  have p0004 :=
    @gFuneqd (.classEq (.cv f) (.cv v)) (synCcnv (.cv f)) (synCcnv (.cv v)) p0003
  have p0005 := @gSseq1 (.cv f) (.cv v) (.cv g)
  have p0006 := @gSseq2 (.cv f) (.cv v) (.cv g)
  have p0007 :=
    @gOrbi12d (.classEq (.cv f) (.cv v)) (synWss (.cv f) (.cv g))
      (synWss (.cv v) (.cv g)) (synWss (.cv g) (.cv f)) (synWss (.cv g) (.cv v)) p0005
      p0006
  have p0008 :=
    @gRalbidv (.classEq (.cv f) (.cv v))
      (synWo (synWss (.cv f) (.cv g)) (synWss (.cv g) (.cv f)))
      (synWo (synWss (.cv v) (.cv g)) (synWss (.cv g) (.cv v))) g A dv_cache_0005 p0007
  have p0009 :=
    @gAnbi12d (.classEq (.cv f) (.cv v)) (synWfun (synCcnv (.cv f)))
      (synWfun (synCcnv (.cv v)))
      (synWral g A (synWo (synWss (.cv f) (.cv g)) (synWss (.cv g) (.cv f))))
      (synWral g A (synWo (synWss (.cv v) (.cv g)) (synWss (.cv g) (.cv v)))) p0004
      p0008
  have p0010 :=
    @gRspcv
      (synWa (synWfun (synCcnv (.cv f)))
        (synWral g A (synWo (synWss (.cv f) (.cv g)) (synWss (.cv g) (.cv f)))))
      (synWa (synWfun (synCcnv (.cv v)))
        (synWral g A (synWo (synWss (.cv v) (.cv g)) (synWss (.cv g) (.cv v)))))
      f (.cv v) A dv_cache_0006 dv_cache_0007 dv_cache_0008 p0009
  have p0011 := @gFuneq (.cv z) (synCcnv (.cv v))
  have p0012 :=
    @gBiimprcd (.classEq (.cv z) (synCcnv (.cv v))) (synWfun (.cv z))
      (synWfun (synCcnv (.cv v))) p0011
  have p0013 := @gSseq2 (.cv g) (.cv x) (.cv v)
  have p0014 := @gSseq1 (.cv g) (.cv x) (.cv v)
  have p0015 :=
    @gOrbi12d (.classEq (.cv g) (.cv x)) (synWss (.cv v) (.cv g))
      (synWss (.cv v) (.cv x)) (synWss (.cv g) (.cv v)) (synWss (.cv x) (.cv v)) p0013
      p0014
  have p0016 :=
    @gRspcv (synWo (synWss (.cv v) (.cv g)) (synWss (.cv g) (.cv v)))
      (synWo (synWss (.cv v) (.cv x)) (synWss (.cv x) (.cv v))) g (.cv x) A
      dv_cache_0009 dv_cache_0010 dv_cache_0011 p0015
  have p0017 := @gCnvss (.cv v) (.cv x)
  have p0018 := @gCnvss (.cv x) (.cv v)
  have p0019 :=
    @gOrim12i (synWss (.cv v) (.cv x)) (synWss (synCcnv (.cv v)) (synCcnv (.cv x)))
      (synWss (.cv x) (.cv v)) (synWss (synCcnv (.cv x)) (synCcnv (.cv v))) p0017
      p0018
  have p0020 := @gSseq12 (.cv z) (synCcnv (.cv v)) (.cv w) (synCcnv (.cv x))
  have p0021 :=
    @gAncoms (.classEq (.cv z) (synCcnv (.cv v))) (.classEq (.cv w) (synCcnv (.cv x)))
      (synWb (synWss (.cv z) (.cv w)) (synWss (synCcnv (.cv v)) (synCcnv (.cv x))))
      p0020
  have p0022 := @gSseq12 (.cv w) (synCcnv (.cv x)) (.cv z) (synCcnv (.cv v))
  have p0023 :=
    @gOrbi12d
      (synWa (.classEq (.cv w) (synCcnv (.cv x))) (.classEq (.cv z) (synCcnv (.cv v))))
      (synWss (.cv z) (.cv w)) (synWss (synCcnv (.cv v)) (synCcnv (.cv x)))
      (synWss (.cv w) (.cv z)) (synWss (synCcnv (.cv x)) (synCcnv (.cv v))) p0021
      p0022
  have p0024 :=
    @gSyl5ibrcom (synWo (synWss (.cv v) (.cv x)) (synWss (.cv x) (.cv v)))
      (synWo (synWss (.cv z) (.cv w)) (synWss (.cv w) (.cv z)))
      (synWa (.classEq (.cv w) (synCcnv (.cv x))) (.classEq (.cv z) (synCcnv (.cv v))))
      (synWo (synWss (synCcnv (.cv v)) (synCcnv (.cv x)))
        (synWss (synCcnv (.cv x)) (synCcnv (.cv v))))
      p0019 p0023
  have p0025 :=
    @gExp3a (synWo (synWss (.cv v) (.cv x)) (synWss (.cv x) (.cv v)))
      (.classEq (.cv w) (synCcnv (.cv x))) (.classEq (.cv z) (synCcnv (.cv v)))
      (synWo (synWss (.cv z) (.cv w)) (synWss (.cv w) (.cv z))) p0024
  have p0026 :=
    @gSyl6com (.classMem (.cv x) A)
      (synWral g A (synWo (synWss (.cv v) (.cv g)) (synWss (.cv g) (.cv v))))
      (synWo (synWss (.cv v) (.cv x)) (synWss (.cv x) (.cv v)))
      (.imp (.classEq (.cv w) (synCcnv (.cv x))) (.imp (.classEq (.cv z) (synCcnv (.cv v)))
          (synWo (synWss (.cv z) (.cv w)) (synWss (.cv w) (.cv z)))))
      p0016 p0025
  have p0027 :=
    @gRexlimdv
      (synWral g A (synWo (synWss (.cv v) (.cv g)) (synWss (.cv g) (.cv v))))
      (.classEq (.cv w) (synCcnv (.cv x)))
      (.imp (.classEq (.cv z) (synCcnv (.cv v)))
        (synWo (synWss (.cv z) (.cv w)) (synWss (.cv w) (.cv z))))
      x A dv_cache_0012 dv_cache_0013 p0026
  have p0028 :=
    @gCom23 (synWral g A (synWo (synWss (.cv v) (.cv g)) (synWss (.cv g) (.cv v))))
      (synWrex x A (.classEq (.cv w) (synCcnv (.cv x))))
      (.classEq (.cv z) (synCcnv (.cv v)))
      (synWo (synWss (.cv z) (.cv w)) (synWss (.cv w) (.cv z))) p0027
  have p0029 :=
    @gAlrimdv (synWral g A (synWo (synWss (.cv v) (.cv g)) (synWss (.cv g) (.cv v))))
      (.classEq (.cv z) (synCcnv (.cv v)))
      (.imp (synWrex x A (.classEq (.cv w) (synCcnv (.cv x))))
        (synWo (synWss (.cv z) (.cv w)) (synWss (.cv w) (.cv z))))
      w dv_cache_0014 dv_cache_0015 p0028
  have p0030 :=
    @gAnim12ii (synWfun (synCcnv (.cv v))) (.classEq (.cv z) (synCcnv (.cv v)))
      (synWfun (.cv z))
      (synWral g A (synWo (synWss (.cv v) (.cv g)) (synWss (.cv g) (.cv v))))
      (.all w (.imp (synWrex x A (.classEq (.cv w) (synCcnv (.cv x))))
          (synWo (synWss (.cv z) (.cv w)) (synWss (.cv w) (.cv z)))))
      p0012 p0029
  have p0031 :=
    @gSyl6com (.classMem (.cv v) A)
      (synWral f A (synWa (synWfun (synCcnv (.cv f)))
          (synWral g A (synWo (synWss (.cv f) (.cv g)) (synWss (.cv g) (.cv f))))))
      (synWa (synWfun (synCcnv (.cv v)))
        (synWral g A (synWo (synWss (.cv v) (.cv g)) (synWss (.cv g) (.cv v)))))
      (.imp (.classEq (.cv z) (synCcnv (.cv v))) (synWa (synWfun (.cv z)) (.all w
            (.imp (synWrex x A (.classEq (.cv w) (synCcnv (.cv x))))
              (synWo (synWss (.cv z) (.cv w)) (synWss (.cv w) (.cv z)))))))
      p0010 p0030
  have p0032 :=
    @gRexlimdv
      (synWral f A (synWa (synWfun (synCcnv (.cv f)))
          (synWral g A (synWo (synWss (.cv f) (.cv g)) (synWss (.cv g) (.cv f))))))
      (.classEq (.cv z) (synCcnv (.cv v)))
      (synWa (synWfun (.cv z)) (.all w
          (.imp (synWrex x A (.classEq (.cv w) (synCcnv (.cv x))))
            (synWo (synWss (.cv z) (.cv w)) (synWss (.cv w) (.cv z))))))
      v A dv_cache_0016 dv_cache_0017 p0031
  have p0033 :=
    @gSyl5bi (synWrex x A (.classEq (.cv z) (synCcnv (.cv x))))
      (synWrex v A (.classEq (.cv z) (synCcnv (.cv v))))
      (synWral f A (synWa (synWfun (synCcnv (.cv f)))
          (synWral g A (synWo (synWss (.cv f) (.cv g)) (synWss (.cv g) (.cv f))))))
      (synWa (synWfun (.cv z)) (.all w
          (.imp (synWrex x A (.classEq (.cv w) (synCcnv (.cv x))))
            (synWo (synWss (.cv z) (.cv w)) (synWss (.cv w) (.cv z))))))
      p0002 p0032
  have p0034 :=
    @gAlrimiv
      (synWral f A (synWa (synWfun (synCcnv (.cv f)))
          (synWral g A (synWo (synWss (.cv f) (.cv g)) (synWss (.cv g) (.cv f))))))
      (.imp (synWrex x A (.classEq (.cv z) (synCcnv (.cv x)))) (synWa (synWfun (.cv z))
          (.all w (.imp (synWrex x A (.classEq (.cv w) (synCcnv (.cv x))))
              (synWo (synWss (.cv z) (.cv w)) (synWss (.cv w) (.cv z)))))))
      z dv_cache_0018 p0033
  have p0035 :=
    (Nominal.biimpRefl (synWral z (.cab y (synWrex x A (.classEq (.cv y) (synCcnv (.cv x)))))
        (synWa (synWfun (.cv z))
          (synWral w (.cab y (synWrex x A (.classEq (.cv y) (synCcnv (.cv x)))))
            (synWo (synWss (.cv z) (.cv w)) (synWss (.cv w) (.cv z)))))))
  have p0036 := @gVex z
  have p0037 := @gEqeq1 (.cv y) (.cv z) (synCcnv (.cv x))
  have p0038 :=
    @gRexbidv (.classEq (.cv y) (.cv z)) (.classEq (.cv y) (synCcnv (.cv x)))
      (.classEq (.cv z) (synCcnv (.cv x))) x A dv_cache_0019 p0037
  have p0039 :=
    @gElab (synWrex x A (.classEq (.cv y) (synCcnv (.cv x))))
      (synWrex x A (.classEq (.cv z) (synCcnv (.cv x)))) y (.cv z) dv_cache_0020
      dv_cache_0021 p0036 p0038
  have p0040 := @gEqeq1 (.cv y) (.cv w) (synCcnv (.cv x))
  have p0041 :=
    @gRexbidv (.classEq (.cv y) (.cv w)) (.classEq (.cv y) (synCcnv (.cv x)))
      (.classEq (.cv w) (synCcnv (.cv x))) x A dv_cache_0022 p0040
  have p0042_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq y w) (synWb (synWrex x A (.classEq (.cv y) (synCcnv (.cv x))))
          (synWrex x A (.classEq (.cv w) (synCcnv (.cv x)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [synWb, synWrex, synWex, synWa, synCcnv, synCopab, synWbr,
          synCop, synCun, synCnin, synWnan, synCcompl]
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0041
  have p0042 :=
    @gRalab (synWrex x A (.classEq (.cv y) (synCcnv (.cv x))))
      (synWrex x A (.classEq (.cv w) (synCcnv (.cv x))))
      (synWo (synWss (.cv z) (.cv w)) (synWss (.cv w) (.cv z))) w y dv_cache_0023
      dv_cache_0024 p0042_e00_recanon
  have p0043 :=
    @gAnbi2i
      (synWral w (.cab y (synWrex x A (.classEq (.cv y) (synCcnv (.cv x)))))
        (synWo (synWss (.cv z) (.cv w)) (synWss (.cv w) (.cv z))))
      (.all w (.imp (synWrex x A (.classEq (.cv w) (synCcnv (.cv x))))
          (synWo (synWss (.cv z) (.cv w)) (synWss (.cv w) (.cv z)))))
      (synWfun (.cv z)) p0042
  have p0044 :=
    @gImbi12i
      (.classMem (.cv z) (.cab y (synWrex x A (.classEq (.cv y) (synCcnv (.cv x))))))
      (synWrex x A (.classEq (.cv z) (synCcnv (.cv x))))
      (synWa (synWfun (.cv z))
        (synWral w (.cab y (synWrex x A (.classEq (.cv y) (synCcnv (.cv x)))))
          (synWo (synWss (.cv z) (.cv w)) (synWss (.cv w) (.cv z)))))
      (synWa (synWfun (.cv z)) (.all w
          (.imp (synWrex x A (.classEq (.cv w) (synCcnv (.cv x))))
            (synWo (synWss (.cv z) (.cv w)) (synWss (.cv w) (.cv z))))))
      p0039 p0043
  have p0045 :=
    @gAlbii
      (.imp (.classMem (.cv z) (.cab y (synWrex x A (.classEq (.cv y) (synCcnv (.cv x))))))
        (synWa (synWfun (.cv z))
          (synWral w (.cab y (synWrex x A (.classEq (.cv y) (synCcnv (.cv x)))))
            (synWo (synWss (.cv z) (.cv w)) (synWss (.cv w) (.cv z))))))
      (.imp (synWrex x A (.classEq (.cv z) (synCcnv (.cv x)))) (synWa (synWfun (.cv z))
          (.all w (.imp (synWrex x A (.classEq (.cv w) (synCcnv (.cv x))))
              (synWo (synWss (.cv z) (.cv w)) (synWss (.cv w) (.cv z)))))))
      z p0044
  have p0046 :=
    @gBitr2i
      (synWral z (.cab y (synWrex x A (.classEq (.cv y) (synCcnv (.cv x)))))
        (synWa (synWfun (.cv z))
          (synWral w (.cab y (synWrex x A (.classEq (.cv y) (synCcnv (.cv x)))))
            (synWo (synWss (.cv z) (.cv w)) (synWss (.cv w) (.cv z))))))
      (.all z (.imp (.classMem (.cv z)
            (.cab y (synWrex x A (.classEq (.cv y) (synCcnv (.cv x))))))
          (synWa (synWfun (.cv z))
            (synWral w (.cab y (synWrex x A (.classEq (.cv y) (synCcnv (.cv x)))))
              (synWo (synWss (.cv z) (.cv w)) (synWss (.cv w) (.cv z)))))))
      (.all z (.imp (synWrex x A (.classEq (.cv z) (synCcnv (.cv x))))
          (synWa (synWfun (.cv z)) (.all w
              (.imp (synWrex x A (.classEq (.cv w) (synCcnv (.cv x))))
                (synWo (synWss (.cv z) (.cv w)) (synWss (.cv w) (.cv z))))))))
      p0035 p0045
  have p0047 :=
    @gSylib
      (synWral f A (synWa (synWfun (synCcnv (.cv f)))
          (synWral g A (synWo (synWss (.cv f) (.cv g)) (synWss (.cv g) (.cv f))))))
      (.all z (.imp (synWrex x A (.classEq (.cv z) (synCcnv (.cv x))))
          (synWa (synWfun (.cv z)) (.all w
              (.imp (synWrex x A (.classEq (.cv w) (synCcnv (.cv x))))
                (synWo (synWss (.cv z) (.cv w)) (synWss (.cv w) (.cv z))))))))
      (synWral z (.cab y (synWrex x A (.classEq (.cv y) (synCcnv (.cv x)))))
        (synWa (synWfun (.cv z))
          (synWral w (.cab y (synWrex x A (.classEq (.cv y) (synCcnv (.cv x)))))
            (synWo (synWss (.cv z) (.cv w)) (synWss (.cv w) (.cv z))))))
      p0034 p0046
  have p0048 :=
    @gFununi (.cab y (synWrex x A (.classEq (.cv y) (synCcnv (.cv x))))) z w
      dv_cache_0025 dv_cache_0026 dv_cache_0027
  have p0049 :=
    @gSyl
      (synWral f A (synWa (synWfun (synCcnv (.cv f)))
          (synWral g A (synWo (synWss (.cv f) (.cv g)) (synWss (.cv g) (.cv f))))))
      (synWral z (.cab y (synWrex x A (.classEq (.cv y) (synCcnv (.cv x)))))
        (synWa (synWfun (.cv z))
          (synWral w (.cab y (synWrex x A (.classEq (.cv y) (synCcnv (.cv x)))))
            (synWo (synWss (.cv z) (.cv w)) (synWss (.cv w) (.cv z))))))
      (synWfun (synCuni (.cab y (synWrex x A (.classEq (.cv y) (synCcnv (.cv x)))))))
      p0047 p0048
  have p0050 := @gCnvuni x A dv_cache_0001
  have p0051 := @gVex x
  have p0052 := @gCnvex (.cv x) p0051
  have p0053 :=
    @gDfiun2 x y A (synCcnv (.cv x)) dv_cache_0028 dv_cache_0029 dv_cache_0030 p0052
  have p0054 :=
    @gEqtri (synCcnv (synCuni A)) (synCiun x A (synCcnv (.cv x)))
      (synCuni (.cab y (synWrex x A (.classEq (.cv y) (synCcnv (.cv x)))))) p0050 p0053
  have p0055 :=
    @gFuneqi (synCcnv (synCuni A))
      (synCuni (.cab y (synWrex x A (.classEq (.cv y) (synCcnv (.cv x)))))) p0054
  have p0056 :=
    @gSylibr
      (synWral f A (synWa (synWfun (synCcnv (.cv f)))
          (synWral g A (synWo (synWss (.cv f) (.cv g)) (synWss (.cv g) (.cv f))))))
      (synWfun (synCuni (.cab y (synWrex x A (.classEq (.cv y) (synCcnv (.cv x)))))))
      (synWfun (synCcnv (synCuni A))) p0049 p0055
  exact p0056

/-- Checked nominal proof certificate identified upstream as `g_fun11uni`. -/
@[expose]
noncomputable def gFun11uni (A : Class) (f : Var) (g : Var) (dv_A_f : f ∉ A.fv)
    (dv_A_g : g ∉ A.fv) (dv_f_g : f ≠ g) :
    Nominal.NPrf
      (.imp (synWral f A (synWa (synWa (synWfun (.cv f)) (synWfun (synCcnv (.cv f))))
            (synWral g A (synWo (synWss (.cv f) (.cv g)) (synWss (.cv g) (.cv f))))))
        (synWa (synWfun (synCuni A)) (synWfun (synCcnv (synCuni A))))) :=
  by
  have dv_cache_0001 : f ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_f, not_false_eq_true])
  have dv_cache_0002 : g ∉ (A).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_g, not_false_eq_true])
  have dv_cache_0003 : f ≠ g :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact (show f ≠ g from (by exact dv_f_g))
  have p0000 := @gSimpl (synWfun (.cv f)) (synWfun (synCcnv (.cv f)))
  have p0001 :=
    @gAnim1i (synWa (synWfun (.cv f)) (synWfun (synCcnv (.cv f)))) (synWfun (.cv f))
      (synWral g A (synWo (synWss (.cv f) (.cv g)) (synWss (.cv g) (.cv f)))) p0000
  have p0002 :=
    @gRalimi
      (synWa (synWa (synWfun (.cv f)) (synWfun (synCcnv (.cv f))))
        (synWral g A (synWo (synWss (.cv f) (.cv g)) (synWss (.cv g) (.cv f)))))
      (synWa (synWfun (.cv f))
        (synWral g A (synWo (synWss (.cv f) (.cv g)) (synWss (.cv g) (.cv f)))))
      f A p0001
  have p0003 := @gFununi A f g dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0004 :=
    @gSyl
      (synWral f A (synWa (synWa (synWfun (.cv f)) (synWfun (synCcnv (.cv f))))
          (synWral g A (synWo (synWss (.cv f) (.cv g)) (synWss (.cv g) (.cv f))))))
      (synWral f A (synWa (synWfun (.cv f))
          (synWral g A (synWo (synWss (.cv f) (.cv g)) (synWss (.cv g) (.cv f))))))
      (synWfun (synCuni A)) p0002 p0003
  have p0005 := @gSimpr (synWfun (.cv f)) (synWfun (synCcnv (.cv f)))
  have p0006 :=
    @gAnim1i (synWa (synWfun (.cv f)) (synWfun (synCcnv (.cv f))))
      (synWfun (synCcnv (.cv f)))
      (synWral g A (synWo (synWss (.cv f) (.cv g)) (synWss (.cv g) (.cv f)))) p0005
  have p0007 :=
    @gRalimi
      (synWa (synWa (synWfun (.cv f)) (synWfun (synCcnv (.cv f))))
        (synWral g A (synWo (synWss (.cv f) (.cv g)) (synWss (.cv g) (.cv f)))))
      (synWa (synWfun (synCcnv (.cv f)))
        (synWral g A (synWo (synWss (.cv f) (.cv g)) (synWss (.cv g) (.cv f)))))
      f A p0006
  have p0008 := @gFuncnvuni A f g dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0009 :=
    @gSyl
      (synWral f A (synWa (synWa (synWfun (.cv f)) (synWfun (synCcnv (.cv f))))
          (synWral g A (synWo (synWss (.cv f) (.cv g)) (synWss (.cv g) (.cv f))))))
      (synWral f A (synWa (synWfun (synCcnv (.cv f)))
          (synWral g A (synWo (synWss (.cv f) (.cv g)) (synWss (.cv g) (.cv f))))))
      (synWfun (synCcnv (synCuni A))) p0007 p0008
  have p0010 :=
    @gJca
      (synWral f A (synWa (synWa (synWfun (.cv f)) (synWfun (synCcnv (.cv f))))
          (synWral g A (synWo (synWss (.cv f) (.cv g)) (synWss (.cv g) (.cv f))))))
      (synWfun (synCuni A)) (synWfun (synCcnv (synCuni A))) p0004 p0009
  exact p0010

/-- Checked nominal proof certificate identified upstream as `g_funres11`. -/
@[expose]
noncomputable def gFunres11 (A : Class) (F : Class) :
    Nominal.NPrf (.imp (synWfun (synCcnv F)) (synWfun (synCcnv (synCres F A)))) :=
  by
  have p0000 := @gResss F A
  have p0001 := @gCnvss (synCres F A) F
  have p0002 := @gFunss (synCcnv (synCres F A)) (synCcnv F)
  have p0003 :=
    @gMp2b (synWss (synCres F A) F) (synWss (synCcnv (synCres F A)) (synCcnv F))
      (.imp (synWfun (synCcnv F)) (synWfun (synCcnv (synCres F A)))) p0000 p0001
      p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_funcnvres`. -/
@[expose]
noncomputable def gFuncnvres (A : Class) (F : Class) :
    Nominal.NPrf
      (.imp (synWfun (synCcnv F))
        (.classEq (synCcnv (synCres F A)) (synCres (synCcnv F) (synCima F A)))) :=
  by
  have p0000 := @gDfima3 F A
  have p0001 := @gDfrn4 (synCres F A)
  have p0002 :=
    @gEqtri (synCima F A) (synCrn (synCres F A)) (synCdm (synCcnv (synCres F A)))
      p0000 p0001
  have p0003 :=
    @gReseq2i (synCima F A) (synCdm (synCcnv (synCres F A))) (synCcnv F) p0002
  have p0004 := @gResss F A
  have p0005 := @gCnvss (synCres F A) F
  have p0006 := Nominal.mp p0004 p0005
  have p0007 := @gFunssres (synCcnv F) (synCcnv (synCres F A))
  have p0008 :=
    @gMpan2 (synWfun (synCcnv F)) (synWss (synCcnv (synCres F A)) (synCcnv F))
      (.classEq (synCres (synCcnv F) (synCdm (synCcnv (synCres F A))))
        (synCcnv (synCres F A)))
      p0006 p0007
  have p0009 :=
    @gSyl5req (synWfun (synCcnv F)) (synCres (synCcnv F) (synCima F A))
      (synCres (synCcnv F) (synCdm (synCcnv (synCres F A))))
      (synCcnv (synCres F A)) p0003 p0008
  exact p0009

/-- Checked nominal proof certificate identified upstream as `g_cnvresid`. -/
@[expose]
noncomputable def gCnvresid (A : Class) :
    Nominal.NPrf (.classEq (synCcnv (synCres (synCid) A)) (synCres (synCid) A)) :=
  by
  have p0000 := @gCnvi
  have p0001 := @gEqcomi (synCcnv (synCid)) (synCid) p0000
  have p0002 := @gFuni
  have p0003 := @gFuneq (synCid) (synCcnv (synCid))
  have p0004 :=
    @gMpbii (.classEq (synCid) (synCcnv (synCid))) (synWfun (synCid))
      (synWfun (synCcnv (synCid))) p0002 p0003
  have p0005 := Nominal.mp p0001 p0004
  have p0006 := @gFuncnvres A (synCid)
  have p0008 := @gImai A
  have p0009 :=
    @gReseq12i (synCcnv (synCid)) (synCid) (synCima (synCid) A) A p0000 p0008
  have p0010 :=
    @gSyl6eq (synWfun (synCcnv (synCid))) (synCcnv (synCres (synCid) A))
      (synCres (synCcnv (synCid)) (synCima (synCid) A)) (synCres (synCid) A) p0006
      p0009
  have p0011 := Nominal.mp p0005 p0010
  exact p0011

/-- Checked nominal proof certificate identified upstream as `g_funcnvres2`. -/
@[expose]
noncomputable def gFuncnvres2 (A : Class) (F : Class) :
    Nominal.NPrf
      (.imp (synWfun F) (.classEq (synCcnv (synCres (synCcnv F) A))
          (synCres F (synCima (synCcnv F) A)))) :=
  by
  have p0000 := @gCnvcnv F
  have p0001 := @gFuneqi (synCcnv (synCcnv F)) F p0000
  have p0002 := @gFuncnvres A (synCcnv F)
  have p0003 :=
    @gSylbir (synWfun F) (synWfun (synCcnv (synCcnv F)))
      (.classEq (synCcnv (synCres (synCcnv F) A))
        (synCres (synCcnv (synCcnv F)) (synCima (synCcnv F) A)))
      p0001 p0002
  have p0004 := @gReseq1i (synCcnv (synCcnv F)) F (synCima (synCcnv F) A) p0000
  have p0005 :=
    @gSyl6eq (synWfun F) (synCcnv (synCres (synCcnv F) A))
      (synCres (synCcnv (synCcnv F)) (synCima (synCcnv F) A))
      (synCres F (synCima (synCcnv F) A)) p0003 p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_funimacnv`. -/
@[expose]
noncomputable def gFunimacnv (A : Class) (F : Class) :
    Nominal.NPrf
      (.imp (synWfun F)
        (.classEq (synCima F (synCima (synCcnv F) A)) (synCin A (synCrn F)))) :=
  by
  have p0000 := @gFuncnvres2 A F
  have p0001 :=
    @gRneqd (synWfun F) (synCcnv (synCres (synCcnv F) A))
      (synCres F (synCima (synCcnv F) A)) p0000
  have p0002 := @gDfima3 F (synCima (synCcnv F) A)
  have p0003 :=
    @gSyl6reqr (synWfun F) (synCrn (synCcnv (synCres (synCcnv F) A)))
      (synCrn (synCres F (synCima (synCcnv F) A)))
      (synCima F (synCima (synCcnv F) A)) p0001 p0002
  have p0004 := @gDfrn4 F
  have p0005 := @gIneq2i (synCrn F) (synCdm (synCcnv F)) A p0004
  have p0006 := @gDmres (synCcnv F) A
  have p0007 := (Nominal.classEqRefl (synCdm (synCres (synCcnv F) A)))
  have p0008 :=
    @gN3eqtr2ri (synCin A (synCrn F)) (synCin A (synCdm (synCcnv F)))
      (synCdm (synCres (synCcnv F) A)) (synCrn (synCcnv (synCres (synCcnv F) A)))
      p0005 p0006 p0007
  have p0009 :=
    @gSyl6eq (synWfun F) (synCima F (synCima (synCcnv F) A))
      (synCrn (synCcnv (synCres (synCcnv F) A))) (synCin A (synCrn F)) p0003 p0008
  exact p0009

/-- Checked nominal proof certificate identified upstream as `g_funimass2`. -/
@[expose]
noncomputable def gFunimass2 (A : Class) (B : Class) (F : Class) :
    Nominal.NPrf
      (.imp (synWa (synWfun F) (synWss A (synCima (synCcnv F) B)))
        (synWss (synCima F A) B)) :=
  by
  have p0000 := @gImass2 A (synCima (synCcnv F) B) F
  have p0001 := @gFunimacnv B F
  have p0002 :=
    @gSseq2d (synWfun F) (synCima F (synCima (synCcnv F) B)) (synCin B (synCrn F))
      (synCima F A) p0001
  have p0003 := @gInss1 B (synCrn F)
  have p0004 := @gSstr2 (synCima F A) (synCin B (synCrn F)) B
  have p0005 :=
    @gMpi (synWss (synCima F A) (synCin B (synCrn F)))
      (synWss (synCin B (synCrn F)) B) (synWss (synCima F A) B) p0003 p0004
  have p0006 :=
    @gSyl6bi (synWfun F) (synWss (synCima F A) (synCima F (synCima (synCcnv F) B)))
      (synWss (synCima F A) (synCin B (synCrn F))) (synWss (synCima F A) B) p0002
      p0005
  have p0007 :=
    @gImp (synWfun F) (synWss (synCima F A) (synCima F (synCima (synCcnv F) B)))
      (synWss (synCima F A) B) p0006
  have p0008 :=
    @gSylan2 (synWss A (synCima (synCcnv F) B)) (synWfun F)
      (synWss (synCima F A) (synCima F (synCima (synCcnv F) B)))
      (synWss (synCima F A) B) p0000 p0007
  exact p0008


end NFChoice.DirectNominalPrf.WPPReplay

end
