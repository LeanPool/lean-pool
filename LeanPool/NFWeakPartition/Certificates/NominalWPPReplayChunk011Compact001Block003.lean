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

@[expose]
noncomputable def g_dfxp2 (A : Class) (B : Class) :
    Nominal.NPrf
      (.classEq (syn_cxp A B) (syn_cin (syn_cima (syn_ccnv (syn_c1st)) A)
          (syn_cima (syn_ccnv (syn_c2nd)) B))) :=
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
  have dv_cache_0001 : v ∉ ((Wff.classEq (.cv x) (syn_cop (.cv y) (.cv w)))).fv := by
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
  have dv_cache_0002 : w ∉ ((Wff.classEq (.cv x) (syn_cop (.cv v) (.cv z)))).fv :=
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
      ((syn_wa (.classEq (.cv x) (syn_cop (.cv y) (.cv z)))
          (.classEq (.cv x) (syn_cop (.cv y) (.cv z))))).fv :=
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
      ((syn_wa (.classEq (.cv x) (syn_cop (.cv y) (.cv z)))
          (.classEq (.cv x) (syn_cop (.cv y) (.cv z))))).fv :=
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
  have dv_cache_0010 : w ∉ ((Wff.classEq (.cv x) (syn_cop (.cv y) (.cv z)))).fv :=
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
  have dv_cache_0011 : v ∉ ((Wff.classEq (.cv x) (syn_cop (.cv y) (.cv z)))).fv :=
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
  have dv_cache_0021 : y ∉ ((syn_ccnv (syn_c1st))).fv :=
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
  have dv_cache_0022 : z ∉ ((syn_ccnv (syn_c2nd))).fv :=
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
  have dv_cache_0023 : z ∉ ((syn_wbr (.cv y) (syn_ccnv (syn_c1st)) (.cv x))).fv :=
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
  have dv_cache_0024 : y ∉ ((syn_wbr (.cv z) (syn_ccnv (syn_c2nd)) (.cv x))).fv :=
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
  have dv_cache_0025 : x ∉ ((syn_cxp A B)).fv :=
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
      ((syn_cin (syn_cima (syn_ccnv (syn_c1st)) A) (syn_cima (syn_ccnv (syn_c2nd)) B))).fv :=
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
    @g_eeanv (.classEq (.cv x) (syn_cop (.cv y) (.cv w)))
      (.classEq (.cv x) (syn_cop (.cv v) (.cv z))) w v dv_cache_0001 dv_cache_0002
  have p0001 := @g_vex z
  have p0002 := @g_vex y
  have p0003 := @g_opeq2 (.cv w) (.cv z) (.cv y)
  have p0004_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq w z) (.classEq (syn_cop (.cv y) (.cv w)) (syn_cop (.cv y) (.cv z)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex syn_wex
          syn_cphi
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0003
  have p0004 :=
    @g_eqeq2d (.objEq w z) (syn_cop (.cv y) (.cv w)) (syn_cop (.cv y) (.cv z)) (.cv x)
      p0004_e00_recanon
  have p0005 := @g_opeq1 (.cv v) (.cv y) (.cv z)
  have p0006_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq v y) (.classEq (syn_cop (.cv v) (.cv z)) (syn_cop (.cv y) (.cv z)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex syn_wex
          syn_cphi
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0005
  have p0006 :=
    @g_eqeq2d (.objEq v y) (syn_cop (.cv v) (.cv z)) (syn_cop (.cv y) (.cv z)) (.cv x)
      p0006_e00_recanon
  have p0007 :=
    @g_bi2anan9 (.objEq w z) (.classEq (.cv x) (syn_cop (.cv y) (.cv w)))
      (.classEq (.cv x) (syn_cop (.cv y) (.cv z))) (.objEq v y)
      (.classEq (.cv x) (syn_cop (.cv v) (.cv z)))
      (.classEq (.cv x) (syn_cop (.cv y) (.cv z))) p0004 p0006
  have p0008_e02_recanon :
    Nominal.NPrf
      (.imp (syn_wa (.classEq (.cv w) (.cv z)) (.classEq (.cv v) (.cv y))) (syn_wb
          (syn_wa (.classEq (.cv x) (syn_cop (.cv y) (.cv w)))
            (.classEq (.cv x) (syn_cop (.cv v) (.cv z))))
          (syn_wa (.classEq (.cv x) (syn_cop (.cv y) (.cv z)))
            (.classEq (.cv x) (syn_cop (.cv y) (.cv z)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wa syn_wb
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0007
  have p0008 :=
    @g_spc2ev
      (syn_wa (.classEq (.cv x) (syn_cop (.cv y) (.cv w)))
        (.classEq (.cv x) (syn_cop (.cv v) (.cv z))))
      (syn_wa (.classEq (.cv x) (syn_cop (.cv y) (.cv z)))
        (.classEq (.cv x) (syn_cop (.cv y) (.cv z))))
      w v (.cv z) (.cv y) dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
      dv_cache_0007 dv_cache_0008 dv_cache_0009 p0001 p0002 p0008_e02_recanon
  have p0009 :=
    @g_anidms (.classEq (.cv x) (syn_cop (.cv y) (.cv z)))
      (syn_wex w (syn_wex v (syn_wa (.classEq (.cv x) (syn_cop (.cv y) (.cv w)))
            (.classEq (.cv x) (syn_cop (.cv v) (.cv z))))))
      p0008
  have p0010 :=
    @g_simpl (.classEq (.cv x) (syn_cop (.cv y) (.cv w)))
      (.classEq (.cv x) (syn_cop (.cv v) (.cv z)))
  have p0011 := @g_eqtr2 (.cv x) (syn_cop (.cv y) (.cv w)) (syn_cop (.cv v) (.cv z))
  have p0012 := @g_opth (.cv y) (.cv w) (.cv v) (.cv z)
  have p0013_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq w z) (.classEq (syn_cop (.cv y) (.cv w)) (syn_cop (.cv y) (.cv z)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex syn_wex
          syn_cphi
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0003
  have p0013 :=
    @g_adantl (.objEq w z) (.classEq (syn_cop (.cv y) (.cv w)) (syn_cop (.cv y) (.cv z)))
      (.objEq y v) p0013_e00_recanon
  have p0014_e00_recanon :
    Nominal.NPrf
      (syn_wb (.classEq (syn_cop (.cv y) (.cv w)) (syn_cop (.cv v) (.cv z)))
        (syn_wa (.objEq y v) (.objEq w z))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex syn_wex
          syn_cphi
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
    @g_sylbi (.classEq (syn_cop (.cv y) (.cv w)) (syn_cop (.cv v) (.cv z)))
      (syn_wa (.objEq y v) (.objEq w z))
      (.classEq (syn_cop (.cv y) (.cv w)) (syn_cop (.cv y) (.cv z))) p0014_e00_recanon
      p0013
  have p0015 :=
    @g_syl
      (syn_wa (.classEq (.cv x) (syn_cop (.cv y) (.cv w)))
        (.classEq (.cv x) (syn_cop (.cv v) (.cv z))))
      (.classEq (syn_cop (.cv y) (.cv w)) (syn_cop (.cv v) (.cv z)))
      (.classEq (syn_cop (.cv y) (.cv w)) (syn_cop (.cv y) (.cv z))) p0011 p0014
  have p0016 :=
    @g_eqtrd
      (syn_wa (.classEq (.cv x) (syn_cop (.cv y) (.cv w)))
        (.classEq (.cv x) (syn_cop (.cv v) (.cv z))))
      (.cv x) (syn_cop (.cv y) (.cv w)) (syn_cop (.cv y) (.cv z)) p0010 p0015
  have p0017 :=
    @g_exlimivv
      (syn_wa (.classEq (.cv x) (syn_cop (.cv y) (.cv w)))
        (.classEq (.cv x) (syn_cop (.cv v) (.cv z))))
      (.classEq (.cv x) (syn_cop (.cv y) (.cv z))) w v dv_cache_0010 dv_cache_0011 p0016
  have p0018 :=
    @g_impbii (.classEq (.cv x) (syn_cop (.cv y) (.cv z)))
      (syn_wex w (syn_wex v (syn_wa (.classEq (.cv x) (syn_cop (.cv y) (.cv w)))
            (.classEq (.cv x) (syn_cop (.cv v) (.cv z))))))
      p0009 p0017
  have p0019 := @g_brcnv (.cv y) (.cv x) (syn_c1st)
  have p0020 := @g_br1st w (.cv x) (.cv y) dv_cache_0012 dv_cache_0005 p0002
  have p0021 :=
    @g_bitri (syn_wbr (.cv y) (syn_ccnv (syn_c1st)) (.cv x))
      (syn_wbr (.cv x) (syn_c1st) (.cv y))
      (syn_wex w (.classEq (.cv x) (syn_cop (.cv y) (.cv w)))) p0019 p0020
  have p0022 := @g_brcnv (.cv z) (.cv x) (syn_c2nd)
  have p0023 := @g_br2nd v (.cv x) (.cv z) dv_cache_0013 dv_cache_0004 p0001
  have p0024 :=
    @g_bitri (syn_wbr (.cv z) (syn_ccnv (syn_c2nd)) (.cv x))
      (syn_wbr (.cv x) (syn_c2nd) (.cv z))
      (syn_wex v (.classEq (.cv x) (syn_cop (.cv v) (.cv z)))) p0022 p0023
  have p0025 :=
    @g_anbi12i (syn_wbr (.cv y) (syn_ccnv (syn_c1st)) (.cv x))
      (syn_wex w (.classEq (.cv x) (syn_cop (.cv y) (.cv w))))
      (syn_wbr (.cv z) (syn_ccnv (syn_c2nd)) (.cv x))
      (syn_wex v (.classEq (.cv x) (syn_cop (.cv v) (.cv z)))) p0021 p0024
  have p0026 :=
    @g_n_3bitr4i
      (syn_wex w (syn_wex v (syn_wa (.classEq (.cv x) (syn_cop (.cv y) (.cv w)))
            (.classEq (.cv x) (syn_cop (.cv v) (.cv z))))))
      (syn_wa (syn_wex w (.classEq (.cv x) (syn_cop (.cv y) (.cv w))))
        (syn_wex v (.classEq (.cv x) (syn_cop (.cv v) (.cv z)))))
      (.classEq (.cv x) (syn_cop (.cv y) (.cv z)))
      (syn_wa (syn_wbr (.cv y) (syn_ccnv (syn_c1st)) (.cv x))
        (syn_wbr (.cv z) (syn_ccnv (syn_c2nd)) (.cv x)))
      p0000 p0018 p0025
  have p0027 :=
    @g_n_2rexbii (.classEq (.cv x) (syn_cop (.cv y) (.cv z)))
      (syn_wa (syn_wbr (.cv y) (syn_ccnv (syn_c1st)) (.cv x))
        (syn_wbr (.cv z) (syn_ccnv (syn_c2nd)) (.cv x)))
      y z A B p0026
  have p0028 :=
    @g_elxp2 y z (.cv x) A B dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020
  have p0029 :=
    @g_elima y (.cv x) (syn_ccnv (syn_c1st)) A dv_cache_0014 dv_cache_0021 dv_cache_0016
  have p0030 :=
    @g_elima z (.cv x) (syn_ccnv (syn_c2nd)) B dv_cache_0015 dv_cache_0022 dv_cache_0019
  have p0031 :=
    @g_anbi12i (.classMem (.cv x) (syn_cima (syn_ccnv (syn_c1st)) A))
      (syn_wrex y A (syn_wbr (.cv y) (syn_ccnv (syn_c1st)) (.cv x)))
      (.classMem (.cv x) (syn_cima (syn_ccnv (syn_c2nd)) B))
      (syn_wrex z B (syn_wbr (.cv z) (syn_ccnv (syn_c2nd)) (.cv x))) p0029 p0030
  have p0032 :=
    @g_elin (.cv x) (syn_cima (syn_ccnv (syn_c1st)) A) (syn_cima (syn_ccnv (syn_c2nd)) B)
  have p0033 :=
    @g_reeanv (syn_wbr (.cv y) (syn_ccnv (syn_c1st)) (.cv x))
      (syn_wbr (.cv z) (syn_ccnv (syn_c2nd)) (.cv x)) y z A B dv_cache_0017 dv_cache_0018
      dv_cache_0023 dv_cache_0024 dv_cache_0020
  have p0034 :=
    @g_n_3bitr4i
      (syn_wa (.classMem (.cv x) (syn_cima (syn_ccnv (syn_c1st)) A))
        (.classMem (.cv x) (syn_cima (syn_ccnv (syn_c2nd)) B)))
      (syn_wa (syn_wrex y A (syn_wbr (.cv y) (syn_ccnv (syn_c1st)) (.cv x)))
        (syn_wrex z B (syn_wbr (.cv z) (syn_ccnv (syn_c2nd)) (.cv x))))
      (.classMem (.cv x)
        (syn_cin (syn_cima (syn_ccnv (syn_c1st)) A) (syn_cima (syn_ccnv (syn_c2nd)) B)))
      (syn_wrex y A (syn_wrex z B (syn_wa (syn_wbr (.cv y) (syn_ccnv (syn_c1st)) (.cv x))
            (syn_wbr (.cv z) (syn_ccnv (syn_c2nd)) (.cv x)))))
      p0031 p0032 p0033
  have p0035 :=
    @g_n_3bitr4i
      (syn_wrex y A (syn_wrex z B (.classEq (.cv x) (syn_cop (.cv y) (.cv z)))))
      (syn_wrex y A (syn_wrex z B (syn_wa (syn_wbr (.cv y) (syn_ccnv (syn_c1st)) (.cv x))
            (syn_wbr (.cv z) (syn_ccnv (syn_c2nd)) (.cv x)))))
      (.classMem (.cv x) (syn_cxp A B))
      (.classMem (.cv x)
        (syn_cin (syn_cima (syn_ccnv (syn_c1st)) A) (syn_cima (syn_ccnv (syn_c2nd)) B)))
      p0027 p0028 p0034
  have p0036 :=
    @g_eqriv x (syn_cxp A B)
      (syn_cin (syn_cima (syn_ccnv (syn_c1st)) A) (syn_cima (syn_ccnv (syn_c2nd)) B))
      dv_cache_0025 dv_cache_0026 p0035
  exact p0036

@[expose]
noncomputable def g_xpexg (A : Class) (B : Class) (V : Class) (W : Class) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem A V) (.classMem B W)) (.classMem (syn_cxp A B) (syn_cvv))) :=
  by
  have p0000 := @g_dfxp2 A B
  have p0001 := @g_n_1stex
  have p0002 := @g_cnvex (syn_c1st) p0001
  have p0003 := @g_imaexg (syn_ccnv (syn_c1st)) A (syn_cvv) V
  have p0004 :=
    @g_mpan (.classMem (syn_ccnv (syn_c1st)) (syn_cvv)) (.classMem A V)
      (.classMem (syn_cima (syn_ccnv (syn_c1st)) A) (syn_cvv)) p0002 p0003
  have p0005 := @g_n_2ndex
  have p0006 := @g_cnvex (syn_c2nd) p0005
  have p0007 := @g_imaexg (syn_ccnv (syn_c2nd)) B (syn_cvv) W
  have p0008 :=
    @g_mpan (.classMem (syn_ccnv (syn_c2nd)) (syn_cvv)) (.classMem B W)
      (.classMem (syn_cima (syn_ccnv (syn_c2nd)) B) (syn_cvv)) p0006 p0007
  have p0009 :=
    @g_inexg (syn_cima (syn_ccnv (syn_c1st)) A) (syn_cima (syn_ccnv (syn_c2nd)) B)
      (syn_cvv) (syn_cvv)
  have p0010 :=
    @g_syl2an (.classMem A V) (.classMem (syn_cima (syn_ccnv (syn_c1st)) A) (syn_cvv))
      (.classMem (syn_cima (syn_ccnv (syn_c2nd)) B) (syn_cvv))
      (.classMem (syn_cin (syn_cima (syn_ccnv (syn_c1st)) A) (syn_cima (syn_ccnv (syn_c2nd)) B))
        (syn_cvv))
      (.classMem B W) p0004 p0008 p0009
  have p0011 :=
    @g_syl5eqel (syn_wa (.classMem A V) (.classMem B W)) (syn_cxp A B)
      (syn_cin (syn_cima (syn_ccnv (syn_c1st)) A) (syn_cima (syn_ccnv (syn_c2nd)) B))
      (syn_cvv) p0000 p0010
  exact p0011

@[expose]
noncomputable def g_xpex (A : Class) (B : Class)
    (hyp_xpex_1 : Nominal.NPrf (.classMem A (syn_cvv)))
    (hyp_xpex_2 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf (.classMem (syn_cxp A B) (syn_cvv)) :=
  by
  have p0000 := @g_xpexg A B (syn_cvv) (syn_cvv)
  have p0001 :=
    @g_mp2an (.classMem A (syn_cvv)) (.classMem B (syn_cvv))
      (.classMem (syn_cxp A B) (syn_cvv)) hyp_xpex_1 hyp_xpex_2 p0000
  exact p0001

@[expose]
noncomputable def g_resexg (A : Class) (B : Class) (V : Class) (W : Class) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem A V) (.classMem B W)) (.classMem (syn_cres A B) (syn_cvv))) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_cres A B))
  have p0001 := @g_vvex
  have p0002 := @g_xpexg B (syn_cvv) W (syn_cvv)
  have p0003 :=
    @g_mpan2 (.classMem B W) (.classMem (syn_cvv) (syn_cvv))
      (.classMem (syn_cxp B (syn_cvv)) (syn_cvv)) p0001 p0002
  have p0004 := @g_inexg A (syn_cxp B (syn_cvv)) V (syn_cvv)
  have p0005 :=
    @g_sylan2 (.classMem B W) (.classMem A V) (.classMem (syn_cxp B (syn_cvv)) (syn_cvv))
      (.classMem (syn_cin A (syn_cxp B (syn_cvv))) (syn_cvv)) p0003 p0004
  have p0006 :=
    @g_syl5eqel (syn_wa (.classMem A V) (.classMem B W)) (syn_cres A B)
      (syn_cin A (syn_cxp B (syn_cvv))) (syn_cvv) p0000 p0005
  exact p0006

@[expose]
noncomputable def g_resex (A : Class) (B : Class)
    (hyp_resex_1 : Nominal.NPrf (.classMem A (syn_cvv)))
    (hyp_resex_2 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf (.classMem (syn_cres A B) (syn_cvv)) :=
  by
  have p0000 := @g_resexg A B (syn_cvv) (syn_cvv)
  have p0001 :=
    @g_mp2an (.classMem A (syn_cvv)) (.classMem B (syn_cvv))
      (.classMem (syn_cres A B) (syn_cvv)) hyp_resex_1 hyp_resex_2 p0000
  exact p0001

@[expose]
noncomputable def g_dffun2 (x : Var) (y : Var) (z : Var) (A : Class) (dv_A_x : x ∉ A.fv)
    (dv_A_y : y ∉ A.fv) (dv_A_z : z ∉ A.fv) (dv_x_y : x ≠ y) (dv_x_z : x ≠ z)
    (dv_y_z : y ≠ z) :
    Nominal.NPrf
      (syn_wb (syn_wfun A) (.all x (.all y (.all z
              (.imp (syn_wa (syn_wbr (.cv x) A (.cv y)) (syn_wbr (.cv x) A (.cv z)))
                (.objEq y z)))))) :=
  by
  have dv_cache_0001 : y ∉ ((syn_ccom A (syn_ccnv A))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, Finset.mem_union, dv_A_y,
          or_false, not_false_eq_true])
  have dv_cache_0002 : z ∉ ((syn_ccom A (syn_ccnv A))).fv :=
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
  have dv_cache_0003 : y ∉ ((syn_cid)).fv :=
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
  have dv_cache_0004 : z ∉ ((syn_cid)).fv :=
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
  have dv_cache_0009 : x ∉ ((syn_ccnv A)).fv :=
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
  have p0000 := (Nominal.biimpRefl (syn_wfun A))
  have p0001 :=
    @g_ssrel y z (syn_ccom A (syn_ccnv A)) (syn_cid) dv_cache_0001 dv_cache_0002
      dv_cache_0003 dv_cache_0004 dv_cache_0005
  have p0002 :=
    @g_opelco x (.cv y) (.cv z) A (syn_ccnv A) dv_cache_0006 dv_cache_0007 dv_cache_0008
      dv_cache_0009
  have p0003 := @g_brcnv (.cv y) (.cv x) A
  have p0004 :=
    @g_anbi1i (syn_wbr (.cv y) (syn_ccnv A) (.cv x)) (syn_wbr (.cv x) A (.cv y))
      (syn_wbr (.cv x) A (.cv z)) p0003
  have p0005 :=
    @g_exbii (syn_wa (syn_wbr (.cv y) (syn_ccnv A) (.cv x)) (syn_wbr (.cv x) A (.cv z)))
      (syn_wa (syn_wbr (.cv x) A (.cv y)) (syn_wbr (.cv x) A (.cv z))) x p0004
  have p0006 :=
    @g_bitri (.classMem (syn_cop (.cv y) (.cv z)) (syn_ccom A (syn_ccnv A)))
      (syn_wex x (syn_wa (syn_wbr (.cv y) (syn_ccnv A) (.cv x)) (syn_wbr (.cv x) A (.cv z))))
      (syn_wex x (syn_wa (syn_wbr (.cv x) A (.cv y)) (syn_wbr (.cv x) A (.cv z)))) p0002
      p0005
  have p0007 := (Nominal.biimpRefl (syn_wbr (.cv y) (syn_cid) (.cv z)))
  have p0008 := @g_vex z
  have p0009 := @g_ideq (.cv y) (.cv z) p0008
  have p0010_e01_recanon :
    Nominal.NPrf (syn_wb (syn_wbr (.cv y) (syn_cid) (.cv z)) (.objEq y z)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex
          syn_wex syn_cphi syn_cid syn_copab
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
    @g_bitr3i (.classMem (syn_cop (.cv y) (.cv z)) (syn_cid))
      (syn_wbr (.cv y) (syn_cid) (.cv z)) (.objEq y z) p0007 p0010_e01_recanon
  have p0011 :=
    @g_imbi12i (.classMem (syn_cop (.cv y) (.cv z)) (syn_ccom A (syn_ccnv A)))
      (syn_wex x (syn_wa (syn_wbr (.cv x) A (.cv y)) (syn_wbr (.cv x) A (.cv z))))
      (.classMem (syn_cop (.cv y) (.cv z)) (syn_cid)) (.objEq y z) p0006 p0010
  have p0012 :=
    @g_n_19_23v (syn_wa (syn_wbr (.cv x) A (.cv y)) (syn_wbr (.cv x) A (.cv z)))
      (.objEq y z) x dv_cache_0010
  have p0013 :=
    @g_bitr4i
      (.imp (.classMem (syn_cop (.cv y) (.cv z)) (syn_ccom A (syn_ccnv A)))
        (.classMem (syn_cop (.cv y) (.cv z)) (syn_cid)))
      (.imp (syn_wex x (syn_wa (syn_wbr (.cv x) A (.cv y)) (syn_wbr (.cv x) A (.cv z))))
        (.objEq y z))
      (.all x (.imp (syn_wa (syn_wbr (.cv x) A (.cv y)) (syn_wbr (.cv x) A (.cv z)))
          (.objEq y z)))
      p0011 p0012
  have p0014 :=
    @g_n_2albii
      (.imp (.classMem (syn_cop (.cv y) (.cv z)) (syn_ccom A (syn_ccnv A)))
        (.classMem (syn_cop (.cv y) (.cv z)) (syn_cid)))
      (.all x (.imp (syn_wa (syn_wbr (.cv x) A (.cv y)) (syn_wbr (.cv x) A (.cv z)))
          (.objEq y z)))
      y z p0013
  have p0015 :=
    @g_alrot3
      (.imp (syn_wa (syn_wbr (.cv x) A (.cv y)) (syn_wbr (.cv x) A (.cv z))) (.objEq y z))
      x y z
  have p0016 :=
    @g_bitr4i
      (.all y (.all z (.imp (.classMem (syn_cop (.cv y) (.cv z)) (syn_ccom A (syn_ccnv A)))
            (.classMem (syn_cop (.cv y) (.cv z)) (syn_cid)))))
      (.all y (.all z (.all x
            (.imp (syn_wa (syn_wbr (.cv x) A (.cv y)) (syn_wbr (.cv x) A (.cv z)))
              (.objEq y z)))))
      (.all x (.all y (.all z
            (.imp (syn_wa (syn_wbr (.cv x) A (.cv y)) (syn_wbr (.cv x) A (.cv z)))
              (.objEq y z)))))
      p0014 p0015
  have p0017 :=
    @g_n_3bitri (syn_wfun A) (syn_wss (syn_ccom A (syn_ccnv A)) (syn_cid))
      (.all y (.all z (.imp (.classMem (syn_cop (.cv y) (.cv z)) (syn_ccom A (syn_ccnv A)))
            (.classMem (syn_cop (.cv y) (.cv z)) (syn_cid)))))
      (.all x (.all y (.all z
            (.imp (syn_wa (syn_wbr (.cv x) A (.cv y)) (syn_wbr (.cv x) A (.cv z)))
              (.objEq y z)))))
      p0000 p0001 p0016
  exact p0017

@[expose]
noncomputable def g_dffun3 (x : Var) (y : Var) (z : Var) (A : Class) (dv_A_x : x ∉ A.fv)
    (dv_A_y : y ∉ A.fv) (dv_A_z : z ∉ A.fv) (dv_x_y : x ≠ y) (dv_x_z : x ≠ z)
    (dv_y_z : y ≠ z) :
    Nominal.NPrf
      (syn_wb (syn_wfun A)
        (.all x (syn_wex z (.all y (.imp (syn_wbr (.cv x) A (.cv y)) (.objEq y z)))))) :=
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
  have dv_cache_0007 : z ∉ ((syn_wbr (.cv x) A (.cv y))).fv :=
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
  have dv_cache_0008 : y ∉ ((syn_wbr (.cv x) A (.cv z))).fv :=
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
    @g_dffun2 x y z A dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006
  have p0001 := @g_breq2 (.cv y) (.cv z) (.cv x) A
  have p0002_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq y z) (syn_wb (syn_wbr (.cv x) A (.cv y)) (syn_wbr (.cv x) A (.cv z)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex
          syn_wex syn_cphi
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0001
  have p0002 :=
    @g_mo4 (syn_wbr (.cv x) A (.cv y)) (syn_wbr (.cv x) A (.cv z)) y z dv_cache_0007
      dv_cache_0008 dv_cache_0006 p0002_e00_recanon
  have p0003 := @g_nfv (syn_wbr (.cv x) A (.cv y)) z dv_cache_0007
  have p0004 := @g_mo2 (syn_wbr (.cv x) A (.cv y)) y z dv_cache_0006 p0003
  have p0005 :=
    @g_bitr3i
      (.all y (.all z (.imp (syn_wa (syn_wbr (.cv x) A (.cv y)) (syn_wbr (.cv x) A (.cv z)))
            (.objEq y z))))
      (syn_wmo y (syn_wbr (.cv x) A (.cv y)))
      (syn_wex z (.all y (.imp (syn_wbr (.cv x) A (.cv y)) (.objEq y z)))) p0002 p0004
  have p0006 :=
    @g_albii
      (.all y (.all z (.imp (syn_wa (syn_wbr (.cv x) A (.cv y)) (syn_wbr (.cv x) A (.cv z)))
            (.objEq y z))))
      (syn_wex z (.all y (.imp (syn_wbr (.cv x) A (.cv y)) (.objEq y z)))) x p0005
  have p0007 :=
    @g_bitri (syn_wfun A)
      (.all x (.all y (.all z
            (.imp (syn_wa (syn_wbr (.cv x) A (.cv y)) (syn_wbr (.cv x) A (.cv z)))
              (.objEq y z)))))
      (.all x (syn_wex z (.all y (.imp (syn_wbr (.cv x) A (.cv y)) (.objEq y z))))) p0000
      p0006
  exact p0007

@[expose]
noncomputable def g_dffun4 (x : Var) (y : Var) (z : Var) (A : Class) (dv_A_x : x ∉ A.fv)
    (dv_A_y : y ∉ A.fv) (dv_A_z : z ∉ A.fv) (dv_x_y : x ≠ y) (dv_x_z : x ≠ z)
    (dv_y_z : y ≠ z) :
    Nominal.NPrf
      (syn_wb (syn_wfun A) (.all x (.all y (.all z (.imp
                (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) A)
                  (.classMem (syn_cop (.cv x) (.cv z)) A)) (.objEq y z)))))) :=
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
    @g_dffun2 x y z A dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006
  have p0001 := (Nominal.biimpRefl (syn_wbr (.cv x) A (.cv y)))
  have p0002 := (Nominal.biimpRefl (syn_wbr (.cv x) A (.cv z)))
  have p0003 :=
    @g_anbi12i (syn_wbr (.cv x) A (.cv y)) (.classMem (syn_cop (.cv x) (.cv y)) A)
      (syn_wbr (.cv x) A (.cv z)) (.classMem (syn_cop (.cv x) (.cv z)) A) p0001 p0002
  have p0004 :=
    @g_imbi1i (syn_wa (syn_wbr (.cv x) A (.cv y)) (syn_wbr (.cv x) A (.cv z)))
      (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) A) (.classMem (syn_cop (.cv x) (.cv z)) A))
      (.objEq y z) p0003
  have p0005 :=
    @g_albii
      (.imp (syn_wa (syn_wbr (.cv x) A (.cv y)) (syn_wbr (.cv x) A (.cv z))) (.objEq y z))
      (.imp (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) A)
          (.classMem (syn_cop (.cv x) (.cv z)) A)) (.objEq y z))
      z p0004
  have p0006 :=
    @g_n_2albii
      (.all z (.imp (syn_wa (syn_wbr (.cv x) A (.cv y)) (syn_wbr (.cv x) A (.cv z)))
          (.objEq y z)))
      (.all z (.imp (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) A)
            (.classMem (syn_cop (.cv x) (.cv z)) A)) (.objEq y z)))
      x y p0005
  have p0007 :=
    @g_bitri (syn_wfun A)
      (.all x (.all y (.all z
            (.imp (syn_wa (syn_wbr (.cv x) A (.cv y)) (syn_wbr (.cv x) A (.cv z)))
              (.objEq y z)))))
      (.all x (.all y (.all z (.imp (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) A)
                (.classMem (syn_cop (.cv x) (.cv z)) A)) (.objEq y z)))))
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

@[expose]
noncomputable def g_dffun6f (x : Var) (y : Var) (A : Class) (dv_x_y : x ≠ y)
    (hyp_dffun6f_1 : Nominal.NPrf (syn_wnfc x A))
    (hyp_dffun6f_2 : Nominal.NPrf (syn_wnfc y A)) :
    Nominal.NPrf (syn_wb (syn_wfun A) (.all x (syn_wmo y (syn_wbr (.cv x) A (.cv y))))) :=
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
  have dv_cache_0009 : v ∉ ((syn_wbr (.cv w) A (.cv y))).fv :=
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
  have dv_cache_0010 : u ∉ ((syn_wbr (.cv w) A (.cv v))).fv :=
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
  have dv_cache_0013 : w ∉ ((syn_wmo y (syn_wbr (.cv x) A (.cv y)))).fv :=
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
    @g_dffun3 w v u A dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006
  have p0001 := @g_nfcv y (.cv w) dv_cache_0007
  have p0002 := @g_nfcv y (.cv v) dv_cache_0008
  have p0003 := @g_nfbr y (.cv w) (.cv v) A p0001 hyp_dffun6f_2 p0002
  have p0004 := @g_nfv (syn_wbr (.cv w) A (.cv y)) v dv_cache_0009
  have p0005 := @g_breq2 (.cv v) (.cv y) (.cv w) A
  have p0006_e02_recanon :
    Nominal.NPrf
      (.imp (.objEq v y) (syn_wb (syn_wbr (.cv w) A (.cv v)) (syn_wbr (.cv w) A (.cv y)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex
          syn_wex syn_cphi
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0005
  have p0006 :=
    @g_cbvmo (syn_wbr (.cv w) A (.cv v)) (syn_wbr (.cv w) A (.cv y)) v y p0003 p0004
      p0006_e02_recanon
  have p0007 :=
    @g_albii (syn_wmo v (syn_wbr (.cv w) A (.cv v)))
      (syn_wmo y (syn_wbr (.cv w) A (.cv y))) w p0006
  have p0008 := @g_nfv (syn_wbr (.cv w) A (.cv v)) u dv_cache_0010
  have p0009 := @g_mo2 (syn_wbr (.cv w) A (.cv v)) v u dv_cache_0006 p0008
  have p0010 :=
    @g_albii (syn_wmo v (syn_wbr (.cv w) A (.cv v)))
      (syn_wex u (.all v (.imp (syn_wbr (.cv w) A (.cv v)) (.objEq v u)))) w p0009
  have p0011 := @g_nfcv x (.cv w) dv_cache_0011
  have p0012 := @g_nfcv x (.cv y) dv_cache_0012
  have p0013 := @g_nfbr x (.cv w) (.cv y) A p0011 hyp_dffun6f_1 p0012
  have p0014 := @g_nfmo (syn_wbr (.cv w) A (.cv y)) x y p0013
  have p0015 := @g_nfv (syn_wmo y (syn_wbr (.cv x) A (.cv y))) w dv_cache_0013
  have p0016 := @g_breq1 (.cv w) (.cv x) (.cv y) A
  have p0017_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq w x) (syn_wb (syn_wbr (.cv w) A (.cv y)) (syn_wbr (.cv x) A (.cv y)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex
          syn_wex syn_cphi
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0016
  have p0017 :=
    @g_mobidv (.objEq w x) (syn_wbr (.cv w) A (.cv y)) (syn_wbr (.cv x) A (.cv y)) y
      dv_cache_0014 p0017_e00_recanon
  have p0018 :=
    @g_cbval (syn_wmo y (syn_wbr (.cv w) A (.cv y)))
      (syn_wmo y (syn_wbr (.cv x) A (.cv y))) w x p0014 p0015 p0017
  have p0019 :=
    @g_n_3bitr3ri (.all w (syn_wmo v (syn_wbr (.cv w) A (.cv v))))
      (.all w (syn_wmo y (syn_wbr (.cv w) A (.cv y))))
      (.all w (syn_wex u (.all v (.imp (syn_wbr (.cv w) A (.cv v)) (.objEq v u)))))
      (.all x (syn_wmo y (syn_wbr (.cv x) A (.cv y)))) p0007 p0010 p0018
  have p0020 :=
    @g_bitr4i (syn_wfun A)
      (.all w (syn_wex u (.all v (.imp (syn_wbr (.cv w) A (.cv v)) (.objEq v u)))))
      (.all x (syn_wmo y (syn_wbr (.cv x) A (.cv y)))) p0000 p0019
  exact p0020

@[expose]
noncomputable def g_dffun6 (x : Var) (y : Var) (F : Class) (dv_F_x : x ∉ F.fv)
    (dv_F_y : y ∉ F.fv) (dv_x_y : x ≠ y) :
    Nominal.NPrf (syn_wb (syn_wfun F) (.all x (syn_wmo y (syn_wbr (.cv x) F (.cv y))))) :=
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
  have p0000 := @g_nfcv x F dv_cache_0001
  have p0001 := @g_nfcv y F dv_cache_0002
  have p0002 := @g_dffun6f x y F dv_cache_0003 p0000 p0001
  exact p0002

@[expose]
noncomputable def g_funmo (y : Var) (A : Class) (F : Class) (dv_A_y : y ∉ A.fv)
    (dv_F_y : y ∉ F.fv) :
    Nominal.NPrf (.imp (syn_wfun F) (syn_wmo y (syn_wbr A F (.cv y)))) :=
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
  have dv_cache_0003 : x ∉ ((syn_wmo y (syn_wbr A F (.cv y)))).fv :=
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
  have dv_cache_0007 : y ∉ ((Wff.classMem A (syn_cvv))).fv :=
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
  have p0000 := @g_brreldmex A (.cv y) F
  have p0001 := @g_ancri (syn_wbr A F (.cv y)) (.classMem A (syn_cvv)) p0000
  have p0002 := Nominal.gen p0001 y
  have p0003 := @g_breq1 (.cv x) A (.cv y) F
  have p0004 :=
    @g_mobidv (.classEq (.cv x) A) (syn_wbr (.cv x) F (.cv y)) (syn_wbr A F (.cv y)) y
      dv_cache_0001 p0003
  have p0005 :=
    @g_spcgv (syn_wmo y (syn_wbr (.cv x) F (.cv y))) (syn_wmo y (syn_wbr A F (.cv y))) x A
      (syn_cvv) dv_cache_0002 dv_cache_0003 p0004
  have p0006 :=
    @g_com12 (.classMem A (syn_cvv)) (.all x (syn_wmo y (syn_wbr (.cv x) F (.cv y))))
      (syn_wmo y (syn_wbr A F (.cv y))) p0005
  have p0007 := @g_dffun6 x y F dv_cache_0004 dv_cache_0005 dv_cache_0006
  have p0008 := @g_moanimv (.classMem A (syn_cvv)) (syn_wbr A F (.cv y)) y dv_cache_0007
  have p0009 :=
    @g_n_3imtr4i (.all x (syn_wmo y (syn_wbr (.cv x) F (.cv y))))
      (.imp (.classMem A (syn_cvv)) (syn_wmo y (syn_wbr A F (.cv y)))) (syn_wfun F)
      (syn_wmo y (syn_wa (.classMem A (syn_cvv)) (syn_wbr A F (.cv y)))) p0006 p0007 p0008
  have p0010 :=
    @g_moim (syn_wbr A F (.cv y)) (syn_wa (.classMem A (syn_cvv)) (syn_wbr A F (.cv y))) y
  have p0011 :=
    @g_mpsyl
      (.all y (.imp (syn_wbr A F (.cv y))
          (syn_wa (.classMem A (syn_cvv)) (syn_wbr A F (.cv y)))))
      (syn_wfun F) (syn_wmo y (syn_wa (.classMem A (syn_cvv)) (syn_wbr A F (.cv y))))
      (syn_wmo y (syn_wbr A F (.cv y))) p0002 p0009 p0010
  exact p0011

@[expose]
noncomputable def g_funss (A : Class) (B : Class) :
    Nominal.NPrf (.imp (syn_wss A B) (.imp (syn_wfun B) (syn_wfun A))) :=
  by
  have p0000 := @g_coss1 A B (syn_ccnv A)
  have p0001 := @g_cnvss A B
  have p0002 := @g_coss2 (syn_ccnv A) (syn_ccnv B) B
  have p0003 :=
    @g_syl (syn_wss A B) (syn_wss (syn_ccnv A) (syn_ccnv B))
      (syn_wss (syn_ccom B (syn_ccnv A)) (syn_ccom B (syn_ccnv B))) p0001 p0002
  have p0004 :=
    @g_sstrd (syn_wss A B) (syn_ccom A (syn_ccnv A)) (syn_ccom B (syn_ccnv A))
      (syn_ccom B (syn_ccnv B)) p0000 p0003
  have p0005 := @g_sstr2 (syn_ccom A (syn_ccnv A)) (syn_ccom B (syn_ccnv B)) (syn_cid)
  have p0006 :=
    @g_syl (syn_wss A B) (syn_wss (syn_ccom A (syn_ccnv A)) (syn_ccom B (syn_ccnv B)))
      (.imp (syn_wss (syn_ccom B (syn_ccnv B)) (syn_cid))
        (syn_wss (syn_ccom A (syn_ccnv A)) (syn_cid)))
      p0004 p0005
  have p0007 := (Nominal.biimpRefl (syn_wfun B))
  have p0008 := (Nominal.biimpRefl (syn_wfun A))
  have p0009 :=
    @g_n_3imtr4g (syn_wss A B) (syn_wss (syn_ccom B (syn_ccnv B)) (syn_cid))
      (syn_wss (syn_ccom A (syn_ccnv A)) (syn_cid)) (syn_wfun B) (syn_wfun A) p0006 p0007
      p0008
  exact p0009

@[expose]
noncomputable def g_funeq (A : Class) (B : Class) :
    Nominal.NPrf (.imp (.classEq A B) (syn_wb (syn_wfun A) (syn_wfun B))) :=
  by
  have p0000 := @g_funss B A
  have p0001 := @g_funss A B
  have p0002 :=
    @g_anim12i (syn_wss B A) (.imp (syn_wfun A) (syn_wfun B)) (syn_wss A B)
      (.imp (syn_wfun B) (syn_wfun A)) p0000 p0001
  have p0003 :=
    @g_ancoms (syn_wss B A) (syn_wss A B)
      (syn_wa (.imp (syn_wfun A) (syn_wfun B)) (.imp (syn_wfun B) (syn_wfun A))) p0002
  have p0004 := @g_eqss A B
  have p0005 := @g_dfbi2 (syn_wfun A) (syn_wfun B)
  have p0006 :=
    @g_n_3imtr4i (syn_wa (syn_wss A B) (syn_wss B A))
      (syn_wa (.imp (syn_wfun A) (syn_wfun B)) (.imp (syn_wfun B) (syn_wfun A)))
      (.classEq A B) (syn_wb (syn_wfun A) (syn_wfun B)) p0003 p0004 p0005
  exact p0006

@[expose]
noncomputable def g_funeqi (A : Class) (B : Class)
    (hyp_funeqi_1 : Nominal.NPrf (.classEq A B)) :
    Nominal.NPrf (syn_wb (syn_wfun A) (syn_wfun B)) :=
  by
  have p0000 := @g_funeq A B
  have p0001 := Nominal.mp hyp_funeqi_1 p0000
  exact p0001

@[expose]
noncomputable def g_funeqd (ph : Wff) (A : Class) (B : Class)
    (hyp_funeqd_1 : Nominal.NPrf (.imp ph (.classEq A B))) :
    Nominal.NPrf (.imp ph (syn_wb (syn_wfun A) (syn_wfun B))) :=
  by
  have p0000 := @g_funeq A B
  have p0001 :=
    @g_syl ph (.classEq A B) (syn_wb (syn_wfun A) (syn_wfun B)) hyp_funeqd_1 p0000
  exact p0001

@[expose]
noncomputable def g_funeu (y : Var) (A : Class) (B : Class) (F : Class)
    (dv_A_y : y ∉ A.fv) (dv_F_y : y ∉ F.fv) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wfun F) (syn_wbr A F B)) (syn_weu y (syn_wbr A F (.cv y)))) :=
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
  have p0000 := @g_breldm A B F
  have p0001 := @g_eldm y A F dv_cache_0001 dv_cache_0002
  have p0002 :=
    @g_sylib (syn_wbr A F B) (.classMem A (syn_cdm F)) (syn_wex y (syn_wbr A F (.cv y)))
      p0000 p0001
  have p0003 :=
    @g_adantl (syn_wbr A F B) (syn_wex y (syn_wbr A F (.cv y))) (syn_wfun F) p0002
  have p0004 := @g_funmo y A F dv_cache_0001 dv_cache_0002
  have p0005 :=
    @g_adantr (syn_wfun F) (syn_wmo y (syn_wbr A F (.cv y))) (syn_wbr A F B) p0004
  have p0006 :=
    @g_jca (syn_wa (syn_wfun F) (syn_wbr A F B)) (syn_wex y (syn_wbr A F (.cv y)))
      (syn_wmo y (syn_wbr A F (.cv y))) p0003 p0005
  have p0007 := @g_eu5 (syn_wbr A F (.cv y)) y
  have p0008 :=
    @g_sylibr (syn_wa (syn_wfun F) (syn_wbr A F B))
      (syn_wa (syn_wex y (syn_wbr A F (.cv y))) (syn_wmo y (syn_wbr A F (.cv y))))
      (syn_weu y (syn_wbr A F (.cv y))) p0006 p0007
  exact p0008

@[expose]
noncomputable def g_funeu2 (y : Var) (A : Class) (B : Class) (F : Class)
    (dv_A_y : y ∉ A.fv) (dv_F_y : y ∉ F.fv) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wfun F) (.classMem (syn_cop A B) F))
        (syn_weu y (.classMem (syn_cop A (.cv y)) F))) :=
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
  have p0000 := (Nominal.biimpRefl (syn_wbr A F B))
  have p0001 := @g_funeu y A B F dv_cache_0001 dv_cache_0002
  have p0002 := (Nominal.biimpRefl (syn_wbr A F (.cv y)))
  have p0003 := @g_eubii (syn_wbr A F (.cv y)) (.classMem (syn_cop A (.cv y)) F) y p0002
  have p0004 :=
    @g_sylib (syn_wa (syn_wfun F) (syn_wbr A F B)) (syn_weu y (syn_wbr A F (.cv y)))
      (syn_weu y (.classMem (syn_cop A (.cv y)) F)) p0001 p0003
  have p0005 :=
    @g_sylan2br (.classMem (syn_cop A B) F) (syn_wfun F) (syn_wbr A F B)
      (syn_weu y (.classMem (syn_cop A (.cv y)) F)) p0000 p0004
  exact p0005

@[expose]
noncomputable def g_funfn (A : Class) :
    Nominal.NPrf (syn_wb (syn_wfun A) (syn_wfn A (syn_cdm A))) :=
  by
  have p0000 := @g_eqid (syn_cdm A)
  have p0001 := @g_biantru (.classEq (syn_cdm A) (syn_cdm A)) (syn_wfun A) p0000
  have p0002 := (Nominal.biimpRefl (syn_wfn A (syn_cdm A)))
  have p0003 :=
    @g_bitr4i (syn_wfun A) (syn_wa (syn_wfun A) (.classEq (syn_cdm A) (syn_cdm A)))
      (syn_wfn A (syn_cdm A)) p0001 p0002
  exact p0003

@[expose]
noncomputable def g_funi : Nominal.NPrf (syn_wfun (syn_cid)) :=
  by
  have p0000 := @g_cnvi
  have p0001 := @g_coeq2i (syn_ccnv (syn_cid)) (syn_cid) (syn_cid) p0000
  have p0002 := @g_coi1 (syn_cid)
  have p0003 :=
    @g_eqtri (syn_ccom (syn_cid) (syn_ccnv (syn_cid))) (syn_ccom (syn_cid) (syn_cid))
      (syn_cid) p0001 p0002
  have p0004 := @g_eqimssi (syn_ccom (syn_cid) (syn_ccnv (syn_cid))) (syn_cid) p0003
  have p0005 := (Nominal.biimpRefl (syn_wfun (syn_cid)))
  have p0006 :=
    @g_mpbir (syn_wfun (syn_cid))
      (syn_wss (syn_ccom (syn_cid) (syn_ccnv (syn_cid))) (syn_cid)) p0004 p0005
  exact p0006

@[expose]
noncomputable def g_funopab (ph : Wff) (x : Var) (y : Var) (dv_x_y : x ≠ y) :
    Nominal.NPrf (syn_wb (syn_wfun (syn_copab x y ph)) (.all x (syn_wmo y ph))) :=
  by
  have dv_cache_0001 : x ≠ y := by exact (show x ≠ y from (by exact dv_x_y))
  have p0000 := @g_nfopab1 ph x y
  have p0001 := @g_nfopab2 ph x y
  have p0002 := @g_dffun6f x y (syn_copab x y ph) dv_cache_0001 p0000 p0001
  have p0003 := (Nominal.biimpRefl (syn_wbr (.cv x) (syn_copab x y ph) (.cv y)))
  have p0004 := @g_opabid ph x y
  have p0005 :=
    @g_bitri (syn_wbr (.cv x) (syn_copab x y ph) (.cv y))
      (.classMem (syn_cop (.cv x) (.cv y)) (syn_copab x y ph)) ph p0003 p0004
  have p0006 := @g_mobii (syn_wbr (.cv x) (syn_copab x y ph) (.cv y)) ph y p0005
  have p0007 :=
    @g_albii (syn_wmo y (syn_wbr (.cv x) (syn_copab x y ph) (.cv y))) (syn_wmo y ph) x
      p0006
  have p0008 :=
    @g_bitri (syn_wfun (syn_copab x y ph))
      (.all x (syn_wmo y (syn_wbr (.cv x) (syn_copab x y ph) (.cv y))))
      (.all x (syn_wmo y ph)) p0002 p0007
  exact p0008

@[expose]
noncomputable def g_funco (F : Class) (G : Class) :
    Nominal.NPrf (.imp (syn_wa (syn_wfun F) (syn_wfun G)) (syn_wfun (syn_ccom F G))) :=
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
  have dv_cache_0005 : z ∉ ((syn_wfun F)).fv :=
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
  have dv_cache_0006 : y ∉ ((syn_wbr (.cv x) G (.cv z))).fv :=
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
  have dv_cache_0007 : x ∉ ((syn_wa (syn_wfun F) (syn_wfun G))).fv :=
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
  have p0000 := @g_funmo z (.cv x) G dv_cache_0001 dv_cache_0002
  have p0001 := @g_funmo y (.cv z) F dv_cache_0003 dv_cache_0004
  have p0002 :=
    @g_alrimiv (syn_wfun F) (syn_wmo y (syn_wbr (.cv z) F (.cv y))) z dv_cache_0005 p0001
  have p0003 :=
    @g_moexexv (syn_wbr (.cv x) G (.cv z)) (syn_wbr (.cv z) F (.cv y)) z y dv_cache_0006
  have p0004 :=
    @g_syl2anr (syn_wfun G) (syn_wmo z (syn_wbr (.cv x) G (.cv z)))
      (.all z (syn_wmo y (syn_wbr (.cv z) F (.cv y))))
      (syn_wmo y (syn_wex z (syn_wa (syn_wbr (.cv x) G (.cv z)) (syn_wbr (.cv z) F (.cv y)))))
      (syn_wfun F) p0000 p0002 p0003
  have p0005 :=
    @g_alrimiv (syn_wa (syn_wfun F) (syn_wfun G))
      (syn_wmo y (syn_wex z (syn_wa (syn_wbr (.cv x) G (.cv z)) (syn_wbr (.cv z) F (.cv y)))))
      x dv_cache_0007 p0004
  have p0006 :=
    @g_funopab
      (syn_wex z (syn_wa (syn_wbr (.cv x) G (.cv z)) (syn_wbr (.cv z) F (.cv y)))) x y
      dv_cache_0008
  have p0007 :=
    @g_sylibr (syn_wa (syn_wfun F) (syn_wfun G))
      (.all x (syn_wmo y
          (syn_wex z (syn_wa (syn_wbr (.cv x) G (.cv z)) (syn_wbr (.cv z) F (.cv y))))))
      (syn_wfun (syn_copab x y
          (syn_wex z (syn_wa (syn_wbr (.cv x) G (.cv z)) (syn_wbr (.cv z) F (.cv y))))))
      p0005 p0006
  have p0008 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_co x y z F G
      dv_cache_0009 dv_cache_0004 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0002
      dv_cache_0008 dv_cache_0013 dv_cache_0014
  have p0009 :=
    @g_funeqi (syn_ccom F G)
      (syn_copab x y
        (syn_wex z (syn_wa (syn_wbr (.cv x) G (.cv z)) (syn_wbr (.cv z) F (.cv y)))))
      p0008
  have p0010 :=
    @g_sylibr (syn_wa (syn_wfun F) (syn_wfun G))
      (syn_wfun (syn_copab x y
          (syn_wex z (syn_wa (syn_wbr (.cv x) G (.cv z)) (syn_wbr (.cv z) F (.cv y))))))
      (syn_wfun (syn_ccom F G)) p0007 p0009
  exact p0010

@[expose]
noncomputable def g_funres (A : Class) (F : Class) :
    Nominal.NPrf (.imp (syn_wfun F) (syn_wfun (syn_cres F A))) :=
  by
  have p0000 := @g_resss F A
  have p0001 := @g_funss (syn_cres F A) F
  have p0002 := Nominal.mp p0000 p0001
  exact p0002

@[expose]
noncomputable def g_funssres (F : Class) (G : Class) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wfun F) (syn_wss G F)) (.classEq (syn_cres F (syn_cdm G)) G)) :=
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
  have dv_cache_0004 : y ∉ ((syn_wss G F)).fv :=
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
  have dv_cache_0005 : x ∉ ((syn_cres F (syn_cdm G))).fv :=
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
  have dv_cache_0006 : y ∉ ((syn_cres F (syn_cdm G))).fv :=
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
  have dv_cache_0008 : x ∉ ((syn_wa (syn_wfun F) (syn_wss G F))).fv :=
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
  have dv_cache_0009 : y ∉ ((syn_wa (syn_wfun F) (syn_wss G F))).fv :=
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
  have p0000 := @g_ssel G F (syn_cop (.cv x) (.cv y))
  have p0001 :=
    @g_adantl (syn_wss G F)
      (.imp (.classMem (syn_cop (.cv x) (.cv y)) G) (.classMem (syn_cop (.cv x) (.cv y)) F))
      (syn_wfun F) p0000
  have p0002 := @g_opeldm (.cv x) (.cv y) G
  have p0003 :=
    @g_a1i (.imp (.classMem (syn_cop (.cv x) (.cv y)) G) (.classMem (.cv x) (syn_cdm G)))
      (syn_wa (syn_wfun F) (syn_wss G F)) p0002
  have p0004 :=
    @g_jcad (syn_wa (syn_wfun F) (syn_wss G F)) (.classMem (syn_cop (.cv x) (.cv y)) G)
      (.classMem (syn_cop (.cv x) (.cv y)) F) (.classMem (.cv x) (syn_cdm G)) p0001 p0003
  have p0005 := @g_funeu2 y (.cv x) (.cv y) F dv_cache_0001 dv_cache_0002
  have p0006 := @g_eldm2 y (.cv x) G dv_cache_0001 dv_cache_0003
  have p0007 :=
    @g_ancrd (syn_wss G F) (.classMem (syn_cop (.cv x) (.cv y)) G)
      (.classMem (syn_cop (.cv x) (.cv y)) F) p0000
  have p0008 :=
    @g_eximdv (syn_wss G F) (.classMem (syn_cop (.cv x) (.cv y)) G)
      (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) F) (.classMem (syn_cop (.cv x) (.cv y)) G))
      y dv_cache_0004 p0007
  have p0009 :=
    @g_syl5bi (.classMem (.cv x) (syn_cdm G))
      (syn_wex y (.classMem (syn_cop (.cv x) (.cv y)) G)) (syn_wss G F)
      (syn_wex y (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) F)
          (.classMem (syn_cop (.cv x) (.cv y)) G)))
      p0006 p0008
  have p0010 :=
    @g_imp (syn_wss G F) (.classMem (.cv x) (syn_cdm G))
      (syn_wex y (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) F)
          (.classMem (syn_cop (.cv x) (.cv y)) G)))
      p0009
  have p0011 :=
    @g_eupick (.classMem (syn_cop (.cv x) (.cv y)) F)
      (.classMem (syn_cop (.cv x) (.cv y)) G) y
  have p0012 :=
    @g_syl2an (syn_wa (syn_wfun F) (.classMem (syn_cop (.cv x) (.cv y)) F))
      (syn_weu y (.classMem (syn_cop (.cv x) (.cv y)) F))
      (syn_wex y (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) F)
          (.classMem (syn_cop (.cv x) (.cv y)) G)))
      (.imp (.classMem (syn_cop (.cv x) (.cv y)) F) (.classMem (syn_cop (.cv x) (.cv y)) G))
      (syn_wa (syn_wss G F) (.classMem (.cv x) (syn_cdm G))) p0005 p0010 p0011
  have p0013 :=
    @g_exp43 (syn_wfun F) (.classMem (syn_cop (.cv x) (.cv y)) F) (syn_wss G F)
      (.classMem (.cv x) (syn_cdm G))
      (.imp (.classMem (syn_cop (.cv x) (.cv y)) F) (.classMem (syn_cop (.cv x) (.cv y)) G))
      p0012
  have p0014 :=
    @g_com23 (syn_wfun F) (.classMem (syn_cop (.cv x) (.cv y)) F) (syn_wss G F)
      (.imp (.classMem (.cv x) (syn_cdm G)) (.imp (.classMem (syn_cop (.cv x) (.cv y)) F)
          (.classMem (syn_cop (.cv x) (.cv y)) G)))
      p0013
  have p0015 :=
    @g_imp (syn_wfun F) (syn_wss G F)
      (.imp (.classMem (syn_cop (.cv x) (.cv y)) F) (.imp (.classMem (.cv x) (syn_cdm G))
          (.imp (.classMem (syn_cop (.cv x) (.cv y)) F)
            (.classMem (syn_cop (.cv x) (.cv y)) G))))
      p0014
  have p0016 :=
    @g_com34 (syn_wa (syn_wfun F) (syn_wss G F)) (.classMem (syn_cop (.cv x) (.cv y)) F)
      (.classMem (.cv x) (syn_cdm G)) (.classMem (syn_cop (.cv x) (.cv y)) F)
      (.classMem (syn_cop (.cv x) (.cv y)) G) p0015
  have p0017 :=
    @g_pm2_43d (syn_wa (syn_wfun F) (syn_wss G F)) (.classMem (syn_cop (.cv x) (.cv y)) F)
      (.imp (.classMem (.cv x) (syn_cdm G)) (.classMem (syn_cop (.cv x) (.cv y)) G)) p0016
  have p0018 :=
    @g_imp3a (syn_wa (syn_wfun F) (syn_wss G F)) (.classMem (syn_cop (.cv x) (.cv y)) F)
      (.classMem (.cv x) (syn_cdm G)) (.classMem (syn_cop (.cv x) (.cv y)) G) p0017
  have p0019 :=
    @g_impbid (syn_wa (syn_wfun F) (syn_wss G F)) (.classMem (syn_cop (.cv x) (.cv y)) G)
      (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) F) (.classMem (.cv x) (syn_cdm G)))
      p0004 p0018
  have p0020 := @g_opelres (.cv x) (.cv y) F (syn_cdm G)
  have p0021 :=
    @g_syl6rbbr (syn_wa (syn_wfun F) (syn_wss G F))
      (.classMem (syn_cop (.cv x) (.cv y)) G)
      (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) F) (.classMem (.cv x) (syn_cdm G)))
      (.classMem (syn_cop (.cv x) (.cv y)) (syn_cres F (syn_cdm G))) p0019 p0020
  have p0022 :=
    @g_eqrelrdv (syn_wa (syn_wfun F) (syn_wss G F)) x y (syn_cres F (syn_cdm G)) G
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

@[expose]
noncomputable def g_funun (F : Class) (G : Class) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wa (syn_wfun F) (syn_wfun G))
          (.classEq (syn_cin (syn_cdm F) (syn_cdm G)) (syn_c0))) (syn_wfun (syn_cun F G))) :=
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
  have dv_cache_0001 : x ∉ ((syn_cdm F)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, fresh_x_not_F,
          not_false_eq_true])
  have dv_cache_0002 : x ∉ ((syn_cdm G)).fv :=
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
      ((syn_wa (syn_wa (syn_wfun F) (syn_wfun G))
          (.classEq (syn_cin (syn_cdm F) (syn_cdm G)) (syn_c0)))).fv :=
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
      ((syn_wa (syn_wa (syn_wfun F) (syn_wfun G))
          (.classEq (syn_cin (syn_cdm F) (syn_cdm G)) (syn_c0)))).fv :=
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
      ((syn_wa (syn_wa (syn_wfun F) (syn_wfun G))
          (.classEq (syn_cin (syn_cdm F) (syn_cdm G)) (syn_c0)))).fv :=
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
  have dv_cache_0015 : x ∉ ((syn_cun F G)).fv :=
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
  have dv_cache_0016 : y ∉ ((syn_cun F G)).fv :=
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
  have dv_cache_0017 : z ∉ ((syn_cun F G)).fv :=
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
  have p0000 := @g_elun (syn_cop (.cv x) (.cv y)) F G
  have p0001 := @g_elun (syn_cop (.cv x) (.cv z)) F G
  have p0002 :=
    @g_anbi12i (.classMem (syn_cop (.cv x) (.cv y)) (syn_cun F G))
      (syn_wo (.classMem (syn_cop (.cv x) (.cv y)) F) (.classMem (syn_cop (.cv x) (.cv y)) G))
      (.classMem (syn_cop (.cv x) (.cv z)) (syn_cun F G))
      (syn_wo (.classMem (syn_cop (.cv x) (.cv z)) F) (.classMem (syn_cop (.cv x) (.cv z)) G))
      p0000 p0001
  have p0003 :=
    @g_anddi (.classMem (syn_cop (.cv x) (.cv y)) F)
      (.classMem (syn_cop (.cv x) (.cv y)) G) (.classMem (syn_cop (.cv x) (.cv z)) F)
      (.classMem (syn_cop (.cv x) (.cv z)) G)
  have p0004 :=
    @g_bitri
      (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) (syn_cun F G))
        (.classMem (syn_cop (.cv x) (.cv z)) (syn_cun F G)))
      (syn_wa (syn_wo (.classMem (syn_cop (.cv x) (.cv y)) F)
          (.classMem (syn_cop (.cv x) (.cv y)) G))
        (syn_wo (.classMem (syn_cop (.cv x) (.cv z)) F)
          (.classMem (syn_cop (.cv x) (.cv z)) G)))
      (syn_wo (syn_wo (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) F)
            (.classMem (syn_cop (.cv x) (.cv z)) F))
          (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) F)
            (.classMem (syn_cop (.cv x) (.cv z)) G))) (syn_wo
          (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) G)
            (.classMem (syn_cop (.cv x) (.cv z)) F))
          (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) G)
            (.classMem (syn_cop (.cv x) (.cv z)) G))))
      p0002 p0003
  have p0005 :=
    @g_sp (.imp (.classMem (.cv x) (syn_cdm F)) (.neg (.classMem (.cv x) (syn_cdm G)))) x
  have p0006 := @g_disj1 x (syn_cdm F) (syn_cdm G) dv_cache_0001 dv_cache_0002
  have p0007 := @g_imnan (.classMem (.cv x) (syn_cdm F)) (.classMem (.cv x) (syn_cdm G))
  have p0008 :=
    @g_bicomi
      (.imp (.classMem (.cv x) (syn_cdm F)) (.neg (.classMem (.cv x) (syn_cdm G))))
      (.neg (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (.cv x) (syn_cdm G))))
      p0007
  have p0009 :=
    @g_n_3imtr4i
      (.all x (.imp (.classMem (.cv x) (syn_cdm F)) (.neg (.classMem (.cv x) (syn_cdm G)))))
      (.imp (.classMem (.cv x) (syn_cdm F)) (.neg (.classMem (.cv x) (syn_cdm G))))
      (.classEq (syn_cin (syn_cdm F) (syn_cdm G)) (syn_c0))
      (.neg (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (.cv x) (syn_cdm G))))
      p0005 p0006 p0008
  have p0010 := @g_opeldm (.cv x) (.cv y) F
  have p0011 := @g_opeldm (.cv x) (.cv z) G
  have p0012 :=
    @g_anim12i (.classMem (syn_cop (.cv x) (.cv y)) F) (.classMem (.cv x) (syn_cdm F))
      (.classMem (syn_cop (.cv x) (.cv z)) G) (.classMem (.cv x) (syn_cdm G)) p0010 p0011
  have p0013 :=
    @g_nsyl (.classEq (syn_cin (syn_cdm F) (syn_cdm G)) (syn_c0))
      (syn_wa (.classMem (.cv x) (syn_cdm F)) (.classMem (.cv x) (syn_cdm G)))
      (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) F) (.classMem (syn_cop (.cv x) (.cv z)) G))
      p0009 p0012
  have p0014 :=
    @g_orel2
      (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) F) (.classMem (syn_cop (.cv x) (.cv z)) G))
      (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) F) (.classMem (syn_cop (.cv x) (.cv z)) F))
  have p0015 :=
    @g_syl (.classEq (syn_cin (syn_cdm F) (syn_cdm G)) (syn_c0))
      (.neg (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) F)
          (.classMem (syn_cop (.cv x) (.cv z)) G)))
      (.imp (syn_wo (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) F)
            (.classMem (syn_cop (.cv x) (.cv z)) F))
          (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) F)
            (.classMem (syn_cop (.cv x) (.cv z)) G)))
        (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) F)
          (.classMem (syn_cop (.cv x) (.cv z)) F)))
      p0013 p0014
  have p0016 :=
    @g_sp (.imp (.classMem (.cv x) (syn_cdm G)) (.neg (.classMem (.cv x) (syn_cdm F)))) x
  have p0017 := @g_incom (syn_cdm F) (syn_cdm G)
  have p0018 :=
    @g_eqeq1i (syn_cin (syn_cdm F) (syn_cdm G)) (syn_cin (syn_cdm G) (syn_cdm F)) (syn_c0)
      p0017
  have p0019 := @g_disj1 x (syn_cdm G) (syn_cdm F) dv_cache_0002 dv_cache_0001
  have p0020 :=
    @g_bitri (.classEq (syn_cin (syn_cdm F) (syn_cdm G)) (syn_c0))
      (.classEq (syn_cin (syn_cdm G) (syn_cdm F)) (syn_c0))
      (.all x (.imp (.classMem (.cv x) (syn_cdm G)) (.neg (.classMem (.cv x) (syn_cdm F)))))
      p0018 p0019
  have p0021 := @g_imnan (.classMem (.cv x) (syn_cdm G)) (.classMem (.cv x) (syn_cdm F))
  have p0022 :=
    @g_bicomi
      (.imp (.classMem (.cv x) (syn_cdm G)) (.neg (.classMem (.cv x) (syn_cdm F))))
      (.neg (syn_wa (.classMem (.cv x) (syn_cdm G)) (.classMem (.cv x) (syn_cdm F))))
      p0021
  have p0023 :=
    @g_n_3imtr4i
      (.all x (.imp (.classMem (.cv x) (syn_cdm G)) (.neg (.classMem (.cv x) (syn_cdm F)))))
      (.imp (.classMem (.cv x) (syn_cdm G)) (.neg (.classMem (.cv x) (syn_cdm F))))
      (.classEq (syn_cin (syn_cdm F) (syn_cdm G)) (syn_c0))
      (.neg (syn_wa (.classMem (.cv x) (syn_cdm G)) (.classMem (.cv x) (syn_cdm F))))
      p0016 p0020 p0022
  have p0024 := @g_opeldm (.cv x) (.cv y) G
  have p0025 := @g_opeldm (.cv x) (.cv z) F
  have p0026 :=
    @g_anim12i (.classMem (syn_cop (.cv x) (.cv y)) G) (.classMem (.cv x) (syn_cdm G))
      (.classMem (syn_cop (.cv x) (.cv z)) F) (.classMem (.cv x) (syn_cdm F)) p0024 p0025
  have p0027 :=
    @g_nsyl (.classEq (syn_cin (syn_cdm F) (syn_cdm G)) (syn_c0))
      (syn_wa (.classMem (.cv x) (syn_cdm G)) (.classMem (.cv x) (syn_cdm F)))
      (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) G) (.classMem (syn_cop (.cv x) (.cv z)) F))
      p0023 p0026
  have p0028 :=
    @g_orel1
      (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) G) (.classMem (syn_cop (.cv x) (.cv z)) F))
      (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) G) (.classMem (syn_cop (.cv x) (.cv z)) G))
  have p0029 :=
    @g_syl (.classEq (syn_cin (syn_cdm F) (syn_cdm G)) (syn_c0))
      (.neg (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) G)
          (.classMem (syn_cop (.cv x) (.cv z)) F)))
      (.imp (syn_wo (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) G)
            (.classMem (syn_cop (.cv x) (.cv z)) F))
          (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) G)
            (.classMem (syn_cop (.cv x) (.cv z)) G)))
        (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) G)
          (.classMem (syn_cop (.cv x) (.cv z)) G)))
      p0027 p0028
  have p0030 :=
    @g_orim12d (.classEq (syn_cin (syn_cdm F) (syn_cdm G)) (syn_c0))
      (syn_wo (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) F)
          (.classMem (syn_cop (.cv x) (.cv z)) F))
        (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) F)
          (.classMem (syn_cop (.cv x) (.cv z)) G)))
      (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) F) (.classMem (syn_cop (.cv x) (.cv z)) F))
      (syn_wo (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) G)
          (.classMem (syn_cop (.cv x) (.cv z)) F))
        (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) G)
          (.classMem (syn_cop (.cv x) (.cv z)) G)))
      (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) G) (.classMem (syn_cop (.cv x) (.cv z)) G))
      p0015 p0029
  have p0031 :=
    @g_syl5bi
      (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) (syn_cun F G))
        (.classMem (syn_cop (.cv x) (.cv z)) (syn_cun F G)))
      (syn_wo (syn_wo (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) F)
            (.classMem (syn_cop (.cv x) (.cv z)) F))
          (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) F)
            (.classMem (syn_cop (.cv x) (.cv z)) G))) (syn_wo
          (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) G)
            (.classMem (syn_cop (.cv x) (.cv z)) F))
          (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) G)
            (.classMem (syn_cop (.cv x) (.cv z)) G))))
      (.classEq (syn_cin (syn_cdm F) (syn_cdm G)) (syn_c0))
      (syn_wo (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) F)
          (.classMem (syn_cop (.cv x) (.cv z)) F))
        (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) G)
          (.classMem (syn_cop (.cv x) (.cv z)) G)))
      p0004 p0030
  have p0032 :=
    @g_dffun4 x y z F dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
      dv_cache_0007 dv_cache_0008
  have p0033 :=
    @g_biimpi (syn_wfun F)
      (.all x (.all y (.all z (.imp (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) F)
                (.classMem (syn_cop (.cv x) (.cv z)) F)) (.objEq y z)))))
      p0032
  have p0034 :=
    @g_n_19_21bi (syn_wfun F)
      (.all y (.all z (.imp (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) F)
              (.classMem (syn_cop (.cv x) (.cv z)) F)) (.objEq y z))))
      x p0033
  have p0035 :=
    @g_n_19_21bbi (syn_wfun F)
      (.imp (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) F)
          (.classMem (syn_cop (.cv x) (.cv z)) F)) (.objEq y z))
      y z p0034
  have p0036 :=
    @g_dffun4 x y z G dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0006
      dv_cache_0007 dv_cache_0008
  have p0037 :=
    @g_biimpi (syn_wfun G)
      (.all x (.all y (.all z (.imp (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) G)
                (.classMem (syn_cop (.cv x) (.cv z)) G)) (.objEq y z)))))
      p0036
  have p0038 :=
    @g_n_19_21bi (syn_wfun G)
      (.all y (.all z (.imp (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) G)
              (.classMem (syn_cop (.cv x) (.cv z)) G)) (.objEq y z))))
      x p0037
  have p0039 :=
    @g_n_19_21bbi (syn_wfun G)
      (.imp (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) G)
          (.classMem (syn_cop (.cv x) (.cv z)) G)) (.objEq y z))
      y z p0038
  have p0040 :=
    @g_jaao (syn_wfun F)
      (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) F) (.classMem (syn_cop (.cv x) (.cv z)) F))
      (.objEq y z) (syn_wfun G)
      (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) G) (.classMem (syn_cop (.cv x) (.cv z)) G))
      p0035 p0039
  have p0041 :=
    @g_sylan9r (.classEq (syn_cin (syn_cdm F) (syn_cdm G)) (syn_c0))
      (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) (syn_cun F G))
        (.classMem (syn_cop (.cv x) (.cv z)) (syn_cun F G)))
      (syn_wo (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) F)
          (.classMem (syn_cop (.cv x) (.cv z)) F))
        (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) G)
          (.classMem (syn_cop (.cv x) (.cv z)) G)))
      (syn_wa (syn_wfun F) (syn_wfun G)) (.objEq y z) p0031 p0040
  have p0042 :=
    @g_alrimiv
      (syn_wa (syn_wa (syn_wfun F) (syn_wfun G))
        (.classEq (syn_cin (syn_cdm F) (syn_cdm G)) (syn_c0)))
      (.imp (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) (syn_cun F G))
          (.classMem (syn_cop (.cv x) (.cv z)) (syn_cun F G))) (.objEq y z))
      z dv_cache_0012 p0041
  have p0043 :=
    @g_alrimivv
      (syn_wa (syn_wa (syn_wfun F) (syn_wfun G))
        (.classEq (syn_cin (syn_cdm F) (syn_cdm G)) (syn_c0)))
      (.all z (.imp (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) (syn_cun F G))
            (.classMem (syn_cop (.cv x) (.cv z)) (syn_cun F G))) (.objEq y z)))
      x y dv_cache_0013 dv_cache_0014 p0042
  have p0044 :=
    @g_dffun4 x y z (syn_cun F G) dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0006
      dv_cache_0007 dv_cache_0008
  have p0045 :=
    @g_sylibr
      (syn_wa (syn_wa (syn_wfun F) (syn_wfun G))
        (.classEq (syn_cin (syn_cdm F) (syn_cdm G)) (syn_c0)))
      (.all x (.all y (.all z (.imp (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) (syn_cun F G))
                (.classMem (syn_cop (.cv x) (.cv z)) (syn_cun F G))) (.objEq y z)))))
      (syn_wfun (syn_cun F G)) p0043 p0044
  exact p0045

@[expose]
noncomputable def g_funsn (A : Class) (B : Class) :
    Nominal.NPrf (syn_wfun (syn_csn (syn_cop A B))) :=
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
  have dv_cache_0001 : x ∉ ((syn_csn (syn_cop A B))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union,
          fresh_x_not_A, fresh_x_not_B, or_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((syn_csn (syn_cop A B))).fv :=
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
    @g_dffun6 x y (syn_csn (syn_cop A B)) dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0001 := @g_moeq y B dv_cache_0004
  have p0002 := @g_a1i (syn_wmo y (.classEq (.cv y) B)) (.classEq (.cv x) A) p0001
  have p0003 := (Nominal.biimpRefl (syn_wbr (.cv x) (syn_csn (syn_cop A B)) (.cv y)))
  have p0004 := @g_vex x
  have p0005 := @g_vex y
  have p0006 := @g_opex (.cv x) (.cv y) p0004 p0005
  have p0007 := @g_elsnc (syn_cop (.cv x) (.cv y)) (syn_cop A B) p0006
  have p0008 := @g_opth (.cv x) (.cv y) A B
  have p0009 :=
    @g_bitri (.classMem (syn_cop (.cv x) (.cv y)) (syn_csn (syn_cop A B)))
      (.classEq (syn_cop (.cv x) (.cv y)) (syn_cop A B))
      (syn_wa (.classEq (.cv x) A) (.classEq (.cv y) B)) p0007 p0008
  have p0010 :=
    @g_bitri (syn_wbr (.cv x) (syn_csn (syn_cop A B)) (.cv y))
      (.classMem (syn_cop (.cv x) (.cv y)) (syn_csn (syn_cop A B)))
      (syn_wa (.classEq (.cv x) A) (.classEq (.cv y) B)) p0003 p0009
  have p0011 :=
    @g_mobii (syn_wbr (.cv x) (syn_csn (syn_cop A B)) (.cv y))
      (syn_wa (.classEq (.cv x) A) (.classEq (.cv y) B)) y p0010
  have p0012 := @g_moanimv (.classEq (.cv x) A) (.classEq (.cv y) B) y dv_cache_0005
  have p0013 :=
    @g_bitri (syn_wmo y (syn_wbr (.cv x) (syn_csn (syn_cop A B)) (.cv y)))
      (syn_wmo y (syn_wa (.classEq (.cv x) A) (.classEq (.cv y) B)))
      (.imp (.classEq (.cv x) A) (syn_wmo y (.classEq (.cv y) B))) p0011 p0012
  have p0014 :=
    @g_mpbir (syn_wmo y (syn_wbr (.cv x) (syn_csn (syn_cop A B)) (.cv y)))
      (.imp (.classEq (.cv x) A) (syn_wmo y (.classEq (.cv y) B))) p0002 p0013
  have p0015 :=
    @g_mpgbir (syn_wfun (syn_csn (syn_cop A B)))
      (syn_wmo y (syn_wbr (.cv x) (syn_csn (syn_cop A B)) (.cv y))) x p0000 p0014
  exact p0015

@[expose]
noncomputable def g_fnsn (A : Class) (B : Class)
    (_hyp_fnsn_1 : Nominal.NPrf (.classMem A (syn_cvv)))
    (hyp_fnsn_2 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf (syn_wfn (syn_csn (syn_cop A B)) (syn_csn A)) :=
  by
  have p0000 := @g_funsn A B
  have p0001 := @g_dmsnop A B hyp_fnsn_2
  have p0002 := (Nominal.biimpRefl (syn_wfn (syn_csn (syn_cop A B)) (syn_csn A)))
  have p0003 :=
    @g_mpbir2an (syn_wfn (syn_csn (syn_cop A B)) (syn_csn A))
      (syn_wfun (syn_csn (syn_cop A B)))
      (.classEq (syn_cdm (syn_csn (syn_cop A B))) (syn_csn A)) p0000 p0001 p0002
  exact p0003

@[expose]
noncomputable def g_fun0 : Nominal.NPrf (syn_wfun (syn_c0)) :=
  by
  have p0000 := @g_co01 (syn_ccnv (syn_c0))
  have p0001 := @g_n_0ss (syn_cid)
  have p0002 :=
    @g_eqsstri (syn_ccom (syn_c0) (syn_ccnv (syn_c0))) (syn_c0) (syn_cid) p0000 p0001
  have p0003 := (Nominal.biimpRefl (syn_wfun (syn_c0)))
  have p0004 :=
    @g_mpbir (syn_wfun (syn_c0))
      (syn_wss (syn_ccom (syn_c0) (syn_ccnv (syn_c0))) (syn_cid)) p0002 p0003
  exact p0004

@[expose]
noncomputable def g_funcnv2 (x : Var) (y : Var) (A : Class) (dv_A_x : x ∉ A.fv)
    (dv_A_y : y ∉ A.fv) (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (syn_wb (syn_wfun (syn_ccnv A)) (.all y (syn_wmo x (syn_wbr (.cv x) A (.cv y))))) :=
  by
  have dv_cache_0001 : y ∉ ((syn_ccnv A)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, dv_A_y,
          not_false_eq_true])
  have dv_cache_0002 : x ∉ ((syn_ccnv A)).fv :=
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
  have p0000 := @g_dffun6 y x (syn_ccnv A) dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0001 := @g_brcnv (.cv y) (.cv x) A
  have p0002 :=
    @g_mobii (syn_wbr (.cv y) (syn_ccnv A) (.cv x)) (syn_wbr (.cv x) A (.cv y)) x p0001
  have p0003 :=
    @g_albii (syn_wmo x (syn_wbr (.cv y) (syn_ccnv A) (.cv x)))
      (syn_wmo x (syn_wbr (.cv x) A (.cv y))) y p0002
  have p0004 :=
    @g_bitri (syn_wfun (syn_ccnv A))
      (.all y (syn_wmo x (syn_wbr (.cv y) (syn_ccnv A) (.cv x))))
      (.all y (syn_wmo x (syn_wbr (.cv x) A (.cv y)))) p0000 p0003
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

@[expose]
noncomputable def g_fununi (A : Class) (f : Var) (g : Var) (dv_A_f : f ∉ A.fv)
    (dv_A_g : g ∉ A.fv) (dv_f_g : f ≠ g) :
    Nominal.NPrf
      (.imp (syn_wral f A (syn_wa (syn_wfun (.cv f))
            (syn_wral g A (syn_wo (syn_wss (.cv f) (.cv g)) (syn_wss (.cv g) (.cv f))))))
        (syn_wfun (syn_cuni A))) :=
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
  have dv_cache_0001 : g ∉ ((syn_wfun (.cv f))).fv := by
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
      ((syn_wa (syn_wfun (.cv w))
          (syn_wo (syn_wss (.cv w) (.cv g)) (syn_wss (.cv g) (.cv w))))).fv :=
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
      ((syn_wa (syn_wfun (.cv w))
          (syn_wo (syn_wss (.cv w) (.cv g)) (syn_wss (.cv g) (.cv w))))).fv :=
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
      ((syn_wa (syn_wfun (.cv f))
          (syn_wo (syn_wss (.cv f) (.cv g)) (syn_wss (.cv g) (.cv f))))).fv :=
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
      ((syn_wa (syn_wfun (.cv w))
          (syn_wo (syn_wss (.cv w) (.cv v)) (syn_wss (.cv v) (.cv w))))).fv :=
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
      ((syn_wa (syn_wfun (.cv f))
          (syn_wo (syn_wss (.cv w) (.cv f)) (syn_wss (.cv f) (.cv w))))).fv :=
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
      ((syn_wa (syn_wfun (.cv f))
          (syn_wo (syn_wss (.cv w) (.cv f)) (syn_wss (.cv f) (.cv w))))).fv :=
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
      ((syn_wa (syn_wfun (.cv v))
          (syn_wo (syn_wss (.cv w) (.cv v)) (syn_wss (.cv v) (.cv w))))).fv :=
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
  have dv_cache_0026 : w ∉ ((syn_cop (.cv x) (.cv y))).fv :=
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
  have dv_cache_0027 : v ∉ ((syn_cop (.cv x) (.cv z))).fv :=
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
      ((syn_wa (.classMem (syn_cop (.cv x) (.cv y)) (.cv w)) (.classMem (.cv w) A))).fv :=
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
      ((syn_wa (.classMem (syn_cop (.cv x) (.cv z)) (.cv v)) (.classMem (.cv v) A))).fv :=
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
      ((syn_wral f A (syn_wral g A (syn_wa (syn_wfun (.cv f))
              (syn_wo (syn_wss (.cv f) (.cv g)) (syn_wss (.cv g) (.cv f))))))).fv :=
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
      ((syn_wral f A (syn_wral g A (syn_wa (syn_wfun (.cv f))
              (syn_wo (syn_wss (.cv f) (.cv g)) (syn_wss (.cv g) (.cv f))))))).fv :=
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
      ((syn_wral f A (syn_wral g A (syn_wa (syn_wfun (.cv f))
              (syn_wo (syn_wss (.cv f) (.cv g)) (syn_wss (.cv g) (.cv f))))))).fv :=
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
  have dv_cache_0036 : x ∉ ((syn_cuni A)).fv :=
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
  have dv_cache_0037 : y ∉ ((syn_cuni A)).fv :=
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
  have dv_cache_0038 : z ∉ ((syn_cuni A)).fv :=
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
    @g_r19_28av (syn_wfun (.cv f))
      (syn_wo (syn_wss (.cv f) (.cv g)) (syn_wss (.cv g) (.cv f))) g A dv_cache_0001
  have p0001 :=
    @g_ralimi
      (syn_wa (syn_wfun (.cv f))
        (syn_wral g A (syn_wo (syn_wss (.cv f) (.cv g)) (syn_wss (.cv g) (.cv f)))))
      (syn_wral g A (syn_wa (syn_wfun (.cv f))
          (syn_wo (syn_wss (.cv f) (.cv g)) (syn_wss (.cv g) (.cv f)))))
      f A p0000
  have p0002 := @g_ssel (.cv w) (.cv v) (syn_cop (.cv x) (.cv y))
  have p0003 :=
    @g_anim1d (syn_wss (.cv w) (.cv v)) (.classMem (syn_cop (.cv x) (.cv y)) (.cv w))
      (.classMem (syn_cop (.cv x) (.cv y)) (.cv v))
      (.classMem (syn_cop (.cv x) (.cv z)) (.cv v)) p0002
  have p0004 :=
    @g_dffun4 x y z (.cv v) dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
  have p0005 :=
    @g_sp
      (.imp (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) (.cv v))
          (.classMem (syn_cop (.cv x) (.cv z)) (.cv v))) (.objEq y z))
      z
  have p0006 :=
    @g_sps
      (.all z (.imp (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) (.cv v))
            (.classMem (syn_cop (.cv x) (.cv z)) (.cv v))) (.objEq y z)))
      (.imp (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) (.cv v))
          (.classMem (syn_cop (.cv x) (.cv z)) (.cv v))) (.objEq y z))
      y p0005
  have p0007 :=
    @g_sps
      (.all y (.all z (.imp (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) (.cv v))
              (.classMem (syn_cop (.cv x) (.cv z)) (.cv v))) (.objEq y z))))
      (.imp (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) (.cv v))
          (.classMem (syn_cop (.cv x) (.cv z)) (.cv v))) (.objEq y z))
      x p0006
  have p0008 :=
    @g_sylbi (syn_wfun (.cv v))
      (.all x (.all y (.all z (.imp (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) (.cv v))
                (.classMem (syn_cop (.cv x) (.cv z)) (.cv v))) (.objEq y z)))))
      (.imp (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) (.cv v))
          (.classMem (syn_cop (.cv x) (.cv z)) (.cv v))) (.objEq y z))
      p0004 p0007
  have p0009 :=
    @g_syl9r (syn_wss (.cv w) (.cv v))
      (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) (.cv w))
        (.classMem (syn_cop (.cv x) (.cv z)) (.cv v)))
      (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) (.cv v))
        (.classMem (syn_cop (.cv x) (.cv z)) (.cv v)))
      (syn_wfun (.cv v)) (.objEq y z) p0003 p0008
  have p0010 :=
    @g_adantl (syn_wfun (.cv v))
      (.imp (syn_wss (.cv w) (.cv v)) (.imp
          (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) (.cv w))
            (.classMem (syn_cop (.cv x) (.cv z)) (.cv v))) (.objEq y z)))
      (syn_wfun (.cv w)) p0009
  have p0011 := @g_ssel (.cv v) (.cv w) (syn_cop (.cv x) (.cv z))
  have p0012 :=
    @g_anim2d (syn_wss (.cv v) (.cv w)) (.classMem (syn_cop (.cv x) (.cv z)) (.cv v))
      (.classMem (syn_cop (.cv x) (.cv z)) (.cv w))
      (.classMem (syn_cop (.cv x) (.cv y)) (.cv w)) p0011
  have p0013 :=
    @g_dffun4 x y z (.cv w) dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0005
      dv_cache_0006 dv_cache_0007
  have p0014 :=
    @g_sp
      (.imp (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) (.cv w))
          (.classMem (syn_cop (.cv x) (.cv z)) (.cv w))) (.objEq y z))
      z
  have p0015 :=
    @g_sps
      (.all z (.imp (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) (.cv w))
            (.classMem (syn_cop (.cv x) (.cv z)) (.cv w))) (.objEq y z)))
      (.imp (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) (.cv w))
          (.classMem (syn_cop (.cv x) (.cv z)) (.cv w))) (.objEq y z))
      y p0014
  have p0016 :=
    @g_sps
      (.all y (.all z (.imp (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) (.cv w))
              (.classMem (syn_cop (.cv x) (.cv z)) (.cv w))) (.objEq y z))))
      (.imp (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) (.cv w))
          (.classMem (syn_cop (.cv x) (.cv z)) (.cv w))) (.objEq y z))
      x p0015
  have p0017 :=
    @g_sylbi (syn_wfun (.cv w))
      (.all x (.all y (.all z (.imp (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) (.cv w))
                (.classMem (syn_cop (.cv x) (.cv z)) (.cv w))) (.objEq y z)))))
      (.imp (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) (.cv w))
          (.classMem (syn_cop (.cv x) (.cv z)) (.cv w))) (.objEq y z))
      p0013 p0016
  have p0018 :=
    @g_syl9r (syn_wss (.cv v) (.cv w))
      (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) (.cv w))
        (.classMem (syn_cop (.cv x) (.cv z)) (.cv v)))
      (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) (.cv w))
        (.classMem (syn_cop (.cv x) (.cv z)) (.cv w)))
      (syn_wfun (.cv w)) (.objEq y z) p0012 p0017
  have p0019 :=
    @g_adantr (syn_wfun (.cv w))
      (.imp (syn_wss (.cv v) (.cv w)) (.imp
          (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) (.cv w))
            (.classMem (syn_cop (.cv x) (.cv z)) (.cv v))) (.objEq y z)))
      (syn_wfun (.cv v)) p0018
  have p0020 :=
    @g_jaod (syn_wa (syn_wfun (.cv w)) (syn_wfun (.cv v))) (syn_wss (.cv w) (.cv v))
      (.imp (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) (.cv w))
          (.classMem (syn_cop (.cv x) (.cv z)) (.cv v))) (.objEq y z))
      (syn_wss (.cv v) (.cv w)) p0010 p0019
  have p0021 :=
    @g_imp (syn_wa (syn_wfun (.cv w)) (syn_wfun (.cv v)))
      (syn_wo (syn_wss (.cv w) (.cv v)) (syn_wss (.cv v) (.cv w)))
      (.imp (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) (.cv w))
          (.classMem (syn_cop (.cv x) (.cv z)) (.cv v))) (.objEq y z))
      p0020
  have p0022 :=
    @g_ralimi
      (syn_wa (syn_wa (syn_wfun (.cv w)) (syn_wfun (.cv v)))
        (syn_wo (syn_wss (.cv w) (.cv v)) (syn_wss (.cv v) (.cv w))))
      (.imp (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) (.cv w))
          (.classMem (syn_cop (.cv x) (.cv z)) (.cv v))) (.objEq y z))
      v A p0021
  have p0023 :=
    @g_ralimi
      (syn_wral v A (syn_wa (syn_wa (syn_wfun (.cv w)) (syn_wfun (.cv v)))
          (syn_wo (syn_wss (.cv w) (.cv v)) (syn_wss (.cv v) (.cv w)))))
      (syn_wral v A (.imp (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) (.cv w))
            (.classMem (syn_cop (.cv x) (.cv z)) (.cv v))) (.objEq y z)))
      w A p0022
  have p0024 := @g_funeq (.cv f) (.cv w)
  have p0025 := @g_sseq1 (.cv f) (.cv w) (.cv g)
  have p0026 := @g_sseq2 (.cv f) (.cv w) (.cv g)
  have p0027_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq f w) (syn_wb (syn_wss (.cv f) (.cv g)) (syn_wss (.cv w) (.cv g)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wss syn_cin syn_ccompl syn_cnin syn_wnan syn_wa
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0025
  have p0027_e01_recanon :
    Nominal.NPrf
      (.imp (.objEq f w) (syn_wb (syn_wss (.cv g) (.cv f)) (syn_wss (.cv g) (.cv w)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wss syn_cin syn_ccompl syn_cnin syn_wnan syn_wa
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0026
  have p0027 :=
    @g_orbi12d (.objEq f w) (syn_wss (.cv f) (.cv g)) (syn_wss (.cv w) (.cv g))
      (syn_wss (.cv g) (.cv f)) (syn_wss (.cv g) (.cv w)) p0027_e00_recanon
      p0027_e01_recanon
  have p0028_e00_recanon :
    Nominal.NPrf (.imp (.objEq f w) (syn_wb (syn_wfun (.cv f)) (syn_wfun (.cv w)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wfun syn_wss syn_cin syn_ccompl syn_cnin syn_wnan syn_wa
          syn_ccom syn_copab syn_wex syn_ccnv syn_cid
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0024
  have p0028 :=
    @g_anbi12d (.objEq f w) (syn_wfun (.cv f)) (syn_wfun (.cv w))
      (syn_wo (syn_wss (.cv f) (.cv g)) (syn_wss (.cv g) (.cv f)))
      (syn_wo (syn_wss (.cv w) (.cv g)) (syn_wss (.cv g) (.cv w))) p0028_e00_recanon p0027
  have p0029 := @g_sseq2 (.cv g) (.cv v) (.cv w)
  have p0030 := @g_sseq1 (.cv g) (.cv v) (.cv w)
  have p0031_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq g v) (syn_wb (syn_wss (.cv w) (.cv g)) (syn_wss (.cv w) (.cv v)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wss syn_cin syn_ccompl syn_cnin syn_wnan syn_wa
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0029
  have p0031_e01_recanon :
    Nominal.NPrf
      (.imp (.objEq g v) (syn_wb (syn_wss (.cv g) (.cv w)) (syn_wss (.cv v) (.cv w)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wss syn_cin syn_ccompl syn_cnin syn_wnan syn_wa
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0030
  have p0031 :=
    @g_orbi12d (.objEq g v) (syn_wss (.cv w) (.cv g)) (syn_wss (.cv w) (.cv v))
      (syn_wss (.cv g) (.cv w)) (syn_wss (.cv v) (.cv w)) p0031_e00_recanon
      p0031_e01_recanon
  have p0032 :=
    @g_anbi2d (.objEq g v) (syn_wo (syn_wss (.cv w) (.cv g)) (syn_wss (.cv g) (.cv w)))
      (syn_wo (syn_wss (.cv w) (.cv v)) (syn_wss (.cv v) (.cv w))) (syn_wfun (.cv w))
      p0031
  have p0033 :=
    @g_cbvral2v
      (syn_wa (syn_wfun (.cv f)) (syn_wo (syn_wss (.cv f) (.cv g)) (syn_wss (.cv g) (.cv f))))
      (syn_wa (syn_wfun (.cv w)) (syn_wo (syn_wss (.cv w) (.cv v)) (syn_wss (.cv v) (.cv w))))
      (syn_wa (syn_wfun (.cv w)) (syn_wo (syn_wss (.cv w) (.cv g)) (syn_wss (.cv g) (.cv w))))
      f g w v A A dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0011 dv_cache_0014
      dv_cache_0012 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019
      dv_cache_0020 p0028 p0032
  have p0034 :=
    @g_ralcom
      (syn_wa (syn_wfun (.cv f)) (syn_wo (syn_wss (.cv f) (.cv g)) (syn_wss (.cv g) (.cv f))))
      f g A A dv_cache_0014 dv_cache_0011 dv_cache_0019
  have p0035 := @g_orcom (syn_wss (.cv f) (.cv g)) (syn_wss (.cv g) (.cv f))
  have p0036 := @g_sseq1 (.cv g) (.cv w) (.cv f)
  have p0037 := @g_sseq2 (.cv g) (.cv w) (.cv f)
  have p0038_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq g w) (syn_wb (syn_wss (.cv g) (.cv f)) (syn_wss (.cv w) (.cv f)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wss syn_cin syn_ccompl syn_cnin syn_wnan syn_wa
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0036
  have p0038_e01_recanon :
    Nominal.NPrf
      (.imp (.objEq g w) (syn_wb (syn_wss (.cv f) (.cv g)) (syn_wss (.cv f) (.cv w)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wss syn_cin syn_ccompl syn_cnin syn_wnan syn_wa
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0037
  have p0038 :=
    @g_orbi12d (.objEq g w) (syn_wss (.cv g) (.cv f)) (syn_wss (.cv w) (.cv f))
      (syn_wss (.cv f) (.cv g)) (syn_wss (.cv f) (.cv w)) p0038_e00_recanon
      p0038_e01_recanon
  have p0039 :=
    @g_syl5bb (syn_wo (syn_wss (.cv f) (.cv g)) (syn_wss (.cv g) (.cv f)))
      (syn_wo (syn_wss (.cv g) (.cv f)) (syn_wss (.cv f) (.cv g))) (.objEq g w)
      (syn_wo (syn_wss (.cv w) (.cv f)) (syn_wss (.cv f) (.cv w))) p0035 p0038
  have p0040 :=
    @g_anbi2d (.objEq g w) (syn_wo (syn_wss (.cv f) (.cv g)) (syn_wss (.cv g) (.cv f)))
      (syn_wo (syn_wss (.cv w) (.cv f)) (syn_wss (.cv f) (.cv w))) (syn_wfun (.cv f))
      p0039
  have p0041 := @g_funeq (.cv f) (.cv v)
  have p0042 := @g_sseq2 (.cv f) (.cv v) (.cv w)
  have p0043 := @g_sseq1 (.cv f) (.cv v) (.cv w)
  have p0044_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq f v) (syn_wb (syn_wss (.cv w) (.cv f)) (syn_wss (.cv w) (.cv v)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wss syn_cin syn_ccompl syn_cnin syn_wnan syn_wa
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0042
  have p0044_e01_recanon :
    Nominal.NPrf
      (.imp (.objEq f v) (syn_wb (syn_wss (.cv f) (.cv w)) (syn_wss (.cv v) (.cv w)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wss syn_cin syn_ccompl syn_cnin syn_wnan syn_wa
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0043
  have p0044 :=
    @g_orbi12d (.objEq f v) (syn_wss (.cv w) (.cv f)) (syn_wss (.cv w) (.cv v))
      (syn_wss (.cv f) (.cv w)) (syn_wss (.cv v) (.cv w)) p0044_e00_recanon
      p0044_e01_recanon
  have p0045_e00_recanon :
    Nominal.NPrf (.imp (.objEq f v) (syn_wb (syn_wfun (.cv f)) (syn_wfun (.cv v)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wfun syn_wss syn_cin syn_ccompl syn_cnin syn_wnan syn_wa
          syn_ccom syn_copab syn_wex syn_ccnv syn_cid
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0041
  have p0045 :=
    @g_anbi12d (.objEq f v) (syn_wfun (.cv f)) (syn_wfun (.cv v))
      (syn_wo (syn_wss (.cv w) (.cv f)) (syn_wss (.cv f) (.cv w)))
      (syn_wo (syn_wss (.cv w) (.cv v)) (syn_wss (.cv v) (.cv w))) p0045_e00_recanon p0044
  have p0046 :=
    @g_cbvral2v
      (syn_wa (syn_wfun (.cv f)) (syn_wo (syn_wss (.cv f) (.cv g)) (syn_wss (.cv g) (.cv f))))
      (syn_wa (syn_wfun (.cv v)) (syn_wo (syn_wss (.cv w) (.cv v)) (syn_wss (.cv v) (.cv w))))
      (syn_wa (syn_wfun (.cv f)) (syn_wo (syn_wss (.cv w) (.cv f)) (syn_wss (.cv f) (.cv w))))
      g f w v A A dv_cache_0014 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0011
      dv_cache_0012 dv_cache_0021 dv_cache_0022 dv_cache_0017 dv_cache_0023 dv_cache_0024
      dv_cache_0025 p0040 p0045
  have p0047 :=
    @g_bitri
      (syn_wral f A (syn_wral g A (syn_wa (syn_wfun (.cv f))
            (syn_wo (syn_wss (.cv f) (.cv g)) (syn_wss (.cv g) (.cv f))))))
      (syn_wral g A (syn_wral f A (syn_wa (syn_wfun (.cv f))
            (syn_wo (syn_wss (.cv f) (.cv g)) (syn_wss (.cv g) (.cv f))))))
      (syn_wral w A (syn_wral v A (syn_wa (syn_wfun (.cv v))
            (syn_wo (syn_wss (.cv w) (.cv v)) (syn_wss (.cv v) (.cv w))))))
      p0034 p0046
  have p0048 :=
    @g_anbi12i
      (syn_wral f A (syn_wral g A (syn_wa (syn_wfun (.cv f))
            (syn_wo (syn_wss (.cv f) (.cv g)) (syn_wss (.cv g) (.cv f))))))
      (syn_wral w A (syn_wral v A (syn_wa (syn_wfun (.cv w))
            (syn_wo (syn_wss (.cv w) (.cv v)) (syn_wss (.cv v) (.cv w))))))
      (syn_wral f A (syn_wral g A (syn_wa (syn_wfun (.cv f))
            (syn_wo (syn_wss (.cv f) (.cv g)) (syn_wss (.cv g) (.cv f))))))
      (syn_wral w A (syn_wral v A (syn_wa (syn_wfun (.cv v))
            (syn_wo (syn_wss (.cv w) (.cv v)) (syn_wss (.cv v) (.cv w))))))
      p0033 p0047
  have p0049 :=
    @g_anidm
      (syn_wral f A (syn_wral g A (syn_wa (syn_wfun (.cv f))
            (syn_wo (syn_wss (.cv f) (.cv g)) (syn_wss (.cv g) (.cv f))))))
  have p0050 :=
    @g_anandir (syn_wfun (.cv w)) (syn_wfun (.cv v))
      (syn_wo (syn_wss (.cv w) (.cv v)) (syn_wss (.cv v) (.cv w)))
  have p0051 :=
    @g_n_2ralbii
      (syn_wa (syn_wa (syn_wfun (.cv w)) (syn_wfun (.cv v)))
        (syn_wo (syn_wss (.cv w) (.cv v)) (syn_wss (.cv v) (.cv w))))
      (syn_wa (syn_wa (syn_wfun (.cv w))
          (syn_wo (syn_wss (.cv w) (.cv v)) (syn_wss (.cv v) (.cv w))))
        (syn_wa (syn_wfun (.cv v))
          (syn_wo (syn_wss (.cv w) (.cv v)) (syn_wss (.cv v) (.cv w)))))
      w v A A p0050
  have p0052 :=
    @g_r19_26_2
      (syn_wa (syn_wfun (.cv w)) (syn_wo (syn_wss (.cv w) (.cv v)) (syn_wss (.cv v) (.cv w))))
      (syn_wa (syn_wfun (.cv v)) (syn_wo (syn_wss (.cv w) (.cv v)) (syn_wss (.cv v) (.cv w))))
      w v A A
  have p0053 :=
    @g_bitr2i
      (syn_wral w A (syn_wral v A (syn_wa (syn_wa (syn_wfun (.cv w)) (syn_wfun (.cv v)))
            (syn_wo (syn_wss (.cv w) (.cv v)) (syn_wss (.cv v) (.cv w))))))
      (syn_wral w A (syn_wral v A (syn_wa (syn_wa (syn_wfun (.cv w))
              (syn_wo (syn_wss (.cv w) (.cv v)) (syn_wss (.cv v) (.cv w))))
            (syn_wa (syn_wfun (.cv v))
              (syn_wo (syn_wss (.cv w) (.cv v)) (syn_wss (.cv v) (.cv w)))))))
      (syn_wa (syn_wral w A (syn_wral v A (syn_wa (syn_wfun (.cv w))
              (syn_wo (syn_wss (.cv w) (.cv v)) (syn_wss (.cv v) (.cv w)))))) (syn_wral w A
          (syn_wral v A (syn_wa (syn_wfun (.cv v))
              (syn_wo (syn_wss (.cv w) (.cv v)) (syn_wss (.cv v) (.cv w)))))))
      p0051 p0052
  have p0054 :=
    @g_n_3bitr3i
      (syn_wa (syn_wral f A (syn_wral g A (syn_wa (syn_wfun (.cv f))
              (syn_wo (syn_wss (.cv f) (.cv g)) (syn_wss (.cv g) (.cv f)))))) (syn_wral f A
          (syn_wral g A (syn_wa (syn_wfun (.cv f))
              (syn_wo (syn_wss (.cv f) (.cv g)) (syn_wss (.cv g) (.cv f)))))))
      (syn_wa (syn_wral w A (syn_wral v A (syn_wa (syn_wfun (.cv w))
              (syn_wo (syn_wss (.cv w) (.cv v)) (syn_wss (.cv v) (.cv w)))))) (syn_wral w A
          (syn_wral v A (syn_wa (syn_wfun (.cv v))
              (syn_wo (syn_wss (.cv w) (.cv v)) (syn_wss (.cv v) (.cv w)))))))
      (syn_wral f A (syn_wral g A (syn_wa (syn_wfun (.cv f))
            (syn_wo (syn_wss (.cv f) (.cv g)) (syn_wss (.cv g) (.cv f))))))
      (syn_wral w A (syn_wral v A (syn_wa (syn_wa (syn_wfun (.cv w)) (syn_wfun (.cv v)))
            (syn_wo (syn_wss (.cv w) (.cv v)) (syn_wss (.cv v) (.cv w))))))
      p0048 p0049 p0053
  have p0055 := @g_eluni w (syn_cop (.cv x) (.cv y)) A dv_cache_0026 dv_cache_0012
  have p0056 := @g_eluni v (syn_cop (.cv x) (.cv z)) A dv_cache_0027 dv_cache_0013
  have p0057 :=
    @g_anbi12i (.classMem (syn_cop (.cv x) (.cv y)) (syn_cuni A))
      (syn_wex w (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) (.cv w)) (.classMem (.cv w) A)))
      (.classMem (syn_cop (.cv x) (.cv z)) (syn_cuni A))
      (syn_wex v (syn_wa (.classMem (syn_cop (.cv x) (.cv z)) (.cv v)) (.classMem (.cv v) A)))
      p0055 p0056
  have p0058 :=
    @g_eeanv (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) (.cv w)) (.classMem (.cv w) A))
      (syn_wa (.classMem (syn_cop (.cv x) (.cv z)) (.cv v)) (.classMem (.cv v) A)) w v
      dv_cache_0028 dv_cache_0029
  have p0059 :=
    @g_an4 (.classMem (syn_cop (.cv x) (.cv y)) (.cv w)) (.classMem (.cv w) A)
      (.classMem (syn_cop (.cv x) (.cv z)) (.cv v)) (.classMem (.cv v) A)
  have p0060 :=
    @g_ancom
      (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) (.cv w))
        (.classMem (syn_cop (.cv x) (.cv z)) (.cv v)))
      (syn_wa (.classMem (.cv w) A) (.classMem (.cv v) A))
  have p0061 :=
    @g_bitri
      (syn_wa (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) (.cv w)) (.classMem (.cv w) A))
        (syn_wa (.classMem (syn_cop (.cv x) (.cv z)) (.cv v)) (.classMem (.cv v) A)))
      (syn_wa (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) (.cv w))
          (.classMem (syn_cop (.cv x) (.cv z)) (.cv v)))
        (syn_wa (.classMem (.cv w) A) (.classMem (.cv v) A)))
      (syn_wa (syn_wa (.classMem (.cv w) A) (.classMem (.cv v) A))
        (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) (.cv w))
          (.classMem (syn_cop (.cv x) (.cv z)) (.cv v))))
      p0059 p0060
  have p0062 :=
    @g_n_2exbii
      (syn_wa (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) (.cv w)) (.classMem (.cv w) A))
        (syn_wa (.classMem (syn_cop (.cv x) (.cv z)) (.cv v)) (.classMem (.cv v) A)))
      (syn_wa (syn_wa (.classMem (.cv w) A) (.classMem (.cv v) A))
        (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) (.cv w))
          (.classMem (syn_cop (.cv x) (.cv z)) (.cv v))))
      w v p0061
  have p0063 :=
    @g_n_3bitr2i
      (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) (syn_cuni A))
        (.classMem (syn_cop (.cv x) (.cv z)) (syn_cuni A)))
      (syn_wa (syn_wex w
          (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) (.cv w)) (.classMem (.cv w) A)))
        (syn_wex v
          (syn_wa (.classMem (syn_cop (.cv x) (.cv z)) (.cv v)) (.classMem (.cv v) A))))
      (syn_wex w (syn_wex v (syn_wa
            (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) (.cv w)) (.classMem (.cv w) A))
            (syn_wa (.classMem (syn_cop (.cv x) (.cv z)) (.cv v)) (.classMem (.cv v) A)))))
      (syn_wex w (syn_wex v (syn_wa (syn_wa (.classMem (.cv w) A) (.classMem (.cv v) A))
            (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) (.cv w))
              (.classMem (syn_cop (.cv x) (.cv z)) (.cv v))))))
      p0057 p0058 p0062
  have p0064 :=
    @g_imbi1i
      (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) (syn_cuni A))
        (.classMem (syn_cop (.cv x) (.cv z)) (syn_cuni A)))
      (syn_wex w (syn_wex v (syn_wa (syn_wa (.classMem (.cv w) A) (.classMem (.cv v) A))
            (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) (.cv w))
              (.classMem (syn_cop (.cv x) (.cv z)) (.cv v))))))
      (.objEq y z) p0063
  have p0065 :=
    @g_n_19_23v
      (syn_wa (syn_wa (.classMem (.cv w) A) (.classMem (.cv v) A))
        (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) (.cv w))
          (.classMem (syn_cop (.cv x) (.cv z)) (.cv v))))
      (.objEq y z) v dv_cache_0030
  have p0066 :=
    @g_albii
      (.all v (.imp (syn_wa (syn_wa (.classMem (.cv w) A) (.classMem (.cv v) A))
            (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) (.cv w))
              (.classMem (syn_cop (.cv x) (.cv z)) (.cv v)))) (.objEq y z)))
      (.imp (syn_wex v (syn_wa (syn_wa (.classMem (.cv w) A) (.classMem (.cv v) A))
            (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) (.cv w))
              (.classMem (syn_cop (.cv x) (.cv z)) (.cv v))))) (.objEq y z))
      w p0065
  have p0067 :=
    @g_impexp (syn_wa (.classMem (.cv w) A) (.classMem (.cv v) A))
      (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) (.cv w))
        (.classMem (syn_cop (.cv x) (.cv z)) (.cv v)))
      (.objEq y z)
  have p0068 :=
    @g_n_2albii
      (.imp (syn_wa (syn_wa (.classMem (.cv w) A) (.classMem (.cv v) A))
          (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) (.cv w))
            (.classMem (syn_cop (.cv x) (.cv z)) (.cv v)))) (.objEq y z))
      (.imp (syn_wa (.classMem (.cv w) A) (.classMem (.cv v) A)) (.imp
          (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) (.cv w))
            (.classMem (syn_cop (.cv x) (.cv z)) (.cv v))) (.objEq y z)))
      w v p0067
  have p0069 :=
    @g_r2al
      (.imp (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) (.cv w))
          (.classMem (syn_cop (.cv x) (.cv z)) (.cv v))) (.objEq y z))
      w v A A dv_cache_0013 dv_cache_0031
  have p0070 :=
    @g_bitr4i
      (.all w (.all v (.imp (syn_wa (syn_wa (.classMem (.cv w) A) (.classMem (.cv v) A))
              (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) (.cv w))
                (.classMem (syn_cop (.cv x) (.cv z)) (.cv v)))) (.objEq y z))))
      (.all w (.all v (.imp (syn_wa (.classMem (.cv w) A) (.classMem (.cv v) A)) (.imp
              (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) (.cv w))
                (.classMem (syn_cop (.cv x) (.cv z)) (.cv v))) (.objEq y z)))))
      (syn_wral w A (syn_wral v A (.imp (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) (.cv w))
              (.classMem (syn_cop (.cv x) (.cv z)) (.cv v))) (.objEq y z))))
      p0068 p0069
  have p0071 :=
    @g_n_19_23v
      (syn_wex v (syn_wa (syn_wa (.classMem (.cv w) A) (.classMem (.cv v) A))
          (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) (.cv w))
            (.classMem (syn_cop (.cv x) (.cv z)) (.cv v)))))
      (.objEq y z) w dv_cache_0032
  have p0072 :=
    @g_n_3bitr3ri
      (.all w (.all v (.imp (syn_wa (syn_wa (.classMem (.cv w) A) (.classMem (.cv v) A))
              (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) (.cv w))
                (.classMem (syn_cop (.cv x) (.cv z)) (.cv v)))) (.objEq y z))))
      (.all w (.imp (syn_wex v (syn_wa (syn_wa (.classMem (.cv w) A) (.classMem (.cv v) A))
              (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) (.cv w))
                (.classMem (syn_cop (.cv x) (.cv z)) (.cv v))))) (.objEq y z)))
      (syn_wral w A (syn_wral v A (.imp (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) (.cv w))
              (.classMem (syn_cop (.cv x) (.cv z)) (.cv v))) (.objEq y z))))
      (.imp (syn_wex w (syn_wex v (syn_wa (syn_wa (.classMem (.cv w) A) (.classMem (.cv v) A))
              (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) (.cv w))
                (.classMem (syn_cop (.cv x) (.cv z)) (.cv v)))))) (.objEq y z))
      p0066 p0070 p0071
  have p0073 :=
    @g_bitri
      (.imp (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) (syn_cuni A))
          (.classMem (syn_cop (.cv x) (.cv z)) (syn_cuni A))) (.objEq y z))
      (.imp (syn_wex w (syn_wex v (syn_wa (syn_wa (.classMem (.cv w) A) (.classMem (.cv v) A))
              (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) (.cv w))
                (.classMem (syn_cop (.cv x) (.cv z)) (.cv v)))))) (.objEq y z))
      (syn_wral w A (syn_wral v A (.imp (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) (.cv w))
              (.classMem (syn_cop (.cv x) (.cv z)) (.cv v))) (.objEq y z))))
      p0064 p0072
  have p0074 :=
    @g_n_3imtr4i
      (syn_wral w A (syn_wral v A (syn_wa (syn_wa (syn_wfun (.cv w)) (syn_wfun (.cv v)))
            (syn_wo (syn_wss (.cv w) (.cv v)) (syn_wss (.cv v) (.cv w))))))
      (syn_wral w A (syn_wral v A (.imp (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) (.cv w))
              (.classMem (syn_cop (.cv x) (.cv z)) (.cv v))) (.objEq y z))))
      (syn_wral f A (syn_wral g A (syn_wa (syn_wfun (.cv f))
            (syn_wo (syn_wss (.cv f) (.cv g)) (syn_wss (.cv g) (.cv f))))))
      (.imp (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) (syn_cuni A))
          (.classMem (syn_cop (.cv x) (.cv z)) (syn_cuni A))) (.objEq y z))
      p0023 p0054 p0073
  have p0075 :=
    @g_alrimiv
      (syn_wral f A (syn_wral g A (syn_wa (syn_wfun (.cv f))
            (syn_wo (syn_wss (.cv f) (.cv g)) (syn_wss (.cv g) (.cv f))))))
      (.imp (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) (syn_cuni A))
          (.classMem (syn_cop (.cv x) (.cv z)) (syn_cuni A))) (.objEq y z))
      z dv_cache_0033 p0074
  have p0076 :=
    @g_alrimivv
      (syn_wral f A (syn_wral g A (syn_wa (syn_wfun (.cv f))
            (syn_wo (syn_wss (.cv f) (.cv g)) (syn_wss (.cv g) (.cv f))))))
      (.all z (.imp (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) (syn_cuni A))
            (.classMem (syn_cop (.cv x) (.cv z)) (syn_cuni A))) (.objEq y z)))
      x y dv_cache_0034 dv_cache_0035 p0075
  have p0077 :=
    @g_syl
      (syn_wral f A (syn_wa (syn_wfun (.cv f))
          (syn_wral g A (syn_wo (syn_wss (.cv f) (.cv g)) (syn_wss (.cv g) (.cv f))))))
      (syn_wral f A (syn_wral g A (syn_wa (syn_wfun (.cv f))
            (syn_wo (syn_wss (.cv f) (.cv g)) (syn_wss (.cv g) (.cv f))))))
      (.all x (.all y (.all z (.imp (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) (syn_cuni A))
                (.classMem (syn_cop (.cv x) (.cv z)) (syn_cuni A))) (.objEq y z)))))
      p0001 p0076
  have p0078 :=
    @g_dffun4 x y z (syn_cuni A) dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0005
      dv_cache_0006 dv_cache_0007
  have p0079 :=
    @g_sylibr
      (syn_wral f A (syn_wa (syn_wfun (.cv f))
          (syn_wral g A (syn_wo (syn_wss (.cv f) (.cv g)) (syn_wss (.cv g) (.cv f))))))
      (.all x (.all y (.all z (.imp (syn_wa (.classMem (syn_cop (.cv x) (.cv y)) (syn_cuni A))
                (.classMem (syn_cop (.cv x) (.cv z)) (syn_cuni A))) (.objEq y z)))))
      (syn_wfun (syn_cuni A)) p0077 p0078
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

@[expose]
noncomputable def g_funcnvuni (A : Class) (f : Var) (g : Var) (dv_A_f : f ∉ A.fv)
    (dv_A_g : g ∉ A.fv) (dv_f_g : f ≠ g) :
    Nominal.NPrf
      (.imp (syn_wral f A (syn_wa (syn_wfun (syn_ccnv (.cv f)))
            (syn_wral g A (syn_wo (syn_wss (.cv f) (.cv g)) (syn_wss (.cv g) (.cv f))))))
        (syn_wfun (syn_ccnv (syn_cuni A)))) :=
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
  have dv_cache_0003 : v ∉ ((Wff.classEq (.cv z) (syn_ccnv (.cv x)))).fv :=
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
  have dv_cache_0004 : x ∉ ((Wff.classEq (.cv z) (syn_ccnv (.cv v)))).fv :=
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
      ((syn_wa (syn_wfun (syn_ccnv (.cv v))) (syn_wral g A
            (syn_wo (syn_wss (.cv v) (.cv g)) (syn_wss (.cv g) (.cv v)))))).fv :=
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
    g ∉ ((syn_wo (syn_wss (.cv v) (.cv x)) (syn_wss (.cv x) (.cv v)))).fv :=
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
      ((Wff.imp (.classEq (.cv z) (syn_ccnv (.cv v)))
          (syn_wo (syn_wss (.cv z) (.cv w)) (syn_wss (.cv w) (.cv z))))).fv :=
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
      ((syn_wral g A (syn_wo (syn_wss (.cv v) (.cv g)) (syn_wss (.cv g) (.cv v))))).fv :=
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
      ((syn_wral g A (syn_wo (syn_wss (.cv v) (.cv g)) (syn_wss (.cv g) (.cv v))))).fv :=
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
  have dv_cache_0015 : w ∉ ((Wff.classEq (.cv z) (syn_ccnv (.cv v)))).fv :=
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
      ((syn_wa (syn_wfun (.cv z)) (.all w
            (.imp (syn_wrex x A (.classEq (.cv w) (syn_ccnv (.cv x))))
              (syn_wo (syn_wss (.cv z) (.cv w)) (syn_wss (.cv w) (.cv z))))))).fv :=
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
      ((syn_wral f A (syn_wa (syn_wfun (syn_ccnv (.cv f))) (syn_wral g A
              (syn_wo (syn_wss (.cv f) (.cv g)) (syn_wss (.cv g) (.cv f))))))).fv :=
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
      ((syn_wral f A (syn_wa (syn_wfun (syn_ccnv (.cv f))) (syn_wral g A
              (syn_wo (syn_wss (.cv f) (.cv g)) (syn_wss (.cv g) (.cv f))))))).fv :=
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
  have dv_cache_0021 : y ∉ ((syn_wrex x A (.classEq (.cv z) (syn_ccnv (.cv x))))).fv :=
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
  have dv_cache_0023 : y ∉ ((syn_wrex x A (.classEq (.cv w) (syn_ccnv (.cv x))))).fv :=
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
    z ∉ ((Class.cab y (syn_wrex x A (.classEq (.cv y) (syn_ccnv (.cv x)))))).fv :=
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
    w ∉ ((Class.cab y (syn_wrex x A (.classEq (.cv y) (syn_ccnv (.cv x)))))).fv :=
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
  have dv_cache_0029 : y ∉ ((syn_ccnv (.cv x))).fv :=
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
  have p0000 := @g_cnveq (.cv x) (.cv v)
  have p0001 :=
    @g_eqeq2d (.classEq (.cv x) (.cv v)) (syn_ccnv (.cv x)) (syn_ccnv (.cv v)) (.cv z)
      p0000
  have p0002_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq x v) (syn_wb (.classEq (.cv z) (syn_ccnv (.cv x)))
          (.classEq (.cv z) (syn_ccnv (.cv v))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_ccnv syn_copab syn_wex syn_wbr syn_cop syn_cun syn_cnin syn_wnan
          syn_wa syn_ccompl syn_wrex syn_cphi
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0001
  have p0002 :=
    @g_cbvrexv (.classEq (.cv z) (syn_ccnv (.cv x))) (.classEq (.cv z) (syn_ccnv (.cv v)))
      x v A dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 p0002_e00_recanon
  have p0003 := @g_cnveq (.cv f) (.cv v)
  have p0004 :=
    @g_funeqd (.classEq (.cv f) (.cv v)) (syn_ccnv (.cv f)) (syn_ccnv (.cv v)) p0003
  have p0005 := @g_sseq1 (.cv f) (.cv v) (.cv g)
  have p0006 := @g_sseq2 (.cv f) (.cv v) (.cv g)
  have p0007 :=
    @g_orbi12d (.classEq (.cv f) (.cv v)) (syn_wss (.cv f) (.cv g))
      (syn_wss (.cv v) (.cv g)) (syn_wss (.cv g) (.cv f)) (syn_wss (.cv g) (.cv v)) p0005
      p0006
  have p0008 :=
    @g_ralbidv (.classEq (.cv f) (.cv v))
      (syn_wo (syn_wss (.cv f) (.cv g)) (syn_wss (.cv g) (.cv f)))
      (syn_wo (syn_wss (.cv v) (.cv g)) (syn_wss (.cv g) (.cv v))) g A dv_cache_0005 p0007
  have p0009 :=
    @g_anbi12d (.classEq (.cv f) (.cv v)) (syn_wfun (syn_ccnv (.cv f)))
      (syn_wfun (syn_ccnv (.cv v)))
      (syn_wral g A (syn_wo (syn_wss (.cv f) (.cv g)) (syn_wss (.cv g) (.cv f))))
      (syn_wral g A (syn_wo (syn_wss (.cv v) (.cv g)) (syn_wss (.cv g) (.cv v)))) p0004
      p0008
  have p0010 :=
    @g_rspcv
      (syn_wa (syn_wfun (syn_ccnv (.cv f)))
        (syn_wral g A (syn_wo (syn_wss (.cv f) (.cv g)) (syn_wss (.cv g) (.cv f)))))
      (syn_wa (syn_wfun (syn_ccnv (.cv v)))
        (syn_wral g A (syn_wo (syn_wss (.cv v) (.cv g)) (syn_wss (.cv g) (.cv v)))))
      f (.cv v) A dv_cache_0006 dv_cache_0007 dv_cache_0008 p0009
  have p0011 := @g_funeq (.cv z) (syn_ccnv (.cv v))
  have p0012 :=
    @g_biimprcd (.classEq (.cv z) (syn_ccnv (.cv v))) (syn_wfun (.cv z))
      (syn_wfun (syn_ccnv (.cv v))) p0011
  have p0013 := @g_sseq2 (.cv g) (.cv x) (.cv v)
  have p0014 := @g_sseq1 (.cv g) (.cv x) (.cv v)
  have p0015 :=
    @g_orbi12d (.classEq (.cv g) (.cv x)) (syn_wss (.cv v) (.cv g))
      (syn_wss (.cv v) (.cv x)) (syn_wss (.cv g) (.cv v)) (syn_wss (.cv x) (.cv v)) p0013
      p0014
  have p0016 :=
    @g_rspcv (syn_wo (syn_wss (.cv v) (.cv g)) (syn_wss (.cv g) (.cv v)))
      (syn_wo (syn_wss (.cv v) (.cv x)) (syn_wss (.cv x) (.cv v))) g (.cv x) A
      dv_cache_0009 dv_cache_0010 dv_cache_0011 p0015
  have p0017 := @g_cnvss (.cv v) (.cv x)
  have p0018 := @g_cnvss (.cv x) (.cv v)
  have p0019 :=
    @g_orim12i (syn_wss (.cv v) (.cv x)) (syn_wss (syn_ccnv (.cv v)) (syn_ccnv (.cv x)))
      (syn_wss (.cv x) (.cv v)) (syn_wss (syn_ccnv (.cv x)) (syn_ccnv (.cv v))) p0017
      p0018
  have p0020 := @g_sseq12 (.cv z) (syn_ccnv (.cv v)) (.cv w) (syn_ccnv (.cv x))
  have p0021 :=
    @g_ancoms (.classEq (.cv z) (syn_ccnv (.cv v))) (.classEq (.cv w) (syn_ccnv (.cv x)))
      (syn_wb (syn_wss (.cv z) (.cv w)) (syn_wss (syn_ccnv (.cv v)) (syn_ccnv (.cv x))))
      p0020
  have p0022 := @g_sseq12 (.cv w) (syn_ccnv (.cv x)) (.cv z) (syn_ccnv (.cv v))
  have p0023 :=
    @g_orbi12d
      (syn_wa (.classEq (.cv w) (syn_ccnv (.cv x))) (.classEq (.cv z) (syn_ccnv (.cv v))))
      (syn_wss (.cv z) (.cv w)) (syn_wss (syn_ccnv (.cv v)) (syn_ccnv (.cv x)))
      (syn_wss (.cv w) (.cv z)) (syn_wss (syn_ccnv (.cv x)) (syn_ccnv (.cv v))) p0021
      p0022
  have p0024 :=
    @g_syl5ibrcom (syn_wo (syn_wss (.cv v) (.cv x)) (syn_wss (.cv x) (.cv v)))
      (syn_wo (syn_wss (.cv z) (.cv w)) (syn_wss (.cv w) (.cv z)))
      (syn_wa (.classEq (.cv w) (syn_ccnv (.cv x))) (.classEq (.cv z) (syn_ccnv (.cv v))))
      (syn_wo (syn_wss (syn_ccnv (.cv v)) (syn_ccnv (.cv x)))
        (syn_wss (syn_ccnv (.cv x)) (syn_ccnv (.cv v))))
      p0019 p0023
  have p0025 :=
    @g_exp3a (syn_wo (syn_wss (.cv v) (.cv x)) (syn_wss (.cv x) (.cv v)))
      (.classEq (.cv w) (syn_ccnv (.cv x))) (.classEq (.cv z) (syn_ccnv (.cv v)))
      (syn_wo (syn_wss (.cv z) (.cv w)) (syn_wss (.cv w) (.cv z))) p0024
  have p0026 :=
    @g_syl6com (.classMem (.cv x) A)
      (syn_wral g A (syn_wo (syn_wss (.cv v) (.cv g)) (syn_wss (.cv g) (.cv v))))
      (syn_wo (syn_wss (.cv v) (.cv x)) (syn_wss (.cv x) (.cv v)))
      (.imp (.classEq (.cv w) (syn_ccnv (.cv x))) (.imp (.classEq (.cv z) (syn_ccnv (.cv v)))
          (syn_wo (syn_wss (.cv z) (.cv w)) (syn_wss (.cv w) (.cv z)))))
      p0016 p0025
  have p0027 :=
    @g_rexlimdv
      (syn_wral g A (syn_wo (syn_wss (.cv v) (.cv g)) (syn_wss (.cv g) (.cv v))))
      (.classEq (.cv w) (syn_ccnv (.cv x)))
      (.imp (.classEq (.cv z) (syn_ccnv (.cv v)))
        (syn_wo (syn_wss (.cv z) (.cv w)) (syn_wss (.cv w) (.cv z))))
      x A dv_cache_0012 dv_cache_0013 p0026
  have p0028 :=
    @g_com23 (syn_wral g A (syn_wo (syn_wss (.cv v) (.cv g)) (syn_wss (.cv g) (.cv v))))
      (syn_wrex x A (.classEq (.cv w) (syn_ccnv (.cv x))))
      (.classEq (.cv z) (syn_ccnv (.cv v)))
      (syn_wo (syn_wss (.cv z) (.cv w)) (syn_wss (.cv w) (.cv z))) p0027
  have p0029 :=
    @g_alrimdv (syn_wral g A (syn_wo (syn_wss (.cv v) (.cv g)) (syn_wss (.cv g) (.cv v))))
      (.classEq (.cv z) (syn_ccnv (.cv v)))
      (.imp (syn_wrex x A (.classEq (.cv w) (syn_ccnv (.cv x))))
        (syn_wo (syn_wss (.cv z) (.cv w)) (syn_wss (.cv w) (.cv z))))
      w dv_cache_0014 dv_cache_0015 p0028
  have p0030 :=
    @g_anim12ii (syn_wfun (syn_ccnv (.cv v))) (.classEq (.cv z) (syn_ccnv (.cv v)))
      (syn_wfun (.cv z))
      (syn_wral g A (syn_wo (syn_wss (.cv v) (.cv g)) (syn_wss (.cv g) (.cv v))))
      (.all w (.imp (syn_wrex x A (.classEq (.cv w) (syn_ccnv (.cv x))))
          (syn_wo (syn_wss (.cv z) (.cv w)) (syn_wss (.cv w) (.cv z)))))
      p0012 p0029
  have p0031 :=
    @g_syl6com (.classMem (.cv v) A)
      (syn_wral f A (syn_wa (syn_wfun (syn_ccnv (.cv f)))
          (syn_wral g A (syn_wo (syn_wss (.cv f) (.cv g)) (syn_wss (.cv g) (.cv f))))))
      (syn_wa (syn_wfun (syn_ccnv (.cv v)))
        (syn_wral g A (syn_wo (syn_wss (.cv v) (.cv g)) (syn_wss (.cv g) (.cv v)))))
      (.imp (.classEq (.cv z) (syn_ccnv (.cv v))) (syn_wa (syn_wfun (.cv z)) (.all w
            (.imp (syn_wrex x A (.classEq (.cv w) (syn_ccnv (.cv x))))
              (syn_wo (syn_wss (.cv z) (.cv w)) (syn_wss (.cv w) (.cv z)))))))
      p0010 p0030
  have p0032 :=
    @g_rexlimdv
      (syn_wral f A (syn_wa (syn_wfun (syn_ccnv (.cv f)))
          (syn_wral g A (syn_wo (syn_wss (.cv f) (.cv g)) (syn_wss (.cv g) (.cv f))))))
      (.classEq (.cv z) (syn_ccnv (.cv v)))
      (syn_wa (syn_wfun (.cv z)) (.all w
          (.imp (syn_wrex x A (.classEq (.cv w) (syn_ccnv (.cv x))))
            (syn_wo (syn_wss (.cv z) (.cv w)) (syn_wss (.cv w) (.cv z))))))
      v A dv_cache_0016 dv_cache_0017 p0031
  have p0033 :=
    @g_syl5bi (syn_wrex x A (.classEq (.cv z) (syn_ccnv (.cv x))))
      (syn_wrex v A (.classEq (.cv z) (syn_ccnv (.cv v))))
      (syn_wral f A (syn_wa (syn_wfun (syn_ccnv (.cv f)))
          (syn_wral g A (syn_wo (syn_wss (.cv f) (.cv g)) (syn_wss (.cv g) (.cv f))))))
      (syn_wa (syn_wfun (.cv z)) (.all w
          (.imp (syn_wrex x A (.classEq (.cv w) (syn_ccnv (.cv x))))
            (syn_wo (syn_wss (.cv z) (.cv w)) (syn_wss (.cv w) (.cv z))))))
      p0002 p0032
  have p0034 :=
    @g_alrimiv
      (syn_wral f A (syn_wa (syn_wfun (syn_ccnv (.cv f)))
          (syn_wral g A (syn_wo (syn_wss (.cv f) (.cv g)) (syn_wss (.cv g) (.cv f))))))
      (.imp (syn_wrex x A (.classEq (.cv z) (syn_ccnv (.cv x)))) (syn_wa (syn_wfun (.cv z))
          (.all w (.imp (syn_wrex x A (.classEq (.cv w) (syn_ccnv (.cv x))))
              (syn_wo (syn_wss (.cv z) (.cv w)) (syn_wss (.cv w) (.cv z)))))))
      z dv_cache_0018 p0033
  have p0035 :=
    (Nominal.biimpRefl (syn_wral z (.cab y (syn_wrex x A (.classEq (.cv y) (syn_ccnv (.cv x)))))
        (syn_wa (syn_wfun (.cv z))
          (syn_wral w (.cab y (syn_wrex x A (.classEq (.cv y) (syn_ccnv (.cv x)))))
            (syn_wo (syn_wss (.cv z) (.cv w)) (syn_wss (.cv w) (.cv z)))))))
  have p0036 := @g_vex z
  have p0037 := @g_eqeq1 (.cv y) (.cv z) (syn_ccnv (.cv x))
  have p0038 :=
    @g_rexbidv (.classEq (.cv y) (.cv z)) (.classEq (.cv y) (syn_ccnv (.cv x)))
      (.classEq (.cv z) (syn_ccnv (.cv x))) x A dv_cache_0019 p0037
  have p0039 :=
    @g_elab (syn_wrex x A (.classEq (.cv y) (syn_ccnv (.cv x))))
      (syn_wrex x A (.classEq (.cv z) (syn_ccnv (.cv x)))) y (.cv z) dv_cache_0020
      dv_cache_0021 p0036 p0038
  have p0040 := @g_eqeq1 (.cv y) (.cv w) (syn_ccnv (.cv x))
  have p0041 :=
    @g_rexbidv (.classEq (.cv y) (.cv w)) (.classEq (.cv y) (syn_ccnv (.cv x)))
      (.classEq (.cv w) (syn_ccnv (.cv x))) x A dv_cache_0022 p0040
  have p0042_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq y w) (syn_wb (syn_wrex x A (.classEq (.cv y) (syn_ccnv (.cv x))))
          (syn_wrex x A (.classEq (.cv w) (syn_ccnv (.cv x)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [syn_wb, syn_wrex, syn_wex, syn_wa, syn_ccnv, syn_copab, syn_wbr,
          syn_cop, syn_cun, syn_cnin, syn_wnan, syn_ccompl]
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0041
  have p0042 :=
    @g_ralab (syn_wrex x A (.classEq (.cv y) (syn_ccnv (.cv x))))
      (syn_wrex x A (.classEq (.cv w) (syn_ccnv (.cv x))))
      (syn_wo (syn_wss (.cv z) (.cv w)) (syn_wss (.cv w) (.cv z))) w y dv_cache_0023
      dv_cache_0024 p0042_e00_recanon
  have p0043 :=
    @g_anbi2i
      (syn_wral w (.cab y (syn_wrex x A (.classEq (.cv y) (syn_ccnv (.cv x)))))
        (syn_wo (syn_wss (.cv z) (.cv w)) (syn_wss (.cv w) (.cv z))))
      (.all w (.imp (syn_wrex x A (.classEq (.cv w) (syn_ccnv (.cv x))))
          (syn_wo (syn_wss (.cv z) (.cv w)) (syn_wss (.cv w) (.cv z)))))
      (syn_wfun (.cv z)) p0042
  have p0044 :=
    @g_imbi12i
      (.classMem (.cv z) (.cab y (syn_wrex x A (.classEq (.cv y) (syn_ccnv (.cv x))))))
      (syn_wrex x A (.classEq (.cv z) (syn_ccnv (.cv x))))
      (syn_wa (syn_wfun (.cv z))
        (syn_wral w (.cab y (syn_wrex x A (.classEq (.cv y) (syn_ccnv (.cv x)))))
          (syn_wo (syn_wss (.cv z) (.cv w)) (syn_wss (.cv w) (.cv z)))))
      (syn_wa (syn_wfun (.cv z)) (.all w
          (.imp (syn_wrex x A (.classEq (.cv w) (syn_ccnv (.cv x))))
            (syn_wo (syn_wss (.cv z) (.cv w)) (syn_wss (.cv w) (.cv z))))))
      p0039 p0043
  have p0045 :=
    @g_albii
      (.imp (.classMem (.cv z) (.cab y (syn_wrex x A (.classEq (.cv y) (syn_ccnv (.cv x))))))
        (syn_wa (syn_wfun (.cv z))
          (syn_wral w (.cab y (syn_wrex x A (.classEq (.cv y) (syn_ccnv (.cv x)))))
            (syn_wo (syn_wss (.cv z) (.cv w)) (syn_wss (.cv w) (.cv z))))))
      (.imp (syn_wrex x A (.classEq (.cv z) (syn_ccnv (.cv x)))) (syn_wa (syn_wfun (.cv z))
          (.all w (.imp (syn_wrex x A (.classEq (.cv w) (syn_ccnv (.cv x))))
              (syn_wo (syn_wss (.cv z) (.cv w)) (syn_wss (.cv w) (.cv z)))))))
      z p0044
  have p0046 :=
    @g_bitr2i
      (syn_wral z (.cab y (syn_wrex x A (.classEq (.cv y) (syn_ccnv (.cv x)))))
        (syn_wa (syn_wfun (.cv z))
          (syn_wral w (.cab y (syn_wrex x A (.classEq (.cv y) (syn_ccnv (.cv x)))))
            (syn_wo (syn_wss (.cv z) (.cv w)) (syn_wss (.cv w) (.cv z))))))
      (.all z (.imp (.classMem (.cv z)
            (.cab y (syn_wrex x A (.classEq (.cv y) (syn_ccnv (.cv x))))))
          (syn_wa (syn_wfun (.cv z))
            (syn_wral w (.cab y (syn_wrex x A (.classEq (.cv y) (syn_ccnv (.cv x)))))
              (syn_wo (syn_wss (.cv z) (.cv w)) (syn_wss (.cv w) (.cv z)))))))
      (.all z (.imp (syn_wrex x A (.classEq (.cv z) (syn_ccnv (.cv x))))
          (syn_wa (syn_wfun (.cv z)) (.all w
              (.imp (syn_wrex x A (.classEq (.cv w) (syn_ccnv (.cv x))))
                (syn_wo (syn_wss (.cv z) (.cv w)) (syn_wss (.cv w) (.cv z))))))))
      p0035 p0045
  have p0047 :=
    @g_sylib
      (syn_wral f A (syn_wa (syn_wfun (syn_ccnv (.cv f)))
          (syn_wral g A (syn_wo (syn_wss (.cv f) (.cv g)) (syn_wss (.cv g) (.cv f))))))
      (.all z (.imp (syn_wrex x A (.classEq (.cv z) (syn_ccnv (.cv x))))
          (syn_wa (syn_wfun (.cv z)) (.all w
              (.imp (syn_wrex x A (.classEq (.cv w) (syn_ccnv (.cv x))))
                (syn_wo (syn_wss (.cv z) (.cv w)) (syn_wss (.cv w) (.cv z))))))))
      (syn_wral z (.cab y (syn_wrex x A (.classEq (.cv y) (syn_ccnv (.cv x)))))
        (syn_wa (syn_wfun (.cv z))
          (syn_wral w (.cab y (syn_wrex x A (.classEq (.cv y) (syn_ccnv (.cv x)))))
            (syn_wo (syn_wss (.cv z) (.cv w)) (syn_wss (.cv w) (.cv z))))))
      p0034 p0046
  have p0048 :=
    @g_fununi (.cab y (syn_wrex x A (.classEq (.cv y) (syn_ccnv (.cv x))))) z w
      dv_cache_0025 dv_cache_0026 dv_cache_0027
  have p0049 :=
    @g_syl
      (syn_wral f A (syn_wa (syn_wfun (syn_ccnv (.cv f)))
          (syn_wral g A (syn_wo (syn_wss (.cv f) (.cv g)) (syn_wss (.cv g) (.cv f))))))
      (syn_wral z (.cab y (syn_wrex x A (.classEq (.cv y) (syn_ccnv (.cv x)))))
        (syn_wa (syn_wfun (.cv z))
          (syn_wral w (.cab y (syn_wrex x A (.classEq (.cv y) (syn_ccnv (.cv x)))))
            (syn_wo (syn_wss (.cv z) (.cv w)) (syn_wss (.cv w) (.cv z))))))
      (syn_wfun (syn_cuni (.cab y (syn_wrex x A (.classEq (.cv y) (syn_ccnv (.cv x)))))))
      p0047 p0048
  have p0050 := @g_cnvuni x A dv_cache_0001
  have p0051 := @g_vex x
  have p0052 := @g_cnvex (.cv x) p0051
  have p0053 :=
    @g_dfiun2 x y A (syn_ccnv (.cv x)) dv_cache_0028 dv_cache_0029 dv_cache_0030 p0052
  have p0054 :=
    @g_eqtri (syn_ccnv (syn_cuni A)) (syn_ciun x A (syn_ccnv (.cv x)))
      (syn_cuni (.cab y (syn_wrex x A (.classEq (.cv y) (syn_ccnv (.cv x)))))) p0050 p0053
  have p0055 :=
    @g_funeqi (syn_ccnv (syn_cuni A))
      (syn_cuni (.cab y (syn_wrex x A (.classEq (.cv y) (syn_ccnv (.cv x)))))) p0054
  have p0056 :=
    @g_sylibr
      (syn_wral f A (syn_wa (syn_wfun (syn_ccnv (.cv f)))
          (syn_wral g A (syn_wo (syn_wss (.cv f) (.cv g)) (syn_wss (.cv g) (.cv f))))))
      (syn_wfun (syn_cuni (.cab y (syn_wrex x A (.classEq (.cv y) (syn_ccnv (.cv x)))))))
      (syn_wfun (syn_ccnv (syn_cuni A))) p0049 p0055
  exact p0056

@[expose]
noncomputable def g_fun11uni (A : Class) (f : Var) (g : Var) (dv_A_f : f ∉ A.fv)
    (dv_A_g : g ∉ A.fv) (dv_f_g : f ≠ g) :
    Nominal.NPrf
      (.imp (syn_wral f A (syn_wa (syn_wa (syn_wfun (.cv f)) (syn_wfun (syn_ccnv (.cv f))))
            (syn_wral g A (syn_wo (syn_wss (.cv f) (.cv g)) (syn_wss (.cv g) (.cv f))))))
        (syn_wa (syn_wfun (syn_cuni A)) (syn_wfun (syn_ccnv (syn_cuni A))))) :=
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
  have p0000 := @g_simpl (syn_wfun (.cv f)) (syn_wfun (syn_ccnv (.cv f)))
  have p0001 :=
    @g_anim1i (syn_wa (syn_wfun (.cv f)) (syn_wfun (syn_ccnv (.cv f)))) (syn_wfun (.cv f))
      (syn_wral g A (syn_wo (syn_wss (.cv f) (.cv g)) (syn_wss (.cv g) (.cv f)))) p0000
  have p0002 :=
    @g_ralimi
      (syn_wa (syn_wa (syn_wfun (.cv f)) (syn_wfun (syn_ccnv (.cv f))))
        (syn_wral g A (syn_wo (syn_wss (.cv f) (.cv g)) (syn_wss (.cv g) (.cv f)))))
      (syn_wa (syn_wfun (.cv f))
        (syn_wral g A (syn_wo (syn_wss (.cv f) (.cv g)) (syn_wss (.cv g) (.cv f)))))
      f A p0001
  have p0003 := @g_fununi A f g dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0004 :=
    @g_syl
      (syn_wral f A (syn_wa (syn_wa (syn_wfun (.cv f)) (syn_wfun (syn_ccnv (.cv f))))
          (syn_wral g A (syn_wo (syn_wss (.cv f) (.cv g)) (syn_wss (.cv g) (.cv f))))))
      (syn_wral f A (syn_wa (syn_wfun (.cv f))
          (syn_wral g A (syn_wo (syn_wss (.cv f) (.cv g)) (syn_wss (.cv g) (.cv f))))))
      (syn_wfun (syn_cuni A)) p0002 p0003
  have p0005 := @g_simpr (syn_wfun (.cv f)) (syn_wfun (syn_ccnv (.cv f)))
  have p0006 :=
    @g_anim1i (syn_wa (syn_wfun (.cv f)) (syn_wfun (syn_ccnv (.cv f))))
      (syn_wfun (syn_ccnv (.cv f)))
      (syn_wral g A (syn_wo (syn_wss (.cv f) (.cv g)) (syn_wss (.cv g) (.cv f)))) p0005
  have p0007 :=
    @g_ralimi
      (syn_wa (syn_wa (syn_wfun (.cv f)) (syn_wfun (syn_ccnv (.cv f))))
        (syn_wral g A (syn_wo (syn_wss (.cv f) (.cv g)) (syn_wss (.cv g) (.cv f)))))
      (syn_wa (syn_wfun (syn_ccnv (.cv f)))
        (syn_wral g A (syn_wo (syn_wss (.cv f) (.cv g)) (syn_wss (.cv g) (.cv f)))))
      f A p0006
  have p0008 := @g_funcnvuni A f g dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0009 :=
    @g_syl
      (syn_wral f A (syn_wa (syn_wa (syn_wfun (.cv f)) (syn_wfun (syn_ccnv (.cv f))))
          (syn_wral g A (syn_wo (syn_wss (.cv f) (.cv g)) (syn_wss (.cv g) (.cv f))))))
      (syn_wral f A (syn_wa (syn_wfun (syn_ccnv (.cv f)))
          (syn_wral g A (syn_wo (syn_wss (.cv f) (.cv g)) (syn_wss (.cv g) (.cv f))))))
      (syn_wfun (syn_ccnv (syn_cuni A))) p0007 p0008
  have p0010 :=
    @g_jca
      (syn_wral f A (syn_wa (syn_wa (syn_wfun (.cv f)) (syn_wfun (syn_ccnv (.cv f))))
          (syn_wral g A (syn_wo (syn_wss (.cv f) (.cv g)) (syn_wss (.cv g) (.cv f))))))
      (syn_wfun (syn_cuni A)) (syn_wfun (syn_ccnv (syn_cuni A))) p0004 p0009
  exact p0010

@[expose]
noncomputable def g_funres11 (A : Class) (F : Class) :
    Nominal.NPrf (.imp (syn_wfun (syn_ccnv F)) (syn_wfun (syn_ccnv (syn_cres F A)))) :=
  by
  have p0000 := @g_resss F A
  have p0001 := @g_cnvss (syn_cres F A) F
  have p0002 := @g_funss (syn_ccnv (syn_cres F A)) (syn_ccnv F)
  have p0003 :=
    @g_mp2b (syn_wss (syn_cres F A) F) (syn_wss (syn_ccnv (syn_cres F A)) (syn_ccnv F))
      (.imp (syn_wfun (syn_ccnv F)) (syn_wfun (syn_ccnv (syn_cres F A)))) p0000 p0001
      p0002
  exact p0003

@[expose]
noncomputable def g_funcnvres (A : Class) (F : Class) :
    Nominal.NPrf
      (.imp (syn_wfun (syn_ccnv F))
        (.classEq (syn_ccnv (syn_cres F A)) (syn_cres (syn_ccnv F) (syn_cima F A)))) :=
  by
  have p0000 := @g_dfima3 F A
  have p0001 := @g_dfrn4 (syn_cres F A)
  have p0002 :=
    @g_eqtri (syn_cima F A) (syn_crn (syn_cres F A)) (syn_cdm (syn_ccnv (syn_cres F A)))
      p0000 p0001
  have p0003 :=
    @g_reseq2i (syn_cima F A) (syn_cdm (syn_ccnv (syn_cres F A))) (syn_ccnv F) p0002
  have p0004 := @g_resss F A
  have p0005 := @g_cnvss (syn_cres F A) F
  have p0006 := Nominal.mp p0004 p0005
  have p0007 := @g_funssres (syn_ccnv F) (syn_ccnv (syn_cres F A))
  have p0008 :=
    @g_mpan2 (syn_wfun (syn_ccnv F)) (syn_wss (syn_ccnv (syn_cres F A)) (syn_ccnv F))
      (.classEq (syn_cres (syn_ccnv F) (syn_cdm (syn_ccnv (syn_cres F A))))
        (syn_ccnv (syn_cres F A)))
      p0006 p0007
  have p0009 :=
    @g_syl5req (syn_wfun (syn_ccnv F)) (syn_cres (syn_ccnv F) (syn_cima F A))
      (syn_cres (syn_ccnv F) (syn_cdm (syn_ccnv (syn_cres F A))))
      (syn_ccnv (syn_cres F A)) p0003 p0008
  exact p0009

@[expose]
noncomputable def g_cnvresid (A : Class) :
    Nominal.NPrf (.classEq (syn_ccnv (syn_cres (syn_cid) A)) (syn_cres (syn_cid) A)) :=
  by
  have p0000 := @g_cnvi
  have p0001 := @g_eqcomi (syn_ccnv (syn_cid)) (syn_cid) p0000
  have p0002 := @g_funi
  have p0003 := @g_funeq (syn_cid) (syn_ccnv (syn_cid))
  have p0004 :=
    @g_mpbii (.classEq (syn_cid) (syn_ccnv (syn_cid))) (syn_wfun (syn_cid))
      (syn_wfun (syn_ccnv (syn_cid))) p0002 p0003
  have p0005 := Nominal.mp p0001 p0004
  have p0006 := @g_funcnvres A (syn_cid)
  have p0008 := @g_imai A
  have p0009 :=
    @g_reseq12i (syn_ccnv (syn_cid)) (syn_cid) (syn_cima (syn_cid) A) A p0000 p0008
  have p0010 :=
    @g_syl6eq (syn_wfun (syn_ccnv (syn_cid))) (syn_ccnv (syn_cres (syn_cid) A))
      (syn_cres (syn_ccnv (syn_cid)) (syn_cima (syn_cid) A)) (syn_cres (syn_cid) A) p0006
      p0009
  have p0011 := Nominal.mp p0005 p0010
  exact p0011

@[expose]
noncomputable def g_funcnvres2 (A : Class) (F : Class) :
    Nominal.NPrf
      (.imp (syn_wfun F) (.classEq (syn_ccnv (syn_cres (syn_ccnv F) A))
          (syn_cres F (syn_cima (syn_ccnv F) A)))) :=
  by
  have p0000 := @g_cnvcnv F
  have p0001 := @g_funeqi (syn_ccnv (syn_ccnv F)) F p0000
  have p0002 := @g_funcnvres A (syn_ccnv F)
  have p0003 :=
    @g_sylbir (syn_wfun F) (syn_wfun (syn_ccnv (syn_ccnv F)))
      (.classEq (syn_ccnv (syn_cres (syn_ccnv F) A))
        (syn_cres (syn_ccnv (syn_ccnv F)) (syn_cima (syn_ccnv F) A)))
      p0001 p0002
  have p0004 := @g_reseq1i (syn_ccnv (syn_ccnv F)) F (syn_cima (syn_ccnv F) A) p0000
  have p0005 :=
    @g_syl6eq (syn_wfun F) (syn_ccnv (syn_cres (syn_ccnv F) A))
      (syn_cres (syn_ccnv (syn_ccnv F)) (syn_cima (syn_ccnv F) A))
      (syn_cres F (syn_cima (syn_ccnv F) A)) p0003 p0004
  exact p0005

@[expose]
noncomputable def g_funimacnv (A : Class) (F : Class) :
    Nominal.NPrf
      (.imp (syn_wfun F)
        (.classEq (syn_cima F (syn_cima (syn_ccnv F) A)) (syn_cin A (syn_crn F)))) :=
  by
  have p0000 := @g_funcnvres2 A F
  have p0001 :=
    @g_rneqd (syn_wfun F) (syn_ccnv (syn_cres (syn_ccnv F) A))
      (syn_cres F (syn_cima (syn_ccnv F) A)) p0000
  have p0002 := @g_dfima3 F (syn_cima (syn_ccnv F) A)
  have p0003 :=
    @g_syl6reqr (syn_wfun F) (syn_crn (syn_ccnv (syn_cres (syn_ccnv F) A)))
      (syn_crn (syn_cres F (syn_cima (syn_ccnv F) A)))
      (syn_cima F (syn_cima (syn_ccnv F) A)) p0001 p0002
  have p0004 := @g_dfrn4 F
  have p0005 := @g_ineq2i (syn_crn F) (syn_cdm (syn_ccnv F)) A p0004
  have p0006 := @g_dmres (syn_ccnv F) A
  have p0007 := (Nominal.classEqRefl (syn_cdm (syn_cres (syn_ccnv F) A)))
  have p0008 :=
    @g_n_3eqtr2ri (syn_cin A (syn_crn F)) (syn_cin A (syn_cdm (syn_ccnv F)))
      (syn_cdm (syn_cres (syn_ccnv F) A)) (syn_crn (syn_ccnv (syn_cres (syn_ccnv F) A)))
      p0005 p0006 p0007
  have p0009 :=
    @g_syl6eq (syn_wfun F) (syn_cima F (syn_cima (syn_ccnv F) A))
      (syn_crn (syn_ccnv (syn_cres (syn_ccnv F) A))) (syn_cin A (syn_crn F)) p0003 p0008
  exact p0009

@[expose]
noncomputable def g_funimass2 (A : Class) (B : Class) (F : Class) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wfun F) (syn_wss A (syn_cima (syn_ccnv F) B)))
        (syn_wss (syn_cima F A) B)) :=
  by
  have p0000 := @g_imass2 A (syn_cima (syn_ccnv F) B) F
  have p0001 := @g_funimacnv B F
  have p0002 :=
    @g_sseq2d (syn_wfun F) (syn_cima F (syn_cima (syn_ccnv F) B)) (syn_cin B (syn_crn F))
      (syn_cima F A) p0001
  have p0003 := @g_inss1 B (syn_crn F)
  have p0004 := @g_sstr2 (syn_cima F A) (syn_cin B (syn_crn F)) B
  have p0005 :=
    @g_mpi (syn_wss (syn_cima F A) (syn_cin B (syn_crn F)))
      (syn_wss (syn_cin B (syn_crn F)) B) (syn_wss (syn_cima F A) B) p0003 p0004
  have p0006 :=
    @g_syl6bi (syn_wfun F) (syn_wss (syn_cima F A) (syn_cima F (syn_cima (syn_ccnv F) B)))
      (syn_wss (syn_cima F A) (syn_cin B (syn_crn F))) (syn_wss (syn_cima F A) B) p0002
      p0005
  have p0007 :=
    @g_imp (syn_wfun F) (syn_wss (syn_cima F A) (syn_cima F (syn_cima (syn_ccnv F) B)))
      (syn_wss (syn_cima F A) B) p0006
  have p0008 :=
    @g_sylan2 (syn_wss A (syn_cima (syn_ccnv F) B)) (syn_wfun F)
      (syn_wss (syn_cima F A) (syn_cima F (syn_cima (syn_ccnv F) B)))
      (syn_wss (syn_cima F A) B) p0000 p0007
  exact p0008


end NFChoice.DirectNominalPrf.WPPReplay

end
