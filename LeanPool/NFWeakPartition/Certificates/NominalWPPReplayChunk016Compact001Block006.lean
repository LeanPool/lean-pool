/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NominalWPPReplayChunk016Compact001Block005

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NominalWPPReplayChunk016Compact001Part026`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_sifrndv (D : Class) (R : Class) :
    Nominal.NPrf
      (.imp (syn_wbr R (syn_cwe) D) (syn_wbr (syn_csi R) (syn_cfound) (syn_cpw1 D))) :=
  by
  let proofSupport : Finset Var := D.fv ∪ R.fv
  let x : Var := freshVar proofSupport 0
  let z : Var := freshVar proofSupport 1
  let y : Var := freshVar proofSupport 2
  let v : Var := freshVar proofSupport 3
  let u : Var := freshVar proofSupport 4
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_D : x ∉ D.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_not_R : x ∉ R.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_z_not_D : z ∉ D.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (h))
  have fresh_z_not_R : z ∉ R.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_y_not_D : y ∉ D.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (h))
  have fresh_y_not_R : y ∉ R.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_v : v ∉ proofSupport :=
    by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_v_not_R : v ∉ R.fv := by
    intro h
    exact fresh_v (Finset.mem_union_right _ (h))
  have fresh_u : u ∉ proofSupport :=
    by
    change freshVar proofSupport 4 ∉ proofSupport
    exact freshVar_not_mem proofSupport 4
  have fresh_u_not_D : u ∉ D.fv := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (h))
  have fresh_u_not_R : u ∉ R.fv := by
    intro h
    exact fresh_u (Finset.mem_union_right _ (h))
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
  have fresh_x_ne_v : x ≠ v :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_v_ne_x : v ≠ x := Ne.symm fresh_x_ne_v
  have fresh_x_ne_u : x ≠ u :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 0) (j := 4) (by decide)
  have fresh_u_ne_x : u ≠ x := Ne.symm fresh_x_ne_u
  have fresh_z_ne_y : z ≠ y :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_y_ne_z : y ≠ z := Ne.symm fresh_z_ne_y
  have fresh_z_ne_v : z ≠ v :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_v_ne_z : v ≠ z := Ne.symm fresh_z_ne_v
  have fresh_z_ne_u : z ≠ u :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 1) (j := 4) (by decide)
  have fresh_u_ne_z : u ≠ z := Ne.symm fresh_z_ne_u
  have fresh_y_ne_u : y ≠ u :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 2) (j := 4) (by decide)
  have fresh_u_ne_y : u ≠ y := Ne.symm fresh_y_ne_u
  have fresh_v_ne_u : v ≠ u :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 3) (j := 4) (by decide)
  have fresh_u_ne_v : u ≠ v := Ne.symm fresh_v_ne_u
  have dv_cache_0001 : u ∉ (R).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_u_not_R, not_false_eq_true])
  have dv_cache_0002 : v ∉ (R).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_v_not_R, not_false_eq_true])
  have dv_cache_0003 : u ∉ ((syn_cuni (.cv x))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_u_ne_x,
          not_false_eq_true])
  have dv_cache_0004 : v ∉ ((syn_cuni (.cv x))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_v_ne_x,
          not_false_eq_true])
  have dv_cache_0005 : u ≠ v :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show u ≠ v from (by exact fresh_u_ne_v))
  have dv_cache_0006 : v ∉ ((syn_cuni (.cv z))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_v_ne_z,
          not_false_eq_true])
  have dv_cache_0007 :
    v ∉
      ((Wff.imp (syn_wbr (syn_cuni (.cv z)) R (.cv u))
          (.classEq (syn_cuni (.cv z)) (.cv u)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union,
          Finset.mem_singleton, fresh_v_ne_z, fresh_v_ne_u, fresh_v_not_R, or_false,
          not_false_eq_true])
  have dv_cache_0008 :
    z ∉
      ((syn_wa (syn_wa (syn_wbr R (syn_cwe) D)
            (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0))))
          (syn_wa (.classMem (.cv u) (syn_cuni (.cv x))) (syn_wral v (syn_cuni (.cv x))
              (.imp (syn_wbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
          NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_z_not_R, fresh_z_not_D, fresh_z_ne_x, fresh_z_ne_u,
          fresh_z_ne_v, compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0009 : z ∉ ((Wff.classEq (.cv y) (syn_csn (.cv u)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_y, fresh_z_ne_u, or_false, not_false_eq_true])
  have dv_cache_0010 : y ∉ ((syn_csn (.cv u))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_y_ne_u,
          not_false_eq_true])
  have dv_cache_0011 : y ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_y_ne_x, not_false_eq_true])
  have dv_cache_0012 :
    y ∉
      ((syn_wral z (.cv x) (.imp (syn_wbr (.cv z) (syn_csi R) (syn_csn (.cv u)))
            (.classEq (.cv z) (syn_csn (.cv u)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_y_ne_x, fresh_y_ne_z, fresh_y_ne_u, fresh_y_not_R,
          or_false, and_false, not_false_eq_true])
  have dv_cache_0013 :
    u ∉
      ((syn_wrex y (.cv x) (syn_wral z (.cv x) (.imp (syn_wbr (.cv z) (syn_csi R) (.cv y))
              (.classEq (.cv z) (.cv y)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
          NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_u_ne_x, fresh_u_ne_z, fresh_u_ne_y, fresh_u_not_R,
          or_false, and_false, not_false_eq_true])
  have dv_cache_0014 :
    u ∉
      ((syn_wa (syn_wbr R (syn_cwe) D)
          (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union,
          Finset.mem_singleton, fresh_u_not_R, fresh_u_not_D, fresh_u_ne_x,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0015 : x ∉ ((syn_cpw1 D)).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, fresh_x_not_D,
          not_false_eq_true])
  have dv_cache_0016 : z ∉ ((syn_cpw1 D)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, fresh_z_not_D,
          not_false_eq_true])
  have dv_cache_0017 : y ∉ ((syn_cpw1 D)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, fresh_y_not_D,
          not_false_eq_true])
  have dv_cache_0018 : x ∉ ((syn_csi R)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi, fresh_x_not_R,
          not_false_eq_true])
  have dv_cache_0019 : z ∉ ((syn_csi R)).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi, fresh_z_not_R,
          not_false_eq_true])
  have dv_cache_0020 : y ∉ ((syn_csi R)).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi, fresh_y_not_R,
          not_false_eq_true])
  have dv_cache_0021 : x ∉ ((syn_wbr R (syn_cwe) D)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe, Finset.mem_union,
          fresh_x_not_R, fresh_x_not_D, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0022 : x ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact (show x ≠ z from (by exact fresh_x_ne_z))
  have dv_cache_0023 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0024 : z ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
    exact (show z ≠ y from (by exact fresh_z_ne_y))
  have p0000 := @g_brex R D (syn_cwe)
  have p0001 :=
    @g_simpld (syn_wbr R (syn_cwe) D) (.classMem R (syn_cvv)) (.classMem D (syn_cvv))
      p0000
  have p0002 := @g_siexg R (syn_cvv)
  have p0003 :=
    @g_syl (syn_wbr R (syn_cwe) D) (.classMem R (syn_cvv))
      (.classMem (syn_csi R) (syn_cvv)) p0001 p0002
  have p0005 :=
    @g_simprd (syn_wbr R (syn_cwe) D) (.classMem R (syn_cvv)) (.classMem D (syn_cvv))
      p0000
  have p0006 := @g_pw1exg D (syn_cvv)
  have p0007 :=
    @g_syl (syn_wbr R (syn_cwe) D) (.classMem D (syn_cvv))
      (.classMem (syn_cpw1 D) (syn_cvv)) p0005 p0006
  have p0008 :=
    @g_simpl (syn_wbr R (syn_cwe) D)
      (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0)))
  have p0009 := (Nominal.classEqRefl (syn_cwe))
  have p0010 := @g_breqi R D (syn_cwe) (syn_cin (syn_cstrict) (syn_cfound)) p0009
  have p0011 := @g_brin R D (syn_cstrict) (syn_cfound)
  have p0012 :=
    @g_bitri (syn_wbr R (syn_cwe) D) (syn_wbr R (syn_cin (syn_cstrict) (syn_cfound)) D)
      (syn_wa (syn_wbr R (syn_cstrict) D) (syn_wbr R (syn_cfound) D)) p0010 p0011
  have p0013 :=
    @g_simprbi (syn_wbr R (syn_cwe) D) (syn_wbr R (syn_cstrict) D)
      (syn_wbr R (syn_cfound) D) p0012
  have p0014 :=
    @g_syl
      (syn_wa (syn_wbr R (syn_cwe) D)
        (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0))))
      (syn_wbr R (syn_cwe) D) (syn_wbr R (syn_cfound) D) p0008 p0013
  have p0015 := @g_vex x
  have p0016 := @g_uniex (.cv x) p0015
  have p0017 :=
    @g_a1i (.classMem (syn_cuni (.cv x)) (syn_cvv))
      (syn_wa (syn_wbr R (syn_cwe) D)
        (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0))))
      p0016
  have p0018 :=
    @g_simpr (syn_wbr R (syn_cwe) D)
      (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0)))
  have p0019 := @g_simpl (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0))
  have p0020 :=
    @g_syl
      (syn_wa (syn_wbr R (syn_cwe) D)
        (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0))))
      (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0)))
      (syn_wss (.cv x) (syn_cpw1 D)) p0018 p0019
  have p0021 := @g_pw1subuniss x D
  have p0022 :=
    @g_syl
      (syn_wa (syn_wbr R (syn_cwe) D)
        (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0))))
      (syn_wss (.cv x) (syn_cpw1 D)) (syn_wss (syn_cuni (.cv x)) D) p0020 p0021
  have p0023 :=
    @g_simpr (syn_wbr R (syn_cwe) D)
      (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0)))
  have p0024 := @g_pw1subunine x D
  have p0025 :=
    @g_syl
      (syn_wa (syn_wbr R (syn_cwe) D)
        (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0))))
      (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0)))
      (syn_wne (syn_cuni (.cv x)) (syn_c0)) p0023 p0024
  have p0026 :=
    @g_frd
      (syn_wa (syn_wbr R (syn_cwe) D)
        (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0))))
      u v D R (syn_cvv) (syn_cuni (.cv x)) dv_cache_0001 dv_cache_0002 dv_cache_0003
      dv_cache_0004 dv_cache_0005 p0014 p0017 p0022 p0025
  have p0027 :=
    @g_simpr
      (syn_wa (syn_wbr R (syn_cwe) D)
        (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0))))
      (syn_wa (.classMem (.cv u) (syn_cuni (.cv x))) (syn_wral v (syn_cuni (.cv x))
          (.imp (syn_wbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u)))))
  have p0028 :=
    @g_simpl (.classMem (.cv u) (syn_cuni (.cv x)))
      (syn_wral v (syn_cuni (.cv x))
        (.imp (syn_wbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u))))
  have p0029 :=
    @g_syl
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) D)
          (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0))))
        (syn_wa (.classMem (.cv u) (syn_cuni (.cv x))) (syn_wral v (syn_cuni (.cv x))
            (.imp (syn_wbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u))))))
      (syn_wa (.classMem (.cv u) (syn_cuni (.cv x))) (syn_wral v (syn_cuni (.cv x))
          (.imp (syn_wbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u)))))
      (.classMem (.cv u) (syn_cuni (.cv x))) p0027 p0028
  have p0030 := @g_snelpw1 (.cv u) (syn_cuni (.cv x))
  have p0031 :=
    @g_biimpri (.classMem (syn_csn (.cv u)) (syn_cpw1 (syn_cuni (.cv x))))
      (.classMem (.cv u) (syn_cuni (.cv x))) p0030
  have p0032 :=
    @g_syl
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) D)
          (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0))))
        (syn_wa (.classMem (.cv u) (syn_cuni (.cv x))) (syn_wral v (syn_cuni (.cv x))
            (.imp (syn_wbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u))))))
      (.classMem (.cv u) (syn_cuni (.cv x)))
      (.classMem (syn_csn (.cv u)) (syn_cpw1 (syn_cuni (.cv x)))) p0029 p0031
  have p0033 :=
    @g_simpl
      (syn_wa (syn_wbr R (syn_cwe) D)
        (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0))))
      (syn_wa (.classMem (.cv u) (syn_cuni (.cv x))) (syn_wral v (syn_cuni (.cv x))
          (.imp (syn_wbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u)))))
  have p0034 :=
    @g_simpr (syn_wbr R (syn_cwe) D)
      (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0)))
  have p0035 := @g_simpl (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0))
  have p0036 :=
    @g_syl
      (syn_wa (syn_wbr R (syn_cwe) D)
        (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0))))
      (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0)))
      (syn_wss (.cv x) (syn_cpw1 D)) p0034 p0035
  have p0037 := @g_pw1ss1c D
  have p0038 :=
    @g_a1i (syn_wss (syn_cpw1 D) (syn_c1c))
      (syn_wa (syn_wbr R (syn_cwe) D)
        (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0))))
      p0037
  have p0039 :=
    @g_sstrd
      (syn_wa (syn_wbr R (syn_cwe) D)
        (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0))))
      (.cv x) (syn_cpw1 D) (syn_c1c) p0036 p0038
  have p0040 := @g_eqpw1uni (.cv x)
  have p0041 :=
    @g_syl
      (syn_wa (syn_wbr R (syn_cwe) D)
        (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0))))
      (syn_wss (.cv x) (syn_c1c)) (.classEq (.cv x) (syn_cpw1 (syn_cuni (.cv x)))) p0039
      p0040
  have p0042 :=
    @g_syl
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) D)
          (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0))))
        (syn_wa (.classMem (.cv u) (syn_cuni (.cv x))) (syn_wral v (syn_cuni (.cv x))
            (.imp (syn_wbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u))))))
      (syn_wa (syn_wbr R (syn_cwe) D)
        (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0))))
      (.classEq (.cv x) (syn_cpw1 (syn_cuni (.cv x)))) p0033 p0041
  have p0043 :=
    @g_eleqtrrd
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) D)
          (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0))))
        (syn_wa (.classMem (.cv u) (syn_cuni (.cv x))) (syn_wral v (syn_cuni (.cv x))
            (.imp (syn_wbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u))))))
      (syn_csn (.cv u)) (syn_cpw1 (syn_cuni (.cv x))) (.cv x) p0032 p0042
  have p0044 :=
    @g_simpl
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D)
            (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0))))
          (syn_wa (.classMem (.cv u) (syn_cuni (.cv x))) (syn_wral v (syn_cuni (.cv x))
              (.imp (syn_wbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u))))))
        (.classMem (.cv z) (.cv x)))
      (syn_wbr (.cv z) (syn_csi R) (syn_csn (.cv u)))
  have p0045 :=
    @g_simpr
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) D)
          (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0))))
        (syn_wa (.classMem (.cv u) (syn_cuni (.cv x))) (syn_wral v (syn_cuni (.cv x))
            (.imp (syn_wbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u))))))
      (.classMem (.cv z) (.cv x))
  have p0046 :=
    @g_simpl
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) D)
          (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0))))
        (syn_wa (.classMem (.cv u) (syn_cuni (.cv x))) (syn_wral v (syn_cuni (.cv x))
            (.imp (syn_wbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u))))))
      (.classMem (.cv z) (.cv x))
  have p0047 :=
    @g_simpl
      (syn_wa (syn_wbr R (syn_cwe) D)
        (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0))))
      (syn_wa (.classMem (.cv u) (syn_cuni (.cv x))) (syn_wral v (syn_cuni (.cv x))
          (.imp (syn_wbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u)))))
  have p0048 :=
    @g_simpr (syn_wbr R (syn_cwe) D)
      (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0)))
  have p0049 := @g_simpl (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0))
  have p0050 :=
    @g_syl
      (syn_wa (syn_wbr R (syn_cwe) D)
        (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0))))
      (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0)))
      (syn_wss (.cv x) (syn_cpw1 D)) p0048 p0049
  have p0051 := @g_pw1ss1c D
  have p0052 :=
    @g_a1i (syn_wss (syn_cpw1 D) (syn_c1c))
      (syn_wa (syn_wbr R (syn_cwe) D)
        (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0))))
      p0051
  have p0053 :=
    @g_sstrd
      (syn_wa (syn_wbr R (syn_cwe) D)
        (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0))))
      (.cv x) (syn_cpw1 D) (syn_c1c) p0050 p0052
  have p0054 := @g_eqpw1uni (.cv x)
  have p0055 :=
    @g_syl
      (syn_wa (syn_wbr R (syn_cwe) D)
        (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0))))
      (syn_wss (.cv x) (syn_c1c)) (.classEq (.cv x) (syn_cpw1 (syn_cuni (.cv x)))) p0053
      p0054
  have p0056 :=
    @g_syl
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) D)
          (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0))))
        (syn_wa (.classMem (.cv u) (syn_cuni (.cv x))) (syn_wral v (syn_cuni (.cv x))
            (.imp (syn_wbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u))))))
      (syn_wa (syn_wbr R (syn_cwe) D)
        (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0))))
      (.classEq (.cv x) (syn_cpw1 (syn_cuni (.cv x)))) p0047 p0055
  have p0057 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D)
            (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0))))
          (syn_wa (.classMem (.cv u) (syn_cuni (.cv x))) (syn_wral v (syn_cuni (.cv x))
              (.imp (syn_wbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u))))))
        (.classMem (.cv z) (.cv x)))
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) D)
          (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0))))
        (syn_wa (.classMem (.cv u) (syn_cuni (.cv x))) (syn_wral v (syn_cuni (.cv x))
            (.imp (syn_wbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u))))))
      (.classEq (.cv x) (syn_cpw1 (syn_cuni (.cv x)))) p0046 p0056
  have p0058 :=
    @g_eleqtrd
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D)
            (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0))))
          (syn_wa (.classMem (.cv u) (syn_cuni (.cv x))) (syn_wral v (syn_cuni (.cv x))
              (.imp (syn_wbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u))))))
        (.classMem (.cv z) (.cv x)))
      (.cv z) (.cv x) (syn_cpw1 (syn_cuni (.cv x))) p0045 p0057
  have p0059 := @g_hnwpw1argcl (syn_cuni (.cv x)) z
  have p0060 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D)
            (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0))))
          (syn_wa (.classMem (.cv u) (syn_cuni (.cv x))) (syn_wral v (syn_cuni (.cv x))
              (.imp (syn_wbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u))))))
        (.classMem (.cv z) (.cv x)))
      (.classMem (.cv z) (syn_cpw1 (syn_cuni (.cv x))))
      (syn_wa (.classMem (syn_cuni (.cv z)) (syn_cuni (.cv x)))
        (.classEq (.cv z) (syn_csn (syn_cuni (.cv z)))))
      p0058 p0059
  have p0061 :=
    @g_simprd
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D)
            (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0))))
          (syn_wa (.classMem (.cv u) (syn_cuni (.cv x))) (syn_wral v (syn_cuni (.cv x))
              (.imp (syn_wbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u))))))
        (.classMem (.cv z) (.cv x)))
      (.classMem (syn_cuni (.cv z)) (syn_cuni (.cv x)))
      (.classEq (.cv z) (syn_csn (syn_cuni (.cv z)))) p0060
  have p0062 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D)
              (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0))))
            (syn_wa (.classMem (.cv u) (syn_cuni (.cv x))) (syn_wral v (syn_cuni (.cv x))
                (.imp (syn_wbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u))))))
          (.classMem (.cv z) (.cv x))) (syn_wbr (.cv z) (syn_csi R) (syn_csn (.cv u))))
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D)
            (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0))))
          (syn_wa (.classMem (.cv u) (syn_cuni (.cv x))) (syn_wral v (syn_cuni (.cv x))
              (.imp (syn_wbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u))))))
        (.classMem (.cv z) (.cv x)))
      (.classEq (.cv z) (syn_csn (syn_cuni (.cv z)))) p0044 p0061
  have p0063 :=
    @g_simpr
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D)
            (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0))))
          (syn_wa (.classMem (.cv u) (syn_cuni (.cv x))) (syn_wral v (syn_cuni (.cv x))
              (.imp (syn_wbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u))))))
        (.classMem (.cv z) (.cv x)))
      (syn_wbr (.cv z) (syn_csi R) (syn_csn (.cv u)))
  have p0064 :=
    @g_simpl
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D)
            (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0))))
          (syn_wa (.classMem (.cv u) (syn_cuni (.cv x))) (syn_wral v (syn_cuni (.cv x))
              (.imp (syn_wbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u))))))
        (.classMem (.cv z) (.cv x)))
      (syn_wbr (.cv z) (syn_csi R) (syn_csn (.cv u)))
  have p0065 :=
    @g_simpr
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) D)
          (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0))))
        (syn_wa (.classMem (.cv u) (syn_cuni (.cv x))) (syn_wral v (syn_cuni (.cv x))
            (.imp (syn_wbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u))))))
      (.classMem (.cv z) (.cv x))
  have p0066 :=
    @g_simpl
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) D)
          (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0))))
        (syn_wa (.classMem (.cv u) (syn_cuni (.cv x))) (syn_wral v (syn_cuni (.cv x))
            (.imp (syn_wbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u))))))
      (.classMem (.cv z) (.cv x))
  have p0067 :=
    @g_simpl
      (syn_wa (syn_wbr R (syn_cwe) D)
        (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0))))
      (syn_wa (.classMem (.cv u) (syn_cuni (.cv x))) (syn_wral v (syn_cuni (.cv x))
          (.imp (syn_wbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u)))))
  have p0068 :=
    @g_simpr (syn_wbr R (syn_cwe) D)
      (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0)))
  have p0069 := @g_simpl (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0))
  have p0070 :=
    @g_syl
      (syn_wa (syn_wbr R (syn_cwe) D)
        (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0))))
      (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0)))
      (syn_wss (.cv x) (syn_cpw1 D)) p0068 p0069
  have p0071 := @g_pw1ss1c D
  have p0072 :=
    @g_a1i (syn_wss (syn_cpw1 D) (syn_c1c))
      (syn_wa (syn_wbr R (syn_cwe) D)
        (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0))))
      p0071
  have p0073 :=
    @g_sstrd
      (syn_wa (syn_wbr R (syn_cwe) D)
        (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0))))
      (.cv x) (syn_cpw1 D) (syn_c1c) p0070 p0072
  have p0074 := @g_eqpw1uni (.cv x)
  have p0075 :=
    @g_syl
      (syn_wa (syn_wbr R (syn_cwe) D)
        (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0))))
      (syn_wss (.cv x) (syn_c1c)) (.classEq (.cv x) (syn_cpw1 (syn_cuni (.cv x)))) p0073
      p0074
  have p0076 :=
    @g_syl
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) D)
          (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0))))
        (syn_wa (.classMem (.cv u) (syn_cuni (.cv x))) (syn_wral v (syn_cuni (.cv x))
            (.imp (syn_wbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u))))))
      (syn_wa (syn_wbr R (syn_cwe) D)
        (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0))))
      (.classEq (.cv x) (syn_cpw1 (syn_cuni (.cv x)))) p0067 p0075
  have p0077 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D)
            (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0))))
          (syn_wa (.classMem (.cv u) (syn_cuni (.cv x))) (syn_wral v (syn_cuni (.cv x))
              (.imp (syn_wbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u))))))
        (.classMem (.cv z) (.cv x)))
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) D)
          (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0))))
        (syn_wa (.classMem (.cv u) (syn_cuni (.cv x))) (syn_wral v (syn_cuni (.cv x))
            (.imp (syn_wbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u))))))
      (.classEq (.cv x) (syn_cpw1 (syn_cuni (.cv x)))) p0066 p0076
  have p0078 :=
    @g_eleqtrd
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D)
            (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0))))
          (syn_wa (.classMem (.cv u) (syn_cuni (.cv x))) (syn_wral v (syn_cuni (.cv x))
              (.imp (syn_wbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u))))))
        (.classMem (.cv z) (.cv x)))
      (.cv z) (.cv x) (syn_cpw1 (syn_cuni (.cv x))) p0065 p0077
  have p0079 := @g_hnwpw1argcl (syn_cuni (.cv x)) z
  have p0080 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D)
            (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0))))
          (syn_wa (.classMem (.cv u) (syn_cuni (.cv x))) (syn_wral v (syn_cuni (.cv x))
              (.imp (syn_wbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u))))))
        (.classMem (.cv z) (.cv x)))
      (.classMem (.cv z) (syn_cpw1 (syn_cuni (.cv x))))
      (syn_wa (.classMem (syn_cuni (.cv z)) (syn_cuni (.cv x)))
        (.classEq (.cv z) (syn_csn (syn_cuni (.cv z)))))
      p0078 p0079
  have p0081 :=
    @g_simprd
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D)
            (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0))))
          (syn_wa (.classMem (.cv u) (syn_cuni (.cv x))) (syn_wral v (syn_cuni (.cv x))
              (.imp (syn_wbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u))))))
        (.classMem (.cv z) (.cv x)))
      (.classMem (syn_cuni (.cv z)) (syn_cuni (.cv x)))
      (.classEq (.cv z) (syn_csn (syn_cuni (.cv z)))) p0080
  have p0082 :=
    @g_breq1d
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D)
            (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0))))
          (syn_wa (.classMem (.cv u) (syn_cuni (.cv x))) (syn_wral v (syn_cuni (.cv x))
              (.imp (syn_wbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u))))))
        (.classMem (.cv z) (.cv x)))
      (.cv z) (syn_csn (syn_cuni (.cv z))) (syn_csn (.cv u)) (syn_csi R) p0081
  have p0083 := @g_vex z
  have p0084 := @g_uniex (.cv z) p0083
  have p0085 := @g_vex u
  have p0086 := @g_brsnsi (syn_cuni (.cv z)) (.cv u) R p0084 p0085
  have p0087 :=
    @g_a1i
      (syn_wb (syn_wbr (syn_csn (syn_cuni (.cv z))) (syn_csi R) (syn_csn (.cv u)))
        (syn_wbr (syn_cuni (.cv z)) R (.cv u)))
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D)
            (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0))))
          (syn_wa (.classMem (.cv u) (syn_cuni (.cv x))) (syn_wral v (syn_cuni (.cv x))
              (.imp (syn_wbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u))))))
        (.classMem (.cv z) (.cv x)))
      p0086
  have p0088 :=
    @g_bitrd
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D)
            (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0))))
          (syn_wa (.classMem (.cv u) (syn_cuni (.cv x))) (syn_wral v (syn_cuni (.cv x))
              (.imp (syn_wbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u))))))
        (.classMem (.cv z) (.cv x)))
      (syn_wbr (.cv z) (syn_csi R) (syn_csn (.cv u)))
      (syn_wbr (syn_csn (syn_cuni (.cv z))) (syn_csi R) (syn_csn (.cv u)))
      (syn_wbr (syn_cuni (.cv z)) R (.cv u)) p0082 p0087
  have p0089 :=
    @g_biimpd
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D)
            (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0))))
          (syn_wa (.classMem (.cv u) (syn_cuni (.cv x))) (syn_wral v (syn_cuni (.cv x))
              (.imp (syn_wbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u))))))
        (.classMem (.cv z) (.cv x)))
      (syn_wbr (.cv z) (syn_csi R) (syn_csn (.cv u)))
      (syn_wbr (syn_cuni (.cv z)) R (.cv u)) p0088
  have p0090 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D)
              (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0))))
            (syn_wa (.classMem (.cv u) (syn_cuni (.cv x))) (syn_wral v (syn_cuni (.cv x))
                (.imp (syn_wbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u))))))
          (.classMem (.cv z) (.cv x))) (syn_wbr (.cv z) (syn_csi R) (syn_csn (.cv u))))
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D)
            (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0))))
          (syn_wa (.classMem (.cv u) (syn_cuni (.cv x))) (syn_wral v (syn_cuni (.cv x))
              (.imp (syn_wbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u))))))
        (.classMem (.cv z) (.cv x)))
      (.imp (syn_wbr (.cv z) (syn_csi R) (syn_csn (.cv u)))
        (syn_wbr (syn_cuni (.cv z)) R (.cv u)))
      p0064 p0089
  have p0091 :=
    @g_mpd
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D)
              (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0))))
            (syn_wa (.classMem (.cv u) (syn_cuni (.cv x))) (syn_wral v (syn_cuni (.cv x))
                (.imp (syn_wbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u))))))
          (.classMem (.cv z) (.cv x))) (syn_wbr (.cv z) (syn_csi R) (syn_csn (.cv u))))
      (syn_wbr (.cv z) (syn_csi R) (syn_csn (.cv u)))
      (syn_wbr (syn_cuni (.cv z)) R (.cv u)) p0063 p0090
  have p0092 :=
    @g_simpl
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D)
            (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0))))
          (syn_wa (.classMem (.cv u) (syn_cuni (.cv x))) (syn_wral v (syn_cuni (.cv x))
              (.imp (syn_wbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u))))))
        (.classMem (.cv z) (.cv x)))
      (syn_wbr (.cv z) (syn_csi R) (syn_csn (.cv u)))
  have p0093 :=
    @g_simpl
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) D)
          (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0))))
        (syn_wa (.classMem (.cv u) (syn_cuni (.cv x))) (syn_wral v (syn_cuni (.cv x))
            (.imp (syn_wbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u))))))
      (.classMem (.cv z) (.cv x))
  have p0094 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D)
              (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0))))
            (syn_wa (.classMem (.cv u) (syn_cuni (.cv x))) (syn_wral v (syn_cuni (.cv x))
                (.imp (syn_wbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u))))))
          (.classMem (.cv z) (.cv x))) (syn_wbr (.cv z) (syn_csi R) (syn_csn (.cv u))))
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D)
            (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0))))
          (syn_wa (.classMem (.cv u) (syn_cuni (.cv x))) (syn_wral v (syn_cuni (.cv x))
              (.imp (syn_wbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u))))))
        (.classMem (.cv z) (.cv x)))
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) D)
          (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0))))
        (syn_wa (.classMem (.cv u) (syn_cuni (.cv x))) (syn_wral v (syn_cuni (.cv x))
            (.imp (syn_wbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u))))))
      p0092 p0093
  have p0095 :=
    @g_simpr
      (syn_wa (syn_wbr R (syn_cwe) D)
        (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0))))
      (syn_wa (.classMem (.cv u) (syn_cuni (.cv x))) (syn_wral v (syn_cuni (.cv x))
          (.imp (syn_wbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u)))))
  have p0096 :=
    @g_simpr (.classMem (.cv u) (syn_cuni (.cv x)))
      (syn_wral v (syn_cuni (.cv x))
        (.imp (syn_wbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u))))
  have p0097 :=
    @g_syl
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) D)
          (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0))))
        (syn_wa (.classMem (.cv u) (syn_cuni (.cv x))) (syn_wral v (syn_cuni (.cv x))
            (.imp (syn_wbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u))))))
      (syn_wa (.classMem (.cv u) (syn_cuni (.cv x))) (syn_wral v (syn_cuni (.cv x))
          (.imp (syn_wbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u)))))
      (syn_wral v (syn_cuni (.cv x))
        (.imp (syn_wbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u))))
      p0095 p0096
  have p0098 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D)
              (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0))))
            (syn_wa (.classMem (.cv u) (syn_cuni (.cv x))) (syn_wral v (syn_cuni (.cv x))
                (.imp (syn_wbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u))))))
          (.classMem (.cv z) (.cv x))) (syn_wbr (.cv z) (syn_csi R) (syn_csn (.cv u))))
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) D)
          (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0))))
        (syn_wa (.classMem (.cv u) (syn_cuni (.cv x))) (syn_wral v (syn_cuni (.cv x))
            (.imp (syn_wbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u))))))
      (syn_wral v (syn_cuni (.cv x))
        (.imp (syn_wbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u))))
      p0094 p0097
  have p0099 :=
    @g_simpl
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D)
            (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0))))
          (syn_wa (.classMem (.cv u) (syn_cuni (.cv x))) (syn_wral v (syn_cuni (.cv x))
              (.imp (syn_wbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u))))))
        (.classMem (.cv z) (.cv x)))
      (syn_wbr (.cv z) (syn_csi R) (syn_csn (.cv u)))
  have p0100 :=
    @g_simpr
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) D)
          (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0))))
        (syn_wa (.classMem (.cv u) (syn_cuni (.cv x))) (syn_wral v (syn_cuni (.cv x))
            (.imp (syn_wbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u))))))
      (.classMem (.cv z) (.cv x))
  have p0101 :=
    @g_simpl
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) D)
          (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0))))
        (syn_wa (.classMem (.cv u) (syn_cuni (.cv x))) (syn_wral v (syn_cuni (.cv x))
            (.imp (syn_wbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u))))))
      (.classMem (.cv z) (.cv x))
  have p0102 :=
    @g_simpl
      (syn_wa (syn_wbr R (syn_cwe) D)
        (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0))))
      (syn_wa (.classMem (.cv u) (syn_cuni (.cv x))) (syn_wral v (syn_cuni (.cv x))
          (.imp (syn_wbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u)))))
  have p0103 :=
    @g_simpr (syn_wbr R (syn_cwe) D)
      (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0)))
  have p0104 := @g_simpl (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0))
  have p0105 :=
    @g_syl
      (syn_wa (syn_wbr R (syn_cwe) D)
        (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0))))
      (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0)))
      (syn_wss (.cv x) (syn_cpw1 D)) p0103 p0104
  have p0106 := @g_pw1ss1c D
  have p0107 :=
    @g_a1i (syn_wss (syn_cpw1 D) (syn_c1c))
      (syn_wa (syn_wbr R (syn_cwe) D)
        (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0))))
      p0106
  have p0108 :=
    @g_sstrd
      (syn_wa (syn_wbr R (syn_cwe) D)
        (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0))))
      (.cv x) (syn_cpw1 D) (syn_c1c) p0105 p0107
  have p0109 := @g_eqpw1uni (.cv x)
  have p0110 :=
    @g_syl
      (syn_wa (syn_wbr R (syn_cwe) D)
        (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0))))
      (syn_wss (.cv x) (syn_c1c)) (.classEq (.cv x) (syn_cpw1 (syn_cuni (.cv x)))) p0108
      p0109
  have p0111 :=
    @g_syl
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) D)
          (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0))))
        (syn_wa (.classMem (.cv u) (syn_cuni (.cv x))) (syn_wral v (syn_cuni (.cv x))
            (.imp (syn_wbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u))))))
      (syn_wa (syn_wbr R (syn_cwe) D)
        (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0))))
      (.classEq (.cv x) (syn_cpw1 (syn_cuni (.cv x)))) p0102 p0110
  have p0112 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D)
            (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0))))
          (syn_wa (.classMem (.cv u) (syn_cuni (.cv x))) (syn_wral v (syn_cuni (.cv x))
              (.imp (syn_wbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u))))))
        (.classMem (.cv z) (.cv x)))
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) D)
          (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0))))
        (syn_wa (.classMem (.cv u) (syn_cuni (.cv x))) (syn_wral v (syn_cuni (.cv x))
            (.imp (syn_wbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u))))))
      (.classEq (.cv x) (syn_cpw1 (syn_cuni (.cv x)))) p0101 p0111
  have p0113 :=
    @g_eleqtrd
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D)
            (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0))))
          (syn_wa (.classMem (.cv u) (syn_cuni (.cv x))) (syn_wral v (syn_cuni (.cv x))
              (.imp (syn_wbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u))))))
        (.classMem (.cv z) (.cv x)))
      (.cv z) (.cv x) (syn_cpw1 (syn_cuni (.cv x))) p0100 p0112
  have p0114 := @g_hnwpw1argcl (syn_cuni (.cv x)) z
  have p0115 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D)
            (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0))))
          (syn_wa (.classMem (.cv u) (syn_cuni (.cv x))) (syn_wral v (syn_cuni (.cv x))
              (.imp (syn_wbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u))))))
        (.classMem (.cv z) (.cv x)))
      (.classMem (.cv z) (syn_cpw1 (syn_cuni (.cv x))))
      (syn_wa (.classMem (syn_cuni (.cv z)) (syn_cuni (.cv x)))
        (.classEq (.cv z) (syn_csn (syn_cuni (.cv z)))))
      p0113 p0114
  have p0116 :=
    @g_simpld
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D)
            (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0))))
          (syn_wa (.classMem (.cv u) (syn_cuni (.cv x))) (syn_wral v (syn_cuni (.cv x))
              (.imp (syn_wbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u))))))
        (.classMem (.cv z) (.cv x)))
      (.classMem (syn_cuni (.cv z)) (syn_cuni (.cv x)))
      (.classEq (.cv z) (syn_csn (syn_cuni (.cv z)))) p0115
  have p0117 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D)
              (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0))))
            (syn_wa (.classMem (.cv u) (syn_cuni (.cv x))) (syn_wral v (syn_cuni (.cv x))
                (.imp (syn_wbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u))))))
          (.classMem (.cv z) (.cv x))) (syn_wbr (.cv z) (syn_csi R) (syn_csn (.cv u))))
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D)
            (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0))))
          (syn_wa (.classMem (.cv u) (syn_cuni (.cv x))) (syn_wral v (syn_cuni (.cv x))
              (.imp (syn_wbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u))))))
        (.classMem (.cv z) (.cv x)))
      (.classMem (syn_cuni (.cv z)) (syn_cuni (.cv x))) p0099 p0116
  have p0118 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D)
              (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0))))
            (syn_wa (.classMem (.cv u) (syn_cuni (.cv x))) (syn_wral v (syn_cuni (.cv x))
                (.imp (syn_wbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u))))))
          (.classMem (.cv z) (.cv x))) (syn_wbr (.cv z) (syn_csi R) (syn_csn (.cv u))))
      (syn_wral v (syn_cuni (.cv x))
        (.imp (syn_wbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u))))
      (.classMem (syn_cuni (.cv z)) (syn_cuni (.cv x))) p0098 p0117
  have p0119 := @g_breq1 (.cv v) (syn_cuni (.cv z)) (.cv u) R
  have p0120 := @g_eqeq1 (.cv v) (syn_cuni (.cv z)) (.cv u)
  have p0121 :=
    @g_imbi12d (.classEq (.cv v) (syn_cuni (.cv z))) (syn_wbr (.cv v) R (.cv u))
      (syn_wbr (syn_cuni (.cv z)) R (.cv u)) (.classEq (.cv v) (.cv u))
      (.classEq (syn_cuni (.cv z)) (.cv u)) p0119 p0120
  have p0122 :=
    @g_rspccva (.imp (syn_wbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u)))
      (.imp (syn_wbr (syn_cuni (.cv z)) R (.cv u)) (.classEq (syn_cuni (.cv z)) (.cv u)))
      v (syn_cuni (.cv z)) (syn_cuni (.cv x)) dv_cache_0006 dv_cache_0004 dv_cache_0007
      p0121
  have p0123 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D)
              (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0))))
            (syn_wa (.classMem (.cv u) (syn_cuni (.cv x))) (syn_wral v (syn_cuni (.cv x))
                (.imp (syn_wbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u))))))
          (.classMem (.cv z) (.cv x))) (syn_wbr (.cv z) (syn_csi R) (syn_csn (.cv u))))
      (syn_wa (syn_wral v (syn_cuni (.cv x))
          (.imp (syn_wbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u))))
        (.classMem (syn_cuni (.cv z)) (syn_cuni (.cv x))))
      (.imp (syn_wbr (syn_cuni (.cv z)) R (.cv u)) (.classEq (syn_cuni (.cv z)) (.cv u)))
      p0118 p0122
  have p0124 :=
    @g_mpd
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D)
              (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0))))
            (syn_wa (.classMem (.cv u) (syn_cuni (.cv x))) (syn_wral v (syn_cuni (.cv x))
                (.imp (syn_wbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u))))))
          (.classMem (.cv z) (.cv x))) (syn_wbr (.cv z) (syn_csi R) (syn_csn (.cv u))))
      (syn_wbr (syn_cuni (.cv z)) R (.cv u)) (.classEq (syn_cuni (.cv z)) (.cv u)) p0091
      p0123
  have p0125 :=
    @g_sneqd
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D)
              (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0))))
            (syn_wa (.classMem (.cv u) (syn_cuni (.cv x))) (syn_wral v (syn_cuni (.cv x))
                (.imp (syn_wbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u))))))
          (.classMem (.cv z) (.cv x))) (syn_wbr (.cv z) (syn_csi R) (syn_csn (.cv u))))
      (syn_cuni (.cv z)) (.cv u) p0124
  have p0126 :=
    @g_eqtrd
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D)
              (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0))))
            (syn_wa (.classMem (.cv u) (syn_cuni (.cv x))) (syn_wral v (syn_cuni (.cv x))
                (.imp (syn_wbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u))))))
          (.classMem (.cv z) (.cv x))) (syn_wbr (.cv z) (syn_csi R) (syn_csn (.cv u))))
      (.cv z) (syn_csn (syn_cuni (.cv z))) (syn_csn (.cv u)) p0062 p0125
  have p0127 :=
    @g_ex
      (syn_wa (syn_wa (syn_wa (syn_wbr R (syn_cwe) D)
            (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0))))
          (syn_wa (.classMem (.cv u) (syn_cuni (.cv x))) (syn_wral v (syn_cuni (.cv x))
              (.imp (syn_wbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u))))))
        (.classMem (.cv z) (.cv x)))
      (syn_wbr (.cv z) (syn_csi R) (syn_csn (.cv u))) (.classEq (.cv z) (syn_csn (.cv u)))
      p0126
  have p0128 :=
    @g_ralrimiva
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) D)
          (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0))))
        (syn_wa (.classMem (.cv u) (syn_cuni (.cv x))) (syn_wral v (syn_cuni (.cv x))
            (.imp (syn_wbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u))))))
      (.imp (syn_wbr (.cv z) (syn_csi R) (syn_csn (.cv u)))
        (.classEq (.cv z) (syn_csn (.cv u))))
      z (.cv x) dv_cache_0008 p0127
  have p0129 :=
    @g_jca
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) D)
          (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0))))
        (syn_wa (.classMem (.cv u) (syn_cuni (.cv x))) (syn_wral v (syn_cuni (.cv x))
            (.imp (syn_wbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u))))))
      (.classMem (syn_csn (.cv u)) (.cv x))
      (syn_wral z (.cv x) (.imp (syn_wbr (.cv z) (syn_csi R) (syn_csn (.cv u)))
          (.classEq (.cv z) (syn_csn (.cv u)))))
      p0043 p0128
  have p0130 := @g_breq2 (.cv y) (syn_csn (.cv u)) (.cv z) (syn_csi R)
  have p0131 := @g_eqeq2 (.cv y) (syn_csn (.cv u)) (.cv z)
  have p0132 :=
    @g_imbi12d (.classEq (.cv y) (syn_csn (.cv u))) (syn_wbr (.cv z) (syn_csi R) (.cv y))
      (syn_wbr (.cv z) (syn_csi R) (syn_csn (.cv u))) (.classEq (.cv z) (.cv y))
      (.classEq (.cv z) (syn_csn (.cv u))) p0130 p0131
  have p0133 :=
    @g_ralbidv (.classEq (.cv y) (syn_csn (.cv u)))
      (.imp (syn_wbr (.cv z) (syn_csi R) (.cv y)) (.classEq (.cv z) (.cv y)))
      (.imp (syn_wbr (.cv z) (syn_csi R) (syn_csn (.cv u)))
        (.classEq (.cv z) (syn_csn (.cv u))))
      z (.cv x) dv_cache_0009 p0132
  have p0134 :=
    @g_rspcev
      (syn_wral z (.cv x)
        (.imp (syn_wbr (.cv z) (syn_csi R) (.cv y)) (.classEq (.cv z) (.cv y))))
      (syn_wral z (.cv x) (.imp (syn_wbr (.cv z) (syn_csi R) (syn_csn (.cv u)))
          (.classEq (.cv z) (syn_csn (.cv u)))))
      y (syn_csn (.cv u)) (.cv x) dv_cache_0010 dv_cache_0011 dv_cache_0012 p0133
  have p0135 :=
    @g_syl
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) D)
          (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0))))
        (syn_wa (.classMem (.cv u) (syn_cuni (.cv x))) (syn_wral v (syn_cuni (.cv x))
            (.imp (syn_wbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u))))))
      (syn_wa (.classMem (syn_csn (.cv u)) (.cv x)) (syn_wral z (.cv x)
          (.imp (syn_wbr (.cv z) (syn_csi R) (syn_csn (.cv u)))
            (.classEq (.cv z) (syn_csn (.cv u))))))
      (syn_wrex y (.cv x) (syn_wral z (.cv x)
          (.imp (syn_wbr (.cv z) (syn_csi R) (.cv y)) (.classEq (.cv z) (.cv y)))))
      p0129 p0134
  have p0136_e00_recanon :
    Nominal.NPrf
      (.imp (syn_wa (syn_wbr R (syn_cwe) D)
          (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0))))
        (syn_wrex u (syn_cuni (.cv x)) (syn_wral v (syn_cuni (.cv x))
            (.imp (syn_wbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wa syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_ccompl syn_wrex
          syn_wex syn_cphi syn_cwe syn_cin syn_cstrict syn_cfound syn_copab
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.all
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
              · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _)
      p0026
  have p0136 :=
    @g_rexlimddv
      (syn_wa (syn_wbr R (syn_cwe) D)
        (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0))))
      (syn_wral v (syn_cuni (.cv x))
        (.imp (syn_wbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u))))
      (syn_wrex y (.cv x) (syn_wral z (.cv x)
          (.imp (syn_wbr (.cv z) (syn_csi R) (.cv y)) (.classEq (.cv z) (.cv y)))))
      u (syn_cuni (.cv x)) dv_cache_0013 dv_cache_0014 p0136_e00_recanon p0135
  have p0137_e02_recanon :
    Nominal.NPrf
      (.imp (syn_wa (syn_wbr R (syn_cwe) D)
          (syn_wa (syn_wss (.cv x) (syn_cpw1 D)) (syn_wne (.cv x) (syn_c0))))
        (syn_wrex y (.cv x) (syn_wral z (.cv x)
            (.imp (syn_wbr (.cv z) (syn_csi R) (.cv y)) (.objEq z y))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wa syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_ccompl syn_wrex
          syn_wex syn_cphi syn_cwe syn_cin syn_cstrict syn_cfound syn_copab
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.all
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
              · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _)
      p0136
  have p0137 :=
    @g_frrd (syn_wbr R (syn_cwe) D) x z y (syn_cpw1 D) (syn_csi R) dv_cache_0015
      dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
      dv_cache_0022 dv_cache_0023 dv_cache_0024 p0003 p0007 p0137_e02_recanon
  exact p0137


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk016Compact001Part027`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_siwendv (D : Class) (R : Class) :
    Nominal.NPrf
      (.imp (syn_wbr R (syn_cwe) D) (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D))) :=
  by
  have p0000 := @g_siorndv D R
  have p0001 := @g_sifrndv D R
  have p0002 :=
    @g_jca (syn_wbr R (syn_cwe) D) (syn_wbr (syn_csi R) (syn_cstrict) (syn_cpw1 D))
      (syn_wbr (syn_csi R) (syn_cfound) (syn_cpw1 D)) p0000 p0001
  have p0003 := (Nominal.classEqRefl (syn_cwe))
  have p0004 :=
    @g_breqi (syn_csi R) (syn_cpw1 D) (syn_cwe) (syn_cin (syn_cstrict) (syn_cfound)) p0003
  have p0005 := @g_brin (syn_csi R) (syn_cpw1 D) (syn_cstrict) (syn_cfound)
  have p0006 :=
    @g_bitri (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D))
      (syn_wbr (syn_csi R) (syn_cin (syn_cstrict) (syn_cfound)) (syn_cpw1 D))
      (syn_wa (syn_wbr (syn_csi R) (syn_cstrict) (syn_cpw1 D))
        (syn_wbr (syn_csi R) (syn_cfound) (syn_cpw1 D)))
      p0004 p0005
  have p0007 :=
    @g_biimpri (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D))
      (syn_wa (syn_wbr (syn_csi R) (syn_cstrict) (syn_cpw1 D))
        (syn_wbr (syn_csi R) (syn_cfound) (syn_cpw1 D)))
      p0006
  have p0008 :=
    @g_syl (syn_wbr R (syn_cwe) D)
      (syn_wa (syn_wbr (syn_csi R) (syn_cstrict) (syn_cpw1 D))
        (syn_wbr (syn_csi R) (syn_cfound) (syn_cpw1 D)))
      (syn_wbr (syn_csi R) (syn_cwe) (syn_cpw1 D)) p0002 p0007
  exact p0008

@[expose]
noncomputable def g_wecutcardtypedleastndv (y : Var) (z : Var) (D : Class) (R : Class)
    (K : Class) (q : Var) (dv_D_q : q ∉ D.fv) (dv_D_y : y ∉ D.fv) (dv_D_z : z ∉ D.fv)
    (dv_K_q : q ∉ K.fv) (dv_K_y : y ∉ K.fv) (dv_K_z : z ∉ K.fv) (dv_R_q : q ∉ R.fv)
    (dv_R_y : y ∉ R.fv) (dv_R_z : z ∉ R.fv) (dv_q_y : q ≠ y) (dv_q_z : q ≠ z)
    (dv_y_z : y ≠ z) (hyp_wecutcardtypedleastndv_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D))
    (hyp_wecutcardtypedleastndv_2 : Nominal.NPrf (.classMem K (syn_cvv))) :
    Nominal.NPrf
      (.imp (syn_wrex q (syn_cpw1 (syn_cpw1 D)) (.classMem (syn_cnc (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (syn_cuni (syn_cuni (.cv q))))))) K))
        (syn_wrex y (syn_cpw1 (syn_cpw1 D)) (syn_wa (.classMem (syn_cnc (syn_cin D
                  (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                    (syn_csn (syn_cuni (syn_cuni (.cv y))))))) K)
            (syn_wral z (syn_cpw1 (syn_cpw1 D)) (.imp (.classMem (syn_cnc (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                        (syn_csn (syn_cuni (syn_cuni (.cv z))))))) K)
                (syn_wbr (.cv y) (syn_csi (syn_csi R)) (.cv z))))))) :=
  by
  have dv_cache_0001 : q ∉ ((syn_cima (syn_ccnv (syn_cwecutcardfn R D)) K)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwecutcardfn,
          Finset.mem_union, dv_D_q, dv_R_q, dv_K_q, or_false, not_false_eq_true])
  have dv_cache_0002 : q ∉ (D).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_D_q, not_false_eq_true])
  have dv_cache_0003 : q ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_R_q, not_false_eq_true])
  have dv_cache_0004 : q ∉ ((syn_cpw1 (syn_cpw1 D))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, dv_D_q,
          not_false_eq_true])
  have dv_cache_0005 : y ∉ ((syn_cpw1 (syn_cpw1 D))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, dv_D_y,
          not_false_eq_true])
  have dv_cache_0006 : z ∉ ((syn_cpw1 (syn_cpw1 D))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, dv_D_z,
          not_false_eq_true])
  have dv_cache_0007 : y ∉ ((syn_csi (syn_csi R))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi, dv_R_y,
          not_false_eq_true])
  have dv_cache_0008 : z ∉ ((syn_csi (syn_csi R))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi, dv_R_z,
          not_false_eq_true])
  have dv_cache_0009 :
    q ∉ ((Wff.classMem (.cv y) (syn_cima (syn_ccnv (syn_cwecutcardfn R D)) K))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwecutcardfn,
          Finset.mem_union, Finset.mem_singleton, dv_q_y, dv_D_q, dv_R_q, dv_K_q,
          or_false, not_false_eq_true])
  have dv_cache_0010 :
    y ∉
      ((syn_wrex q (syn_cpw1 (syn_cpw1 D)) (.classMem (syn_cnc (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (syn_cuni (syn_cuni (.cv q))))))) K))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, dv_D_y, dv_R_y, (Ne.symm dv_q_y), dv_K_y,
          compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0011 :
    z ∉
      ((syn_wrex q (syn_cpw1 (syn_cpw1 D)) (.classMem (syn_cnc (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (syn_cuni (syn_cuni (.cv q))))))) K))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, dv_D_z, dv_R_z, (Ne.symm dv_q_z), dv_K_z,
          compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0012 :
    y ∉ ((Wff.classMem (.cv q) (syn_cima (syn_ccnv (syn_cwecutcardfn R D)) K))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwecutcardfn,
          Finset.mem_union, Finset.mem_singleton, (Ne.symm dv_q_y), dv_D_y, dv_R_y,
          dv_K_y, or_false, not_false_eq_true])
  have dv_cache_0013 :
    z ∉ ((Wff.classMem (.cv q) (syn_cima (syn_ccnv (syn_cwecutcardfn R D)) K))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwecutcardfn,
          Finset.mem_union, Finset.mem_singleton, (Ne.symm dv_q_z), dv_D_z, dv_R_z,
          dv_K_z, or_false, not_false_eq_true])
  have dv_cache_0014 :
    q ∉ ((Wff.classMem (.cv z) (syn_cima (syn_ccnv (syn_cwecutcardfn R D)) K))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwecutcardfn,
          Finset.mem_union, Finset.mem_singleton, dv_q_z, dv_D_q, dv_R_q, dv_K_q,
          or_false, not_false_eq_true])
  have dv_cache_0015 : q ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (show q ≠ y from (by exact dv_q_y))
  have dv_cache_0016 : q ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (show q ≠ z from (by exact dv_q_z))
  have dv_cache_0017 : y ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (show y ≠ z from (by exact dv_y_z))
  have dv_cache_0018 : y ∉ (D).fv :=
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
        simp only [dv_D_y, not_false_eq_true])
  have dv_cache_0019 : y ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_R_y, not_false_eq_true])
  have dv_cache_0020 : z ∉ (D).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_D_z, not_false_eq_true])
  have dv_cache_0021 : z ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_R_z, not_false_eq_true])
  have p0000 := @g_abid2 q (syn_cima (syn_ccnv (syn_cwecutcardfn R D)) K) dv_cache_0001
  have p0001 := @g_wecutcardfnex D R hyp_wecutcardtypedleastndv_1
  have p0002 := @g_cnvex (syn_cwecutcardfn R D) p0001
  have p0003 :=
    @g_imaex (syn_ccnv (syn_cwecutcardfn R D)) K p0002 hyp_wecutcardtypedleastndv_2
  have p0004 :=
    @g_eqeltri (.cab q (.classMem (.cv q) (syn_cima (syn_ccnv (syn_cwecutcardfn R D)) K)))
      (syn_cima (syn_ccnv (syn_cwecutcardfn R D)) K) (syn_cvv) p0000 p0003
  have p0005 := @g_eleq1 (.cv q) (.cv y) (syn_cima (syn_ccnv (syn_cwecutcardfn R D)) K)
  have p0006 := @g_eleq1 (.cv q) (.cv z) (syn_cima (syn_ccnv (syn_cwecutcardfn R D)) K)
  have p0007 := @g_siwendv D R
  have p0008 := Nominal.mp hyp_wecutcardtypedleastndv_1 p0007
  have p0009 := @g_siwendv (syn_cpw1 D) (syn_csi R)
  have p0010 := Nominal.mp p0008 p0009
  have p0011 :=
    @g_a1i (syn_wbr (syn_csi (syn_csi R)) (syn_cwe) (syn_cpw1 (syn_cpw1 D)))
      (syn_wrex q (syn_cpw1 (syn_cpw1 D)) (.classMem (syn_cnc (syn_cin D
              (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (.cv q))))))) K))
      p0010
  have p0012 :=
    @g_id
      (syn_wrex q (syn_cpw1 (syn_cpw1 D)) (.classMem (syn_cnc (syn_cin D
              (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (.cv q))))))) K))
  have p0013 := @g_wecutcardpreimandv D R K q dv_cache_0002 dv_cache_0003
  have p0014 :=
    @g_biimprd (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))
      (.classMem (.cv q) (syn_cima (syn_ccnv (syn_cwecutcardfn R D)) K))
      (.classMem (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
              (syn_csn (syn_cuni (syn_cuni (.cv q))))))) K)
      p0013
  have p0015 :=
    @g_reximia
      (.classMem (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
              (syn_csn (syn_cuni (syn_cuni (.cv q))))))) K)
      (.classMem (.cv q) (syn_cima (syn_ccnv (syn_cwecutcardfn R D)) K)) q
      (syn_cpw1 (syn_cpw1 D)) p0014
  have p0016 :=
    @g_syl
      (syn_wrex q (syn_cpw1 (syn_cpw1 D)) (.classMem (syn_cnc (syn_cin D
              (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (.cv q))))))) K))
      (syn_wrex q (syn_cpw1 (syn_cpw1 D)) (.classMem (syn_cnc (syn_cin D
              (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (.cv q))))))) K))
      (syn_wrex q (syn_cpw1 (syn_cpw1 D))
        (.classMem (.cv q) (syn_cima (syn_ccnv (syn_cwecutcardfn R D)) K)))
      p0012 p0015
  have p0017_e01_recanon :
    Nominal.NPrf
      (.imp (.objEq q y)
        (syn_wb (.classMem (.cv q) (syn_cima (syn_ccnv (syn_cwecutcardfn R D)) K))
          (.classMem (.cv y) (syn_cima (syn_ccnv (syn_cwecutcardfn R D)) K)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cima syn_wrex syn_wex syn_wa syn_wbr syn_cop syn_cun syn_cnin
          syn_wnan syn_ccompl syn_ccnv syn_copab syn_cwecutcardfn syn_cmpt syn_cpw1
          syn_cin syn_cpw syn_wss syn_c1c syn_cnc syn_cec syn_cen
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0005
  have p0017_e02_recanon :
    Nominal.NPrf
      (.imp (.objEq q z)
        (syn_wb (.classMem (.cv q) (syn_cima (syn_ccnv (syn_cwecutcardfn R D)) K))
          (.classMem (.cv z) (syn_cima (syn_ccnv (syn_cwecutcardfn R D)) K)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cima syn_wrex syn_wex syn_wa syn_wbr syn_cop syn_cun syn_cnin
          syn_wnan syn_ccompl syn_ccnv syn_copab syn_cwecutcardfn syn_cmpt syn_cpw1
          syn_cin syn_cpw syn_wss syn_c1c syn_cnc syn_cec syn_cen
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0006
  have p0017 :=
    @g_weds
      (syn_wrex q (syn_cpw1 (syn_cpw1 D)) (.classMem (syn_cnc (syn_cin D
              (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (.cv q))))))) K))
      (.classMem (.cv q) (syn_cima (syn_ccnv (syn_cwecutcardfn R D)) K))
      (.classMem (.cv y) (syn_cima (syn_ccnv (syn_cwecutcardfn R D)) K))
      (.classMem (.cv z) (syn_cima (syn_ccnv (syn_cwecutcardfn R D)) K)) q y z
      (syn_cpw1 (syn_cpw1 D)) (syn_csi (syn_csi R)) dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      p0004 p0017_e01_recanon p0017_e02_recanon p0011 p0016
  have p0018 := @g_wecutcardpreimandv D R K y dv_cache_0018 dv_cache_0019
  have p0019 := @g_wecutcardpreimandv D R K z dv_cache_0020 dv_cache_0021
  have p0020 :=
    @g_imbi1d (.classMem (.cv z) (syn_cpw1 (syn_cpw1 D)))
      (.classMem (.cv z) (syn_cima (syn_ccnv (syn_cwecutcardfn R D)) K))
      (.classMem (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
              (syn_csn (syn_cuni (syn_cuni (.cv z))))))) K)
      (syn_wbr (.cv y) (syn_csi (syn_csi R)) (.cv z)) p0019
  have p0021 :=
    @g_ralbiia
      (.imp (.classMem (.cv z) (syn_cima (syn_ccnv (syn_cwecutcardfn R D)) K))
        (syn_wbr (.cv y) (syn_csi (syn_csi R)) (.cv z)))
      (.imp (.classMem (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (.cv z))))))) K)
        (syn_wbr (.cv y) (syn_csi (syn_csi R)) (.cv z)))
      z (syn_cpw1 (syn_cpw1 D)) p0020
  have p0022 :=
    @g_a1i
      (syn_wb (syn_wral z (syn_cpw1 (syn_cpw1 D))
          (.imp (.classMem (.cv z) (syn_cima (syn_ccnv (syn_cwecutcardfn R D)) K))
            (syn_wbr (.cv y) (syn_csi (syn_csi R)) (.cv z))))
        (syn_wral z (syn_cpw1 (syn_cpw1 D)) (.imp (.classMem (syn_cnc (syn_cin D
                  (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                    (syn_csn (syn_cuni (syn_cuni (.cv z))))))) K)
            (syn_wbr (.cv y) (syn_csi (syn_csi R)) (.cv z)))))
      (.classMem (.cv y) (syn_cpw1 (syn_cpw1 D))) p0021
  have p0023 :=
    @g_anbi12d (.classMem (.cv y) (syn_cpw1 (syn_cpw1 D)))
      (.classMem (.cv y) (syn_cima (syn_ccnv (syn_cwecutcardfn R D)) K))
      (.classMem (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
              (syn_csn (syn_cuni (syn_cuni (.cv y))))))) K)
      (syn_wral z (syn_cpw1 (syn_cpw1 D))
        (.imp (.classMem (.cv z) (syn_cima (syn_ccnv (syn_cwecutcardfn R D)) K))
          (syn_wbr (.cv y) (syn_csi (syn_csi R)) (.cv z))))
      (syn_wral z (syn_cpw1 (syn_cpw1 D)) (.imp (.classMem (syn_cnc (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (syn_cuni (syn_cuni (.cv z))))))) K)
          (syn_wbr (.cv y) (syn_csi (syn_csi R)) (.cv z))))
      p0018 p0022
  have p0024 :=
    @g_biimpd (.classMem (.cv y) (syn_cpw1 (syn_cpw1 D)))
      (syn_wa (.classMem (.cv y) (syn_cima (syn_ccnv (syn_cwecutcardfn R D)) K))
        (syn_wral z (syn_cpw1 (syn_cpw1 D))
          (.imp (.classMem (.cv z) (syn_cima (syn_ccnv (syn_cwecutcardfn R D)) K))
            (syn_wbr (.cv y) (syn_csi (syn_csi R)) (.cv z)))))
      (syn_wa (.classMem (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (.cv y))))))) K)
        (syn_wral z (syn_cpw1 (syn_cpw1 D)) (.imp (.classMem (syn_cnc (syn_cin D
                  (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                    (syn_csn (syn_cuni (syn_cuni (.cv z))))))) K)
            (syn_wbr (.cv y) (syn_csi (syn_csi R)) (.cv z)))))
      p0023
  have p0025 :=
    @g_reximia
      (syn_wa (.classMem (.cv y) (syn_cima (syn_ccnv (syn_cwecutcardfn R D)) K))
        (syn_wral z (syn_cpw1 (syn_cpw1 D))
          (.imp (.classMem (.cv z) (syn_cima (syn_ccnv (syn_cwecutcardfn R D)) K))
            (syn_wbr (.cv y) (syn_csi (syn_csi R)) (.cv z)))))
      (syn_wa (.classMem (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (.cv y))))))) K)
        (syn_wral z (syn_cpw1 (syn_cpw1 D)) (.imp (.classMem (syn_cnc (syn_cin D
                  (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                    (syn_csn (syn_cuni (syn_cuni (.cv z))))))) K)
            (syn_wbr (.cv y) (syn_csi (syn_csi R)) (.cv z)))))
      y (syn_cpw1 (syn_cpw1 D)) p0024
  have p0026 :=
    @g_syl
      (syn_wrex q (syn_cpw1 (syn_cpw1 D)) (.classMem (syn_cnc (syn_cin D
              (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (.cv q))))))) K))
      (syn_wrex y (syn_cpw1 (syn_cpw1 D))
        (syn_wa (.classMem (.cv y) (syn_cima (syn_ccnv (syn_cwecutcardfn R D)) K))
          (syn_wral z (syn_cpw1 (syn_cpw1 D))
            (.imp (.classMem (.cv z) (syn_cima (syn_ccnv (syn_cwecutcardfn R D)) K))
              (syn_wbr (.cv y) (syn_csi (syn_csi R)) (.cv z))))))
      (syn_wrex y (syn_cpw1 (syn_cpw1 D)) (syn_wa (.classMem (syn_cnc (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (syn_cuni (syn_cuni (.cv y))))))) K)
          (syn_wral z (syn_cpw1 (syn_cpw1 D)) (.imp (.classMem (syn_cnc (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                      (syn_csn (syn_cuni (syn_cuni (.cv z))))))) K)
              (syn_wbr (.cv y) (syn_csi (syn_csi R)) (.cv z))))))
      p0017 p0025
  exact p0026

@[expose]
noncomputable def g_wecutssndv (x : Var) (y : Var) (D : Class) (R : Class)
    (_dv_D_x : x ∉ D.fv) (_dv_D_y : y ∉ D.fv) (_dv_R_x : x ∉ R.fv) (_dv_R_y : y ∉ R.fv)
    (_dv_x_y : x ≠ y) (hyp_wecutssndv_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D)) :
    Nominal.NPrf
      (.imp (syn_w3a (.classMem (.cv x) D) (.classMem (.cv y) D) (syn_wbr (.cv x) R (.cv y)))
        (syn_wss (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))) :=
  by
  let proofSupport : Finset Var :=
    ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ D.fv ∪ R.fv
  let z : Var := freshVar proofSupport 0
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z_ne_x : z ≠ x := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_z_ne_y : z ≠ y := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_z_not_D : z ∉ D.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_z_not_R : z ∉ R.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have dv_cache_0001 :
    z ∉ ((syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))).fv :=
    by
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_z_not_D, fresh_z_not_R, fresh_z_ne_x,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0002 :
    z ∉ ((syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_z_not_D, fresh_z_not_R, fresh_z_ne_y,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0003 :
    z ∉
      ((syn_w3a (.classMem (.cv x) D) (.classMem (.cv y) D) (syn_wbr (.cv x) R (.cv y)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_x, fresh_z_ne_y, fresh_z_not_R, fresh_z_not_D,
          or_false, not_false_eq_true])
  have p0000 :=
    @g_simpr
      (syn_w3a (.classMem (.cv x) D) (.classMem (.cv y) D) (syn_wbr (.cv x) R (.cv y)))
      (.classMem (.cv z)
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
  have p0001 := @g_id (.classEq (.cv x) (.cv y))
  have p0002 := @g_sneqd (.classEq (.cv x) (.cv y)) (.cv x) (.cv y) p0001
  have p0003 :=
    @g_imaeq2d (.classEq (.cv x) (.cv y)) (syn_csn (.cv x)) (syn_csn (.cv y))
      (syn_ccnv (syn_cdif R (syn_cid))) p0002
  have p0004 :=
    @g_ineq2d (.classEq (.cv x) (.cv y))
      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))
      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))) D p0003
  have p0005 :=
    @g_eleq2d (.classEq (.cv x) (.cv y))
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (.cv z)
      p0004
  have p0006 :=
    @g_biimpd (.classEq (.cv x) (.cv y))
      (.classMem (.cv z)
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
      (.classMem (.cv z)
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
      p0005
  have p0007 :=
    @g_com12 (.classEq (.cv x) (.cv y))
      (.classMem (.cv z)
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
      (.classMem (.cv z)
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
      p0006
  have p0008 :=
    @g_syl
      (syn_wa (syn_w3a (.classMem (.cv x) D) (.classMem (.cv y) D) (syn_wbr (.cv x) R (.cv y)))
        (.classMem (.cv z)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (.classMem (.cv z)
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
      (.imp (.classEq (.cv x) (.cv y)) (.classMem (.cv z)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      p0000 p0007
  have p0009 :=
    @g_a1i (syn_wbr R (syn_cwe) D)
      (syn_wa (syn_wa (syn_w3a (.classMem (.cv x) D) (.classMem (.cv y) D)
            (syn_wbr (.cv x) R (.cv y))) (.classMem (.cv z)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (.neg (.classEq (.cv x) (.cv y))))
      hyp_wecutssndv_1
  have p0010 :=
    @g_simpl
      (syn_wa (syn_w3a (.classMem (.cv x) D) (.classMem (.cv y) D) (syn_wbr (.cv x) R (.cv y)))
        (.classMem (.cv z)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (.neg (.classEq (.cv x) (.cv y)))
  have p0011 :=
    @g_simpl
      (syn_w3a (.classMem (.cv x) D) (.classMem (.cv y) D) (syn_wbr (.cv x) R (.cv y)))
      (.classMem (.cv z)
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
  have p0012 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (.classMem (.cv x) D) (.classMem (.cv y) D)
            (syn_wbr (.cv x) R (.cv y))) (.classMem (.cv z)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (.neg (.classEq (.cv x) (.cv y))))
      (syn_wa (syn_w3a (.classMem (.cv x) D) (.classMem (.cv y) D) (syn_wbr (.cv x) R (.cv y)))
        (.classMem (.cv z)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (syn_w3a (.classMem (.cv x) D) (.classMem (.cv y) D) (syn_wbr (.cv x) R (.cv y)))
      p0010 p0011
  have p0013 :=
    @g_simp2 (.classMem (.cv x) D) (.classMem (.cv y) D) (syn_wbr (.cv x) R (.cv y))
  have p0014 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (.classMem (.cv x) D) (.classMem (.cv y) D)
            (syn_wbr (.cv x) R (.cv y))) (.classMem (.cv z)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (.neg (.classEq (.cv x) (.cv y))))
      (syn_w3a (.classMem (.cv x) D) (.classMem (.cv y) D) (syn_wbr (.cv x) R (.cv y)))
      (.classMem (.cv y) D) p0012 p0013
  have p0015 :=
    @g_jca
      (syn_wa (syn_wa (syn_w3a (.classMem (.cv x) D) (.classMem (.cv y) D)
            (syn_wbr (.cv x) R (.cv y))) (.classMem (.cv z)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (.neg (.classEq (.cv x) (.cv y))))
      (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D) p0009 p0014
  have p0019 :=
    @g_simp1 (.classMem (.cv x) D) (.classMem (.cv y) D) (syn_wbr (.cv x) R (.cv y))
  have p0020 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (.classMem (.cv x) D) (.classMem (.cv y) D)
            (syn_wbr (.cv x) R (.cv y))) (.classMem (.cv z)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (.neg (.classEq (.cv x) (.cv y))))
      (syn_w3a (.classMem (.cv x) D) (.classMem (.cv y) D) (syn_wbr (.cv x) R (.cv y)))
      (.classMem (.cv x) D) p0012 p0019
  have p0024 :=
    @g_simp3 (.classMem (.cv x) D) (.classMem (.cv y) D) (syn_wbr (.cv x) R (.cv y))
  have p0025 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (.classMem (.cv x) D) (.classMem (.cv y) D)
            (syn_wbr (.cv x) R (.cv y))) (.classMem (.cv z)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (.neg (.classEq (.cv x) (.cv y))))
      (syn_w3a (.classMem (.cv x) D) (.classMem (.cv y) D) (syn_wbr (.cv x) R (.cv y)))
      (syn_wbr (.cv x) R (.cv y)) p0012 p0024
  have p0026 :=
    @g_simpr
      (syn_wa (syn_w3a (.classMem (.cv x) D) (.classMem (.cv y) D) (syn_wbr (.cv x) R (.cv y)))
        (.classMem (.cv z)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (.neg (.classEq (.cv x) (.cv y)))
  have p0027 := (Nominal.biimpRefl (syn_wne (.cv x) (.cv y)))
  have p0028 :=
    @g_biimpri (syn_wne (.cv x) (.cv y)) (.neg (.classEq (.cv x) (.cv y))) p0027
  have p0029 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (.classMem (.cv x) D) (.classMem (.cv y) D)
            (syn_wbr (.cv x) R (.cv y))) (.classMem (.cv z)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (.neg (.classEq (.cv x) (.cv y))))
      (.neg (.classEq (.cv x) (.cv y))) (syn_wne (.cv x) (.cv y)) p0026 p0028
  have p0030 :=
    @g_jca
      (syn_wa (syn_wa (syn_w3a (.classMem (.cv x) D) (.classMem (.cv y) D)
            (syn_wbr (.cv x) R (.cv y))) (.classMem (.cv z)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (.neg (.classEq (.cv x) (.cv y))))
      (syn_wbr (.cv x) R (.cv y)) (syn_wne (.cv x) (.cv y)) p0025 p0029
  have p0031 :=
    @g_jca
      (syn_wa (syn_wa (syn_w3a (.classMem (.cv x) D) (.classMem (.cv y) D)
            (syn_wbr (.cv x) R (.cv y))) (.classMem (.cv z)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (.neg (.classEq (.cv x) (.cv y))))
      (.classMem (.cv x) D) (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wne (.cv x) (.cv y)))
      p0020 p0030
  have p0032 := @g_elstrictseg y x D R
  have p0033 :=
    @g_biimpri
      (.classMem (.cv x)
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
      (syn_wa (.classMem (.cv x) D)
        (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wne (.cv x) (.cv y))))
      p0032
  have p0034 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (.classMem (.cv x) D) (.classMem (.cv y) D)
            (syn_wbr (.cv x) R (.cv y))) (.classMem (.cv z)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (.neg (.classEq (.cv x) (.cv y))))
      (syn_wa (.classMem (.cv x) D)
        (syn_wa (syn_wbr (.cv x) R (.cv y)) (syn_wne (.cv x) (.cv y))))
      (.classMem (.cv x)
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
      p0031 p0033
  have p0037 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (.classMem (.cv x) D) (.classMem (.cv y) D)
            (syn_wbr (.cv x) R (.cv y))) (.classMem (.cv z)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (.neg (.classEq (.cv x) (.cv y))))
      (syn_wa (syn_w3a (.classMem (.cv x) D) (.classMem (.cv y) D) (syn_wbr (.cv x) R (.cv y)))
        (.classMem (.cv z)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (.classMem (.cv z)
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
      p0010 p0000
  have p0038 := @g_elstrictseg x z D R
  have p0039 :=
    @g_biimpi
      (.classMem (.cv z)
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
      (syn_wa (.classMem (.cv z) D)
        (syn_wa (syn_wbr (.cv z) R (.cv x)) (syn_wne (.cv z) (.cv x))))
      p0038
  have p0040 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (.classMem (.cv x) D) (.classMem (.cv y) D)
            (syn_wbr (.cv x) R (.cv y))) (.classMem (.cv z)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (.neg (.classEq (.cv x) (.cv y))))
      (.classMem (.cv z)
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
      (syn_wa (.classMem (.cv z) D)
        (syn_wa (syn_wbr (.cv z) R (.cv x)) (syn_wne (.cv z) (.cv x))))
      p0037 p0039
  have p0041 :=
    @g_simpld
      (syn_wa (syn_wa (syn_w3a (.classMem (.cv x) D) (.classMem (.cv y) D)
            (syn_wbr (.cv x) R (.cv y))) (.classMem (.cv z)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (.neg (.classEq (.cv x) (.cv y))))
      (.classMem (.cv z) D) (syn_wa (syn_wbr (.cv z) R (.cv x)) (syn_wne (.cv z) (.cv x)))
      p0040
  have p0042 :=
    @g_jca
      (syn_wa (syn_wa (syn_w3a (.classMem (.cv x) D) (.classMem (.cv y) D)
            (syn_wbr (.cv x) R (.cv y))) (.classMem (.cv z)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (.neg (.classEq (.cv x) (.cv y))))
      (.classMem (.cv x)
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
      (.classMem (.cv z) D) p0034 p0041
  have p0049 :=
    @g_simprd
      (syn_wa (syn_wa (syn_w3a (.classMem (.cv x) D) (.classMem (.cv y) D)
            (syn_wbr (.cv x) R (.cv y))) (.classMem (.cv z)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (.neg (.classEq (.cv x) (.cv y))))
      (.classMem (.cv z) D) (syn_wa (syn_wbr (.cv z) R (.cv x)) (syn_wne (.cv z) (.cv x)))
      p0040
  have p0050 :=
    @g_simpld
      (syn_wa (syn_wa (syn_w3a (.classMem (.cv x) D) (.classMem (.cv y) D)
            (syn_wbr (.cv x) R (.cv y))) (.classMem (.cv z)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (.neg (.classEq (.cv x) (.cv y))))
      (syn_wbr (.cv z) R (.cv x)) (syn_wne (.cv z) (.cv x)) p0049
  have p0051 :=
    @g_n_3jca
      (syn_wa (syn_wa (syn_w3a (.classMem (.cv x) D) (.classMem (.cv y) D)
            (syn_wbr (.cv x) R (.cv y))) (.classMem (.cv z)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (.neg (.classEq (.cv x) (.cv y))))
      (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D))
      (syn_wa (.classMem (.cv x)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
        (.classMem (.cv z) D))
      (syn_wbr (.cv z) R (.cv x)) p0015 p0042 p0050
  have p0052 := @g_strictsegdown y x z D R
  have p0053 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (.classMem (.cv x) D) (.classMem (.cv y) D)
            (syn_wbr (.cv x) R (.cv y))) (.classMem (.cv z)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (.neg (.classEq (.cv x) (.cv y))))
      (syn_w3a (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (syn_wa (.classMem (.cv x)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
          (.classMem (.cv z) D)) (syn_wbr (.cv z) R (.cv x)))
      (.classMem (.cv z)
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
      p0051 p0052
  have p0054 :=
    @g_ex
      (syn_wa (syn_w3a (.classMem (.cv x) D) (.classMem (.cv y) D) (syn_wbr (.cv x) R (.cv y)))
        (.classMem (.cv z)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (.neg (.classEq (.cv x) (.cv y)))
      (.classMem (.cv z)
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
      p0053
  have p0055 :=
    @g_pm2_61d
      (syn_wa (syn_w3a (.classMem (.cv x) D) (.classMem (.cv y) D) (syn_wbr (.cv x) R (.cv y)))
        (.classMem (.cv z)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (.classEq (.cv x) (.cv y))
      (.classMem (.cv z)
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
      p0008 p0054
  have p0056 :=
    @g_ex
      (syn_w3a (.classMem (.cv x) D) (.classMem (.cv y) D) (syn_wbr (.cv x) R (.cv y)))
      (.classMem (.cv z)
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
      (.classMem (.cv z)
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
      p0055
  have p0057 :=
    @g_ssrdv
      (syn_w3a (.classMem (.cv x) D) (.classMem (.cv y) D) (syn_wbr (.cv x) R (.cv y))) z
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
      dv_cache_0001 dv_cache_0002 dv_cache_0003 p0056
  exact p0057

@[expose]
noncomputable def g_wecutnclecndv (x : Var) (y : Var) (D : Class) (R : Class)
    (dv_D_x : x ∉ D.fv) (dv_D_y : y ∉ D.fv) (dv_R_x : x ∉ R.fv) (dv_R_y : y ∉ R.fv)
    (dv_x_y : x ≠ y) (hyp_wecutnclecndv_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D)) :
    Nominal.NPrf
      (.imp (syn_w3a (.classMem (.cv x) D) (.classMem (.cv y) D) (syn_wbr (.cv x) R (.cv y)))
        (syn_wbr (syn_cnc
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
          (syn_clec) (syn_cnc (syn_cin D
              (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))) :=
  by
  have dv_cache_0001 : x ∉ (D).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_D_x, not_false_eq_true])
  have dv_cache_0002 : y ∉ (D).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_D_y, not_false_eq_true])
  have dv_cache_0003 : x ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_R_x, not_false_eq_true])
  have dv_cache_0004 : y ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_R_y, not_false_eq_true])
  have dv_cache_0005 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show x ≠ y from (by exact dv_x_y))
  have p0000 :=
    @g_wecutssndv x y D R dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 hyp_wecutnclecndv_1
  have p0001 := @g_brex R D (syn_cwe)
  have p0002 := Nominal.mp hyp_wecutnclecndv_1 p0001
  have p0003 := @g_simpri (.classMem R (syn_cvv)) (.classMem D (syn_cvv)) p0002
  have p0006 := @g_simpli (.classMem R (syn_cvv)) (.classMem D (syn_cvv)) p0002
  have p0007 := @g_idex
  have p0008 := @g_difex R (syn_cid) p0006 p0007
  have p0009 := @g_cnvex (syn_cdif R (syn_cid)) p0008
  have p0010 := @g_snex (.cv x)
  have p0011 := @g_imaex (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)) p0009 p0010
  have p0012 :=
    @g_inex D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))) p0003 p0011
  have p0022 := @g_snex (.cv y)
  have p0023 := @g_imaex (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)) p0009 p0022
  have p0024 :=
    @g_inex D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))) p0003 p0023
  have p0025 :=
    @g_nclec (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) p0012
      p0024
  have p0026 :=
    @g_syl
      (syn_w3a (.classMem (.cv x) D) (.classMem (.cv y) D) (syn_wbr (.cv x) R (.cv y)))
      (syn_wss (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
      (syn_wbr (syn_cnc
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_clec)
        (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      p0000 p0025
  exact p0026


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk016Compact001Part028`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_wecutnclecclndv (A : Class) (B : Class) (D : Class) (R : Class)
    (_dv_A_R : Disjoint A.fv R.fv)
    (hyp_wecutnclecclndv_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D)) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem A (syn_cvv)) (.classMem B (syn_cvv)))
        (.imp (syn_w3a (.classMem A D) (.classMem B D) (syn_wbr A R B)) (syn_wbr
            (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn A))))
            (syn_clec) (syn_cnc
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))))))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ D.fv ∪ R.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_x_not_D : x ∉ D.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_R : x ∉ R.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_y_not_D : y ∉ D.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_R : y ∉ R.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have dv_cache_0001 : x ∉ (D).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_D, not_false_eq_true])
  have dv_cache_0002 : y ∉ (D).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_D, not_false_eq_true])
  have dv_cache_0003 : x ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_R, not_false_eq_true])
  have dv_cache_0004 : y ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_R, not_false_eq_true])
  have dv_cache_0005 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0006 : x ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_A, not_false_eq_true])
  have dv_cache_0007 : y ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_A, not_false_eq_true])
  have dv_cache_0008 : y ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_B, not_false_eq_true])
  have dv_cache_0009 :
    y ∉
      ((Wff.imp (syn_w3a (.classMem A D) (.classMem B D) (syn_wbr A R B)) (syn_wbr
            (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn A))))
            (syn_clec) (syn_cnc (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, Finset.mem_union,
          fresh_y_not_A, fresh_y_not_B, fresh_y_not_R, fresh_y_not_D,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0010 :
    x ∉
      ((Wff.imp (syn_w3a (.classMem A D) (.classMem (.cv y) D) (syn_wbr A R (.cv y))) (syn_wbr
            (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn A))))
            (syn_clec) (syn_cnc (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, Finset.mem_union,
          Finset.mem_singleton, fresh_x_not_A, fresh_x_ne_y, fresh_x_not_R, fresh_x_not_D,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have p0000 := @g_id (.classEq (.cv x) A)
  have p0001 := @g_eleq1d (.classEq (.cv x) A) (.cv x) A D p0000
  have p0003 := @g_breq1d (.classEq (.cv x) A) (.cv x) A (.cv y) R p0000
  have p0004 :=
    @g_n_3anbi13d (.classEq (.cv x) A) (.classMem (.cv x) D) (.classMem A D)
      (syn_wbr (.cv x) R (.cv y)) (syn_wbr A R (.cv y)) (.classMem (.cv y) D) p0001 p0003
  have p0006 := @g_sneqd (.classEq (.cv x) A) (.cv x) A p0000
  have p0007 :=
    @g_imaeq2d (.classEq (.cv x) A) (syn_csn (.cv x)) (syn_csn A)
      (syn_ccnv (syn_cdif R (syn_cid))) p0006
  have p0008 :=
    @g_ineq2d (.classEq (.cv x) A)
      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))
      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn A)) D p0007
  have p0009 :=
    @g_nceqd (.classEq (.cv x) A)
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn A))) p0008
  have p0010 :=
    @g_breq1d (.classEq (.cv x) A)
      (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
      (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn A))))
      (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
      (syn_clec) p0009
  have p0011 :=
    @g_imbi12d (.classEq (.cv x) A)
      (syn_w3a (.classMem (.cv x) D) (.classMem (.cv y) D) (syn_wbr (.cv x) R (.cv y)))
      (syn_w3a (.classMem A D) (.classMem (.cv y) D) (syn_wbr A R (.cv y)))
      (syn_wbr (syn_cnc
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))) (syn_clec)
        (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (syn_wbr (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn A))))
        (syn_clec) (syn_cnc
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      p0004 p0010
  have p0012 := @g_id (.classEq (.cv y) B)
  have p0013 := @g_eleq1d (.classEq (.cv y) B) (.cv y) B D p0012
  have p0015 := @g_breq2d (.classEq (.cv y) B) (.cv y) B A R p0012
  have p0016 :=
    @g_n_3anbi23d (.classEq (.cv y) B) (.classMem (.cv y) D) (.classMem B D)
      (syn_wbr A R (.cv y)) (syn_wbr A R B) (.classMem A D) p0013 p0015
  have p0018 := @g_sneqd (.classEq (.cv y) B) (.cv y) B p0012
  have p0019 :=
    @g_imaeq2d (.classEq (.cv y) B) (syn_csn (.cv y)) (syn_csn B)
      (syn_ccnv (syn_cdif R (syn_cid))) p0018
  have p0020 :=
    @g_ineq2d (.classEq (.cv y) B)
      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))
      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)) D p0019
  have p0021 :=
    @g_nceqd (.classEq (.cv y) B)
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))) p0020
  have p0022 :=
    @g_breq2d (.classEq (.cv y) B)
      (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
      (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))))
      (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn A))))
      (syn_clec) p0021
  have p0023 :=
    @g_imbi12d (.classEq (.cv y) B)
      (syn_w3a (.classMem A D) (.classMem (.cv y) D) (syn_wbr A R (.cv y)))
      (syn_w3a (.classMem A D) (.classMem B D) (syn_wbr A R B))
      (syn_wbr (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn A))))
        (syn_clec) (syn_cnc
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (syn_wbr (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn A))))
        (syn_clec)
        (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B)))))
      p0016 p0022
  have p0024 :=
    @g_wecutnclecndv x y D R dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 hyp_wecutnclecclndv_1
  have p0025 :=
    @g_vtocl2g
      (.imp (syn_w3a (.classMem (.cv x) D) (.classMem (.cv y) D) (syn_wbr (.cv x) R (.cv y)))
        (syn_wbr (syn_cnc
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
          (syn_clec) (syn_cnc
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))))
      (.imp (syn_w3a (.classMem A D) (.classMem (.cv y) D) (syn_wbr A R (.cv y))) (syn_wbr
          (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn A))))
          (syn_clec) (syn_cnc
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))))
      (.imp (syn_w3a (.classMem A D) (.classMem B D) (syn_wbr A R B)) (syn_wbr
          (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn A))))
          (syn_clec)
          (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn B))))))
      x y A B (syn_cvv) (syn_cvv) dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
      dv_cache_0010 p0011 p0023 p0024
  exact p0025

@[expose]
noncomputable def g_wecuttypedbrndv (y : Var) (z : Var) (D : Class) (R : Class)
    (_dv_D_y : y ∉ D.fv) (_dv_D_z : z ∉ D.fv) (_dv_R_y : y ∉ R.fv) (_dv_R_z : z ∉ R.fv)
    (_dv_y_z : y ≠ z) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem (.cv y) (syn_cpw1 (syn_cpw1 D)))
          (.classMem (.cv z) (syn_cpw1 (syn_cpw1 D))))
        (syn_wb (syn_wbr (.cv y) (syn_csi (syn_csi R)) (.cv z))
          (syn_wbr (syn_cuni (syn_cuni (.cv y))) R (syn_cuni (syn_cuni (.cv z)))))) :=
  by
  have p0000 :=
    @g_simpl (.classMem (.cv y) (syn_cpw1 (syn_cpw1 D)))
      (.classMem (.cv z) (syn_cpw1 (syn_cpw1 D)))
  have p0001 := @g_pw12argcl (.cv y) D
  have p0002 :=
    @g_syl
      (syn_wa (.classMem (.cv y) (syn_cpw1 (syn_cpw1 D)))
        (.classMem (.cv z) (syn_cpw1 (syn_cpw1 D))))
      (.classMem (.cv y) (syn_cpw1 (syn_cpw1 D)))
      (syn_wa (.classMem (syn_cuni (syn_cuni (.cv y))) D)
        (.classEq (.cv y) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv y)))))))
      p0000 p0001
  have p0003 :=
    @g_simprd
      (syn_wa (.classMem (.cv y) (syn_cpw1 (syn_cpw1 D)))
        (.classMem (.cv z) (syn_cpw1 (syn_cpw1 D))))
      (.classMem (syn_cuni (syn_cuni (.cv y))) D)
      (.classEq (.cv y) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv y)))))) p0002
  have p0004 :=
    @g_simpr (.classMem (.cv y) (syn_cpw1 (syn_cpw1 D)))
      (.classMem (.cv z) (syn_cpw1 (syn_cpw1 D)))
  have p0005 := @g_pw12argcl (.cv z) D
  have p0006 :=
    @g_syl
      (syn_wa (.classMem (.cv y) (syn_cpw1 (syn_cpw1 D)))
        (.classMem (.cv z) (syn_cpw1 (syn_cpw1 D))))
      (.classMem (.cv z) (syn_cpw1 (syn_cpw1 D)))
      (syn_wa (.classMem (syn_cuni (syn_cuni (.cv z))) D)
        (.classEq (.cv z) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv z)))))))
      p0004 p0005
  have p0007 :=
    @g_simprd
      (syn_wa (.classMem (.cv y) (syn_cpw1 (syn_cpw1 D)))
        (.classMem (.cv z) (syn_cpw1 (syn_cpw1 D))))
      (.classMem (syn_cuni (syn_cuni (.cv z))) D)
      (.classEq (.cv z) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv z)))))) p0006
  have p0008 :=
    @g_breq12d
      (syn_wa (.classMem (.cv y) (syn_cpw1 (syn_cpw1 D)))
        (.classMem (.cv z) (syn_cpw1 (syn_cpw1 D))))
      (.cv y) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv y))))) (.cv z)
      (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv z))))) (syn_csi (syn_csi R)) p0003 p0007
  have p0009 := @g_snex (syn_cuni (syn_cuni (.cv y)))
  have p0010 := @g_snex (syn_cuni (syn_cuni (.cv z)))
  have p0011 :=
    @g_brsnsi (syn_csn (syn_cuni (syn_cuni (.cv y))))
      (syn_csn (syn_cuni (syn_cuni (.cv z)))) (syn_csi R) p0009 p0010
  have p0012 := @g_vex y
  have p0013 := @g_uniex (.cv y) p0012
  have p0014 := @g_uniex (syn_cuni (.cv y)) p0013
  have p0015 := @g_vex z
  have p0016 := @g_uniex (.cv z) p0015
  have p0017 := @g_uniex (syn_cuni (.cv z)) p0016
  have p0018 :=
    @g_brsnsi (syn_cuni (syn_cuni (.cv y))) (syn_cuni (syn_cuni (.cv z))) R p0014 p0017
  have p0019 :=
    @g_bitri
      (syn_wbr (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv y))))) (syn_csi (syn_csi R))
        (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv z))))))
      (syn_wbr (syn_csn (syn_cuni (syn_cuni (.cv y)))) (syn_csi R)
        (syn_csn (syn_cuni (syn_cuni (.cv z)))))
      (syn_wbr (syn_cuni (syn_cuni (.cv y))) R (syn_cuni (syn_cuni (.cv z)))) p0011 p0018
  have p0020 :=
    @g_a1i
      (syn_wb (syn_wbr (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv y))))) (syn_csi (syn_csi R))
          (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv z))))))
        (syn_wbr (syn_cuni (syn_cuni (.cv y))) R (syn_cuni (syn_cuni (.cv z)))))
      (syn_wa (.classMem (.cv y) (syn_cpw1 (syn_cpw1 D)))
        (.classMem (.cv z) (syn_cpw1 (syn_cpw1 D))))
      p0019
  have p0021 :=
    @g_bitrd
      (syn_wa (.classMem (.cv y) (syn_cpw1 (syn_cpw1 D)))
        (.classMem (.cv z) (syn_cpw1 (syn_cpw1 D))))
      (syn_wbr (.cv y) (syn_csi (syn_csi R)) (.cv z))
      (syn_wbr (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv y))))) (syn_csi (syn_csi R))
        (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv z))))))
      (syn_wbr (syn_cuni (syn_cuni (.cv y))) R (syn_cuni (syn_cuni (.cv z)))) p0008 p0020
  exact p0021

@[expose]
noncomputable def g_wecuttypednclecndv (y : Var) (z : Var) (D : Class) (R : Class)
    (dv_D_y : y ∉ D.fv) (dv_D_z : z ∉ D.fv) (dv_R_y : y ∉ R.fv) (dv_R_z : z ∉ R.fv)
    (dv_y_z : y ≠ z) (hyp_wecuttypednclecndv_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D)) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem (.cv y) (syn_cpw1 (syn_cpw1 D)))
          (.classMem (.cv z) (syn_cpw1 (syn_cpw1 D))))
        (.imp (syn_wbr (.cv y) (syn_csi (syn_csi R)) (.cv z)) (syn_wbr (syn_cnc (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (syn_cuni (syn_cuni (.cv y))))))) (syn_clec) (syn_cnc (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (syn_cuni (syn_cuni (.cv z)))))))))) :=
  by
  have dv_cache_0001 : y ∉ (D).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_D_y, not_false_eq_true])
  have dv_cache_0002 : z ∉ (D).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_D_z, not_false_eq_true])
  have dv_cache_0003 : y ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_R_y, not_false_eq_true])
  have dv_cache_0004 : z ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_R_z, not_false_eq_true])
  have dv_cache_0005 : y ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show y ≠ z from (by exact dv_y_z))
  have dv_cache_0006 : Disjoint ((syn_cuni (syn_cuni (.cv y)))).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (show Disjoint ((syn_cuni (syn_cuni (.cv y)))).fv (R).fv from (by
          rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni];
          exact
            (show Disjoint (((syn_cuni (.cv y))).fv) ((R).fv) from
              (by
                rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni];
                exact
                  (show Disjoint (((Class.cv y)).fv) ((R).fv) from
                    (by
                      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
                      exact
                        (show Disjoint (({ y } : Finset Var)) ((R).fv) from
                          (Finset.disjoint_singleton_left.mpr
                            (show y ∉ (R).fv from (by exact dv_R_y))))))))))
  have p0000 :=
    @g_simpl
      (syn_wa (.classMem (.cv y) (syn_cpw1 (syn_cpw1 D)))
        (.classMem (.cv z) (syn_cpw1 (syn_cpw1 D))))
      (syn_wbr (.cv y) (syn_csi (syn_csi R)) (.cv z))
  have p0001 :=
    @g_simpl (.classMem (.cv y) (syn_cpw1 (syn_cpw1 D)))
      (.classMem (.cv z) (syn_cpw1 (syn_cpw1 D)))
  have p0002 := @g_pw12argcl (.cv y) D
  have p0003 :=
    @g_syl
      (syn_wa (.classMem (.cv y) (syn_cpw1 (syn_cpw1 D)))
        (.classMem (.cv z) (syn_cpw1 (syn_cpw1 D))))
      (.classMem (.cv y) (syn_cpw1 (syn_cpw1 D)))
      (syn_wa (.classMem (syn_cuni (syn_cuni (.cv y))) D)
        (.classEq (.cv y) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv y)))))))
      p0001 p0002
  have p0004 :=
    @g_simpld
      (syn_wa (.classMem (.cv y) (syn_cpw1 (syn_cpw1 D)))
        (.classMem (.cv z) (syn_cpw1 (syn_cpw1 D))))
      (.classMem (syn_cuni (syn_cuni (.cv y))) D)
      (.classEq (.cv y) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv y)))))) p0003
  have p0005 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv y) (syn_cpw1 (syn_cpw1 D)))
          (.classMem (.cv z) (syn_cpw1 (syn_cpw1 D))))
        (syn_wbr (.cv y) (syn_csi (syn_csi R)) (.cv z)))
      (syn_wa (.classMem (.cv y) (syn_cpw1 (syn_cpw1 D)))
        (.classMem (.cv z) (syn_cpw1 (syn_cpw1 D))))
      (.classMem (syn_cuni (syn_cuni (.cv y))) D) p0000 p0004
  have p0007 :=
    @g_simpr (.classMem (.cv y) (syn_cpw1 (syn_cpw1 D)))
      (.classMem (.cv z) (syn_cpw1 (syn_cpw1 D)))
  have p0008 := @g_pw12argcl (.cv z) D
  have p0009 :=
    @g_syl
      (syn_wa (.classMem (.cv y) (syn_cpw1 (syn_cpw1 D)))
        (.classMem (.cv z) (syn_cpw1 (syn_cpw1 D))))
      (.classMem (.cv z) (syn_cpw1 (syn_cpw1 D)))
      (syn_wa (.classMem (syn_cuni (syn_cuni (.cv z))) D)
        (.classEq (.cv z) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv z)))))))
      p0007 p0008
  have p0010 :=
    @g_simpld
      (syn_wa (.classMem (.cv y) (syn_cpw1 (syn_cpw1 D)))
        (.classMem (.cv z) (syn_cpw1 (syn_cpw1 D))))
      (.classMem (syn_cuni (syn_cuni (.cv z))) D)
      (.classEq (.cv z) (syn_csn (syn_csn (syn_cuni (syn_cuni (.cv z)))))) p0009
  have p0011 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv y) (syn_cpw1 (syn_cpw1 D)))
          (.classMem (.cv z) (syn_cpw1 (syn_cpw1 D))))
        (syn_wbr (.cv y) (syn_csi (syn_csi R)) (.cv z)))
      (syn_wa (.classMem (.cv y) (syn_cpw1 (syn_cpw1 D)))
        (.classMem (.cv z) (syn_cpw1 (syn_cpw1 D))))
      (.classMem (syn_cuni (syn_cuni (.cv z))) D) p0000 p0010
  have p0012 :=
    @g_simpr
      (syn_wa (.classMem (.cv y) (syn_cpw1 (syn_cpw1 D)))
        (.classMem (.cv z) (syn_cpw1 (syn_cpw1 D))))
      (syn_wbr (.cv y) (syn_csi (syn_csi R)) (.cv z))
  have p0014 :=
    @g_wecuttypedbrndv y z D R dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005
  have p0015 :=
    @g_biimpd
      (syn_wa (.classMem (.cv y) (syn_cpw1 (syn_cpw1 D)))
        (.classMem (.cv z) (syn_cpw1 (syn_cpw1 D))))
      (syn_wbr (.cv y) (syn_csi (syn_csi R)) (.cv z))
      (syn_wbr (syn_cuni (syn_cuni (.cv y))) R (syn_cuni (syn_cuni (.cv z)))) p0014
  have p0016 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv y) (syn_cpw1 (syn_cpw1 D)))
          (.classMem (.cv z) (syn_cpw1 (syn_cpw1 D))))
        (syn_wbr (.cv y) (syn_csi (syn_csi R)) (.cv z)))
      (syn_wa (.classMem (.cv y) (syn_cpw1 (syn_cpw1 D)))
        (.classMem (.cv z) (syn_cpw1 (syn_cpw1 D))))
      (.imp (syn_wbr (.cv y) (syn_csi (syn_csi R)) (.cv z))
        (syn_wbr (syn_cuni (syn_cuni (.cv y))) R (syn_cuni (syn_cuni (.cv z)))))
      p0000 p0015
  have p0017 :=
    @g_mpd
      (syn_wa (syn_wa (.classMem (.cv y) (syn_cpw1 (syn_cpw1 D)))
          (.classMem (.cv z) (syn_cpw1 (syn_cpw1 D))))
        (syn_wbr (.cv y) (syn_csi (syn_csi R)) (.cv z)))
      (syn_wbr (.cv y) (syn_csi (syn_csi R)) (.cv z))
      (syn_wbr (syn_cuni (syn_cuni (.cv y))) R (syn_cuni (syn_cuni (.cv z)))) p0012 p0016
  have p0018 :=
    @g_n_3jca
      (syn_wa (syn_wa (.classMem (.cv y) (syn_cpw1 (syn_cpw1 D)))
          (.classMem (.cv z) (syn_cpw1 (syn_cpw1 D))))
        (syn_wbr (.cv y) (syn_csi (syn_csi R)) (.cv z)))
      (.classMem (syn_cuni (syn_cuni (.cv y))) D)
      (.classMem (syn_cuni (syn_cuni (.cv z))) D)
      (syn_wbr (syn_cuni (syn_cuni (.cv y))) R (syn_cuni (syn_cuni (.cv z)))) p0005 p0011
      p0017
  have p0019 := @g_vex y
  have p0020 := @g_uniex (.cv y) p0019
  have p0021 := @g_uniex (syn_cuni (.cv y)) p0020
  have p0022 := @g_vex z
  have p0023 := @g_uniex (.cv z) p0022
  have p0024 := @g_uniex (syn_cuni (.cv z)) p0023
  have p0025 :=
    @g_pm3_2i (.classMem (syn_cuni (syn_cuni (.cv y))) (syn_cvv))
      (.classMem (syn_cuni (syn_cuni (.cv z))) (syn_cvv)) p0021 p0024
  have p0026 :=
    @g_wecutnclecclndv (syn_cuni (syn_cuni (.cv y))) (syn_cuni (syn_cuni (.cv z))) D R
      dv_cache_0006 hyp_wecuttypednclecndv_1
  have p0027 := Nominal.mp p0025 p0026
  have p0028 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv y) (syn_cpw1 (syn_cpw1 D)))
          (.classMem (.cv z) (syn_cpw1 (syn_cpw1 D))))
        (syn_wbr (.cv y) (syn_csi (syn_csi R)) (.cv z)))
      (syn_w3a (.classMem (syn_cuni (syn_cuni (.cv y))) D)
        (.classMem (syn_cuni (syn_cuni (.cv z))) D)
        (syn_wbr (syn_cuni (syn_cuni (.cv y))) R (syn_cuni (syn_cuni (.cv z)))))
      (syn_wbr (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
              (syn_csn (syn_cuni (syn_cuni (.cv y))))))) (syn_clec) (syn_cnc (syn_cin D
            (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
              (syn_csn (syn_cuni (syn_cuni (.cv z))))))))
      p0018 p0027
  have p0029 :=
    @g_ex
      (syn_wa (.classMem (.cv y) (syn_cpw1 (syn_cpw1 D)))
        (.classMem (.cv z) (syn_cpw1 (syn_cpw1 D))))
      (syn_wbr (.cv y) (syn_csi (syn_csi R)) (.cv z))
      (syn_wbr (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
              (syn_csn (syn_cuni (syn_cuni (.cv y))))))) (syn_clec) (syn_cnc (syn_cin D
            (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
              (syn_csn (syn_cuni (syn_cuni (.cv z))))))))
      p0028
  exact p0029

@[expose]
noncomputable def g_wecutcardtypedcardleastndv (y : Var) (z : Var) (D : Class) (R : Class)
    (K : Class) (q : Var) (dv_D_q : q ∉ D.fv) (dv_D_y : y ∉ D.fv) (dv_D_z : z ∉ D.fv)
    (dv_K_q : q ∉ K.fv) (dv_K_y : y ∉ K.fv) (dv_K_z : z ∉ K.fv) (dv_R_q : q ∉ R.fv)
    (dv_R_y : y ∉ R.fv) (dv_R_z : z ∉ R.fv) (dv_q_y : q ≠ y) (dv_q_z : q ≠ z)
    (dv_y_z : y ≠ z)
    (hyp_wecutcardtypedcardleastndv_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D))
    (hyp_wecutcardtypedcardleastndv_2 : Nominal.NPrf (.classMem K (syn_cvv))) :
    Nominal.NPrf
      (.imp (syn_wrex q (syn_cpw1 (syn_cpw1 D)) (.classMem (syn_cnc (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (syn_cuni (syn_cuni (.cv q))))))) K))
        (syn_wrex y (syn_cpw1 (syn_cpw1 D)) (syn_wa (.classMem (syn_cnc (syn_cin D
                  (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                    (syn_csn (syn_cuni (syn_cuni (.cv y))))))) K)
            (syn_wral z (syn_cpw1 (syn_cpw1 D)) (.imp (.classMem (syn_cnc (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                        (syn_csn (syn_cuni (syn_cuni (.cv z))))))) K) (syn_wbr (syn_cnc
                    (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                        (syn_csn (syn_cuni (syn_cuni (.cv y))))))) (syn_clec) (syn_cnc
                    (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                        (syn_csn (syn_cuni (syn_cuni (.cv z))))))))))))) :=
  by
  have dv_cache_0001 : q ∉ (D).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_D_q, not_false_eq_true])
  have dv_cache_0002 : y ∉ (D).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_D_y, not_false_eq_true])
  have dv_cache_0003 : z ∉ (D).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_D_z, not_false_eq_true])
  have dv_cache_0004 : q ∉ (K).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_K_q, not_false_eq_true])
  have dv_cache_0005 : y ∉ (K).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_K_y, not_false_eq_true])
  have dv_cache_0006 : z ∉ (K).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_K_z, not_false_eq_true])
  have dv_cache_0007 : q ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_R_q, not_false_eq_true])
  have dv_cache_0008 : y ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_R_y, not_false_eq_true])
  have dv_cache_0009 : z ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_R_z, not_false_eq_true])
  have dv_cache_0010 : q ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (show q ≠ y from (by exact dv_q_y))
  have dv_cache_0011 : q ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (show q ≠ z from (by exact dv_q_z))
  have dv_cache_0012 : y ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (show y ≠ z from (by exact dv_y_z))
  have dv_cache_0013 : z ∉ ((Wff.classMem (.cv y) (syn_cpw1 (syn_cpw1 D)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union,
          Finset.mem_singleton, (Ne.symm dv_y_z), dv_D_z, or_false, not_false_eq_true])
  have p0000 :=
    @g_wecutcardtypedleastndv y z D R K q dv_cache_0001 dv_cache_0002 dv_cache_0003
      dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
      dv_cache_0010 dv_cache_0011 dv_cache_0012 hyp_wecutcardtypedcardleastndv_1
      hyp_wecutcardtypedcardleastndv_2
  have p0001 :=
    @g_wecuttypednclecndv y z D R dv_cache_0002 dv_cache_0003 dv_cache_0008 dv_cache_0009
      dv_cache_0012 hyp_wecutcardtypedcardleastndv_1
  have p0002 :=
    @g_imim2d
      (syn_wa (.classMem (.cv y) (syn_cpw1 (syn_cpw1 D)))
        (.classMem (.cv z) (syn_cpw1 (syn_cpw1 D))))
      (syn_wbr (.cv y) (syn_csi (syn_csi R)) (.cv z))
      (syn_wbr (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
              (syn_csn (syn_cuni (syn_cuni (.cv y))))))) (syn_clec) (syn_cnc (syn_cin D
            (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
              (syn_csn (syn_cuni (syn_cuni (.cv z))))))))
      (.classMem (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
              (syn_csn (syn_cuni (syn_cuni (.cv z))))))) K)
      p0001
  have p0003 :=
    @g_ralimdva (.classMem (.cv y) (syn_cpw1 (syn_cpw1 D)))
      (.imp (.classMem (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (.cv z))))))) K)
        (syn_wbr (.cv y) (syn_csi (syn_csi R)) (.cv z)))
      (.imp (.classMem (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (.cv z))))))) K) (syn_wbr (syn_cnc (syn_cin D
              (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (.cv y))))))) (syn_clec) (syn_cnc (syn_cin D
              (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (.cv z)))))))))
      z (syn_cpw1 (syn_cpw1 D)) dv_cache_0013 p0002
  have p0004 :=
    @g_anim2d (.classMem (.cv y) (syn_cpw1 (syn_cpw1 D)))
      (syn_wral z (syn_cpw1 (syn_cpw1 D)) (.imp (.classMem (syn_cnc (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (syn_cuni (syn_cuni (.cv z))))))) K)
          (syn_wbr (.cv y) (syn_csi (syn_csi R)) (.cv z))))
      (syn_wral z (syn_cpw1 (syn_cpw1 D)) (.imp (.classMem (syn_cnc (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (syn_cuni (syn_cuni (.cv z))))))) K) (syn_wbr (syn_cnc (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (syn_cuni (syn_cuni (.cv y))))))) (syn_clec) (syn_cnc (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (syn_cuni (syn_cuni (.cv z))))))))))
      (.classMem (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
              (syn_csn (syn_cuni (syn_cuni (.cv y))))))) K)
      p0003
  have p0005 :=
    @g_reximia
      (syn_wa (.classMem (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (.cv y))))))) K)
        (syn_wral z (syn_cpw1 (syn_cpw1 D)) (.imp (.classMem (syn_cnc (syn_cin D
                  (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                    (syn_csn (syn_cuni (syn_cuni (.cv z))))))) K)
            (syn_wbr (.cv y) (syn_csi (syn_csi R)) (.cv z)))))
      (syn_wa (.classMem (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (.cv y))))))) K)
        (syn_wral z (syn_cpw1 (syn_cpw1 D)) (.imp (.classMem (syn_cnc (syn_cin D
                  (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                    (syn_csn (syn_cuni (syn_cuni (.cv z))))))) K) (syn_wbr (syn_cnc (syn_cin D
                  (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                    (syn_csn (syn_cuni (syn_cuni (.cv y))))))) (syn_clec) (syn_cnc (syn_cin D
                  (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                    (syn_csn (syn_cuni (syn_cuni (.cv z)))))))))))
      y (syn_cpw1 (syn_cpw1 D)) p0004
  have p0006 :=
    @g_syl
      (syn_wrex q (syn_cpw1 (syn_cpw1 D)) (.classMem (syn_cnc (syn_cin D
              (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (.cv q))))))) K))
      (syn_wrex y (syn_cpw1 (syn_cpw1 D)) (syn_wa (.classMem (syn_cnc (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (syn_cuni (syn_cuni (.cv y))))))) K)
          (syn_wral z (syn_cpw1 (syn_cpw1 D)) (.imp (.classMem (syn_cnc (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                      (syn_csn (syn_cuni (syn_cuni (.cv z))))))) K)
              (syn_wbr (.cv y) (syn_csi (syn_csi R)) (.cv z))))))
      (syn_wrex y (syn_cpw1 (syn_cpw1 D)) (syn_wa (.classMem (syn_cnc (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (syn_cuni (syn_cuni (.cv y))))))) K)
          (syn_wral z (syn_cpw1 (syn_cpw1 D)) (.imp (.classMem (syn_cnc (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                      (syn_csn (syn_cuni (syn_cuni (.cv z))))))) K) (syn_wbr (syn_cnc (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                      (syn_csn (syn_cuni (syn_cuni (.cv y))))))) (syn_clec) (syn_cnc (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                      (syn_csn (syn_cuni (syn_cuni (.cv z))))))))))))
      p0000 p0005
  exact p0006

@[expose]
noncomputable def g_elwppcandstrictslice (C : Class) (k : Var) (F : Class) :
    Nominal.NPrf
      (syn_wb (.classMem (.cv k)
          (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))))
        (syn_wa (.classMem (.cv k) (syn_cwppcand F C)) (syn_wbr (.cv k) (syn_cltc) C))) :=
  by
  have p0000 :=
    @g_elin (.cv k) (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))
  have p0001 := @g_biid (.classMem (.cv k) (syn_cwppcand F C))
  have p0002 := @g_eliniseg (syn_cltc) C (.cv k)
  have p0003 :=
    @g_anbi12i (.classMem (.cv k) (syn_cwppcand F C))
      (.classMem (.cv k) (syn_cwppcand F C))
      (.classMem (.cv k) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))
      (syn_wbr (.cv k) (syn_cltc) C) p0001 p0002
  have p0004 :=
    @g_bitri
      (.classMem (.cv k)
        (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))))
      (syn_wa (.classMem (.cv k) (syn_cwppcand F C))
        (.classMem (.cv k) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C))))
      (syn_wa (.classMem (.cv k) (syn_cwppcand F C)) (syn_wbr (.cv k) (syn_cltc) C)) p0000
      p0003
  exact p0004

@[expose]
noncomputable def g_wppreachexndv (C : Class) (F : Class)
    (hyp_wppreachexndv_1 : Nominal.NPrf (.classMem F (syn_cvv))) :
    Nominal.NPrf (.classMem (syn_cwppreach F C) (syn_cvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_cwppreach F C))
  have p0001 :=
    @g_eqid (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
  have p0002 := @g_cnvex F hyp_wppreachexndv_1
  have p0003 := @g_imageex (syn_ccnv F) p0002
  have p0004 :=
    @g_frecex (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
      (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)) p0001 p0003
  have p0005 :=
    @g_rnex (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) p0004
  have p0006 :=
    @g_uniex
      (syn_crn (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))))
      p0005
  have p0007 :=
    @g_eqeltri (syn_cwppreach F C)
      (syn_cuni
        (syn_crn (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))))
      (syn_cvv) p0000 p0006
  exact p0007

@[expose]
noncomputable def g_wppcandexndv (C : Class) (F : Class)
    (hyp_wppcandexndv_1 : Nominal.NPrf (.classMem F (syn_cvv))) :
    Nominal.NPrf (.classMem (syn_cwppcand F C) (syn_cvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_cwppcand F C))
  have p0001 := @g_vvex
  have p0002 := @g_hwcardsexg (syn_cvv)
  have p0003 := Nominal.mp p0001 p0002
  have p0004 := @g_lecex
  have p0005 := @g_cnvex (syn_clec) p0004
  have p0006 := @g_snex C
  have p0007 := @g_imaex (syn_ccnv (syn_clec)) (syn_csn C) p0005 p0006
  have p0008 :=
    @g_inex (syn_chwcards (syn_cvv)) (syn_cima (syn_ccnv (syn_clec)) (syn_csn C)) p0003
      p0007
  have p0009 := @g_wppreachexndv C F hyp_wppcandexndv_1
  have p0010 :=
    @g_inex
      (syn_cin (syn_chwcards (syn_cvv)) (syn_cima (syn_ccnv (syn_clec)) (syn_csn C)))
      (syn_cwppreach F C) p0008 p0009
  have p0011 :=
    @g_eqeltri (syn_cwppcand F C)
      (syn_cin (syn_cin (syn_chwcards (syn_cvv)) (syn_cima (syn_ccnv (syn_clec)) (syn_csn C)))
        (syn_cwppreach F C))
      (syn_cvv) p0000 p0010
  exact p0011

@[expose]
noncomputable def g_wppcandstrictsliceexndv (C : Class) (F : Class)
    (hyp_wppcandstrictsliceexndv_1 : Nominal.NPrf (.classMem F (syn_cvv))) :
    Nominal.NPrf
      (.classMem (syn_cin (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)))
        (syn_cvv)) :=
  by
  have p0000 := @g_wppcandexndv C F hyp_wppcandstrictsliceexndv_1
  have p0001 := @g_ltcex
  have p0002 := @g_cnvex (syn_cltc) p0001
  have p0003 := @g_snex C
  have p0004 := @g_imaex (syn_ccnv (syn_cltc)) (syn_csn C) p0002 p0003
  have p0005 :=
    @g_inex (syn_cwppcand F C) (syn_cima (syn_ccnv (syn_cltc)) (syn_csn C)) p0000 p0004
  exact p0005

@[expose]
noncomputable def g_wppcandnltpivoteqd (C : Class) (k : Var) (F : Class) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem (.cv k) (syn_cwppcand F C))
          (.neg (syn_wbr (.cv k) (syn_cltc) C))) (.classEq (.cv k) C)) :=
  by
  have p0000 := @g_id (.classEq (.cv k) C)
  have p0001 :=
    @g_a1i (.imp (.classEq (.cv k) C) (.classEq (.cv k) C))
      (syn_wa (.classMem (.cv k) (syn_cwppcand F C)) (.neg (syn_wbr (.cv k) (syn_cltc) C)))
      p0000
  have p0002 :=
    @g_simpl (.classMem (.cv k) (syn_cwppcand F C)) (.neg (syn_wbr (.cv k) (syn_cltc) C))
  have p0003 := @g_elwppcand C (.cv k) F
  have p0004 :=
    @g_biimpi (.classMem (.cv k) (syn_cwppcand F C))
      (syn_wa (syn_wa (.classMem (.cv k) (syn_chwcards (syn_cvv)))
          (syn_wbr (.cv k) (syn_clec) C)) (.classMem (.cv k) (syn_cwppreach F C)))
      p0003
  have p0005 :=
    @g_syl
      (syn_wa (.classMem (.cv k) (syn_cwppcand F C)) (.neg (syn_wbr (.cv k) (syn_cltc) C)))
      (.classMem (.cv k) (syn_cwppcand F C))
      (syn_wa (syn_wa (.classMem (.cv k) (syn_chwcards (syn_cvv)))
          (syn_wbr (.cv k) (syn_clec) C)) (.classMem (.cv k) (syn_cwppreach F C)))
      p0002 p0004
  have p0006 :=
    @g_simpld
      (syn_wa (.classMem (.cv k) (syn_cwppcand F C)) (.neg (syn_wbr (.cv k) (syn_cltc) C)))
      (syn_wa (.classMem (.cv k) (syn_chwcards (syn_cvv))) (syn_wbr (.cv k) (syn_clec) C))
      (.classMem (.cv k) (syn_cwppreach F C)) p0005
  have p0007 :=
    @g_simprd
      (syn_wa (.classMem (.cv k) (syn_cwppcand F C)) (.neg (syn_wbr (.cv k) (syn_cltc) C)))
      (.classMem (.cv k) (syn_chwcards (syn_cvv))) (syn_wbr (.cv k) (syn_clec) C) p0006
  have p0008 := @g_brltc (.cv k) C
  have p0009 :=
    @g_biimpri (syn_wbr (.cv k) (syn_cltc) C)
      (syn_wa (syn_wbr (.cv k) (syn_clec) C) (syn_wne (.cv k) C)) p0008
  have p0010 :=
    @g_ex (syn_wbr (.cv k) (syn_clec) C) (syn_wne (.cv k) C)
      (syn_wbr (.cv k) (syn_cltc) C) p0009
  have p0011 :=
    @g_syl
      (syn_wa (.classMem (.cv k) (syn_cwppcand F C)) (.neg (syn_wbr (.cv k) (syn_cltc) C)))
      (syn_wbr (.cv k) (syn_clec) C)
      (.imp (syn_wne (.cv k) C) (syn_wbr (.cv k) (syn_cltc) C)) p0007 p0010
  have p0012 :=
    @g_simpr (.classMem (.cv k) (syn_cwppcand F C)) (.neg (syn_wbr (.cv k) (syn_cltc) C))
  have p0013 :=
    @g_pm2_21d
      (syn_wa (.classMem (.cv k) (syn_cwppcand F C)) (.neg (syn_wbr (.cv k) (syn_cltc) C)))
      (syn_wbr (.cv k) (syn_cltc) C) (.classEq (.cv k) C) p0012
  have p0014 :=
    @g_syld
      (syn_wa (.classMem (.cv k) (syn_cwppcand F C)) (.neg (syn_wbr (.cv k) (syn_cltc) C)))
      (syn_wne (.cv k) C) (syn_wbr (.cv k) (syn_cltc) C) (.classEq (.cv k) C) p0011 p0013
  have p0015 :=
    @g_pm2_61dne
      (syn_wa (.classMem (.cv k) (syn_cwppcand F C)) (.neg (syn_wbr (.cv k) (syn_cltc) C)))
      (.classEq (.cv k) C) (.cv k) C p0001 p0014
  exact p0015


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk016Compact001Part029`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_wecutcardrepleastdndv (y : Var) (D : Class) (R : Class) (k : Var)
    (K : Class) (q : Var) (dv_D_k : k ∉ D.fv) (dv_D_q : q ∉ D.fv) (dv_D_y : y ∉ D.fv)
    (dv_K_k : k ∉ K.fv) (dv_K_q : q ∉ K.fv) (dv_K_y : y ∉ K.fv) (dv_R_k : k ∉ R.fv)
    (dv_R_q : q ∉ R.fv) (dv_R_y : y ∉ R.fv) (dv_k_q : k ≠ q) (dv_k_y : k ≠ y)
    (dv_q_y : q ≠ y) (hyp_wecutcardrepleastdndv_1 : Nominal.NPrf (syn_wbr R (syn_cwe) D))
    (hyp_wecutcardrepleastdndv_2 : Nominal.NPrf (.classMem K (syn_cvv)))
    (hyp_wecutcardrepleastdndv_3 : Nominal.NPrf (syn_wral k K
          (syn_wrex q (syn_cpw1 (syn_cpw1 D)) (.classEq (.cv k) (syn_cnc (syn_cin D
                  (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                    (syn_csn (syn_cuni (syn_cuni (.cv q))))))))))) :
    Nominal.NPrf
      (.imp (syn_wne K (syn_c0)) (syn_wrex y (syn_cpw1 (syn_cpw1 D)) (syn_wa (.classMem (syn_cnc
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                    (syn_csn (syn_cuni (syn_cuni (.cv y))))))) K) (syn_wral k K (syn_wbr
                (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                      (syn_csn (syn_cuni (syn_cuni (.cv y))))))) (syn_clec) (.cv k)))))) :=
  by
  let proofSupport : Finset Var :=
    ({ y } : Finset Var) ∪ D.fv ∪ R.fv ∪ ({ k } : Finset Var) ∪ K.fv ∪
      ({ q } : Finset Var)
  let z : Var := freshVar proofSupport 0
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z_ne_y : z ≠ y := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _
                (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))))
  have fresh_y_ne_z : y ≠ z := Ne.symm fresh_z_ne_y
  have fresh_z_not_D : z ∉ D.fv := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_z_not_R : z ∉ R.fv := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_z_ne_k : z ≠ k := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_k_ne_z : k ≠ z := Ne.symm fresh_z_ne_k
  have fresh_z_not_K : z ∉ K.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_z_ne_q : z ≠ q := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_q_ne_z : q ≠ z := Ne.symm fresh_z_ne_q
  have dv_cache_0001 : k ∉ (K).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_K_k, not_false_eq_true])
  have dv_cache_0002 : q ∉ (K).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_K_q, not_false_eq_true])
  have dv_cache_0003 : k ∉ ((syn_cpw1 (syn_cpw1 D))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, dv_D_k,
          not_false_eq_true])
  have dv_cache_0004 : k ≠ q :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show k ≠ q from (by exact dv_k_q))
  have dv_cache_0005 :
    k ∉
      ((Wff.classMem (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (.cv q))))))) K)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, dv_D_k, dv_R_k, dv_k_q, dv_K_k, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0006 : q ∉ (D).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_D_q, not_false_eq_true])
  have dv_cache_0007 : y ∉ (D).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_D_y, not_false_eq_true])
  have dv_cache_0008 : z ∉ (D).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_D, not_false_eq_true])
  have dv_cache_0009 : y ∉ (K).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_K_y, not_false_eq_true])
  have dv_cache_0010 : z ∉ (K).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_K, not_false_eq_true])
  have dv_cache_0011 : q ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_R_q, not_false_eq_true])
  have dv_cache_0012 : y ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_R_y, not_false_eq_true])
  have dv_cache_0013 : z ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_R, not_false_eq_true])
  have dv_cache_0014 : q ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact (show q ≠ y from (by exact dv_q_y))
  have dv_cache_0015 : q ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (show q ≠ z from (by exact fresh_q_ne_z))
  have dv_cache_0016 : y ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (show y ≠ z from (by exact fresh_y_ne_z))
  have dv_cache_0017 : z ∉ ((Class.cv q)).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_z_ne_q, not_false_eq_true])
  have dv_cache_0018 : z ∉ ((syn_cpw1 (syn_cpw1 D))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, fresh_z_not_D,
          not_false_eq_true])
  have dv_cache_0019 :
    z ∉
      ((Wff.imp (.classMem (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (syn_cuni (syn_cuni (.cv q))))))) K) (syn_wbr (syn_cnc (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (syn_cuni (syn_cuni (.cv y))))))) (syn_clec) (syn_cnc (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (syn_cuni (syn_cuni (.cv q)))))))))).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, Finset.mem_union,
          Finset.mem_singleton, fresh_z_not_D, fresh_z_not_R, fresh_z_ne_q, fresh_z_not_K,
          fresh_z_ne_y, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0020 :
    q ∉
      ((syn_wbr (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (.cv y))))))) (syn_clec) (.cv k))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, Finset.mem_union,
          Finset.mem_singleton, dv_D_q, dv_R_q, dv_q_y, (Ne.symm dv_k_q),
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0021 :
    q ∉
      ((syn_wa (syn_wa (.classMem (syn_cnc (syn_cin D
                  (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                    (syn_csn (syn_cuni (syn_cuni (.cv y))))))) K)
            (syn_wral z (syn_cpw1 (syn_cpw1 D)) (.imp (.classMem (syn_cnc (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                        (syn_csn (syn_cuni (syn_cuni (.cv z))))))) K) (syn_wbr (syn_cnc
                    (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                        (syn_csn (syn_cuni (syn_cuni (.cv y))))))) (syn_clec) (syn_cnc
                    (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                        (syn_csn (syn_cuni (syn_cuni (.cv z)))))))))))
          (.classMem (.cv k) K))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, dv_D_q, dv_R_q, dv_q_y, dv_K_q,
          fresh_q_ne_z, (Ne.symm dv_k_q), compact_fv_not_mem_empty, or_false, and_false,
          not_false_eq_true])
  have dv_cache_0022 :
    k ∉
      ((syn_wa (.classMem (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (syn_cuni (syn_cuni (.cv y))))))) K)
          (syn_wral z (syn_cpw1 (syn_cpw1 D)) (.imp (.classMem (syn_cnc (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                      (syn_csn (syn_cuni (syn_cuni (.cv z))))))) K) (syn_wbr (syn_cnc (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                      (syn_csn (syn_cuni (syn_cuni (.cv y))))))) (syn_clec) (syn_cnc (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                      (syn_csn (syn_cuni (syn_cuni (.cv z)))))))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact
      (by
        have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, dv_D_k, dv_R_k, dv_k_y, dv_K_k,
          fresh_k_ne_z, compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have p0000 := @g_id (syn_wne K (syn_c0))
  have p0001 :=
    @g_jctir (syn_wne K (syn_c0)) (syn_wne K (syn_c0))
      (syn_wral k K (syn_wrex q (syn_cpw1 (syn_cpw1 D)) (.classEq (.cv k) (syn_cnc (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (syn_cuni (syn_cuni (.cv q))))))))))
      p0000 hyp_wecutcardrepleastdndv_3
  have p0002 :=
    @g_r19_2z
      (syn_wrex q (syn_cpw1 (syn_cpw1 D)) (.classEq (.cv k) (syn_cnc (syn_cin D
              (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (.cv q)))))))))
      k K dv_cache_0001
  have p0003 :=
    @g_syl (syn_wne K (syn_c0))
      (syn_wa (syn_wne K (syn_c0)) (syn_wral k K (syn_wrex q (syn_cpw1 (syn_cpw1 D))
            (.classEq (.cv k) (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                    (syn_csn (syn_cuni (syn_cuni (.cv q)))))))))))
      (syn_wrex k K (syn_wrex q (syn_cpw1 (syn_cpw1 D)) (.classEq (.cv k) (syn_cnc (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (syn_cuni (syn_cuni (.cv q))))))))))
      p0001 p0002
  have p0004 :=
    @g_rexcom
      (.classEq (.cv k) (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
              (syn_csn (syn_cuni (syn_cuni (.cv q))))))))
      k q K (syn_cpw1 (syn_cpw1 D)) dv_cache_0002 dv_cache_0003 dv_cache_0004
  have p0005 :=
    @g_biimpi
      (syn_wrex k K (syn_wrex q (syn_cpw1 (syn_cpw1 D)) (.classEq (.cv k) (syn_cnc (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (syn_cuni (syn_cuni (.cv q))))))))))
      (syn_wrex q (syn_cpw1 (syn_cpw1 D)) (syn_wrex k K (.classEq (.cv k) (syn_cnc (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (syn_cuni (syn_cuni (.cv q))))))))))
      p0004
  have p0006 :=
    @g_syl (syn_wne K (syn_c0))
      (syn_wrex k K (syn_wrex q (syn_cpw1 (syn_cpw1 D)) (.classEq (.cv k) (syn_cnc (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (syn_cuni (syn_cuni (.cv q))))))))))
      (syn_wrex q (syn_cpw1 (syn_cpw1 D)) (syn_wrex k K (.classEq (.cv k) (syn_cnc (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (syn_cuni (syn_cuni (.cv q))))))))))
      p0003 p0005
  have p0007 :=
    @g_simpr (.classMem (.cv k) K)
      (.classEq (.cv k) (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
              (syn_csn (syn_cuni (syn_cuni (.cv q))))))))
  have p0008 :=
    @g_simpl (.classMem (.cv k) K)
      (.classEq (.cv k) (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
              (syn_csn (syn_cuni (syn_cuni (.cv q))))))))
  have p0009 :=
    @g_eqeltrrd
      (syn_wa (.classMem (.cv k) K) (.classEq (.cv k) (syn_cnc (syn_cin D
              (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (.cv q)))))))))
      (.cv k)
      (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
            (syn_csn (syn_cuni (syn_cuni (.cv q)))))))
      K p0007 p0008
  have p0010 :=
    @g_rexlimiva
      (.classEq (.cv k) (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
              (syn_csn (syn_cuni (syn_cuni (.cv q))))))))
      (.classMem (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
              (syn_csn (syn_cuni (syn_cuni (.cv q))))))) K)
      k K dv_cache_0005 p0009
  have p0011 :=
    @g_reximi
      (syn_wrex k K (.classEq (.cv k) (syn_cnc (syn_cin D
              (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (.cv q)))))))))
      (.classMem (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
              (syn_csn (syn_cuni (syn_cuni (.cv q))))))) K)
      q (syn_cpw1 (syn_cpw1 D)) p0010
  have p0012 :=
    @g_syl (syn_wne K (syn_c0))
      (syn_wrex q (syn_cpw1 (syn_cpw1 D)) (syn_wrex k K (.classEq (.cv k) (syn_cnc (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (syn_cuni (syn_cuni (.cv q))))))))))
      (syn_wrex q (syn_cpw1 (syn_cpw1 D)) (.classMem (syn_cnc (syn_cin D
              (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (.cv q))))))) K))
      p0006 p0011
  have p0013 :=
    @g_wecutcardtypedcardleastndv y z D R K q dv_cache_0006 dv_cache_0007 dv_cache_0008
      dv_cache_0002 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
      dv_cache_0014 dv_cache_0015 dv_cache_0016 hyp_wecutcardrepleastdndv_1
      hyp_wecutcardrepleastdndv_2
  have p0014 :=
    @g_syl (syn_wne K (syn_c0))
      (syn_wrex q (syn_cpw1 (syn_cpw1 D)) (.classMem (syn_cnc (syn_cin D
              (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (.cv q))))))) K))
      (syn_wrex y (syn_cpw1 (syn_cpw1 D)) (syn_wa (.classMem (syn_cnc (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (syn_cuni (syn_cuni (.cv y))))))) K)
          (syn_wral z (syn_cpw1 (syn_cpw1 D)) (.imp (.classMem (syn_cnc (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                      (syn_csn (syn_cuni (syn_cuni (.cv z))))))) K) (syn_wbr (syn_cnc (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                      (syn_csn (syn_cuni (syn_cuni (.cv y))))))) (syn_clec) (syn_cnc (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                      (syn_csn (syn_cuni (syn_cuni (.cv z))))))))))))
      p0012 p0013
  have p0015 :=
    @g_simpl
      (.classMem (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
              (syn_csn (syn_cuni (syn_cuni (.cv y))))))) K)
      (syn_wral z (syn_cpw1 (syn_cpw1 D)) (.imp (.classMem (syn_cnc (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (syn_cuni (syn_cuni (.cv z))))))) K) (syn_wbr (syn_cnc (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (syn_cuni (syn_cuni (.cv y))))))) (syn_clec) (syn_cnc (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (syn_cuni (syn_cuni (.cv z))))))))))
  have p0016 :=
    @g_simpr
      (syn_wa (.classMem (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (.cv y))))))) K)
        (syn_wral z (syn_cpw1 (syn_cpw1 D)) (.imp (.classMem (syn_cnc (syn_cin D
                  (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                    (syn_csn (syn_cuni (syn_cuni (.cv z))))))) K) (syn_wbr (syn_cnc (syn_cin D
                  (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                    (syn_csn (syn_cuni (syn_cuni (.cv y))))))) (syn_clec) (syn_cnc (syn_cin D
                  (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                    (syn_csn (syn_cuni (syn_cuni (.cv z)))))))))))
      (.classMem (.cv k) K)
  have p0017 :=
    @g_rsp
      (syn_wrex q (syn_cpw1 (syn_cpw1 D)) (.classEq (.cv k) (syn_cnc (syn_cin D
              (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (.cv q)))))))))
      k K
  have p0018 := Nominal.mp hyp_wecutcardrepleastdndv_3 p0017
  have p0019 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (syn_cuni (syn_cuni (.cv y))))))) K)
          (syn_wral z (syn_cpw1 (syn_cpw1 D)) (.imp (.classMem (syn_cnc (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                      (syn_csn (syn_cuni (syn_cuni (.cv z))))))) K) (syn_wbr (syn_cnc (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                      (syn_csn (syn_cuni (syn_cuni (.cv y))))))) (syn_clec) (syn_cnc (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                      (syn_csn (syn_cuni (syn_cuni (.cv z))))))))))) (.classMem (.cv k) K))
      (.classMem (.cv k) K)
      (syn_wrex q (syn_cpw1 (syn_cpw1 D)) (.classEq (.cv k) (syn_cnc (syn_cin D
              (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (.cv q)))))))))
      p0016 p0018
  have p0020 :=
    @g_simpr
      (syn_wa (syn_wa (.classMem (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (syn_cuni (syn_cuni (.cv y))))))) K)
          (syn_wral z (syn_cpw1 (syn_cpw1 D)) (.imp (.classMem (syn_cnc (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                      (syn_csn (syn_cuni (syn_cuni (.cv z))))))) K) (syn_wbr (syn_cnc (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                      (syn_csn (syn_cuni (syn_cuni (.cv y))))))) (syn_clec) (syn_cnc (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                      (syn_csn (syn_cuni (syn_cuni (.cv z))))))))))) (.classMem (.cv k) K))
      (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classEq (.cv k) (syn_cnc (syn_cin D
              (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (.cv q)))))))))
  have p0021 :=
    @g_simprd
      (syn_wa (syn_wa (syn_wa (.classMem (syn_cnc (syn_cin D
                  (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                    (syn_csn (syn_cuni (syn_cuni (.cv y))))))) K)
            (syn_wral z (syn_cpw1 (syn_cpw1 D)) (.imp (.classMem (syn_cnc (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                        (syn_csn (syn_cuni (syn_cuni (.cv z))))))) K) (syn_wbr (syn_cnc
                    (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                        (syn_csn (syn_cuni (syn_cuni (.cv y))))))) (syn_clec) (syn_cnc
                    (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                        (syn_csn (syn_cuni (syn_cuni (.cv z))))))))))) (.classMem (.cv k) K))
        (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classEq (.cv k) (syn_cnc
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (syn_cuni (syn_cuni (.cv q))))))))))
      (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))
      (.classEq (.cv k) (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
              (syn_csn (syn_cuni (syn_cuni (.cv q))))))))
      p0020
  have p0022 :=
    @g_simpl
      (syn_wa (syn_wa (.classMem (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (syn_cuni (syn_cuni (.cv y))))))) K)
          (syn_wral z (syn_cpw1 (syn_cpw1 D)) (.imp (.classMem (syn_cnc (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                      (syn_csn (syn_cuni (syn_cuni (.cv z))))))) K) (syn_wbr (syn_cnc (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                      (syn_csn (syn_cuni (syn_cuni (.cv y))))))) (syn_clec) (syn_cnc (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                      (syn_csn (syn_cuni (syn_cuni (.cv z))))))))))) (.classMem (.cv k) K))
      (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classEq (.cv k) (syn_cnc (syn_cin D
              (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (.cv q)))))))))
  have p0024 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem (syn_cnc (syn_cin D
                  (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                    (syn_csn (syn_cuni (syn_cuni (.cv y))))))) K)
            (syn_wral z (syn_cpw1 (syn_cpw1 D)) (.imp (.classMem (syn_cnc (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                        (syn_csn (syn_cuni (syn_cuni (.cv z))))))) K) (syn_wbr (syn_cnc
                    (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                        (syn_csn (syn_cuni (syn_cuni (.cv y))))))) (syn_clec) (syn_cnc
                    (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                        (syn_csn (syn_cuni (syn_cuni (.cv z))))))))))) (.classMem (.cv k) K))
        (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classEq (.cv k) (syn_cnc
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (syn_cuni (syn_cuni (.cv q))))))))))
      (syn_wa (syn_wa (.classMem (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (syn_cuni (syn_cuni (.cv y))))))) K)
          (syn_wral z (syn_cpw1 (syn_cpw1 D)) (.imp (.classMem (syn_cnc (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                      (syn_csn (syn_cuni (syn_cuni (.cv z))))))) K) (syn_wbr (syn_cnc (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                      (syn_csn (syn_cuni (syn_cuni (.cv y))))))) (syn_clec) (syn_cnc (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                      (syn_csn (syn_cuni (syn_cuni (.cv z))))))))))) (.classMem (.cv k) K))
      (.classMem (.cv k) K) p0022 p0016
  have p0025 :=
    @g_eqeltrrd
      (syn_wa (syn_wa (syn_wa (.classMem (syn_cnc (syn_cin D
                  (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                    (syn_csn (syn_cuni (syn_cuni (.cv y))))))) K)
            (syn_wral z (syn_cpw1 (syn_cpw1 D)) (.imp (.classMem (syn_cnc (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                        (syn_csn (syn_cuni (syn_cuni (.cv z))))))) K) (syn_wbr (syn_cnc
                    (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                        (syn_csn (syn_cuni (syn_cuni (.cv y))))))) (syn_clec) (syn_cnc
                    (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                        (syn_csn (syn_cuni (syn_cuni (.cv z))))))))))) (.classMem (.cv k) K))
        (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classEq (.cv k) (syn_cnc
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (syn_cuni (syn_cuni (.cv q))))))))))
      (.cv k)
      (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
            (syn_csn (syn_cuni (syn_cuni (.cv q)))))))
      K p0021 p0024
  have p0027 :=
    @g_simpl
      (syn_wa (.classMem (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (.cv y))))))) K)
        (syn_wral z (syn_cpw1 (syn_cpw1 D)) (.imp (.classMem (syn_cnc (syn_cin D
                  (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                    (syn_csn (syn_cuni (syn_cuni (.cv z))))))) K) (syn_wbr (syn_cnc (syn_cin D
                  (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                    (syn_csn (syn_cuni (syn_cuni (.cv y))))))) (syn_clec) (syn_cnc (syn_cin D
                  (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                    (syn_csn (syn_cuni (syn_cuni (.cv z)))))))))))
      (.classMem (.cv k) K)
  have p0028 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem (syn_cnc (syn_cin D
                  (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                    (syn_csn (syn_cuni (syn_cuni (.cv y))))))) K)
            (syn_wral z (syn_cpw1 (syn_cpw1 D)) (.imp (.classMem (syn_cnc (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                        (syn_csn (syn_cuni (syn_cuni (.cv z))))))) K) (syn_wbr (syn_cnc
                    (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                        (syn_csn (syn_cuni (syn_cuni (.cv y))))))) (syn_clec) (syn_cnc
                    (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                        (syn_csn (syn_cuni (syn_cuni (.cv z))))))))))) (.classMem (.cv k) K))
        (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classEq (.cv k) (syn_cnc
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (syn_cuni (syn_cuni (.cv q))))))))))
      (syn_wa (syn_wa (.classMem (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (syn_cuni (syn_cuni (.cv y))))))) K)
          (syn_wral z (syn_cpw1 (syn_cpw1 D)) (.imp (.classMem (syn_cnc (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                      (syn_csn (syn_cuni (syn_cuni (.cv z))))))) K) (syn_wbr (syn_cnc (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                      (syn_csn (syn_cuni (syn_cuni (.cv y))))))) (syn_clec) (syn_cnc (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                      (syn_csn (syn_cuni (syn_cuni (.cv z))))))))))) (.classMem (.cv k) K))
      (syn_wa (.classMem (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (.cv y))))))) K)
        (syn_wral z (syn_cpw1 (syn_cpw1 D)) (.imp (.classMem (syn_cnc (syn_cin D
                  (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                    (syn_csn (syn_cuni (syn_cuni (.cv z))))))) K) (syn_wbr (syn_cnc (syn_cin D
                  (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                    (syn_csn (syn_cuni (syn_cuni (.cv y))))))) (syn_clec) (syn_cnc (syn_cin D
                  (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                    (syn_csn (syn_cuni (syn_cuni (.cv z)))))))))))
      p0022 p0027
  have p0029 :=
    @g_simpr
      (.classMem (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
              (syn_csn (syn_cuni (syn_cuni (.cv y))))))) K)
      (syn_wral z (syn_cpw1 (syn_cpw1 D)) (.imp (.classMem (syn_cnc (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (syn_cuni (syn_cuni (.cv z))))))) K) (syn_wbr (syn_cnc (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (syn_cuni (syn_cuni (.cv y))))))) (syn_clec) (syn_cnc (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (syn_cuni (syn_cuni (.cv z))))))))))
  have p0030 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem (syn_cnc (syn_cin D
                  (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                    (syn_csn (syn_cuni (syn_cuni (.cv y))))))) K)
            (syn_wral z (syn_cpw1 (syn_cpw1 D)) (.imp (.classMem (syn_cnc (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                        (syn_csn (syn_cuni (syn_cuni (.cv z))))))) K) (syn_wbr (syn_cnc
                    (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                        (syn_csn (syn_cuni (syn_cuni (.cv y))))))) (syn_clec) (syn_cnc
                    (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                        (syn_csn (syn_cuni (syn_cuni (.cv z))))))))))) (.classMem (.cv k) K))
        (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classEq (.cv k) (syn_cnc
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (syn_cuni (syn_cuni (.cv q))))))))))
      (syn_wa (.classMem (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (.cv y))))))) K)
        (syn_wral z (syn_cpw1 (syn_cpw1 D)) (.imp (.classMem (syn_cnc (syn_cin D
                  (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                    (syn_csn (syn_cuni (syn_cuni (.cv z))))))) K) (syn_wbr (syn_cnc (syn_cin D
                  (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                    (syn_csn (syn_cuni (syn_cuni (.cv y))))))) (syn_clec) (syn_cnc (syn_cin D
                  (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                    (syn_csn (syn_cuni (syn_cuni (.cv z)))))))))))
      (syn_wral z (syn_cpw1 (syn_cpw1 D)) (.imp (.classMem (syn_cnc (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (syn_cuni (syn_cuni (.cv z))))))) K) (syn_wbr (syn_cnc (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (syn_cuni (syn_cuni (.cv y))))))) (syn_clec) (syn_cnc (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (syn_cuni (syn_cuni (.cv z))))))))))
      p0028 p0029
  have p0032 :=
    @g_simpld
      (syn_wa (syn_wa (syn_wa (.classMem (syn_cnc (syn_cin D
                  (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                    (syn_csn (syn_cuni (syn_cuni (.cv y))))))) K)
            (syn_wral z (syn_cpw1 (syn_cpw1 D)) (.imp (.classMem (syn_cnc (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                        (syn_csn (syn_cuni (syn_cuni (.cv z))))))) K) (syn_wbr (syn_cnc
                    (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                        (syn_csn (syn_cuni (syn_cuni (.cv y))))))) (syn_clec) (syn_cnc
                    (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                        (syn_csn (syn_cuni (syn_cuni (.cv z))))))))))) (.classMem (.cv k) K))
        (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classEq (.cv k) (syn_cnc
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (syn_cuni (syn_cuni (.cv q))))))))))
      (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))
      (.classEq (.cv k) (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
              (syn_csn (syn_cuni (syn_cuni (.cv q))))))))
      p0020
  have p0033 := @g_id (.classEq (.cv z) (.cv q))
  have p0034 := @g_unieqd (.classEq (.cv z) (.cv q)) (.cv z) (.cv q) p0033
  have p0035 :=
    @g_unieqd (.classEq (.cv z) (.cv q)) (syn_cuni (.cv z)) (syn_cuni (.cv q)) p0034
  have p0036 :=
    @g_sneqd (.classEq (.cv z) (.cv q)) (syn_cuni (syn_cuni (.cv z)))
      (syn_cuni (syn_cuni (.cv q))) p0035
  have p0037 :=
    @g_imaeq2d (.classEq (.cv z) (.cv q)) (syn_csn (syn_cuni (syn_cuni (.cv z))))
      (syn_csn (syn_cuni (syn_cuni (.cv q)))) (syn_ccnv (syn_cdif R (syn_cid))) p0036
  have p0038 :=
    @g_ineq2d (.classEq (.cv z) (.cv q))
      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv z)))))
      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (.cv q)))))
      D p0037
  have p0039 :=
    @g_nceqd (.classEq (.cv z) (.cv q))
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
          (syn_csn (syn_cuni (syn_cuni (.cv z))))))
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
          (syn_csn (syn_cuni (syn_cuni (.cv q))))))
      p0038
  have p0040 :=
    @g_eleq1d (.classEq (.cv z) (.cv q))
      (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
            (syn_csn (syn_cuni (syn_cuni (.cv z)))))))
      (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
            (syn_csn (syn_cuni (syn_cuni (.cv q)))))))
      K p0039
  have p0048 :=
    @g_breq2d (.classEq (.cv z) (.cv q))
      (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
            (syn_csn (syn_cuni (syn_cuni (.cv z)))))))
      (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
            (syn_csn (syn_cuni (syn_cuni (.cv q)))))))
      (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
            (syn_csn (syn_cuni (syn_cuni (.cv y)))))))
      (syn_clec) p0039
  have p0049 :=
    @g_imbi12d (.classEq (.cv z) (.cv q))
      (.classMem (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
              (syn_csn (syn_cuni (syn_cuni (.cv z))))))) K)
      (.classMem (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
              (syn_csn (syn_cuni (syn_cuni (.cv q))))))) K)
      (syn_wbr (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
              (syn_csn (syn_cuni (syn_cuni (.cv y))))))) (syn_clec) (syn_cnc (syn_cin D
            (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
              (syn_csn (syn_cuni (syn_cuni (.cv z))))))))
      (syn_wbr (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
              (syn_csn (syn_cuni (syn_cuni (.cv y))))))) (syn_clec) (syn_cnc (syn_cin D
            (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
              (syn_csn (syn_cuni (syn_cuni (.cv q))))))))
      p0040 p0048
  have p0050 :=
    @g_rspcv
      (.imp (.classMem (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (.cv z))))))) K) (syn_wbr (syn_cnc (syn_cin D
              (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (.cv y))))))) (syn_clec) (syn_cnc (syn_cin D
              (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (.cv z)))))))))
      (.imp (.classMem (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (.cv q))))))) K) (syn_wbr (syn_cnc (syn_cin D
              (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (.cv y))))))) (syn_clec) (syn_cnc (syn_cin D
              (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (.cv q)))))))))
      z (.cv q) (syn_cpw1 (syn_cpw1 D)) dv_cache_0017 dv_cache_0018 dv_cache_0019 p0049
  have p0051 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem (syn_cnc (syn_cin D
                  (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                    (syn_csn (syn_cuni (syn_cuni (.cv y))))))) K)
            (syn_wral z (syn_cpw1 (syn_cpw1 D)) (.imp (.classMem (syn_cnc (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                        (syn_csn (syn_cuni (syn_cuni (.cv z))))))) K) (syn_wbr (syn_cnc
                    (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                        (syn_csn (syn_cuni (syn_cuni (.cv y))))))) (syn_clec) (syn_cnc
                    (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                        (syn_csn (syn_cuni (syn_cuni (.cv z))))))))))) (.classMem (.cv k) K))
        (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classEq (.cv k) (syn_cnc
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (syn_cuni (syn_cuni (.cv q))))))))))
      (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D)))
      (.imp (syn_wral z (syn_cpw1 (syn_cpw1 D)) (.imp (.classMem (syn_cnc (syn_cin D
                  (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                    (syn_csn (syn_cuni (syn_cuni (.cv z))))))) K) (syn_wbr (syn_cnc (syn_cin D
                  (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                    (syn_csn (syn_cuni (syn_cuni (.cv y))))))) (syn_clec) (syn_cnc (syn_cin D
                  (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                    (syn_csn (syn_cuni (syn_cuni (.cv z)))))))))) (.imp (.classMem (syn_cnc
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (syn_cuni (syn_cuni (.cv q))))))) K) (syn_wbr (syn_cnc (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (syn_cuni (syn_cuni (.cv y))))))) (syn_clec) (syn_cnc (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (syn_cuni (syn_cuni (.cv q))))))))))
      p0032 p0050
  have p0052 :=
    @g_mpd
      (syn_wa (syn_wa (syn_wa (.classMem (syn_cnc (syn_cin D
                  (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                    (syn_csn (syn_cuni (syn_cuni (.cv y))))))) K)
            (syn_wral z (syn_cpw1 (syn_cpw1 D)) (.imp (.classMem (syn_cnc (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                        (syn_csn (syn_cuni (syn_cuni (.cv z))))))) K) (syn_wbr (syn_cnc
                    (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                        (syn_csn (syn_cuni (syn_cuni (.cv y))))))) (syn_clec) (syn_cnc
                    (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                        (syn_csn (syn_cuni (syn_cuni (.cv z))))))))))) (.classMem (.cv k) K))
        (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classEq (.cv k) (syn_cnc
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (syn_cuni (syn_cuni (.cv q))))))))))
      (syn_wral z (syn_cpw1 (syn_cpw1 D)) (.imp (.classMem (syn_cnc (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (syn_cuni (syn_cuni (.cv z))))))) K) (syn_wbr (syn_cnc (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (syn_cuni (syn_cuni (.cv y))))))) (syn_clec) (syn_cnc (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (syn_cuni (syn_cuni (.cv z))))))))))
      (.imp (.classMem (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (.cv q))))))) K) (syn_wbr (syn_cnc (syn_cin D
              (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (.cv y))))))) (syn_clec) (syn_cnc (syn_cin D
              (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (.cv q)))))))))
      p0030 p0051
  have p0053 :=
    @g_mpd
      (syn_wa (syn_wa (syn_wa (.classMem (syn_cnc (syn_cin D
                  (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                    (syn_csn (syn_cuni (syn_cuni (.cv y))))))) K)
            (syn_wral z (syn_cpw1 (syn_cpw1 D)) (.imp (.classMem (syn_cnc (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                        (syn_csn (syn_cuni (syn_cuni (.cv z))))))) K) (syn_wbr (syn_cnc
                    (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                        (syn_csn (syn_cuni (syn_cuni (.cv y))))))) (syn_clec) (syn_cnc
                    (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                        (syn_csn (syn_cuni (syn_cuni (.cv z))))))))))) (.classMem (.cv k) K))
        (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classEq (.cv k) (syn_cnc
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (syn_cuni (syn_cuni (.cv q))))))))))
      (.classMem (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
              (syn_csn (syn_cuni (syn_cuni (.cv q))))))) K)
      (syn_wbr (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
              (syn_csn (syn_cuni (syn_cuni (.cv y))))))) (syn_clec) (syn_cnc (syn_cin D
            (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
              (syn_csn (syn_cuni (syn_cuni (.cv q))))))))
      p0025 p0052
  have p0056 :=
    @g_breq2d
      (syn_wa (syn_wa (syn_wa (.classMem (syn_cnc (syn_cin D
                  (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                    (syn_csn (syn_cuni (syn_cuni (.cv y))))))) K)
            (syn_wral z (syn_cpw1 (syn_cpw1 D)) (.imp (.classMem (syn_cnc (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                        (syn_csn (syn_cuni (syn_cuni (.cv z))))))) K) (syn_wbr (syn_cnc
                    (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                        (syn_csn (syn_cuni (syn_cuni (.cv y))))))) (syn_clec) (syn_cnc
                    (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                        (syn_csn (syn_cuni (syn_cuni (.cv z))))))))))) (.classMem (.cv k) K))
        (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classEq (.cv k) (syn_cnc
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (syn_cuni (syn_cuni (.cv q))))))))))
      (.cv k)
      (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
            (syn_csn (syn_cuni (syn_cuni (.cv q)))))))
      (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
            (syn_csn (syn_cuni (syn_cuni (.cv y)))))))
      (syn_clec) p0021
  have p0057 :=
    @g_biimprd
      (syn_wa (syn_wa (syn_wa (.classMem (syn_cnc (syn_cin D
                  (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                    (syn_csn (syn_cuni (syn_cuni (.cv y))))))) K)
            (syn_wral z (syn_cpw1 (syn_cpw1 D)) (.imp (.classMem (syn_cnc (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                        (syn_csn (syn_cuni (syn_cuni (.cv z))))))) K) (syn_wbr (syn_cnc
                    (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                        (syn_csn (syn_cuni (syn_cuni (.cv y))))))) (syn_clec) (syn_cnc
                    (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                        (syn_csn (syn_cuni (syn_cuni (.cv z))))))))))) (.classMem (.cv k) K))
        (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classEq (.cv k) (syn_cnc
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (syn_cuni (syn_cuni (.cv q))))))))))
      (syn_wbr (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
              (syn_csn (syn_cuni (syn_cuni (.cv y))))))) (syn_clec) (.cv k))
      (syn_wbr (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
              (syn_csn (syn_cuni (syn_cuni (.cv y))))))) (syn_clec) (syn_cnc (syn_cin D
            (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
              (syn_csn (syn_cuni (syn_cuni (.cv q))))))))
      p0056
  have p0058 :=
    @g_mpd
      (syn_wa (syn_wa (syn_wa (.classMem (syn_cnc (syn_cin D
                  (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                    (syn_csn (syn_cuni (syn_cuni (.cv y))))))) K)
            (syn_wral z (syn_cpw1 (syn_cpw1 D)) (.imp (.classMem (syn_cnc (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                        (syn_csn (syn_cuni (syn_cuni (.cv z))))))) K) (syn_wbr (syn_cnc
                    (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                        (syn_csn (syn_cuni (syn_cuni (.cv y))))))) (syn_clec) (syn_cnc
                    (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                        (syn_csn (syn_cuni (syn_cuni (.cv z))))))))))) (.classMem (.cv k) K))
        (syn_wa (.classMem (.cv q) (syn_cpw1 (syn_cpw1 D))) (.classEq (.cv k) (syn_cnc
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (syn_cuni (syn_cuni (.cv q))))))))))
      (syn_wbr (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
              (syn_csn (syn_cuni (syn_cuni (.cv y))))))) (syn_clec) (syn_cnc (syn_cin D
            (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
              (syn_csn (syn_cuni (syn_cuni (.cv q))))))))
      (syn_wbr (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
              (syn_csn (syn_cuni (syn_cuni (.cv y))))))) (syn_clec) (.cv k))
      p0053 p0057
  have p0059 :=
    @g_rexlimdvaa
      (syn_wa (syn_wa (.classMem (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (syn_cuni (syn_cuni (.cv y))))))) K)
          (syn_wral z (syn_cpw1 (syn_cpw1 D)) (.imp (.classMem (syn_cnc (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                      (syn_csn (syn_cuni (syn_cuni (.cv z))))))) K) (syn_wbr (syn_cnc (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                      (syn_csn (syn_cuni (syn_cuni (.cv y))))))) (syn_clec) (syn_cnc (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                      (syn_csn (syn_cuni (syn_cuni (.cv z))))))))))) (.classMem (.cv k) K))
      (.classEq (.cv k) (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
              (syn_csn (syn_cuni (syn_cuni (.cv q))))))))
      (syn_wbr (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
              (syn_csn (syn_cuni (syn_cuni (.cv y))))))) (syn_clec) (.cv k))
      q (syn_cpw1 (syn_cpw1 D)) dv_cache_0020 dv_cache_0021 p0058
  have p0060 :=
    @g_mpd
      (syn_wa (syn_wa (.classMem (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (syn_cuni (syn_cuni (.cv y))))))) K)
          (syn_wral z (syn_cpw1 (syn_cpw1 D)) (.imp (.classMem (syn_cnc (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                      (syn_csn (syn_cuni (syn_cuni (.cv z))))))) K) (syn_wbr (syn_cnc (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                      (syn_csn (syn_cuni (syn_cuni (.cv y))))))) (syn_clec) (syn_cnc (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                      (syn_csn (syn_cuni (syn_cuni (.cv z))))))))))) (.classMem (.cv k) K))
      (syn_wrex q (syn_cpw1 (syn_cpw1 D)) (.classEq (.cv k) (syn_cnc (syn_cin D
              (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (.cv q)))))))))
      (syn_wbr (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
              (syn_csn (syn_cuni (syn_cuni (.cv y))))))) (syn_clec) (.cv k))
      p0019 p0059
  have p0061 :=
    @g_ralrimiva
      (syn_wa (.classMem (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (.cv y))))))) K)
        (syn_wral z (syn_cpw1 (syn_cpw1 D)) (.imp (.classMem (syn_cnc (syn_cin D
                  (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                    (syn_csn (syn_cuni (syn_cuni (.cv z))))))) K) (syn_wbr (syn_cnc (syn_cin D
                  (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                    (syn_csn (syn_cuni (syn_cuni (.cv y))))))) (syn_clec) (syn_cnc (syn_cin D
                  (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                    (syn_csn (syn_cuni (syn_cuni (.cv z)))))))))))
      (syn_wbr (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
              (syn_csn (syn_cuni (syn_cuni (.cv y))))))) (syn_clec) (.cv k))
      k K dv_cache_0022 p0060
  have p0062 :=
    @g_jca
      (syn_wa (.classMem (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (.cv y))))))) K)
        (syn_wral z (syn_cpw1 (syn_cpw1 D)) (.imp (.classMem (syn_cnc (syn_cin D
                  (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                    (syn_csn (syn_cuni (syn_cuni (.cv z))))))) K) (syn_wbr (syn_cnc (syn_cin D
                  (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                    (syn_csn (syn_cuni (syn_cuni (.cv y))))))) (syn_clec) (syn_cnc (syn_cin D
                  (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                    (syn_csn (syn_cuni (syn_cuni (.cv z)))))))))))
      (.classMem (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
              (syn_csn (syn_cuni (syn_cuni (.cv y))))))) K)
      (syn_wral k K (syn_wbr (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (.cv y))))))) (syn_clec) (.cv k)))
      p0015 p0061
  have p0063 :=
    @g_reximi
      (syn_wa (.classMem (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (.cv y))))))) K)
        (syn_wral z (syn_cpw1 (syn_cpw1 D)) (.imp (.classMem (syn_cnc (syn_cin D
                  (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                    (syn_csn (syn_cuni (syn_cuni (.cv z))))))) K) (syn_wbr (syn_cnc (syn_cin D
                  (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                    (syn_csn (syn_cuni (syn_cuni (.cv y))))))) (syn_clec) (syn_cnc (syn_cin D
                  (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                    (syn_csn (syn_cuni (syn_cuni (.cv z)))))))))))
      (syn_wa (.classMem (syn_cnc (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (.cv y))))))) K) (syn_wral k K (syn_wbr (syn_cnc
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (syn_cuni (syn_cuni (.cv y))))))) (syn_clec) (.cv k))))
      y (syn_cpw1 (syn_cpw1 D)) p0062
  have p0064 :=
    @g_syl (syn_wne K (syn_c0))
      (syn_wrex y (syn_cpw1 (syn_cpw1 D)) (syn_wa (.classMem (syn_cnc (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (syn_cuni (syn_cuni (.cv y))))))) K)
          (syn_wral z (syn_cpw1 (syn_cpw1 D)) (.imp (.classMem (syn_cnc (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                      (syn_csn (syn_cuni (syn_cuni (.cv z))))))) K) (syn_wbr (syn_cnc (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                      (syn_csn (syn_cuni (syn_cuni (.cv y))))))) (syn_clec) (syn_cnc (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                      (syn_csn (syn_cuni (syn_cuni (.cv z))))))))))))
      (syn_wrex y (syn_cpw1 (syn_cpw1 D)) (syn_wa (.classMem (syn_cnc (syn_cin D
                (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                  (syn_csn (syn_cuni (syn_cuni (.cv y))))))) K) (syn_wral k K (syn_wbr (syn_cnc
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                    (syn_csn (syn_cuni (syn_cuni (.cv y))))))) (syn_clec) (.cv k)))))
      p0014 p0063
  exact p0064


end NFChoice.DirectNominalPrf.WPPReplay

end
