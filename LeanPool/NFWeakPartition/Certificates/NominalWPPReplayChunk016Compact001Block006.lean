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

/-- Checked nominal proof certificate identified upstream as `g_sifrndv`. -/
@[expose]
noncomputable def gSifrndv (D : Class) (R : Class) :
    Nominal.NPrf
      (.imp (synWbr R (synCwe) D) (synWbr (synCsi R) (synCfound) (synCpw1 D))) :=
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
  have dv_cache_0003 : u ∉ ((synCuni (.cv x))).fv :=
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
  have dv_cache_0004 : v ∉ ((synCuni (.cv x))).fv :=
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
  have dv_cache_0006 : v ∉ ((synCuni (.cv z))).fv :=
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
      ((Wff.imp (synWbr (synCuni (.cv z)) R (.cv u))
          (.classEq (synCuni (.cv z)) (.cv u)))).fv :=
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
      ((synWa (synWa (synWbr R (synCwe) D)
            (synWa (synWss (.cv x) (synCpw1 D)) (synWne (.cv x) (synC0))))
          (synWa (.classMem (.cv u) (synCuni (.cv x))) (synWral v (synCuni (.cv x))
              (.imp (synWbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u))))))).fv :=
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
  have dv_cache_0009 : z ∉ ((Wff.classEq (.cv y) (synCsn (.cv u)))).fv :=
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
  have dv_cache_0010 : y ∉ ((synCsn (.cv u))).fv :=
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
      ((synWral z (.cv x) (.imp (synWbr (.cv z) (synCsi R) (synCsn (.cv u)))
            (.classEq (.cv z) (synCsn (.cv u)))))).fv :=
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
      ((synWrex y (.cv x) (synWral z (.cv x) (.imp (synWbr (.cv z) (synCsi R) (.cv y))
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
      ((synWa (synWbr R (synCwe) D)
          (synWa (synWss (.cv x) (synCpw1 D)) (synWne (.cv x) (synC0))))).fv :=
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
  have dv_cache_0015 : x ∉ ((synCpw1 D)).fv :=
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
  have dv_cache_0016 : z ∉ ((synCpw1 D)).fv :=
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
  have dv_cache_0017 : y ∉ ((synCpw1 D)).fv :=
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
  have dv_cache_0018 : x ∉ ((synCsi R)).fv :=
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
  have dv_cache_0019 : z ∉ ((synCsi R)).fv :=
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
  have dv_cache_0020 : y ∉ ((synCsi R)).fv :=
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
  have dv_cache_0021 : x ∉ ((synWbr R (synCwe) D)).fv :=
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
  have p0000 := @gBrex R D (synCwe)
  have p0001 :=
    @gSimpld (synWbr R (synCwe) D) (.classMem R (synCvv)) (.classMem D (synCvv))
      p0000
  have p0002 := @gSiexg R (synCvv)
  have p0003 :=
    @gSyl (synWbr R (synCwe) D) (.classMem R (synCvv))
      (.classMem (synCsi R) (synCvv)) p0001 p0002
  have p0005 :=
    @gSimprd (synWbr R (synCwe) D) (.classMem R (synCvv)) (.classMem D (synCvv))
      p0000
  have p0006 := @gPw1exg D (synCvv)
  have p0007 :=
    @gSyl (synWbr R (synCwe) D) (.classMem D (synCvv))
      (.classMem (synCpw1 D) (synCvv)) p0005 p0006
  have p0008 :=
    @gSimpl (synWbr R (synCwe) D)
      (synWa (synWss (.cv x) (synCpw1 D)) (synWne (.cv x) (synC0)))
  have p0009 := (Nominal.classEqRefl (synCwe))
  have p0010 := @gBreqi R D (synCwe) (synCin (synCstrict) (synCfound)) p0009
  have p0011 := @gBrin R D (synCstrict) (synCfound)
  have p0012 :=
    @gBitri (synWbr R (synCwe) D) (synWbr R (synCin (synCstrict) (synCfound)) D)
      (synWa (synWbr R (synCstrict) D) (synWbr R (synCfound) D)) p0010 p0011
  have p0013 :=
    @gSimprbi (synWbr R (synCwe) D) (synWbr R (synCstrict) D)
      (synWbr R (synCfound) D) p0012
  have p0014 :=
    @gSyl
      (synWa (synWbr R (synCwe) D)
        (synWa (synWss (.cv x) (synCpw1 D)) (synWne (.cv x) (synC0))))
      (synWbr R (synCwe) D) (synWbr R (synCfound) D) p0008 p0013
  have p0015 := @gVex x
  have p0016 := @gUniex (.cv x) p0015
  have p0017 :=
    @gA1i (.classMem (synCuni (.cv x)) (synCvv))
      (synWa (synWbr R (synCwe) D)
        (synWa (synWss (.cv x) (synCpw1 D)) (synWne (.cv x) (synC0))))
      p0016
  have p0018 :=
    @gSimpr (synWbr R (synCwe) D)
      (synWa (synWss (.cv x) (synCpw1 D)) (synWne (.cv x) (synC0)))
  have p0019 := @gSimpl (synWss (.cv x) (synCpw1 D)) (synWne (.cv x) (synC0))
  have p0020 :=
    @gSyl
      (synWa (synWbr R (synCwe) D)
        (synWa (synWss (.cv x) (synCpw1 D)) (synWne (.cv x) (synC0))))
      (synWa (synWss (.cv x) (synCpw1 D)) (synWne (.cv x) (synC0)))
      (synWss (.cv x) (synCpw1 D)) p0018 p0019
  have p0021 := @gPw1subuniss x D
  have p0022 :=
    @gSyl
      (synWa (synWbr R (synCwe) D)
        (synWa (synWss (.cv x) (synCpw1 D)) (synWne (.cv x) (synC0))))
      (synWss (.cv x) (synCpw1 D)) (synWss (synCuni (.cv x)) D) p0020 p0021
  have p0023 :=
    @gSimpr (synWbr R (synCwe) D)
      (synWa (synWss (.cv x) (synCpw1 D)) (synWne (.cv x) (synC0)))
  have p0024 := @gPw1subunine x D
  have p0025 :=
    @gSyl
      (synWa (synWbr R (synCwe) D)
        (synWa (synWss (.cv x) (synCpw1 D)) (synWne (.cv x) (synC0))))
      (synWa (synWss (.cv x) (synCpw1 D)) (synWne (.cv x) (synC0)))
      (synWne (synCuni (.cv x)) (synC0)) p0023 p0024
  have p0026 :=
    @gFrd
      (synWa (synWbr R (synCwe) D)
        (synWa (synWss (.cv x) (synCpw1 D)) (synWne (.cv x) (synC0))))
      u v D R (synCvv) (synCuni (.cv x)) dv_cache_0001 dv_cache_0002 dv_cache_0003
      dv_cache_0004 dv_cache_0005 p0014 p0017 p0022 p0025
  have p0027 :=
    @gSimpr
      (synWa (synWbr R (synCwe) D)
        (synWa (synWss (.cv x) (synCpw1 D)) (synWne (.cv x) (synC0))))
      (synWa (.classMem (.cv u) (synCuni (.cv x))) (synWral v (synCuni (.cv x))
          (.imp (synWbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u)))))
  have p0028 :=
    @gSimpl (.classMem (.cv u) (synCuni (.cv x)))
      (synWral v (synCuni (.cv x))
        (.imp (synWbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u))))
  have p0029 :=
    @gSyl
      (synWa (synWa (synWbr R (synCwe) D)
          (synWa (synWss (.cv x) (synCpw1 D)) (synWne (.cv x) (synC0))))
        (synWa (.classMem (.cv u) (synCuni (.cv x))) (synWral v (synCuni (.cv x))
            (.imp (synWbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u))))))
      (synWa (.classMem (.cv u) (synCuni (.cv x))) (synWral v (synCuni (.cv x))
          (.imp (synWbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u)))))
      (.classMem (.cv u) (synCuni (.cv x))) p0027 p0028
  have p0030 := @gSnelpw1 (.cv u) (synCuni (.cv x))
  have p0031 :=
    @gBiimpri (.classMem (synCsn (.cv u)) (synCpw1 (synCuni (.cv x))))
      (.classMem (.cv u) (synCuni (.cv x))) p0030
  have p0032 :=
    @gSyl
      (synWa (synWa (synWbr R (synCwe) D)
          (synWa (synWss (.cv x) (synCpw1 D)) (synWne (.cv x) (synC0))))
        (synWa (.classMem (.cv u) (synCuni (.cv x))) (synWral v (synCuni (.cv x))
            (.imp (synWbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u))))))
      (.classMem (.cv u) (synCuni (.cv x)))
      (.classMem (synCsn (.cv u)) (synCpw1 (synCuni (.cv x)))) p0029 p0031
  have p0033 :=
    @gSimpl
      (synWa (synWbr R (synCwe) D)
        (synWa (synWss (.cv x) (synCpw1 D)) (synWne (.cv x) (synC0))))
      (synWa (.classMem (.cv u) (synCuni (.cv x))) (synWral v (synCuni (.cv x))
          (.imp (synWbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u)))))
  have p0034 :=
    @gSimpr (synWbr R (synCwe) D)
      (synWa (synWss (.cv x) (synCpw1 D)) (synWne (.cv x) (synC0)))
  have p0035 := @gSimpl (synWss (.cv x) (synCpw1 D)) (synWne (.cv x) (synC0))
  have p0036 :=
    @gSyl
      (synWa (synWbr R (synCwe) D)
        (synWa (synWss (.cv x) (synCpw1 D)) (synWne (.cv x) (synC0))))
      (synWa (synWss (.cv x) (synCpw1 D)) (synWne (.cv x) (synC0)))
      (synWss (.cv x) (synCpw1 D)) p0034 p0035
  have p0037 := @gPw1ss1c D
  have p0038 :=
    @gA1i (synWss (synCpw1 D) (synC1c))
      (synWa (synWbr R (synCwe) D)
        (synWa (synWss (.cv x) (synCpw1 D)) (synWne (.cv x) (synC0))))
      p0037
  have p0039 :=
    @gSstrd
      (synWa (synWbr R (synCwe) D)
        (synWa (synWss (.cv x) (synCpw1 D)) (synWne (.cv x) (synC0))))
      (.cv x) (synCpw1 D) (synC1c) p0036 p0038
  have p0040 := @gEqpw1uni (.cv x)
  have p0041 :=
    @gSyl
      (synWa (synWbr R (synCwe) D)
        (synWa (synWss (.cv x) (synCpw1 D)) (synWne (.cv x) (synC0))))
      (synWss (.cv x) (synC1c)) (.classEq (.cv x) (synCpw1 (synCuni (.cv x)))) p0039
      p0040
  have p0042 :=
    @gSyl
      (synWa (synWa (synWbr R (synCwe) D)
          (synWa (synWss (.cv x) (synCpw1 D)) (synWne (.cv x) (synC0))))
        (synWa (.classMem (.cv u) (synCuni (.cv x))) (synWral v (synCuni (.cv x))
            (.imp (synWbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u))))))
      (synWa (synWbr R (synCwe) D)
        (synWa (synWss (.cv x) (synCpw1 D)) (synWne (.cv x) (synC0))))
      (.classEq (.cv x) (synCpw1 (synCuni (.cv x)))) p0033 p0041
  have p0043 :=
    @gEleqtrrd
      (synWa (synWa (synWbr R (synCwe) D)
          (synWa (synWss (.cv x) (synCpw1 D)) (synWne (.cv x) (synC0))))
        (synWa (.classMem (.cv u) (synCuni (.cv x))) (synWral v (synCuni (.cv x))
            (.imp (synWbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u))))))
      (synCsn (.cv u)) (synCpw1 (synCuni (.cv x))) (.cv x) p0032 p0042
  have p0044 :=
    @gSimpl
      (synWa (synWa (synWa (synWbr R (synCwe) D)
            (synWa (synWss (.cv x) (synCpw1 D)) (synWne (.cv x) (synC0))))
          (synWa (.classMem (.cv u) (synCuni (.cv x))) (synWral v (synCuni (.cv x))
              (.imp (synWbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u))))))
        (.classMem (.cv z) (.cv x)))
      (synWbr (.cv z) (synCsi R) (synCsn (.cv u)))
  have p0045 :=
    @gSimpr
      (synWa (synWa (synWbr R (synCwe) D)
          (synWa (synWss (.cv x) (synCpw1 D)) (synWne (.cv x) (synC0))))
        (synWa (.classMem (.cv u) (synCuni (.cv x))) (synWral v (synCuni (.cv x))
            (.imp (synWbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u))))))
      (.classMem (.cv z) (.cv x))
  have p0046 :=
    @gSimpl
      (synWa (synWa (synWbr R (synCwe) D)
          (synWa (synWss (.cv x) (synCpw1 D)) (synWne (.cv x) (synC0))))
        (synWa (.classMem (.cv u) (synCuni (.cv x))) (synWral v (synCuni (.cv x))
            (.imp (synWbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u))))))
      (.classMem (.cv z) (.cv x))
  have p0047 :=
    @gSimpl
      (synWa (synWbr R (synCwe) D)
        (synWa (synWss (.cv x) (synCpw1 D)) (synWne (.cv x) (synC0))))
      (synWa (.classMem (.cv u) (synCuni (.cv x))) (synWral v (synCuni (.cv x))
          (.imp (synWbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u)))))
  have p0048 :=
    @gSimpr (synWbr R (synCwe) D)
      (synWa (synWss (.cv x) (synCpw1 D)) (synWne (.cv x) (synC0)))
  have p0049 := @gSimpl (synWss (.cv x) (synCpw1 D)) (synWne (.cv x) (synC0))
  have p0050 :=
    @gSyl
      (synWa (synWbr R (synCwe) D)
        (synWa (synWss (.cv x) (synCpw1 D)) (synWne (.cv x) (synC0))))
      (synWa (synWss (.cv x) (synCpw1 D)) (synWne (.cv x) (synC0)))
      (synWss (.cv x) (synCpw1 D)) p0048 p0049
  have p0051 := @gPw1ss1c D
  have p0052 :=
    @gA1i (synWss (synCpw1 D) (synC1c))
      (synWa (synWbr R (synCwe) D)
        (synWa (synWss (.cv x) (synCpw1 D)) (synWne (.cv x) (synC0))))
      p0051
  have p0053 :=
    @gSstrd
      (synWa (synWbr R (synCwe) D)
        (synWa (synWss (.cv x) (synCpw1 D)) (synWne (.cv x) (synC0))))
      (.cv x) (synCpw1 D) (synC1c) p0050 p0052
  have p0054 := @gEqpw1uni (.cv x)
  have p0055 :=
    @gSyl
      (synWa (synWbr R (synCwe) D)
        (synWa (synWss (.cv x) (synCpw1 D)) (synWne (.cv x) (synC0))))
      (synWss (.cv x) (synC1c)) (.classEq (.cv x) (synCpw1 (synCuni (.cv x)))) p0053
      p0054
  have p0056 :=
    @gSyl
      (synWa (synWa (synWbr R (synCwe) D)
          (synWa (synWss (.cv x) (synCpw1 D)) (synWne (.cv x) (synC0))))
        (synWa (.classMem (.cv u) (synCuni (.cv x))) (synWral v (synCuni (.cv x))
            (.imp (synWbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u))))))
      (synWa (synWbr R (synCwe) D)
        (synWa (synWss (.cv x) (synCpw1 D)) (synWne (.cv x) (synC0))))
      (.classEq (.cv x) (synCpw1 (synCuni (.cv x)))) p0047 p0055
  have p0057 :=
    @gSyl
      (synWa (synWa (synWa (synWbr R (synCwe) D)
            (synWa (synWss (.cv x) (synCpw1 D)) (synWne (.cv x) (synC0))))
          (synWa (.classMem (.cv u) (synCuni (.cv x))) (synWral v (synCuni (.cv x))
              (.imp (synWbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u))))))
        (.classMem (.cv z) (.cv x)))
      (synWa (synWa (synWbr R (synCwe) D)
          (synWa (synWss (.cv x) (synCpw1 D)) (synWne (.cv x) (synC0))))
        (synWa (.classMem (.cv u) (synCuni (.cv x))) (synWral v (synCuni (.cv x))
            (.imp (synWbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u))))))
      (.classEq (.cv x) (synCpw1 (synCuni (.cv x)))) p0046 p0056
  have p0058 :=
    @gEleqtrd
      (synWa (synWa (synWa (synWbr R (synCwe) D)
            (synWa (synWss (.cv x) (synCpw1 D)) (synWne (.cv x) (synC0))))
          (synWa (.classMem (.cv u) (synCuni (.cv x))) (synWral v (synCuni (.cv x))
              (.imp (synWbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u))))))
        (.classMem (.cv z) (.cv x)))
      (.cv z) (.cv x) (synCpw1 (synCuni (.cv x))) p0045 p0057
  have p0059 := @gHnwpw1argcl (synCuni (.cv x)) z
  have p0060 :=
    @gSyl
      (synWa (synWa (synWa (synWbr R (synCwe) D)
            (synWa (synWss (.cv x) (synCpw1 D)) (synWne (.cv x) (synC0))))
          (synWa (.classMem (.cv u) (synCuni (.cv x))) (synWral v (synCuni (.cv x))
              (.imp (synWbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u))))))
        (.classMem (.cv z) (.cv x)))
      (.classMem (.cv z) (synCpw1 (synCuni (.cv x))))
      (synWa (.classMem (synCuni (.cv z)) (synCuni (.cv x)))
        (.classEq (.cv z) (synCsn (synCuni (.cv z)))))
      p0058 p0059
  have p0061 :=
    @gSimprd
      (synWa (synWa (synWa (synWbr R (synCwe) D)
            (synWa (synWss (.cv x) (synCpw1 D)) (synWne (.cv x) (synC0))))
          (synWa (.classMem (.cv u) (synCuni (.cv x))) (synWral v (synCuni (.cv x))
              (.imp (synWbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u))))))
        (.classMem (.cv z) (.cv x)))
      (.classMem (synCuni (.cv z)) (synCuni (.cv x)))
      (.classEq (.cv z) (synCsn (synCuni (.cv z)))) p0060
  have p0062 :=
    @gSyl
      (synWa (synWa (synWa (synWa (synWbr R (synCwe) D)
              (synWa (synWss (.cv x) (synCpw1 D)) (synWne (.cv x) (synC0))))
            (synWa (.classMem (.cv u) (synCuni (.cv x))) (synWral v (synCuni (.cv x))
                (.imp (synWbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u))))))
          (.classMem (.cv z) (.cv x))) (synWbr (.cv z) (synCsi R) (synCsn (.cv u))))
      (synWa (synWa (synWa (synWbr R (synCwe) D)
            (synWa (synWss (.cv x) (synCpw1 D)) (synWne (.cv x) (synC0))))
          (synWa (.classMem (.cv u) (synCuni (.cv x))) (synWral v (synCuni (.cv x))
              (.imp (synWbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u))))))
        (.classMem (.cv z) (.cv x)))
      (.classEq (.cv z) (synCsn (synCuni (.cv z)))) p0044 p0061
  have p0063 :=
    @gSimpr
      (synWa (synWa (synWa (synWbr R (synCwe) D)
            (synWa (synWss (.cv x) (synCpw1 D)) (synWne (.cv x) (synC0))))
          (synWa (.classMem (.cv u) (synCuni (.cv x))) (synWral v (synCuni (.cv x))
              (.imp (synWbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u))))))
        (.classMem (.cv z) (.cv x)))
      (synWbr (.cv z) (synCsi R) (synCsn (.cv u)))
  have p0064 :=
    @gSimpl
      (synWa (synWa (synWa (synWbr R (synCwe) D)
            (synWa (synWss (.cv x) (synCpw1 D)) (synWne (.cv x) (synC0))))
          (synWa (.classMem (.cv u) (synCuni (.cv x))) (synWral v (synCuni (.cv x))
              (.imp (synWbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u))))))
        (.classMem (.cv z) (.cv x)))
      (synWbr (.cv z) (synCsi R) (synCsn (.cv u)))
  have p0065 :=
    @gSimpr
      (synWa (synWa (synWbr R (synCwe) D)
          (synWa (synWss (.cv x) (synCpw1 D)) (synWne (.cv x) (synC0))))
        (synWa (.classMem (.cv u) (synCuni (.cv x))) (synWral v (synCuni (.cv x))
            (.imp (synWbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u))))))
      (.classMem (.cv z) (.cv x))
  have p0066 :=
    @gSimpl
      (synWa (synWa (synWbr R (synCwe) D)
          (synWa (synWss (.cv x) (synCpw1 D)) (synWne (.cv x) (synC0))))
        (synWa (.classMem (.cv u) (synCuni (.cv x))) (synWral v (synCuni (.cv x))
            (.imp (synWbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u))))))
      (.classMem (.cv z) (.cv x))
  have p0067 :=
    @gSimpl
      (synWa (synWbr R (synCwe) D)
        (synWa (synWss (.cv x) (synCpw1 D)) (synWne (.cv x) (synC0))))
      (synWa (.classMem (.cv u) (synCuni (.cv x))) (synWral v (synCuni (.cv x))
          (.imp (synWbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u)))))
  have p0068 :=
    @gSimpr (synWbr R (synCwe) D)
      (synWa (synWss (.cv x) (synCpw1 D)) (synWne (.cv x) (synC0)))
  have p0069 := @gSimpl (synWss (.cv x) (synCpw1 D)) (synWne (.cv x) (synC0))
  have p0070 :=
    @gSyl
      (synWa (synWbr R (synCwe) D)
        (synWa (synWss (.cv x) (synCpw1 D)) (synWne (.cv x) (synC0))))
      (synWa (synWss (.cv x) (synCpw1 D)) (synWne (.cv x) (synC0)))
      (synWss (.cv x) (synCpw1 D)) p0068 p0069
  have p0071 := @gPw1ss1c D
  have p0072 :=
    @gA1i (synWss (synCpw1 D) (synC1c))
      (synWa (synWbr R (synCwe) D)
        (synWa (synWss (.cv x) (synCpw1 D)) (synWne (.cv x) (synC0))))
      p0071
  have p0073 :=
    @gSstrd
      (synWa (synWbr R (synCwe) D)
        (synWa (synWss (.cv x) (synCpw1 D)) (synWne (.cv x) (synC0))))
      (.cv x) (synCpw1 D) (synC1c) p0070 p0072
  have p0074 := @gEqpw1uni (.cv x)
  have p0075 :=
    @gSyl
      (synWa (synWbr R (synCwe) D)
        (synWa (synWss (.cv x) (synCpw1 D)) (synWne (.cv x) (synC0))))
      (synWss (.cv x) (synC1c)) (.classEq (.cv x) (synCpw1 (synCuni (.cv x)))) p0073
      p0074
  have p0076 :=
    @gSyl
      (synWa (synWa (synWbr R (synCwe) D)
          (synWa (synWss (.cv x) (synCpw1 D)) (synWne (.cv x) (synC0))))
        (synWa (.classMem (.cv u) (synCuni (.cv x))) (synWral v (synCuni (.cv x))
            (.imp (synWbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u))))))
      (synWa (synWbr R (synCwe) D)
        (synWa (synWss (.cv x) (synCpw1 D)) (synWne (.cv x) (synC0))))
      (.classEq (.cv x) (synCpw1 (synCuni (.cv x)))) p0067 p0075
  have p0077 :=
    @gSyl
      (synWa (synWa (synWa (synWbr R (synCwe) D)
            (synWa (synWss (.cv x) (synCpw1 D)) (synWne (.cv x) (synC0))))
          (synWa (.classMem (.cv u) (synCuni (.cv x))) (synWral v (synCuni (.cv x))
              (.imp (synWbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u))))))
        (.classMem (.cv z) (.cv x)))
      (synWa (synWa (synWbr R (synCwe) D)
          (synWa (synWss (.cv x) (synCpw1 D)) (synWne (.cv x) (synC0))))
        (synWa (.classMem (.cv u) (synCuni (.cv x))) (synWral v (synCuni (.cv x))
            (.imp (synWbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u))))))
      (.classEq (.cv x) (synCpw1 (synCuni (.cv x)))) p0066 p0076
  have p0078 :=
    @gEleqtrd
      (synWa (synWa (synWa (synWbr R (synCwe) D)
            (synWa (synWss (.cv x) (synCpw1 D)) (synWne (.cv x) (synC0))))
          (synWa (.classMem (.cv u) (synCuni (.cv x))) (synWral v (synCuni (.cv x))
              (.imp (synWbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u))))))
        (.classMem (.cv z) (.cv x)))
      (.cv z) (.cv x) (synCpw1 (synCuni (.cv x))) p0065 p0077
  have p0079 := @gHnwpw1argcl (synCuni (.cv x)) z
  have p0080 :=
    @gSyl
      (synWa (synWa (synWa (synWbr R (synCwe) D)
            (synWa (synWss (.cv x) (synCpw1 D)) (synWne (.cv x) (synC0))))
          (synWa (.classMem (.cv u) (synCuni (.cv x))) (synWral v (synCuni (.cv x))
              (.imp (synWbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u))))))
        (.classMem (.cv z) (.cv x)))
      (.classMem (.cv z) (synCpw1 (synCuni (.cv x))))
      (synWa (.classMem (synCuni (.cv z)) (synCuni (.cv x)))
        (.classEq (.cv z) (synCsn (synCuni (.cv z)))))
      p0078 p0079
  have p0081 :=
    @gSimprd
      (synWa (synWa (synWa (synWbr R (synCwe) D)
            (synWa (synWss (.cv x) (synCpw1 D)) (synWne (.cv x) (synC0))))
          (synWa (.classMem (.cv u) (synCuni (.cv x))) (synWral v (synCuni (.cv x))
              (.imp (synWbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u))))))
        (.classMem (.cv z) (.cv x)))
      (.classMem (synCuni (.cv z)) (synCuni (.cv x)))
      (.classEq (.cv z) (synCsn (synCuni (.cv z)))) p0080
  have p0082 :=
    @gBreq1d
      (synWa (synWa (synWa (synWbr R (synCwe) D)
            (synWa (synWss (.cv x) (synCpw1 D)) (synWne (.cv x) (synC0))))
          (synWa (.classMem (.cv u) (synCuni (.cv x))) (synWral v (synCuni (.cv x))
              (.imp (synWbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u))))))
        (.classMem (.cv z) (.cv x)))
      (.cv z) (synCsn (synCuni (.cv z))) (synCsn (.cv u)) (synCsi R) p0081
  have p0083 := @gVex z
  have p0084 := @gUniex (.cv z) p0083
  have p0085 := @gVex u
  have p0086 := @gBrsnsi (synCuni (.cv z)) (.cv u) R p0084 p0085
  have p0087 :=
    @gA1i
      (synWb (synWbr (synCsn (synCuni (.cv z))) (synCsi R) (synCsn (.cv u)))
        (synWbr (synCuni (.cv z)) R (.cv u)))
      (synWa (synWa (synWa (synWbr R (synCwe) D)
            (synWa (synWss (.cv x) (synCpw1 D)) (synWne (.cv x) (synC0))))
          (synWa (.classMem (.cv u) (synCuni (.cv x))) (synWral v (synCuni (.cv x))
              (.imp (synWbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u))))))
        (.classMem (.cv z) (.cv x)))
      p0086
  have p0088 :=
    @gBitrd
      (synWa (synWa (synWa (synWbr R (synCwe) D)
            (synWa (synWss (.cv x) (synCpw1 D)) (synWne (.cv x) (synC0))))
          (synWa (.classMem (.cv u) (synCuni (.cv x))) (synWral v (synCuni (.cv x))
              (.imp (synWbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u))))))
        (.classMem (.cv z) (.cv x)))
      (synWbr (.cv z) (synCsi R) (synCsn (.cv u)))
      (synWbr (synCsn (synCuni (.cv z))) (synCsi R) (synCsn (.cv u)))
      (synWbr (synCuni (.cv z)) R (.cv u)) p0082 p0087
  have p0089 :=
    @gBiimpd
      (synWa (synWa (synWa (synWbr R (synCwe) D)
            (synWa (synWss (.cv x) (synCpw1 D)) (synWne (.cv x) (synC0))))
          (synWa (.classMem (.cv u) (synCuni (.cv x))) (synWral v (synCuni (.cv x))
              (.imp (synWbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u))))))
        (.classMem (.cv z) (.cv x)))
      (synWbr (.cv z) (synCsi R) (synCsn (.cv u)))
      (synWbr (synCuni (.cv z)) R (.cv u)) p0088
  have p0090 :=
    @gSyl
      (synWa (synWa (synWa (synWa (synWbr R (synCwe) D)
              (synWa (synWss (.cv x) (synCpw1 D)) (synWne (.cv x) (synC0))))
            (synWa (.classMem (.cv u) (synCuni (.cv x))) (synWral v (synCuni (.cv x))
                (.imp (synWbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u))))))
          (.classMem (.cv z) (.cv x))) (synWbr (.cv z) (synCsi R) (synCsn (.cv u))))
      (synWa (synWa (synWa (synWbr R (synCwe) D)
            (synWa (synWss (.cv x) (synCpw1 D)) (synWne (.cv x) (synC0))))
          (synWa (.classMem (.cv u) (synCuni (.cv x))) (synWral v (synCuni (.cv x))
              (.imp (synWbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u))))))
        (.classMem (.cv z) (.cv x)))
      (.imp (synWbr (.cv z) (synCsi R) (synCsn (.cv u)))
        (synWbr (synCuni (.cv z)) R (.cv u)))
      p0064 p0089
  have p0091 :=
    @gMpd
      (synWa (synWa (synWa (synWa (synWbr R (synCwe) D)
              (synWa (synWss (.cv x) (synCpw1 D)) (synWne (.cv x) (synC0))))
            (synWa (.classMem (.cv u) (synCuni (.cv x))) (synWral v (synCuni (.cv x))
                (.imp (synWbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u))))))
          (.classMem (.cv z) (.cv x))) (synWbr (.cv z) (synCsi R) (synCsn (.cv u))))
      (synWbr (.cv z) (synCsi R) (synCsn (.cv u)))
      (synWbr (synCuni (.cv z)) R (.cv u)) p0063 p0090
  have p0092 :=
    @gSimpl
      (synWa (synWa (synWa (synWbr R (synCwe) D)
            (synWa (synWss (.cv x) (synCpw1 D)) (synWne (.cv x) (synC0))))
          (synWa (.classMem (.cv u) (synCuni (.cv x))) (synWral v (synCuni (.cv x))
              (.imp (synWbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u))))))
        (.classMem (.cv z) (.cv x)))
      (synWbr (.cv z) (synCsi R) (synCsn (.cv u)))
  have p0093 :=
    @gSimpl
      (synWa (synWa (synWbr R (synCwe) D)
          (synWa (synWss (.cv x) (synCpw1 D)) (synWne (.cv x) (synC0))))
        (synWa (.classMem (.cv u) (synCuni (.cv x))) (synWral v (synCuni (.cv x))
            (.imp (synWbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u))))))
      (.classMem (.cv z) (.cv x))
  have p0094 :=
    @gSyl
      (synWa (synWa (synWa (synWa (synWbr R (synCwe) D)
              (synWa (synWss (.cv x) (synCpw1 D)) (synWne (.cv x) (synC0))))
            (synWa (.classMem (.cv u) (synCuni (.cv x))) (synWral v (synCuni (.cv x))
                (.imp (synWbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u))))))
          (.classMem (.cv z) (.cv x))) (synWbr (.cv z) (synCsi R) (synCsn (.cv u))))
      (synWa (synWa (synWa (synWbr R (synCwe) D)
            (synWa (synWss (.cv x) (synCpw1 D)) (synWne (.cv x) (synC0))))
          (synWa (.classMem (.cv u) (synCuni (.cv x))) (synWral v (synCuni (.cv x))
              (.imp (synWbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u))))))
        (.classMem (.cv z) (.cv x)))
      (synWa (synWa (synWbr R (synCwe) D)
          (synWa (synWss (.cv x) (synCpw1 D)) (synWne (.cv x) (synC0))))
        (synWa (.classMem (.cv u) (synCuni (.cv x))) (synWral v (synCuni (.cv x))
            (.imp (synWbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u))))))
      p0092 p0093
  have p0095 :=
    @gSimpr
      (synWa (synWbr R (synCwe) D)
        (synWa (synWss (.cv x) (synCpw1 D)) (synWne (.cv x) (synC0))))
      (synWa (.classMem (.cv u) (synCuni (.cv x))) (synWral v (synCuni (.cv x))
          (.imp (synWbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u)))))
  have p0096 :=
    @gSimpr (.classMem (.cv u) (synCuni (.cv x)))
      (synWral v (synCuni (.cv x))
        (.imp (synWbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u))))
  have p0097 :=
    @gSyl
      (synWa (synWa (synWbr R (synCwe) D)
          (synWa (synWss (.cv x) (synCpw1 D)) (synWne (.cv x) (synC0))))
        (synWa (.classMem (.cv u) (synCuni (.cv x))) (synWral v (synCuni (.cv x))
            (.imp (synWbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u))))))
      (synWa (.classMem (.cv u) (synCuni (.cv x))) (synWral v (synCuni (.cv x))
          (.imp (synWbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u)))))
      (synWral v (synCuni (.cv x))
        (.imp (synWbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u))))
      p0095 p0096
  have p0098 :=
    @gSyl
      (synWa (synWa (synWa (synWa (synWbr R (synCwe) D)
              (synWa (synWss (.cv x) (synCpw1 D)) (synWne (.cv x) (synC0))))
            (synWa (.classMem (.cv u) (synCuni (.cv x))) (synWral v (synCuni (.cv x))
                (.imp (synWbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u))))))
          (.classMem (.cv z) (.cv x))) (synWbr (.cv z) (synCsi R) (synCsn (.cv u))))
      (synWa (synWa (synWbr R (synCwe) D)
          (synWa (synWss (.cv x) (synCpw1 D)) (synWne (.cv x) (synC0))))
        (synWa (.classMem (.cv u) (synCuni (.cv x))) (synWral v (synCuni (.cv x))
            (.imp (synWbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u))))))
      (synWral v (synCuni (.cv x))
        (.imp (synWbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u))))
      p0094 p0097
  have p0099 :=
    @gSimpl
      (synWa (synWa (synWa (synWbr R (synCwe) D)
            (synWa (synWss (.cv x) (synCpw1 D)) (synWne (.cv x) (synC0))))
          (synWa (.classMem (.cv u) (synCuni (.cv x))) (synWral v (synCuni (.cv x))
              (.imp (synWbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u))))))
        (.classMem (.cv z) (.cv x)))
      (synWbr (.cv z) (synCsi R) (synCsn (.cv u)))
  have p0100 :=
    @gSimpr
      (synWa (synWa (synWbr R (synCwe) D)
          (synWa (synWss (.cv x) (synCpw1 D)) (synWne (.cv x) (synC0))))
        (synWa (.classMem (.cv u) (synCuni (.cv x))) (synWral v (synCuni (.cv x))
            (.imp (synWbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u))))))
      (.classMem (.cv z) (.cv x))
  have p0101 :=
    @gSimpl
      (synWa (synWa (synWbr R (synCwe) D)
          (synWa (synWss (.cv x) (synCpw1 D)) (synWne (.cv x) (synC0))))
        (synWa (.classMem (.cv u) (synCuni (.cv x))) (synWral v (synCuni (.cv x))
            (.imp (synWbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u))))))
      (.classMem (.cv z) (.cv x))
  have p0102 :=
    @gSimpl
      (synWa (synWbr R (synCwe) D)
        (synWa (synWss (.cv x) (synCpw1 D)) (synWne (.cv x) (synC0))))
      (synWa (.classMem (.cv u) (synCuni (.cv x))) (synWral v (synCuni (.cv x))
          (.imp (synWbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u)))))
  have p0103 :=
    @gSimpr (synWbr R (synCwe) D)
      (synWa (synWss (.cv x) (synCpw1 D)) (synWne (.cv x) (synC0)))
  have p0104 := @gSimpl (synWss (.cv x) (synCpw1 D)) (synWne (.cv x) (synC0))
  have p0105 :=
    @gSyl
      (synWa (synWbr R (synCwe) D)
        (synWa (synWss (.cv x) (synCpw1 D)) (synWne (.cv x) (synC0))))
      (synWa (synWss (.cv x) (synCpw1 D)) (synWne (.cv x) (synC0)))
      (synWss (.cv x) (synCpw1 D)) p0103 p0104
  have p0106 := @gPw1ss1c D
  have p0107 :=
    @gA1i (synWss (synCpw1 D) (synC1c))
      (synWa (synWbr R (synCwe) D)
        (synWa (synWss (.cv x) (synCpw1 D)) (synWne (.cv x) (synC0))))
      p0106
  have p0108 :=
    @gSstrd
      (synWa (synWbr R (synCwe) D)
        (synWa (synWss (.cv x) (synCpw1 D)) (synWne (.cv x) (synC0))))
      (.cv x) (synCpw1 D) (synC1c) p0105 p0107
  have p0109 := @gEqpw1uni (.cv x)
  have p0110 :=
    @gSyl
      (synWa (synWbr R (synCwe) D)
        (synWa (synWss (.cv x) (synCpw1 D)) (synWne (.cv x) (synC0))))
      (synWss (.cv x) (synC1c)) (.classEq (.cv x) (synCpw1 (synCuni (.cv x)))) p0108
      p0109
  have p0111 :=
    @gSyl
      (synWa (synWa (synWbr R (synCwe) D)
          (synWa (synWss (.cv x) (synCpw1 D)) (synWne (.cv x) (synC0))))
        (synWa (.classMem (.cv u) (synCuni (.cv x))) (synWral v (synCuni (.cv x))
            (.imp (synWbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u))))))
      (synWa (synWbr R (synCwe) D)
        (synWa (synWss (.cv x) (synCpw1 D)) (synWne (.cv x) (synC0))))
      (.classEq (.cv x) (synCpw1 (synCuni (.cv x)))) p0102 p0110
  have p0112 :=
    @gSyl
      (synWa (synWa (synWa (synWbr R (synCwe) D)
            (synWa (synWss (.cv x) (synCpw1 D)) (synWne (.cv x) (synC0))))
          (synWa (.classMem (.cv u) (synCuni (.cv x))) (synWral v (synCuni (.cv x))
              (.imp (synWbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u))))))
        (.classMem (.cv z) (.cv x)))
      (synWa (synWa (synWbr R (synCwe) D)
          (synWa (synWss (.cv x) (synCpw1 D)) (synWne (.cv x) (synC0))))
        (synWa (.classMem (.cv u) (synCuni (.cv x))) (synWral v (synCuni (.cv x))
            (.imp (synWbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u))))))
      (.classEq (.cv x) (synCpw1 (synCuni (.cv x)))) p0101 p0111
  have p0113 :=
    @gEleqtrd
      (synWa (synWa (synWa (synWbr R (synCwe) D)
            (synWa (synWss (.cv x) (synCpw1 D)) (synWne (.cv x) (synC0))))
          (synWa (.classMem (.cv u) (synCuni (.cv x))) (synWral v (synCuni (.cv x))
              (.imp (synWbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u))))))
        (.classMem (.cv z) (.cv x)))
      (.cv z) (.cv x) (synCpw1 (synCuni (.cv x))) p0100 p0112
  have p0114 := @gHnwpw1argcl (synCuni (.cv x)) z
  have p0115 :=
    @gSyl
      (synWa (synWa (synWa (synWbr R (synCwe) D)
            (synWa (synWss (.cv x) (synCpw1 D)) (synWne (.cv x) (synC0))))
          (synWa (.classMem (.cv u) (synCuni (.cv x))) (synWral v (synCuni (.cv x))
              (.imp (synWbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u))))))
        (.classMem (.cv z) (.cv x)))
      (.classMem (.cv z) (synCpw1 (synCuni (.cv x))))
      (synWa (.classMem (synCuni (.cv z)) (synCuni (.cv x)))
        (.classEq (.cv z) (synCsn (synCuni (.cv z)))))
      p0113 p0114
  have p0116 :=
    @gSimpld
      (synWa (synWa (synWa (synWbr R (synCwe) D)
            (synWa (synWss (.cv x) (synCpw1 D)) (synWne (.cv x) (synC0))))
          (synWa (.classMem (.cv u) (synCuni (.cv x))) (synWral v (synCuni (.cv x))
              (.imp (synWbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u))))))
        (.classMem (.cv z) (.cv x)))
      (.classMem (synCuni (.cv z)) (synCuni (.cv x)))
      (.classEq (.cv z) (synCsn (synCuni (.cv z)))) p0115
  have p0117 :=
    @gSyl
      (synWa (synWa (synWa (synWa (synWbr R (synCwe) D)
              (synWa (synWss (.cv x) (synCpw1 D)) (synWne (.cv x) (synC0))))
            (synWa (.classMem (.cv u) (synCuni (.cv x))) (synWral v (synCuni (.cv x))
                (.imp (synWbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u))))))
          (.classMem (.cv z) (.cv x))) (synWbr (.cv z) (synCsi R) (synCsn (.cv u))))
      (synWa (synWa (synWa (synWbr R (synCwe) D)
            (synWa (synWss (.cv x) (synCpw1 D)) (synWne (.cv x) (synC0))))
          (synWa (.classMem (.cv u) (synCuni (.cv x))) (synWral v (synCuni (.cv x))
              (.imp (synWbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u))))))
        (.classMem (.cv z) (.cv x)))
      (.classMem (synCuni (.cv z)) (synCuni (.cv x))) p0099 p0116
  have p0118 :=
    @gJca
      (synWa (synWa (synWa (synWa (synWbr R (synCwe) D)
              (synWa (synWss (.cv x) (synCpw1 D)) (synWne (.cv x) (synC0))))
            (synWa (.classMem (.cv u) (synCuni (.cv x))) (synWral v (synCuni (.cv x))
                (.imp (synWbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u))))))
          (.classMem (.cv z) (.cv x))) (synWbr (.cv z) (synCsi R) (synCsn (.cv u))))
      (synWral v (synCuni (.cv x))
        (.imp (synWbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u))))
      (.classMem (synCuni (.cv z)) (synCuni (.cv x))) p0098 p0117
  have p0119 := @gBreq1 (.cv v) (synCuni (.cv z)) (.cv u) R
  have p0120 := @gEqeq1 (.cv v) (synCuni (.cv z)) (.cv u)
  have p0121 :=
    @gImbi12d (.classEq (.cv v) (synCuni (.cv z))) (synWbr (.cv v) R (.cv u))
      (synWbr (synCuni (.cv z)) R (.cv u)) (.classEq (.cv v) (.cv u))
      (.classEq (synCuni (.cv z)) (.cv u)) p0119 p0120
  have p0122 :=
    @gRspccva (.imp (synWbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u)))
      (.imp (synWbr (synCuni (.cv z)) R (.cv u)) (.classEq (synCuni (.cv z)) (.cv u)))
      v (synCuni (.cv z)) (synCuni (.cv x)) dv_cache_0006 dv_cache_0004 dv_cache_0007
      p0121
  have p0123 :=
    @gSyl
      (synWa (synWa (synWa (synWa (synWbr R (synCwe) D)
              (synWa (synWss (.cv x) (synCpw1 D)) (synWne (.cv x) (synC0))))
            (synWa (.classMem (.cv u) (synCuni (.cv x))) (synWral v (synCuni (.cv x))
                (.imp (synWbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u))))))
          (.classMem (.cv z) (.cv x))) (synWbr (.cv z) (synCsi R) (synCsn (.cv u))))
      (synWa (synWral v (synCuni (.cv x))
          (.imp (synWbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u))))
        (.classMem (synCuni (.cv z)) (synCuni (.cv x))))
      (.imp (synWbr (synCuni (.cv z)) R (.cv u)) (.classEq (synCuni (.cv z)) (.cv u)))
      p0118 p0122
  have p0124 :=
    @gMpd
      (synWa (synWa (synWa (synWa (synWbr R (synCwe) D)
              (synWa (synWss (.cv x) (synCpw1 D)) (synWne (.cv x) (synC0))))
            (synWa (.classMem (.cv u) (synCuni (.cv x))) (synWral v (synCuni (.cv x))
                (.imp (synWbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u))))))
          (.classMem (.cv z) (.cv x))) (synWbr (.cv z) (synCsi R) (synCsn (.cv u))))
      (synWbr (synCuni (.cv z)) R (.cv u)) (.classEq (synCuni (.cv z)) (.cv u)) p0091
      p0123
  have p0125 :=
    @gSneqd
      (synWa (synWa (synWa (synWa (synWbr R (synCwe) D)
              (synWa (synWss (.cv x) (synCpw1 D)) (synWne (.cv x) (synC0))))
            (synWa (.classMem (.cv u) (synCuni (.cv x))) (synWral v (synCuni (.cv x))
                (.imp (synWbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u))))))
          (.classMem (.cv z) (.cv x))) (synWbr (.cv z) (synCsi R) (synCsn (.cv u))))
      (synCuni (.cv z)) (.cv u) p0124
  have p0126 :=
    @gEqtrd
      (synWa (synWa (synWa (synWa (synWbr R (synCwe) D)
              (synWa (synWss (.cv x) (synCpw1 D)) (synWne (.cv x) (synC0))))
            (synWa (.classMem (.cv u) (synCuni (.cv x))) (synWral v (synCuni (.cv x))
                (.imp (synWbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u))))))
          (.classMem (.cv z) (.cv x))) (synWbr (.cv z) (synCsi R) (synCsn (.cv u))))
      (.cv z) (synCsn (synCuni (.cv z))) (synCsn (.cv u)) p0062 p0125
  have p0127 :=
    @gEx
      (synWa (synWa (synWa (synWbr R (synCwe) D)
            (synWa (synWss (.cv x) (synCpw1 D)) (synWne (.cv x) (synC0))))
          (synWa (.classMem (.cv u) (synCuni (.cv x))) (synWral v (synCuni (.cv x))
              (.imp (synWbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u))))))
        (.classMem (.cv z) (.cv x)))
      (synWbr (.cv z) (synCsi R) (synCsn (.cv u))) (.classEq (.cv z) (synCsn (.cv u)))
      p0126
  have p0128 :=
    @gRalrimiva
      (synWa (synWa (synWbr R (synCwe) D)
          (synWa (synWss (.cv x) (synCpw1 D)) (synWne (.cv x) (synC0))))
        (synWa (.classMem (.cv u) (synCuni (.cv x))) (synWral v (synCuni (.cv x))
            (.imp (synWbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u))))))
      (.imp (synWbr (.cv z) (synCsi R) (synCsn (.cv u)))
        (.classEq (.cv z) (synCsn (.cv u))))
      z (.cv x) dv_cache_0008 p0127
  have p0129 :=
    @gJca
      (synWa (synWa (synWbr R (synCwe) D)
          (synWa (synWss (.cv x) (synCpw1 D)) (synWne (.cv x) (synC0))))
        (synWa (.classMem (.cv u) (synCuni (.cv x))) (synWral v (synCuni (.cv x))
            (.imp (synWbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u))))))
      (.classMem (synCsn (.cv u)) (.cv x))
      (synWral z (.cv x) (.imp (synWbr (.cv z) (synCsi R) (synCsn (.cv u)))
          (.classEq (.cv z) (synCsn (.cv u)))))
      p0043 p0128
  have p0130 := @gBreq2 (.cv y) (synCsn (.cv u)) (.cv z) (synCsi R)
  have p0131 := @gEqeq2 (.cv y) (synCsn (.cv u)) (.cv z)
  have p0132 :=
    @gImbi12d (.classEq (.cv y) (synCsn (.cv u))) (synWbr (.cv z) (synCsi R) (.cv y))
      (synWbr (.cv z) (synCsi R) (synCsn (.cv u))) (.classEq (.cv z) (.cv y))
      (.classEq (.cv z) (synCsn (.cv u))) p0130 p0131
  have p0133 :=
    @gRalbidv (.classEq (.cv y) (synCsn (.cv u)))
      (.imp (synWbr (.cv z) (synCsi R) (.cv y)) (.classEq (.cv z) (.cv y)))
      (.imp (synWbr (.cv z) (synCsi R) (synCsn (.cv u)))
        (.classEq (.cv z) (synCsn (.cv u))))
      z (.cv x) dv_cache_0009 p0132
  have p0134 :=
    @gRspcev
      (synWral z (.cv x)
        (.imp (synWbr (.cv z) (synCsi R) (.cv y)) (.classEq (.cv z) (.cv y))))
      (synWral z (.cv x) (.imp (synWbr (.cv z) (synCsi R) (synCsn (.cv u)))
          (.classEq (.cv z) (synCsn (.cv u)))))
      y (synCsn (.cv u)) (.cv x) dv_cache_0010 dv_cache_0011 dv_cache_0012 p0133
  have p0135 :=
    @gSyl
      (synWa (synWa (synWbr R (synCwe) D)
          (synWa (synWss (.cv x) (synCpw1 D)) (synWne (.cv x) (synC0))))
        (synWa (.classMem (.cv u) (synCuni (.cv x))) (synWral v (synCuni (.cv x))
            (.imp (synWbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u))))))
      (synWa (.classMem (synCsn (.cv u)) (.cv x)) (synWral z (.cv x)
          (.imp (synWbr (.cv z) (synCsi R) (synCsn (.cv u)))
            (.classEq (.cv z) (synCsn (.cv u))))))
      (synWrex y (.cv x) (synWral z (.cv x)
          (.imp (synWbr (.cv z) (synCsi R) (.cv y)) (.classEq (.cv z) (.cv y)))))
      p0129 p0134
  have p0136_e00_recanon :
    Nominal.NPrf
      (.imp (synWa (synWbr R (synCwe) D)
          (synWa (synWss (.cv x) (synCpw1 D)) (synWne (.cv x) (synC0))))
        (synWrex u (synCuni (.cv x)) (synWral v (synCuni (.cv x))
            (.imp (synWbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWa synWbr synCop synCun synCnin synWnan synCcompl synWrex
          synWex synCphi synCwe synCin synCstrict synCfound synCopab
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
    @gRexlimddv
      (synWa (synWbr R (synCwe) D)
        (synWa (synWss (.cv x) (synCpw1 D)) (synWne (.cv x) (synC0))))
      (synWral v (synCuni (.cv x))
        (.imp (synWbr (.cv v) R (.cv u)) (.classEq (.cv v) (.cv u))))
      (synWrex y (.cv x) (synWral z (.cv x)
          (.imp (synWbr (.cv z) (synCsi R) (.cv y)) (.classEq (.cv z) (.cv y)))))
      u (synCuni (.cv x)) dv_cache_0013 dv_cache_0014 p0136_e00_recanon p0135
  have p0137_e02_recanon :
    Nominal.NPrf
      (.imp (synWa (synWbr R (synCwe) D)
          (synWa (synWss (.cv x) (synCpw1 D)) (synWne (.cv x) (synC0))))
        (synWrex y (.cv x) (synWral z (.cv x)
            (.imp (synWbr (.cv z) (synCsi R) (.cv y)) (.objEq z y))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWa synWbr synCop synCun synCnin synWnan synCcompl synWrex
          synWex synCphi synCwe synCin synCstrict synCfound synCopab
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
    @gFrrd (synWbr R (synCwe) D) x z y (synCpw1 D) (synCsi R) dv_cache_0015
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

/-- Checked nominal proof certificate identified upstream as `g_siwendv`. -/
@[expose]
noncomputable def gSiwendv (D : Class) (R : Class) :
    Nominal.NPrf
      (.imp (synWbr R (synCwe) D) (synWbr (synCsi R) (synCwe) (synCpw1 D))) :=
  by
  have p0000 := @gSiorndv D R
  have p0001 := @gSifrndv D R
  have p0002 :=
    @gJca (synWbr R (synCwe) D) (synWbr (synCsi R) (synCstrict) (synCpw1 D))
      (synWbr (synCsi R) (synCfound) (synCpw1 D)) p0000 p0001
  have p0003 := (Nominal.classEqRefl (synCwe))
  have p0004 :=
    @gBreqi (synCsi R) (synCpw1 D) (synCwe) (synCin (synCstrict) (synCfound)) p0003
  have p0005 := @gBrin (synCsi R) (synCpw1 D) (synCstrict) (synCfound)
  have p0006 :=
    @gBitri (synWbr (synCsi R) (synCwe) (synCpw1 D))
      (synWbr (synCsi R) (synCin (synCstrict) (synCfound)) (synCpw1 D))
      (synWa (synWbr (synCsi R) (synCstrict) (synCpw1 D))
        (synWbr (synCsi R) (synCfound) (synCpw1 D)))
      p0004 p0005
  have p0007 :=
    @gBiimpri (synWbr (synCsi R) (synCwe) (synCpw1 D))
      (synWa (synWbr (synCsi R) (synCstrict) (synCpw1 D))
        (synWbr (synCsi R) (synCfound) (synCpw1 D)))
      p0006
  have p0008 :=
    @gSyl (synWbr R (synCwe) D)
      (synWa (synWbr (synCsi R) (synCstrict) (synCpw1 D))
        (synWbr (synCsi R) (synCfound) (synCpw1 D)))
      (synWbr (synCsi R) (synCwe) (synCpw1 D)) p0002 p0007
  exact p0008

/-- Checked nominal proof certificate identified upstream as `g_wecutcardtypedleastndv`. -/
@[expose]
noncomputable def gWecutcardtypedleastndv (y : Var) (z : Var) (D : Class) (R : Class)
    (K : Class) (q : Var) (dv_D_q : q ∉ D.fv) (dv_D_y : y ∉ D.fv) (dv_D_z : z ∉ D.fv)
    (dv_K_q : q ∉ K.fv) (dv_K_y : y ∉ K.fv) (dv_K_z : z ∉ K.fv) (dv_R_q : q ∉ R.fv)
    (dv_R_y : y ∉ R.fv) (dv_R_z : z ∉ R.fv) (dv_q_y : q ≠ y) (dv_q_z : q ≠ z)
    (dv_y_z : y ≠ z) (hyp_wecutcardtypedleastndv_1 : Nominal.NPrf (synWbr R (synCwe) D))
    (hyp_wecutcardtypedleastndv_2 : Nominal.NPrf (.classMem K (synCvv))) :
    Nominal.NPrf
      (.imp (synWrex q (synCpw1 (synCpw1 D)) (.classMem (synCnc (synCin D
                (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (synCuni (synCuni (.cv q))))))) K))
        (synWrex y (synCpw1 (synCpw1 D)) (synWa (.classMem (synCnc (synCin D
                  (synCima (synCcnv (synCdif R (synCid)))
                    (synCsn (synCuni (synCuni (.cv y))))))) K)
            (synWral z (synCpw1 (synCpw1 D)) (.imp (.classMem (synCnc (synCin D
                      (synCima (synCcnv (synCdif R (synCid)))
                        (synCsn (synCuni (synCuni (.cv z))))))) K)
                (synWbr (.cv y) (synCsi (synCsi R)) (.cv z))))))) :=
  by
  have dv_cache_0001 : q ∉ ((synCima (synCcnv (synCwecutcardfn R D)) K)).fv := by
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
  have dv_cache_0004 : q ∉ ((synCpw1 (synCpw1 D))).fv :=
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
  have dv_cache_0005 : y ∉ ((synCpw1 (synCpw1 D))).fv :=
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
  have dv_cache_0006 : z ∉ ((synCpw1 (synCpw1 D))).fv :=
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
  have dv_cache_0007 : y ∉ ((synCsi (synCsi R))).fv :=
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
  have dv_cache_0008 : z ∉ ((synCsi (synCsi R))).fv :=
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
    q ∉ ((Wff.classMem (.cv y) (synCima (synCcnv (synCwecutcardfn R D)) K))).fv :=
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
      ((synWrex q (synCpw1 (synCpw1 D)) (.classMem (synCnc (synCin D
                (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (synCuni (synCuni (.cv q))))))) K))).fv :=
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
      ((synWrex q (synCpw1 (synCpw1 D)) (.classMem (synCnc (synCin D
                (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (synCuni (synCuni (.cv q))))))) K))).fv :=
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
    y ∉ ((Wff.classMem (.cv q) (synCima (synCcnv (synCwecutcardfn R D)) K))).fv :=
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
    z ∉ ((Wff.classMem (.cv q) (synCima (synCcnv (synCwecutcardfn R D)) K))).fv :=
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
    q ∉ ((Wff.classMem (.cv z) (synCima (synCcnv (synCwecutcardfn R D)) K))).fv :=
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
  have p0000 := @gAbid2 q (synCima (synCcnv (synCwecutcardfn R D)) K) dv_cache_0001
  have p0001 := @gWecutcardfnex D R hyp_wecutcardtypedleastndv_1
  have p0002 := @gCnvex (synCwecutcardfn R D) p0001
  have p0003 :=
    @gImaex (synCcnv (synCwecutcardfn R D)) K p0002 hyp_wecutcardtypedleastndv_2
  have p0004 :=
    @gEqeltri (.cab q (.classMem (.cv q) (synCima (synCcnv (synCwecutcardfn R D)) K)))
      (synCima (synCcnv (synCwecutcardfn R D)) K) (synCvv) p0000 p0003
  have p0005 := @gEleq1 (.cv q) (.cv y) (synCima (synCcnv (synCwecutcardfn R D)) K)
  have p0006 := @gEleq1 (.cv q) (.cv z) (synCima (synCcnv (synCwecutcardfn R D)) K)
  have p0007 := @gSiwendv D R
  have p0008 := Nominal.mp hyp_wecutcardtypedleastndv_1 p0007
  have p0009 := @gSiwendv (synCpw1 D) (synCsi R)
  have p0010 := Nominal.mp p0008 p0009
  have p0011 :=
    @gA1i (synWbr (synCsi (synCsi R)) (synCwe) (synCpw1 (synCpw1 D)))
      (synWrex q (synCpw1 (synCpw1 D)) (.classMem (synCnc (synCin D
              (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (.cv q))))))) K))
      p0010
  have p0012 :=
    @gId
      (synWrex q (synCpw1 (synCpw1 D)) (.classMem (synCnc (synCin D
              (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (.cv q))))))) K))
  have p0013 := @gWecutcardpreimandv D R K q dv_cache_0002 dv_cache_0003
  have p0014 :=
    @gBiimprd (.classMem (.cv q) (synCpw1 (synCpw1 D)))
      (.classMem (.cv q) (synCima (synCcnv (synCwecutcardfn R D)) K))
      (.classMem (synCnc (synCin D (synCima (synCcnv (synCdif R (synCid)))
              (synCsn (synCuni (synCuni (.cv q))))))) K)
      p0013
  have p0015 :=
    @gReximia
      (.classMem (synCnc (synCin D (synCima (synCcnv (synCdif R (synCid)))
              (synCsn (synCuni (synCuni (.cv q))))))) K)
      (.classMem (.cv q) (synCima (synCcnv (synCwecutcardfn R D)) K)) q
      (synCpw1 (synCpw1 D)) p0014
  have p0016 :=
    @gSyl
      (synWrex q (synCpw1 (synCpw1 D)) (.classMem (synCnc (synCin D
              (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (.cv q))))))) K))
      (synWrex q (synCpw1 (synCpw1 D)) (.classMem (synCnc (synCin D
              (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (.cv q))))))) K))
      (synWrex q (synCpw1 (synCpw1 D))
        (.classMem (.cv q) (synCima (synCcnv (synCwecutcardfn R D)) K)))
      p0012 p0015
  have p0017_e01_recanon :
    Nominal.NPrf
      (.imp (.objEq q y)
        (synWb (.classMem (.cv q) (synCima (synCcnv (synCwecutcardfn R D)) K))
          (.classMem (.cv y) (synCima (synCcnv (synCwecutcardfn R D)) K)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCima synWrex synWex synWa synWbr synCop synCun synCnin
          synWnan synCcompl synCcnv synCopab synCwecutcardfn synCmpt synCpw1
          synCin synCpw synWss synC1c synCnc synCec synCen
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
        (synWb (.classMem (.cv q) (synCima (synCcnv (synCwecutcardfn R D)) K))
          (.classMem (.cv z) (synCima (synCcnv (synCwecutcardfn R D)) K)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCima synWrex synWex synWa synWbr synCop synCun synCnin
          synWnan synCcompl synCcnv synCopab synCwecutcardfn synCmpt synCpw1
          synCin synCpw synWss synC1c synCnc synCec synCen
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0006
  have p0017 :=
    @gWeds
      (synWrex q (synCpw1 (synCpw1 D)) (.classMem (synCnc (synCin D
              (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (.cv q))))))) K))
      (.classMem (.cv q) (synCima (synCcnv (synCwecutcardfn R D)) K))
      (.classMem (.cv y) (synCima (synCcnv (synCwecutcardfn R D)) K))
      (.classMem (.cv z) (synCima (synCcnv (synCwecutcardfn R D)) K)) q y z
      (synCpw1 (synCpw1 D)) (synCsi (synCsi R)) dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      p0004 p0017_e01_recanon p0017_e02_recanon p0011 p0016
  have p0018 := @gWecutcardpreimandv D R K y dv_cache_0018 dv_cache_0019
  have p0019 := @gWecutcardpreimandv D R K z dv_cache_0020 dv_cache_0021
  have p0020 :=
    @gImbi1d (.classMem (.cv z) (synCpw1 (synCpw1 D)))
      (.classMem (.cv z) (synCima (synCcnv (synCwecutcardfn R D)) K))
      (.classMem (synCnc (synCin D (synCima (synCcnv (synCdif R (synCid)))
              (synCsn (synCuni (synCuni (.cv z))))))) K)
      (synWbr (.cv y) (synCsi (synCsi R)) (.cv z)) p0019
  have p0021 :=
    @gRalbiia
      (.imp (.classMem (.cv z) (synCima (synCcnv (synCwecutcardfn R D)) K))
        (synWbr (.cv y) (synCsi (synCsi R)) (.cv z)))
      (.imp (.classMem (synCnc (synCin D (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (.cv z))))))) K)
        (synWbr (.cv y) (synCsi (synCsi R)) (.cv z)))
      z (synCpw1 (synCpw1 D)) p0020
  have p0022 :=
    @gA1i
      (synWb (synWral z (synCpw1 (synCpw1 D))
          (.imp (.classMem (.cv z) (synCima (synCcnv (synCwecutcardfn R D)) K))
            (synWbr (.cv y) (synCsi (synCsi R)) (.cv z))))
        (synWral z (synCpw1 (synCpw1 D)) (.imp (.classMem (synCnc (synCin D
                  (synCima (synCcnv (synCdif R (synCid)))
                    (synCsn (synCuni (synCuni (.cv z))))))) K)
            (synWbr (.cv y) (synCsi (synCsi R)) (.cv z)))))
      (.classMem (.cv y) (synCpw1 (synCpw1 D))) p0021
  have p0023 :=
    @gAnbi12d (.classMem (.cv y) (synCpw1 (synCpw1 D)))
      (.classMem (.cv y) (synCima (synCcnv (synCwecutcardfn R D)) K))
      (.classMem (synCnc (synCin D (synCima (synCcnv (synCdif R (synCid)))
              (synCsn (synCuni (synCuni (.cv y))))))) K)
      (synWral z (synCpw1 (synCpw1 D))
        (.imp (.classMem (.cv z) (synCima (synCcnv (synCwecutcardfn R D)) K))
          (synWbr (.cv y) (synCsi (synCsi R)) (.cv z))))
      (synWral z (synCpw1 (synCpw1 D)) (.imp (.classMem (synCnc (synCin D
                (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (synCuni (synCuni (.cv z))))))) K)
          (synWbr (.cv y) (synCsi (synCsi R)) (.cv z))))
      p0018 p0022
  have p0024 :=
    @gBiimpd (.classMem (.cv y) (synCpw1 (synCpw1 D)))
      (synWa (.classMem (.cv y) (synCima (synCcnv (synCwecutcardfn R D)) K))
        (synWral z (synCpw1 (synCpw1 D))
          (.imp (.classMem (.cv z) (synCima (synCcnv (synCwecutcardfn R D)) K))
            (synWbr (.cv y) (synCsi (synCsi R)) (.cv z)))))
      (synWa (.classMem (synCnc (synCin D (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (.cv y))))))) K)
        (synWral z (synCpw1 (synCpw1 D)) (.imp (.classMem (synCnc (synCin D
                  (synCima (synCcnv (synCdif R (synCid)))
                    (synCsn (synCuni (synCuni (.cv z))))))) K)
            (synWbr (.cv y) (synCsi (synCsi R)) (.cv z)))))
      p0023
  have p0025 :=
    @gReximia
      (synWa (.classMem (.cv y) (synCima (synCcnv (synCwecutcardfn R D)) K))
        (synWral z (synCpw1 (synCpw1 D))
          (.imp (.classMem (.cv z) (synCima (synCcnv (synCwecutcardfn R D)) K))
            (synWbr (.cv y) (synCsi (synCsi R)) (.cv z)))))
      (synWa (.classMem (synCnc (synCin D (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (.cv y))))))) K)
        (synWral z (synCpw1 (synCpw1 D)) (.imp (.classMem (synCnc (synCin D
                  (synCima (synCcnv (synCdif R (synCid)))
                    (synCsn (synCuni (synCuni (.cv z))))))) K)
            (synWbr (.cv y) (synCsi (synCsi R)) (.cv z)))))
      y (synCpw1 (synCpw1 D)) p0024
  have p0026 :=
    @gSyl
      (synWrex q (synCpw1 (synCpw1 D)) (.classMem (synCnc (synCin D
              (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (.cv q))))))) K))
      (synWrex y (synCpw1 (synCpw1 D))
        (synWa (.classMem (.cv y) (synCima (synCcnv (synCwecutcardfn R D)) K))
          (synWral z (synCpw1 (synCpw1 D))
            (.imp (.classMem (.cv z) (synCima (synCcnv (synCwecutcardfn R D)) K))
              (synWbr (.cv y) (synCsi (synCsi R)) (.cv z))))))
      (synWrex y (synCpw1 (synCpw1 D)) (synWa (.classMem (synCnc (synCin D
                (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (synCuni (synCuni (.cv y))))))) K)
          (synWral z (synCpw1 (synCpw1 D)) (.imp (.classMem (synCnc (synCin D
                    (synCima (synCcnv (synCdif R (synCid)))
                      (synCsn (synCuni (synCuni (.cv z))))))) K)
              (synWbr (.cv y) (synCsi (synCsi R)) (.cv z))))))
      p0017 p0025
  exact p0026

/-- Checked nominal proof certificate identified upstream as `g_wecutssndv`. -/
@[expose]
noncomputable def gWecutssndv (x : Var) (y : Var) (D : Class) (R : Class)
    (_dv_D_x : x ∉ D.fv) (_dv_D_y : y ∉ D.fv) (_dv_R_x : x ∉ R.fv) (_dv_R_y : y ∉ R.fv)
    (_dv_x_y : x ≠ y) (hyp_wecutssndv_1 : Nominal.NPrf (synWbr R (synCwe) D)) :
    Nominal.NPrf
      (.imp (synW3a (.classMem (.cv x) D) (.classMem (.cv y) D) (synWbr (.cv x) R (.cv y)))
        (synWss (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))) :=
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
    z ∉ ((synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))).fv :=
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
    z ∉ ((synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))).fv :=
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
      ((synW3a (.classMem (.cv x) D) (.classMem (.cv y) D) (synWbr (.cv x) R (.cv y)))).fv :=
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
    @gSimpr
      (synW3a (.classMem (.cv x) D) (.classMem (.cv y) D) (synWbr (.cv x) R (.cv y)))
      (.classMem (.cv z)
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
  have p0001 := @gId (.classEq (.cv x) (.cv y))
  have p0002 := @gSneqd (.classEq (.cv x) (.cv y)) (.cv x) (.cv y) p0001
  have p0003 :=
    @gImaeq2d (.classEq (.cv x) (.cv y)) (synCsn (.cv x)) (synCsn (.cv y))
      (synCcnv (synCdif R (synCid))) p0002
  have p0004 :=
    @gIneq2d (.classEq (.cv x) (.cv y))
      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))
      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))) D p0003
  have p0005 :=
    @gEleq2d (.classEq (.cv x) (.cv y))
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (.cv z)
      p0004
  have p0006 :=
    @gBiimpd (.classEq (.cv x) (.cv y))
      (.classMem (.cv z)
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      (.classMem (.cv z)
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
      p0005
  have p0007 :=
    @gCom12 (.classEq (.cv x) (.cv y))
      (.classMem (.cv z)
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      (.classMem (.cv z)
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
      p0006
  have p0008 :=
    @gSyl
      (synWa (synW3a (.classMem (.cv x) D) (.classMem (.cv y) D) (synWbr (.cv x) R (.cv y)))
        (.classMem (.cv z)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (.classMem (.cv z)
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      (.imp (.classEq (.cv x) (.cv y)) (.classMem (.cv z)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      p0000 p0007
  have p0009 :=
    @gA1i (synWbr R (synCwe) D)
      (synWa (synWa (synW3a (.classMem (.cv x) D) (.classMem (.cv y) D)
            (synWbr (.cv x) R (.cv y))) (.classMem (.cv z)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (.neg (.classEq (.cv x) (.cv y))))
      hyp_wecutssndv_1
  have p0010 :=
    @gSimpl
      (synWa (synW3a (.classMem (.cv x) D) (.classMem (.cv y) D) (synWbr (.cv x) R (.cv y)))
        (.classMem (.cv z)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (.neg (.classEq (.cv x) (.cv y)))
  have p0011 :=
    @gSimpl
      (synW3a (.classMem (.cv x) D) (.classMem (.cv y) D) (synWbr (.cv x) R (.cv y)))
      (.classMem (.cv z)
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
  have p0012 :=
    @gSyl
      (synWa (synWa (synW3a (.classMem (.cv x) D) (.classMem (.cv y) D)
            (synWbr (.cv x) R (.cv y))) (.classMem (.cv z)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (.neg (.classEq (.cv x) (.cv y))))
      (synWa (synW3a (.classMem (.cv x) D) (.classMem (.cv y) D) (synWbr (.cv x) R (.cv y)))
        (.classMem (.cv z)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (synW3a (.classMem (.cv x) D) (.classMem (.cv y) D) (synWbr (.cv x) R (.cv y)))
      p0010 p0011
  have p0013 :=
    @gSimp2 (.classMem (.cv x) D) (.classMem (.cv y) D) (synWbr (.cv x) R (.cv y))
  have p0014 :=
    @gSyl
      (synWa (synWa (synW3a (.classMem (.cv x) D) (.classMem (.cv y) D)
            (synWbr (.cv x) R (.cv y))) (.classMem (.cv z)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (.neg (.classEq (.cv x) (.cv y))))
      (synW3a (.classMem (.cv x) D) (.classMem (.cv y) D) (synWbr (.cv x) R (.cv y)))
      (.classMem (.cv y) D) p0012 p0013
  have p0015 :=
    @gJca
      (synWa (synWa (synW3a (.classMem (.cv x) D) (.classMem (.cv y) D)
            (synWbr (.cv x) R (.cv y))) (.classMem (.cv z)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (.neg (.classEq (.cv x) (.cv y))))
      (synWbr R (synCwe) D) (.classMem (.cv y) D) p0009 p0014
  have p0019 :=
    @gSimp1 (.classMem (.cv x) D) (.classMem (.cv y) D) (synWbr (.cv x) R (.cv y))
  have p0020 :=
    @gSyl
      (synWa (synWa (synW3a (.classMem (.cv x) D) (.classMem (.cv y) D)
            (synWbr (.cv x) R (.cv y))) (.classMem (.cv z)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (.neg (.classEq (.cv x) (.cv y))))
      (synW3a (.classMem (.cv x) D) (.classMem (.cv y) D) (synWbr (.cv x) R (.cv y)))
      (.classMem (.cv x) D) p0012 p0019
  have p0024 :=
    @gSimp3 (.classMem (.cv x) D) (.classMem (.cv y) D) (synWbr (.cv x) R (.cv y))
  have p0025 :=
    @gSyl
      (synWa (synWa (synW3a (.classMem (.cv x) D) (.classMem (.cv y) D)
            (synWbr (.cv x) R (.cv y))) (.classMem (.cv z)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (.neg (.classEq (.cv x) (.cv y))))
      (synW3a (.classMem (.cv x) D) (.classMem (.cv y) D) (synWbr (.cv x) R (.cv y)))
      (synWbr (.cv x) R (.cv y)) p0012 p0024
  have p0026 :=
    @gSimpr
      (synWa (synW3a (.classMem (.cv x) D) (.classMem (.cv y) D) (synWbr (.cv x) R (.cv y)))
        (.classMem (.cv z)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (.neg (.classEq (.cv x) (.cv y)))
  have p0027 := (Nominal.biimpRefl (synWne (.cv x) (.cv y)))
  have p0028 :=
    @gBiimpri (synWne (.cv x) (.cv y)) (.neg (.classEq (.cv x) (.cv y))) p0027
  have p0029 :=
    @gSyl
      (synWa (synWa (synW3a (.classMem (.cv x) D) (.classMem (.cv y) D)
            (synWbr (.cv x) R (.cv y))) (.classMem (.cv z)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (.neg (.classEq (.cv x) (.cv y))))
      (.neg (.classEq (.cv x) (.cv y))) (synWne (.cv x) (.cv y)) p0026 p0028
  have p0030 :=
    @gJca
      (synWa (synWa (synW3a (.classMem (.cv x) D) (.classMem (.cv y) D)
            (synWbr (.cv x) R (.cv y))) (.classMem (.cv z)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (.neg (.classEq (.cv x) (.cv y))))
      (synWbr (.cv x) R (.cv y)) (synWne (.cv x) (.cv y)) p0025 p0029
  have p0031 :=
    @gJca
      (synWa (synWa (synW3a (.classMem (.cv x) D) (.classMem (.cv y) D)
            (synWbr (.cv x) R (.cv y))) (.classMem (.cv z)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (.neg (.classEq (.cv x) (.cv y))))
      (.classMem (.cv x) D) (synWa (synWbr (.cv x) R (.cv y)) (synWne (.cv x) (.cv y)))
      p0020 p0030
  have p0032 := @gElstrictseg y x D R
  have p0033 :=
    @gBiimpri
      (.classMem (.cv x)
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
      (synWa (.classMem (.cv x) D)
        (synWa (synWbr (.cv x) R (.cv y)) (synWne (.cv x) (.cv y))))
      p0032
  have p0034 :=
    @gSyl
      (synWa (synWa (synW3a (.classMem (.cv x) D) (.classMem (.cv y) D)
            (synWbr (.cv x) R (.cv y))) (.classMem (.cv z)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (.neg (.classEq (.cv x) (.cv y))))
      (synWa (.classMem (.cv x) D)
        (synWa (synWbr (.cv x) R (.cv y)) (synWne (.cv x) (.cv y))))
      (.classMem (.cv x)
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
      p0031 p0033
  have p0037 :=
    @gSyl
      (synWa (synWa (synW3a (.classMem (.cv x) D) (.classMem (.cv y) D)
            (synWbr (.cv x) R (.cv y))) (.classMem (.cv z)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (.neg (.classEq (.cv x) (.cv y))))
      (synWa (synW3a (.classMem (.cv x) D) (.classMem (.cv y) D) (synWbr (.cv x) R (.cv y)))
        (.classMem (.cv z)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (.classMem (.cv z)
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      p0010 p0000
  have p0038 := @gElstrictseg x z D R
  have p0039 :=
    @gBiimpi
      (.classMem (.cv z)
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      (synWa (.classMem (.cv z) D)
        (synWa (synWbr (.cv z) R (.cv x)) (synWne (.cv z) (.cv x))))
      p0038
  have p0040 :=
    @gSyl
      (synWa (synWa (synW3a (.classMem (.cv x) D) (.classMem (.cv y) D)
            (synWbr (.cv x) R (.cv y))) (.classMem (.cv z)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (.neg (.classEq (.cv x) (.cv y))))
      (.classMem (.cv z)
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      (synWa (.classMem (.cv z) D)
        (synWa (synWbr (.cv z) R (.cv x)) (synWne (.cv z) (.cv x))))
      p0037 p0039
  have p0041 :=
    @gSimpld
      (synWa (synWa (synW3a (.classMem (.cv x) D) (.classMem (.cv y) D)
            (synWbr (.cv x) R (.cv y))) (.classMem (.cv z)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (.neg (.classEq (.cv x) (.cv y))))
      (.classMem (.cv z) D) (synWa (synWbr (.cv z) R (.cv x)) (synWne (.cv z) (.cv x)))
      p0040
  have p0042 :=
    @gJca
      (synWa (synWa (synW3a (.classMem (.cv x) D) (.classMem (.cv y) D)
            (synWbr (.cv x) R (.cv y))) (.classMem (.cv z)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (.neg (.classEq (.cv x) (.cv y))))
      (.classMem (.cv x)
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
      (.classMem (.cv z) D) p0034 p0041
  have p0049 :=
    @gSimprd
      (synWa (synWa (synW3a (.classMem (.cv x) D) (.classMem (.cv y) D)
            (synWbr (.cv x) R (.cv y))) (.classMem (.cv z)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (.neg (.classEq (.cv x) (.cv y))))
      (.classMem (.cv z) D) (synWa (synWbr (.cv z) R (.cv x)) (synWne (.cv z) (.cv x)))
      p0040
  have p0050 :=
    @gSimpld
      (synWa (synWa (synW3a (.classMem (.cv x) D) (.classMem (.cv y) D)
            (synWbr (.cv x) R (.cv y))) (.classMem (.cv z)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (.neg (.classEq (.cv x) (.cv y))))
      (synWbr (.cv z) R (.cv x)) (synWne (.cv z) (.cv x)) p0049
  have p0051 :=
    @gN3jca
      (synWa (synWa (synW3a (.classMem (.cv x) D) (.classMem (.cv y) D)
            (synWbr (.cv x) R (.cv y))) (.classMem (.cv z)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (.neg (.classEq (.cv x) (.cv y))))
      (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D))
      (synWa (.classMem (.cv x)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
        (.classMem (.cv z) D))
      (synWbr (.cv z) R (.cv x)) p0015 p0042 p0050
  have p0052 := @gStrictsegdown y x z D R
  have p0053 :=
    @gSyl
      (synWa (synWa (synW3a (.classMem (.cv x) D) (.classMem (.cv y) D)
            (synWbr (.cv x) R (.cv y))) (.classMem (.cv z)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (.neg (.classEq (.cv x) (.cv y))))
      (synW3a (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (synWa (.classMem (.cv x)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
          (.classMem (.cv z) D)) (synWbr (.cv z) R (.cv x)))
      (.classMem (.cv z)
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
      p0051 p0052
  have p0054 :=
    @gEx
      (synWa (synW3a (.classMem (.cv x) D) (.classMem (.cv y) D) (synWbr (.cv x) R (.cv y)))
        (.classMem (.cv z)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (.neg (.classEq (.cv x) (.cv y)))
      (.classMem (.cv z)
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
      p0053
  have p0055 :=
    @gPm261d
      (synWa (synW3a (.classMem (.cv x) D) (.classMem (.cv y) D) (synWbr (.cv x) R (.cv y)))
        (.classMem (.cv z)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (.classEq (.cv x) (.cv y))
      (.classMem (.cv z)
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
      p0008 p0054
  have p0056 :=
    @gEx
      (synW3a (.classMem (.cv x) D) (.classMem (.cv y) D) (synWbr (.cv x) R (.cv y)))
      (.classMem (.cv z)
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      (.classMem (.cv z)
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
      p0055
  have p0057 :=
    @gSsrdv
      (synW3a (.classMem (.cv x) D) (.classMem (.cv y) D) (synWbr (.cv x) R (.cv y))) z
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
      dv_cache_0001 dv_cache_0002 dv_cache_0003 p0056
  exact p0057

/-- Checked nominal proof certificate identified upstream as `g_wecutnclecndv`. -/
@[expose]
noncomputable def gWecutnclecndv (x : Var) (y : Var) (D : Class) (R : Class)
    (dv_D_x : x ∉ D.fv) (dv_D_y : y ∉ D.fv) (dv_R_x : x ∉ R.fv) (dv_R_y : y ∉ R.fv)
    (dv_x_y : x ≠ y) (hyp_wecutnclecndv_1 : Nominal.NPrf (synWbr R (synCwe) D)) :
    Nominal.NPrf
      (.imp (synW3a (.classMem (.cv x) D) (.classMem (.cv y) D) (synWbr (.cv x) R (.cv y)))
        (synWbr (synCnc
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
          (synClec) (synCnc (synCin D
              (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))) :=
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
    @gWecutssndv x y D R dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 hyp_wecutnclecndv_1
  have p0001 := @gBrex R D (synCwe)
  have p0002 := Nominal.mp hyp_wecutnclecndv_1 p0001
  have p0003 := @gSimpri (.classMem R (synCvv)) (.classMem D (synCvv)) p0002
  have p0006 := @gSimpli (.classMem R (synCvv)) (.classMem D (synCvv)) p0002
  have p0007 := @gIdex
  have p0008 := @gDifex R (synCid) p0006 p0007
  have p0009 := @gCnvex (synCdif R (synCid)) p0008
  have p0010 := @gSnex (.cv x)
  have p0011 := @gImaex (synCcnv (synCdif R (synCid))) (synCsn (.cv x)) p0009 p0010
  have p0012 :=
    @gInex D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))) p0003 p0011
  have p0022 := @gSnex (.cv y)
  have p0023 := @gImaex (synCcnv (synCdif R (synCid))) (synCsn (.cv y)) p0009 p0022
  have p0024 :=
    @gInex D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))) p0003 p0023
  have p0025 :=
    @gNclec (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) p0012
      p0024
  have p0026 :=
    @gSyl
      (synW3a (.classMem (.cv x) D) (.classMem (.cv y) D) (synWbr (.cv x) R (.cv y)))
      (synWss (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
      (synWbr (synCnc
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))) (synClec)
        (synCnc (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
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

/-- Checked nominal proof certificate identified upstream as `g_wecutnclecclndv`. -/
@[expose]
noncomputable def gWecutnclecclndv (A : Class) (B : Class) (D : Class) (R : Class)
    (_dv_A_R : Disjoint A.fv R.fv)
    (hyp_wecutnclecclndv_1 : Nominal.NPrf (synWbr R (synCwe) D)) :
    Nominal.NPrf
      (.imp (synWa (.classMem A (synCvv)) (.classMem B (synCvv)))
        (.imp (synW3a (.classMem A D) (.classMem B D) (synWbr A R B)) (synWbr
            (synCnc (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn A))))
            (synClec) (synCnc
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B))))))) :=
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
      ((Wff.imp (synW3a (.classMem A D) (.classMem B D) (synWbr A R B)) (synWbr
            (synCnc (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn A))))
            (synClec) (synCnc (synCin D
                (synCima (synCcnv (synCdif R (synCid))) (synCsn B))))))).fv :=
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
      ((Wff.imp (synW3a (.classMem A D) (.classMem (.cv y) D) (synWbr A R (.cv y))) (synWbr
            (synCnc (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn A))))
            (synClec) (synCnc (synCin D
                (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))))).fv :=
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
  have p0000 := @gId (.classEq (.cv x) A)
  have p0001 := @gEleq1d (.classEq (.cv x) A) (.cv x) A D p0000
  have p0003 := @gBreq1d (.classEq (.cv x) A) (.cv x) A (.cv y) R p0000
  have p0004 :=
    @gN3anbi13d (.classEq (.cv x) A) (.classMem (.cv x) D) (.classMem A D)
      (synWbr (.cv x) R (.cv y)) (synWbr A R (.cv y)) (.classMem (.cv y) D) p0001 p0003
  have p0006 := @gSneqd (.classEq (.cv x) A) (.cv x) A p0000
  have p0007 :=
    @gImaeq2d (.classEq (.cv x) A) (synCsn (.cv x)) (synCsn A)
      (synCcnv (synCdif R (synCid))) p0006
  have p0008 :=
    @gIneq2d (.classEq (.cv x) A)
      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))
      (synCima (synCcnv (synCdif R (synCid))) (synCsn A)) D p0007
  have p0009 :=
    @gNceqd (.classEq (.cv x) A)
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn A))) p0008
  have p0010 :=
    @gBreq1d (.classEq (.cv x) A)
      (synCnc (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      (synCnc (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn A))))
      (synCnc (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
      (synClec) p0009
  have p0011 :=
    @gImbi12d (.classEq (.cv x) A)
      (synW3a (.classMem (.cv x) D) (.classMem (.cv y) D) (synWbr (.cv x) R (.cv y)))
      (synW3a (.classMem A D) (.classMem (.cv y) D) (synWbr A R (.cv y)))
      (synWbr (synCnc
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))) (synClec)
        (synCnc (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (synWbr (synCnc (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn A))))
        (synClec) (synCnc
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      p0004 p0010
  have p0012 := @gId (.classEq (.cv y) B)
  have p0013 := @gEleq1d (.classEq (.cv y) B) (.cv y) B D p0012
  have p0015 := @gBreq2d (.classEq (.cv y) B) (.cv y) B A R p0012
  have p0016 :=
    @gN3anbi23d (.classEq (.cv y) B) (.classMem (.cv y) D) (.classMem B D)
      (synWbr A R (.cv y)) (synWbr A R B) (.classMem A D) p0013 p0015
  have p0018 := @gSneqd (.classEq (.cv y) B) (.cv y) B p0012
  have p0019 :=
    @gImaeq2d (.classEq (.cv y) B) (synCsn (.cv y)) (synCsn B)
      (synCcnv (synCdif R (synCid))) p0018
  have p0020 :=
    @gIneq2d (.classEq (.cv y) B)
      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))
      (synCima (synCcnv (synCdif R (synCid))) (synCsn B)) D p0019
  have p0021 :=
    @gNceqd (.classEq (.cv y) B)
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B))) p0020
  have p0022 :=
    @gBreq2d (.classEq (.cv y) B)
      (synCnc (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
      (synCnc (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B))))
      (synCnc (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn A))))
      (synClec) p0021
  have p0023 :=
    @gImbi12d (.classEq (.cv y) B)
      (synW3a (.classMem A D) (.classMem (.cv y) D) (synWbr A R (.cv y)))
      (synW3a (.classMem A D) (.classMem B D) (synWbr A R B))
      (synWbr (synCnc (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn A))))
        (synClec) (synCnc
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (synWbr (synCnc (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn A))))
        (synClec)
        (synCnc (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B)))))
      p0016 p0022
  have p0024 :=
    @gWecutnclecndv x y D R dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 hyp_wecutnclecclndv_1
  have p0025 :=
    @gVtocl2g
      (.imp (synW3a (.classMem (.cv x) D) (.classMem (.cv y) D) (synWbr (.cv x) R (.cv y)))
        (synWbr (synCnc
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
          (synClec) (synCnc
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))))
      (.imp (synW3a (.classMem A D) (.classMem (.cv y) D) (synWbr A R (.cv y))) (synWbr
          (synCnc (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn A))))
          (synClec) (synCnc
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))))
      (.imp (synW3a (.classMem A D) (.classMem B D) (synWbr A R B)) (synWbr
          (synCnc (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn A))))
          (synClec)
          (synCnc (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn B))))))
      x y A B (synCvv) (synCvv) dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
      dv_cache_0010 p0011 p0023 p0024
  exact p0025

/-- Checked nominal proof certificate identified upstream as `g_wecuttypedbrndv`. -/
@[expose]
noncomputable def gWecuttypedbrndv (y : Var) (z : Var) (D : Class) (R : Class)
    (_dv_D_y : y ∉ D.fv) (_dv_D_z : z ∉ D.fv) (_dv_R_y : y ∉ R.fv) (_dv_R_z : z ∉ R.fv)
    (_dv_y_z : y ≠ z) :
    Nominal.NPrf
      (.imp (synWa (.classMem (.cv y) (synCpw1 (synCpw1 D)))
          (.classMem (.cv z) (synCpw1 (synCpw1 D))))
        (synWb (synWbr (.cv y) (synCsi (synCsi R)) (.cv z))
          (synWbr (synCuni (synCuni (.cv y))) R (synCuni (synCuni (.cv z)))))) :=
  by
  have p0000 :=
    @gSimpl (.classMem (.cv y) (synCpw1 (synCpw1 D)))
      (.classMem (.cv z) (synCpw1 (synCpw1 D)))
  have p0001 := @gPw12argcl (.cv y) D
  have p0002 :=
    @gSyl
      (synWa (.classMem (.cv y) (synCpw1 (synCpw1 D)))
        (.classMem (.cv z) (synCpw1 (synCpw1 D))))
      (.classMem (.cv y) (synCpw1 (synCpw1 D)))
      (synWa (.classMem (synCuni (synCuni (.cv y))) D)
        (.classEq (.cv y) (synCsn (synCsn (synCuni (synCuni (.cv y)))))))
      p0000 p0001
  have p0003 :=
    @gSimprd
      (synWa (.classMem (.cv y) (synCpw1 (synCpw1 D)))
        (.classMem (.cv z) (synCpw1 (synCpw1 D))))
      (.classMem (synCuni (synCuni (.cv y))) D)
      (.classEq (.cv y) (synCsn (synCsn (synCuni (synCuni (.cv y)))))) p0002
  have p0004 :=
    @gSimpr (.classMem (.cv y) (synCpw1 (synCpw1 D)))
      (.classMem (.cv z) (synCpw1 (synCpw1 D)))
  have p0005 := @gPw12argcl (.cv z) D
  have p0006 :=
    @gSyl
      (synWa (.classMem (.cv y) (synCpw1 (synCpw1 D)))
        (.classMem (.cv z) (synCpw1 (synCpw1 D))))
      (.classMem (.cv z) (synCpw1 (synCpw1 D)))
      (synWa (.classMem (synCuni (synCuni (.cv z))) D)
        (.classEq (.cv z) (synCsn (synCsn (synCuni (synCuni (.cv z)))))))
      p0004 p0005
  have p0007 :=
    @gSimprd
      (synWa (.classMem (.cv y) (synCpw1 (synCpw1 D)))
        (.classMem (.cv z) (synCpw1 (synCpw1 D))))
      (.classMem (synCuni (synCuni (.cv z))) D)
      (.classEq (.cv z) (synCsn (synCsn (synCuni (synCuni (.cv z)))))) p0006
  have p0008 :=
    @gBreq12d
      (synWa (.classMem (.cv y) (synCpw1 (synCpw1 D)))
        (.classMem (.cv z) (synCpw1 (synCpw1 D))))
      (.cv y) (synCsn (synCsn (synCuni (synCuni (.cv y))))) (.cv z)
      (synCsn (synCsn (synCuni (synCuni (.cv z))))) (synCsi (synCsi R)) p0003 p0007
  have p0009 := @gSnex (synCuni (synCuni (.cv y)))
  have p0010 := @gSnex (synCuni (synCuni (.cv z)))
  have p0011 :=
    @gBrsnsi (synCsn (synCuni (synCuni (.cv y))))
      (synCsn (synCuni (synCuni (.cv z)))) (synCsi R) p0009 p0010
  have p0012 := @gVex y
  have p0013 := @gUniex (.cv y) p0012
  have p0014 := @gUniex (synCuni (.cv y)) p0013
  have p0015 := @gVex z
  have p0016 := @gUniex (.cv z) p0015
  have p0017 := @gUniex (synCuni (.cv z)) p0016
  have p0018 :=
    @gBrsnsi (synCuni (synCuni (.cv y))) (synCuni (synCuni (.cv z))) R p0014 p0017
  have p0019 :=
    @gBitri
      (synWbr (synCsn (synCsn (synCuni (synCuni (.cv y))))) (synCsi (synCsi R))
        (synCsn (synCsn (synCuni (synCuni (.cv z))))))
      (synWbr (synCsn (synCuni (synCuni (.cv y)))) (synCsi R)
        (synCsn (synCuni (synCuni (.cv z)))))
      (synWbr (synCuni (synCuni (.cv y))) R (synCuni (synCuni (.cv z)))) p0011 p0018
  have p0020 :=
    @gA1i
      (synWb (synWbr (synCsn (synCsn (synCuni (synCuni (.cv y))))) (synCsi (synCsi R))
          (synCsn (synCsn (synCuni (synCuni (.cv z))))))
        (synWbr (synCuni (synCuni (.cv y))) R (synCuni (synCuni (.cv z)))))
      (synWa (.classMem (.cv y) (synCpw1 (synCpw1 D)))
        (.classMem (.cv z) (synCpw1 (synCpw1 D))))
      p0019
  have p0021 :=
    @gBitrd
      (synWa (.classMem (.cv y) (synCpw1 (synCpw1 D)))
        (.classMem (.cv z) (synCpw1 (synCpw1 D))))
      (synWbr (.cv y) (synCsi (synCsi R)) (.cv z))
      (synWbr (synCsn (synCsn (synCuni (synCuni (.cv y))))) (synCsi (synCsi R))
        (synCsn (synCsn (synCuni (synCuni (.cv z))))))
      (synWbr (synCuni (synCuni (.cv y))) R (synCuni (synCuni (.cv z)))) p0008 p0020
  exact p0021

/-- Checked nominal proof certificate identified upstream as `g_wecuttypednclecndv`. -/
@[expose]
noncomputable def gWecuttypednclecndv (y : Var) (z : Var) (D : Class) (R : Class)
    (dv_D_y : y ∉ D.fv) (dv_D_z : z ∉ D.fv) (dv_R_y : y ∉ R.fv) (dv_R_z : z ∉ R.fv)
    (dv_y_z : y ≠ z) (hyp_wecuttypednclecndv_1 : Nominal.NPrf (synWbr R (synCwe) D)) :
    Nominal.NPrf
      (.imp (synWa (.classMem (.cv y) (synCpw1 (synCpw1 D)))
          (.classMem (.cv z) (synCpw1 (synCpw1 D))))
        (.imp (synWbr (.cv y) (synCsi (synCsi R)) (.cv z)) (synWbr (synCnc (synCin D
                (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (synCuni (synCuni (.cv y))))))) (synClec) (synCnc (synCin D
                (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (synCuni (synCuni (.cv z)))))))))) :=
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
  have dv_cache_0006 : Disjoint ((synCuni (synCuni (.cv y)))).fv (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (show Disjoint ((synCuni (synCuni (.cv y)))).fv (R).fv from (by
          rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni];
          exact
            (show Disjoint (((synCuni (.cv y))).fv) ((R).fv) from
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
    @gSimpl
      (synWa (.classMem (.cv y) (synCpw1 (synCpw1 D)))
        (.classMem (.cv z) (synCpw1 (synCpw1 D))))
      (synWbr (.cv y) (synCsi (synCsi R)) (.cv z))
  have p0001 :=
    @gSimpl (.classMem (.cv y) (synCpw1 (synCpw1 D)))
      (.classMem (.cv z) (synCpw1 (synCpw1 D)))
  have p0002 := @gPw12argcl (.cv y) D
  have p0003 :=
    @gSyl
      (synWa (.classMem (.cv y) (synCpw1 (synCpw1 D)))
        (.classMem (.cv z) (synCpw1 (synCpw1 D))))
      (.classMem (.cv y) (synCpw1 (synCpw1 D)))
      (synWa (.classMem (synCuni (synCuni (.cv y))) D)
        (.classEq (.cv y) (synCsn (synCsn (synCuni (synCuni (.cv y)))))))
      p0001 p0002
  have p0004 :=
    @gSimpld
      (synWa (.classMem (.cv y) (synCpw1 (synCpw1 D)))
        (.classMem (.cv z) (synCpw1 (synCpw1 D))))
      (.classMem (synCuni (synCuni (.cv y))) D)
      (.classEq (.cv y) (synCsn (synCsn (synCuni (synCuni (.cv y)))))) p0003
  have p0005 :=
    @gSyl
      (synWa (synWa (.classMem (.cv y) (synCpw1 (synCpw1 D)))
          (.classMem (.cv z) (synCpw1 (synCpw1 D))))
        (synWbr (.cv y) (synCsi (synCsi R)) (.cv z)))
      (synWa (.classMem (.cv y) (synCpw1 (synCpw1 D)))
        (.classMem (.cv z) (synCpw1 (synCpw1 D))))
      (.classMem (synCuni (synCuni (.cv y))) D) p0000 p0004
  have p0007 :=
    @gSimpr (.classMem (.cv y) (synCpw1 (synCpw1 D)))
      (.classMem (.cv z) (synCpw1 (synCpw1 D)))
  have p0008 := @gPw12argcl (.cv z) D
  have p0009 :=
    @gSyl
      (synWa (.classMem (.cv y) (synCpw1 (synCpw1 D)))
        (.classMem (.cv z) (synCpw1 (synCpw1 D))))
      (.classMem (.cv z) (synCpw1 (synCpw1 D)))
      (synWa (.classMem (synCuni (synCuni (.cv z))) D)
        (.classEq (.cv z) (synCsn (synCsn (synCuni (synCuni (.cv z)))))))
      p0007 p0008
  have p0010 :=
    @gSimpld
      (synWa (.classMem (.cv y) (synCpw1 (synCpw1 D)))
        (.classMem (.cv z) (synCpw1 (synCpw1 D))))
      (.classMem (synCuni (synCuni (.cv z))) D)
      (.classEq (.cv z) (synCsn (synCsn (synCuni (synCuni (.cv z)))))) p0009
  have p0011 :=
    @gSyl
      (synWa (synWa (.classMem (.cv y) (synCpw1 (synCpw1 D)))
          (.classMem (.cv z) (synCpw1 (synCpw1 D))))
        (synWbr (.cv y) (synCsi (synCsi R)) (.cv z)))
      (synWa (.classMem (.cv y) (synCpw1 (synCpw1 D)))
        (.classMem (.cv z) (synCpw1 (synCpw1 D))))
      (.classMem (synCuni (synCuni (.cv z))) D) p0000 p0010
  have p0012 :=
    @gSimpr
      (synWa (.classMem (.cv y) (synCpw1 (synCpw1 D)))
        (.classMem (.cv z) (synCpw1 (synCpw1 D))))
      (synWbr (.cv y) (synCsi (synCsi R)) (.cv z))
  have p0014 :=
    @gWecuttypedbrndv y z D R dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005
  have p0015 :=
    @gBiimpd
      (synWa (.classMem (.cv y) (synCpw1 (synCpw1 D)))
        (.classMem (.cv z) (synCpw1 (synCpw1 D))))
      (synWbr (.cv y) (synCsi (synCsi R)) (.cv z))
      (synWbr (synCuni (synCuni (.cv y))) R (synCuni (synCuni (.cv z)))) p0014
  have p0016 :=
    @gSyl
      (synWa (synWa (.classMem (.cv y) (synCpw1 (synCpw1 D)))
          (.classMem (.cv z) (synCpw1 (synCpw1 D))))
        (synWbr (.cv y) (synCsi (synCsi R)) (.cv z)))
      (synWa (.classMem (.cv y) (synCpw1 (synCpw1 D)))
        (.classMem (.cv z) (synCpw1 (synCpw1 D))))
      (.imp (synWbr (.cv y) (synCsi (synCsi R)) (.cv z))
        (synWbr (synCuni (synCuni (.cv y))) R (synCuni (synCuni (.cv z)))))
      p0000 p0015
  have p0017 :=
    @gMpd
      (synWa (synWa (.classMem (.cv y) (synCpw1 (synCpw1 D)))
          (.classMem (.cv z) (synCpw1 (synCpw1 D))))
        (synWbr (.cv y) (synCsi (synCsi R)) (.cv z)))
      (synWbr (.cv y) (synCsi (synCsi R)) (.cv z))
      (synWbr (synCuni (synCuni (.cv y))) R (synCuni (synCuni (.cv z)))) p0012 p0016
  have p0018 :=
    @gN3jca
      (synWa (synWa (.classMem (.cv y) (synCpw1 (synCpw1 D)))
          (.classMem (.cv z) (synCpw1 (synCpw1 D))))
        (synWbr (.cv y) (synCsi (synCsi R)) (.cv z)))
      (.classMem (synCuni (synCuni (.cv y))) D)
      (.classMem (synCuni (synCuni (.cv z))) D)
      (synWbr (synCuni (synCuni (.cv y))) R (synCuni (synCuni (.cv z)))) p0005 p0011
      p0017
  have p0019 := @gVex y
  have p0020 := @gUniex (.cv y) p0019
  have p0021 := @gUniex (synCuni (.cv y)) p0020
  have p0022 := @gVex z
  have p0023 := @gUniex (.cv z) p0022
  have p0024 := @gUniex (synCuni (.cv z)) p0023
  have p0025 :=
    @gPm32i (.classMem (synCuni (synCuni (.cv y))) (synCvv))
      (.classMem (synCuni (synCuni (.cv z))) (synCvv)) p0021 p0024
  have p0026 :=
    @gWecutnclecclndv (synCuni (synCuni (.cv y))) (synCuni (synCuni (.cv z))) D R
      dv_cache_0006 hyp_wecuttypednclecndv_1
  have p0027 := Nominal.mp p0025 p0026
  have p0028 :=
    @gSyl
      (synWa (synWa (.classMem (.cv y) (synCpw1 (synCpw1 D)))
          (.classMem (.cv z) (synCpw1 (synCpw1 D))))
        (synWbr (.cv y) (synCsi (synCsi R)) (.cv z)))
      (synW3a (.classMem (synCuni (synCuni (.cv y))) D)
        (.classMem (synCuni (synCuni (.cv z))) D)
        (synWbr (synCuni (synCuni (.cv y))) R (synCuni (synCuni (.cv z)))))
      (synWbr (synCnc (synCin D (synCima (synCcnv (synCdif R (synCid)))
              (synCsn (synCuni (synCuni (.cv y))))))) (synClec) (synCnc (synCin D
            (synCima (synCcnv (synCdif R (synCid)))
              (synCsn (synCuni (synCuni (.cv z))))))))
      p0018 p0027
  have p0029 :=
    @gEx
      (synWa (.classMem (.cv y) (synCpw1 (synCpw1 D)))
        (.classMem (.cv z) (synCpw1 (synCpw1 D))))
      (synWbr (.cv y) (synCsi (synCsi R)) (.cv z))
      (synWbr (synCnc (synCin D (synCima (synCcnv (synCdif R (synCid)))
              (synCsn (synCuni (synCuni (.cv y))))))) (synClec) (synCnc (synCin D
            (synCima (synCcnv (synCdif R (synCid)))
              (synCsn (synCuni (synCuni (.cv z))))))))
      p0028
  exact p0029

/-- Checked nominal proof certificate identified upstream as `g_wecutcardtypedcardleastndv`. -/
@[expose]
noncomputable def gWecutcardtypedcardleastndv (y : Var) (z : Var) (D : Class) (R : Class)
    (K : Class) (q : Var) (dv_D_q : q ∉ D.fv) (dv_D_y : y ∉ D.fv) (dv_D_z : z ∉ D.fv)
    (dv_K_q : q ∉ K.fv) (dv_K_y : y ∉ K.fv) (dv_K_z : z ∉ K.fv) (dv_R_q : q ∉ R.fv)
    (dv_R_y : y ∉ R.fv) (dv_R_z : z ∉ R.fv) (dv_q_y : q ≠ y) (dv_q_z : q ≠ z)
    (dv_y_z : y ≠ z)
    (hyp_wecutcardtypedcardleastndv_1 : Nominal.NPrf (synWbr R (synCwe) D))
    (hyp_wecutcardtypedcardleastndv_2 : Nominal.NPrf (.classMem K (synCvv))) :
    Nominal.NPrf
      (.imp (synWrex q (synCpw1 (synCpw1 D)) (.classMem (synCnc (synCin D
                (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (synCuni (synCuni (.cv q))))))) K))
        (synWrex y (synCpw1 (synCpw1 D)) (synWa (.classMem (synCnc (synCin D
                  (synCima (synCcnv (synCdif R (synCid)))
                    (synCsn (synCuni (synCuni (.cv y))))))) K)
            (synWral z (synCpw1 (synCpw1 D)) (.imp (.classMem (synCnc (synCin D
                      (synCima (synCcnv (synCdif R (synCid)))
                        (synCsn (synCuni (synCuni (.cv z))))))) K) (synWbr (synCnc
                    (synCin D (synCima (synCcnv (synCdif R (synCid)))
                        (synCsn (synCuni (synCuni (.cv y))))))) (synClec) (synCnc
                    (synCin D (synCima (synCcnv (synCdif R (synCid)))
                        (synCsn (synCuni (synCuni (.cv z))))))))))))) :=
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
  have dv_cache_0013 : z ∉ ((Wff.classMem (.cv y) (synCpw1 (synCpw1 D)))).fv :=
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
    @gWecutcardtypedleastndv y z D R K q dv_cache_0001 dv_cache_0002 dv_cache_0003
      dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
      dv_cache_0010 dv_cache_0011 dv_cache_0012 hyp_wecutcardtypedcardleastndv_1
      hyp_wecutcardtypedcardleastndv_2
  have p0001 :=
    @gWecuttypednclecndv y z D R dv_cache_0002 dv_cache_0003 dv_cache_0008 dv_cache_0009
      dv_cache_0012 hyp_wecutcardtypedcardleastndv_1
  have p0002 :=
    @gImim2d
      (synWa (.classMem (.cv y) (synCpw1 (synCpw1 D)))
        (.classMem (.cv z) (synCpw1 (synCpw1 D))))
      (synWbr (.cv y) (synCsi (synCsi R)) (.cv z))
      (synWbr (synCnc (synCin D (synCima (synCcnv (synCdif R (synCid)))
              (synCsn (synCuni (synCuni (.cv y))))))) (synClec) (synCnc (synCin D
            (synCima (synCcnv (synCdif R (synCid)))
              (synCsn (synCuni (synCuni (.cv z))))))))
      (.classMem (synCnc (synCin D (synCima (synCcnv (synCdif R (synCid)))
              (synCsn (synCuni (synCuni (.cv z))))))) K)
      p0001
  have p0003 :=
    @gRalimdva (.classMem (.cv y) (synCpw1 (synCpw1 D)))
      (.imp (.classMem (synCnc (synCin D (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (.cv z))))))) K)
        (synWbr (.cv y) (synCsi (synCsi R)) (.cv z)))
      (.imp (.classMem (synCnc (synCin D (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (.cv z))))))) K) (synWbr (synCnc (synCin D
              (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (.cv y))))))) (synClec) (synCnc (synCin D
              (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (.cv z)))))))))
      z (synCpw1 (synCpw1 D)) dv_cache_0013 p0002
  have p0004 :=
    @gAnim2d (.classMem (.cv y) (synCpw1 (synCpw1 D)))
      (synWral z (synCpw1 (synCpw1 D)) (.imp (.classMem (synCnc (synCin D
                (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (synCuni (synCuni (.cv z))))))) K)
          (synWbr (.cv y) (synCsi (synCsi R)) (.cv z))))
      (synWral z (synCpw1 (synCpw1 D)) (.imp (.classMem (synCnc (synCin D
                (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (synCuni (synCuni (.cv z))))))) K) (synWbr (synCnc (synCin D
                (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (synCuni (synCuni (.cv y))))))) (synClec) (synCnc (synCin D
                (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (synCuni (synCuni (.cv z))))))))))
      (.classMem (synCnc (synCin D (synCima (synCcnv (synCdif R (synCid)))
              (synCsn (synCuni (synCuni (.cv y))))))) K)
      p0003
  have p0005 :=
    @gReximia
      (synWa (.classMem (synCnc (synCin D (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (.cv y))))))) K)
        (synWral z (synCpw1 (synCpw1 D)) (.imp (.classMem (synCnc (synCin D
                  (synCima (synCcnv (synCdif R (synCid)))
                    (synCsn (synCuni (synCuni (.cv z))))))) K)
            (synWbr (.cv y) (synCsi (synCsi R)) (.cv z)))))
      (synWa (.classMem (synCnc (synCin D (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (.cv y))))))) K)
        (synWral z (synCpw1 (synCpw1 D)) (.imp (.classMem (synCnc (synCin D
                  (synCima (synCcnv (synCdif R (synCid)))
                    (synCsn (synCuni (synCuni (.cv z))))))) K) (synWbr (synCnc (synCin D
                  (synCima (synCcnv (synCdif R (synCid)))
                    (synCsn (synCuni (synCuni (.cv y))))))) (synClec) (synCnc (synCin D
                  (synCima (synCcnv (synCdif R (synCid)))
                    (synCsn (synCuni (synCuni (.cv z)))))))))))
      y (synCpw1 (synCpw1 D)) p0004
  have p0006 :=
    @gSyl
      (synWrex q (synCpw1 (synCpw1 D)) (.classMem (synCnc (synCin D
              (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (.cv q))))))) K))
      (synWrex y (synCpw1 (synCpw1 D)) (synWa (.classMem (synCnc (synCin D
                (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (synCuni (synCuni (.cv y))))))) K)
          (synWral z (synCpw1 (synCpw1 D)) (.imp (.classMem (synCnc (synCin D
                    (synCima (synCcnv (synCdif R (synCid)))
                      (synCsn (synCuni (synCuni (.cv z))))))) K)
              (synWbr (.cv y) (synCsi (synCsi R)) (.cv z))))))
      (synWrex y (synCpw1 (synCpw1 D)) (synWa (.classMem (synCnc (synCin D
                (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (synCuni (synCuni (.cv y))))))) K)
          (synWral z (synCpw1 (synCpw1 D)) (.imp (.classMem (synCnc (synCin D
                    (synCima (synCcnv (synCdif R (synCid)))
                      (synCsn (synCuni (synCuni (.cv z))))))) K) (synWbr (synCnc (synCin D
                    (synCima (synCcnv (synCdif R (synCid)))
                      (synCsn (synCuni (synCuni (.cv y))))))) (synClec) (synCnc (synCin D
                    (synCima (synCcnv (synCdif R (synCid)))
                      (synCsn (synCuni (synCuni (.cv z))))))))))))
      p0000 p0005
  exact p0006

/-- Checked nominal proof certificate identified upstream as `g_elwppcandstrictslice`. -/
@[expose]
noncomputable def gElwppcandstrictslice (C : Class) (k : Var) (F : Class) :
    Nominal.NPrf
      (synWb (.classMem (.cv k)
          (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C))))
        (synWa (.classMem (.cv k) (synCwppcand F C)) (synWbr (.cv k) (synCltc) C))) :=
  by
  have p0000 :=
    @gElin (.cv k) (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C))
  have p0001 := @gBiid (.classMem (.cv k) (synCwppcand F C))
  have p0002 := @gEliniseg (synCltc) C (.cv k)
  have p0003 :=
    @gAnbi12i (.classMem (.cv k) (synCwppcand F C))
      (.classMem (.cv k) (synCwppcand F C))
      (.classMem (.cv k) (synCima (synCcnv (synCltc)) (synCsn C)))
      (synWbr (.cv k) (synCltc) C) p0001 p0002
  have p0004 :=
    @gBitri
      (.classMem (.cv k)
        (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C))))
      (synWa (.classMem (.cv k) (synCwppcand F C))
        (.classMem (.cv k) (synCima (synCcnv (synCltc)) (synCsn C))))
      (synWa (.classMem (.cv k) (synCwppcand F C)) (synWbr (.cv k) (synCltc) C)) p0000
      p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_wppreachexndv`. -/
@[expose]
noncomputable def gWppreachexndv (C : Class) (F : Class)
    (hyp_wppreachexndv_1 : Nominal.NPrf (.classMem F (synCvv))) :
    Nominal.NPrf (.classMem (synCwppreach F C) (synCvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (synCwppreach F C))
  have p0001 :=
    @gEqid (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
  have p0002 := @gCnvex F hyp_wppreachexndv_1
  have p0003 := @gImageex (synCcnv F) p0002
  have p0004 :=
    @gFrecex (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
      (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)) p0001 p0003
  have p0005 :=
    @gRnex (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C))) p0004
  have p0006 :=
    @gUniex
      (synCrn (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C))))
      p0005
  have p0007 :=
    @gEqeltri (synCwppreach F C)
      (synCuni
        (synCrn (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))))
      (synCvv) p0000 p0006
  exact p0007

/-- Checked nominal proof certificate identified upstream as `g_wppcandexndv`. -/
@[expose]
noncomputable def gWppcandexndv (C : Class) (F : Class)
    (hyp_wppcandexndv_1 : Nominal.NPrf (.classMem F (synCvv))) :
    Nominal.NPrf (.classMem (synCwppcand F C) (synCvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (synCwppcand F C))
  have p0001 := @gVvex
  have p0002 := @gHwcardsexg (synCvv)
  have p0003 := Nominal.mp p0001 p0002
  have p0004 := @gLecex
  have p0005 := @gCnvex (synClec) p0004
  have p0006 := @gSnex C
  have p0007 := @gImaex (synCcnv (synClec)) (synCsn C) p0005 p0006
  have p0008 :=
    @gInex (synChwcards (synCvv)) (synCima (synCcnv (synClec)) (synCsn C)) p0003
      p0007
  have p0009 := @gWppreachexndv C F hyp_wppcandexndv_1
  have p0010 :=
    @gInex
      (synCin (synChwcards (synCvv)) (synCima (synCcnv (synClec)) (synCsn C)))
      (synCwppreach F C) p0008 p0009
  have p0011 :=
    @gEqeltri (synCwppcand F C)
      (synCin (synCin (synChwcards (synCvv)) (synCima (synCcnv (synClec)) (synCsn C)))
        (synCwppreach F C))
      (synCvv) p0000 p0010
  exact p0011

/-- Checked nominal proof certificate identified upstream as `g_wppcandstrictsliceexndv`. -/
@[expose]
noncomputable def gWppcandstrictsliceexndv (C : Class) (F : Class)
    (hyp_wppcandstrictsliceexndv_1 : Nominal.NPrf (.classMem F (synCvv))) :
    Nominal.NPrf
      (.classMem (synCin (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C)))
        (synCvv)) :=
  by
  have p0000 := @gWppcandexndv C F hyp_wppcandstrictsliceexndv_1
  have p0001 := @gLtcex
  have p0002 := @gCnvex (synCltc) p0001
  have p0003 := @gSnex C
  have p0004 := @gImaex (synCcnv (synCltc)) (synCsn C) p0002 p0003
  have p0005 :=
    @gInex (synCwppcand F C) (synCima (synCcnv (synCltc)) (synCsn C)) p0000 p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_wppcandnltpivoteqd`. -/
@[expose]
noncomputable def gWppcandnltpivoteqd (C : Class) (k : Var) (F : Class) :
    Nominal.NPrf
      (.imp (synWa (.classMem (.cv k) (synCwppcand F C))
          (.neg (synWbr (.cv k) (synCltc) C))) (.classEq (.cv k) C)) :=
  by
  have p0000 := @gId (.classEq (.cv k) C)
  have p0001 :=
    @gA1i (.imp (.classEq (.cv k) C) (.classEq (.cv k) C))
      (synWa (.classMem (.cv k) (synCwppcand F C)) (.neg (synWbr (.cv k) (synCltc) C)))
      p0000
  have p0002 :=
    @gSimpl (.classMem (.cv k) (synCwppcand F C)) (.neg (synWbr (.cv k) (synCltc) C))
  have p0003 := @gElwppcand C (.cv k) F
  have p0004 :=
    @gBiimpi (.classMem (.cv k) (synCwppcand F C))
      (synWa (synWa (.classMem (.cv k) (synChwcards (synCvv)))
          (synWbr (.cv k) (synClec) C)) (.classMem (.cv k) (synCwppreach F C)))
      p0003
  have p0005 :=
    @gSyl
      (synWa (.classMem (.cv k) (synCwppcand F C)) (.neg (synWbr (.cv k) (synCltc) C)))
      (.classMem (.cv k) (synCwppcand F C))
      (synWa (synWa (.classMem (.cv k) (synChwcards (synCvv)))
          (synWbr (.cv k) (synClec) C)) (.classMem (.cv k) (synCwppreach F C)))
      p0002 p0004
  have p0006 :=
    @gSimpld
      (synWa (.classMem (.cv k) (synCwppcand F C)) (.neg (synWbr (.cv k) (synCltc) C)))
      (synWa (.classMem (.cv k) (synChwcards (synCvv))) (synWbr (.cv k) (synClec) C))
      (.classMem (.cv k) (synCwppreach F C)) p0005
  have p0007 :=
    @gSimprd
      (synWa (.classMem (.cv k) (synCwppcand F C)) (.neg (synWbr (.cv k) (synCltc) C)))
      (.classMem (.cv k) (synChwcards (synCvv))) (synWbr (.cv k) (synClec) C) p0006
  have p0008 := @gBrltc (.cv k) C
  have p0009 :=
    @gBiimpri (synWbr (.cv k) (synCltc) C)
      (synWa (synWbr (.cv k) (synClec) C) (synWne (.cv k) C)) p0008
  have p0010 :=
    @gEx (synWbr (.cv k) (synClec) C) (synWne (.cv k) C)
      (synWbr (.cv k) (synCltc) C) p0009
  have p0011 :=
    @gSyl
      (synWa (.classMem (.cv k) (synCwppcand F C)) (.neg (synWbr (.cv k) (synCltc) C)))
      (synWbr (.cv k) (synClec) C)
      (.imp (synWne (.cv k) C) (synWbr (.cv k) (synCltc) C)) p0007 p0010
  have p0012 :=
    @gSimpr (.classMem (.cv k) (synCwppcand F C)) (.neg (synWbr (.cv k) (synCltc) C))
  have p0013 :=
    @gPm221d
      (synWa (.classMem (.cv k) (synCwppcand F C)) (.neg (synWbr (.cv k) (synCltc) C)))
      (synWbr (.cv k) (synCltc) C) (.classEq (.cv k) C) p0012
  have p0014 :=
    @gSyld
      (synWa (.classMem (.cv k) (synCwppcand F C)) (.neg (synWbr (.cv k) (synCltc) C)))
      (synWne (.cv k) C) (synWbr (.cv k) (synCltc) C) (.classEq (.cv k) C) p0011 p0013
  have p0015 :=
    @gPm261dne
      (synWa (.classMem (.cv k) (synCwppcand F C)) (.neg (synWbr (.cv k) (synCltc) C)))
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

/-- Checked nominal proof certificate identified upstream as `g_wecutcardrepleastdndv`. -/
@[expose]
noncomputable def gWecutcardrepleastdndv (y : Var) (D : Class) (R : Class) (k : Var)
    (K : Class) (q : Var) (dv_D_k : k ∉ D.fv) (dv_D_q : q ∉ D.fv) (dv_D_y : y ∉ D.fv)
    (dv_K_k : k ∉ K.fv) (dv_K_q : q ∉ K.fv) (dv_K_y : y ∉ K.fv) (dv_R_k : k ∉ R.fv)
    (dv_R_q : q ∉ R.fv) (dv_R_y : y ∉ R.fv) (dv_k_q : k ≠ q) (dv_k_y : k ≠ y)
    (dv_q_y : q ≠ y) (hyp_wecutcardrepleastdndv_1 : Nominal.NPrf (synWbr R (synCwe) D))
    (hyp_wecutcardrepleastdndv_2 : Nominal.NPrf (.classMem K (synCvv)))
    (hyp_wecutcardrepleastdndv_3 : Nominal.NPrf (synWral k K
          (synWrex q (synCpw1 (synCpw1 D)) (.classEq (.cv k) (synCnc (synCin D
                  (synCima (synCcnv (synCdif R (synCid)))
                    (synCsn (synCuni (synCuni (.cv q))))))))))) :
    Nominal.NPrf
      (.imp (synWne K (synC0)) (synWrex y (synCpw1 (synCpw1 D)) (synWa (.classMem (synCnc
                (synCin D (synCima (synCcnv (synCdif R (synCid)))
                    (synCsn (synCuni (synCuni (.cv y))))))) K) (synWral k K (synWbr
                (synCnc (synCin D (synCima (synCcnv (synCdif R (synCid)))
                      (synCsn (synCuni (synCuni (.cv y))))))) (synClec) (.cv k)))))) :=
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
  have dv_cache_0003 : k ∉ ((synCpw1 (synCpw1 D))).fv :=
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
      ((Wff.classMem (synCnc (synCin D (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (.cv q))))))) K)).fv :=
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
  have dv_cache_0018 : z ∉ ((synCpw1 (synCpw1 D))).fv :=
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
      ((Wff.imp (.classMem (synCnc (synCin D (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (synCuni (synCuni (.cv q))))))) K) (synWbr (synCnc (synCin D
                (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (synCuni (synCuni (.cv y))))))) (synClec) (synCnc (synCin D
                (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (synCuni (synCuni (.cv q)))))))))).fv :=
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
      ((synWbr (synCnc (synCin D (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (.cv y))))))) (synClec) (.cv k))).fv :=
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
      ((synWa (synWa (.classMem (synCnc (synCin D
                  (synCima (synCcnv (synCdif R (synCid)))
                    (synCsn (synCuni (synCuni (.cv y))))))) K)
            (synWral z (synCpw1 (synCpw1 D)) (.imp (.classMem (synCnc (synCin D
                      (synCima (synCcnv (synCdif R (synCid)))
                        (synCsn (synCuni (synCuni (.cv z))))))) K) (synWbr (synCnc
                    (synCin D (synCima (synCcnv (synCdif R (synCid)))
                        (synCsn (synCuni (synCuni (.cv y))))))) (synClec) (synCnc
                    (synCin D (synCima (synCcnv (synCdif R (synCid)))
                        (synCsn (synCuni (synCuni (.cv z)))))))))))
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
      ((synWa (.classMem (synCnc (synCin D (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (synCuni (synCuni (.cv y))))))) K)
          (synWral z (synCpw1 (synCpw1 D)) (.imp (.classMem (synCnc (synCin D
                    (synCima (synCcnv (synCdif R (synCid)))
                      (synCsn (synCuni (synCuni (.cv z))))))) K) (synWbr (synCnc (synCin D
                    (synCima (synCcnv (synCdif R (synCid)))
                      (synCsn (synCuni (synCuni (.cv y))))))) (synClec) (synCnc (synCin D
                    (synCima (synCcnv (synCdif R (synCid)))
                      (synCsn (synCuni (synCuni (.cv z)))))))))))).fv :=
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
  have p0000 := @gId (synWne K (synC0))
  have p0001 :=
    @gJctir (synWne K (synC0)) (synWne K (synC0))
      (synWral k K (synWrex q (synCpw1 (synCpw1 D)) (.classEq (.cv k) (synCnc (synCin D
                (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (synCuni (synCuni (.cv q))))))))))
      p0000 hyp_wecutcardrepleastdndv_3
  have p0002 :=
    @gR192z
      (synWrex q (synCpw1 (synCpw1 D)) (.classEq (.cv k) (synCnc (synCin D
              (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (.cv q)))))))))
      k K dv_cache_0001
  have p0003 :=
    @gSyl (synWne K (synC0))
      (synWa (synWne K (synC0)) (synWral k K (synWrex q (synCpw1 (synCpw1 D))
            (.classEq (.cv k) (synCnc (synCin D (synCima (synCcnv (synCdif R (synCid)))
                    (synCsn (synCuni (synCuni (.cv q)))))))))))
      (synWrex k K (synWrex q (synCpw1 (synCpw1 D)) (.classEq (.cv k) (synCnc (synCin D
                (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (synCuni (synCuni (.cv q))))))))))
      p0001 p0002
  have p0004 :=
    @gRexcom
      (.classEq (.cv k) (synCnc (synCin D (synCima (synCcnv (synCdif R (synCid)))
              (synCsn (synCuni (synCuni (.cv q))))))))
      k q K (synCpw1 (synCpw1 D)) dv_cache_0002 dv_cache_0003 dv_cache_0004
  have p0005 :=
    @gBiimpi
      (synWrex k K (synWrex q (synCpw1 (synCpw1 D)) (.classEq (.cv k) (synCnc (synCin D
                (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (synCuni (synCuni (.cv q))))))))))
      (synWrex q (synCpw1 (synCpw1 D)) (synWrex k K (.classEq (.cv k) (synCnc (synCin D
                (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (synCuni (synCuni (.cv q))))))))))
      p0004
  have p0006 :=
    @gSyl (synWne K (synC0))
      (synWrex k K (synWrex q (synCpw1 (synCpw1 D)) (.classEq (.cv k) (synCnc (synCin D
                (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (synCuni (synCuni (.cv q))))))))))
      (synWrex q (synCpw1 (synCpw1 D)) (synWrex k K (.classEq (.cv k) (synCnc (synCin D
                (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (synCuni (synCuni (.cv q))))))))))
      p0003 p0005
  have p0007 :=
    @gSimpr (.classMem (.cv k) K)
      (.classEq (.cv k) (synCnc (synCin D (synCima (synCcnv (synCdif R (synCid)))
              (synCsn (synCuni (synCuni (.cv q))))))))
  have p0008 :=
    @gSimpl (.classMem (.cv k) K)
      (.classEq (.cv k) (synCnc (synCin D (synCima (synCcnv (synCdif R (synCid)))
              (synCsn (synCuni (synCuni (.cv q))))))))
  have p0009 :=
    @gEqeltrrd
      (synWa (.classMem (.cv k) K) (.classEq (.cv k) (synCnc (synCin D
              (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (.cv q)))))))))
      (.cv k)
      (synCnc (synCin D (synCima (synCcnv (synCdif R (synCid)))
            (synCsn (synCuni (synCuni (.cv q)))))))
      K p0007 p0008
  have p0010 :=
    @gRexlimiva
      (.classEq (.cv k) (synCnc (synCin D (synCima (synCcnv (synCdif R (synCid)))
              (synCsn (synCuni (synCuni (.cv q))))))))
      (.classMem (synCnc (synCin D (synCima (synCcnv (synCdif R (synCid)))
              (synCsn (synCuni (synCuni (.cv q))))))) K)
      k K dv_cache_0005 p0009
  have p0011 :=
    @gReximi
      (synWrex k K (.classEq (.cv k) (synCnc (synCin D
              (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (.cv q)))))))))
      (.classMem (synCnc (synCin D (synCima (synCcnv (synCdif R (synCid)))
              (synCsn (synCuni (synCuni (.cv q))))))) K)
      q (synCpw1 (synCpw1 D)) p0010
  have p0012 :=
    @gSyl (synWne K (synC0))
      (synWrex q (synCpw1 (synCpw1 D)) (synWrex k K (.classEq (.cv k) (synCnc (synCin D
                (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (synCuni (synCuni (.cv q))))))))))
      (synWrex q (synCpw1 (synCpw1 D)) (.classMem (synCnc (synCin D
              (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (.cv q))))))) K))
      p0006 p0011
  have p0013 :=
    @gWecutcardtypedcardleastndv y z D R K q dv_cache_0006 dv_cache_0007 dv_cache_0008
      dv_cache_0002 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013
      dv_cache_0014 dv_cache_0015 dv_cache_0016 hyp_wecutcardrepleastdndv_1
      hyp_wecutcardrepleastdndv_2
  have p0014 :=
    @gSyl (synWne K (synC0))
      (synWrex q (synCpw1 (synCpw1 D)) (.classMem (synCnc (synCin D
              (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (.cv q))))))) K))
      (synWrex y (synCpw1 (synCpw1 D)) (synWa (.classMem (synCnc (synCin D
                (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (synCuni (synCuni (.cv y))))))) K)
          (synWral z (synCpw1 (synCpw1 D)) (.imp (.classMem (synCnc (synCin D
                    (synCima (synCcnv (synCdif R (synCid)))
                      (synCsn (synCuni (synCuni (.cv z))))))) K) (synWbr (synCnc (synCin D
                    (synCima (synCcnv (synCdif R (synCid)))
                      (synCsn (synCuni (synCuni (.cv y))))))) (synClec) (synCnc (synCin D
                    (synCima (synCcnv (synCdif R (synCid)))
                      (synCsn (synCuni (synCuni (.cv z))))))))))))
      p0012 p0013
  have p0015 :=
    @gSimpl
      (.classMem (synCnc (synCin D (synCima (synCcnv (synCdif R (synCid)))
              (synCsn (synCuni (synCuni (.cv y))))))) K)
      (synWral z (synCpw1 (synCpw1 D)) (.imp (.classMem (synCnc (synCin D
                (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (synCuni (synCuni (.cv z))))))) K) (synWbr (synCnc (synCin D
                (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (synCuni (synCuni (.cv y))))))) (synClec) (synCnc (synCin D
                (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (synCuni (synCuni (.cv z))))))))))
  have p0016 :=
    @gSimpr
      (synWa (.classMem (synCnc (synCin D (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (.cv y))))))) K)
        (synWral z (synCpw1 (synCpw1 D)) (.imp (.classMem (synCnc (synCin D
                  (synCima (synCcnv (synCdif R (synCid)))
                    (synCsn (synCuni (synCuni (.cv z))))))) K) (synWbr (synCnc (synCin D
                  (synCima (synCcnv (synCdif R (synCid)))
                    (synCsn (synCuni (synCuni (.cv y))))))) (synClec) (synCnc (synCin D
                  (synCima (synCcnv (synCdif R (synCid)))
                    (synCsn (synCuni (synCuni (.cv z)))))))))))
      (.classMem (.cv k) K)
  have p0017 :=
    @gRsp
      (synWrex q (synCpw1 (synCpw1 D)) (.classEq (.cv k) (synCnc (synCin D
              (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (.cv q)))))))))
      k K
  have p0018 := Nominal.mp hyp_wecutcardrepleastdndv_3 p0017
  have p0019 :=
    @gSyl
      (synWa (synWa (.classMem (synCnc (synCin D (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (synCuni (synCuni (.cv y))))))) K)
          (synWral z (synCpw1 (synCpw1 D)) (.imp (.classMem (synCnc (synCin D
                    (synCima (synCcnv (synCdif R (synCid)))
                      (synCsn (synCuni (synCuni (.cv z))))))) K) (synWbr (synCnc (synCin D
                    (synCima (synCcnv (synCdif R (synCid)))
                      (synCsn (synCuni (synCuni (.cv y))))))) (synClec) (synCnc (synCin D
                    (synCima (synCcnv (synCdif R (synCid)))
                      (synCsn (synCuni (synCuni (.cv z))))))))))) (.classMem (.cv k) K))
      (.classMem (.cv k) K)
      (synWrex q (synCpw1 (synCpw1 D)) (.classEq (.cv k) (synCnc (synCin D
              (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (.cv q)))))))))
      p0016 p0018
  have p0020 :=
    @gSimpr
      (synWa (synWa (.classMem (synCnc (synCin D (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (synCuni (synCuni (.cv y))))))) K)
          (synWral z (synCpw1 (synCpw1 D)) (.imp (.classMem (synCnc (synCin D
                    (synCima (synCcnv (synCdif R (synCid)))
                      (synCsn (synCuni (synCuni (.cv z))))))) K) (synWbr (synCnc (synCin D
                    (synCima (synCcnv (synCdif R (synCid)))
                      (synCsn (synCuni (synCuni (.cv y))))))) (synClec) (synCnc (synCin D
                    (synCima (synCcnv (synCdif R (synCid)))
                      (synCsn (synCuni (synCuni (.cv z))))))))))) (.classMem (.cv k) K))
      (synWa (.classMem (.cv q) (synCpw1 (synCpw1 D))) (.classEq (.cv k) (synCnc (synCin D
              (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (.cv q)))))))))
  have p0021 :=
    @gSimprd
      (synWa (synWa (synWa (.classMem (synCnc (synCin D
                  (synCima (synCcnv (synCdif R (synCid)))
                    (synCsn (synCuni (synCuni (.cv y))))))) K)
            (synWral z (synCpw1 (synCpw1 D)) (.imp (.classMem (synCnc (synCin D
                      (synCima (synCcnv (synCdif R (synCid)))
                        (synCsn (synCuni (synCuni (.cv z))))))) K) (synWbr (synCnc
                    (synCin D (synCima (synCcnv (synCdif R (synCid)))
                        (synCsn (synCuni (synCuni (.cv y))))))) (synClec) (synCnc
                    (synCin D (synCima (synCcnv (synCdif R (synCid)))
                        (synCsn (synCuni (synCuni (.cv z))))))))))) (.classMem (.cv k) K))
        (synWa (.classMem (.cv q) (synCpw1 (synCpw1 D))) (.classEq (.cv k) (synCnc
              (synCin D (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (synCuni (synCuni (.cv q))))))))))
      (.classMem (.cv q) (synCpw1 (synCpw1 D)))
      (.classEq (.cv k) (synCnc (synCin D (synCima (synCcnv (synCdif R (synCid)))
              (synCsn (synCuni (synCuni (.cv q))))))))
      p0020
  have p0022 :=
    @gSimpl
      (synWa (synWa (.classMem (synCnc (synCin D (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (synCuni (synCuni (.cv y))))))) K)
          (synWral z (synCpw1 (synCpw1 D)) (.imp (.classMem (synCnc (synCin D
                    (synCima (synCcnv (synCdif R (synCid)))
                      (synCsn (synCuni (synCuni (.cv z))))))) K) (synWbr (synCnc (synCin D
                    (synCima (synCcnv (synCdif R (synCid)))
                      (synCsn (synCuni (synCuni (.cv y))))))) (synClec) (synCnc (synCin D
                    (synCima (synCcnv (synCdif R (synCid)))
                      (synCsn (synCuni (synCuni (.cv z))))))))))) (.classMem (.cv k) K))
      (synWa (.classMem (.cv q) (synCpw1 (synCpw1 D))) (.classEq (.cv k) (synCnc (synCin D
              (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (.cv q)))))))))
  have p0024 :=
    @gSyl
      (synWa (synWa (synWa (.classMem (synCnc (synCin D
                  (synCima (synCcnv (synCdif R (synCid)))
                    (synCsn (synCuni (synCuni (.cv y))))))) K)
            (synWral z (synCpw1 (synCpw1 D)) (.imp (.classMem (synCnc (synCin D
                      (synCima (synCcnv (synCdif R (synCid)))
                        (synCsn (synCuni (synCuni (.cv z))))))) K) (synWbr (synCnc
                    (synCin D (synCima (synCcnv (synCdif R (synCid)))
                        (synCsn (synCuni (synCuni (.cv y))))))) (synClec) (synCnc
                    (synCin D (synCima (synCcnv (synCdif R (synCid)))
                        (synCsn (synCuni (synCuni (.cv z))))))))))) (.classMem (.cv k) K))
        (synWa (.classMem (.cv q) (synCpw1 (synCpw1 D))) (.classEq (.cv k) (synCnc
              (synCin D (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (synCuni (synCuni (.cv q))))))))))
      (synWa (synWa (.classMem (synCnc (synCin D (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (synCuni (synCuni (.cv y))))))) K)
          (synWral z (synCpw1 (synCpw1 D)) (.imp (.classMem (synCnc (synCin D
                    (synCima (synCcnv (synCdif R (synCid)))
                      (synCsn (synCuni (synCuni (.cv z))))))) K) (synWbr (synCnc (synCin D
                    (synCima (synCcnv (synCdif R (synCid)))
                      (synCsn (synCuni (synCuni (.cv y))))))) (synClec) (synCnc (synCin D
                    (synCima (synCcnv (synCdif R (synCid)))
                      (synCsn (synCuni (synCuni (.cv z))))))))))) (.classMem (.cv k) K))
      (.classMem (.cv k) K) p0022 p0016
  have p0025 :=
    @gEqeltrrd
      (synWa (synWa (synWa (.classMem (synCnc (synCin D
                  (synCima (synCcnv (synCdif R (synCid)))
                    (synCsn (synCuni (synCuni (.cv y))))))) K)
            (synWral z (synCpw1 (synCpw1 D)) (.imp (.classMem (synCnc (synCin D
                      (synCima (synCcnv (synCdif R (synCid)))
                        (synCsn (synCuni (synCuni (.cv z))))))) K) (synWbr (synCnc
                    (synCin D (synCima (synCcnv (synCdif R (synCid)))
                        (synCsn (synCuni (synCuni (.cv y))))))) (synClec) (synCnc
                    (synCin D (synCima (synCcnv (synCdif R (synCid)))
                        (synCsn (synCuni (synCuni (.cv z))))))))))) (.classMem (.cv k) K))
        (synWa (.classMem (.cv q) (synCpw1 (synCpw1 D))) (.classEq (.cv k) (synCnc
              (synCin D (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (synCuni (synCuni (.cv q))))))))))
      (.cv k)
      (synCnc (synCin D (synCima (synCcnv (synCdif R (synCid)))
            (synCsn (synCuni (synCuni (.cv q)))))))
      K p0021 p0024
  have p0027 :=
    @gSimpl
      (synWa (.classMem (synCnc (synCin D (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (.cv y))))))) K)
        (synWral z (synCpw1 (synCpw1 D)) (.imp (.classMem (synCnc (synCin D
                  (synCima (synCcnv (synCdif R (synCid)))
                    (synCsn (synCuni (synCuni (.cv z))))))) K) (synWbr (synCnc (synCin D
                  (synCima (synCcnv (synCdif R (synCid)))
                    (synCsn (synCuni (synCuni (.cv y))))))) (synClec) (synCnc (synCin D
                  (synCima (synCcnv (synCdif R (synCid)))
                    (synCsn (synCuni (synCuni (.cv z)))))))))))
      (.classMem (.cv k) K)
  have p0028 :=
    @gSyl
      (synWa (synWa (synWa (.classMem (synCnc (synCin D
                  (synCima (synCcnv (synCdif R (synCid)))
                    (synCsn (synCuni (synCuni (.cv y))))))) K)
            (synWral z (synCpw1 (synCpw1 D)) (.imp (.classMem (synCnc (synCin D
                      (synCima (synCcnv (synCdif R (synCid)))
                        (synCsn (synCuni (synCuni (.cv z))))))) K) (synWbr (synCnc
                    (synCin D (synCima (synCcnv (synCdif R (synCid)))
                        (synCsn (synCuni (synCuni (.cv y))))))) (synClec) (synCnc
                    (synCin D (synCima (synCcnv (synCdif R (synCid)))
                        (synCsn (synCuni (synCuni (.cv z))))))))))) (.classMem (.cv k) K))
        (synWa (.classMem (.cv q) (synCpw1 (synCpw1 D))) (.classEq (.cv k) (synCnc
              (synCin D (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (synCuni (synCuni (.cv q))))))))))
      (synWa (synWa (.classMem (synCnc (synCin D (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (synCuni (synCuni (.cv y))))))) K)
          (synWral z (synCpw1 (synCpw1 D)) (.imp (.classMem (synCnc (synCin D
                    (synCima (synCcnv (synCdif R (synCid)))
                      (synCsn (synCuni (synCuni (.cv z))))))) K) (synWbr (synCnc (synCin D
                    (synCima (synCcnv (synCdif R (synCid)))
                      (synCsn (synCuni (synCuni (.cv y))))))) (synClec) (synCnc (synCin D
                    (synCima (synCcnv (synCdif R (synCid)))
                      (synCsn (synCuni (synCuni (.cv z))))))))))) (.classMem (.cv k) K))
      (synWa (.classMem (synCnc (synCin D (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (.cv y))))))) K)
        (synWral z (synCpw1 (synCpw1 D)) (.imp (.classMem (synCnc (synCin D
                  (synCima (synCcnv (synCdif R (synCid)))
                    (synCsn (synCuni (synCuni (.cv z))))))) K) (synWbr (synCnc (synCin D
                  (synCima (synCcnv (synCdif R (synCid)))
                    (synCsn (synCuni (synCuni (.cv y))))))) (synClec) (synCnc (synCin D
                  (synCima (synCcnv (synCdif R (synCid)))
                    (synCsn (synCuni (synCuni (.cv z)))))))))))
      p0022 p0027
  have p0029 :=
    @gSimpr
      (.classMem (synCnc (synCin D (synCima (synCcnv (synCdif R (synCid)))
              (synCsn (synCuni (synCuni (.cv y))))))) K)
      (synWral z (synCpw1 (synCpw1 D)) (.imp (.classMem (synCnc (synCin D
                (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (synCuni (synCuni (.cv z))))))) K) (synWbr (synCnc (synCin D
                (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (synCuni (synCuni (.cv y))))))) (synClec) (synCnc (synCin D
                (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (synCuni (synCuni (.cv z))))))))))
  have p0030 :=
    @gSyl
      (synWa (synWa (synWa (.classMem (synCnc (synCin D
                  (synCima (synCcnv (synCdif R (synCid)))
                    (synCsn (synCuni (synCuni (.cv y))))))) K)
            (synWral z (synCpw1 (synCpw1 D)) (.imp (.classMem (synCnc (synCin D
                      (synCima (synCcnv (synCdif R (synCid)))
                        (synCsn (synCuni (synCuni (.cv z))))))) K) (synWbr (synCnc
                    (synCin D (synCima (synCcnv (synCdif R (synCid)))
                        (synCsn (synCuni (synCuni (.cv y))))))) (synClec) (synCnc
                    (synCin D (synCima (synCcnv (synCdif R (synCid)))
                        (synCsn (synCuni (synCuni (.cv z))))))))))) (.classMem (.cv k) K))
        (synWa (.classMem (.cv q) (synCpw1 (synCpw1 D))) (.classEq (.cv k) (synCnc
              (synCin D (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (synCuni (synCuni (.cv q))))))))))
      (synWa (.classMem (synCnc (synCin D (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (.cv y))))))) K)
        (synWral z (synCpw1 (synCpw1 D)) (.imp (.classMem (synCnc (synCin D
                  (synCima (synCcnv (synCdif R (synCid)))
                    (synCsn (synCuni (synCuni (.cv z))))))) K) (synWbr (synCnc (synCin D
                  (synCima (synCcnv (synCdif R (synCid)))
                    (synCsn (synCuni (synCuni (.cv y))))))) (synClec) (synCnc (synCin D
                  (synCima (synCcnv (synCdif R (synCid)))
                    (synCsn (synCuni (synCuni (.cv z)))))))))))
      (synWral z (synCpw1 (synCpw1 D)) (.imp (.classMem (synCnc (synCin D
                (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (synCuni (synCuni (.cv z))))))) K) (synWbr (synCnc (synCin D
                (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (synCuni (synCuni (.cv y))))))) (synClec) (synCnc (synCin D
                (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (synCuni (synCuni (.cv z))))))))))
      p0028 p0029
  have p0032 :=
    @gSimpld
      (synWa (synWa (synWa (.classMem (synCnc (synCin D
                  (synCima (synCcnv (synCdif R (synCid)))
                    (synCsn (synCuni (synCuni (.cv y))))))) K)
            (synWral z (synCpw1 (synCpw1 D)) (.imp (.classMem (synCnc (synCin D
                      (synCima (synCcnv (synCdif R (synCid)))
                        (synCsn (synCuni (synCuni (.cv z))))))) K) (synWbr (synCnc
                    (synCin D (synCima (synCcnv (synCdif R (synCid)))
                        (synCsn (synCuni (synCuni (.cv y))))))) (synClec) (synCnc
                    (synCin D (synCima (synCcnv (synCdif R (synCid)))
                        (synCsn (synCuni (synCuni (.cv z))))))))))) (.classMem (.cv k) K))
        (synWa (.classMem (.cv q) (synCpw1 (synCpw1 D))) (.classEq (.cv k) (synCnc
              (synCin D (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (synCuni (synCuni (.cv q))))))))))
      (.classMem (.cv q) (synCpw1 (synCpw1 D)))
      (.classEq (.cv k) (synCnc (synCin D (synCima (synCcnv (synCdif R (synCid)))
              (synCsn (synCuni (synCuni (.cv q))))))))
      p0020
  have p0033 := @gId (.classEq (.cv z) (.cv q))
  have p0034 := @gUnieqd (.classEq (.cv z) (.cv q)) (.cv z) (.cv q) p0033
  have p0035 :=
    @gUnieqd (.classEq (.cv z) (.cv q)) (synCuni (.cv z)) (synCuni (.cv q)) p0034
  have p0036 :=
    @gSneqd (.classEq (.cv z) (.cv q)) (synCuni (synCuni (.cv z)))
      (synCuni (synCuni (.cv q))) p0035
  have p0037 :=
    @gImaeq2d (.classEq (.cv z) (.cv q)) (synCsn (synCuni (synCuni (.cv z))))
      (synCsn (synCuni (synCuni (.cv q)))) (synCcnv (synCdif R (synCid))) p0036
  have p0038 :=
    @gIneq2d (.classEq (.cv z) (.cv q))
      (synCima (synCcnv (synCdif R (synCid))) (synCsn (synCuni (synCuni (.cv z)))))
      (synCima (synCcnv (synCdif R (synCid))) (synCsn (synCuni (synCuni (.cv q)))))
      D p0037
  have p0039 :=
    @gNceqd (.classEq (.cv z) (.cv q))
      (synCin D (synCima (synCcnv (synCdif R (synCid)))
          (synCsn (synCuni (synCuni (.cv z))))))
      (synCin D (synCima (synCcnv (synCdif R (synCid)))
          (synCsn (synCuni (synCuni (.cv q))))))
      p0038
  have p0040 :=
    @gEleq1d (.classEq (.cv z) (.cv q))
      (synCnc (synCin D (synCima (synCcnv (synCdif R (synCid)))
            (synCsn (synCuni (synCuni (.cv z)))))))
      (synCnc (synCin D (synCima (synCcnv (synCdif R (synCid)))
            (synCsn (synCuni (synCuni (.cv q)))))))
      K p0039
  have p0048 :=
    @gBreq2d (.classEq (.cv z) (.cv q))
      (synCnc (synCin D (synCima (synCcnv (synCdif R (synCid)))
            (synCsn (synCuni (synCuni (.cv z)))))))
      (synCnc (synCin D (synCima (synCcnv (synCdif R (synCid)))
            (synCsn (synCuni (synCuni (.cv q)))))))
      (synCnc (synCin D (synCima (synCcnv (synCdif R (synCid)))
            (synCsn (synCuni (synCuni (.cv y)))))))
      (synClec) p0039
  have p0049 :=
    @gImbi12d (.classEq (.cv z) (.cv q))
      (.classMem (synCnc (synCin D (synCima (synCcnv (synCdif R (synCid)))
              (synCsn (synCuni (synCuni (.cv z))))))) K)
      (.classMem (synCnc (synCin D (synCima (synCcnv (synCdif R (synCid)))
              (synCsn (synCuni (synCuni (.cv q))))))) K)
      (synWbr (synCnc (synCin D (synCima (synCcnv (synCdif R (synCid)))
              (synCsn (synCuni (synCuni (.cv y))))))) (synClec) (synCnc (synCin D
            (synCima (synCcnv (synCdif R (synCid)))
              (synCsn (synCuni (synCuni (.cv z))))))))
      (synWbr (synCnc (synCin D (synCima (synCcnv (synCdif R (synCid)))
              (synCsn (synCuni (synCuni (.cv y))))))) (synClec) (synCnc (synCin D
            (synCima (synCcnv (synCdif R (synCid)))
              (synCsn (synCuni (synCuni (.cv q))))))))
      p0040 p0048
  have p0050 :=
    @gRspcv
      (.imp (.classMem (synCnc (synCin D (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (.cv z))))))) K) (synWbr (synCnc (synCin D
              (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (.cv y))))))) (synClec) (synCnc (synCin D
              (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (.cv z)))))))))
      (.imp (.classMem (synCnc (synCin D (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (.cv q))))))) K) (synWbr (synCnc (synCin D
              (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (.cv y))))))) (synClec) (synCnc (synCin D
              (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (.cv q)))))))))
      z (.cv q) (synCpw1 (synCpw1 D)) dv_cache_0017 dv_cache_0018 dv_cache_0019 p0049
  have p0051 :=
    @gSyl
      (synWa (synWa (synWa (.classMem (synCnc (synCin D
                  (synCima (synCcnv (synCdif R (synCid)))
                    (synCsn (synCuni (synCuni (.cv y))))))) K)
            (synWral z (synCpw1 (synCpw1 D)) (.imp (.classMem (synCnc (synCin D
                      (synCima (synCcnv (synCdif R (synCid)))
                        (synCsn (synCuni (synCuni (.cv z))))))) K) (synWbr (synCnc
                    (synCin D (synCima (synCcnv (synCdif R (synCid)))
                        (synCsn (synCuni (synCuni (.cv y))))))) (synClec) (synCnc
                    (synCin D (synCima (synCcnv (synCdif R (synCid)))
                        (synCsn (synCuni (synCuni (.cv z))))))))))) (.classMem (.cv k) K))
        (synWa (.classMem (.cv q) (synCpw1 (synCpw1 D))) (.classEq (.cv k) (synCnc
              (synCin D (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (synCuni (synCuni (.cv q))))))))))
      (.classMem (.cv q) (synCpw1 (synCpw1 D)))
      (.imp (synWral z (synCpw1 (synCpw1 D)) (.imp (.classMem (synCnc (synCin D
                  (synCima (synCcnv (synCdif R (synCid)))
                    (synCsn (synCuni (synCuni (.cv z))))))) K) (synWbr (synCnc (synCin D
                  (synCima (synCcnv (synCdif R (synCid)))
                    (synCsn (synCuni (synCuni (.cv y))))))) (synClec) (synCnc (synCin D
                  (synCima (synCcnv (synCdif R (synCid)))
                    (synCsn (synCuni (synCuni (.cv z)))))))))) (.imp (.classMem (synCnc
              (synCin D (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (synCuni (synCuni (.cv q))))))) K) (synWbr (synCnc (synCin D
                (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (synCuni (synCuni (.cv y))))))) (synClec) (synCnc (synCin D
                (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (synCuni (synCuni (.cv q))))))))))
      p0032 p0050
  have p0052 :=
    @gMpd
      (synWa (synWa (synWa (.classMem (synCnc (synCin D
                  (synCima (synCcnv (synCdif R (synCid)))
                    (synCsn (synCuni (synCuni (.cv y))))))) K)
            (synWral z (synCpw1 (synCpw1 D)) (.imp (.classMem (synCnc (synCin D
                      (synCima (synCcnv (synCdif R (synCid)))
                        (synCsn (synCuni (synCuni (.cv z))))))) K) (synWbr (synCnc
                    (synCin D (synCima (synCcnv (synCdif R (synCid)))
                        (synCsn (synCuni (synCuni (.cv y))))))) (synClec) (synCnc
                    (synCin D (synCima (synCcnv (synCdif R (synCid)))
                        (synCsn (synCuni (synCuni (.cv z))))))))))) (.classMem (.cv k) K))
        (synWa (.classMem (.cv q) (synCpw1 (synCpw1 D))) (.classEq (.cv k) (synCnc
              (synCin D (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (synCuni (synCuni (.cv q))))))))))
      (synWral z (synCpw1 (synCpw1 D)) (.imp (.classMem (synCnc (synCin D
                (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (synCuni (synCuni (.cv z))))))) K) (synWbr (synCnc (synCin D
                (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (synCuni (synCuni (.cv y))))))) (synClec) (synCnc (synCin D
                (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (synCuni (synCuni (.cv z))))))))))
      (.imp (.classMem (synCnc (synCin D (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (.cv q))))))) K) (synWbr (synCnc (synCin D
              (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (.cv y))))))) (synClec) (synCnc (synCin D
              (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (.cv q)))))))))
      p0030 p0051
  have p0053 :=
    @gMpd
      (synWa (synWa (synWa (.classMem (synCnc (synCin D
                  (synCima (synCcnv (synCdif R (synCid)))
                    (synCsn (synCuni (synCuni (.cv y))))))) K)
            (synWral z (synCpw1 (synCpw1 D)) (.imp (.classMem (synCnc (synCin D
                      (synCima (synCcnv (synCdif R (synCid)))
                        (synCsn (synCuni (synCuni (.cv z))))))) K) (synWbr (synCnc
                    (synCin D (synCima (synCcnv (synCdif R (synCid)))
                        (synCsn (synCuni (synCuni (.cv y))))))) (synClec) (synCnc
                    (synCin D (synCima (synCcnv (synCdif R (synCid)))
                        (synCsn (synCuni (synCuni (.cv z))))))))))) (.classMem (.cv k) K))
        (synWa (.classMem (.cv q) (synCpw1 (synCpw1 D))) (.classEq (.cv k) (synCnc
              (synCin D (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (synCuni (synCuni (.cv q))))))))))
      (.classMem (synCnc (synCin D (synCima (synCcnv (synCdif R (synCid)))
              (synCsn (synCuni (synCuni (.cv q))))))) K)
      (synWbr (synCnc (synCin D (synCima (synCcnv (synCdif R (synCid)))
              (synCsn (synCuni (synCuni (.cv y))))))) (synClec) (synCnc (synCin D
            (synCima (synCcnv (synCdif R (synCid)))
              (synCsn (synCuni (synCuni (.cv q))))))))
      p0025 p0052
  have p0056 :=
    @gBreq2d
      (synWa (synWa (synWa (.classMem (synCnc (synCin D
                  (synCima (synCcnv (synCdif R (synCid)))
                    (synCsn (synCuni (synCuni (.cv y))))))) K)
            (synWral z (synCpw1 (synCpw1 D)) (.imp (.classMem (synCnc (synCin D
                      (synCima (synCcnv (synCdif R (synCid)))
                        (synCsn (synCuni (synCuni (.cv z))))))) K) (synWbr (synCnc
                    (synCin D (synCima (synCcnv (synCdif R (synCid)))
                        (synCsn (synCuni (synCuni (.cv y))))))) (synClec) (synCnc
                    (synCin D (synCima (synCcnv (synCdif R (synCid)))
                        (synCsn (synCuni (synCuni (.cv z))))))))))) (.classMem (.cv k) K))
        (synWa (.classMem (.cv q) (synCpw1 (synCpw1 D))) (.classEq (.cv k) (synCnc
              (synCin D (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (synCuni (synCuni (.cv q))))))))))
      (.cv k)
      (synCnc (synCin D (synCima (synCcnv (synCdif R (synCid)))
            (synCsn (synCuni (synCuni (.cv q)))))))
      (synCnc (synCin D (synCima (synCcnv (synCdif R (synCid)))
            (synCsn (synCuni (synCuni (.cv y)))))))
      (synClec) p0021
  have p0057 :=
    @gBiimprd
      (synWa (synWa (synWa (.classMem (synCnc (synCin D
                  (synCima (synCcnv (synCdif R (synCid)))
                    (synCsn (synCuni (synCuni (.cv y))))))) K)
            (synWral z (synCpw1 (synCpw1 D)) (.imp (.classMem (synCnc (synCin D
                      (synCima (synCcnv (synCdif R (synCid)))
                        (synCsn (synCuni (synCuni (.cv z))))))) K) (synWbr (synCnc
                    (synCin D (synCima (synCcnv (synCdif R (synCid)))
                        (synCsn (synCuni (synCuni (.cv y))))))) (synClec) (synCnc
                    (synCin D (synCima (synCcnv (synCdif R (synCid)))
                        (synCsn (synCuni (synCuni (.cv z))))))))))) (.classMem (.cv k) K))
        (synWa (.classMem (.cv q) (synCpw1 (synCpw1 D))) (.classEq (.cv k) (synCnc
              (synCin D (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (synCuni (synCuni (.cv q))))))))))
      (synWbr (synCnc (synCin D (synCima (synCcnv (synCdif R (synCid)))
              (synCsn (synCuni (synCuni (.cv y))))))) (synClec) (.cv k))
      (synWbr (synCnc (synCin D (synCima (synCcnv (synCdif R (synCid)))
              (synCsn (synCuni (synCuni (.cv y))))))) (synClec) (synCnc (synCin D
            (synCima (synCcnv (synCdif R (synCid)))
              (synCsn (synCuni (synCuni (.cv q))))))))
      p0056
  have p0058 :=
    @gMpd
      (synWa (synWa (synWa (.classMem (synCnc (synCin D
                  (synCima (synCcnv (synCdif R (synCid)))
                    (synCsn (synCuni (synCuni (.cv y))))))) K)
            (synWral z (synCpw1 (synCpw1 D)) (.imp (.classMem (synCnc (synCin D
                      (synCima (synCcnv (synCdif R (synCid)))
                        (synCsn (synCuni (synCuni (.cv z))))))) K) (synWbr (synCnc
                    (synCin D (synCima (synCcnv (synCdif R (synCid)))
                        (synCsn (synCuni (synCuni (.cv y))))))) (synClec) (synCnc
                    (synCin D (synCima (synCcnv (synCdif R (synCid)))
                        (synCsn (synCuni (synCuni (.cv z))))))))))) (.classMem (.cv k) K))
        (synWa (.classMem (.cv q) (synCpw1 (synCpw1 D))) (.classEq (.cv k) (synCnc
              (synCin D (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (synCuni (synCuni (.cv q))))))))))
      (synWbr (synCnc (synCin D (synCima (synCcnv (synCdif R (synCid)))
              (synCsn (synCuni (synCuni (.cv y))))))) (synClec) (synCnc (synCin D
            (synCima (synCcnv (synCdif R (synCid)))
              (synCsn (synCuni (synCuni (.cv q))))))))
      (synWbr (synCnc (synCin D (synCima (synCcnv (synCdif R (synCid)))
              (synCsn (synCuni (synCuni (.cv y))))))) (synClec) (.cv k))
      p0053 p0057
  have p0059 :=
    @gRexlimdvaa
      (synWa (synWa (.classMem (synCnc (synCin D (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (synCuni (synCuni (.cv y))))))) K)
          (synWral z (synCpw1 (synCpw1 D)) (.imp (.classMem (synCnc (synCin D
                    (synCima (synCcnv (synCdif R (synCid)))
                      (synCsn (synCuni (synCuni (.cv z))))))) K) (synWbr (synCnc (synCin D
                    (synCima (synCcnv (synCdif R (synCid)))
                      (synCsn (synCuni (synCuni (.cv y))))))) (synClec) (synCnc (synCin D
                    (synCima (synCcnv (synCdif R (synCid)))
                      (synCsn (synCuni (synCuni (.cv z))))))))))) (.classMem (.cv k) K))
      (.classEq (.cv k) (synCnc (synCin D (synCima (synCcnv (synCdif R (synCid)))
              (synCsn (synCuni (synCuni (.cv q))))))))
      (synWbr (synCnc (synCin D (synCima (synCcnv (synCdif R (synCid)))
              (synCsn (synCuni (synCuni (.cv y))))))) (synClec) (.cv k))
      q (synCpw1 (synCpw1 D)) dv_cache_0020 dv_cache_0021 p0058
  have p0060 :=
    @gMpd
      (synWa (synWa (.classMem (synCnc (synCin D (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (synCuni (synCuni (.cv y))))))) K)
          (synWral z (synCpw1 (synCpw1 D)) (.imp (.classMem (synCnc (synCin D
                    (synCima (synCcnv (synCdif R (synCid)))
                      (synCsn (synCuni (synCuni (.cv z))))))) K) (synWbr (synCnc (synCin D
                    (synCima (synCcnv (synCdif R (synCid)))
                      (synCsn (synCuni (synCuni (.cv y))))))) (synClec) (synCnc (synCin D
                    (synCima (synCcnv (synCdif R (synCid)))
                      (synCsn (synCuni (synCuni (.cv z))))))))))) (.classMem (.cv k) K))
      (synWrex q (synCpw1 (synCpw1 D)) (.classEq (.cv k) (synCnc (synCin D
              (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (.cv q)))))))))
      (synWbr (synCnc (synCin D (synCima (synCcnv (synCdif R (synCid)))
              (synCsn (synCuni (synCuni (.cv y))))))) (synClec) (.cv k))
      p0019 p0059
  have p0061 :=
    @gRalrimiva
      (synWa (.classMem (synCnc (synCin D (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (.cv y))))))) K)
        (synWral z (synCpw1 (synCpw1 D)) (.imp (.classMem (synCnc (synCin D
                  (synCima (synCcnv (synCdif R (synCid)))
                    (synCsn (synCuni (synCuni (.cv z))))))) K) (synWbr (synCnc (synCin D
                  (synCima (synCcnv (synCdif R (synCid)))
                    (synCsn (synCuni (synCuni (.cv y))))))) (synClec) (synCnc (synCin D
                  (synCima (synCcnv (synCdif R (synCid)))
                    (synCsn (synCuni (synCuni (.cv z)))))))))))
      (synWbr (synCnc (synCin D (synCima (synCcnv (synCdif R (synCid)))
              (synCsn (synCuni (synCuni (.cv y))))))) (synClec) (.cv k))
      k K dv_cache_0022 p0060
  have p0062 :=
    @gJca
      (synWa (.classMem (synCnc (synCin D (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (.cv y))))))) K)
        (synWral z (synCpw1 (synCpw1 D)) (.imp (.classMem (synCnc (synCin D
                  (synCima (synCcnv (synCdif R (synCid)))
                    (synCsn (synCuni (synCuni (.cv z))))))) K) (synWbr (synCnc (synCin D
                  (synCima (synCcnv (synCdif R (synCid)))
                    (synCsn (synCuni (synCuni (.cv y))))))) (synClec) (synCnc (synCin D
                  (synCima (synCcnv (synCdif R (synCid)))
                    (synCsn (synCuni (synCuni (.cv z)))))))))))
      (.classMem (synCnc (synCin D (synCima (synCcnv (synCdif R (synCid)))
              (synCsn (synCuni (synCuni (.cv y))))))) K)
      (synWral k K (synWbr (synCnc (synCin D (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (.cv y))))))) (synClec) (.cv k)))
      p0015 p0061
  have p0063 :=
    @gReximi
      (synWa (.classMem (synCnc (synCin D (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (.cv y))))))) K)
        (synWral z (synCpw1 (synCpw1 D)) (.imp (.classMem (synCnc (synCin D
                  (synCima (synCcnv (synCdif R (synCid)))
                    (synCsn (synCuni (synCuni (.cv z))))))) K) (synWbr (synCnc (synCin D
                  (synCima (synCcnv (synCdif R (synCid)))
                    (synCsn (synCuni (synCuni (.cv y))))))) (synClec) (synCnc (synCin D
                  (synCima (synCcnv (synCdif R (synCid)))
                    (synCsn (synCuni (synCuni (.cv z)))))))))))
      (synWa (.classMem (synCnc (synCin D (synCima (synCcnv (synCdif R (synCid)))
                (synCsn (synCuni (synCuni (.cv y))))))) K) (synWral k K (synWbr (synCnc
              (synCin D (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (synCuni (synCuni (.cv y))))))) (synClec) (.cv k))))
      y (synCpw1 (synCpw1 D)) p0062
  have p0064 :=
    @gSyl (synWne K (synC0))
      (synWrex y (synCpw1 (synCpw1 D)) (synWa (.classMem (synCnc (synCin D
                (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (synCuni (synCuni (.cv y))))))) K)
          (synWral z (synCpw1 (synCpw1 D)) (.imp (.classMem (synCnc (synCin D
                    (synCima (synCcnv (synCdif R (synCid)))
                      (synCsn (synCuni (synCuni (.cv z))))))) K) (synWbr (synCnc (synCin D
                    (synCima (synCcnv (synCdif R (synCid)))
                      (synCsn (synCuni (synCuni (.cv y))))))) (synClec) (synCnc (synCin D
                    (synCima (synCcnv (synCdif R (synCid)))
                      (synCsn (synCuni (synCuni (.cv z))))))))))))
      (synWrex y (synCpw1 (synCpw1 D)) (synWa (.classMem (synCnc (synCin D
                (synCima (synCcnv (synCdif R (synCid)))
                  (synCsn (synCuni (synCuni (.cv y))))))) K) (synWral k K (synWbr (synCnc
                (synCin D (synCima (synCcnv (synCdif R (synCid)))
                    (synCsn (synCuni (synCuni (.cv y))))))) (synClec) (.cv k)))))
      p0014 p0063
  exact p0064


end NFChoice.DirectNominalPrf.WPPReplay

end
