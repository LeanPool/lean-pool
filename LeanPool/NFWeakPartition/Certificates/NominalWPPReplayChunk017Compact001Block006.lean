/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NominalWPPReplayChunk017Compact001Block005

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NominalWPPReplayChunk017Compact001Part025`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_hncodecmpsetconnexndv (A : Class) :
    Nominal.NPrf
      (.imp (.classMem A (syn_cvv))
        (syn_wbr (syn_chncodecmpset A) (syn_cconnex) (syn_chwcn A))) :=
  by
  let proofSupport : Finset Var := A.fv
  let u : Var := freshVar proofSupport 0
  let v : Var := freshVar proofSupport 1
  let h : Var := freshVar proofSupport 2
  let x : Var := freshVar proofSupport 3
  have fresh_u : u ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_u_not_A : u ∉ A.fv := by
    intro h
    exact fresh_u (h)
  have fresh_v : v ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_v_not_A : v ∉ A.fv := by
    intro h
    exact fresh_v (h)
  have fresh_h : h ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_h_not_A : h ∉ A.fv := by
    intro h
    exact fresh_h (h)
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (h)
  have fresh_u_ne_v : u ≠ v :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_u_ne_h : u ≠ h :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_h_ne_u : h ≠ u := Ne.symm fresh_u_ne_h
  have fresh_u_ne_x : u ≠ x :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_x_ne_u : x ≠ u := Ne.symm fresh_u_ne_x
  have fresh_v_ne_h : v ≠ h :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_h_ne_v : h ≠ v := Ne.symm fresh_v_ne_h
  have fresh_v_ne_x : v ≠ x :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_x_ne_v : x ≠ v := Ne.symm fresh_v_ne_x
  have fresh_h_ne_x : h ≠ x :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have dv_cache_0001 : h ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_h_not_A, not_false_eq_true])
  have dv_cache_0002 : u ∉ (A).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_u_not_A, not_false_eq_true])
  have dv_cache_0003 : v ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_v_not_A, not_false_eq_true])
  have dv_cache_0004 : x ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_A, not_false_eq_true])
  have dv_cache_0005 : h ≠ u :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show h ≠ u from (by exact fresh_h_ne_u))
  have dv_cache_0006 : h ≠ v :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show h ≠ v from (by exact fresh_h_ne_v))
  have dv_cache_0007 : h ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact (show h ≠ x from (by exact fresh_h_ne_x))
  have dv_cache_0008 : u ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact (show u ≠ x from (by exact fresh_u_ne_x))
  have dv_cache_0009 : v ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (show v ≠ x from (by exact fresh_v_ne_x))
  have dv_cache_0010 :
    h ∉
      ((syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
          (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
            (syn_c0)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union,
          Finset.mem_singleton, fresh_h_ne_u, fresh_h_not_A, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0011 :
    h ∉
      ((syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
          (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
            (syn_c0)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union,
          Finset.mem_singleton, fresh_h_ne_v, fresh_h_not_A, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0012 :
    x ∉
      ((syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
          (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
            (syn_c0)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_u, fresh_x_not_A, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0013 :
    x ∉
      ((syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
          (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
            (syn_c0)))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_v, fresh_x_not_A, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0014 :
    h ∉
      ((Wff.classMem (.cv x) (syn_cfv (syn_c2nd)
            (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact
      (by
        have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union,
          Finset.mem_singleton, fresh_h_ne_x, fresh_h_ne_v, fresh_h_not_A,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0015 :
    h ∉
      ((syn_chnwcutcode (syn_cfv (syn_c1st) (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0)))) (syn_cfv (syn_c2nd)
            (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0)))) (.cv x))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact
      (by
        have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutcode,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union,
          Finset.mem_singleton, fresh_h_ne_x, fresh_h_ne_v, fresh_h_not_A,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0016 :
    h ∉
      ((Wff.classMem (.cv x) (syn_cfv (syn_c2nd)
            (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact
      (by
        have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union,
          Finset.mem_singleton, fresh_h_ne_x, fresh_h_ne_u, fresh_h_not_A,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0017 :
    h ∉
      ((syn_chnwcutcode (syn_cfv (syn_c1st) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0)))) (syn_cfv (syn_c2nd)
            (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0)))) (.cv x))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact
      (by
        have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutcode,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union,
          Finset.mem_singleton, fresh_h_ne_x, fresh_h_ne_u, fresh_h_not_A,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0018 : u ∉ ((syn_chwcn A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
          fresh_u_not_A, not_false_eq_true])
  have dv_cache_0019 : v ∉ ((syn_chwcn A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
          fresh_v_not_A, not_false_eq_true])
  have dv_cache_0020 : u ∉ ((syn_chncodecmpset A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodecmpset,
          fresh_u_not_A, not_false_eq_true])
  have dv_cache_0021 : v ∉ ((syn_chncodecmpset A)).fv :=
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
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodecmpset,
          fresh_v_not_A, not_false_eq_true])
  have dv_cache_0022 : u ∉ ((Wff.classMem A (syn_cvv))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
          fresh_u_not_A, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0023 : v ∉ ((Wff.classMem A (syn_cvv))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
          fresh_v_not_A, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0024 : u ≠ v :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
    exact (show u ≠ v from (by exact fresh_u_ne_v))
  have p0000 := @g_hncodecmpsetexg A
  have p0001 := @g_hwcnexg A
  have p0002 :=
    @g_simp2 (.classMem A (syn_cvv)) (.classMem (.cv u) (syn_chwcn A))
      (.classMem (.cv v) (syn_chwcn A))
  have p0003 :=
    @g_simp3 (.classMem A (syn_cvv)) (.classMem (.cv u) (syn_chwcn A))
      (.classMem (.cv v) (syn_chwcn A))
  have p0004 :=
    @g_jca
      (syn_w3a (.classMem A (syn_cvv)) (.classMem (.cv u) (syn_chwcn A))
        (.classMem (.cv v) (syn_chwcn A)))
      (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)) p0002 p0003
  have p0005 :=
    @g_hncodecomparisontotalndv x v u A h dv_cache_0001 dv_cache_0002 dv_cache_0003
      dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
  have p0006 := @g_hncodetotalleftmemndv u A dv_cache_0002
  have p0007 :=
    @g_id
      (.classMem (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
          (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
        (syn_chwcn A))
  have p0008 := @g_hncodetotalrightmemndv v A dv_cache_0003
  have p0009 :=
    @g_a1i
      (.classMem (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
          (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
        (syn_chwcn A))
      (.classMem (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
          (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
        (syn_chwcn A))
      p0008
  have p0010 :=
    @g_jca
      (.classMem (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
          (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
        (syn_chwcn A))
      (.classMem (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
          (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
        (syn_chwcn A))
      (.classMem (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
          (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
        (syn_chwcn A))
      p0007 p0009
  have p0011 := Nominal.mp p0006 p0010
  have p0012 :=
    @g_hwnisodirectisobclndv A
      (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
        (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
      (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
        (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
      h dv_cache_0001 dv_cache_0010 dv_cache_0011
  have p0013 := Nominal.mp p0011 p0012
  have p0014 :=
    @g_biimpri
      (syn_wbr (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
          (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
        (syn_chwniso A) (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
          (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
      (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st)
            (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0)))) (syn_cfv (syn_c1st)
            (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0)))) (syn_cfv (syn_c2nd)
            (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0)))) (syn_cfv (syn_c2nd)
            (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0))))))
      p0013
  have p0015 :=
    @g_orc
      (syn_wbr (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
          (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
        (syn_chwniso A) (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
          (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
      (syn_wrex x (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
        (syn_wbr (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
          (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st)
              (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
                (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                  (syn_c0)))) (syn_cfv (syn_c2nd)
              (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
                (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                  (syn_c0)))) (.cv x))))
  have p0016 :=
    @g_syl
      (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st)
            (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0)))) (syn_cfv (syn_c1st)
            (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0)))) (syn_cfv (syn_c2nd)
            (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0)))) (syn_cfv (syn_c2nd)
            (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0))))))
      (syn_wbr (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
          (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
        (syn_chwniso A) (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
          (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
      (syn_wo (syn_wbr (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
          (syn_chwniso A) (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
        (syn_wrex x (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0)))) (syn_wbr (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0))) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st)
                (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
                  (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                    (syn_c0)))) (syn_cfv (syn_c2nd)
                (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
                  (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                    (syn_c0)))) (.cv x)))))
      p0014 p0015
  have p0023 :=
    @g_hncodecmpsetstrictcutsemclndv x A
      (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
        (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
      (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
        (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
      dv_cache_0004 dv_cache_0012 dv_cache_0013
  have p0024 := Nominal.mp p0011 p0023
  have p0025 :=
    @g_biimpri
      (syn_wbr (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
          (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
        (syn_chncodecmpset A) (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
          (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
      (syn_wo (syn_wbr (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
          (syn_chwniso A) (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
        (syn_wrex x (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0)))) (syn_wbr (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0))) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st)
                (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
                  (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                    (syn_c0)))) (syn_cfv (syn_c2nd)
                (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
                  (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                    (syn_c0)))) (.cv x)))))
      p0024
  have p0026 :=
    @g_syl
      (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st)
            (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0)))) (syn_cfv (syn_c1st)
            (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0)))) (syn_cfv (syn_c2nd)
            (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0)))) (syn_cfv (syn_c2nd)
            (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0))))))
      (syn_wo (syn_wbr (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
          (syn_chwniso A) (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
        (syn_wrex x (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0)))) (syn_wbr (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0))) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st)
                (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
                  (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                    (syn_c0)))) (syn_cfv (syn_c2nd)
                (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
                  (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                    (syn_c0)))) (.cv x)))))
      (syn_wbr (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
          (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
        (syn_chncodecmpset A) (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
          (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
      p0016 p0025
  have p0027 :=
    @g_orc
      (syn_wbr (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
          (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
        (syn_chncodecmpset A) (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
          (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
      (syn_wbr (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
          (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
        (syn_chncodecmpset A) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
          (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
  have p0028 :=
    @g_syl
      (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st)
            (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0)))) (syn_cfv (syn_c1st)
            (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0)))) (syn_cfv (syn_c2nd)
            (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0)))) (syn_cfv (syn_c2nd)
            (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0))))))
      (syn_wbr (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
          (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
        (syn_chncodecmpset A) (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
          (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
      (syn_wo (syn_wbr (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
          (syn_chncodecmpset A) (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
        (syn_wbr (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
          (syn_chncodecmpset A) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
              (syn_c0)))))
      p0026 p0027
  have p0030 :=
    @g_hwcnweclndv A
      (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
        (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
  have p0031 := Nominal.mp p0008 p0030
  have p0032 :=
    @g_wecutisogencodeparts x
      (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
          (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
      (syn_cfv (syn_c1st) (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
          (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
      p0031
  have p0033 :=
    @g_simpld
      (.classMem (.cv x) (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
              (syn_c0)))))
      (.classEq (syn_cfv (syn_c1st) (syn_chnwcutcode (syn_cfv (syn_c1st)
              (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
                (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                  (syn_c0)))) (syn_cfv (syn_c2nd)
              (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
                (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                  (syn_c0)))) (.cv x))) (syn_cin (syn_cfv (syn_c1st)
            (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0)))) (syn_cxp (syn_cin (syn_cfv (syn_c2nd)
                (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
                  (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                    (syn_c0)))) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st)
                      (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v) (syn_cop
                          (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                          (syn_c0)))) (syn_cid))) (syn_csn (.cv x)))) (syn_cin
              (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
                  (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                    (syn_c0)))) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st)
                      (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v) (syn_cop
                          (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                          (syn_c0)))) (syn_cid))) (syn_csn (.cv x)))))))
      (.classEq (syn_cfv (syn_c2nd) (syn_chnwcutcode (syn_cfv (syn_c1st)
              (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
                (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                  (syn_c0)))) (syn_cfv (syn_c2nd)
              (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
                (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                  (syn_c0)))) (.cv x))) (syn_cin (syn_cfv (syn_c2nd)
            (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0)))) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st)
                  (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v) (syn_cop
                      (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                      (syn_c0)))) (syn_cid))) (syn_csn (.cv x)))))
      p0032
  have p0034 :=
    @g_eqcomd
      (.classMem (.cv x) (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
              (syn_c0)))))
      (syn_cfv (syn_c1st) (syn_chnwcutcode (syn_cfv (syn_c1st)
            (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0)))) (syn_cfv (syn_c2nd)
            (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0)))) (.cv x)))
      (syn_cin (syn_cfv (syn_c1st) (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
        (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
                (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                  (syn_c0)))) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st)
                    (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v) (syn_cop
                        (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                        (syn_c0)))) (syn_cid))) (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd)
              (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
                (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                  (syn_c0)))) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st)
                    (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v) (syn_cop
                        (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                        (syn_c0)))) (syn_cid))) (syn_csn (.cv x))))))
      p0033
  have p0035 :=
    @g_isoeq3
      (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
          (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
      (syn_cin (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
        (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st)
                (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
                  (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                    (syn_c0)))) (syn_cid))) (syn_csn (.cv x))))
      (syn_cfv (syn_c1st) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
          (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
      (syn_cin (syn_cfv (syn_c1st) (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
        (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
                (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                  (syn_c0)))) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st)
                    (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v) (syn_cop
                        (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                        (syn_c0)))) (syn_cid))) (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd)
              (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
                (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                  (syn_c0)))) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st)
                    (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v) (syn_cop
                        (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                        (syn_c0)))) (syn_cid))) (syn_csn (.cv x))))))
      (syn_cfv (syn_c1st) (syn_chnwcutcode (syn_cfv (syn_c1st)
            (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0)))) (syn_cfv (syn_c2nd)
            (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0)))) (.cv x)))
      (.cv h)
  have p0036 :=
    @g_syl
      (.classMem (.cv x) (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
              (syn_c0)))))
      (.classEq (syn_cin (syn_cfv (syn_c1st) (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0)))) (syn_cxp (syn_cin (syn_cfv (syn_c2nd)
                (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
                  (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                    (syn_c0)))) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st)
                      (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v) (syn_cop
                          (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                          (syn_c0)))) (syn_cid))) (syn_csn (.cv x)))) (syn_cin
              (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
                  (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                    (syn_c0)))) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st)
                      (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v) (syn_cop
                          (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                          (syn_c0)))) (syn_cid))) (syn_csn (.cv x)))))) (syn_cfv (syn_c1st)
          (syn_chnwcutcode (syn_cfv (syn_c1st)
              (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
                (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                  (syn_c0)))) (syn_cfv (syn_c2nd)
              (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
                (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                  (syn_c0)))) (.cv x))))
      (syn_wb (syn_wiso (.cv h) (syn_cfv (syn_c1st)
            (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0)))) (syn_cin (syn_cfv (syn_c1st)
              (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
                (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                  (syn_c0)))) (syn_cxp (syn_cin (syn_cfv (syn_c2nd)
                  (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v) (syn_cop
                      (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                      (syn_c0)))) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st)
                        (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v) (syn_cop
                            (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                            (syn_c0)))) (syn_cid))) (syn_csn (.cv x)))) (syn_cin
                (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v) (syn_cop
                      (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                      (syn_c0)))) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st)
                        (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v) (syn_cop
                            (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                            (syn_c0)))) (syn_cid))) (syn_csn (.cv x)))))) (syn_cfv (syn_c2nd)
            (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0)))) (syn_cin (syn_cfv (syn_c2nd)
              (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
                (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                  (syn_c0)))) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st)
                    (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v) (syn_cop
                        (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                        (syn_c0)))) (syn_cid))) (syn_csn (.cv x))))) (syn_wiso (.cv h)
          (syn_cfv (syn_c1st) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0)))) (syn_cfv (syn_c1st) (syn_chnwcutcode (syn_cfv (syn_c1st)
                (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
                  (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                    (syn_c0)))) (syn_cfv (syn_c2nd)
                (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
                  (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                    (syn_c0)))) (.cv x))) (syn_cfv (syn_c2nd)
            (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0)))) (syn_cin (syn_cfv (syn_c2nd)
              (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
                (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                  (syn_c0)))) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st)
                    (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v) (syn_cop
                        (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                        (syn_c0)))) (syn_cid))) (syn_csn (.cv x))))))
      p0034 p0035
  have p0041 :=
    @g_simprd
      (.classMem (.cv x) (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
              (syn_c0)))))
      (.classEq (syn_cfv (syn_c1st) (syn_chnwcutcode (syn_cfv (syn_c1st)
              (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
                (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                  (syn_c0)))) (syn_cfv (syn_c2nd)
              (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
                (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                  (syn_c0)))) (.cv x))) (syn_cin (syn_cfv (syn_c1st)
            (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0)))) (syn_cxp (syn_cin (syn_cfv (syn_c2nd)
                (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
                  (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                    (syn_c0)))) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st)
                      (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v) (syn_cop
                          (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                          (syn_c0)))) (syn_cid))) (syn_csn (.cv x)))) (syn_cin
              (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
                  (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                    (syn_c0)))) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st)
                      (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v) (syn_cop
                          (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                          (syn_c0)))) (syn_cid))) (syn_csn (.cv x)))))))
      (.classEq (syn_cfv (syn_c2nd) (syn_chnwcutcode (syn_cfv (syn_c1st)
              (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
                (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                  (syn_c0)))) (syn_cfv (syn_c2nd)
              (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
                (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                  (syn_c0)))) (.cv x))) (syn_cin (syn_cfv (syn_c2nd)
            (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0)))) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st)
                  (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v) (syn_cop
                      (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                      (syn_c0)))) (syn_cid))) (syn_csn (.cv x)))))
      p0032
  have p0042 :=
    @g_eqcomd
      (.classMem (.cv x) (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
              (syn_c0)))))
      (syn_cfv (syn_c2nd) (syn_chnwcutcode (syn_cfv (syn_c1st)
            (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0)))) (syn_cfv (syn_c2nd)
            (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0)))) (.cv x)))
      (syn_cin (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
        (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st)
                (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
                  (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                    (syn_c0)))) (syn_cid))) (syn_csn (.cv x))))
      p0041
  have p0043 :=
    @g_isoeq5
      (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
          (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
      (syn_cin (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
        (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st)
                (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
                  (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                    (syn_c0)))) (syn_cid))) (syn_csn (.cv x))))
      (syn_cfv (syn_c2nd) (syn_chnwcutcode (syn_cfv (syn_c1st)
            (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0)))) (syn_cfv (syn_c2nd)
            (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0)))) (.cv x)))
      (syn_cfv (syn_c1st) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
          (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
      (syn_cfv (syn_c1st) (syn_chnwcutcode (syn_cfv (syn_c1st)
            (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0)))) (syn_cfv (syn_c2nd)
            (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0)))) (.cv x)))
      (.cv h)
  have p0044 :=
    @g_syl
      (.classMem (.cv x) (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
              (syn_c0)))))
      (.classEq (syn_cin (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0)))) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st)
                  (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v) (syn_cop
                      (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                      (syn_c0)))) (syn_cid))) (syn_csn (.cv x)))) (syn_cfv (syn_c2nd)
          (syn_chnwcutcode (syn_cfv (syn_c1st)
              (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
                (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                  (syn_c0)))) (syn_cfv (syn_c2nd)
              (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
                (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                  (syn_c0)))) (.cv x))))
      (syn_wb (syn_wiso (.cv h) (syn_cfv (syn_c1st)
            (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0)))) (syn_cfv (syn_c1st) (syn_chnwcutcode (syn_cfv (syn_c1st)
                (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
                  (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                    (syn_c0)))) (syn_cfv (syn_c2nd)
                (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
                  (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                    (syn_c0)))) (.cv x))) (syn_cfv (syn_c2nd)
            (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0)))) (syn_cin (syn_cfv (syn_c2nd)
              (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
                (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                  (syn_c0)))) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st)
                    (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v) (syn_cop
                        (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                        (syn_c0)))) (syn_cid))) (syn_csn (.cv x))))) (syn_wiso (.cv h)
          (syn_cfv (syn_c1st) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0)))) (syn_cfv (syn_c1st) (syn_chnwcutcode (syn_cfv (syn_c1st)
                (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
                  (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                    (syn_c0)))) (syn_cfv (syn_c2nd)
                (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
                  (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                    (syn_c0)))) (.cv x))) (syn_cfv (syn_c2nd)
            (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0)))) (syn_cfv (syn_c2nd) (syn_chnwcutcode (syn_cfv (syn_c1st)
                (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
                  (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                    (syn_c0)))) (syn_cfv (syn_c2nd)
                (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
                  (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                    (syn_c0)))) (.cv x)))))
      p0042 p0043
  have p0045 :=
    @g_bitrd
      (.classMem (.cv x) (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
              (syn_c0)))))
      (syn_wiso (.cv h) (syn_cfv (syn_c1st) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
        (syn_cin (syn_cfv (syn_c1st) (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0)))) (syn_cxp (syn_cin (syn_cfv (syn_c2nd)
                (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
                  (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                    (syn_c0)))) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st)
                      (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v) (syn_cop
                          (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                          (syn_c0)))) (syn_cid))) (syn_csn (.cv x)))) (syn_cin
              (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
                  (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                    (syn_c0)))) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st)
                      (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v) (syn_cop
                          (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                          (syn_c0)))) (syn_cid))) (syn_csn (.cv x)))))) (syn_cfv (syn_c2nd)
          (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
        (syn_cin (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0)))) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st)
                  (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v) (syn_cop
                      (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                      (syn_c0)))) (syn_cid))) (syn_csn (.cv x)))))
      (syn_wiso (.cv h) (syn_cfv (syn_c1st) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
        (syn_cfv (syn_c1st) (syn_chnwcutcode (syn_cfv (syn_c1st)
              (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
                (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                  (syn_c0)))) (syn_cfv (syn_c2nd)
              (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
                (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                  (syn_c0)))) (.cv x))) (syn_cfv (syn_c2nd)
          (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
        (syn_cin (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0)))) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st)
                  (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v) (syn_cop
                      (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                      (syn_c0)))) (syn_cid))) (syn_csn (.cv x)))))
      (syn_wiso (.cv h) (syn_cfv (syn_c1st) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
        (syn_cfv (syn_c1st) (syn_chnwcutcode (syn_cfv (syn_c1st)
              (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
                (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                  (syn_c0)))) (syn_cfv (syn_c2nd)
              (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
                (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                  (syn_c0)))) (.cv x))) (syn_cfv (syn_c2nd)
          (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
        (syn_cfv (syn_c2nd) (syn_chnwcutcode (syn_cfv (syn_c1st)
              (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
                (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                  (syn_c0)))) (syn_cfv (syn_c2nd)
              (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
                (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                  (syn_c0)))) (.cv x))))
      p0036 p0044
  have p0046 :=
    @g_exbidv
      (.classMem (.cv x) (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
              (syn_c0)))))
      (syn_wiso (.cv h) (syn_cfv (syn_c1st) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
        (syn_cin (syn_cfv (syn_c1st) (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0)))) (syn_cxp (syn_cin (syn_cfv (syn_c2nd)
                (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
                  (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                    (syn_c0)))) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st)
                      (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v) (syn_cop
                          (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                          (syn_c0)))) (syn_cid))) (syn_csn (.cv x)))) (syn_cin
              (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
                  (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                    (syn_c0)))) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st)
                      (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v) (syn_cop
                          (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                          (syn_c0)))) (syn_cid))) (syn_csn (.cv x)))))) (syn_cfv (syn_c2nd)
          (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
        (syn_cin (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0)))) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st)
                  (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v) (syn_cop
                      (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                      (syn_c0)))) (syn_cid))) (syn_csn (.cv x)))))
      (syn_wiso (.cv h) (syn_cfv (syn_c1st) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
        (syn_cfv (syn_c1st) (syn_chnwcutcode (syn_cfv (syn_c1st)
              (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
                (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                  (syn_c0)))) (syn_cfv (syn_c2nd)
              (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
                (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                  (syn_c0)))) (.cv x))) (syn_cfv (syn_c2nd)
          (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
        (syn_cfv (syn_c2nd) (syn_chnwcutcode (syn_cfv (syn_c1st)
              (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
                (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                  (syn_c0)))) (syn_cfv (syn_c2nd)
              (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
                (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                  (syn_c0)))) (.cv x))))
      h dv_cache_0014 p0045
  have p0048 :=
    @g_a1i
      (.classMem (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
          (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
        (syn_chwcn A))
      (.classMem (.cv x) (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
              (syn_c0)))))
      p0006
  have p0052 :=
    @g_hnwcutcodecnclndv (.cv x)
      (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
          (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
      (syn_cfv (syn_c1st) (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
          (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
      p0031
  have p0054 :=
    @g_hwcnbaseclndv A
      (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
        (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
  have p0055 := Nominal.mp p0008 p0054
  have p0056 :=
    @g_hwcnssbase A
      (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
          (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
      p0055
  have p0057 :=
    @g_ssel
      (syn_chwcn (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
              (syn_c0)))))
      (syn_chwcn A)
      (syn_chnwcutcode (syn_cfv (syn_c1st) (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
        (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
        (.cv x))
  have p0058 := Nominal.mp p0056 p0057
  have p0059 :=
    @g_syl
      (.classMem (.cv x) (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
              (syn_c0)))))
      (.classMem (syn_chnwcutcode (syn_cfv (syn_c1st)
            (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0)))) (syn_cfv (syn_c2nd)
            (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0)))) (.cv x)) (syn_chwcn (syn_cfv (syn_c2nd)
            (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0))))))
      (.classMem (syn_chnwcutcode (syn_cfv (syn_c1st)
            (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0)))) (syn_cfv (syn_c2nd)
            (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0)))) (.cv x)) (syn_chwcn A))
      p0052 p0058
  have p0060 :=
    @g_jca
      (.classMem (.cv x) (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
              (syn_c0)))))
      (.classMem (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
          (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
        (syn_chwcn A))
      (.classMem (syn_chnwcutcode (syn_cfv (syn_c1st)
            (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0)))) (syn_cfv (syn_c2nd)
            (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0)))) (.cv x)) (syn_chwcn A))
      p0048 p0059
  have p0061 :=
    @g_hwnisodirectisobclndv A
      (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
        (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
      (syn_chnwcutcode (syn_cfv (syn_c1st) (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
        (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
        (.cv x))
      h dv_cache_0001 dv_cache_0010 dv_cache_0015
  have p0062 :=
    @g_syl
      (.classMem (.cv x) (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
              (syn_c0)))))
      (syn_wa (.classMem (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
          (syn_chwcn A)) (.classMem (syn_chnwcutcode (syn_cfv (syn_c1st)
              (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
                (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                  (syn_c0)))) (syn_cfv (syn_c2nd)
              (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
                (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                  (syn_c0)))) (.cv x)) (syn_chwcn A)))
      (syn_wb (syn_wbr (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
          (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st)
              (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
                (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                  (syn_c0)))) (syn_cfv (syn_c2nd)
              (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
                (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                  (syn_c0)))) (.cv x))) (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st)
              (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
                (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                  (syn_c0)))) (syn_cfv (syn_c1st) (syn_chnwcutcode (syn_cfv (syn_c1st)
                  (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v) (syn_cop
                      (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                      (syn_c0)))) (syn_cfv (syn_c2nd)
                  (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v) (syn_cop
                      (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                      (syn_c0)))) (.cv x))) (syn_cfv (syn_c2nd)
              (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
                (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                  (syn_c0)))) (syn_cfv (syn_c2nd) (syn_chnwcutcode (syn_cfv (syn_c1st)
                  (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v) (syn_cop
                      (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                      (syn_c0)))) (syn_cfv (syn_c2nd)
                  (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v) (syn_cop
                      (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                      (syn_c0)))) (.cv x))))))
      p0060 p0061
  have p0063 :=
    @g_bicomd
      (.classMem (.cv x) (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
              (syn_c0)))))
      (syn_wbr (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
          (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
        (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st)
            (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0)))) (syn_cfv (syn_c2nd)
            (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0)))) (.cv x)))
      (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st)
            (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0)))) (syn_cfv (syn_c1st) (syn_chnwcutcode (syn_cfv (syn_c1st)
                (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
                  (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                    (syn_c0)))) (syn_cfv (syn_c2nd)
                (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
                  (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                    (syn_c0)))) (.cv x))) (syn_cfv (syn_c2nd)
            (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0)))) (syn_cfv (syn_c2nd) (syn_chnwcutcode (syn_cfv (syn_c1st)
                (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
                  (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                    (syn_c0)))) (syn_cfv (syn_c2nd)
                (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
                  (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                    (syn_c0)))) (.cv x)))))
      p0062
  have p0064 :=
    @g_bitrd
      (.classMem (.cv x) (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
              (syn_c0)))))
      (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st)
            (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0)))) (syn_cin (syn_cfv (syn_c1st)
              (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
                (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                  (syn_c0)))) (syn_cxp (syn_cin (syn_cfv (syn_c2nd)
                  (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v) (syn_cop
                      (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                      (syn_c0)))) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st)
                        (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v) (syn_cop
                            (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                            (syn_c0)))) (syn_cid))) (syn_csn (.cv x)))) (syn_cin
                (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v) (syn_cop
                      (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                      (syn_c0)))) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st)
                        (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v) (syn_cop
                            (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                            (syn_c0)))) (syn_cid))) (syn_csn (.cv x)))))) (syn_cfv (syn_c2nd)
            (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0)))) (syn_cin (syn_cfv (syn_c2nd)
              (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
                (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                  (syn_c0)))) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st)
                    (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v) (syn_cop
                        (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                        (syn_c0)))) (syn_cid))) (syn_csn (.cv x))))))
      (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st)
            (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0)))) (syn_cfv (syn_c1st) (syn_chnwcutcode (syn_cfv (syn_c1st)
                (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
                  (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                    (syn_c0)))) (syn_cfv (syn_c2nd)
                (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
                  (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                    (syn_c0)))) (.cv x))) (syn_cfv (syn_c2nd)
            (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0)))) (syn_cfv (syn_c2nd) (syn_chnwcutcode (syn_cfv (syn_c1st)
                (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
                  (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                    (syn_c0)))) (syn_cfv (syn_c2nd)
                (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
                  (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                    (syn_c0)))) (.cv x)))))
      (syn_wbr (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
          (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
        (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st)
            (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0)))) (syn_cfv (syn_c2nd)
            (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0)))) (.cv x)))
      p0046 p0063
  have p0065 :=
    @g_rexbiia
      (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st)
            (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0)))) (syn_cin (syn_cfv (syn_c1st)
              (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
                (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                  (syn_c0)))) (syn_cxp (syn_cin (syn_cfv (syn_c2nd)
                  (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v) (syn_cop
                      (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                      (syn_c0)))) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st)
                        (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v) (syn_cop
                            (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                            (syn_c0)))) (syn_cid))) (syn_csn (.cv x)))) (syn_cin
                (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v) (syn_cop
                      (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                      (syn_c0)))) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st)
                        (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v) (syn_cop
                            (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                            (syn_c0)))) (syn_cid))) (syn_csn (.cv x)))))) (syn_cfv (syn_c2nd)
            (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0)))) (syn_cin (syn_cfv (syn_c2nd)
              (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
                (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                  (syn_c0)))) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st)
                    (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v) (syn_cop
                        (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                        (syn_c0)))) (syn_cid))) (syn_csn (.cv x))))))
      (syn_wbr (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
          (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
        (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st)
            (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0)))) (syn_cfv (syn_c2nd)
            (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0)))) (.cv x)))
      x
      (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
          (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
      p0064
  have p0066 :=
    @g_biimpi
      (syn_wrex x (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
        (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st)
              (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
                (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                  (syn_c0)))) (syn_cin (syn_cfv (syn_c1st)
                (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
                  (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                    (syn_c0)))) (syn_cxp (syn_cin (syn_cfv (syn_c2nd)
                    (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v) (syn_cop
                        (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                        (syn_c0)))) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st)
                          (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v) (syn_cop
                              (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                              (syn_c0)))) (syn_cid))) (syn_csn (.cv x)))) (syn_cin
                  (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
                      (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                        (syn_c0)))) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st)
                          (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v) (syn_cop
                              (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                              (syn_c0)))) (syn_cid))) (syn_csn (.cv x)))))) (syn_cfv (syn_c2nd)
              (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
                (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                  (syn_c0)))) (syn_cin (syn_cfv (syn_c2nd)
                (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
                  (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                    (syn_c0)))) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st)
                      (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v) (syn_cop
                          (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                          (syn_c0)))) (syn_cid))) (syn_csn (.cv x)))))))
      (syn_wrex x (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
        (syn_wbr (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
          (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st)
              (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
                (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                  (syn_c0)))) (syn_cfv (syn_c2nd)
              (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
                (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                  (syn_c0)))) (.cv x))))
      p0065
  have p0067 :=
    @g_olc
      (syn_wrex x (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
        (syn_wbr (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
          (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st)
              (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
                (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                  (syn_c0)))) (syn_cfv (syn_c2nd)
              (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
                (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                  (syn_c0)))) (.cv x))))
      (syn_wbr (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
          (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
        (syn_chwniso A) (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
          (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
  have p0068 :=
    @g_syl
      (syn_wrex x (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
        (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st)
              (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
                (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                  (syn_c0)))) (syn_cin (syn_cfv (syn_c1st)
                (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
                  (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                    (syn_c0)))) (syn_cxp (syn_cin (syn_cfv (syn_c2nd)
                    (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v) (syn_cop
                        (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                        (syn_c0)))) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st)
                          (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v) (syn_cop
                              (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                              (syn_c0)))) (syn_cid))) (syn_csn (.cv x)))) (syn_cin
                  (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
                      (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                        (syn_c0)))) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st)
                          (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v) (syn_cop
                              (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                              (syn_c0)))) (syn_cid))) (syn_csn (.cv x)))))) (syn_cfv (syn_c2nd)
              (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
                (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                  (syn_c0)))) (syn_cin (syn_cfv (syn_c2nd)
                (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
                  (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                    (syn_c0)))) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st)
                      (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v) (syn_cop
                          (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                          (syn_c0)))) (syn_cid))) (syn_csn (.cv x)))))))
      (syn_wrex x (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
        (syn_wbr (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
          (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st)
              (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
                (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                  (syn_c0)))) (syn_cfv (syn_c2nd)
              (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
                (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                  (syn_c0)))) (.cv x))))
      (syn_wo (syn_wbr (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
          (syn_chwniso A) (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
        (syn_wrex x (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0)))) (syn_wbr (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0))) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st)
                (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
                  (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                    (syn_c0)))) (syn_cfv (syn_c2nd)
                (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
                  (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                    (syn_c0)))) (.cv x)))))
      p0066 p0067
  have p0078 :=
    @g_syl
      (syn_wrex x (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
        (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st)
              (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
                (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                  (syn_c0)))) (syn_cin (syn_cfv (syn_c1st)
                (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
                  (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                    (syn_c0)))) (syn_cxp (syn_cin (syn_cfv (syn_c2nd)
                    (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v) (syn_cop
                        (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                        (syn_c0)))) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st)
                          (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v) (syn_cop
                              (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                              (syn_c0)))) (syn_cid))) (syn_csn (.cv x)))) (syn_cin
                  (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
                      (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                        (syn_c0)))) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st)
                          (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v) (syn_cop
                              (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                              (syn_c0)))) (syn_cid))) (syn_csn (.cv x)))))) (syn_cfv (syn_c2nd)
              (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
                (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                  (syn_c0)))) (syn_cin (syn_cfv (syn_c2nd)
                (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
                  (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                    (syn_c0)))) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st)
                      (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v) (syn_cop
                          (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                          (syn_c0)))) (syn_cid))) (syn_csn (.cv x)))))))
      (syn_wo (syn_wbr (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
          (syn_chwniso A) (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
        (syn_wrex x (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0)))) (syn_wbr (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0))) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st)
                (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
                  (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                    (syn_c0)))) (syn_cfv (syn_c2nd)
                (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
                  (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                    (syn_c0)))) (.cv x)))))
      (syn_wbr (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
          (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
        (syn_chncodecmpset A) (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
          (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
      p0068 p0025
  have p0080 :=
    @g_syl
      (syn_wrex x (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
        (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st)
              (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
                (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                  (syn_c0)))) (syn_cin (syn_cfv (syn_c1st)
                (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
                  (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                    (syn_c0)))) (syn_cxp (syn_cin (syn_cfv (syn_c2nd)
                    (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v) (syn_cop
                        (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                        (syn_c0)))) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st)
                          (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v) (syn_cop
                              (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                              (syn_c0)))) (syn_cid))) (syn_csn (.cv x)))) (syn_cin
                  (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
                      (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                        (syn_c0)))) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st)
                          (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v) (syn_cop
                              (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                              (syn_c0)))) (syn_cid))) (syn_csn (.cv x)))))) (syn_cfv (syn_c2nd)
              (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
                (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                  (syn_c0)))) (syn_cin (syn_cfv (syn_c2nd)
                (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
                  (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                    (syn_c0)))) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st)
                      (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v) (syn_cop
                          (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                          (syn_c0)))) (syn_cid))) (syn_csn (.cv x)))))))
      (syn_wbr (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
          (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
        (syn_chncodecmpset A) (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
          (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
      (syn_wo (syn_wbr (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
          (syn_chncodecmpset A) (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
        (syn_wbr (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
          (syn_chncodecmpset A) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
              (syn_c0)))))
      p0078 p0027
  have p0082 :=
    @g_hwcnweclndv A
      (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
        (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
  have p0083 := Nominal.mp p0006 p0082
  have p0084 :=
    @g_wecutisogencodeparts x
      (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
          (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
      (syn_cfv (syn_c1st) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
          (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
      p0083
  have p0085 :=
    @g_simpld
      (.classMem (.cv x) (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
              (syn_c0)))))
      (.classEq (syn_cfv (syn_c1st) (syn_chnwcutcode (syn_cfv (syn_c1st)
              (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
                (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                  (syn_c0)))) (syn_cfv (syn_c2nd)
              (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
                (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                  (syn_c0)))) (.cv x))) (syn_cin (syn_cfv (syn_c1st)
            (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0)))) (syn_cxp (syn_cin (syn_cfv (syn_c2nd)
                (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
                  (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                    (syn_c0)))) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st)
                      (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop
                          (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                          (syn_c0)))) (syn_cid))) (syn_csn (.cv x)))) (syn_cin
              (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
                  (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                    (syn_c0)))) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st)
                      (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop
                          (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                          (syn_c0)))) (syn_cid))) (syn_csn (.cv x)))))))
      (.classEq (syn_cfv (syn_c2nd) (syn_chnwcutcode (syn_cfv (syn_c1st)
              (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
                (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                  (syn_c0)))) (syn_cfv (syn_c2nd)
              (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
                (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                  (syn_c0)))) (.cv x))) (syn_cin (syn_cfv (syn_c2nd)
            (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0)))) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st)
                  (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop
                      (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                      (syn_c0)))) (syn_cid))) (syn_csn (.cv x)))))
      p0084
  have p0086 :=
    @g_eqcomd
      (.classMem (.cv x) (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
              (syn_c0)))))
      (syn_cfv (syn_c1st) (syn_chnwcutcode (syn_cfv (syn_c1st)
            (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0)))) (syn_cfv (syn_c2nd)
            (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0)))) (.cv x)))
      (syn_cin (syn_cfv (syn_c1st) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
        (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
                (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                  (syn_c0)))) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st)
                    (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop
                        (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                        (syn_c0)))) (syn_cid))) (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd)
              (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
                (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                  (syn_c0)))) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st)
                    (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop
                        (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                        (syn_c0)))) (syn_cid))) (syn_csn (.cv x))))))
      p0085
  have p0087 :=
    @g_isoeq3
      (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
          (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
      (syn_cin (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
        (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st)
                (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
                  (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                    (syn_c0)))) (syn_cid))) (syn_csn (.cv x))))
      (syn_cfv (syn_c1st) (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
          (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
      (syn_cin (syn_cfv (syn_c1st) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
        (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
                (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                  (syn_c0)))) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st)
                    (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop
                        (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                        (syn_c0)))) (syn_cid))) (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd)
              (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
                (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                  (syn_c0)))) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st)
                    (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop
                        (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                        (syn_c0)))) (syn_cid))) (syn_csn (.cv x))))))
      (syn_cfv (syn_c1st) (syn_chnwcutcode (syn_cfv (syn_c1st)
            (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0)))) (syn_cfv (syn_c2nd)
            (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0)))) (.cv x)))
      (.cv h)
  have p0088 :=
    @g_syl
      (.classMem (.cv x) (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
              (syn_c0)))))
      (.classEq (syn_cin (syn_cfv (syn_c1st) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0)))) (syn_cxp (syn_cin (syn_cfv (syn_c2nd)
                (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
                  (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                    (syn_c0)))) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st)
                      (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop
                          (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                          (syn_c0)))) (syn_cid))) (syn_csn (.cv x)))) (syn_cin
              (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
                  (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                    (syn_c0)))) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st)
                      (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop
                          (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                          (syn_c0)))) (syn_cid))) (syn_csn (.cv x)))))) (syn_cfv (syn_c1st)
          (syn_chnwcutcode (syn_cfv (syn_c1st)
              (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
                (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                  (syn_c0)))) (syn_cfv (syn_c2nd)
              (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
                (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                  (syn_c0)))) (.cv x))))
      (syn_wb (syn_wiso (.cv h) (syn_cfv (syn_c1st)
            (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0)))) (syn_cin (syn_cfv (syn_c1st)
              (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
                (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                  (syn_c0)))) (syn_cxp (syn_cin (syn_cfv (syn_c2nd)
                  (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop
                      (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                      (syn_c0)))) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st)
                        (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop
                            (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                            (syn_c0)))) (syn_cid))) (syn_csn (.cv x)))) (syn_cin
                (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop
                      (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                      (syn_c0)))) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st)
                        (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop
                            (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                            (syn_c0)))) (syn_cid))) (syn_csn (.cv x)))))) (syn_cfv (syn_c2nd)
            (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0)))) (syn_cin (syn_cfv (syn_c2nd)
              (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
                (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                  (syn_c0)))) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st)
                    (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop
                        (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                        (syn_c0)))) (syn_cid))) (syn_csn (.cv x))))) (syn_wiso (.cv h)
          (syn_cfv (syn_c1st) (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0)))) (syn_cfv (syn_c1st) (syn_chnwcutcode (syn_cfv (syn_c1st)
                (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
                  (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                    (syn_c0)))) (syn_cfv (syn_c2nd)
                (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
                  (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                    (syn_c0)))) (.cv x))) (syn_cfv (syn_c2nd)
            (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0)))) (syn_cin (syn_cfv (syn_c2nd)
              (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
                (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                  (syn_c0)))) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st)
                    (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop
                        (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                        (syn_c0)))) (syn_cid))) (syn_csn (.cv x))))))
      p0086 p0087
  have p0093 :=
    @g_simprd
      (.classMem (.cv x) (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
              (syn_c0)))))
      (.classEq (syn_cfv (syn_c1st) (syn_chnwcutcode (syn_cfv (syn_c1st)
              (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
                (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                  (syn_c0)))) (syn_cfv (syn_c2nd)
              (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
                (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                  (syn_c0)))) (.cv x))) (syn_cin (syn_cfv (syn_c1st)
            (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0)))) (syn_cxp (syn_cin (syn_cfv (syn_c2nd)
                (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
                  (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                    (syn_c0)))) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st)
                      (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop
                          (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                          (syn_c0)))) (syn_cid))) (syn_csn (.cv x)))) (syn_cin
              (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
                  (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                    (syn_c0)))) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st)
                      (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop
                          (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                          (syn_c0)))) (syn_cid))) (syn_csn (.cv x)))))))
      (.classEq (syn_cfv (syn_c2nd) (syn_chnwcutcode (syn_cfv (syn_c1st)
              (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
                (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                  (syn_c0)))) (syn_cfv (syn_c2nd)
              (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
                (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                  (syn_c0)))) (.cv x))) (syn_cin (syn_cfv (syn_c2nd)
            (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0)))) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st)
                  (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop
                      (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                      (syn_c0)))) (syn_cid))) (syn_csn (.cv x)))))
      p0084
  have p0094 :=
    @g_eqcomd
      (.classMem (.cv x) (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
              (syn_c0)))))
      (syn_cfv (syn_c2nd) (syn_chnwcutcode (syn_cfv (syn_c1st)
            (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0)))) (syn_cfv (syn_c2nd)
            (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0)))) (.cv x)))
      (syn_cin (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
        (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st)
                (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
                  (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                    (syn_c0)))) (syn_cid))) (syn_csn (.cv x))))
      p0093
  have p0095 :=
    @g_isoeq5
      (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
          (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
      (syn_cin (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
        (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st)
                (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
                  (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                    (syn_c0)))) (syn_cid))) (syn_csn (.cv x))))
      (syn_cfv (syn_c2nd) (syn_chnwcutcode (syn_cfv (syn_c1st)
            (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0)))) (syn_cfv (syn_c2nd)
            (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0)))) (.cv x)))
      (syn_cfv (syn_c1st) (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
          (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
      (syn_cfv (syn_c1st) (syn_chnwcutcode (syn_cfv (syn_c1st)
            (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0)))) (syn_cfv (syn_c2nd)
            (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0)))) (.cv x)))
      (.cv h)
  have p0096 :=
    @g_syl
      (.classMem (.cv x) (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
              (syn_c0)))))
      (.classEq (syn_cin (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0)))) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st)
                  (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop
                      (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                      (syn_c0)))) (syn_cid))) (syn_csn (.cv x)))) (syn_cfv (syn_c2nd)
          (syn_chnwcutcode (syn_cfv (syn_c1st)
              (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
                (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                  (syn_c0)))) (syn_cfv (syn_c2nd)
              (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
                (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                  (syn_c0)))) (.cv x))))
      (syn_wb (syn_wiso (.cv h) (syn_cfv (syn_c1st)
            (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0)))) (syn_cfv (syn_c1st) (syn_chnwcutcode (syn_cfv (syn_c1st)
                (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
                  (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                    (syn_c0)))) (syn_cfv (syn_c2nd)
                (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
                  (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                    (syn_c0)))) (.cv x))) (syn_cfv (syn_c2nd)
            (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0)))) (syn_cin (syn_cfv (syn_c2nd)
              (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
                (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                  (syn_c0)))) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st)
                    (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop
                        (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                        (syn_c0)))) (syn_cid))) (syn_csn (.cv x))))) (syn_wiso (.cv h)
          (syn_cfv (syn_c1st) (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0)))) (syn_cfv (syn_c1st) (syn_chnwcutcode (syn_cfv (syn_c1st)
                (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
                  (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                    (syn_c0)))) (syn_cfv (syn_c2nd)
                (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
                  (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                    (syn_c0)))) (.cv x))) (syn_cfv (syn_c2nd)
            (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0)))) (syn_cfv (syn_c2nd) (syn_chnwcutcode (syn_cfv (syn_c1st)
                (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
                  (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                    (syn_c0)))) (syn_cfv (syn_c2nd)
                (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
                  (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                    (syn_c0)))) (.cv x)))))
      p0094 p0095
  have p0097 :=
    @g_bitrd
      (.classMem (.cv x) (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
              (syn_c0)))))
      (syn_wiso (.cv h) (syn_cfv (syn_c1st) (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
        (syn_cin (syn_cfv (syn_c1st) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0)))) (syn_cxp (syn_cin (syn_cfv (syn_c2nd)
                (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
                  (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                    (syn_c0)))) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st)
                      (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop
                          (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                          (syn_c0)))) (syn_cid))) (syn_csn (.cv x)))) (syn_cin
              (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
                  (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                    (syn_c0)))) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st)
                      (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop
                          (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                          (syn_c0)))) (syn_cid))) (syn_csn (.cv x)))))) (syn_cfv (syn_c2nd)
          (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
        (syn_cin (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0)))) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st)
                  (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop
                      (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                      (syn_c0)))) (syn_cid))) (syn_csn (.cv x)))))
      (syn_wiso (.cv h) (syn_cfv (syn_c1st) (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
        (syn_cfv (syn_c1st) (syn_chnwcutcode (syn_cfv (syn_c1st)
              (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
                (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                  (syn_c0)))) (syn_cfv (syn_c2nd)
              (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
                (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                  (syn_c0)))) (.cv x))) (syn_cfv (syn_c2nd)
          (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
        (syn_cin (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0)))) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st)
                  (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop
                      (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                      (syn_c0)))) (syn_cid))) (syn_csn (.cv x)))))
      (syn_wiso (.cv h) (syn_cfv (syn_c1st) (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
        (syn_cfv (syn_c1st) (syn_chnwcutcode (syn_cfv (syn_c1st)
              (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
                (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                  (syn_c0)))) (syn_cfv (syn_c2nd)
              (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
                (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                  (syn_c0)))) (.cv x))) (syn_cfv (syn_c2nd)
          (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
        (syn_cfv (syn_c2nd) (syn_chnwcutcode (syn_cfv (syn_c1st)
              (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
                (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                  (syn_c0)))) (syn_cfv (syn_c2nd)
              (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
                (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                  (syn_c0)))) (.cv x))))
      p0088 p0096
  have p0098 :=
    @g_exbidv
      (.classMem (.cv x) (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
              (syn_c0)))))
      (syn_wiso (.cv h) (syn_cfv (syn_c1st) (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
        (syn_cin (syn_cfv (syn_c1st) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0)))) (syn_cxp (syn_cin (syn_cfv (syn_c2nd)
                (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
                  (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                    (syn_c0)))) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st)
                      (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop
                          (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                          (syn_c0)))) (syn_cid))) (syn_csn (.cv x)))) (syn_cin
              (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
                  (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                    (syn_c0)))) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st)
                      (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop
                          (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                          (syn_c0)))) (syn_cid))) (syn_csn (.cv x)))))) (syn_cfv (syn_c2nd)
          (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
        (syn_cin (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0)))) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st)
                  (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop
                      (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                      (syn_c0)))) (syn_cid))) (syn_csn (.cv x)))))
      (syn_wiso (.cv h) (syn_cfv (syn_c1st) (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
        (syn_cfv (syn_c1st) (syn_chnwcutcode (syn_cfv (syn_c1st)
              (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
                (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                  (syn_c0)))) (syn_cfv (syn_c2nd)
              (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
                (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                  (syn_c0)))) (.cv x))) (syn_cfv (syn_c2nd)
          (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
        (syn_cfv (syn_c2nd) (syn_chnwcutcode (syn_cfv (syn_c1st)
              (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
                (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                  (syn_c0)))) (syn_cfv (syn_c2nd)
              (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
                (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                  (syn_c0)))) (.cv x))))
      h dv_cache_0016 p0097
  have p0100 :=
    @g_a1i
      (.classMem (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
          (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
        (syn_chwcn A))
      (.classMem (.cv x) (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
              (syn_c0)))))
      p0008
  have p0104 :=
    @g_hnwcutcodecnclndv (.cv x)
      (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
          (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
      (syn_cfv (syn_c1st) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
          (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
      p0083
  have p0106 :=
    @g_hwcnbaseclndv A
      (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
        (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
  have p0107 := Nominal.mp p0006 p0106
  have p0108 :=
    @g_hwcnssbase A
      (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
          (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
      p0107
  have p0109 :=
    @g_ssel
      (syn_chwcn (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
              (syn_c0)))))
      (syn_chwcn A)
      (syn_chnwcutcode (syn_cfv (syn_c1st) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
        (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
        (.cv x))
  have p0110 := Nominal.mp p0108 p0109
  have p0111 :=
    @g_syl
      (.classMem (.cv x) (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
              (syn_c0)))))
      (.classMem (syn_chnwcutcode (syn_cfv (syn_c1st)
            (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0)))) (syn_cfv (syn_c2nd)
            (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0)))) (.cv x)) (syn_chwcn (syn_cfv (syn_c2nd)
            (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0))))))
      (.classMem (syn_chnwcutcode (syn_cfv (syn_c1st)
            (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0)))) (syn_cfv (syn_c2nd)
            (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0)))) (.cv x)) (syn_chwcn A))
      p0104 p0110
  have p0112 :=
    @g_jca
      (.classMem (.cv x) (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
              (syn_c0)))))
      (.classMem (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
          (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
        (syn_chwcn A))
      (.classMem (syn_chnwcutcode (syn_cfv (syn_c1st)
            (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0)))) (syn_cfv (syn_c2nd)
            (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0)))) (.cv x)) (syn_chwcn A))
      p0100 p0111
  have p0113 :=
    @g_hwnisodirectisobclndv A
      (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
        (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
      (syn_chnwcutcode (syn_cfv (syn_c1st) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
        (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
        (.cv x))
      h dv_cache_0001 dv_cache_0011 dv_cache_0017
  have p0114 :=
    @g_syl
      (.classMem (.cv x) (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
              (syn_c0)))))
      (syn_wa (.classMem (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
          (syn_chwcn A)) (.classMem (syn_chnwcutcode (syn_cfv (syn_c1st)
              (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
                (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                  (syn_c0)))) (syn_cfv (syn_c2nd)
              (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
                (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                  (syn_c0)))) (.cv x)) (syn_chwcn A)))
      (syn_wb (syn_wbr (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
          (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st)
              (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
                (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                  (syn_c0)))) (syn_cfv (syn_c2nd)
              (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
                (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                  (syn_c0)))) (.cv x))) (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st)
              (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
                (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                  (syn_c0)))) (syn_cfv (syn_c1st) (syn_chnwcutcode (syn_cfv (syn_c1st)
                  (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop
                      (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                      (syn_c0)))) (syn_cfv (syn_c2nd)
                  (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop
                      (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                      (syn_c0)))) (.cv x))) (syn_cfv (syn_c2nd)
              (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
                (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                  (syn_c0)))) (syn_cfv (syn_c2nd) (syn_chnwcutcode (syn_cfv (syn_c1st)
                  (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop
                      (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                      (syn_c0)))) (syn_cfv (syn_c2nd)
                  (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop
                      (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                      (syn_c0)))) (.cv x))))))
      p0112 p0113
  have p0115 :=
    @g_bicomd
      (.classMem (.cv x) (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
              (syn_c0)))))
      (syn_wbr (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
          (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
        (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st)
            (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0)))) (syn_cfv (syn_c2nd)
            (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0)))) (.cv x)))
      (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st)
            (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0)))) (syn_cfv (syn_c1st) (syn_chnwcutcode (syn_cfv (syn_c1st)
                (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
                  (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                    (syn_c0)))) (syn_cfv (syn_c2nd)
                (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
                  (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                    (syn_c0)))) (.cv x))) (syn_cfv (syn_c2nd)
            (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0)))) (syn_cfv (syn_c2nd) (syn_chnwcutcode (syn_cfv (syn_c1st)
                (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
                  (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                    (syn_c0)))) (syn_cfv (syn_c2nd)
                (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
                  (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                    (syn_c0)))) (.cv x)))))
      p0114
  have p0116 :=
    @g_bitrd
      (.classMem (.cv x) (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
              (syn_c0)))))
      (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st)
            (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0)))) (syn_cin (syn_cfv (syn_c1st)
              (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
                (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                  (syn_c0)))) (syn_cxp (syn_cin (syn_cfv (syn_c2nd)
                  (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop
                      (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                      (syn_c0)))) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st)
                        (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop
                            (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                            (syn_c0)))) (syn_cid))) (syn_csn (.cv x)))) (syn_cin
                (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop
                      (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                      (syn_c0)))) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st)
                        (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop
                            (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                            (syn_c0)))) (syn_cid))) (syn_csn (.cv x)))))) (syn_cfv (syn_c2nd)
            (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0)))) (syn_cin (syn_cfv (syn_c2nd)
              (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
                (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                  (syn_c0)))) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st)
                    (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop
                        (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                        (syn_c0)))) (syn_cid))) (syn_csn (.cv x))))))
      (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st)
            (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0)))) (syn_cfv (syn_c1st) (syn_chnwcutcode (syn_cfv (syn_c1st)
                (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
                  (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                    (syn_c0)))) (syn_cfv (syn_c2nd)
                (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
                  (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                    (syn_c0)))) (.cv x))) (syn_cfv (syn_c2nd)
            (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0)))) (syn_cfv (syn_c2nd) (syn_chnwcutcode (syn_cfv (syn_c1st)
                (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
                  (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                    (syn_c0)))) (syn_cfv (syn_c2nd)
                (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
                  (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                    (syn_c0)))) (.cv x)))))
      (syn_wbr (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
          (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
        (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st)
            (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0)))) (syn_cfv (syn_c2nd)
            (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0)))) (.cv x)))
      p0098 p0115
  have p0117 :=
    @g_rexbiia
      (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st)
            (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0)))) (syn_cin (syn_cfv (syn_c1st)
              (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
                (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                  (syn_c0)))) (syn_cxp (syn_cin (syn_cfv (syn_c2nd)
                  (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop
                      (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                      (syn_c0)))) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st)
                        (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop
                            (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                            (syn_c0)))) (syn_cid))) (syn_csn (.cv x)))) (syn_cin
                (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop
                      (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                      (syn_c0)))) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st)
                        (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop
                            (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                            (syn_c0)))) (syn_cid))) (syn_csn (.cv x)))))) (syn_cfv (syn_c2nd)
            (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0)))) (syn_cin (syn_cfv (syn_c2nd)
              (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
                (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                  (syn_c0)))) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st)
                    (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop
                        (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                        (syn_c0)))) (syn_cid))) (syn_csn (.cv x))))))
      (syn_wbr (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
          (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
        (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st)
            (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0)))) (syn_cfv (syn_c2nd)
            (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0)))) (.cv x)))
      x
      (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
          (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
      p0116
  have p0118 :=
    @g_biimpi
      (syn_wrex x (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
        (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st)
              (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
                (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                  (syn_c0)))) (syn_cin (syn_cfv (syn_c1st)
                (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
                  (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                    (syn_c0)))) (syn_cxp (syn_cin (syn_cfv (syn_c2nd)
                    (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop
                        (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                        (syn_c0)))) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st)
                          (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop
                              (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                              (syn_c0)))) (syn_cid))) (syn_csn (.cv x)))) (syn_cin
                  (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
                      (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                        (syn_c0)))) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st)
                          (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop
                              (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                              (syn_c0)))) (syn_cid))) (syn_csn (.cv x)))))) (syn_cfv (syn_c2nd)
              (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
                (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                  (syn_c0)))) (syn_cin (syn_cfv (syn_c2nd)
                (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
                  (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                    (syn_c0)))) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st)
                      (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop
                          (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                          (syn_c0)))) (syn_cid))) (syn_csn (.cv x)))))))
      (syn_wrex x (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
        (syn_wbr (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
          (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st)
              (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
                (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                  (syn_c0)))) (syn_cfv (syn_c2nd)
              (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
                (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                  (syn_c0)))) (.cv x))))
      p0117
  have p0119 :=
    @g_olc
      (syn_wrex x (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
        (syn_wbr (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
          (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st)
              (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
                (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                  (syn_c0)))) (syn_cfv (syn_c2nd)
              (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
                (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                  (syn_c0)))) (.cv x))))
      (syn_wbr (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
          (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
        (syn_chwniso A) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
          (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
  have p0120 :=
    @g_syl
      (syn_wrex x (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
        (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st)
              (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
                (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                  (syn_c0)))) (syn_cin (syn_cfv (syn_c1st)
                (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
                  (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                    (syn_c0)))) (syn_cxp (syn_cin (syn_cfv (syn_c2nd)
                    (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop
                        (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                        (syn_c0)))) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st)
                          (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop
                              (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                              (syn_c0)))) (syn_cid))) (syn_csn (.cv x)))) (syn_cin
                  (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
                      (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                        (syn_c0)))) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st)
                          (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop
                              (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                              (syn_c0)))) (syn_cid))) (syn_csn (.cv x)))))) (syn_cfv (syn_c2nd)
              (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
                (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                  (syn_c0)))) (syn_cin (syn_cfv (syn_c2nd)
                (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
                  (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                    (syn_c0)))) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st)
                      (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop
                          (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                          (syn_c0)))) (syn_cid))) (syn_csn (.cv x)))))))
      (syn_wrex x (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
        (syn_wbr (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
          (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st)
              (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
                (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                  (syn_c0)))) (syn_cfv (syn_c2nd)
              (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
                (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                  (syn_c0)))) (.cv x))))
      (syn_wo (syn_wbr (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
          (syn_chwniso A) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
        (syn_wrex x (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0)))) (syn_wbr (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0))) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st)
                (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
                  (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                    (syn_c0)))) (syn_cfv (syn_c2nd)
                (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
                  (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                    (syn_c0)))) (.cv x)))))
      p0118 p0119
  have p0122 :=
    @g_id
      (.classMem (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
          (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
        (syn_chwcn A))
  have p0124 :=
    @g_a1i
      (.classMem (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
          (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
        (syn_chwcn A))
      (.classMem (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
          (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
        (syn_chwcn A))
      p0006
  have p0125 :=
    @g_jca
      (.classMem (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
          (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
        (syn_chwcn A))
      (.classMem (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
          (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
        (syn_chwcn A))
      (.classMem (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
          (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
        (syn_chwcn A))
      p0122 p0124
  have p0126 := Nominal.mp p0008 p0125
  have p0127 :=
    @g_hncodecmpsetstrictcutsemclndv x A
      (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
        (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
      (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
        (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
      dv_cache_0004 dv_cache_0013 dv_cache_0012
  have p0128 := Nominal.mp p0126 p0127
  have p0129 :=
    @g_biimpri
      (syn_wbr (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
          (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
        (syn_chncodecmpset A) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
          (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
      (syn_wo (syn_wbr (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
          (syn_chwniso A) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
        (syn_wrex x (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0)))) (syn_wbr (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0))) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st)
                (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
                  (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                    (syn_c0)))) (syn_cfv (syn_c2nd)
                (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
                  (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                    (syn_c0)))) (.cv x)))))
      p0128
  have p0130 :=
    @g_syl
      (syn_wrex x (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
        (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st)
              (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
                (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                  (syn_c0)))) (syn_cin (syn_cfv (syn_c1st)
                (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
                  (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                    (syn_c0)))) (syn_cxp (syn_cin (syn_cfv (syn_c2nd)
                    (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop
                        (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                        (syn_c0)))) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st)
                          (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop
                              (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                              (syn_c0)))) (syn_cid))) (syn_csn (.cv x)))) (syn_cin
                  (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
                      (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                        (syn_c0)))) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st)
                          (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop
                              (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                              (syn_c0)))) (syn_cid))) (syn_csn (.cv x)))))) (syn_cfv (syn_c2nd)
              (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
                (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                  (syn_c0)))) (syn_cin (syn_cfv (syn_c2nd)
                (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
                  (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                    (syn_c0)))) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st)
                      (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop
                          (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                          (syn_c0)))) (syn_cid))) (syn_csn (.cv x)))))))
      (syn_wo (syn_wbr (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
          (syn_chwniso A) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
        (syn_wrex x (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0)))) (syn_wbr (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0))) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st)
                (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
                  (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                    (syn_c0)))) (syn_cfv (syn_c2nd)
                (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
                  (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                    (syn_c0)))) (.cv x)))))
      (syn_wbr (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
          (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
        (syn_chncodecmpset A) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
          (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
      p0120 p0129
  have p0131 :=
    @g_olc
      (syn_wbr (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
          (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
        (syn_chncodecmpset A) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
          (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
      (syn_wbr (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
          (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
        (syn_chncodecmpset A) (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
          (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
  have p0132 :=
    @g_syl
      (syn_wrex x (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
        (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st)
              (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
                (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                  (syn_c0)))) (syn_cin (syn_cfv (syn_c1st)
                (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
                  (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                    (syn_c0)))) (syn_cxp (syn_cin (syn_cfv (syn_c2nd)
                    (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop
                        (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                        (syn_c0)))) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st)
                          (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop
                              (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                              (syn_c0)))) (syn_cid))) (syn_csn (.cv x)))) (syn_cin
                  (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
                      (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                        (syn_c0)))) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st)
                          (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop
                              (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                              (syn_c0)))) (syn_cid))) (syn_csn (.cv x)))))) (syn_cfv (syn_c2nd)
              (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
                (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                  (syn_c0)))) (syn_cin (syn_cfv (syn_c2nd)
                (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
                  (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                    (syn_c0)))) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st)
                      (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop
                          (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                          (syn_c0)))) (syn_cid))) (syn_csn (.cv x)))))))
      (syn_wbr (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
          (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
        (syn_chncodecmpset A) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
          (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
      (syn_wo (syn_wbr (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
          (syn_chncodecmpset A) (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
        (syn_wbr (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
          (syn_chncodecmpset A) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
              (syn_c0)))))
      p0130 p0131
  have p0133 :=
    @g_n_3jaoi
      (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st)
            (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0)))) (syn_cfv (syn_c1st)
            (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0)))) (syn_cfv (syn_c2nd)
            (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0)))) (syn_cfv (syn_c2nd)
            (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0))))))
      (syn_wo (syn_wbr (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
          (syn_chncodecmpset A) (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
        (syn_wbr (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
          (syn_chncodecmpset A) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
              (syn_c0)))))
      (syn_wrex x (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
        (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st)
              (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
                (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                  (syn_c0)))) (syn_cin (syn_cfv (syn_c1st)
                (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
                  (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                    (syn_c0)))) (syn_cxp (syn_cin (syn_cfv (syn_c2nd)
                    (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v) (syn_cop
                        (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                        (syn_c0)))) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st)
                          (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v) (syn_cop
                              (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                              (syn_c0)))) (syn_cid))) (syn_csn (.cv x)))) (syn_cin
                  (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
                      (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                        (syn_c0)))) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st)
                          (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v) (syn_cop
                              (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                              (syn_c0)))) (syn_cid))) (syn_csn (.cv x)))))) (syn_cfv (syn_c2nd)
              (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
                (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                  (syn_c0)))) (syn_cin (syn_cfv (syn_c2nd)
                (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
                  (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                    (syn_c0)))) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st)
                      (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v) (syn_cop
                          (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                          (syn_c0)))) (syn_cid))) (syn_csn (.cv x)))))))
      (syn_wrex x (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
        (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st)
              (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
                (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                  (syn_c0)))) (syn_cin (syn_cfv (syn_c1st)
                (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
                  (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                    (syn_c0)))) (syn_cxp (syn_cin (syn_cfv (syn_c2nd)
                    (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop
                        (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                        (syn_c0)))) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st)
                          (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop
                              (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                              (syn_c0)))) (syn_cid))) (syn_csn (.cv x)))) (syn_cin
                  (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
                      (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                        (syn_c0)))) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st)
                          (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop
                              (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                              (syn_c0)))) (syn_cid))) (syn_csn (.cv x)))))) (syn_cfv (syn_c2nd)
              (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
                (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                  (syn_c0)))) (syn_cin (syn_cfv (syn_c2nd)
                (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
                  (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                    (syn_c0)))) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st)
                      (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop
                          (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                          (syn_c0)))) (syn_cid))) (syn_csn (.cv x)))))))
      p0028 p0080 p0132
  have p0134 := Nominal.mp p0005 p0133
  have p0135 :=
    @g_a1i
      (syn_wo (syn_wbr (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
          (syn_chncodecmpset A) (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
        (syn_wbr (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
          (syn_chncodecmpset A) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
              (syn_c0)))))
      (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) p0134
  have p0136 :=
    @g_simpl (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))
  have p0137 :=
    @g_iftrue (.classMem (.cv u) (syn_chwcn A)) (.cv u)
      (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))
  have p0138 :=
    @g_syl (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
      (.classMem (.cv u) (syn_chwcn A))
      (.classEq (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
          (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
        (.cv u))
      p0136 p0137
  have p0139 :=
    @g_simpr (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))
  have p0140 :=
    @g_iftrue (.classMem (.cv v) (syn_chwcn A)) (.cv v)
      (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))
  have p0141 :=
    @g_syl (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
      (.classMem (.cv v) (syn_chwcn A))
      (.classEq (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
          (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
        (.cv v))
      p0139 p0140
  have p0142 :=
    @g_breq12d
      (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
      (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
        (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
      (.cv u)
      (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
        (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
      (.cv v) (syn_chncodecmpset A) p0138 p0141
  have p0149 :=
    @g_breq12d
      (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
      (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
        (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
      (.cv v)
      (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
        (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
      (.cv u) (syn_chncodecmpset A) p0141 p0138
  have p0150 :=
    @g_orbi12d
      (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
      (syn_wbr (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
          (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
        (syn_chncodecmpset A) (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
          (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
      (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v))
      (syn_wbr (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
          (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
        (syn_chncodecmpset A) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
          (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
      (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv u)) p0142 p0149
  have p0151 :=
    @g_mpbid (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
      (syn_wo (syn_wbr (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
          (syn_chncodecmpset A) (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
        (syn_wbr (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
          (syn_chncodecmpset A) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
              (syn_c0)))))
      (syn_wo (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v))
        (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv u)))
      p0135 p0150
  have p0152 :=
    @g_syl
      (syn_w3a (.classMem A (syn_cvv)) (.classMem (.cv u) (syn_chwcn A))
        (.classMem (.cv v) (syn_chwcn A)))
      (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
      (syn_wo (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v))
        (syn_wbr (.cv v) (syn_chncodecmpset A) (.cv u)))
      p0004 p0151
  have p0153 :=
    @g_connexrd (.classMem A (syn_cvv)) u v (syn_chwcn A) (syn_chncodecmpset A) (syn_cvv)
      (syn_cvv) dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
      dv_cache_0023 dv_cache_0024 p0000 p0001 p0152
  exact p0153


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk017Compact001Part026`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_hnwcutcodenestndv (x : Var) (y : Var) (D : Class) (R : Class) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (.classEq (syn_chnwcutcode (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (.cv x))
          (syn_chnwcutcode R D (.cv x)))) :=
  by
  have p0000 :=
    (Nominal.classEqRefl (syn_chnwcutcode (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (.cv x)))
  have p0001 :=
    @g_a1i
      (.classEq (syn_chnwcutcode (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (.cv x))
        (syn_cop (syn_cin (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (syn_cxp (syn_cin
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cima (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D
                            (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                              (syn_csn (.cv y)))))) (syn_cid))) (syn_csn (.cv x)))) (syn_cin
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cima (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D
                            (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                              (syn_csn (.cv y)))))) (syn_cid))) (syn_csn (.cv x)))))) (syn_cin
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cima
              (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                      (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
                  (syn_cid))) (syn_csn (.cv x))))))
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      p0000
  have p0002 := @g_strictsegcut x y D R
  have p0004 :=
    @g_xpeq12d
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (syn_cin (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
        (syn_cima (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
              (syn_cid))) (syn_csn (.cv x))))
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
      (syn_cin (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
        (syn_cima (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
              (syn_cid))) (syn_csn (.cv x))))
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) p0002
      p0002
  have p0005 :=
    @g_ineq2
      (syn_cxp (syn_cin
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cima
            (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
                (syn_cid))) (syn_csn (.cv x)))) (syn_cin
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cima
            (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
                (syn_cid))) (syn_csn (.cv x)))))
      (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
      (syn_cin R (syn_cxp
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
  have p0006 :=
    @g_syl
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (.classEq (syn_cxp (syn_cin
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cima
              (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                      (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
                  (syn_cid))) (syn_csn (.cv x)))) (syn_cin
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cima
              (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                      (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
                  (syn_cid))) (syn_csn (.cv x))))) (syn_cxp
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (.classEq (syn_cin (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_cxp (syn_cin
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cima (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D
                          (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                            (syn_csn (.cv y)))))) (syn_cid))) (syn_csn (.cv x)))) (syn_cin
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cima (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D
                          (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                            (syn_csn (.cv y)))))) (syn_cid))) (syn_csn (.cv x)))))) (syn_cin
          (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))))
      p0004 p0005
  have p0008 :=
    @g_inss1 (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
      (syn_cima (syn_ccnv (syn_cdif (syn_cin R (syn_cxp
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
            (syn_cid))) (syn_csn (.cv x)))
  have p0009 :=
    @g_a1i
      (syn_wss (syn_cin
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cima
            (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
                (syn_cid))) (syn_csn (.cv x))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      p0008
  have p0010 :=
    @g_eqsstr3d
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
      (syn_cin (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
        (syn_cima (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
              (syn_cid))) (syn_csn (.cv x))))
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) p0002
      p0009
  have p0011 := @g_strictsegrestrnest x y D R
  have p0012 :=
    @g_syl
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (syn_wss (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))))
      (.classEq (syn_cin (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))))
      p0010 p0011
  have p0013 :=
    @g_eqtrd
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (syn_cin (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (syn_cxp (syn_cin
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cima
              (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                      (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
                  (syn_cid))) (syn_csn (.cv x)))) (syn_cin
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cima
              (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                      (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
                  (syn_cid))) (syn_csn (.cv x))))))
      (syn_cin (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (syn_cin R (syn_cxp
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      p0006 p0012
  have p0015 :=
    @g_opeq12d
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (syn_cin (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (syn_cxp (syn_cin
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cima
              (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                      (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
                  (syn_cid))) (syn_csn (.cv x)))) (syn_cin
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cima
              (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                      (syn_cin D
                        (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
                  (syn_cid))) (syn_csn (.cv x))))))
      (syn_cin R (syn_cxp
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (syn_cin (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
        (syn_cima (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                    (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
              (syn_cid))) (syn_csn (.cv x))))
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))) p0013
      p0002
  have p0016 := (Nominal.classEqRefl (syn_chnwcutcode R D (.cv x)))
  have p0017 :=
    @g_a1i
      (.classEq (syn_chnwcutcode R D (.cv x)) (syn_cop (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      p0016
  have p0018 :=
    @g_eqcomd
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (syn_chnwcutcode R D (.cv x))
      (syn_cop (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
      p0017
  have p0019 :=
    @g_n_3eqtrd
      (syn_wa (syn_wa (syn_wbr R (syn_cwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
      (syn_chnwcutcode (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (.cv x))
      (syn_cop (syn_cin (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
          (syn_cxp (syn_cin
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cima (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D
                          (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                            (syn_csn (.cv y)))))) (syn_cid))) (syn_csn (.cv x)))) (syn_cin
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
              (syn_cima (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D
                          (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))
                        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                            (syn_csn (.cv y)))))) (syn_cid))) (syn_csn (.cv x)))))) (syn_cin
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cima
            (syn_ccnv (syn_cdif (syn_cin R (syn_cxp (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y)))) (syn_cin D
                      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv y))))))
                (syn_cid))) (syn_csn (.cv x)))))
      (syn_cop (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
      (syn_chnwcutcode R D (.cv x)) p0001 p0015 p0018
  exact p0019

@[expose]
noncomputable def g_hnwcutcodeeq12ndv (x : Var) (D : Class) (R : Class) (S : Class)
    (E : Class) :
    Nominal.NPrf
      (.imp (syn_wa (.classEq R S) (.classEq D E))
        (.classEq (syn_chnwcutcode R D (.cv x)) (syn_chnwcutcode S E (.cv x)))) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_chnwcutcode R D (.cv x)))
  have p0001 :=
    @g_a1i
      (.classEq (syn_chnwcutcode R D (.cv x)) (syn_cop (syn_cin R (syn_cxp
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
              (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (syn_wa (.classEq R S) (.classEq D E)) p0000
  have p0002 := @g_simpl (.classEq R S) (.classEq D E)
  have p0003 := @g_simpr (.classEq R S) (.classEq D E)
  have p0005 := @g_difeq1d (syn_wa (.classEq R S) (.classEq D E)) R S (syn_cid) p0002
  have p0006 :=
    @g_cnveqd (syn_wa (.classEq R S) (.classEq D E)) (syn_cdif R (syn_cid))
      (syn_cdif S (syn_cid)) p0005
  have p0007 :=
    @g_imaeq1d (syn_wa (.classEq R S) (.classEq D E)) (syn_ccnv (syn_cdif R (syn_cid)))
      (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)) p0006
  have p0008 :=
    @g_ineq12d (syn_wa (.classEq R S) (.classEq D E)) D E
      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))
      (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))) p0003 p0007
  have p0015 :=
    @g_xpeq12d (syn_wa (.classEq R S) (.classEq D E))
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
      (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
      (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) p0008
      p0008
  have p0016 :=
    @g_ineq12d (syn_wa (.classEq R S) (.classEq D E)) R S
      (syn_cxp (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
      (syn_cxp (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))
        (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))
      p0002 p0015
  have p0023 :=
    @g_opeq12d (syn_wa (.classEq R S) (.classEq D E))
      (syn_cin R (syn_cxp
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
          (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
      (syn_cin S (syn_cxp
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))))
      (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
      (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))) p0016
      p0008
  have p0024 := (Nominal.classEqRefl (syn_chnwcutcode S E (.cv x)))
  have p0025 :=
    @g_a1i
      (.classEq (syn_chnwcutcode S E (.cv x)) (syn_cop (syn_cin S (syn_cxp
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))
              (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))))
          (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))))
      (syn_wa (.classEq R S) (.classEq D E)) p0024
  have p0026 :=
    @g_eqcomd (syn_wa (.classEq R S) (.classEq D E)) (syn_chnwcutcode S E (.cv x))
      (syn_cop (syn_cin S (syn_cxp
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))))
        (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))
      p0025
  have p0027 :=
    @g_n_3eqtrd (syn_wa (.classEq R S) (.classEq D E)) (syn_chnwcutcode R D (.cv x))
      (syn_cop (syn_cin R (syn_cxp
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))
            (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x))))))
        (syn_cin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (.cv x)))))
      (syn_cop (syn_cin S (syn_cxp
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))
            (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x))))))
        (syn_cin E (syn_cima (syn_ccnv (syn_cdif S (syn_cid))) (syn_csn (.cv x)))))
      (syn_chnwcutcode S E (.cv x)) p0001 p0023 p0026
  exact p0027

@[expose]
noncomputable def g_hnwcutcodeambientndv (x : Var) (u : Var) (A : Class)
    (dv_A_u : u ∉ A.fv) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem (.cv u) (syn_chwcn A))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (.classMem
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
          (syn_chwcn A))) :=
  by
  have dv_cache_0001 : u ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_u, not_false_eq_true])
  have p0000 :=
    @g_simpr (.classMem (.cv u) (syn_chwcn A))
      (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
  have p0001 :=
    @g_simpl (.classMem (.cv u) (syn_chwcn A))
      (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
  have p0002 :=
    @g_iftrue (.classMem (.cv u) (syn_chwcn A)) (.cv u)
      (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))
  have p0003 :=
    @g_syl
      (syn_wa (.classMem (.cv u) (syn_chwcn A))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
      (.classMem (.cv u) (syn_chwcn A))
      (.classEq (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
          (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
        (.cv u))
      p0001 p0002
  have p0004 :=
    @g_fveq2d
      (syn_wa (.classMem (.cv u) (syn_chwcn A))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
      (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
        (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
      (.cv u) (syn_c2nd) p0003
  have p0005 :=
    @g_eleq2d
      (syn_wa (.classMem (.cv u) (syn_chwcn A))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
      (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
          (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
      (syn_cfv (syn_c2nd) (.cv u)) (.cv x) p0004
  have p0006 :=
    @g_mpbird
      (syn_wa (.classMem (.cv u) (syn_chwcn A))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
      (.classMem (.cv x) (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
              (syn_c0)))))
      (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))) p0000 p0005
  have p0007 := @g_hncodetotalleftmemndv u A dv_cache_0001
  have p0008 :=
    @g_hwcnweclndv A
      (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
        (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
  have p0009 := Nominal.mp p0007 p0008
  have p0010 :=
    @g_hnwcutcodecnclndv (.cv x)
      (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
          (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
      (syn_cfv (syn_c1st) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
          (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
      p0009
  have p0012 :=
    @g_hwcnbaseclndv A
      (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
        (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
  have p0013 := Nominal.mp p0007 p0012
  have p0014 :=
    @g_hwcnssbase A
      (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
          (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
      p0013
  have p0015 :=
    @g_ssel
      (syn_chwcn (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
              (syn_c0)))))
      (syn_chwcn A)
      (syn_chnwcutcode (syn_cfv (syn_c1st) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
        (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
        (.cv x))
  have p0016 := Nominal.mp p0014 p0015
  have p0017 :=
    @g_syl
      (.classMem (.cv x) (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
              (syn_c0)))))
      (.classMem (syn_chnwcutcode (syn_cfv (syn_c1st)
            (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0)))) (syn_cfv (syn_c2nd)
            (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0)))) (.cv x)) (syn_chwcn (syn_cfv (syn_c2nd)
            (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0))))))
      (.classMem (syn_chnwcutcode (syn_cfv (syn_c1st)
            (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0)))) (syn_cfv (syn_c2nd)
            (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0)))) (.cv x)) (syn_chwcn A))
      p0010 p0016
  have p0018 :=
    @g_syl
      (syn_wa (.classMem (.cv u) (syn_chwcn A))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
      (.classMem (.cv x) (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
              (syn_c0)))))
      (.classMem (syn_chnwcutcode (syn_cfv (syn_c1st)
            (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0)))) (syn_cfv (syn_c2nd)
            (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0)))) (.cv x)) (syn_chwcn A))
      p0006 p0017
  have p0022 :=
    @g_fveq2d
      (syn_wa (.classMem (.cv u) (syn_chwcn A))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
      (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
        (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
      (.cv u) (syn_c1st) p0003
  have p0027 :=
    @g_jca
      (syn_wa (.classMem (.cv u) (syn_chwcn A))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
      (.classEq (syn_cfv (syn_c1st) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
        (syn_cfv (syn_c1st) (.cv u)))
      (.classEq (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
        (syn_cfv (syn_c2nd) (.cv u)))
      p0022 p0004
  have p0028 :=
    @g_hnwcutcodeeq12ndv x
      (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
          (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
      (syn_cfv (syn_c1st) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
          (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
      (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
  have p0029 :=
    @g_syl
      (syn_wa (.classMem (.cv u) (syn_chwcn A))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
      (syn_wa (.classEq (syn_cfv (syn_c1st) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0)))) (syn_cfv (syn_c1st) (.cv u))) (.classEq (syn_cfv (syn_c2nd)
            (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0)))) (syn_cfv (syn_c2nd) (.cv u))))
      (.classEq (syn_chnwcutcode (syn_cfv (syn_c1st)
            (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0)))) (syn_cfv (syn_c2nd)
            (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0)))) (.cv x))
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
      p0027 p0028
  have p0030 :=
    @g_eleq1d
      (syn_wa (.classMem (.cv u) (syn_chwcn A))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
      (syn_chnwcutcode (syn_cfv (syn_c1st) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
        (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
        (.cv x))
      (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
      (syn_chwcn A) p0029
  have p0031 :=
    @g_mpbid
      (syn_wa (.classMem (.cv u) (syn_chwcn A))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
      (.classMem (syn_chnwcutcode (syn_cfv (syn_c1st)
            (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0)))) (syn_cfv (syn_c2nd)
            (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0)))) (.cv x)) (syn_chwcn A))
      (.classMem (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (.cv x)) (syn_chwcn A))
      p0018 p0030
  exact p0031


end NFChoice.DirectNominalPrf.WPPReplay

end
