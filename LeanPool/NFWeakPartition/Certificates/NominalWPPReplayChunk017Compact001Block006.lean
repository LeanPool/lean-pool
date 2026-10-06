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

/-- Checked nominal proof certificate identified upstream as `g_hncodecmpsetconnexndv`. -/
@[expose]
noncomputable def gHncodecmpsetconnexndv (A : Class) :
    Nominal.NPrf
      (.imp (.classMem A (synCvv))
        (synWbr (synChncodecmpset A) (synCconnex) (synChwcn A))) :=
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
      ((synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
          (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
            (synC0)))).fv :=
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
      ((synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
          (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
            (synC0)))).fv :=
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
      ((synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
          (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
            (synC0)))).fv :=
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
      ((synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
          (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
            (synC0)))).fv :=
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
      ((Wff.classMem (.cv x) (synCfv (synC2nd)
            (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0)))))).fv :=
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
      ((synChnwcutcode (synCfv (synC1st) (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0)))) (synCfv (synC2nd)
            (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0)))) (.cv x))).fv :=
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
      ((Wff.classMem (.cv x) (synCfv (synC2nd)
            (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0)))))).fv :=
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
      ((synChnwcutcode (synCfv (synC1st) (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0)))) (synCfv (synC2nd)
            (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0)))) (.cv x))).fv :=
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
  have dv_cache_0018 : u ∉ ((synChwcn A)).fv :=
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
  have dv_cache_0019 : v ∉ ((synChwcn A)).fv :=
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
  have dv_cache_0020 : u ∉ ((synChncodecmpset A)).fv :=
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
  have dv_cache_0021 : v ∉ ((synChncodecmpset A)).fv :=
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
  have dv_cache_0022 : u ∉ ((Wff.classMem A (synCvv))).fv :=
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
  have dv_cache_0023 : v ∉ ((Wff.classMem A (synCvv))).fv :=
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
  have p0000 := @gHncodecmpsetexg A
  have p0001 := @gHwcnexg A
  have p0002 :=
    @gSimp2 (.classMem A (synCvv)) (.classMem (.cv u) (synChwcn A))
      (.classMem (.cv v) (synChwcn A))
  have p0003 :=
    @gSimp3 (.classMem A (synCvv)) (.classMem (.cv u) (synChwcn A))
      (.classMem (.cv v) (synChwcn A))
  have p0004 :=
    @gJca
      (synW3a (.classMem A (synCvv)) (.classMem (.cv u) (synChwcn A))
        (.classMem (.cv v) (synChwcn A)))
      (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)) p0002 p0003
  have p0005 :=
    @gHncodecomparisontotalndv x v u A h dv_cache_0001 dv_cache_0002 dv_cache_0003
      dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
  have p0006 := @gHncodetotalleftmemndv u A dv_cache_0002
  have p0007 :=
    @gId
      (.classMem (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
          (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
        (synChwcn A))
  have p0008 := @gHncodetotalrightmemndv v A dv_cache_0003
  have p0009 :=
    @gA1i
      (.classMem (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
          (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
        (synChwcn A))
      (.classMem (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
          (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
        (synChwcn A))
      p0008
  have p0010 :=
    @gJca
      (.classMem (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
          (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
        (synChwcn A))
      (.classMem (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
          (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
        (synChwcn A))
      (.classMem (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
          (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
        (synChwcn A))
      p0007 p0009
  have p0011 := Nominal.mp p0006 p0010
  have p0012 :=
    @gHwnisodirectisobclndv A
      (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
        (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
      (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
        (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
      h dv_cache_0001 dv_cache_0010 dv_cache_0011
  have p0013 := Nominal.mp p0011 p0012
  have p0014 :=
    @gBiimpri
      (synWbr (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
          (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
        (synChwniso A) (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
          (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
      (synWex h (synWiso (.cv h) (synCfv (synC1st)
            (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0)))) (synCfv (synC1st)
            (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0)))) (synCfv (synC2nd)
            (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0)))) (synCfv (synC2nd)
            (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0))))))
      p0013
  have p0015 :=
    @gOrc
      (synWbr (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
          (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
        (synChwniso A) (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
          (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
      (synWrex x (synCfv (synC2nd) (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
        (synWbr (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
          (synChwniso A) (synChnwcutcode (synCfv (synC1st)
              (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0)))) (synCfv (synC2nd)
              (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0)))) (.cv x))))
  have p0016 :=
    @gSyl
      (synWex h (synWiso (.cv h) (synCfv (synC1st)
            (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0)))) (synCfv (synC1st)
            (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0)))) (synCfv (synC2nd)
            (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0)))) (synCfv (synC2nd)
            (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0))))))
      (synWbr (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
          (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
        (synChwniso A) (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
          (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
      (synWo (synWbr (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
          (synChwniso A) (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
        (synWrex x (synCfv (synC2nd) (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0)))) (synWbr (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0))) (synChwniso A) (synChnwcutcode (synCfv (synC1st)
                (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
                  (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                    (synC0)))) (synCfv (synC2nd)
                (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
                  (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                    (synC0)))) (.cv x)))))
      p0014 p0015
  have p0023 :=
    @gHncodecmpsetstrictcutsemclndv x A
      (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
        (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
      (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
        (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
      dv_cache_0004 dv_cache_0012 dv_cache_0013
  have p0024 := Nominal.mp p0011 p0023
  have p0025 :=
    @gBiimpri
      (synWbr (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
          (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
        (synChncodecmpset A) (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
          (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
      (synWo (synWbr (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
          (synChwniso A) (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
        (synWrex x (synCfv (synC2nd) (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0)))) (synWbr (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0))) (synChwniso A) (synChnwcutcode (synCfv (synC1st)
                (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
                  (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                    (synC0)))) (synCfv (synC2nd)
                (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
                  (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                    (synC0)))) (.cv x)))))
      p0024
  have p0026 :=
    @gSyl
      (synWex h (synWiso (.cv h) (synCfv (synC1st)
            (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0)))) (synCfv (synC1st)
            (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0)))) (synCfv (synC2nd)
            (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0)))) (synCfv (synC2nd)
            (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0))))))
      (synWo (synWbr (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
          (synChwniso A) (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
        (synWrex x (synCfv (synC2nd) (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0)))) (synWbr (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0))) (synChwniso A) (synChnwcutcode (synCfv (synC1st)
                (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
                  (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                    (synC0)))) (synCfv (synC2nd)
                (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
                  (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                    (synC0)))) (.cv x)))))
      (synWbr (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
          (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
        (synChncodecmpset A) (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
          (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
      p0016 p0025
  have p0027 :=
    @gOrc
      (synWbr (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
          (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
        (synChncodecmpset A) (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
          (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
      (synWbr (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
          (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
        (synChncodecmpset A) (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
          (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
  have p0028 :=
    @gSyl
      (synWex h (synWiso (.cv h) (synCfv (synC1st)
            (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0)))) (synCfv (synC1st)
            (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0)))) (synCfv (synC2nd)
            (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0)))) (synCfv (synC2nd)
            (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0))))))
      (synWbr (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
          (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
        (synChncodecmpset A) (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
          (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
      (synWo (synWbr (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
          (synChncodecmpset A) (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
        (synWbr (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
          (synChncodecmpset A) (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
              (synC0)))))
      p0026 p0027
  have p0030 :=
    @gHwcnweclndv A
      (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
        (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
  have p0031 := Nominal.mp p0008 p0030
  have p0032 :=
    @gWecutisogencodeparts x
      (synCfv (synC2nd) (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
          (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
      (synCfv (synC1st) (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
          (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
      p0031
  have p0033 :=
    @gSimpld
      (.classMem (.cv x) (synCfv (synC2nd) (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
              (synC0)))))
      (.classEq (synCfv (synC1st) (synChnwcutcode (synCfv (synC1st)
              (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0)))) (synCfv (synC2nd)
              (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0)))) (.cv x))) (synCin (synCfv (synC1st)
            (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0)))) (synCxp (synCin (synCfv (synC2nd)
                (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
                  (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                    (synC0)))) (synCima (synCcnv (synCdif (synCfv (synC1st)
                      (synCif (.classMem (.cv v) (synChwcn A)) (.cv v) (synCop
                          (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                          (synC0)))) (synCid))) (synCsn (.cv x)))) (synCin
              (synCfv (synC2nd) (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
                  (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                    (synC0)))) (synCima (synCcnv (synCdif (synCfv (synC1st)
                      (synCif (.classMem (.cv v) (synChwcn A)) (.cv v) (synCop
                          (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                          (synC0)))) (synCid))) (synCsn (.cv x)))))))
      (.classEq (synCfv (synC2nd) (synChnwcutcode (synCfv (synC1st)
              (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0)))) (synCfv (synC2nd)
              (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0)))) (.cv x))) (synCin (synCfv (synC2nd)
            (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0)))) (synCima (synCcnv (synCdif (synCfv (synC1st)
                  (synCif (.classMem (.cv v) (synChwcn A)) (.cv v) (synCop
                      (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                      (synC0)))) (synCid))) (synCsn (.cv x)))))
      p0032
  have p0034 :=
    @gEqcomd
      (.classMem (.cv x) (synCfv (synC2nd) (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
              (synC0)))))
      (synCfv (synC1st) (synChnwcutcode (synCfv (synC1st)
            (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0)))) (synCfv (synC2nd)
            (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0)))) (.cv x)))
      (synCin (synCfv (synC1st) (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
        (synCxp (synCin (synCfv (synC2nd) (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0)))) (synCima (synCcnv (synCdif (synCfv (synC1st)
                    (synCif (.classMem (.cv v) (synChwcn A)) (.cv v) (synCop
                        (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                        (synC0)))) (synCid))) (synCsn (.cv x)))) (synCin (synCfv (synC2nd)
              (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0)))) (synCima (synCcnv (synCdif (synCfv (synC1st)
                    (synCif (.classMem (.cv v) (synChwcn A)) (.cv v) (synCop
                        (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                        (synC0)))) (synCid))) (synCsn (.cv x))))))
      p0033
  have p0035 :=
    @gIsoeq3
      (synCfv (synC2nd) (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
          (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
      (synCin (synCfv (synC2nd) (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
        (synCima (synCcnv (synCdif (synCfv (synC1st)
                (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
                  (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                    (synC0)))) (synCid))) (synCsn (.cv x))))
      (synCfv (synC1st) (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
          (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
      (synCin (synCfv (synC1st) (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
        (synCxp (synCin (synCfv (synC2nd) (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0)))) (synCima (synCcnv (synCdif (synCfv (synC1st)
                    (synCif (.classMem (.cv v) (synChwcn A)) (.cv v) (synCop
                        (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                        (synC0)))) (synCid))) (synCsn (.cv x)))) (synCin (synCfv (synC2nd)
              (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0)))) (synCima (synCcnv (synCdif (synCfv (synC1st)
                    (synCif (.classMem (.cv v) (synChwcn A)) (.cv v) (synCop
                        (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                        (synC0)))) (synCid))) (synCsn (.cv x))))))
      (synCfv (synC1st) (synChnwcutcode (synCfv (synC1st)
            (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0)))) (synCfv (synC2nd)
            (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0)))) (.cv x)))
      (.cv h)
  have p0036 :=
    @gSyl
      (.classMem (.cv x) (synCfv (synC2nd) (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
              (synC0)))))
      (.classEq (synCin (synCfv (synC1st) (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0)))) (synCxp (synCin (synCfv (synC2nd)
                (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
                  (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                    (synC0)))) (synCima (synCcnv (synCdif (synCfv (synC1st)
                      (synCif (.classMem (.cv v) (synChwcn A)) (.cv v) (synCop
                          (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                          (synC0)))) (synCid))) (synCsn (.cv x)))) (synCin
              (synCfv (synC2nd) (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
                  (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                    (synC0)))) (synCima (synCcnv (synCdif (synCfv (synC1st)
                      (synCif (.classMem (.cv v) (synChwcn A)) (.cv v) (synCop
                          (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                          (synC0)))) (synCid))) (synCsn (.cv x)))))) (synCfv (synC1st)
          (synChnwcutcode (synCfv (synC1st)
              (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0)))) (synCfv (synC2nd)
              (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0)))) (.cv x))))
      (synWb (synWiso (.cv h) (synCfv (synC1st)
            (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0)))) (synCin (synCfv (synC1st)
              (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0)))) (synCxp (synCin (synCfv (synC2nd)
                  (synCif (.classMem (.cv v) (synChwcn A)) (.cv v) (synCop
                      (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                      (synC0)))) (synCima (synCcnv (synCdif (synCfv (synC1st)
                        (synCif (.classMem (.cv v) (synChwcn A)) (.cv v) (synCop
                            (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                            (synC0)))) (synCid))) (synCsn (.cv x)))) (synCin
                (synCfv (synC2nd) (synCif (.classMem (.cv v) (synChwcn A)) (.cv v) (synCop
                      (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                      (synC0)))) (synCima (synCcnv (synCdif (synCfv (synC1st)
                        (synCif (.classMem (.cv v) (synChwcn A)) (.cv v) (synCop
                            (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                            (synC0)))) (synCid))) (synCsn (.cv x)))))) (synCfv (synC2nd)
            (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0)))) (synCin (synCfv (synC2nd)
              (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0)))) (synCima (synCcnv (synCdif (synCfv (synC1st)
                    (synCif (.classMem (.cv v) (synChwcn A)) (.cv v) (synCop
                        (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                        (synC0)))) (synCid))) (synCsn (.cv x))))) (synWiso (.cv h)
          (synCfv (synC1st) (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0)))) (synCfv (synC1st) (synChnwcutcode (synCfv (synC1st)
                (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
                  (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                    (synC0)))) (synCfv (synC2nd)
                (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
                  (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                    (synC0)))) (.cv x))) (synCfv (synC2nd)
            (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0)))) (synCin (synCfv (synC2nd)
              (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0)))) (synCima (synCcnv (synCdif (synCfv (synC1st)
                    (synCif (.classMem (.cv v) (synChwcn A)) (.cv v) (synCop
                        (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                        (synC0)))) (synCid))) (synCsn (.cv x))))))
      p0034 p0035
  have p0041 :=
    @gSimprd
      (.classMem (.cv x) (synCfv (synC2nd) (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
              (synC0)))))
      (.classEq (synCfv (synC1st) (synChnwcutcode (synCfv (synC1st)
              (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0)))) (synCfv (synC2nd)
              (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0)))) (.cv x))) (synCin (synCfv (synC1st)
            (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0)))) (synCxp (synCin (synCfv (synC2nd)
                (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
                  (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                    (synC0)))) (synCima (synCcnv (synCdif (synCfv (synC1st)
                      (synCif (.classMem (.cv v) (synChwcn A)) (.cv v) (synCop
                          (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                          (synC0)))) (synCid))) (synCsn (.cv x)))) (synCin
              (synCfv (synC2nd) (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
                  (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                    (synC0)))) (synCima (synCcnv (synCdif (synCfv (synC1st)
                      (synCif (.classMem (.cv v) (synChwcn A)) (.cv v) (synCop
                          (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                          (synC0)))) (synCid))) (synCsn (.cv x)))))))
      (.classEq (synCfv (synC2nd) (synChnwcutcode (synCfv (synC1st)
              (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0)))) (synCfv (synC2nd)
              (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0)))) (.cv x))) (synCin (synCfv (synC2nd)
            (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0)))) (synCima (synCcnv (synCdif (synCfv (synC1st)
                  (synCif (.classMem (.cv v) (synChwcn A)) (.cv v) (synCop
                      (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                      (synC0)))) (synCid))) (synCsn (.cv x)))))
      p0032
  have p0042 :=
    @gEqcomd
      (.classMem (.cv x) (synCfv (synC2nd) (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
              (synC0)))))
      (synCfv (synC2nd) (synChnwcutcode (synCfv (synC1st)
            (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0)))) (synCfv (synC2nd)
            (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0)))) (.cv x)))
      (synCin (synCfv (synC2nd) (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
        (synCima (synCcnv (synCdif (synCfv (synC1st)
                (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
                  (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                    (synC0)))) (synCid))) (synCsn (.cv x))))
      p0041
  have p0043 :=
    @gIsoeq5
      (synCfv (synC2nd) (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
          (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
      (synCin (synCfv (synC2nd) (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
        (synCima (synCcnv (synCdif (synCfv (synC1st)
                (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
                  (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                    (synC0)))) (synCid))) (synCsn (.cv x))))
      (synCfv (synC2nd) (synChnwcutcode (synCfv (synC1st)
            (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0)))) (synCfv (synC2nd)
            (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0)))) (.cv x)))
      (synCfv (synC1st) (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
          (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
      (synCfv (synC1st) (synChnwcutcode (synCfv (synC1st)
            (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0)))) (synCfv (synC2nd)
            (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0)))) (.cv x)))
      (.cv h)
  have p0044 :=
    @gSyl
      (.classMem (.cv x) (synCfv (synC2nd) (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
              (synC0)))))
      (.classEq (synCin (synCfv (synC2nd) (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0)))) (synCima (synCcnv (synCdif (synCfv (synC1st)
                  (synCif (.classMem (.cv v) (synChwcn A)) (.cv v) (synCop
                      (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                      (synC0)))) (synCid))) (synCsn (.cv x)))) (synCfv (synC2nd)
          (synChnwcutcode (synCfv (synC1st)
              (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0)))) (synCfv (synC2nd)
              (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0)))) (.cv x))))
      (synWb (synWiso (.cv h) (synCfv (synC1st)
            (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0)))) (synCfv (synC1st) (synChnwcutcode (synCfv (synC1st)
                (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
                  (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                    (synC0)))) (synCfv (synC2nd)
                (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
                  (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                    (synC0)))) (.cv x))) (synCfv (synC2nd)
            (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0)))) (synCin (synCfv (synC2nd)
              (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0)))) (synCima (synCcnv (synCdif (synCfv (synC1st)
                    (synCif (.classMem (.cv v) (synChwcn A)) (.cv v) (synCop
                        (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                        (synC0)))) (synCid))) (synCsn (.cv x))))) (synWiso (.cv h)
          (synCfv (synC1st) (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0)))) (synCfv (synC1st) (synChnwcutcode (synCfv (synC1st)
                (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
                  (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                    (synC0)))) (synCfv (synC2nd)
                (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
                  (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                    (synC0)))) (.cv x))) (synCfv (synC2nd)
            (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0)))) (synCfv (synC2nd) (synChnwcutcode (synCfv (synC1st)
                (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
                  (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                    (synC0)))) (synCfv (synC2nd)
                (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
                  (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                    (synC0)))) (.cv x)))))
      p0042 p0043
  have p0045 :=
    @gBitrd
      (.classMem (.cv x) (synCfv (synC2nd) (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
              (synC0)))))
      (synWiso (.cv h) (synCfv (synC1st) (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
        (synCin (synCfv (synC1st) (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0)))) (synCxp (synCin (synCfv (synC2nd)
                (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
                  (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                    (synC0)))) (synCima (synCcnv (synCdif (synCfv (synC1st)
                      (synCif (.classMem (.cv v) (synChwcn A)) (.cv v) (synCop
                          (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                          (synC0)))) (synCid))) (synCsn (.cv x)))) (synCin
              (synCfv (synC2nd) (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
                  (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                    (synC0)))) (synCima (synCcnv (synCdif (synCfv (synC1st)
                      (synCif (.classMem (.cv v) (synChwcn A)) (.cv v) (synCop
                          (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                          (synC0)))) (synCid))) (synCsn (.cv x)))))) (synCfv (synC2nd)
          (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
        (synCin (synCfv (synC2nd) (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0)))) (synCima (synCcnv (synCdif (synCfv (synC1st)
                  (synCif (.classMem (.cv v) (synChwcn A)) (.cv v) (synCop
                      (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                      (synC0)))) (synCid))) (synCsn (.cv x)))))
      (synWiso (.cv h) (synCfv (synC1st) (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
        (synCfv (synC1st) (synChnwcutcode (synCfv (synC1st)
              (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0)))) (synCfv (synC2nd)
              (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0)))) (.cv x))) (synCfv (synC2nd)
          (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
        (synCin (synCfv (synC2nd) (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0)))) (synCima (synCcnv (synCdif (synCfv (synC1st)
                  (synCif (.classMem (.cv v) (synChwcn A)) (.cv v) (synCop
                      (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                      (synC0)))) (synCid))) (synCsn (.cv x)))))
      (synWiso (.cv h) (synCfv (synC1st) (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
        (synCfv (synC1st) (synChnwcutcode (synCfv (synC1st)
              (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0)))) (synCfv (synC2nd)
              (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0)))) (.cv x))) (synCfv (synC2nd)
          (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
        (synCfv (synC2nd) (synChnwcutcode (synCfv (synC1st)
              (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0)))) (synCfv (synC2nd)
              (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0)))) (.cv x))))
      p0036 p0044
  have p0046 :=
    @gExbidv
      (.classMem (.cv x) (synCfv (synC2nd) (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
              (synC0)))))
      (synWiso (.cv h) (synCfv (synC1st) (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
        (synCin (synCfv (synC1st) (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0)))) (synCxp (synCin (synCfv (synC2nd)
                (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
                  (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                    (synC0)))) (synCima (synCcnv (synCdif (synCfv (synC1st)
                      (synCif (.classMem (.cv v) (synChwcn A)) (.cv v) (synCop
                          (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                          (synC0)))) (synCid))) (synCsn (.cv x)))) (synCin
              (synCfv (synC2nd) (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
                  (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                    (synC0)))) (synCima (synCcnv (synCdif (synCfv (synC1st)
                      (synCif (.classMem (.cv v) (synChwcn A)) (.cv v) (synCop
                          (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                          (synC0)))) (synCid))) (synCsn (.cv x)))))) (synCfv (synC2nd)
          (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
        (synCin (synCfv (synC2nd) (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0)))) (synCima (synCcnv (synCdif (synCfv (synC1st)
                  (synCif (.classMem (.cv v) (synChwcn A)) (.cv v) (synCop
                      (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                      (synC0)))) (synCid))) (synCsn (.cv x)))))
      (synWiso (.cv h) (synCfv (synC1st) (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
        (synCfv (synC1st) (synChnwcutcode (synCfv (synC1st)
              (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0)))) (synCfv (synC2nd)
              (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0)))) (.cv x))) (synCfv (synC2nd)
          (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
        (synCfv (synC2nd) (synChnwcutcode (synCfv (synC1st)
              (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0)))) (synCfv (synC2nd)
              (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0)))) (.cv x))))
      h dv_cache_0014 p0045
  have p0048 :=
    @gA1i
      (.classMem (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
          (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
        (synChwcn A))
      (.classMem (.cv x) (synCfv (synC2nd) (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
              (synC0)))))
      p0006
  have p0052 :=
    @gHnwcutcodecnclndv (.cv x)
      (synCfv (synC2nd) (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
          (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
      (synCfv (synC1st) (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
          (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
      p0031
  have p0054 :=
    @gHwcnbaseclndv A
      (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
        (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
  have p0055 := Nominal.mp p0008 p0054
  have p0056 :=
    @gHwcnssbase A
      (synCfv (synC2nd) (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
          (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
      p0055
  have p0057 :=
    @gSsel
      (synChwcn (synCfv (synC2nd) (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
              (synC0)))))
      (synChwcn A)
      (synChnwcutcode (synCfv (synC1st) (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
        (synCfv (synC2nd) (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
        (.cv x))
  have p0058 := Nominal.mp p0056 p0057
  have p0059 :=
    @gSyl
      (.classMem (.cv x) (synCfv (synC2nd) (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
              (synC0)))))
      (.classMem (synChnwcutcode (synCfv (synC1st)
            (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0)))) (synCfv (synC2nd)
            (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0)))) (.cv x)) (synChwcn (synCfv (synC2nd)
            (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0))))))
      (.classMem (synChnwcutcode (synCfv (synC1st)
            (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0)))) (synCfv (synC2nd)
            (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0)))) (.cv x)) (synChwcn A))
      p0052 p0058
  have p0060 :=
    @gJca
      (.classMem (.cv x) (synCfv (synC2nd) (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
              (synC0)))))
      (.classMem (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
          (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
        (synChwcn A))
      (.classMem (synChnwcutcode (synCfv (synC1st)
            (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0)))) (synCfv (synC2nd)
            (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0)))) (.cv x)) (synChwcn A))
      p0048 p0059
  have p0061 :=
    @gHwnisodirectisobclndv A
      (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
        (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
      (synChnwcutcode (synCfv (synC1st) (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
        (synCfv (synC2nd) (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
        (.cv x))
      h dv_cache_0001 dv_cache_0010 dv_cache_0015
  have p0062 :=
    @gSyl
      (.classMem (.cv x) (synCfv (synC2nd) (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
              (synC0)))))
      (synWa (.classMem (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
          (synChwcn A)) (.classMem (synChnwcutcode (synCfv (synC1st)
              (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0)))) (synCfv (synC2nd)
              (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0)))) (.cv x)) (synChwcn A)))
      (synWb (synWbr (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
          (synChwniso A) (synChnwcutcode (synCfv (synC1st)
              (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0)))) (synCfv (synC2nd)
              (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0)))) (.cv x))) (synWex h (synWiso (.cv h) (synCfv (synC1st)
              (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0)))) (synCfv (synC1st) (synChnwcutcode (synCfv (synC1st)
                  (synCif (.classMem (.cv v) (synChwcn A)) (.cv v) (synCop
                      (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                      (synC0)))) (synCfv (synC2nd)
                  (synCif (.classMem (.cv v) (synChwcn A)) (.cv v) (synCop
                      (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                      (synC0)))) (.cv x))) (synCfv (synC2nd)
              (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0)))) (synCfv (synC2nd) (synChnwcutcode (synCfv (synC1st)
                  (synCif (.classMem (.cv v) (synChwcn A)) (.cv v) (synCop
                      (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                      (synC0)))) (synCfv (synC2nd)
                  (synCif (.classMem (.cv v) (synChwcn A)) (.cv v) (synCop
                      (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                      (synC0)))) (.cv x))))))
      p0060 p0061
  have p0063 :=
    @gBicomd
      (.classMem (.cv x) (synCfv (synC2nd) (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
              (synC0)))))
      (synWbr (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
          (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
        (synChwniso A) (synChnwcutcode (synCfv (synC1st)
            (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0)))) (synCfv (synC2nd)
            (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0)))) (.cv x)))
      (synWex h (synWiso (.cv h) (synCfv (synC1st)
            (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0)))) (synCfv (synC1st) (synChnwcutcode (synCfv (synC1st)
                (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
                  (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                    (synC0)))) (synCfv (synC2nd)
                (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
                  (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                    (synC0)))) (.cv x))) (synCfv (synC2nd)
            (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0)))) (synCfv (synC2nd) (synChnwcutcode (synCfv (synC1st)
                (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
                  (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                    (synC0)))) (synCfv (synC2nd)
                (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
                  (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                    (synC0)))) (.cv x)))))
      p0062
  have p0064 :=
    @gBitrd
      (.classMem (.cv x) (synCfv (synC2nd) (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
              (synC0)))))
      (synWex h (synWiso (.cv h) (synCfv (synC1st)
            (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0)))) (synCin (synCfv (synC1st)
              (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0)))) (synCxp (synCin (synCfv (synC2nd)
                  (synCif (.classMem (.cv v) (synChwcn A)) (.cv v) (synCop
                      (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                      (synC0)))) (synCima (synCcnv (synCdif (synCfv (synC1st)
                        (synCif (.classMem (.cv v) (synChwcn A)) (.cv v) (synCop
                            (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                            (synC0)))) (synCid))) (synCsn (.cv x)))) (synCin
                (synCfv (synC2nd) (synCif (.classMem (.cv v) (synChwcn A)) (.cv v) (synCop
                      (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                      (synC0)))) (synCima (synCcnv (synCdif (synCfv (synC1st)
                        (synCif (.classMem (.cv v) (synChwcn A)) (.cv v) (synCop
                            (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                            (synC0)))) (synCid))) (synCsn (.cv x)))))) (synCfv (synC2nd)
            (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0)))) (synCin (synCfv (synC2nd)
              (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0)))) (synCima (synCcnv (synCdif (synCfv (synC1st)
                    (synCif (.classMem (.cv v) (synChwcn A)) (.cv v) (synCop
                        (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                        (synC0)))) (synCid))) (synCsn (.cv x))))))
      (synWex h (synWiso (.cv h) (synCfv (synC1st)
            (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0)))) (synCfv (synC1st) (synChnwcutcode (synCfv (synC1st)
                (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
                  (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                    (synC0)))) (synCfv (synC2nd)
                (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
                  (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                    (synC0)))) (.cv x))) (synCfv (synC2nd)
            (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0)))) (synCfv (synC2nd) (synChnwcutcode (synCfv (synC1st)
                (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
                  (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                    (synC0)))) (synCfv (synC2nd)
                (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
                  (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                    (synC0)))) (.cv x)))))
      (synWbr (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
          (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
        (synChwniso A) (synChnwcutcode (synCfv (synC1st)
            (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0)))) (synCfv (synC2nd)
            (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0)))) (.cv x)))
      p0046 p0063
  have p0065 :=
    @gRexbiia
      (synWex h (synWiso (.cv h) (synCfv (synC1st)
            (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0)))) (synCin (synCfv (synC1st)
              (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0)))) (synCxp (synCin (synCfv (synC2nd)
                  (synCif (.classMem (.cv v) (synChwcn A)) (.cv v) (synCop
                      (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                      (synC0)))) (synCima (synCcnv (synCdif (synCfv (synC1st)
                        (synCif (.classMem (.cv v) (synChwcn A)) (.cv v) (synCop
                            (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                            (synC0)))) (synCid))) (synCsn (.cv x)))) (synCin
                (synCfv (synC2nd) (synCif (.classMem (.cv v) (synChwcn A)) (.cv v) (synCop
                      (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                      (synC0)))) (synCima (synCcnv (synCdif (synCfv (synC1st)
                        (synCif (.classMem (.cv v) (synChwcn A)) (.cv v) (synCop
                            (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                            (synC0)))) (synCid))) (synCsn (.cv x)))))) (synCfv (synC2nd)
            (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0)))) (synCin (synCfv (synC2nd)
              (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0)))) (synCima (synCcnv (synCdif (synCfv (synC1st)
                    (synCif (.classMem (.cv v) (synChwcn A)) (.cv v) (synCop
                        (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                        (synC0)))) (synCid))) (synCsn (.cv x))))))
      (synWbr (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
          (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
        (synChwniso A) (synChnwcutcode (synCfv (synC1st)
            (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0)))) (synCfv (synC2nd)
            (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0)))) (.cv x)))
      x
      (synCfv (synC2nd) (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
          (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
      p0064
  have p0066 :=
    @gBiimpi
      (synWrex x (synCfv (synC2nd) (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
        (synWex h (synWiso (.cv h) (synCfv (synC1st)
              (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0)))) (synCin (synCfv (synC1st)
                (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
                  (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                    (synC0)))) (synCxp (synCin (synCfv (synC2nd)
                    (synCif (.classMem (.cv v) (synChwcn A)) (.cv v) (synCop
                        (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                        (synC0)))) (synCima (synCcnv (synCdif (synCfv (synC1st)
                          (synCif (.classMem (.cv v) (synChwcn A)) (.cv v) (synCop
                              (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                              (synC0)))) (synCid))) (synCsn (.cv x)))) (synCin
                  (synCfv (synC2nd) (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
                      (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                        (synC0)))) (synCima (synCcnv (synCdif (synCfv (synC1st)
                          (synCif (.classMem (.cv v) (synChwcn A)) (.cv v) (synCop
                              (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                              (synC0)))) (synCid))) (synCsn (.cv x)))))) (synCfv (synC2nd)
              (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0)))) (synCin (synCfv (synC2nd)
                (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
                  (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                    (synC0)))) (synCima (synCcnv (synCdif (synCfv (synC1st)
                      (synCif (.classMem (.cv v) (synChwcn A)) (.cv v) (synCop
                          (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                          (synC0)))) (synCid))) (synCsn (.cv x)))))))
      (synWrex x (synCfv (synC2nd) (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
        (synWbr (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
          (synChwniso A) (synChnwcutcode (synCfv (synC1st)
              (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0)))) (synCfv (synC2nd)
              (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0)))) (.cv x))))
      p0065
  have p0067 :=
    @gOlc
      (synWrex x (synCfv (synC2nd) (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
        (synWbr (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
          (synChwniso A) (synChnwcutcode (synCfv (synC1st)
              (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0)))) (synCfv (synC2nd)
              (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0)))) (.cv x))))
      (synWbr (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
          (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
        (synChwniso A) (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
          (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
  have p0068 :=
    @gSyl
      (synWrex x (synCfv (synC2nd) (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
        (synWex h (synWiso (.cv h) (synCfv (synC1st)
              (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0)))) (synCin (synCfv (synC1st)
                (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
                  (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                    (synC0)))) (synCxp (synCin (synCfv (synC2nd)
                    (synCif (.classMem (.cv v) (synChwcn A)) (.cv v) (synCop
                        (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                        (synC0)))) (synCima (synCcnv (synCdif (synCfv (synC1st)
                          (synCif (.classMem (.cv v) (synChwcn A)) (.cv v) (synCop
                              (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                              (synC0)))) (synCid))) (synCsn (.cv x)))) (synCin
                  (synCfv (synC2nd) (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
                      (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                        (synC0)))) (synCima (synCcnv (synCdif (synCfv (synC1st)
                          (synCif (.classMem (.cv v) (synChwcn A)) (.cv v) (synCop
                              (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                              (synC0)))) (synCid))) (synCsn (.cv x)))))) (synCfv (synC2nd)
              (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0)))) (synCin (synCfv (synC2nd)
                (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
                  (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                    (synC0)))) (synCima (synCcnv (synCdif (synCfv (synC1st)
                      (synCif (.classMem (.cv v) (synChwcn A)) (.cv v) (synCop
                          (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                          (synC0)))) (synCid))) (synCsn (.cv x)))))))
      (synWrex x (synCfv (synC2nd) (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
        (synWbr (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
          (synChwniso A) (synChnwcutcode (synCfv (synC1st)
              (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0)))) (synCfv (synC2nd)
              (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0)))) (.cv x))))
      (synWo (synWbr (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
          (synChwniso A) (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
        (synWrex x (synCfv (synC2nd) (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0)))) (synWbr (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0))) (synChwniso A) (synChnwcutcode (synCfv (synC1st)
                (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
                  (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                    (synC0)))) (synCfv (synC2nd)
                (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
                  (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                    (synC0)))) (.cv x)))))
      p0066 p0067
  have p0078 :=
    @gSyl
      (synWrex x (synCfv (synC2nd) (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
        (synWex h (synWiso (.cv h) (synCfv (synC1st)
              (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0)))) (synCin (synCfv (synC1st)
                (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
                  (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                    (synC0)))) (synCxp (synCin (synCfv (synC2nd)
                    (synCif (.classMem (.cv v) (synChwcn A)) (.cv v) (synCop
                        (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                        (synC0)))) (synCima (synCcnv (synCdif (synCfv (synC1st)
                          (synCif (.classMem (.cv v) (synChwcn A)) (.cv v) (synCop
                              (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                              (synC0)))) (synCid))) (synCsn (.cv x)))) (synCin
                  (synCfv (synC2nd) (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
                      (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                        (synC0)))) (synCima (synCcnv (synCdif (synCfv (synC1st)
                          (synCif (.classMem (.cv v) (synChwcn A)) (.cv v) (synCop
                              (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                              (synC0)))) (synCid))) (synCsn (.cv x)))))) (synCfv (synC2nd)
              (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0)))) (synCin (synCfv (synC2nd)
                (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
                  (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                    (synC0)))) (synCima (synCcnv (synCdif (synCfv (synC1st)
                      (synCif (.classMem (.cv v) (synChwcn A)) (.cv v) (synCop
                          (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                          (synC0)))) (synCid))) (synCsn (.cv x)))))))
      (synWo (synWbr (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
          (synChwniso A) (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
        (synWrex x (synCfv (synC2nd) (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0)))) (synWbr (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0))) (synChwniso A) (synChnwcutcode (synCfv (synC1st)
                (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
                  (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                    (synC0)))) (synCfv (synC2nd)
                (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
                  (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                    (synC0)))) (.cv x)))))
      (synWbr (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
          (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
        (synChncodecmpset A) (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
          (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
      p0068 p0025
  have p0080 :=
    @gSyl
      (synWrex x (synCfv (synC2nd) (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
        (synWex h (synWiso (.cv h) (synCfv (synC1st)
              (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0)))) (synCin (synCfv (synC1st)
                (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
                  (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                    (synC0)))) (synCxp (synCin (synCfv (synC2nd)
                    (synCif (.classMem (.cv v) (synChwcn A)) (.cv v) (synCop
                        (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                        (synC0)))) (synCima (synCcnv (synCdif (synCfv (synC1st)
                          (synCif (.classMem (.cv v) (synChwcn A)) (.cv v) (synCop
                              (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                              (synC0)))) (synCid))) (synCsn (.cv x)))) (synCin
                  (synCfv (synC2nd) (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
                      (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                        (synC0)))) (synCima (synCcnv (synCdif (synCfv (synC1st)
                          (synCif (.classMem (.cv v) (synChwcn A)) (.cv v) (synCop
                              (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                              (synC0)))) (synCid))) (synCsn (.cv x)))))) (synCfv (synC2nd)
              (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0)))) (synCin (synCfv (synC2nd)
                (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
                  (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                    (synC0)))) (synCima (synCcnv (synCdif (synCfv (synC1st)
                      (synCif (.classMem (.cv v) (synChwcn A)) (.cv v) (synCop
                          (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                          (synC0)))) (synCid))) (synCsn (.cv x)))))))
      (synWbr (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
          (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
        (synChncodecmpset A) (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
          (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
      (synWo (synWbr (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
          (synChncodecmpset A) (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
        (synWbr (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
          (synChncodecmpset A) (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
              (synC0)))))
      p0078 p0027
  have p0082 :=
    @gHwcnweclndv A
      (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
        (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
  have p0083 := Nominal.mp p0006 p0082
  have p0084 :=
    @gWecutisogencodeparts x
      (synCfv (synC2nd) (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
          (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
      (synCfv (synC1st) (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
          (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
      p0083
  have p0085 :=
    @gSimpld
      (.classMem (.cv x) (synCfv (synC2nd) (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
              (synC0)))))
      (.classEq (synCfv (synC1st) (synChnwcutcode (synCfv (synC1st)
              (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0)))) (synCfv (synC2nd)
              (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0)))) (.cv x))) (synCin (synCfv (synC1st)
            (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0)))) (synCxp (synCin (synCfv (synC2nd)
                (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
                  (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                    (synC0)))) (synCima (synCcnv (synCdif (synCfv (synC1st)
                      (synCif (.classMem (.cv u) (synChwcn A)) (.cv u) (synCop
                          (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                          (synC0)))) (synCid))) (synCsn (.cv x)))) (synCin
              (synCfv (synC2nd) (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
                  (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                    (synC0)))) (synCima (synCcnv (synCdif (synCfv (synC1st)
                      (synCif (.classMem (.cv u) (synChwcn A)) (.cv u) (synCop
                          (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                          (synC0)))) (synCid))) (synCsn (.cv x)))))))
      (.classEq (synCfv (synC2nd) (synChnwcutcode (synCfv (synC1st)
              (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0)))) (synCfv (synC2nd)
              (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0)))) (.cv x))) (synCin (synCfv (synC2nd)
            (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0)))) (synCima (synCcnv (synCdif (synCfv (synC1st)
                  (synCif (.classMem (.cv u) (synChwcn A)) (.cv u) (synCop
                      (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                      (synC0)))) (synCid))) (synCsn (.cv x)))))
      p0084
  have p0086 :=
    @gEqcomd
      (.classMem (.cv x) (synCfv (synC2nd) (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
              (synC0)))))
      (synCfv (synC1st) (synChnwcutcode (synCfv (synC1st)
            (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0)))) (synCfv (synC2nd)
            (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0)))) (.cv x)))
      (synCin (synCfv (synC1st) (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
        (synCxp (synCin (synCfv (synC2nd) (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0)))) (synCima (synCcnv (synCdif (synCfv (synC1st)
                    (synCif (.classMem (.cv u) (synChwcn A)) (.cv u) (synCop
                        (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                        (synC0)))) (synCid))) (synCsn (.cv x)))) (synCin (synCfv (synC2nd)
              (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0)))) (synCima (synCcnv (synCdif (synCfv (synC1st)
                    (synCif (.classMem (.cv u) (synChwcn A)) (.cv u) (synCop
                        (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                        (synC0)))) (synCid))) (synCsn (.cv x))))))
      p0085
  have p0087 :=
    @gIsoeq3
      (synCfv (synC2nd) (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
          (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
      (synCin (synCfv (synC2nd) (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
        (synCima (synCcnv (synCdif (synCfv (synC1st)
                (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
                  (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                    (synC0)))) (synCid))) (synCsn (.cv x))))
      (synCfv (synC1st) (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
          (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
      (synCin (synCfv (synC1st) (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
        (synCxp (synCin (synCfv (synC2nd) (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0)))) (synCima (synCcnv (synCdif (synCfv (synC1st)
                    (synCif (.classMem (.cv u) (synChwcn A)) (.cv u) (synCop
                        (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                        (synC0)))) (synCid))) (synCsn (.cv x)))) (synCin (synCfv (synC2nd)
              (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0)))) (synCima (synCcnv (synCdif (synCfv (synC1st)
                    (synCif (.classMem (.cv u) (synChwcn A)) (.cv u) (synCop
                        (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                        (synC0)))) (synCid))) (synCsn (.cv x))))))
      (synCfv (synC1st) (synChnwcutcode (synCfv (synC1st)
            (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0)))) (synCfv (synC2nd)
            (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0)))) (.cv x)))
      (.cv h)
  have p0088 :=
    @gSyl
      (.classMem (.cv x) (synCfv (synC2nd) (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
              (synC0)))))
      (.classEq (synCin (synCfv (synC1st) (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0)))) (synCxp (synCin (synCfv (synC2nd)
                (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
                  (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                    (synC0)))) (synCima (synCcnv (synCdif (synCfv (synC1st)
                      (synCif (.classMem (.cv u) (synChwcn A)) (.cv u) (synCop
                          (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                          (synC0)))) (synCid))) (synCsn (.cv x)))) (synCin
              (synCfv (synC2nd) (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
                  (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                    (synC0)))) (synCima (synCcnv (synCdif (synCfv (synC1st)
                      (synCif (.classMem (.cv u) (synChwcn A)) (.cv u) (synCop
                          (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                          (synC0)))) (synCid))) (synCsn (.cv x)))))) (synCfv (synC1st)
          (synChnwcutcode (synCfv (synC1st)
              (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0)))) (synCfv (synC2nd)
              (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0)))) (.cv x))))
      (synWb (synWiso (.cv h) (synCfv (synC1st)
            (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0)))) (synCin (synCfv (synC1st)
              (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0)))) (synCxp (synCin (synCfv (synC2nd)
                  (synCif (.classMem (.cv u) (synChwcn A)) (.cv u) (synCop
                      (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                      (synC0)))) (synCima (synCcnv (synCdif (synCfv (synC1st)
                        (synCif (.classMem (.cv u) (synChwcn A)) (.cv u) (synCop
                            (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                            (synC0)))) (synCid))) (synCsn (.cv x)))) (synCin
                (synCfv (synC2nd) (synCif (.classMem (.cv u) (synChwcn A)) (.cv u) (synCop
                      (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                      (synC0)))) (synCima (synCcnv (synCdif (synCfv (synC1st)
                        (synCif (.classMem (.cv u) (synChwcn A)) (.cv u) (synCop
                            (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                            (synC0)))) (synCid))) (synCsn (.cv x)))))) (synCfv (synC2nd)
            (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0)))) (synCin (synCfv (synC2nd)
              (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0)))) (synCima (synCcnv (synCdif (synCfv (synC1st)
                    (synCif (.classMem (.cv u) (synChwcn A)) (.cv u) (synCop
                        (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                        (synC0)))) (synCid))) (synCsn (.cv x))))) (synWiso (.cv h)
          (synCfv (synC1st) (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0)))) (synCfv (synC1st) (synChnwcutcode (synCfv (synC1st)
                (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
                  (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                    (synC0)))) (synCfv (synC2nd)
                (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
                  (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                    (synC0)))) (.cv x))) (synCfv (synC2nd)
            (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0)))) (synCin (synCfv (synC2nd)
              (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0)))) (synCima (synCcnv (synCdif (synCfv (synC1st)
                    (synCif (.classMem (.cv u) (synChwcn A)) (.cv u) (synCop
                        (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                        (synC0)))) (synCid))) (synCsn (.cv x))))))
      p0086 p0087
  have p0093 :=
    @gSimprd
      (.classMem (.cv x) (synCfv (synC2nd) (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
              (synC0)))))
      (.classEq (synCfv (synC1st) (synChnwcutcode (synCfv (synC1st)
              (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0)))) (synCfv (synC2nd)
              (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0)))) (.cv x))) (synCin (synCfv (synC1st)
            (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0)))) (synCxp (synCin (synCfv (synC2nd)
                (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
                  (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                    (synC0)))) (synCima (synCcnv (synCdif (synCfv (synC1st)
                      (synCif (.classMem (.cv u) (synChwcn A)) (.cv u) (synCop
                          (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                          (synC0)))) (synCid))) (synCsn (.cv x)))) (synCin
              (synCfv (synC2nd) (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
                  (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                    (synC0)))) (synCima (synCcnv (synCdif (synCfv (synC1st)
                      (synCif (.classMem (.cv u) (synChwcn A)) (.cv u) (synCop
                          (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                          (synC0)))) (synCid))) (synCsn (.cv x)))))))
      (.classEq (synCfv (synC2nd) (synChnwcutcode (synCfv (synC1st)
              (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0)))) (synCfv (synC2nd)
              (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0)))) (.cv x))) (synCin (synCfv (synC2nd)
            (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0)))) (synCima (synCcnv (synCdif (synCfv (synC1st)
                  (synCif (.classMem (.cv u) (synChwcn A)) (.cv u) (synCop
                      (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                      (synC0)))) (synCid))) (synCsn (.cv x)))))
      p0084
  have p0094 :=
    @gEqcomd
      (.classMem (.cv x) (synCfv (synC2nd) (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
              (synC0)))))
      (synCfv (synC2nd) (synChnwcutcode (synCfv (synC1st)
            (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0)))) (synCfv (synC2nd)
            (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0)))) (.cv x)))
      (synCin (synCfv (synC2nd) (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
        (synCima (synCcnv (synCdif (synCfv (synC1st)
                (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
                  (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                    (synC0)))) (synCid))) (synCsn (.cv x))))
      p0093
  have p0095 :=
    @gIsoeq5
      (synCfv (synC2nd) (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
          (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
      (synCin (synCfv (synC2nd) (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
        (synCima (synCcnv (synCdif (synCfv (synC1st)
                (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
                  (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                    (synC0)))) (synCid))) (synCsn (.cv x))))
      (synCfv (synC2nd) (synChnwcutcode (synCfv (synC1st)
            (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0)))) (synCfv (synC2nd)
            (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0)))) (.cv x)))
      (synCfv (synC1st) (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
          (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
      (synCfv (synC1st) (synChnwcutcode (synCfv (synC1st)
            (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0)))) (synCfv (synC2nd)
            (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0)))) (.cv x)))
      (.cv h)
  have p0096 :=
    @gSyl
      (.classMem (.cv x) (synCfv (synC2nd) (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
              (synC0)))))
      (.classEq (synCin (synCfv (synC2nd) (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0)))) (synCima (synCcnv (synCdif (synCfv (synC1st)
                  (synCif (.classMem (.cv u) (synChwcn A)) (.cv u) (synCop
                      (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                      (synC0)))) (synCid))) (synCsn (.cv x)))) (synCfv (synC2nd)
          (synChnwcutcode (synCfv (synC1st)
              (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0)))) (synCfv (synC2nd)
              (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0)))) (.cv x))))
      (synWb (synWiso (.cv h) (synCfv (synC1st)
            (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0)))) (synCfv (synC1st) (synChnwcutcode (synCfv (synC1st)
                (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
                  (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                    (synC0)))) (synCfv (synC2nd)
                (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
                  (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                    (synC0)))) (.cv x))) (synCfv (synC2nd)
            (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0)))) (synCin (synCfv (synC2nd)
              (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0)))) (synCima (synCcnv (synCdif (synCfv (synC1st)
                    (synCif (.classMem (.cv u) (synChwcn A)) (.cv u) (synCop
                        (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                        (synC0)))) (synCid))) (synCsn (.cv x))))) (synWiso (.cv h)
          (synCfv (synC1st) (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0)))) (synCfv (synC1st) (synChnwcutcode (synCfv (synC1st)
                (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
                  (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                    (synC0)))) (synCfv (synC2nd)
                (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
                  (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                    (synC0)))) (.cv x))) (synCfv (synC2nd)
            (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0)))) (synCfv (synC2nd) (synChnwcutcode (synCfv (synC1st)
                (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
                  (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                    (synC0)))) (synCfv (synC2nd)
                (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
                  (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                    (synC0)))) (.cv x)))))
      p0094 p0095
  have p0097 :=
    @gBitrd
      (.classMem (.cv x) (synCfv (synC2nd) (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
              (synC0)))))
      (synWiso (.cv h) (synCfv (synC1st) (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
        (synCin (synCfv (synC1st) (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0)))) (synCxp (synCin (synCfv (synC2nd)
                (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
                  (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                    (synC0)))) (synCima (synCcnv (synCdif (synCfv (synC1st)
                      (synCif (.classMem (.cv u) (synChwcn A)) (.cv u) (synCop
                          (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                          (synC0)))) (synCid))) (synCsn (.cv x)))) (synCin
              (synCfv (synC2nd) (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
                  (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                    (synC0)))) (synCima (synCcnv (synCdif (synCfv (synC1st)
                      (synCif (.classMem (.cv u) (synChwcn A)) (.cv u) (synCop
                          (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                          (synC0)))) (synCid))) (synCsn (.cv x)))))) (synCfv (synC2nd)
          (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
        (synCin (synCfv (synC2nd) (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0)))) (synCima (synCcnv (synCdif (synCfv (synC1st)
                  (synCif (.classMem (.cv u) (synChwcn A)) (.cv u) (synCop
                      (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                      (synC0)))) (synCid))) (synCsn (.cv x)))))
      (synWiso (.cv h) (synCfv (synC1st) (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
        (synCfv (synC1st) (synChnwcutcode (synCfv (synC1st)
              (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0)))) (synCfv (synC2nd)
              (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0)))) (.cv x))) (synCfv (synC2nd)
          (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
        (synCin (synCfv (synC2nd) (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0)))) (synCima (synCcnv (synCdif (synCfv (synC1st)
                  (synCif (.classMem (.cv u) (synChwcn A)) (.cv u) (synCop
                      (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                      (synC0)))) (synCid))) (synCsn (.cv x)))))
      (synWiso (.cv h) (synCfv (synC1st) (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
        (synCfv (synC1st) (synChnwcutcode (synCfv (synC1st)
              (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0)))) (synCfv (synC2nd)
              (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0)))) (.cv x))) (synCfv (synC2nd)
          (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
        (synCfv (synC2nd) (synChnwcutcode (synCfv (synC1st)
              (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0)))) (synCfv (synC2nd)
              (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0)))) (.cv x))))
      p0088 p0096
  have p0098 :=
    @gExbidv
      (.classMem (.cv x) (synCfv (synC2nd) (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
              (synC0)))))
      (synWiso (.cv h) (synCfv (synC1st) (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
        (synCin (synCfv (synC1st) (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0)))) (synCxp (synCin (synCfv (synC2nd)
                (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
                  (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                    (synC0)))) (synCima (synCcnv (synCdif (synCfv (synC1st)
                      (synCif (.classMem (.cv u) (synChwcn A)) (.cv u) (synCop
                          (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                          (synC0)))) (synCid))) (synCsn (.cv x)))) (synCin
              (synCfv (synC2nd) (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
                  (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                    (synC0)))) (synCima (synCcnv (synCdif (synCfv (synC1st)
                      (synCif (.classMem (.cv u) (synChwcn A)) (.cv u) (synCop
                          (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                          (synC0)))) (synCid))) (synCsn (.cv x)))))) (synCfv (synC2nd)
          (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
        (synCin (synCfv (synC2nd) (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0)))) (synCima (synCcnv (synCdif (synCfv (synC1st)
                  (synCif (.classMem (.cv u) (synChwcn A)) (.cv u) (synCop
                      (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                      (synC0)))) (synCid))) (synCsn (.cv x)))))
      (synWiso (.cv h) (synCfv (synC1st) (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
        (synCfv (synC1st) (synChnwcutcode (synCfv (synC1st)
              (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0)))) (synCfv (synC2nd)
              (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0)))) (.cv x))) (synCfv (synC2nd)
          (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
        (synCfv (synC2nd) (synChnwcutcode (synCfv (synC1st)
              (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0)))) (synCfv (synC2nd)
              (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0)))) (.cv x))))
      h dv_cache_0016 p0097
  have p0100 :=
    @gA1i
      (.classMem (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
          (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
        (synChwcn A))
      (.classMem (.cv x) (synCfv (synC2nd) (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
              (synC0)))))
      p0008
  have p0104 :=
    @gHnwcutcodecnclndv (.cv x)
      (synCfv (synC2nd) (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
          (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
      (synCfv (synC1st) (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
          (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
      p0083
  have p0106 :=
    @gHwcnbaseclndv A
      (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
        (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
  have p0107 := Nominal.mp p0006 p0106
  have p0108 :=
    @gHwcnssbase A
      (synCfv (synC2nd) (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
          (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
      p0107
  have p0109 :=
    @gSsel
      (synChwcn (synCfv (synC2nd) (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
              (synC0)))))
      (synChwcn A)
      (synChnwcutcode (synCfv (synC1st) (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
        (synCfv (synC2nd) (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
        (.cv x))
  have p0110 := Nominal.mp p0108 p0109
  have p0111 :=
    @gSyl
      (.classMem (.cv x) (synCfv (synC2nd) (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
              (synC0)))))
      (.classMem (synChnwcutcode (synCfv (synC1st)
            (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0)))) (synCfv (synC2nd)
            (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0)))) (.cv x)) (synChwcn (synCfv (synC2nd)
            (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0))))))
      (.classMem (synChnwcutcode (synCfv (synC1st)
            (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0)))) (synCfv (synC2nd)
            (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0)))) (.cv x)) (synChwcn A))
      p0104 p0110
  have p0112 :=
    @gJca
      (.classMem (.cv x) (synCfv (synC2nd) (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
              (synC0)))))
      (.classMem (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
          (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
        (synChwcn A))
      (.classMem (synChnwcutcode (synCfv (synC1st)
            (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0)))) (synCfv (synC2nd)
            (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0)))) (.cv x)) (synChwcn A))
      p0100 p0111
  have p0113 :=
    @gHwnisodirectisobclndv A
      (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
        (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
      (synChnwcutcode (synCfv (synC1st) (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
        (synCfv (synC2nd) (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
        (.cv x))
      h dv_cache_0001 dv_cache_0011 dv_cache_0017
  have p0114 :=
    @gSyl
      (.classMem (.cv x) (synCfv (synC2nd) (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
              (synC0)))))
      (synWa (.classMem (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
          (synChwcn A)) (.classMem (synChnwcutcode (synCfv (synC1st)
              (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0)))) (synCfv (synC2nd)
              (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0)))) (.cv x)) (synChwcn A)))
      (synWb (synWbr (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
          (synChwniso A) (synChnwcutcode (synCfv (synC1st)
              (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0)))) (synCfv (synC2nd)
              (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0)))) (.cv x))) (synWex h (synWiso (.cv h) (synCfv (synC1st)
              (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0)))) (synCfv (synC1st) (synChnwcutcode (synCfv (synC1st)
                  (synCif (.classMem (.cv u) (synChwcn A)) (.cv u) (synCop
                      (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                      (synC0)))) (synCfv (synC2nd)
                  (synCif (.classMem (.cv u) (synChwcn A)) (.cv u) (synCop
                      (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                      (synC0)))) (.cv x))) (synCfv (synC2nd)
              (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0)))) (synCfv (synC2nd) (synChnwcutcode (synCfv (synC1st)
                  (synCif (.classMem (.cv u) (synChwcn A)) (.cv u) (synCop
                      (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                      (synC0)))) (synCfv (synC2nd)
                  (synCif (.classMem (.cv u) (synChwcn A)) (.cv u) (synCop
                      (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                      (synC0)))) (.cv x))))))
      p0112 p0113
  have p0115 :=
    @gBicomd
      (.classMem (.cv x) (synCfv (synC2nd) (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
              (synC0)))))
      (synWbr (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
          (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
        (synChwniso A) (synChnwcutcode (synCfv (synC1st)
            (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0)))) (synCfv (synC2nd)
            (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0)))) (.cv x)))
      (synWex h (synWiso (.cv h) (synCfv (synC1st)
            (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0)))) (synCfv (synC1st) (synChnwcutcode (synCfv (synC1st)
                (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
                  (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                    (synC0)))) (synCfv (synC2nd)
                (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
                  (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                    (synC0)))) (.cv x))) (synCfv (synC2nd)
            (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0)))) (synCfv (synC2nd) (synChnwcutcode (synCfv (synC1st)
                (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
                  (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                    (synC0)))) (synCfv (synC2nd)
                (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
                  (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                    (synC0)))) (.cv x)))))
      p0114
  have p0116 :=
    @gBitrd
      (.classMem (.cv x) (synCfv (synC2nd) (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
              (synC0)))))
      (synWex h (synWiso (.cv h) (synCfv (synC1st)
            (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0)))) (synCin (synCfv (synC1st)
              (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0)))) (synCxp (synCin (synCfv (synC2nd)
                  (synCif (.classMem (.cv u) (synChwcn A)) (.cv u) (synCop
                      (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                      (synC0)))) (synCima (synCcnv (synCdif (synCfv (synC1st)
                        (synCif (.classMem (.cv u) (synChwcn A)) (.cv u) (synCop
                            (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                            (synC0)))) (synCid))) (synCsn (.cv x)))) (synCin
                (synCfv (synC2nd) (synCif (.classMem (.cv u) (synChwcn A)) (.cv u) (synCop
                      (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                      (synC0)))) (synCima (synCcnv (synCdif (synCfv (synC1st)
                        (synCif (.classMem (.cv u) (synChwcn A)) (.cv u) (synCop
                            (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                            (synC0)))) (synCid))) (synCsn (.cv x)))))) (synCfv (synC2nd)
            (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0)))) (synCin (synCfv (synC2nd)
              (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0)))) (synCima (synCcnv (synCdif (synCfv (synC1st)
                    (synCif (.classMem (.cv u) (synChwcn A)) (.cv u) (synCop
                        (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                        (synC0)))) (synCid))) (synCsn (.cv x))))))
      (synWex h (synWiso (.cv h) (synCfv (synC1st)
            (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0)))) (synCfv (synC1st) (synChnwcutcode (synCfv (synC1st)
                (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
                  (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                    (synC0)))) (synCfv (synC2nd)
                (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
                  (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                    (synC0)))) (.cv x))) (synCfv (synC2nd)
            (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0)))) (synCfv (synC2nd) (synChnwcutcode (synCfv (synC1st)
                (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
                  (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                    (synC0)))) (synCfv (synC2nd)
                (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
                  (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                    (synC0)))) (.cv x)))))
      (synWbr (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
          (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
        (synChwniso A) (synChnwcutcode (synCfv (synC1st)
            (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0)))) (synCfv (synC2nd)
            (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0)))) (.cv x)))
      p0098 p0115
  have p0117 :=
    @gRexbiia
      (synWex h (synWiso (.cv h) (synCfv (synC1st)
            (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0)))) (synCin (synCfv (synC1st)
              (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0)))) (synCxp (synCin (synCfv (synC2nd)
                  (synCif (.classMem (.cv u) (synChwcn A)) (.cv u) (synCop
                      (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                      (synC0)))) (synCima (synCcnv (synCdif (synCfv (synC1st)
                        (synCif (.classMem (.cv u) (synChwcn A)) (.cv u) (synCop
                            (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                            (synC0)))) (synCid))) (synCsn (.cv x)))) (synCin
                (synCfv (synC2nd) (synCif (.classMem (.cv u) (synChwcn A)) (.cv u) (synCop
                      (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                      (synC0)))) (synCima (synCcnv (synCdif (synCfv (synC1st)
                        (synCif (.classMem (.cv u) (synChwcn A)) (.cv u) (synCop
                            (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                            (synC0)))) (synCid))) (synCsn (.cv x)))))) (synCfv (synC2nd)
            (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0)))) (synCin (synCfv (synC2nd)
              (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0)))) (synCima (synCcnv (synCdif (synCfv (synC1st)
                    (synCif (.classMem (.cv u) (synChwcn A)) (.cv u) (synCop
                        (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                        (synC0)))) (synCid))) (synCsn (.cv x))))))
      (synWbr (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
          (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
        (synChwniso A) (synChnwcutcode (synCfv (synC1st)
            (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0)))) (synCfv (synC2nd)
            (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0)))) (.cv x)))
      x
      (synCfv (synC2nd) (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
          (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
      p0116
  have p0118 :=
    @gBiimpi
      (synWrex x (synCfv (synC2nd) (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
        (synWex h (synWiso (.cv h) (synCfv (synC1st)
              (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0)))) (synCin (synCfv (synC1st)
                (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
                  (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                    (synC0)))) (synCxp (synCin (synCfv (synC2nd)
                    (synCif (.classMem (.cv u) (synChwcn A)) (.cv u) (synCop
                        (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                        (synC0)))) (synCima (synCcnv (synCdif (synCfv (synC1st)
                          (synCif (.classMem (.cv u) (synChwcn A)) (.cv u) (synCop
                              (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                              (synC0)))) (synCid))) (synCsn (.cv x)))) (synCin
                  (synCfv (synC2nd) (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
                      (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                        (synC0)))) (synCima (synCcnv (synCdif (synCfv (synC1st)
                          (synCif (.classMem (.cv u) (synChwcn A)) (.cv u) (synCop
                              (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                              (synC0)))) (synCid))) (synCsn (.cv x)))))) (synCfv (synC2nd)
              (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0)))) (synCin (synCfv (synC2nd)
                (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
                  (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                    (synC0)))) (synCima (synCcnv (synCdif (synCfv (synC1st)
                      (synCif (.classMem (.cv u) (synChwcn A)) (.cv u) (synCop
                          (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                          (synC0)))) (synCid))) (synCsn (.cv x)))))))
      (synWrex x (synCfv (synC2nd) (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
        (synWbr (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
          (synChwniso A) (synChnwcutcode (synCfv (synC1st)
              (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0)))) (synCfv (synC2nd)
              (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0)))) (.cv x))))
      p0117
  have p0119 :=
    @gOlc
      (synWrex x (synCfv (synC2nd) (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
        (synWbr (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
          (synChwniso A) (synChnwcutcode (synCfv (synC1st)
              (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0)))) (synCfv (synC2nd)
              (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0)))) (.cv x))))
      (synWbr (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
          (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
        (synChwniso A) (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
          (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
  have p0120 :=
    @gSyl
      (synWrex x (synCfv (synC2nd) (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
        (synWex h (synWiso (.cv h) (synCfv (synC1st)
              (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0)))) (synCin (synCfv (synC1st)
                (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
                  (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                    (synC0)))) (synCxp (synCin (synCfv (synC2nd)
                    (synCif (.classMem (.cv u) (synChwcn A)) (.cv u) (synCop
                        (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                        (synC0)))) (synCima (synCcnv (synCdif (synCfv (synC1st)
                          (synCif (.classMem (.cv u) (synChwcn A)) (.cv u) (synCop
                              (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                              (synC0)))) (synCid))) (synCsn (.cv x)))) (synCin
                  (synCfv (synC2nd) (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
                      (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                        (synC0)))) (synCima (synCcnv (synCdif (synCfv (synC1st)
                          (synCif (.classMem (.cv u) (synChwcn A)) (.cv u) (synCop
                              (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                              (synC0)))) (synCid))) (synCsn (.cv x)))))) (synCfv (synC2nd)
              (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0)))) (synCin (synCfv (synC2nd)
                (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
                  (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                    (synC0)))) (synCima (synCcnv (synCdif (synCfv (synC1st)
                      (synCif (.classMem (.cv u) (synChwcn A)) (.cv u) (synCop
                          (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                          (synC0)))) (synCid))) (synCsn (.cv x)))))))
      (synWrex x (synCfv (synC2nd) (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
        (synWbr (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
          (synChwniso A) (synChnwcutcode (synCfv (synC1st)
              (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0)))) (synCfv (synC2nd)
              (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0)))) (.cv x))))
      (synWo (synWbr (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
          (synChwniso A) (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
        (synWrex x (synCfv (synC2nd) (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0)))) (synWbr (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0))) (synChwniso A) (synChnwcutcode (synCfv (synC1st)
                (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
                  (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                    (synC0)))) (synCfv (synC2nd)
                (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
                  (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                    (synC0)))) (.cv x)))))
      p0118 p0119
  have p0122 :=
    @gId
      (.classMem (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
          (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
        (synChwcn A))
  have p0124 :=
    @gA1i
      (.classMem (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
          (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
        (synChwcn A))
      (.classMem (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
          (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
        (synChwcn A))
      p0006
  have p0125 :=
    @gJca
      (.classMem (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
          (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
        (synChwcn A))
      (.classMem (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
          (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
        (synChwcn A))
      (.classMem (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
          (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
        (synChwcn A))
      p0122 p0124
  have p0126 := Nominal.mp p0008 p0125
  have p0127 :=
    @gHncodecmpsetstrictcutsemclndv x A
      (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
        (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
      (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
        (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
      dv_cache_0004 dv_cache_0013 dv_cache_0012
  have p0128 := Nominal.mp p0126 p0127
  have p0129 :=
    @gBiimpri
      (synWbr (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
          (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
        (synChncodecmpset A) (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
          (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
      (synWo (synWbr (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
          (synChwniso A) (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
        (synWrex x (synCfv (synC2nd) (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0)))) (synWbr (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0))) (synChwniso A) (synChnwcutcode (synCfv (synC1st)
                (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
                  (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                    (synC0)))) (synCfv (synC2nd)
                (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
                  (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                    (synC0)))) (.cv x)))))
      p0128
  have p0130 :=
    @gSyl
      (synWrex x (synCfv (synC2nd) (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
        (synWex h (synWiso (.cv h) (synCfv (synC1st)
              (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0)))) (synCin (synCfv (synC1st)
                (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
                  (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                    (synC0)))) (synCxp (synCin (synCfv (synC2nd)
                    (synCif (.classMem (.cv u) (synChwcn A)) (.cv u) (synCop
                        (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                        (synC0)))) (synCima (synCcnv (synCdif (synCfv (synC1st)
                          (synCif (.classMem (.cv u) (synChwcn A)) (.cv u) (synCop
                              (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                              (synC0)))) (synCid))) (synCsn (.cv x)))) (synCin
                  (synCfv (synC2nd) (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
                      (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                        (synC0)))) (synCima (synCcnv (synCdif (synCfv (synC1st)
                          (synCif (.classMem (.cv u) (synChwcn A)) (.cv u) (synCop
                              (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                              (synC0)))) (synCid))) (synCsn (.cv x)))))) (synCfv (synC2nd)
              (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0)))) (synCin (synCfv (synC2nd)
                (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
                  (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                    (synC0)))) (synCima (synCcnv (synCdif (synCfv (synC1st)
                      (synCif (.classMem (.cv u) (synChwcn A)) (.cv u) (synCop
                          (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                          (synC0)))) (synCid))) (synCsn (.cv x)))))))
      (synWo (synWbr (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
          (synChwniso A) (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
        (synWrex x (synCfv (synC2nd) (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0)))) (synWbr (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0))) (synChwniso A) (synChnwcutcode (synCfv (synC1st)
                (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
                  (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                    (synC0)))) (synCfv (synC2nd)
                (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
                  (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                    (synC0)))) (.cv x)))))
      (synWbr (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
          (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
        (synChncodecmpset A) (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
          (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
      p0120 p0129
  have p0131 :=
    @gOlc
      (synWbr (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
          (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
        (synChncodecmpset A) (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
          (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
      (synWbr (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
          (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
        (synChncodecmpset A) (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
          (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
  have p0132 :=
    @gSyl
      (synWrex x (synCfv (synC2nd) (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
        (synWex h (synWiso (.cv h) (synCfv (synC1st)
              (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0)))) (synCin (synCfv (synC1st)
                (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
                  (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                    (synC0)))) (synCxp (synCin (synCfv (synC2nd)
                    (synCif (.classMem (.cv u) (synChwcn A)) (.cv u) (synCop
                        (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                        (synC0)))) (synCima (synCcnv (synCdif (synCfv (synC1st)
                          (synCif (.classMem (.cv u) (synChwcn A)) (.cv u) (synCop
                              (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                              (synC0)))) (synCid))) (synCsn (.cv x)))) (synCin
                  (synCfv (synC2nd) (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
                      (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                        (synC0)))) (synCima (synCcnv (synCdif (synCfv (synC1st)
                          (synCif (.classMem (.cv u) (synChwcn A)) (.cv u) (synCop
                              (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                              (synC0)))) (synCid))) (synCsn (.cv x)))))) (synCfv (synC2nd)
              (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0)))) (synCin (synCfv (synC2nd)
                (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
                  (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                    (synC0)))) (synCima (synCcnv (synCdif (synCfv (synC1st)
                      (synCif (.classMem (.cv u) (synChwcn A)) (.cv u) (synCop
                          (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                          (synC0)))) (synCid))) (synCsn (.cv x)))))))
      (synWbr (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
          (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
        (synChncodecmpset A) (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
          (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
      (synWo (synWbr (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
          (synChncodecmpset A) (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
        (synWbr (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
          (synChncodecmpset A) (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
              (synC0)))))
      p0130 p0131
  have p0133 :=
    @gN3jaoi
      (synWex h (synWiso (.cv h) (synCfv (synC1st)
            (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0)))) (synCfv (synC1st)
            (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0)))) (synCfv (synC2nd)
            (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0)))) (synCfv (synC2nd)
            (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0))))))
      (synWo (synWbr (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
          (synChncodecmpset A) (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
        (synWbr (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
          (synChncodecmpset A) (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
              (synC0)))))
      (synWrex x (synCfv (synC2nd) (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
        (synWex h (synWiso (.cv h) (synCfv (synC1st)
              (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0)))) (synCin (synCfv (synC1st)
                (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
                  (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                    (synC0)))) (synCxp (synCin (synCfv (synC2nd)
                    (synCif (.classMem (.cv v) (synChwcn A)) (.cv v) (synCop
                        (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                        (synC0)))) (synCima (synCcnv (synCdif (synCfv (synC1st)
                          (synCif (.classMem (.cv v) (synChwcn A)) (.cv v) (synCop
                              (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                              (synC0)))) (synCid))) (synCsn (.cv x)))) (synCin
                  (synCfv (synC2nd) (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
                      (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                        (synC0)))) (synCima (synCcnv (synCdif (synCfv (synC1st)
                          (synCif (.classMem (.cv v) (synChwcn A)) (.cv v) (synCop
                              (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                              (synC0)))) (synCid))) (synCsn (.cv x)))))) (synCfv (synC2nd)
              (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0)))) (synCin (synCfv (synC2nd)
                (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
                  (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                    (synC0)))) (synCima (synCcnv (synCdif (synCfv (synC1st)
                      (synCif (.classMem (.cv v) (synChwcn A)) (.cv v) (synCop
                          (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                          (synC0)))) (synCid))) (synCsn (.cv x)))))))
      (synWrex x (synCfv (synC2nd) (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
        (synWex h (synWiso (.cv h) (synCfv (synC1st)
              (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0)))) (synCin (synCfv (synC1st)
                (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
                  (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                    (synC0)))) (synCxp (synCin (synCfv (synC2nd)
                    (synCif (.classMem (.cv u) (synChwcn A)) (.cv u) (synCop
                        (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                        (synC0)))) (synCima (synCcnv (synCdif (synCfv (synC1st)
                          (synCif (.classMem (.cv u) (synChwcn A)) (.cv u) (synCop
                              (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                              (synC0)))) (synCid))) (synCsn (.cv x)))) (synCin
                  (synCfv (synC2nd) (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
                      (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                        (synC0)))) (synCima (synCcnv (synCdif (synCfv (synC1st)
                          (synCif (.classMem (.cv u) (synChwcn A)) (.cv u) (synCop
                              (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                              (synC0)))) (synCid))) (synCsn (.cv x)))))) (synCfv (synC2nd)
              (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
                (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                  (synC0)))) (synCin (synCfv (synC2nd)
                (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
                  (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                    (synC0)))) (synCima (synCcnv (synCdif (synCfv (synC1st)
                      (synCif (.classMem (.cv u) (synChwcn A)) (.cv u) (synCop
                          (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                          (synC0)))) (synCid))) (synCsn (.cv x)))))))
      p0028 p0080 p0132
  have p0134 := Nominal.mp p0005 p0133
  have p0135 :=
    @gA1i
      (synWo (synWbr (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
          (synChncodecmpset A) (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
        (synWbr (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
          (synChncodecmpset A) (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
              (synC0)))))
      (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))) p0134
  have p0136 :=
    @gSimpl (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))
  have p0137 :=
    @gIftrue (.classMem (.cv u) (synChwcn A)) (.cv u)
      (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))
  have p0138 :=
    @gSyl (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
      (.classMem (.cv u) (synChwcn A))
      (.classEq (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
          (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
        (.cv u))
      p0136 p0137
  have p0139 :=
    @gSimpr (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))
  have p0140 :=
    @gIftrue (.classMem (.cv v) (synChwcn A)) (.cv v)
      (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))
  have p0141 :=
    @gSyl (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
      (.classMem (.cv v) (synChwcn A))
      (.classEq (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
          (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
        (.cv v))
      p0139 p0140
  have p0142 :=
    @gBreq12d
      (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
      (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
        (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
      (.cv u)
      (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
        (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
      (.cv v) (synChncodecmpset A) p0138 p0141
  have p0149 :=
    @gBreq12d
      (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
      (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
        (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
      (.cv v)
      (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
        (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
      (.cv u) (synChncodecmpset A) p0141 p0138
  have p0150 :=
    @gOrbi12d
      (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
      (synWbr (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
          (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
        (synChncodecmpset A) (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
          (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
      (synWbr (.cv u) (synChncodecmpset A) (.cv v))
      (synWbr (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
          (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
        (synChncodecmpset A) (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
          (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
      (synWbr (.cv v) (synChncodecmpset A) (.cv u)) p0142 p0149
  have p0151 :=
    @gMpbid (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
      (synWo (synWbr (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
          (synChncodecmpset A) (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
        (synWbr (synCif (.classMem (.cv v) (synChwcn A)) (.cv v)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
          (synChncodecmpset A) (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
              (synC0)))))
      (synWo (synWbr (.cv u) (synChncodecmpset A) (.cv v))
        (synWbr (.cv v) (synChncodecmpset A) (.cv u)))
      p0135 p0150
  have p0152 :=
    @gSyl
      (synW3a (.classMem A (synCvv)) (.classMem (.cv u) (synChwcn A))
        (.classMem (.cv v) (synChwcn A)))
      (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
      (synWo (synWbr (.cv u) (synChncodecmpset A) (.cv v))
        (synWbr (.cv v) (synChncodecmpset A) (.cv u)))
      p0004 p0151
  have p0153 :=
    @gConnexrd (.classMem A (synCvv)) u v (synChwcn A) (synChncodecmpset A) (synCvv)
      (synCvv) dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
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

/-- Checked nominal proof certificate identified upstream as `g_hnwcutcodenestndv`. -/
@[expose]
noncomputable def gHnwcutcodenestndv (x : Var) (y : Var) (D : Class) (R : Class) :
    Nominal.NPrf
      (.imp (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (.classEq (synChnwcutcode (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (.cv x))
          (synChnwcutcode R D (.cv x)))) :=
  by
  have p0000 :=
    (Nominal.classEqRefl (synChnwcutcode (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (.cv x)))
  have p0001 :=
    @gA1i
      (.classEq (synChnwcutcode (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (.cv x))
        (synCop (synCin (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
            (synCxp (synCin
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCima (synCcnv (synCdif (synCin R (synCxp (synCin D
                            (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                          (synCin D (synCima (synCcnv (synCdif R (synCid)))
                              (synCsn (.cv y)))))) (synCid))) (synCsn (.cv x)))) (synCin
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCima (synCcnv (synCdif (synCin R (synCxp (synCin D
                            (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                          (synCin D (synCima (synCcnv (synCdif R (synCid)))
                              (synCsn (.cv y)))))) (synCid))) (synCsn (.cv x)))))) (synCin
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCima
              (synCcnv (synCdif (synCin R (synCxp (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                      (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
                  (synCid))) (synCsn (.cv x))))))
      (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      p0000
  have p0002 := @gStrictsegcut x y D R
  have p0004 :=
    @gXpeq12d
      (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (synCin (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
        (synCima (synCcnv (synCdif (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
              (synCid))) (synCsn (.cv x))))
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
      (synCin (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
        (synCima (synCcnv (synCdif (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
              (synCid))) (synCsn (.cv x))))
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) p0002
      p0002
  have p0005 :=
    @gIneq2
      (synCxp (synCin
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCima
            (synCcnv (synCdif (synCin R (synCxp (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
                (synCid))) (synCsn (.cv x)))) (synCin
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCima
            (synCcnv (synCdif (synCin R (synCxp (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
                (synCid))) (synCsn (.cv x)))))
      (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      (synCin R (synCxp
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
  have p0006 :=
    @gSyl
      (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (.classEq (synCxp (synCin
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCima
              (synCcnv (synCdif (synCin R (synCxp (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                      (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
                  (synCid))) (synCsn (.cv x)))) (synCin
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCima
              (synCcnv (synCdif (synCin R (synCxp (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                      (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
                  (synCid))) (synCsn (.cv x))))) (synCxp
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (.classEq (synCin (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synCxp (synCin
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCima (synCcnv (synCdif (synCin R (synCxp (synCin D
                          (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                        (synCin D (synCima (synCcnv (synCdif R (synCid)))
                            (synCsn (.cv y)))))) (synCid))) (synCsn (.cv x)))) (synCin
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCima (synCcnv (synCdif (synCin R (synCxp (synCin D
                          (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                        (synCin D (synCima (synCcnv (synCdif R (synCid)))
                            (synCsn (.cv y)))))) (synCid))) (synCsn (.cv x)))))) (synCin
          (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))))
      p0004 p0005
  have p0008 :=
    @gInss1 (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
      (synCima (synCcnv (synCdif (synCin R (synCxp
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
            (synCid))) (synCsn (.cv x)))
  have p0009 :=
    @gA1i
      (synWss (synCin
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCima
            (synCcnv (synCdif (synCin R (synCxp (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
                (synCid))) (synCsn (.cv x))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
      (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      p0008
  have p0010 :=
    @gEqsstr3d
      (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
      (synCin (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
        (synCima (synCcnv (synCdif (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
              (synCid))) (synCsn (.cv x))))
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) p0002
      p0009
  have p0011 := @gStrictsegrestrnest x y D R
  have p0012 :=
    @gSyl
      (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (synWss (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))))
      (.classEq (synCin (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))))
      p0010 p0011
  have p0013 :=
    @gEqtrd
      (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (synCin (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (synCxp (synCin
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCima
              (synCcnv (synCdif (synCin R (synCxp (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                      (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
                  (synCid))) (synCsn (.cv x)))) (synCin
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCima
              (synCcnv (synCdif (synCin R (synCxp (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                      (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
                  (synCid))) (synCsn (.cv x))))))
      (synCin (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (synCin R (synCxp
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      p0006 p0012
  have p0015 :=
    @gOpeq12d
      (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (synCin (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (synCxp (synCin
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCima
              (synCcnv (synCdif (synCin R (synCxp (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                      (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
                  (synCid))) (synCsn (.cv x)))) (synCin
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCima
              (synCcnv (synCdif (synCin R (synCxp (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                      (synCin D
                        (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
                  (synCid))) (synCsn (.cv x))))))
      (synCin R (synCxp
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (synCin (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
        (synCima (synCcnv (synCdif (synCin R (synCxp (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCin D
                    (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
              (synCid))) (synCsn (.cv x))))
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))) p0013
      p0002
  have p0016 := (Nominal.classEqRefl (synChnwcutcode R D (.cv x)))
  have p0017 :=
    @gA1i
      (.classEq (synChnwcutcode R D (.cv x)) (synCop (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      p0016
  have p0018 :=
    @gEqcomd
      (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (synChnwcutcode R D (.cv x))
      (synCop (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      p0017
  have p0019 :=
    @gN3eqtrd
      (synWa (synWa (synWbr R (synCwe) D) (.classMem (.cv y) D)) (.classMem (.cv x)
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
      (synChnwcutcode (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (.cv x))
      (synCop (synCin (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
          (synCxp (synCin
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCima (synCcnv (synCdif (synCin R (synCxp (synCin D
                          (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                        (synCin D (synCima (synCcnv (synCdif R (synCid)))
                            (synCsn (.cv y)))))) (synCid))) (synCsn (.cv x)))) (synCin
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
              (synCima (synCcnv (synCdif (synCin R (synCxp (synCin D
                          (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))
                        (synCin D (synCima (synCcnv (synCdif R (synCid)))
                            (synCsn (.cv y)))))) (synCid))) (synCsn (.cv x)))))) (synCin
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCima
            (synCcnv (synCdif (synCin R (synCxp (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y)))) (synCin D
                      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv y))))))
                (synCid))) (synCsn (.cv x)))))
      (synCop (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      (synChnwcutcode R D (.cv x)) p0001 p0015 p0018
  exact p0019

/-- Checked nominal proof certificate identified upstream as `g_hnwcutcodeeq12ndv`. -/
@[expose]
noncomputable def gHnwcutcodeeq12ndv (x : Var) (D : Class) (R : Class) (S : Class)
    (E : Class) :
    Nominal.NPrf
      (.imp (synWa (.classEq R S) (.classEq D E))
        (.classEq (synChnwcutcode R D (.cv x)) (synChnwcutcode S E (.cv x)))) :=
  by
  have p0000 := (Nominal.classEqRefl (synChnwcutcode R D (.cv x)))
  have p0001 :=
    @gA1i
      (.classEq (synChnwcutcode R D (.cv x)) (synCop (synCin R (synCxp
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
              (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (synWa (.classEq R S) (.classEq D E)) p0000
  have p0002 := @gSimpl (.classEq R S) (.classEq D E)
  have p0003 := @gSimpr (.classEq R S) (.classEq D E)
  have p0005 := @gDifeq1d (synWa (.classEq R S) (.classEq D E)) R S (synCid) p0002
  have p0006 :=
    @gCnveqd (synWa (.classEq R S) (.classEq D E)) (synCdif R (synCid))
      (synCdif S (synCid)) p0005
  have p0007 :=
    @gImaeq1d (synWa (.classEq R S) (.classEq D E)) (synCcnv (synCdif R (synCid)))
      (synCcnv (synCdif S (synCid))) (synCsn (.cv x)) p0006
  have p0008 :=
    @gIneq12d (synWa (.classEq R S) (.classEq D E)) D E
      (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))
      (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x))) p0003 p0007
  have p0015 :=
    @gXpeq12d (synWa (.classEq R S) (.classEq D E))
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
      (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x))))
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
      (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))) p0008
      p0008
  have p0016 :=
    @gIneq12d (synWa (.classEq R S) (.classEq D E)) R S
      (synCxp (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      (synCxp (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x))))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))
      p0002 p0015
  have p0023 :=
    @gOpeq12d (synWa (.classEq R S) (.classEq D E))
      (synCin R (synCxp
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
          (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
      (synCin S (synCxp
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x))))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x))))))
      (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
      (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))) p0016
      p0008
  have p0024 := (Nominal.classEqRefl (synChnwcutcode S E (.cv x)))
  have p0025 :=
    @gA1i
      (.classEq (synChnwcutcode S E (.cv x)) (synCop (synCin S (synCxp
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x))))
              (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x))))))
          (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x))))))
      (synWa (.classEq R S) (.classEq D E)) p0024
  have p0026 :=
    @gEqcomd (synWa (.classEq R S) (.classEq D E)) (synChnwcutcode S E (.cv x))
      (synCop (synCin S (synCxp
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x))))))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))
      p0025
  have p0027 :=
    @gN3eqtrd (synWa (.classEq R S) (.classEq D E)) (synChnwcutcode R D (.cv x))
      (synCop (synCin R (synCxp
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))
            (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x))))))
        (synCin D (synCima (synCcnv (synCdif R (synCid))) (synCsn (.cv x)))))
      (synCop (synCin S (synCxp
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x))))
            (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x))))))
        (synCin E (synCima (synCcnv (synCdif S (synCid))) (synCsn (.cv x)))))
      (synChnwcutcode S E (.cv x)) p0001 p0023 p0026
  exact p0027

/-- Checked nominal proof certificate identified upstream as `g_hnwcutcodeambientndv`. -/
@[expose]
noncomputable def gHnwcutcodeambientndv (x : Var) (u : Var) (A : Class)
    (dv_A_u : u ∉ A.fv) :
    Nominal.NPrf
      (.imp (synWa (.classMem (.cv u) (synChwcn A))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))) (.classMem
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
          (synChwcn A))) :=
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
    @gSimpr (.classMem (.cv u) (synChwcn A))
      (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
  have p0001 :=
    @gSimpl (.classMem (.cv u) (synChwcn A))
      (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))
  have p0002 :=
    @gIftrue (.classMem (.cv u) (synChwcn A)) (.cv u)
      (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))
  have p0003 :=
    @gSyl
      (synWa (.classMem (.cv u) (synChwcn A))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))
      (.classMem (.cv u) (synChwcn A))
      (.classEq (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
          (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
        (.cv u))
      p0001 p0002
  have p0004 :=
    @gFveq2d
      (synWa (.classMem (.cv u) (synChwcn A))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))
      (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
        (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
      (.cv u) (synC2nd) p0003
  have p0005 :=
    @gEleq2d
      (synWa (.classMem (.cv u) (synChwcn A))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))
      (synCfv (synC2nd) (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
          (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
      (synCfv (synC2nd) (.cv u)) (.cv x) p0004
  have p0006 :=
    @gMpbird
      (synWa (.classMem (.cv u) (synChwcn A))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))
      (.classMem (.cv x) (synCfv (synC2nd) (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
              (synC0)))))
      (.classMem (.cv x) (synCfv (synC2nd) (.cv u))) p0000 p0005
  have p0007 := @gHncodetotalleftmemndv u A dv_cache_0001
  have p0008 :=
    @gHwcnweclndv A
      (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
        (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
  have p0009 := Nominal.mp p0007 p0008
  have p0010 :=
    @gHnwcutcodecnclndv (.cv x)
      (synCfv (synC2nd) (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
          (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
      (synCfv (synC1st) (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
          (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
      p0009
  have p0012 :=
    @gHwcnbaseclndv A
      (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
        (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
  have p0013 := Nominal.mp p0007 p0012
  have p0014 :=
    @gHwcnssbase A
      (synCfv (synC2nd) (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
          (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
      p0013
  have p0015 :=
    @gSsel
      (synChwcn (synCfv (synC2nd) (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
              (synC0)))))
      (synChwcn A)
      (synChnwcutcode (synCfv (synC1st) (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
        (synCfv (synC2nd) (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
        (.cv x))
  have p0016 := Nominal.mp p0014 p0015
  have p0017 :=
    @gSyl
      (.classMem (.cv x) (synCfv (synC2nd) (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
              (synC0)))))
      (.classMem (synChnwcutcode (synCfv (synC1st)
            (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0)))) (synCfv (synC2nd)
            (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0)))) (.cv x)) (synChwcn (synCfv (synC2nd)
            (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0))))))
      (.classMem (synChnwcutcode (synCfv (synC1st)
            (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0)))) (synCfv (synC2nd)
            (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0)))) (.cv x)) (synChwcn A))
      p0010 p0016
  have p0018 :=
    @gSyl
      (synWa (.classMem (.cv u) (synChwcn A))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))
      (.classMem (.cv x) (synCfv (synC2nd) (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
              (synC0)))))
      (.classMem (synChnwcutcode (synCfv (synC1st)
            (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0)))) (synCfv (synC2nd)
            (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0)))) (.cv x)) (synChwcn A))
      p0006 p0017
  have p0022 :=
    @gFveq2d
      (synWa (.classMem (.cv u) (synChwcn A))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))
      (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
        (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0)))
      (.cv u) (synC1st) p0003
  have p0027 :=
    @gJca
      (synWa (.classMem (.cv u) (synChwcn A))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))
      (.classEq (synCfv (synC1st) (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
        (synCfv (synC1st) (.cv u)))
      (.classEq (synCfv (synC2nd) (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
        (synCfv (synC2nd) (.cv u)))
      p0022 p0004
  have p0028 :=
    @gHnwcutcodeeq12ndv x
      (synCfv (synC2nd) (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
          (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
      (synCfv (synC1st) (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
          (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
      (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
  have p0029 :=
    @gSyl
      (synWa (.classMem (.cv u) (synChwcn A))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))
      (synWa (.classEq (synCfv (synC1st) (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0)))) (synCfv (synC1st) (.cv u))) (.classEq (synCfv (synC2nd)
            (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0)))) (synCfv (synC2nd) (.cv u))))
      (.classEq (synChnwcutcode (synCfv (synC1st)
            (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0)))) (synCfv (synC2nd)
            (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0)))) (.cv x))
        (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x)))
      p0027 p0028
  have p0030 :=
    @gEleq1d
      (synWa (.classMem (.cv u) (synChwcn A))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))
      (synChnwcutcode (synCfv (synC1st) (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
        (synCfv (synC2nd) (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
            (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0))) (synC0))))
        (.cv x))
      (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
      (synChwcn A) p0029
  have p0031 :=
    @gMpbid
      (synWa (.classMem (.cv u) (synChwcn A))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))
      (.classMem (synChnwcutcode (synCfv (synC1st)
            (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0)))) (synCfv (synC2nd)
            (synCif (.classMem (.cv u) (synChwcn A)) (.cv u)
              (synCop (synCin (synCkqrel (synClefin)) (synCxp (synC0) (synC0)))
                (synC0)))) (.cv x)) (synChwcn A))
      (.classMem (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (.cv x)) (synChwcn A))
      p0018 p0030
  exact p0031


end NFChoice.DirectNominalPrf.WPPReplay

end
