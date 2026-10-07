/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NominalWPPReplayChunk017Compact001Block008

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NominalWPPReplayChunk017Compact001Part038`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_hncodecmpstrictnoreversendv`. -/
@[expose]
noncomputable def gHncodecmpstrictnoreversendv (x : Var) (v : Var) (u : Var) (A : Class)
    (dv_A_u : u ∉ A.fv) (dv_A_v : v ∉ A.fv) (dv_A_x : x ∉ A.fv) (dv_u_x : u ≠ x)
    (dv_v_x : v ≠ x) :
    Nominal.NPrf
      (.imp (synWa (.classMem A (synCvv))
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))) (.imp
          (synWrex x (synCfv (synC2nd) (.cv v)) (synWbr (.cv u) (synChwniso A)
              (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                (.cv x)))) (.neg (synWbr (.cv v) (synChncodecmpset A) (.cv u))))) :=
  by
  let proofSupport : Finset Var :=
    ({ x } : Finset Var) ∪ ({ v } : Finset Var) ∪ ({ u } : Finset Var) ∪ A.fv
  let y : Var := freshVar proofSupport 0
  let z : Var := freshVar proofSupport 1
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_ne_x : y ≠ x := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_y_ne_v : y ≠ v := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_y_ne_u : y ≠ u := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_z_ne_x : z ≠ x := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_x_ne_z : x ≠ z := Ne.symm fresh_z_ne_x
  have fresh_z_ne_v : z ≠ v := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_v_ne_z : v ≠ z := Ne.symm fresh_z_ne_v
  have fresh_z_ne_u : z ≠ u := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_u_ne_z : u ≠ z := Ne.symm fresh_z_ne_u
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have fresh_y_ne_z : y ≠ z :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have dv_cache_0001 : v ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_v, not_false_eq_true])
  have dv_cache_0002 : u ∉ (A).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_u, not_false_eq_true])
  have dv_cache_0003 :
    z ∉
      ((synW3a (synWa (.classMem A (synCvv))
            (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv v))) (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
              (.cv x))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutcode,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_u, fresh_z_ne_x, fresh_z_ne_v, fresh_z_not_A,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0004 : z ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_A, not_false_eq_true])
  have dv_cache_0005 : v ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show v ≠ z from (by exact fresh_v_ne_z))
  have dv_cache_0006 : u ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show u ≠ z from (by exact fresh_u_ne_z))
  have dv_cache_0007 : x ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact (show x ≠ z from (by exact fresh_x_ne_z))
  have dv_cache_0008 :
    y ∉
      ((synWrex z (synCfv (synC2nd) (.cv u)) (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
              (.cv z))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutcode,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_y_ne_u, fresh_y_ne_z,
          fresh_y_not_A, compact_fv_not_mem_empty, or_false, and_false,
          not_false_eq_true])
  have dv_cache_0009 :
    y ∉
      ((synW3a (synWa (.classMem A (synCvv))
            (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv v))) (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
              (.cv x))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutcode,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_u, fresh_y_ne_x, fresh_y_ne_v, fresh_y_not_A,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0010 : y ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_A, not_false_eq_true])
  have dv_cache_0011 : y ∉ ((Class.cv v)).fv :=
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
          fresh_y_ne_v, not_false_eq_true])
  have dv_cache_0012 : y ∉ ((Class.cv u)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_y_ne_u, not_false_eq_true])
  have dv_cache_0013 :
    x ∉ ((Wff.neg (synWbr (.cv v) (synChncodecmpset A) (.cv u)))).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_neg,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodecmpset,
          Finset.mem_union, Finset.mem_singleton, (Ne.symm dv_v_x), (Ne.symm dv_u_x),
          dv_A_x, or_false, not_false_eq_true])
  have dv_cache_0014 :
    x ∉
      ((synWa (.classMem A (synCvv)) (synWa (.classMem (.cv u) (synChwcn A))
            (.classMem (.cv v) (synChwcn A))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, Finset.mem_union,
          Finset.mem_singleton, dv_A_x, (Ne.symm dv_u_x), (Ne.symm dv_v_x),
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have p0000 :=
    @gSimp1
      (synWa (.classMem A (synCvv))
        (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
      (.classMem (.cv x) (synCfv (synC2nd) (.cv v)))
      (synWbr (.cv u) (synChwniso A)
        (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x)))
  have p0001 :=
    @gSimprd
      (synW3a (synWa (.classMem A (synCvv))
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv v))) (synWbr (.cv u) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x))))
      (.classMem A (synCvv))
      (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))) p0000
  have p0002 :=
    @gSimprd
      (synW3a (synWa (.classMem A (synCvv))
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv v))) (synWbr (.cv u) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x))))
      (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)) p0001
  have p0003 :=
    @gSimp2
      (synWa (.classMem A (synCvv))
        (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
      (.classMem (.cv x) (synCfv (synC2nd) (.cv v)))
      (synWbr (.cv u) (synChwniso A)
        (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x)))
  have p0004 :=
    @gJca
      (synW3a (synWa (.classMem A (synCvv))
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv v))) (synWbr (.cv u) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x))))
      (.classMem (.cv v) (synChwcn A)) (.classMem (.cv x) (synCfv (synC2nd) (.cv v)))
      p0002 p0003
  have p0005 := @gHnwcutcodeselfnoisondv x v A dv_cache_0001
  have p0006 :=
    @gSyl
      (synW3a (synWa (.classMem A (synCvv))
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv v))) (synWbr (.cv u) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x))))
      (synWa (.classMem (.cv v) (synChwcn A))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv v))))
      (.neg (synWbr (.cv v) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x))))
      p0004 p0005
  have p0007 :=
    @gSimpl
      (synW3a (synWa (.classMem A (synCvv))
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv v))) (synWbr (.cv u) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x))))
      (synWbr (.cv v) (synChwniso A) (.cv u))
  have p0009 :=
    @gSimpld
      (synW3a (synWa (.classMem A (synCvv))
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv v))) (synWbr (.cv u) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x))))
      (.classMem A (synCvv))
      (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))) p0000
  have p0010 := @gHwnisoer A
  have p0011 :=
    @gSyl
      (synW3a (synWa (.classMem A (synCvv))
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv v))) (synWbr (.cv u) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x))))
      (.classMem A (synCvv)) (synWbr (synChwniso A) (synCer) (synChwcn A)) p0009
      p0010
  have p0012 :=
    @gSyl
      (synWa (synW3a (synWa (.classMem A (synCvv))
            (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv v))) (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
              (.cv x)))) (synWbr (.cv v) (synChwniso A) (.cv u)))
      (synW3a (synWa (.classMem A (synCvv))
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv v))) (synWbr (.cv u) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x))))
      (synWbr (synChwniso A) (synCer) (synChwcn A)) p0007 p0011
  have p0017 :=
    @gSyl
      (synWa (synW3a (synWa (.classMem A (synCvv))
            (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv v))) (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
              (.cv x)))) (synWbr (.cv v) (synChwniso A) (.cv u)))
      (synW3a (synWa (.classMem A (synCvv))
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv v))) (synWbr (.cv u) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x))))
      (.classMem (.cv v) (synChwcn A)) p0007 p0002
  have p0021 :=
    @gSimpld
      (synW3a (synWa (.classMem A (synCvv))
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv v))) (synWbr (.cv u) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x))))
      (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)) p0001
  have p0022 :=
    @gSyl
      (synWa (synW3a (synWa (.classMem A (synCvv))
            (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv v))) (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
              (.cv x)))) (synWbr (.cv v) (synChwniso A) (.cv u)))
      (synW3a (synWa (.classMem A (synCvv))
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv v))) (synWbr (.cv u) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x))))
      (.classMem (.cv u) (synChwcn A)) p0007 p0021
  have p0029 := @gHnwcutcodeambientndv x v A dv_cache_0001
  have p0030 :=
    @gSyl
      (synW3a (synWa (.classMem A (synCvv))
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv v))) (synWbr (.cv u) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x))))
      (synWa (.classMem (.cv v) (synChwcn A))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv v))))
      (.classMem (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
          (.cv x)) (synChwcn A))
      p0004 p0029
  have p0031 :=
    @gSyl
      (synWa (synW3a (synWa (.classMem A (synCvv))
            (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv v))) (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
              (.cv x)))) (synWbr (.cv v) (synChwniso A) (.cv u)))
      (synW3a (synWa (.classMem A (synCvv))
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv v))) (synWbr (.cv u) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x))))
      (.classMem (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
          (.cv x)) (synChwcn A))
      p0007 p0030
  have p0032 :=
    @gSimpr
      (synW3a (synWa (.classMem A (synCvv))
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv v))) (synWbr (.cv u) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x))))
      (synWbr (.cv v) (synChwniso A) (.cv u))
  have p0034 :=
    @gSimp3
      (synWa (.classMem A (synCvv))
        (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
      (.classMem (.cv x) (synCfv (synC2nd) (.cv v)))
      (synWbr (.cv u) (synChwniso A)
        (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x)))
  have p0035 :=
    @gSyl
      (synWa (synW3a (synWa (.classMem A (synCvv))
            (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv v))) (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
              (.cv x)))) (synWbr (.cv v) (synChwniso A) (.cv u)))
      (synW3a (synWa (.classMem A (synCvv))
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv v))) (synWbr (.cv u) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x))))
      (synWbr (.cv u) (synChwniso A)
        (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x)))
      p0007 p0034
  have p0036 :=
    @gErtrd
      (synWa (synW3a (synWa (.classMem A (synCvv))
            (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv v))) (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
              (.cv x)))) (synWbr (.cv v) (synChwniso A) (.cv u)))
      (synChwcn A) (synChwniso A) (.cv v) (.cv u)
      (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x))
      p0012 p0017 p0022 p0031 p0032 p0035
  have p0037 :=
    @gExpcom
      (synW3a (synWa (.classMem A (synCvv))
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv v))) (synWbr (.cv u) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x))))
      (synWbr (.cv v) (synChwniso A) (.cv u))
      (synWbr (.cv v) (synChwniso A)
        (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x)))
      p0036
  have p0038 :=
    @gCom12 (synWbr (.cv v) (synChwniso A) (.cv u))
      (synW3a (synWa (.classMem A (synCvv))
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv v))) (synWbr (.cv u) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x))))
      (synWbr (.cv v) (synChwniso A)
        (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x)))
      p0037
  have p0039 :=
    @gMtod
      (synW3a (synWa (.classMem A (synCvv))
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv v))) (synWbr (.cv u) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x))))
      (synWbr (.cv v) (synChwniso A) (.cv u))
      (synWbr (.cv v) (synChwniso A)
        (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x)))
      p0006 p0038
  have p0040 :=
    @gSimpl
      (synW3a (synWa (.classMem A (synCvv))
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv v))) (synWbr (.cv u) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x))))
      (.classMem (.cv z) (synCfv (synC2nd) (.cv u)))
  have p0044 :=
    @gSyl
      (synWa (synW3a (synWa (.classMem A (synCvv))
            (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv v))) (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
              (.cv x)))) (.classMem (.cv z) (synCfv (synC2nd) (.cv u))))
      (synW3a (synWa (.classMem A (synCvv))
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv v))) (synWbr (.cv u) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x))))
      (.classMem (.cv u) (synChwcn A)) p0040 p0021
  have p0045 :=
    @gSimpr
      (synW3a (synWa (.classMem A (synCvv))
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv v))) (synWbr (.cv u) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x))))
      (.classMem (.cv z) (synCfv (synC2nd) (.cv u)))
  have p0046 :=
    @gJca
      (synWa (synW3a (synWa (.classMem A (synCvv))
            (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv v))) (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
              (.cv x)))) (.classMem (.cv z) (synCfv (synC2nd) (.cv u))))
      (.classMem (.cv u) (synChwcn A)) (.classMem (.cv z) (synCfv (synC2nd) (.cv u)))
      p0044 p0045
  have p0047 := @gHnwcutcodeselfnoisondv z u A dv_cache_0002
  have p0048 :=
    @gSyl
      (synWa (synW3a (synWa (.classMem A (synCvv))
            (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv v))) (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
              (.cv x)))) (.classMem (.cv z) (synCfv (synC2nd) (.cv u))))
      (synWa (.classMem (.cv u) (synChwcn A))
        (.classMem (.cv z) (synCfv (synC2nd) (.cv u))))
      (.neg (synWbr (.cv u) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv z))))
      p0046 p0047
  have p0049 :=
    @gNrexdv
      (synW3a (synWa (.classMem A (synCvv))
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv v))) (synWbr (.cv u) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x))))
      (synWbr (.cv u) (synChwniso A)
        (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv z)))
      z (synCfv (synC2nd) (.cv u)) dv_cache_0003 p0048
  have p0050 :=
    @gSimp1
      (synW3a (synWa (.classMem A (synCvv))
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv v))) (synWbr (.cv u) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x))))
      (.classMem (.cv y) (synCfv (synC2nd) (.cv u)))
      (synWbr (.cv v) (synChwniso A)
        (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv y)))
  have p0053 :=
    @gSyl
      (synW3a (synW3a (synWa (.classMem A (synCvv))
            (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv v))) (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
              (.cv x)))) (.classMem (.cv y) (synCfv (synC2nd) (.cv u)))
        (synWbr (.cv v) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv y))))
      (synW3a (synWa (.classMem A (synCvv))
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv v))) (synWbr (.cv u) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x))))
      (.classMem A (synCvv)) p0050 p0009
  have p0058 :=
    @gSyl
      (synW3a (synW3a (synWa (.classMem A (synCvv))
            (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv v))) (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
              (.cv x)))) (.classMem (.cv y) (synCfv (synC2nd) (.cv u)))
        (synWbr (.cv v) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv y))))
      (synW3a (synWa (.classMem A (synCvv))
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv v))) (synWbr (.cv u) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x))))
      (.classMem (.cv u) (synChwcn A)) p0050 p0021
  have p0063 :=
    @gSyl
      (synW3a (synW3a (synWa (.classMem A (synCvv))
            (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv v))) (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
              (.cv x)))) (.classMem (.cv y) (synCfv (synC2nd) (.cv u)))
        (synWbr (.cv v) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv y))))
      (synW3a (synWa (.classMem A (synCvv))
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv v))) (synWbr (.cv u) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x))))
      (.classMem (.cv v) (synChwcn A)) p0050 p0002
  have p0064 :=
    @gJca
      (synW3a (synW3a (synWa (.classMem A (synCvv))
            (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv v))) (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
              (.cv x)))) (.classMem (.cv y) (synCfv (synC2nd) (.cv u)))
        (synWbr (.cv v) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv y))))
      (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)) p0058 p0063
  have p0070 :=
    @gJca
      (synW3a (synW3a (synWa (.classMem A (synCvv))
            (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv v))) (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
              (.cv x)))) (.classMem (.cv y) (synCfv (synC2nd) (.cv u)))
        (synWbr (.cv v) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv y))))
      (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
      (.classMem (.cv u) (synChwcn A)) p0064 p0058
  have p0071 :=
    @gJca
      (synW3a (synW3a (synWa (.classMem A (synCvv))
            (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv v))) (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
              (.cv x)))) (.classMem (.cv y) (synCfv (synC2nd) (.cv u)))
        (synWbr (.cv v) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv y))))
      (.classMem A (synCvv))
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (.classMem (.cv u) (synChwcn A)))
      p0053 p0070
  have p0074 :=
    @gSyl
      (synW3a (synW3a (synWa (.classMem A (synCvv))
            (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv v))) (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
              (.cv x)))) (.classMem (.cv y) (synCfv (synC2nd) (.cv u)))
        (synWbr (.cv v) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv y))))
      (synW3a (synWa (.classMem A (synCvv))
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv v))) (synWbr (.cv u) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x))))
      (.classMem (.cv x) (synCfv (synC2nd) (.cv v))) p0050 p0003
  have p0077 :=
    @gSyl
      (synW3a (synW3a (synWa (.classMem A (synCvv))
            (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv v))) (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
              (.cv x)))) (.classMem (.cv y) (synCfv (synC2nd) (.cv u)))
        (synWbr (.cv v) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv y))))
      (synW3a (synWa (.classMem A (synCvv))
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv v))) (synWbr (.cv u) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x))))
      (synWbr (.cv u) (synChwniso A)
        (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x)))
      p0050 p0034
  have p0078 :=
    @gJca
      (synW3a (synW3a (synWa (.classMem A (synCvv))
            (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv v))) (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
              (.cv x)))) (.classMem (.cv y) (synCfv (synC2nd) (.cv u)))
        (synWbr (.cv v) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv y))))
      (.classMem (.cv x) (synCfv (synC2nd) (.cv v)))
      (synWbr (.cv u) (synChwniso A)
        (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x)))
      p0074 p0077
  have p0079 :=
    @gJca
      (synW3a (synW3a (synWa (.classMem A (synCvv))
            (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv v))) (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
              (.cv x)))) (.classMem (.cv y) (synCfv (synC2nd) (.cv u)))
        (synWbr (.cv v) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv y))))
      (synWa (.classMem A (synCvv)) (synWa
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
          (.classMem (.cv u) (synChwcn A))))
      (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv v))) (synWbr (.cv u) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x))))
      p0071 p0078
  have p0090 :=
    @gJca
      (synW3a (synW3a (synWa (.classMem A (synCvv))
            (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv v))) (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
              (.cv x)))) (.classMem (.cv y) (synCfv (synC2nd) (.cv u)))
        (synWbr (.cv v) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv y))))
      (.classMem (.cv v) (synChwcn A)) (.classMem (.cv u) (synChwcn A)) p0063 p0058
  have p0091 :=
    @gSimp2
      (synW3a (synWa (.classMem A (synCvv))
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv v))) (synWbr (.cv u) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x))))
      (.classMem (.cv y) (synCfv (synC2nd) (.cv u)))
      (synWbr (.cv v) (synChwniso A)
        (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv y)))
  have p0092 :=
    @gJca
      (synW3a (synW3a (synWa (.classMem A (synCvv))
            (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv v))) (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
              (.cv x)))) (.classMem (.cv y) (synCfv (synC2nd) (.cv u)))
        (synWbr (.cv v) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv y))))
      (synWa (.classMem (.cv v) (synChwcn A)) (.classMem (.cv u) (synChwcn A)))
      (.classMem (.cv y) (synCfv (synC2nd) (.cv u))) p0090 p0091
  have p0093 :=
    @gSimp3
      (synW3a (synWa (.classMem A (synCvv))
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv v))) (synWbr (.cv u) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x))))
      (.classMem (.cv y) (synCfv (synC2nd) (.cv u)))
      (synWbr (.cv v) (synChwniso A)
        (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv y)))
  have p0097 :=
    @gJca
      (synW3a (synW3a (synWa (.classMem A (synCvv))
            (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv v))) (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
              (.cv x)))) (.classMem (.cv y) (synCfv (synC2nd) (.cv u)))
        (synWbr (.cv v) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv y))))
      (synWbr (.cv v) (synChwniso A)
        (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv y)))
      (.classMem (.cv x) (synCfv (synC2nd) (.cv v))) p0093 p0074
  have p0098 :=
    @gJca
      (synW3a (synW3a (synWa (.classMem A (synCvv))
            (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv v))) (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
              (.cv x)))) (.classMem (.cv y) (synCfv (synC2nd) (.cv u)))
        (synWbr (.cv v) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv y))))
      (synWa (synWa (.classMem (.cv v) (synChwcn A)) (.classMem (.cv u) (synChwcn A)))
        (.classMem (.cv y) (synCfv (synC2nd) (.cv u))))
      (synWa (synWbr (.cv v) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv y)))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv v))))
      p0092 p0097
  have p0099 :=
    @gHnwcutcodetransportintocutndv x y z u v A dv_cache_0001 dv_cache_0002 dv_cache_0004
      dv_cache_0005 dv_cache_0006 dv_cache_0007
  have p0100 :=
    @gSyl
      (synW3a (synW3a (synWa (.classMem A (synCvv))
            (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv v))) (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
              (.cv x)))) (.classMem (.cv y) (synCfv (synC2nd) (.cv u)))
        (synWbr (.cv v) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv y))))
      (synWa (synWa
          (synWa (.classMem (.cv v) (synChwcn A)) (.classMem (.cv u) (synChwcn A)))
          (.classMem (.cv y) (synCfv (synC2nd) (.cv u)))) (synWa
          (synWbr (.cv v) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv y)))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv v)))))
      (synWrex z (synCfv (synC2nd) (.cv u)) (synWbr
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x))
          (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv z))))
      p0098 p0099
  have p0101 :=
    @gJca
      (synW3a (synW3a (synWa (.classMem A (synCvv))
            (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv v))) (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
              (.cv x)))) (.classMem (.cv y) (synCfv (synC2nd) (.cv u)))
        (synWbr (.cv v) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv y))))
      (synWa (synWa (.classMem A (synCvv)) (synWa
            (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
            (.classMem (.cv u) (synChwcn A))))
        (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv v)))
          (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
              (.cv x)))))
      (synWrex z (synCfv (synC2nd) (.cv u)) (synWbr
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x))
          (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv z))))
      p0079 p0100
  have p0102 :=
    @gHnwcutcodestrictextendndv x z u v u A dv_cache_0002 dv_cache_0001 dv_cache_0002
      dv_cache_0004 dv_cache_0006 dv_cache_0005 dv_cache_0006 dv_cache_0007
  have p0103 :=
    @gSyl
      (synW3a (synW3a (synWa (.classMem A (synCvv))
            (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv v))) (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
              (.cv x)))) (.classMem (.cv y) (synCfv (synC2nd) (.cv u)))
        (synWbr (.cv v) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv y))))
      (synWa (synWa (synWa (.classMem A (synCvv)) (synWa
              (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
              (.classMem (.cv u) (synChwcn A))))
          (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv v)))
            (synWbr (.cv u) (synChwniso A)
              (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                (.cv x))))) (synWrex z (synCfv (synC2nd) (.cv u)) (synWbr
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x))
            (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
              (.cv z)))))
      (synWrex z (synCfv (synC2nd) (.cv u)) (synWbr (.cv u) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv z))))
      p0101 p0102
  have p0104 :=
    @gN3exp
      (synW3a (synWa (.classMem A (synCvv))
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv v))) (synWbr (.cv u) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x))))
      (.classMem (.cv y) (synCfv (synC2nd) (.cv u)))
      (synWbr (.cv v) (synChwniso A)
        (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv y)))
      (synWrex z (synCfv (synC2nd) (.cv u)) (synWbr (.cv u) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv z))))
      p0103
  have p0105 :=
    @gRexlimdv
      (synW3a (synWa (.classMem A (synCvv))
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv v))) (synWbr (.cv u) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x))))
      (synWbr (.cv v) (synChwniso A)
        (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv y)))
      (synWrex z (synCfv (synC2nd) (.cv u)) (synWbr (.cv u) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv z))))
      y (synCfv (synC2nd) (.cv u)) dv_cache_0008 dv_cache_0009 p0104
  have p0106 :=
    @gMtod
      (synW3a (synWa (.classMem A (synCvv))
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv v))) (synWbr (.cv u) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x))))
      (synWrex y (synCfv (synC2nd) (.cv u)) (synWbr (.cv v) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv y))))
      (synWrex z (synCfv (synC2nd) (.cv u)) (synWbr (.cv u) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv z))))
      p0049 p0105
  have p0107 :=
    @gJca
      (synW3a (synWa (.classMem A (synCvv))
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv v))) (synWbr (.cv u) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x))))
      (.neg (synWbr (.cv v) (synChwniso A) (.cv u)))
      (.neg (synWrex y (synCfv (synC2nd) (.cv u)) (synWbr (.cv v) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
              (.cv y)))))
      p0039 p0106
  have p0108 :=
    @gIoran (synWbr (.cv v) (synChwniso A) (.cv u))
      (synWrex y (synCfv (synC2nd) (.cv u)) (synWbr (.cv v) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv y))))
  have p0109 :=
    @gA1i
      (synWb (.neg (synWo (synWbr (.cv v) (synChwniso A) (.cv u))
            (synWrex y (synCfv (synC2nd) (.cv u)) (synWbr (.cv v) (synChwniso A)
                (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
                  (.cv y)))))) (synWa (.neg (synWbr (.cv v) (synChwniso A) (.cv u))) (.neg
            (synWrex y (synCfv (synC2nd) (.cv u)) (synWbr (.cv v) (synChwniso A)
                (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
                  (.cv y)))))))
      (synW3a (synWa (.classMem A (synCvv))
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv v))) (synWbr (.cv u) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x))))
      p0108
  have p0110 :=
    @gMpbird
      (synW3a (synWa (.classMem A (synCvv))
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv v))) (synWbr (.cv u) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x))))
      (.neg (synWo (synWbr (.cv v) (synChwniso A) (.cv u))
          (synWrex y (synCfv (synC2nd) (.cv u)) (synWbr (.cv v) (synChwniso A)
              (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
                (.cv y))))))
      (synWa (.neg (synWbr (.cv v) (synChwniso A) (.cv u))) (.neg
          (synWrex y (synCfv (synC2nd) (.cv u)) (synWbr (.cv v) (synChwniso A)
              (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
                (.cv y))))))
      p0107 p0109
  have p0117 :=
    @gJca
      (synW3a (synWa (.classMem A (synCvv))
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv v))) (synWbr (.cv u) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x))))
      (.classMem (.cv v) (synChwcn A)) (.classMem (.cv u) (synChwcn A)) p0002 p0021
  have p0118 :=
    @gHncodecmpsetstrictcutsemclndv y A (.cv v) (.cv u) dv_cache_0010 dv_cache_0011
      dv_cache_0012
  have p0119 :=
    @gSyl
      (synW3a (synWa (.classMem A (synCvv))
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv v))) (synWbr (.cv u) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x))))
      (synWa (.classMem (.cv v) (synChwcn A)) (.classMem (.cv u) (synChwcn A)))
      (synWb (synWbr (.cv v) (synChncodecmpset A) (.cv u))
        (synWo (synWbr (.cv v) (synChwniso A) (.cv u))
          (synWrex y (synCfv (synC2nd) (.cv u)) (synWbr (.cv v) (synChwniso A)
              (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
                (.cv y))))))
      p0117 p0118
  have p0120 :=
    @gBiimpd
      (synW3a (synWa (.classMem A (synCvv))
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv v))) (synWbr (.cv u) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x))))
      (synWbr (.cv v) (synChncodecmpset A) (.cv u))
      (synWo (synWbr (.cv v) (synChwniso A) (.cv u)) (synWrex y (synCfv (synC2nd) (.cv u))
          (synWbr (.cv v) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
              (.cv y)))))
      p0119
  have p0121 :=
    @gMtod
      (synW3a (synWa (.classMem A (synCvv))
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv v))) (synWbr (.cv u) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x))))
      (synWbr (.cv v) (synChncodecmpset A) (.cv u))
      (synWo (synWbr (.cv v) (synChwniso A) (.cv u)) (synWrex y (synCfv (synC2nd) (.cv u))
          (synWbr (.cv v) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
              (.cv y)))))
      p0110 p0120
  have p0122 :=
    @gN3exp
      (synWa (.classMem A (synCvv))
        (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
      (.classMem (.cv x) (synCfv (synC2nd) (.cv v)))
      (synWbr (.cv u) (synChwniso A)
        (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x)))
      (.neg (synWbr (.cv v) (synChncodecmpset A) (.cv u))) p0121
  have p0123 :=
    @gRexlimdv
      (synWa (.classMem A (synCvv))
        (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
      (synWbr (.cv u) (synChwniso A)
        (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x)))
      (.neg (synWbr (.cv v) (synChncodecmpset A) (.cv u))) x
      (synCfv (synC2nd) (.cv v)) dv_cache_0013 dv_cache_0014 p0122
  exact p0123


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk017Compact001Part039`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_hncodecmpkerptndv`. -/
@[expose]
noncomputable def gHncodecmpkerptndv (v : Var) (u : Var) (A : Class) (dv_A_u : u ∉ A.fv)
    (dv_A_v : v ∉ A.fv) (dv_u_v : u ≠ v) :
    Nominal.NPrf
      (.imp (synWa (.classMem A (synCvv))
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
        (synWb (synWbr (.cv u) (synClnker (synChncodecmpset A)) (.cv v))
          (synWbr (.cv u) (synChwniso A) (.cv v)))) :=
  by
  let proofSupport : Finset Var := ({ v } : Finset Var) ∪ ({ u } : Finset Var) ∪ A.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_ne_v : x ≠ v := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_v_ne_x : v ≠ x := Ne.symm fresh_x_ne_v
  have fresh_x_ne_u : x ≠ u := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_u_ne_x : u ≠ x := Ne.symm fresh_x_ne_u
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_ne_v : y ≠ v := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_y_ne_u : y ≠ u := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have dv_cache_0001 : u ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_u, not_false_eq_true])
  have dv_cache_0002 : v ∉ (A).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_v, not_false_eq_true])
  have dv_cache_0003 : x ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_A, not_false_eq_true])
  have dv_cache_0004 : u ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show u ≠ x from (by exact fresh_u_ne_x))
  have dv_cache_0005 : v ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show v ≠ x from (by exact fresh_v_ne_x))
  have dv_cache_0006 : x ∉ ((Class.cv u)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_x_ne_u, not_false_eq_true])
  have dv_cache_0007 : x ∉ ((Class.cv v)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_x_ne_v, not_false_eq_true])
  have dv_cache_0008 : u ≠ v :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact (show u ≠ v from (by exact dv_u_v))
  have dv_cache_0009 : y ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_A, not_false_eq_true])
  have dv_cache_0010 : y ∉ ((Class.cv v)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_y_ne_v, not_false_eq_true])
  have dv_cache_0011 : y ∉ ((Class.cv u)).fv :=
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
          fresh_y_ne_u, not_false_eq_true])
  have p0000 :=
    @gSimpr
      (synWa (.classMem A (synCvv))
        (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
      (synWbr (.cv u) (synClnker (synChncodecmpset A)) (.cv v))
  have p0001 := @gBrlnker (synChncodecmpset A) (.cv u) (.cv v)
  have p0002 :=
    @gSylib
      (synWa (synWa (.classMem A (synCvv))
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
        (synWbr (.cv u) (synClnker (synChncodecmpset A)) (.cv v)))
      (synWbr (.cv u) (synClnker (synChncodecmpset A)) (.cv v))
      (synWa (synWbr (.cv u) (synChncodecmpset A) (.cv v))
        (synWbr (.cv v) (synChncodecmpset A) (.cv u)))
      p0000 p0001
  have p0003 :=
    @gSimprd
      (synWa (synWa (.classMem A (synCvv))
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
        (synWbr (.cv u) (synClnker (synChncodecmpset A)) (.cv v)))
      (synWbr (.cv u) (synChncodecmpset A) (.cv v))
      (synWbr (.cv v) (synChncodecmpset A) (.cv u)) p0002
  have p0004 :=
    @gSimpl
      (synWa (.classMem A (synCvv))
        (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
      (synWbr (.cv u) (synClnker (synChncodecmpset A)) (.cv v))
  have p0005 :=
    @gHncodecmpstrictnoreversendv x v u A dv_cache_0001 dv_cache_0002 dv_cache_0003
      dv_cache_0004 dv_cache_0005
  have p0006 :=
    @gSyl
      (synWa (synWa (.classMem A (synCvv))
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
        (synWbr (.cv u) (synClnker (synChncodecmpset A)) (.cv v)))
      (synWa (.classMem A (synCvv))
        (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
      (.imp (synWrex x (synCfv (synC2nd) (.cv v)) (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
              (.cv x)))) (.neg (synWbr (.cv v) (synChncodecmpset A) (.cv u))))
      p0004 p0005
  have p0007 :=
    @gMt2d
      (synWa (synWa (.classMem A (synCvv))
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
        (synWbr (.cv u) (synClnker (synChncodecmpset A)) (.cv v)))
      (synWrex x (synCfv (synC2nd) (.cv v)) (synWbr (.cv u) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x))))
      (synWbr (.cv v) (synChncodecmpset A) (.cv u)) p0003 p0006
  have p0011 :=
    @gSimpld
      (synWa (synWa (.classMem A (synCvv))
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
        (synWbr (.cv u) (synClnker (synChncodecmpset A)) (.cv v)))
      (synWbr (.cv u) (synChncodecmpset A) (.cv v))
      (synWbr (.cv v) (synChncodecmpset A) (.cv u)) p0002
  have p0013 :=
    @gSimpr (.classMem A (synCvv))
      (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
  have p0014 :=
    @gSyl
      (synWa (synWa (.classMem A (synCvv))
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
        (synWbr (.cv u) (synClnker (synChncodecmpset A)) (.cv v)))
      (synWa (.classMem A (synCvv))
        (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
      (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))) p0004
      p0013
  have p0015 :=
    @gHncodecmpsetstrictcutsemclndv x A (.cv u) (.cv v) dv_cache_0003 dv_cache_0006
      dv_cache_0007
  have p0016 :=
    @gSyl
      (synWa (synWa (.classMem A (synCvv))
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
        (synWbr (.cv u) (synClnker (synChncodecmpset A)) (.cv v)))
      (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
      (synWb (synWbr (.cv u) (synChncodecmpset A) (.cv v))
        (synWo (synWbr (.cv u) (synChwniso A) (.cv v))
          (synWrex x (synCfv (synC2nd) (.cv v)) (synWbr (.cv u) (synChwniso A)
              (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                (.cv x))))))
      p0014 p0015
  have p0017 :=
    @gMpbid
      (synWa (synWa (.classMem A (synCvv))
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
        (synWbr (.cv u) (synClnker (synChncodecmpset A)) (.cv v)))
      (synWbr (.cv u) (synChncodecmpset A) (.cv v))
      (synWo (synWbr (.cv u) (synChwniso A) (.cv v)) (synWrex x (synCfv (synC2nd) (.cv v))
          (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
              (.cv x)))))
      p0011 p0016
  have p0018 :=
    @gOrcomd
      (synWa (synWa (.classMem A (synCvv))
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
        (synWbr (.cv u) (synClnker (synChncodecmpset A)) (.cv v)))
      (synWbr (.cv u) (synChwniso A) (.cv v))
      (synWrex x (synCfv (synC2nd) (.cv v)) (synWbr (.cv u) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x))))
      p0017
  have p0019 :=
    @gOrcanai
      (synWa (synWa (.classMem A (synCvv))
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
        (synWbr (.cv u) (synClnker (synChncodecmpset A)) (.cv v)))
      (synWrex x (synCfv (synC2nd) (.cv v)) (synWbr (.cv u) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x))))
      (synWbr (.cv u) (synChwniso A) (.cv v)) p0018
  have p0020 :=
    @gMpdan
      (synWa (synWa (.classMem A (synCvv))
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
        (synWbr (.cv u) (synClnker (synChncodecmpset A)) (.cv v)))
      (.neg (synWrex x (synCfv (synC2nd) (.cv v)) (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
              (.cv x)))))
      (synWbr (.cv u) (synChwniso A) (.cv v)) p0007 p0019
  have p0021 :=
    @gSimpr
      (synWa (.classMem A (synCvv))
        (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
      (synWbr (.cv u) (synChwniso A) (.cv v))
  have p0022 :=
    @gOrc (synWbr (.cv u) (synChwniso A) (.cv v))
      (synWrex x (synCfv (synC2nd) (.cv v)) (synWbr (.cv u) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x))))
  have p0023 :=
    @gSyl
      (synWa (synWa (.classMem A (synCvv))
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
        (synWbr (.cv u) (synChwniso A) (.cv v)))
      (synWbr (.cv u) (synChwniso A) (.cv v))
      (synWo (synWbr (.cv u) (synChwniso A) (.cv v)) (synWrex x (synCfv (synC2nd) (.cv v))
          (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
              (.cv x)))))
      p0021 p0022
  have p0024 :=
    @gSimpl
      (synWa (.classMem A (synCvv))
        (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
      (synWbr (.cv u) (synChwniso A) (.cv v))
  have p0026 :=
    @gSyl
      (synWa (synWa (.classMem A (synCvv))
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
        (synWbr (.cv u) (synChwniso A) (.cv v)))
      (synWa (.classMem A (synCvv))
        (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
      (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))) p0024
      p0013
  have p0028 :=
    @gSyl
      (synWa (synWa (.classMem A (synCvv))
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
        (synWbr (.cv u) (synChwniso A) (.cv v)))
      (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
      (synWb (synWbr (.cv u) (synChncodecmpset A) (.cv v))
        (synWo (synWbr (.cv u) (synChwniso A) (.cv v))
          (synWrex x (synCfv (synC2nd) (.cv v)) (synWbr (.cv u) (synChwniso A)
              (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                (.cv x))))))
      p0026 p0015
  have p0029 :=
    @gMpbird
      (synWa (synWa (.classMem A (synCvv))
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
        (synWbr (.cv u) (synChwniso A) (.cv v)))
      (synWbr (.cv u) (synChncodecmpset A) (.cv v))
      (synWo (synWbr (.cv u) (synChwniso A) (.cv v)) (synWrex x (synCfv (synC2nd) (.cv v))
          (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
              (.cv x)))))
      p0023 p0028
  have p0031 := @gHwnisosymi v u A dv_cache_0001 dv_cache_0002 dv_cache_0008
  have p0032 :=
    @gSyl
      (synWa (synWa (.classMem A (synCvv))
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
        (synWbr (.cv u) (synChwniso A) (.cv v)))
      (synWbr (.cv u) (synChwniso A) (.cv v)) (synWbr (.cv v) (synChwniso A) (.cv u))
      p0021 p0031
  have p0033 :=
    @gOrc (synWbr (.cv v) (synChwniso A) (.cv u))
      (synWrex y (synCfv (synC2nd) (.cv u)) (synWbr (.cv v) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv y))))
  have p0034 :=
    @gSyl
      (synWa (synWa (.classMem A (synCvv))
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
        (synWbr (.cv u) (synChwniso A) (.cv v)))
      (synWbr (.cv v) (synChwniso A) (.cv u))
      (synWo (synWbr (.cv v) (synChwniso A) (.cv u)) (synWrex y (synCfv (synC2nd) (.cv u))
          (synWbr (.cv v) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
              (.cv y)))))
      p0032 p0033
  have p0038 :=
    @gSimprd
      (synWa (synWa (.classMem A (synCvv))
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
        (synWbr (.cv u) (synChwniso A) (.cv v)))
      (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)) p0026
  have p0042 :=
    @gSimpld
      (synWa (synWa (.classMem A (synCvv))
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
        (synWbr (.cv u) (synChwniso A) (.cv v)))
      (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)) p0026
  have p0043 :=
    @gJca
      (synWa (synWa (.classMem A (synCvv))
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
        (synWbr (.cv u) (synChwniso A) (.cv v)))
      (.classMem (.cv v) (synChwcn A)) (.classMem (.cv u) (synChwcn A)) p0038 p0042
  have p0044 :=
    @gHncodecmpsetstrictcutsemclndv y A (.cv v) (.cv u) dv_cache_0009 dv_cache_0010
      dv_cache_0011
  have p0045 :=
    @gSyl
      (synWa (synWa (.classMem A (synCvv))
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
        (synWbr (.cv u) (synChwniso A) (.cv v)))
      (synWa (.classMem (.cv v) (synChwcn A)) (.classMem (.cv u) (synChwcn A)))
      (synWb (synWbr (.cv v) (synChncodecmpset A) (.cv u))
        (synWo (synWbr (.cv v) (synChwniso A) (.cv u))
          (synWrex y (synCfv (synC2nd) (.cv u)) (synWbr (.cv v) (synChwniso A)
              (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
                (.cv y))))))
      p0043 p0044
  have p0046 :=
    @gMpbird
      (synWa (synWa (.classMem A (synCvv))
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
        (synWbr (.cv u) (synChwniso A) (.cv v)))
      (synWbr (.cv v) (synChncodecmpset A) (.cv u))
      (synWo (synWbr (.cv v) (synChwniso A) (.cv u)) (synWrex y (synCfv (synC2nd) (.cv u))
          (synWbr (.cv v) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
              (.cv y)))))
      p0034 p0045
  have p0047 :=
    @gJca
      (synWa (synWa (.classMem A (synCvv))
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
        (synWbr (.cv u) (synChwniso A) (.cv v)))
      (synWbr (.cv u) (synChncodecmpset A) (.cv v))
      (synWbr (.cv v) (synChncodecmpset A) (.cv u)) p0029 p0046
  have p0049 :=
    @gSylibr
      (synWa (synWa (.classMem A (synCvv))
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
        (synWbr (.cv u) (synChwniso A) (.cv v)))
      (synWa (synWbr (.cv u) (synChncodecmpset A) (.cv v))
        (synWbr (.cv v) (synChncodecmpset A) (.cv u)))
      (synWbr (.cv u) (synClnker (synChncodecmpset A)) (.cv v)) p0047 p0001
  have p0050 :=
    @gImpbida
      (synWa (.classMem A (synCvv))
        (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
      (synWbr (.cv u) (synClnker (synChncodecmpset A)) (.cv v))
      (synWbr (.cv u) (synChwniso A) (.cv v)) p0020 p0049
  exact p0050

/-- Checked nominal proof certificate identified upstream as `g_hncodecmplnkerndv`. -/
@[expose]
noncomputable def gHncodecmplnkerndv (A : Class) :
    Nominal.NPrf
      (.imp (.classMem A (synCvv))
        (.classEq (synClnker (synChncodecmpset A)) (synChwniso A))) :=
  by
  let proofSupport : Finset Var := A.fv
  let u : Var := freshVar proofSupport 0
  let v : Var := freshVar proofSupport 1
  let x : Var := freshVar proofSupport 2
  let y : Var := freshVar proofSupport 3
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
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (h)
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (h)
  have fresh_u_ne_v : u ≠ v :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_u_ne_x : u ≠ x :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_x_ne_u : x ≠ u := Ne.symm fresh_u_ne_x
  have fresh_u_ne_y : u ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_y_ne_u : y ≠ u := Ne.symm fresh_u_ne_y
  have fresh_v_ne_x : v ≠ x :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_x_ne_v : x ≠ v := Ne.symm fresh_v_ne_x
  have fresh_v_ne_y : v ≠ y :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_y_ne_v : y ≠ v := Ne.symm fresh_v_ne_y
  have dv_cache_0001 : u ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_u_not_A, not_false_eq_true])
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
  have dv_cache_0003 : x ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_A, not_false_eq_true])
  have dv_cache_0004 : u ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show u ≠ x from (by exact fresh_u_ne_x))
  have dv_cache_0005 : v ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show v ≠ x from (by exact fresh_v_ne_x))
  have dv_cache_0006 : x ∉ ((Class.cv u)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_x_ne_u, not_false_eq_true])
  have dv_cache_0007 : x ∉ ((Class.cv v)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_x_ne_v, not_false_eq_true])
  have dv_cache_0008 : u ≠ v :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact (show u ≠ v from (by exact fresh_u_ne_v))
  have dv_cache_0009 : y ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_A, not_false_eq_true])
  have dv_cache_0010 : y ∉ ((Class.cv v)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_y_ne_v, not_false_eq_true])
  have dv_cache_0011 : y ∉ ((Class.cv u)).fv :=
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
          fresh_y_ne_u, not_false_eq_true])
  have dv_cache_0012 : u ∉ ((synClnker (synChncodecmpset A))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnker,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodecmpset,
          fresh_u_not_A, not_false_eq_true])
  have dv_cache_0013 : v ∉ ((synClnker (synChncodecmpset A))).fv :=
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
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnker,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodecmpset,
          fresh_v_not_A, not_false_eq_true])
  have dv_cache_0014 : u ∉ ((synChwniso A)).fv :=
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
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso,
          fresh_u_not_A, not_false_eq_true])
  have dv_cache_0015 : v ∉ ((synChwniso A)).fv :=
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
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso,
          fresh_v_not_A, not_false_eq_true])
  have dv_cache_0016 : u ∉ ((Wff.classMem A (synCvv))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
          fresh_u_not_A, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0017 : v ∉ ((Wff.classMem A (synCvv))).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
          fresh_v_not_A, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have p0000 :=
    @gSimpl (.classMem A (synCvv))
      (synWbr (.cv u) (synClnker (synChncodecmpset A)) (.cv v))
  have p0001 :=
    @gSimpr (.classMem A (synCvv))
      (synWbr (.cv u) (synClnker (synChncodecmpset A)) (.cv v))
  have p0002 := @gBrlnker (synChncodecmpset A) (.cv u) (.cv v)
  have p0003 :=
    @gSylib
      (synWa (.classMem A (synCvv))
        (synWbr (.cv u) (synClnker (synChncodecmpset A)) (.cv v)))
      (synWbr (.cv u) (synClnker (synChncodecmpset A)) (.cv v))
      (synWa (synWbr (.cv u) (synChncodecmpset A) (.cv v))
        (synWbr (.cv v) (synChncodecmpset A) (.cv u)))
      p0001 p0002
  have p0004 :=
    @gSimpld
      (synWa (.classMem A (synCvv))
        (synWbr (.cv u) (synClnker (synChncodecmpset A)) (.cv v)))
      (synWbr (.cv u) (synChncodecmpset A) (.cv v))
      (synWbr (.cv v) (synChncodecmpset A) (.cv u)) p0003
  have p0005 := @gHncodecmpsetssxpndv A
  have p0006 :=
    @gBrel (.cv u) (.cv v) (synChwcn A) (synChwcn A) (synChncodecmpset A) p0005
  have p0007 :=
    @gSyl
      (synWa (.classMem A (synCvv))
        (synWbr (.cv u) (synClnker (synChncodecmpset A)) (.cv v)))
      (synWbr (.cv u) (synChncodecmpset A) (.cv v))
      (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))) p0004
      p0006
  have p0008 :=
    @gJca
      (synWa (.classMem A (synCvv))
        (synWbr (.cv u) (synClnker (synChncodecmpset A)) (.cv v)))
      (.classMem A (synCvv))
      (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))) p0000
      p0007
  have p0010 :=
    @gJca
      (synWa (.classMem A (synCvv))
        (synWbr (.cv u) (synClnker (synChncodecmpset A)) (.cv v)))
      (synWa (.classMem A (synCvv))
        (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
      (synWbr (.cv u) (synClnker (synChncodecmpset A)) (.cv v)) p0008 p0001
  have p0011 :=
    @gSimpr
      (synWa (.classMem A (synCvv))
        (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
      (synWbr (.cv u) (synClnker (synChncodecmpset A)) (.cv v))
  have p0013 :=
    @gSylib
      (synWa (synWa (.classMem A (synCvv))
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
        (synWbr (.cv u) (synClnker (synChncodecmpset A)) (.cv v)))
      (synWbr (.cv u) (synClnker (synChncodecmpset A)) (.cv v))
      (synWa (synWbr (.cv u) (synChncodecmpset A) (.cv v))
        (synWbr (.cv v) (synChncodecmpset A) (.cv u)))
      p0011 p0002
  have p0014 :=
    @gSimprd
      (synWa (synWa (.classMem A (synCvv))
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
        (synWbr (.cv u) (synClnker (synChncodecmpset A)) (.cv v)))
      (synWbr (.cv u) (synChncodecmpset A) (.cv v))
      (synWbr (.cv v) (synChncodecmpset A) (.cv u)) p0013
  have p0015 :=
    @gSimpl
      (synWa (.classMem A (synCvv))
        (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
      (synWbr (.cv u) (synClnker (synChncodecmpset A)) (.cv v))
  have p0016 :=
    @gHncodecmpstrictnoreversendv x v u A dv_cache_0001 dv_cache_0002 dv_cache_0003
      dv_cache_0004 dv_cache_0005
  have p0017 :=
    @gSyl
      (synWa (synWa (.classMem A (synCvv))
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
        (synWbr (.cv u) (synClnker (synChncodecmpset A)) (.cv v)))
      (synWa (.classMem A (synCvv))
        (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
      (.imp (synWrex x (synCfv (synC2nd) (.cv v)) (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
              (.cv x)))) (.neg (synWbr (.cv v) (synChncodecmpset A) (.cv u))))
      p0015 p0016
  have p0018 :=
    @gMt2d
      (synWa (synWa (.classMem A (synCvv))
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
        (synWbr (.cv u) (synClnker (synChncodecmpset A)) (.cv v)))
      (synWrex x (synCfv (synC2nd) (.cv v)) (synWbr (.cv u) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x))))
      (synWbr (.cv v) (synChncodecmpset A) (.cv u)) p0014 p0017
  have p0022 :=
    @gSimpld
      (synWa (synWa (.classMem A (synCvv))
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
        (synWbr (.cv u) (synClnker (synChncodecmpset A)) (.cv v)))
      (synWbr (.cv u) (synChncodecmpset A) (.cv v))
      (synWbr (.cv v) (synChncodecmpset A) (.cv u)) p0013
  have p0024 :=
    @gSimpr (.classMem A (synCvv))
      (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
  have p0025 :=
    @gSyl
      (synWa (synWa (.classMem A (synCvv))
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
        (synWbr (.cv u) (synClnker (synChncodecmpset A)) (.cv v)))
      (synWa (.classMem A (synCvv))
        (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
      (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))) p0015
      p0024
  have p0026 :=
    @gHncodecmpsetstrictcutsemclndv x A (.cv u) (.cv v) dv_cache_0003 dv_cache_0006
      dv_cache_0007
  have p0027 :=
    @gSyl
      (synWa (synWa (.classMem A (synCvv))
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
        (synWbr (.cv u) (synClnker (synChncodecmpset A)) (.cv v)))
      (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
      (synWb (synWbr (.cv u) (synChncodecmpset A) (.cv v))
        (synWo (synWbr (.cv u) (synChwniso A) (.cv v))
          (synWrex x (synCfv (synC2nd) (.cv v)) (synWbr (.cv u) (synChwniso A)
              (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                (.cv x))))))
      p0025 p0026
  have p0028 :=
    @gMpbid
      (synWa (synWa (.classMem A (synCvv))
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
        (synWbr (.cv u) (synClnker (synChncodecmpset A)) (.cv v)))
      (synWbr (.cv u) (synChncodecmpset A) (.cv v))
      (synWo (synWbr (.cv u) (synChwniso A) (.cv v)) (synWrex x (synCfv (synC2nd) (.cv v))
          (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
              (.cv x)))))
      p0022 p0027
  have p0029 :=
    @gOrcomd
      (synWa (synWa (.classMem A (synCvv))
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
        (synWbr (.cv u) (synClnker (synChncodecmpset A)) (.cv v)))
      (synWbr (.cv u) (synChwniso A) (.cv v))
      (synWrex x (synCfv (synC2nd) (.cv v)) (synWbr (.cv u) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x))))
      p0028
  have p0030 :=
    @gOrcanai
      (synWa (synWa (.classMem A (synCvv))
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
        (synWbr (.cv u) (synClnker (synChncodecmpset A)) (.cv v)))
      (synWrex x (synCfv (synC2nd) (.cv v)) (synWbr (.cv u) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x))))
      (synWbr (.cv u) (synChwniso A) (.cv v)) p0029
  have p0031 :=
    @gMpdan
      (synWa (synWa (.classMem A (synCvv))
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
        (synWbr (.cv u) (synClnker (synChncodecmpset A)) (.cv v)))
      (.neg (synWrex x (synCfv (synC2nd) (.cv v)) (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
              (.cv x)))))
      (synWbr (.cv u) (synChwniso A) (.cv v)) p0018 p0030
  have p0032 :=
    @gSyl
      (synWa (.classMem A (synCvv))
        (synWbr (.cv u) (synClnker (synChncodecmpset A)) (.cv v)))
      (synWa (synWa (.classMem A (synCvv))
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
        (synWbr (.cv u) (synClnker (synChncodecmpset A)) (.cv v)))
      (synWbr (.cv u) (synChwniso A) (.cv v)) p0010 p0031
  have p0033 :=
    @gEx (.classMem A (synCvv))
      (synWbr (.cv u) (synClnker (synChncodecmpset A)) (.cv v))
      (synWbr (.cv u) (synChwniso A) (.cv v)) p0032
  have p0034 := @gSimpl (.classMem A (synCvv)) (synWbr (.cv u) (synChwniso A) (.cv v))
  have p0035 := @gSimpr (.classMem A (synCvv)) (synWbr (.cv u) (synChwniso A) (.cv v))
  have p0036 := @gBreldm (.cv u) (.cv v) (synChwniso A)
  have p0037 :=
    @gSyl (synWa (.classMem A (synCvv)) (synWbr (.cv u) (synChwniso A) (.cv v)))
      (synWbr (.cv u) (synChwniso A) (.cv v))
      (.classMem (.cv u) (synCdm (synChwniso A))) p0035 p0036
  have p0038 := @gHwnisodm A
  have p0039 :=
    @gA1i (.classEq (synCdm (synChwniso A)) (synChwcn A))
      (synWa (.classMem A (synCvv)) (synWbr (.cv u) (synChwniso A) (.cv v))) p0038
  have p0040 :=
    @gEleqtrd (synWa (.classMem A (synCvv)) (synWbr (.cv u) (synChwniso A) (.cv v)))
      (.cv u) (synCdm (synChwniso A)) (synChwcn A) p0037 p0039
  have p0042 := @gHwnisosymi v u A dv_cache_0001 dv_cache_0002 dv_cache_0008
  have p0043 :=
    @gSyl (synWa (.classMem A (synCvv)) (synWbr (.cv u) (synChwniso A) (.cv v)))
      (synWbr (.cv u) (synChwniso A) (.cv v)) (synWbr (.cv v) (synChwniso A) (.cv u))
      p0035 p0042
  have p0044 := @gBreldm (.cv v) (.cv u) (synChwniso A)
  have p0045 :=
    @gSyl (synWa (.classMem A (synCvv)) (synWbr (.cv u) (synChwniso A) (.cv v)))
      (synWbr (.cv v) (synChwniso A) (.cv u))
      (.classMem (.cv v) (synCdm (synChwniso A))) p0043 p0044
  have p0048 :=
    @gEleqtrd (synWa (.classMem A (synCvv)) (synWbr (.cv u) (synChwniso A) (.cv v)))
      (.cv v) (synCdm (synChwniso A)) (synChwcn A) p0045 p0039
  have p0049 :=
    @gJca (synWa (.classMem A (synCvv)) (synWbr (.cv u) (synChwniso A) (.cv v)))
      (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)) p0040 p0048
  have p0050 :=
    @gJca (synWa (.classMem A (synCvv)) (synWbr (.cv u) (synChwniso A) (.cv v)))
      (.classMem A (synCvv))
      (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))) p0034
      p0049
  have p0052 :=
    @gJca (synWa (.classMem A (synCvv)) (synWbr (.cv u) (synChwniso A) (.cv v)))
      (synWa (.classMem A (synCvv))
        (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
      (synWbr (.cv u) (synChwniso A) (.cv v)) p0050 p0035
  have p0053 :=
    @gSimpr
      (synWa (.classMem A (synCvv))
        (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
      (synWbr (.cv u) (synChwniso A) (.cv v))
  have p0054 :=
    @gOrc (synWbr (.cv u) (synChwniso A) (.cv v))
      (synWrex x (synCfv (synC2nd) (.cv v)) (synWbr (.cv u) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x))))
  have p0055 :=
    @gSyl
      (synWa (synWa (.classMem A (synCvv))
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
        (synWbr (.cv u) (synChwniso A) (.cv v)))
      (synWbr (.cv u) (synChwniso A) (.cv v))
      (synWo (synWbr (.cv u) (synChwniso A) (.cv v)) (synWrex x (synCfv (synC2nd) (.cv v))
          (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
              (.cv x)))))
      p0053 p0054
  have p0056 :=
    @gSimpl
      (synWa (.classMem A (synCvv))
        (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
      (synWbr (.cv u) (synChwniso A) (.cv v))
  have p0058 :=
    @gSyl
      (synWa (synWa (.classMem A (synCvv))
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
        (synWbr (.cv u) (synChwniso A) (.cv v)))
      (synWa (.classMem A (synCvv))
        (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
      (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))) p0056
      p0024
  have p0060 :=
    @gSyl
      (synWa (synWa (.classMem A (synCvv))
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
        (synWbr (.cv u) (synChwniso A) (.cv v)))
      (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
      (synWb (synWbr (.cv u) (synChncodecmpset A) (.cv v))
        (synWo (synWbr (.cv u) (synChwniso A) (.cv v))
          (synWrex x (synCfv (synC2nd) (.cv v)) (synWbr (.cv u) (synChwniso A)
              (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                (.cv x))))))
      p0058 p0026
  have p0061 :=
    @gMpbird
      (synWa (synWa (.classMem A (synCvv))
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
        (synWbr (.cv u) (synChwniso A) (.cv v)))
      (synWbr (.cv u) (synChncodecmpset A) (.cv v))
      (synWo (synWbr (.cv u) (synChwniso A) (.cv v)) (synWrex x (synCfv (synC2nd) (.cv v))
          (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
              (.cv x)))))
      p0055 p0060
  have p0064 :=
    @gSyl
      (synWa (synWa (.classMem A (synCvv))
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
        (synWbr (.cv u) (synChwniso A) (.cv v)))
      (synWbr (.cv u) (synChwniso A) (.cv v)) (synWbr (.cv v) (synChwniso A) (.cv u))
      p0053 p0042
  have p0065 :=
    @gOrc (synWbr (.cv v) (synChwniso A) (.cv u))
      (synWrex y (synCfv (synC2nd) (.cv u)) (synWbr (.cv v) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv y))))
  have p0066 :=
    @gSyl
      (synWa (synWa (.classMem A (synCvv))
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
        (synWbr (.cv u) (synChwniso A) (.cv v)))
      (synWbr (.cv v) (synChwniso A) (.cv u))
      (synWo (synWbr (.cv v) (synChwniso A) (.cv u)) (synWrex y (synCfv (synC2nd) (.cv u))
          (synWbr (.cv v) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
              (.cv y)))))
      p0064 p0065
  have p0070 :=
    @gSimprd
      (synWa (synWa (.classMem A (synCvv))
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
        (synWbr (.cv u) (synChwniso A) (.cv v)))
      (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)) p0058
  have p0074 :=
    @gSimpld
      (synWa (synWa (.classMem A (synCvv))
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
        (synWbr (.cv u) (synChwniso A) (.cv v)))
      (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)) p0058
  have p0075 :=
    @gJca
      (synWa (synWa (.classMem A (synCvv))
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
        (synWbr (.cv u) (synChwniso A) (.cv v)))
      (.classMem (.cv v) (synChwcn A)) (.classMem (.cv u) (synChwcn A)) p0070 p0074
  have p0076 :=
    @gHncodecmpsetstrictcutsemclndv y A (.cv v) (.cv u) dv_cache_0009 dv_cache_0010
      dv_cache_0011
  have p0077 :=
    @gSyl
      (synWa (synWa (.classMem A (synCvv))
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
        (synWbr (.cv u) (synChwniso A) (.cv v)))
      (synWa (.classMem (.cv v) (synChwcn A)) (.classMem (.cv u) (synChwcn A)))
      (synWb (synWbr (.cv v) (synChncodecmpset A) (.cv u))
        (synWo (synWbr (.cv v) (synChwniso A) (.cv u))
          (synWrex y (synCfv (synC2nd) (.cv u)) (synWbr (.cv v) (synChwniso A)
              (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
                (.cv y))))))
      p0075 p0076
  have p0078 :=
    @gMpbird
      (synWa (synWa (.classMem A (synCvv))
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
        (synWbr (.cv u) (synChwniso A) (.cv v)))
      (synWbr (.cv v) (synChncodecmpset A) (.cv u))
      (synWo (synWbr (.cv v) (synChwniso A) (.cv u)) (synWrex y (synCfv (synC2nd) (.cv u))
          (synWbr (.cv v) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
              (.cv y)))))
      p0066 p0077
  have p0079 :=
    @gJca
      (synWa (synWa (.classMem A (synCvv))
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
        (synWbr (.cv u) (synChwniso A) (.cv v)))
      (synWbr (.cv u) (synChncodecmpset A) (.cv v))
      (synWbr (.cv v) (synChncodecmpset A) (.cv u)) p0061 p0078
  have p0081 :=
    @gSylibr
      (synWa (synWa (.classMem A (synCvv))
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
        (synWbr (.cv u) (synChwniso A) (.cv v)))
      (synWa (synWbr (.cv u) (synChncodecmpset A) (.cv v))
        (synWbr (.cv v) (synChncodecmpset A) (.cv u)))
      (synWbr (.cv u) (synClnker (synChncodecmpset A)) (.cv v)) p0079 p0002
  have p0082 :=
    @gSyl (synWa (.classMem A (synCvv)) (synWbr (.cv u) (synChwniso A) (.cv v)))
      (synWa (synWa (.classMem A (synCvv))
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
        (synWbr (.cv u) (synChwniso A) (.cv v)))
      (synWbr (.cv u) (synClnker (synChncodecmpset A)) (.cv v)) p0052 p0081
  have p0083 :=
    @gEx (.classMem A (synCvv)) (synWbr (.cv u) (synChwniso A) (.cv v))
      (synWbr (.cv u) (synClnker (synChncodecmpset A)) (.cv v)) p0082
  have p0084 :=
    @gImpbid (.classMem A (synCvv))
      (synWbr (.cv u) (synClnker (synChncodecmpset A)) (.cv v))
      (synWbr (.cv u) (synChwniso A) (.cv v)) p0033 p0083
  have p0085 :=
    (Nominal.biimpRefl (synWbr (.cv u) (synClnker (synChncodecmpset A)) (.cv v)))
  have p0086 :=
    @gBicomi (synWbr (.cv u) (synClnker (synChncodecmpset A)) (.cv v))
      (.classMem (synCop (.cv u) (.cv v)) (synClnker (synChncodecmpset A))) p0085
  have p0087 := (Nominal.biimpRefl (synWbr (.cv u) (synChwniso A) (.cv v)))
  have p0088 :=
    @gBicomi (synWbr (.cv u) (synChwniso A) (.cv v))
      (.classMem (synCop (.cv u) (.cv v)) (synChwniso A)) p0087
  have p0089 :=
    @gN3bitr4g (.classMem A (synCvv))
      (synWbr (.cv u) (synClnker (synChncodecmpset A)) (.cv v))
      (synWbr (.cv u) (synChwniso A) (.cv v))
      (.classMem (synCop (.cv u) (.cv v)) (synClnker (synChncodecmpset A)))
      (.classMem (synCop (.cv u) (.cv v)) (synChwniso A)) p0084 p0086 p0088
  have p0090 :=
    @gEqrelrdv (.classMem A (synCvv)) u v (synClnker (synChncodecmpset A))
      (synChwniso A) dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
      dv_cache_0016 dv_cache_0017 dv_cache_0008 p0089
  exact p0090


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk017Compact001Part040`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_hncodecmpstrictbrndv`. -/
@[expose]
noncomputable def gHncodecmpstrictbrndv (x : Var) (v : Var) (u : Var) (A : Class)
    (dv_A_u : u ∉ A.fv) (dv_A_v : v ∉ A.fv) (dv_A_x : x ∉ A.fv) (dv_u_v : u ≠ v)
    (dv_u_x : u ≠ x) (dv_v_x : v ≠ x) :
    Nominal.NPrf
      (.imp (synWa (.classMem A (synCvv))
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))) (synWb
          (synWbr (.cv u)
            (synCdif (synChncodecmpset A) (synCcnv (synChncodecmpset A))) (.cv v))
          (synWrex x (synCfv (synC2nd) (.cv v)) (synWbr (.cv u) (synChwniso A)
              (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                (.cv x)))))) :=
  by
  have dv_cache_0001 : u ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_u, not_false_eq_true])
  have dv_cache_0002 : v ∉ (A).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_v, not_false_eq_true])
  have dv_cache_0003 : u ≠ v :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact (show u ≠ v from (by exact dv_u_v))
  have dv_cache_0004 : x ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_x, not_false_eq_true])
  have dv_cache_0005 : x ∉ ((Class.cv u)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          (Ne.symm dv_u_x), not_false_eq_true])
  have dv_cache_0006 : x ∉ ((Class.cv v)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          (Ne.symm dv_v_x), not_false_eq_true])
  have dv_cache_0007 : u ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact (show u ≠ x from (by exact dv_u_x))
  have dv_cache_0008 : v ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact (show v ≠ x from (by exact dv_v_x))
  have p0000 :=
    @gBrdif (.cv u) (.cv v) (synChncodecmpset A) (synCcnv (synChncodecmpset A))
  have p0001 := @gBrcnv (.cv u) (.cv v) (synChncodecmpset A)
  have p0002 :=
    @gNotbii (synWbr (.cv u) (synCcnv (synChncodecmpset A)) (.cv v))
      (synWbr (.cv v) (synChncodecmpset A) (.cv u)) p0001
  have p0003 :=
    @gAnbi2i (.neg (synWbr (.cv u) (synCcnv (synChncodecmpset A)) (.cv v)))
      (.neg (synWbr (.cv v) (synChncodecmpset A) (.cv u)))
      (synWbr (.cv u) (synChncodecmpset A) (.cv v)) p0002
  have p0004 :=
    @gBitri
      (synWbr (.cv u) (synCdif (synChncodecmpset A) (synCcnv (synChncodecmpset A)))
        (.cv v))
      (synWa (synWbr (.cv u) (synChncodecmpset A) (.cv v))
        (.neg (synWbr (.cv u) (synCcnv (synChncodecmpset A)) (.cv v))))
      (synWa (synWbr (.cv u) (synChncodecmpset A) (.cv v))
        (.neg (synWbr (.cv v) (synChncodecmpset A) (.cv u))))
      p0000 p0003
  have p0005 :=
    @gA1i
      (synWb (synWbr (.cv u) (synCdif (synChncodecmpset A) (synCcnv (synChncodecmpset A)))
          (.cv v)) (synWa (synWbr (.cv u) (synChncodecmpset A) (.cv v))
          (.neg (synWbr (.cv v) (synChncodecmpset A) (.cv u)))))
      (synWa (.classMem A (synCvv))
        (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
      p0004
  have p0006 :=
    @gSimpr
      (synWa (.classMem A (synCvv))
        (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
      (synWa (synWbr (.cv u) (synChncodecmpset A) (.cv v))
        (.neg (synWbr (.cv v) (synChncodecmpset A) (.cv u))))
  have p0007 :=
    @gSimprd
      (synWa (synWa (.classMem A (synCvv))
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
        (synWa (synWbr (.cv u) (synChncodecmpset A) (.cv v))
          (.neg (synWbr (.cv v) (synChncodecmpset A) (.cv u)))))
      (synWbr (.cv u) (synChncodecmpset A) (.cv v))
      (.neg (synWbr (.cv v) (synChncodecmpset A) (.cv u))) p0006
  have p0008 :=
    @gSimpl
      (synWa (.classMem A (synCvv))
        (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
      (synWa (synWbr (.cv u) (synChncodecmpset A) (.cv v))
        (.neg (synWbr (.cv v) (synChncodecmpset A) (.cv u))))
  have p0009 := @gHncodecmpkerptndv v u A dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0010 :=
    @gSyl
      (synWa (synWa (.classMem A (synCvv))
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
        (synWa (synWbr (.cv u) (synChncodecmpset A) (.cv v))
          (.neg (synWbr (.cv v) (synChncodecmpset A) (.cv u)))))
      (synWa (.classMem A (synCvv))
        (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
      (synWb (synWbr (.cv u) (synClnker (synChncodecmpset A)) (.cv v))
        (synWbr (.cv u) (synChwniso A) (.cv v)))
      p0008 p0009
  have p0011 :=
    @gBiimprd
      (synWa (synWa (.classMem A (synCvv))
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
        (synWa (synWbr (.cv u) (synChncodecmpset A) (.cv v))
          (.neg (synWbr (.cv v) (synChncodecmpset A) (.cv u)))))
      (synWbr (.cv u) (synClnker (synChncodecmpset A)) (.cv v))
      (synWbr (.cv u) (synChwniso A) (.cv v)) p0010
  have p0012 := @gBrlnker (synChncodecmpset A) (.cv u) (.cv v)
  have p0013 :=
    @gBiimpi (synWbr (.cv u) (synClnker (synChncodecmpset A)) (.cv v))
      (synWa (synWbr (.cv u) (synChncodecmpset A) (.cv v))
        (synWbr (.cv v) (synChncodecmpset A) (.cv u)))
      p0012
  have p0014 :=
    @gSyl6
      (synWa (synWa (.classMem A (synCvv))
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
        (synWa (synWbr (.cv u) (synChncodecmpset A) (.cv v))
          (.neg (synWbr (.cv v) (synChncodecmpset A) (.cv u)))))
      (synWbr (.cv u) (synChwniso A) (.cv v))
      (synWbr (.cv u) (synClnker (synChncodecmpset A)) (.cv v))
      (synWa (synWbr (.cv u) (synChncodecmpset A) (.cv v))
        (synWbr (.cv v) (synChncodecmpset A) (.cv u)))
      p0011 p0013
  have p0015 :=
    @gSimpr (synWbr (.cv u) (synChncodecmpset A) (.cv v))
      (synWbr (.cv v) (synChncodecmpset A) (.cv u))
  have p0016 :=
    @gSyl6
      (synWa (synWa (.classMem A (synCvv))
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
        (synWa (synWbr (.cv u) (synChncodecmpset A) (.cv v))
          (.neg (synWbr (.cv v) (synChncodecmpset A) (.cv u)))))
      (synWbr (.cv u) (synChwniso A) (.cv v))
      (synWa (synWbr (.cv u) (synChncodecmpset A) (.cv v))
        (synWbr (.cv v) (synChncodecmpset A) (.cv u)))
      (synWbr (.cv v) (synChncodecmpset A) (.cv u)) p0014 p0015
  have p0017 :=
    @gMtod
      (synWa (synWa (.classMem A (synCvv))
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
        (synWa (synWbr (.cv u) (synChncodecmpset A) (.cv v))
          (.neg (synWbr (.cv v) (synChncodecmpset A) (.cv u)))))
      (synWbr (.cv u) (synChwniso A) (.cv v))
      (synWbr (.cv v) (synChncodecmpset A) (.cv u)) p0007 p0016
  have p0019 :=
    @gSimpld
      (synWa (synWa (.classMem A (synCvv))
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
        (synWa (synWbr (.cv u) (synChncodecmpset A) (.cv v))
          (.neg (synWbr (.cv v) (synChncodecmpset A) (.cv u)))))
      (synWbr (.cv u) (synChncodecmpset A) (.cv v))
      (.neg (synWbr (.cv v) (synChncodecmpset A) (.cv u))) p0006
  have p0021 :=
    @gSimpr (.classMem A (synCvv))
      (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
  have p0022 :=
    @gSyl
      (synWa (synWa (.classMem A (synCvv))
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
        (synWa (synWbr (.cv u) (synChncodecmpset A) (.cv v))
          (.neg (synWbr (.cv v) (synChncodecmpset A) (.cv u)))))
      (synWa (.classMem A (synCvv))
        (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
      (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))) p0008
      p0021
  have p0023 :=
    @gHncodecmpsetstrictcutsemclndv x A (.cv u) (.cv v) dv_cache_0004 dv_cache_0005
      dv_cache_0006
  have p0024 :=
    @gSyl
      (synWa (synWa (.classMem A (synCvv))
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
        (synWa (synWbr (.cv u) (synChncodecmpset A) (.cv v))
          (.neg (synWbr (.cv v) (synChncodecmpset A) (.cv u)))))
      (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
      (synWb (synWbr (.cv u) (synChncodecmpset A) (.cv v))
        (synWo (synWbr (.cv u) (synChwniso A) (.cv v))
          (synWrex x (synCfv (synC2nd) (.cv v)) (synWbr (.cv u) (synChwniso A)
              (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                (.cv x))))))
      p0022 p0023
  have p0025 :=
    @gMpbid
      (synWa (synWa (.classMem A (synCvv))
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
        (synWa (synWbr (.cv u) (synChncodecmpset A) (.cv v))
          (.neg (synWbr (.cv v) (synChncodecmpset A) (.cv u)))))
      (synWbr (.cv u) (synChncodecmpset A) (.cv v))
      (synWo (synWbr (.cv u) (synChwniso A) (.cv v)) (synWrex x (synCfv (synC2nd) (.cv v))
          (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
              (.cv x)))))
      p0019 p0024
  have p0026 :=
    @gOrcanai
      (synWa (synWa (.classMem A (synCvv))
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
        (synWa (synWbr (.cv u) (synChncodecmpset A) (.cv v))
          (.neg (synWbr (.cv v) (synChncodecmpset A) (.cv u)))))
      (synWbr (.cv u) (synChwniso A) (.cv v))
      (synWrex x (synCfv (synC2nd) (.cv v)) (synWbr (.cv u) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x))))
      p0025
  have p0027 :=
    @gMpdan
      (synWa (synWa (.classMem A (synCvv))
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
        (synWa (synWbr (.cv u) (synChncodecmpset A) (.cv v))
          (.neg (synWbr (.cv v) (synChncodecmpset A) (.cv u)))))
      (.neg (synWbr (.cv u) (synChwniso A) (.cv v)))
      (synWrex x (synCfv (synC2nd) (.cv v)) (synWbr (.cv u) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x))))
      p0017 p0026
  have p0028 :=
    @gSimpr
      (synWa (.classMem A (synCvv))
        (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
      (synWrex x (synCfv (synC2nd) (.cv v)) (synWbr (.cv u) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x))))
  have p0029 :=
    @gOlc
      (synWrex x (synCfv (synC2nd) (.cv v)) (synWbr (.cv u) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x))))
      (synWbr (.cv u) (synChwniso A) (.cv v))
  have p0030 :=
    @gSyl
      (synWa (synWa (.classMem A (synCvv))
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
        (synWrex x (synCfv (synC2nd) (.cv v)) (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
              (.cv x)))))
      (synWrex x (synCfv (synC2nd) (.cv v)) (synWbr (.cv u) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x))))
      (synWo (synWbr (.cv u) (synChwniso A) (.cv v)) (synWrex x (synCfv (synC2nd) (.cv v))
          (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
              (.cv x)))))
      p0028 p0029
  have p0031 :=
    @gSimpl
      (synWa (.classMem A (synCvv))
        (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
      (synWrex x (synCfv (synC2nd) (.cv v)) (synWbr (.cv u) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x))))
  have p0033 :=
    @gSyl
      (synWa (synWa (.classMem A (synCvv))
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
        (synWrex x (synCfv (synC2nd) (.cv v)) (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
              (.cv x)))))
      (synWa (.classMem A (synCvv))
        (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
      (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))) p0031
      p0021
  have p0035 :=
    @gSyl
      (synWa (synWa (.classMem A (synCvv))
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
        (synWrex x (synCfv (synC2nd) (.cv v)) (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
              (.cv x)))))
      (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
      (synWb (synWbr (.cv u) (synChncodecmpset A) (.cv v))
        (synWo (synWbr (.cv u) (synChwniso A) (.cv v))
          (synWrex x (synCfv (synC2nd) (.cv v)) (synWbr (.cv u) (synChwniso A)
              (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                (.cv x))))))
      p0033 p0023
  have p0036 :=
    @gMpbird
      (synWa (synWa (.classMem A (synCvv))
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
        (synWrex x (synCfv (synC2nd) (.cv v)) (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
              (.cv x)))))
      (synWbr (.cv u) (synChncodecmpset A) (.cv v))
      (synWo (synWbr (.cv u) (synChwniso A) (.cv v)) (synWrex x (synCfv (synC2nd) (.cv v))
          (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
              (.cv x)))))
      p0030 p0035
  have p0039 :=
    @gHncodecmpstrictnoreversendv x v u A dv_cache_0001 dv_cache_0002 dv_cache_0004
      dv_cache_0007 dv_cache_0008
  have p0040 :=
    @gSyl
      (synWa (synWa (.classMem A (synCvv))
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
        (synWrex x (synCfv (synC2nd) (.cv v)) (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
              (.cv x)))))
      (synWa (.classMem A (synCvv))
        (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
      (.imp (synWrex x (synCfv (synC2nd) (.cv v)) (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
              (.cv x)))) (.neg (synWbr (.cv v) (synChncodecmpset A) (.cv u))))
      p0031 p0039
  have p0041 :=
    @gMpd
      (synWa (synWa (.classMem A (synCvv))
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
        (synWrex x (synCfv (synC2nd) (.cv v)) (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
              (.cv x)))))
      (synWrex x (synCfv (synC2nd) (.cv v)) (synWbr (.cv u) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x))))
      (.neg (synWbr (.cv v) (synChncodecmpset A) (.cv u))) p0028 p0040
  have p0042 :=
    @gJca
      (synWa (synWa (.classMem A (synCvv))
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
        (synWrex x (synCfv (synC2nd) (.cv v)) (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
              (.cv x)))))
      (synWbr (.cv u) (synChncodecmpset A) (.cv v))
      (.neg (synWbr (.cv v) (synChncodecmpset A) (.cv u))) p0036 p0041
  have p0043 :=
    @gImpbida
      (synWa (.classMem A (synCvv))
        (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
      (synWa (synWbr (.cv u) (synChncodecmpset A) (.cv v))
        (.neg (synWbr (.cv v) (synChncodecmpset A) (.cv u))))
      (synWrex x (synCfv (synC2nd) (.cv v)) (synWbr (.cv u) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x))))
      p0027 p0042
  have p0044 :=
    @gBitrd
      (synWa (.classMem A (synCvv))
        (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A))))
      (synWbr (.cv u) (synCdif (synChncodecmpset A) (synCcnv (synChncodecmpset A)))
        (.cv v))
      (synWa (synWbr (.cv u) (synChncodecmpset A) (.cv v))
        (.neg (synWbr (.cv v) (synChncodecmpset A) (.cv u))))
      (synWrex x (synCfv (synC2nd) (.cv v)) (synWbr (.cv u) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x))))
      p0005 p0043
  exact p0044

/-- Checked nominal proof certificate identified upstream as `g_hncodecutfnex`. -/
@[expose]
noncomputable def gHncodecutfnex :
    Nominal.NPrf (.classMem (synChncodecutfn) (synCvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (synChncodecutfn))
  have p0001 := (Nominal.classEqRefl (synChncoderelfn))
  have p0002 := @gLninteropex
  have p0003 := @gN1stex
  have p0005 := @gCoex (synC1st) (synC1st) p0003 p0003
  have p0006 := (Nominal.classEqRefl (synChncodesquarefn))
  have p0007 := @gCrossex
  have p0008 := (Nominal.classEqRefl (synChncodecarrierfn))
  have p0010 := @gN2ndex
  have p0012 := @gCoex (synC2nd) (synC1st) p0010 p0003
  have p0013 := (Nominal.classEqRefl (synChncodepredfn))
  have p0014 := @gLnimageopex
  have p0015 := @gSwapex
  have p0016 := @gImageex (synCswap) p0015
  have p0017 := (Nominal.classEqRefl (synChncodestrictfn))
  have p0018 := @gLndifopex
  have p0022 := @gVvex
  have p0023 := @gSnex (synCid)
  have p0024 := @gXpex (synCvv) (synCsn (synCid)) p0022 p0023
  have p0025 :=
    @gTxpex (synCcom (synC1st) (synC1st)) (synCxp (synCvv) (synCsn (synCid)))
      p0005 p0024
  have p0026 :=
    @gCoex (synClndifop)
      (synCtxp (synCcom (synC1st) (synC1st)) (synCxp (synCvv) (synCsn (synCid))))
      p0018 p0025
  have p0027 :=
    @gEqeltri (synChncodestrictfn)
      (synCcom (synClndifop) (synCtxp (synCcom (synC1st) (synC1st))
          (synCxp (synCvv) (synCsn (synCid)))))
      (synCvv) p0017 p0026
  have p0028 := @gCoex (synCimage (synCswap)) (synChncodestrictfn) p0016 p0027
  have p0030 :=
    @gTxpex (synCcom (synCimage (synCswap)) (synChncodestrictfn)) (synC2nd) p0028
      p0010
  have p0031 :=
    @gCoex (synClnimageop)
      (synCtxp (synCcom (synCimage (synCswap)) (synChncodestrictfn)) (synC2nd))
      p0014 p0030
  have p0032 :=
    @gEqeltri (synChncodepredfn)
      (synCcom (synClnimageop)
        (synCtxp (synCcom (synCimage (synCswap)) (synChncodestrictfn)) (synC2nd)))
      (synCvv) p0013 p0031
  have p0033 := @gTxpex (synCcom (synC2nd) (synC1st)) (synChncodepredfn) p0012 p0032
  have p0034 :=
    @gCoex (synClninterop)
      (synCtxp (synCcom (synC2nd) (synC1st)) (synChncodepredfn)) p0002 p0033
  have p0035 :=
    @gEqeltri (synChncodecarrierfn)
      (synCcom (synClninterop)
        (synCtxp (synCcom (synC2nd) (synC1st)) (synChncodepredfn)))
      (synCvv) p0008 p0034
  have p0064 := @gTxpex (synChncodecarrierfn) (synChncodecarrierfn) p0035 p0035
  have p0065 :=
    @gCoex (synCcross) (synCtxp (synChncodecarrierfn) (synChncodecarrierfn)) p0007
      p0064
  have p0066 :=
    @gEqeltri (synChncodesquarefn)
      (synCcom (synCcross) (synCtxp (synChncodecarrierfn) (synChncodecarrierfn)))
      (synCvv) p0006 p0065
  have p0067 :=
    @gTxpex (synCcom (synC1st) (synC1st)) (synChncodesquarefn) p0005 p0066
  have p0068 :=
    @gCoex (synClninterop)
      (synCtxp (synCcom (synC1st) (synC1st)) (synChncodesquarefn)) p0002 p0067
  have p0069 :=
    @gEqeltri (synChncoderelfn)
      (synCcom (synClninterop)
        (synCtxp (synCcom (synC1st) (synC1st)) (synChncodesquarefn)))
      (synCvv) p0001 p0068
  have p0098 := @gTxpex (synChncoderelfn) (synChncodecarrierfn) p0069 p0035
  have p0099 :=
    @gEqeltri (synChncodecutfn) (synCtxp (synChncoderelfn) (synChncodecarrierfn))
      (synCvv) p0000 p0098
  exact p0099

/-- Checked nominal proof certificate identified upstream as `g_hncodepredinputsexg`. -/
@[expose]
noncomputable def gHncodepredinputsexg (v : Var) (A : Class) (X : Class)
    (_dv_A_v : v ∉ A.fv) :
    Nominal.NPrf
      (.imp (synWa (.classMem A (synCvv)) (.classMem X (synCvv)))
        (.classMem (synChncodepredinputs A X v) (synCvv))) :=
  by
  have p0000 := @gSnex (.cv v)
  have p0001 := @gFvex (.cv v) (synC2nd)
  have p0002 := @gPw1ex (synCfv (synC2nd) (.cv v)) p0001
  have p0003 :=
    @gXpex (synCsn (.cv v)) (synCpw1 (synCfv (synC2nd) (.cv v))) p0000 p0002
  have p0004 :=
    @gA1i
      (.classMem (synCxp (synCsn (.cv v)) (synCpw1 (synCfv (synC2nd) (.cv v)))) (synCvv))
      (synWa (.classMem A (synCvv)) (.classMem X (synCvv))) p0003
  have p0005 := @gHncodecutfnex
  have p0006 := @gCnvexg (synChncodecutfn) (synCvv)
  have p0007 := Nominal.mp p0005 p0006
  have p0008 :=
    @gA1i (.classMem (synCcnv (synChncodecutfn)) (synCvv))
      (synWa (.classMem A (synCvv)) (.classMem X (synCvv))) p0007
  have p0009 := @gSimpl (.classMem A (synCvv)) (.classMem X (synCvv))
  have p0010 := @gHwnisoexg A
  have p0011 :=
    @gSyl (synWa (.classMem A (synCvv)) (.classMem X (synCvv)))
      (.classMem A (synCvv)) (.classMem (synChwniso A) (synCvv)) p0009 p0010
  have p0012 := @gSimpr (.classMem A (synCvv)) (.classMem X (synCvv))
  have p0013 :=
    @gJca (synWa (.classMem A (synCvv)) (.classMem X (synCvv)))
      (.classMem (synChwniso A) (synCvv)) (.classMem X (synCvv)) p0011 p0012
  have p0014 := @gImaexg (synChwniso A) X (synCvv) (synCvv)
  have p0015 :=
    @gSyl (synWa (.classMem A (synCvv)) (.classMem X (synCvv)))
      (synWa (.classMem (synChwniso A) (synCvv)) (.classMem X (synCvv)))
      (.classMem (synCima (synChwniso A) X) (synCvv)) p0013 p0014
  have p0016 :=
    @gJca (synWa (.classMem A (synCvv)) (.classMem X (synCvv)))
      (.classMem (synCcnv (synChncodecutfn)) (synCvv))
      (.classMem (synCima (synChwniso A) X) (synCvv)) p0008 p0015
  have p0017 :=
    @gImaexg (synCcnv (synChncodecutfn)) (synCima (synChwniso A) X) (synCvv)
      (synCvv)
  have p0018 :=
    @gSyl (synWa (.classMem A (synCvv)) (.classMem X (synCvv)))
      (synWa (.classMem (synCcnv (synChncodecutfn)) (synCvv))
        (.classMem (synCima (synChwniso A) X) (synCvv)))
      (.classMem (synCima (synCcnv (synChncodecutfn)) (synCima (synChwniso A) X))
        (synCvv))
      p0016 p0017
  have p0019 :=
    @gJca (synWa (.classMem A (synCvv)) (.classMem X (synCvv)))
      (.classMem (synCxp (synCsn (.cv v)) (synCpw1 (synCfv (synC2nd) (.cv v)))) (synCvv))
      (.classMem (synCima (synCcnv (synChncodecutfn)) (synCima (synChwniso A) X))
        (synCvv))
      p0004 p0018
  have p0020 :=
    @gInexg (synCxp (synCsn (.cv v)) (synCpw1 (synCfv (synC2nd) (.cv v))))
      (synCima (synCcnv (synChncodecutfn)) (synCima (synChwniso A) X)) (synCvv)
      (synCvv)
  have p0021 :=
    @gSyl (synWa (.classMem A (synCvv)) (.classMem X (synCvv)))
      (synWa (.classMem (synCxp (synCsn (.cv v)) (synCpw1 (synCfv (synC2nd) (.cv v))))
          (synCvv))
        (.classMem (synCima (synCcnv (synChncodecutfn)) (synCima (synChwniso A) X))
          (synCvv)))
      (.classMem (synCin (synCxp (synCsn (.cv v)) (synCpw1 (synCfv (synC2nd) (.cv v))))
          (synCima (synCcnv (synChncodecutfn)) (synCima (synChwniso A) X))) (synCvv))
      p0019 p0020
  have p0022 := (Nominal.classEqRefl (synChncodepredinputs A X v))
  have p0023 :=
    @gEleq1i (synChncodepredinputs A X v)
      (synCin (synCxp (synCsn (.cv v)) (synCpw1 (synCfv (synC2nd) (.cv v))))
        (synCima (synCcnv (synChncodecutfn)) (synCima (synChwniso A) X)))
      (synCvv) p0022
  have p0024 :=
    @gSylibr (synWa (.classMem A (synCvv)) (.classMem X (synCvv)))
      (.classMem (synCin (synCxp (synCsn (.cv v)) (synCpw1 (synCfv (synC2nd) (.cv v))))
          (synCima (synCcnv (synChncodecutfn)) (synCima (synChwniso A) X))) (synCvv))
      (.classMem (synChncodepredinputs A X v) (synCvv)) p0021 p0023
  exact p0024

/-- Checked nominal proof certificate identified upstream as `g_hncodepredinputsssndv`. -/
@[expose]
noncomputable def gHncodepredinputsssndv (v : Var) (A : Class) (X : Class)
    (_dv_A_v : v ∉ A.fv) :
    Nominal.NPrf
      (synWss (synChncodepredinputs A X v)
        (synCxp (synCsn (.cv v)) (synCpw1 (synCfv (synC2nd) (.cv v))))) :=
  by
  have p0000 := (Nominal.classEqRefl (synChncodepredinputs A X v))
  have p0001 :=
    @gInss1 (synCxp (synCsn (.cv v)) (synCpw1 (synCfv (synC2nd) (.cv v))))
      (synCima (synCcnv (synChncodecutfn)) (synCima (synChwniso A) X))
  have p0002 :=
    @gEqsstri (synChncodepredinputs A X v)
      (synCin (synCxp (synCsn (.cv v)) (synCpw1 (synCfv (synC2nd) (.cv v))))
        (synCima (synCcnv (synChncodecutfn)) (synCima (synChwniso A) X)))
      (synCxp (synCsn (.cv v)) (synCpw1 (synCfv (synC2nd) (.cv v)))) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_hncodepredinputmemndv`. -/
@[expose]
noncomputable def gHncodepredinputmemndv (x : Var) (v : Var) (u : Var) (A : Class)
    (X : Class) (dv_A_u : u ∉ A.fv) (dv_A_v : v ∉ A.fv) (dv_X_u : u ∉ X.fv)
    (dv_u_v : u ≠ v) (dv_u_x : u ≠ x) :
    Nominal.NPrf
      (.imp (.classMem (.cv v) (synChwcn A)) (synWb
          (.classMem (synCop (.cv v) (synCsn (.cv x))) (synChncodepredinputs A X v))
          (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv v))) (synWrex u X
              (synWbr (.cv u) (synChwniso A)
                (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                  (.cv x))))))) :=
  by
  have dv_cache_0001 : v ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_v, not_false_eq_true])
  have dv_cache_0002 :
    u ∉
      ((synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
          (.cv x))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutcode,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union,
          Finset.mem_singleton, dv_u_x, dv_u_v, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0003 : u ∉ ((synChwniso A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso, dv_A_u,
          not_false_eq_true])
  have dv_cache_0004 : u ∉ (X).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_X_u, not_false_eq_true])
  have p0000 := (Nominal.classEqRefl (synChncodepredinputs A X v))
  have p0001 :=
    @gEleq2i (synChncodepredinputs A X v)
      (synCin (synCxp (synCsn (.cv v)) (synCpw1 (synCfv (synC2nd) (.cv v))))
        (synCima (synCcnv (synChncodecutfn)) (synCima (synChwniso A) X)))
      (synCop (.cv v) (synCsn (.cv x))) p0000
  have p0002 :=
    @gA1i
      (synWb (.classMem (synCop (.cv v) (synCsn (.cv x))) (synChncodepredinputs A X v))
        (.classMem (synCop (.cv v) (synCsn (.cv x)))
          (synCin (synCxp (synCsn (.cv v)) (synCpw1 (synCfv (synC2nd) (.cv v))))
            (synCima (synCcnv (synChncodecutfn)) (synCima (synChwniso A) X)))))
      (.classMem (.cv v) (synChwcn A)) p0001
  have p0003 :=
    @gElin (synCop (.cv v) (synCsn (.cv x)))
      (synCxp (synCsn (.cv v)) (synCpw1 (synCfv (synC2nd) (.cv v))))
      (synCima (synCcnv (synChncodecutfn)) (synCima (synChwniso A) X))
  have p0004 :=
    @gA1i
      (synWb (.classMem (synCop (.cv v) (synCsn (.cv x)))
          (synCin (synCxp (synCsn (.cv v)) (synCpw1 (synCfv (synC2nd) (.cv v))))
            (synCima (synCcnv (synChncodecutfn)) (synCima (synChwniso A) X)))) (synWa
          (.classMem (synCop (.cv v) (synCsn (.cv x)))
            (synCxp (synCsn (.cv v)) (synCpw1 (synCfv (synC2nd) (.cv v)))))
          (.classMem (synCop (.cv v) (synCsn (.cv x)))
            (synCima (synCcnv (synChncodecutfn)) (synCima (synChwniso A) X)))))
      (.classMem (.cv v) (synChwcn A)) p0003
  have p0005 :=
    @gOpelxp (.cv v) (synCsn (.cv x)) (synCsn (.cv v))
      (synCpw1 (synCfv (synC2nd) (.cv v)))
  have p0006 := @gVex v
  have p0007 := @gSnid (.cv v) p0006
  have p0008 :=
    @gBiantrur (.classMem (.cv v) (synCsn (.cv v)))
      (.classMem (synCsn (.cv x)) (synCpw1 (synCfv (synC2nd) (.cv v)))) p0007
  have p0009 :=
    @gBicomi (.classMem (synCsn (.cv x)) (synCpw1 (synCfv (synC2nd) (.cv v))))
      (synWa (.classMem (.cv v) (synCsn (.cv v)))
        (.classMem (synCsn (.cv x)) (synCpw1 (synCfv (synC2nd) (.cv v)))))
      p0008
  have p0010 :=
    @gBitri
      (.classMem (synCop (.cv v) (synCsn (.cv x)))
        (synCxp (synCsn (.cv v)) (synCpw1 (synCfv (synC2nd) (.cv v)))))
      (synWa (.classMem (.cv v) (synCsn (.cv v)))
        (.classMem (synCsn (.cv x)) (synCpw1 (synCfv (synC2nd) (.cv v)))))
      (.classMem (synCsn (.cv x)) (synCpw1 (synCfv (synC2nd) (.cv v)))) p0005 p0009
  have p0011 := @gSnelpw1 (.cv x) (synCfv (synC2nd) (.cv v))
  have p0012 :=
    @gBitri
      (.classMem (synCop (.cv v) (synCsn (.cv x)))
        (synCxp (synCsn (.cv v)) (synCpw1 (synCfv (synC2nd) (.cv v)))))
      (.classMem (synCsn (.cv x)) (synCpw1 (synCfv (synC2nd) (.cv v))))
      (.classMem (.cv x) (synCfv (synC2nd) (.cv v))) p0010 p0011
  have p0013 :=
    @gA1i
      (synWb (.classMem (synCop (.cv v) (synCsn (.cv x)))
          (synCxp (synCsn (.cv v)) (synCpw1 (synCfv (synC2nd) (.cv v)))))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv v))))
      (.classMem (.cv v) (synChwcn A)) p0012
  have p0014 := @gHncodecutfnfn
  have p0015 :=
    @gElpreima (synCvv) (synCop (.cv v) (synCsn (.cv x))) (synCima (synChwniso A) X)
      (synChncodecutfn)
  have p0016 := Nominal.mp p0014 p0015
  have p0018 := @gSnex (.cv x)
  have p0019 := @gOpex (.cv v) (synCsn (.cv x)) p0006 p0018
  have p0020 :=
    @gBiantrur (.classMem (synCop (.cv v) (synCsn (.cv x))) (synCvv))
      (.classMem (synCfv (synChncodecutfn) (synCop (.cv v) (synCsn (.cv x))))
        (synCima (synChwniso A) X))
      p0019
  have p0021 :=
    @gBicomi
      (.classMem (synCfv (synChncodecutfn) (synCop (.cv v) (synCsn (.cv x))))
        (synCima (synChwniso A) X))
      (synWa (.classMem (synCop (.cv v) (synCsn (.cv x))) (synCvv))
        (.classMem (synCfv (synChncodecutfn) (synCop (.cv v) (synCsn (.cv x))))
          (synCima (synChwniso A) X)))
      p0020
  have p0022 :=
    @gBitri
      (.classMem (synCop (.cv v) (synCsn (.cv x)))
        (synCima (synCcnv (synChncodecutfn)) (synCima (synChwniso A) X)))
      (synWa (.classMem (synCop (.cv v) (synCsn (.cv x))) (synCvv))
        (.classMem (synCfv (synChncodecutfn) (synCop (.cv v) (synCsn (.cv x))))
          (synCima (synChwniso A) X)))
      (.classMem (synCfv (synChncodecutfn) (synCop (.cv v) (synCsn (.cv x))))
        (synCima (synChwniso A) X))
      p0016 p0021
  have p0023 :=
    @gA1i
      (synWb (.classMem (synCop (.cv v) (synCsn (.cv x)))
          (synCima (synCcnv (synChncodecutfn)) (synCima (synChwniso A) X)))
        (.classMem (synCfv (synChncodecutfn) (synCop (.cv v) (synCsn (.cv x))))
          (synCima (synChwniso A) X)))
      (.classMem (.cv v) (synChwcn A)) p0022
  have p0024 := @gHncodecutfnvalhwcn x v A dv_cache_0001
  have p0025 :=
    @gEleq1d (.classMem (.cv v) (synChwcn A))
      (synCfv (synChncodecutfn) (synCop (.cv v) (synCsn (.cv x))))
      (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x))
      (synCima (synChwniso A) X) p0024
  have p0026 :=
    @gBitrd (.classMem (.cv v) (synChwcn A))
      (.classMem (synCop (.cv v) (synCsn (.cv x)))
        (synCima (synCcnv (synChncodecutfn)) (synCima (synChwniso A) X)))
      (.classMem (synCfv (synChncodecutfn) (synCop (.cv v) (synCsn (.cv x))))
        (synCima (synChwniso A) X))
      (.classMem (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
          (.cv x)) (synCima (synChwniso A) X))
      p0023 p0025
  have p0027 :=
    @gElima u
      (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x))
      (synChwniso A) X dv_cache_0002 dv_cache_0003 dv_cache_0004
  have p0028 :=
    @gA1i
      (synWb (.classMem
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x))
          (synCima (synChwniso A) X)) (synWrex u X (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
              (.cv x)))))
      (.classMem (.cv v) (synChwcn A)) p0027
  have p0029 :=
    @gBitrd (.classMem (.cv v) (synChwcn A))
      (.classMem (synCop (.cv v) (synCsn (.cv x)))
        (synCima (synCcnv (synChncodecutfn)) (synCima (synChwniso A) X)))
      (.classMem (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
          (.cv x)) (synCima (synChwniso A) X))
      (synWrex u X (synWbr (.cv u) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x))))
      p0026 p0028
  have p0030 :=
    @gAnbi12d (.classMem (.cv v) (synChwcn A))
      (.classMem (synCop (.cv v) (synCsn (.cv x)))
        (synCxp (synCsn (.cv v)) (synCpw1 (synCfv (synC2nd) (.cv v)))))
      (.classMem (.cv x) (synCfv (synC2nd) (.cv v)))
      (.classMem (synCop (.cv v) (synCsn (.cv x)))
        (synCima (synCcnv (synChncodecutfn)) (synCima (synChwniso A) X)))
      (synWrex u X (synWbr (.cv u) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x))))
      p0013 p0029
  have p0031 :=
    @gBitrd (.classMem (.cv v) (synChwcn A))
      (.classMem (synCop (.cv v) (synCsn (.cv x)))
        (synCin (synCxp (synCsn (.cv v)) (synCpw1 (synCfv (synC2nd) (.cv v))))
          (synCima (synCcnv (synChncodecutfn)) (synCima (synChwniso A) X))))
      (synWa (.classMem (synCop (.cv v) (synCsn (.cv x)))
          (synCxp (synCsn (.cv v)) (synCpw1 (synCfv (synC2nd) (.cv v)))))
        (.classMem (synCop (.cv v) (synCsn (.cv x)))
          (synCima (synCcnv (synChncodecutfn)) (synCima (synChwniso A) X))))
      (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv v))) (synWrex u X
          (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
              (.cv x)))))
      p0004 p0030
  have p0032 :=
    @gBitrd (.classMem (.cv v) (synChwcn A))
      (.classMem (synCop (.cv v) (synCsn (.cv x))) (synChncodepredinputs A X v))
      (.classMem (synCop (.cv v) (synCsn (.cv x)))
        (synCin (synCxp (synCsn (.cv v)) (synCpw1 (synCfv (synC2nd) (.cv v))))
          (synCima (synCcnv (synChncodecutfn)) (synCima (synChwniso A) X))))
      (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv v))) (synWrex u X
          (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
              (.cv x)))))
      p0002 p0031
  exact p0032

/-- Checked nominal proof certificate identified upstream as `g_hncodepredendsexg`. -/
@[expose]
noncomputable def gHncodepredendsexg (v : Var) (A : Class) (X : Class)
    (dv_A_v : v ∉ A.fv) :
    Nominal.NPrf
      (.imp (synWa (.classMem A (synCvv)) (.classMem X (synCvv)))
        (.classMem (synChncodepredends A X v) (synCvv))) :=
  by
  have dv_cache_0001 : v ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_v, not_false_eq_true])
  have p0000 := @gN2ndex
  have p0001 :=
    @gA1i (.classMem (synC2nd) (synCvv))
      (synWa (.classMem A (synCvv)) (.classMem X (synCvv))) p0000
  have p0002 := @gHncodepredinputsexg v A X dv_cache_0001
  have p0003 :=
    @gJca (synWa (.classMem A (synCvv)) (.classMem X (synCvv)))
      (.classMem (synC2nd) (synCvv)) (.classMem (synChncodepredinputs A X v) (synCvv))
      p0001 p0002
  have p0004 := @gImaexg (synC2nd) (synChncodepredinputs A X v) (synCvv) (synCvv)
  have p0005 :=
    @gSyl (synWa (.classMem A (synCvv)) (.classMem X (synCvv)))
      (synWa (.classMem (synC2nd) (synCvv))
        (.classMem (synChncodepredinputs A X v) (synCvv)))
      (.classMem (synCima (synC2nd) (synChncodepredinputs A X v)) (synCvv)) p0003
      p0004
  have p0006 := @gUniexg (synCima (synC2nd) (synChncodepredinputs A X v)) (synCvv)
  have p0007 :=
    @gSyl (synWa (.classMem A (synCvv)) (.classMem X (synCvv)))
      (.classMem (synCima (synC2nd) (synChncodepredinputs A X v)) (synCvv))
      (.classMem (synCuni (synCima (synC2nd) (synChncodepredinputs A X v))) (synCvv))
      p0005 p0006
  have p0008 := (Nominal.classEqRefl (synChncodepredends A X v))
  have p0009 :=
    @gEleq1i (synChncodepredends A X v)
      (synCuni (synCima (synC2nd) (synChncodepredinputs A X v))) (synCvv) p0008
  have p0010 :=
    @gSylibr (synWa (.classMem A (synCvv)) (.classMem X (synCvv)))
      (.classMem (synCuni (synCima (synC2nd) (synChncodepredinputs A X v))) (synCvv))
      (.classMem (synChncodepredends A X v) (synCvv)) p0007 p0009
  exact p0010


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk017Compact001Part041`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_hncodepredendsmemndv`. -/
@[expose]
noncomputable def gHncodepredendsmemndv (x : Var) (v : Var) (u : Var) (A : Class)
    (X : Class) (dv_A_u : u ∉ A.fv) (dv_A_v : v ∉ A.fv) (dv_X_u : u ∉ X.fv)
    (dv_u_v : u ≠ v) (dv_u_x : u ≠ x) :
    Nominal.NPrf
      (.imp (.classMem (.cv v) (synChwcn A))
        (synWb (.classMem (.cv x) (synChncodepredends A X v))
          (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv v))) (synWrex u X
              (synWbr (.cv u) (synChwniso A)
                (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                  (.cv x))))))) :=
  by
  let proofSupport : Finset Var :=
    ({ x } : Finset Var) ∪ ({ v } : Finset Var) ∪ ({ u } : Finset Var) ∪ A.fv ∪ X.fv
  let p : Var := freshVar proofSupport 0
  have fresh_p : p ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_p_ne_x : p ≠ x := by
    intro h
    exact
      fresh_p
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))
  have fresh_p_ne_v : p ≠ v := by
    intro h
    exact
      fresh_p
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))
  have fresh_p_ne_u : p ≠ u := by
    intro h
    exact
      fresh_p
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_p_not_A : p ∉ A.fv := by
    intro h
    exact fresh_p (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_p_not_X : p ∉ X.fv := by
    intro h
    exact fresh_p (Finset.mem_union_right _ (h))
  have dv_cache_0001 : p ∉ ((synChncodepredinputs A X v)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodepredinputs,
          Finset.mem_union, Finset.mem_singleton, fresh_p_not_A, fresh_p_not_X,
          fresh_p_ne_v, or_false, not_false_eq_true])
  have dv_cache_0002 : p ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_p_ne_x, not_false_eq_true])
  have dv_cache_0003 : p ∉ ((synC2nd)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0004 : v ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_v, not_false_eq_true])
  have dv_cache_0005 : u ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_u, not_false_eq_true])
  have dv_cache_0006 : u ∉ (X).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_X_u, not_false_eq_true])
  have dv_cache_0007 : u ≠ v :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact (show u ≠ v from (by exact dv_u_v))
  have dv_cache_0008 : u ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact (show u ≠ x from (by exact dv_u_x))
  have dv_cache_0009 :
    p ∉
      ((synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv v))) (synWrex u X
            (synWbr (.cv u) (synChwniso A)
              (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                (.cv x)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutcode,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_p_ne_x, fresh_p_ne_v,
          fresh_p_not_X, fresh_p_ne_u, fresh_p_not_A, compact_fv_not_mem_empty, or_false,
          and_false, not_false_eq_true])
  have dv_cache_0010 : p ∉ ((Wff.classMem (.cv v) (synChwcn A))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, Finset.mem_union,
          Finset.mem_singleton, fresh_p_ne_v, fresh_p_not_A, or_false, not_false_eq_true])
  have dv_cache_0011 : p ∉ ((synCop (.cv v) (synCsn (.cv x)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
          Finset.mem_singleton, fresh_p_ne_v, fresh_p_ne_x, or_false, not_false_eq_true])
  have dv_cache_0012 :
    p ∉
      ((Wff.classMem (.cv x) (synCfv (synC2nd) (synCop (.cv v) (synCsn (.cv x)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
          Finset.mem_singleton, fresh_p_ne_x, fresh_p_ne_v, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have p0000 := (Nominal.classEqRefl (synChncodepredends A X v))
  have p0001 :=
    @gEleq2i (synChncodepredends A X v)
      (synCuni (synCima (synC2nd) (synChncodepredinputs A X v))) (.cv x) p0000
  have p0002 := @gLn2ndfn
  have p0003 := @gFnfun (synCvv) (synC2nd)
  have p0004 := Nominal.mp p0002 p0003
  have p0005 :=
    @gEluniima p (synChncodepredinputs A X v) (.cv x) (synC2nd) dv_cache_0001
      dv_cache_0002 dv_cache_0003
  have p0006 := Nominal.mp p0004 p0005
  have p0007 :=
    @gBitri (.classMem (.cv x) (synChncodepredends A X v))
      (.classMem (.cv x) (synCuni (synCima (synC2nd) (synChncodepredinputs A X v))))
      (synWrex p (synChncodepredinputs A X v)
        (.classMem (.cv x) (synCfv (synC2nd) (.cv p))))
      p0001 p0006
  have p0008 :=
    @gA1i
      (synWb (.classMem (.cv x) (synChncodepredends A X v))
        (synWrex p (synChncodepredinputs A X v)
          (.classMem (.cv x) (synCfv (synC2nd) (.cv p)))))
      (.classMem (.cv v) (synChwcn A)) p0007
  have p0009 :=
    @gBiimpd (.classMem (.cv v) (synChwcn A))
      (.classMem (.cv x) (synChncodepredends A X v))
      (synWrex p (synChncodepredinputs A X v)
        (.classMem (.cv x) (synCfv (synC2nd) (.cv p))))
      p0008
  have p0010 :=
    @gSimpr (.classMem (.cv v) (synChwcn A))
      (synWa (.classMem (.cv p) (synChncodepredinputs A X v))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv p))))
  have p0011 :=
    @gSimpld
      (synWa (.classMem (.cv v) (synChwcn A))
        (synWa (.classMem (.cv p) (synChncodepredinputs A X v))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv p)))))
      (.classMem (.cv p) (synChncodepredinputs A X v))
      (.classMem (.cv x) (synCfv (synC2nd) (.cv p))) p0010
  have p0013 :=
    @gSimpl (.classMem (.cv p) (synChncodepredinputs A X v))
      (.classMem (.cv x) (synCfv (synC2nd) (.cv p)))
  have p0014 := @gHncodepredinputsssndv v A X dv_cache_0004
  have p0015 :=
    @gSseli (synChncodepredinputs A X v)
      (synCxp (synCsn (.cv v)) (synCpw1 (synCfv (synC2nd) (.cv v)))) (.cv p) p0014
  have p0016 :=
    @gSyl
      (synWa (.classMem (.cv p) (synChncodepredinputs A X v))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv p))))
      (.classMem (.cv p) (synChncodepredinputs A X v))
      (.classMem (.cv p) (synCxp (synCsn (.cv v)) (synCpw1 (synCfv (synC2nd) (.cv v)))))
      p0013 p0015
  have p0017 :=
    @gN1st2nd2 (.cv p) (synCsn (.cv v)) (synCpw1 (synCfv (synC2nd) (.cv v)))
  have p0018 :=
    @gSyl
      (synWa (.classMem (.cv p) (synChncodepredinputs A X v))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv p))))
      (.classMem (.cv p) (synCxp (synCsn (.cv v)) (synCpw1 (synCfv (synC2nd) (.cv v)))))
      (.classEq (.cv p) (synCop (synCfv (synC1st) (.cv p)) (synCfv (synC2nd) (.cv p))))
      p0016 p0017
  have p0029 :=
    @gEleq1d
      (synWa (.classMem (.cv p) (synChncodepredinputs A X v))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv p))))
      (.cv p) (synCop (synCfv (synC1st) (.cv p)) (synCfv (synC2nd) (.cv p)))
      (synCxp (synCsn (.cv v)) (synCpw1 (synCfv (synC2nd) (.cv v)))) p0018
  have p0030 :=
    @gMpbid
      (synWa (.classMem (.cv p) (synChncodepredinputs A X v))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv p))))
      (.classMem (.cv p) (synCxp (synCsn (.cv v)) (synCpw1 (synCfv (synC2nd) (.cv v)))))
      (.classMem (synCop (synCfv (synC1st) (.cv p)) (synCfv (synC2nd) (.cv p)))
        (synCxp (synCsn (.cv v)) (synCpw1 (synCfv (synC2nd) (.cv v)))))
      p0016 p0029
  have p0031 :=
    @gOpelxp (synCfv (synC1st) (.cv p)) (synCfv (synC2nd) (.cv p)) (synCsn (.cv v))
      (synCpw1 (synCfv (synC2nd) (.cv v)))
  have p0032 :=
    @gA1i
      (synWb (.classMem (synCop (synCfv (synC1st) (.cv p)) (synCfv (synC2nd) (.cv p)))
          (synCxp (synCsn (.cv v)) (synCpw1 (synCfv (synC2nd) (.cv v)))))
        (synWa (.classMem (synCfv (synC1st) (.cv p)) (synCsn (.cv v)))
          (.classMem (synCfv (synC2nd) (.cv p)) (synCpw1 (synCfv (synC2nd) (.cv v))))))
      (synWa (.classMem (.cv p) (synChncodepredinputs A X v))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv p))))
      p0031
  have p0033 :=
    @gMpbid
      (synWa (.classMem (.cv p) (synChncodepredinputs A X v))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv p))))
      (.classMem (synCop (synCfv (synC1st) (.cv p)) (synCfv (synC2nd) (.cv p)))
        (synCxp (synCsn (.cv v)) (synCpw1 (synCfv (synC2nd) (.cv v)))))
      (synWa (.classMem (synCfv (synC1st) (.cv p)) (synCsn (.cv v)))
        (.classMem (synCfv (synC2nd) (.cv p)) (synCpw1 (synCfv (synC2nd) (.cv v)))))
      p0030 p0032
  have p0034 :=
    @gSimpld
      (synWa (.classMem (.cv p) (synChncodepredinputs A X v))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv p))))
      (.classMem (synCfv (synC1st) (.cv p)) (synCsn (.cv v)))
      (.classMem (synCfv (synC2nd) (.cv p)) (synCpw1 (synCfv (synC2nd) (.cv v))))
      p0033
  have p0035 := @gElsni (synCfv (synC1st) (.cv p)) (.cv v)
  have p0036 :=
    @gSyl
      (synWa (.classMem (.cv p) (synChncodepredinputs A X v))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv p))))
      (.classMem (synCfv (synC1st) (.cv p)) (synCsn (.cv v)))
      (.classEq (synCfv (synC1st) (.cv p)) (.cv v)) p0034 p0035
  have p0052 :=
    @gSimprd
      (synWa (.classMem (.cv p) (synChncodepredinputs A X v))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv p))))
      (.classMem (synCfv (synC1st) (.cv p)) (synCsn (.cv v)))
      (.classMem (synCfv (synC2nd) (.cv p)) (synCpw1 (synCfv (synC2nd) (.cv v))))
      p0033
  have p0053 := @gPw1argclcl (synCfv (synC2nd) (.cv v)) (synCfv (synC2nd) (.cv p))
  have p0054 :=
    @gSyl
      (synWa (.classMem (.cv p) (synChncodepredinputs A X v))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv p))))
      (.classMem (synCfv (synC2nd) (.cv p)) (synCpw1 (synCfv (synC2nd) (.cv v))))
      (synWa (.classMem (synCuni (synCfv (synC2nd) (.cv p))) (synCfv (synC2nd) (.cv v)))
        (.classEq (synCfv (synC2nd) (.cv p))
          (synCsn (synCuni (synCfv (synC2nd) (.cv p))))))
      p0052 p0053
  have p0055 :=
    @gSimprd
      (synWa (.classMem (.cv p) (synChncodepredinputs A X v))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv p))))
      (.classMem (synCuni (synCfv (synC2nd) (.cv p))) (synCfv (synC2nd) (.cv v)))
      (.classEq (synCfv (synC2nd) (.cv p)) (synCsn (synCuni (synCfv (synC2nd) (.cv p)))))
      p0054
  have p0056 :=
    @gSimpr (.classMem (.cv p) (synChncodepredinputs A X v))
      (.classMem (.cv x) (synCfv (synC2nd) (.cv p)))
  have p0076 :=
    @gEleqtrd
      (synWa (.classMem (.cv p) (synChncodepredinputs A X v))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv p))))
      (.cv x) (synCfv (synC2nd) (.cv p))
      (synCsn (synCuni (synCfv (synC2nd) (.cv p)))) p0056 p0055
  have p0077 := @gElsni (.cv x) (synCuni (synCfv (synC2nd) (.cv p)))
  have p0078 :=
    @gSyl
      (synWa (.classMem (.cv p) (synChncodepredinputs A X v))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv p))))
      (.classMem (.cv x) (synCsn (synCuni (synCfv (synC2nd) (.cv p)))))
      (.classEq (.cv x) (synCuni (synCfv (synC2nd) (.cv p)))) p0076 p0077
  have p0079 :=
    @gEqcomd
      (synWa (.classMem (.cv p) (synChncodepredinputs A X v))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv p))))
      (.cv x) (synCuni (synCfv (synC2nd) (.cv p))) p0078
  have p0080 :=
    @gSneqd
      (synWa (.classMem (.cv p) (synChncodepredinputs A X v))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv p))))
      (synCuni (synCfv (synC2nd) (.cv p))) (.cv x) p0079
  have p0081 :=
    @gEqtrd
      (synWa (.classMem (.cv p) (synChncodepredinputs A X v))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv p))))
      (synCfv (synC2nd) (.cv p)) (synCsn (synCuni (synCfv (synC2nd) (.cv p))))
      (synCsn (.cv x)) p0055 p0080
  have p0082 :=
    @gOpeq12d
      (synWa (.classMem (.cv p) (synChncodepredinputs A X v))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv p))))
      (synCfv (synC1st) (.cv p)) (.cv v) (synCfv (synC2nd) (.cv p)) (synCsn (.cv x))
      p0036 p0081
  have p0083 :=
    @gEqtrd
      (synWa (.classMem (.cv p) (synChncodepredinputs A X v))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv p))))
      (.cv p) (synCop (synCfv (synC1st) (.cv p)) (synCfv (synC2nd) (.cv p)))
      (synCop (.cv v) (synCsn (.cv x))) p0018 p0082
  have p0084 :=
    @gSyl
      (synWa (.classMem (.cv v) (synChwcn A))
        (synWa (.classMem (.cv p) (synChncodepredinputs A X v))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv p)))))
      (synWa (.classMem (.cv p) (synChncodepredinputs A X v))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv p))))
      (.classEq (.cv p) (synCop (.cv v) (synCsn (.cv x)))) p0010 p0083
  have p0085 :=
    @gEleq1d
      (synWa (.classMem (.cv v) (synChwcn A))
        (synWa (.classMem (.cv p) (synChncodepredinputs A X v))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv p)))))
      (.cv p) (synCop (.cv v) (synCsn (.cv x))) (synChncodepredinputs A X v) p0084
  have p0086 :=
    @gMpbid
      (synWa (.classMem (.cv v) (synChwcn A))
        (synWa (.classMem (.cv p) (synChncodepredinputs A X v))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv p)))))
      (.classMem (.cv p) (synChncodepredinputs A X v))
      (.classMem (synCop (.cv v) (synCsn (.cv x))) (synChncodepredinputs A X v)) p0011
      p0085
  have p0087 :=
    @gSimpl (.classMem (.cv v) (synChwcn A))
      (synWa (.classMem (.cv p) (synChncodepredinputs A X v))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv p))))
  have p0088 :=
    @gHncodepredinputmemndv x v u A X dv_cache_0005 dv_cache_0004 dv_cache_0006
      dv_cache_0007 dv_cache_0008
  have p0089 :=
    @gSyl
      (synWa (.classMem (.cv v) (synChwcn A))
        (synWa (.classMem (.cv p) (synChncodepredinputs A X v))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv p)))))
      (.classMem (.cv v) (synChwcn A))
      (synWb (.classMem (synCop (.cv v) (synCsn (.cv x))) (synChncodepredinputs A X v))
        (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv v))) (synWrex u X
            (synWbr (.cv u) (synChwniso A)
              (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                (.cv x))))))
      p0087 p0088
  have p0090 :=
    @gMpbid
      (synWa (.classMem (.cv v) (synChwcn A))
        (synWa (.classMem (.cv p) (synChncodepredinputs A X v))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv p)))))
      (.classMem (synCop (.cv v) (synCsn (.cv x))) (synChncodepredinputs A X v))
      (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv v))) (synWrex u X
          (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
              (.cv x)))))
      p0086 p0089
  have p0091 :=
    @gRexlimdvaa (.classMem (.cv v) (synChwcn A))
      (.classMem (.cv x) (synCfv (synC2nd) (.cv p)))
      (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv v))) (synWrex u X
          (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
              (.cv x)))))
      p (synChncodepredinputs A X v) dv_cache_0009 dv_cache_0010 p0090
  have p0092 :=
    @gSyld (.classMem (.cv v) (synChwcn A))
      (.classMem (.cv x) (synChncodepredends A X v))
      (synWrex p (synChncodepredinputs A X v)
        (.classMem (.cv x) (synCfv (synC2nd) (.cv p))))
      (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv v))) (synWrex u X
          (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
              (.cv x)))))
      p0009 p0091
  have p0093 :=
    @gSimpr (.classMem (.cv v) (synChwcn A))
      (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv v))) (synWrex u X
          (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
              (.cv x)))))
  have p0094 :=
    @gSimpl (.classMem (.cv v) (synChwcn A))
      (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv v))) (synWrex u X
          (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
              (.cv x)))))
  have p0096 :=
    @gBiimprd (.classMem (.cv v) (synChwcn A))
      (.classMem (synCop (.cv v) (synCsn (.cv x))) (synChncodepredinputs A X v))
      (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv v))) (synWrex u X
          (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
              (.cv x)))))
      p0088
  have p0097 :=
    @gSyl
      (synWa (.classMem (.cv v) (synChwcn A))
        (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv v))) (synWrex u X
            (synWbr (.cv u) (synChwniso A)
              (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                (.cv x))))))
      (.classMem (.cv v) (synChwcn A))
      (.imp (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv v))) (synWrex u X
            (synWbr (.cv u) (synChwniso A)
              (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                (.cv x)))))
        (.classMem (synCop (.cv v) (synCsn (.cv x))) (synChncodepredinputs A X v)))
      p0094 p0096
  have p0098 :=
    @gMpd
      (synWa (.classMem (.cv v) (synChwcn A))
        (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv v))) (synWrex u X
            (synWbr (.cv u) (synChwniso A)
              (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                (.cv x))))))
      (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv v))) (synWrex u X
          (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
              (.cv x)))))
      (.classMem (synCop (.cv v) (synCsn (.cv x))) (synChncodepredinputs A X v)) p0093
      p0097
  have p0099 := @gVex x
  have p0100 := @gSnid (.cv x) p0099
  have p0101 := @gVex v
  have p0102 := @gSnex (.cv x)
  have p0103 := @gOpfv2nd (.cv v) (synCsn (.cv x)) p0101 p0102
  have p0104 :=
    @gEleqtrri (.cv x) (synCsn (.cv x))
      (synCfv (synC2nd) (synCop (.cv v) (synCsn (.cv x)))) p0100 p0103
  have p0105 :=
    @gA1i (.classMem (.cv x) (synCfv (synC2nd) (synCop (.cv v) (synCsn (.cv x)))))
      (synWa (.classMem (.cv v) (synChwcn A))
        (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv v))) (synWrex u X
            (synWbr (.cv u) (synChwniso A)
              (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                (.cv x))))))
      p0104
  have p0106 :=
    @gJca
      (synWa (.classMem (.cv v) (synChwcn A))
        (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv v))) (synWrex u X
            (synWbr (.cv u) (synChwniso A)
              (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                (.cv x))))))
      (.classMem (synCop (.cv v) (synCsn (.cv x))) (synChncodepredinputs A X v))
      (.classMem (.cv x) (synCfv (synC2nd) (synCop (.cv v) (synCsn (.cv x))))) p0098
      p0105
  have p0107 := @gId (.classEq (.cv p) (synCop (.cv v) (synCsn (.cv x))))
  have p0108 :=
    @gFveq2d (.classEq (.cv p) (synCop (.cv v) (synCsn (.cv x)))) (.cv p)
      (synCop (.cv v) (synCsn (.cv x))) (synC2nd) p0107
  have p0109 :=
    @gEleq2d (.classEq (.cv p) (synCop (.cv v) (synCsn (.cv x))))
      (synCfv (synC2nd) (.cv p))
      (synCfv (synC2nd) (synCop (.cv v) (synCsn (.cv x)))) (.cv x) p0108
  have p0110 :=
    @gRspcev (.classMem (.cv x) (synCfv (synC2nd) (.cv p)))
      (.classMem (.cv x) (synCfv (synC2nd) (synCop (.cv v) (synCsn (.cv x))))) p
      (synCop (.cv v) (synCsn (.cv x))) (synChncodepredinputs A X v) dv_cache_0011
      dv_cache_0001 dv_cache_0012 p0109
  have p0111 :=
    @gSyl
      (synWa (.classMem (.cv v) (synChwcn A))
        (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv v))) (synWrex u X
            (synWbr (.cv u) (synChwniso A)
              (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                (.cv x))))))
      (synWa (.classMem (synCop (.cv v) (synCsn (.cv x))) (synChncodepredinputs A X v))
        (.classMem (.cv x) (synCfv (synC2nd) (synCop (.cv v) (synCsn (.cv x))))))
      (synWrex p (synChncodepredinputs A X v)
        (.classMem (.cv x) (synCfv (synC2nd) (.cv p))))
      p0106 p0110
  have p0120 :=
    @gBiimpri (.classMem (.cv x) (synChncodepredends A X v))
      (synWrex p (synChncodepredinputs A X v)
        (.classMem (.cv x) (synCfv (synC2nd) (.cv p))))
      p0007
  have p0121 :=
    @gSyl
      (synWa (.classMem (.cv v) (synChwcn A))
        (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv v))) (synWrex u X
            (synWbr (.cv u) (synChwniso A)
              (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                (.cv x))))))
      (synWrex p (synChncodepredinputs A X v)
        (.classMem (.cv x) (synCfv (synC2nd) (.cv p))))
      (.classMem (.cv x) (synChncodepredends A X v)) p0111 p0120
  have p0122 :=
    @gEx (.classMem (.cv v) (synChwcn A))
      (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv v))) (synWrex u X
          (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
              (.cv x)))))
      (.classMem (.cv x) (synChncodepredends A X v)) p0121
  have p0123 :=
    @gImpbid (.classMem (.cv v) (synChwcn A))
      (.classMem (.cv x) (synChncodepredends A X v))
      (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv v))) (synWrex u X
          (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
              (.cv x)))))
      p0092 p0122
  exact p0123

/-- Checked nominal proof certificate identified upstream as `g_hncodepredendsssndv`. -/
@[expose]
noncomputable def gHncodepredendsssndv (v : Var) (A : Class) (X : Class)
    (dv_A_v : v ∉ A.fv) :
    Nominal.NPrf
      (.imp (.classMem (.cv v) (synChwcn A))
        (synWss (synChncodepredends A X v) (synCfv (synC2nd) (.cv v)))) :=
  by
  let proofSupport : Finset Var := ({ v } : Finset Var) ∪ A.fv ∪ X.fv
  let x : Var := freshVar proofSupport 0
  let u : Var := freshVar proofSupport 1
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_ne_v : x ≠ v := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_X : x ∉ X.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_u : u ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_u_ne_v : u ≠ v := by
    intro h
    exact
      fresh_u
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_u_not_A : u ∉ A.fv := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_u_not_X : u ∉ X.fv := by
    intro h
    exact fresh_u (Finset.mem_union_right _ (h))
  have fresh_x_ne_u : x ≠ u :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_u_ne_x : u ≠ x := Ne.symm fresh_x_ne_u
  have dv_cache_0001 : u ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_u_not_A, not_false_eq_true])
  have dv_cache_0002 : v ∉ (A).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_v, not_false_eq_true])
  have dv_cache_0003 : u ∉ (X).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_u_not_X, not_false_eq_true])
  have dv_cache_0004 : u ≠ v :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show u ≠ v from (by exact fresh_u_ne_v))
  have dv_cache_0005 : u ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show u ≠ x from (by exact fresh_u_ne_x))
  have dv_cache_0006 : x ∉ ((synChncodepredends A X v)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodepredends,
          Finset.mem_union, Finset.mem_singleton, fresh_x_not_A, fresh_x_not_X,
          fresh_x_ne_v, or_false, not_false_eq_true])
  have dv_cache_0007 : x ∉ ((synCfv (synC2nd) (.cv v))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_v, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0008 : x ∉ ((Wff.classMem (.cv v) (synChwcn A))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_v, fresh_x_not_A, or_false, not_false_eq_true])
  have p0000 :=
    @gHncodepredendsmemndv x v u A X dv_cache_0001 dv_cache_0002 dv_cache_0003
      dv_cache_0004 dv_cache_0005
  have p0001 :=
    @gBiimpd (.classMem (.cv v) (synChwcn A))
      (.classMem (.cv x) (synChncodepredends A X v))
      (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv v))) (synWrex u X
          (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
              (.cv x)))))
      p0000
  have p0002 :=
    @gSimpl (.classMem (.cv x) (synCfv (synC2nd) (.cv v)))
      (synWrex u X (synWbr (.cv u) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv x))))
  have p0003 :=
    @gSyl6 (.classMem (.cv v) (synChwcn A))
      (.classMem (.cv x) (synChncodepredends A X v))
      (synWa (.classMem (.cv x) (synCfv (synC2nd) (.cv v))) (synWrex u X
          (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
              (.cv x)))))
      (.classMem (.cv x) (synCfv (synC2nd) (.cv v))) p0001 p0002
  have p0004 :=
    @gSsrdv (.classMem (.cv v) (synChwcn A)) x (synChncodepredends A X v)
      (synCfv (synC2nd) (.cv v)) dv_cache_0006 dv_cache_0007 dv_cache_0008 p0003
  exact p0004


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk017Compact001Part042`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as
`g_hnwcutcodetransportintocutsegndv`.
-/
@[expose]
noncomputable def gHnwcutcodetransportintocutsegndv (x : Var) (y : Var) (z : Var)
    (v : Var) (u : Var) (A : Class) (dv_A_u : u ∉ A.fv) (dv_A_v : v ∉ A.fv)
    (dv_A_z : z ∉ A.fv) (dv_u_z : u ≠ z) (dv_v_z : v ≠ z) (dv_x_z : x ≠ z)
    (dv_y_z : y ≠ z) :
    Nominal.NPrf
      (.imp (synWa (synWa
            (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
            (.classMem (.cv y) (synCfv (synC2nd) (.cv v)))) (synWa
            (synWbr (.cv u) (synChwniso A)
              (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                (.cv y))) (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))) (synWrex z
          (synCin (synCfv (synC2nd) (.cv v))
            (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
              (synCsn (.cv y)))) (synWbr
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
            (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
              (.cv z))))) :=
  by
  let proofSupport : Finset Var :=
    ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ ({ z } : Finset Var) ∪
          ({ v } : Finset Var) ∪
        ({ u } : Finset Var) ∪
      A.fv
  let w : Var := freshVar proofSupport 0
  have fresh_w : w ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_w_ne_x : w ≠ x := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _
                (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))))
  have fresh_x_ne_w : x ≠ w := Ne.symm fresh_w_ne_x
  have fresh_w_ne_y : w ≠ y := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _
                (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))))
  have fresh_w_ne_z : w ≠ z := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))
  have fresh_z_ne_w : z ≠ w := Ne.symm fresh_w_ne_z
  have fresh_w_ne_v : w ≠ v := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_w_ne_u : w ≠ u := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_u_ne_w : u ≠ w := Ne.symm fresh_w_ne_u
  have fresh_w_not_A : w ∉ A.fv := by
    intro h
    exact fresh_w (Finset.mem_union_right _ (h))
  have dv_cache_0001 : v ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_v, not_false_eq_true])
  have dv_cache_0002 : u ∉ (A).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_u, not_false_eq_true])
  have dv_cache_0003 : w ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_w_not_A, not_false_eq_true])
  have dv_cache_0004 :
    w ∉
      ((synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
          (.cv y))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutcode,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union,
          Finset.mem_singleton, fresh_w_ne_y, fresh_w_ne_v, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0005 : u ≠ w :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show u ≠ w from (by exact fresh_u_ne_w))
  have dv_cache_0006 : x ≠ w :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show x ≠ w from (by exact fresh_x_ne_w))
  have dv_cache_0007 : Disjoint ((Class.cv z)).fv ((synCfv (synC1st) (.cv v))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (show Disjoint ((Class.cv z)).fv ((synCfv (synC1st) (.cv v))).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv];
          exact
            (show
              Disjoint (({ z } : Finset Var)) ((((Class.cv v)).fv) ∪ (((synC1st)).fv))
              from
              (Finset.disjoint_union_right.mpr
                ⟨(show Disjoint (({ z } : Finset Var)) (((Class.cv v)).fv) from
                    (by
                      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
                      exact
                        (show Disjoint (({ z } : Finset Var)) (({ v } : Finset Var)) from
                          (Finset.disjoint_singleton_left.mpr
                            (show z ∉ ({ v } : Finset Var) from
                              (by
                                simpa only [Finset.mem_singleton] using
                                  (show z ≠ v from (by exact Ne.symm dv_v_z)))))))),
                  (show Disjoint (({ z } : Finset Var)) (((synC1st)).fv) from
                    (by
                      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st];
                      exact
                        (show Disjoint (({ z } : Finset Var)) ((∅ : Finset Var)) from
                          (by simp))))⟩))))
  have dv_cache_0008 : z ∉ ((Class.cv w)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_z_ne_w, not_false_eq_true])
  have dv_cache_0009 :
    z ∉
      ((synCin (synCfv (synC2nd) (.cv v))
          (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
            (synCsn (.cv y))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
          Finset.mem_singleton, (Ne.symm dv_v_z), (Ne.symm dv_y_z),
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0010 :
    z ∉
      ((synWbr (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
            (.cv x)) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
            (.cv w)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutcode,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso, Finset.mem_union,
          Finset.mem_singleton, (Ne.symm dv_x_z), (Ne.symm dv_u_z), fresh_z_ne_w,
          (Ne.symm dv_v_z), dv_A_z, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0011 :
    w ∉
      ((synWrex z (synCin (synCfv (synC2nd) (.cv v))
            (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
              (synCsn (.cv y)))) (synWbr
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
            (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
              (.cv z))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cid,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutcode,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_w_ne_v, fresh_w_ne_y,
          fresh_w_ne_x, fresh_w_ne_u, fresh_w_ne_z, fresh_w_not_A,
          compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0012 :
    w ∉
      ((synWa (synWa
            (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
            (.classMem (.cv y) (synCfv (synC2nd) (.cv v)))) (synWa
            (synWbr (.cv u) (synChwniso A)
              (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                (.cv y))) (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutcode,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, Finset.mem_union,
          Finset.mem_singleton, fresh_w_ne_u, fresh_w_not_A, fresh_w_ne_v, fresh_w_ne_y,
          fresh_w_ne_x, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have p0000 :=
    @gSimpl
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (.classMem (.cv y) (synCfv (synC2nd) (.cv v))))
      (synWa (synWbr (.cv u) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv y)))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))
  have p0001 :=
    @gSimpld
      (synWa (synWa
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
          (.classMem (.cv y) (synCfv (synC2nd) (.cv v)))) (synWa
          (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv y)))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))))
      (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
      (.classMem (.cv y) (synCfv (synC2nd) (.cv v))) p0000
  have p0002 :=
    @gSimpld
      (synWa (synWa
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
          (.classMem (.cv y) (synCfv (synC2nd) (.cv v)))) (synWa
          (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv y)))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))))
      (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)) p0001
  have p0005 :=
    @gSimprd
      (synWa (synWa
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
          (.classMem (.cv y) (synCfv (synC2nd) (.cv v)))) (synWa
          (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv y)))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))))
      (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)) p0001
  have p0007 :=
    @gSimprd
      (synWa (synWa
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
          (.classMem (.cv y) (synCfv (synC2nd) (.cv v)))) (synWa
          (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv y)))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))))
      (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
      (.classMem (.cv y) (synCfv (synC2nd) (.cv v))) p0000
  have p0008 :=
    @gJca
      (synWa (synWa
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
          (.classMem (.cv y) (synCfv (synC2nd) (.cv v)))) (synWa
          (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv y)))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))))
      (.classMem (.cv v) (synChwcn A)) (.classMem (.cv y) (synCfv (synC2nd) (.cv v)))
      p0005 p0007
  have p0009 := @gHnwcutcodeambientndv y v A dv_cache_0001
  have p0010 :=
    @gSyl
      (synWa (synWa
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
          (.classMem (.cv y) (synCfv (synC2nd) (.cv v)))) (synWa
          (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv y)))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))))
      (synWa (.classMem (.cv v) (synChwcn A))
        (.classMem (.cv y) (synCfv (synC2nd) (.cv v))))
      (.classMem (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
          (.cv y)) (synChwcn A))
      p0008 p0009
  have p0011 :=
    @gJca
      (synWa (synWa
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
          (.classMem (.cv y) (synCfv (synC2nd) (.cv v)))) (synWa
          (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv y)))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))))
      (.classMem (.cv u) (synChwcn A))
      (.classMem (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
          (.cv y)) (synChwcn A))
      p0002 p0010
  have p0012 :=
    @gSimpr
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
        (.classMem (.cv y) (synCfv (synC2nd) (.cv v))))
      (synWa (synWbr (.cv u) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv y)))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))
  have p0013 :=
    @gSimpld
      (synWa (synWa
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
          (.classMem (.cv y) (synCfv (synC2nd) (.cv v)))) (synWa
          (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv y)))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))))
      (synWbr (.cv u) (synChwniso A)
        (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv y)))
      (.classMem (.cv x) (synCfv (synC2nd) (.cv u))) p0012
  have p0015 :=
    @gSimprd
      (synWa (synWa
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
          (.classMem (.cv y) (synCfv (synC2nd) (.cv v)))) (synWa
          (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv y)))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))))
      (synWbr (.cv u) (synChwniso A)
        (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv y)))
      (.classMem (.cv x) (synCfv (synC2nd) (.cv u))) p0012
  have p0016 :=
    @gJca
      (synWa (synWa
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
          (.classMem (.cv y) (synCfv (synC2nd) (.cv v)))) (synWa
          (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv y)))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))))
      (synWbr (.cv u) (synChwniso A)
        (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv y)))
      (.classMem (.cv x) (synCfv (synC2nd) (.cv u))) p0013 p0015
  have p0017 :=
    @gJca
      (synWa (synWa
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
          (.classMem (.cv y) (synCfv (synC2nd) (.cv v)))) (synWa
          (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv y)))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))))
      (synWa (.classMem (.cv u) (synChwcn A)) (.classMem
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv y))
          (synChwcn A)))
      (synWa (synWbr (.cv u) (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv y)))
        (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))
      p0011 p0016
  have p0018 :=
    @gHnwcutcodetransporttgtclndv x w u A
      (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv y))
      dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
  have p0019 :=
    @gSyl
      (synWa (synWa
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
          (.classMem (.cv y) (synCfv (synC2nd) (.cv v)))) (synWa
          (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv y)))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))))
      (synWa (synWa (.classMem (.cv u) (synChwcn A)) (.classMem
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv y))
            (synChwcn A))) (synWa (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv y)))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))))
      (synWrex w (synCfv (synC2nd)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv y)))
        (synWbr (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
            (.cv x)) (synChwniso A) (synChnwcutcode (synCfv (synC1st)
              (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                (.cv y))) (synCfv (synC2nd)
              (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                (.cv y))) (.cv w))))
      p0017 p0018
  have p0020 :=
    @gSimpr
      (synWa (synWa
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
          (.classMem (.cv y) (synCfv (synC2nd) (.cv v)))) (synWa
          (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv y)))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))))
      (synWa (.classMem (.cv w) (synCfv (synC2nd)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
              (.cv y)))) (synWbr
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
          (synChwniso A) (synChnwcutcode (synCfv (synC1st)
              (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                (.cv y))) (synCfv (synC2nd)
              (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                (.cv y))) (.cv w))))
  have p0021 :=
    @gSimpld
      (synWa (synWa (synWa
            (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
            (.classMem (.cv y) (synCfv (synC2nd) (.cv v)))) (synWa
            (synWbr (.cv u) (synChwniso A)
              (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                (.cv y))) (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))) (synWa
          (.classMem (.cv w) (synCfv (synC2nd)
              (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                (.cv y)))) (synWbr
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
            (synChwniso A) (synChnwcutcode (synCfv (synC1st)
                (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                  (.cv y))) (synCfv (synC2nd)
                (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                  (.cv y))) (.cv w)))))
      (.classMem (.cv w) (synCfv (synC2nd)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv y))))
      (synWbr (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (.cv x)) (synChwniso A) (synChnwcutcode (synCfv (synC1st)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv y)))
          (synCfv (synC2nd)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv y)))
          (.cv w)))
      p0020
  have p0022 :=
    @gSimpl
      (synWa (synWa
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
          (.classMem (.cv y) (synCfv (synC2nd) (.cv v)))) (synWa
          (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv y)))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))))
      (synWa (.classMem (.cv w) (synCfv (synC2nd)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
              (.cv y)))) (synWbr
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
          (synChwniso A) (synChnwcutcode (synCfv (synC1st)
              (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                (.cv y))) (synCfv (synC2nd)
              (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                (.cv y))) (.cv w))))
  have p0029 := @gHnwcutcodepartsndv y v A dv_cache_0001
  have p0030 :=
    @gSyl
      (synWa (synWa
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
          (.classMem (.cv y) (synCfv (synC2nd) (.cv v)))) (synWa
          (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv y)))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))))
      (synWa (.classMem (.cv v) (synChwcn A))
        (.classMem (.cv y) (synCfv (synC2nd) (.cv v))))
      (synWa (.classEq (synCfv (synC1st)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv y)))
          (synCin (synCfv (synC1st) (.cv v)) (synCxp (synCin (synCfv (synC2nd) (.cv v))
                (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
                  (synCsn (.cv y)))) (synCin (synCfv (synC2nd) (.cv v))
                (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
                  (synCsn (.cv y))))))) (.classEq (synCfv (synC2nd)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv y)))
          (synCin (synCfv (synC2nd) (.cv v))
            (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
              (synCsn (.cv y))))))
      p0008 p0029
  have p0031 :=
    @gSimprd
      (synWa (synWa
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
          (.classMem (.cv y) (synCfv (synC2nd) (.cv v)))) (synWa
          (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv y)))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))))
      (.classEq (synCfv (synC1st)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv y)))
        (synCin (synCfv (synC1st) (.cv v)) (synCxp (synCin (synCfv (synC2nd) (.cv v))
              (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
                (synCsn (.cv y)))) (synCin (synCfv (synC2nd) (.cv v))
              (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
                (synCsn (.cv y)))))))
      (.classEq (synCfv (synC2nd)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv y)))
        (synCin (synCfv (synC2nd) (.cv v))
          (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
            (synCsn (.cv y)))))
      p0030
  have p0032 :=
    @gSyl
      (synWa (synWa (synWa
            (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
            (.classMem (.cv y) (synCfv (synC2nd) (.cv v)))) (synWa
            (synWbr (.cv u) (synChwniso A)
              (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                (.cv y))) (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))) (synWa
          (.classMem (.cv w) (synCfv (synC2nd)
              (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                (.cv y)))) (synWbr
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
            (synChwniso A) (synChnwcutcode (synCfv (synC1st)
                (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                  (.cv y))) (synCfv (synC2nd)
                (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                  (.cv y))) (.cv w)))))
      (synWa (synWa
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
          (.classMem (.cv y) (synCfv (synC2nd) (.cv v)))) (synWa
          (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv y)))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))))
      (.classEq (synCfv (synC2nd)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv y)))
        (synCin (synCfv (synC2nd) (.cv v))
          (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
            (synCsn (.cv y)))))
      p0022 p0031
  have p0033 :=
    @gEleq2d
      (synWa (synWa (synWa
            (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
            (.classMem (.cv y) (synCfv (synC2nd) (.cv v)))) (synWa
            (synWbr (.cv u) (synChwniso A)
              (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                (.cv y))) (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))) (synWa
          (.classMem (.cv w) (synCfv (synC2nd)
              (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                (.cv y)))) (synWbr
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
            (synChwniso A) (synChnwcutcode (synCfv (synC1st)
                (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                  (.cv y))) (synCfv (synC2nd)
                (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                  (.cv y))) (.cv w)))))
      (synCfv (synC2nd)
        (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv y)))
      (synCin (synCfv (synC2nd) (.cv v))
        (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
          (synCsn (.cv y))))
      (.cv w) p0032
  have p0034 :=
    @gMpbid
      (synWa (synWa (synWa
            (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
            (.classMem (.cv y) (synCfv (synC2nd) (.cv v)))) (synWa
            (synWbr (.cv u) (synChwniso A)
              (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                (.cv y))) (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))) (synWa
          (.classMem (.cv w) (synCfv (synC2nd)
              (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                (.cv y)))) (synWbr
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
            (synChwniso A) (synChnwcutcode (synCfv (synC1st)
                (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                  (.cv y))) (synCfv (synC2nd)
                (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                  (.cv y))) (.cv w)))))
      (.classMem (.cv w) (synCfv (synC2nd)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv y))))
      (.classMem (.cv w) (synCin (synCfv (synC2nd) (.cv v))
          (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
            (synCsn (.cv y)))))
      p0021 p0033
  have p0036 :=
    @gSimprd
      (synWa (synWa (synWa
            (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
            (.classMem (.cv y) (synCfv (synC2nd) (.cv v)))) (synWa
            (synWbr (.cv u) (synChwniso A)
              (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                (.cv y))) (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))) (synWa
          (.classMem (.cv w) (synCfv (synC2nd)
              (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                (.cv y)))) (synWbr
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
            (synChwniso A) (synChnwcutcode (synCfv (synC1st)
                (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                  (.cv y))) (synCfv (synC2nd)
                (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                  (.cv y))) (.cv w)))))
      (.classMem (.cv w) (synCfv (synC2nd)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv y))))
      (synWbr (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (.cv x)) (synChwniso A) (synChnwcutcode (synCfv (synC1st)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv y)))
          (synCfv (synC2nd)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv y)))
          (.cv w)))
      p0020
  have p0046 :=
    @gSimpld
      (synWa (synWa
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
          (.classMem (.cv y) (synCfv (synC2nd) (.cv v)))) (synWa
          (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv y)))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))))
      (.classEq (synCfv (synC1st)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv y)))
        (synCin (synCfv (synC1st) (.cv v)) (synCxp (synCin (synCfv (synC2nd) (.cv v))
              (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
                (synCsn (.cv y)))) (synCin (synCfv (synC2nd) (.cv v))
              (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
                (synCsn (.cv y)))))))
      (.classEq (synCfv (synC2nd)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv y)))
        (synCin (synCfv (synC2nd) (.cv v))
          (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
            (synCsn (.cv y)))))
      p0030
  have p0047 :=
    @gSyl
      (synWa (synWa (synWa
            (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
            (.classMem (.cv y) (synCfv (synC2nd) (.cv v)))) (synWa
            (synWbr (.cv u) (synChwniso A)
              (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                (.cv y))) (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))) (synWa
          (.classMem (.cv w) (synCfv (synC2nd)
              (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                (.cv y)))) (synWbr
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
            (synChwniso A) (synChnwcutcode (synCfv (synC1st)
                (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                  (.cv y))) (synCfv (synC2nd)
                (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                  (.cv y))) (.cv w)))))
      (synWa (synWa
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
          (.classMem (.cv y) (synCfv (synC2nd) (.cv v)))) (synWa
          (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv y)))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))))
      (.classEq (synCfv (synC1st)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv y)))
        (synCin (synCfv (synC1st) (.cv v)) (synCxp (synCin (synCfv (synC2nd) (.cv v))
              (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
                (synCsn (.cv y)))) (synCin (synCfv (synC2nd) (.cv v))
              (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
                (synCsn (.cv y)))))))
      p0022 p0046
  have p0059 :=
    @gJca
      (synWa (synWa (synWa
            (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
            (.classMem (.cv y) (synCfv (synC2nd) (.cv v)))) (synWa
            (synWbr (.cv u) (synChwniso A)
              (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                (.cv y))) (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))) (synWa
          (.classMem (.cv w) (synCfv (synC2nd)
              (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                (.cv y)))) (synWbr
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
            (synChwniso A) (synChnwcutcode (synCfv (synC1st)
                (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                  (.cv y))) (synCfv (synC2nd)
                (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                  (.cv y))) (.cv w)))))
      (.classEq (synCfv (synC1st)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv y)))
        (synCin (synCfv (synC1st) (.cv v)) (synCxp (synCin (synCfv (synC2nd) (.cv v))
              (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
                (synCsn (.cv y)))) (synCin (synCfv (synC2nd) (.cv v))
              (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
                (synCsn (.cv y)))))))
      (.classEq (synCfv (synC2nd)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv y)))
        (synCin (synCfv (synC2nd) (.cv v))
          (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
            (synCsn (.cv y)))))
      p0047 p0032
  have p0060 :=
    @gHnwcutcodeeq12ndv w
      (synCfv (synC2nd)
        (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv y)))
      (synCfv (synC1st)
        (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv y)))
      (synCin (synCfv (synC1st) (.cv v)) (synCxp (synCin (synCfv (synC2nd) (.cv v))
            (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
              (synCsn (.cv y)))) (synCin (synCfv (synC2nd) (.cv v))
            (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
              (synCsn (.cv y))))))
      (synCin (synCfv (synC2nd) (.cv v))
        (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
          (synCsn (.cv y))))
  have p0061 :=
    @gSyl
      (synWa (synWa (synWa
            (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
            (.classMem (.cv y) (synCfv (synC2nd) (.cv v)))) (synWa
            (synWbr (.cv u) (synChwniso A)
              (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                (.cv y))) (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))) (synWa
          (.classMem (.cv w) (synCfv (synC2nd)
              (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                (.cv y)))) (synWbr
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
            (synChwniso A) (synChnwcutcode (synCfv (synC1st)
                (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                  (.cv y))) (synCfv (synC2nd)
                (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                  (.cv y))) (.cv w)))))
      (synWa (.classEq (synCfv (synC1st)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv y)))
          (synCin (synCfv (synC1st) (.cv v)) (synCxp (synCin (synCfv (synC2nd) (.cv v))
                (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
                  (synCsn (.cv y)))) (synCin (synCfv (synC2nd) (.cv v))
                (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
                  (synCsn (.cv y))))))) (.classEq (synCfv (synC2nd)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv y)))
          (synCin (synCfv (synC2nd) (.cv v))
            (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
              (synCsn (.cv y))))))
      (.classEq (synChnwcutcode (synCfv (synC1st)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv y)))
          (synCfv (synC2nd)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv y)))
          (.cv w)) (synChnwcutcode (synCin (synCfv (synC1st) (.cv v)) (synCxp
              (synCin (synCfv (synC2nd) (.cv v))
                (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
                  (synCsn (.cv y)))) (synCin (synCfv (synC2nd) (.cv v))
                (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
                  (synCsn (.cv y)))))) (synCin (synCfv (synC2nd) (.cv v))
            (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
              (synCsn (.cv y)))) (.cv w)))
      p0059 p0060
  have p0066 := @gHwcnweclndv A (.cv v)
  have p0067 :=
    @gSyl
      (synWa (synWa
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
          (.classMem (.cv y) (synCfv (synC2nd) (.cv v)))) (synWa
          (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv y)))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))))
      (.classMem (.cv v) (synChwcn A))
      (synWbr (synCfv (synC1st) (.cv v)) (synCwe) (synCfv (synC2nd) (.cv v))) p0005
      p0066
  have p0068 :=
    @gSyl
      (synWa (synWa (synWa
            (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
            (.classMem (.cv y) (synCfv (synC2nd) (.cv v)))) (synWa
            (synWbr (.cv u) (synChwniso A)
              (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                (.cv y))) (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))) (synWa
          (.classMem (.cv w) (synCfv (synC2nd)
              (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                (.cv y)))) (synWbr
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
            (synChwniso A) (synChnwcutcode (synCfv (synC1st)
                (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                  (.cv y))) (synCfv (synC2nd)
                (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                  (.cv y))) (.cv w)))))
      (synWa (synWa
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
          (.classMem (.cv y) (synCfv (synC2nd) (.cv v)))) (synWa
          (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv y)))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))))
      (synWbr (synCfv (synC1st) (.cv v)) (synCwe) (synCfv (synC2nd) (.cv v))) p0022
      p0067
  have p0072 :=
    @gSyl
      (synWa (synWa (synWa
            (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
            (.classMem (.cv y) (synCfv (synC2nd) (.cv v)))) (synWa
            (synWbr (.cv u) (synChwniso A)
              (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                (.cv y))) (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))) (synWa
          (.classMem (.cv w) (synCfv (synC2nd)
              (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                (.cv y)))) (synWbr
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
            (synChwniso A) (synChnwcutcode (synCfv (synC1st)
                (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                  (.cv y))) (synCfv (synC2nd)
                (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                  (.cv y))) (.cv w)))))
      (synWa (synWa
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
          (.classMem (.cv y) (synCfv (synC2nd) (.cv v)))) (synWa
          (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv y)))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))))
      (.classMem (.cv y) (synCfv (synC2nd) (.cv v))) p0022 p0007
  have p0073 :=
    @gJca
      (synWa (synWa (synWa
            (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
            (.classMem (.cv y) (synCfv (synC2nd) (.cv v)))) (synWa
            (synWbr (.cv u) (synChwniso A)
              (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                (.cv y))) (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))) (synWa
          (.classMem (.cv w) (synCfv (synC2nd)
              (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                (.cv y)))) (synWbr
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
            (synChwniso A) (synChnwcutcode (synCfv (synC1st)
                (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                  (.cv y))) (synCfv (synC2nd)
                (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                  (.cv y))) (.cv w)))))
      (synWbr (synCfv (synC1st) (.cv v)) (synCwe) (synCfv (synC2nd) (.cv v)))
      (.classMem (.cv y) (synCfv (synC2nd) (.cv v))) p0068 p0072
  have p0089 :=
    @gJca
      (synWa (synWa (synWa
            (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
            (.classMem (.cv y) (synCfv (synC2nd) (.cv v)))) (synWa
            (synWbr (.cv u) (synChwniso A)
              (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                (.cv y))) (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))) (synWa
          (.classMem (.cv w) (synCfv (synC2nd)
              (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                (.cv y)))) (synWbr
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
            (synChwniso A) (synChnwcutcode (synCfv (synC1st)
                (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                  (.cv y))) (synCfv (synC2nd)
                (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                  (.cv y))) (.cv w)))))
      (synWa (synWbr (synCfv (synC1st) (.cv v)) (synCwe) (synCfv (synC2nd) (.cv v)))
        (.classMem (.cv y) (synCfv (synC2nd) (.cv v))))
      (.classMem (.cv w) (synCin (synCfv (synC2nd) (.cv v))
          (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
            (synCsn (.cv y)))))
      p0073 p0034
  have p0090 :=
    @gHnwcutcodenestndv w y (synCfv (synC2nd) (.cv v)) (synCfv (synC1st) (.cv v))
  have p0091 :=
    @gSyl
      (synWa (synWa (synWa
            (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
            (.classMem (.cv y) (synCfv (synC2nd) (.cv v)))) (synWa
            (synWbr (.cv u) (synChwniso A)
              (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                (.cv y))) (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))) (synWa
          (.classMem (.cv w) (synCfv (synC2nd)
              (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                (.cv y)))) (synWbr
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
            (synChwniso A) (synChnwcutcode (synCfv (synC1st)
                (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                  (.cv y))) (synCfv (synC2nd)
                (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                  (.cv y))) (.cv w)))))
      (synWa (synWa
          (synWbr (synCfv (synC1st) (.cv v)) (synCwe) (synCfv (synC2nd) (.cv v)))
          (.classMem (.cv y) (synCfv (synC2nd) (.cv v)))) (.classMem (.cv w)
          (synCin (synCfv (synC2nd) (.cv v))
            (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
              (synCsn (.cv y))))))
      (.classEq (synChnwcutcode (synCin (synCfv (synC1st) (.cv v)) (synCxp
              (synCin (synCfv (synC2nd) (.cv v))
                (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
                  (synCsn (.cv y)))) (synCin (synCfv (synC2nd) (.cv v))
                (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
                  (synCsn (.cv y)))))) (synCin (synCfv (synC2nd) (.cv v))
            (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
              (synCsn (.cv y)))) (.cv w))
        (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv w)))
      p0089 p0090
  have p0092 :=
    @gEqtrd
      (synWa (synWa (synWa
            (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
            (.classMem (.cv y) (synCfv (synC2nd) (.cv v)))) (synWa
            (synWbr (.cv u) (synChwniso A)
              (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                (.cv y))) (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))) (synWa
          (.classMem (.cv w) (synCfv (synC2nd)
              (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                (.cv y)))) (synWbr
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
            (synChwniso A) (synChnwcutcode (synCfv (synC1st)
                (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                  (.cv y))) (synCfv (synC2nd)
                (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                  (.cv y))) (.cv w)))))
      (synChnwcutcode (synCfv (synC1st)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv y)))
        (synCfv (synC2nd)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv y)))
        (.cv w))
      (synChnwcutcode (synCin (synCfv (synC1st) (.cv v)) (synCxp
            (synCin (synCfv (synC2nd) (.cv v))
              (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
                (synCsn (.cv y)))) (synCin (synCfv (synC2nd) (.cv v))
              (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
                (synCsn (.cv y)))))) (synCin (synCfv (synC2nd) (.cv v))
          (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
            (synCsn (.cv y)))) (.cv w))
      (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv w))
      p0061 p0091
  have p0093 :=
    @gBreq2d
      (synWa (synWa (synWa
            (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
            (.classMem (.cv y) (synCfv (synC2nd) (.cv v)))) (synWa
            (synWbr (.cv u) (synChwniso A)
              (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                (.cv y))) (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))) (synWa
          (.classMem (.cv w) (synCfv (synC2nd)
              (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                (.cv y)))) (synWbr
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
            (synChwniso A) (synChnwcutcode (synCfv (synC1st)
                (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                  (.cv y))) (synCfv (synC2nd)
                (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                  (.cv y))) (.cv w)))))
      (synChnwcutcode (synCfv (synC1st)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv y)))
        (synCfv (synC2nd)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv y)))
        (.cv w))
      (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv w))
      (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
      (synChwniso A) p0092
  have p0094 :=
    @gMpbid
      (synWa (synWa (synWa
            (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
            (.classMem (.cv y) (synCfv (synC2nd) (.cv v)))) (synWa
            (synWbr (.cv u) (synChwniso A)
              (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                (.cv y))) (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))) (synWa
          (.classMem (.cv w) (synCfv (synC2nd)
              (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                (.cv y)))) (synWbr
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
            (synChwniso A) (synChnwcutcode (synCfv (synC1st)
                (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                  (.cv y))) (synCfv (synC2nd)
                (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                  (.cv y))) (.cv w)))))
      (synWbr (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (.cv x)) (synChwniso A) (synChnwcutcode (synCfv (synC1st)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv y)))
          (synCfv (synC2nd)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv y)))
          (.cv w)))
      (synWbr (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (.cv x)) (synChwniso A)
        (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv w)))
      p0036 p0093
  have p0095 :=
    @gJca
      (synWa (synWa (synWa
            (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
            (.classMem (.cv y) (synCfv (synC2nd) (.cv v)))) (synWa
            (synWbr (.cv u) (synChwniso A)
              (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                (.cv y))) (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))) (synWa
          (.classMem (.cv w) (synCfv (synC2nd)
              (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                (.cv y)))) (synWbr
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
            (synChwniso A) (synChnwcutcode (synCfv (synC1st)
                (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                  (.cv y))) (synCfv (synC2nd)
                (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                  (.cv y))) (.cv w)))))
      (.classMem (.cv w) (synCin (synCfv (synC2nd) (.cv v))
          (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
            (synCsn (.cv y)))))
      (synWbr (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (.cv x)) (synChwniso A)
        (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv w)))
      p0034 p0094
  have p0096 :=
    @gHnwcutcodeeq3 (.cv z) (.cv w) (synCfv (synC2nd) (.cv v))
      (synCfv (synC1st) (.cv v)) dv_cache_0007
  have p0097 :=
    @gBreq2d (.classEq (.cv z) (.cv w))
      (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv z))
      (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv w))
      (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
      (synChwniso A) p0096
  have p0098 :=
    @gRspcev
      (synWbr (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (.cv x)) (synChwniso A)
        (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv z)))
      (synWbr (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (.cv x)) (synChwniso A)
        (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv w)))
      z (.cv w)
      (synCin (synCfv (synC2nd) (.cv v))
        (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
          (synCsn (.cv y))))
      dv_cache_0008 dv_cache_0009 dv_cache_0010 p0097
  have p0099 :=
    @gSyl
      (synWa (synWa (synWa
            (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
            (.classMem (.cv y) (synCfv (synC2nd) (.cv v)))) (synWa
            (synWbr (.cv u) (synChwniso A)
              (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                (.cv y))) (.classMem (.cv x) (synCfv (synC2nd) (.cv u))))) (synWa
          (.classMem (.cv w) (synCfv (synC2nd)
              (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                (.cv y)))) (synWbr
            (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
            (synChwniso A) (synChnwcutcode (synCfv (synC1st)
                (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                  (.cv y))) (synCfv (synC2nd)
                (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v))
                  (.cv y))) (.cv w)))))
      (synWa (.classMem (.cv w) (synCin (synCfv (synC2nd) (.cv v))
            (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
              (synCsn (.cv y))))) (synWbr
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
          (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv w))))
      (synWrex z (synCin (synCfv (synC2nd) (.cv v))
          (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
            (synCsn (.cv y)))) (synWbr
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
          (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv z))))
      p0095 p0098
  have p0100 :=
    @gRexlimddv
      (synWa (synWa
          (synWa (.classMem (.cv u) (synChwcn A)) (.classMem (.cv v) (synChwcn A)))
          (.classMem (.cv y) (synCfv (synC2nd) (.cv v)))) (synWa
          (synWbr (.cv u) (synChwniso A)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv y)))
          (.classMem (.cv x) (synCfv (synC2nd) (.cv u)))))
      (synWbr (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
          (.cv x)) (synChwniso A) (synChnwcutcode (synCfv (synC1st)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv y)))
          (synCfv (synC2nd)
            (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv y)))
          (.cv w)))
      (synWrex z (synCin (synCfv (synC2nd) (.cv v))
          (synCima (synCcnv (synCdif (synCfv (synC1st) (.cv v)) (synCid)))
            (synCsn (.cv y)))) (synWbr
          (synChnwcutcode (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)) (.cv x))
          (synChwniso A)
          (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv z))))
      w
      (synCfv (synC2nd)
        (synChnwcutcode (synCfv (synC1st) (.cv v)) (synCfv (synC2nd) (.cv v)) (.cv y)))
      dv_cache_0011 dv_cache_0012 p0019 p0099
  exact p0100


end NFChoice.DirectNominalPrf.WPPReplay

end
