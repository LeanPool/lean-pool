/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NominalWPPReplayChunk017Compact001Block009

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NominalWPPReplayChunk017Compact001Part043`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_hncodepredstrictdescentndv (x : Var) (y : Var) (z : Var) (v : Var)
    (u : Var) (A : Class) (dv_A_u : u ∉ A.fv) (dv_A_v : v ∉ A.fv) (dv_A_y : y ∉ A.fv)
    (dv_A_z : z ∉ A.fv) (dv_u_y : u ≠ y) (dv_u_z : u ≠ z) (dv_v_z : v ≠ z)
    (dv_x_z : x ≠ z) (dv_y_z : y ≠ z) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
              (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
              (.classMem (.cv y) (syn_chwcn A)))) (syn_wa
            (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
              (syn_wbr (.cv u) (syn_chwniso A)
                (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                  (.cv x)))) (syn_wbr (.cv y)
              (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv u))))
        (syn_wrex z (syn_cin (syn_cfv (syn_c2nd) (.cv v))
            (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
              (syn_csn (.cv x)))) (syn_wbr (.cv y) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv z))))) :=
  by
  let proofSupport : Finset Var :=
    ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ ({ z } : Finset Var) ∪
          ({ v } : Finset Var) ∪
        ({ u } : Finset Var) ∪
      A.fv
  let t : Var := freshVar proofSupport 0
  have fresh_t : t ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_t_ne_x : t ≠ x := by
    intro h
    exact
      fresh_t
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _
                (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))))
  have fresh_t_ne_y : t ≠ y := by
    intro h
    exact
      fresh_t
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _
                (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))))
  have fresh_y_ne_t : y ≠ t := Ne.symm fresh_t_ne_y
  have fresh_t_ne_z : t ≠ z := by
    intro h
    exact
      fresh_t
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))
  have fresh_z_ne_t : z ≠ t := Ne.symm fresh_t_ne_z
  have fresh_t_ne_v : t ≠ v := by
    intro h
    exact
      fresh_t
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_t_ne_u : t ≠ u := by
    intro h
    exact
      fresh_t
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_u_ne_t : u ≠ t := Ne.symm fresh_t_ne_u
  have fresh_t_not_A : t ∉ A.fv := by
    intro h
    exact fresh_t (Finset.mem_union_right _ (h))
  have dv_cache_0001 : y ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_y, not_false_eq_true])
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
  have dv_cache_0003 : t ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_t_not_A, not_false_eq_true])
  have dv_cache_0004 : y ≠ u :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show y ≠ u from (by exact Ne.symm dv_u_y))
  have dv_cache_0005 : y ≠ t :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show y ≠ t from (by exact fresh_y_ne_t))
  have dv_cache_0006 : u ≠ t :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show u ≠ t from (by exact fresh_u_ne_t))
  have dv_cache_0007 : v ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_v, not_false_eq_true])
  have dv_cache_0008 : z ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_z, not_false_eq_true])
  have dv_cache_0009 : u ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (show u ≠ z from (by exact dv_u_z))
  have dv_cache_0010 : v ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (show v ≠ z from (by exact dv_v_z))
  have dv_cache_0011 : t ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (show t ≠ z from (by exact fresh_t_ne_z))
  have dv_cache_0012 : x ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (show x ≠ z from (by exact dv_x_z))
  have dv_cache_0013 :
    z ∉
      ((syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
                (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
                (.classMem (.cv y) (syn_chwcn A)))) (syn_wa
              (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
                (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v))
                    (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) (syn_wbr (.cv y)
                (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv u))))
          (syn_wa (.classMem (.cv t) (syn_cfv (syn_c2nd) (.cv u)))
            (syn_wbr (.cv y) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                (.cv t)))))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutcode,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodecmpset,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, Finset.mem_union,
          Finset.mem_singleton, dv_A_z, (Ne.symm dv_u_z), (Ne.symm dv_v_z),
          (Ne.symm dv_y_z), (Ne.symm dv_x_z), fresh_z_ne_t, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0014 :
    t ∉
      ((syn_wrex z (syn_cin (syn_cfv (syn_c2nd) (.cv v))
            (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
              (syn_csn (.cv x)))) (syn_wbr (.cv y) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv z))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
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
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutcode,
          Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, fresh_t_ne_v,
          fresh_t_ne_x, fresh_t_ne_y, fresh_t_ne_z, fresh_t_not_A,
          compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0015 :
    t ∉
      ((syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
              (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
              (.classMem (.cv y) (syn_chwcn A)))) (syn_wa
            (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
              (syn_wbr (.cv u) (syn_chwniso A)
                (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                  (.cv x)))) (syn_wbr (.cv y)
              (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A)))
              (.cv u))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutcode,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodecmpset,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, Finset.mem_union,
          Finset.mem_singleton, fresh_t_not_A, fresh_t_ne_u, fresh_t_ne_v, fresh_t_ne_y,
          fresh_t_ne_x, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have p0000 :=
    @g_simpr
      (syn_wa (.classMem A (syn_cvv)) (syn_wa
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
          (.classMem (.cv y) (syn_chwcn A))))
      (syn_wa (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
          (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv x))))
        (syn_wbr (.cv y) (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A)))
          (.cv u)))
  have p0001 :=
    @g_simprd
      (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
            (.classMem (.cv y) (syn_chwcn A)))) (syn_wa
          (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
            (syn_wbr (.cv u) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv x)))) (syn_wbr (.cv y)
            (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv u))))
      (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))
      (syn_wbr (.cv y) (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A)))
        (.cv u))
      p0000
  have p0002 :=
    @g_simpl
      (syn_wa (.classMem A (syn_cvv)) (syn_wa
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
          (.classMem (.cv y) (syn_chwcn A))))
      (syn_wa (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
          (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv x))))
        (syn_wbr (.cv y) (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A)))
          (.cv u)))
  have p0003 :=
    @g_simpld
      (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
            (.classMem (.cv y) (syn_chwcn A)))) (syn_wa
          (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
            (syn_wbr (.cv u) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv x)))) (syn_wbr (.cv y)
            (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv u))))
      (.classMem A (syn_cvv))
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (.classMem (.cv y) (syn_chwcn A)))
      p0002
  have p0005 :=
    @g_simprd
      (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
            (.classMem (.cv y) (syn_chwcn A)))) (syn_wa
          (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
            (syn_wbr (.cv u) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv x)))) (syn_wbr (.cv y)
            (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv u))))
      (.classMem A (syn_cvv))
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (.classMem (.cv y) (syn_chwcn A)))
      p0002
  have p0006 :=
    @g_simprd
      (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
            (.classMem (.cv y) (syn_chwcn A)))) (syn_wa
          (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
            (syn_wbr (.cv u) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv x)))) (syn_wbr (.cv y)
            (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv u))))
      (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
      (.classMem (.cv y) (syn_chwcn A)) p0005
  have p0009 :=
    @g_simpld
      (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
            (.classMem (.cv y) (syn_chwcn A)))) (syn_wa
          (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
            (syn_wbr (.cv u) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv x)))) (syn_wbr (.cv y)
            (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv u))))
      (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
      (.classMem (.cv y) (syn_chwcn A)) p0005
  have p0010 :=
    @g_simpld
      (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
            (.classMem (.cv y) (syn_chwcn A)))) (syn_wa
          (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
            (syn_wbr (.cv u) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv x)))) (syn_wbr (.cv y)
            (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv u))))
      (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)) p0009
  have p0011 :=
    @g_jca
      (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
            (.classMem (.cv y) (syn_chwcn A)))) (syn_wa
          (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
            (syn_wbr (.cv u) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv x)))) (syn_wbr (.cv y)
            (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv u))))
      (.classMem (.cv y) (syn_chwcn A)) (.classMem (.cv u) (syn_chwcn A)) p0006 p0010
  have p0012 :=
    @g_jca
      (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
            (.classMem (.cv y) (syn_chwcn A)))) (syn_wa
          (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
            (syn_wbr (.cv u) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv x)))) (syn_wbr (.cv y)
            (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv u))))
      (.classMem A (syn_cvv))
      (syn_wa (.classMem (.cv y) (syn_chwcn A)) (.classMem (.cv u) (syn_chwcn A))) p0003
      p0011
  have p0013 :=
    @g_hncodecmpstrictbrndv t u y A dv_cache_0001 dv_cache_0002 dv_cache_0003
      dv_cache_0004 dv_cache_0005 dv_cache_0006
  have p0014 :=
    @g_syl
      (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
            (.classMem (.cv y) (syn_chwcn A)))) (syn_wa
          (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
            (syn_wbr (.cv u) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv x)))) (syn_wbr (.cv y)
            (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv u))))
      (syn_wa (.classMem A (syn_cvv))
        (syn_wa (.classMem (.cv y) (syn_chwcn A)) (.classMem (.cv u) (syn_chwcn A))))
      (syn_wb (syn_wbr (.cv y) (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A)))
          (.cv u)) (syn_wrex t (syn_cfv (syn_c2nd) (.cv u)) (syn_wbr (.cv y) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
              (.cv t)))))
      p0012 p0013
  have p0015 :=
    @g_mpbid
      (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
            (.classMem (.cv y) (syn_chwcn A)))) (syn_wa
          (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
            (syn_wbr (.cv u) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv x)))) (syn_wbr (.cv y)
            (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv u))))
      (syn_wbr (.cv y) (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A)))
        (.cv u))
      (syn_wrex t (syn_cfv (syn_c2nd) (.cv u)) (syn_wbr (.cv y) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv t))))
      p0001 p0014
  have p0016 :=
    @g_simpl
      (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
            (.classMem (.cv y) (syn_chwcn A)))) (syn_wa
          (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
            (syn_wbr (.cv u) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv x)))) (syn_wbr (.cv y)
            (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv u))))
      (syn_wa (.classMem (.cv t) (syn_cfv (syn_c2nd) (.cv u))) (syn_wbr (.cv y) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv t))))
  have p0021 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
              (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
              (.classMem (.cv y) (syn_chwcn A)))) (syn_wa
            (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
              (syn_wbr (.cv u) (syn_chwniso A)
                (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                  (.cv x)))) (syn_wbr (.cv y)
              (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv u))))
        (syn_wa (.classMem (.cv t) (syn_cfv (syn_c2nd) (.cv u)))
          (syn_wbr (.cv y) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
              (.cv t)))))
      (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
            (.classMem (.cv y) (syn_chwcn A)))) (syn_wa
          (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
            (syn_wbr (.cv u) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv x)))) (syn_wbr (.cv y)
            (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv u))))
      (.classMem (.cv u) (syn_chwcn A)) p0016 p0010
  have p0026 :=
    @g_simprd
      (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
            (.classMem (.cv y) (syn_chwcn A)))) (syn_wa
          (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
            (syn_wbr (.cv u) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv x)))) (syn_wbr (.cv y)
            (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv u))))
      (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)) p0009
  have p0027 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
              (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
              (.classMem (.cv y) (syn_chwcn A)))) (syn_wa
            (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
              (syn_wbr (.cv u) (syn_chwniso A)
                (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                  (.cv x)))) (syn_wbr (.cv y)
              (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv u))))
        (syn_wa (.classMem (.cv t) (syn_cfv (syn_c2nd) (.cv u)))
          (syn_wbr (.cv y) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
              (.cv t)))))
      (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
            (.classMem (.cv y) (syn_chwcn A)))) (syn_wa
          (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
            (syn_wbr (.cv u) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv x)))) (syn_wbr (.cv y)
            (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv u))))
      (.classMem (.cv v) (syn_chwcn A)) p0016 p0026
  have p0028 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
              (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
              (.classMem (.cv y) (syn_chwcn A)))) (syn_wa
            (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
              (syn_wbr (.cv u) (syn_chwniso A)
                (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                  (.cv x)))) (syn_wbr (.cv y)
              (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv u))))
        (syn_wa (.classMem (.cv t) (syn_cfv (syn_c2nd) (.cv u)))
          (syn_wbr (.cv y) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
              (.cv t)))))
      (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)) p0021 p0027
  have p0031 :=
    @g_simpld
      (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
            (.classMem (.cv y) (syn_chwcn A)))) (syn_wa
          (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
            (syn_wbr (.cv u) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv x)))) (syn_wbr (.cv y)
            (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv u))))
      (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))
      (syn_wbr (.cv y) (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A)))
        (.cv u))
      p0000
  have p0032 :=
    @g_simpld
      (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
            (.classMem (.cv y) (syn_chwcn A)))) (syn_wa
          (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
            (syn_wbr (.cv u) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv x)))) (syn_wbr (.cv y)
            (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv u))))
      (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
      (syn_wbr (.cv u) (syn_chwniso A)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))
      p0031
  have p0033 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
              (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
              (.classMem (.cv y) (syn_chwcn A)))) (syn_wa
            (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
              (syn_wbr (.cv u) (syn_chwniso A)
                (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                  (.cv x)))) (syn_wbr (.cv y)
              (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv u))))
        (syn_wa (.classMem (.cv t) (syn_cfv (syn_c2nd) (.cv u)))
          (syn_wbr (.cv y) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
              (.cv t)))))
      (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
            (.classMem (.cv y) (syn_chwcn A)))) (syn_wa
          (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
            (syn_wbr (.cv u) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv x)))) (syn_wbr (.cv y)
            (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv u))))
      (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) p0016 p0032
  have p0034 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
              (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
              (.classMem (.cv y) (syn_chwcn A)))) (syn_wa
            (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
              (syn_wbr (.cv u) (syn_chwniso A)
                (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                  (.cv x)))) (syn_wbr (.cv y)
              (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv u))))
        (syn_wa (.classMem (.cv t) (syn_cfv (syn_c2nd) (.cv u)))
          (syn_wbr (.cv y) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
              (.cv t)))))
      (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
      (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) p0028 p0033
  have p0038 :=
    @g_simprd
      (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
            (.classMem (.cv y) (syn_chwcn A)))) (syn_wa
          (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
            (syn_wbr (.cv u) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv x)))) (syn_wbr (.cv y)
            (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv u))))
      (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
      (syn_wbr (.cv u) (syn_chwniso A)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))
      p0031
  have p0039 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
              (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
              (.classMem (.cv y) (syn_chwcn A)))) (syn_wa
            (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
              (syn_wbr (.cv u) (syn_chwniso A)
                (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                  (.cv x)))) (syn_wbr (.cv y)
              (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv u))))
        (syn_wa (.classMem (.cv t) (syn_cfv (syn_c2nd) (.cv u)))
          (syn_wbr (.cv y) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
              (.cv t)))))
      (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
            (.classMem (.cv y) (syn_chwcn A)))) (syn_wa
          (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
            (syn_wbr (.cv u) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv x)))) (syn_wbr (.cv y)
            (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv u))))
      (syn_wbr (.cv u) (syn_chwniso A)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))
      p0016 p0038
  have p0040 :=
    @g_simpr
      (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
            (.classMem (.cv y) (syn_chwcn A)))) (syn_wa
          (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
            (syn_wbr (.cv u) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv x)))) (syn_wbr (.cv y)
            (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv u))))
      (syn_wa (.classMem (.cv t) (syn_cfv (syn_c2nd) (.cv u))) (syn_wbr (.cv y) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv t))))
  have p0041 :=
    @g_simpld
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
              (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
              (.classMem (.cv y) (syn_chwcn A)))) (syn_wa
            (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
              (syn_wbr (.cv u) (syn_chwniso A)
                (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                  (.cv x)))) (syn_wbr (.cv y)
              (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv u))))
        (syn_wa (.classMem (.cv t) (syn_cfv (syn_c2nd) (.cv u)))
          (syn_wbr (.cv y) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
              (.cv t)))))
      (.classMem (.cv t) (syn_cfv (syn_c2nd) (.cv u)))
      (syn_wbr (.cv y) (syn_chwniso A)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv t)))
      p0040
  have p0042 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
              (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
              (.classMem (.cv y) (syn_chwcn A)))) (syn_wa
            (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
              (syn_wbr (.cv u) (syn_chwniso A)
                (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                  (.cv x)))) (syn_wbr (.cv y)
              (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv u))))
        (syn_wa (.classMem (.cv t) (syn_cfv (syn_c2nd) (.cv u)))
          (syn_wbr (.cv y) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
              (.cv t)))))
      (syn_wbr (.cv u) (syn_chwniso A)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))
      (.classMem (.cv t) (syn_cfv (syn_c2nd) (.cv u))) p0039 p0041
  have p0043 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
              (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
              (.classMem (.cv y) (syn_chwcn A)))) (syn_wa
            (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
              (syn_wbr (.cv u) (syn_chwniso A)
                (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                  (.cv x)))) (syn_wbr (.cv y)
              (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv u))))
        (syn_wa (.classMem (.cv t) (syn_cfv (syn_c2nd) (.cv u)))
          (syn_wbr (.cv y) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
              (.cv t)))))
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))))
      (syn_wa (syn_wbr (.cv u) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))
        (.classMem (.cv t) (syn_cfv (syn_c2nd) (.cv u))))
      p0034 p0042
  have p0044 :=
    @g_hnwcutcodetransportintocutsegndv t x z v u A dv_cache_0002 dv_cache_0007
      dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
  have p0045 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
              (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
              (.classMem (.cv y) (syn_chwcn A)))) (syn_wa
            (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
              (syn_wbr (.cv u) (syn_chwniso A)
                (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                  (.cv x)))) (syn_wbr (.cv y)
              (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv u))))
        (syn_wa (.classMem (.cv t) (syn_cfv (syn_c2nd) (.cv u)))
          (syn_wbr (.cv y) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
              (.cv t)))))
      (syn_wa (syn_wa
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))) (syn_wa
          (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))
          (.classMem (.cv t) (syn_cfv (syn_c2nd) (.cv u)))))
      (syn_wrex z (syn_cin (syn_cfv (syn_c2nd) (.cv v))
          (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
            (syn_csn (.cv x)))) (syn_wbr
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv t))
          (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv z))))
      p0043 p0044
  have p0046 :=
    @g_simpl
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
              (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
              (.classMem (.cv y) (syn_chwcn A)))) (syn_wa
            (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
              (syn_wbr (.cv u) (syn_chwniso A)
                (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                  (.cv x)))) (syn_wbr (.cv y)
              (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv u))))
        (syn_wa (.classMem (.cv t) (syn_cfv (syn_c2nd) (.cv u)))
          (syn_wbr (.cv y) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
              (.cv t)))))
      (syn_wa (.classMem (.cv z) (syn_cin (syn_cfv (syn_c2nd) (.cv v))
            (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
              (syn_csn (.cv x))))) (syn_wbr
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv t))
          (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv z))))
  have p0050 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
              (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
              (.classMem (.cv y) (syn_chwcn A)))) (syn_wa
            (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
              (syn_wbr (.cv u) (syn_chwniso A)
                (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                  (.cv x)))) (syn_wbr (.cv y)
              (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv u))))
        (syn_wa (.classMem (.cv t) (syn_cfv (syn_c2nd) (.cv u)))
          (syn_wbr (.cv y) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
              (.cv t)))))
      (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
            (.classMem (.cv y) (syn_chwcn A)))) (syn_wa
          (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
            (syn_wbr (.cv u) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv x)))) (syn_wbr (.cv y)
            (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv u))))
      (.classMem A (syn_cvv)) p0016 p0003
  have p0051 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
                (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
                (.classMem (.cv y) (syn_chwcn A)))) (syn_wa
              (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
                (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v))
                    (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) (syn_wbr (.cv y)
                (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv u))))
          (syn_wa (.classMem (.cv t) (syn_cfv (syn_c2nd) (.cv u)))
            (syn_wbr (.cv y) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                (.cv t))))) (syn_wa (.classMem (.cv z) (syn_cin (syn_cfv (syn_c2nd) (.cv v))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
                (syn_csn (.cv x))))) (syn_wbr
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv t))
            (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv z)))))
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
              (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
              (.classMem (.cv y) (syn_chwcn A)))) (syn_wa
            (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
              (syn_wbr (.cv u) (syn_chwniso A)
                (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                  (.cv x)))) (syn_wbr (.cv y)
              (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv u))))
        (syn_wa (.classMem (.cv t) (syn_cfv (syn_c2nd) (.cv u)))
          (syn_wbr (.cv y) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
              (.cv t)))))
      (.classMem A (syn_cvv)) p0046 p0050
  have p0052 := @g_hwnisoerv A
  have p0053 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
                (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
                (.classMem (.cv y) (syn_chwcn A)))) (syn_wa
              (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
                (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v))
                    (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) (syn_wbr (.cv y)
                (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv u))))
          (syn_wa (.classMem (.cv t) (syn_cfv (syn_c2nd) (.cv u)))
            (syn_wbr (.cv y) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                (.cv t))))) (syn_wa (.classMem (.cv z) (syn_cin (syn_cfv (syn_c2nd) (.cv v))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
                (syn_csn (.cv x))))) (syn_wbr
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv t))
            (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv z)))))
      (.classMem A (syn_cvv)) (syn_wbr (syn_chwniso A) (syn_cer) (syn_cvv)) p0051 p0052
  have p0059 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
              (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
              (.classMem (.cv y) (syn_chwcn A)))) (syn_wa
            (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
              (syn_wbr (.cv u) (syn_chwniso A)
                (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                  (.cv x)))) (syn_wbr (.cv y)
              (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv u))))
        (syn_wa (.classMem (.cv t) (syn_cfv (syn_c2nd) (.cv u)))
          (syn_wbr (.cv y) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
              (.cv t)))))
      (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
            (.classMem (.cv y) (syn_chwcn A)))) (syn_wa
          (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
            (syn_wbr (.cv u) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv x)))) (syn_wbr (.cv y)
            (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv u))))
      (.classMem (.cv y) (syn_chwcn A)) p0016 p0006
  have p0060 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
                (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
                (.classMem (.cv y) (syn_chwcn A)))) (syn_wa
              (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
                (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v))
                    (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) (syn_wbr (.cv y)
                (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv u))))
          (syn_wa (.classMem (.cv t) (syn_cfv (syn_c2nd) (.cv u)))
            (syn_wbr (.cv y) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                (.cv t))))) (syn_wa (.classMem (.cv z) (syn_cin (syn_cfv (syn_c2nd) (.cv v))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
                (syn_csn (.cv x))))) (syn_wbr
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv t))
            (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv z)))))
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
              (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
              (.classMem (.cv y) (syn_chwcn A)))) (syn_wa
            (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
              (syn_wbr (.cv u) (syn_chwniso A)
                (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                  (.cv x)))) (syn_wbr (.cv y)
              (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv u))))
        (syn_wa (.classMem (.cv t) (syn_cfv (syn_c2nd) (.cv u)))
          (syn_wbr (.cv y) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
              (.cv t)))))
      (.classMem (.cv y) (syn_chwcn A)) p0046 p0059
  have p0061 := @g_elex (.cv y) (syn_chwcn A)
  have p0062 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
                (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
                (.classMem (.cv y) (syn_chwcn A)))) (syn_wa
              (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
                (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v))
                    (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) (syn_wbr (.cv y)
                (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv u))))
          (syn_wa (.classMem (.cv t) (syn_cfv (syn_c2nd) (.cv u)))
            (syn_wbr (.cv y) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                (.cv t))))) (syn_wa (.classMem (.cv z) (syn_cin (syn_cfv (syn_c2nd) (.cv v))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
                (syn_csn (.cv x))))) (syn_wbr
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv t))
            (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv z)))))
      (.classMem (.cv y) (syn_chwcn A)) (.classMem (.cv y) (syn_cvv)) p0060 p0061
  have p0070 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
                (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
                (.classMem (.cv y) (syn_chwcn A)))) (syn_wa
              (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
                (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v))
                    (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) (syn_wbr (.cv y)
                (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv u))))
          (syn_wa (.classMem (.cv t) (syn_cfv (syn_c2nd) (.cv u)))
            (syn_wbr (.cv y) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                (.cv t))))) (syn_wa (.classMem (.cv z) (syn_cin (syn_cfv (syn_c2nd) (.cv v))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
                (syn_csn (.cv x))))) (syn_wbr
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv t))
            (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv z)))))
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
              (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
              (.classMem (.cv y) (syn_chwcn A)))) (syn_wa
            (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
              (syn_wbr (.cv u) (syn_chwniso A)
                (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                  (.cv x)))) (syn_wbr (.cv y)
              (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv u))))
        (syn_wa (.classMem (.cv t) (syn_cfv (syn_c2nd) (.cv u)))
          (syn_wbr (.cv y) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
              (.cv t)))))
      (.classMem (.cv u) (syn_chwcn A)) p0046 p0021
  have p0074 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
                (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
                (.classMem (.cv y) (syn_chwcn A)))) (syn_wa
              (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
                (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v))
                    (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) (syn_wbr (.cv y)
                (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv u))))
          (syn_wa (.classMem (.cv t) (syn_cfv (syn_c2nd) (.cv u)))
            (syn_wbr (.cv y) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                (.cv t))))) (syn_wa (.classMem (.cv z) (syn_cin (syn_cfv (syn_c2nd) (.cv v))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
                (syn_csn (.cv x))))) (syn_wbr
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv t))
            (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv z)))))
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
              (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
              (.classMem (.cv y) (syn_chwcn A)))) (syn_wa
            (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
              (syn_wbr (.cv u) (syn_chwniso A)
                (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                  (.cv x)))) (syn_wbr (.cv y)
              (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv u))))
        (syn_wa (.classMem (.cv t) (syn_cfv (syn_c2nd) (.cv u)))
          (syn_wbr (.cv y) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
              (.cv t)))))
      (.classMem (.cv t) (syn_cfv (syn_c2nd) (.cv u))) p0046 p0041
  have p0075 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
                (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
                (.classMem (.cv y) (syn_chwcn A)))) (syn_wa
              (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
                (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v))
                    (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) (syn_wbr (.cv y)
                (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv u))))
          (syn_wa (.classMem (.cv t) (syn_cfv (syn_c2nd) (.cv u)))
            (syn_wbr (.cv y) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                (.cv t))))) (syn_wa (.classMem (.cv z) (syn_cin (syn_cfv (syn_c2nd) (.cv v))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
                (syn_csn (.cv x))))) (syn_wbr
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv t))
            (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv z)))))
      (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv t) (syn_cfv (syn_c2nd) (.cv u)))
      p0070 p0074
  have p0076 := @g_hnwcutcodeambientndv t u A dv_cache_0002
  have p0077 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
                (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
                (.classMem (.cv y) (syn_chwcn A)))) (syn_wa
              (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
                (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v))
                    (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) (syn_wbr (.cv y)
                (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv u))))
          (syn_wa (.classMem (.cv t) (syn_cfv (syn_c2nd) (.cv u)))
            (syn_wbr (.cv y) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                (.cv t))))) (syn_wa (.classMem (.cv z) (syn_cin (syn_cfv (syn_c2nd) (.cv v))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
                (syn_csn (.cv x))))) (syn_wbr
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv t))
            (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv z)))))
      (syn_wa (.classMem (.cv u) (syn_chwcn A))
        (.classMem (.cv t) (syn_cfv (syn_c2nd) (.cv u))))
      (.classMem (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (.cv t)) (syn_chwcn A))
      p0075 p0076
  have p0078 :=
    @g_elex
      (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv t))
      (syn_chwcn A)
  have p0079 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
                (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
                (.classMem (.cv y) (syn_chwcn A)))) (syn_wa
              (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
                (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v))
                    (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) (syn_wbr (.cv y)
                (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv u))))
          (syn_wa (.classMem (.cv t) (syn_cfv (syn_c2nd) (.cv u)))
            (syn_wbr (.cv y) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                (.cv t))))) (syn_wa (.classMem (.cv z) (syn_cin (syn_cfv (syn_c2nd) (.cv v))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
                (syn_csn (.cv x))))) (syn_wbr
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv t))
            (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv z)))))
      (.classMem (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (.cv t)) (syn_chwcn A))
      (.classMem (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (.cv t)) (syn_cvv))
      p0077 p0078
  have p0087 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
                (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
                (.classMem (.cv y) (syn_chwcn A)))) (syn_wa
              (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
                (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v))
                    (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) (syn_wbr (.cv y)
                (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv u))))
          (syn_wa (.classMem (.cv t) (syn_cfv (syn_c2nd) (.cv u)))
            (syn_wbr (.cv y) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                (.cv t))))) (syn_wa (.classMem (.cv z) (syn_cin (syn_cfv (syn_c2nd) (.cv v))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
                (syn_csn (.cv x))))) (syn_wbr
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv t))
            (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv z)))))
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
              (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
              (.classMem (.cv y) (syn_chwcn A)))) (syn_wa
            (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
              (syn_wbr (.cv u) (syn_chwniso A)
                (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                  (.cv x)))) (syn_wbr (.cv y)
              (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv u))))
        (syn_wa (.classMem (.cv t) (syn_cfv (syn_c2nd) (.cv u)))
          (syn_wbr (.cv y) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
              (.cv t)))))
      (.classMem (.cv v) (syn_chwcn A)) p0046 p0027
  have p0088 :=
    @g_simpr
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
              (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
              (.classMem (.cv y) (syn_chwcn A)))) (syn_wa
            (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
              (syn_wbr (.cv u) (syn_chwniso A)
                (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                  (.cv x)))) (syn_wbr (.cv y)
              (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv u))))
        (syn_wa (.classMem (.cv t) (syn_cfv (syn_c2nd) (.cv u)))
          (syn_wbr (.cv y) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
              (.cv t)))))
      (syn_wa (.classMem (.cv z) (syn_cin (syn_cfv (syn_c2nd) (.cv v))
            (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
              (syn_csn (.cv x))))) (syn_wbr
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv t))
          (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv z))))
  have p0089 :=
    @g_simpld
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
                (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
                (.classMem (.cv y) (syn_chwcn A)))) (syn_wa
              (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
                (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v))
                    (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) (syn_wbr (.cv y)
                (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv u))))
          (syn_wa (.classMem (.cv t) (syn_cfv (syn_c2nd) (.cv u)))
            (syn_wbr (.cv y) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                (.cv t))))) (syn_wa (.classMem (.cv z) (syn_cin (syn_cfv (syn_c2nd) (.cv v))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
                (syn_csn (.cv x))))) (syn_wbr
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv t))
            (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv z)))))
      (.classMem (.cv z) (syn_cin (syn_cfv (syn_c2nd) (.cv v))
          (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
            (syn_csn (.cv x)))))
      (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (.cv t)) (syn_chwniso A)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv z)))
      p0088
  have p0090 :=
    @g_inss1 (syn_cfv (syn_c2nd) (.cv v))
      (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid))) (syn_csn (.cv x)))
  have p0091 :=
    @g_sseli
      (syn_cin (syn_cfv (syn_c2nd) (.cv v))
        (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
          (syn_csn (.cv x))))
      (syn_cfv (syn_c2nd) (.cv v)) (.cv z) p0090
  have p0092 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
                (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
                (.classMem (.cv y) (syn_chwcn A)))) (syn_wa
              (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
                (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v))
                    (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) (syn_wbr (.cv y)
                (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv u))))
          (syn_wa (.classMem (.cv t) (syn_cfv (syn_c2nd) (.cv u)))
            (syn_wbr (.cv y) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                (.cv t))))) (syn_wa (.classMem (.cv z) (syn_cin (syn_cfv (syn_c2nd) (.cv v))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
                (syn_csn (.cv x))))) (syn_wbr
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv t))
            (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv z)))))
      (.classMem (.cv z) (syn_cin (syn_cfv (syn_c2nd) (.cv v))
          (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
            (syn_csn (.cv x)))))
      (.classMem (.cv z) (syn_cfv (syn_c2nd) (.cv v))) p0089 p0091
  have p0093 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
                (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
                (.classMem (.cv y) (syn_chwcn A)))) (syn_wa
              (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
                (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v))
                    (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) (syn_wbr (.cv y)
                (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv u))))
          (syn_wa (.classMem (.cv t) (syn_cfv (syn_c2nd) (.cv u)))
            (syn_wbr (.cv y) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                (.cv t))))) (syn_wa (.classMem (.cv z) (syn_cin (syn_cfv (syn_c2nd) (.cv v))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
                (syn_csn (.cv x))))) (syn_wbr
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv t))
            (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv z)))))
      (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv z) (syn_cfv (syn_c2nd) (.cv v)))
      p0087 p0092
  have p0094 := @g_hnwcutcodeambientndv z v A dv_cache_0007
  have p0095 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
                (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
                (.classMem (.cv y) (syn_chwcn A)))) (syn_wa
              (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
                (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v))
                    (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) (syn_wbr (.cv y)
                (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv u))))
          (syn_wa (.classMem (.cv t) (syn_cfv (syn_c2nd) (.cv u)))
            (syn_wbr (.cv y) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                (.cv t))))) (syn_wa (.classMem (.cv z) (syn_cin (syn_cfv (syn_c2nd) (.cv v))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
                (syn_csn (.cv x))))) (syn_wbr
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv t))
            (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv z)))))
      (syn_wa (.classMem (.cv v) (syn_chwcn A))
        (.classMem (.cv z) (syn_cfv (syn_c2nd) (.cv v))))
      (.classMem (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
          (.cv z)) (syn_chwcn A))
      p0093 p0094
  have p0096 :=
    @g_elex
      (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv z))
      (syn_chwcn A)
  have p0097 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
                (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
                (.classMem (.cv y) (syn_chwcn A)))) (syn_wa
              (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
                (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v))
                    (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) (syn_wbr (.cv y)
                (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv u))))
          (syn_wa (.classMem (.cv t) (syn_cfv (syn_c2nd) (.cv u)))
            (syn_wbr (.cv y) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                (.cv t))))) (syn_wa (.classMem (.cv z) (syn_cin (syn_cfv (syn_c2nd) (.cv v))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
                (syn_csn (.cv x))))) (syn_wbr
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv t))
            (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv z)))))
      (.classMem (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
          (.cv z)) (syn_chwcn A))
      (.classMem (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
          (.cv z)) (syn_cvv))
      p0095 p0096
  have p0100 :=
    @g_simprd
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
              (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
              (.classMem (.cv y) (syn_chwcn A)))) (syn_wa
            (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
              (syn_wbr (.cv u) (syn_chwniso A)
                (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                  (.cv x)))) (syn_wbr (.cv y)
              (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv u))))
        (syn_wa (.classMem (.cv t) (syn_cfv (syn_c2nd) (.cv u)))
          (syn_wbr (.cv y) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
              (.cv t)))))
      (.classMem (.cv t) (syn_cfv (syn_c2nd) (.cv u)))
      (syn_wbr (.cv y) (syn_chwniso A)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv t)))
      p0040
  have p0101 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
                (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
                (.classMem (.cv y) (syn_chwcn A)))) (syn_wa
              (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
                (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v))
                    (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) (syn_wbr (.cv y)
                (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv u))))
          (syn_wa (.classMem (.cv t) (syn_cfv (syn_c2nd) (.cv u)))
            (syn_wbr (.cv y) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                (.cv t))))) (syn_wa (.classMem (.cv z) (syn_cin (syn_cfv (syn_c2nd) (.cv v))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
                (syn_csn (.cv x))))) (syn_wbr
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv t))
            (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv z)))))
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
              (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
              (.classMem (.cv y) (syn_chwcn A)))) (syn_wa
            (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
              (syn_wbr (.cv u) (syn_chwniso A)
                (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                  (.cv x)))) (syn_wbr (.cv y)
              (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv u))))
        (syn_wa (.classMem (.cv t) (syn_cfv (syn_c2nd) (.cv u)))
          (syn_wbr (.cv y) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
              (.cv t)))))
      (syn_wbr (.cv y) (syn_chwniso A)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv t)))
      p0046 p0100
  have p0103 :=
    @g_simprd
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
                (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
                (.classMem (.cv y) (syn_chwcn A)))) (syn_wa
              (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
                (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v))
                    (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) (syn_wbr (.cv y)
                (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv u))))
          (syn_wa (.classMem (.cv t) (syn_cfv (syn_c2nd) (.cv u)))
            (syn_wbr (.cv y) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                (.cv t))))) (syn_wa (.classMem (.cv z) (syn_cin (syn_cfv (syn_c2nd) (.cv v))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
                (syn_csn (.cv x))))) (syn_wbr
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv t))
            (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv z)))))
      (.classMem (.cv z) (syn_cin (syn_cfv (syn_c2nd) (.cv v))
          (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
            (syn_csn (.cv x)))))
      (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (.cv t)) (syn_chwniso A)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv z)))
      p0088
  have p0104 :=
    @g_ertrd
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
                (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
                (.classMem (.cv y) (syn_chwcn A)))) (syn_wa
              (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
                (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v))
                    (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) (syn_wbr (.cv y)
                (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv u))))
          (syn_wa (.classMem (.cv t) (syn_cfv (syn_c2nd) (.cv u)))
            (syn_wbr (.cv y) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                (.cv t))))) (syn_wa (.classMem (.cv z) (syn_cin (syn_cfv (syn_c2nd) (.cv v))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
                (syn_csn (.cv x))))) (syn_wbr
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv t))
            (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv z)))))
      (syn_cvv) (syn_chwniso A) (.cv y)
      (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv t))
      (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv z))
      p0053 p0062 p0079 p0097 p0101 p0103
  have p0105 :=
    @g_anassrs
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
              (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
              (.classMem (.cv y) (syn_chwcn A)))) (syn_wa
            (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
              (syn_wbr (.cv u) (syn_chwniso A)
                (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                  (.cv x)))) (syn_wbr (.cv y)
              (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv u))))
        (syn_wa (.classMem (.cv t) (syn_cfv (syn_c2nd) (.cv u)))
          (syn_wbr (.cv y) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
              (.cv t)))))
      (.classMem (.cv z) (syn_cin (syn_cfv (syn_c2nd) (.cv v))
          (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
            (syn_csn (.cv x)))))
      (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (.cv t)) (syn_chwniso A)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv z)))
      (syn_wbr (.cv y) (syn_chwniso A)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv z)))
      p0104
  have p0106 :=
    @g_ex
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
                (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
                (.classMem (.cv y) (syn_chwcn A)))) (syn_wa
              (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
                (syn_wbr (.cv u) (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v))
                    (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))) (syn_wbr (.cv y)
                (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv u))))
          (syn_wa (.classMem (.cv t) (syn_cfv (syn_c2nd) (.cv u)))
            (syn_wbr (.cv y) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                (.cv t))))) (.classMem (.cv z) (syn_cin (syn_cfv (syn_c2nd) (.cv v))
            (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
              (syn_csn (.cv x))))))
      (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (.cv t)) (syn_chwniso A)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv z)))
      (syn_wbr (.cv y) (syn_chwniso A)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv z)))
      p0105
  have p0107 :=
    @g_reximdva
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
              (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
              (.classMem (.cv y) (syn_chwcn A)))) (syn_wa
            (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
              (syn_wbr (.cv u) (syn_chwniso A)
                (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                  (.cv x)))) (syn_wbr (.cv y)
              (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv u))))
        (syn_wa (.classMem (.cv t) (syn_cfv (syn_c2nd) (.cv u)))
          (syn_wbr (.cv y) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
              (.cv t)))))
      (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (.cv t)) (syn_chwniso A)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv z)))
      (syn_wbr (.cv y) (syn_chwniso A)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv z)))
      z
      (syn_cin (syn_cfv (syn_c2nd) (.cv v))
        (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
          (syn_csn (.cv x))))
      dv_cache_0013 p0106
  have p0108 :=
    @g_mpd
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
              (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
              (.classMem (.cv y) (syn_chwcn A)))) (syn_wa
            (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
              (syn_wbr (.cv u) (syn_chwniso A)
                (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                  (.cv x)))) (syn_wbr (.cv y)
              (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv u))))
        (syn_wa (.classMem (.cv t) (syn_cfv (syn_c2nd) (.cv u)))
          (syn_wbr (.cv y) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
              (.cv t)))))
      (syn_wrex z (syn_cin (syn_cfv (syn_c2nd) (.cv v))
          (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
            (syn_csn (.cv x)))) (syn_wbr
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv t))
          (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv z))))
      (syn_wrex z (syn_cin (syn_cfv (syn_c2nd) (.cv v))
          (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
            (syn_csn (.cv x)))) (syn_wbr (.cv y) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv z))))
      p0045 p0107
  have p0109 :=
    @g_rexlimddv
      (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
            (.classMem (.cv y) (syn_chwcn A)))) (syn_wa
          (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
            (syn_wbr (.cv u) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv x)))) (syn_wbr (.cv y)
            (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv u))))
      (syn_wbr (.cv y) (syn_chwniso A)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv t)))
      (syn_wrex z (syn_cin (syn_cfv (syn_c2nd) (.cv v))
          (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
            (syn_csn (.cv x)))) (syn_wbr (.cv y) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv z))))
      t (syn_cfv (syn_c2nd) (.cv u)) dv_cache_0014 dv_cache_0015 p0015 p0108
  exact p0109


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk017Compact001Part044`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_hncodepredrepminimalndv (x : Var) (y : Var) (z : Var) (v : Var)
    (u : Var) (A : Class) (X : Class) (dv_A_u : u ∉ A.fv) (dv_A_v : v ∉ A.fv)
    (dv_A_y : y ∉ A.fv) (dv_A_z : z ∉ A.fv) (dv_X_y : y ∉ X.fv) (dv_X_z : z ∉ X.fv)
    (dv_u_y : u ≠ y) (_dv_u_z : u ≠ z) (dv_v_y : v ≠ y) (dv_v_z : v ≠ z) (dv_x_y : x ≠ y)
    (dv_x_z : x ≠ z) (dv_y_z : y ≠ z) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wa (.classMem A (syn_cvv))
            (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wa
            (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v))
              (syn_wa (.classMem (.cv u) X) (syn_wbr (.cv u) (syn_chwniso A)
                  (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v))
                    (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))))
            (syn_wral z (syn_chncodepredends A X v)
              (.imp (syn_wbr (.cv z) (syn_cfv (syn_c1st) (.cv v)) (.cv x))
                (.classEq (.cv z) (.cv x)))))) (syn_wral y X (.imp (syn_wbr (.cv y)
              (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv u))
            (.classEq (.cv y) (.cv u))))) :=
  by
  let proofSupport : Finset Var :=
    ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ ({ z } : Finset Var) ∪
            ({ v } : Finset Var) ∪
          ({ u } : Finset Var) ∪
        A.fv ∪
      X.fv
  let t : Var := freshVar proofSupport 0
  let a : Var := freshVar proofSupport 1
  have fresh_t : t ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_t_ne_x : t ≠ x := by
    intro h
    exact
      fresh_t
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _
                  (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))))
  have fresh_x_ne_t : x ≠ t := Ne.symm fresh_t_ne_x
  have fresh_t_ne_y : t ≠ y := by
    intro h
    exact
      fresh_t
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _
                  (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))))
  have fresh_y_ne_t : y ≠ t := Ne.symm fresh_t_ne_y
  have fresh_t_ne_z : t ≠ z := by
    intro h
    exact
      fresh_t
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _
                (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))))
  have fresh_z_ne_t : z ≠ t := Ne.symm fresh_t_ne_z
  have fresh_t_ne_v : t ≠ v := by
    intro h
    exact
      fresh_t
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))
  have fresh_v_ne_t : v ≠ t := Ne.symm fresh_t_ne_v
  have fresh_t_ne_u : t ≠ u := by
    intro h
    exact
      fresh_t
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_u_ne_t : u ≠ t := Ne.symm fresh_t_ne_u
  have fresh_t_not_A : t ∉ A.fv := by
    intro h
    exact fresh_t (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_t_not_X : t ∉ X.fv := by
    intro h
    exact fresh_t (Finset.mem_union_right _ (h))
  have fresh_a : a ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_a_ne_y : a ≠ y := by
    intro h
    exact
      fresh_a
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _
                  (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))))
  have fresh_a_ne_v : a ≠ v := by
    intro h
    exact
      fresh_a
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))
  have fresh_a_not_A : a ∉ A.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_a_not_X : a ∉ X.fv := by
    intro h
    exact fresh_a (Finset.mem_union_right _ (h))
  have fresh_t_ne_a : t ≠ a :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_a_ne_t : a ≠ t := Ne.symm fresh_t_ne_a
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
  have dv_cache_0003 : y ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_y, not_false_eq_true])
  have dv_cache_0004 : t ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_t_not_A, not_false_eq_true])
  have dv_cache_0005 : u ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show u ≠ y from (by exact dv_u_y))
  have dv_cache_0006 : u ≠ t :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show u ≠ t from (by exact fresh_u_ne_t))
  have dv_cache_0007 : v ≠ t :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact (show v ≠ t from (by exact fresh_v_ne_t))
  have dv_cache_0008 : x ≠ t :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact (show x ≠ t from (by exact fresh_x_ne_t))
  have dv_cache_0009 : y ≠ t :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (show y ≠ t from (by exact fresh_y_ne_t))
  have dv_cache_0010 : a ∉ ((Class.cv y)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_a_ne_y, not_false_eq_true])
  have dv_cache_0011 : a ∉ (X).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_a_not_X, not_false_eq_true])
  have dv_cache_0012 :
    a ∉
      ((syn_wbr (.cv y) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
            (.cv t)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutcode,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union,
          Finset.mem_singleton, fresh_a_ne_y, fresh_a_ne_t, fresh_a_ne_v, fresh_a_not_A,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0013 : a ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_a_not_A, not_false_eq_true])
  have dv_cache_0014 : a ≠ v :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact (show a ≠ v from (by exact fresh_a_ne_v))
  have dv_cache_0015 : a ≠ t :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (show a ≠ t from (by exact fresh_a_ne_t))
  have dv_cache_0016 : z ∉ ((Class.cv t)).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_z_ne_t, not_false_eq_true])
  have dv_cache_0017 : z ∉ ((syn_chncodepredends A X v)).fv :=
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
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodepredends,
          Finset.mem_union, Finset.mem_singleton, dv_A_z, dv_X_z, (Ne.symm dv_v_z),
          or_false, not_false_eq_true])
  have dv_cache_0018 :
    z ∉
      ((Wff.imp (syn_wbr (.cv t) (syn_cfv (syn_c1st) (.cv v)) (.cv x))
          (.classEq (.cv t) (.cv x)))).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_t, (Ne.symm dv_x_z), (Ne.symm dv_v_z),
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0019 : t ∉ ((Wff.classEq (.cv y) (.cv u))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_t_ne_y, fresh_t_ne_u, or_false, not_false_eq_true])
  have dv_cache_0020 :
    t ∉
      ((syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv))
                (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wa
                (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v))
                  (syn_wa (.classMem (.cv u) X) (syn_wbr (.cv u) (syn_chwniso A)
                      (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v))
                        (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))))
                (syn_wral z (syn_chncodepredends A X v)
                  (.imp (syn_wbr (.cv z) (syn_cfv (syn_c1st) (.cv v)) (.cv x))
                    (.classEq (.cv z) (.cv x)))))) (.classMem (.cv y) X)) (syn_wbr (.cv y)
            (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv u)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodepredends,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutcode,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
          NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodecmpset,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_t_not_A, fresh_t_not_X,
          fresh_t_ne_v, fresh_t_ne_x, fresh_t_ne_u, fresh_t_ne_z, fresh_t_ne_y,
          compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0021 :
    y ∉
      ((syn_wa (syn_wa (.classMem A (syn_cvv))
            (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wa
            (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v))
              (syn_wa (.classMem (.cv u) X) (syn_wbr (.cv u) (syn_chwniso A)
                  (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v))
                    (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))))
            (syn_wral z (syn_chncodepredends A X v)
              (.imp (syn_wbr (.cv z) (syn_cfv (syn_c1st) (.cv v)) (.cv x))
                (.classEq (.cv z) (.cv x))))))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodepredends,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutcode,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
          NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, dv_A_y, dv_X_y, (Ne.symm dv_v_y), (Ne.symm dv_x_y),
          (Ne.symm dv_u_y), dv_y_z, compact_fv_not_mem_empty, or_false, and_false,
          not_false_eq_true])
  have p0000 :=
    @g_simpl
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv))
            (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wa
            (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v))
              (syn_wa (.classMem (.cv u) X) (syn_wbr (.cv u) (syn_chwniso A)
                  (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v))
                    (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))))
            (syn_wral z (syn_chncodepredends A X v)
              (.imp (syn_wbr (.cv z) (syn_cfv (syn_c1st) (.cv v)) (.cv x))
                (.classEq (.cv z) (.cv x)))))) (.classMem (.cv y) X))
      (syn_wbr (.cv y) (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A)))
        (.cv u))
  have p0001 :=
    @g_simpl
      (syn_wa (syn_wa (.classMem A (syn_cvv))
          (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wa
          (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v)) (syn_wa (.classMem (.cv u) X)
              (syn_wbr (.cv u) (syn_chwniso A)
                (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                  (.cv x))))) (syn_wral z (syn_chncodepredends A X v)
            (.imp (syn_wbr (.cv z) (syn_cfv (syn_c1st) (.cv v)) (.cv x))
              (.classEq (.cv z) (.cv x))))))
      (.classMem (.cv y) X)
  have p0002 :=
    @g_simpl
      (syn_wa (.classMem A (syn_cvv))
        (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
      (syn_wa (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v))
          (syn_wa (.classMem (.cv u) X) (syn_wbr (.cv u) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv x))))) (syn_wral z (syn_chncodepredends A X v)
          (.imp (syn_wbr (.cv z) (syn_cfv (syn_c1st) (.cv v)) (.cv x))
            (.classEq (.cv z) (.cv x)))))
  have p0003 :=
    @g_simpld
      (syn_wa (syn_wa (.classMem A (syn_cvv))
          (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wa
          (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v)) (syn_wa (.classMem (.cv u) X)
              (syn_wbr (.cv u) (syn_chwniso A)
                (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                  (.cv x))))) (syn_wral z (syn_chncodepredends A X v)
            (.imp (syn_wbr (.cv z) (syn_cfv (syn_c1st) (.cv v)) (.cv x))
              (.classEq (.cv z) (.cv x))))))
      (.classMem A (syn_cvv))
      (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) p0002
  have p0004 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv))
            (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wa
            (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v))
              (syn_wa (.classMem (.cv u) X) (syn_wbr (.cv u) (syn_chwniso A)
                  (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v))
                    (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))))
            (syn_wral z (syn_chncodepredends A X v)
              (.imp (syn_wbr (.cv z) (syn_cfv (syn_c1st) (.cv v)) (.cv x))
                (.classEq (.cv z) (.cv x)))))) (.classMem (.cv y) X))
      (syn_wa (syn_wa (.classMem A (syn_cvv))
          (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wa
          (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v)) (syn_wa (.classMem (.cv u) X)
              (syn_wbr (.cv u) (syn_chwniso A)
                (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                  (.cv x))))) (syn_wral z (syn_chncodepredends A X v)
            (.imp (syn_wbr (.cv z) (syn_cfv (syn_c1st) (.cv v)) (.cv x))
              (.classEq (.cv z) (.cv x))))))
      (.classMem A (syn_cvv)) p0001 p0003
  have p0005 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv))
              (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wa
              (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v))
                (syn_wa (.classMem (.cv u) X) (syn_wbr (.cv u) (syn_chwniso A)
                    (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v))
                      (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))))
              (syn_wral z (syn_chncodepredends A X v)
                (.imp (syn_wbr (.cv z) (syn_cfv (syn_c1st) (.cv v)) (.cv x))
                  (.classEq (.cv z) (.cv x)))))) (.classMem (.cv y) X))
        (syn_wbr (.cv y) (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A)))
          (.cv u)))
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv))
            (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wa
            (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v))
              (syn_wa (.classMem (.cv u) X) (syn_wbr (.cv u) (syn_chwniso A)
                  (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v))
                    (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))))
            (syn_wral z (syn_chncodepredends A X v)
              (.imp (syn_wbr (.cv z) (syn_cfv (syn_c1st) (.cv v)) (.cv x))
                (.classEq (.cv z) (.cv x)))))) (.classMem (.cv y) X))
      (.classMem A (syn_cvv)) p0000 p0004
  have p0009 :=
    @g_simprd
      (syn_wa (syn_wa (.classMem A (syn_cvv))
          (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wa
          (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v)) (syn_wa (.classMem (.cv u) X)
              (syn_wbr (.cv u) (syn_chwniso A)
                (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                  (.cv x))))) (syn_wral z (syn_chncodepredends A X v)
            (.imp (syn_wbr (.cv z) (syn_cfv (syn_c1st) (.cv v)) (.cv x))
              (.classEq (.cv z) (.cv x))))))
      (.classMem A (syn_cvv))
      (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) p0002
  have p0010 :=
    @g_simpld
      (syn_wa (syn_wa (.classMem A (syn_cvv))
          (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wa
          (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v)) (syn_wa (.classMem (.cv u) X)
              (syn_wbr (.cv u) (syn_chwniso A)
                (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                  (.cv x))))) (syn_wral z (syn_chncodepredends A X v)
            (.imp (syn_wbr (.cv z) (syn_cfv (syn_c1st) (.cv v)) (.cv x))
              (.classEq (.cv z) (.cv x))))))
      (syn_wss X (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)) p0009
  have p0011 :=
    @g_simpr
      (syn_wa (.classMem A (syn_cvv))
        (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
      (syn_wa (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v))
          (syn_wa (.classMem (.cv u) X) (syn_wbr (.cv u) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv x))))) (syn_wral z (syn_chncodepredends A X v)
          (.imp (syn_wbr (.cv z) (syn_cfv (syn_c1st) (.cv v)) (.cv x))
            (.classEq (.cv z) (.cv x)))))
  have p0012 :=
    @g_simpld
      (syn_wa (syn_wa (.classMem A (syn_cvv))
          (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wa
          (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v)) (syn_wa (.classMem (.cv u) X)
              (syn_wbr (.cv u) (syn_chwniso A)
                (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                  (.cv x))))) (syn_wral z (syn_chncodepredends A X v)
            (.imp (syn_wbr (.cv z) (syn_cfv (syn_c1st) (.cv v)) (.cv x))
              (.classEq (.cv z) (.cv x))))))
      (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v)) (syn_wa (.classMem (.cv u) X)
          (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv x)))))
      (syn_wral z (syn_chncodepredends A X v)
        (.imp (syn_wbr (.cv z) (syn_cfv (syn_c1st) (.cv v)) (.cv x))
          (.classEq (.cv z) (.cv x))))
      p0011
  have p0013 :=
    @g_simprd
      (syn_wa (syn_wa (.classMem A (syn_cvv))
          (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wa
          (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v)) (syn_wa (.classMem (.cv u) X)
              (syn_wbr (.cv u) (syn_chwniso A)
                (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                  (.cv x))))) (syn_wral z (syn_chncodepredends A X v)
            (.imp (syn_wbr (.cv z) (syn_cfv (syn_c1st) (.cv v)) (.cv x))
              (.classEq (.cv z) (.cv x))))))
      (.classMem (.cv x) (syn_chncodepredends A X v))
      (syn_wa (.classMem (.cv u) X) (syn_wbr (.cv u) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))
      p0012
  have p0014 :=
    @g_simpld
      (syn_wa (syn_wa (.classMem A (syn_cvv))
          (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wa
          (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v)) (syn_wa (.classMem (.cv u) X)
              (syn_wbr (.cv u) (syn_chwniso A)
                (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                  (.cv x))))) (syn_wral z (syn_chncodepredends A X v)
            (.imp (syn_wbr (.cv z) (syn_cfv (syn_c1st) (.cv v)) (.cv x))
              (.classEq (.cv z) (.cv x))))))
      (.classMem (.cv u) X)
      (syn_wbr (.cv u) (syn_chwniso A)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))
      p0013
  have p0015 :=
    @g_sseldd
      (syn_wa (syn_wa (.classMem A (syn_cvv))
          (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wa
          (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v)) (syn_wa (.classMem (.cv u) X)
              (syn_wbr (.cv u) (syn_chwniso A)
                (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                  (.cv x))))) (syn_wral z (syn_chncodepredends A X v)
            (.imp (syn_wbr (.cv z) (syn_cfv (syn_c1st) (.cv v)) (.cv x))
              (.classEq (.cv z) (.cv x))))))
      X (syn_chwcn A) (.cv u) p0010 p0014
  have p0016 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv))
            (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wa
            (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v))
              (syn_wa (.classMem (.cv u) X) (syn_wbr (.cv u) (syn_chwniso A)
                  (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v))
                    (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))))
            (syn_wral z (syn_chncodepredends A X v)
              (.imp (syn_wbr (.cv z) (syn_cfv (syn_c1st) (.cv v)) (.cv x))
                (.classEq (.cv z) (.cv x)))))) (.classMem (.cv y) X))
      (syn_wa (syn_wa (.classMem A (syn_cvv))
          (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wa
          (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v)) (syn_wa (.classMem (.cv u) X)
              (syn_wbr (.cv u) (syn_chwniso A)
                (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                  (.cv x))))) (syn_wral z (syn_chncodepredends A X v)
            (.imp (syn_wbr (.cv z) (syn_cfv (syn_c1st) (.cv v)) (.cv x))
              (.classEq (.cv z) (.cv x))))))
      (.classMem (.cv u) (syn_chwcn A)) p0001 p0015
  have p0017 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv))
              (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wa
              (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v))
                (syn_wa (.classMem (.cv u) X) (syn_wbr (.cv u) (syn_chwniso A)
                    (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v))
                      (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))))
              (syn_wral z (syn_chncodepredends A X v)
                (.imp (syn_wbr (.cv z) (syn_cfv (syn_c1st) (.cv v)) (.cv x))
                  (.classEq (.cv z) (.cv x)))))) (.classMem (.cv y) X))
        (syn_wbr (.cv y) (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A)))
          (.cv u)))
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv))
            (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wa
            (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v))
              (syn_wa (.classMem (.cv u) X) (syn_wbr (.cv u) (syn_chwniso A)
                  (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v))
                    (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))))
            (syn_wral z (syn_chncodepredends A X v)
              (.imp (syn_wbr (.cv z) (syn_cfv (syn_c1st) (.cv v)) (.cv x))
                (.classEq (.cv z) (.cv x)))))) (.classMem (.cv y) X))
      (.classMem (.cv u) (syn_chwcn A)) p0000 p0016
  have p0022 :=
    @g_simprd
      (syn_wa (syn_wa (.classMem A (syn_cvv))
          (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wa
          (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v)) (syn_wa (.classMem (.cv u) X)
              (syn_wbr (.cv u) (syn_chwniso A)
                (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                  (.cv x))))) (syn_wral z (syn_chncodepredends A X v)
            (.imp (syn_wbr (.cv z) (syn_cfv (syn_c1st) (.cv v)) (.cv x))
              (.classEq (.cv z) (.cv x))))))
      (syn_wss X (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)) p0009
  have p0023 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv))
            (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wa
            (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v))
              (syn_wa (.classMem (.cv u) X) (syn_wbr (.cv u) (syn_chwniso A)
                  (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v))
                    (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))))
            (syn_wral z (syn_chncodepredends A X v)
              (.imp (syn_wbr (.cv z) (syn_cfv (syn_c1st) (.cv v)) (.cv x))
                (.classEq (.cv z) (.cv x)))))) (.classMem (.cv y) X))
      (syn_wa (syn_wa (.classMem A (syn_cvv))
          (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wa
          (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v)) (syn_wa (.classMem (.cv u) X)
              (syn_wbr (.cv u) (syn_chwniso A)
                (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                  (.cv x))))) (syn_wral z (syn_chncodepredends A X v)
            (.imp (syn_wbr (.cv z) (syn_cfv (syn_c1st) (.cv v)) (.cv x))
              (.classEq (.cv z) (.cv x))))))
      (.classMem (.cv v) (syn_chwcn A)) p0001 p0022
  have p0024 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv))
              (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wa
              (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v))
                (syn_wa (.classMem (.cv u) X) (syn_wbr (.cv u) (syn_chwniso A)
                    (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v))
                      (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))))
              (syn_wral z (syn_chncodepredends A X v)
                (.imp (syn_wbr (.cv z) (syn_cfv (syn_c1st) (.cv v)) (.cv x))
                  (.classEq (.cv z) (.cv x)))))) (.classMem (.cv y) X))
        (syn_wbr (.cv y) (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A)))
          (.cv u)))
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv))
            (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wa
            (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v))
              (syn_wa (.classMem (.cv u) X) (syn_wbr (.cv u) (syn_chwniso A)
                  (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v))
                    (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))))
            (syn_wral z (syn_chncodepredends A X v)
              (.imp (syn_wbr (.cv z) (syn_cfv (syn_c1st) (.cv v)) (.cv x))
                (.classEq (.cv z) (.cv x)))))) (.classMem (.cv y) X))
      (.classMem (.cv v) (syn_chwcn A)) p0000 p0023
  have p0025 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv))
              (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wa
              (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v))
                (syn_wa (.classMem (.cv u) X) (syn_wbr (.cv u) (syn_chwniso A)
                    (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v))
                      (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))))
              (syn_wral z (syn_chncodepredends A X v)
                (.imp (syn_wbr (.cv z) (syn_cfv (syn_c1st) (.cv v)) (.cv x))
                  (.classEq (.cv z) (.cv x)))))) (.classMem (.cv y) X))
        (syn_wbr (.cv y) (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A)))
          (.cv u)))
      (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)) p0017 p0024
  have p0031 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv))
            (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wa
            (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v))
              (syn_wa (.classMem (.cv u) X) (syn_wbr (.cv u) (syn_chwniso A)
                  (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v))
                    (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))))
            (syn_wral z (syn_chncodepredends A X v)
              (.imp (syn_wbr (.cv z) (syn_cfv (syn_c1st) (.cv v)) (.cv x))
                (.classEq (.cv z) (.cv x)))))) (.classMem (.cv y) X))
      (syn_wa (syn_wa (.classMem A (syn_cvv))
          (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wa
          (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v)) (syn_wa (.classMem (.cv u) X)
              (syn_wbr (.cv u) (syn_chwniso A)
                (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                  (.cv x))))) (syn_wral z (syn_chncodepredends A X v)
            (.imp (syn_wbr (.cv z) (syn_cfv (syn_c1st) (.cv v)) (.cv x))
              (.classEq (.cv z) (.cv x))))))
      (syn_wss X (syn_chwcn A)) p0001 p0010
  have p0032 :=
    @g_simpr
      (syn_wa (syn_wa (.classMem A (syn_cvv))
          (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wa
          (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v)) (syn_wa (.classMem (.cv u) X)
              (syn_wbr (.cv u) (syn_chwniso A)
                (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                  (.cv x))))) (syn_wral z (syn_chncodepredends A X v)
            (.imp (syn_wbr (.cv z) (syn_cfv (syn_c1st) (.cv v)) (.cv x))
              (.classEq (.cv z) (.cv x))))))
      (.classMem (.cv y) X)
  have p0033 :=
    @g_sseldd
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv))
            (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wa
            (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v))
              (syn_wa (.classMem (.cv u) X) (syn_wbr (.cv u) (syn_chwniso A)
                  (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v))
                    (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))))
            (syn_wral z (syn_chncodepredends A X v)
              (.imp (syn_wbr (.cv z) (syn_cfv (syn_c1st) (.cv v)) (.cv x))
                (.classEq (.cv z) (.cv x)))))) (.classMem (.cv y) X))
      X (syn_chwcn A) (.cv y) p0031 p0032
  have p0034 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv))
              (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wa
              (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v))
                (syn_wa (.classMem (.cv u) X) (syn_wbr (.cv u) (syn_chwniso A)
                    (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v))
                      (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))))
              (syn_wral z (syn_chncodepredends A X v)
                (.imp (syn_wbr (.cv z) (syn_cfv (syn_c1st) (.cv v)) (.cv x))
                  (.classEq (.cv z) (.cv x)))))) (.classMem (.cv y) X))
        (syn_wbr (.cv y) (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A)))
          (.cv u)))
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv))
            (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wa
            (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v))
              (syn_wa (.classMem (.cv u) X) (syn_wbr (.cv u) (syn_chwniso A)
                  (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v))
                    (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))))
            (syn_wral z (syn_chncodepredends A X v)
              (.imp (syn_wbr (.cv z) (syn_cfv (syn_c1st) (.cv v)) (.cv x))
                (.classEq (.cv z) (.cv x)))))) (.classMem (.cv y) X))
      (.classMem (.cv y) (syn_chwcn A)) p0000 p0033
  have p0035 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv))
              (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wa
              (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v))
                (syn_wa (.classMem (.cv u) X) (syn_wbr (.cv u) (syn_chwniso A)
                    (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v))
                      (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))))
              (syn_wral z (syn_chncodepredends A X v)
                (.imp (syn_wbr (.cv z) (syn_cfv (syn_c1st) (.cv v)) (.cv x))
                  (.classEq (.cv z) (.cv x)))))) (.classMem (.cv y) X))
        (syn_wbr (.cv y) (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A)))
          (.cv u)))
      (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
      (.classMem (.cv y) (syn_chwcn A)) p0025 p0034
  have p0036 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv))
              (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wa
              (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v))
                (syn_wa (.classMem (.cv u) X) (syn_wbr (.cv u) (syn_chwniso A)
                    (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v))
                      (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))))
              (syn_wral z (syn_chncodepredends A X v)
                (.imp (syn_wbr (.cv z) (syn_cfv (syn_c1st) (.cv v)) (.cv x))
                  (.classEq (.cv z) (.cv x)))))) (.classMem (.cv y) X))
        (syn_wbr (.cv y) (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A)))
          (.cv u)))
      (.classMem A (syn_cvv))
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (.classMem (.cv y) (syn_chwcn A)))
      p0005 p0035
  have p0042 := @g_hncodepredendsssndv v A X dv_cache_0001
  have p0043 :=
    @g_syl
      (syn_wa (syn_wa (.classMem A (syn_cvv))
          (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wa
          (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v)) (syn_wa (.classMem (.cv u) X)
              (syn_wbr (.cv u) (syn_chwniso A)
                (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                  (.cv x))))) (syn_wral z (syn_chncodepredends A X v)
            (.imp (syn_wbr (.cv z) (syn_cfv (syn_c1st) (.cv v)) (.cv x))
              (.classEq (.cv z) (.cv x))))))
      (.classMem (.cv v) (syn_chwcn A))
      (syn_wss (syn_chncodepredends A X v) (syn_cfv (syn_c2nd) (.cv v))) p0022 p0042
  have p0046 :=
    @g_simpld
      (syn_wa (syn_wa (.classMem A (syn_cvv))
          (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wa
          (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v)) (syn_wa (.classMem (.cv u) X)
              (syn_wbr (.cv u) (syn_chwniso A)
                (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                  (.cv x))))) (syn_wral z (syn_chncodepredends A X v)
            (.imp (syn_wbr (.cv z) (syn_cfv (syn_c1st) (.cv v)) (.cv x))
              (.classEq (.cv z) (.cv x))))))
      (.classMem (.cv x) (syn_chncodepredends A X v))
      (syn_wa (.classMem (.cv u) X) (syn_wbr (.cv u) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))
      p0012
  have p0047 :=
    @g_sseldd
      (syn_wa (syn_wa (.classMem A (syn_cvv))
          (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wa
          (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v)) (syn_wa (.classMem (.cv u) X)
              (syn_wbr (.cv u) (syn_chwniso A)
                (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                  (.cv x))))) (syn_wral z (syn_chncodepredends A X v)
            (.imp (syn_wbr (.cv z) (syn_cfv (syn_c1st) (.cv v)) (.cv x))
              (.classEq (.cv z) (.cv x))))))
      (syn_chncodepredends A X v) (syn_cfv (syn_c2nd) (.cv v)) (.cv x) p0043 p0046
  have p0048 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv))
            (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wa
            (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v))
              (syn_wa (.classMem (.cv u) X) (syn_wbr (.cv u) (syn_chwniso A)
                  (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v))
                    (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))))
            (syn_wral z (syn_chncodepredends A X v)
              (.imp (syn_wbr (.cv z) (syn_cfv (syn_c1st) (.cv v)) (.cv x))
                (.classEq (.cv z) (.cv x)))))) (.classMem (.cv y) X))
      (syn_wa (syn_wa (.classMem A (syn_cvv))
          (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wa
          (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v)) (syn_wa (.classMem (.cv u) X)
              (syn_wbr (.cv u) (syn_chwniso A)
                (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                  (.cv x))))) (syn_wral z (syn_chncodepredends A X v)
            (.imp (syn_wbr (.cv z) (syn_cfv (syn_c1st) (.cv v)) (.cv x))
              (.classEq (.cv z) (.cv x))))))
      (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) p0001 p0047
  have p0049 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv))
              (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wa
              (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v))
                (syn_wa (.classMem (.cv u) X) (syn_wbr (.cv u) (syn_chwniso A)
                    (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v))
                      (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))))
              (syn_wral z (syn_chncodepredends A X v)
                (.imp (syn_wbr (.cv z) (syn_cfv (syn_c1st) (.cv v)) (.cv x))
                  (.classEq (.cv z) (.cv x)))))) (.classMem (.cv y) X))
        (syn_wbr (.cv y) (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A)))
          (.cv u)))
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv))
            (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wa
            (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v))
              (syn_wa (.classMem (.cv u) X) (syn_wbr (.cv u) (syn_chwniso A)
                  (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v))
                    (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))))
            (syn_wral z (syn_chncodepredends A X v)
              (.imp (syn_wbr (.cv z) (syn_cfv (syn_c1st) (.cv v)) (.cv x))
                (.classEq (.cv z) (.cv x)))))) (.classMem (.cv y) X))
      (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) p0000 p0048
  have p0055 :=
    @g_simprd
      (syn_wa (syn_wa (.classMem A (syn_cvv))
          (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wa
          (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v)) (syn_wa (.classMem (.cv u) X)
              (syn_wbr (.cv u) (syn_chwniso A)
                (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                  (.cv x))))) (syn_wral z (syn_chncodepredends A X v)
            (.imp (syn_wbr (.cv z) (syn_cfv (syn_c1st) (.cv v)) (.cv x))
              (.classEq (.cv z) (.cv x))))))
      (.classMem (.cv u) X)
      (syn_wbr (.cv u) (syn_chwniso A)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))
      p0013
  have p0056 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv))
            (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wa
            (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v))
              (syn_wa (.classMem (.cv u) X) (syn_wbr (.cv u) (syn_chwniso A)
                  (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v))
                    (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))))
            (syn_wral z (syn_chncodepredends A X v)
              (.imp (syn_wbr (.cv z) (syn_cfv (syn_c1st) (.cv v)) (.cv x))
                (.classEq (.cv z) (.cv x)))))) (.classMem (.cv y) X))
      (syn_wa (syn_wa (.classMem A (syn_cvv))
          (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wa
          (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v)) (syn_wa (.classMem (.cv u) X)
              (syn_wbr (.cv u) (syn_chwniso A)
                (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                  (.cv x))))) (syn_wral z (syn_chncodepredends A X v)
            (.imp (syn_wbr (.cv z) (syn_cfv (syn_c1st) (.cv v)) (.cv x))
              (.classEq (.cv z) (.cv x))))))
      (syn_wbr (.cv u) (syn_chwniso A)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))
      p0001 p0055
  have p0057 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv))
              (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wa
              (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v))
                (syn_wa (.classMem (.cv u) X) (syn_wbr (.cv u) (syn_chwniso A)
                    (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v))
                      (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))))
              (syn_wral z (syn_chncodepredends A X v)
                (.imp (syn_wbr (.cv z) (syn_cfv (syn_c1st) (.cv v)) (.cv x))
                  (.classEq (.cv z) (.cv x)))))) (.classMem (.cv y) X))
        (syn_wbr (.cv y) (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A)))
          (.cv u)))
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv))
            (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wa
            (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v))
              (syn_wa (.classMem (.cv u) X) (syn_wbr (.cv u) (syn_chwniso A)
                  (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v))
                    (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))))
            (syn_wral z (syn_chncodepredends A X v)
              (.imp (syn_wbr (.cv z) (syn_cfv (syn_c1st) (.cv v)) (.cv x))
                (.classEq (.cv z) (.cv x)))))) (.classMem (.cv y) X))
      (syn_wbr (.cv u) (syn_chwniso A)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))
      p0000 p0056
  have p0058 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv))
              (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wa
              (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v))
                (syn_wa (.classMem (.cv u) X) (syn_wbr (.cv u) (syn_chwniso A)
                    (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v))
                      (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))))
              (syn_wral z (syn_chncodepredends A X v)
                (.imp (syn_wbr (.cv z) (syn_cfv (syn_c1st) (.cv v)) (.cv x))
                  (.classEq (.cv z) (.cv x)))))) (.classMem (.cv y) X))
        (syn_wbr (.cv y) (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A)))
          (.cv u)))
      (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
      (syn_wbr (.cv u) (syn_chwniso A)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))
      p0049 p0057
  have p0059 :=
    @g_simpr
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv))
            (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wa
            (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v))
              (syn_wa (.classMem (.cv u) X) (syn_wbr (.cv u) (syn_chwniso A)
                  (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v))
                    (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))))
            (syn_wral z (syn_chncodepredends A X v)
              (.imp (syn_wbr (.cv z) (syn_cfv (syn_c1st) (.cv v)) (.cv x))
                (.classEq (.cv z) (.cv x)))))) (.classMem (.cv y) X))
      (syn_wbr (.cv y) (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A)))
        (.cv u))
  have p0060 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv))
              (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wa
              (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v))
                (syn_wa (.classMem (.cv u) X) (syn_wbr (.cv u) (syn_chwniso A)
                    (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v))
                      (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))))
              (syn_wral z (syn_chncodepredends A X v)
                (.imp (syn_wbr (.cv z) (syn_cfv (syn_c1st) (.cv v)) (.cv x))
                  (.classEq (.cv z) (.cv x)))))) (.classMem (.cv y) X))
        (syn_wbr (.cv y) (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A)))
          (.cv u)))
      (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))
      (syn_wbr (.cv y) (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A)))
        (.cv u))
      p0058 p0059
  have p0061 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv))
              (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wa
              (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v))
                (syn_wa (.classMem (.cv u) X) (syn_wbr (.cv u) (syn_chwniso A)
                    (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v))
                      (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))))
              (syn_wral z (syn_chncodepredends A X v)
                (.imp (syn_wbr (.cv z) (syn_cfv (syn_c1st) (.cv v)) (.cv x))
                  (.classEq (.cv z) (.cv x)))))) (.classMem (.cv y) X))
        (syn_wbr (.cv y) (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A)))
          (.cv u)))
      (syn_wa (.classMem A (syn_cvv)) (syn_wa
          (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
          (.classMem (.cv y) (syn_chwcn A))))
      (syn_wa (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
          (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv x))))
        (syn_wbr (.cv y) (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A)))
          (.cv u)))
      p0036 p0060
  have p0062 :=
    @g_hncodepredstrictdescentndv x y t v u A dv_cache_0002 dv_cache_0001 dv_cache_0003
      dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
  have p0063 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv))
              (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wa
              (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v))
                (syn_wa (.classMem (.cv u) X) (syn_wbr (.cv u) (syn_chwniso A)
                    (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v))
                      (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))))
              (syn_wral z (syn_chncodepredends A X v)
                (.imp (syn_wbr (.cv z) (syn_cfv (syn_c1st) (.cv v)) (.cv x))
                  (.classEq (.cv z) (.cv x)))))) (.classMem (.cv y) X))
        (syn_wbr (.cv y) (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A)))
          (.cv u)))
      (syn_wa (syn_wa (.classMem A (syn_cvv)) (syn_wa
            (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
            (.classMem (.cv y) (syn_chwcn A)))) (syn_wa
          (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
            (syn_wbr (.cv u) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv x)))) (syn_wbr (.cv y)
            (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv u))))
      (syn_wrex t (syn_cin (syn_cfv (syn_c2nd) (.cv v))
          (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
            (syn_csn (.cv x)))) (syn_wbr (.cv y) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv t))))
      p0061 p0062
  have p0064 :=
    @g_simpr
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv))
              (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wa
              (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v))
                (syn_wa (.classMem (.cv u) X) (syn_wbr (.cv u) (syn_chwniso A)
                    (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v))
                      (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))))
              (syn_wral z (syn_chncodepredends A X v)
                (.imp (syn_wbr (.cv z) (syn_cfv (syn_c1st) (.cv v)) (.cv x))
                  (.classEq (.cv z) (.cv x)))))) (.classMem (.cv y) X))
        (syn_wbr (.cv y) (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A)))
          (.cv u)))
      (syn_wa (.classMem (.cv t) (syn_cin (syn_cfv (syn_c2nd) (.cv v))
            (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
              (syn_csn (.cv x))))) (syn_wbr (.cv y) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv t))))
  have p0065 :=
    @g_simpld
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv))
                (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wa
                (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v))
                  (syn_wa (.classMem (.cv u) X) (syn_wbr (.cv u) (syn_chwniso A)
                      (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v))
                        (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))))
                (syn_wral z (syn_chncodepredends A X v)
                  (.imp (syn_wbr (.cv z) (syn_cfv (syn_c1st) (.cv v)) (.cv x))
                    (.classEq (.cv z) (.cv x)))))) (.classMem (.cv y) X)) (syn_wbr (.cv y)
            (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv u))) (syn_wa
          (.classMem (.cv t) (syn_cin (syn_cfv (syn_c2nd) (.cv v))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
                (syn_csn (.cv x))))) (syn_wbr (.cv y) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv t)))))
      (.classMem (.cv t) (syn_cin (syn_cfv (syn_c2nd) (.cv v))
          (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
            (syn_csn (.cv x)))))
      (syn_wbr (.cv y) (syn_chwniso A)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv t)))
      p0064
  have p0066 :=
    @g_elstrictseg x t (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (syn_c1st) (.cv v))
  have p0067 :=
    @g_biimpi
      (.classMem (.cv t) (syn_cin (syn_cfv (syn_c2nd) (.cv v))
          (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
            (syn_csn (.cv x)))))
      (syn_wa (.classMem (.cv t) (syn_cfv (syn_c2nd) (.cv v)))
        (syn_wa (syn_wbr (.cv t) (syn_cfv (syn_c1st) (.cv v)) (.cv x))
          (syn_wne (.cv t) (.cv x))))
      p0066
  have p0068 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv))
                (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wa
                (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v))
                  (syn_wa (.classMem (.cv u) X) (syn_wbr (.cv u) (syn_chwniso A)
                      (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v))
                        (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))))
                (syn_wral z (syn_chncodepredends A X v)
                  (.imp (syn_wbr (.cv z) (syn_cfv (syn_c1st) (.cv v)) (.cv x))
                    (.classEq (.cv z) (.cv x)))))) (.classMem (.cv y) X)) (syn_wbr (.cv y)
            (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv u))) (syn_wa
          (.classMem (.cv t) (syn_cin (syn_cfv (syn_c2nd) (.cv v))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
                (syn_csn (.cv x))))) (syn_wbr (.cv y) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv t)))))
      (.classMem (.cv t) (syn_cin (syn_cfv (syn_c2nd) (.cv v))
          (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
            (syn_csn (.cv x)))))
      (syn_wa (.classMem (.cv t) (syn_cfv (syn_c2nd) (.cv v)))
        (syn_wa (syn_wbr (.cv t) (syn_cfv (syn_c1st) (.cv v)) (.cv x))
          (syn_wne (.cv t) (.cv x))))
      p0065 p0067
  have p0069 :=
    @g_simprd
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv))
                (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wa
                (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v))
                  (syn_wa (.classMem (.cv u) X) (syn_wbr (.cv u) (syn_chwniso A)
                      (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v))
                        (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))))
                (syn_wral z (syn_chncodepredends A X v)
                  (.imp (syn_wbr (.cv z) (syn_cfv (syn_c1st) (.cv v)) (.cv x))
                    (.classEq (.cv z) (.cv x)))))) (.classMem (.cv y) X)) (syn_wbr (.cv y)
            (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv u))) (syn_wa
          (.classMem (.cv t) (syn_cin (syn_cfv (syn_c2nd) (.cv v))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
                (syn_csn (.cv x))))) (syn_wbr (.cv y) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv t)))))
      (.classMem (.cv t) (syn_cfv (syn_c2nd) (.cv v)))
      (syn_wa (syn_wbr (.cv t) (syn_cfv (syn_c1st) (.cv v)) (.cv x)) (syn_wne (.cv t) (.cv x)))
      p0068
  have p0070 :=
    @g_simpld
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv))
                (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wa
                (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v))
                  (syn_wa (.classMem (.cv u) X) (syn_wbr (.cv u) (syn_chwniso A)
                      (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v))
                        (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))))
                (syn_wral z (syn_chncodepredends A X v)
                  (.imp (syn_wbr (.cv z) (syn_cfv (syn_c1st) (.cv v)) (.cv x))
                    (.classEq (.cv z) (.cv x)))))) (.classMem (.cv y) X)) (syn_wbr (.cv y)
            (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv u))) (syn_wa
          (.classMem (.cv t) (syn_cin (syn_cfv (syn_c2nd) (.cv v))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
                (syn_csn (.cv x))))) (syn_wbr (.cv y) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv t)))))
      (syn_wbr (.cv t) (syn_cfv (syn_c1st) (.cv v)) (.cv x)) (syn_wne (.cv t) (.cv x))
      p0069
  have p0071 :=
    @g_simpl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv))
              (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wa
              (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v))
                (syn_wa (.classMem (.cv u) X) (syn_wbr (.cv u) (syn_chwniso A)
                    (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v))
                      (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))))
              (syn_wral z (syn_chncodepredends A X v)
                (.imp (syn_wbr (.cv z) (syn_cfv (syn_c1st) (.cv v)) (.cv x))
                  (.classEq (.cv z) (.cv x)))))) (.classMem (.cv y) X))
        (syn_wbr (.cv y) (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A)))
          (.cv u)))
      (syn_wa (.classMem (.cv t) (syn_cin (syn_cfv (syn_c2nd) (.cv v))
            (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
              (syn_csn (.cv x))))) (syn_wbr (.cv y) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv t))))
  have p0075 :=
    @g_simprd
      (syn_wa (syn_wa (.classMem A (syn_cvv))
          (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wa
          (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v)) (syn_wa (.classMem (.cv u) X)
              (syn_wbr (.cv u) (syn_chwniso A)
                (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                  (.cv x))))) (syn_wral z (syn_chncodepredends A X v)
            (.imp (syn_wbr (.cv z) (syn_cfv (syn_c1st) (.cv v)) (.cv x))
              (.classEq (.cv z) (.cv x))))))
      (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v)) (syn_wa (.classMem (.cv u) X)
          (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv x)))))
      (syn_wral z (syn_chncodepredends A X v)
        (.imp (syn_wbr (.cv z) (syn_cfv (syn_c1st) (.cv v)) (.cv x))
          (.classEq (.cv z) (.cv x))))
      p0011
  have p0076 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv))
            (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wa
            (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v))
              (syn_wa (.classMem (.cv u) X) (syn_wbr (.cv u) (syn_chwniso A)
                  (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v))
                    (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))))
            (syn_wral z (syn_chncodepredends A X v)
              (.imp (syn_wbr (.cv z) (syn_cfv (syn_c1st) (.cv v)) (.cv x))
                (.classEq (.cv z) (.cv x)))))) (.classMem (.cv y) X))
      (syn_wa (syn_wa (.classMem A (syn_cvv))
          (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wa
          (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v)) (syn_wa (.classMem (.cv u) X)
              (syn_wbr (.cv u) (syn_chwniso A)
                (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                  (.cv x))))) (syn_wral z (syn_chncodepredends A X v)
            (.imp (syn_wbr (.cv z) (syn_cfv (syn_c1st) (.cv v)) (.cv x))
              (.classEq (.cv z) (.cv x))))))
      (syn_wral z (syn_chncodepredends A X v)
        (.imp (syn_wbr (.cv z) (syn_cfv (syn_c1st) (.cv v)) (.cv x))
          (.classEq (.cv z) (.cv x))))
      p0001 p0075
  have p0077 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv))
              (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wa
              (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v))
                (syn_wa (.classMem (.cv u) X) (syn_wbr (.cv u) (syn_chwniso A)
                    (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v))
                      (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))))
              (syn_wral z (syn_chncodepredends A X v)
                (.imp (syn_wbr (.cv z) (syn_cfv (syn_c1st) (.cv v)) (.cv x))
                  (.classEq (.cv z) (.cv x)))))) (.classMem (.cv y) X))
        (syn_wbr (.cv y) (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A)))
          (.cv u)))
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv))
            (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wa
            (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v))
              (syn_wa (.classMem (.cv u) X) (syn_wbr (.cv u) (syn_chwniso A)
                  (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v))
                    (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))))
            (syn_wral z (syn_chncodepredends A X v)
              (.imp (syn_wbr (.cv z) (syn_cfv (syn_c1st) (.cv v)) (.cv x))
                (.classEq (.cv z) (.cv x)))))) (.classMem (.cv y) X))
      (syn_wral z (syn_chncodepredends A X v)
        (.imp (syn_wbr (.cv z) (syn_cfv (syn_c1st) (.cv v)) (.cv x))
          (.classEq (.cv z) (.cv x))))
      p0000 p0076
  have p0078 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv))
                (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wa
                (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v))
                  (syn_wa (.classMem (.cv u) X) (syn_wbr (.cv u) (syn_chwniso A)
                      (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v))
                        (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))))
                (syn_wral z (syn_chncodepredends A X v)
                  (.imp (syn_wbr (.cv z) (syn_cfv (syn_c1st) (.cv v)) (.cv x))
                    (.classEq (.cv z) (.cv x)))))) (.classMem (.cv y) X)) (syn_wbr (.cv y)
            (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv u))) (syn_wa
          (.classMem (.cv t) (syn_cin (syn_cfv (syn_c2nd) (.cv v))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
                (syn_csn (.cv x))))) (syn_wbr (.cv y) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv t)))))
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv))
              (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wa
              (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v))
                (syn_wa (.classMem (.cv u) X) (syn_wbr (.cv u) (syn_chwniso A)
                    (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v))
                      (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))))
              (syn_wral z (syn_chncodepredends A X v)
                (.imp (syn_wbr (.cv z) (syn_cfv (syn_c1st) (.cv v)) (.cv x))
                  (.classEq (.cv z) (.cv x)))))) (.classMem (.cv y) X))
        (syn_wbr (.cv y) (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A)))
          (.cv u)))
      (syn_wral z (syn_chncodepredends A X v)
        (.imp (syn_wbr (.cv z) (syn_cfv (syn_c1st) (.cv v)) (.cv x))
          (.classEq (.cv z) (.cv x))))
      p0071 p0077
  have p0084 :=
    @g_simpld
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv))
                (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wa
                (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v))
                  (syn_wa (.classMem (.cv u) X) (syn_wbr (.cv u) (syn_chwniso A)
                      (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v))
                        (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))))
                (syn_wral z (syn_chncodepredends A X v)
                  (.imp (syn_wbr (.cv z) (syn_cfv (syn_c1st) (.cv v)) (.cv x))
                    (.classEq (.cv z) (.cv x)))))) (.classMem (.cv y) X)) (syn_wbr (.cv y)
            (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv u))) (syn_wa
          (.classMem (.cv t) (syn_cin (syn_cfv (syn_c2nd) (.cv v))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
                (syn_csn (.cv x))))) (syn_wbr (.cv y) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv t)))))
      (.classMem (.cv t) (syn_cfv (syn_c2nd) (.cv v)))
      (syn_wa (syn_wbr (.cv t) (syn_cfv (syn_c1st) (.cv v)) (.cv x)) (syn_wne (.cv t) (.cv x)))
      p0068
  have p0088 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv))
              (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wa
              (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v))
                (syn_wa (.classMem (.cv u) X) (syn_wbr (.cv u) (syn_chwniso A)
                    (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v))
                      (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))))
              (syn_wral z (syn_chncodepredends A X v)
                (.imp (syn_wbr (.cv z) (syn_cfv (syn_c1st) (.cv v)) (.cv x))
                  (.classEq (.cv z) (.cv x)))))) (.classMem (.cv y) X))
        (syn_wbr (.cv y) (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A)))
          (.cv u)))
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv))
            (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wa
            (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v))
              (syn_wa (.classMem (.cv u) X) (syn_wbr (.cv u) (syn_chwniso A)
                  (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v))
                    (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))))
            (syn_wral z (syn_chncodepredends A X v)
              (.imp (syn_wbr (.cv z) (syn_cfv (syn_c1st) (.cv v)) (.cv x))
                (.classEq (.cv z) (.cv x)))))) (.classMem (.cv y) X))
      (.classMem (.cv y) X) p0000 p0032
  have p0089 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv))
                (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wa
                (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v))
                  (syn_wa (.classMem (.cv u) X) (syn_wbr (.cv u) (syn_chwniso A)
                      (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v))
                        (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))))
                (syn_wral z (syn_chncodepredends A X v)
                  (.imp (syn_wbr (.cv z) (syn_cfv (syn_c1st) (.cv v)) (.cv x))
                    (.classEq (.cv z) (.cv x)))))) (.classMem (.cv y) X)) (syn_wbr (.cv y)
            (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv u))) (syn_wa
          (.classMem (.cv t) (syn_cin (syn_cfv (syn_c2nd) (.cv v))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
                (syn_csn (.cv x))))) (syn_wbr (.cv y) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv t)))))
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv))
              (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wa
              (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v))
                (syn_wa (.classMem (.cv u) X) (syn_wbr (.cv u) (syn_chwniso A)
                    (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v))
                      (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))))
              (syn_wral z (syn_chncodepredends A X v)
                (.imp (syn_wbr (.cv z) (syn_cfv (syn_c1st) (.cv v)) (.cv x))
                  (.classEq (.cv z) (.cv x)))))) (.classMem (.cv y) X))
        (syn_wbr (.cv y) (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A)))
          (.cv u)))
      (.classMem (.cv y) X) p0071 p0088
  have p0091 :=
    @g_simprd
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv))
                (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wa
                (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v))
                  (syn_wa (.classMem (.cv u) X) (syn_wbr (.cv u) (syn_chwniso A)
                      (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v))
                        (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))))
                (syn_wral z (syn_chncodepredends A X v)
                  (.imp (syn_wbr (.cv z) (syn_cfv (syn_c1st) (.cv v)) (.cv x))
                    (.classEq (.cv z) (.cv x)))))) (.classMem (.cv y) X)) (syn_wbr (.cv y)
            (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv u))) (syn_wa
          (.classMem (.cv t) (syn_cin (syn_cfv (syn_c2nd) (.cv v))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
                (syn_csn (.cv x))))) (syn_wbr (.cv y) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv t)))))
      (.classMem (.cv t) (syn_cin (syn_cfv (syn_c2nd) (.cv v))
          (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
            (syn_csn (.cv x)))))
      (syn_wbr (.cv y) (syn_chwniso A)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv t)))
      p0064
  have p0092 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv))
                (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wa
                (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v))
                  (syn_wa (.classMem (.cv u) X) (syn_wbr (.cv u) (syn_chwniso A)
                      (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v))
                        (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))))
                (syn_wral z (syn_chncodepredends A X v)
                  (.imp (syn_wbr (.cv z) (syn_cfv (syn_c1st) (.cv v)) (.cv x))
                    (.classEq (.cv z) (.cv x)))))) (.classMem (.cv y) X)) (syn_wbr (.cv y)
            (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv u))) (syn_wa
          (.classMem (.cv t) (syn_cin (syn_cfv (syn_c2nd) (.cv v))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
                (syn_csn (.cv x))))) (syn_wbr (.cv y) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv t)))))
      (.classMem (.cv y) X)
      (syn_wbr (.cv y) (syn_chwniso A)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv t)))
      p0089 p0091
  have p0093 :=
    @g_breq1 (.cv a) (.cv y)
      (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv t))
      (syn_chwniso A)
  have p0094 :=
    @g_rspcev
      (syn_wbr (.cv a) (syn_chwniso A)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv t)))
      (syn_wbr (.cv y) (syn_chwniso A)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv t)))
      a (.cv y) X dv_cache_0010 dv_cache_0011 dv_cache_0012 p0093
  have p0095 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv))
                (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wa
                (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v))
                  (syn_wa (.classMem (.cv u) X) (syn_wbr (.cv u) (syn_chwniso A)
                      (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v))
                        (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))))
                (syn_wral z (syn_chncodepredends A X v)
                  (.imp (syn_wbr (.cv z) (syn_cfv (syn_c1st) (.cv v)) (.cv x))
                    (.classEq (.cv z) (.cv x)))))) (.classMem (.cv y) X)) (syn_wbr (.cv y)
            (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv u))) (syn_wa
          (.classMem (.cv t) (syn_cin (syn_cfv (syn_c2nd) (.cv v))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
                (syn_csn (.cv x))))) (syn_wbr (.cv y) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv t)))))
      (syn_wa (.classMem (.cv y) X) (syn_wbr (.cv y) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv t))))
      (syn_wrex a X (syn_wbr (.cv a) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv t))))
      p0092 p0094
  have p0096 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv))
                (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wa
                (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v))
                  (syn_wa (.classMem (.cv u) X) (syn_wbr (.cv u) (syn_chwniso A)
                      (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v))
                        (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))))
                (syn_wral z (syn_chncodepredends A X v)
                  (.imp (syn_wbr (.cv z) (syn_cfv (syn_c1st) (.cv v)) (.cv x))
                    (.classEq (.cv z) (.cv x)))))) (.classMem (.cv y) X)) (syn_wbr (.cv y)
            (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv u))) (syn_wa
          (.classMem (.cv t) (syn_cin (syn_cfv (syn_c2nd) (.cv v))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
                (syn_csn (.cv x))))) (syn_wbr (.cv y) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv t)))))
      (.classMem (.cv t) (syn_cfv (syn_c2nd) (.cv v)))
      (syn_wrex a X (syn_wbr (.cv a) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv t))))
      p0084 p0095
  have p0105 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv))
                (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wa
                (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v))
                  (syn_wa (.classMem (.cv u) X) (syn_wbr (.cv u) (syn_chwniso A)
                      (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v))
                        (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))))
                (syn_wral z (syn_chncodepredends A X v)
                  (.imp (syn_wbr (.cv z) (syn_cfv (syn_c1st) (.cv v)) (.cv x))
                    (.classEq (.cv z) (.cv x)))))) (.classMem (.cv y) X)) (syn_wbr (.cv y)
            (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv u))) (syn_wa
          (.classMem (.cv t) (syn_cin (syn_cfv (syn_c2nd) (.cv v))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
                (syn_csn (.cv x))))) (syn_wbr (.cv y) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv t)))))
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv))
              (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wa
              (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v))
                (syn_wa (.classMem (.cv u) X) (syn_wbr (.cv u) (syn_chwniso A)
                    (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v))
                      (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))))
              (syn_wral z (syn_chncodepredends A X v)
                (.imp (syn_wbr (.cv z) (syn_cfv (syn_c1st) (.cv v)) (.cv x))
                  (.classEq (.cv z) (.cv x)))))) (.classMem (.cv y) X))
        (syn_wbr (.cv y) (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A)))
          (.cv u)))
      (.classMem (.cv v) (syn_chwcn A)) p0071 p0024
  have p0106 :=
    @g_hncodepredendsmemndv t v a A X dv_cache_0013 dv_cache_0001 dv_cache_0011
      dv_cache_0014 dv_cache_0015
  have p0107 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv))
                (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wa
                (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v))
                  (syn_wa (.classMem (.cv u) X) (syn_wbr (.cv u) (syn_chwniso A)
                      (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v))
                        (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))))
                (syn_wral z (syn_chncodepredends A X v)
                  (.imp (syn_wbr (.cv z) (syn_cfv (syn_c1st) (.cv v)) (.cv x))
                    (.classEq (.cv z) (.cv x)))))) (.classMem (.cv y) X)) (syn_wbr (.cv y)
            (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv u))) (syn_wa
          (.classMem (.cv t) (syn_cin (syn_cfv (syn_c2nd) (.cv v))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
                (syn_csn (.cv x))))) (syn_wbr (.cv y) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv t)))))
      (.classMem (.cv v) (syn_chwcn A))
      (syn_wb (.classMem (.cv t) (syn_chncodepredends A X v))
        (syn_wa (.classMem (.cv t) (syn_cfv (syn_c2nd) (.cv v))) (syn_wrex a X
            (syn_wbr (.cv a) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv t))))))
      p0105 p0106
  have p0108 :=
    @g_mpbird
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv))
                (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wa
                (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v))
                  (syn_wa (.classMem (.cv u) X) (syn_wbr (.cv u) (syn_chwniso A)
                      (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v))
                        (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))))
                (syn_wral z (syn_chncodepredends A X v)
                  (.imp (syn_wbr (.cv z) (syn_cfv (syn_c1st) (.cv v)) (.cv x))
                    (.classEq (.cv z) (.cv x)))))) (.classMem (.cv y) X)) (syn_wbr (.cv y)
            (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv u))) (syn_wa
          (.classMem (.cv t) (syn_cin (syn_cfv (syn_c2nd) (.cv v))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
                (syn_csn (.cv x))))) (syn_wbr (.cv y) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv t)))))
      (.classMem (.cv t) (syn_chncodepredends A X v))
      (syn_wa (.classMem (.cv t) (syn_cfv (syn_c2nd) (.cv v))) (syn_wrex a X
          (syn_wbr (.cv a) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv t)))))
      p0096 p0107
  have p0109 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv))
                (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wa
                (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v))
                  (syn_wa (.classMem (.cv u) X) (syn_wbr (.cv u) (syn_chwniso A)
                      (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v))
                        (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))))
                (syn_wral z (syn_chncodepredends A X v)
                  (.imp (syn_wbr (.cv z) (syn_cfv (syn_c1st) (.cv v)) (.cv x))
                    (.classEq (.cv z) (.cv x)))))) (.classMem (.cv y) X)) (syn_wbr (.cv y)
            (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv u))) (syn_wa
          (.classMem (.cv t) (syn_cin (syn_cfv (syn_c2nd) (.cv v))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
                (syn_csn (.cv x))))) (syn_wbr (.cv y) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv t)))))
      (syn_wral z (syn_chncodepredends A X v)
        (.imp (syn_wbr (.cv z) (syn_cfv (syn_c1st) (.cv v)) (.cv x))
          (.classEq (.cv z) (.cv x))))
      (.classMem (.cv t) (syn_chncodepredends A X v)) p0078 p0108
  have p0110 := @g_breq1 (.cv z) (.cv t) (.cv x) (syn_cfv (syn_c1st) (.cv v))
  have p0111 := @g_eqeq1 (.cv z) (.cv t) (.cv x)
  have p0112 :=
    @g_imbi12d (.classEq (.cv z) (.cv t))
      (syn_wbr (.cv z) (syn_cfv (syn_c1st) (.cv v)) (.cv x))
      (syn_wbr (.cv t) (syn_cfv (syn_c1st) (.cv v)) (.cv x)) (.classEq (.cv z) (.cv x))
      (.classEq (.cv t) (.cv x)) p0110 p0111
  have p0113 :=
    @g_rspccva
      (.imp (syn_wbr (.cv z) (syn_cfv (syn_c1st) (.cv v)) (.cv x)) (.classEq (.cv z) (.cv x)))
      (.imp (syn_wbr (.cv t) (syn_cfv (syn_c1st) (.cv v)) (.cv x)) (.classEq (.cv t) (.cv x)))
      z (.cv t) (syn_chncodepredends A X v) dv_cache_0016 dv_cache_0017 dv_cache_0018
      p0112
  have p0114 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv))
                (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wa
                (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v))
                  (syn_wa (.classMem (.cv u) X) (syn_wbr (.cv u) (syn_chwniso A)
                      (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v))
                        (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))))
                (syn_wral z (syn_chncodepredends A X v)
                  (.imp (syn_wbr (.cv z) (syn_cfv (syn_c1st) (.cv v)) (.cv x))
                    (.classEq (.cv z) (.cv x)))))) (.classMem (.cv y) X)) (syn_wbr (.cv y)
            (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv u))) (syn_wa
          (.classMem (.cv t) (syn_cin (syn_cfv (syn_c2nd) (.cv v))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
                (syn_csn (.cv x))))) (syn_wbr (.cv y) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv t)))))
      (syn_wa (syn_wral z (syn_chncodepredends A X v)
          (.imp (syn_wbr (.cv z) (syn_cfv (syn_c1st) (.cv v)) (.cv x))
            (.classEq (.cv z) (.cv x)))) (.classMem (.cv t) (syn_chncodepredends A X v)))
      (.imp (syn_wbr (.cv t) (syn_cfv (syn_c1st) (.cv v)) (.cv x)) (.classEq (.cv t) (.cv x)))
      p0109 p0113
  have p0115 :=
    @g_mpd
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv))
                (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wa
                (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v))
                  (syn_wa (.classMem (.cv u) X) (syn_wbr (.cv u) (syn_chwniso A)
                      (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v))
                        (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))))
                (syn_wral z (syn_chncodepredends A X v)
                  (.imp (syn_wbr (.cv z) (syn_cfv (syn_c1st) (.cv v)) (.cv x))
                    (.classEq (.cv z) (.cv x)))))) (.classMem (.cv y) X)) (syn_wbr (.cv y)
            (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv u))) (syn_wa
          (.classMem (.cv t) (syn_cin (syn_cfv (syn_c2nd) (.cv v))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
                (syn_csn (.cv x))))) (syn_wbr (.cv y) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv t)))))
      (syn_wbr (.cv t) (syn_cfv (syn_c1st) (.cv v)) (.cv x)) (.classEq (.cv t) (.cv x))
      p0070 p0114
  have p0122 :=
    @g_simprd
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv))
                (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wa
                (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v))
                  (syn_wa (.classMem (.cv u) X) (syn_wbr (.cv u) (syn_chwniso A)
                      (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v))
                        (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))))
                (syn_wral z (syn_chncodepredends A X v)
                  (.imp (syn_wbr (.cv z) (syn_cfv (syn_c1st) (.cv v)) (.cv x))
                    (.classEq (.cv z) (.cv x)))))) (.classMem (.cv y) X)) (syn_wbr (.cv y)
            (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv u))) (syn_wa
          (.classMem (.cv t) (syn_cin (syn_cfv (syn_c2nd) (.cv v))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
                (syn_csn (.cv x))))) (syn_wbr (.cv y) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv t)))))
      (syn_wbr (.cv t) (syn_cfv (syn_c1st) (.cv v)) (.cv x)) (syn_wne (.cv t) (.cv x))
      p0069
  have p0123 :=
    @g_pm2_21ddne
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv))
                (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wa
                (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v))
                  (syn_wa (.classMem (.cv u) X) (syn_wbr (.cv u) (syn_chwniso A)
                      (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v))
                        (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))))
                (syn_wral z (syn_chncodepredends A X v)
                  (.imp (syn_wbr (.cv z) (syn_cfv (syn_c1st) (.cv v)) (.cv x))
                    (.classEq (.cv z) (.cv x)))))) (.classMem (.cv y) X)) (syn_wbr (.cv y)
            (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv u))) (syn_wa
          (.classMem (.cv t) (syn_cin (syn_cfv (syn_c2nd) (.cv v))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
                (syn_csn (.cv x))))) (syn_wbr (.cv y) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv t)))))
      (.classEq (.cv y) (.cv u)) (.cv t) (.cv x) p0115 p0122
  have p0124 :=
    @g_rexlimddv
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv))
              (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wa
              (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v))
                (syn_wa (.classMem (.cv u) X) (syn_wbr (.cv u) (syn_chwniso A)
                    (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v))
                      (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))))
              (syn_wral z (syn_chncodepredends A X v)
                (.imp (syn_wbr (.cv z) (syn_cfv (syn_c1st) (.cv v)) (.cv x))
                  (.classEq (.cv z) (.cv x)))))) (.classMem (.cv y) X))
        (syn_wbr (.cv y) (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A)))
          (.cv u)))
      (syn_wbr (.cv y) (syn_chwniso A)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv t)))
      (.classEq (.cv y) (.cv u)) t
      (syn_cin (syn_cfv (syn_c2nd) (.cv v))
        (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
          (syn_csn (.cv x))))
      dv_cache_0019 dv_cache_0020 p0063 p0123
  have p0125 :=
    @g_ex
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv))
            (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wa
            (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v))
              (syn_wa (.classMem (.cv u) X) (syn_wbr (.cv u) (syn_chwniso A)
                  (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v))
                    (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))))
            (syn_wral z (syn_chncodepredends A X v)
              (.imp (syn_wbr (.cv z) (syn_cfv (syn_c1st) (.cv v)) (.cv x))
                (.classEq (.cv z) (.cv x)))))) (.classMem (.cv y) X))
      (syn_wbr (.cv y) (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A)))
        (.cv u))
      (.classEq (.cv y) (.cv u)) p0124
  have p0126 :=
    @g_ralrimiva
      (syn_wa (syn_wa (.classMem A (syn_cvv))
          (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wa
          (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v)) (syn_wa (.classMem (.cv u) X)
              (syn_wbr (.cv u) (syn_chwniso A)
                (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                  (.cv x))))) (syn_wral z (syn_chncodepredends A X v)
            (.imp (syn_wbr (.cv z) (syn_cfv (syn_c1st) (.cv v)) (.cv x))
              (.classEq (.cv z) (.cv x))))))
      (.imp (syn_wbr (.cv y) (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A)))
          (.cv u)) (.classEq (.cv y) (.cv u)))
      y X dv_cache_0021 p0125
  exact p0126


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk017Compact001Part045`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_hncodepredemptyminimalndv (y : Var) (v : Var) (A : Class) (X : Class)
    (dv_A_v : v ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_X_y : y ∉ X.fv) (dv_v_y : v ≠ y) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wa (.classMem A (syn_cvv))
            (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X)))
          (.classEq (syn_chncodepredends A X v) (syn_c0))) (syn_wral y X (.imp (syn_wbr (.cv y)
              (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv v))
            (.classEq (.cv y) (.cv v))))) :=
  by
  let proofSupport : Finset Var :=
    ({ y } : Finset Var) ∪ ({ v } : Finset Var) ∪ A.fv ∪ X.fv
  let t : Var := freshVar proofSupport 0
  let a : Var := freshVar proofSupport 1
  have fresh_t : t ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_t_ne_y : t ≠ y := by
    intro h
    exact
      fresh_t
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_y_ne_t : y ≠ t := Ne.symm fresh_t_ne_y
  have fresh_t_ne_v : t ≠ v := by
    intro h
    exact
      fresh_t
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_v_ne_t : v ≠ t := Ne.symm fresh_t_ne_v
  have fresh_t_not_A : t ∉ A.fv := by
    intro h
    exact fresh_t (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_t_not_X : t ∉ X.fv := by
    intro h
    exact fresh_t (Finset.mem_union_right _ (h))
  have fresh_a : a ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_a_ne_y : a ≠ y := by
    intro h
    exact
      fresh_a
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_a_ne_v : a ≠ v := by
    intro h
    exact
      fresh_a
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_a_not_A : a ∉ A.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_a_not_X : a ∉ X.fv := by
    intro h
    exact fresh_a (Finset.mem_union_right _ (h))
  have fresh_t_ne_a : t ≠ a :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_a_ne_t : a ≠ t := Ne.symm fresh_t_ne_a
  have dv_cache_0001 : y ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_y, not_false_eq_true])
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
  have dv_cache_0003 : t ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_t_not_A, not_false_eq_true])
  have dv_cache_0004 : y ≠ v :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show y ≠ v from (by exact Ne.symm dv_v_y))
  have dv_cache_0005 : y ≠ t :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show y ≠ t from (by exact fresh_y_ne_t))
  have dv_cache_0006 : v ≠ t :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show v ≠ t from (by exact fresh_v_ne_t))
  have dv_cache_0007 : a ∉ ((Class.cv y)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_a_ne_y, not_false_eq_true])
  have dv_cache_0008 : a ∉ (X).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_a_not_X, not_false_eq_true])
  have dv_cache_0009 :
    a ∉
      ((syn_wbr (.cv y) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
            (.cv t)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutcode,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union,
          Finset.mem_singleton, fresh_a_ne_y, fresh_a_ne_t, fresh_a_ne_v, fresh_a_not_A,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0010 : a ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_a_not_A, not_false_eq_true])
  have dv_cache_0011 : a ≠ v :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (show a ≠ v from (by exact fresh_a_ne_v))
  have dv_cache_0012 : a ≠ t :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (show a ≠ t from (by exact fresh_a_ne_t))
  have dv_cache_0013 : t ∉ ((Wff.classEq (.cv y) (.cv v))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_t_ne_y, fresh_t_ne_v, or_false, not_false_eq_true])
  have dv_cache_0014 :
    t ∉
      ((syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv))
                (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X)))
              (.classEq (syn_chncodepredends A X v) (syn_c0))) (.classMem (.cv y) X))
          (syn_wbr (.cv y) (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A)))
            (.cv v)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodepredends,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodecmpset,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, Finset.mem_union,
          Finset.mem_singleton, fresh_t_not_A, fresh_t_not_X, fresh_t_ne_v, fresh_t_ne_y,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0015 :
    y ∉
      ((syn_wa (syn_wa (.classMem A (syn_cvv))
            (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X)))
          (.classEq (syn_chncodepredends A X v) (syn_c0)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodepredends,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union,
          Finset.mem_singleton, dv_A_y, dv_X_y, (Ne.symm dv_v_y),
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have p0000 :=
    @g_simpr
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv))
            (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X)))
          (.classEq (syn_chncodepredends A X v) (syn_c0))) (.classMem (.cv y) X))
      (syn_wbr (.cv y) (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A)))
        (.cv v))
  have p0001 :=
    @g_simpl
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv))
            (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X)))
          (.classEq (syn_chncodepredends A X v) (syn_c0))) (.classMem (.cv y) X))
      (syn_wbr (.cv y) (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A)))
        (.cv v))
  have p0002 :=
    @g_simpl
      (syn_wa (syn_wa (.classMem A (syn_cvv))
          (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X)))
        (.classEq (syn_chncodepredends A X v) (syn_c0)))
      (.classMem (.cv y) X)
  have p0003 :=
    @g_simpl
      (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X)))
      (.classEq (syn_chncodepredends A X v) (syn_c0))
  have p0004 :=
    @g_simpld
      (syn_wa (syn_wa (.classMem A (syn_cvv))
          (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X)))
        (.classEq (syn_chncodepredends A X v) (syn_c0)))
      (.classMem A (syn_cvv)) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))
      p0003
  have p0005 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv))
            (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X)))
          (.classEq (syn_chncodepredends A X v) (syn_c0))) (.classMem (.cv y) X))
      (syn_wa (syn_wa (.classMem A (syn_cvv))
          (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X)))
        (.classEq (syn_chncodepredends A X v) (syn_c0)))
      (.classMem A (syn_cvv)) p0002 p0004
  have p0006 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv))
              (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X)))
            (.classEq (syn_chncodepredends A X v) (syn_c0))) (.classMem (.cv y) X))
        (syn_wbr (.cv y) (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A)))
          (.cv v)))
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv))
            (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X)))
          (.classEq (syn_chncodepredends A X v) (syn_c0))) (.classMem (.cv y) X))
      (.classMem A (syn_cvv)) p0001 p0005
  have p0010 :=
    @g_simprd
      (syn_wa (syn_wa (.classMem A (syn_cvv))
          (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X)))
        (.classEq (syn_chncodepredends A X v) (syn_c0)))
      (.classMem A (syn_cvv)) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X))
      p0003
  have p0011 :=
    @g_simpld
      (syn_wa (syn_wa (.classMem A (syn_cvv))
          (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X)))
        (.classEq (syn_chncodepredends A X v) (syn_c0)))
      (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X) p0010
  have p0012 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv))
            (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X)))
          (.classEq (syn_chncodepredends A X v) (syn_c0))) (.classMem (.cv y) X))
      (syn_wa (syn_wa (.classMem A (syn_cvv))
          (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X)))
        (.classEq (syn_chncodepredends A X v) (syn_c0)))
      (syn_wss X (syn_chwcn A)) p0002 p0011
  have p0013 :=
    @g_simpr
      (syn_wa (syn_wa (.classMem A (syn_cvv))
          (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X)))
        (.classEq (syn_chncodepredends A X v) (syn_c0)))
      (.classMem (.cv y) X)
  have p0014 :=
    @g_sseldd
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv))
            (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X)))
          (.classEq (syn_chncodepredends A X v) (syn_c0))) (.classMem (.cv y) X))
      X (syn_chwcn A) (.cv y) p0012 p0013
  have p0015 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv))
              (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X)))
            (.classEq (syn_chncodepredends A X v) (syn_c0))) (.classMem (.cv y) X))
        (syn_wbr (.cv y) (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A)))
          (.cv v)))
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv))
            (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X)))
          (.classEq (syn_chncodepredends A X v) (syn_c0))) (.classMem (.cv y) X))
      (.classMem (.cv y) (syn_chwcn A)) p0001 p0014
  have p0023 :=
    @g_simprd
      (syn_wa (syn_wa (.classMem A (syn_cvv))
          (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X)))
        (.classEq (syn_chncodepredends A X v) (syn_c0)))
      (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X) p0010
  have p0024 :=
    @g_sseldd
      (syn_wa (syn_wa (.classMem A (syn_cvv))
          (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X)))
        (.classEq (syn_chncodepredends A X v) (syn_c0)))
      X (syn_chwcn A) (.cv v) p0011 p0023
  have p0025 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv))
            (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X)))
          (.classEq (syn_chncodepredends A X v) (syn_c0))) (.classMem (.cv y) X))
      (syn_wa (syn_wa (.classMem A (syn_cvv))
          (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X)))
        (.classEq (syn_chncodepredends A X v) (syn_c0)))
      (.classMem (.cv v) (syn_chwcn A)) p0002 p0024
  have p0026 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv))
              (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X)))
            (.classEq (syn_chncodepredends A X v) (syn_c0))) (.classMem (.cv y) X))
        (syn_wbr (.cv y) (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A)))
          (.cv v)))
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv))
            (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X)))
          (.classEq (syn_chncodepredends A X v) (syn_c0))) (.classMem (.cv y) X))
      (.classMem (.cv v) (syn_chwcn A)) p0001 p0025
  have p0027 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv))
              (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X)))
            (.classEq (syn_chncodepredends A X v) (syn_c0))) (.classMem (.cv y) X))
        (syn_wbr (.cv y) (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A)))
          (.cv v)))
      (.classMem (.cv y) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)) p0015 p0026
  have p0028 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv))
              (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X)))
            (.classEq (syn_chncodepredends A X v) (syn_c0))) (.classMem (.cv y) X))
        (syn_wbr (.cv y) (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A)))
          (.cv v)))
      (.classMem A (syn_cvv))
      (syn_wa (.classMem (.cv y) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) p0006
      p0027
  have p0029 :=
    @g_hncodecmpstrictbrndv t v y A dv_cache_0001 dv_cache_0002 dv_cache_0003
      dv_cache_0004 dv_cache_0005 dv_cache_0006
  have p0030 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv))
              (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X)))
            (.classEq (syn_chncodepredends A X v) (syn_c0))) (.classMem (.cv y) X))
        (syn_wbr (.cv y) (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A)))
          (.cv v)))
      (syn_wa (.classMem A (syn_cvv))
        (syn_wa (.classMem (.cv y) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
      (syn_wb (syn_wbr (.cv y) (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A)))
          (.cv v)) (syn_wrex t (syn_cfv (syn_c2nd) (.cv v)) (syn_wbr (.cv y) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv t)))))
      p0028 p0029
  have p0031 :=
    @g_mpbid
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv))
              (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X)))
            (.classEq (syn_chncodepredends A X v) (syn_c0))) (.classMem (.cv y) X))
        (syn_wbr (.cv y) (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A)))
          (.cv v)))
      (syn_wbr (.cv y) (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A)))
        (.cv v))
      (syn_wrex t (syn_cfv (syn_c2nd) (.cv v)) (syn_wbr (.cv y) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv t))))
      p0000 p0030
  have p0032 :=
    @g_simpl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv))
              (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X)))
            (.classEq (syn_chncodepredends A X v) (syn_c0))) (.classMem (.cv y) X))
        (syn_wbr (.cv y) (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A)))
          (.cv v)))
      (syn_wa (.classMem (.cv t) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv y) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv t))))
  have p0035 :=
    @g_simpr
      (syn_wa (.classMem A (syn_cvv)) (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X)))
      (.classEq (syn_chncodepredends A X v) (syn_c0))
  have p0036 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv))
            (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X)))
          (.classEq (syn_chncodepredends A X v) (syn_c0))) (.classMem (.cv y) X))
      (syn_wa (syn_wa (.classMem A (syn_cvv))
          (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X)))
        (.classEq (syn_chncodepredends A X v) (syn_c0)))
      (.classEq (syn_chncodepredends A X v) (syn_c0)) p0002 p0035
  have p0037 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv))
              (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X)))
            (.classEq (syn_chncodepredends A X v) (syn_c0))) (.classMem (.cv y) X))
        (syn_wbr (.cv y) (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A)))
          (.cv v)))
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv))
            (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X)))
          (.classEq (syn_chncodepredends A X v) (syn_c0))) (.classMem (.cv y) X))
      (.classEq (syn_chncodepredends A X v) (syn_c0)) p0001 p0036
  have p0038 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv))
                (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X)))
              (.classEq (syn_chncodepredends A X v) (syn_c0))) (.classMem (.cv y) X))
          (syn_wbr (.cv y)
            (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv v)))
        (syn_wa (.classMem (.cv t) (syn_cfv (syn_c2nd) (.cv v)))
          (syn_wbr (.cv y) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv t)))))
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv))
              (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X)))
            (.classEq (syn_chncodepredends A X v) (syn_c0))) (.classMem (.cv y) X))
        (syn_wbr (.cv y) (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A)))
          (.cv v)))
      (.classEq (syn_chncodepredends A X v) (syn_c0)) p0032 p0037
  have p0039 :=
    @g_simpr
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv))
              (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X)))
            (.classEq (syn_chncodepredends A X v) (syn_c0))) (.classMem (.cv y) X))
        (syn_wbr (.cv y) (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A)))
          (.cv v)))
      (syn_wa (.classMem (.cv t) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv y) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv t))))
  have p0040 :=
    @g_simpld
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv))
                (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X)))
              (.classEq (syn_chncodepredends A X v) (syn_c0))) (.classMem (.cv y) X))
          (syn_wbr (.cv y)
            (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv v)))
        (syn_wa (.classMem (.cv t) (syn_cfv (syn_c2nd) (.cv v)))
          (syn_wbr (.cv y) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv t)))))
      (.classMem (.cv t) (syn_cfv (syn_c2nd) (.cv v)))
      (syn_wbr (.cv y) (syn_chwniso A)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv t)))
      p0039
  have p0044 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv))
              (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X)))
            (.classEq (syn_chncodepredends A X v) (syn_c0))) (.classMem (.cv y) X))
        (syn_wbr (.cv y) (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A)))
          (.cv v)))
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv))
            (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X)))
          (.classEq (syn_chncodepredends A X v) (syn_c0))) (.classMem (.cv y) X))
      (.classMem (.cv y) X) p0001 p0013
  have p0045 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv))
                (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X)))
              (.classEq (syn_chncodepredends A X v) (syn_c0))) (.classMem (.cv y) X))
          (syn_wbr (.cv y)
            (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv v)))
        (syn_wa (.classMem (.cv t) (syn_cfv (syn_c2nd) (.cv v)))
          (syn_wbr (.cv y) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv t)))))
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv))
              (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X)))
            (.classEq (syn_chncodepredends A X v) (syn_c0))) (.classMem (.cv y) X))
        (syn_wbr (.cv y) (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A)))
          (.cv v)))
      (.classMem (.cv y) X) p0032 p0044
  have p0047 :=
    @g_simprd
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv))
                (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X)))
              (.classEq (syn_chncodepredends A X v) (syn_c0))) (.classMem (.cv y) X))
          (syn_wbr (.cv y)
            (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv v)))
        (syn_wa (.classMem (.cv t) (syn_cfv (syn_c2nd) (.cv v)))
          (syn_wbr (.cv y) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv t)))))
      (.classMem (.cv t) (syn_cfv (syn_c2nd) (.cv v)))
      (syn_wbr (.cv y) (syn_chwniso A)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv t)))
      p0039
  have p0048 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv))
                (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X)))
              (.classEq (syn_chncodepredends A X v) (syn_c0))) (.classMem (.cv y) X))
          (syn_wbr (.cv y)
            (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv v)))
        (syn_wa (.classMem (.cv t) (syn_cfv (syn_c2nd) (.cv v)))
          (syn_wbr (.cv y) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv t)))))
      (.classMem (.cv y) X)
      (syn_wbr (.cv y) (syn_chwniso A)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv t)))
      p0045 p0047
  have p0049 :=
    @g_breq1 (.cv a) (.cv y)
      (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv t))
      (syn_chwniso A)
  have p0050 :=
    @g_rspcev
      (syn_wbr (.cv a) (syn_chwniso A)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv t)))
      (syn_wbr (.cv y) (syn_chwniso A)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv t)))
      a (.cv y) X dv_cache_0007 dv_cache_0008 dv_cache_0009 p0049
  have p0051 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv))
                (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X)))
              (.classEq (syn_chncodepredends A X v) (syn_c0))) (.classMem (.cv y) X))
          (syn_wbr (.cv y)
            (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv v)))
        (syn_wa (.classMem (.cv t) (syn_cfv (syn_c2nd) (.cv v)))
          (syn_wbr (.cv y) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv t)))))
      (syn_wa (.classMem (.cv y) X) (syn_wbr (.cv y) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv t))))
      (syn_wrex a X (syn_wbr (.cv a) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv t))))
      p0048 p0050
  have p0052 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv))
                (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X)))
              (.classEq (syn_chncodepredends A X v) (syn_c0))) (.classMem (.cv y) X))
          (syn_wbr (.cv y)
            (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv v)))
        (syn_wa (.classMem (.cv t) (syn_cfv (syn_c2nd) (.cv v)))
          (syn_wbr (.cv y) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv t)))))
      (.classMem (.cv t) (syn_cfv (syn_c2nd) (.cv v)))
      (syn_wrex a X (syn_wbr (.cv a) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv t))))
      p0040 p0051
  have p0065 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv))
                (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X)))
              (.classEq (syn_chncodepredends A X v) (syn_c0))) (.classMem (.cv y) X))
          (syn_wbr (.cv y)
            (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv v)))
        (syn_wa (.classMem (.cv t) (syn_cfv (syn_c2nd) (.cv v)))
          (syn_wbr (.cv y) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv t)))))
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv))
              (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X)))
            (.classEq (syn_chncodepredends A X v) (syn_c0))) (.classMem (.cv y) X))
        (syn_wbr (.cv y) (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A)))
          (.cv v)))
      (.classMem (.cv v) (syn_chwcn A)) p0032 p0026
  have p0066 :=
    @g_hncodepredendsmemndv t v a A X dv_cache_0010 dv_cache_0002 dv_cache_0008
      dv_cache_0011 dv_cache_0012
  have p0067 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv))
                (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X)))
              (.classEq (syn_chncodepredends A X v) (syn_c0))) (.classMem (.cv y) X))
          (syn_wbr (.cv y)
            (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv v)))
        (syn_wa (.classMem (.cv t) (syn_cfv (syn_c2nd) (.cv v)))
          (syn_wbr (.cv y) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv t)))))
      (.classMem (.cv v) (syn_chwcn A))
      (syn_wb (.classMem (.cv t) (syn_chncodepredends A X v))
        (syn_wa (.classMem (.cv t) (syn_cfv (syn_c2nd) (.cv v))) (syn_wrex a X
            (syn_wbr (.cv a) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv t))))))
      p0065 p0066
  have p0068 :=
    @g_mpbird
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv))
                (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X)))
              (.classEq (syn_chncodepredends A X v) (syn_c0))) (.classMem (.cv y) X))
          (syn_wbr (.cv y)
            (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv v)))
        (syn_wa (.classMem (.cv t) (syn_cfv (syn_c2nd) (.cv v)))
          (syn_wbr (.cv y) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv t)))))
      (.classMem (.cv t) (syn_chncodepredends A X v))
      (syn_wa (.classMem (.cv t) (syn_cfv (syn_c2nd) (.cv v))) (syn_wrex a X
          (syn_wbr (.cv a) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv t)))))
      p0052 p0067
  have p0069 := @g_ne0i (syn_chncodepredends A X v) (.cv t)
  have p0070 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv))
                (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X)))
              (.classEq (syn_chncodepredends A X v) (syn_c0))) (.classMem (.cv y) X))
          (syn_wbr (.cv y)
            (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv v)))
        (syn_wa (.classMem (.cv t) (syn_cfv (syn_c2nd) (.cv v)))
          (syn_wbr (.cv y) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv t)))))
      (.classMem (.cv t) (syn_chncodepredends A X v))
      (syn_wne (syn_chncodepredends A X v) (syn_c0)) p0068 p0069
  have p0071 :=
    @g_pm2_21ddne
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv))
                (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X)))
              (.classEq (syn_chncodepredends A X v) (syn_c0))) (.classMem (.cv y) X))
          (syn_wbr (.cv y)
            (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv v)))
        (syn_wa (.classMem (.cv t) (syn_cfv (syn_c2nd) (.cv v)))
          (syn_wbr (.cv y) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv t)))))
      (.classEq (.cv y) (.cv v)) (syn_chncodepredends A X v) (syn_c0) p0038 p0070
  have p0072 :=
    @g_rexlimddv
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv))
              (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X)))
            (.classEq (syn_chncodepredends A X v) (syn_c0))) (.classMem (.cv y) X))
        (syn_wbr (.cv y) (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A)))
          (.cv v)))
      (syn_wbr (.cv y) (syn_chwniso A)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv t)))
      (.classEq (.cv y) (.cv v)) t (syn_cfv (syn_c2nd) (.cv v)) dv_cache_0013
      dv_cache_0014 p0031 p0071
  have p0073 :=
    @g_ex
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv))
            (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X)))
          (.classEq (syn_chncodepredends A X v) (syn_c0))) (.classMem (.cv y) X))
      (syn_wbr (.cv y) (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A)))
        (.cv v))
      (.classEq (.cv y) (.cv v)) p0072
  have p0074 :=
    @g_ralrimiva
      (syn_wa (syn_wa (.classMem A (syn_cvv))
          (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X)))
        (.classEq (syn_chncodepredends A X v) (syn_c0)))
      (.imp (syn_wbr (.cv y) (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A)))
          (.cv v)) (.classEq (.cv y) (.cv v)))
      y X dv_cache_0015 p0073
  exact p0074

@[expose]
noncomputable def g_wefrndv (D : Class) (R : Class) :
    Nominal.NPrf (.imp (syn_wbr R (syn_cwe) D) (syn_wbr R (syn_cfound) D)) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_cwe))
  have p0001 := @g_breqi R D (syn_cwe) (syn_cin (syn_cstrict) (syn_cfound)) p0000
  have p0002 := @g_brin R D (syn_cstrict) (syn_cfound)
  have p0003 :=
    @g_bitri (syn_wbr R (syn_cwe) D) (syn_wbr R (syn_cin (syn_cstrict) (syn_cfound)) D)
      (syn_wa (syn_wbr R (syn_cstrict) D) (syn_wbr R (syn_cfound) D)) p0001 p0002
  have p0004 :=
    @g_simprbi (syn_wbr R (syn_cwe) D) (syn_wbr R (syn_cstrict) D)
      (syn_wbr R (syn_cfound) D) p0003
  exact p0004


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk017Compact001Part046`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_hncodeprednonemptyminimalndv (z : Var) (v : Var) (u : Var) (A : Class)
    (X : Class) (dv_A_u : u ∉ A.fv) (dv_A_v : v ∉ A.fv) (dv_A_z : z ∉ A.fv)
    (dv_X_u : u ∉ X.fv) (dv_X_z : z ∉ X.fv) (dv_u_v : u ≠ v) (dv_u_z : u ≠ z)
    (dv_v_z : v ≠ z) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv)))
            (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X)))
          (syn_wne (syn_chncodepredends A X v) (syn_c0))) (syn_wrex u X (syn_wral z X (.imp
              (syn_wbr (.cv z)
                (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv u))
              (.classEq (.cv z) (.cv u)))))) :=
  by
  let proofSupport : Finset Var :=
    ({ z } : Finset Var) ∪ ({ v } : Finset Var) ∪ ({ u } : Finset Var) ∪ A.fv ∪ X.fv
  let a : Var := freshVar proofSupport 0
  let x : Var := freshVar proofSupport 1
  have fresh_a : a ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_a_ne_z : a ≠ z := by
    intro h
    exact
      fresh_a
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))
  have fresh_z_ne_a : z ≠ a := Ne.symm fresh_a_ne_z
  have fresh_a_ne_v : a ≠ v := by
    intro h
    exact
      fresh_a
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))
  have fresh_v_ne_a : v ≠ a := Ne.symm fresh_a_ne_v
  have fresh_a_ne_u : a ≠ u := by
    intro h
    exact
      fresh_a
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_u_ne_a : u ≠ a := Ne.symm fresh_a_ne_u
  have fresh_a_not_A : a ∉ A.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_a_not_X : a ∉ X.fv := by
    intro h
    exact fresh_a (Finset.mem_union_right _ (h))
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_x_ne_z : x ≠ z := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))
  have fresh_x_ne_v : x ≠ v := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))
  have fresh_x_ne_u : x ≠ u := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_u_ne_x : u ≠ x := Ne.symm fresh_x_ne_u
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_X : x ∉ X.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_a_ne_x : a ≠ x :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_x_ne_a : x ≠ a := Ne.symm fresh_a_ne_x
  have dv_cache_0001 : v ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_v, not_false_eq_true])
  have dv_cache_0002 : x ∉ ((syn_cfv (syn_c1st) (.cv v))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_v, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0003 : a ∉ ((syn_cfv (syn_c1st) (.cv v))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_a_ne_v, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0004 : x ∉ ((syn_chncodepredends A X v)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodepredends,
          Finset.mem_union, Finset.mem_singleton, fresh_x_not_A, fresh_x_not_X,
          fresh_x_ne_v, or_false, not_false_eq_true])
  have dv_cache_0005 : a ∉ ((syn_chncodepredends A X v)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodepredends,
          Finset.mem_union, Finset.mem_singleton, fresh_a_not_A, fresh_a_not_X,
          fresh_a_ne_v, or_false, not_false_eq_true])
  have dv_cache_0006 : x ≠ a :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show x ≠ a from (by exact fresh_x_ne_a))
  have dv_cache_0007 : u ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_u, not_false_eq_true])
  have dv_cache_0008 : u ∉ (X).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_X_u, not_false_eq_true])
  have dv_cache_0009 : u ≠ v :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (show u ≠ v from (by exact dv_u_v))
  have dv_cache_0010 : u ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (show u ≠ x from (by exact fresh_u_ne_x))
  have dv_cache_0011 : z ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_z, not_false_eq_true])
  have dv_cache_0012 : a ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_a_not_A, not_false_eq_true])
  have dv_cache_0013 : z ∉ (X).fv :=
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
        simp only [dv_X_z, not_false_eq_true])
  have dv_cache_0014 : a ∉ (X).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_a_not_X, not_false_eq_true])
  have dv_cache_0015 : u ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (show u ≠ z from (by exact dv_u_z))
  have dv_cache_0016 : u ≠ a :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (show u ≠ a from (by exact fresh_u_ne_a))
  have dv_cache_0017 : v ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (show v ≠ z from (by exact dv_v_z))
  have dv_cache_0018 : v ≠ a :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact (show v ≠ a from (by exact fresh_v_ne_a))
  have dv_cache_0019 : x ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018
    exact (show x ≠ z from (by exact fresh_x_ne_z))
  have dv_cache_0020 : z ≠ a :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019
    exact (show z ≠ a from (by exact fresh_z_ne_a))
  have dv_cache_0021 :
    u ∉
      ((syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv)))
              (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X)))
            (syn_wne (syn_chncodepredends A X v) (syn_c0)))
          (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v))
            (syn_wral a (syn_chncodepredends A X v)
              (.imp (syn_wbr (.cv a) (syn_cfv (syn_c1st) (.cv v)) (.cv x))
                (.classEq (.cv a) (.cv x))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodepredends,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
          NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, dv_A_u, dv_X_u, dv_u_v, fresh_u_ne_x, fresh_u_ne_a,
          compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0022 :
    x ∉
      ((syn_wrex u X (syn_wral z X (.imp (syn_wbr (.cv z)
                (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv u))
              (.classEq (.cv z) (.cv u)))))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
          NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodecmpset,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_x_not_X, fresh_x_ne_z, fresh_x_ne_u, fresh_x_not_A,
          or_false, and_false, not_false_eq_true])
  have dv_cache_0023 :
    x ∉
      ((syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv)))
            (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X)))
          (syn_wne (syn_chncodepredends A X v) (syn_c0)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodepredends,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union,
          Finset.mem_singleton, fresh_x_not_A, fresh_x_not_X, fresh_x_ne_v,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have p0000 :=
    @g_simpl
      (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv)))
        (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X)))
      (syn_wne (syn_chncodepredends A X v) (syn_c0))
  have p0001 :=
    @g_simprd
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv)))
          (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X)))
        (syn_wne (syn_chncodepredends A X v) (syn_c0)))
      (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv)))
      (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X)) p0000
  have p0002 :=
    @g_simpld
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv)))
          (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X)))
        (syn_wne (syn_chncodepredends A X v) (syn_c0)))
      (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X) p0001
  have p0005 :=
    @g_simprd
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv)))
          (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X)))
        (syn_wne (syn_chncodepredends A X v) (syn_c0)))
      (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X) p0001
  have p0006 :=
    @g_sseldd
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv)))
          (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X)))
        (syn_wne (syn_chncodepredends A X v) (syn_c0)))
      X (syn_chwcn A) (.cv v) p0002 p0005
  have p0007 := @g_hwcnwendv v A dv_cache_0001
  have p0008 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv)))
          (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X)))
        (syn_wne (syn_chncodepredends A X v) (syn_c0)))
      (.classMem (.cv v) (syn_chwcn A))
      (syn_wbr (syn_cfv (syn_c1st) (.cv v)) (syn_cwe) (syn_cfv (syn_c2nd) (.cv v))) p0006
      p0007
  have p0009 := @g_wefrndv (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (syn_c1st) (.cv v))
  have p0010 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv)))
          (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X)))
        (syn_wne (syn_chncodepredends A X v) (syn_c0)))
      (syn_wbr (syn_cfv (syn_c1st) (.cv v)) (syn_cwe) (syn_cfv (syn_c2nd) (.cv v)))
      (syn_wbr (syn_cfv (syn_c1st) (.cv v)) (syn_cfound) (syn_cfv (syn_c2nd) (.cv v)))
      p0008 p0009
  have p0012 :=
    @g_simpld
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv)))
          (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X)))
        (syn_wne (syn_chncodepredends A X v) (syn_c0)))
      (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv)))
      (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X)) p0000
  have p0013 :=
    @g_simpld
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv)))
          (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X)))
        (syn_wne (syn_chncodepredends A X v) (syn_c0)))
      (.classMem A (syn_cvv)) (.classMem X (syn_cvv)) p0012
  have p0016 :=
    @g_simprd
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv)))
          (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X)))
        (syn_wne (syn_chncodepredends A X v) (syn_c0)))
      (.classMem A (syn_cvv)) (.classMem X (syn_cvv)) p0012
  have p0017 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv)))
          (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X)))
        (syn_wne (syn_chncodepredends A X v) (syn_c0)))
      (.classMem A (syn_cvv)) (.classMem X (syn_cvv)) p0013 p0016
  have p0018 := @g_hncodepredendsexg v A X dv_cache_0001
  have p0019 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv)))
          (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X)))
        (syn_wne (syn_chncodepredends A X v) (syn_c0)))
      (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv)))
      (.classMem (syn_chncodepredends A X v) (syn_cvv)) p0017 p0018
  have p0027 := @g_hncodepredendsssndv v A X dv_cache_0001
  have p0028 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv)))
          (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X)))
        (syn_wne (syn_chncodepredends A X v) (syn_c0)))
      (.classMem (.cv v) (syn_chwcn A))
      (syn_wss (syn_chncodepredends A X v) (syn_cfv (syn_c2nd) (.cv v))) p0006 p0027
  have p0029 :=
    @g_simpr
      (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv)))
        (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X)))
      (syn_wne (syn_chncodepredends A X v) (syn_c0))
  have p0030 :=
    @g_frd
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv)))
          (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X)))
        (syn_wne (syn_chncodepredends A X v) (syn_c0)))
      x a (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (syn_c1st) (.cv v)) (syn_cvv)
      (syn_chncodepredends A X v) dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 p0010 p0019 p0028 p0029
  have p0031 :=
    @g_simpr
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv)))
          (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X)))
        (syn_wne (syn_chncodepredends A X v) (syn_c0)))
      (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v))
        (syn_wral a (syn_chncodepredends A X v)
          (.imp (syn_wbr (.cv a) (syn_cfv (syn_c1st) (.cv v)) (.cv x))
            (.classEq (.cv a) (.cv x)))))
  have p0032 :=
    @g_simpld
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv)))
            (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X)))
          (syn_wne (syn_chncodepredends A X v) (syn_c0)))
        (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v))
          (syn_wral a (syn_chncodepredends A X v)
            (.imp (syn_wbr (.cv a) (syn_cfv (syn_c1st) (.cv v)) (.cv x))
              (.classEq (.cv a) (.cv x))))))
      (.classMem (.cv x) (syn_chncodepredends A X v))
      (syn_wral a (syn_chncodepredends A X v)
        (.imp (syn_wbr (.cv a) (syn_cfv (syn_c1st) (.cv v)) (.cv x))
          (.classEq (.cv a) (.cv x))))
      p0031
  have p0033 :=
    @g_simpl
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv)))
          (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X)))
        (syn_wne (syn_chncodepredends A X v) (syn_c0)))
      (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v))
        (syn_wral a (syn_chncodepredends A X v)
          (.imp (syn_wbr (.cv a) (syn_cfv (syn_c1st) (.cv v)) (.cv x))
            (.classEq (.cv a) (.cv x)))))
  have p0041 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv)))
            (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X)))
          (syn_wne (syn_chncodepredends A X v) (syn_c0)))
        (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v))
          (syn_wral a (syn_chncodepredends A X v)
            (.imp (syn_wbr (.cv a) (syn_cfv (syn_c1st) (.cv v)) (.cv x))
              (.classEq (.cv a) (.cv x))))))
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv)))
          (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X)))
        (syn_wne (syn_chncodepredends A X v) (syn_c0)))
      (.classMem (.cv v) (syn_chwcn A)) p0033 p0006
  have p0042 :=
    @g_hncodepredendsmemndv x v u A X dv_cache_0007 dv_cache_0001 dv_cache_0008
      dv_cache_0009 dv_cache_0010
  have p0043 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv)))
            (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X)))
          (syn_wne (syn_chncodepredends A X v) (syn_c0)))
        (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v))
          (syn_wral a (syn_chncodepredends A X v)
            (.imp (syn_wbr (.cv a) (syn_cfv (syn_c1st) (.cv v)) (.cv x))
              (.classEq (.cv a) (.cv x))))))
      (.classMem (.cv v) (syn_chwcn A))
      (syn_wb (.classMem (.cv x) (syn_chncodepredends A X v))
        (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wrex u X
            (syn_wbr (.cv u) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv x))))))
      p0041 p0042
  have p0044 :=
    @g_mpbid
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv)))
            (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X)))
          (syn_wne (syn_chncodepredends A X v) (syn_c0)))
        (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v))
          (syn_wral a (syn_chncodepredends A X v)
            (.imp (syn_wbr (.cv a) (syn_cfv (syn_c1st) (.cv v)) (.cv x))
              (.classEq (.cv a) (.cv x))))))
      (.classMem (.cv x) (syn_chncodepredends A X v))
      (syn_wa (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) (syn_wrex u X
          (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv x)))))
      p0032 p0043
  have p0045 :=
    @g_simprd
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv)))
            (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X)))
          (syn_wne (syn_chncodepredends A X v) (syn_c0)))
        (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v))
          (syn_wral a (syn_chncodepredends A X v)
            (.imp (syn_wbr (.cv a) (syn_cfv (syn_c1st) (.cv v)) (.cv x))
              (.classEq (.cv a) (.cv x))))))
      (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
      (syn_wrex u X (syn_wbr (.cv u) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))
      p0044
  have p0046 :=
    @g_simpl
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv)))
              (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X)))
            (syn_wne (syn_chncodepredends A X v) (syn_c0)))
          (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v))
            (syn_wral a (syn_chncodepredends A X v)
              (.imp (syn_wbr (.cv a) (syn_cfv (syn_c1st) (.cv v)) (.cv x))
                (.classEq (.cv a) (.cv x)))))) (.classMem (.cv u) X))
      (syn_wbr (.cv u) (syn_chwniso A)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))
  have p0047 :=
    @g_simpld
      (syn_wa (syn_wa (syn_wa (syn_wa
              (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv)))
                (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X)))
              (syn_wne (syn_chncodepredends A X v) (syn_c0)))
            (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v))
              (syn_wral a (syn_chncodepredends A X v)
                (.imp (syn_wbr (.cv a) (syn_cfv (syn_c1st) (.cv v)) (.cv x))
                  (.classEq (.cv a) (.cv x)))))) (.classMem (.cv u) X))
        (syn_wbr (.cv u) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv)))
            (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X)))
          (syn_wne (syn_chncodepredends A X v) (syn_c0)))
        (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v))
          (syn_wral a (syn_chncodepredends A X v)
            (.imp (syn_wbr (.cv a) (syn_cfv (syn_c1st) (.cv v)) (.cv x))
              (.classEq (.cv a) (.cv x))))))
      (.classMem (.cv u) X) p0046
  have p0052 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv)))
            (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X)))
          (syn_wne (syn_chncodepredends A X v) (syn_c0)))
        (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v))
          (syn_wral a (syn_chncodepredends A X v)
            (.imp (syn_wbr (.cv a) (syn_cfv (syn_c1st) (.cv v)) (.cv x))
              (.classEq (.cv a) (.cv x))))))
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv)))
          (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X)))
        (syn_wne (syn_chncodepredends A X v) (syn_c0)))
      (.classMem A (syn_cvv)) p0033 p0013
  have p0053 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa
              (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv)))
                (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X)))
              (syn_wne (syn_chncodepredends A X v) (syn_c0)))
            (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v))
              (syn_wral a (syn_chncodepredends A X v)
                (.imp (syn_wbr (.cv a) (syn_cfv (syn_c1st) (.cv v)) (.cv x))
                  (.classEq (.cv a) (.cv x)))))) (.classMem (.cv u) X))
        (syn_wbr (.cv u) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv)))
            (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X)))
          (syn_wne (syn_chncodepredends A X v) (syn_c0)))
        (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v))
          (syn_wral a (syn_chncodepredends A X v)
            (.imp (syn_wbr (.cv a) (syn_cfv (syn_c1st) (.cv v)) (.cv x))
              (.classEq (.cv a) (.cv x))))))
      (.classMem A (syn_cvv)) p0047 p0052
  have p0060 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv)))
            (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X)))
          (syn_wne (syn_chncodepredends A X v) (syn_c0)))
        (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v))
          (syn_wral a (syn_chncodepredends A X v)
            (.imp (syn_wbr (.cv a) (syn_cfv (syn_c1st) (.cv v)) (.cv x))
              (.classEq (.cv a) (.cv x))))))
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv)))
          (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X)))
        (syn_wne (syn_chncodepredends A X v) (syn_c0)))
      (syn_wss X (syn_chwcn A)) p0033 p0002
  have p0061 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa
              (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv)))
                (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X)))
              (syn_wne (syn_chncodepredends A X v) (syn_c0)))
            (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v))
              (syn_wral a (syn_chncodepredends A X v)
                (.imp (syn_wbr (.cv a) (syn_cfv (syn_c1st) (.cv v)) (.cv x))
                  (.classEq (.cv a) (.cv x)))))) (.classMem (.cv u) X))
        (syn_wbr (.cv u) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv)))
            (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X)))
          (syn_wne (syn_chncodepredends A X v) (syn_c0)))
        (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v))
          (syn_wral a (syn_chncodepredends A X v)
            (.imp (syn_wbr (.cv a) (syn_cfv (syn_c1st) (.cv v)) (.cv x))
              (.classEq (.cv a) (.cv x))))))
      (syn_wss X (syn_chwcn A)) p0047 p0060
  have p0073 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa
              (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv)))
                (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X)))
              (syn_wne (syn_chncodepredends A X v) (syn_c0)))
            (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v))
              (syn_wral a (syn_chncodepredends A X v)
                (.imp (syn_wbr (.cv a) (syn_cfv (syn_c1st) (.cv v)) (.cv x))
                  (.classEq (.cv a) (.cv x)))))) (.classMem (.cv u) X))
        (syn_wbr (.cv u) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv)))
            (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X)))
          (syn_wne (syn_chncodepredends A X v) (syn_c0)))
        (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v))
          (syn_wral a (syn_chncodepredends A X v)
            (.imp (syn_wbr (.cv a) (syn_cfv (syn_c1st) (.cv v)) (.cv x))
              (.classEq (.cv a) (.cv x))))))
      (.classMem (.cv v) (syn_chwcn A)) p0047 p0041
  have p0074 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (syn_wa
              (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv)))
                (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X)))
              (syn_wne (syn_chncodepredends A X v) (syn_c0)))
            (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v))
              (syn_wral a (syn_chncodepredends A X v)
                (.imp (syn_wbr (.cv a) (syn_cfv (syn_c1st) (.cv v)) (.cv x))
                  (.classEq (.cv a) (.cv x)))))) (.classMem (.cv u) X))
        (syn_wbr (.cv u) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))
      (syn_wss X (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)) p0061 p0073
  have p0075 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (syn_wa
              (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv)))
                (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X)))
              (syn_wne (syn_chncodepredends A X v) (syn_c0)))
            (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v))
              (syn_wral a (syn_chncodepredends A X v)
                (.imp (syn_wbr (.cv a) (syn_cfv (syn_c1st) (.cv v)) (.cv x))
                  (.classEq (.cv a) (.cv x)))))) (.classMem (.cv u) X))
        (syn_wbr (.cv u) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))
      (.classMem A (syn_cvv))
      (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) p0053 p0074
  have p0080 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa
              (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv)))
                (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X)))
              (syn_wne (syn_chncodepredends A X v) (syn_c0)))
            (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v))
              (syn_wral a (syn_chncodepredends A X v)
                (.imp (syn_wbr (.cv a) (syn_cfv (syn_c1st) (.cv v)) (.cv x))
                  (.classEq (.cv a) (.cv x)))))) (.classMem (.cv u) X))
        (syn_wbr (.cv u) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv)))
            (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X)))
          (syn_wne (syn_chncodepredends A X v) (syn_c0)))
        (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v))
          (syn_wral a (syn_chncodepredends A X v)
            (.imp (syn_wbr (.cv a) (syn_cfv (syn_c1st) (.cv v)) (.cv x))
              (.classEq (.cv a) (.cv x))))))
      (.classMem (.cv x) (syn_chncodepredends A X v)) p0047 p0032
  have p0082 :=
    @g_simprd
      (syn_wa (syn_wa (syn_wa (syn_wa
              (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv)))
                (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X)))
              (syn_wne (syn_chncodepredends A X v) (syn_c0)))
            (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v))
              (syn_wral a (syn_chncodepredends A X v)
                (.imp (syn_wbr (.cv a) (syn_cfv (syn_c1st) (.cv v)) (.cv x))
                  (.classEq (.cv a) (.cv x)))))) (.classMem (.cv u) X))
        (syn_wbr (.cv u) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv)))
            (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X)))
          (syn_wne (syn_chncodepredends A X v) (syn_c0)))
        (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v))
          (syn_wral a (syn_chncodepredends A X v)
            (.imp (syn_wbr (.cv a) (syn_cfv (syn_c1st) (.cv v)) (.cv x))
              (.classEq (.cv a) (.cv x))))))
      (.classMem (.cv u) X) p0046
  have p0083 :=
    @g_simpr
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv)))
              (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X)))
            (syn_wne (syn_chncodepredends A X v) (syn_c0)))
          (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v))
            (syn_wral a (syn_chncodepredends A X v)
              (.imp (syn_wbr (.cv a) (syn_cfv (syn_c1st) (.cv v)) (.cv x))
                (.classEq (.cv a) (.cv x)))))) (.classMem (.cv u) X))
      (syn_wbr (.cv u) (syn_chwniso A)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))
  have p0084 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (syn_wa
              (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv)))
                (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X)))
              (syn_wne (syn_chncodepredends A X v) (syn_c0)))
            (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v))
              (syn_wral a (syn_chncodepredends A X v)
                (.imp (syn_wbr (.cv a) (syn_cfv (syn_c1st) (.cv v)) (.cv x))
                  (.classEq (.cv a) (.cv x)))))) (.classMem (.cv u) X))
        (syn_wbr (.cv u) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))
      (.classMem (.cv u) X)
      (syn_wbr (.cv u) (syn_chwniso A)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))
      p0082 p0083
  have p0085 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (syn_wa
              (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv)))
                (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X)))
              (syn_wne (syn_chncodepredends A X v) (syn_c0)))
            (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v))
              (syn_wral a (syn_chncodepredends A X v)
                (.imp (syn_wbr (.cv a) (syn_cfv (syn_c1st) (.cv v)) (.cv x))
                  (.classEq (.cv a) (.cv x)))))) (.classMem (.cv u) X))
        (syn_wbr (.cv u) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))
      (.classMem (.cv x) (syn_chncodepredends A X v))
      (syn_wa (.classMem (.cv u) X) (syn_wbr (.cv u) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))
      p0080 p0084
  have p0089 :=
    @g_simprd
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv)))
            (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X)))
          (syn_wne (syn_chncodepredends A X v) (syn_c0)))
        (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v))
          (syn_wral a (syn_chncodepredends A X v)
            (.imp (syn_wbr (.cv a) (syn_cfv (syn_c1st) (.cv v)) (.cv x))
              (.classEq (.cv a) (.cv x))))))
      (.classMem (.cv x) (syn_chncodepredends A X v))
      (syn_wral a (syn_chncodepredends A X v)
        (.imp (syn_wbr (.cv a) (syn_cfv (syn_c1st) (.cv v)) (.cv x))
          (.classEq (.cv a) (.cv x))))
      p0031
  have p0090 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa
              (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv)))
                (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X)))
              (syn_wne (syn_chncodepredends A X v) (syn_c0)))
            (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v))
              (syn_wral a (syn_chncodepredends A X v)
                (.imp (syn_wbr (.cv a) (syn_cfv (syn_c1st) (.cv v)) (.cv x))
                  (.classEq (.cv a) (.cv x)))))) (.classMem (.cv u) X))
        (syn_wbr (.cv u) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv)))
            (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X)))
          (syn_wne (syn_chncodepredends A X v) (syn_c0)))
        (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v))
          (syn_wral a (syn_chncodepredends A X v)
            (.imp (syn_wbr (.cv a) (syn_cfv (syn_c1st) (.cv v)) (.cv x))
              (.classEq (.cv a) (.cv x))))))
      (syn_wral a (syn_chncodepredends A X v)
        (.imp (syn_wbr (.cv a) (syn_cfv (syn_c1st) (.cv v)) (.cv x))
          (.classEq (.cv a) (.cv x))))
      p0047 p0089
  have p0091 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (syn_wa
              (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv)))
                (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X)))
              (syn_wne (syn_chncodepredends A X v) (syn_c0)))
            (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v))
              (syn_wral a (syn_chncodepredends A X v)
                (.imp (syn_wbr (.cv a) (syn_cfv (syn_c1st) (.cv v)) (.cv x))
                  (.classEq (.cv a) (.cv x)))))) (.classMem (.cv u) X))
        (syn_wbr (.cv u) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))
      (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v)) (syn_wa (.classMem (.cv u) X)
          (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv x)))))
      (syn_wral a (syn_chncodepredends A X v)
        (.imp (syn_wbr (.cv a) (syn_cfv (syn_c1st) (.cv v)) (.cv x))
          (.classEq (.cv a) (.cv x))))
      p0085 p0090
  have p0092 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (syn_wa
              (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv)))
                (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X)))
              (syn_wne (syn_chncodepredends A X v) (syn_c0)))
            (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v))
              (syn_wral a (syn_chncodepredends A X v)
                (.imp (syn_wbr (.cv a) (syn_cfv (syn_c1st) (.cv v)) (.cv x))
                  (.classEq (.cv a) (.cv x)))))) (.classMem (.cv u) X))
        (syn_wbr (.cv u) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))
      (syn_wa (.classMem A (syn_cvv))
        (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))))
      (syn_wa (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v))
          (syn_wa (.classMem (.cv u) X) (syn_wbr (.cv u) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv x))))) (syn_wral a (syn_chncodepredends A X v)
          (.imp (syn_wbr (.cv a) (syn_cfv (syn_c1st) (.cv v)) (.cv x))
            (.classEq (.cv a) (.cv x)))))
      p0075 p0091
  have p0093 :=
    @g_hncodepredrepminimalndv x z a v u A X dv_cache_0007 dv_cache_0001 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0006 dv_cache_0020
  have p0094 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa
              (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv)))
                (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X)))
              (syn_wne (syn_chncodepredends A X v) (syn_c0)))
            (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v))
              (syn_wral a (syn_chncodepredends A X v)
                (.imp (syn_wbr (.cv a) (syn_cfv (syn_c1st) (.cv v)) (.cv x))
                  (.classEq (.cv a) (.cv x)))))) (.classMem (.cv u) X))
        (syn_wbr (.cv u) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))
      (syn_wa (syn_wa (.classMem A (syn_cvv))
          (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))) (syn_wa
          (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v)) (syn_wa (.classMem (.cv u) X)
              (syn_wbr (.cv u) (syn_chwniso A)
                (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                  (.cv x))))) (syn_wral a (syn_chncodepredends A X v)
            (.imp (syn_wbr (.cv a) (syn_cfv (syn_c1st) (.cv v)) (.cv x))
              (.classEq (.cv a) (.cv x))))))
      (syn_wral z X (.imp (syn_wbr (.cv z)
            (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv u))
          (.classEq (.cv z) (.cv u))))
      p0092 p0093
  have p0095 :=
    @g_ex
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv)))
              (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X)))
            (syn_wne (syn_chncodepredends A X v) (syn_c0)))
          (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v))
            (syn_wral a (syn_chncodepredends A X v)
              (.imp (syn_wbr (.cv a) (syn_cfv (syn_c1st) (.cv v)) (.cv x))
                (.classEq (.cv a) (.cv x)))))) (.classMem (.cv u) X))
      (syn_wbr (.cv u) (syn_chwniso A)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))
      (syn_wral z X (.imp (syn_wbr (.cv z)
            (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv u))
          (.classEq (.cv z) (.cv u))))
      p0094
  have p0096 :=
    @g_reximdva
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv)))
            (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X)))
          (syn_wne (syn_chncodepredends A X v) (syn_c0)))
        (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v))
          (syn_wral a (syn_chncodepredends A X v)
            (.imp (syn_wbr (.cv a) (syn_cfv (syn_c1st) (.cv v)) (.cv x))
              (.classEq (.cv a) (.cv x))))))
      (syn_wbr (.cv u) (syn_chwniso A)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))
      (syn_wral z X (.imp (syn_wbr (.cv z)
            (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv u))
          (.classEq (.cv z) (.cv u))))
      u X dv_cache_0021 p0095
  have p0097 :=
    @g_mpd
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv)))
            (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X)))
          (syn_wne (syn_chncodepredends A X v) (syn_c0)))
        (syn_wa (.classMem (.cv x) (syn_chncodepredends A X v))
          (syn_wral a (syn_chncodepredends A X v)
            (.imp (syn_wbr (.cv a) (syn_cfv (syn_c1st) (.cv v)) (.cv x))
              (.classEq (.cv a) (.cv x))))))
      (syn_wrex u X (syn_wbr (.cv u) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))
      (syn_wrex u X (syn_wral z X (.imp (syn_wbr (.cv z)
              (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv u))
            (.classEq (.cv z) (.cv u)))))
      p0045 p0096
  have p0098_e00_recanon :
    Nominal.NPrf
      (.imp (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv)))
            (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X)))
          (syn_wne (syn_chncodepredends A X v) (syn_c0)))
        (syn_wrex x (syn_chncodepredends A X v) (syn_wral a (syn_chncodepredends A X v)
            (.imp (syn_wbr (.cv a) (syn_cfv (syn_c1st) (.cv v)) (.cv x))
              (.classEq (.cv a) (.cv x)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wa syn_wne syn_chncodepredends syn_cuni syn_wex syn_cima syn_wrex
          syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_ccompl syn_c2nd syn_copab
          syn_chncodepredinputs syn_cin syn_cxp syn_csn syn_cpw1 syn_cfv syn_cio syn_c0
          syn_cdif syn_cvv
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st]
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
      p0030
  have p0098 :=
    @g_rexlimddv
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cvv)) (.classMem X (syn_cvv)))
          (syn_wa (syn_wss X (syn_chwcn A)) (.classMem (.cv v) X)))
        (syn_wne (syn_chncodepredends A X v) (syn_c0)))
      (syn_wral a (syn_chncodepredends A X v)
        (.imp (syn_wbr (.cv a) (syn_cfv (syn_c1st) (.cv v)) (.cv x))
          (.classEq (.cv a) (.cv x))))
      (syn_wrex u X (syn_wral z X (.imp (syn_wbr (.cv z)
              (syn_cdif (syn_chncodecmpset A) (syn_ccnv (syn_chncodecmpset A))) (.cv u))
            (.classEq (.cv z) (.cv u)))))
      x (syn_chncodepredends A X v) dv_cache_0022 dv_cache_0023 p0098_e00_recanon p0097
  exact p0098


end NFChoice.DirectNominalPrf.WPPReplay

end
