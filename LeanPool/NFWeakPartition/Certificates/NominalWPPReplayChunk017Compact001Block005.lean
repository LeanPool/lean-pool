/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NominalWPPReplayChunk017Compact001Block004

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NominalWPPReplayChunk017Compact001Part021`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_hncodecutreledgedecode (x : Var) (v : Var) (u : Var) (A : Class)
    (C : Class) (_dv_A_C : Disjoint A.fv C.fv) (dv_A_u : u ∉ A.fv) (_dv_A_v : v ∉ A.fv)
    (dv_A_x : x ∉ A.fv) (dv_C_u : u ∉ C.fv) (_dv_C_v : v ∉ C.fv) (dv_C_x : x ∉ C.fv)
    (dv_u_v : u ≠ v) (dv_u_x : u ≠ x) (dv_v_x : v ≠ x) :
    Nominal.NPrf
      (.imp (syn_wbr C (syn_chncodecutrel A) (.cv v)) (syn_wrex u (syn_chwcn A)
          (syn_wrex x (syn_cfv (syn_c2nd) (.cv u)) (syn_wa (.classEq C
                (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                  (.cv x))) (.classEq (.cv v) (.cv u)))))) :=
  by
  let proofSupport : Finset Var :=
    ({ x } : Finset Var) ∪ ({ v } : Finset Var) ∪ ({ u } : Finset Var) ∪ A.fv ∪ C.fv
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
  have fresh_x_ne_p : x ≠ p := Ne.symm fresh_p_ne_x
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
  have fresh_u_ne_p : u ≠ p := Ne.symm fresh_p_ne_u
  have fresh_p_not_A : p ∉ A.fv := by
    intro h
    exact fresh_p (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_p_not_C : p ∉ C.fv := by
    intro h
    exact fresh_p (Finset.mem_union_right _ (h))
  have dv_cache_0001 : p ∉ ((syn_cop C (.cv v))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_p_not_C, fresh_p_ne_v, or_false, not_false_eq_true])
  have dv_cache_0002 : p ∉ ((syn_chncodecutinputs A)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodecutinputs,
          fresh_p_not_A, not_false_eq_true])
  have dv_cache_0003 : p ∉ ((syn_chncodecutpairfn)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodecutpairfn,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0004 : p ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_p_not_A, not_false_eq_true])
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
  have dv_cache_0006 : x ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_x, not_false_eq_true])
  have dv_cache_0007 : p ≠ u :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact (show p ≠ u from (by exact fresh_p_ne_u))
  have dv_cache_0008 : p ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact (show p ≠ x from (by exact fresh_p_ne_x))
  have dv_cache_0009 : u ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (show u ≠ x from (by exact dv_u_x))
  have dv_cache_0010 :
    x ∉
      ((syn_wa (syn_wa (.classMem (.cv p) (syn_chncodecutinputs A))
            (.classEq (syn_cfv (syn_chncodecutpairfn) (.cv p)) (syn_cop C (.cv v))))
          (.classMem (.cv u) (syn_chwcn A)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodecutinputs,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodecutpairfn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_p, dv_A_x, dv_C_x, (Ne.symm dv_v_x),
          (Ne.symm dv_u_x), compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0011 :
    u ∉
      ((syn_wa (.classMem (.cv p) (syn_chncodecutinputs A))
          (.classEq (syn_cfv (syn_chncodecutpairfn) (.cv p)) (syn_cop C (.cv v))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodecutinputs,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodecutpairfn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union,
          Finset.mem_singleton, fresh_u_ne_p, dv_A_u, dv_C_u, dv_u_v,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0012 :
    p ∉
      ((syn_wrex u (syn_chwcn A) (syn_wrex x (syn_cfv (syn_c2nd) (.cv u)) (syn_wa (.classEq C
                (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                  (.cv x))) (.classEq (.cv v) (.cv u)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutcode,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_p_not_A, fresh_p_ne_u,
          fresh_p_not_C, fresh_p_ne_x, fresh_p_ne_v, compact_fv_not_mem_empty, or_false,
          and_false, not_false_eq_true])
  have p0000 := (Nominal.biimpRefl (syn_wbr C (syn_chncodecutrel A) (.cv v)))
  have p0001 :=
    @g_biimpi (syn_wbr C (syn_chncodecutrel A) (.cv v))
      (.classMem (syn_cop C (.cv v)) (syn_chncodecutrel A)) p0000
  have p0002 := (Nominal.classEqRefl (syn_chncodecutrel A))
  have p0003 :=
    @g_eleq2i (syn_chncodecutrel A)
      (syn_cima (syn_chncodecutpairfn) (syn_chncodecutinputs A)) (syn_cop C (.cv v)) p0002
  have p0004 :=
    @g_sylib (syn_wbr C (syn_chncodecutrel A) (.cv v))
      (.classMem (syn_cop C (.cv v)) (syn_chncodecutrel A))
      (.classMem (syn_cop C (.cv v)) (syn_cima (syn_chncodecutpairfn) (syn_chncodecutinputs A)))
      p0001 p0003
  have p0005 := @g_hncodecutpairfnfn
  have p0006 := @g_fnfun (syn_cvv) (syn_chncodecutpairfn)
  have p0007 := Nominal.mp p0005 p0006
  have p0008 :=
    @g_fvelima p (syn_cop C (.cv v)) (syn_chncodecutinputs A) (syn_chncodecutpairfn)
      dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0009 :=
    @g_mpan (syn_wfun (syn_chncodecutpairfn))
      (.classMem (syn_cop C (.cv v)) (syn_cima (syn_chncodecutpairfn) (syn_chncodecutinputs A)))
      (syn_wrex p (syn_chncodecutinputs A)
        (.classEq (syn_cfv (syn_chncodecutpairfn) (.cv p)) (syn_cop C (.cv v))))
      p0007 p0008
  have p0010 :=
    @g_syl (syn_wbr C (syn_chncodecutrel A) (.cv v))
      (.classMem (syn_cop C (.cv v)) (syn_cima (syn_chncodecutpairfn) (syn_chncodecutinputs A)))
      (syn_wrex p (syn_chncodecutinputs A)
        (.classEq (syn_cfv (syn_chncodecutpairfn) (.cv p)) (syn_cop C (.cv v))))
      p0004 p0009
  have p0011 :=
    @g_simpl (.classMem (.cv p) (syn_chncodecutinputs A))
      (.classEq (syn_cfv (syn_chncodecutpairfn) (.cv p)) (syn_cop C (.cv v)))
  have p0012 :=
    @g_hncodecutinputdecode x u A p dv_cache_0004 dv_cache_0005 dv_cache_0006
      dv_cache_0007 dv_cache_0008 dv_cache_0009
  have p0013 :=
    @g_syl
      (syn_wa (.classMem (.cv p) (syn_chncodecutinputs A))
        (.classEq (syn_cfv (syn_chncodecutpairfn) (.cv p)) (syn_cop C (.cv v))))
      (.classMem (.cv p) (syn_chncodecutinputs A))
      (syn_wrex u (syn_chwcn A) (syn_wrex x (syn_cfv (syn_c2nd) (.cv u))
          (.classEq (.cv p) (syn_cop (.cv u) (syn_csn (.cv x))))))
      p0011 p0012
  have p0014 :=
    @g_simpr
      (syn_wa (syn_wa (.classMem (.cv p) (syn_chncodecutinputs A))
          (.classEq (syn_cfv (syn_chncodecutpairfn) (.cv p)) (syn_cop C (.cv v))))
        (.classMem (.cv u) (syn_chwcn A)))
      (.classEq (.cv p) (syn_cop (.cv u) (syn_csn (.cv x))))
  have p0015 :=
    @g_fveq2d
      (syn_wa (syn_wa (syn_wa (.classMem (.cv p) (syn_chncodecutinputs A))
            (.classEq (syn_cfv (syn_chncodecutpairfn) (.cv p)) (syn_cop C (.cv v))))
          (.classMem (.cv u) (syn_chwcn A)))
        (.classEq (.cv p) (syn_cop (.cv u) (syn_csn (.cv x)))))
      (.cv p) (syn_cop (.cv u) (syn_csn (.cv x))) (syn_chncodecutpairfn) p0014
  have p0016 :=
    @g_simpl
      (syn_wa (syn_wa (.classMem (.cv p) (syn_chncodecutinputs A))
          (.classEq (syn_cfv (syn_chncodecutpairfn) (.cv p)) (syn_cop C (.cv v))))
        (.classMem (.cv u) (syn_chwcn A)))
      (.classEq (.cv p) (syn_cop (.cv u) (syn_csn (.cv x))))
  have p0017 :=
    @g_simpr
      (syn_wa (.classMem (.cv p) (syn_chncodecutinputs A))
        (.classEq (syn_cfv (syn_chncodecutpairfn) (.cv p)) (syn_cop C (.cv v))))
      (.classMem (.cv u) (syn_chwcn A))
  have p0018 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem (.cv p) (syn_chncodecutinputs A))
            (.classEq (syn_cfv (syn_chncodecutpairfn) (.cv p)) (syn_cop C (.cv v))))
          (.classMem (.cv u) (syn_chwcn A)))
        (.classEq (.cv p) (syn_cop (.cv u) (syn_csn (.cv x)))))
      (syn_wa (syn_wa (.classMem (.cv p) (syn_chncodecutinputs A))
          (.classEq (syn_cfv (syn_chncodecutpairfn) (.cv p)) (syn_cop C (.cv v))))
        (.classMem (.cv u) (syn_chwcn A)))
      (.classMem (.cv u) (syn_chwcn A)) p0016 p0017
  have p0019 := @g_hncodecutpairfnvalhwcn x u A dv_cache_0005
  have p0020 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem (.cv p) (syn_chncodecutinputs A))
            (.classEq (syn_cfv (syn_chncodecutpairfn) (.cv p)) (syn_cop C (.cv v))))
          (.classMem (.cv u) (syn_chwcn A)))
        (.classEq (.cv p) (syn_cop (.cv u) (syn_csn (.cv x)))))
      (.classMem (.cv u) (syn_chwcn A))
      (.classEq (syn_cfv (syn_chncodecutpairfn) (syn_cop (.cv u) (syn_csn (.cv x)))) (syn_cop
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
          (.cv u)))
      p0018 p0019
  have p0021 :=
    @g_eqtrd
      (syn_wa (syn_wa (syn_wa (.classMem (.cv p) (syn_chncodecutinputs A))
            (.classEq (syn_cfv (syn_chncodecutpairfn) (.cv p)) (syn_cop C (.cv v))))
          (.classMem (.cv u) (syn_chwcn A)))
        (.classEq (.cv p) (syn_cop (.cv u) (syn_csn (.cv x)))))
      (syn_cfv (syn_chncodecutpairfn) (.cv p))
      (syn_cfv (syn_chncodecutpairfn) (syn_cop (.cv u) (syn_csn (.cv x))))
      (syn_cop (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (.cv x)) (.cv u))
      p0015 p0020
  have p0022 :=
    @g_eqcomd
      (syn_wa (syn_wa (syn_wa (.classMem (.cv p) (syn_chncodecutinputs A))
            (.classEq (syn_cfv (syn_chncodecutpairfn) (.cv p)) (syn_cop C (.cv v))))
          (.classMem (.cv u) (syn_chwcn A)))
        (.classEq (.cv p) (syn_cop (.cv u) (syn_csn (.cv x)))))
      (syn_cfv (syn_chncodecutpairfn) (.cv p))
      (syn_cop (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (.cv x)) (.cv u))
      p0021
  have p0024 :=
    @g_simpl
      (syn_wa (.classMem (.cv p) (syn_chncodecutinputs A))
        (.classEq (syn_cfv (syn_chncodecutpairfn) (.cv p)) (syn_cop C (.cv v))))
      (.classMem (.cv u) (syn_chwcn A))
  have p0025 :=
    @g_simpr (.classMem (.cv p) (syn_chncodecutinputs A))
      (.classEq (syn_cfv (syn_chncodecutpairfn) (.cv p)) (syn_cop C (.cv v)))
  have p0026 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv p) (syn_chncodecutinputs A))
          (.classEq (syn_cfv (syn_chncodecutpairfn) (.cv p)) (syn_cop C (.cv v))))
        (.classMem (.cv u) (syn_chwcn A)))
      (syn_wa (.classMem (.cv p) (syn_chncodecutinputs A))
        (.classEq (syn_cfv (syn_chncodecutpairfn) (.cv p)) (syn_cop C (.cv v))))
      (.classEq (syn_cfv (syn_chncodecutpairfn) (.cv p)) (syn_cop C (.cv v))) p0024 p0025
  have p0027 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem (.cv p) (syn_chncodecutinputs A))
            (.classEq (syn_cfv (syn_chncodecutpairfn) (.cv p)) (syn_cop C (.cv v))))
          (.classMem (.cv u) (syn_chwcn A)))
        (.classEq (.cv p) (syn_cop (.cv u) (syn_csn (.cv x)))))
      (syn_wa (syn_wa (.classMem (.cv p) (syn_chncodecutinputs A))
          (.classEq (syn_cfv (syn_chncodecutpairfn) (.cv p)) (syn_cop C (.cv v))))
        (.classMem (.cv u) (syn_chwcn A)))
      (.classEq (syn_cfv (syn_chncodecutpairfn) (.cv p)) (syn_cop C (.cv v))) p0016 p0026
  have p0028 :=
    @g_eqtrd
      (syn_wa (syn_wa (syn_wa (.classMem (.cv p) (syn_chncodecutinputs A))
            (.classEq (syn_cfv (syn_chncodecutpairfn) (.cv p)) (syn_cop C (.cv v))))
          (.classMem (.cv u) (syn_chwcn A)))
        (.classEq (.cv p) (syn_cop (.cv u) (syn_csn (.cv x)))))
      (syn_cop (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (.cv x)) (.cv u))
      (syn_cfv (syn_chncodecutpairfn) (.cv p)) (syn_cop C (.cv v)) p0022 p0027
  have p0029 :=
    @g_opth
      (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
      (.cv u) C (.cv v)
  have p0030 :=
    @g_sylib
      (syn_wa (syn_wa (syn_wa (.classMem (.cv p) (syn_chncodecutinputs A))
            (.classEq (syn_cfv (syn_chncodecutpairfn) (.cv p)) (syn_cop C (.cv v))))
          (.classMem (.cv u) (syn_chwcn A)))
        (.classEq (.cv p) (syn_cop (.cv u) (syn_csn (.cv x)))))
      (.classEq (syn_cop
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
          (.cv u)) (syn_cop C (.cv v)))
      (syn_wa (.classEq
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) C)
        (.classEq (.cv u) (.cv v)))
      p0028 p0029
  have p0031 :=
    @g_simpl
      (.classEq (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (.cv x)) C)
      (.classEq (.cv u) (.cv v))
  have p0032 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem (.cv p) (syn_chncodecutinputs A))
            (.classEq (syn_cfv (syn_chncodecutpairfn) (.cv p)) (syn_cop C (.cv v))))
          (.classMem (.cv u) (syn_chwcn A)))
        (.classEq (.cv p) (syn_cop (.cv u) (syn_csn (.cv x)))))
      (syn_wa (.classEq
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) C)
        (.classEq (.cv u) (.cv v)))
      (.classEq (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (.cv x)) C)
      p0030 p0031
  have p0033 :=
    @g_eqcomd
      (syn_wa (syn_wa (syn_wa (.classMem (.cv p) (syn_chncodecutinputs A))
            (.classEq (syn_cfv (syn_chncodecutpairfn) (.cv p)) (syn_cop C (.cv v))))
          (.classMem (.cv u) (syn_chwcn A)))
        (.classEq (.cv p) (syn_cop (.cv u) (syn_csn (.cv x)))))
      (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
      C p0032
  have p0051 :=
    @g_simpr
      (.classEq (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (.cv x)) C)
      (.classEq (.cv u) (.cv v))
  have p0052 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem (.cv p) (syn_chncodecutinputs A))
            (.classEq (syn_cfv (syn_chncodecutpairfn) (.cv p)) (syn_cop C (.cv v))))
          (.classMem (.cv u) (syn_chwcn A)))
        (.classEq (.cv p) (syn_cop (.cv u) (syn_csn (.cv x)))))
      (syn_wa (.classEq
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)) C)
        (.classEq (.cv u) (.cv v)))
      (.classEq (.cv u) (.cv v)) p0030 p0051
  have p0053 :=
    @g_eqcomd
      (syn_wa (syn_wa (syn_wa (.classMem (.cv p) (syn_chncodecutinputs A))
            (.classEq (syn_cfv (syn_chncodecutpairfn) (.cv p)) (syn_cop C (.cv v))))
          (.classMem (.cv u) (syn_chwcn A)))
        (.classEq (.cv p) (syn_cop (.cv u) (syn_csn (.cv x)))))
      (.cv u) (.cv v) p0052
  have p0054 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (.classMem (.cv p) (syn_chncodecutinputs A))
            (.classEq (syn_cfv (syn_chncodecutpairfn) (.cv p)) (syn_cop C (.cv v))))
          (.classMem (.cv u) (syn_chwcn A)))
        (.classEq (.cv p) (syn_cop (.cv u) (syn_csn (.cv x)))))
      (.classEq C (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (.cv x)))
      (.classEq (.cv v) (.cv u)) p0033 p0053
  have p0055 :=
    @g_ex
      (syn_wa (syn_wa (.classMem (.cv p) (syn_chncodecutinputs A))
          (.classEq (syn_cfv (syn_chncodecutpairfn) (.cv p)) (syn_cop C (.cv v))))
        (.classMem (.cv u) (syn_chwcn A)))
      (.classEq (.cv p) (syn_cop (.cv u) (syn_csn (.cv x))))
      (syn_wa (.classEq C
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
        (.classEq (.cv v) (.cv u)))
      p0054
  have p0056 :=
    @g_reximdv
      (syn_wa (syn_wa (.classMem (.cv p) (syn_chncodecutinputs A))
          (.classEq (syn_cfv (syn_chncodecutpairfn) (.cv p)) (syn_cop C (.cv v))))
        (.classMem (.cv u) (syn_chwcn A)))
      (.classEq (.cv p) (syn_cop (.cv u) (syn_csn (.cv x))))
      (syn_wa (.classEq C
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
        (.classEq (.cv v) (.cv u)))
      x (syn_cfv (syn_c2nd) (.cv u)) dv_cache_0010 p0055
  have p0057 :=
    @g_reximdva
      (syn_wa (.classMem (.cv p) (syn_chncodecutinputs A))
        (.classEq (syn_cfv (syn_chncodecutpairfn) (.cv p)) (syn_cop C (.cv v))))
      (syn_wrex x (syn_cfv (syn_c2nd) (.cv u))
        (.classEq (.cv p) (syn_cop (.cv u) (syn_csn (.cv x)))))
      (syn_wrex x (syn_cfv (syn_c2nd) (.cv u)) (syn_wa (.classEq C
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
          (.classEq (.cv v) (.cv u))))
      u (syn_chwcn A) dv_cache_0011 p0056
  have p0058 :=
    @g_mpd
      (syn_wa (.classMem (.cv p) (syn_chncodecutinputs A))
        (.classEq (syn_cfv (syn_chncodecutpairfn) (.cv p)) (syn_cop C (.cv v))))
      (syn_wrex u (syn_chwcn A) (syn_wrex x (syn_cfv (syn_c2nd) (.cv u))
          (.classEq (.cv p) (syn_cop (.cv u) (syn_csn (.cv x))))))
      (syn_wrex u (syn_chwcn A) (syn_wrex x (syn_cfv (syn_c2nd) (.cv u)) (syn_wa (.classEq C
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                (.cv x))) (.classEq (.cv v) (.cv u)))))
      p0013 p0057
  have p0059 :=
    @g_ex (.classMem (.cv p) (syn_chncodecutinputs A))
      (.classEq (syn_cfv (syn_chncodecutpairfn) (.cv p)) (syn_cop C (.cv v)))
      (syn_wrex u (syn_chwcn A) (syn_wrex x (syn_cfv (syn_c2nd) (.cv u)) (syn_wa (.classEq C
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                (.cv x))) (.classEq (.cv v) (.cv u)))))
      p0058
  have p0060 :=
    @g_rexlimiv (.classEq (syn_cfv (syn_chncodecutpairfn) (.cv p)) (syn_cop C (.cv v)))
      (syn_wrex u (syn_chwcn A) (syn_wrex x (syn_cfv (syn_c2nd) (.cv u)) (syn_wa (.classEq C
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                (.cv x))) (.classEq (.cv v) (.cv u)))))
      p (syn_chncodecutinputs A) dv_cache_0012 p0059
  have p0061 :=
    @g_syl (syn_wbr C (syn_chncodecutrel A) (.cv v))
      (syn_wrex p (syn_chncodecutinputs A)
        (.classEq (syn_cfv (syn_chncodecutpairfn) (.cv p)) (syn_cop C (.cv v))))
      (syn_wrex u (syn_chwcn A) (syn_wrex x (syn_cfv (syn_c2nd) (.cv u)) (syn_wa (.classEq C
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                (.cv x))) (.classEq (.cv v) (.cv u)))))
      p0010 p0060
  exact p0061

@[expose]
noncomputable def g_hncodecutfnvalhwcn (x : Var) (u : Var) (A : Class)
    (_dv_A_u : u ∉ A.fv) :
    Nominal.NPrf
      (.imp (.classMem (.cv u) (syn_chwcn A))
        (.classEq (syn_cfv (syn_chncodecutfn) (syn_cop (.cv u) (syn_csn (.cv x))))
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
            (.cv x)))) :=
  by
  have p0000 := @g_hwcnpair u A
  have p0001 :=
    @g_opeq1d (.classMem (.cv u) (syn_chwcn A)) (.cv u)
      (syn_cop (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))
      (syn_csn (.cv x)) p0000
  have p0002 :=
    @g_fveq2d (.classMem (.cv u) (syn_chwcn A)) (syn_cop (.cv u) (syn_csn (.cv x)))
      (syn_cop (syn_cop (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))
        (syn_csn (.cv x)))
      (syn_chncodecutfn) p0001
  have p0003 := @g_fvex (.cv u) (syn_c1st)
  have p0004 := @g_fvex (.cv u) (syn_c2nd)
  have p0005 :=
    @g_hncodecutfnval x (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c1st) (.cv u)) p0003
      p0004
  have p0006 :=
    @g_a1i
      (.classEq (syn_cfv (syn_chncodecutfn)
          (syn_cop (syn_cop (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))
            (syn_csn (.cv x))))
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
      (.classMem (.cv u) (syn_chwcn A)) p0005
  have p0007 :=
    @g_eqtrd (.classMem (.cv u) (syn_chwcn A))
      (syn_cfv (syn_chncodecutfn) (syn_cop (.cv u) (syn_csn (.cv x))))
      (syn_cfv (syn_chncodecutfn)
        (syn_cop (syn_cop (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))
          (syn_csn (.cv x))))
      (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))
      p0002 p0006
  exact p0007

@[expose]
noncomputable def g_hncodecutreledgedecodetarget (x : Var) (v : Var) (A : Class)
    (C : Class) (dv_A_C : Disjoint A.fv C.fv) (dv_A_v : v ∉ A.fv) (_dv_A_x : x ∉ A.fv)
    (dv_C_v : v ∉ C.fv) (dv_C_x : x ∉ C.fv) (dv_v_x : v ≠ x) :
    Nominal.NPrf
      (.imp (syn_wbr C (syn_chncodecutrel A) (.cv v)) (syn_wrex x (syn_cfv (syn_c2nd) (.cv v))
          (.classEq C (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv x))))) :=
  by
  let proofSupport : Finset Var :=
    ({ x } : Finset Var) ∪ ({ v } : Finset Var) ∪ A.fv ∪ C.fv
  let z : Var := freshVar proofSupport 0
  let u : Var := freshVar proofSupport 1
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
  have fresh_x_ne_z : x ≠ z := Ne.symm fresh_z_ne_x
  have fresh_z_ne_v : z ≠ v := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_v_ne_z : v ≠ z := Ne.symm fresh_z_ne_v
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_z_not_C : z ∉ C.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have fresh_u : u ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_u_ne_x : u ≠ x := by
    intro h
    exact
      fresh_u
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_u_ne_v : u ≠ v := by
    intro h
    exact
      fresh_u
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_u_not_A : u ∉ A.fv := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_u_not_C : u ∉ C.fv := by
    intro h
    exact fresh_u (Finset.mem_union_right _ (h))
  have fresh_z_ne_u : z ≠ u :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_u_ne_z : u ≠ z := Ne.symm fresh_z_ne_u
  have dv_cache_0001 : Disjoint (A).fv (C).fv := by
    exact
      (show Disjoint (A).fv (C).fv from (show Disjoint (A).fv (C).fv from (by exact dv_A_C)))
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
        simp only [dv_A_v, not_false_eq_true])
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
  have dv_cache_0005 : u ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_u_not_C, not_false_eq_true])
  have dv_cache_0006 : v ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_C_v, not_false_eq_true])
  have dv_cache_0007 : z ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_C, not_false_eq_true])
  have dv_cache_0008 : u ≠ v :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact (show u ≠ v from (by exact fresh_u_ne_v))
  have dv_cache_0009 : u ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (show u ≠ z from (by exact fresh_u_ne_z))
  have dv_cache_0010 : v ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (show v ≠ z from (by exact fresh_v_ne_z))
  have dv_cache_0011 : Disjoint ((Class.cv x)).fv ((syn_cfv (syn_c1st) (.cv v))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (show Disjoint ((Class.cv x)).fv ((syn_cfv (syn_c1st) (.cv v))).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv];
          exact
            (show
              Disjoint (({ x } : Finset Var)) ((((Class.cv v)).fv) ∪ (((syn_c1st)).fv))
              from
              (Finset.disjoint_union_right.mpr
                ⟨(show Disjoint (({ x } : Finset Var)) (((Class.cv v)).fv) from
                    (by
                      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
                      exact
                        (show Disjoint (({ x } : Finset Var)) (({ v } : Finset Var)) from
                          (Finset.disjoint_singleton_left.mpr
                            (show x ∉ ({ v } : Finset Var) from
                              (by
                                simpa only [Finset.mem_singleton] using
                                  (show x ≠ v from (by exact Ne.symm dv_v_x)))))))),
                  (show Disjoint (({ x } : Finset Var)) (((syn_c1st)).fv) from
                    (by
                      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st];
                      exact
                        (show Disjoint (({ x } : Finset Var)) ((∅ : Finset Var)) from
                          (by simp))))⟩))))
  have dv_cache_0012 : x ∉ ((Class.cv z)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_x_ne_z, not_false_eq_true])
  have dv_cache_0013 : x ∉ ((syn_cfv (syn_c2nd) (.cv v))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, (Ne.symm dv_v_x), compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0014 :
    x ∉
      ((Wff.classEq C (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
            (.cv z)))).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutcode,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union,
          Finset.mem_singleton, dv_C_x, fresh_x_ne_z, (Ne.symm dv_v_x),
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0015 :
    z ∉
      ((syn_wrex x (syn_cfv (syn_c2nd) (.cv v)) (.classEq C
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv x))))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutcode,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_z_ne_v, fresh_z_not_C,
          fresh_z_ne_x, compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0016 : z ∉ ((Wff.classMem (.cv u) (syn_chwcn A))).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_u, fresh_z_not_A, or_false, not_false_eq_true])
  have dv_cache_0017 :
    u ∉
      ((syn_wrex x (syn_cfv (syn_c2nd) (.cv v)) (.classEq C
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv x))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutcode,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_u_ne_v, fresh_u_not_C,
          fresh_u_ne_x, compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have p0000 :=
    @g_hncodecutreledgedecode z v u A C dv_cache_0001 dv_cache_0002 dv_cache_0003
      dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
      dv_cache_0010
  have p0001 :=
    @g_simpl
      (syn_wa (.classMem (.cv u) (syn_chwcn A))
        (.classMem (.cv z) (syn_cfv (syn_c2nd) (.cv u))))
      (syn_wa (.classEq C
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv z)))
        (.classEq (.cv v) (.cv u)))
  have p0002 :=
    @g_simpr (.classMem (.cv u) (syn_chwcn A))
      (.classMem (.cv z) (syn_cfv (syn_c2nd) (.cv u)))
  have p0003 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A))
          (.classMem (.cv z) (syn_cfv (syn_c2nd) (.cv u)))) (syn_wa (.classEq C
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv z)))
          (.classEq (.cv v) (.cv u))))
      (syn_wa (.classMem (.cv u) (syn_chwcn A))
        (.classMem (.cv z) (syn_cfv (syn_c2nd) (.cv u))))
      (.classMem (.cv z) (syn_cfv (syn_c2nd) (.cv u))) p0001 p0002
  have p0004 :=
    @g_simpr
      (syn_wa (.classMem (.cv u) (syn_chwcn A))
        (.classMem (.cv z) (syn_cfv (syn_c2nd) (.cv u))))
      (syn_wa (.classEq C
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv z)))
        (.classEq (.cv v) (.cv u)))
  have p0005 :=
    @g_simpr
      (.classEq C (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (.cv z)))
      (.classEq (.cv v) (.cv u))
  have p0006 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A))
          (.classMem (.cv z) (syn_cfv (syn_c2nd) (.cv u)))) (syn_wa (.classEq C
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv z)))
          (.classEq (.cv v) (.cv u))))
      (syn_wa (.classEq C
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv z)))
        (.classEq (.cv v) (.cv u)))
      (.classEq (.cv v) (.cv u)) p0004 p0005
  have p0007 :=
    @g_eqcomd
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A))
          (.classMem (.cv z) (syn_cfv (syn_c2nd) (.cv u)))) (syn_wa (.classEq C
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv z)))
          (.classEq (.cv v) (.cv u))))
      (.cv v) (.cv u) p0006
  have p0008 :=
    @g_fveq2d
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A))
          (.classMem (.cv z) (syn_cfv (syn_c2nd) (.cv u)))) (syn_wa (.classEq C
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv z)))
          (.classEq (.cv v) (.cv u))))
      (.cv u) (.cv v) (syn_c2nd) p0007
  have p0009 :=
    @g_eleqtrd
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A))
          (.classMem (.cv z) (syn_cfv (syn_c2nd) (.cv u)))) (syn_wa (.classEq C
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv z)))
          (.classEq (.cv v) (.cv u))))
      (.cv z) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv v)) p0003 p0008
  have p0011 :=
    @g_simpl
      (.classEq C (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (.cv z)))
      (.classEq (.cv v) (.cv u))
  have p0012 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A))
          (.classMem (.cv z) (syn_cfv (syn_c2nd) (.cv u)))) (syn_wa (.classEq C
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv z)))
          (.classEq (.cv v) (.cv u))))
      (syn_wa (.classEq C
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv z)))
        (.classEq (.cv v) (.cv u)))
      (.classEq C (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (.cv z)))
      p0004 p0011
  have p0014 :=
    @g_simpl (.classMem (.cv u) (syn_chwcn A))
      (.classMem (.cv z) (syn_cfv (syn_c2nd) (.cv u)))
  have p0015 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A))
          (.classMem (.cv z) (syn_cfv (syn_c2nd) (.cv u)))) (syn_wa (.classEq C
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv z)))
          (.classEq (.cv v) (.cv u))))
      (syn_wa (.classMem (.cv u) (syn_chwcn A))
        (.classMem (.cv z) (syn_cfv (syn_c2nd) (.cv u))))
      (.classMem (.cv u) (syn_chwcn A)) p0001 p0014
  have p0016 := @g_hncodecutfnvalhwcn z u A dv_cache_0002
  have p0017 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A))
          (.classMem (.cv z) (syn_cfv (syn_c2nd) (.cv u)))) (syn_wa (.classEq C
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv z)))
          (.classEq (.cv v) (.cv u))))
      (.classMem (.cv u) (syn_chwcn A))
      (.classEq (syn_cfv (syn_chncodecutfn) (syn_cop (.cv u) (syn_csn (.cv z))))
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv z)))
      p0015 p0016
  have p0018 :=
    @g_eqcomd
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A))
          (.classMem (.cv z) (syn_cfv (syn_c2nd) (.cv u)))) (syn_wa (.classEq C
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv z)))
          (.classEq (.cv v) (.cv u))))
      (syn_cfv (syn_chncodecutfn) (syn_cop (.cv u) (syn_csn (.cv z))))
      (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv z))
      p0017
  have p0023 :=
    @g_opeq1d
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A))
          (.classMem (.cv z) (syn_cfv (syn_c2nd) (.cv u)))) (syn_wa (.classEq C
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv z)))
          (.classEq (.cv v) (.cv u))))
      (.cv u) (.cv v) (syn_csn (.cv z)) p0007
  have p0024 :=
    @g_fveq2d
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A))
          (.classMem (.cv z) (syn_cfv (syn_c2nd) (.cv u)))) (syn_wa (.classEq C
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv z)))
          (.classEq (.cv v) (.cv u))))
      (syn_cop (.cv u) (syn_csn (.cv z))) (syn_cop (.cv v) (syn_csn (.cv z)))
      (syn_chncodecutfn) p0023
  have p0031 :=
    @g_eqeltrd
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A))
          (.classMem (.cv z) (syn_cfv (syn_c2nd) (.cv u)))) (syn_wa (.classEq C
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv z)))
          (.classEq (.cv v) (.cv u))))
      (.cv v) (.cv u) (syn_chwcn A) p0006 p0015
  have p0032 := @g_hncodecutfnvalhwcn z v A dv_cache_0003
  have p0033 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A))
          (.classMem (.cv z) (syn_cfv (syn_c2nd) (.cv u)))) (syn_wa (.classEq C
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv z)))
          (.classEq (.cv v) (.cv u))))
      (.classMem (.cv v) (syn_chwcn A))
      (.classEq (syn_cfv (syn_chncodecutfn) (syn_cop (.cv v) (syn_csn (.cv z))))
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv z)))
      p0031 p0032
  have p0034 :=
    @g_n_3eqtrd
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A))
          (.classMem (.cv z) (syn_cfv (syn_c2nd) (.cv u)))) (syn_wa (.classEq C
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv z)))
          (.classEq (.cv v) (.cv u))))
      (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv z))
      (syn_cfv (syn_chncodecutfn) (syn_cop (.cv u) (syn_csn (.cv z))))
      (syn_cfv (syn_chncodecutfn) (syn_cop (.cv v) (syn_csn (.cv z))))
      (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv z))
      p0018 p0024 p0033
  have p0035 :=
    @g_eqtrd
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A))
          (.classMem (.cv z) (syn_cfv (syn_c2nd) (.cv u)))) (syn_wa (.classEq C
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv z)))
          (.classEq (.cv v) (.cv u))))
      C
      (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv z))
      (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv z))
      p0012 p0034
  have p0036 :=
    @g_jca
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A))
          (.classMem (.cv z) (syn_cfv (syn_c2nd) (.cv u)))) (syn_wa (.classEq C
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv z)))
          (.classEq (.cv v) (.cv u))))
      (.classMem (.cv z) (syn_cfv (syn_c2nd) (.cv v)))
      (.classEq C (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
          (.cv z)))
      p0009 p0035
  have p0037 :=
    @g_hnwcutcodeeq3 (.cv x) (.cv z) (syn_cfv (syn_c2nd) (.cv v))
      (syn_cfv (syn_c1st) (.cv v)) dv_cache_0011
  have p0038 :=
    @g_eqeq2d (.classEq (.cv x) (.cv z))
      (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))
      (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv z))
      C p0037
  have p0039 :=
    @g_rspcev
      (.classEq C (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
          (.cv x)))
      (.classEq C (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
          (.cv z)))
      x (.cv z) (syn_cfv (syn_c2nd) (.cv v)) dv_cache_0012 dv_cache_0013 dv_cache_0014
      p0038
  have p0040 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A))
          (.classMem (.cv z) (syn_cfv (syn_c2nd) (.cv u)))) (syn_wa (.classEq C
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv z)))
          (.classEq (.cv v) (.cv u))))
      (syn_wa (.classMem (.cv z) (syn_cfv (syn_c2nd) (.cv v))) (.classEq C
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv z))))
      (syn_wrex x (syn_cfv (syn_c2nd) (.cv v)) (.classEq C
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))
      p0036 p0039
  have p0041 :=
    @g_ex
      (syn_wa (.classMem (.cv u) (syn_chwcn A))
        (.classMem (.cv z) (syn_cfv (syn_c2nd) (.cv u))))
      (syn_wa (.classEq C
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv z)))
        (.classEq (.cv v) (.cv u)))
      (syn_wrex x (syn_cfv (syn_c2nd) (.cv v)) (.classEq C
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))
      p0040
  have p0042 :=
    @g_rexlimdva (.classMem (.cv u) (syn_chwcn A))
      (syn_wa (.classEq C
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv z)))
        (.classEq (.cv v) (.cv u)))
      (syn_wrex x (syn_cfv (syn_c2nd) (.cv v)) (.classEq C
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))
      z (syn_cfv (syn_c2nd) (.cv u)) dv_cache_0015 dv_cache_0016 p0041
  have p0043 :=
    @g_rexlimiv
      (syn_wrex z (syn_cfv (syn_c2nd) (.cv u)) (syn_wa (.classEq C
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv z)))
          (.classEq (.cv v) (.cv u))))
      (syn_wrex x (syn_cfv (syn_c2nd) (.cv v)) (.classEq C
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))
      u (syn_chwcn A) dv_cache_0017 p0042
  have p0044 :=
    @g_syl (syn_wbr C (syn_chncodecutrel A) (.cv v))
      (syn_wrex u (syn_chwcn A) (syn_wrex z (syn_cfv (syn_c2nd) (.cv u)) (syn_wa (.classEq C
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                (.cv z))) (.classEq (.cv v) (.cv u)))))
      (syn_wrex x (syn_cfv (syn_c2nd) (.cv v)) (.classEq C
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))
      p0000 p0043
  exact p0044

@[expose]
noncomputable def g_hncodecutreledgeihwcn (x : Var) (v : Var) (A : Class)
    (dv_A_v : v ∉ A.fv) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem (.cv v) (syn_chwcn A))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))) (syn_wbr
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))
          (syn_chncodecutrel A) (.cv v))) :=
  by
  have dv_cache_0001 : Disjoint (A).fv ((syn_cfv (syn_c1st) (.cv v))).fv := by
    exact
      (show Disjoint (A).fv ((syn_cfv (syn_c1st) (.cv v))).fv from (by
          rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv];
          exact
            (show Disjoint ((A).fv) ((((Class.cv v)).fv) ∪ (((syn_c1st)).fv)) from
              (Finset.disjoint_union_right.mpr
                ⟨(show Disjoint ((A).fv) (((Class.cv v)).fv) from
                    (by
                      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
                      exact
                        (show Disjoint ((A).fv) (({ v } : Finset Var)) from
                          (Finset.disjoint_singleton_right.mpr
                            (show v ∉ (A).fv from (by exact dv_A_v)))))),
                  (show Disjoint ((A).fv) (((syn_c1st)).fv) from
                    (by
                      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st];
                      exact
                        (show Disjoint ((A).fv) ((∅ : Finset Var)) from (by simp))))⟩))))
  have p0000 :=
    @g_simpl (.classMem (.cv v) (syn_chwcn A))
      (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
  have p0001 := @g_hwcnpair v A
  have p0002 :=
    @g_syl
      (syn_wa (.classMem (.cv v) (syn_chwcn A))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))))
      (.classMem (.cv v) (syn_chwcn A))
      (.classEq (.cv v) (syn_cop (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))))
      p0000 p0001
  have p0004 :=
    @g_eqeltrrd
      (syn_wa (.classMem (.cv v) (syn_chwcn A))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))))
      (.cv v) (syn_cop (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)))
      (syn_chwcn A) p0002 p0000
  have p0005 :=
    @g_simpr (.classMem (.cv v) (syn_chwcn A))
      (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
  have p0006 :=
    @g_jca
      (syn_wa (.classMem (.cv v) (syn_chwcn A))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))))
      (.classMem (syn_cop (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)))
        (syn_chwcn A))
      (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))) p0004 p0005
  have p0007 := @g_fvex (.cv v) (syn_c1st)
  have p0008 := @g_fvex (.cv v) (syn_c2nd)
  have p0009 :=
    @g_hncodecutreledgei x A (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (syn_c1st) (.cv v))
      dv_cache_0001 p0007 p0008
  have p0010 :=
    @g_syl
      (syn_wa (.classMem (.cv v) (syn_chwcn A))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))))
      (syn_wa (.classMem (syn_cop (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)))
          (syn_chwcn A)) (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))))
      (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
          (.cv x)) (syn_chncodecutrel A)
        (syn_cop (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))))
      p0006 p0009
  have p0014 :=
    @g_eqcomd
      (syn_wa (.classMem (.cv v) (syn_chwcn A))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))))
      (.cv v) (syn_cop (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))) p0002
  have p0015 :=
    @g_breq2d
      (syn_wa (.classMem (.cv v) (syn_chwcn A))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))))
      (syn_cop (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))) (.cv v)
      (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))
      (syn_chncodecutrel A) p0014
  have p0016 :=
    @g_mpbid
      (syn_wa (.classMem (.cv v) (syn_chwcn A))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))))
      (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
          (.cv x)) (syn_chncodecutrel A)
        (syn_cop (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))))
      (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
          (.cv x)) (syn_chncodecutrel A) (.cv v))
      p0010 p0015
  exact p0016


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk017Compact001Part022`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_hncodecmpsetstrictcutsemdv (x : Var) (v : Var) (u : Var) (A : Class)
    (_dv_A_u : u ∉ A.fv) (dv_A_v : v ∉ A.fv) (dv_A_x : x ∉ A.fv) (dv_u_x : u ≠ x)
    (dv_v_x : v ≠ x) :
    Nominal.NPrf
      (.imp (.classMem (.cv v) (syn_chwcn A))
        (syn_wb (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v))
          (syn_wo (syn_wbr (.cv u) (syn_chwniso A) (.cv v))
            (syn_wrex x (syn_cfv (syn_c2nd) (.cv v)) (syn_wbr (.cv u) (syn_chwniso A)
                (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                  (.cv x))))))) :=
  by
  let proofSupport : Finset Var :=
    ({ x } : Finset Var) ∪ ({ v } : Finset Var) ∪ ({ u } : Finset Var) ∪ A.fv
  let c : Var := freshVar proofSupport 0
  let z : Var := freshVar proofSupport 1
  have fresh_c : c ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_c_ne_x : c ≠ x := by
    intro h
    exact
      fresh_c
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_x_ne_c : x ≠ c := Ne.symm fresh_c_ne_x
  have fresh_c_ne_v : c ≠ v := by
    intro h
    exact
      fresh_c
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_v_ne_c : v ≠ c := Ne.symm fresh_c_ne_v
  have fresh_c_ne_u : c ≠ u := by
    intro h
    exact
      fresh_c
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_u_ne_c : u ≠ c := Ne.symm fresh_c_ne_u
  have fresh_c_not_A : c ∉ A.fv := by
    intro h
    exact fresh_c (Finset.mem_union_right _ (h))
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
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have fresh_c_ne_z : c ≠ z :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_z_ne_c : z ≠ c := Ne.symm fresh_c_ne_z
  have dv_cache_0001 : c ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_c_not_A, not_false_eq_true])
  have dv_cache_0002 : u ≠ c := by
    clear dv_cache_0001
    exact (show u ≠ c from (by exact fresh_u_ne_c))
  have dv_cache_0003 : v ≠ c :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact (show v ≠ c from (by exact fresh_v_ne_c))
  have dv_cache_0004 : Disjoint (A).fv ((Class.cv c)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (show Disjoint (A).fv ((Class.cv c)).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint ((A).fv) (({ c } : Finset Var)) from
              (Finset.disjoint_singleton_right.mpr
                (show c ∉ (A).fv from (by exact fresh_c_not_A))))))
  have dv_cache_0005 : v ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_v, not_false_eq_true])
  have dv_cache_0006 : z ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_A, not_false_eq_true])
  have dv_cache_0007 : v ∉ ((Class.cv c)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_v_ne_c, not_false_eq_true])
  have dv_cache_0008 : z ∉ ((Class.cv c)).fv :=
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
          fresh_z_ne_c, not_false_eq_true])
  have dv_cache_0009 : v ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (show v ≠ z from (by exact fresh_v_ne_z))
  have dv_cache_0010 : Disjoint ((Class.cv x)).fv ((syn_cfv (syn_c1st) (.cv v))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (show Disjoint ((Class.cv x)).fv ((syn_cfv (syn_c1st) (.cv v))).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv];
          exact
            (show
              Disjoint (({ x } : Finset Var)) ((((Class.cv v)).fv) ∪ (((syn_c1st)).fv))
              from
              (Finset.disjoint_union_right.mpr
                ⟨(show Disjoint (({ x } : Finset Var)) (((Class.cv v)).fv) from
                    (by
                      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
                      exact
                        (show Disjoint (({ x } : Finset Var)) (({ v } : Finset Var)) from
                          (Finset.disjoint_singleton_left.mpr
                            (show x ∉ ({ v } : Finset Var) from
                              (by
                                simpa only [Finset.mem_singleton] using
                                  (show x ≠ v from (by exact Ne.symm dv_v_x)))))))),
                  (show Disjoint (({ x } : Finset Var)) (((syn_c1st)).fv) from
                    (by
                      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st];
                      exact
                        (show Disjoint (({ x } : Finset Var)) ((∅ : Finset Var)) from
                          (by simp))))⟩))))
  have dv_cache_0011 : x ∉ ((Class.cv z)).fv :=
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
          fresh_x_ne_z, not_false_eq_true])
  have dv_cache_0012 : x ∉ ((syn_cfv (syn_c2nd) (.cv v))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, (Ne.symm dv_v_x), compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0013 :
    x ∉
      ((syn_wbr (.cv u) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
            (.cv z)))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutcode,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union,
          Finset.mem_singleton, (Ne.symm dv_u_x), fresh_x_ne_z, (Ne.symm dv_v_x), dv_A_x,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0014 :
    z ∉
      ((syn_wrex x (syn_cfv (syn_c2nd) (.cv v)) (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv x))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
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
          Finset.mem_erase, Finset.mem_singleton, fresh_z_ne_v, fresh_z_ne_u,
          fresh_z_ne_x, fresh_z_not_A, compact_fv_not_mem_empty, or_false, and_false,
          not_false_eq_true])
  have dv_cache_0015 : z ∉ ((syn_wbr (.cv u) (syn_chwniso A) (.cv c))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_u, fresh_z_ne_c, fresh_z_not_A, or_false,
          not_false_eq_true])
  have dv_cache_0016 :
    c ∉
      ((syn_wrex x (syn_cfv (syn_c2nd) (.cv v)) (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv x))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact
      (by
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
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
          Finset.mem_erase, Finset.mem_singleton, fresh_c_ne_v, fresh_c_ne_u,
          fresh_c_ne_x, fresh_c_not_A, compact_fv_not_mem_empty, or_false, and_false,
          not_false_eq_true])
  have dv_cache_0017 :
    c ∉
      ((syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
          (.cv x))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact
      (by
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutcode,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union,
          Finset.mem_singleton, fresh_c_ne_x, fresh_c_ne_v, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0018 :
    c ∉
      ((syn_wa (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))
          (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv x)) (syn_chncodecutrel A) (.cv v)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact
      (by
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutcode,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodecutrel,
          Finset.mem_union, Finset.mem_singleton, fresh_c_ne_u, fresh_c_ne_x,
          fresh_c_ne_v, fresh_c_not_A, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0019 :
    c ∉
      ((syn_wa (.classMem (.cv v) (syn_chwcn A))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018
    exact
      (by
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union,
          Finset.mem_singleton, fresh_c_ne_v, fresh_c_not_A, fresh_c_ne_x,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0020 :
    x ∉
      ((syn_wex c (syn_wa (syn_wbr (.cv u) (syn_chwniso A) (.cv c))
            (syn_wbr (.cv c) (syn_chncodecutrel A) (.cv v))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodecutrel,
          Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, (Ne.symm dv_u_x),
          fresh_x_ne_c, dv_A_x, (Ne.symm dv_v_x), or_false, and_false, not_false_eq_true])
  have dv_cache_0021 : x ∉ ((Wff.classMem (.cv v) (syn_chwcn A))).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, Finset.mem_union,
          Finset.mem_singleton, (Ne.symm dv_v_x), dv_A_x, or_false, not_false_eq_true])
  have p0000 := @g_brhncodecmpset c v u A dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0001 :=
    @g_a1i
      (syn_wb (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v))
        (syn_wo (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wex c
            (syn_wa (syn_wbr (.cv u) (syn_chwniso A) (.cv c))
              (syn_wbr (.cv c) (syn_chncodecutrel A) (.cv v))))))
      (.classMem (.cv v) (syn_chwcn A)) p0000
  have p0002 :=
    @g_hncodecutreledgedecodetarget z v A (.cv c) dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
  have p0003 :=
    @g_simpl
      (syn_wa (syn_wbr (.cv u) (syn_chwniso A) (.cv c))
        (.classMem (.cv z) (syn_cfv (syn_c2nd) (.cv v))))
      (.classEq (.cv c)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv z)))
  have p0004 :=
    @g_simpr (syn_wbr (.cv u) (syn_chwniso A) (.cv c))
      (.classMem (.cv z) (syn_cfv (syn_c2nd) (.cv v)))
  have p0005 :=
    @g_syl
      (syn_wa (syn_wa (syn_wbr (.cv u) (syn_chwniso A) (.cv c))
          (.classMem (.cv z) (syn_cfv (syn_c2nd) (.cv v)))) (.classEq (.cv c)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv z))))
      (syn_wa (syn_wbr (.cv u) (syn_chwniso A) (.cv c))
        (.classMem (.cv z) (syn_cfv (syn_c2nd) (.cv v))))
      (.classMem (.cv z) (syn_cfv (syn_c2nd) (.cv v))) p0003 p0004
  have p0007 :=
    @g_simpl (syn_wbr (.cv u) (syn_chwniso A) (.cv c))
      (.classMem (.cv z) (syn_cfv (syn_c2nd) (.cv v)))
  have p0008 :=
    @g_syl
      (syn_wa (syn_wa (syn_wbr (.cv u) (syn_chwniso A) (.cv c))
          (.classMem (.cv z) (syn_cfv (syn_c2nd) (.cv v)))) (.classEq (.cv c)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv z))))
      (syn_wa (syn_wbr (.cv u) (syn_chwniso A) (.cv c))
        (.classMem (.cv z) (syn_cfv (syn_c2nd) (.cv v))))
      (syn_wbr (.cv u) (syn_chwniso A) (.cv c)) p0003 p0007
  have p0009 :=
    @g_simpr
      (syn_wa (syn_wbr (.cv u) (syn_chwniso A) (.cv c))
        (.classMem (.cv z) (syn_cfv (syn_c2nd) (.cv v))))
      (.classEq (.cv c)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv z)))
  have p0010 :=
    @g_breq2d
      (syn_wa (syn_wa (syn_wbr (.cv u) (syn_chwniso A) (.cv c))
          (.classMem (.cv z) (syn_cfv (syn_c2nd) (.cv v)))) (.classEq (.cv c)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv z))))
      (.cv c)
      (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv z))
      (.cv u) (syn_chwniso A) p0009
  have p0011 :=
    @g_mpbid
      (syn_wa (syn_wa (syn_wbr (.cv u) (syn_chwniso A) (.cv c))
          (.classMem (.cv z) (syn_cfv (syn_c2nd) (.cv v)))) (.classEq (.cv c)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv z))))
      (syn_wbr (.cv u) (syn_chwniso A) (.cv c))
      (syn_wbr (.cv u) (syn_chwniso A)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv z)))
      p0008 p0010
  have p0012 :=
    @g_jca
      (syn_wa (syn_wa (syn_wbr (.cv u) (syn_chwniso A) (.cv c))
          (.classMem (.cv z) (syn_cfv (syn_c2nd) (.cv v)))) (.classEq (.cv c)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv z))))
      (.classMem (.cv z) (syn_cfv (syn_c2nd) (.cv v)))
      (syn_wbr (.cv u) (syn_chwniso A)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv z)))
      p0005 p0011
  have p0013 :=
    @g_hnwcutcodeeq3 (.cv x) (.cv z) (syn_cfv (syn_c2nd) (.cv v))
      (syn_cfv (syn_c1st) (.cv v)) dv_cache_0010
  have p0014 :=
    @g_breq2d (.classEq (.cv x) (.cv z))
      (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))
      (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv z))
      (.cv u) (syn_chwniso A) p0013
  have p0015 :=
    @g_rspcev
      (syn_wbr (.cv u) (syn_chwniso A)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))
      (syn_wbr (.cv u) (syn_chwniso A)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv z)))
      x (.cv z) (syn_cfv (syn_c2nd) (.cv v)) dv_cache_0011 dv_cache_0012 dv_cache_0013
      p0014
  have p0016 :=
    @g_syl
      (syn_wa (syn_wa (syn_wbr (.cv u) (syn_chwniso A) (.cv c))
          (.classMem (.cv z) (syn_cfv (syn_c2nd) (.cv v)))) (.classEq (.cv c)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv z))))
      (syn_wa (.classMem (.cv z) (syn_cfv (syn_c2nd) (.cv v))) (syn_wbr (.cv u) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv z))))
      (syn_wrex x (syn_cfv (syn_c2nd) (.cv v)) (syn_wbr (.cv u) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))
      p0012 p0015
  have p0017 :=
    @g_ex
      (syn_wa (syn_wbr (.cv u) (syn_chwniso A) (.cv c))
        (.classMem (.cv z) (syn_cfv (syn_c2nd) (.cv v))))
      (.classEq (.cv c)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv z)))
      (syn_wrex x (syn_cfv (syn_c2nd) (.cv v)) (syn_wbr (.cv u) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))
      p0016
  have p0018 :=
    @g_rexlimdva (syn_wbr (.cv u) (syn_chwniso A) (.cv c))
      (.classEq (.cv c)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv z)))
      (syn_wrex x (syn_cfv (syn_c2nd) (.cv v)) (syn_wbr (.cv u) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))
      z (syn_cfv (syn_c2nd) (.cv v)) dv_cache_0014 dv_cache_0015 p0017
  have p0019 :=
    @g_syl5 (syn_wbr (.cv c) (syn_chncodecutrel A) (.cv v))
      (syn_wrex z (syn_cfv (syn_c2nd) (.cv v)) (.classEq (.cv c)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv z))))
      (syn_wbr (.cv u) (syn_chwniso A) (.cv c))
      (syn_wrex x (syn_cfv (syn_c2nd) (.cv v)) (syn_wbr (.cv u) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))
      p0002 p0018
  have p0020 :=
    @g_imp (syn_wbr (.cv u) (syn_chwniso A) (.cv c))
      (syn_wbr (.cv c) (syn_chncodecutrel A) (.cv v))
      (syn_wrex x (syn_cfv (syn_c2nd) (.cv v)) (syn_wbr (.cv u) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))
      p0019
  have p0021 :=
    @g_exlimiv
      (syn_wa (syn_wbr (.cv u) (syn_chwniso A) (.cv c))
        (syn_wbr (.cv c) (syn_chncodecutrel A) (.cv v)))
      (syn_wrex x (syn_cfv (syn_c2nd) (.cv v)) (syn_wbr (.cv u) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))
      c dv_cache_0016 p0020
  have p0022 :=
    @g_a1i
      (.imp (syn_wex c (syn_wa (syn_wbr (.cv u) (syn_chwniso A) (.cv c))
            (syn_wbr (.cv c) (syn_chncodecutrel A) (.cv v))))
        (syn_wrex x (syn_cfv (syn_c2nd) (.cv v)) (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv x)))))
      (.classMem (.cv v) (syn_chwcn A)) p0021
  have p0023 :=
    @g_simpr
      (syn_wa (.classMem (.cv v) (syn_chwcn A))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))))
      (syn_wbr (.cv u) (syn_chwniso A)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))
  have p0024 :=
    @g_simpl
      (syn_wa (.classMem (.cv v) (syn_chwcn A))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))))
      (syn_wbr (.cv u) (syn_chwniso A)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))
  have p0025 := @g_hncodecutreledgeihwcn x v A dv_cache_0005
  have p0026 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv v) (syn_chwcn A))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))) (syn_wbr (.cv u) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))
      (syn_wa (.classMem (.cv v) (syn_chwcn A))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))))
      (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
          (.cv x)) (syn_chncodecutrel A) (.cv v))
      p0024 p0025
  have p0027 :=
    @g_jca
      (syn_wa (syn_wa (.classMem (.cv v) (syn_chwcn A))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))) (syn_wbr (.cv u) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))
      (syn_wbr (.cv u) (syn_chwniso A)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))
      (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
          (.cv x)) (syn_chncodecutrel A) (.cv v))
      p0023 p0026
  have p0028 :=
    @g_ex
      (syn_wa (.classMem (.cv v) (syn_chwcn A))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))))
      (syn_wbr (.cv u) (syn_chwniso A)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))
      (syn_wa (syn_wbr (.cv u) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))
        (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
            (.cv x)) (syn_chncodecutrel A) (.cv v)))
      p0027
  have p0029 :=
    @g_simpl (.classMem (.cv v) (syn_chwcn A))
      (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))
  have p0030 := @g_hncodecutfnvalhwcn x v A dv_cache_0005
  have p0031 :=
    @g_syl
      (syn_wa (.classMem (.cv v) (syn_chwcn A))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))))
      (.classMem (.cv v) (syn_chwcn A))
      (.classEq (syn_cfv (syn_chncodecutfn) (syn_cop (.cv v) (syn_csn (.cv x))))
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))
      p0029 p0030
  have p0032 := @g_fvex (syn_cop (.cv v) (syn_csn (.cv x))) (syn_chncodecutfn)
  have p0033 :=
    @g_a1i
      (.classMem (syn_cfv (syn_chncodecutfn) (syn_cop (.cv v) (syn_csn (.cv x)))) (syn_cvv))
      (syn_wa (.classMem (.cv v) (syn_chwcn A))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))))
      p0032
  have p0034 :=
    @g_eqeltrrd
      (syn_wa (.classMem (.cv v) (syn_chwcn A))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))))
      (syn_cfv (syn_chncodecutfn) (syn_cop (.cv v) (syn_csn (.cv x))))
      (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))
      (syn_cvv) p0031 p0033
  have p0035 :=
    @g_simpr
      (syn_wa (.classMem (.cv v) (syn_chwcn A))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))))
      (.classEq (.cv c)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))
  have p0036 :=
    @g_id
      (.classEq (.cv c)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))
  have p0037 :=
    @g_breq2d
      (.classEq (.cv c)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))
      (.cv c)
      (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))
      (.cv u) (syn_chwniso A) p0036
  have p0039 :=
    @g_breq1d
      (.classEq (.cv c)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))
      (.cv c)
      (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))
      (.cv v) (syn_chncodecutrel A) p0036
  have p0040 :=
    @g_anbi12d
      (.classEq (.cv c)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))
      (syn_wbr (.cv u) (syn_chwniso A) (.cv c))
      (syn_wbr (.cv u) (syn_chwniso A)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))
      (syn_wbr (.cv c) (syn_chncodecutrel A) (.cv v))
      (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
          (.cv x)) (syn_chncodecutrel A) (.cv v))
      p0037 p0039
  have p0041 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv v) (syn_chwcn A))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))) (.classEq (.cv c)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))
      (.classEq (.cv c)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))
      (syn_wb (syn_wa (syn_wbr (.cv u) (syn_chwniso A) (.cv c))
          (syn_wbr (.cv c) (syn_chncodecutrel A) (.cv v))) (syn_wa
          (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))
          (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv x)) (syn_chncodecutrel A) (.cv v))))
      p0035 p0040
  have p0042 :=
    @g_biimprd
      (syn_wa (syn_wa (.classMem (.cv v) (syn_chwcn A))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v)))) (.classEq (.cv c)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))
      (syn_wa (syn_wbr (.cv u) (syn_chwniso A) (.cv c))
        (syn_wbr (.cv c) (syn_chncodecutrel A) (.cv v)))
      (syn_wa (syn_wbr (.cv u) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))
        (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
            (.cv x)) (syn_chncodecutrel A) (.cv v)))
      p0041
  have p0043 :=
    @g_spcimedv
      (syn_wa (.classMem (.cv v) (syn_chwcn A))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))))
      (syn_wa (syn_wbr (.cv u) (syn_chwniso A) (.cv c))
        (syn_wbr (.cv c) (syn_chncodecutrel A) (.cv v)))
      (syn_wa (syn_wbr (.cv u) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))
        (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
            (.cv x)) (syn_chncodecutrel A) (.cv v)))
      c
      (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))
      (syn_cvv) dv_cache_0017 dv_cache_0018 dv_cache_0019 p0034 p0042
  have p0044 :=
    @g_syld
      (syn_wa (.classMem (.cv v) (syn_chwcn A))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv v))))
      (syn_wbr (.cv u) (syn_chwniso A)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))
      (syn_wa (syn_wbr (.cv u) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))
        (syn_wbr (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
            (.cv x)) (syn_chncodecutrel A) (.cv v)))
      (syn_wex c (syn_wa (syn_wbr (.cv u) (syn_chwniso A) (.cv c))
          (syn_wbr (.cv c) (syn_chncodecutrel A) (.cv v))))
      p0028 p0043
  have p0045 :=
    @g_rexlimdva (.classMem (.cv v) (syn_chwcn A))
      (syn_wbr (.cv u) (syn_chwniso A)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))
      (syn_wex c (syn_wa (syn_wbr (.cv u) (syn_chwniso A) (.cv c))
          (syn_wbr (.cv c) (syn_chncodecutrel A) (.cv v))))
      x (syn_cfv (syn_c2nd) (.cv v)) dv_cache_0020 dv_cache_0021 p0044
  have p0046 :=
    @g_impbid (.classMem (.cv v) (syn_chwcn A))
      (syn_wex c (syn_wa (syn_wbr (.cv u) (syn_chwniso A) (.cv c))
          (syn_wbr (.cv c) (syn_chncodecutrel A) (.cv v))))
      (syn_wrex x (syn_cfv (syn_c2nd) (.cv v)) (syn_wbr (.cv u) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))
      p0022 p0045
  have p0047 :=
    @g_orbi2d (.classMem (.cv v) (syn_chwcn A))
      (syn_wex c (syn_wa (syn_wbr (.cv u) (syn_chwniso A) (.cv c))
          (syn_wbr (.cv c) (syn_chncodecutrel A) (.cv v))))
      (syn_wrex x (syn_cfv (syn_c2nd) (.cv v)) (syn_wbr (.cv u) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))
      (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) p0046
  have p0048 :=
    @g_bitrd (.classMem (.cv v) (syn_chwcn A))
      (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v))
      (syn_wo (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wex c
          (syn_wa (syn_wbr (.cv u) (syn_chwniso A) (.cv c))
            (syn_wbr (.cv c) (syn_chncodecutrel A) (.cv v)))))
      (syn_wo (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wrex x (syn_cfv (syn_c2nd) (.cv v))
          (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv x)))))
      p0001 p0047
  exact p0048

@[expose]
noncomputable def g_hncodecmpsetrefndv (A : Class) :
    Nominal.NPrf
      (.imp (.classMem A (syn_cvv)) (syn_wbr (syn_chncodecmpset A) (syn_cref) (syn_chwcn A))) :=
  by
  let proofSupport : Finset Var := A.fv
  let u : Var := freshVar proofSupport 0
  let x : Var := freshVar proofSupport 1
  have fresh_u : u ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_u_not_A : u ∉ A.fv := by
    intro h
    exact fresh_u (h)
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (h)
  have fresh_u_ne_x : u ≠ x :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have dv_cache_0001 : u ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_u_not_A, not_false_eq_true])
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
  have dv_cache_0003 : u ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact (show u ≠ x from (by exact fresh_u_ne_x))
  have dv_cache_0004 : u ∉ ((syn_chwcn A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
          fresh_u_not_A, not_false_eq_true])
  have dv_cache_0005 : u ∉ ((syn_chncodecmpset A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodecmpset,
          fresh_u_not_A, not_false_eq_true])
  have dv_cache_0006 : u ∉ ((Wff.classMem A (syn_cvv))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
          fresh_u_not_A, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have p0000 := @g_hncodecmpsetexg A
  have p0001 := @g_hwcnexg A
  have p0002 := @g_simpr (.classMem A (syn_cvv)) (.classMem (.cv u) (syn_chwcn A))
  have p0003 := @g_hwnisorefli u A dv_cache_0001
  have p0004 :=
    @g_orc (syn_wbr (.cv u) (syn_chwniso A) (.cv u))
      (syn_wrex x (syn_cfv (syn_c2nd) (.cv u)) (syn_wbr (.cv u) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x))))
  have p0005 :=
    @g_syl (.classMem (.cv u) (syn_chwcn A)) (syn_wbr (.cv u) (syn_chwniso A) (.cv u))
      (syn_wo (syn_wbr (.cv u) (syn_chwniso A) (.cv u)) (syn_wrex x (syn_cfv (syn_c2nd) (.cv u))
          (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
              (.cv x)))))
      p0003 p0004
  have p0006 :=
    @g_hncodecmpsetstrictcutsemdv x u u A dv_cache_0001 dv_cache_0001 dv_cache_0002
      dv_cache_0003 dv_cache_0003
  have p0007 :=
    @g_mpbird (.classMem (.cv u) (syn_chwcn A))
      (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv u))
      (syn_wo (syn_wbr (.cv u) (syn_chwniso A) (.cv u)) (syn_wrex x (syn_cfv (syn_c2nd) (.cv u))
          (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
              (.cv x)))))
      p0005 p0006
  have p0008 :=
    @g_syl (syn_wa (.classMem A (syn_cvv)) (.classMem (.cv u) (syn_chwcn A)))
      (.classMem (.cv u) (syn_chwcn A)) (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv u))
      p0002 p0007
  have p0009 :=
    @g_refrd (.classMem A (syn_cvv)) u (syn_chwcn A) (syn_chncodecmpset A) (syn_cvv)
      (syn_cvv) dv_cache_0004 dv_cache_0005 dv_cache_0006 p0000 p0001 p0008
  exact p0009

@[expose]
noncomputable def g_hncodecutreltargetclndv (v : Var) (A : Class) (C : Class)
    (dv_A_C : Disjoint A.fv C.fv) (dv_A_v : v ∉ A.fv) (dv_C_v : v ∉ C.fv) :
    Nominal.NPrf
      (.imp (syn_wbr C (syn_chncodecutrel A) (.cv v)) (.classMem (.cv v) (syn_chwcn A))) :=
  by
  let proofSupport : Finset Var := ({ v } : Finset Var) ∪ A.fv ∪ C.fv
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
  have fresh_v_ne_x : v ≠ x := Ne.symm fresh_x_ne_v
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_C : x ∉ C.fv := by
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
  have fresh_u_not_C : u ∉ C.fv := by
    intro h
    exact fresh_u (Finset.mem_union_right _ (h))
  have fresh_x_ne_u : x ≠ u :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_u_ne_x : u ≠ x := Ne.symm fresh_x_ne_u
  have dv_cache_0001 : Disjoint (A).fv (C).fv := by
    exact
      (show Disjoint (A).fv (C).fv from (show Disjoint (A).fv (C).fv from (by exact dv_A_C)))
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
        simp only [dv_A_v, not_false_eq_true])
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
  have dv_cache_0005 : u ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_u_not_C, not_false_eq_true])
  have dv_cache_0006 : v ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_C_v, not_false_eq_true])
  have dv_cache_0007 : x ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_C, not_false_eq_true])
  have dv_cache_0008 : u ≠ v :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact (show u ≠ v from (by exact fresh_u_ne_v))
  have dv_cache_0009 : u ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (show u ≠ x from (by exact fresh_u_ne_x))
  have dv_cache_0010 : v ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (show v ≠ x from (by exact fresh_v_ne_x))
  have dv_cache_0011 : x ∉ ((Wff.classMem (.cv v) (syn_chwcn A))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
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
  have dv_cache_0012 : x ∉ ((Wff.classMem (.cv u) (syn_chwcn A))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_u, fresh_x_not_A, or_false, not_false_eq_true])
  have dv_cache_0013 : u ∉ ((Wff.classMem (.cv v) (syn_chwcn A))).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, Finset.mem_union,
          Finset.mem_singleton, fresh_u_ne_v, fresh_u_not_A, or_false, not_false_eq_true])
  have p0000 :=
    @g_hncodecutreledgedecode x v u A C dv_cache_0001 dv_cache_0002 dv_cache_0003
      dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
      dv_cache_0010
  have p0001 :=
    @g_simpl
      (syn_wa (.classMem (.cv u) (syn_chwcn A))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
      (syn_wa (.classEq C
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
        (.classEq (.cv v) (.cv u)))
  have p0002 :=
    @g_simpl (.classMem (.cv u) (syn_chwcn A))
      (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
  have p0003 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (syn_wa (.classEq C
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
          (.classEq (.cv v) (.cv u))))
      (syn_wa (.classMem (.cv u) (syn_chwcn A))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
      (.classMem (.cv u) (syn_chwcn A)) p0001 p0002
  have p0004 :=
    @g_simpr
      (syn_wa (.classMem (.cv u) (syn_chwcn A))
        (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u))))
      (syn_wa (.classEq C
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
        (.classEq (.cv v) (.cv u)))
  have p0005 :=
    @g_simpr
      (.classEq C (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
          (.cv x)))
      (.classEq (.cv v) (.cv u))
  have p0006 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (syn_wa (.classEq C
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
          (.classEq (.cv v) (.cv u))))
      (syn_wa (.classEq C
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
        (.classEq (.cv v) (.cv u)))
      (.classEq (.cv v) (.cv u)) p0004 p0005
  have p0007 :=
    @g_eleq1d
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (syn_wa (.classEq C
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
          (.classEq (.cv v) (.cv u))))
      (.cv v) (.cv u) (syn_chwcn A) p0006
  have p0008 :=
    @g_mpbird
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A))
          (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))) (syn_wa (.classEq C
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
          (.classEq (.cv v) (.cv u))))
      (.classMem (.cv v) (syn_chwcn A)) (.classMem (.cv u) (syn_chwcn A)) p0003 p0007
  have p0009 :=
    @g_exp31 (.classMem (.cv u) (syn_chwcn A))
      (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
      (syn_wa (.classEq C
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
        (.classEq (.cv v) (.cv u)))
      (.classMem (.cv v) (syn_chwcn A)) p0008
  have p0010 :=
    @g_imp (.classMem (.cv u) (syn_chwcn A))
      (.classMem (.cv x) (syn_cfv (syn_c2nd) (.cv u)))
      (.imp (syn_wa (.classEq C
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
          (.classEq (.cv v) (.cv u))) (.classMem (.cv v) (syn_chwcn A)))
      p0009
  have p0011 :=
    @g_rexlimdva (.classMem (.cv u) (syn_chwcn A))
      (syn_wa (.classEq C
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
        (.classEq (.cv v) (.cv u)))
      (.classMem (.cv v) (syn_chwcn A)) x (syn_cfv (syn_c2nd) (.cv u)) dv_cache_0011
      dv_cache_0012 p0010
  have p0012 :=
    @g_rexlimiv
      (syn_wrex x (syn_cfv (syn_c2nd) (.cv u)) (syn_wa (.classEq C
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)) (.cv x)))
          (.classEq (.cv v) (.cv u))))
      (.classMem (.cv v) (syn_chwcn A)) u (syn_chwcn A) dv_cache_0013 p0011
  have p0013 :=
    @g_syl (syn_wbr C (syn_chncodecutrel A) (.cv v))
      (syn_wrex u (syn_chwcn A) (syn_wrex x (syn_cfv (syn_c2nd) (.cv u)) (syn_wa (.classEq C
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
                (.cv x))) (.classEq (.cv v) (.cv u)))))
      (.classMem (.cv v) (syn_chwcn A)) p0000 p0012
  exact p0013


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk017Compact001Part023`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_hncodecmpsetssxpndv (A : Class) :
    Nominal.NPrf (syn_wss (syn_chncodecmpset A) (syn_cxp (syn_chwcn A) (syn_chwcn A))) :=
  by
  let proofSupport : Finset Var := A.fv
  let u : Var := freshVar proofSupport 0
  let v : Var := freshVar proofSupport 1
  let c : Var := freshVar proofSupport 2
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
  have fresh_c : c ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_c_not_A : c ∉ A.fv := by
    intro h
    exact fresh_c (h)
  have fresh_u_ne_v : u ≠ v :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_u_ne_c : u ≠ c :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_c_ne_u : c ≠ u := Ne.symm fresh_u_ne_c
  have fresh_v_ne_c : v ≠ c :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_c_ne_v : c ≠ v := Ne.symm fresh_v_ne_c
  have dv_cache_0001 : c ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_c_not_A, not_false_eq_true])
  have dv_cache_0002 : u ≠ c := by
    clear dv_cache_0001
    exact (show u ≠ c from (by exact fresh_u_ne_c))
  have dv_cache_0003 : v ≠ c :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact (show v ≠ c from (by exact fresh_v_ne_c))
  have dv_cache_0004 : u ≠ v :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show u ≠ v from (by exact fresh_u_ne_v))
  have dv_cache_0005 : Disjoint (A).fv ((Class.cv c)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (show Disjoint (A).fv ((Class.cv c)).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint ((A).fv) (({ c } : Finset Var)) from
              (Finset.disjoint_singleton_right.mpr
                (show c ∉ (A).fv from (by exact fresh_c_not_A))))))
  have dv_cache_0006 : v ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_v_not_A, not_false_eq_true])
  have dv_cache_0007 : v ∉ ((Class.cv c)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_v_ne_c, not_false_eq_true])
  have dv_cache_0008 :
    c ∉
      ((syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, Finset.mem_union,
          Finset.mem_singleton, fresh_c_ne_u, fresh_c_not_A, fresh_c_ne_v, or_false,
          not_false_eq_true])
  have dv_cache_0009 : u ∉ ((syn_chncodecmpset A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodecmpset,
          fresh_u_not_A, not_false_eq_true])
  have dv_cache_0010 : v ∉ ((syn_chncodecmpset A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodecmpset,
          fresh_v_not_A, not_false_eq_true])
  have dv_cache_0011 : u ∉ ((syn_cxp (syn_chwcn A) (syn_chwcn A))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, Finset.mem_union,
          fresh_u_not_A, or_false, not_false_eq_true])
  have dv_cache_0012 : v ∉ ((syn_cxp (syn_chwcn A) (syn_chwcn A))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, Finset.mem_union,
          fresh_v_not_A, or_false, not_false_eq_true])
  have p0000 := (Nominal.biimpRefl (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v)))
  have p0001 :=
    @g_biimpri (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v))
      (.classMem (syn_cop (.cv u) (.cv v)) (syn_chncodecmpset A)) p0000
  have p0002 := @g_brhncodecmpset c v u A dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0003 :=
    @g_biimpi (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v))
      (syn_wo (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wex c
          (syn_wa (syn_wbr (.cv u) (syn_chwniso A) (.cv c))
            (syn_wbr (.cv c) (syn_chncodecutrel A) (.cv v)))))
      p0002
  have p0004 := @g_hwnisohwisob v u A dv_cache_0004
  have p0005 :=
    @g_biimpi (syn_wbr (.cv u) (syn_chwniso A) (.cv v))
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (syn_wbr (.cv u) (syn_chwiso A) (.cv v)))
      p0004
  have p0006 :=
    @g_simpl (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
      (syn_wbr (.cv u) (syn_chwiso A) (.cv v))
  have p0007 :=
    @g_syl (syn_wbr (.cv u) (syn_chwniso A) (.cv v))
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
        (syn_wbr (.cv u) (syn_chwiso A) (.cv v)))
      (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) p0005
      p0006
  have p0008 :=
    @g_simpl (syn_wbr (.cv u) (syn_chwniso A) (.cv c))
      (syn_wbr (.cv c) (syn_chncodecutrel A) (.cv v))
  have p0009 := @g_hwnisohwisob c u A dv_cache_0002
  have p0010 :=
    @g_biimpi (syn_wbr (.cv u) (syn_chwniso A) (.cv c))
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv c) (syn_chwcn A)))
        (syn_wbr (.cv u) (syn_chwiso A) (.cv c)))
      p0009
  have p0011 :=
    @g_simpl (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv c) (syn_chwcn A)))
      (syn_wbr (.cv u) (syn_chwiso A) (.cv c))
  have p0012 :=
    @g_syl (syn_wbr (.cv u) (syn_chwniso A) (.cv c))
      (syn_wa (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv c) (syn_chwcn A)))
        (syn_wbr (.cv u) (syn_chwiso A) (.cv c)))
      (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv c) (syn_chwcn A))) p0010
      p0011
  have p0013 :=
    @g_simpl (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv c) (syn_chwcn A))
  have p0014 :=
    @g_syl (syn_wbr (.cv u) (syn_chwniso A) (.cv c))
      (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv c) (syn_chwcn A)))
      (.classMem (.cv u) (syn_chwcn A)) p0012 p0013
  have p0015 :=
    @g_syl
      (syn_wa (syn_wbr (.cv u) (syn_chwniso A) (.cv c))
        (syn_wbr (.cv c) (syn_chncodecutrel A) (.cv v)))
      (syn_wbr (.cv u) (syn_chwniso A) (.cv c)) (.classMem (.cv u) (syn_chwcn A)) p0008
      p0014
  have p0016 :=
    @g_simpr (syn_wbr (.cv u) (syn_chwniso A) (.cv c))
      (syn_wbr (.cv c) (syn_chncodecutrel A) (.cv v))
  have p0017 :=
    @g_hncodecutreltargetclndv v A (.cv c) dv_cache_0005 dv_cache_0006 dv_cache_0007
  have p0018 :=
    @g_syl
      (syn_wa (syn_wbr (.cv u) (syn_chwniso A) (.cv c))
        (syn_wbr (.cv c) (syn_chncodecutrel A) (.cv v)))
      (syn_wbr (.cv c) (syn_chncodecutrel A) (.cv v)) (.classMem (.cv v) (syn_chwcn A))
      p0016 p0017
  have p0019 :=
    @g_jca
      (syn_wa (syn_wbr (.cv u) (syn_chwniso A) (.cv c))
        (syn_wbr (.cv c) (syn_chncodecutrel A) (.cv v)))
      (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)) p0015 p0018
  have p0020 :=
    @g_exlimiv
      (syn_wa (syn_wbr (.cv u) (syn_chwniso A) (.cv c))
        (syn_wbr (.cv c) (syn_chncodecutrel A) (.cv v)))
      (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) c
      dv_cache_0008 p0019
  have p0021 :=
    @g_jaoi (syn_wbr (.cv u) (syn_chwniso A) (.cv v))
      (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
      (syn_wex c (syn_wa (syn_wbr (.cv u) (syn_chwniso A) (.cv c))
          (syn_wbr (.cv c) (syn_chncodecutrel A) (.cv v))))
      p0007 p0020
  have p0022 :=
    @g_syl (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v))
      (syn_wo (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wex c
          (syn_wa (syn_wbr (.cv u) (syn_chwniso A) (.cv c))
            (syn_wbr (.cv c) (syn_chncodecutrel A) (.cv v)))))
      (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) p0003
      p0021
  have p0023 := @g_opelxp (.cv u) (.cv v) (syn_chwcn A) (syn_chwcn A)
  have p0024 :=
    @g_biimpri (.classMem (syn_cop (.cv u) (.cv v)) (syn_cxp (syn_chwcn A) (syn_chwcn A)))
      (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A))) p0023
  have p0025 :=
    @g_syl (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v))
      (syn_wa (.classMem (.cv u) (syn_chwcn A)) (.classMem (.cv v) (syn_chwcn A)))
      (.classMem (syn_cop (.cv u) (.cv v)) (syn_cxp (syn_chwcn A) (syn_chwcn A))) p0022
      p0024
  have p0026 :=
    @g_syl (.classMem (syn_cop (.cv u) (.cv v)) (syn_chncodecmpset A))
      (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v))
      (.classMem (syn_cop (.cv u) (.cv v)) (syn_cxp (syn_chwcn A) (syn_chwcn A))) p0001
      p0025
  have p0027 :=
    @g_relssi u v (syn_chncodecmpset A) (syn_cxp (syn_chwcn A) (syn_chwcn A))
      dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0004 p0026
  exact p0027

@[expose]
noncomputable def g_hncodecmpdefaultcnndv (A : Class) :
    Nominal.NPrf
      (.classMem
        (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))
        (syn_chwcn A)) :=
  by
  have dv_cache_0001 :
    Disjoint (A).fv
      ((syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))).fv :=
    by
    exact
      (show Disjoint (A).fv ((syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))).fv
        from (by
          rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin];
          exact
            (show
              Disjoint ((A).fv)
                ((((syn_ckqrel (syn_clefin))).fv) ∪ (((syn_cxp (syn_c0) (syn_c0))).fv))
              from
              (Finset.disjoint_union_right.mpr
                ⟨(show Disjoint ((A).fv) (((syn_ckqrel (syn_clefin))).fv) from
                    (by
                      rw [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel];
                      exact
                        (show Disjoint ((A).fv) (((syn_clefin)).fv) from
                          (by
                            rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin];
                            exact
                              (show Disjoint ((A).fv) ((∅ : Finset Var)) from
                                (by simp)))))),
                  (show Disjoint ((A).fv) (((syn_cxp (syn_c0) (syn_c0))).fv) from
                    (by
                      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp];
                      exact
                        (show Disjoint ((A).fv) ((((syn_c0)).fv) ∪ (((syn_c0)).fv)) from
                          (Finset.disjoint_union_right.mpr
                            ⟨(show Disjoint ((A).fv) (((syn_c0)).fv) from
                                (by
                                  rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0];
                                  exact
                                    (show Disjoint ((A).fv) ((∅ : Finset Var)) from
                                      (by simp)))),
                              (show Disjoint ((A).fv) (((syn_c0)).fv) from
                                (by
                                  rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0];
                                  exact
                                    (show Disjoint ((A).fv) ((∅ : Finset Var)) from
                                      (by simp))))⟩))))⟩))))
  have p0000 := @g_wecomparisondefaultemptywe
  have p0001 := @g_n_0ss A
  have p0002 :=
    @g_pm3_2i
      (syn_wbr (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_cwe)
        (syn_c0))
      (syn_wss (syn_c0) A) p0000 p0001
  have p0004 :=
    @g_brex (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)
      (syn_cwe)
  have p0005 := Nominal.mp p0000 p0004
  have p0006 :=
    @g_simpli
      (.classMem (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_cvv))
      (.classMem (syn_c0) (syn_cvv)) p0005
  have p0010 :=
    @g_simpri
      (.classMem (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_cvv))
      (.classMem (syn_c0) (syn_cvv)) p0005
  have p0011 :=
    @g_elhwcodes A (syn_c0)
      (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) dv_cache_0001 p0006
      p0010
  have p0012 :=
    @g_biimpri
      (.classMem
        (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))
        (syn_chwcodes A))
      (syn_wa (syn_wbr (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_cwe)
          (syn_c0)) (syn_wss (syn_c0) A))
      p0011
  have p0013 := Nominal.mp p0002 p0012
  have p0014 := @g_inss2 (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))
  have p0023 :=
    @g_opfv1st (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)
      p0006 p0010
  have p0032 :=
    @g_opfv2nd (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)
      p0006 p0010
  have p0042 :=
    @g_xpeq12i
      (syn_cfv (syn_c2nd)
        (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
      (syn_c0)
      (syn_cfv (syn_c2nd)
        (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
      (syn_c0) p0032 p0032
  have p0043 :=
    @g_sseq12i
      (syn_cfv (syn_c1st)
        (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
      (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
      (syn_cxp (syn_cfv (syn_c2nd)
          (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
        (syn_cfv (syn_c2nd)
          (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
      (syn_cxp (syn_c0) (syn_c0)) p0023 p0042
  have p0044 :=
    @g_biimpri
      (syn_wss (syn_cfv (syn_c1st)
          (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
        (syn_cxp (syn_cfv (syn_c2nd)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
          (syn_cfv (syn_c2nd)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
              (syn_c0)))))
      (syn_wss (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
        (syn_cxp (syn_c0) (syn_c0)))
      p0043
  have p0045 := Nominal.mp p0014 p0044
  have p0046 :=
    @g_pm3_2i
      (.classMem
        (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))
        (syn_chwcodes A))
      (syn_wss (syn_cfv (syn_c1st)
          (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
        (syn_cxp (syn_cfv (syn_c2nd)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
          (syn_cfv (syn_c2nd)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
              (syn_c0)))))
      p0013 p0045
  have p0055 :=
    @g_opex (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0) p0006
      p0010
  have p0056 :=
    @g_elhwcncl A
      (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))
  have p0057 := Nominal.mp p0055 p0056
  have p0058 :=
    @g_biimpri
      (.classMem
        (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))
        (syn_chwcn A))
      (syn_wa (.classMem
          (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))
          (syn_chwcodes A)) (syn_wss (syn_cfv (syn_c1st)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
          (syn_cxp (syn_cfv (syn_c2nd)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0))) (syn_cfv (syn_c2nd)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0))))))
      p0057
  have p0059 := Nominal.mp p0046 p0058
  exact p0059

@[expose]
noncomputable def g_hwcnweclndv (A : Class) (B : Class) :
    Nominal.NPrf
      (.imp (.classMem B (syn_chwcn A))
        (syn_wbr (syn_cfv (syn_c1st) B) (syn_cwe) (syn_cfv (syn_c2nd) B))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  let u : Var := freshVar proofSupport 0
  have fresh_u : u ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_u_not_A : u ∉ A.fv := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (h))
  have fresh_u_not_B : u ∉ B.fv := by
    intro h
    exact fresh_u (Finset.mem_union_right _ (h))
  have dv_cache_0001 : u ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_u_not_A, not_false_eq_true])
  have dv_cache_0002 : u ∉ (B).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_u_not_B, not_false_eq_true])
  have dv_cache_0003 :
    u ∉
      ((Wff.imp (.classMem B (syn_chwcn A))
          (syn_wbr (syn_cfv (syn_c1st) B) (syn_cwe) (syn_cfv (syn_c2nd) B)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union,
          fresh_u_not_B, fresh_u_not_A, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have p0000 := @g_id (.classMem B (syn_chwcn A))
  have p0001 := @g_elex B (syn_chwcn A)
  have p0002 := @g_id (.classEq (.cv u) B)
  have p0003 := @g_eleq1d (.classEq (.cv u) B) (.cv u) B (syn_chwcn A) p0002
  have p0005 := @g_fveq2d (.classEq (.cv u) B) (.cv u) B (syn_c1st) p0002
  have p0007 := @g_fveq2d (.classEq (.cv u) B) (.cv u) B (syn_c2nd) p0002
  have p0008 :=
    @g_breq12d (.classEq (.cv u) B) (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c1st) B)
      (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) B) (syn_cwe) p0005 p0007
  have p0009 :=
    @g_imbi12d (.classEq (.cv u) B) (.classMem (.cv u) (syn_chwcn A))
      (.classMem B (syn_chwcn A))
      (syn_wbr (syn_cfv (syn_c1st) (.cv u)) (syn_cwe) (syn_cfv (syn_c2nd) (.cv u)))
      (syn_wbr (syn_cfv (syn_c1st) B) (syn_cwe) (syn_cfv (syn_c2nd) B)) p0003 p0008
  have p0010 := @g_hwcnwendv u A dv_cache_0001
  have p0011 :=
    @g_vtoclg
      (.imp (.classMem (.cv u) (syn_chwcn A))
        (syn_wbr (syn_cfv (syn_c1st) (.cv u)) (syn_cwe) (syn_cfv (syn_c2nd) (.cv u))))
      (.imp (.classMem B (syn_chwcn A))
        (syn_wbr (syn_cfv (syn_c1st) B) (syn_cwe) (syn_cfv (syn_c2nd) B)))
      u B (syn_cvv) dv_cache_0002 dv_cache_0003 p0009 p0010
  have p0012 :=
    @g_syl (.classMem B (syn_chwcn A)) (.classMem B (syn_cvv))
      (.imp (.classMem B (syn_chwcn A))
        (syn_wbr (syn_cfv (syn_c1st) B) (syn_cwe) (syn_cfv (syn_c2nd) B)))
      p0001 p0011
  have p0013 :=
    @g_mpd (.classMem B (syn_chwcn A)) (.classMem B (syn_chwcn A))
      (syn_wbr (syn_cfv (syn_c1st) B) (syn_cwe) (syn_cfv (syn_c2nd) B)) p0000 p0012
  exact p0013

@[expose]
noncomputable def g_hwcnbaseclndv (A : Class) (B : Class) :
    Nominal.NPrf (.imp (.classMem B (syn_chwcn A)) (syn_wss (syn_cfv (syn_c2nd) B) A)) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  let u : Var := freshVar proofSupport 0
  have fresh_u : u ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_u_not_A : u ∉ A.fv := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (h))
  have fresh_u_not_B : u ∉ B.fv := by
    intro h
    exact fresh_u (Finset.mem_union_right _ (h))
  have dv_cache_0001 : u ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_u_not_A, not_false_eq_true])
  have dv_cache_0002 : u ∉ (B).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_u_not_B, not_false_eq_true])
  have dv_cache_0003 :
    u ∉ ((Wff.imp (.classMem B (syn_chwcn A)) (syn_wss (syn_cfv (syn_c2nd) B) A))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union,
          fresh_u_not_B, fresh_u_not_A, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have p0000 := @g_id (.classMem B (syn_chwcn A))
  have p0001 := @g_elex B (syn_chwcn A)
  have p0002 := @g_id (.classEq (.cv u) B)
  have p0003 := @g_eleq1d (.classEq (.cv u) B) (.cv u) B (syn_chwcn A) p0002
  have p0005 := @g_fveq2d (.classEq (.cv u) B) (.cv u) B (syn_c2nd) p0002
  have p0006 :=
    @g_sseq1d (.classEq (.cv u) B) (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) B) A
      p0005
  have p0007 :=
    @g_imbi12d (.classEq (.cv u) B) (.classMem (.cv u) (syn_chwcn A))
      (.classMem B (syn_chwcn A)) (syn_wss (syn_cfv (syn_c2nd) (.cv u)) A)
      (syn_wss (syn_cfv (syn_c2nd) B) A) p0003 p0006
  have p0008 := @g_hwcnbase u A dv_cache_0001
  have p0009 :=
    @g_vtoclg
      (.imp (.classMem (.cv u) (syn_chwcn A)) (syn_wss (syn_cfv (syn_c2nd) (.cv u)) A))
      (.imp (.classMem B (syn_chwcn A)) (syn_wss (syn_cfv (syn_c2nd) B) A)) u B (syn_cvv)
      dv_cache_0002 dv_cache_0003 p0007 p0008
  have p0010 :=
    @g_syl (.classMem B (syn_chwcn A)) (.classMem B (syn_cvv))
      (.imp (.classMem B (syn_chwcn A)) (syn_wss (syn_cfv (syn_c2nd) B) A)) p0001 p0009
  have p0011 :=
    @g_mpd (.classMem B (syn_chwcn A)) (.classMem B (syn_chwcn A))
      (syn_wss (syn_cfv (syn_c2nd) B) A) p0000 p0010
  exact p0011


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk017Compact001Part024`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_hncodecmpsetstrictcutsemclndv (x : Var) (A : Class) (B : Class)
    (C : Class) (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_C_x : x ∉ C.fv) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A)))
        (syn_wb (syn_wbr B (syn_chncodecmpset A) C) (syn_wo (syn_wbr B (syn_chwniso A) C)
            (syn_wrex x (syn_cfv (syn_c2nd) C) (syn_wbr B (syn_chwniso A)
                (syn_chnwcutcode (syn_cfv (syn_c1st) C) (syn_cfv (syn_c2nd) C) (.cv x))))))) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ A.fv ∪ B.fv ∪ C.fv
  let v : Var := freshVar proofSupport 0
  let u : Var := freshVar proofSupport 1
  have fresh_v : v ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_v_ne_x : v ≠ x := by
    intro h
    exact
      fresh_v
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_x_ne_v : x ≠ v := Ne.symm fresh_v_ne_x
  have fresh_v_not_A : v ∉ A.fv := by
    intro h
    exact
      fresh_v
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_v_not_B : v ∉ B.fv := by
    intro h
    exact fresh_v (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_v_not_C : v ∉ C.fv := by
    intro h
    exact fresh_v (Finset.mem_union_right _ (h))
  have fresh_u : u ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_u_ne_x : u ≠ x := by
    intro h
    exact
      fresh_u
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_x_ne_u : x ≠ u := Ne.symm fresh_u_ne_x
  have fresh_u_not_A : u ∉ A.fv := by
    intro h
    exact
      fresh_u
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_u_not_B : u ∉ B.fv := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_v_ne_u : v ≠ u :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_u_ne_v : u ≠ v := Ne.symm fresh_v_ne_u
  have dv_cache_0001 : x ∉ ((syn_cfv (syn_c2nd) (.cv v))).fv := by
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
  have dv_cache_0002 : x ∉ ((syn_cfv (syn_c2nd) C)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union, dv_C_x,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ ((Wff.classEq (.cv v) C)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_v, dv_C_x, or_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ ((Wff.classEq (.cv u) B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_u, dv_B_x, or_false, not_false_eq_true])
  have dv_cache_0005 : u ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_u_not_A, not_false_eq_true])
  have dv_cache_0006 : v ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_v_not_A, not_false_eq_true])
  have dv_cache_0007 : x ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_x, not_false_eq_true])
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
  have dv_cache_0010 : u ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_u_not_B, not_false_eq_true])
  have dv_cache_0011 :
    u ∉
      ((Wff.imp (.classMem (.cv v) (syn_chwcn A))
          (syn_wb (syn_wbr B (syn_chncodecmpset A) (.cv v))
            (syn_wo (syn_wbr B (syn_chwniso A) (.cv v)) (syn_wrex x (syn_cfv (syn_c2nd) (.cv v))
                (syn_wbr B (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v))
                    (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodecmpset,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wo,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutcode,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_u_ne_v, fresh_u_not_A,
          fresh_u_not_B, fresh_u_ne_x, compact_fv_not_mem_empty, or_false, and_false,
          not_false_eq_true])
  have dv_cache_0012 : v ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_v_not_C, not_false_eq_true])
  have dv_cache_0013 :
    v ∉
      ((Wff.imp (.classMem B (syn_cvv)) (.imp (.classMem C (syn_chwcn A))
            (syn_wb (syn_wbr B (syn_chncodecmpset A) C) (syn_wo (syn_wbr B (syn_chwniso A) C)
                (syn_wrex x (syn_cfv (syn_c2nd) C) (syn_wbr B (syn_chwniso A)
                    (syn_chnwcutcode (syn_cfv (syn_c1st) C) (syn_cfv (syn_c2nd) C)
                      (.cv x))))))))).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodecmpset,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wo,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutcode,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_v_not_B, fresh_v_not_C, fresh_v_not_A, fresh_v_ne_x,
          compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have p0000 := @g_simpr (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A))
  have p0001 := @g_simpl (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A))
  have p0002 := @g_elex B (syn_chwcn A)
  have p0003 :=
    @g_syl (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A)))
      (.classMem B (syn_chwcn A)) (.classMem B (syn_cvv)) p0001 p0002
  have p0005 := @g_elex C (syn_chwcn A)
  have p0006 :=
    @g_syl (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A)))
      (.classMem C (syn_chwcn A)) (.classMem C (syn_cvv)) p0000 p0005
  have p0007 := @g_id (.classEq (.cv v) C)
  have p0008 := @g_eleq1d (.classEq (.cv v) C) (.cv v) C (syn_chwcn A) p0007
  have p0009 := @g_eqid B
  have p0010 := @g_a1i (.classEq B B) (.classEq (.cv v) C) p0009
  have p0012 :=
    @g_breq12d (.classEq (.cv v) C) B B (.cv v) C (syn_chncodecmpset A) p0010 p0007
  have p0016 := @g_breq12d (.classEq (.cv v) C) B B (.cv v) C (syn_chwniso A) p0010 p0007
  have p0018 := @g_fveq2d (.classEq (.cv v) C) (.cv v) C (syn_c2nd) p0007
  have p0021 :=
    (Nominal.classEqRefl
      (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))
  have p0022 :=
    @g_a1i
      (.classEq (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
          (.cv x)) (syn_cop (syn_cin (syn_cfv (syn_c1st) (.cv v)) (syn_cxp
              (syn_cin (syn_cfv (syn_c2nd) (.cv v))
                (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
                  (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (.cv v))
                (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
                  (syn_csn (.cv x)))))) (syn_cin (syn_cfv (syn_c2nd) (.cv v))
            (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
              (syn_csn (.cv x))))))
      (.classEq (.cv v) C) p0021
  have p0024 := @g_fveq2d (.classEq (.cv v) C) (.cv v) C (syn_c1st) p0007
  have p0029 :=
    @g_difeq1d (.classEq (.cv v) C) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c1st) C)
      (syn_cid) p0024
  have p0030 :=
    @g_cnveqd (.classEq (.cv v) C) (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid))
      (syn_cdif (syn_cfv (syn_c1st) C) (syn_cid)) p0029
  have p0031 :=
    @g_imaeq1d (.classEq (.cv v) C)
      (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
      (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) C) (syn_cid))) (syn_csn (.cv x)) p0030
  have p0032 :=
    @g_ineq12d (.classEq (.cv v) C) (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (syn_c2nd) C)
      (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid))) (syn_csn (.cv x)))
      (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) C) (syn_cid))) (syn_csn (.cv x)))
      p0018 p0031
  have p0041 :=
    @g_xpeq12d (.classEq (.cv v) C)
      (syn_cin (syn_cfv (syn_c2nd) (.cv v))
        (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
          (syn_csn (.cv x))))
      (syn_cin (syn_cfv (syn_c2nd) C)
        (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) C) (syn_cid))) (syn_csn (.cv x))))
      (syn_cin (syn_cfv (syn_c2nd) (.cv v))
        (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
          (syn_csn (.cv x))))
      (syn_cin (syn_cfv (syn_c2nd) C)
        (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) C) (syn_cid))) (syn_csn (.cv x))))
      p0032 p0032
  have p0042 :=
    @g_ineq12d (.classEq (.cv v) C) (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c1st) C)
      (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (.cv v))
          (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
            (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (.cv v))
          (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
            (syn_csn (.cv x)))))
      (syn_cxp (syn_cin (syn_cfv (syn_c2nd) C)
          (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) C) (syn_cid))) (syn_csn (.cv x))))
        (syn_cin (syn_cfv (syn_c2nd) C)
          (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) C) (syn_cid))) (syn_csn (.cv x)))))
      p0024 p0041
  have p0051 :=
    @g_opeq12d (.classEq (.cv v) C)
      (syn_cin (syn_cfv (syn_c1st) (.cv v)) (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (.cv v))
            (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
              (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (.cv v))
            (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
              (syn_csn (.cv x))))))
      (syn_cin (syn_cfv (syn_c1st) C) (syn_cxp (syn_cin (syn_cfv (syn_c2nd) C)
            (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) C) (syn_cid))) (syn_csn (.cv x))))
          (syn_cin (syn_cfv (syn_c2nd) C)
            (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) C) (syn_cid)))
              (syn_csn (.cv x))))))
      (syn_cin (syn_cfv (syn_c2nd) (.cv v))
        (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
          (syn_csn (.cv x))))
      (syn_cin (syn_cfv (syn_c2nd) C)
        (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) C) (syn_cid))) (syn_csn (.cv x))))
      p0042 p0032
  have p0052 :=
    (Nominal.classEqRefl
      (syn_chnwcutcode (syn_cfv (syn_c1st) C) (syn_cfv (syn_c2nd) C) (.cv x)))
  have p0053 :=
    @g_a1i
      (.classEq (syn_chnwcutcode (syn_cfv (syn_c1st) C) (syn_cfv (syn_c2nd) C) (.cv x)) (syn_cop
          (syn_cin (syn_cfv (syn_c1st) C) (syn_cxp (syn_cin (syn_cfv (syn_c2nd) C)
                (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) C) (syn_cid)))
                  (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) C)
                (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) C) (syn_cid)))
                  (syn_csn (.cv x)))))) (syn_cin (syn_cfv (syn_c2nd) C)
            (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) C) (syn_cid)))
              (syn_csn (.cv x))))))
      (.classEq (.cv v) C) p0052
  have p0054 :=
    @g_eqcomd (.classEq (.cv v) C)
      (syn_chnwcutcode (syn_cfv (syn_c1st) C) (syn_cfv (syn_c2nd) C) (.cv x))
      (syn_cop (syn_cin (syn_cfv (syn_c1st) C) (syn_cxp (syn_cin (syn_cfv (syn_c2nd) C)
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) C) (syn_cid)))
                (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) C)
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) C) (syn_cid)))
                (syn_csn (.cv x)))))) (syn_cin (syn_cfv (syn_c2nd) C)
          (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) C) (syn_cid))) (syn_csn (.cv x)))))
      p0053
  have p0055 :=
    @g_n_3eqtrd (.classEq (.cv v) C)
      (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))
      (syn_cop (syn_cin (syn_cfv (syn_c1st) (.cv v)) (syn_cxp
            (syn_cin (syn_cfv (syn_c2nd) (.cv v))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
                (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (.cv v))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
                (syn_csn (.cv x)))))) (syn_cin (syn_cfv (syn_c2nd) (.cv v))
          (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
            (syn_csn (.cv x)))))
      (syn_cop (syn_cin (syn_cfv (syn_c1st) C) (syn_cxp (syn_cin (syn_cfv (syn_c2nd) C)
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) C) (syn_cid)))
                (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) C)
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) C) (syn_cid)))
                (syn_csn (.cv x)))))) (syn_cin (syn_cfv (syn_c2nd) C)
          (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) C) (syn_cid))) (syn_csn (.cv x)))))
      (syn_chnwcutcode (syn_cfv (syn_c1st) C) (syn_cfv (syn_c2nd) C) (.cv x)) p0022 p0051
      p0054
  have p0056 :=
    @g_breq12d (.classEq (.cv v) C) B B
      (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))
      (syn_chnwcutcode (syn_cfv (syn_c1st) C) (syn_cfv (syn_c2nd) C) (.cv x))
      (syn_chwniso A) p0010 p0055
  have p0057 :=
    @g_rexeqbidv (.classEq (.cv v) C)
      (syn_wbr B (syn_chwniso A)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))
      (syn_wbr B (syn_chwniso A)
        (syn_chnwcutcode (syn_cfv (syn_c1st) C) (syn_cfv (syn_c2nd) C) (.cv x)))
      x (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (syn_c2nd) C) dv_cache_0001 dv_cache_0002
      dv_cache_0003 p0018 p0056
  have p0058 :=
    @g_orbi12d (.classEq (.cv v) C) (syn_wbr B (syn_chwniso A) (.cv v))
      (syn_wbr B (syn_chwniso A) C)
      (syn_wrex x (syn_cfv (syn_c2nd) (.cv v)) (syn_wbr B (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))
      (syn_wrex x (syn_cfv (syn_c2nd) C) (syn_wbr B (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) C) (syn_cfv (syn_c2nd) C) (.cv x))))
      p0016 p0057
  have p0059 :=
    @g_bibi12d (.classEq (.cv v) C) (syn_wbr B (syn_chncodecmpset A) (.cv v))
      (syn_wbr B (syn_chncodecmpset A) C)
      (syn_wo (syn_wbr B (syn_chwniso A) (.cv v)) (syn_wrex x (syn_cfv (syn_c2nd) (.cv v))
          (syn_wbr B (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv x)))))
      (syn_wo (syn_wbr B (syn_chwniso A) C) (syn_wrex x (syn_cfv (syn_c2nd) C)
          (syn_wbr B (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) C) (syn_cfv (syn_c2nd) C) (.cv x)))))
      p0012 p0058
  have p0060 :=
    @g_imbi12d (.classEq (.cv v) C) (.classMem (.cv v) (syn_chwcn A))
      (.classMem C (syn_chwcn A))
      (syn_wb (syn_wbr B (syn_chncodecmpset A) (.cv v))
        (syn_wo (syn_wbr B (syn_chwniso A) (.cv v)) (syn_wrex x (syn_cfv (syn_c2nd) (.cv v))
            (syn_wbr B (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv x))))))
      (syn_wb (syn_wbr B (syn_chncodecmpset A) C) (syn_wo (syn_wbr B (syn_chwniso A) C)
          (syn_wrex x (syn_cfv (syn_c2nd) C) (syn_wbr B (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) C) (syn_cfv (syn_c2nd) C) (.cv x))))))
      p0008 p0059
  have p0061 :=
    @g_imbi2d (.classEq (.cv v) C)
      (.imp (.classMem (.cv v) (syn_chwcn A)) (syn_wb (syn_wbr B (syn_chncodecmpset A) (.cv v))
          (syn_wo (syn_wbr B (syn_chwniso A) (.cv v)) (syn_wrex x (syn_cfv (syn_c2nd) (.cv v))
              (syn_wbr B (syn_chwniso A)
                (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                  (.cv x)))))))
      (.imp (.classMem C (syn_chwcn A)) (syn_wb (syn_wbr B (syn_chncodecmpset A) C)
          (syn_wo (syn_wbr B (syn_chwniso A) C) (syn_wrex x (syn_cfv (syn_c2nd) C)
              (syn_wbr B (syn_chwniso A)
                (syn_chnwcutcode (syn_cfv (syn_c1st) C) (syn_cfv (syn_c2nd) C) (.cv x)))))))
      (.classMem B (syn_cvv)) p0060
  have p0062 := @g_eqid (.cv v)
  have p0063 := @g_a1i (.classEq (.cv v) (.cv v)) (.classEq (.cv u) B) p0062
  have p0064 := @g_eleq1d (.classEq (.cv u) B) (.cv v) (.cv v) (syn_chwcn A) p0063
  have p0065 := @g_id (.classEq (.cv u) B)
  have p0068 :=
    @g_breq12d (.classEq (.cv u) B) (.cv u) B (.cv v) (.cv v) (syn_chncodecmpset A) p0065
      p0063
  have p0072 :=
    @g_breq12d (.classEq (.cv u) B) (.cv u) B (.cv v) (.cv v) (syn_chwniso A) p0065 p0063
  have p0075 := @g_fveq2d (.classEq (.cv u) B) (.cv v) (.cv v) (syn_c2nd) p0063
  have p0078 :=
    @g_a1i
      (.classEq (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
          (.cv x)) (syn_cop (syn_cin (syn_cfv (syn_c1st) (.cv v)) (syn_cxp
              (syn_cin (syn_cfv (syn_c2nd) (.cv v))
                (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
                  (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (.cv v))
                (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
                  (syn_csn (.cv x)))))) (syn_cin (syn_cfv (syn_c2nd) (.cv v))
            (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
              (syn_csn (.cv x))))))
      (.classEq (.cv u) B) p0021
  have p0081 := @g_fveq2d (.classEq (.cv u) B) (.cv v) (.cv v) (syn_c1st) p0063
  have p0088 :=
    @g_difeq1d (.classEq (.cv u) B) (syn_cfv (syn_c1st) (.cv v))
      (syn_cfv (syn_c1st) (.cv v)) (syn_cid) p0081
  have p0089 :=
    @g_cnveqd (.classEq (.cv u) B) (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid))
      (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)) p0088
  have p0090 :=
    @g_imaeq1d (.classEq (.cv u) B)
      (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
      (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid))) (syn_csn (.cv x)) p0089
  have p0091 :=
    @g_ineq12d (.classEq (.cv u) B) (syn_cfv (syn_c2nd) (.cv v))
      (syn_cfv (syn_c2nd) (.cv v))
      (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid))) (syn_csn (.cv x)))
      (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid))) (syn_csn (.cv x)))
      p0075 p0090
  have p0102 :=
    @g_xpeq12d (.classEq (.cv u) B)
      (syn_cin (syn_cfv (syn_c2nd) (.cv v))
        (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
          (syn_csn (.cv x))))
      (syn_cin (syn_cfv (syn_c2nd) (.cv v))
        (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
          (syn_csn (.cv x))))
      (syn_cin (syn_cfv (syn_c2nd) (.cv v))
        (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
          (syn_csn (.cv x))))
      (syn_cin (syn_cfv (syn_c2nd) (.cv v))
        (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
          (syn_csn (.cv x))))
      p0091 p0091
  have p0103 :=
    @g_ineq12d (.classEq (.cv u) B) (syn_cfv (syn_c1st) (.cv v))
      (syn_cfv (syn_c1st) (.cv v))
      (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (.cv v))
          (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
            (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (.cv v))
          (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
            (syn_csn (.cv x)))))
      (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (.cv v))
          (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
            (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (.cv v))
          (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
            (syn_csn (.cv x)))))
      p0081 p0102
  have p0114 :=
    @g_opeq12d (.classEq (.cv u) B)
      (syn_cin (syn_cfv (syn_c1st) (.cv v)) (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (.cv v))
            (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
              (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (.cv v))
            (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
              (syn_csn (.cv x))))))
      (syn_cin (syn_cfv (syn_c1st) (.cv v)) (syn_cxp (syn_cin (syn_cfv (syn_c2nd) (.cv v))
            (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
              (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (.cv v))
            (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
              (syn_csn (.cv x))))))
      (syn_cin (syn_cfv (syn_c2nd) (.cv v))
        (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
          (syn_csn (.cv x))))
      (syn_cin (syn_cfv (syn_c2nd) (.cv v))
        (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
          (syn_csn (.cv x))))
      p0103 p0091
  have p0117 :=
    @g_eqcomd (.classEq (.cv u) B)
      (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))
      (syn_cop (syn_cin (syn_cfv (syn_c1st) (.cv v)) (syn_cxp
            (syn_cin (syn_cfv (syn_c2nd) (.cv v))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
                (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (.cv v))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
                (syn_csn (.cv x)))))) (syn_cin (syn_cfv (syn_c2nd) (.cv v))
          (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
            (syn_csn (.cv x)))))
      p0078
  have p0118 :=
    @g_n_3eqtrd (.classEq (.cv u) B)
      (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))
      (syn_cop (syn_cin (syn_cfv (syn_c1st) (.cv v)) (syn_cxp
            (syn_cin (syn_cfv (syn_c2nd) (.cv v))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
                (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (.cv v))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
                (syn_csn (.cv x)))))) (syn_cin (syn_cfv (syn_c2nd) (.cv v))
          (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
            (syn_csn (.cv x)))))
      (syn_cop (syn_cin (syn_cfv (syn_c1st) (.cv v)) (syn_cxp
            (syn_cin (syn_cfv (syn_c2nd) (.cv v))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
                (syn_csn (.cv x)))) (syn_cin (syn_cfv (syn_c2nd) (.cv v))
              (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
                (syn_csn (.cv x)))))) (syn_cin (syn_cfv (syn_c2nd) (.cv v))
          (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st) (.cv v)) (syn_cid)))
            (syn_csn (.cv x)))))
      (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))
      p0078 p0114 p0117
  have p0119 :=
    @g_breq12d (.classEq (.cv u) B) (.cv u) B
      (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))
      (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))
      (syn_chwniso A) p0065 p0118
  have p0120 :=
    @g_rexeqbidv (.classEq (.cv u) B)
      (syn_wbr (.cv u) (syn_chwniso A)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))
      (syn_wbr B (syn_chwniso A)
        (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x)))
      x (syn_cfv (syn_c2nd) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) dv_cache_0001
      dv_cache_0001 dv_cache_0004 p0075 p0119
  have p0121 :=
    @g_orbi12d (.classEq (.cv u) B) (syn_wbr (.cv u) (syn_chwniso A) (.cv v))
      (syn_wbr B (syn_chwniso A) (.cv v))
      (syn_wrex x (syn_cfv (syn_c2nd) (.cv v)) (syn_wbr (.cv u) (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))
      (syn_wrex x (syn_cfv (syn_c2nd) (.cv v)) (syn_wbr B (syn_chwniso A)
          (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))
      p0072 p0120
  have p0122 :=
    @g_bibi12d (.classEq (.cv u) B) (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v))
      (syn_wbr B (syn_chncodecmpset A) (.cv v))
      (syn_wo (syn_wbr (.cv u) (syn_chwniso A) (.cv v)) (syn_wrex x (syn_cfv (syn_c2nd) (.cv v))
          (syn_wbr (.cv u) (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv x)))))
      (syn_wo (syn_wbr B (syn_chwniso A) (.cv v)) (syn_wrex x (syn_cfv (syn_c2nd) (.cv v))
          (syn_wbr B (syn_chwniso A)
            (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
              (.cv x)))))
      p0068 p0121
  have p0123 :=
    @g_imbi12d (.classEq (.cv u) B) (.classMem (.cv v) (syn_chwcn A))
      (.classMem (.cv v) (syn_chwcn A))
      (syn_wb (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v))
        (syn_wo (syn_wbr (.cv u) (syn_chwniso A) (.cv v))
          (syn_wrex x (syn_cfv (syn_c2nd) (.cv v)) (syn_wbr (.cv u) (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv x))))))
      (syn_wb (syn_wbr B (syn_chncodecmpset A) (.cv v))
        (syn_wo (syn_wbr B (syn_chwniso A) (.cv v)) (syn_wrex x (syn_cfv (syn_c2nd) (.cv v))
            (syn_wbr B (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                (.cv x))))))
      p0064 p0122
  have p0124 :=
    @g_hncodecmpsetstrictcutsemdv x v u A dv_cache_0005 dv_cache_0006 dv_cache_0007
      dv_cache_0008 dv_cache_0009
  have p0125 :=
    @g_vtoclg
      (.imp (.classMem (.cv v) (syn_chwcn A))
        (syn_wb (syn_wbr (.cv u) (syn_chncodecmpset A) (.cv v))
          (syn_wo (syn_wbr (.cv u) (syn_chwniso A) (.cv v))
            (syn_wrex x (syn_cfv (syn_c2nd) (.cv v)) (syn_wbr (.cv u) (syn_chwniso A)
                (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                  (.cv x)))))))
      (.imp (.classMem (.cv v) (syn_chwcn A)) (syn_wb (syn_wbr B (syn_chncodecmpset A) (.cv v))
          (syn_wo (syn_wbr B (syn_chwniso A) (.cv v)) (syn_wrex x (syn_cfv (syn_c2nd) (.cv v))
              (syn_wbr B (syn_chwniso A)
                (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v)) (syn_cfv (syn_c2nd) (.cv v))
                  (.cv x)))))))
      u B (syn_cvv) dv_cache_0010 dv_cache_0011 p0123 p0124
  have p0126 :=
    @g_vtoclg
      (.imp (.classMem B (syn_cvv)) (.imp (.classMem (.cv v) (syn_chwcn A))
          (syn_wb (syn_wbr B (syn_chncodecmpset A) (.cv v))
            (syn_wo (syn_wbr B (syn_chwniso A) (.cv v)) (syn_wrex x (syn_cfv (syn_c2nd) (.cv v))
                (syn_wbr B (syn_chwniso A) (syn_chnwcutcode (syn_cfv (syn_c1st) (.cv v))
                    (syn_cfv (syn_c2nd) (.cv v)) (.cv x))))))))
      (.imp (.classMem B (syn_cvv)) (.imp (.classMem C (syn_chwcn A))
          (syn_wb (syn_wbr B (syn_chncodecmpset A) C) (syn_wo (syn_wbr B (syn_chwniso A) C)
              (syn_wrex x (syn_cfv (syn_c2nd) C) (syn_wbr B (syn_chwniso A)
                  (syn_chnwcutcode (syn_cfv (syn_c1st) C) (syn_cfv (syn_c2nd) C) (.cv x))))))))
      v C (syn_cvv) dv_cache_0012 dv_cache_0013 p0061 p0125
  have p0127 :=
    @g_syl (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A)))
      (.classMem C (syn_cvv))
      (.imp (.classMem B (syn_cvv)) (.imp (.classMem C (syn_chwcn A))
          (syn_wb (syn_wbr B (syn_chncodecmpset A) C) (syn_wo (syn_wbr B (syn_chwniso A) C)
              (syn_wrex x (syn_cfv (syn_c2nd) C) (syn_wbr B (syn_chwniso A)
                  (syn_chnwcutcode (syn_cfv (syn_c1st) C) (syn_cfv (syn_c2nd) C) (.cv x))))))))
      p0006 p0126
  have p0128 :=
    @g_mpd (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A)))
      (.classMem B (syn_cvv))
      (.imp (.classMem C (syn_chwcn A)) (syn_wb (syn_wbr B (syn_chncodecmpset A) C)
          (syn_wo (syn_wbr B (syn_chwniso A) C) (syn_wrex x (syn_cfv (syn_c2nd) C)
              (syn_wbr B (syn_chwniso A)
                (syn_chnwcutcode (syn_cfv (syn_c1st) C) (syn_cfv (syn_c2nd) C) (.cv x)))))))
      p0003 p0127
  have p0129 :=
    @g_mpd (syn_wa (.classMem B (syn_chwcn A)) (.classMem C (syn_chwcn A)))
      (.classMem C (syn_chwcn A))
      (syn_wb (syn_wbr B (syn_chncodecmpset A) C) (syn_wo (syn_wbr B (syn_chwniso A) C)
          (syn_wrex x (syn_cfv (syn_c2nd) C) (syn_wbr B (syn_chwniso A)
              (syn_chnwcutcode (syn_cfv (syn_c1st) C) (syn_cfv (syn_c2nd) C) (.cv x))))))
      p0000 p0128
  exact p0129

@[expose]
noncomputable def g_hncodetotalleftmemndv (u : Var) (A : Class) (_dv_A_u : u ∉ A.fv) :
    Nominal.NPrf
      (.classMem (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
          (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
        (syn_chwcn A)) :=
  by
  have p0000 := @g_hncodecmpdefaultcnndv A
  have p0001 :=
    @g_simpr
      (.classMem
        (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))
        (syn_chwcn A))
      (.classMem (.cv u) (syn_chwcn A))
  have p0002 :=
    @g_simpl
      (.classMem
        (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))
        (syn_chwcn A))
      (.neg (.classMem (.cv u) (syn_chwcn A)))
  have p0003 :=
    @g_ifclda
      (.classMem
        (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))
        (syn_chwcn A))
      (.classMem (.cv u) (syn_chwcn A)) (.cv u)
      (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))
      (syn_chwcn A) p0001 p0002
  have p0004 := Nominal.mp p0000 p0003
  exact p0004

@[expose]
noncomputable def g_hncodetotalrightmemndv (v : Var) (A : Class) (_dv_A_v : v ∉ A.fv) :
    Nominal.NPrf
      (.classMem (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
          (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
        (syn_chwcn A)) :=
  by
  have p0000 := @g_hncodecmpdefaultcnndv A
  have p0001 :=
    @g_simpr
      (.classMem
        (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))
        (syn_chwcn A))
      (.classMem (.cv v) (syn_chwcn A))
  have p0002 :=
    @g_simpl
      (.classMem
        (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))
        (syn_chwcn A))
      (.neg (.classMem (.cv v) (syn_chwcn A)))
  have p0003 :=
    @g_ifclda
      (.classMem
        (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))
        (syn_chwcn A))
      (.classMem (.cv v) (syn_chwcn A)) (.cv v)
      (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))
      (syn_chwcn A) p0001 p0002
  have p0004 := Nominal.mp p0000 p0003
  exact p0004

@[expose]
noncomputable def g_hncodecomparisontotalndv (x : Var) (v : Var) (u : Var) (A : Class)
    (h : Var) (dv_A_h : h ∉ A.fv) (_dv_A_u : u ∉ A.fv) (_dv_A_v : v ∉ A.fv)
    (dv_A_x : x ∉ A.fv) (dv_h_u : h ≠ u) (dv_h_v : h ≠ v) (dv_h_x : h ≠ x)
    (dv_u_x : u ≠ x) (dv_v_x : v ≠ x) :
    Nominal.NPrf
      (syn_w3o (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st)
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
                  (syn_c0)))))) (syn_wrex x (syn_cfv (syn_c2nd)
            (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0)))) (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st)
                (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
                  (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                    (syn_c0)))) (syn_cin (syn_cfv (syn_c1st)
                  (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v) (syn_cop
                      (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
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
                                (syn_c0)))) (syn_cid))) (syn_csn (.cv x))))))
              (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
                  (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                    (syn_c0)))) (syn_cin (syn_cfv (syn_c2nd)
                  (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v) (syn_cop
                      (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                      (syn_c0)))) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st)
                        (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v) (syn_cop
                            (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                            (syn_c0)))) (syn_cid))) (syn_csn (.cv x))))))) (syn_wrex x
          (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
              (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                (syn_c0)))) (syn_wex h (syn_wiso (.cv h) (syn_cfv (syn_c1st)
                (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
                  (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                    (syn_c0)))) (syn_cin (syn_cfv (syn_c1st)
                  (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop
                      (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
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
                                (syn_c0)))) (syn_cid))) (syn_csn (.cv x))))))
              (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
                  (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                    (syn_c0)))) (syn_cin (syn_cfv (syn_c2nd)
                  (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop
                      (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                      (syn_c0)))) (syn_cima (syn_ccnv (syn_cdif (syn_cfv (syn_c1st)
                        (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u) (syn_cop
                            (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
                            (syn_c0)))) (syn_cid))) (syn_csn (.cv x)))))))) :=
  by
  have dv_cache_0001 :
    h ∉
      ((syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
              (syn_c0))))).fv :=
    by
    exact
      (by
        have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union,
          Finset.mem_singleton, dv_h_u, dv_A_h, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0002 :
    x ∉
      ((syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
              (syn_c0))))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union,
          Finset.mem_singleton, (Ne.symm dv_u_x), dv_A_x, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0003 :
    h ∉
      ((syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
              (syn_c0))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union,
          Finset.mem_singleton, dv_h_v, dv_A_h, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0004 :
    x ∉
      ((syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
              (syn_c0))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union,
          Finset.mem_singleton, (Ne.symm dv_v_x), dv_A_x, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0005 :
    h ∉
      ((syn_cfv (syn_c1st) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
              (syn_c0))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
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
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union,
          Finset.mem_singleton, dv_h_u, dv_A_h, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0006 :
    x ∉
      ((syn_cfv (syn_c1st) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
              (syn_c0))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
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
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union,
          Finset.mem_singleton, (Ne.symm dv_u_x), dv_A_x, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0007 :
    h ∉
      ((syn_cfv (syn_c1st) (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
              (syn_c0))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
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
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union,
          Finset.mem_singleton, dv_h_v, dv_A_h, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0008 :
    x ∉
      ((syn_cfv (syn_c1st) (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
            (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0)))
              (syn_c0))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
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
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union,
          Finset.mem_singleton, (Ne.symm dv_v_x), dv_A_x, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0009 : h ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (show h ≠ x from (by exact dv_h_x))
  have p0000 := @g_hncodecmpdefaultcnndv A
  have p0001 :=
    @g_simpr
      (.classMem
        (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))
        (syn_chwcn A))
      (.classMem (.cv u) (syn_chwcn A))
  have p0002 :=
    @g_simpl
      (.classMem
        (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))
        (syn_chwcn A))
      (.neg (.classMem (.cv u) (syn_chwcn A)))
  have p0003 :=
    @g_ifclda
      (.classMem
        (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))
        (syn_chwcn A))
      (.classMem (.cv u) (syn_chwcn A)) (.cv u)
      (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))
      (syn_chwcn A) p0001 p0002
  have p0004 := Nominal.mp p0000 p0003
  have p0005 :=
    @g_hwcnweclndv A
      (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
        (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
  have p0006 := Nominal.mp p0004 p0005
  have p0008 :=
    @g_simpr
      (.classMem
        (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))
        (syn_chwcn A))
      (.classMem (.cv v) (syn_chwcn A))
  have p0009 :=
    @g_simpl
      (.classMem
        (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))
        (syn_chwcn A))
      (.neg (.classMem (.cv v) (syn_chwcn A)))
  have p0010 :=
    @g_ifclda
      (.classMem
        (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))
        (syn_chwcn A))
      (.classMem (.cv v) (syn_chwcn A)) (.cv v)
      (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))
      (syn_chwcn A) p0008 p0009
  have p0011 := Nominal.mp p0000 p0010
  have p0012 :=
    @g_hwcnweclndv A
      (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
        (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0)))
  have p0013 := Nominal.mp p0011 p0012
  have p0014 :=
    @g_wecomparisonterminalfdv x
      (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
          (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
      (syn_cfv (syn_c1st) (syn_cif (.classMem (.cv u) (syn_chwcn A)) (.cv u)
          (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
      (syn_cfv (syn_c1st) (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
          (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
      h
      (syn_cfv (syn_c2nd) (syn_cif (.classMem (.cv v) (syn_chwcn A)) (.cv v)
          (syn_cop (syn_cin (syn_ckqrel (syn_clefin)) (syn_cxp (syn_c0) (syn_c0))) (syn_c0))))
      dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
      dv_cache_0007 dv_cache_0008 dv_cache_0009 p0006 p0013
  exact p0014


end NFChoice.DirectNominalPrf.WPPReplay

end
