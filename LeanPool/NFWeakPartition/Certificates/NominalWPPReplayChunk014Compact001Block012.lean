/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NominalWPPReplayChunk014Compact001Block011

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NominalWPPReplayChunk014Compact001Part056`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_ltfinsucle (A : Class) (B : Class) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
        (.imp (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_cltfin))
          (.classMem (syn_copk B A) (syn_clefin)))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  let p : Var := freshVar proofSupport 0
  have fresh_p : p ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_p_not_A : p ∉ A.fv := by
    intro h
    exact fresh_p (Finset.mem_union_left _ (h))
  have fresh_p_not_B : p ∉ B.fv := by
    intro h
    exact fresh_p (Finset.mem_union_right _ (h))
  have dv_cache_0001 : p ∉ (B).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_p_not_B, not_false_eq_true])
  have dv_cache_0002 : p ∉ ((syn_cplc A (syn_c1c))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          fresh_p_not_A, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0003 : p ∉ ((Wff.classMem (syn_copk B A) (syn_clefin))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin, Finset.mem_union,
          fresh_p_not_B, fresh_p_not_A, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0004 :
    p ∉
      ((syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
          (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_cltfin)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cltfin, Finset.mem_union,
          fresh_p_not_A, fresh_p_not_B, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have p0000 :=
    @g_simpr (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
      (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_cltfin))
  have p0001 :=
    @g_simpl (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
      (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_cltfin))
  have p0002 := @g_simpr (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))
  have p0003 :=
    @g_syl
      (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
        (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_cltfin)))
      (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (.classMem B (syn_cnnc))
      p0001 p0002
  have p0004 := @g_elex B (syn_cnnc)
  have p0005 :=
    @g_syl
      (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
        (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_cltfin)))
      (.classMem B (syn_cnnc)) (.classMem B (syn_cvv)) p0003 p0004
  have p0007 := @g_simpl (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))
  have p0008 :=
    @g_syl
      (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
        (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_cltfin)))
      (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (.classMem A (syn_cnnc))
      p0001 p0007
  have p0009 := @g_peano2 A
  have p0010 :=
    @g_syl
      (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
        (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_cltfin)))
      (.classMem A (syn_cnnc)) (.classMem (syn_cplc A (syn_c1c)) (syn_cnnc)) p0008 p0009
  have p0011 := @g_elex (syn_cplc A (syn_c1c)) (syn_cnnc)
  have p0012 :=
    @g_syl
      (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
        (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_cltfin)))
      (.classMem (syn_cplc A (syn_c1c)) (syn_cnnc))
      (.classMem (syn_cplc A (syn_c1c)) (syn_cvv)) p0010 p0011
  have p0013 :=
    @g_jca
      (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
        (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_cltfin)))
      (.classMem B (syn_cvv)) (.classMem (syn_cplc A (syn_c1c)) (syn_cvv)) p0005 p0012
  have p0014 :=
    @g_opkltfing p B (syn_cplc A (syn_c1c)) (syn_cvv) (syn_cvv) dv_cache_0001
      dv_cache_0002
  have p0015 :=
    @g_syl
      (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
        (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_cltfin)))
      (syn_wa (.classMem B (syn_cvv)) (.classMem (syn_cplc A (syn_c1c)) (syn_cvv)))
      (syn_wb (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_cltfin))
        (syn_wa (syn_wne B (syn_c0)) (syn_wrex p (syn_cnnc)
            (.classEq (syn_cplc A (syn_c1c)) (syn_cplc (syn_cplc B (.cv p)) (syn_c1c))))))
      p0013 p0014
  have p0016 :=
    @g_biimpd
      (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
        (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_cltfin)))
      (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_cltfin))
      (syn_wa (syn_wne B (syn_c0)) (syn_wrex p (syn_cnnc)
          (.classEq (syn_cplc A (syn_c1c)) (syn_cplc (syn_cplc B (.cv p)) (syn_c1c)))))
      p0015
  have p0017 :=
    @g_mpd
      (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
        (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_cltfin)))
      (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_cltfin))
      (syn_wa (syn_wne B (syn_c0)) (syn_wrex p (syn_cnnc)
          (.classEq (syn_cplc A (syn_c1c)) (syn_cplc (syn_cplc B (.cv p)) (syn_c1c)))))
      p0000 p0016
  have p0018 :=
    @g_simpr (syn_wne B (syn_c0))
      (syn_wrex p (syn_cnnc)
        (.classEq (syn_cplc A (syn_c1c)) (syn_cplc (syn_cplc B (.cv p)) (syn_c1c))))
  have p0019 :=
    @g_syl
      (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
        (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_cltfin)))
      (syn_wa (syn_wne B (syn_c0)) (syn_wrex p (syn_cnnc)
          (.classEq (syn_cplc A (syn_c1c)) (syn_cplc (syn_cplc B (.cv p)) (syn_c1c)))))
      (syn_wrex p (syn_cnnc)
        (.classEq (syn_cplc A (syn_c1c)) (syn_cplc (syn_cplc B (.cv p)) (syn_c1c))))
      p0017 p0018
  have p0020 :=
    @g_simpl
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
          (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_cltfin)))
        (.classMem (.cv p) (syn_cnnc)))
      (.classEq (syn_cplc A (syn_c1c)) (syn_cplc (syn_cplc B (.cv p)) (syn_c1c)))
  have p0021 :=
    @g_simpl
      (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
        (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_cltfin)))
      (.classMem (.cv p) (syn_cnnc))
  have p0027 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
          (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_cltfin)))
        (.classMem (.cv p) (syn_cnnc)))
      (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
        (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_cltfin)))
      (.classMem B (syn_cvv)) p0021 p0005
  have p0028 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
            (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_cltfin)))
          (.classMem (.cv p) (syn_cnnc)))
        (.classEq (syn_cplc A (syn_c1c)) (syn_cplc (syn_cplc B (.cv p)) (syn_c1c))))
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
          (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_cltfin)))
        (.classMem (.cv p) (syn_cnnc)))
      (.classMem B (syn_cvv)) p0020 p0027
  have p0030 :=
    @g_simpr
      (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
        (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_cltfin)))
      (.classMem (.cv p) (syn_cnnc))
  have p0031 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
            (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_cltfin)))
          (.classMem (.cv p) (syn_cnnc)))
        (.classEq (syn_cplc A (syn_c1c)) (syn_cplc (syn_cplc B (.cv p)) (syn_c1c))))
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
          (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_cltfin)))
        (.classMem (.cv p) (syn_cnnc)))
      (.classMem (.cv p) (syn_cnnc)) p0020 p0030
  have p0032 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
            (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_cltfin)))
          (.classMem (.cv p) (syn_cnnc)))
        (.classEq (syn_cplc A (syn_c1c)) (syn_cplc (syn_cplc B (.cv p)) (syn_c1c))))
      (.classMem B (syn_cvv)) (.classMem (.cv p) (syn_cnnc)) p0028 p0031
  have p0033 := @g_lefinaddc B (.cv p) (syn_cvv)
  have p0034 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
            (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_cltfin)))
          (.classMem (.cv p) (syn_cnnc)))
        (.classEq (syn_cplc A (syn_c1c)) (syn_cplc (syn_cplc B (.cv p)) (syn_c1c))))
      (syn_wa (.classMem B (syn_cvv)) (.classMem (.cv p) (syn_cnnc)))
      (.classMem (syn_copk B (syn_cplc B (.cv p))) (syn_clefin)) p0032 p0033
  have p0035 :=
    @g_simpr
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
          (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_cltfin)))
        (.classMem (.cv p) (syn_cnnc)))
      (.classEq (syn_cplc A (syn_c1c)) (syn_cplc (syn_cplc B (.cv p)) (syn_c1c)))
  have p0041 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
          (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_cltfin)))
        (.classMem (.cv p) (syn_cnnc)))
      (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
        (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_cltfin)))
      (.classMem A (syn_cnnc)) p0021 p0008
  have p0046 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
          (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_cltfin)))
        (.classMem (.cv p) (syn_cnnc)))
      (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
        (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_cltfin)))
      (.classMem B (syn_cnnc)) p0021 p0003
  have p0048 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
          (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_cltfin)))
        (.classMem (.cv p) (syn_cnnc)))
      (.classMem B (syn_cnnc)) (.classMem (.cv p) (syn_cnnc)) p0046 p0030
  have p0049 := @g_nncaddccl B (.cv p)
  have p0050 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
          (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_cltfin)))
        (.classMem (.cv p) (syn_cnnc)))
      (syn_wa (.classMem B (syn_cnnc)) (.classMem (.cv p) (syn_cnnc)))
      (.classMem (syn_cplc B (.cv p)) (syn_cnnc)) p0048 p0049
  have p0051 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
          (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_cltfin)))
        (.classMem (.cv p) (syn_cnnc)))
      (.classMem A (syn_cnnc)) (.classMem (syn_cplc B (.cv p)) (syn_cnnc)) p0041 p0050
  have p0052 := @g_suc11nnc A (syn_cplc B (.cv p))
  have p0053 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
          (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_cltfin)))
        (.classMem (.cv p) (syn_cnnc)))
      (syn_wa (.classMem A (syn_cnnc)) (.classMem (syn_cplc B (.cv p)) (syn_cnnc)))
      (syn_wb (.classEq (syn_cplc A (syn_c1c)) (syn_cplc (syn_cplc B (.cv p)) (syn_c1c)))
        (.classEq A (syn_cplc B (.cv p))))
      p0051 p0052
  have p0054 :=
    @g_biimpd
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
          (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_cltfin)))
        (.classMem (.cv p) (syn_cnnc)))
      (.classEq (syn_cplc A (syn_c1c)) (syn_cplc (syn_cplc B (.cv p)) (syn_c1c)))
      (.classEq A (syn_cplc B (.cv p))) p0053
  have p0055 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
            (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_cltfin)))
          (.classMem (.cv p) (syn_cnnc)))
        (.classEq (syn_cplc A (syn_c1c)) (syn_cplc (syn_cplc B (.cv p)) (syn_c1c))))
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
          (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_cltfin)))
        (.classMem (.cv p) (syn_cnnc)))
      (.imp (.classEq (syn_cplc A (syn_c1c)) (syn_cplc (syn_cplc B (.cv p)) (syn_c1c)))
        (.classEq A (syn_cplc B (.cv p))))
      p0020 p0054
  have p0056 :=
    @g_mpd
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
            (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_cltfin)))
          (.classMem (.cv p) (syn_cnnc)))
        (.classEq (syn_cplc A (syn_c1c)) (syn_cplc (syn_cplc B (.cv p)) (syn_c1c))))
      (.classEq (syn_cplc A (syn_c1c)) (syn_cplc (syn_cplc B (.cv p)) (syn_c1c)))
      (.classEq A (syn_cplc B (.cv p))) p0035 p0055
  have p0057 :=
    @g_eqcomd
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
            (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_cltfin)))
          (.classMem (.cv p) (syn_cnnc)))
        (.classEq (syn_cplc A (syn_c1c)) (syn_cplc (syn_cplc B (.cv p)) (syn_c1c))))
      A (syn_cplc B (.cv p)) p0056
  have p0058 :=
    @g_opkeq2d
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
            (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_cltfin)))
          (.classMem (.cv p) (syn_cnnc)))
        (.classEq (syn_cplc A (syn_c1c)) (syn_cplc (syn_cplc B (.cv p)) (syn_c1c))))
      (syn_cplc B (.cv p)) A B p0057
  have p0059 :=
    @g_eleq1d
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
            (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_cltfin)))
          (.classMem (.cv p) (syn_cnnc)))
        (.classEq (syn_cplc A (syn_c1c)) (syn_cplc (syn_cplc B (.cv p)) (syn_c1c))))
      (syn_copk B (syn_cplc B (.cv p))) (syn_copk B A) (syn_clefin) p0058
  have p0060 :=
    @g_mpbid
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
            (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_cltfin)))
          (.classMem (.cv p) (syn_cnnc)))
        (.classEq (syn_cplc A (syn_c1c)) (syn_cplc (syn_cplc B (.cv p)) (syn_c1c))))
      (.classMem (syn_copk B (syn_cplc B (.cv p))) (syn_clefin))
      (.classMem (syn_copk B A) (syn_clefin)) p0034 p0059
  have p0061 :=
    @g_ex
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
          (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_cltfin)))
        (.classMem (.cv p) (syn_cnnc)))
      (.classEq (syn_cplc A (syn_c1c)) (syn_cplc (syn_cplc B (.cv p)) (syn_c1c)))
      (.classMem (syn_copk B A) (syn_clefin)) p0060
  have p0062 :=
    @g_rexlimdva
      (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
        (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_cltfin)))
      (.classEq (syn_cplc A (syn_c1c)) (syn_cplc (syn_cplc B (.cv p)) (syn_c1c)))
      (.classMem (syn_copk B A) (syn_clefin)) p (syn_cnnc) dv_cache_0003 dv_cache_0004
      p0061
  have p0063 :=
    @g_mpd
      (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
        (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_cltfin)))
      (syn_wrex p (syn_cnnc)
        (.classEq (syn_cplc A (syn_c1c)) (syn_cplc (syn_cplc B (.cv p)) (syn_c1c))))
      (.classMem (syn_copk B A) (syn_clefin)) p0019 p0062
  have p0064 :=
    @g_ex (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
      (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_cltfin))
      (.classMem (syn_copk B A) (syn_clefin)) p0063
  exact p0064

@[expose]
noncomputable def g_lefinsucsplit (A : Class) (B : Class) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
        (syn_wb (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_clefin))
          (syn_wo (.classMem (syn_copk B A) (syn_clefin))
            (.classEq B (syn_cplc A (syn_c1c)))))) :=
  by
  have p0000 :=
    @g_simpr (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
      (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_clefin))
  have p0001 :=
    @g_simpl (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
      (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_clefin))
  have p0002 := @g_simpr (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))
  have p0003 := @g_elex B (syn_cnnc)
  have p0004 :=
    @g_syl (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
      (.classMem B (syn_cnnc)) (.classMem B (syn_cvv)) p0002 p0003
  have p0005 := @g_simpl (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))
  have p0006 := @g_peano2 A
  have p0007 :=
    @g_syl (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
      (.classMem A (syn_cnnc)) (.classMem (syn_cplc A (syn_c1c)) (syn_cnnc)) p0005 p0006
  have p0008 := @g_elex (syn_cplc A (syn_c1c)) (syn_cnnc)
  have p0009 :=
    @g_syl (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
      (.classMem (syn_cplc A (syn_c1c)) (syn_cnnc))
      (.classMem (syn_cplc A (syn_c1c)) (syn_cvv)) p0007 p0008
  have p0010 :=
    @g_jca (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
      (.classMem B (syn_cvv)) (.classMem (syn_cplc A (syn_c1c)) (syn_cvv)) p0004 p0009
  have p0011 := @g_lefinlteqall B (syn_cplc A (syn_c1c)) (syn_cvv) (syn_cvv)
  have p0012 :=
    @g_syl (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
      (syn_wa (.classMem B (syn_cvv)) (.classMem (syn_cplc A (syn_c1c)) (syn_cvv)))
      (syn_wb (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_clefin))
        (syn_wo (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_cltfin))
          (.classEq B (syn_cplc A (syn_c1c)))))
      p0010 p0011
  have p0013 :=
    @g_biimpd (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
      (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_clefin))
      (syn_wo (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_cltfin))
        (.classEq B (syn_cplc A (syn_c1c))))
      p0012
  have p0014 :=
    @g_syl
      (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
        (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_clefin)))
      (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
      (.imp (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_clefin))
        (syn_wo (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_cltfin))
          (.classEq B (syn_cplc A (syn_c1c)))))
      p0001 p0013
  have p0015 :=
    @g_mpd
      (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
        (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_clefin)))
      (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_clefin))
      (syn_wo (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_cltfin))
        (.classEq B (syn_cplc A (syn_c1c))))
      p0000 p0014
  have p0017 := @g_ltfinsucle A B
  have p0018 :=
    @g_orc (.classMem (syn_copk B A) (syn_clefin)) (.classEq B (syn_cplc A (syn_c1c)))
  have p0019 :=
    @g_syl6 (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
      (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_cltfin))
      (.classMem (syn_copk B A) (syn_clefin))
      (syn_wo (.classMem (syn_copk B A) (syn_clefin)) (.classEq B (syn_cplc A (syn_c1c))))
      p0017 p0018
  have p0020 :=
    @g_olc (.classEq B (syn_cplc A (syn_c1c))) (.classMem (syn_copk B A) (syn_clefin))
  have p0021 :=
    @g_a1i
      (.imp (.classEq B (syn_cplc A (syn_c1c))) (syn_wo (.classMem (syn_copk B A) (syn_clefin))
          (.classEq B (syn_cplc A (syn_c1c)))))
      (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) p0020
  have p0022 :=
    @g_jaod (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
      (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_cltfin))
      (syn_wo (.classMem (syn_copk B A) (syn_clefin)) (.classEq B (syn_cplc A (syn_c1c))))
      (.classEq B (syn_cplc A (syn_c1c))) p0019 p0021
  have p0023 :=
    @g_syl
      (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
        (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_clefin)))
      (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
      (.imp (syn_wo (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_cltfin))
          (.classEq B (syn_cplc A (syn_c1c)))) (syn_wo (.classMem (syn_copk B A) (syn_clefin))
          (.classEq B (syn_cplc A (syn_c1c)))))
      p0001 p0022
  have p0024 :=
    @g_mpd
      (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
        (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_clefin)))
      (syn_wo (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_cltfin))
        (.classEq B (syn_cplc A (syn_c1c))))
      (syn_wo (.classMem (syn_copk B A) (syn_clefin)) (.classEq B (syn_cplc A (syn_c1c))))
      p0015 p0023
  have p0025 :=
    @g_ex (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
      (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_clefin))
      (syn_wo (.classMem (syn_copk B A) (syn_clefin)) (.classEq B (syn_cplc A (syn_c1c))))
      p0024
  have p0026 :=
    @g_simpr (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
      (.classMem (syn_copk B A) (syn_clefin))
  have p0027 :=
    @g_simpl (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
      (.classMem (syn_copk B A) (syn_clefin))
  have p0029 := @g_elex A (syn_cnnc)
  have p0030 :=
    @g_syl (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
      (.classMem A (syn_cnnc)) (.classMem A (syn_cvv)) p0005 p0029
  have p0031 := @g_n_1cnnc
  have p0032 :=
    @g_a1i (.classMem (syn_c1c) (syn_cnnc))
      (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) p0031
  have p0033 :=
    @g_jca (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
      (.classMem A (syn_cvv)) (.classMem (syn_c1c) (syn_cnnc)) p0030 p0032
  have p0034 := @g_lefinaddc A (syn_c1c) (syn_cvv)
  have p0035 :=
    @g_syl (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
      (syn_wa (.classMem A (syn_cvv)) (.classMem (syn_c1c) (syn_cnnc)))
      (.classMem (syn_copk A (syn_cplc A (syn_c1c))) (syn_clefin)) p0033 p0034
  have p0036 :=
    @g_syl
      (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
        (.classMem (syn_copk B A) (syn_clefin)))
      (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
      (.classMem (syn_copk A (syn_cplc A (syn_c1c))) (syn_clefin)) p0027 p0035
  have p0037 :=
    @g_jca
      (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
        (.classMem (syn_copk B A) (syn_clefin)))
      (.classMem (syn_copk B A) (syn_clefin))
      (.classMem (syn_copk A (syn_cplc A (syn_c1c))) (syn_clefin)) p0026 p0036
  have p0044 :=
    @g_n_3jca (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
      (.classMem B (syn_cnnc)) (.classMem A (syn_cnnc))
      (.classMem (syn_cplc A (syn_c1c)) (syn_cnnc)) p0002 p0005 p0007
  have p0045 := @g_lefintrnn B A (syn_cplc A (syn_c1c))
  have p0046 :=
    @g_syl (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
      (syn_w3a (.classMem B (syn_cnnc)) (.classMem A (syn_cnnc))
        (.classMem (syn_cplc A (syn_c1c)) (syn_cnnc)))
      (.imp (syn_wa (.classMem (syn_copk B A) (syn_clefin))
          (.classMem (syn_copk A (syn_cplc A (syn_c1c))) (syn_clefin)))
        (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_clefin)))
      p0044 p0045
  have p0047 :=
    @g_syl
      (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
        (.classMem (syn_copk B A) (syn_clefin)))
      (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
      (.imp (syn_wa (.classMem (syn_copk B A) (syn_clefin))
          (.classMem (syn_copk A (syn_cplc A (syn_c1c))) (syn_clefin)))
        (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_clefin)))
      p0027 p0046
  have p0048 :=
    @g_mpd
      (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
        (.classMem (syn_copk B A) (syn_clefin)))
      (syn_wa (.classMem (syn_copk B A) (syn_clefin))
        (.classMem (syn_copk A (syn_cplc A (syn_c1c))) (syn_clefin)))
      (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_clefin)) p0037 p0047
  have p0049 :=
    @g_ex (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
      (.classMem (syn_copk B A) (syn_clefin))
      (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_clefin)) p0048
  have p0050 :=
    @g_simpl (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
      (.classEq B (syn_cplc A (syn_c1c)))
  have p0056 :=
    @g_syl
      (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
        (.classEq B (syn_cplc A (syn_c1c))))
      (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
      (.classMem (syn_cplc A (syn_c1c)) (syn_cvv)) p0050 p0009
  have p0057 := @g_lefinrflx (syn_cplc A (syn_c1c)) (syn_cvv)
  have p0058 :=
    @g_syl
      (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
        (.classEq B (syn_cplc A (syn_c1c))))
      (.classMem (syn_cplc A (syn_c1c)) (syn_cvv))
      (.classMem (syn_copk (syn_cplc A (syn_c1c)) (syn_cplc A (syn_c1c))) (syn_clefin))
      p0056 p0057
  have p0059 :=
    @g_simpr (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
      (.classEq B (syn_cplc A (syn_c1c)))
  have p0060 :=
    @g_opkeq1d
      (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
        (.classEq B (syn_cplc A (syn_c1c))))
      B (syn_cplc A (syn_c1c)) (syn_cplc A (syn_c1c)) p0059
  have p0061 :=
    @g_eleq1d
      (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
        (.classEq B (syn_cplc A (syn_c1c))))
      (syn_copk B (syn_cplc A (syn_c1c)))
      (syn_copk (syn_cplc A (syn_c1c)) (syn_cplc A (syn_c1c))) (syn_clefin) p0060
  have p0062 :=
    @g_mpbird
      (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
        (.classEq B (syn_cplc A (syn_c1c))))
      (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_clefin))
      (.classMem (syn_copk (syn_cplc A (syn_c1c)) (syn_cplc A (syn_c1c))) (syn_clefin))
      p0058 p0061
  have p0063 :=
    @g_ex (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
      (.classEq B (syn_cplc A (syn_c1c)))
      (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_clefin)) p0062
  have p0064 :=
    @g_jaod (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
      (.classMem (syn_copk B A) (syn_clefin))
      (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_clefin))
      (.classEq B (syn_cplc A (syn_c1c))) p0049 p0063
  have p0065 :=
    @g_impbid (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
      (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_clefin))
      (syn_wo (.classMem (syn_copk B A) (syn_clefin)) (.classEq B (syn_cplc A (syn_c1c))))
      p0025 p0064
  exact p0065

@[expose]
noncomputable def g_lefinzeroeq (B : Class) :
    Nominal.NPrf
      (.imp (.classMem B (syn_cnnc)) (syn_wb (.classMem (syn_copk B (syn_c0c)) (syn_clefin))
          (.classEq B (syn_c0c)))) :=
  by
  have p0000 :=
    @g_simpr (.classMem B (syn_cnnc)) (.classMem (syn_copk B (syn_c0c)) (syn_clefin))
  have p0001 :=
    @g_simpl (.classMem B (syn_cnnc)) (.classMem (syn_copk B (syn_c0c)) (syn_clefin))
  have p0002 := @g_id (.classMem B (syn_cnnc))
  have p0003 := @g_n_0cminle B
  have p0004 :=
    @g_syl (.classMem B (syn_cnnc)) (.classMem B (syn_cnnc))
      (.classMem (syn_copk (syn_c0c) B) (syn_clefin)) p0002 p0003
  have p0005 :=
    @g_syl
      (syn_wa (.classMem B (syn_cnnc)) (.classMem (syn_copk B (syn_c0c)) (syn_clefin)))
      (.classMem B (syn_cnnc)) (.classMem (syn_copk (syn_c0c) B) (syn_clefin)) p0001 p0004
  have p0006 :=
    @g_jca
      (syn_wa (.classMem B (syn_cnnc)) (.classMem (syn_copk B (syn_c0c)) (syn_clefin)))
      (.classMem (syn_copk B (syn_c0c)) (syn_clefin))
      (.classMem (syn_copk (syn_c0c) B) (syn_clefin)) p0000 p0005
  have p0009 := @g_peano1
  have p0010 := @g_a1i (.classMem (syn_c0c) (syn_cnnc)) (.classMem B (syn_cnnc)) p0009
  have p0011 :=
    @g_jca (.classMem B (syn_cnnc)) (.classMem B (syn_cnnc))
      (.classMem (syn_c0c) (syn_cnnc)) p0002 p0010
  have p0012 :=
    @g_syl
      (syn_wa (.classMem B (syn_cnnc)) (.classMem (syn_copk B (syn_c0c)) (syn_clefin)))
      (.classMem B (syn_cnnc))
      (syn_wa (.classMem B (syn_cnnc)) (.classMem (syn_c0c) (syn_cnnc))) p0001 p0011
  have p0013 := @g_lefinantinn B (syn_c0c)
  have p0014 :=
    @g_syl
      (syn_wa (.classMem B (syn_cnnc)) (.classMem (syn_copk B (syn_c0c)) (syn_clefin)))
      (syn_wa (.classMem B (syn_cnnc)) (.classMem (syn_c0c) (syn_cnnc)))
      (.imp (syn_wa (.classMem (syn_copk B (syn_c0c)) (syn_clefin))
          (.classMem (syn_copk (syn_c0c) B) (syn_clefin))) (.classEq B (syn_c0c)))
      p0012 p0013
  have p0015 :=
    @g_mpd
      (syn_wa (.classMem B (syn_cnnc)) (.classMem (syn_copk B (syn_c0c)) (syn_clefin)))
      (syn_wa (.classMem (syn_copk B (syn_c0c)) (syn_clefin))
        (.classMem (syn_copk (syn_c0c) B) (syn_clefin)))
      (.classEq B (syn_c0c)) p0006 p0014
  have p0016 :=
    @g_ex (.classMem B (syn_cnnc)) (.classMem (syn_copk B (syn_c0c)) (syn_clefin))
      (.classEq B (syn_c0c)) p0015
  have p0017 := @g_n_0cex
  have p0018 := @g_lefinrflx (syn_c0c) (syn_cvv)
  have p0019 := Nominal.mp p0017 p0018
  have p0020 :=
    @g_a1i (.classMem (syn_copk (syn_c0c) (syn_c0c)) (syn_clefin))
      (syn_wa (.classMem B (syn_cnnc)) (.classEq B (syn_c0c))) p0019
  have p0021 := @g_simpr (.classMem B (syn_cnnc)) (.classEq B (syn_c0c))
  have p0022 :=
    @g_opkeq1d (syn_wa (.classMem B (syn_cnnc)) (.classEq B (syn_c0c))) B (syn_c0c)
      (syn_c0c) p0021
  have p0023 :=
    @g_eleq1d (syn_wa (.classMem B (syn_cnnc)) (.classEq B (syn_c0c)))
      (syn_copk B (syn_c0c)) (syn_copk (syn_c0c) (syn_c0c)) (syn_clefin) p0022
  have p0024 :=
    @g_mpbird (syn_wa (.classMem B (syn_cnnc)) (.classEq B (syn_c0c)))
      (.classMem (syn_copk B (syn_c0c)) (syn_clefin))
      (.classMem (syn_copk (syn_c0c) (syn_c0c)) (syn_clefin)) p0020 p0023
  have p0025 :=
    @g_ex (.classMem B (syn_cnnc)) (.classEq B (syn_c0c))
      (.classMem (syn_copk B (syn_c0c)) (syn_clefin)) p0024
  have p0026 :=
    @g_impbid (.classMem B (syn_cnnc)) (.classMem (syn_copk B (syn_c0c)) (syn_clefin))
      (.classEq B (syn_c0c)) p0016 p0025
  exact p0026

@[expose]
noncomputable def g_kqfinsucsplit (A : Class) (B : Class) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
        (syn_wb (syn_wbr B (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))
          (syn_wo (syn_wbr B (syn_ckqrel (syn_clefin)) A)
            (.classEq B (syn_cplc A (syn_c1c)))))) :=
  by
  have p0000 := @g_simpr (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))
  have p0001 := @g_elex B (syn_cnnc)
  have p0002 :=
    @g_syl (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
      (.classMem B (syn_cnnc)) (.classMem B (syn_cvv)) p0000 p0001
  have p0003 := @g_simpl (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))
  have p0004 := @g_peano2 A
  have p0005 :=
    @g_syl (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
      (.classMem A (syn_cnnc)) (.classMem (syn_cplc A (syn_c1c)) (syn_cnnc)) p0003 p0004
  have p0006 := @g_elex (syn_cplc A (syn_c1c)) (syn_cnnc)
  have p0007 :=
    @g_syl (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
      (.classMem (syn_cplc A (syn_c1c)) (syn_cnnc))
      (.classMem (syn_cplc A (syn_c1c)) (syn_cvv)) p0005 p0006
  have p0008 :=
    @g_jca (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
      (.classMem B (syn_cvv)) (.classMem (syn_cplc A (syn_c1c)) (syn_cvv)) p0002 p0007
  have p0009 := @g_kqlefinbr B (syn_cplc A (syn_c1c)) (syn_cvv) (syn_cvv)
  have p0010 :=
    @g_syl (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
      (syn_wa (.classMem B (syn_cvv)) (.classMem (syn_cplc A (syn_c1c)) (syn_cvv)))
      (syn_wb (syn_wbr B (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))
        (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_clefin)))
      p0008 p0009
  have p0011 := @g_lefinsucsplit A B
  have p0012 :=
    @g_bitrd (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
      (syn_wbr B (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))
      (.classMem (syn_copk B (syn_cplc A (syn_c1c))) (syn_clefin))
      (syn_wo (.classMem (syn_copk B A) (syn_clefin)) (.classEq B (syn_cplc A (syn_c1c))))
      p0010 p0011
  have p0017 := @g_elex A (syn_cnnc)
  have p0018 :=
    @g_syl (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
      (.classMem A (syn_cnnc)) (.classMem A (syn_cvv)) p0003 p0017
  have p0019 :=
    @g_jca (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
      (.classMem B (syn_cvv)) (.classMem A (syn_cvv)) p0002 p0018
  have p0020 := @g_kqlefinbr B A (syn_cvv) (syn_cvv)
  have p0021 :=
    @g_syl (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
      (syn_wa (.classMem B (syn_cvv)) (.classMem A (syn_cvv)))
      (syn_wb (syn_wbr B (syn_ckqrel (syn_clefin)) A) (.classMem (syn_copk B A) (syn_clefin)))
      p0019 p0020
  have p0022 :=
    @g_orbi1d (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
      (syn_wbr B (syn_ckqrel (syn_clefin)) A) (.classMem (syn_copk B A) (syn_clefin))
      (.classEq B (syn_cplc A (syn_c1c))) p0021
  have p0023 :=
    @g_bitr4d (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
      (syn_wbr B (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))
      (syn_wo (.classMem (syn_copk B A) (syn_clefin)) (.classEq B (syn_cplc A (syn_c1c))))
      (syn_wo (syn_wbr B (syn_ckqrel (syn_clefin)) A) (.classEq B (syn_cplc A (syn_c1c))))
      p0012 p0022
  exact p0023

@[expose]
noncomputable def g_kqfinzeroeq (B : Class) :
    Nominal.NPrf
      (.imp (.classMem B (syn_cnnc)) (syn_wb (syn_wbr B (syn_ckqrel (syn_clefin)) (syn_c0c))
          (.classEq B (syn_c0c)))) :=
  by
  have p0000 := @g_id (.classMem B (syn_cnnc))
  have p0001 := @g_elex B (syn_cnnc)
  have p0002 :=
    @g_syl (.classMem B (syn_cnnc)) (.classMem B (syn_cnnc)) (.classMem B (syn_cvv)) p0000
      p0001
  have p0003 := @g_n_0cex
  have p0004 := @g_a1i (.classMem (syn_c0c) (syn_cvv)) (.classMem B (syn_cnnc)) p0003
  have p0005 :=
    @g_jca (.classMem B (syn_cnnc)) (.classMem B (syn_cvv))
      (.classMem (syn_c0c) (syn_cvv)) p0002 p0004
  have p0006 := @g_kqlefinbr B (syn_c0c) (syn_cvv) (syn_cvv)
  have p0007 :=
    @g_syl (.classMem B (syn_cnnc))
      (syn_wa (.classMem B (syn_cvv)) (.classMem (syn_c0c) (syn_cvv)))
      (syn_wb (syn_wbr B (syn_ckqrel (syn_clefin)) (syn_c0c))
        (.classMem (syn_copk B (syn_c0c)) (syn_clefin)))
      p0005 p0006
  have p0008 := @g_lefinzeroeq B
  have p0009 :=
    @g_bitrd (.classMem B (syn_cnnc)) (syn_wbr B (syn_ckqrel (syn_clefin)) (syn_c0c))
      (.classMem (syn_copk B (syn_c0c)) (syn_clefin)) (.classEq B (syn_c0c)) p0007 p0008
  exact p0009

@[expose]
noncomputable def g_kqfin0min (B : Class) :
    Nominal.NPrf
      (.imp (.classMem B (syn_cnnc)) (syn_wbr (syn_c0c) (syn_ckqrel (syn_clefin)) B)) :=
  by
  have p0000 := @g_n_0cminle B
  have p0001 := @g_n_0cex
  have p0002 := @g_a1i (.classMem (syn_c0c) (syn_cvv)) (.classMem B (syn_cnnc)) p0001
  have p0003 := @g_id (.classMem B (syn_cnnc))
  have p0004 := @g_elex B (syn_cnnc)
  have p0005 :=
    @g_syl (.classMem B (syn_cnnc)) (.classMem B (syn_cnnc)) (.classMem B (syn_cvv)) p0003
      p0004
  have p0006 :=
    @g_jca (.classMem B (syn_cnnc)) (.classMem (syn_c0c) (syn_cvv))
      (.classMem B (syn_cvv)) p0002 p0005
  have p0007 := @g_kqlefinbr (syn_c0c) B (syn_cvv) (syn_cvv)
  have p0008 :=
    @g_syl (.classMem B (syn_cnnc))
      (syn_wa (.classMem (syn_c0c) (syn_cvv)) (.classMem B (syn_cvv)))
      (syn_wb (syn_wbr (syn_c0c) (syn_ckqrel (syn_clefin)) B)
        (.classMem (syn_copk (syn_c0c) B) (syn_clefin)))
      p0006 p0007
  have p0009 :=
    @g_mpbird (.classMem B (syn_cnnc)) (syn_wbr (syn_c0c) (syn_ckqrel (syn_clefin)) B)
      (.classMem (syn_copk (syn_c0c) B) (syn_clefin)) p0000 p0008
  exact p0009

@[expose]
noncomputable def g_finleastbase (y : Var) (z : Var) (t : Var) (X : Class)
    (dv_X_t : t ∉ X.fv) (dv_X_y : y ∉ X.fv) (dv_X_z : z ∉ X.fv) (dv_t_y : t ≠ y)
    (dv_t_z : t ≠ z) (dv_y_z : y ≠ z) :
    Nominal.NPrf
      (.imp (syn_wss X (syn_cnnc))
        (.imp (syn_wrex t X (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_c0c))) (syn_wrex z X
            (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))))) :=
  by
  have dv_cache_0001 :
    y ∉
      ((syn_wa (syn_wa (syn_wss X (syn_cnnc)) (.classMem (.cv t) X))
          (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_c0c)))).fv :=
    by
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union,
          Finset.mem_singleton, dv_X_y, (Ne.symm dv_t_y), compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((Wff.classEq (.cv z) (syn_c0c))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union,
          Finset.mem_singleton, dv_y_z, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0003 : z ∉ ((syn_c0c)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0004 : z ∉ (X).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_X_z, not_false_eq_true])
  have dv_cache_0005 :
    z ∉ ((syn_wral y X (syn_wbr (syn_c0c) (syn_ckqrel (syn_clefin)) (.cv y)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, dv_X_z, (Ne.symm dv_y_z), compact_fv_not_mem_empty,
          or_false, and_false, not_false_eq_true])
  have dv_cache_0006 :
    t ∉
      ((syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, dv_X_t, dv_t_z, dv_t_y,
          compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0007 : t ∉ ((syn_wss X (syn_cnnc))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union, dv_X_t,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have p0000 :=
    @g_simpl (syn_wa (syn_wss X (syn_cnnc)) (.classMem (.cv t) X))
      (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_c0c))
  have p0001 := @g_simpr (syn_wss X (syn_cnnc)) (.classMem (.cv t) X)
  have p0002 :=
    @g_syl
      (syn_wa (syn_wa (syn_wss X (syn_cnnc)) (.classMem (.cv t) X))
        (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_c0c)))
      (syn_wa (syn_wss X (syn_cnnc)) (.classMem (.cv t) X)) (.classMem (.cv t) X) p0000
      p0001
  have p0003 :=
    @g_simpr (syn_wa (syn_wss X (syn_cnnc)) (.classMem (.cv t) X))
      (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_c0c))
  have p0005 := @g_simpl (syn_wss X (syn_cnnc)) (.classMem (.cv t) X)
  have p0007 :=
    @g_sseldd (syn_wa (syn_wss X (syn_cnnc)) (.classMem (.cv t) X)) X (syn_cnnc) (.cv t)
      p0005 p0001
  have p0008 := @g_kqfinzeroeq (.cv t)
  have p0009 :=
    @g_syl (syn_wa (syn_wss X (syn_cnnc)) (.classMem (.cv t) X))
      (.classMem (.cv t) (syn_cnnc))
      (syn_wb (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_c0c))
        (.classEq (.cv t) (syn_c0c)))
      p0007 p0008
  have p0010 :=
    @g_biimpd (syn_wa (syn_wss X (syn_cnnc)) (.classMem (.cv t) X))
      (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_c0c)) (.classEq (.cv t) (syn_c0c))
      p0009
  have p0011 :=
    @g_syl
      (syn_wa (syn_wa (syn_wss X (syn_cnnc)) (.classMem (.cv t) X))
        (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_c0c)))
      (syn_wa (syn_wss X (syn_cnnc)) (.classMem (.cv t) X))
      (.imp (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_c0c)) (.classEq (.cv t) (syn_c0c)))
      p0000 p0010
  have p0012 :=
    @g_mpd
      (syn_wa (syn_wa (syn_wss X (syn_cnnc)) (.classMem (.cv t) X))
        (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_c0c)))
      (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_c0c)) (.classEq (.cv t) (syn_c0c))
      p0003 p0011
  have p0013 :=
    @g_eleq1d
      (syn_wa (syn_wa (syn_wss X (syn_cnnc)) (.classMem (.cv t) X))
        (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_c0c)))
      (.cv t) (syn_c0c) X p0012
  have p0014 :=
    @g_mpbid
      (syn_wa (syn_wa (syn_wss X (syn_cnnc)) (.classMem (.cv t) X))
        (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_c0c)))
      (.classMem (.cv t) X) (.classMem (syn_c0c) X) p0002 p0013
  have p0015 :=
    @g_simpl
      (syn_wa (syn_wa (syn_wss X (syn_cnnc)) (.classMem (.cv t) X))
        (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_c0c)))
      (.classMem (.cv y) X)
  have p0017 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wss X (syn_cnnc)) (.classMem (.cv t) X))
          (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_c0c))) (.classMem (.cv y) X))
      (syn_wa (syn_wa (syn_wss X (syn_cnnc)) (.classMem (.cv t) X))
        (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_c0c)))
      (syn_wa (syn_wss X (syn_cnnc)) (.classMem (.cv t) X)) p0015 p0000
  have p0019 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wss X (syn_cnnc)) (.classMem (.cv t) X))
          (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_c0c))) (.classMem (.cv y) X))
      (syn_wa (syn_wss X (syn_cnnc)) (.classMem (.cv t) X)) (syn_wss X (syn_cnnc)) p0017
      p0005
  have p0020 :=
    @g_simpr
      (syn_wa (syn_wa (syn_wss X (syn_cnnc)) (.classMem (.cv t) X))
        (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_c0c)))
      (.classMem (.cv y) X)
  have p0021 :=
    @g_sseldd
      (syn_wa (syn_wa (syn_wa (syn_wss X (syn_cnnc)) (.classMem (.cv t) X))
          (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_c0c))) (.classMem (.cv y) X))
      X (syn_cnnc) (.cv y) p0019 p0020
  have p0022 := @g_kqfin0min (.cv y)
  have p0023 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wss X (syn_cnnc)) (.classMem (.cv t) X))
          (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_c0c))) (.classMem (.cv y) X))
      (.classMem (.cv y) (syn_cnnc)) (syn_wbr (syn_c0c) (syn_ckqrel (syn_clefin)) (.cv y))
      p0021 p0022
  have p0024 :=
    @g_ralrimiva
      (syn_wa (syn_wa (syn_wss X (syn_cnnc)) (.classMem (.cv t) X))
        (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_c0c)))
      (syn_wbr (syn_c0c) (syn_ckqrel (syn_clefin)) (.cv y)) y X dv_cache_0001 p0023
  have p0025 :=
    @g_jca
      (syn_wa (syn_wa (syn_wss X (syn_cnnc)) (.classMem (.cv t) X))
        (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_c0c)))
      (.classMem (syn_c0c) X)
      (syn_wral y X (syn_wbr (syn_c0c) (syn_ckqrel (syn_clefin)) (.cv y))) p0014 p0024
  have p0026 := @g_breq1 (.cv z) (syn_c0c) (.cv y) (syn_ckqrel (syn_clefin))
  have p0027 :=
    @g_ralbidv (.classEq (.cv z) (syn_c0c))
      (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y))
      (syn_wbr (syn_c0c) (syn_ckqrel (syn_clefin)) (.cv y)) y X dv_cache_0002 p0026
  have p0028 :=
    @g_rspcev (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))
      (syn_wral y X (syn_wbr (syn_c0c) (syn_ckqrel (syn_clefin)) (.cv y))) z (syn_c0c) X
      dv_cache_0003 dv_cache_0004 dv_cache_0005 p0027
  have p0029 :=
    @g_syl
      (syn_wa (syn_wa (syn_wss X (syn_cnnc)) (.classMem (.cv t) X))
        (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_c0c)))
      (syn_wa (.classMem (syn_c0c) X)
        (syn_wral y X (syn_wbr (syn_c0c) (syn_ckqrel (syn_clefin)) (.cv y))))
      (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y))))
      p0025 p0028
  have p0030 :=
    @g_ex (syn_wa (syn_wss X (syn_cnnc)) (.classMem (.cv t) X))
      (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_c0c))
      (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y))))
      p0029
  have p0031 :=
    @g_rexlimdva (syn_wss X (syn_cnnc))
      (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_c0c))
      (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))) t
      X dv_cache_0006 dv_cache_0007 p0030
  exact p0031


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk014Compact001Part057`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_finleaststep (y : Var) (z : Var) (u : Var) (t : Var) (A : Class)
    (X : Class) (dv_A_t : t ∉ A.fv) (dv_A_u : u ∉ A.fv) (dv_A_y : y ∉ A.fv)
    (dv_A_z : z ∉ A.fv) (dv_X_t : t ∉ X.fv) (dv_X_u : u ∉ X.fv) (dv_X_y : y ∉ X.fv)
    (dv_X_z : z ∉ X.fv) (dv_t_u : t ≠ u) (dv_t_y : t ≠ y) (dv_t_z : t ≠ z)
    (dv_u_y : u ≠ y) (_dv_u_z : u ≠ z) (dv_y_z : y ≠ z) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.imp
          (syn_wa (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))
            (syn_wrex t X (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))))
          (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))))) :=
  by
  have dv_cache_0001 : u ∉ ((Class.cv t)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          (Ne.symm dv_t_u), not_false_eq_true])
  have dv_cache_0002 : u ∉ (X).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_X_u, not_false_eq_true])
  have dv_cache_0003 : u ∉ ((syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin, Finset.mem_union,
          Finset.mem_singleton, (Ne.symm dv_t_u), dv_A_u, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0004 : u ∉ ((Class.cv y)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, dv_u_y,
          not_false_eq_true])
  have dv_cache_0005 : u ∉ ((syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin, Finset.mem_union,
          Finset.mem_singleton, dv_u_y, dv_A_u, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0006 :
    y ∉
      ((syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc)))
              (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A))))
            (.classMem (.cv t) X))
          (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.CoreFVSimp.fv_wff_neg,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, dv_A_y, dv_X_y, (Ne.symm dv_u_y),
          (Ne.symm dv_t_y), compact_fv_not_mem_empty, or_false, and_false,
          not_false_eq_true])
  have dv_cache_0007 : y ∉ ((Wff.classEq (.cv z) (syn_cplc A (syn_c1c)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          Finset.mem_singleton, dv_y_z, dv_A_y, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0008 : z ∉ ((syn_cplc A (syn_c1c))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union, dv_A_z,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0009 : z ∉ (X).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_X_z, not_false_eq_true])
  have dv_cache_0010 :
    z ∉
      ((syn_wral y X (syn_wbr (syn_cplc A (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv y)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, dv_X_z, dv_A_z, (Ne.symm dv_y_z),
          compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0011 :
    t ∉
      ((syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, dv_X_t, dv_t_z, dv_t_y,
          compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0012 :
    t ∉
      ((syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc)))
          (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.CoreFVSimp.fv_wff_neg,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, dv_A_t, dv_X_t, dv_t_u,
          compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have p0000 :=
    @g_simpr (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc)))
      (syn_wa (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))
        (syn_wrex t X (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))))
  have p0001 :=
    @g_simpr (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))
      (syn_wrex t X (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c))))
  have p0002 :=
    @g_syl
      (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc)))
        (syn_wa (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))
          (syn_wrex t X (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c))))))
      (syn_wa (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))
        (syn_wrex t X (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))))
      (syn_wrex t X (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c))))
      p0000 p0001
  have p0003 :=
    @g_simpl (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc)))
      (syn_wa (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))
        (syn_wrex t X (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))))
  have p0005 :=
    @g_simpl (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))
      (syn_wrex t X (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c))))
  have p0006 :=
    @g_syl
      (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc)))
        (syn_wa (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))
          (syn_wrex t X (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c))))))
      (syn_wa (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))
        (syn_wrex t X (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))))
      (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A))) p0000 p0005
  have p0007 :=
    @g_jca
      (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc)))
        (syn_wa (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))
          (syn_wrex t X (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c))))))
      (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc)))
      (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A))) p0003 p0006
  have p0008 :=
    @g_simpl
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc)))
          (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A))))
        (.classMem (.cv t) X))
      (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))
  have p0009 :=
    @g_simpr
      (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc)))
        (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A))))
      (.classMem (.cv t) X)
  have p0010 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc)))
            (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A))))
          (.classMem (.cv t) X))
        (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c))))
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc)))
          (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A))))
        (.classMem (.cv t) X))
      (.classMem (.cv t) X) p0008 p0009
  have p0011 :=
    @g_simpr
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc)))
          (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A))))
        (.classMem (.cv t) X))
      (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))
  have p0013 :=
    @g_simpl
      (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc)))
        (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A))))
      (.classMem (.cv t) X)
  have p0014 :=
    @g_simpl (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc)))
      (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))
  have p0015 := @g_simpl (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))
  have p0016 :=
    @g_syl
      (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc)))
        (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A))))
      (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (.classMem A (syn_cnnc))
      p0014 p0015
  have p0017 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc)))
          (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A))))
        (.classMem (.cv t) X))
      (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc)))
        (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A))))
      (.classMem A (syn_cnnc)) p0013 p0016
  have p0020 := @g_simpr (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))
  have p0021 :=
    @g_syl
      (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc)))
        (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A))))
      (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc))) (syn_wss X (syn_cnnc))
      p0014 p0020
  have p0022 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc)))
          (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A))))
        (.classMem (.cv t) X))
      (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc)))
        (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A))))
      (syn_wss X (syn_cnnc)) p0013 p0021
  have p0024 :=
    @g_sseldd
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc)))
          (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A))))
        (.classMem (.cv t) X))
      X (syn_cnnc) (.cv t) p0022 p0009
  have p0025 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc)))
          (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A))))
        (.classMem (.cv t) X))
      (.classMem A (syn_cnnc)) (.classMem (.cv t) (syn_cnnc)) p0017 p0024
  have p0026 := @g_kqfinsucsplit A (.cv t)
  have p0027 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc)))
          (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A))))
        (.classMem (.cv t) X))
      (syn_wa (.classMem A (syn_cnnc)) (.classMem (.cv t) (syn_cnnc)))
      (syn_wb (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))
        (syn_wo (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) A)
          (.classEq (.cv t) (syn_cplc A (syn_c1c)))))
      p0025 p0026
  have p0028 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc)))
            (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A))))
          (.classMem (.cv t) X))
        (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c))))
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc)))
          (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A))))
        (.classMem (.cv t) X))
      (syn_wb (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))
        (syn_wo (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) A)
          (.classEq (.cv t) (syn_cplc A (syn_c1c)))))
      p0008 p0027
  have p0029 :=
    @g_biimpd
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc)))
            (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A))))
          (.classMem (.cv t) X))
        (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c))))
      (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))
      (syn_wo (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) A)
        (.classEq (.cv t) (syn_cplc A (syn_c1c))))
      p0028
  have p0030 :=
    @g_mpd
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc)))
            (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A))))
          (.classMem (.cv t) X))
        (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c))))
      (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))
      (syn_wo (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) A)
        (.classEq (.cv t) (syn_cplc A (syn_c1c))))
      p0011 p0029
  have p0033 :=
    @g_simpr (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc)))
      (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))
  have p0034 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc)))
          (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A))))
        (.classMem (.cv t) X))
      (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc)))
        (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A))))
      (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A))) p0013 p0033
  have p0035 :=
    @g_simpl
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc)))
          (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A))))
        (.classMem (.cv t) X))
      (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) A)
  have p0037 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc)))
            (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A))))
          (.classMem (.cv t) X)) (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) A))
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc)))
          (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A))))
        (.classMem (.cv t) X))
      (.classMem (.cv t) X) p0035 p0009
  have p0038 :=
    @g_simpr
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc)))
          (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A))))
        (.classMem (.cv t) X))
      (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) A)
  have p0039 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc)))
            (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A))))
          (.classMem (.cv t) X)) (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) A))
      (.classMem (.cv t) X) (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) A) p0037 p0038
  have p0040 := @g_breq1 (.cv u) (.cv t) A (syn_ckqrel (syn_clefin))
  have p0041 :=
    @g_rspcev (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)
      (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) A) u (.cv t) X dv_cache_0001
      dv_cache_0002 dv_cache_0003 p0040
  have p0042 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc)))
            (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A))))
          (.classMem (.cv t) X)) (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) A))
      (syn_wa (.classMem (.cv t) X) (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) A))
      (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)) p0039 p0041
  have p0043 :=
    @g_ex
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc)))
          (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A))))
        (.classMem (.cv t) X))
      (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) A)
      (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)) p0042
  have p0044 :=
    @g_con3d
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc)))
          (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A))))
        (.classMem (.cv t) X))
      (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) A)
      (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)) p0043
  have p0045 :=
    @g_mpd
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc)))
          (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A))))
        (.classMem (.cv t) X))
      (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))
      (.neg (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) A)) p0034 p0044
  have p0046 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc)))
            (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A))))
          (.classMem (.cv t) X))
        (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c))))
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc)))
          (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A))))
        (.classMem (.cv t) X))
      (.neg (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) A)) p0008 p0045
  have p0047 :=
    @g_pm2_21d
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc)))
            (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A))))
          (.classMem (.cv t) X))
        (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c))))
      (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) A)
      (.classEq (.cv t) (syn_cplc A (syn_c1c))) p0046
  have p0048 := @g_id (.classEq (.cv t) (syn_cplc A (syn_c1c)))
  have p0049 :=
    @g_a1i
      (.imp (.classEq (.cv t) (syn_cplc A (syn_c1c))) (.classEq (.cv t) (syn_cplc A (syn_c1c))))
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc)))
            (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A))))
          (.classMem (.cv t) X))
        (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c))))
      p0048
  have p0050 :=
    @g_jaod
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc)))
            (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A))))
          (.classMem (.cv t) X))
        (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c))))
      (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) A)
      (.classEq (.cv t) (syn_cplc A (syn_c1c))) (.classEq (.cv t) (syn_cplc A (syn_c1c)))
      p0047 p0049
  have p0051 :=
    @g_mpd
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc)))
            (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A))))
          (.classMem (.cv t) X))
        (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c))))
      (syn_wo (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) A)
        (.classEq (.cv t) (syn_cplc A (syn_c1c))))
      (.classEq (.cv t) (syn_cplc A (syn_c1c))) p0030 p0050
  have p0052 :=
    @g_eleq1d
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc)))
            (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A))))
          (.classMem (.cv t) X))
        (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c))))
      (.cv t) (syn_cplc A (syn_c1c)) X p0051
  have p0053 :=
    @g_mpbid
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc)))
            (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A))))
          (.classMem (.cv t) X))
        (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c))))
      (.classMem (.cv t) X) (.classMem (syn_cplc A (syn_c1c)) X) p0010 p0052
  have p0054 := @g_finleor
  have p0055 := @g_sopc (syn_cnnc) (syn_ckqrel (syn_clefin))
  have p0056 :=
    @g_biimpi (syn_wbr (syn_ckqrel (syn_clefin)) (syn_cstrict) (syn_cnnc))
      (syn_wa (syn_wbr (syn_ckqrel (syn_clefin)) (syn_cpartial) (syn_cnnc))
        (syn_wbr (syn_ckqrel (syn_clefin)) (syn_cconnex) (syn_cnnc)))
      p0055
  have p0057 := Nominal.mp p0054 p0056
  have p0058 :=
    @g_simpr (syn_wbr (syn_ckqrel (syn_clefin)) (syn_cpartial) (syn_cnnc))
      (syn_wbr (syn_ckqrel (syn_clefin)) (syn_cconnex) (syn_cnnc))
  have p0059 := Nominal.mp p0057 p0058
  have p0060 :=
    @g_a1i (syn_wbr (syn_ckqrel (syn_clefin)) (syn_cconnex) (syn_cnnc))
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc)))
              (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A))))
            (.classMem (.cv t) X))
          (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c))))
        (.classMem (.cv y) X))
      p0059
  have p0061 :=
    @g_simpl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc)))
            (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A))))
          (.classMem (.cv t) X))
        (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c))))
      (.classMem (.cv y) X)
  have p0063 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc)))
              (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A))))
            (.classMem (.cv t) X))
          (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c))))
        (.classMem (.cv y) X))
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc)))
            (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A))))
          (.classMem (.cv t) X))
        (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c))))
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc)))
          (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A))))
        (.classMem (.cv t) X))
      p0061 p0008
  have p0069 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc)))
              (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A))))
            (.classMem (.cv t) X))
          (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c))))
        (.classMem (.cv y) X))
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc)))
          (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A))))
        (.classMem (.cv t) X))
      (.classMem A (syn_cnnc)) p0063 p0017
  have p0070 := @g_peano2 A
  have p0071 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc)))
              (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A))))
            (.classMem (.cv t) X))
          (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c))))
        (.classMem (.cv y) X))
      (.classMem A (syn_cnnc)) (.classMem (syn_cplc A (syn_c1c)) (syn_cnnc)) p0069 p0070
  have p0080 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc)))
              (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A))))
            (.classMem (.cv t) X))
          (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c))))
        (.classMem (.cv y) X))
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc)))
          (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A))))
        (.classMem (.cv t) X))
      (syn_wss X (syn_cnnc)) p0063 p0022
  have p0081 :=
    @g_simpr
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc)))
            (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A))))
          (.classMem (.cv t) X))
        (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c))))
      (.classMem (.cv y) X)
  have p0082 :=
    @g_sseldd
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc)))
              (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A))))
            (.classMem (.cv t) X))
          (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c))))
        (.classMem (.cv y) X))
      X (syn_cnnc) (.cv y) p0080 p0081
  have p0083 :=
    @g_connexd
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc)))
              (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A))))
            (.classMem (.cv t) X))
          (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c))))
        (.classMem (.cv y) X))
      (syn_cnnc) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)) (.cv y) p0060 p0071
      p0082
  have p0084 := @g_id (syn_wbr (syn_cplc A (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv y))
  have p0085 :=
    @g_a1i
      (.imp (syn_wbr (syn_cplc A (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv y))
        (syn_wbr (syn_cplc A (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv y)))
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc)))
              (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A))))
            (.classMem (.cv t) X))
          (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c))))
        (.classMem (.cv y) X))
      p0084
  have p0086 :=
    @g_simpl
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc)))
              (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A))))
            (.classMem (.cv t) X))
          (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c))))
        (.classMem (.cv y) X))
      (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))
  have p0098 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa
              (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc)))
                (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A))))
              (.classMem (.cv t) X))
            (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c))))
          (.classMem (.cv y) X))
        (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c))))
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc)))
              (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A))))
            (.classMem (.cv t) X))
          (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c))))
        (.classMem (.cv y) X))
      (.classMem (syn_cplc A (syn_c1c)) (syn_cnnc)) p0086 p0071
  have p0099 := @g_elex (syn_cplc A (syn_c1c)) (syn_cnnc)
  have p0100 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa
              (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc)))
                (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A))))
              (.classMem (.cv t) X))
            (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c))))
          (.classMem (.cv y) X))
        (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c))))
      (.classMem (syn_cplc A (syn_c1c)) (syn_cnnc))
      (.classMem (syn_cplc A (syn_c1c)) (syn_cvv)) p0098 p0099
  have p0101 := @g_lefinrflx (syn_cplc A (syn_c1c)) (syn_cvv)
  have p0102 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa
              (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc)))
                (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A))))
              (.classMem (.cv t) X))
            (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c))))
          (.classMem (.cv y) X))
        (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c))))
      (.classMem (syn_cplc A (syn_c1c)) (syn_cvv))
      (.classMem (syn_copk (syn_cplc A (syn_c1c)) (syn_cplc A (syn_c1c))) (syn_clefin))
      p0100 p0101
  have p0133 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (syn_wa
              (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc)))
                (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A))))
              (.classMem (.cv t) X))
            (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c))))
          (.classMem (.cv y) X))
        (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c))))
      (.classMem (syn_cplc A (syn_c1c)) (syn_cvv))
      (.classMem (syn_cplc A (syn_c1c)) (syn_cvv)) p0100 p0100
  have p0134 :=
    @g_kqlefinbr (syn_cplc A (syn_c1c)) (syn_cplc A (syn_c1c)) (syn_cvv) (syn_cvv)
  have p0135 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa
              (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc)))
                (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A))))
              (.classMem (.cv t) X))
            (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c))))
          (.classMem (.cv y) X))
        (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c))))
      (syn_wa (.classMem (syn_cplc A (syn_c1c)) (syn_cvv))
        (.classMem (syn_cplc A (syn_c1c)) (syn_cvv)))
      (syn_wb (syn_wbr (syn_cplc A (syn_c1c)) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))
        (.classMem (syn_copk (syn_cplc A (syn_c1c)) (syn_cplc A (syn_c1c))) (syn_clefin)))
      p0133 p0134
  have p0136 :=
    @g_mpbird
      (syn_wa (syn_wa (syn_wa (syn_wa
              (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc)))
                (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A))))
              (.classMem (.cv t) X))
            (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c))))
          (.classMem (.cv y) X))
        (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c))))
      (syn_wbr (syn_cplc A (syn_c1c)) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))
      (.classMem (syn_copk (syn_cplc A (syn_c1c)) (syn_cplc A (syn_c1c))) (syn_clefin))
      p0102 p0135
  have p0137 :=
    @g_simpr
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc)))
              (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A))))
            (.classMem (.cv t) X))
          (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c))))
        (.classMem (.cv y) X))
      (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))
  have p0159 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc)))
              (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A))))
            (.classMem (.cv t) X))
          (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c))))
        (.classMem (.cv y) X))
      (.classMem A (syn_cnnc)) (.classMem (.cv y) (syn_cnnc)) p0069 p0082
  have p0160 := @g_kqfinsucsplit A (.cv y)
  have p0161 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc)))
              (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A))))
            (.classMem (.cv t) X))
          (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c))))
        (.classMem (.cv y) X))
      (syn_wa (.classMem A (syn_cnnc)) (.classMem (.cv y) (syn_cnnc)))
      (syn_wb (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))
        (syn_wo (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) A)
          (.classEq (.cv y) (syn_cplc A (syn_c1c)))))
      p0159 p0160
  have p0162 :=
    @g_biimpd
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc)))
              (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A))))
            (.classMem (.cv t) X))
          (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c))))
        (.classMem (.cv y) X))
      (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))
      (syn_wo (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) A)
        (.classEq (.cv y) (syn_cplc A (syn_c1c))))
      p0161
  have p0163 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa
              (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc)))
                (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A))))
              (.classMem (.cv t) X))
            (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c))))
          (.classMem (.cv y) X))
        (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c))))
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc)))
              (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A))))
            (.classMem (.cv t) X))
          (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c))))
        (.classMem (.cv y) X))
      (.imp (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))
        (syn_wo (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) A)
          (.classEq (.cv y) (syn_cplc A (syn_c1c)))))
      p0086 p0162
  have p0164 :=
    @g_mpd
      (syn_wa (syn_wa (syn_wa (syn_wa
              (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc)))
                (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A))))
              (.classMem (.cv t) X))
            (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c))))
          (.classMem (.cv y) X))
        (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c))))
      (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))
      (syn_wo (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) A)
        (.classEq (.cv y) (syn_cplc A (syn_c1c))))
      p0137 p0163
  have p0172 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc)))
              (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A))))
            (.classMem (.cv t) X))
          (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c))))
        (.classMem (.cv y) X))
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc)))
          (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A))))
        (.classMem (.cv t) X))
      (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A))) p0063 p0034
  have p0173 :=
    @g_simpl
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc)))
              (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A))))
            (.classMem (.cv t) X))
          (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c))))
        (.classMem (.cv y) X))
      (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) A)
  have p0175 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa
              (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc)))
                (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A))))
              (.classMem (.cv t) X))
            (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c))))
          (.classMem (.cv y) X)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) A))
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc)))
              (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A))))
            (.classMem (.cv t) X))
          (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c))))
        (.classMem (.cv y) X))
      (.classMem (.cv y) X) p0173 p0081
  have p0176 :=
    @g_simpr
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc)))
              (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A))))
            (.classMem (.cv t) X))
          (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c))))
        (.classMem (.cv y) X))
      (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) A)
  have p0177 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (syn_wa
              (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc)))
                (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A))))
              (.classMem (.cv t) X))
            (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c))))
          (.classMem (.cv y) X)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) A))
      (.classMem (.cv y) X) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) A) p0175 p0176
  have p0178 := @g_breq1 (.cv u) (.cv y) A (syn_ckqrel (syn_clefin))
  have p0179 :=
    @g_rspcev (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)
      (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) A) u (.cv y) X dv_cache_0004
      dv_cache_0002 dv_cache_0005 p0178
  have p0180 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa
              (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc)))
                (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A))))
              (.classMem (.cv t) X))
            (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c))))
          (.classMem (.cv y) X)) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) A))
      (syn_wa (.classMem (.cv y) X) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) A))
      (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)) p0177 p0179
  have p0181 :=
    @g_ex
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc)))
              (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A))))
            (.classMem (.cv t) X))
          (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c))))
        (.classMem (.cv y) X))
      (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) A)
      (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)) p0180
  have p0182 :=
    @g_con3d
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc)))
              (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A))))
            (.classMem (.cv t) X))
          (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c))))
        (.classMem (.cv y) X))
      (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) A)
      (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)) p0181
  have p0183 :=
    @g_mpd
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc)))
              (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A))))
            (.classMem (.cv t) X))
          (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c))))
        (.classMem (.cv y) X))
      (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))
      (.neg (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) A)) p0172 p0182
  have p0184 :=
    @g_pm2_21d
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc)))
              (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A))))
            (.classMem (.cv t) X))
          (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c))))
        (.classMem (.cv y) X))
      (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) A)
      (.classEq (.cv y) (syn_cplc A (syn_c1c))) p0183
  have p0185 := @g_id (.classEq (.cv y) (syn_cplc A (syn_c1c)))
  have p0186 :=
    @g_a1i
      (.imp (.classEq (.cv y) (syn_cplc A (syn_c1c))) (.classEq (.cv y) (syn_cplc A (syn_c1c))))
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc)))
              (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A))))
            (.classMem (.cv t) X))
          (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c))))
        (.classMem (.cv y) X))
      p0185
  have p0187 :=
    @g_jaod
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc)))
              (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A))))
            (.classMem (.cv t) X))
          (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c))))
        (.classMem (.cv y) X))
      (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) A)
      (.classEq (.cv y) (syn_cplc A (syn_c1c))) (.classEq (.cv y) (syn_cplc A (syn_c1c)))
      p0184 p0186
  have p0188 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa
              (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc)))
                (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A))))
              (.classMem (.cv t) X))
            (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c))))
          (.classMem (.cv y) X))
        (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c))))
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc)))
              (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A))))
            (.classMem (.cv t) X))
          (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c))))
        (.classMem (.cv y) X))
      (.imp (syn_wo (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) A)
          (.classEq (.cv y) (syn_cplc A (syn_c1c)))) (.classEq (.cv y) (syn_cplc A (syn_c1c))))
      p0086 p0187
  have p0189 :=
    @g_mpd
      (syn_wa (syn_wa (syn_wa (syn_wa
              (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc)))
                (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A))))
              (.classMem (.cv t) X))
            (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c))))
          (.classMem (.cv y) X))
        (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c))))
      (syn_wo (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) A)
        (.classEq (.cv y) (syn_cplc A (syn_c1c))))
      (.classEq (.cv y) (syn_cplc A (syn_c1c))) p0164 p0188
  have p0190 :=
    @g_breq2d
      (syn_wa (syn_wa (syn_wa (syn_wa
              (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc)))
                (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A))))
              (.classMem (.cv t) X))
            (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c))))
          (.classMem (.cv y) X))
        (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c))))
      (.cv y) (syn_cplc A (syn_c1c)) (syn_cplc A (syn_c1c)) (syn_ckqrel (syn_clefin))
      p0189
  have p0191 :=
    @g_mpbird
      (syn_wa (syn_wa (syn_wa (syn_wa
              (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc)))
                (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A))))
              (.classMem (.cv t) X))
            (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c))))
          (.classMem (.cv y) X))
        (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c))))
      (syn_wbr (syn_cplc A (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv y))
      (syn_wbr (syn_cplc A (syn_c1c)) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))
      p0136 p0190
  have p0192 :=
    @g_ex
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc)))
              (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A))))
            (.classMem (.cv t) X))
          (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c))))
        (.classMem (.cv y) X))
      (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))
      (syn_wbr (syn_cplc A (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv y)) p0191
  have p0193 :=
    @g_jaod
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc)))
              (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A))))
            (.classMem (.cv t) X))
          (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c))))
        (.classMem (.cv y) X))
      (syn_wbr (syn_cplc A (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv y))
      (syn_wbr (syn_cplc A (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv y))
      (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c))) p0085 p0192
  have p0194 :=
    @g_mpd
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc)))
              (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A))))
            (.classMem (.cv t) X))
          (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c))))
        (.classMem (.cv y) X))
      (syn_wo (syn_wbr (syn_cplc A (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv y))
        (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c))))
      (syn_wbr (syn_cplc A (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv y)) p0083 p0193
  have p0195 :=
    @g_ralrimiva
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc)))
            (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A))))
          (.classMem (.cv t) X))
        (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c))))
      (syn_wbr (syn_cplc A (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv y)) y X dv_cache_0006
      p0194
  have p0196 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc)))
            (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A))))
          (.classMem (.cv t) X))
        (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c))))
      (.classMem (syn_cplc A (syn_c1c)) X)
      (syn_wral y X (syn_wbr (syn_cplc A (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv y)))
      p0053 p0195
  have p0197 := @g_breq1 (.cv z) (syn_cplc A (syn_c1c)) (.cv y) (syn_ckqrel (syn_clefin))
  have p0198 :=
    @g_ralbidv (.classEq (.cv z) (syn_cplc A (syn_c1c)))
      (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y))
      (syn_wbr (syn_cplc A (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv y)) y X dv_cache_0007
      p0197
  have p0199 :=
    @g_rspcev (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))
      (syn_wral y X (syn_wbr (syn_cplc A (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv y))) z
      (syn_cplc A (syn_c1c)) X dv_cache_0008 dv_cache_0009 dv_cache_0010 p0198
  have p0200 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc)))
            (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A))))
          (.classMem (.cv t) X))
        (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c))))
      (syn_wa (.classMem (syn_cplc A (syn_c1c)) X)
        (syn_wral y X (syn_wbr (syn_cplc A (syn_c1c)) (syn_ckqrel (syn_clefin)) (.cv y))))
      (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y))))
      p0196 p0199
  have p0201 :=
    @g_ex
      (syn_wa (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc)))
          (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A))))
        (.classMem (.cv t) X))
      (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))
      (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y))))
      p0200
  have p0202 :=
    @g_rexlimdva
      (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc)))
        (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A))))
      (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))
      (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))) t
      X dv_cache_0011 dv_cache_0012 p0201
  have p0203 :=
    @g_syl
      (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc)))
        (syn_wa (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))
          (syn_wrex t X (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c))))))
      (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc)))
        (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A))))
      (.imp (syn_wrex t X (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c))))
        (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))))
      p0007 p0202
  have p0204 :=
    @g_mpd
      (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc)))
        (syn_wa (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))
          (syn_wrex t X (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c))))))
      (syn_wrex t X (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c))))
      (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y))))
      p0002 p0203
  have p0205 :=
    @g_ex (syn_wa (.classMem A (syn_cnnc)) (syn_wss X (syn_cnnc)))
      (syn_wa (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) A)))
        (syn_wrex t X (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc A (syn_c1c)))))
      (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y))))
      p0204
  exact p0205


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk014Compact001Part058`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_finleastnn (y : Var) (z : Var) (V : Class) (X : Class)
    (_dv_V_y : y ∉ V.fv) (_dv_V_z : z ∉ V.fv) (dv_X_y : y ∉ X.fv) (dv_X_z : z ∉ X.fv)
    (dv_y_z : y ≠ z) :
    Nominal.NPrf
      (.imp (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (syn_wrex z X
          (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y))))) :=
  by
  let proofSupport : Finset Var :=
    ({ y } : Finset Var) ∪ ({ z } : Finset Var) ∪ V.fv ∪ X.fv
  let t : Var := freshVar proofSupport 0
  let u : Var := freshVar proofSupport 1
  let n : Var := freshVar proofSupport 2
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
  have fresh_t_ne_z : t ≠ z := by
    intro h
    exact
      fresh_t
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_t_not_V : t ∉ V.fv := by
    intro h
    exact fresh_t (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_t_not_X : t ∉ X.fv := by
    intro h
    exact fresh_t (Finset.mem_union_right _ (h))
  have fresh_u : u ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_u_ne_y : u ≠ y := by
    intro h
    exact
      fresh_u
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_u_ne_z : u ≠ z := by
    intro h
    exact
      fresh_u
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_u_not_X : u ∉ X.fv := by
    intro h
    exact fresh_u (Finset.mem_union_right _ (h))
  have fresh_n : n ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_n_ne_y : n ≠ y := by
    intro h
    exact
      fresh_n
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_y_ne_n : y ≠ n := Ne.symm fresh_n_ne_y
  have fresh_n_ne_z : n ≠ z := by
    intro h
    exact
      fresh_n
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_z_ne_n : z ≠ n := Ne.symm fresh_n_ne_z
  have fresh_n_not_V : n ∉ V.fv := by
    intro h
    exact fresh_n (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_n_not_X : n ∉ X.fv := by
    intro h
    exact fresh_n (Finset.mem_union_right _ (h))
  have fresh_t_ne_u : t ≠ u :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_u_ne_t : u ≠ t := Ne.symm fresh_t_ne_u
  have fresh_t_ne_n : t ≠ n :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_u_ne_n : u ≠ n :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have dv_cache_0001 : t ∉ (X).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_t_not_X, not_false_eq_true])
  have dv_cache_0002 : u ∉ ((Class.cv t)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_u_ne_t, not_false_eq_true])
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
  have dv_cache_0004 : u ∉ ((syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (.cv t))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin, Finset.mem_union,
          Finset.mem_singleton, fresh_u_ne_t, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0005 : u ∉ ((syn_ckqrel (syn_clefin))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0006 : t ∉ ((syn_c0c)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0007 : t ∉ ((syn_ckqrel (syn_clefin))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0008 : y ∉ (X).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_X_y, not_false_eq_true])
  have dv_cache_0009 : z ∉ (X).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_X_z, not_false_eq_true])
  have dv_cache_0010 : t ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (show t ≠ y from (by exact fresh_t_ne_y))
  have dv_cache_0011 : t ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (show t ≠ z from (by exact fresh_t_ne_z))
  have dv_cache_0012 : y ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (show y ≠ z from (by exact dv_y_z))
  have dv_cache_0013 : u ∉ ((Class.cv n)).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_u_ne_n, not_false_eq_true])
  have dv_cache_0014 : t ∉ ((syn_cplc (.cv n) (syn_c1c))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          Finset.mem_singleton, fresh_t_ne_n, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0015 : t ∉ ((Class.cv n)).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_t_ne_n, not_false_eq_true])
  have dv_cache_0016 : y ∉ ((Class.cv n)).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_y_ne_n, not_false_eq_true])
  have dv_cache_0017 : z ∉ ((Class.cv n)).fv :=
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
          fresh_z_ne_n, not_false_eq_true])
  have dv_cache_0018 : t ≠ u :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact (show t ≠ u from (by exact fresh_t_ne_u))
  have dv_cache_0019 : u ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018
    exact (show u ≠ y from (by exact fresh_u_ne_y))
  have dv_cache_0020 : u ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019
    exact (show u ≠ z from (by exact fresh_u_ne_z))
  have dv_cache_0021 :
    n ∉
      ((syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg
            (syn_wrex z X
              (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
          NFChoice.Compiler.CoreFVSimp.fv_wff_neg,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_n_not_X, fresh_n_not_V,
          fresh_n_ne_z, fresh_n_ne_y, compact_fv_not_mem_empty, or_false, and_false,
          not_false_eq_true])
  have dv_cache_0022 :
    n ∉ ((syn_cdif (syn_cvv) (syn_cima (syn_ckqrel (syn_clefin)) X))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin, Finset.mem_union,
          fresh_n_not_X, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0023 :
    t ∉
      ((syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_t_not_X, fresh_t_ne_z,
          fresh_t_ne_y, compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0024 :
    t ∉
      ((syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg
            (syn_wrex z X
              (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
          NFChoice.Compiler.CoreFVSimp.fv_wff_neg,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_t_not_X, fresh_t_not_V,
          fresh_t_ne_z, fresh_t_ne_y, compact_fv_not_mem_empty, or_false, and_false,
          not_false_eq_true])
  have p0000 :=
    @g_simpl (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0)))
      (.neg (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))))
  have p0001 := @g_simp3 (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))
  have p0002 :=
    @g_syl
      (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg
          (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y))))))
      (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0)))
      (syn_wne X (syn_c0)) p0000 p0001
  have p0003 := @g_n0 t X dv_cache_0001
  have p0004 := @g_biimpi (syn_wne X (syn_c0)) (syn_wex t (.classMem (.cv t) X)) p0003
  have p0005 :=
    @g_syl
      (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg
          (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y))))))
      (syn_wne X (syn_c0)) (syn_wex t (.classMem (.cv t) X)) p0002 p0004
  have p0006 :=
    @g_simpr
      (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg
          (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y))))))
      (.classMem (.cv t) X)
  have p0007 :=
    @g_simpl
      (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg
          (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y))))))
      (.classMem (.cv t) X)
  have p0009 := @g_simp2 (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))
  have p0010 :=
    @g_syl
      (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg
          (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y))))))
      (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0)))
      (syn_wss X (syn_cnnc)) p0000 p0009
  have p0011 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0)))
          (.neg (syn_wrex z X
              (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y))))))
        (.classMem (.cv t) X))
      (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg
          (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y))))))
      (syn_wss X (syn_cnnc)) p0007 p0010
  have p0013 :=
    @g_sseldd
      (syn_wa (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0)))
          (.neg (syn_wrex z X
              (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y))))))
        (.classMem (.cv t) X))
      X (syn_cnnc) (.cv t) p0011 p0006
  have p0014 := @g_elex (.cv t) (syn_cnnc)
  have p0015 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0)))
          (.neg (syn_wrex z X
              (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y))))))
        (.classMem (.cv t) X))
      (.classMem (.cv t) (syn_cnnc)) (.classMem (.cv t) (syn_cvv)) p0013 p0014
  have p0016 := @g_lefinrflx (.cv t) (syn_cvv)
  have p0017 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0)))
          (.neg (syn_wrex z X
              (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y))))))
        (.classMem (.cv t) X))
      (.classMem (.cv t) (syn_cvv)) (.classMem (syn_copk (.cv t) (.cv t)) (syn_clefin))
      p0015 p0016
  have p0036 :=
    @g_jca
      (syn_wa (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0)))
          (.neg (syn_wrex z X
              (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y))))))
        (.classMem (.cv t) X))
      (.classMem (.cv t) (syn_cvv)) (.classMem (.cv t) (syn_cvv)) p0015 p0015
  have p0037 := @g_kqlefinbr (.cv t) (.cv t) (syn_cvv) (syn_cvv)
  have p0038 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0)))
          (.neg (syn_wrex z X
              (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y))))))
        (.classMem (.cv t) X))
      (syn_wa (.classMem (.cv t) (syn_cvv)) (.classMem (.cv t) (syn_cvv)))
      (syn_wb (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (.cv t))
        (.classMem (syn_copk (.cv t) (.cv t)) (syn_clefin)))
      p0036 p0037
  have p0039 :=
    @g_mpbird
      (syn_wa (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0)))
          (.neg (syn_wrex z X
              (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y))))))
        (.classMem (.cv t) X))
      (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (.cv t))
      (.classMem (syn_copk (.cv t) (.cv t)) (syn_clefin)) p0017 p0038
  have p0040 :=
    @g_jca
      (syn_wa (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0)))
          (.neg (syn_wrex z X
              (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y))))))
        (.classMem (.cv t) X))
      (.classMem (.cv t) X) (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (.cv t)) p0006
      p0039
  have p0041 := @g_breq1 (.cv u) (.cv t) (.cv t) (syn_ckqrel (syn_clefin))
  have p0042 :=
    @g_rspcev (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) (.cv t))
      (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (.cv t)) u (.cv t) X dv_cache_0002
      dv_cache_0003 dv_cache_0004 p0041
  have p0043 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0)))
          (.neg (syn_wrex z X
              (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y))))))
        (.classMem (.cv t) X))
      (syn_wa (.classMem (.cv t) X) (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (.cv t)))
      (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) (.cv t))) p0040 p0042
  have p0044 :=
    @g_elima u (.cv t) (syn_ckqrel (syn_clefin)) X dv_cache_0002 dv_cache_0005
      dv_cache_0003
  have p0045 :=
    @g_a1i
      (syn_wb (.classMem (.cv t) (syn_cima (syn_ckqrel (syn_clefin)) X))
        (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) (.cv t))))
      (syn_wa (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0)))
          (.neg (syn_wrex z X
              (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y))))))
        (.classMem (.cv t) X))
      p0044
  have p0046 :=
    @g_mpbird
      (syn_wa (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0)))
          (.neg (syn_wrex z X
              (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y))))))
        (.classMem (.cv t) X))
      (.classMem (.cv t) (syn_cima (syn_ckqrel (syn_clefin)) X))
      (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) (.cv t))) p0043 p0045
  have p0048 := @g_vvex
  have p0049 :=
    @g_a1i (.classMem (syn_cvv) (syn_cvv))
      (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg
          (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y))))))
      p0048
  have p0050 := @g_lefinex
  have p0051 := @g_kqrelex (syn_clefin) p0050
  have p0052 :=
    @g_a1i (.classMem (syn_ckqrel (syn_clefin)) (syn_cvv))
      (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg
          (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y))))))
      p0051
  have p0054 := @g_simp1 (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))
  have p0055 :=
    @g_syl
      (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg
          (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y))))))
      (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0)))
      (.classMem X V) p0000 p0054
  have p0056 :=
    @g_jca
      (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg
          (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y))))))
      (.classMem (syn_ckqrel (syn_clefin)) (syn_cvv)) (.classMem X V) p0052 p0055
  have p0057 := @g_imaexg (syn_ckqrel (syn_clefin)) X (syn_cvv) V
  have p0058 :=
    @g_syl
      (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg
          (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y))))))
      (syn_wa (.classMem (syn_ckqrel (syn_clefin)) (syn_cvv)) (.classMem X V))
      (.classMem (syn_cima (syn_ckqrel (syn_clefin)) X) (syn_cvv)) p0056 p0057
  have p0059 :=
    @g_jca
      (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg
          (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y))))))
      (.classMem (syn_cvv) (syn_cvv))
      (.classMem (syn_cima (syn_ckqrel (syn_clefin)) X) (syn_cvv)) p0049 p0058
  have p0060 :=
    @g_difexg (syn_cvv) (syn_cima (syn_ckqrel (syn_clefin)) X) (syn_cvv) (syn_cvv)
  have p0061 :=
    @g_syl
      (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg
          (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y))))))
      (syn_wa (.classMem (syn_cvv) (syn_cvv))
        (.classMem (syn_cima (syn_ckqrel (syn_clefin)) X) (syn_cvv)))
      (.classMem (syn_cdif (syn_cvv) (syn_cima (syn_ckqrel (syn_clefin)) X)) (syn_cvv))
      p0059 p0060
  have p0062 := @g_n_0cex
  have p0063 :=
    @g_a1i (.classMem (syn_c0c) (syn_cvv))
      (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg
          (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y))))))
      p0062
  have p0064 :=
    @g_simpr (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0)))
      (.neg (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))))
  have p0065 :=
    @g_elima t (syn_c0c) (syn_ckqrel (syn_clefin)) X dv_cache_0006 dv_cache_0007
      dv_cache_0001
  have p0066 :=
    @g_biimpi (.classMem (syn_c0c) (syn_cima (syn_ckqrel (syn_clefin)) X))
      (syn_wrex t X (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_c0c))) p0065
  have p0070 :=
    @g_finleastbase y z t X dv_cache_0001 dv_cache_0008 dv_cache_0009 dv_cache_0010
      dv_cache_0011 dv_cache_0012
  have p0071 :=
    @g_syl
      (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg
          (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y))))))
      (syn_wss X (syn_cnnc))
      (.imp (syn_wrex t X (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_c0c)))
        (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))))
      p0010 p0070
  have p0072 :=
    @g_syl5 (.classMem (syn_c0c) (syn_cima (syn_ckqrel (syn_clefin)) X))
      (syn_wrex t X (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_c0c)))
      (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg
          (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y))))))
      (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y))))
      p0066 p0071
  have p0073 :=
    @g_con3d
      (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg
          (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y))))))
      (.classMem (syn_c0c) (syn_cima (syn_ckqrel (syn_clefin)) X))
      (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y))))
      p0072
  have p0074 :=
    @g_mpd
      (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg
          (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y))))))
      (.neg (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))))
      (.neg (.classMem (syn_c0c) (syn_cima (syn_ckqrel (syn_clefin)) X))) p0064 p0073
  have p0075 :=
    @g_jca
      (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg
          (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y))))))
      (.classMem (syn_c0c) (syn_cvv))
      (.neg (.classMem (syn_c0c) (syn_cima (syn_ckqrel (syn_clefin)) X))) p0063 p0074
  have p0076 := @g_eldif (syn_c0c) (syn_cvv) (syn_cima (syn_ckqrel (syn_clefin)) X)
  have p0077 :=
    @g_a1i
      (syn_wb (.classMem (syn_c0c) (syn_cdif (syn_cvv) (syn_cima (syn_ckqrel (syn_clefin)) X)))
        (syn_wa (.classMem (syn_c0c) (syn_cvv))
          (.neg (.classMem (syn_c0c) (syn_cima (syn_ckqrel (syn_clefin)) X)))))
      (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg
          (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y))))))
      p0076
  have p0078 :=
    @g_mpbird
      (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg
          (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y))))))
      (.classMem (syn_c0c) (syn_cdif (syn_cvv) (syn_cima (syn_ckqrel (syn_clefin)) X)))
      (syn_wa (.classMem (syn_c0c) (syn_cvv))
        (.neg (.classMem (syn_c0c) (syn_cima (syn_ckqrel (syn_clefin)) X))))
      p0075 p0077
  have p0079 :=
    @g_simpl
      (syn_wa (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0)))
          (.neg (syn_wrex z X
              (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y))))))
        (.classMem (.cv n) (syn_cnnc)))
      (.classMem (.cv n) (syn_cdif (syn_cvv) (syn_cima (syn_ckqrel (syn_clefin)) X)))
  have p0080 :=
    @g_simpr
      (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg
          (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y))))))
      (.classMem (.cv n) (syn_cnnc))
  have p0081 :=
    @g_syl
      (syn_wa (syn_wa
          (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg
              (syn_wrex z X
                (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y))))))
          (.classMem (.cv n) (syn_cnnc)))
        (.classMem (.cv n) (syn_cdif (syn_cvv) (syn_cima (syn_ckqrel (syn_clefin)) X))))
      (syn_wa (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0)))
          (.neg (syn_wrex z X
              (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y))))))
        (.classMem (.cv n) (syn_cnnc)))
      (.classMem (.cv n) (syn_cnnc)) p0079 p0080
  have p0082 := @g_peano2 (.cv n)
  have p0083 :=
    @g_syl
      (syn_wa (syn_wa
          (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg
              (syn_wrex z X
                (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y))))))
          (.classMem (.cv n) (syn_cnnc)))
        (.classMem (.cv n) (syn_cdif (syn_cvv) (syn_cima (syn_ckqrel (syn_clefin)) X))))
      (.classMem (.cv n) (syn_cnnc)) (.classMem (syn_cplc (.cv n) (syn_c1c)) (syn_cnnc))
      p0081 p0082
  have p0084 := @g_elex (syn_cplc (.cv n) (syn_c1c)) (syn_cnnc)
  have p0085 :=
    @g_syl
      (syn_wa (syn_wa
          (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg
              (syn_wrex z X
                (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y))))))
          (.classMem (.cv n) (syn_cnnc)))
        (.classMem (.cv n) (syn_cdif (syn_cvv) (syn_cima (syn_ckqrel (syn_clefin)) X))))
      (.classMem (syn_cplc (.cv n) (syn_c1c)) (syn_cnnc))
      (.classMem (syn_cplc (.cv n) (syn_c1c)) (syn_cvv)) p0083 p0084
  have p0087 :=
    @g_simpl
      (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg
          (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y))))))
      (.classMem (.cv n) (syn_cnnc))
  have p0089 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0)))
          (.neg (syn_wrex z X
              (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y))))))
        (.classMem (.cv n) (syn_cnnc)))
      (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg
          (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y))))))
      (.neg (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))))
      p0087 p0064
  have p0090 :=
    @g_syl
      (syn_wa (syn_wa
          (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg
              (syn_wrex z X
                (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y))))))
          (.classMem (.cv n) (syn_cnnc)))
        (.classMem (.cv n) (syn_cdif (syn_cvv) (syn_cima (syn_ckqrel (syn_clefin)) X))))
      (syn_wa (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0)))
          (.neg (syn_wrex z X
              (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y))))))
        (.classMem (.cv n) (syn_cnnc)))
      (.neg (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))))
      p0079 p0089
  have p0091 :=
    @g_simpl
      (syn_wa (syn_wa
          (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg
              (syn_wrex z X
                (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y))))))
          (.classMem (.cv n) (syn_cnnc)))
        (.classMem (.cv n) (syn_cdif (syn_cvv) (syn_cima (syn_ckqrel (syn_clefin)) X))))
      (.classMem (syn_cplc (.cv n) (syn_c1c)) (syn_cima (syn_ckqrel (syn_clefin)) X))
  have p0092 :=
    @g_simpr
      (syn_wa (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0)))
          (.neg (syn_wrex z X
              (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y))))))
        (.classMem (.cv n) (syn_cnnc)))
      (.classMem (.cv n) (syn_cdif (syn_cvv) (syn_cima (syn_ckqrel (syn_clefin)) X)))
  have p0094 := @g_eldif (.cv n) (syn_cvv) (syn_cima (syn_ckqrel (syn_clefin)) X)
  have p0095 :=
    @g_a1i
      (syn_wb (.classMem (.cv n) (syn_cdif (syn_cvv) (syn_cima (syn_ckqrel (syn_clefin)) X)))
        (syn_wa (.classMem (.cv n) (syn_cvv))
          (.neg (.classMem (.cv n) (syn_cima (syn_ckqrel (syn_clefin)) X)))))
      (syn_wa (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0)))
          (.neg (syn_wrex z X
              (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y))))))
        (.classMem (.cv n) (syn_cnnc)))
      p0094
  have p0096 :=
    @g_biimpd
      (syn_wa (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0)))
          (.neg (syn_wrex z X
              (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y))))))
        (.classMem (.cv n) (syn_cnnc)))
      (.classMem (.cv n) (syn_cdif (syn_cvv) (syn_cima (syn_ckqrel (syn_clefin)) X)))
      (syn_wa (.classMem (.cv n) (syn_cvv))
        (.neg (.classMem (.cv n) (syn_cima (syn_ckqrel (syn_clefin)) X))))
      p0095
  have p0097 :=
    @g_simpr (.classMem (.cv n) (syn_cvv))
      (.neg (.classMem (.cv n) (syn_cima (syn_ckqrel (syn_clefin)) X)))
  have p0098 :=
    @g_syl6
      (syn_wa (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0)))
          (.neg (syn_wrex z X
              (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y))))))
        (.classMem (.cv n) (syn_cnnc)))
      (.classMem (.cv n) (syn_cdif (syn_cvv) (syn_cima (syn_ckqrel (syn_clefin)) X)))
      (syn_wa (.classMem (.cv n) (syn_cvv))
        (.neg (.classMem (.cv n) (syn_cima (syn_ckqrel (syn_clefin)) X))))
      (.neg (.classMem (.cv n) (syn_cima (syn_ckqrel (syn_clefin)) X))) p0096 p0097
  have p0099 :=
    @g_syl
      (syn_wa (syn_wa
          (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg
              (syn_wrex z X
                (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y))))))
          (.classMem (.cv n) (syn_cnnc)))
        (.classMem (.cv n) (syn_cdif (syn_cvv) (syn_cima (syn_ckqrel (syn_clefin)) X))))
      (syn_wa (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0)))
          (.neg (syn_wrex z X
              (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y))))))
        (.classMem (.cv n) (syn_cnnc)))
      (.imp (.classMem (.cv n) (syn_cdif (syn_cvv) (syn_cima (syn_ckqrel (syn_clefin)) X)))
        (.neg (.classMem (.cv n) (syn_cima (syn_ckqrel (syn_clefin)) X))))
      p0079 p0098
  have p0100 :=
    @g_mpd
      (syn_wa (syn_wa
          (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg
              (syn_wrex z X
                (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y))))))
          (.classMem (.cv n) (syn_cnnc)))
        (.classMem (.cv n) (syn_cdif (syn_cvv) (syn_cima (syn_ckqrel (syn_clefin)) X))))
      (.classMem (.cv n) (syn_cdif (syn_cvv) (syn_cima (syn_ckqrel (syn_clefin)) X)))
      (.neg (.classMem (.cv n) (syn_cima (syn_ckqrel (syn_clefin)) X))) p0092 p0099
  have p0101 :=
    @g_elima u (.cv n) (syn_ckqrel (syn_clefin)) X dv_cache_0013 dv_cache_0005
      dv_cache_0003
  have p0102 :=
    @g_biimpri (.classMem (.cv n) (syn_cima (syn_ckqrel (syn_clefin)) X))
      (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) (.cv n))) p0101
  have p0103 :=
    @g_a1i
      (.imp (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) (.cv n)))
        (.classMem (.cv n) (syn_cima (syn_ckqrel (syn_clefin)) X)))
      (syn_wa (syn_wa
          (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg
              (syn_wrex z X
                (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y))))))
          (.classMem (.cv n) (syn_cnnc)))
        (.classMem (.cv n) (syn_cdif (syn_cvv) (syn_cima (syn_ckqrel (syn_clefin)) X))))
      p0102
  have p0104 :=
    @g_con3d
      (syn_wa (syn_wa
          (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg
              (syn_wrex z X
                (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y))))))
          (.classMem (.cv n) (syn_cnnc)))
        (.classMem (.cv n) (syn_cdif (syn_cvv) (syn_cima (syn_ckqrel (syn_clefin)) X))))
      (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) (.cv n)))
      (.classMem (.cv n) (syn_cima (syn_ckqrel (syn_clefin)) X)) p0103
  have p0105 :=
    @g_mpd
      (syn_wa (syn_wa
          (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg
              (syn_wrex z X
                (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y))))))
          (.classMem (.cv n) (syn_cnnc)))
        (.classMem (.cv n) (syn_cdif (syn_cvv) (syn_cima (syn_ckqrel (syn_clefin)) X))))
      (.neg (.classMem (.cv n) (syn_cima (syn_ckqrel (syn_clefin)) X)))
      (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) (.cv n)))) p0100
      p0104
  have p0106 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa
            (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg
                (syn_wrex z X
                  (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y))))))
            (.classMem (.cv n) (syn_cnnc)))
          (.classMem (.cv n) (syn_cdif (syn_cvv) (syn_cima (syn_ckqrel (syn_clefin)) X))))
        (.classMem (syn_cplc (.cv n) (syn_c1c)) (syn_cima (syn_ckqrel (syn_clefin)) X)))
      (syn_wa (syn_wa
          (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg
              (syn_wrex z X
                (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y))))))
          (.classMem (.cv n) (syn_cnnc)))
        (.classMem (.cv n) (syn_cdif (syn_cvv) (syn_cima (syn_ckqrel (syn_clefin)) X))))
      (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) (.cv n)))) p0091
      p0105
  have p0107 :=
    @g_simpr
      (syn_wa (syn_wa
          (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg
              (syn_wrex z X
                (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y))))))
          (.classMem (.cv n) (syn_cnnc)))
        (.classMem (.cv n) (syn_cdif (syn_cvv) (syn_cima (syn_ckqrel (syn_clefin)) X))))
      (.classMem (syn_cplc (.cv n) (syn_c1c)) (syn_cima (syn_ckqrel (syn_clefin)) X))
  have p0108 :=
    @g_elima t (syn_cplc (.cv n) (syn_c1c)) (syn_ckqrel (syn_clefin)) X dv_cache_0014
      dv_cache_0007 dv_cache_0001
  have p0109 :=
    @g_biimpi
      (.classMem (syn_cplc (.cv n) (syn_c1c)) (syn_cima (syn_ckqrel (syn_clefin)) X))
      (syn_wrex t X (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc (.cv n) (syn_c1c))))
      p0108
  have p0110 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa
            (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg
                (syn_wrex z X
                  (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y))))))
            (.classMem (.cv n) (syn_cnnc)))
          (.classMem (.cv n) (syn_cdif (syn_cvv) (syn_cima (syn_ckqrel (syn_clefin)) X))))
        (.classMem (syn_cplc (.cv n) (syn_c1c)) (syn_cima (syn_ckqrel (syn_clefin)) X)))
      (.classMem (syn_cplc (.cv n) (syn_c1c)) (syn_cima (syn_ckqrel (syn_clefin)) X))
      (syn_wrex t X (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc (.cv n) (syn_c1c))))
      p0107 p0109
  have p0111 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa
            (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg
                (syn_wrex z X
                  (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y))))))
            (.classMem (.cv n) (syn_cnnc)))
          (.classMem (.cv n) (syn_cdif (syn_cvv) (syn_cima (syn_ckqrel (syn_clefin)) X))))
        (.classMem (syn_cplc (.cv n) (syn_c1c)) (syn_cima (syn_ckqrel (syn_clefin)) X)))
      (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) (.cv n))))
      (syn_wrex t X (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc (.cv n) (syn_c1c))))
      p0106 p0110
  have p0121 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0)))
          (.neg (syn_wrex z X
              (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y))))))
        (.classMem (.cv n) (syn_cnnc)))
      (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg
          (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y))))))
      (syn_wss X (syn_cnnc)) p0087 p0010
  have p0122 :=
    @g_syl
      (syn_wa (syn_wa
          (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg
              (syn_wrex z X
                (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y))))))
          (.classMem (.cv n) (syn_cnnc)))
        (.classMem (.cv n) (syn_cdif (syn_cvv) (syn_cima (syn_ckqrel (syn_clefin)) X))))
      (syn_wa (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0)))
          (.neg (syn_wrex z X
              (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y))))))
        (.classMem (.cv n) (syn_cnnc)))
      (syn_wss X (syn_cnnc)) p0079 p0121
  have p0123 :=
    @g_jca
      (syn_wa (syn_wa
          (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg
              (syn_wrex z X
                (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y))))))
          (.classMem (.cv n) (syn_cnnc)))
        (.classMem (.cv n) (syn_cdif (syn_cvv) (syn_cima (syn_ckqrel (syn_clefin)) X))))
      (.classMem (.cv n) (syn_cnnc)) (syn_wss X (syn_cnnc)) p0081 p0122
  have p0124 :=
    @g_finleaststep y z u t (.cv n) X dv_cache_0015 dv_cache_0013 dv_cache_0016
      dv_cache_0017 dv_cache_0001 dv_cache_0003 dv_cache_0008 dv_cache_0009 dv_cache_0018
      dv_cache_0010 dv_cache_0011 dv_cache_0019 dv_cache_0020 dv_cache_0012
  have p0125 :=
    @g_syl
      (syn_wa (syn_wa
          (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg
              (syn_wrex z X
                (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y))))))
          (.classMem (.cv n) (syn_cnnc)))
        (.classMem (.cv n) (syn_cdif (syn_cvv) (syn_cima (syn_ckqrel (syn_clefin)) X))))
      (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wss X (syn_cnnc)))
      (.imp (syn_wa (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) (.cv n))))
          (syn_wrex t X
            (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc (.cv n) (syn_c1c)))))
        (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))))
      p0123 p0124
  have p0126 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa
            (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg
                (syn_wrex z X
                  (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y))))))
            (.classMem (.cv n) (syn_cnnc)))
          (.classMem (.cv n) (syn_cdif (syn_cvv) (syn_cima (syn_ckqrel (syn_clefin)) X))))
        (.classMem (syn_cplc (.cv n) (syn_c1c)) (syn_cima (syn_ckqrel (syn_clefin)) X)))
      (syn_wa (syn_wa
          (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg
              (syn_wrex z X
                (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y))))))
          (.classMem (.cv n) (syn_cnnc)))
        (.classMem (.cv n) (syn_cdif (syn_cvv) (syn_cima (syn_ckqrel (syn_clefin)) X))))
      (.imp (syn_wa (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) (.cv n))))
          (syn_wrex t X
            (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc (.cv n) (syn_c1c)))))
        (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))))
      p0091 p0125
  have p0127 :=
    @g_mpd
      (syn_wa (syn_wa (syn_wa
            (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg
                (syn_wrex z X
                  (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y))))))
            (.classMem (.cv n) (syn_cnnc)))
          (.classMem (.cv n) (syn_cdif (syn_cvv) (syn_cima (syn_ckqrel (syn_clefin)) X))))
        (.classMem (syn_cplc (.cv n) (syn_c1c)) (syn_cima (syn_ckqrel (syn_clefin)) X)))
      (syn_wa (.neg (syn_wrex u X (syn_wbr (.cv u) (syn_ckqrel (syn_clefin)) (.cv n))))
        (syn_wrex t X (syn_wbr (.cv t) (syn_ckqrel (syn_clefin)) (syn_cplc (.cv n) (syn_c1c)))))
      (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y))))
      p0111 p0126
  have p0128 :=
    @g_ex
      (syn_wa (syn_wa
          (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg
              (syn_wrex z X
                (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y))))))
          (.classMem (.cv n) (syn_cnnc)))
        (.classMem (.cv n) (syn_cdif (syn_cvv) (syn_cima (syn_ckqrel (syn_clefin)) X))))
      (.classMem (syn_cplc (.cv n) (syn_c1c)) (syn_cima (syn_ckqrel (syn_clefin)) X))
      (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y))))
      p0127
  have p0129 :=
    @g_con3d
      (syn_wa (syn_wa
          (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg
              (syn_wrex z X
                (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y))))))
          (.classMem (.cv n) (syn_cnnc)))
        (.classMem (.cv n) (syn_cdif (syn_cvv) (syn_cima (syn_ckqrel (syn_clefin)) X))))
      (.classMem (syn_cplc (.cv n) (syn_c1c)) (syn_cima (syn_ckqrel (syn_clefin)) X))
      (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y))))
      p0128
  have p0130 :=
    @g_mpd
      (syn_wa (syn_wa
          (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg
              (syn_wrex z X
                (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y))))))
          (.classMem (.cv n) (syn_cnnc)))
        (.classMem (.cv n) (syn_cdif (syn_cvv) (syn_cima (syn_ckqrel (syn_clefin)) X))))
      (.neg (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))))
      (.neg (.classMem (syn_cplc (.cv n) (syn_c1c)) (syn_cima (syn_ckqrel (syn_clefin)) X)))
      p0090 p0129
  have p0131 :=
    @g_jca
      (syn_wa (syn_wa
          (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg
              (syn_wrex z X
                (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y))))))
          (.classMem (.cv n) (syn_cnnc)))
        (.classMem (.cv n) (syn_cdif (syn_cvv) (syn_cima (syn_ckqrel (syn_clefin)) X))))
      (.classMem (syn_cplc (.cv n) (syn_c1c)) (syn_cvv))
      (.neg (.classMem (syn_cplc (.cv n) (syn_c1c)) (syn_cima (syn_ckqrel (syn_clefin)) X)))
      p0085 p0130
  have p0132 :=
    @g_eldif (syn_cplc (.cv n) (syn_c1c)) (syn_cvv) (syn_cima (syn_ckqrel (syn_clefin)) X)
  have p0133 :=
    @g_a1i
      (syn_wb (.classMem (syn_cplc (.cv n) (syn_c1c))
          (syn_cdif (syn_cvv) (syn_cima (syn_ckqrel (syn_clefin)) X)))
        (syn_wa (.classMem (syn_cplc (.cv n) (syn_c1c)) (syn_cvv)) (.neg
            (.classMem (syn_cplc (.cv n) (syn_c1c)) (syn_cima (syn_ckqrel (syn_clefin)) X)))))
      (syn_wa (syn_wa
          (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg
              (syn_wrex z X
                (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y))))))
          (.classMem (.cv n) (syn_cnnc)))
        (.classMem (.cv n) (syn_cdif (syn_cvv) (syn_cima (syn_ckqrel (syn_clefin)) X))))
      p0132
  have p0134 :=
    @g_mpbird
      (syn_wa (syn_wa
          (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg
              (syn_wrex z X
                (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y))))))
          (.classMem (.cv n) (syn_cnnc)))
        (.classMem (.cv n) (syn_cdif (syn_cvv) (syn_cima (syn_ckqrel (syn_clefin)) X))))
      (.classMem (syn_cplc (.cv n) (syn_c1c))
        (syn_cdif (syn_cvv) (syn_cima (syn_ckqrel (syn_clefin)) X)))
      (syn_wa (.classMem (syn_cplc (.cv n) (syn_c1c)) (syn_cvv)) (.neg
          (.classMem (syn_cplc (.cv n) (syn_c1c)) (syn_cima (syn_ckqrel (syn_clefin)) X))))
      p0131 p0133
  have p0135 :=
    @g_ex
      (syn_wa (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0)))
          (.neg (syn_wrex z X
              (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y))))))
        (.classMem (.cv n) (syn_cnnc)))
      (.classMem (.cv n) (syn_cdif (syn_cvv) (syn_cima (syn_ckqrel (syn_clefin)) X)))
      (.classMem (syn_cplc (.cv n) (syn_c1c))
        (syn_cdif (syn_cvv) (syn_cima (syn_ckqrel (syn_clefin)) X)))
      p0134
  have p0136 :=
    @g_ralrimiva
      (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg
          (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y))))))
      (.imp (.classMem (.cv n) (syn_cdif (syn_cvv) (syn_cima (syn_ckqrel (syn_clefin)) X)))
        (.classMem (syn_cplc (.cv n) (syn_c1c))
          (syn_cdif (syn_cvv) (syn_cima (syn_ckqrel (syn_clefin)) X))))
      n (syn_cnnc) dv_cache_0021 p0135
  have p0137 :=
    @g_n_3jca
      (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg
          (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y))))))
      (.classMem (syn_cdif (syn_cvv) (syn_cima (syn_ckqrel (syn_clefin)) X)) (syn_cvv))
      (.classMem (syn_c0c) (syn_cdif (syn_cvv) (syn_cima (syn_ckqrel (syn_clefin)) X)))
      (syn_wral n (syn_cnnc) (.imp
          (.classMem (.cv n) (syn_cdif (syn_cvv) (syn_cima (syn_ckqrel (syn_clefin)) X)))
          (.classMem (syn_cplc (.cv n) (syn_c1c))
            (syn_cdif (syn_cvv) (syn_cima (syn_ckqrel (syn_clefin)) X)))))
      p0061 p0078 p0136
  have p0138 :=
    @g_peano5 n (syn_cdif (syn_cvv) (syn_cima (syn_ckqrel (syn_clefin)) X)) (syn_cvv)
      dv_cache_0022
  have p0139 :=
    @g_syl
      (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg
          (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y))))))
      (syn_w3a (.classMem (syn_cdif (syn_cvv) (syn_cima (syn_ckqrel (syn_clefin)) X)) (syn_cvv))
        (.classMem (syn_c0c) (syn_cdif (syn_cvv) (syn_cima (syn_ckqrel (syn_clefin)) X)))
        (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n)
              (syn_cdif (syn_cvv) (syn_cima (syn_ckqrel (syn_clefin)) X)))
            (.classMem (syn_cplc (.cv n) (syn_c1c))
              (syn_cdif (syn_cvv) (syn_cima (syn_ckqrel (syn_clefin)) X))))))
      (syn_wss (syn_cnnc) (syn_cdif (syn_cvv) (syn_cima (syn_ckqrel (syn_clefin)) X)))
      p0137 p0138
  have p0140 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0)))
          (.neg (syn_wrex z X
              (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y))))))
        (.classMem (.cv t) X))
      (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg
          (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y))))))
      (syn_wss (syn_cnnc) (syn_cdif (syn_cvv) (syn_cima (syn_ckqrel (syn_clefin)) X)))
      p0007 p0139
  have p0148 :=
    @g_sseldd
      (syn_wa (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0)))
          (.neg (syn_wrex z X
              (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y))))))
        (.classMem (.cv t) X))
      (syn_cnnc) (syn_cdif (syn_cvv) (syn_cima (syn_ckqrel (syn_clefin)) X)) (.cv t) p0140
      p0013
  have p0149 := @g_eldif (.cv t) (syn_cvv) (syn_cima (syn_ckqrel (syn_clefin)) X)
  have p0150 :=
    @g_a1i
      (syn_wb (.classMem (.cv t) (syn_cdif (syn_cvv) (syn_cima (syn_ckqrel (syn_clefin)) X)))
        (syn_wa (.classMem (.cv t) (syn_cvv))
          (.neg (.classMem (.cv t) (syn_cima (syn_ckqrel (syn_clefin)) X)))))
      (syn_wa (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0)))
          (.neg (syn_wrex z X
              (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y))))))
        (.classMem (.cv t) X))
      p0149
  have p0151 :=
    @g_mpbid
      (syn_wa (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0)))
          (.neg (syn_wrex z X
              (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y))))))
        (.classMem (.cv t) X))
      (.classMem (.cv t) (syn_cdif (syn_cvv) (syn_cima (syn_ckqrel (syn_clefin)) X)))
      (syn_wa (.classMem (.cv t) (syn_cvv))
        (.neg (.classMem (.cv t) (syn_cima (syn_ckqrel (syn_clefin)) X))))
      p0148 p0150
  have p0152 :=
    @g_simpr (.classMem (.cv t) (syn_cvv))
      (.neg (.classMem (.cv t) (syn_cima (syn_ckqrel (syn_clefin)) X)))
  have p0153 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0)))
          (.neg (syn_wrex z X
              (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y))))))
        (.classMem (.cv t) X))
      (syn_wa (.classMem (.cv t) (syn_cvv))
        (.neg (.classMem (.cv t) (syn_cima (syn_ckqrel (syn_clefin)) X))))
      (.neg (.classMem (.cv t) (syn_cima (syn_ckqrel (syn_clefin)) X))) p0151 p0152
  have p0154 :=
    @g_pm2_21d
      (syn_wa (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0)))
          (.neg (syn_wrex z X
              (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y))))))
        (.classMem (.cv t) X))
      (.classMem (.cv t) (syn_cima (syn_ckqrel (syn_clefin)) X))
      (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y))))
      p0153
  have p0155 :=
    @g_mpd
      (syn_wa (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0)))
          (.neg (syn_wrex z X
              (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y))))))
        (.classMem (.cv t) X))
      (.classMem (.cv t) (syn_cima (syn_ckqrel (syn_clefin)) X))
      (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y))))
      p0046 p0154
  have p0156 :=
    @g_ex
      (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg
          (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y))))))
      (.classMem (.cv t) X)
      (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y))))
      p0155
  have p0157 :=
    @g_exlimdv
      (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg
          (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y))))))
      (.classMem (.cv t) X)
      (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))) t
      dv_cache_0023 dv_cache_0024 p0156
  have p0158 :=
    @g_mpd
      (syn_wa (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0))) (.neg
          (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y))))))
      (syn_wex t (.classMem (.cv t) X))
      (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y))))
      p0005 p0157
  have p0159 :=
    @g_ex (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0)))
      (.neg (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y)))))
      (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y))))
      p0158
  have p0160 :=
    @g_pm2_18d (syn_w3a (.classMem X V) (syn_wss X (syn_cnnc)) (syn_wne X (syn_c0)))
      (syn_wrex z X (syn_wral y X (syn_wbr (.cv z) (syn_ckqrel (syn_clefin)) (.cv y))))
      p0159
  exact p0160


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk014Compact001Part059`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_finlefr :
    Nominal.NPrf (syn_wbr (syn_ckqrel (syn_clefin)) (syn_cfound) (syn_cnnc)) :=
  by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let z : Var := freshVar proofSupport 2
  let w : Var := freshVar proofSupport 3
  let v : Var := freshVar proofSupport 4
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
  have fresh_w_ne_v : w ≠ v :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 3) (j := 4) (by decide)
  have fresh_v_ne_w : v ≠ w := Ne.symm fresh_w_ne_v
  have dv_cache_0001 : v ∉ ((syn_cvv)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0002 : w ∉ ((syn_cvv)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0003 : v ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_v_ne_x, not_false_eq_true])
  have dv_cache_0004 : w ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_w_ne_x, not_false_eq_true])
  have dv_cache_0005 : v ≠ w :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show v ≠ w from (by exact fresh_v_ne_w))
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
  have dv_cache_0007 : v ∉ ((syn_wbr (.cv w) (syn_ckqrel (syn_clefin)) (.cv y))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin, Finset.mem_union,
          Finset.mem_singleton, fresh_v_ne_w, fresh_v_ne_y, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0008 :
    y ∉
      ((syn_wa (syn_wa (syn_wa syn_wtru
              (syn_wa (syn_wss (.cv x) (syn_cnnc)) (syn_wne (.cv x) (syn_c0))))
            (.classMem (.cv w) (.cv x)))
          (syn_wral v (.cv x) (syn_wbr (.cv w) (syn_ckqrel (syn_clefin)) (.cv v))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wtru,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_y_ne_x, fresh_y_ne_w,
          fresh_y_ne_v, compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0009 : y ∉ ((Wff.classEq (.cv z) (.cv w))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_z, fresh_y_ne_w, or_false, not_false_eq_true])
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
  have dv_cache_0011 : z ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_z_ne_x, not_false_eq_true])
  have dv_cache_0012 :
    z ∉
      ((syn_wral y (.cv x) (.imp (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv w))
            (.classEq (.cv y) (.cv w))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_z_ne_x, fresh_z_ne_y, fresh_z_ne_w,
          compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0013 :
    w ∉
      ((syn_wrex z (.cv x) (syn_wral y (.cv x)
            (.imp (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv z))
              (.classEq (.cv y) (.cv z)))))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
          NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_w_ne_x, fresh_w_ne_y, fresh_w_ne_z,
          compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0014 :
    w ∉
      ((syn_wa syn_wtru (syn_wa (syn_wss (.cv x) (syn_cnnc)) (syn_wne (.cv x) (syn_c0))))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wtru,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union,
          Finset.mem_singleton, fresh_w_ne_x, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0015 : x ∉ ((syn_cnnc)).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0016 : y ∉ ((syn_cnnc)).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0017 : z ∉ ((syn_cnnc)).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0018 : x ∉ ((syn_ckqrel (syn_clefin))).fv :=
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
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0019 : y ∉ ((syn_ckqrel (syn_clefin))).fv :=
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
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0020 : z ∉ ((syn_ckqrel (syn_clefin))).fv :=
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
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0021 : x ∉ (syn_wtru).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wtru,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0022 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0023 : x ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact (show x ≠ z from (by exact fresh_x_ne_z))
  have dv_cache_0024 : y ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
    exact (show y ≠ z from (by exact fresh_y_ne_z))
  have p0000 := @g_tru
  have p0001 := @g_lefinex
  have p0002 := @g_kqrelex (syn_clefin) p0001
  have p0003 := @g_a1i (.classMem (syn_ckqrel (syn_clefin)) (syn_cvv)) syn_wtru p0002
  have p0004 := @g_nncex
  have p0005 := @g_a1i (.classMem (syn_cnnc) (syn_cvv)) syn_wtru p0004
  have p0006 := @g_vex x
  have p0007 :=
    @g_a1i (.classMem (.cv x) (syn_cvv))
      (syn_wa syn_wtru (syn_wa (syn_wss (.cv x) (syn_cnnc)) (syn_wne (.cv x) (syn_c0))))
      p0006
  have p0008 :=
    @g_simpr syn_wtru (syn_wa (syn_wss (.cv x) (syn_cnnc)) (syn_wne (.cv x) (syn_c0)))
  have p0009 := @g_simpl (syn_wss (.cv x) (syn_cnnc)) (syn_wne (.cv x) (syn_c0))
  have p0010 :=
    @g_syl
      (syn_wa syn_wtru (syn_wa (syn_wss (.cv x) (syn_cnnc)) (syn_wne (.cv x) (syn_c0))))
      (syn_wa (syn_wss (.cv x) (syn_cnnc)) (syn_wne (.cv x) (syn_c0)))
      (syn_wss (.cv x) (syn_cnnc)) p0008 p0009
  have p0011 :=
    @g_simpr syn_wtru (syn_wa (syn_wss (.cv x) (syn_cnnc)) (syn_wne (.cv x) (syn_c0)))
  have p0012 := @g_simpr (syn_wss (.cv x) (syn_cnnc)) (syn_wne (.cv x) (syn_c0))
  have p0013 :=
    @g_syl
      (syn_wa syn_wtru (syn_wa (syn_wss (.cv x) (syn_cnnc)) (syn_wne (.cv x) (syn_c0))))
      (syn_wa (syn_wss (.cv x) (syn_cnnc)) (syn_wne (.cv x) (syn_c0)))
      (syn_wne (.cv x) (syn_c0)) p0011 p0012
  have p0014 :=
    @g_n_3jca
      (syn_wa syn_wtru (syn_wa (syn_wss (.cv x) (syn_cnnc)) (syn_wne (.cv x) (syn_c0))))
      (.classMem (.cv x) (syn_cvv)) (syn_wss (.cv x) (syn_cnnc))
      (syn_wne (.cv x) (syn_c0)) p0007 p0010 p0013
  have p0015 :=
    @g_finleastnn v w (syn_cvv) (.cv x) dv_cache_0001 dv_cache_0002 dv_cache_0003
      dv_cache_0004 dv_cache_0005
  have p0016 :=
    @g_syl
      (syn_wa syn_wtru (syn_wa (syn_wss (.cv x) (syn_cnnc)) (syn_wne (.cv x) (syn_c0))))
      (syn_w3a (.classMem (.cv x) (syn_cvv)) (syn_wss (.cv x) (syn_cnnc))
        (syn_wne (.cv x) (syn_c0)))
      (syn_wrex w (.cv x)
        (syn_wral v (.cv x) (syn_wbr (.cv w) (syn_ckqrel (syn_clefin)) (.cv v))))
      p0014 p0015
  have p0017 :=
    @g_simpl
      (syn_wa (syn_wa syn_wtru (syn_wa (syn_wss (.cv x) (syn_cnnc)) (syn_wne (.cv x) (syn_c0))))
        (.classMem (.cv w) (.cv x)))
      (syn_wral v (.cv x) (syn_wbr (.cv w) (syn_ckqrel (syn_clefin)) (.cv v)))
  have p0018 :=
    @g_simpr
      (syn_wa syn_wtru (syn_wa (syn_wss (.cv x) (syn_cnnc)) (syn_wne (.cv x) (syn_c0))))
      (.classMem (.cv w) (.cv x))
  have p0019 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa syn_wtru
            (syn_wa (syn_wss (.cv x) (syn_cnnc)) (syn_wne (.cv x) (syn_c0))))
          (.classMem (.cv w) (.cv x)))
        (syn_wral v (.cv x) (syn_wbr (.cv w) (syn_ckqrel (syn_clefin)) (.cv v))))
      (syn_wa (syn_wa syn_wtru (syn_wa (syn_wss (.cv x) (syn_cnnc)) (syn_wne (.cv x) (syn_c0))))
        (.classMem (.cv w) (.cv x)))
      (.classMem (.cv w) (.cv x)) p0017 p0018
  have p0020 := @g_finleor
  have p0021 := @g_sopc (syn_cnnc) (syn_ckqrel (syn_clefin))
  have p0022 :=
    @g_biimpi (syn_wbr (syn_ckqrel (syn_clefin)) (syn_cstrict) (syn_cnnc))
      (syn_wa (syn_wbr (syn_ckqrel (syn_clefin)) (syn_cpartial) (syn_cnnc))
        (syn_wbr (syn_ckqrel (syn_clefin)) (syn_cconnex) (syn_cnnc)))
      p0021
  have p0023 := Nominal.mp p0020 p0022
  have p0024 :=
    @g_simpl (syn_wbr (syn_ckqrel (syn_clefin)) (syn_cpartial) (syn_cnnc))
      (syn_wbr (syn_ckqrel (syn_clefin)) (syn_cconnex) (syn_cnnc))
  have p0025 := Nominal.mp p0023 p0024
  have p0026 := @g_porta (syn_cnnc) (syn_ckqrel (syn_clefin))
  have p0027 :=
    @g_biimpi (syn_wbr (syn_ckqrel (syn_clefin)) (syn_cpartial) (syn_cnnc))
      (syn_w3a (syn_wbr (syn_ckqrel (syn_clefin)) (syn_cref) (syn_cnnc))
        (syn_wbr (syn_ckqrel (syn_clefin)) (syn_ctrans) (syn_cnnc))
        (syn_wbr (syn_ckqrel (syn_clefin)) (syn_cantisym) (syn_cnnc)))
      p0026
  have p0028 := Nominal.mp p0025 p0027
  have p0029 :=
    @g_simp3 (syn_wbr (syn_ckqrel (syn_clefin)) (syn_cref) (syn_cnnc))
      (syn_wbr (syn_ckqrel (syn_clefin)) (syn_ctrans) (syn_cnnc))
      (syn_wbr (syn_ckqrel (syn_clefin)) (syn_cantisym) (syn_cnnc))
  have p0030 := Nominal.mp p0028 p0029
  have p0031 :=
    @g_a1i (syn_wbr (syn_ckqrel (syn_clefin)) (syn_cantisym) (syn_cnnc))
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa syn_wtru
                (syn_wa (syn_wss (.cv x) (syn_cnnc)) (syn_wne (.cv x) (syn_c0))))
              (.classMem (.cv w) (.cv x)))
            (syn_wral v (.cv x) (syn_wbr (.cv w) (syn_ckqrel (syn_clefin)) (.cv v))))
          (.classMem (.cv y) (.cv x))) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv w)))
      p0030
  have p0032 :=
    @g_simpl
      (syn_wa (syn_wa (syn_wa (syn_wa syn_wtru
              (syn_wa (syn_wss (.cv x) (syn_cnnc)) (syn_wne (.cv x) (syn_c0))))
            (.classMem (.cv w) (.cv x)))
          (syn_wral v (.cv x) (syn_wbr (.cv w) (syn_ckqrel (syn_clefin)) (.cv v))))
        (.classMem (.cv y) (.cv x)))
      (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv w))
  have p0033 :=
    @g_simpl
      (syn_wa (syn_wa (syn_wa syn_wtru
            (syn_wa (syn_wss (.cv x) (syn_cnnc)) (syn_wne (.cv x) (syn_c0))))
          (.classMem (.cv w) (.cv x)))
        (syn_wral v (.cv x) (syn_wbr (.cv w) (syn_ckqrel (syn_clefin)) (.cv v))))
      (.classMem (.cv y) (.cv x))
  have p0034 :=
    @g_simpl
      (syn_wa (syn_wa syn_wtru (syn_wa (syn_wss (.cv x) (syn_cnnc)) (syn_wne (.cv x) (syn_c0))))
        (.classMem (.cv w) (.cv x)))
      (syn_wral v (.cv x) (syn_wbr (.cv w) (syn_ckqrel (syn_clefin)) (.cv v)))
  have p0035 :=
    @g_simpl
      (syn_wa syn_wtru (syn_wa (syn_wss (.cv x) (syn_cnnc)) (syn_wne (.cv x) (syn_c0))))
      (.classMem (.cv w) (.cv x))
  have p0036 :=
    @g_simpr syn_wtru (syn_wa (syn_wss (.cv x) (syn_cnnc)) (syn_wne (.cv x) (syn_c0)))
  have p0037 := @g_simpl (syn_wss (.cv x) (syn_cnnc)) (syn_wne (.cv x) (syn_c0))
  have p0038 :=
    @g_syl
      (syn_wa syn_wtru (syn_wa (syn_wss (.cv x) (syn_cnnc)) (syn_wne (.cv x) (syn_c0))))
      (syn_wa (syn_wss (.cv x) (syn_cnnc)) (syn_wne (.cv x) (syn_c0)))
      (syn_wss (.cv x) (syn_cnnc)) p0036 p0037
  have p0039 :=
    @g_syl
      (syn_wa (syn_wa syn_wtru (syn_wa (syn_wss (.cv x) (syn_cnnc)) (syn_wne (.cv x) (syn_c0))))
        (.classMem (.cv w) (.cv x)))
      (syn_wa syn_wtru (syn_wa (syn_wss (.cv x) (syn_cnnc)) (syn_wne (.cv x) (syn_c0))))
      (syn_wss (.cv x) (syn_cnnc)) p0035 p0038
  have p0040 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa syn_wtru
            (syn_wa (syn_wss (.cv x) (syn_cnnc)) (syn_wne (.cv x) (syn_c0))))
          (.classMem (.cv w) (.cv x)))
        (syn_wral v (.cv x) (syn_wbr (.cv w) (syn_ckqrel (syn_clefin)) (.cv v))))
      (syn_wa (syn_wa syn_wtru (syn_wa (syn_wss (.cv x) (syn_cnnc)) (syn_wne (.cv x) (syn_c0))))
        (.classMem (.cv w) (.cv x)))
      (syn_wss (.cv x) (syn_cnnc)) p0034 p0039
  have p0041 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa syn_wtru
              (syn_wa (syn_wss (.cv x) (syn_cnnc)) (syn_wne (.cv x) (syn_c0))))
            (.classMem (.cv w) (.cv x)))
          (syn_wral v (.cv x) (syn_wbr (.cv w) (syn_ckqrel (syn_clefin)) (.cv v))))
        (.classMem (.cv y) (.cv x)))
      (syn_wa (syn_wa (syn_wa syn_wtru
            (syn_wa (syn_wss (.cv x) (syn_cnnc)) (syn_wne (.cv x) (syn_c0))))
          (.classMem (.cv w) (.cv x)))
        (syn_wral v (.cv x) (syn_wbr (.cv w) (syn_ckqrel (syn_clefin)) (.cv v))))
      (syn_wss (.cv x) (syn_cnnc)) p0033 p0040
  have p0042 :=
    @g_simpr
      (syn_wa (syn_wa (syn_wa syn_wtru
            (syn_wa (syn_wss (.cv x) (syn_cnnc)) (syn_wne (.cv x) (syn_c0))))
          (.classMem (.cv w) (.cv x)))
        (syn_wral v (.cv x) (syn_wbr (.cv w) (syn_ckqrel (syn_clefin)) (.cv v))))
      (.classMem (.cv y) (.cv x))
  have p0043 :=
    @g_sseldd
      (syn_wa (syn_wa (syn_wa (syn_wa syn_wtru
              (syn_wa (syn_wss (.cv x) (syn_cnnc)) (syn_wne (.cv x) (syn_c0))))
            (.classMem (.cv w) (.cv x)))
          (syn_wral v (.cv x) (syn_wbr (.cv w) (syn_ckqrel (syn_clefin)) (.cv v))))
        (.classMem (.cv y) (.cv x)))
      (.cv x) (syn_cnnc) (.cv y) p0041 p0042
  have p0044 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa syn_wtru
                (syn_wa (syn_wss (.cv x) (syn_cnnc)) (syn_wne (.cv x) (syn_c0))))
              (.classMem (.cv w) (.cv x)))
            (syn_wral v (.cv x) (syn_wbr (.cv w) (syn_ckqrel (syn_clefin)) (.cv v))))
          (.classMem (.cv y) (.cv x))) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv w)))
      (syn_wa (syn_wa (syn_wa (syn_wa syn_wtru
              (syn_wa (syn_wss (.cv x) (syn_cnnc)) (syn_wne (.cv x) (syn_c0))))
            (.classMem (.cv w) (.cv x)))
          (syn_wral v (.cv x) (syn_wbr (.cv w) (syn_ckqrel (syn_clefin)) (.cv v))))
        (.classMem (.cv y) (.cv x)))
      (.classMem (.cv y) (syn_cnnc)) p0032 p0043
  have p0045 :=
    @g_simpl
      (syn_wa (syn_wa (syn_wa (syn_wa syn_wtru
              (syn_wa (syn_wss (.cv x) (syn_cnnc)) (syn_wne (.cv x) (syn_c0))))
            (.classMem (.cv w) (.cv x)))
          (syn_wral v (.cv x) (syn_wbr (.cv w) (syn_ckqrel (syn_clefin)) (.cv v))))
        (.classMem (.cv y) (.cv x)))
      (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv w))
  have p0046 :=
    @g_simpl
      (syn_wa (syn_wa (syn_wa syn_wtru
            (syn_wa (syn_wss (.cv x) (syn_cnnc)) (syn_wne (.cv x) (syn_c0))))
          (.classMem (.cv w) (.cv x)))
        (syn_wral v (.cv x) (syn_wbr (.cv w) (syn_ckqrel (syn_clefin)) (.cv v))))
      (.classMem (.cv y) (.cv x))
  have p0047 :=
    @g_simpl
      (syn_wa (syn_wa syn_wtru (syn_wa (syn_wss (.cv x) (syn_cnnc)) (syn_wne (.cv x) (syn_c0))))
        (.classMem (.cv w) (.cv x)))
      (syn_wral v (.cv x) (syn_wbr (.cv w) (syn_ckqrel (syn_clefin)) (.cv v)))
  have p0048 :=
    @g_simpl
      (syn_wa syn_wtru (syn_wa (syn_wss (.cv x) (syn_cnnc)) (syn_wne (.cv x) (syn_c0))))
      (.classMem (.cv w) (.cv x))
  have p0049 :=
    @g_simpr syn_wtru (syn_wa (syn_wss (.cv x) (syn_cnnc)) (syn_wne (.cv x) (syn_c0)))
  have p0050 := @g_simpl (syn_wss (.cv x) (syn_cnnc)) (syn_wne (.cv x) (syn_c0))
  have p0051 :=
    @g_syl
      (syn_wa syn_wtru (syn_wa (syn_wss (.cv x) (syn_cnnc)) (syn_wne (.cv x) (syn_c0))))
      (syn_wa (syn_wss (.cv x) (syn_cnnc)) (syn_wne (.cv x) (syn_c0)))
      (syn_wss (.cv x) (syn_cnnc)) p0049 p0050
  have p0052 :=
    @g_syl
      (syn_wa (syn_wa syn_wtru (syn_wa (syn_wss (.cv x) (syn_cnnc)) (syn_wne (.cv x) (syn_c0))))
        (.classMem (.cv w) (.cv x)))
      (syn_wa syn_wtru (syn_wa (syn_wss (.cv x) (syn_cnnc)) (syn_wne (.cv x) (syn_c0))))
      (syn_wss (.cv x) (syn_cnnc)) p0048 p0051
  have p0053 :=
    @g_simpr
      (syn_wa syn_wtru (syn_wa (syn_wss (.cv x) (syn_cnnc)) (syn_wne (.cv x) (syn_c0))))
      (.classMem (.cv w) (.cv x))
  have p0054 :=
    @g_sseldd
      (syn_wa (syn_wa syn_wtru (syn_wa (syn_wss (.cv x) (syn_cnnc)) (syn_wne (.cv x) (syn_c0))))
        (.classMem (.cv w) (.cv x)))
      (.cv x) (syn_cnnc) (.cv w) p0052 p0053
  have p0055 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa syn_wtru
            (syn_wa (syn_wss (.cv x) (syn_cnnc)) (syn_wne (.cv x) (syn_c0))))
          (.classMem (.cv w) (.cv x)))
        (syn_wral v (.cv x) (syn_wbr (.cv w) (syn_ckqrel (syn_clefin)) (.cv v))))
      (syn_wa (syn_wa syn_wtru (syn_wa (syn_wss (.cv x) (syn_cnnc)) (syn_wne (.cv x) (syn_c0))))
        (.classMem (.cv w) (.cv x)))
      (.classMem (.cv w) (syn_cnnc)) p0047 p0054
  have p0056 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa syn_wtru
              (syn_wa (syn_wss (.cv x) (syn_cnnc)) (syn_wne (.cv x) (syn_c0))))
            (.classMem (.cv w) (.cv x)))
          (syn_wral v (.cv x) (syn_wbr (.cv w) (syn_ckqrel (syn_clefin)) (.cv v))))
        (.classMem (.cv y) (.cv x)))
      (syn_wa (syn_wa (syn_wa syn_wtru
            (syn_wa (syn_wss (.cv x) (syn_cnnc)) (syn_wne (.cv x) (syn_c0))))
          (.classMem (.cv w) (.cv x)))
        (syn_wral v (.cv x) (syn_wbr (.cv w) (syn_ckqrel (syn_clefin)) (.cv v))))
      (.classMem (.cv w) (syn_cnnc)) p0046 p0055
  have p0057 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa syn_wtru
                (syn_wa (syn_wss (.cv x) (syn_cnnc)) (syn_wne (.cv x) (syn_c0))))
              (.classMem (.cv w) (.cv x)))
            (syn_wral v (.cv x) (syn_wbr (.cv w) (syn_ckqrel (syn_clefin)) (.cv v))))
          (.classMem (.cv y) (.cv x))) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv w)))
      (syn_wa (syn_wa (syn_wa (syn_wa syn_wtru
              (syn_wa (syn_wss (.cv x) (syn_cnnc)) (syn_wne (.cv x) (syn_c0))))
            (.classMem (.cv w) (.cv x)))
          (syn_wral v (.cv x) (syn_wbr (.cv w) (syn_ckqrel (syn_clefin)) (.cv v))))
        (.classMem (.cv y) (.cv x)))
      (.classMem (.cv w) (syn_cnnc)) p0045 p0056
  have p0058 :=
    @g_simpr
      (syn_wa (syn_wa (syn_wa (syn_wa syn_wtru
              (syn_wa (syn_wss (.cv x) (syn_cnnc)) (syn_wne (.cv x) (syn_c0))))
            (.classMem (.cv w) (.cv x)))
          (syn_wral v (.cv x) (syn_wbr (.cv w) (syn_ckqrel (syn_clefin)) (.cv v))))
        (.classMem (.cv y) (.cv x)))
      (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv w))
  have p0059 :=
    @g_simpl
      (syn_wa (syn_wa (syn_wa (syn_wa syn_wtru
              (syn_wa (syn_wss (.cv x) (syn_cnnc)) (syn_wne (.cv x) (syn_c0))))
            (.classMem (.cv w) (.cv x)))
          (syn_wral v (.cv x) (syn_wbr (.cv w) (syn_ckqrel (syn_clefin)) (.cv v))))
        (.classMem (.cv y) (.cv x)))
      (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv w))
  have p0060 :=
    @g_simpl
      (syn_wa (syn_wa (syn_wa syn_wtru
            (syn_wa (syn_wss (.cv x) (syn_cnnc)) (syn_wne (.cv x) (syn_c0))))
          (.classMem (.cv w) (.cv x)))
        (syn_wral v (.cv x) (syn_wbr (.cv w) (syn_ckqrel (syn_clefin)) (.cv v))))
      (.classMem (.cv y) (.cv x))
  have p0061 :=
    @g_simpr
      (syn_wa (syn_wa syn_wtru (syn_wa (syn_wss (.cv x) (syn_cnnc)) (syn_wne (.cv x) (syn_c0))))
        (.classMem (.cv w) (.cv x)))
      (syn_wral v (.cv x) (syn_wbr (.cv w) (syn_ckqrel (syn_clefin)) (.cv v)))
  have p0062 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa syn_wtru
              (syn_wa (syn_wss (.cv x) (syn_cnnc)) (syn_wne (.cv x) (syn_c0))))
            (.classMem (.cv w) (.cv x)))
          (syn_wral v (.cv x) (syn_wbr (.cv w) (syn_ckqrel (syn_clefin)) (.cv v))))
        (.classMem (.cv y) (.cv x)))
      (syn_wa (syn_wa (syn_wa syn_wtru
            (syn_wa (syn_wss (.cv x) (syn_cnnc)) (syn_wne (.cv x) (syn_c0))))
          (.classMem (.cv w) (.cv x)))
        (syn_wral v (.cv x) (syn_wbr (.cv w) (syn_ckqrel (syn_clefin)) (.cv v))))
      (syn_wral v (.cv x) (syn_wbr (.cv w) (syn_ckqrel (syn_clefin)) (.cv v))) p0060 p0061
  have p0063 :=
    @g_simpr
      (syn_wa (syn_wa (syn_wa syn_wtru
            (syn_wa (syn_wss (.cv x) (syn_cnnc)) (syn_wne (.cv x) (syn_c0))))
          (.classMem (.cv w) (.cv x)))
        (syn_wral v (.cv x) (syn_wbr (.cv w) (syn_ckqrel (syn_clefin)) (.cv v))))
      (.classMem (.cv y) (.cv x))
  have p0064 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (syn_wa syn_wtru
              (syn_wa (syn_wss (.cv x) (syn_cnnc)) (syn_wne (.cv x) (syn_c0))))
            (.classMem (.cv w) (.cv x)))
          (syn_wral v (.cv x) (syn_wbr (.cv w) (syn_ckqrel (syn_clefin)) (.cv v))))
        (.classMem (.cv y) (.cv x)))
      (syn_wral v (.cv x) (syn_wbr (.cv w) (syn_ckqrel (syn_clefin)) (.cv v)))
      (.classMem (.cv y) (.cv x)) p0062 p0063
  have p0065 := @g_breq2 (.cv v) (.cv y) (.cv w) (syn_ckqrel (syn_clefin))
  have p0066 :=
    @g_rspccva (syn_wbr (.cv w) (syn_ckqrel (syn_clefin)) (.cv v))
      (syn_wbr (.cv w) (syn_ckqrel (syn_clefin)) (.cv y)) v (.cv y) (.cv x) dv_cache_0006
      dv_cache_0003 dv_cache_0007 p0065
  have p0067 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa syn_wtru
              (syn_wa (syn_wss (.cv x) (syn_cnnc)) (syn_wne (.cv x) (syn_c0))))
            (.classMem (.cv w) (.cv x)))
          (syn_wral v (.cv x) (syn_wbr (.cv w) (syn_ckqrel (syn_clefin)) (.cv v))))
        (.classMem (.cv y) (.cv x)))
      (syn_wa (syn_wral v (.cv x) (syn_wbr (.cv w) (syn_ckqrel (syn_clefin)) (.cv v)))
        (.classMem (.cv y) (.cv x)))
      (syn_wbr (.cv w) (syn_ckqrel (syn_clefin)) (.cv y)) p0064 p0066
  have p0068 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa syn_wtru
                (syn_wa (syn_wss (.cv x) (syn_cnnc)) (syn_wne (.cv x) (syn_c0))))
              (.classMem (.cv w) (.cv x)))
            (syn_wral v (.cv x) (syn_wbr (.cv w) (syn_ckqrel (syn_clefin)) (.cv v))))
          (.classMem (.cv y) (.cv x))) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv w)))
      (syn_wa (syn_wa (syn_wa (syn_wa syn_wtru
              (syn_wa (syn_wss (.cv x) (syn_cnnc)) (syn_wne (.cv x) (syn_c0))))
            (.classMem (.cv w) (.cv x)))
          (syn_wral v (.cv x) (syn_wbr (.cv w) (syn_ckqrel (syn_clefin)) (.cv v))))
        (.classMem (.cv y) (.cv x)))
      (syn_wbr (.cv w) (syn_ckqrel (syn_clefin)) (.cv y)) p0059 p0067
  have p0069 :=
    @g_antid
      (syn_wa (syn_wa (syn_wa (syn_wa (syn_wa syn_wtru
                (syn_wa (syn_wss (.cv x) (syn_cnnc)) (syn_wne (.cv x) (syn_c0))))
              (.classMem (.cv w) (.cv x)))
            (syn_wral v (.cv x) (syn_wbr (.cv w) (syn_ckqrel (syn_clefin)) (.cv v))))
          (.classMem (.cv y) (.cv x))) (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv w)))
      (syn_cnnc) (syn_ckqrel (syn_clefin)) (.cv y) (.cv w) p0031 p0044 p0057 p0058 p0068
  have p0070 :=
    @g_ex
      (syn_wa (syn_wa (syn_wa (syn_wa syn_wtru
              (syn_wa (syn_wss (.cv x) (syn_cnnc)) (syn_wne (.cv x) (syn_c0))))
            (.classMem (.cv w) (.cv x)))
          (syn_wral v (.cv x) (syn_wbr (.cv w) (syn_ckqrel (syn_clefin)) (.cv v))))
        (.classMem (.cv y) (.cv x)))
      (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv w)) (.classEq (.cv y) (.cv w)) p0069
  have p0071 :=
    @g_ralrimiva
      (syn_wa (syn_wa (syn_wa syn_wtru
            (syn_wa (syn_wss (.cv x) (syn_cnnc)) (syn_wne (.cv x) (syn_c0))))
          (.classMem (.cv w) (.cv x)))
        (syn_wral v (.cv x) (syn_wbr (.cv w) (syn_ckqrel (syn_clefin)) (.cv v))))
      (.imp (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv w)) (.classEq (.cv y) (.cv w)))
      y (.cv x) dv_cache_0008 p0070
  have p0072 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa syn_wtru
            (syn_wa (syn_wss (.cv x) (syn_cnnc)) (syn_wne (.cv x) (syn_c0))))
          (.classMem (.cv w) (.cv x)))
        (syn_wral v (.cv x) (syn_wbr (.cv w) (syn_ckqrel (syn_clefin)) (.cv v))))
      (.classMem (.cv w) (.cv x))
      (syn_wral y (.cv x) (.imp (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv w))
          (.classEq (.cv y) (.cv w))))
      p0019 p0071
  have p0073 := @g_breq2 (.cv z) (.cv w) (.cv y) (syn_ckqrel (syn_clefin))
  have p0074 := @g_eqeq2 (.cv z) (.cv w) (.cv y)
  have p0075 :=
    @g_imbi12d (.classEq (.cv z) (.cv w))
      (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv z))
      (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv w)) (.classEq (.cv y) (.cv z))
      (.classEq (.cv y) (.cv w)) p0073 p0074
  have p0076 :=
    @g_ralbidv (.classEq (.cv z) (.cv w))
      (.imp (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv z)) (.classEq (.cv y) (.cv z)))
      (.imp (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv w)) (.classEq (.cv y) (.cv w)))
      y (.cv x) dv_cache_0009 p0075
  have p0077 :=
    @g_rspcev
      (syn_wral y (.cv x) (.imp (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv z))
          (.classEq (.cv y) (.cv z))))
      (syn_wral y (.cv x) (.imp (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv w))
          (.classEq (.cv y) (.cv w))))
      z (.cv w) (.cv x) dv_cache_0010 dv_cache_0011 dv_cache_0012 p0076
  have p0078 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa syn_wtru
            (syn_wa (syn_wss (.cv x) (syn_cnnc)) (syn_wne (.cv x) (syn_c0))))
          (.classMem (.cv w) (.cv x)))
        (syn_wral v (.cv x) (syn_wbr (.cv w) (syn_ckqrel (syn_clefin)) (.cv v))))
      (syn_wa (.classMem (.cv w) (.cv x)) (syn_wral y (.cv x)
          (.imp (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv w))
            (.classEq (.cv y) (.cv w)))))
      (syn_wrex z (.cv x) (syn_wral y (.cv x)
          (.imp (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv z))
            (.classEq (.cv y) (.cv z)))))
      p0072 p0077
  have p0079 :=
    @g_ex
      (syn_wa (syn_wa syn_wtru (syn_wa (syn_wss (.cv x) (syn_cnnc)) (syn_wne (.cv x) (syn_c0))))
        (.classMem (.cv w) (.cv x)))
      (syn_wral v (.cv x) (syn_wbr (.cv w) (syn_ckqrel (syn_clefin)) (.cv v)))
      (syn_wrex z (.cv x) (syn_wral y (.cv x)
          (.imp (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv z))
            (.classEq (.cv y) (.cv z)))))
      p0078
  have p0080 :=
    @g_rexlimdva
      (syn_wa syn_wtru (syn_wa (syn_wss (.cv x) (syn_cnnc)) (syn_wne (.cv x) (syn_c0))))
      (syn_wral v (.cv x) (syn_wbr (.cv w) (syn_ckqrel (syn_clefin)) (.cv v)))
      (syn_wrex z (.cv x) (syn_wral y (.cv x)
          (.imp (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv z))
            (.classEq (.cv y) (.cv z)))))
      w (.cv x) dv_cache_0013 dv_cache_0014 p0079
  have p0081 :=
    @g_mpd
      (syn_wa syn_wtru (syn_wa (syn_wss (.cv x) (syn_cnnc)) (syn_wne (.cv x) (syn_c0))))
      (syn_wrex w (.cv x)
        (syn_wral v (.cv x) (syn_wbr (.cv w) (syn_ckqrel (syn_clefin)) (.cv v))))
      (syn_wrex z (.cv x) (syn_wral y (.cv x)
          (.imp (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv z))
            (.classEq (.cv y) (.cv z)))))
      p0016 p0080
  have p0082_e02_recanon :
    Nominal.NPrf
      (.imp (syn_wa syn_wtru (syn_wa (syn_wss (.cv x) (syn_cnnc)) (syn_wne (.cv x) (syn_c0))))
        (syn_wrex z (.cv x) (syn_wral y (.cv x)
            (.imp (syn_wbr (.cv y) (syn_ckqrel (syn_clefin)) (.cv z)) (.objEq y z))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wa syn_wtru syn_wrex syn_wex syn_wral syn_wbr syn_cop syn_cun syn_cnin
          syn_wnan syn_ccompl syn_ckqrel syn_copab syn_copk syn_cpr syn_csn syn_clefin
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
      p0081
  have p0082 :=
    @g_frrd syn_wtru x y z (syn_cnnc) (syn_ckqrel (syn_clefin)) dv_cache_0015
      dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
      dv_cache_0022 dv_cache_0023 dv_cache_0024 p0003 p0005 p0082_e02_recanon
  have p0083 := Nominal.mp p0000 p0082
  exact p0083

@[expose]
noncomputable def g_finlewe :
    Nominal.NPrf (syn_wbr (syn_ckqrel (syn_clefin)) (syn_cwe) (syn_cnnc)) :=
  by
  have p0000 := @g_tru
  have p0001 := @g_finleor
  have p0002 :=
    @g_a1i (syn_wbr (syn_ckqrel (syn_clefin)) (syn_cstrict) (syn_cnnc)) syn_wtru p0001
  have p0003 := @g_finlefr
  have p0004 :=
    @g_a1i (syn_wbr (syn_ckqrel (syn_clefin)) (syn_cfound) (syn_cnnc)) syn_wtru p0003
  have p0005 :=
    @g_jca syn_wtru (syn_wbr (syn_ckqrel (syn_clefin)) (syn_cstrict) (syn_cnnc))
      (syn_wbr (syn_ckqrel (syn_clefin)) (syn_cfound) (syn_cnnc)) p0002 p0004
  have p0006 := Nominal.mp p0000 p0005
  have p0007 := (Nominal.classEqRefl (syn_cwe))
  have p0008 :=
    @g_breqi (syn_ckqrel (syn_clefin)) (syn_cnnc) (syn_cwe)
      (syn_cin (syn_cstrict) (syn_cfound)) p0007
  have p0009 := @g_brin (syn_ckqrel (syn_clefin)) (syn_cnnc) (syn_cstrict) (syn_cfound)
  have p0010 :=
    @g_bitri (syn_wbr (syn_ckqrel (syn_clefin)) (syn_cwe) (syn_cnnc))
      (syn_wbr (syn_ckqrel (syn_clefin)) (syn_cin (syn_cstrict) (syn_cfound)) (syn_cnnc))
      (syn_wa (syn_wbr (syn_ckqrel (syn_clefin)) (syn_cstrict) (syn_cnnc))
        (syn_wbr (syn_ckqrel (syn_clefin)) (syn_cfound) (syn_cnnc)))
      p0008 p0009
  have p0011 :=
    @g_mpbir (syn_wbr (syn_ckqrel (syn_clefin)) (syn_cwe) (syn_cnnc))
      (syn_wa (syn_wbr (syn_ckqrel (syn_clefin)) (syn_cstrict) (syn_cnnc))
        (syn_wbr (syn_ckqrel (syn_clefin)) (syn_cfound) (syn_cnnc)))
      p0006 p0010
  exact p0011

@[expose]
noncomputable def g_wpporbit0 (F : Class) (I : Class) (_dv_F_I : Disjoint F.fv I.fv) :
    Nominal.NPrf
      (.imp (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
          (syn_wss (syn_crn F) (syn_cdm F)))
        (.classEq (syn_cfv (syn_cfrec F I) (syn_c0c)) I)) :=
  by
  have p0000 := @g_eqid (syn_cfrec F I)
  have p0001 :=
    @g_simp1 (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
      (syn_wss (syn_crn F) (syn_cdm F))
  have p0002 :=
    @g_simp2 (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
      (syn_wss (syn_crn F) (syn_cdm F))
  have p0003 :=
    @g_simp3 (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
      (syn_wss (syn_crn F) (syn_cdm F))
  have p0004 :=
    @g_frec0
      (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
        (syn_wss (syn_crn F) (syn_cdm F)))
      (syn_cfrec F I) F I p0000 p0001 p0002 p0003
  exact p0004

@[expose]
noncomputable def g_wpporbitsuc (F : Class) (I : Class) (N : Class)
    (_dv_F_I : Disjoint F.fv I.fv) (_dv_F_N : Disjoint F.fv N.fv)
    (_dv_I_N : Disjoint I.fv N.fv) :
    Nominal.NPrf
      (.imp (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
            (syn_wss (syn_crn F) (syn_cdm F))) (.classMem N (syn_cnnc)))
        (.classEq (syn_cfv (syn_cfrec F I) (syn_cplc N (syn_c1c)))
          (syn_cfv F (syn_cfv (syn_cfrec F I) N)))) :=
  by
  have p0000 := @g_eqid (syn_cfrec F I)
  have p0001 :=
    @g_simpl
      (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
        (syn_wss (syn_crn F) (syn_cdm F)))
      (.classMem N (syn_cnnc))
  have p0002 :=
    @g_simp1 (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
      (syn_wss (syn_crn F) (syn_cdm F))
  have p0003 :=
    @g_syl
      (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
          (syn_wss (syn_crn F) (syn_cdm F))) (.classMem N (syn_cnnc)))
      (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
        (syn_wss (syn_crn F) (syn_cdm F)))
      (.classMem F (syn_cfuns)) p0001 p0002
  have p0005 :=
    @g_simp2 (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
      (syn_wss (syn_crn F) (syn_cdm F))
  have p0006 :=
    @g_syl
      (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
          (syn_wss (syn_crn F) (syn_cdm F))) (.classMem N (syn_cnnc)))
      (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
        (syn_wss (syn_crn F) (syn_cdm F)))
      (.classMem I (syn_cdm F)) p0001 p0005
  have p0008 :=
    @g_simp3 (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
      (syn_wss (syn_crn F) (syn_cdm F))
  have p0009 :=
    @g_syl
      (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
          (syn_wss (syn_crn F) (syn_cdm F))) (.classMem N (syn_cnnc)))
      (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
        (syn_wss (syn_crn F) (syn_cdm F)))
      (syn_wss (syn_crn F) (syn_cdm F)) p0001 p0008
  have p0010 :=
    @g_simpr
      (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
        (syn_wss (syn_crn F) (syn_cdm F)))
      (.classMem N (syn_cnnc))
  have p0011 :=
    @g_frecsuc
      (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
          (syn_wss (syn_crn F) (syn_cdm F))) (.classMem N (syn_cnnc)))
      (syn_cfrec F I) F I N p0000 p0003 p0006 p0009 p0010
  exact p0011

@[expose]
noncomputable def g_kqfinsucnle (A : Class) :
    Nominal.NPrf
      (.imp (.classMem A (syn_cnnc))
        (.neg (syn_wbr (syn_cplc A (syn_c1c)) (syn_ckqrel (syn_clefin)) A))) :=
  by
  have p0000 := @g_elex A (syn_cnnc)
  have p0001 := @g_id (.classMem A (syn_cnnc))
  have p0002 := @g_nulnnn
  have p0003 :=
    @g_a1i (.neg (.classMem (syn_c0) (syn_cnnc))) (.classMem A (syn_cnnc)) p0002
  have p0004 :=
    @g_jca (.classMem A (syn_cnnc)) (.classMem A (syn_cnnc))
      (.neg (.classMem (syn_c0) (syn_cnnc))) p0001 p0003
  have p0005 := @g_nelne2 A (syn_c0) (syn_cnnc)
  have p0006 :=
    @g_syl (.classMem A (syn_cnnc))
      (syn_wa (.classMem A (syn_cnnc)) (.neg (.classMem (syn_c0) (syn_cnnc))))
      (syn_wne A (syn_c0)) p0004 p0005
  have p0007 :=
    @g_jca (.classMem A (syn_cnnc)) (.classMem A (syn_cvv)) (syn_wne A (syn_c0)) p0000
      p0006
  have p0008 := @g_ltfinp1 A (syn_cvv)
  have p0009 :=
    @g_syl (.classMem A (syn_cnnc)) (syn_wa (.classMem A (syn_cvv)) (syn_wne A (syn_c0)))
      (.classMem (syn_copk A (syn_cplc A (syn_c1c))) (syn_cltfin)) p0007 p0008
  have p0010 := @g_notnot1 (.classMem (syn_copk A (syn_cplc A (syn_c1c))) (syn_cltfin))
  have p0011 :=
    @g_syl (.classMem A (syn_cnnc))
      (.classMem (syn_copk A (syn_cplc A (syn_c1c))) (syn_cltfin))
      (.neg (.neg (.classMem (syn_copk A (syn_cplc A (syn_c1c))) (syn_cltfin)))) p0009
      p0010
  have p0012 := @g_peano2 A
  have p0014 :=
    @g_jca (.classMem A (syn_cnnc)) (.classMem (syn_cplc A (syn_c1c)) (syn_cnnc))
      (.classMem A (syn_cnnc)) p0012 p0001
  have p0015 := @g_lenltfin (syn_cplc A (syn_c1c)) A
  have p0016 :=
    @g_syl (.classMem A (syn_cnnc))
      (syn_wa (.classMem (syn_cplc A (syn_c1c)) (syn_cnnc)) (.classMem A (syn_cnnc)))
      (syn_wb (.classMem (syn_copk (syn_cplc A (syn_c1c)) A) (syn_clefin))
        (.neg (.classMem (syn_copk A (syn_cplc A (syn_c1c))) (syn_cltfin))))
      p0014 p0015
  have p0017 :=
    @g_mtbird (.classMem A (syn_cnnc))
      (.classMem (syn_copk (syn_cplc A (syn_c1c)) A) (syn_clefin))
      (.neg (.classMem (syn_copk A (syn_cplc A (syn_c1c))) (syn_cltfin))) p0011 p0016
  have p0019 := @g_elex (syn_cplc A (syn_c1c)) (syn_cnnc)
  have p0020 :=
    @g_syl (.classMem A (syn_cnnc)) (.classMem (syn_cplc A (syn_c1c)) (syn_cnnc))
      (.classMem (syn_cplc A (syn_c1c)) (syn_cvv)) p0012 p0019
  have p0022 :=
    @g_jca (.classMem A (syn_cnnc)) (.classMem (syn_cplc A (syn_c1c)) (syn_cvv))
      (.classMem A (syn_cvv)) p0020 p0000
  have p0023 := @g_kqlefinbr (syn_cplc A (syn_c1c)) A (syn_cvv) (syn_cvv)
  have p0024 :=
    @g_syl (.classMem A (syn_cnnc))
      (syn_wa (.classMem (syn_cplc A (syn_c1c)) (syn_cvv)) (.classMem A (syn_cvv)))
      (syn_wb (syn_wbr (syn_cplc A (syn_c1c)) (syn_ckqrel (syn_clefin)) A)
        (.classMem (syn_copk (syn_cplc A (syn_c1c)) A) (syn_clefin)))
      p0022 p0023
  have p0025 :=
    @g_mtbird (.classMem A (syn_cnnc))
      (syn_wbr (syn_cplc A (syn_c1c)) (syn_ckqrel (syn_clefin)) A)
      (.classMem (syn_copk (syn_cplc A (syn_c1c)) A) (syn_clefin)) p0017 p0024
  exact p0025


end NFChoice.DirectNominalPrf.WPPReplay

end
