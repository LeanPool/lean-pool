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

/-- Checked nominal proof certificate identified upstream as `g_ltfinsucle`. -/
@[expose]
noncomputable def gLtfinsucle (A : Class) (B : Class) :
    Nominal.NPrf
      (.imp (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
        (.imp (.classMem (synCopk B (synCplc A (synC1c))) (synCltfin))
          (.classMem (synCopk B A) (synClefin)))) :=
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
  have dv_cache_0002 : p ∉ ((synCplc A (synC1c))).fv :=
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
  have dv_cache_0003 : p ∉ ((Wff.classMem (synCopk B A) (synClefin))).fv :=
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
      ((synWa (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
          (.classMem (synCopk B (synCplc A (synC1c))) (synCltfin)))).fv :=
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
    @gSimpr (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
      (.classMem (synCopk B (synCplc A (synC1c))) (synCltfin))
  have p0001 :=
    @gSimpl (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
      (.classMem (synCopk B (synCplc A (synC1c))) (synCltfin))
  have p0002 := @gSimpr (.classMem A (synCnnc)) (.classMem B (synCnnc))
  have p0003 :=
    @gSyl
      (synWa (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
        (.classMem (synCopk B (synCplc A (synC1c))) (synCltfin)))
      (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc))) (.classMem B (synCnnc))
      p0001 p0002
  have p0004 := @gElex B (synCnnc)
  have p0005 :=
    @gSyl
      (synWa (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
        (.classMem (synCopk B (synCplc A (synC1c))) (synCltfin)))
      (.classMem B (synCnnc)) (.classMem B (synCvv)) p0003 p0004
  have p0007 := @gSimpl (.classMem A (synCnnc)) (.classMem B (synCnnc))
  have p0008 :=
    @gSyl
      (synWa (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
        (.classMem (synCopk B (synCplc A (synC1c))) (synCltfin)))
      (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc))) (.classMem A (synCnnc))
      p0001 p0007
  have p0009 := @gPeano2 A
  have p0010 :=
    @gSyl
      (synWa (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
        (.classMem (synCopk B (synCplc A (synC1c))) (synCltfin)))
      (.classMem A (synCnnc)) (.classMem (synCplc A (synC1c)) (synCnnc)) p0008 p0009
  have p0011 := @gElex (synCplc A (synC1c)) (synCnnc)
  have p0012 :=
    @gSyl
      (synWa (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
        (.classMem (synCopk B (synCplc A (synC1c))) (synCltfin)))
      (.classMem (synCplc A (synC1c)) (synCnnc))
      (.classMem (synCplc A (synC1c)) (synCvv)) p0010 p0011
  have p0013 :=
    @gJca
      (synWa (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
        (.classMem (synCopk B (synCplc A (synC1c))) (synCltfin)))
      (.classMem B (synCvv)) (.classMem (synCplc A (synC1c)) (synCvv)) p0005 p0012
  have p0014 :=
    @gOpkltfing p B (synCplc A (synC1c)) (synCvv) (synCvv) dv_cache_0001
      dv_cache_0002
  have p0015 :=
    @gSyl
      (synWa (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
        (.classMem (synCopk B (synCplc A (synC1c))) (synCltfin)))
      (synWa (.classMem B (synCvv)) (.classMem (synCplc A (synC1c)) (synCvv)))
      (synWb (.classMem (synCopk B (synCplc A (synC1c))) (synCltfin))
        (synWa (synWne B (synC0)) (synWrex p (synCnnc)
            (.classEq (synCplc A (synC1c)) (synCplc (synCplc B (.cv p)) (synC1c))))))
      p0013 p0014
  have p0016 :=
    @gBiimpd
      (synWa (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
        (.classMem (synCopk B (synCplc A (synC1c))) (synCltfin)))
      (.classMem (synCopk B (synCplc A (synC1c))) (synCltfin))
      (synWa (synWne B (synC0)) (synWrex p (synCnnc)
          (.classEq (synCplc A (synC1c)) (synCplc (synCplc B (.cv p)) (synC1c)))))
      p0015
  have p0017 :=
    @gMpd
      (synWa (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
        (.classMem (synCopk B (synCplc A (synC1c))) (synCltfin)))
      (.classMem (synCopk B (synCplc A (synC1c))) (synCltfin))
      (synWa (synWne B (synC0)) (synWrex p (synCnnc)
          (.classEq (synCplc A (synC1c)) (synCplc (synCplc B (.cv p)) (synC1c)))))
      p0000 p0016
  have p0018 :=
    @gSimpr (synWne B (synC0))
      (synWrex p (synCnnc)
        (.classEq (synCplc A (synC1c)) (synCplc (synCplc B (.cv p)) (synC1c))))
  have p0019 :=
    @gSyl
      (synWa (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
        (.classMem (synCopk B (synCplc A (synC1c))) (synCltfin)))
      (synWa (synWne B (synC0)) (synWrex p (synCnnc)
          (.classEq (synCplc A (synC1c)) (synCplc (synCplc B (.cv p)) (synC1c)))))
      (synWrex p (synCnnc)
        (.classEq (synCplc A (synC1c)) (synCplc (synCplc B (.cv p)) (synC1c))))
      p0017 p0018
  have p0020 :=
    @gSimpl
      (synWa (synWa (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
          (.classMem (synCopk B (synCplc A (synC1c))) (synCltfin)))
        (.classMem (.cv p) (synCnnc)))
      (.classEq (synCplc A (synC1c)) (synCplc (synCplc B (.cv p)) (synC1c)))
  have p0021 :=
    @gSimpl
      (synWa (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
        (.classMem (synCopk B (synCplc A (synC1c))) (synCltfin)))
      (.classMem (.cv p) (synCnnc))
  have p0027 :=
    @gSyl
      (synWa (synWa (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
          (.classMem (synCopk B (synCplc A (synC1c))) (synCltfin)))
        (.classMem (.cv p) (synCnnc)))
      (synWa (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
        (.classMem (synCopk B (synCplc A (synC1c))) (synCltfin)))
      (.classMem B (synCvv)) p0021 p0005
  have p0028 :=
    @gSyl
      (synWa (synWa (synWa (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
            (.classMem (synCopk B (synCplc A (synC1c))) (synCltfin)))
          (.classMem (.cv p) (synCnnc)))
        (.classEq (synCplc A (synC1c)) (synCplc (synCplc B (.cv p)) (synC1c))))
      (synWa (synWa (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
          (.classMem (synCopk B (synCplc A (synC1c))) (synCltfin)))
        (.classMem (.cv p) (synCnnc)))
      (.classMem B (synCvv)) p0020 p0027
  have p0030 :=
    @gSimpr
      (synWa (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
        (.classMem (synCopk B (synCplc A (synC1c))) (synCltfin)))
      (.classMem (.cv p) (synCnnc))
  have p0031 :=
    @gSyl
      (synWa (synWa (synWa (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
            (.classMem (synCopk B (synCplc A (synC1c))) (synCltfin)))
          (.classMem (.cv p) (synCnnc)))
        (.classEq (synCplc A (synC1c)) (synCplc (synCplc B (.cv p)) (synC1c))))
      (synWa (synWa (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
          (.classMem (synCopk B (synCplc A (synC1c))) (synCltfin)))
        (.classMem (.cv p) (synCnnc)))
      (.classMem (.cv p) (synCnnc)) p0020 p0030
  have p0032 :=
    @gJca
      (synWa (synWa (synWa (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
            (.classMem (synCopk B (synCplc A (synC1c))) (synCltfin)))
          (.classMem (.cv p) (synCnnc)))
        (.classEq (synCplc A (synC1c)) (synCplc (synCplc B (.cv p)) (synC1c))))
      (.classMem B (synCvv)) (.classMem (.cv p) (synCnnc)) p0028 p0031
  have p0033 := @gLefinaddc B (.cv p) (synCvv)
  have p0034 :=
    @gSyl
      (synWa (synWa (synWa (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
            (.classMem (synCopk B (synCplc A (synC1c))) (synCltfin)))
          (.classMem (.cv p) (synCnnc)))
        (.classEq (synCplc A (synC1c)) (synCplc (synCplc B (.cv p)) (synC1c))))
      (synWa (.classMem B (synCvv)) (.classMem (.cv p) (synCnnc)))
      (.classMem (synCopk B (synCplc B (.cv p))) (synClefin)) p0032 p0033
  have p0035 :=
    @gSimpr
      (synWa (synWa (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
          (.classMem (synCopk B (synCplc A (synC1c))) (synCltfin)))
        (.classMem (.cv p) (synCnnc)))
      (.classEq (synCplc A (synC1c)) (synCplc (synCplc B (.cv p)) (synC1c)))
  have p0041 :=
    @gSyl
      (synWa (synWa (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
          (.classMem (synCopk B (synCplc A (synC1c))) (synCltfin)))
        (.classMem (.cv p) (synCnnc)))
      (synWa (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
        (.classMem (synCopk B (synCplc A (synC1c))) (synCltfin)))
      (.classMem A (synCnnc)) p0021 p0008
  have p0046 :=
    @gSyl
      (synWa (synWa (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
          (.classMem (synCopk B (synCplc A (synC1c))) (synCltfin)))
        (.classMem (.cv p) (synCnnc)))
      (synWa (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
        (.classMem (synCopk B (synCplc A (synC1c))) (synCltfin)))
      (.classMem B (synCnnc)) p0021 p0003
  have p0048 :=
    @gJca
      (synWa (synWa (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
          (.classMem (synCopk B (synCplc A (synC1c))) (synCltfin)))
        (.classMem (.cv p) (synCnnc)))
      (.classMem B (synCnnc)) (.classMem (.cv p) (synCnnc)) p0046 p0030
  have p0049 := @gNncaddccl B (.cv p)
  have p0050 :=
    @gSyl
      (synWa (synWa (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
          (.classMem (synCopk B (synCplc A (synC1c))) (synCltfin)))
        (.classMem (.cv p) (synCnnc)))
      (synWa (.classMem B (synCnnc)) (.classMem (.cv p) (synCnnc)))
      (.classMem (synCplc B (.cv p)) (synCnnc)) p0048 p0049
  have p0051 :=
    @gJca
      (synWa (synWa (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
          (.classMem (synCopk B (synCplc A (synC1c))) (synCltfin)))
        (.classMem (.cv p) (synCnnc)))
      (.classMem A (synCnnc)) (.classMem (synCplc B (.cv p)) (synCnnc)) p0041 p0050
  have p0052 := @gSuc11nnc A (synCplc B (.cv p))
  have p0053 :=
    @gSyl
      (synWa (synWa (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
          (.classMem (synCopk B (synCplc A (synC1c))) (synCltfin)))
        (.classMem (.cv p) (synCnnc)))
      (synWa (.classMem A (synCnnc)) (.classMem (synCplc B (.cv p)) (synCnnc)))
      (synWb (.classEq (synCplc A (synC1c)) (synCplc (synCplc B (.cv p)) (synC1c)))
        (.classEq A (synCplc B (.cv p))))
      p0051 p0052
  have p0054 :=
    @gBiimpd
      (synWa (synWa (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
          (.classMem (synCopk B (synCplc A (synC1c))) (synCltfin)))
        (.classMem (.cv p) (synCnnc)))
      (.classEq (synCplc A (synC1c)) (synCplc (synCplc B (.cv p)) (synC1c)))
      (.classEq A (synCplc B (.cv p))) p0053
  have p0055 :=
    @gSyl
      (synWa (synWa (synWa (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
            (.classMem (synCopk B (synCplc A (synC1c))) (synCltfin)))
          (.classMem (.cv p) (synCnnc)))
        (.classEq (synCplc A (synC1c)) (synCplc (synCplc B (.cv p)) (synC1c))))
      (synWa (synWa (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
          (.classMem (synCopk B (synCplc A (synC1c))) (synCltfin)))
        (.classMem (.cv p) (synCnnc)))
      (.imp (.classEq (synCplc A (synC1c)) (synCplc (synCplc B (.cv p)) (synC1c)))
        (.classEq A (synCplc B (.cv p))))
      p0020 p0054
  have p0056 :=
    @gMpd
      (synWa (synWa (synWa (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
            (.classMem (synCopk B (synCplc A (synC1c))) (synCltfin)))
          (.classMem (.cv p) (synCnnc)))
        (.classEq (synCplc A (synC1c)) (synCplc (synCplc B (.cv p)) (synC1c))))
      (.classEq (synCplc A (synC1c)) (synCplc (synCplc B (.cv p)) (synC1c)))
      (.classEq A (synCplc B (.cv p))) p0035 p0055
  have p0057 :=
    @gEqcomd
      (synWa (synWa (synWa (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
            (.classMem (synCopk B (synCplc A (synC1c))) (synCltfin)))
          (.classMem (.cv p) (synCnnc)))
        (.classEq (synCplc A (synC1c)) (synCplc (synCplc B (.cv p)) (synC1c))))
      A (synCplc B (.cv p)) p0056
  have p0058 :=
    @gOpkeq2d
      (synWa (synWa (synWa (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
            (.classMem (synCopk B (synCplc A (synC1c))) (synCltfin)))
          (.classMem (.cv p) (synCnnc)))
        (.classEq (synCplc A (synC1c)) (synCplc (synCplc B (.cv p)) (synC1c))))
      (synCplc B (.cv p)) A B p0057
  have p0059 :=
    @gEleq1d
      (synWa (synWa (synWa (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
            (.classMem (synCopk B (synCplc A (synC1c))) (synCltfin)))
          (.classMem (.cv p) (synCnnc)))
        (.classEq (synCplc A (synC1c)) (synCplc (synCplc B (.cv p)) (synC1c))))
      (synCopk B (synCplc B (.cv p))) (synCopk B A) (synClefin) p0058
  have p0060 :=
    @gMpbid
      (synWa (synWa (synWa (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
            (.classMem (synCopk B (synCplc A (synC1c))) (synCltfin)))
          (.classMem (.cv p) (synCnnc)))
        (.classEq (synCplc A (synC1c)) (synCplc (synCplc B (.cv p)) (synC1c))))
      (.classMem (synCopk B (synCplc B (.cv p))) (synClefin))
      (.classMem (synCopk B A) (synClefin)) p0034 p0059
  have p0061 :=
    @gEx
      (synWa (synWa (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
          (.classMem (synCopk B (synCplc A (synC1c))) (synCltfin)))
        (.classMem (.cv p) (synCnnc)))
      (.classEq (synCplc A (synC1c)) (synCplc (synCplc B (.cv p)) (synC1c)))
      (.classMem (synCopk B A) (synClefin)) p0060
  have p0062 :=
    @gRexlimdva
      (synWa (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
        (.classMem (synCopk B (synCplc A (synC1c))) (synCltfin)))
      (.classEq (synCplc A (synC1c)) (synCplc (synCplc B (.cv p)) (synC1c)))
      (.classMem (synCopk B A) (synClefin)) p (synCnnc) dv_cache_0003 dv_cache_0004
      p0061
  have p0063 :=
    @gMpd
      (synWa (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
        (.classMem (synCopk B (synCplc A (synC1c))) (synCltfin)))
      (synWrex p (synCnnc)
        (.classEq (synCplc A (synC1c)) (synCplc (synCplc B (.cv p)) (synC1c))))
      (.classMem (synCopk B A) (synClefin)) p0019 p0062
  have p0064 :=
    @gEx (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
      (.classMem (synCopk B (synCplc A (synC1c))) (synCltfin))
      (.classMem (synCopk B A) (synClefin)) p0063
  exact p0064

/-- Checked nominal proof certificate identified upstream as `g_lefinsucsplit`. -/
@[expose]
noncomputable def gLefinsucsplit (A : Class) (B : Class) :
    Nominal.NPrf
      (.imp (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
        (synWb (.classMem (synCopk B (synCplc A (synC1c))) (synClefin))
          (synWo (.classMem (synCopk B A) (synClefin))
            (.classEq B (synCplc A (synC1c)))))) :=
  by
  have p0000 :=
    @gSimpr (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
      (.classMem (synCopk B (synCplc A (synC1c))) (synClefin))
  have p0001 :=
    @gSimpl (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
      (.classMem (synCopk B (synCplc A (synC1c))) (synClefin))
  have p0002 := @gSimpr (.classMem A (synCnnc)) (.classMem B (synCnnc))
  have p0003 := @gElex B (synCnnc)
  have p0004 :=
    @gSyl (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
      (.classMem B (synCnnc)) (.classMem B (synCvv)) p0002 p0003
  have p0005 := @gSimpl (.classMem A (synCnnc)) (.classMem B (synCnnc))
  have p0006 := @gPeano2 A
  have p0007 :=
    @gSyl (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
      (.classMem A (synCnnc)) (.classMem (synCplc A (synC1c)) (synCnnc)) p0005 p0006
  have p0008 := @gElex (synCplc A (synC1c)) (synCnnc)
  have p0009 :=
    @gSyl (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
      (.classMem (synCplc A (synC1c)) (synCnnc))
      (.classMem (synCplc A (synC1c)) (synCvv)) p0007 p0008
  have p0010 :=
    @gJca (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
      (.classMem B (synCvv)) (.classMem (synCplc A (synC1c)) (synCvv)) p0004 p0009
  have p0011 := @gLefinlteqall B (synCplc A (synC1c)) (synCvv) (synCvv)
  have p0012 :=
    @gSyl (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
      (synWa (.classMem B (synCvv)) (.classMem (synCplc A (synC1c)) (synCvv)))
      (synWb (.classMem (synCopk B (synCplc A (synC1c))) (synClefin))
        (synWo (.classMem (synCopk B (synCplc A (synC1c))) (synCltfin))
          (.classEq B (synCplc A (synC1c)))))
      p0010 p0011
  have p0013 :=
    @gBiimpd (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
      (.classMem (synCopk B (synCplc A (synC1c))) (synClefin))
      (synWo (.classMem (synCopk B (synCplc A (synC1c))) (synCltfin))
        (.classEq B (synCplc A (synC1c))))
      p0012
  have p0014 :=
    @gSyl
      (synWa (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
        (.classMem (synCopk B (synCplc A (synC1c))) (synClefin)))
      (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
      (.imp (.classMem (synCopk B (synCplc A (synC1c))) (synClefin))
        (synWo (.classMem (synCopk B (synCplc A (synC1c))) (synCltfin))
          (.classEq B (synCplc A (synC1c)))))
      p0001 p0013
  have p0015 :=
    @gMpd
      (synWa (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
        (.classMem (synCopk B (synCplc A (synC1c))) (synClefin)))
      (.classMem (synCopk B (synCplc A (synC1c))) (synClefin))
      (synWo (.classMem (synCopk B (synCplc A (synC1c))) (synCltfin))
        (.classEq B (synCplc A (synC1c))))
      p0000 p0014
  have p0017 := @gLtfinsucle A B
  have p0018 :=
    @gOrc (.classMem (synCopk B A) (synClefin)) (.classEq B (synCplc A (synC1c)))
  have p0019 :=
    @gSyl6 (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
      (.classMem (synCopk B (synCplc A (synC1c))) (synCltfin))
      (.classMem (synCopk B A) (synClefin))
      (synWo (.classMem (synCopk B A) (synClefin)) (.classEq B (synCplc A (synC1c))))
      p0017 p0018
  have p0020 :=
    @gOlc (.classEq B (synCplc A (synC1c))) (.classMem (synCopk B A) (synClefin))
  have p0021 :=
    @gA1i
      (.imp (.classEq B (synCplc A (synC1c))) (synWo (.classMem (synCopk B A) (synClefin))
          (.classEq B (synCplc A (synC1c)))))
      (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc))) p0020
  have p0022 :=
    @gJaod (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
      (.classMem (synCopk B (synCplc A (synC1c))) (synCltfin))
      (synWo (.classMem (synCopk B A) (synClefin)) (.classEq B (synCplc A (synC1c))))
      (.classEq B (synCplc A (synC1c))) p0019 p0021
  have p0023 :=
    @gSyl
      (synWa (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
        (.classMem (synCopk B (synCplc A (synC1c))) (synClefin)))
      (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
      (.imp (synWo (.classMem (synCopk B (synCplc A (synC1c))) (synCltfin))
          (.classEq B (synCplc A (synC1c)))) (synWo (.classMem (synCopk B A) (synClefin))
          (.classEq B (synCplc A (synC1c)))))
      p0001 p0022
  have p0024 :=
    @gMpd
      (synWa (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
        (.classMem (synCopk B (synCplc A (synC1c))) (synClefin)))
      (synWo (.classMem (synCopk B (synCplc A (synC1c))) (synCltfin))
        (.classEq B (synCplc A (synC1c))))
      (synWo (.classMem (synCopk B A) (synClefin)) (.classEq B (synCplc A (synC1c))))
      p0015 p0023
  have p0025 :=
    @gEx (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
      (.classMem (synCopk B (synCplc A (synC1c))) (synClefin))
      (synWo (.classMem (synCopk B A) (synClefin)) (.classEq B (synCplc A (synC1c))))
      p0024
  have p0026 :=
    @gSimpr (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
      (.classMem (synCopk B A) (synClefin))
  have p0027 :=
    @gSimpl (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
      (.classMem (synCopk B A) (synClefin))
  have p0029 := @gElex A (synCnnc)
  have p0030 :=
    @gSyl (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
      (.classMem A (synCnnc)) (.classMem A (synCvv)) p0005 p0029
  have p0031 := @gN1cnnc
  have p0032 :=
    @gA1i (.classMem (synC1c) (synCnnc))
      (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc))) p0031
  have p0033 :=
    @gJca (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
      (.classMem A (synCvv)) (.classMem (synC1c) (synCnnc)) p0030 p0032
  have p0034 := @gLefinaddc A (synC1c) (synCvv)
  have p0035 :=
    @gSyl (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
      (synWa (.classMem A (synCvv)) (.classMem (synC1c) (synCnnc)))
      (.classMem (synCopk A (synCplc A (synC1c))) (synClefin)) p0033 p0034
  have p0036 :=
    @gSyl
      (synWa (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
        (.classMem (synCopk B A) (synClefin)))
      (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
      (.classMem (synCopk A (synCplc A (synC1c))) (synClefin)) p0027 p0035
  have p0037 :=
    @gJca
      (synWa (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
        (.classMem (synCopk B A) (synClefin)))
      (.classMem (synCopk B A) (synClefin))
      (.classMem (synCopk A (synCplc A (synC1c))) (synClefin)) p0026 p0036
  have p0044 :=
    @gN3jca (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
      (.classMem B (synCnnc)) (.classMem A (synCnnc))
      (.classMem (synCplc A (synC1c)) (synCnnc)) p0002 p0005 p0007
  have p0045 := @gLefintrnn B A (synCplc A (synC1c))
  have p0046 :=
    @gSyl (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
      (synW3a (.classMem B (synCnnc)) (.classMem A (synCnnc))
        (.classMem (synCplc A (synC1c)) (synCnnc)))
      (.imp (synWa (.classMem (synCopk B A) (synClefin))
          (.classMem (synCopk A (synCplc A (synC1c))) (synClefin)))
        (.classMem (synCopk B (synCplc A (synC1c))) (synClefin)))
      p0044 p0045
  have p0047 :=
    @gSyl
      (synWa (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
        (.classMem (synCopk B A) (synClefin)))
      (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
      (.imp (synWa (.classMem (synCopk B A) (synClefin))
          (.classMem (synCopk A (synCplc A (synC1c))) (synClefin)))
        (.classMem (synCopk B (synCplc A (synC1c))) (synClefin)))
      p0027 p0046
  have p0048 :=
    @gMpd
      (synWa (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
        (.classMem (synCopk B A) (synClefin)))
      (synWa (.classMem (synCopk B A) (synClefin))
        (.classMem (synCopk A (synCplc A (synC1c))) (synClefin)))
      (.classMem (synCopk B (synCplc A (synC1c))) (synClefin)) p0037 p0047
  have p0049 :=
    @gEx (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
      (.classMem (synCopk B A) (synClefin))
      (.classMem (synCopk B (synCplc A (synC1c))) (synClefin)) p0048
  have p0050 :=
    @gSimpl (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
      (.classEq B (synCplc A (synC1c)))
  have p0056 :=
    @gSyl
      (synWa (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
        (.classEq B (synCplc A (synC1c))))
      (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
      (.classMem (synCplc A (synC1c)) (synCvv)) p0050 p0009
  have p0057 := @gLefinrflx (synCplc A (synC1c)) (synCvv)
  have p0058 :=
    @gSyl
      (synWa (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
        (.classEq B (synCplc A (synC1c))))
      (.classMem (synCplc A (synC1c)) (synCvv))
      (.classMem (synCopk (synCplc A (synC1c)) (synCplc A (synC1c))) (synClefin))
      p0056 p0057
  have p0059 :=
    @gSimpr (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
      (.classEq B (synCplc A (synC1c)))
  have p0060 :=
    @gOpkeq1d
      (synWa (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
        (.classEq B (synCplc A (synC1c))))
      B (synCplc A (synC1c)) (synCplc A (synC1c)) p0059
  have p0061 :=
    @gEleq1d
      (synWa (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
        (.classEq B (synCplc A (synC1c))))
      (synCopk B (synCplc A (synC1c)))
      (synCopk (synCplc A (synC1c)) (synCplc A (synC1c))) (synClefin) p0060
  have p0062 :=
    @gMpbird
      (synWa (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
        (.classEq B (synCplc A (synC1c))))
      (.classMem (synCopk B (synCplc A (synC1c))) (synClefin))
      (.classMem (synCopk (synCplc A (synC1c)) (synCplc A (synC1c))) (synClefin))
      p0058 p0061
  have p0063 :=
    @gEx (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
      (.classEq B (synCplc A (synC1c)))
      (.classMem (synCopk B (synCplc A (synC1c))) (synClefin)) p0062
  have p0064 :=
    @gJaod (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
      (.classMem (synCopk B A) (synClefin))
      (.classMem (synCopk B (synCplc A (synC1c))) (synClefin))
      (.classEq B (synCplc A (synC1c))) p0049 p0063
  have p0065 :=
    @gImpbid (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
      (.classMem (synCopk B (synCplc A (synC1c))) (synClefin))
      (synWo (.classMem (synCopk B A) (synClefin)) (.classEq B (synCplc A (synC1c))))
      p0025 p0064
  exact p0065

/-- Checked nominal proof certificate identified upstream as `g_lefinzeroeq`. -/
@[expose]
noncomputable def gLefinzeroeq (B : Class) :
    Nominal.NPrf
      (.imp (.classMem B (synCnnc)) (synWb (.classMem (synCopk B (synC0c)) (synClefin))
          (.classEq B (synC0c)))) :=
  by
  have p0000 :=
    @gSimpr (.classMem B (synCnnc)) (.classMem (synCopk B (synC0c)) (synClefin))
  have p0001 :=
    @gSimpl (.classMem B (synCnnc)) (.classMem (synCopk B (synC0c)) (synClefin))
  have p0002 := @gId (.classMem B (synCnnc))
  have p0003 := @gN0cminle B
  have p0004 :=
    @gSyl (.classMem B (synCnnc)) (.classMem B (synCnnc))
      (.classMem (synCopk (synC0c) B) (synClefin)) p0002 p0003
  have p0005 :=
    @gSyl
      (synWa (.classMem B (synCnnc)) (.classMem (synCopk B (synC0c)) (synClefin)))
      (.classMem B (synCnnc)) (.classMem (synCopk (synC0c) B) (synClefin)) p0001 p0004
  have p0006 :=
    @gJca
      (synWa (.classMem B (synCnnc)) (.classMem (synCopk B (synC0c)) (synClefin)))
      (.classMem (synCopk B (synC0c)) (synClefin))
      (.classMem (synCopk (synC0c) B) (synClefin)) p0000 p0005
  have p0009 := @gPeano1
  have p0010 := @gA1i (.classMem (synC0c) (synCnnc)) (.classMem B (synCnnc)) p0009
  have p0011 :=
    @gJca (.classMem B (synCnnc)) (.classMem B (synCnnc))
      (.classMem (synC0c) (synCnnc)) p0002 p0010
  have p0012 :=
    @gSyl
      (synWa (.classMem B (synCnnc)) (.classMem (synCopk B (synC0c)) (synClefin)))
      (.classMem B (synCnnc))
      (synWa (.classMem B (synCnnc)) (.classMem (synC0c) (synCnnc))) p0001 p0011
  have p0013 := @gLefinantinn B (synC0c)
  have p0014 :=
    @gSyl
      (synWa (.classMem B (synCnnc)) (.classMem (synCopk B (synC0c)) (synClefin)))
      (synWa (.classMem B (synCnnc)) (.classMem (synC0c) (synCnnc)))
      (.imp (synWa (.classMem (synCopk B (synC0c)) (synClefin))
          (.classMem (synCopk (synC0c) B) (synClefin))) (.classEq B (synC0c)))
      p0012 p0013
  have p0015 :=
    @gMpd
      (synWa (.classMem B (synCnnc)) (.classMem (synCopk B (synC0c)) (synClefin)))
      (synWa (.classMem (synCopk B (synC0c)) (synClefin))
        (.classMem (synCopk (synC0c) B) (synClefin)))
      (.classEq B (synC0c)) p0006 p0014
  have p0016 :=
    @gEx (.classMem B (synCnnc)) (.classMem (synCopk B (synC0c)) (synClefin))
      (.classEq B (synC0c)) p0015
  have p0017 := @gN0cex
  have p0018 := @gLefinrflx (synC0c) (synCvv)
  have p0019 := Nominal.mp p0017 p0018
  have p0020 :=
    @gA1i (.classMem (synCopk (synC0c) (synC0c)) (synClefin))
      (synWa (.classMem B (synCnnc)) (.classEq B (synC0c))) p0019
  have p0021 := @gSimpr (.classMem B (synCnnc)) (.classEq B (synC0c))
  have p0022 :=
    @gOpkeq1d (synWa (.classMem B (synCnnc)) (.classEq B (synC0c))) B (synC0c)
      (synC0c) p0021
  have p0023 :=
    @gEleq1d (synWa (.classMem B (synCnnc)) (.classEq B (synC0c)))
      (synCopk B (synC0c)) (synCopk (synC0c) (synC0c)) (synClefin) p0022
  have p0024 :=
    @gMpbird (synWa (.classMem B (synCnnc)) (.classEq B (synC0c)))
      (.classMem (synCopk B (synC0c)) (synClefin))
      (.classMem (synCopk (synC0c) (synC0c)) (synClefin)) p0020 p0023
  have p0025 :=
    @gEx (.classMem B (synCnnc)) (.classEq B (synC0c))
      (.classMem (synCopk B (synC0c)) (synClefin)) p0024
  have p0026 :=
    @gImpbid (.classMem B (synCnnc)) (.classMem (synCopk B (synC0c)) (synClefin))
      (.classEq B (synC0c)) p0016 p0025
  exact p0026

/-- Checked nominal proof certificate identified upstream as `g_kqfinsucsplit`. -/
@[expose]
noncomputable def gKqfinsucsplit (A : Class) (B : Class) :
    Nominal.NPrf
      (.imp (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
        (synWb (synWbr B (synCkqrel (synClefin)) (synCplc A (synC1c)))
          (synWo (synWbr B (synCkqrel (synClefin)) A)
            (.classEq B (synCplc A (synC1c)))))) :=
  by
  have p0000 := @gSimpr (.classMem A (synCnnc)) (.classMem B (synCnnc))
  have p0001 := @gElex B (synCnnc)
  have p0002 :=
    @gSyl (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
      (.classMem B (synCnnc)) (.classMem B (synCvv)) p0000 p0001
  have p0003 := @gSimpl (.classMem A (synCnnc)) (.classMem B (synCnnc))
  have p0004 := @gPeano2 A
  have p0005 :=
    @gSyl (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
      (.classMem A (synCnnc)) (.classMem (synCplc A (synC1c)) (synCnnc)) p0003 p0004
  have p0006 := @gElex (synCplc A (synC1c)) (synCnnc)
  have p0007 :=
    @gSyl (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
      (.classMem (synCplc A (synC1c)) (synCnnc))
      (.classMem (synCplc A (synC1c)) (synCvv)) p0005 p0006
  have p0008 :=
    @gJca (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
      (.classMem B (synCvv)) (.classMem (synCplc A (synC1c)) (synCvv)) p0002 p0007
  have p0009 := @gKqlefinbr B (synCplc A (synC1c)) (synCvv) (synCvv)
  have p0010 :=
    @gSyl (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
      (synWa (.classMem B (synCvv)) (.classMem (synCplc A (synC1c)) (synCvv)))
      (synWb (synWbr B (synCkqrel (synClefin)) (synCplc A (synC1c)))
        (.classMem (synCopk B (synCplc A (synC1c))) (synClefin)))
      p0008 p0009
  have p0011 := @gLefinsucsplit A B
  have p0012 :=
    @gBitrd (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
      (synWbr B (synCkqrel (synClefin)) (synCplc A (synC1c)))
      (.classMem (synCopk B (synCplc A (synC1c))) (synClefin))
      (synWo (.classMem (synCopk B A) (synClefin)) (.classEq B (synCplc A (synC1c))))
      p0010 p0011
  have p0017 := @gElex A (synCnnc)
  have p0018 :=
    @gSyl (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
      (.classMem A (synCnnc)) (.classMem A (synCvv)) p0003 p0017
  have p0019 :=
    @gJca (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
      (.classMem B (synCvv)) (.classMem A (synCvv)) p0002 p0018
  have p0020 := @gKqlefinbr B A (synCvv) (synCvv)
  have p0021 :=
    @gSyl (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
      (synWa (.classMem B (synCvv)) (.classMem A (synCvv)))
      (synWb (synWbr B (synCkqrel (synClefin)) A) (.classMem (synCopk B A) (synClefin)))
      p0019 p0020
  have p0022 :=
    @gOrbi1d (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
      (synWbr B (synCkqrel (synClefin)) A) (.classMem (synCopk B A) (synClefin))
      (.classEq B (synCplc A (synC1c))) p0021
  have p0023 :=
    @gBitr4d (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
      (synWbr B (synCkqrel (synClefin)) (synCplc A (synC1c)))
      (synWo (.classMem (synCopk B A) (synClefin)) (.classEq B (synCplc A (synC1c))))
      (synWo (synWbr B (synCkqrel (synClefin)) A) (.classEq B (synCplc A (synC1c))))
      p0012 p0022
  exact p0023

/-- Checked nominal proof certificate identified upstream as `g_kqfinzeroeq`. -/
@[expose]
noncomputable def gKqfinzeroeq (B : Class) :
    Nominal.NPrf
      (.imp (.classMem B (synCnnc)) (synWb (synWbr B (synCkqrel (synClefin)) (synC0c))
          (.classEq B (synC0c)))) :=
  by
  have p0000 := @gId (.classMem B (synCnnc))
  have p0001 := @gElex B (synCnnc)
  have p0002 :=
    @gSyl (.classMem B (synCnnc)) (.classMem B (synCnnc)) (.classMem B (synCvv)) p0000
      p0001
  have p0003 := @gN0cex
  have p0004 := @gA1i (.classMem (synC0c) (synCvv)) (.classMem B (synCnnc)) p0003
  have p0005 :=
    @gJca (.classMem B (synCnnc)) (.classMem B (synCvv))
      (.classMem (synC0c) (synCvv)) p0002 p0004
  have p0006 := @gKqlefinbr B (synC0c) (synCvv) (synCvv)
  have p0007 :=
    @gSyl (.classMem B (synCnnc))
      (synWa (.classMem B (synCvv)) (.classMem (synC0c) (synCvv)))
      (synWb (synWbr B (synCkqrel (synClefin)) (synC0c))
        (.classMem (synCopk B (synC0c)) (synClefin)))
      p0005 p0006
  have p0008 := @gLefinzeroeq B
  have p0009 :=
    @gBitrd (.classMem B (synCnnc)) (synWbr B (synCkqrel (synClefin)) (synC0c))
      (.classMem (synCopk B (synC0c)) (synClefin)) (.classEq B (synC0c)) p0007 p0008
  exact p0009

/-- Checked nominal proof certificate identified upstream as `g_kqfin0min`. -/
@[expose]
noncomputable def gKqfin0min (B : Class) :
    Nominal.NPrf
      (.imp (.classMem B (synCnnc)) (synWbr (synC0c) (synCkqrel (synClefin)) B)) :=
  by
  have p0000 := @gN0cminle B
  have p0001 := @gN0cex
  have p0002 := @gA1i (.classMem (synC0c) (synCvv)) (.classMem B (synCnnc)) p0001
  have p0003 := @gId (.classMem B (synCnnc))
  have p0004 := @gElex B (synCnnc)
  have p0005 :=
    @gSyl (.classMem B (synCnnc)) (.classMem B (synCnnc)) (.classMem B (synCvv)) p0003
      p0004
  have p0006 :=
    @gJca (.classMem B (synCnnc)) (.classMem (synC0c) (synCvv))
      (.classMem B (synCvv)) p0002 p0005
  have p0007 := @gKqlefinbr (synC0c) B (synCvv) (synCvv)
  have p0008 :=
    @gSyl (.classMem B (synCnnc))
      (synWa (.classMem (synC0c) (synCvv)) (.classMem B (synCvv)))
      (synWb (synWbr (synC0c) (synCkqrel (synClefin)) B)
        (.classMem (synCopk (synC0c) B) (synClefin)))
      p0006 p0007
  have p0009 :=
    @gMpbird (.classMem B (synCnnc)) (synWbr (synC0c) (synCkqrel (synClefin)) B)
      (.classMem (synCopk (synC0c) B) (synClefin)) p0000 p0008
  exact p0009

/-- Checked nominal proof certificate identified upstream as `g_finleastbase`. -/
@[expose]
noncomputable def gFinleastbase (y : Var) (z : Var) (t : Var) (X : Class)
    (dv_X_t : t ∉ X.fv) (dv_X_y : y ∉ X.fv) (dv_X_z : z ∉ X.fv) (dv_t_y : t ≠ y)
    (dv_t_z : t ≠ z) (dv_y_z : y ≠ z) :
    Nominal.NPrf
      (.imp (synWss X (synCnnc))
        (.imp (synWrex t X (synWbr (.cv t) (synCkqrel (synClefin)) (synC0c))) (synWrex z X
            (synWral y X (synWbr (.cv z) (synCkqrel (synClefin)) (.cv y)))))) :=
  by
  have dv_cache_0001 :
    y ∉
      ((synWa (synWa (synWss X (synCnnc)) (.classMem (.cv t) X))
          (synWbr (.cv t) (synCkqrel (synClefin)) (synC0c)))).fv :=
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
  have dv_cache_0002 : y ∉ ((Wff.classEq (.cv z) (synC0c))).fv :=
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
  have dv_cache_0003 : z ∉ ((synC0c)).fv :=
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
    z ∉ ((synWral y X (synWbr (synC0c) (synCkqrel (synClefin)) (.cv y)))).fv :=
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
      ((synWrex z X (synWral y X (synWbr (.cv z) (synCkqrel (synClefin)) (.cv y))))).fv :=
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
  have dv_cache_0007 : t ∉ ((synWss X (synCnnc))).fv :=
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
    @gSimpl (synWa (synWss X (synCnnc)) (.classMem (.cv t) X))
      (synWbr (.cv t) (synCkqrel (synClefin)) (synC0c))
  have p0001 := @gSimpr (synWss X (synCnnc)) (.classMem (.cv t) X)
  have p0002 :=
    @gSyl
      (synWa (synWa (synWss X (synCnnc)) (.classMem (.cv t) X))
        (synWbr (.cv t) (synCkqrel (synClefin)) (synC0c)))
      (synWa (synWss X (synCnnc)) (.classMem (.cv t) X)) (.classMem (.cv t) X) p0000
      p0001
  have p0003 :=
    @gSimpr (synWa (synWss X (synCnnc)) (.classMem (.cv t) X))
      (synWbr (.cv t) (synCkqrel (synClefin)) (synC0c))
  have p0005 := @gSimpl (synWss X (synCnnc)) (.classMem (.cv t) X)
  have p0007 :=
    @gSseldd (synWa (synWss X (synCnnc)) (.classMem (.cv t) X)) X (synCnnc) (.cv t)
      p0005 p0001
  have p0008 := @gKqfinzeroeq (.cv t)
  have p0009 :=
    @gSyl (synWa (synWss X (synCnnc)) (.classMem (.cv t) X))
      (.classMem (.cv t) (synCnnc))
      (synWb (synWbr (.cv t) (synCkqrel (synClefin)) (synC0c))
        (.classEq (.cv t) (synC0c)))
      p0007 p0008
  have p0010 :=
    @gBiimpd (synWa (synWss X (synCnnc)) (.classMem (.cv t) X))
      (synWbr (.cv t) (synCkqrel (synClefin)) (synC0c)) (.classEq (.cv t) (synC0c))
      p0009
  have p0011 :=
    @gSyl
      (synWa (synWa (synWss X (synCnnc)) (.classMem (.cv t) X))
        (synWbr (.cv t) (synCkqrel (synClefin)) (synC0c)))
      (synWa (synWss X (synCnnc)) (.classMem (.cv t) X))
      (.imp (synWbr (.cv t) (synCkqrel (synClefin)) (synC0c)) (.classEq (.cv t) (synC0c)))
      p0000 p0010
  have p0012 :=
    @gMpd
      (synWa (synWa (synWss X (synCnnc)) (.classMem (.cv t) X))
        (synWbr (.cv t) (synCkqrel (synClefin)) (synC0c)))
      (synWbr (.cv t) (synCkqrel (synClefin)) (synC0c)) (.classEq (.cv t) (synC0c))
      p0003 p0011
  have p0013 :=
    @gEleq1d
      (synWa (synWa (synWss X (synCnnc)) (.classMem (.cv t) X))
        (synWbr (.cv t) (synCkqrel (synClefin)) (synC0c)))
      (.cv t) (synC0c) X p0012
  have p0014 :=
    @gMpbid
      (synWa (synWa (synWss X (synCnnc)) (.classMem (.cv t) X))
        (synWbr (.cv t) (synCkqrel (synClefin)) (synC0c)))
      (.classMem (.cv t) X) (.classMem (synC0c) X) p0002 p0013
  have p0015 :=
    @gSimpl
      (synWa (synWa (synWss X (synCnnc)) (.classMem (.cv t) X))
        (synWbr (.cv t) (synCkqrel (synClefin)) (synC0c)))
      (.classMem (.cv y) X)
  have p0017 :=
    @gSyl
      (synWa (synWa (synWa (synWss X (synCnnc)) (.classMem (.cv t) X))
          (synWbr (.cv t) (synCkqrel (synClefin)) (synC0c))) (.classMem (.cv y) X))
      (synWa (synWa (synWss X (synCnnc)) (.classMem (.cv t) X))
        (synWbr (.cv t) (synCkqrel (synClefin)) (synC0c)))
      (synWa (synWss X (synCnnc)) (.classMem (.cv t) X)) p0015 p0000
  have p0019 :=
    @gSyl
      (synWa (synWa (synWa (synWss X (synCnnc)) (.classMem (.cv t) X))
          (synWbr (.cv t) (synCkqrel (synClefin)) (synC0c))) (.classMem (.cv y) X))
      (synWa (synWss X (synCnnc)) (.classMem (.cv t) X)) (synWss X (synCnnc)) p0017
      p0005
  have p0020 :=
    @gSimpr
      (synWa (synWa (synWss X (synCnnc)) (.classMem (.cv t) X))
        (synWbr (.cv t) (synCkqrel (synClefin)) (synC0c)))
      (.classMem (.cv y) X)
  have p0021 :=
    @gSseldd
      (synWa (synWa (synWa (synWss X (synCnnc)) (.classMem (.cv t) X))
          (synWbr (.cv t) (synCkqrel (synClefin)) (synC0c))) (.classMem (.cv y) X))
      X (synCnnc) (.cv y) p0019 p0020
  have p0022 := @gKqfin0min (.cv y)
  have p0023 :=
    @gSyl
      (synWa (synWa (synWa (synWss X (synCnnc)) (.classMem (.cv t) X))
          (synWbr (.cv t) (synCkqrel (synClefin)) (synC0c))) (.classMem (.cv y) X))
      (.classMem (.cv y) (synCnnc)) (synWbr (synC0c) (synCkqrel (synClefin)) (.cv y))
      p0021 p0022
  have p0024 :=
    @gRalrimiva
      (synWa (synWa (synWss X (synCnnc)) (.classMem (.cv t) X))
        (synWbr (.cv t) (synCkqrel (synClefin)) (synC0c)))
      (synWbr (synC0c) (synCkqrel (synClefin)) (.cv y)) y X dv_cache_0001 p0023
  have p0025 :=
    @gJca
      (synWa (synWa (synWss X (synCnnc)) (.classMem (.cv t) X))
        (synWbr (.cv t) (synCkqrel (synClefin)) (synC0c)))
      (.classMem (synC0c) X)
      (synWral y X (synWbr (synC0c) (synCkqrel (synClefin)) (.cv y))) p0014 p0024
  have p0026 := @gBreq1 (.cv z) (synC0c) (.cv y) (synCkqrel (synClefin))
  have p0027 :=
    @gRalbidv (.classEq (.cv z) (synC0c))
      (synWbr (.cv z) (synCkqrel (synClefin)) (.cv y))
      (synWbr (synC0c) (synCkqrel (synClefin)) (.cv y)) y X dv_cache_0002 p0026
  have p0028 :=
    @gRspcev (synWral y X (synWbr (.cv z) (synCkqrel (synClefin)) (.cv y)))
      (synWral y X (synWbr (synC0c) (synCkqrel (synClefin)) (.cv y))) z (synC0c) X
      dv_cache_0003 dv_cache_0004 dv_cache_0005 p0027
  have p0029 :=
    @gSyl
      (synWa (synWa (synWss X (synCnnc)) (.classMem (.cv t) X))
        (synWbr (.cv t) (synCkqrel (synClefin)) (synC0c)))
      (synWa (.classMem (synC0c) X)
        (synWral y X (synWbr (synC0c) (synCkqrel (synClefin)) (.cv y))))
      (synWrex z X (synWral y X (synWbr (.cv z) (synCkqrel (synClefin)) (.cv y))))
      p0025 p0028
  have p0030 :=
    @gEx (synWa (synWss X (synCnnc)) (.classMem (.cv t) X))
      (synWbr (.cv t) (synCkqrel (synClefin)) (synC0c))
      (synWrex z X (synWral y X (synWbr (.cv z) (synCkqrel (synClefin)) (.cv y))))
      p0029
  have p0031 :=
    @gRexlimdva (synWss X (synCnnc))
      (synWbr (.cv t) (synCkqrel (synClefin)) (synC0c))
      (synWrex z X (synWral y X (synWbr (.cv z) (synCkqrel (synClefin)) (.cv y)))) t
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

/-- Checked nominal proof certificate identified upstream as `g_finleaststep`. -/
@[expose]
noncomputable def gFinleaststep (y : Var) (z : Var) (u : Var) (t : Var) (A : Class)
    (X : Class) (dv_A_t : t ∉ A.fv) (dv_A_u : u ∉ A.fv) (dv_A_y : y ∉ A.fv)
    (dv_A_z : z ∉ A.fv) (dv_X_t : t ∉ X.fv) (dv_X_u : u ∉ X.fv) (dv_X_y : y ∉ X.fv)
    (dv_X_z : z ∉ X.fv) (dv_t_u : t ≠ u) (dv_t_y : t ≠ y) (dv_t_z : t ≠ z)
    (dv_u_y : u ≠ y) (_dv_u_z : u ≠ z) (dv_y_z : y ≠ z) :
    Nominal.NPrf
      (.imp (synWa (.classMem A (synCnnc)) (synWss X (synCnnc))) (.imp
          (synWa (.neg (synWrex u X (synWbr (.cv u) (synCkqrel (synClefin)) A)))
            (synWrex t X (synWbr (.cv t) (synCkqrel (synClefin)) (synCplc A (synC1c)))))
          (synWrex z X (synWral y X (synWbr (.cv z) (synCkqrel (synClefin)) (.cv y)))))) :=
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
  have dv_cache_0003 : u ∉ ((synWbr (.cv t) (synCkqrel (synClefin)) A)).fv :=
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
  have dv_cache_0005 : u ∉ ((synWbr (.cv y) (synCkqrel (synClefin)) A)).fv :=
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
      ((synWa (synWa (synWa (synWa (.classMem A (synCnnc)) (synWss X (synCnnc)))
              (.neg (synWrex u X (synWbr (.cv u) (synCkqrel (synClefin)) A))))
            (.classMem (.cv t) X))
          (synWbr (.cv t) (synCkqrel (synClefin)) (synCplc A (synC1c))))).fv :=
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
  have dv_cache_0007 : y ∉ ((Wff.classEq (.cv z) (synCplc A (synC1c)))).fv :=
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
  have dv_cache_0008 : z ∉ ((synCplc A (synC1c))).fv :=
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
      ((synWral y X (synWbr (synCplc A (synC1c)) (synCkqrel (synClefin)) (.cv y)))).fv :=
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
      ((synWrex z X (synWral y X (synWbr (.cv z) (synCkqrel (synClefin)) (.cv y))))).fv :=
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
      ((synWa (synWa (.classMem A (synCnnc)) (synWss X (synCnnc)))
          (.neg (synWrex u X (synWbr (.cv u) (synCkqrel (synClefin)) A))))).fv :=
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
    @gSimpr (synWa (.classMem A (synCnnc)) (synWss X (synCnnc)))
      (synWa (.neg (synWrex u X (synWbr (.cv u) (synCkqrel (synClefin)) A)))
        (synWrex t X (synWbr (.cv t) (synCkqrel (synClefin)) (synCplc A (synC1c)))))
  have p0001 :=
    @gSimpr (.neg (synWrex u X (synWbr (.cv u) (synCkqrel (synClefin)) A)))
      (synWrex t X (synWbr (.cv t) (synCkqrel (synClefin)) (synCplc A (synC1c))))
  have p0002 :=
    @gSyl
      (synWa (synWa (.classMem A (synCnnc)) (synWss X (synCnnc)))
        (synWa (.neg (synWrex u X (synWbr (.cv u) (synCkqrel (synClefin)) A)))
          (synWrex t X (synWbr (.cv t) (synCkqrel (synClefin)) (synCplc A (synC1c))))))
      (synWa (.neg (synWrex u X (synWbr (.cv u) (synCkqrel (synClefin)) A)))
        (synWrex t X (synWbr (.cv t) (synCkqrel (synClefin)) (synCplc A (synC1c)))))
      (synWrex t X (synWbr (.cv t) (synCkqrel (synClefin)) (synCplc A (synC1c))))
      p0000 p0001
  have p0003 :=
    @gSimpl (synWa (.classMem A (synCnnc)) (synWss X (synCnnc)))
      (synWa (.neg (synWrex u X (synWbr (.cv u) (synCkqrel (synClefin)) A)))
        (synWrex t X (synWbr (.cv t) (synCkqrel (synClefin)) (synCplc A (synC1c)))))
  have p0005 :=
    @gSimpl (.neg (synWrex u X (synWbr (.cv u) (synCkqrel (synClefin)) A)))
      (synWrex t X (synWbr (.cv t) (synCkqrel (synClefin)) (synCplc A (synC1c))))
  have p0006 :=
    @gSyl
      (synWa (synWa (.classMem A (synCnnc)) (synWss X (synCnnc)))
        (synWa (.neg (synWrex u X (synWbr (.cv u) (synCkqrel (synClefin)) A)))
          (synWrex t X (synWbr (.cv t) (synCkqrel (synClefin)) (synCplc A (synC1c))))))
      (synWa (.neg (synWrex u X (synWbr (.cv u) (synCkqrel (synClefin)) A)))
        (synWrex t X (synWbr (.cv t) (synCkqrel (synClefin)) (synCplc A (synC1c)))))
      (.neg (synWrex u X (synWbr (.cv u) (synCkqrel (synClefin)) A))) p0000 p0005
  have p0007 :=
    @gJca
      (synWa (synWa (.classMem A (synCnnc)) (synWss X (synCnnc)))
        (synWa (.neg (synWrex u X (synWbr (.cv u) (synCkqrel (synClefin)) A)))
          (synWrex t X (synWbr (.cv t) (synCkqrel (synClefin)) (synCplc A (synC1c))))))
      (synWa (.classMem A (synCnnc)) (synWss X (synCnnc)))
      (.neg (synWrex u X (synWbr (.cv u) (synCkqrel (synClefin)) A))) p0003 p0006
  have p0008 :=
    @gSimpl
      (synWa (synWa (synWa (.classMem A (synCnnc)) (synWss X (synCnnc)))
          (.neg (synWrex u X (synWbr (.cv u) (synCkqrel (synClefin)) A))))
        (.classMem (.cv t) X))
      (synWbr (.cv t) (synCkqrel (synClefin)) (synCplc A (synC1c)))
  have p0009 :=
    @gSimpr
      (synWa (synWa (.classMem A (synCnnc)) (synWss X (synCnnc)))
        (.neg (synWrex u X (synWbr (.cv u) (synCkqrel (synClefin)) A))))
      (.classMem (.cv t) X)
  have p0010 :=
    @gSyl
      (synWa (synWa (synWa (synWa (.classMem A (synCnnc)) (synWss X (synCnnc)))
            (.neg (synWrex u X (synWbr (.cv u) (synCkqrel (synClefin)) A))))
          (.classMem (.cv t) X))
        (synWbr (.cv t) (synCkqrel (synClefin)) (synCplc A (synC1c))))
      (synWa (synWa (synWa (.classMem A (synCnnc)) (synWss X (synCnnc)))
          (.neg (synWrex u X (synWbr (.cv u) (synCkqrel (synClefin)) A))))
        (.classMem (.cv t) X))
      (.classMem (.cv t) X) p0008 p0009
  have p0011 :=
    @gSimpr
      (synWa (synWa (synWa (.classMem A (synCnnc)) (synWss X (synCnnc)))
          (.neg (synWrex u X (synWbr (.cv u) (synCkqrel (synClefin)) A))))
        (.classMem (.cv t) X))
      (synWbr (.cv t) (synCkqrel (synClefin)) (synCplc A (synC1c)))
  have p0013 :=
    @gSimpl
      (synWa (synWa (.classMem A (synCnnc)) (synWss X (synCnnc)))
        (.neg (synWrex u X (synWbr (.cv u) (synCkqrel (synClefin)) A))))
      (.classMem (.cv t) X)
  have p0014 :=
    @gSimpl (synWa (.classMem A (synCnnc)) (synWss X (synCnnc)))
      (.neg (synWrex u X (synWbr (.cv u) (synCkqrel (synClefin)) A)))
  have p0015 := @gSimpl (.classMem A (synCnnc)) (synWss X (synCnnc))
  have p0016 :=
    @gSyl
      (synWa (synWa (.classMem A (synCnnc)) (synWss X (synCnnc)))
        (.neg (synWrex u X (synWbr (.cv u) (synCkqrel (synClefin)) A))))
      (synWa (.classMem A (synCnnc)) (synWss X (synCnnc))) (.classMem A (synCnnc))
      p0014 p0015
  have p0017 :=
    @gSyl
      (synWa (synWa (synWa (.classMem A (synCnnc)) (synWss X (synCnnc)))
          (.neg (synWrex u X (synWbr (.cv u) (synCkqrel (synClefin)) A))))
        (.classMem (.cv t) X))
      (synWa (synWa (.classMem A (synCnnc)) (synWss X (synCnnc)))
        (.neg (synWrex u X (synWbr (.cv u) (synCkqrel (synClefin)) A))))
      (.classMem A (synCnnc)) p0013 p0016
  have p0020 := @gSimpr (.classMem A (synCnnc)) (synWss X (synCnnc))
  have p0021 :=
    @gSyl
      (synWa (synWa (.classMem A (synCnnc)) (synWss X (synCnnc)))
        (.neg (synWrex u X (synWbr (.cv u) (synCkqrel (synClefin)) A))))
      (synWa (.classMem A (synCnnc)) (synWss X (synCnnc))) (synWss X (synCnnc))
      p0014 p0020
  have p0022 :=
    @gSyl
      (synWa (synWa (synWa (.classMem A (synCnnc)) (synWss X (synCnnc)))
          (.neg (synWrex u X (synWbr (.cv u) (synCkqrel (synClefin)) A))))
        (.classMem (.cv t) X))
      (synWa (synWa (.classMem A (synCnnc)) (synWss X (synCnnc)))
        (.neg (synWrex u X (synWbr (.cv u) (synCkqrel (synClefin)) A))))
      (synWss X (synCnnc)) p0013 p0021
  have p0024 :=
    @gSseldd
      (synWa (synWa (synWa (.classMem A (synCnnc)) (synWss X (synCnnc)))
          (.neg (synWrex u X (synWbr (.cv u) (synCkqrel (synClefin)) A))))
        (.classMem (.cv t) X))
      X (synCnnc) (.cv t) p0022 p0009
  have p0025 :=
    @gJca
      (synWa (synWa (synWa (.classMem A (synCnnc)) (synWss X (synCnnc)))
          (.neg (synWrex u X (synWbr (.cv u) (synCkqrel (synClefin)) A))))
        (.classMem (.cv t) X))
      (.classMem A (synCnnc)) (.classMem (.cv t) (synCnnc)) p0017 p0024
  have p0026 := @gKqfinsucsplit A (.cv t)
  have p0027 :=
    @gSyl
      (synWa (synWa (synWa (.classMem A (synCnnc)) (synWss X (synCnnc)))
          (.neg (synWrex u X (synWbr (.cv u) (synCkqrel (synClefin)) A))))
        (.classMem (.cv t) X))
      (synWa (.classMem A (synCnnc)) (.classMem (.cv t) (synCnnc)))
      (synWb (synWbr (.cv t) (synCkqrel (synClefin)) (synCplc A (synC1c)))
        (synWo (synWbr (.cv t) (synCkqrel (synClefin)) A)
          (.classEq (.cv t) (synCplc A (synC1c)))))
      p0025 p0026
  have p0028 :=
    @gSyl
      (synWa (synWa (synWa (synWa (.classMem A (synCnnc)) (synWss X (synCnnc)))
            (.neg (synWrex u X (synWbr (.cv u) (synCkqrel (synClefin)) A))))
          (.classMem (.cv t) X))
        (synWbr (.cv t) (synCkqrel (synClefin)) (synCplc A (synC1c))))
      (synWa (synWa (synWa (.classMem A (synCnnc)) (synWss X (synCnnc)))
          (.neg (synWrex u X (synWbr (.cv u) (synCkqrel (synClefin)) A))))
        (.classMem (.cv t) X))
      (synWb (synWbr (.cv t) (synCkqrel (synClefin)) (synCplc A (synC1c)))
        (synWo (synWbr (.cv t) (synCkqrel (synClefin)) A)
          (.classEq (.cv t) (synCplc A (synC1c)))))
      p0008 p0027
  have p0029 :=
    @gBiimpd
      (synWa (synWa (synWa (synWa (.classMem A (synCnnc)) (synWss X (synCnnc)))
            (.neg (synWrex u X (synWbr (.cv u) (synCkqrel (synClefin)) A))))
          (.classMem (.cv t) X))
        (synWbr (.cv t) (synCkqrel (synClefin)) (synCplc A (synC1c))))
      (synWbr (.cv t) (synCkqrel (synClefin)) (synCplc A (synC1c)))
      (synWo (synWbr (.cv t) (synCkqrel (synClefin)) A)
        (.classEq (.cv t) (synCplc A (synC1c))))
      p0028
  have p0030 :=
    @gMpd
      (synWa (synWa (synWa (synWa (.classMem A (synCnnc)) (synWss X (synCnnc)))
            (.neg (synWrex u X (synWbr (.cv u) (synCkqrel (synClefin)) A))))
          (.classMem (.cv t) X))
        (synWbr (.cv t) (synCkqrel (synClefin)) (synCplc A (synC1c))))
      (synWbr (.cv t) (synCkqrel (synClefin)) (synCplc A (synC1c)))
      (synWo (synWbr (.cv t) (synCkqrel (synClefin)) A)
        (.classEq (.cv t) (synCplc A (synC1c))))
      p0011 p0029
  have p0033 :=
    @gSimpr (synWa (.classMem A (synCnnc)) (synWss X (synCnnc)))
      (.neg (synWrex u X (synWbr (.cv u) (synCkqrel (synClefin)) A)))
  have p0034 :=
    @gSyl
      (synWa (synWa (synWa (.classMem A (synCnnc)) (synWss X (synCnnc)))
          (.neg (synWrex u X (synWbr (.cv u) (synCkqrel (synClefin)) A))))
        (.classMem (.cv t) X))
      (synWa (synWa (.classMem A (synCnnc)) (synWss X (synCnnc)))
        (.neg (synWrex u X (synWbr (.cv u) (synCkqrel (synClefin)) A))))
      (.neg (synWrex u X (synWbr (.cv u) (synCkqrel (synClefin)) A))) p0013 p0033
  have p0035 :=
    @gSimpl
      (synWa (synWa (synWa (.classMem A (synCnnc)) (synWss X (synCnnc)))
          (.neg (synWrex u X (synWbr (.cv u) (synCkqrel (synClefin)) A))))
        (.classMem (.cv t) X))
      (synWbr (.cv t) (synCkqrel (synClefin)) A)
  have p0037 :=
    @gSyl
      (synWa (synWa (synWa (synWa (.classMem A (synCnnc)) (synWss X (synCnnc)))
            (.neg (synWrex u X (synWbr (.cv u) (synCkqrel (synClefin)) A))))
          (.classMem (.cv t) X)) (synWbr (.cv t) (synCkqrel (synClefin)) A))
      (synWa (synWa (synWa (.classMem A (synCnnc)) (synWss X (synCnnc)))
          (.neg (synWrex u X (synWbr (.cv u) (synCkqrel (synClefin)) A))))
        (.classMem (.cv t) X))
      (.classMem (.cv t) X) p0035 p0009
  have p0038 :=
    @gSimpr
      (synWa (synWa (synWa (.classMem A (synCnnc)) (synWss X (synCnnc)))
          (.neg (synWrex u X (synWbr (.cv u) (synCkqrel (synClefin)) A))))
        (.classMem (.cv t) X))
      (synWbr (.cv t) (synCkqrel (synClefin)) A)
  have p0039 :=
    @gJca
      (synWa (synWa (synWa (synWa (.classMem A (synCnnc)) (synWss X (synCnnc)))
            (.neg (synWrex u X (synWbr (.cv u) (synCkqrel (synClefin)) A))))
          (.classMem (.cv t) X)) (synWbr (.cv t) (synCkqrel (synClefin)) A))
      (.classMem (.cv t) X) (synWbr (.cv t) (synCkqrel (synClefin)) A) p0037 p0038
  have p0040 := @gBreq1 (.cv u) (.cv t) A (synCkqrel (synClefin))
  have p0041 :=
    @gRspcev (synWbr (.cv u) (synCkqrel (synClefin)) A)
      (synWbr (.cv t) (synCkqrel (synClefin)) A) u (.cv t) X dv_cache_0001
      dv_cache_0002 dv_cache_0003 p0040
  have p0042 :=
    @gSyl
      (synWa (synWa (synWa (synWa (.classMem A (synCnnc)) (synWss X (synCnnc)))
            (.neg (synWrex u X (synWbr (.cv u) (synCkqrel (synClefin)) A))))
          (.classMem (.cv t) X)) (synWbr (.cv t) (synCkqrel (synClefin)) A))
      (synWa (.classMem (.cv t) X) (synWbr (.cv t) (synCkqrel (synClefin)) A))
      (synWrex u X (synWbr (.cv u) (synCkqrel (synClefin)) A)) p0039 p0041
  have p0043 :=
    @gEx
      (synWa (synWa (synWa (.classMem A (synCnnc)) (synWss X (synCnnc)))
          (.neg (synWrex u X (synWbr (.cv u) (synCkqrel (synClefin)) A))))
        (.classMem (.cv t) X))
      (synWbr (.cv t) (synCkqrel (synClefin)) A)
      (synWrex u X (synWbr (.cv u) (synCkqrel (synClefin)) A)) p0042
  have p0044 :=
    @gCon3d
      (synWa (synWa (synWa (.classMem A (synCnnc)) (synWss X (synCnnc)))
          (.neg (synWrex u X (synWbr (.cv u) (synCkqrel (synClefin)) A))))
        (.classMem (.cv t) X))
      (synWbr (.cv t) (synCkqrel (synClefin)) A)
      (synWrex u X (synWbr (.cv u) (synCkqrel (synClefin)) A)) p0043
  have p0045 :=
    @gMpd
      (synWa (synWa (synWa (.classMem A (synCnnc)) (synWss X (synCnnc)))
          (.neg (synWrex u X (synWbr (.cv u) (synCkqrel (synClefin)) A))))
        (.classMem (.cv t) X))
      (.neg (synWrex u X (synWbr (.cv u) (synCkqrel (synClefin)) A)))
      (.neg (synWbr (.cv t) (synCkqrel (synClefin)) A)) p0034 p0044
  have p0046 :=
    @gSyl
      (synWa (synWa (synWa (synWa (.classMem A (synCnnc)) (synWss X (synCnnc)))
            (.neg (synWrex u X (synWbr (.cv u) (synCkqrel (synClefin)) A))))
          (.classMem (.cv t) X))
        (synWbr (.cv t) (synCkqrel (synClefin)) (synCplc A (synC1c))))
      (synWa (synWa (synWa (.classMem A (synCnnc)) (synWss X (synCnnc)))
          (.neg (synWrex u X (synWbr (.cv u) (synCkqrel (synClefin)) A))))
        (.classMem (.cv t) X))
      (.neg (synWbr (.cv t) (synCkqrel (synClefin)) A)) p0008 p0045
  have p0047 :=
    @gPm221d
      (synWa (synWa (synWa (synWa (.classMem A (synCnnc)) (synWss X (synCnnc)))
            (.neg (synWrex u X (synWbr (.cv u) (synCkqrel (synClefin)) A))))
          (.classMem (.cv t) X))
        (synWbr (.cv t) (synCkqrel (synClefin)) (synCplc A (synC1c))))
      (synWbr (.cv t) (synCkqrel (synClefin)) A)
      (.classEq (.cv t) (synCplc A (synC1c))) p0046
  have p0048 := @gId (.classEq (.cv t) (synCplc A (synC1c)))
  have p0049 :=
    @gA1i
      (.imp (.classEq (.cv t) (synCplc A (synC1c))) (.classEq (.cv t) (synCplc A (synC1c))))
      (synWa (synWa (synWa (synWa (.classMem A (synCnnc)) (synWss X (synCnnc)))
            (.neg (synWrex u X (synWbr (.cv u) (synCkqrel (synClefin)) A))))
          (.classMem (.cv t) X))
        (synWbr (.cv t) (synCkqrel (synClefin)) (synCplc A (synC1c))))
      p0048
  have p0050 :=
    @gJaod
      (synWa (synWa (synWa (synWa (.classMem A (synCnnc)) (synWss X (synCnnc)))
            (.neg (synWrex u X (synWbr (.cv u) (synCkqrel (synClefin)) A))))
          (.classMem (.cv t) X))
        (synWbr (.cv t) (synCkqrel (synClefin)) (synCplc A (synC1c))))
      (synWbr (.cv t) (synCkqrel (synClefin)) A)
      (.classEq (.cv t) (synCplc A (synC1c))) (.classEq (.cv t) (synCplc A (synC1c)))
      p0047 p0049
  have p0051 :=
    @gMpd
      (synWa (synWa (synWa (synWa (.classMem A (synCnnc)) (synWss X (synCnnc)))
            (.neg (synWrex u X (synWbr (.cv u) (synCkqrel (synClefin)) A))))
          (.classMem (.cv t) X))
        (synWbr (.cv t) (synCkqrel (synClefin)) (synCplc A (synC1c))))
      (synWo (synWbr (.cv t) (synCkqrel (synClefin)) A)
        (.classEq (.cv t) (synCplc A (synC1c))))
      (.classEq (.cv t) (synCplc A (synC1c))) p0030 p0050
  have p0052 :=
    @gEleq1d
      (synWa (synWa (synWa (synWa (.classMem A (synCnnc)) (synWss X (synCnnc)))
            (.neg (synWrex u X (synWbr (.cv u) (synCkqrel (synClefin)) A))))
          (.classMem (.cv t) X))
        (synWbr (.cv t) (synCkqrel (synClefin)) (synCplc A (synC1c))))
      (.cv t) (synCplc A (synC1c)) X p0051
  have p0053 :=
    @gMpbid
      (synWa (synWa (synWa (synWa (.classMem A (synCnnc)) (synWss X (synCnnc)))
            (.neg (synWrex u X (synWbr (.cv u) (synCkqrel (synClefin)) A))))
          (.classMem (.cv t) X))
        (synWbr (.cv t) (synCkqrel (synClefin)) (synCplc A (synC1c))))
      (.classMem (.cv t) X) (.classMem (synCplc A (synC1c)) X) p0010 p0052
  have p0054 := @gFinleor
  have p0055 := @gSopc (synCnnc) (synCkqrel (synClefin))
  have p0056 :=
    @gBiimpi (synWbr (synCkqrel (synClefin)) (synCstrict) (synCnnc))
      (synWa (synWbr (synCkqrel (synClefin)) (synCpartial) (synCnnc))
        (synWbr (synCkqrel (synClefin)) (synCconnex) (synCnnc)))
      p0055
  have p0057 := Nominal.mp p0054 p0056
  have p0058 :=
    @gSimpr (synWbr (synCkqrel (synClefin)) (synCpartial) (synCnnc))
      (synWbr (synCkqrel (synClefin)) (synCconnex) (synCnnc))
  have p0059 := Nominal.mp p0057 p0058
  have p0060 :=
    @gA1i (synWbr (synCkqrel (synClefin)) (synCconnex) (synCnnc))
      (synWa (synWa (synWa (synWa (synWa (.classMem A (synCnnc)) (synWss X (synCnnc)))
              (.neg (synWrex u X (synWbr (.cv u) (synCkqrel (synClefin)) A))))
            (.classMem (.cv t) X))
          (synWbr (.cv t) (synCkqrel (synClefin)) (synCplc A (synC1c))))
        (.classMem (.cv y) X))
      p0059
  have p0061 :=
    @gSimpl
      (synWa (synWa (synWa (synWa (.classMem A (synCnnc)) (synWss X (synCnnc)))
            (.neg (synWrex u X (synWbr (.cv u) (synCkqrel (synClefin)) A))))
          (.classMem (.cv t) X))
        (synWbr (.cv t) (synCkqrel (synClefin)) (synCplc A (synC1c))))
      (.classMem (.cv y) X)
  have p0063 :=
    @gSyl
      (synWa (synWa (synWa (synWa (synWa (.classMem A (synCnnc)) (synWss X (synCnnc)))
              (.neg (synWrex u X (synWbr (.cv u) (synCkqrel (synClefin)) A))))
            (.classMem (.cv t) X))
          (synWbr (.cv t) (synCkqrel (synClefin)) (synCplc A (synC1c))))
        (.classMem (.cv y) X))
      (synWa (synWa (synWa (synWa (.classMem A (synCnnc)) (synWss X (synCnnc)))
            (.neg (synWrex u X (synWbr (.cv u) (synCkqrel (synClefin)) A))))
          (.classMem (.cv t) X))
        (synWbr (.cv t) (synCkqrel (synClefin)) (synCplc A (synC1c))))
      (synWa (synWa (synWa (.classMem A (synCnnc)) (synWss X (synCnnc)))
          (.neg (synWrex u X (synWbr (.cv u) (synCkqrel (synClefin)) A))))
        (.classMem (.cv t) X))
      p0061 p0008
  have p0069 :=
    @gSyl
      (synWa (synWa (synWa (synWa (synWa (.classMem A (synCnnc)) (synWss X (synCnnc)))
              (.neg (synWrex u X (synWbr (.cv u) (synCkqrel (synClefin)) A))))
            (.classMem (.cv t) X))
          (synWbr (.cv t) (synCkqrel (synClefin)) (synCplc A (synC1c))))
        (.classMem (.cv y) X))
      (synWa (synWa (synWa (.classMem A (synCnnc)) (synWss X (synCnnc)))
          (.neg (synWrex u X (synWbr (.cv u) (synCkqrel (synClefin)) A))))
        (.classMem (.cv t) X))
      (.classMem A (synCnnc)) p0063 p0017
  have p0070 := @gPeano2 A
  have p0071 :=
    @gSyl
      (synWa (synWa (synWa (synWa (synWa (.classMem A (synCnnc)) (synWss X (synCnnc)))
              (.neg (synWrex u X (synWbr (.cv u) (synCkqrel (synClefin)) A))))
            (.classMem (.cv t) X))
          (synWbr (.cv t) (synCkqrel (synClefin)) (synCplc A (synC1c))))
        (.classMem (.cv y) X))
      (.classMem A (synCnnc)) (.classMem (synCplc A (synC1c)) (synCnnc)) p0069 p0070
  have p0080 :=
    @gSyl
      (synWa (synWa (synWa (synWa (synWa (.classMem A (synCnnc)) (synWss X (synCnnc)))
              (.neg (synWrex u X (synWbr (.cv u) (synCkqrel (synClefin)) A))))
            (.classMem (.cv t) X))
          (synWbr (.cv t) (synCkqrel (synClefin)) (synCplc A (synC1c))))
        (.classMem (.cv y) X))
      (synWa (synWa (synWa (.classMem A (synCnnc)) (synWss X (synCnnc)))
          (.neg (synWrex u X (synWbr (.cv u) (synCkqrel (synClefin)) A))))
        (.classMem (.cv t) X))
      (synWss X (synCnnc)) p0063 p0022
  have p0081 :=
    @gSimpr
      (synWa (synWa (synWa (synWa (.classMem A (synCnnc)) (synWss X (synCnnc)))
            (.neg (synWrex u X (synWbr (.cv u) (synCkqrel (synClefin)) A))))
          (.classMem (.cv t) X))
        (synWbr (.cv t) (synCkqrel (synClefin)) (synCplc A (synC1c))))
      (.classMem (.cv y) X)
  have p0082 :=
    @gSseldd
      (synWa (synWa (synWa (synWa (synWa (.classMem A (synCnnc)) (synWss X (synCnnc)))
              (.neg (synWrex u X (synWbr (.cv u) (synCkqrel (synClefin)) A))))
            (.classMem (.cv t) X))
          (synWbr (.cv t) (synCkqrel (synClefin)) (synCplc A (synC1c))))
        (.classMem (.cv y) X))
      X (synCnnc) (.cv y) p0080 p0081
  have p0083 :=
    @gConnexd
      (synWa (synWa (synWa (synWa (synWa (.classMem A (synCnnc)) (synWss X (synCnnc)))
              (.neg (synWrex u X (synWbr (.cv u) (synCkqrel (synClefin)) A))))
            (.classMem (.cv t) X))
          (synWbr (.cv t) (synCkqrel (synClefin)) (synCplc A (synC1c))))
        (.classMem (.cv y) X))
      (synCnnc) (synCkqrel (synClefin)) (synCplc A (synC1c)) (.cv y) p0060 p0071
      p0082
  have p0084 := @gId (synWbr (synCplc A (synC1c)) (synCkqrel (synClefin)) (.cv y))
  have p0085 :=
    @gA1i
      (.imp (synWbr (synCplc A (synC1c)) (synCkqrel (synClefin)) (.cv y))
        (synWbr (synCplc A (synC1c)) (synCkqrel (synClefin)) (.cv y)))
      (synWa (synWa (synWa (synWa (synWa (.classMem A (synCnnc)) (synWss X (synCnnc)))
              (.neg (synWrex u X (synWbr (.cv u) (synCkqrel (synClefin)) A))))
            (.classMem (.cv t) X))
          (synWbr (.cv t) (synCkqrel (synClefin)) (synCplc A (synC1c))))
        (.classMem (.cv y) X))
      p0084
  have p0086 :=
    @gSimpl
      (synWa (synWa (synWa (synWa (synWa (.classMem A (synCnnc)) (synWss X (synCnnc)))
              (.neg (synWrex u X (synWbr (.cv u) (synCkqrel (synClefin)) A))))
            (.classMem (.cv t) X))
          (synWbr (.cv t) (synCkqrel (synClefin)) (synCplc A (synC1c))))
        (.classMem (.cv y) X))
      (synWbr (.cv y) (synCkqrel (synClefin)) (synCplc A (synC1c)))
  have p0098 :=
    @gSyl
      (synWa (synWa (synWa (synWa
              (synWa (synWa (.classMem A (synCnnc)) (synWss X (synCnnc)))
                (.neg (synWrex u X (synWbr (.cv u) (synCkqrel (synClefin)) A))))
              (.classMem (.cv t) X))
            (synWbr (.cv t) (synCkqrel (synClefin)) (synCplc A (synC1c))))
          (.classMem (.cv y) X))
        (synWbr (.cv y) (synCkqrel (synClefin)) (synCplc A (synC1c))))
      (synWa (synWa (synWa (synWa (synWa (.classMem A (synCnnc)) (synWss X (synCnnc)))
              (.neg (synWrex u X (synWbr (.cv u) (synCkqrel (synClefin)) A))))
            (.classMem (.cv t) X))
          (synWbr (.cv t) (synCkqrel (synClefin)) (synCplc A (synC1c))))
        (.classMem (.cv y) X))
      (.classMem (synCplc A (synC1c)) (synCnnc)) p0086 p0071
  have p0099 := @gElex (synCplc A (synC1c)) (synCnnc)
  have p0100 :=
    @gSyl
      (synWa (synWa (synWa (synWa
              (synWa (synWa (.classMem A (synCnnc)) (synWss X (synCnnc)))
                (.neg (synWrex u X (synWbr (.cv u) (synCkqrel (synClefin)) A))))
              (.classMem (.cv t) X))
            (synWbr (.cv t) (synCkqrel (synClefin)) (synCplc A (synC1c))))
          (.classMem (.cv y) X))
        (synWbr (.cv y) (synCkqrel (synClefin)) (synCplc A (synC1c))))
      (.classMem (synCplc A (synC1c)) (synCnnc))
      (.classMem (synCplc A (synC1c)) (synCvv)) p0098 p0099
  have p0101 := @gLefinrflx (synCplc A (synC1c)) (synCvv)
  have p0102 :=
    @gSyl
      (synWa (synWa (synWa (synWa
              (synWa (synWa (.classMem A (synCnnc)) (synWss X (synCnnc)))
                (.neg (synWrex u X (synWbr (.cv u) (synCkqrel (synClefin)) A))))
              (.classMem (.cv t) X))
            (synWbr (.cv t) (synCkqrel (synClefin)) (synCplc A (synC1c))))
          (.classMem (.cv y) X))
        (synWbr (.cv y) (synCkqrel (synClefin)) (synCplc A (synC1c))))
      (.classMem (synCplc A (synC1c)) (synCvv))
      (.classMem (synCopk (synCplc A (synC1c)) (synCplc A (synC1c))) (synClefin))
      p0100 p0101
  have p0133 :=
    @gJca
      (synWa (synWa (synWa (synWa
              (synWa (synWa (.classMem A (synCnnc)) (synWss X (synCnnc)))
                (.neg (synWrex u X (synWbr (.cv u) (synCkqrel (synClefin)) A))))
              (.classMem (.cv t) X))
            (synWbr (.cv t) (synCkqrel (synClefin)) (synCplc A (synC1c))))
          (.classMem (.cv y) X))
        (synWbr (.cv y) (synCkqrel (synClefin)) (synCplc A (synC1c))))
      (.classMem (synCplc A (synC1c)) (synCvv))
      (.classMem (synCplc A (synC1c)) (synCvv)) p0100 p0100
  have p0134 :=
    @gKqlefinbr (synCplc A (synC1c)) (synCplc A (synC1c)) (synCvv) (synCvv)
  have p0135 :=
    @gSyl
      (synWa (synWa (synWa (synWa
              (synWa (synWa (.classMem A (synCnnc)) (synWss X (synCnnc)))
                (.neg (synWrex u X (synWbr (.cv u) (synCkqrel (synClefin)) A))))
              (.classMem (.cv t) X))
            (synWbr (.cv t) (synCkqrel (synClefin)) (synCplc A (synC1c))))
          (.classMem (.cv y) X))
        (synWbr (.cv y) (synCkqrel (synClefin)) (synCplc A (synC1c))))
      (synWa (.classMem (synCplc A (synC1c)) (synCvv))
        (.classMem (synCplc A (synC1c)) (synCvv)))
      (synWb (synWbr (synCplc A (synC1c)) (synCkqrel (synClefin)) (synCplc A (synC1c)))
        (.classMem (synCopk (synCplc A (synC1c)) (synCplc A (synC1c))) (synClefin)))
      p0133 p0134
  have p0136 :=
    @gMpbird
      (synWa (synWa (synWa (synWa
              (synWa (synWa (.classMem A (synCnnc)) (synWss X (synCnnc)))
                (.neg (synWrex u X (synWbr (.cv u) (synCkqrel (synClefin)) A))))
              (.classMem (.cv t) X))
            (synWbr (.cv t) (synCkqrel (synClefin)) (synCplc A (synC1c))))
          (.classMem (.cv y) X))
        (synWbr (.cv y) (synCkqrel (synClefin)) (synCplc A (synC1c))))
      (synWbr (synCplc A (synC1c)) (synCkqrel (synClefin)) (synCplc A (synC1c)))
      (.classMem (synCopk (synCplc A (synC1c)) (synCplc A (synC1c))) (synClefin))
      p0102 p0135
  have p0137 :=
    @gSimpr
      (synWa (synWa (synWa (synWa (synWa (.classMem A (synCnnc)) (synWss X (synCnnc)))
              (.neg (synWrex u X (synWbr (.cv u) (synCkqrel (synClefin)) A))))
            (.classMem (.cv t) X))
          (synWbr (.cv t) (synCkqrel (synClefin)) (synCplc A (synC1c))))
        (.classMem (.cv y) X))
      (synWbr (.cv y) (synCkqrel (synClefin)) (synCplc A (synC1c)))
  have p0159 :=
    @gJca
      (synWa (synWa (synWa (synWa (synWa (.classMem A (synCnnc)) (synWss X (synCnnc)))
              (.neg (synWrex u X (synWbr (.cv u) (synCkqrel (synClefin)) A))))
            (.classMem (.cv t) X))
          (synWbr (.cv t) (synCkqrel (synClefin)) (synCplc A (synC1c))))
        (.classMem (.cv y) X))
      (.classMem A (synCnnc)) (.classMem (.cv y) (synCnnc)) p0069 p0082
  have p0160 := @gKqfinsucsplit A (.cv y)
  have p0161 :=
    @gSyl
      (synWa (synWa (synWa (synWa (synWa (.classMem A (synCnnc)) (synWss X (synCnnc)))
              (.neg (synWrex u X (synWbr (.cv u) (synCkqrel (synClefin)) A))))
            (.classMem (.cv t) X))
          (synWbr (.cv t) (synCkqrel (synClefin)) (synCplc A (synC1c))))
        (.classMem (.cv y) X))
      (synWa (.classMem A (synCnnc)) (.classMem (.cv y) (synCnnc)))
      (synWb (synWbr (.cv y) (synCkqrel (synClefin)) (synCplc A (synC1c)))
        (synWo (synWbr (.cv y) (synCkqrel (synClefin)) A)
          (.classEq (.cv y) (synCplc A (synC1c)))))
      p0159 p0160
  have p0162 :=
    @gBiimpd
      (synWa (synWa (synWa (synWa (synWa (.classMem A (synCnnc)) (synWss X (synCnnc)))
              (.neg (synWrex u X (synWbr (.cv u) (synCkqrel (synClefin)) A))))
            (.classMem (.cv t) X))
          (synWbr (.cv t) (synCkqrel (synClefin)) (synCplc A (synC1c))))
        (.classMem (.cv y) X))
      (synWbr (.cv y) (synCkqrel (synClefin)) (synCplc A (synC1c)))
      (synWo (synWbr (.cv y) (synCkqrel (synClefin)) A)
        (.classEq (.cv y) (synCplc A (synC1c))))
      p0161
  have p0163 :=
    @gSyl
      (synWa (synWa (synWa (synWa
              (synWa (synWa (.classMem A (synCnnc)) (synWss X (synCnnc)))
                (.neg (synWrex u X (synWbr (.cv u) (synCkqrel (synClefin)) A))))
              (.classMem (.cv t) X))
            (synWbr (.cv t) (synCkqrel (synClefin)) (synCplc A (synC1c))))
          (.classMem (.cv y) X))
        (synWbr (.cv y) (synCkqrel (synClefin)) (synCplc A (synC1c))))
      (synWa (synWa (synWa (synWa (synWa (.classMem A (synCnnc)) (synWss X (synCnnc)))
              (.neg (synWrex u X (synWbr (.cv u) (synCkqrel (synClefin)) A))))
            (.classMem (.cv t) X))
          (synWbr (.cv t) (synCkqrel (synClefin)) (synCplc A (synC1c))))
        (.classMem (.cv y) X))
      (.imp (synWbr (.cv y) (synCkqrel (synClefin)) (synCplc A (synC1c)))
        (synWo (synWbr (.cv y) (synCkqrel (synClefin)) A)
          (.classEq (.cv y) (synCplc A (synC1c)))))
      p0086 p0162
  have p0164 :=
    @gMpd
      (synWa (synWa (synWa (synWa
              (synWa (synWa (.classMem A (synCnnc)) (synWss X (synCnnc)))
                (.neg (synWrex u X (synWbr (.cv u) (synCkqrel (synClefin)) A))))
              (.classMem (.cv t) X))
            (synWbr (.cv t) (synCkqrel (synClefin)) (synCplc A (synC1c))))
          (.classMem (.cv y) X))
        (synWbr (.cv y) (synCkqrel (synClefin)) (synCplc A (synC1c))))
      (synWbr (.cv y) (synCkqrel (synClefin)) (synCplc A (synC1c)))
      (synWo (synWbr (.cv y) (synCkqrel (synClefin)) A)
        (.classEq (.cv y) (synCplc A (synC1c))))
      p0137 p0163
  have p0172 :=
    @gSyl
      (synWa (synWa (synWa (synWa (synWa (.classMem A (synCnnc)) (synWss X (synCnnc)))
              (.neg (synWrex u X (synWbr (.cv u) (synCkqrel (synClefin)) A))))
            (.classMem (.cv t) X))
          (synWbr (.cv t) (synCkqrel (synClefin)) (synCplc A (synC1c))))
        (.classMem (.cv y) X))
      (synWa (synWa (synWa (.classMem A (synCnnc)) (synWss X (synCnnc)))
          (.neg (synWrex u X (synWbr (.cv u) (synCkqrel (synClefin)) A))))
        (.classMem (.cv t) X))
      (.neg (synWrex u X (synWbr (.cv u) (synCkqrel (synClefin)) A))) p0063 p0034
  have p0173 :=
    @gSimpl
      (synWa (synWa (synWa (synWa (synWa (.classMem A (synCnnc)) (synWss X (synCnnc)))
              (.neg (synWrex u X (synWbr (.cv u) (synCkqrel (synClefin)) A))))
            (.classMem (.cv t) X))
          (synWbr (.cv t) (synCkqrel (synClefin)) (synCplc A (synC1c))))
        (.classMem (.cv y) X))
      (synWbr (.cv y) (synCkqrel (synClefin)) A)
  have p0175 :=
    @gSyl
      (synWa (synWa (synWa (synWa
              (synWa (synWa (.classMem A (synCnnc)) (synWss X (synCnnc)))
                (.neg (synWrex u X (synWbr (.cv u) (synCkqrel (synClefin)) A))))
              (.classMem (.cv t) X))
            (synWbr (.cv t) (synCkqrel (synClefin)) (synCplc A (synC1c))))
          (.classMem (.cv y) X)) (synWbr (.cv y) (synCkqrel (synClefin)) A))
      (synWa (synWa (synWa (synWa (synWa (.classMem A (synCnnc)) (synWss X (synCnnc)))
              (.neg (synWrex u X (synWbr (.cv u) (synCkqrel (synClefin)) A))))
            (.classMem (.cv t) X))
          (synWbr (.cv t) (synCkqrel (synClefin)) (synCplc A (synC1c))))
        (.classMem (.cv y) X))
      (.classMem (.cv y) X) p0173 p0081
  have p0176 :=
    @gSimpr
      (synWa (synWa (synWa (synWa (synWa (.classMem A (synCnnc)) (synWss X (synCnnc)))
              (.neg (synWrex u X (synWbr (.cv u) (synCkqrel (synClefin)) A))))
            (.classMem (.cv t) X))
          (synWbr (.cv t) (synCkqrel (synClefin)) (synCplc A (synC1c))))
        (.classMem (.cv y) X))
      (synWbr (.cv y) (synCkqrel (synClefin)) A)
  have p0177 :=
    @gJca
      (synWa (synWa (synWa (synWa
              (synWa (synWa (.classMem A (synCnnc)) (synWss X (synCnnc)))
                (.neg (synWrex u X (synWbr (.cv u) (synCkqrel (synClefin)) A))))
              (.classMem (.cv t) X))
            (synWbr (.cv t) (synCkqrel (synClefin)) (synCplc A (synC1c))))
          (.classMem (.cv y) X)) (synWbr (.cv y) (synCkqrel (synClefin)) A))
      (.classMem (.cv y) X) (synWbr (.cv y) (synCkqrel (synClefin)) A) p0175 p0176
  have p0178 := @gBreq1 (.cv u) (.cv y) A (synCkqrel (synClefin))
  have p0179 :=
    @gRspcev (synWbr (.cv u) (synCkqrel (synClefin)) A)
      (synWbr (.cv y) (synCkqrel (synClefin)) A) u (.cv y) X dv_cache_0004
      dv_cache_0002 dv_cache_0005 p0178
  have p0180 :=
    @gSyl
      (synWa (synWa (synWa (synWa
              (synWa (synWa (.classMem A (synCnnc)) (synWss X (synCnnc)))
                (.neg (synWrex u X (synWbr (.cv u) (synCkqrel (synClefin)) A))))
              (.classMem (.cv t) X))
            (synWbr (.cv t) (synCkqrel (synClefin)) (synCplc A (synC1c))))
          (.classMem (.cv y) X)) (synWbr (.cv y) (synCkqrel (synClefin)) A))
      (synWa (.classMem (.cv y) X) (synWbr (.cv y) (synCkqrel (synClefin)) A))
      (synWrex u X (synWbr (.cv u) (synCkqrel (synClefin)) A)) p0177 p0179
  have p0181 :=
    @gEx
      (synWa (synWa (synWa (synWa (synWa (.classMem A (synCnnc)) (synWss X (synCnnc)))
              (.neg (synWrex u X (synWbr (.cv u) (synCkqrel (synClefin)) A))))
            (.classMem (.cv t) X))
          (synWbr (.cv t) (synCkqrel (synClefin)) (synCplc A (synC1c))))
        (.classMem (.cv y) X))
      (synWbr (.cv y) (synCkqrel (synClefin)) A)
      (synWrex u X (synWbr (.cv u) (synCkqrel (synClefin)) A)) p0180
  have p0182 :=
    @gCon3d
      (synWa (synWa (synWa (synWa (synWa (.classMem A (synCnnc)) (synWss X (synCnnc)))
              (.neg (synWrex u X (synWbr (.cv u) (synCkqrel (synClefin)) A))))
            (.classMem (.cv t) X))
          (synWbr (.cv t) (synCkqrel (synClefin)) (synCplc A (synC1c))))
        (.classMem (.cv y) X))
      (synWbr (.cv y) (synCkqrel (synClefin)) A)
      (synWrex u X (synWbr (.cv u) (synCkqrel (synClefin)) A)) p0181
  have p0183 :=
    @gMpd
      (synWa (synWa (synWa (synWa (synWa (.classMem A (synCnnc)) (synWss X (synCnnc)))
              (.neg (synWrex u X (synWbr (.cv u) (synCkqrel (synClefin)) A))))
            (.classMem (.cv t) X))
          (synWbr (.cv t) (synCkqrel (synClefin)) (synCplc A (synC1c))))
        (.classMem (.cv y) X))
      (.neg (synWrex u X (synWbr (.cv u) (synCkqrel (synClefin)) A)))
      (.neg (synWbr (.cv y) (synCkqrel (synClefin)) A)) p0172 p0182
  have p0184 :=
    @gPm221d
      (synWa (synWa (synWa (synWa (synWa (.classMem A (synCnnc)) (synWss X (synCnnc)))
              (.neg (synWrex u X (synWbr (.cv u) (synCkqrel (synClefin)) A))))
            (.classMem (.cv t) X))
          (synWbr (.cv t) (synCkqrel (synClefin)) (synCplc A (synC1c))))
        (.classMem (.cv y) X))
      (synWbr (.cv y) (synCkqrel (synClefin)) A)
      (.classEq (.cv y) (synCplc A (synC1c))) p0183
  have p0185 := @gId (.classEq (.cv y) (synCplc A (synC1c)))
  have p0186 :=
    @gA1i
      (.imp (.classEq (.cv y) (synCplc A (synC1c))) (.classEq (.cv y) (synCplc A (synC1c))))
      (synWa (synWa (synWa (synWa (synWa (.classMem A (synCnnc)) (synWss X (synCnnc)))
              (.neg (synWrex u X (synWbr (.cv u) (synCkqrel (synClefin)) A))))
            (.classMem (.cv t) X))
          (synWbr (.cv t) (synCkqrel (synClefin)) (synCplc A (synC1c))))
        (.classMem (.cv y) X))
      p0185
  have p0187 :=
    @gJaod
      (synWa (synWa (synWa (synWa (synWa (.classMem A (synCnnc)) (synWss X (synCnnc)))
              (.neg (synWrex u X (synWbr (.cv u) (synCkqrel (synClefin)) A))))
            (.classMem (.cv t) X))
          (synWbr (.cv t) (synCkqrel (synClefin)) (synCplc A (synC1c))))
        (.classMem (.cv y) X))
      (synWbr (.cv y) (synCkqrel (synClefin)) A)
      (.classEq (.cv y) (synCplc A (synC1c))) (.classEq (.cv y) (synCplc A (synC1c)))
      p0184 p0186
  have p0188 :=
    @gSyl
      (synWa (synWa (synWa (synWa
              (synWa (synWa (.classMem A (synCnnc)) (synWss X (synCnnc)))
                (.neg (synWrex u X (synWbr (.cv u) (synCkqrel (synClefin)) A))))
              (.classMem (.cv t) X))
            (synWbr (.cv t) (synCkqrel (synClefin)) (synCplc A (synC1c))))
          (.classMem (.cv y) X))
        (synWbr (.cv y) (synCkqrel (synClefin)) (synCplc A (synC1c))))
      (synWa (synWa (synWa (synWa (synWa (.classMem A (synCnnc)) (synWss X (synCnnc)))
              (.neg (synWrex u X (synWbr (.cv u) (synCkqrel (synClefin)) A))))
            (.classMem (.cv t) X))
          (synWbr (.cv t) (synCkqrel (synClefin)) (synCplc A (synC1c))))
        (.classMem (.cv y) X))
      (.imp (synWo (synWbr (.cv y) (synCkqrel (synClefin)) A)
          (.classEq (.cv y) (synCplc A (synC1c)))) (.classEq (.cv y) (synCplc A (synC1c))))
      p0086 p0187
  have p0189 :=
    @gMpd
      (synWa (synWa (synWa (synWa
              (synWa (synWa (.classMem A (synCnnc)) (synWss X (synCnnc)))
                (.neg (synWrex u X (synWbr (.cv u) (synCkqrel (synClefin)) A))))
              (.classMem (.cv t) X))
            (synWbr (.cv t) (synCkqrel (synClefin)) (synCplc A (synC1c))))
          (.classMem (.cv y) X))
        (synWbr (.cv y) (synCkqrel (synClefin)) (synCplc A (synC1c))))
      (synWo (synWbr (.cv y) (synCkqrel (synClefin)) A)
        (.classEq (.cv y) (synCplc A (synC1c))))
      (.classEq (.cv y) (synCplc A (synC1c))) p0164 p0188
  have p0190 :=
    @gBreq2d
      (synWa (synWa (synWa (synWa
              (synWa (synWa (.classMem A (synCnnc)) (synWss X (synCnnc)))
                (.neg (synWrex u X (synWbr (.cv u) (synCkqrel (synClefin)) A))))
              (.classMem (.cv t) X))
            (synWbr (.cv t) (synCkqrel (synClefin)) (synCplc A (synC1c))))
          (.classMem (.cv y) X))
        (synWbr (.cv y) (synCkqrel (synClefin)) (synCplc A (synC1c))))
      (.cv y) (synCplc A (synC1c)) (synCplc A (synC1c)) (synCkqrel (synClefin))
      p0189
  have p0191 :=
    @gMpbird
      (synWa (synWa (synWa (synWa
              (synWa (synWa (.classMem A (synCnnc)) (synWss X (synCnnc)))
                (.neg (synWrex u X (synWbr (.cv u) (synCkqrel (synClefin)) A))))
              (.classMem (.cv t) X))
            (synWbr (.cv t) (synCkqrel (synClefin)) (synCplc A (synC1c))))
          (.classMem (.cv y) X))
        (synWbr (.cv y) (synCkqrel (synClefin)) (synCplc A (synC1c))))
      (synWbr (synCplc A (synC1c)) (synCkqrel (synClefin)) (.cv y))
      (synWbr (synCplc A (synC1c)) (synCkqrel (synClefin)) (synCplc A (synC1c)))
      p0136 p0190
  have p0192 :=
    @gEx
      (synWa (synWa (synWa (synWa (synWa (.classMem A (synCnnc)) (synWss X (synCnnc)))
              (.neg (synWrex u X (synWbr (.cv u) (synCkqrel (synClefin)) A))))
            (.classMem (.cv t) X))
          (synWbr (.cv t) (synCkqrel (synClefin)) (synCplc A (synC1c))))
        (.classMem (.cv y) X))
      (synWbr (.cv y) (synCkqrel (synClefin)) (synCplc A (synC1c)))
      (synWbr (synCplc A (synC1c)) (synCkqrel (synClefin)) (.cv y)) p0191
  have p0193 :=
    @gJaod
      (synWa (synWa (synWa (synWa (synWa (.classMem A (synCnnc)) (synWss X (synCnnc)))
              (.neg (synWrex u X (synWbr (.cv u) (synCkqrel (synClefin)) A))))
            (.classMem (.cv t) X))
          (synWbr (.cv t) (synCkqrel (synClefin)) (synCplc A (synC1c))))
        (.classMem (.cv y) X))
      (synWbr (synCplc A (synC1c)) (synCkqrel (synClefin)) (.cv y))
      (synWbr (synCplc A (synC1c)) (synCkqrel (synClefin)) (.cv y))
      (synWbr (.cv y) (synCkqrel (synClefin)) (synCplc A (synC1c))) p0085 p0192
  have p0194 :=
    @gMpd
      (synWa (synWa (synWa (synWa (synWa (.classMem A (synCnnc)) (synWss X (synCnnc)))
              (.neg (synWrex u X (synWbr (.cv u) (synCkqrel (synClefin)) A))))
            (.classMem (.cv t) X))
          (synWbr (.cv t) (synCkqrel (synClefin)) (synCplc A (synC1c))))
        (.classMem (.cv y) X))
      (synWo (synWbr (synCplc A (synC1c)) (synCkqrel (synClefin)) (.cv y))
        (synWbr (.cv y) (synCkqrel (synClefin)) (synCplc A (synC1c))))
      (synWbr (synCplc A (synC1c)) (synCkqrel (synClefin)) (.cv y)) p0083 p0193
  have p0195 :=
    @gRalrimiva
      (synWa (synWa (synWa (synWa (.classMem A (synCnnc)) (synWss X (synCnnc)))
            (.neg (synWrex u X (synWbr (.cv u) (synCkqrel (synClefin)) A))))
          (.classMem (.cv t) X))
        (synWbr (.cv t) (synCkqrel (synClefin)) (synCplc A (synC1c))))
      (synWbr (synCplc A (synC1c)) (synCkqrel (synClefin)) (.cv y)) y X dv_cache_0006
      p0194
  have p0196 :=
    @gJca
      (synWa (synWa (synWa (synWa (.classMem A (synCnnc)) (synWss X (synCnnc)))
            (.neg (synWrex u X (synWbr (.cv u) (synCkqrel (synClefin)) A))))
          (.classMem (.cv t) X))
        (synWbr (.cv t) (synCkqrel (synClefin)) (synCplc A (synC1c))))
      (.classMem (synCplc A (synC1c)) X)
      (synWral y X (synWbr (synCplc A (synC1c)) (synCkqrel (synClefin)) (.cv y)))
      p0053 p0195
  have p0197 := @gBreq1 (.cv z) (synCplc A (synC1c)) (.cv y) (synCkqrel (synClefin))
  have p0198 :=
    @gRalbidv (.classEq (.cv z) (synCplc A (synC1c)))
      (synWbr (.cv z) (synCkqrel (synClefin)) (.cv y))
      (synWbr (synCplc A (synC1c)) (synCkqrel (synClefin)) (.cv y)) y X dv_cache_0007
      p0197
  have p0199 :=
    @gRspcev (synWral y X (synWbr (.cv z) (synCkqrel (synClefin)) (.cv y)))
      (synWral y X (synWbr (synCplc A (synC1c)) (synCkqrel (synClefin)) (.cv y))) z
      (synCplc A (synC1c)) X dv_cache_0008 dv_cache_0009 dv_cache_0010 p0198
  have p0200 :=
    @gSyl
      (synWa (synWa (synWa (synWa (.classMem A (synCnnc)) (synWss X (synCnnc)))
            (.neg (synWrex u X (synWbr (.cv u) (synCkqrel (synClefin)) A))))
          (.classMem (.cv t) X))
        (synWbr (.cv t) (synCkqrel (synClefin)) (synCplc A (synC1c))))
      (synWa (.classMem (synCplc A (synC1c)) X)
        (synWral y X (synWbr (synCplc A (synC1c)) (synCkqrel (synClefin)) (.cv y))))
      (synWrex z X (synWral y X (synWbr (.cv z) (synCkqrel (synClefin)) (.cv y))))
      p0196 p0199
  have p0201 :=
    @gEx
      (synWa (synWa (synWa (.classMem A (synCnnc)) (synWss X (synCnnc)))
          (.neg (synWrex u X (synWbr (.cv u) (synCkqrel (synClefin)) A))))
        (.classMem (.cv t) X))
      (synWbr (.cv t) (synCkqrel (synClefin)) (synCplc A (synC1c)))
      (synWrex z X (synWral y X (synWbr (.cv z) (synCkqrel (synClefin)) (.cv y))))
      p0200
  have p0202 :=
    @gRexlimdva
      (synWa (synWa (.classMem A (synCnnc)) (synWss X (synCnnc)))
        (.neg (synWrex u X (synWbr (.cv u) (synCkqrel (synClefin)) A))))
      (synWbr (.cv t) (synCkqrel (synClefin)) (synCplc A (synC1c)))
      (synWrex z X (synWral y X (synWbr (.cv z) (synCkqrel (synClefin)) (.cv y)))) t
      X dv_cache_0011 dv_cache_0012 p0201
  have p0203 :=
    @gSyl
      (synWa (synWa (.classMem A (synCnnc)) (synWss X (synCnnc)))
        (synWa (.neg (synWrex u X (synWbr (.cv u) (synCkqrel (synClefin)) A)))
          (synWrex t X (synWbr (.cv t) (synCkqrel (synClefin)) (synCplc A (synC1c))))))
      (synWa (synWa (.classMem A (synCnnc)) (synWss X (synCnnc)))
        (.neg (synWrex u X (synWbr (.cv u) (synCkqrel (synClefin)) A))))
      (.imp (synWrex t X (synWbr (.cv t) (synCkqrel (synClefin)) (synCplc A (synC1c))))
        (synWrex z X (synWral y X (synWbr (.cv z) (synCkqrel (synClefin)) (.cv y)))))
      p0007 p0202
  have p0204 :=
    @gMpd
      (synWa (synWa (.classMem A (synCnnc)) (synWss X (synCnnc)))
        (synWa (.neg (synWrex u X (synWbr (.cv u) (synCkqrel (synClefin)) A)))
          (synWrex t X (synWbr (.cv t) (synCkqrel (synClefin)) (synCplc A (synC1c))))))
      (synWrex t X (synWbr (.cv t) (synCkqrel (synClefin)) (synCplc A (synC1c))))
      (synWrex z X (synWral y X (synWbr (.cv z) (synCkqrel (synClefin)) (.cv y))))
      p0002 p0203
  have p0205 :=
    @gEx (synWa (.classMem A (synCnnc)) (synWss X (synCnnc)))
      (synWa (.neg (synWrex u X (synWbr (.cv u) (synCkqrel (synClefin)) A)))
        (synWrex t X (synWbr (.cv t) (synCkqrel (synClefin)) (synCplc A (synC1c)))))
      (synWrex z X (synWral y X (synWbr (.cv z) (synCkqrel (synClefin)) (.cv y))))
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

/-- Checked nominal proof certificate identified upstream as `g_finleastnn`. -/
@[expose]
noncomputable def gFinleastnn (y : Var) (z : Var) (V : Class) (X : Class)
    (_dv_V_y : y ∉ V.fv) (_dv_V_z : z ∉ V.fv) (dv_X_y : y ∉ X.fv) (dv_X_z : z ∉ X.fv)
    (dv_y_z : y ≠ z) :
    Nominal.NPrf
      (.imp (synW3a (.classMem X V) (synWss X (synCnnc)) (synWne X (synC0))) (synWrex z X
          (synWral y X (synWbr (.cv z) (synCkqrel (synClefin)) (.cv y))))) :=
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
  have dv_cache_0004 : u ∉ ((synWbr (.cv t) (synCkqrel (synClefin)) (.cv t))).fv :=
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
  have dv_cache_0005 : u ∉ ((synCkqrel (synClefin))).fv :=
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
  have dv_cache_0006 : t ∉ ((synC0c)).fv :=
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
  have dv_cache_0007 : t ∉ ((synCkqrel (synClefin))).fv :=
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
  have dv_cache_0014 : t ∉ ((synCplc (.cv n) (synC1c))).fv :=
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
      ((synWa (synW3a (.classMem X V) (synWss X (synCnnc)) (synWne X (synC0))) (.neg
            (synWrex z X
              (synWral y X (synWbr (.cv z) (synCkqrel (synClefin)) (.cv y))))))).fv :=
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
    n ∉ ((synCdif (synCvv) (synCima (synCkqrel (synClefin)) X))).fv :=
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
      ((synWrex z X (synWral y X (synWbr (.cv z) (synCkqrel (synClefin)) (.cv y))))).fv :=
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
      ((synWa (synW3a (.classMem X V) (synWss X (synCnnc)) (synWne X (synC0))) (.neg
            (synWrex z X
              (synWral y X (synWbr (.cv z) (synCkqrel (synClefin)) (.cv y))))))).fv :=
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
    @gSimpl (synW3a (.classMem X V) (synWss X (synCnnc)) (synWne X (synC0)))
      (.neg (synWrex z X (synWral y X (synWbr (.cv z) (synCkqrel (synClefin)) (.cv y)))))
  have p0001 := @gSimp3 (.classMem X V) (synWss X (synCnnc)) (synWne X (synC0))
  have p0002 :=
    @gSyl
      (synWa (synW3a (.classMem X V) (synWss X (synCnnc)) (synWne X (synC0))) (.neg
          (synWrex z X (synWral y X (synWbr (.cv z) (synCkqrel (synClefin)) (.cv y))))))
      (synW3a (.classMem X V) (synWss X (synCnnc)) (synWne X (synC0)))
      (synWne X (synC0)) p0000 p0001
  have p0003 := @gN0 t X dv_cache_0001
  have p0004 := @gBiimpi (synWne X (synC0)) (synWex t (.classMem (.cv t) X)) p0003
  have p0005 :=
    @gSyl
      (synWa (synW3a (.classMem X V) (synWss X (synCnnc)) (synWne X (synC0))) (.neg
          (synWrex z X (synWral y X (synWbr (.cv z) (synCkqrel (synClefin)) (.cv y))))))
      (synWne X (synC0)) (synWex t (.classMem (.cv t) X)) p0002 p0004
  have p0006 :=
    @gSimpr
      (synWa (synW3a (.classMem X V) (synWss X (synCnnc)) (synWne X (synC0))) (.neg
          (synWrex z X (synWral y X (synWbr (.cv z) (synCkqrel (synClefin)) (.cv y))))))
      (.classMem (.cv t) X)
  have p0007 :=
    @gSimpl
      (synWa (synW3a (.classMem X V) (synWss X (synCnnc)) (synWne X (synC0))) (.neg
          (synWrex z X (synWral y X (synWbr (.cv z) (synCkqrel (synClefin)) (.cv y))))))
      (.classMem (.cv t) X)
  have p0009 := @gSimp2 (.classMem X V) (synWss X (synCnnc)) (synWne X (synC0))
  have p0010 :=
    @gSyl
      (synWa (synW3a (.classMem X V) (synWss X (synCnnc)) (synWne X (synC0))) (.neg
          (synWrex z X (synWral y X (synWbr (.cv z) (synCkqrel (synClefin)) (.cv y))))))
      (synW3a (.classMem X V) (synWss X (synCnnc)) (synWne X (synC0)))
      (synWss X (synCnnc)) p0000 p0009
  have p0011 :=
    @gSyl
      (synWa (synWa (synW3a (.classMem X V) (synWss X (synCnnc)) (synWne X (synC0)))
          (.neg (synWrex z X
              (synWral y X (synWbr (.cv z) (synCkqrel (synClefin)) (.cv y))))))
        (.classMem (.cv t) X))
      (synWa (synW3a (.classMem X V) (synWss X (synCnnc)) (synWne X (synC0))) (.neg
          (synWrex z X (synWral y X (synWbr (.cv z) (synCkqrel (synClefin)) (.cv y))))))
      (synWss X (synCnnc)) p0007 p0010
  have p0013 :=
    @gSseldd
      (synWa (synWa (synW3a (.classMem X V) (synWss X (synCnnc)) (synWne X (synC0)))
          (.neg (synWrex z X
              (synWral y X (synWbr (.cv z) (synCkqrel (synClefin)) (.cv y))))))
        (.classMem (.cv t) X))
      X (synCnnc) (.cv t) p0011 p0006
  have p0014 := @gElex (.cv t) (synCnnc)
  have p0015 :=
    @gSyl
      (synWa (synWa (synW3a (.classMem X V) (synWss X (synCnnc)) (synWne X (synC0)))
          (.neg (synWrex z X
              (synWral y X (synWbr (.cv z) (synCkqrel (synClefin)) (.cv y))))))
        (.classMem (.cv t) X))
      (.classMem (.cv t) (synCnnc)) (.classMem (.cv t) (synCvv)) p0013 p0014
  have p0016 := @gLefinrflx (.cv t) (synCvv)
  have p0017 :=
    @gSyl
      (synWa (synWa (synW3a (.classMem X V) (synWss X (synCnnc)) (synWne X (synC0)))
          (.neg (synWrex z X
              (synWral y X (synWbr (.cv z) (synCkqrel (synClefin)) (.cv y))))))
        (.classMem (.cv t) X))
      (.classMem (.cv t) (synCvv)) (.classMem (synCopk (.cv t) (.cv t)) (synClefin))
      p0015 p0016
  have p0036 :=
    @gJca
      (synWa (synWa (synW3a (.classMem X V) (synWss X (synCnnc)) (synWne X (synC0)))
          (.neg (synWrex z X
              (synWral y X (synWbr (.cv z) (synCkqrel (synClefin)) (.cv y))))))
        (.classMem (.cv t) X))
      (.classMem (.cv t) (synCvv)) (.classMem (.cv t) (synCvv)) p0015 p0015
  have p0037 := @gKqlefinbr (.cv t) (.cv t) (synCvv) (synCvv)
  have p0038 :=
    @gSyl
      (synWa (synWa (synW3a (.classMem X V) (synWss X (synCnnc)) (synWne X (synC0)))
          (.neg (synWrex z X
              (synWral y X (synWbr (.cv z) (synCkqrel (synClefin)) (.cv y))))))
        (.classMem (.cv t) X))
      (synWa (.classMem (.cv t) (synCvv)) (.classMem (.cv t) (synCvv)))
      (synWb (synWbr (.cv t) (synCkqrel (synClefin)) (.cv t))
        (.classMem (synCopk (.cv t) (.cv t)) (synClefin)))
      p0036 p0037
  have p0039 :=
    @gMpbird
      (synWa (synWa (synW3a (.classMem X V) (synWss X (synCnnc)) (synWne X (synC0)))
          (.neg (synWrex z X
              (synWral y X (synWbr (.cv z) (synCkqrel (synClefin)) (.cv y))))))
        (.classMem (.cv t) X))
      (synWbr (.cv t) (synCkqrel (synClefin)) (.cv t))
      (.classMem (synCopk (.cv t) (.cv t)) (synClefin)) p0017 p0038
  have p0040 :=
    @gJca
      (synWa (synWa (synW3a (.classMem X V) (synWss X (synCnnc)) (synWne X (synC0)))
          (.neg (synWrex z X
              (synWral y X (synWbr (.cv z) (synCkqrel (synClefin)) (.cv y))))))
        (.classMem (.cv t) X))
      (.classMem (.cv t) X) (synWbr (.cv t) (synCkqrel (synClefin)) (.cv t)) p0006
      p0039
  have p0041 := @gBreq1 (.cv u) (.cv t) (.cv t) (synCkqrel (synClefin))
  have p0042 :=
    @gRspcev (synWbr (.cv u) (synCkqrel (synClefin)) (.cv t))
      (synWbr (.cv t) (synCkqrel (synClefin)) (.cv t)) u (.cv t) X dv_cache_0002
      dv_cache_0003 dv_cache_0004 p0041
  have p0043 :=
    @gSyl
      (synWa (synWa (synW3a (.classMem X V) (synWss X (synCnnc)) (synWne X (synC0)))
          (.neg (synWrex z X
              (synWral y X (synWbr (.cv z) (synCkqrel (synClefin)) (.cv y))))))
        (.classMem (.cv t) X))
      (synWa (.classMem (.cv t) X) (synWbr (.cv t) (synCkqrel (synClefin)) (.cv t)))
      (synWrex u X (synWbr (.cv u) (synCkqrel (synClefin)) (.cv t))) p0040 p0042
  have p0044 :=
    @gElima u (.cv t) (synCkqrel (synClefin)) X dv_cache_0002 dv_cache_0005
      dv_cache_0003
  have p0045 :=
    @gA1i
      (synWb (.classMem (.cv t) (synCima (synCkqrel (synClefin)) X))
        (synWrex u X (synWbr (.cv u) (synCkqrel (synClefin)) (.cv t))))
      (synWa (synWa (synW3a (.classMem X V) (synWss X (synCnnc)) (synWne X (synC0)))
          (.neg (synWrex z X
              (synWral y X (synWbr (.cv z) (synCkqrel (synClefin)) (.cv y))))))
        (.classMem (.cv t) X))
      p0044
  have p0046 :=
    @gMpbird
      (synWa (synWa (synW3a (.classMem X V) (synWss X (synCnnc)) (synWne X (synC0)))
          (.neg (synWrex z X
              (synWral y X (synWbr (.cv z) (synCkqrel (synClefin)) (.cv y))))))
        (.classMem (.cv t) X))
      (.classMem (.cv t) (synCima (synCkqrel (synClefin)) X))
      (synWrex u X (synWbr (.cv u) (synCkqrel (synClefin)) (.cv t))) p0043 p0045
  have p0048 := @gVvex
  have p0049 :=
    @gA1i (.classMem (synCvv) (synCvv))
      (synWa (synW3a (.classMem X V) (synWss X (synCnnc)) (synWne X (synC0))) (.neg
          (synWrex z X (synWral y X (synWbr (.cv z) (synCkqrel (synClefin)) (.cv y))))))
      p0048
  have p0050 := @gLefinex
  have p0051 := @gKqrelex (synClefin) p0050
  have p0052 :=
    @gA1i (.classMem (synCkqrel (synClefin)) (synCvv))
      (synWa (synW3a (.classMem X V) (synWss X (synCnnc)) (synWne X (synC0))) (.neg
          (synWrex z X (synWral y X (synWbr (.cv z) (synCkqrel (synClefin)) (.cv y))))))
      p0051
  have p0054 := @gSimp1 (.classMem X V) (synWss X (synCnnc)) (synWne X (synC0))
  have p0055 :=
    @gSyl
      (synWa (synW3a (.classMem X V) (synWss X (synCnnc)) (synWne X (synC0))) (.neg
          (synWrex z X (synWral y X (synWbr (.cv z) (synCkqrel (synClefin)) (.cv y))))))
      (synW3a (.classMem X V) (synWss X (synCnnc)) (synWne X (synC0)))
      (.classMem X V) p0000 p0054
  have p0056 :=
    @gJca
      (synWa (synW3a (.classMem X V) (synWss X (synCnnc)) (synWne X (synC0))) (.neg
          (synWrex z X (synWral y X (synWbr (.cv z) (synCkqrel (synClefin)) (.cv y))))))
      (.classMem (synCkqrel (synClefin)) (synCvv)) (.classMem X V) p0052 p0055
  have p0057 := @gImaexg (synCkqrel (synClefin)) X (synCvv) V
  have p0058 :=
    @gSyl
      (synWa (synW3a (.classMem X V) (synWss X (synCnnc)) (synWne X (synC0))) (.neg
          (synWrex z X (synWral y X (synWbr (.cv z) (synCkqrel (synClefin)) (.cv y))))))
      (synWa (.classMem (synCkqrel (synClefin)) (synCvv)) (.classMem X V))
      (.classMem (synCima (synCkqrel (synClefin)) X) (synCvv)) p0056 p0057
  have p0059 :=
    @gJca
      (synWa (synW3a (.classMem X V) (synWss X (synCnnc)) (synWne X (synC0))) (.neg
          (synWrex z X (synWral y X (synWbr (.cv z) (synCkqrel (synClefin)) (.cv y))))))
      (.classMem (synCvv) (synCvv))
      (.classMem (synCima (synCkqrel (synClefin)) X) (synCvv)) p0049 p0058
  have p0060 :=
    @gDifexg (synCvv) (synCima (synCkqrel (synClefin)) X) (synCvv) (synCvv)
  have p0061 :=
    @gSyl
      (synWa (synW3a (.classMem X V) (synWss X (synCnnc)) (synWne X (synC0))) (.neg
          (synWrex z X (synWral y X (synWbr (.cv z) (synCkqrel (synClefin)) (.cv y))))))
      (synWa (.classMem (synCvv) (synCvv))
        (.classMem (synCima (synCkqrel (synClefin)) X) (synCvv)))
      (.classMem (synCdif (synCvv) (synCima (synCkqrel (synClefin)) X)) (synCvv))
      p0059 p0060
  have p0062 := @gN0cex
  have p0063 :=
    @gA1i (.classMem (synC0c) (synCvv))
      (synWa (synW3a (.classMem X V) (synWss X (synCnnc)) (synWne X (synC0))) (.neg
          (synWrex z X (synWral y X (synWbr (.cv z) (synCkqrel (synClefin)) (.cv y))))))
      p0062
  have p0064 :=
    @gSimpr (synW3a (.classMem X V) (synWss X (synCnnc)) (synWne X (synC0)))
      (.neg (synWrex z X (synWral y X (synWbr (.cv z) (synCkqrel (synClefin)) (.cv y)))))
  have p0065 :=
    @gElima t (synC0c) (synCkqrel (synClefin)) X dv_cache_0006 dv_cache_0007
      dv_cache_0001
  have p0066 :=
    @gBiimpi (.classMem (synC0c) (synCima (synCkqrel (synClefin)) X))
      (synWrex t X (synWbr (.cv t) (synCkqrel (synClefin)) (synC0c))) p0065
  have p0070 :=
    @gFinleastbase y z t X dv_cache_0001 dv_cache_0008 dv_cache_0009 dv_cache_0010
      dv_cache_0011 dv_cache_0012
  have p0071 :=
    @gSyl
      (synWa (synW3a (.classMem X V) (synWss X (synCnnc)) (synWne X (synC0))) (.neg
          (synWrex z X (synWral y X (synWbr (.cv z) (synCkqrel (synClefin)) (.cv y))))))
      (synWss X (synCnnc))
      (.imp (synWrex t X (synWbr (.cv t) (synCkqrel (synClefin)) (synC0c)))
        (synWrex z X (synWral y X (synWbr (.cv z) (synCkqrel (synClefin)) (.cv y)))))
      p0010 p0070
  have p0072 :=
    @gSyl5 (.classMem (synC0c) (synCima (synCkqrel (synClefin)) X))
      (synWrex t X (synWbr (.cv t) (synCkqrel (synClefin)) (synC0c)))
      (synWa (synW3a (.classMem X V) (synWss X (synCnnc)) (synWne X (synC0))) (.neg
          (synWrex z X (synWral y X (synWbr (.cv z) (synCkqrel (synClefin)) (.cv y))))))
      (synWrex z X (synWral y X (synWbr (.cv z) (synCkqrel (synClefin)) (.cv y))))
      p0066 p0071
  have p0073 :=
    @gCon3d
      (synWa (synW3a (.classMem X V) (synWss X (synCnnc)) (synWne X (synC0))) (.neg
          (synWrex z X (synWral y X (synWbr (.cv z) (synCkqrel (synClefin)) (.cv y))))))
      (.classMem (synC0c) (synCima (synCkqrel (synClefin)) X))
      (synWrex z X (synWral y X (synWbr (.cv z) (synCkqrel (synClefin)) (.cv y))))
      p0072
  have p0074 :=
    @gMpd
      (synWa (synW3a (.classMem X V) (synWss X (synCnnc)) (synWne X (synC0))) (.neg
          (synWrex z X (synWral y X (synWbr (.cv z) (synCkqrel (synClefin)) (.cv y))))))
      (.neg (synWrex z X (synWral y X (synWbr (.cv z) (synCkqrel (synClefin)) (.cv y)))))
      (.neg (.classMem (synC0c) (synCima (synCkqrel (synClefin)) X))) p0064 p0073
  have p0075 :=
    @gJca
      (synWa (synW3a (.classMem X V) (synWss X (synCnnc)) (synWne X (synC0))) (.neg
          (synWrex z X (synWral y X (synWbr (.cv z) (synCkqrel (synClefin)) (.cv y))))))
      (.classMem (synC0c) (synCvv))
      (.neg (.classMem (synC0c) (synCima (synCkqrel (synClefin)) X))) p0063 p0074
  have p0076 := @gEldif (synC0c) (synCvv) (synCima (synCkqrel (synClefin)) X)
  have p0077 :=
    @gA1i
      (synWb (.classMem (synC0c) (synCdif (synCvv) (synCima (synCkqrel (synClefin)) X)))
        (synWa (.classMem (synC0c) (synCvv))
          (.neg (.classMem (synC0c) (synCima (synCkqrel (synClefin)) X)))))
      (synWa (synW3a (.classMem X V) (synWss X (synCnnc)) (synWne X (synC0))) (.neg
          (synWrex z X (synWral y X (synWbr (.cv z) (synCkqrel (synClefin)) (.cv y))))))
      p0076
  have p0078 :=
    @gMpbird
      (synWa (synW3a (.classMem X V) (synWss X (synCnnc)) (synWne X (synC0))) (.neg
          (synWrex z X (synWral y X (synWbr (.cv z) (synCkqrel (synClefin)) (.cv y))))))
      (.classMem (synC0c) (synCdif (synCvv) (synCima (synCkqrel (synClefin)) X)))
      (synWa (.classMem (synC0c) (synCvv))
        (.neg (.classMem (synC0c) (synCima (synCkqrel (synClefin)) X))))
      p0075 p0077
  have p0079 :=
    @gSimpl
      (synWa (synWa (synW3a (.classMem X V) (synWss X (synCnnc)) (synWne X (synC0)))
          (.neg (synWrex z X
              (synWral y X (synWbr (.cv z) (synCkqrel (synClefin)) (.cv y))))))
        (.classMem (.cv n) (synCnnc)))
      (.classMem (.cv n) (synCdif (synCvv) (synCima (synCkqrel (synClefin)) X)))
  have p0080 :=
    @gSimpr
      (synWa (synW3a (.classMem X V) (synWss X (synCnnc)) (synWne X (synC0))) (.neg
          (synWrex z X (synWral y X (synWbr (.cv z) (synCkqrel (synClefin)) (.cv y))))))
      (.classMem (.cv n) (synCnnc))
  have p0081 :=
    @gSyl
      (synWa (synWa
          (synWa (synW3a (.classMem X V) (synWss X (synCnnc)) (synWne X (synC0))) (.neg
              (synWrex z X
                (synWral y X (synWbr (.cv z) (synCkqrel (synClefin)) (.cv y))))))
          (.classMem (.cv n) (synCnnc)))
        (.classMem (.cv n) (synCdif (synCvv) (synCima (synCkqrel (synClefin)) X))))
      (synWa (synWa (synW3a (.classMem X V) (synWss X (synCnnc)) (synWne X (synC0)))
          (.neg (synWrex z X
              (synWral y X (synWbr (.cv z) (synCkqrel (synClefin)) (.cv y))))))
        (.classMem (.cv n) (synCnnc)))
      (.classMem (.cv n) (synCnnc)) p0079 p0080
  have p0082 := @gPeano2 (.cv n)
  have p0083 :=
    @gSyl
      (synWa (synWa
          (synWa (synW3a (.classMem X V) (synWss X (synCnnc)) (synWne X (synC0))) (.neg
              (synWrex z X
                (synWral y X (synWbr (.cv z) (synCkqrel (synClefin)) (.cv y))))))
          (.classMem (.cv n) (synCnnc)))
        (.classMem (.cv n) (synCdif (synCvv) (synCima (synCkqrel (synClefin)) X))))
      (.classMem (.cv n) (synCnnc)) (.classMem (synCplc (.cv n) (synC1c)) (synCnnc))
      p0081 p0082
  have p0084 := @gElex (synCplc (.cv n) (synC1c)) (synCnnc)
  have p0085 :=
    @gSyl
      (synWa (synWa
          (synWa (synW3a (.classMem X V) (synWss X (synCnnc)) (synWne X (synC0))) (.neg
              (synWrex z X
                (synWral y X (synWbr (.cv z) (synCkqrel (synClefin)) (.cv y))))))
          (.classMem (.cv n) (synCnnc)))
        (.classMem (.cv n) (synCdif (synCvv) (synCima (synCkqrel (synClefin)) X))))
      (.classMem (synCplc (.cv n) (synC1c)) (synCnnc))
      (.classMem (synCplc (.cv n) (synC1c)) (synCvv)) p0083 p0084
  have p0087 :=
    @gSimpl
      (synWa (synW3a (.classMem X V) (synWss X (synCnnc)) (synWne X (synC0))) (.neg
          (synWrex z X (synWral y X (synWbr (.cv z) (synCkqrel (synClefin)) (.cv y))))))
      (.classMem (.cv n) (synCnnc))
  have p0089 :=
    @gSyl
      (synWa (synWa (synW3a (.classMem X V) (synWss X (synCnnc)) (synWne X (synC0)))
          (.neg (synWrex z X
              (synWral y X (synWbr (.cv z) (synCkqrel (synClefin)) (.cv y))))))
        (.classMem (.cv n) (synCnnc)))
      (synWa (synW3a (.classMem X V) (synWss X (synCnnc)) (synWne X (synC0))) (.neg
          (synWrex z X (synWral y X (synWbr (.cv z) (synCkqrel (synClefin)) (.cv y))))))
      (.neg (synWrex z X (synWral y X (synWbr (.cv z) (synCkqrel (synClefin)) (.cv y)))))
      p0087 p0064
  have p0090 :=
    @gSyl
      (synWa (synWa
          (synWa (synW3a (.classMem X V) (synWss X (synCnnc)) (synWne X (synC0))) (.neg
              (synWrex z X
                (synWral y X (synWbr (.cv z) (synCkqrel (synClefin)) (.cv y))))))
          (.classMem (.cv n) (synCnnc)))
        (.classMem (.cv n) (synCdif (synCvv) (synCima (synCkqrel (synClefin)) X))))
      (synWa (synWa (synW3a (.classMem X V) (synWss X (synCnnc)) (synWne X (synC0)))
          (.neg (synWrex z X
              (synWral y X (synWbr (.cv z) (synCkqrel (synClefin)) (.cv y))))))
        (.classMem (.cv n) (synCnnc)))
      (.neg (synWrex z X (synWral y X (synWbr (.cv z) (synCkqrel (synClefin)) (.cv y)))))
      p0079 p0089
  have p0091 :=
    @gSimpl
      (synWa (synWa
          (synWa (synW3a (.classMem X V) (synWss X (synCnnc)) (synWne X (synC0))) (.neg
              (synWrex z X
                (synWral y X (synWbr (.cv z) (synCkqrel (synClefin)) (.cv y))))))
          (.classMem (.cv n) (synCnnc)))
        (.classMem (.cv n) (synCdif (synCvv) (synCima (synCkqrel (synClefin)) X))))
      (.classMem (synCplc (.cv n) (synC1c)) (synCima (synCkqrel (synClefin)) X))
  have p0092 :=
    @gSimpr
      (synWa (synWa (synW3a (.classMem X V) (synWss X (synCnnc)) (synWne X (synC0)))
          (.neg (synWrex z X
              (synWral y X (synWbr (.cv z) (synCkqrel (synClefin)) (.cv y))))))
        (.classMem (.cv n) (synCnnc)))
      (.classMem (.cv n) (synCdif (synCvv) (synCima (synCkqrel (synClefin)) X)))
  have p0094 := @gEldif (.cv n) (synCvv) (synCima (synCkqrel (synClefin)) X)
  have p0095 :=
    @gA1i
      (synWb (.classMem (.cv n) (synCdif (synCvv) (synCima (synCkqrel (synClefin)) X)))
        (synWa (.classMem (.cv n) (synCvv))
          (.neg (.classMem (.cv n) (synCima (synCkqrel (synClefin)) X)))))
      (synWa (synWa (synW3a (.classMem X V) (synWss X (synCnnc)) (synWne X (synC0)))
          (.neg (synWrex z X
              (synWral y X (synWbr (.cv z) (synCkqrel (synClefin)) (.cv y))))))
        (.classMem (.cv n) (synCnnc)))
      p0094
  have p0096 :=
    @gBiimpd
      (synWa (synWa (synW3a (.classMem X V) (synWss X (synCnnc)) (synWne X (synC0)))
          (.neg (synWrex z X
              (synWral y X (synWbr (.cv z) (synCkqrel (synClefin)) (.cv y))))))
        (.classMem (.cv n) (synCnnc)))
      (.classMem (.cv n) (synCdif (synCvv) (synCima (synCkqrel (synClefin)) X)))
      (synWa (.classMem (.cv n) (synCvv))
        (.neg (.classMem (.cv n) (synCima (synCkqrel (synClefin)) X))))
      p0095
  have p0097 :=
    @gSimpr (.classMem (.cv n) (synCvv))
      (.neg (.classMem (.cv n) (synCima (synCkqrel (synClefin)) X)))
  have p0098 :=
    @gSyl6
      (synWa (synWa (synW3a (.classMem X V) (synWss X (synCnnc)) (synWne X (synC0)))
          (.neg (synWrex z X
              (synWral y X (synWbr (.cv z) (synCkqrel (synClefin)) (.cv y))))))
        (.classMem (.cv n) (synCnnc)))
      (.classMem (.cv n) (synCdif (synCvv) (synCima (synCkqrel (synClefin)) X)))
      (synWa (.classMem (.cv n) (synCvv))
        (.neg (.classMem (.cv n) (synCima (synCkqrel (synClefin)) X))))
      (.neg (.classMem (.cv n) (synCima (synCkqrel (synClefin)) X))) p0096 p0097
  have p0099 :=
    @gSyl
      (synWa (synWa
          (synWa (synW3a (.classMem X V) (synWss X (synCnnc)) (synWne X (synC0))) (.neg
              (synWrex z X
                (synWral y X (synWbr (.cv z) (synCkqrel (synClefin)) (.cv y))))))
          (.classMem (.cv n) (synCnnc)))
        (.classMem (.cv n) (synCdif (synCvv) (synCima (synCkqrel (synClefin)) X))))
      (synWa (synWa (synW3a (.classMem X V) (synWss X (synCnnc)) (synWne X (synC0)))
          (.neg (synWrex z X
              (synWral y X (synWbr (.cv z) (synCkqrel (synClefin)) (.cv y))))))
        (.classMem (.cv n) (synCnnc)))
      (.imp (.classMem (.cv n) (synCdif (synCvv) (synCima (synCkqrel (synClefin)) X)))
        (.neg (.classMem (.cv n) (synCima (synCkqrel (synClefin)) X))))
      p0079 p0098
  have p0100 :=
    @gMpd
      (synWa (synWa
          (synWa (synW3a (.classMem X V) (synWss X (synCnnc)) (synWne X (synC0))) (.neg
              (synWrex z X
                (synWral y X (synWbr (.cv z) (synCkqrel (synClefin)) (.cv y))))))
          (.classMem (.cv n) (synCnnc)))
        (.classMem (.cv n) (synCdif (synCvv) (synCima (synCkqrel (synClefin)) X))))
      (.classMem (.cv n) (synCdif (synCvv) (synCima (synCkqrel (synClefin)) X)))
      (.neg (.classMem (.cv n) (synCima (synCkqrel (synClefin)) X))) p0092 p0099
  have p0101 :=
    @gElima u (.cv n) (synCkqrel (synClefin)) X dv_cache_0013 dv_cache_0005
      dv_cache_0003
  have p0102 :=
    @gBiimpri (.classMem (.cv n) (synCima (synCkqrel (synClefin)) X))
      (synWrex u X (synWbr (.cv u) (synCkqrel (synClefin)) (.cv n))) p0101
  have p0103 :=
    @gA1i
      (.imp (synWrex u X (synWbr (.cv u) (synCkqrel (synClefin)) (.cv n)))
        (.classMem (.cv n) (synCima (synCkqrel (synClefin)) X)))
      (synWa (synWa
          (synWa (synW3a (.classMem X V) (synWss X (synCnnc)) (synWne X (synC0))) (.neg
              (synWrex z X
                (synWral y X (synWbr (.cv z) (synCkqrel (synClefin)) (.cv y))))))
          (.classMem (.cv n) (synCnnc)))
        (.classMem (.cv n) (synCdif (synCvv) (synCima (synCkqrel (synClefin)) X))))
      p0102
  have p0104 :=
    @gCon3d
      (synWa (synWa
          (synWa (synW3a (.classMem X V) (synWss X (synCnnc)) (synWne X (synC0))) (.neg
              (synWrex z X
                (synWral y X (synWbr (.cv z) (synCkqrel (synClefin)) (.cv y))))))
          (.classMem (.cv n) (synCnnc)))
        (.classMem (.cv n) (synCdif (synCvv) (synCima (synCkqrel (synClefin)) X))))
      (synWrex u X (synWbr (.cv u) (synCkqrel (synClefin)) (.cv n)))
      (.classMem (.cv n) (synCima (synCkqrel (synClefin)) X)) p0103
  have p0105 :=
    @gMpd
      (synWa (synWa
          (synWa (synW3a (.classMem X V) (synWss X (synCnnc)) (synWne X (synC0))) (.neg
              (synWrex z X
                (synWral y X (synWbr (.cv z) (synCkqrel (synClefin)) (.cv y))))))
          (.classMem (.cv n) (synCnnc)))
        (.classMem (.cv n) (synCdif (synCvv) (synCima (synCkqrel (synClefin)) X))))
      (.neg (.classMem (.cv n) (synCima (synCkqrel (synClefin)) X)))
      (.neg (synWrex u X (synWbr (.cv u) (synCkqrel (synClefin)) (.cv n)))) p0100
      p0104
  have p0106 :=
    @gSyl
      (synWa (synWa (synWa
            (synWa (synW3a (.classMem X V) (synWss X (synCnnc)) (synWne X (synC0))) (.neg
                (synWrex z X
                  (synWral y X (synWbr (.cv z) (synCkqrel (synClefin)) (.cv y))))))
            (.classMem (.cv n) (synCnnc)))
          (.classMem (.cv n) (synCdif (synCvv) (synCima (synCkqrel (synClefin)) X))))
        (.classMem (synCplc (.cv n) (synC1c)) (synCima (synCkqrel (synClefin)) X)))
      (synWa (synWa
          (synWa (synW3a (.classMem X V) (synWss X (synCnnc)) (synWne X (synC0))) (.neg
              (synWrex z X
                (synWral y X (synWbr (.cv z) (synCkqrel (synClefin)) (.cv y))))))
          (.classMem (.cv n) (synCnnc)))
        (.classMem (.cv n) (synCdif (synCvv) (synCima (synCkqrel (synClefin)) X))))
      (.neg (synWrex u X (synWbr (.cv u) (synCkqrel (synClefin)) (.cv n)))) p0091
      p0105
  have p0107 :=
    @gSimpr
      (synWa (synWa
          (synWa (synW3a (.classMem X V) (synWss X (synCnnc)) (synWne X (synC0))) (.neg
              (synWrex z X
                (synWral y X (synWbr (.cv z) (synCkqrel (synClefin)) (.cv y))))))
          (.classMem (.cv n) (synCnnc)))
        (.classMem (.cv n) (synCdif (synCvv) (synCima (synCkqrel (synClefin)) X))))
      (.classMem (synCplc (.cv n) (synC1c)) (synCima (synCkqrel (synClefin)) X))
  have p0108 :=
    @gElima t (synCplc (.cv n) (synC1c)) (synCkqrel (synClefin)) X dv_cache_0014
      dv_cache_0007 dv_cache_0001
  have p0109 :=
    @gBiimpi
      (.classMem (synCplc (.cv n) (synC1c)) (synCima (synCkqrel (synClefin)) X))
      (synWrex t X (synWbr (.cv t) (synCkqrel (synClefin)) (synCplc (.cv n) (synC1c))))
      p0108
  have p0110 :=
    @gSyl
      (synWa (synWa (synWa
            (synWa (synW3a (.classMem X V) (synWss X (synCnnc)) (synWne X (synC0))) (.neg
                (synWrex z X
                  (synWral y X (synWbr (.cv z) (synCkqrel (synClefin)) (.cv y))))))
            (.classMem (.cv n) (synCnnc)))
          (.classMem (.cv n) (synCdif (synCvv) (synCima (synCkqrel (synClefin)) X))))
        (.classMem (synCplc (.cv n) (synC1c)) (synCima (synCkqrel (synClefin)) X)))
      (.classMem (synCplc (.cv n) (synC1c)) (synCima (synCkqrel (synClefin)) X))
      (synWrex t X (synWbr (.cv t) (synCkqrel (synClefin)) (synCplc (.cv n) (synC1c))))
      p0107 p0109
  have p0111 :=
    @gJca
      (synWa (synWa (synWa
            (synWa (synW3a (.classMem X V) (synWss X (synCnnc)) (synWne X (synC0))) (.neg
                (synWrex z X
                  (synWral y X (synWbr (.cv z) (synCkqrel (synClefin)) (.cv y))))))
            (.classMem (.cv n) (synCnnc)))
          (.classMem (.cv n) (synCdif (synCvv) (synCima (synCkqrel (synClefin)) X))))
        (.classMem (synCplc (.cv n) (synC1c)) (synCima (synCkqrel (synClefin)) X)))
      (.neg (synWrex u X (synWbr (.cv u) (synCkqrel (synClefin)) (.cv n))))
      (synWrex t X (synWbr (.cv t) (synCkqrel (synClefin)) (synCplc (.cv n) (synC1c))))
      p0106 p0110
  have p0121 :=
    @gSyl
      (synWa (synWa (synW3a (.classMem X V) (synWss X (synCnnc)) (synWne X (synC0)))
          (.neg (synWrex z X
              (synWral y X (synWbr (.cv z) (synCkqrel (synClefin)) (.cv y))))))
        (.classMem (.cv n) (synCnnc)))
      (synWa (synW3a (.classMem X V) (synWss X (synCnnc)) (synWne X (synC0))) (.neg
          (synWrex z X (synWral y X (synWbr (.cv z) (synCkqrel (synClefin)) (.cv y))))))
      (synWss X (synCnnc)) p0087 p0010
  have p0122 :=
    @gSyl
      (synWa (synWa
          (synWa (synW3a (.classMem X V) (synWss X (synCnnc)) (synWne X (synC0))) (.neg
              (synWrex z X
                (synWral y X (synWbr (.cv z) (synCkqrel (synClefin)) (.cv y))))))
          (.classMem (.cv n) (synCnnc)))
        (.classMem (.cv n) (synCdif (synCvv) (synCima (synCkqrel (synClefin)) X))))
      (synWa (synWa (synW3a (.classMem X V) (synWss X (synCnnc)) (synWne X (synC0)))
          (.neg (synWrex z X
              (synWral y X (synWbr (.cv z) (synCkqrel (synClefin)) (.cv y))))))
        (.classMem (.cv n) (synCnnc)))
      (synWss X (synCnnc)) p0079 p0121
  have p0123 :=
    @gJca
      (synWa (synWa
          (synWa (synW3a (.classMem X V) (synWss X (synCnnc)) (synWne X (synC0))) (.neg
              (synWrex z X
                (synWral y X (synWbr (.cv z) (synCkqrel (synClefin)) (.cv y))))))
          (.classMem (.cv n) (synCnnc)))
        (.classMem (.cv n) (synCdif (synCvv) (synCima (synCkqrel (synClefin)) X))))
      (.classMem (.cv n) (synCnnc)) (synWss X (synCnnc)) p0081 p0122
  have p0124 :=
    @gFinleaststep y z u t (.cv n) X dv_cache_0015 dv_cache_0013 dv_cache_0016
      dv_cache_0017 dv_cache_0001 dv_cache_0003 dv_cache_0008 dv_cache_0009 dv_cache_0018
      dv_cache_0010 dv_cache_0011 dv_cache_0019 dv_cache_0020 dv_cache_0012
  have p0125 :=
    @gSyl
      (synWa (synWa
          (synWa (synW3a (.classMem X V) (synWss X (synCnnc)) (synWne X (synC0))) (.neg
              (synWrex z X
                (synWral y X (synWbr (.cv z) (synCkqrel (synClefin)) (.cv y))))))
          (.classMem (.cv n) (synCnnc)))
        (.classMem (.cv n) (synCdif (synCvv) (synCima (synCkqrel (synClefin)) X))))
      (synWa (.classMem (.cv n) (synCnnc)) (synWss X (synCnnc)))
      (.imp (synWa (.neg (synWrex u X (synWbr (.cv u) (synCkqrel (synClefin)) (.cv n))))
          (synWrex t X
            (synWbr (.cv t) (synCkqrel (synClefin)) (synCplc (.cv n) (synC1c)))))
        (synWrex z X (synWral y X (synWbr (.cv z) (synCkqrel (synClefin)) (.cv y)))))
      p0123 p0124
  have p0126 :=
    @gSyl
      (synWa (synWa (synWa
            (synWa (synW3a (.classMem X V) (synWss X (synCnnc)) (synWne X (synC0))) (.neg
                (synWrex z X
                  (synWral y X (synWbr (.cv z) (synCkqrel (synClefin)) (.cv y))))))
            (.classMem (.cv n) (synCnnc)))
          (.classMem (.cv n) (synCdif (synCvv) (synCima (synCkqrel (synClefin)) X))))
        (.classMem (synCplc (.cv n) (synC1c)) (synCima (synCkqrel (synClefin)) X)))
      (synWa (synWa
          (synWa (synW3a (.classMem X V) (synWss X (synCnnc)) (synWne X (synC0))) (.neg
              (synWrex z X
                (synWral y X (synWbr (.cv z) (synCkqrel (synClefin)) (.cv y))))))
          (.classMem (.cv n) (synCnnc)))
        (.classMem (.cv n) (synCdif (synCvv) (synCima (synCkqrel (synClefin)) X))))
      (.imp (synWa (.neg (synWrex u X (synWbr (.cv u) (synCkqrel (synClefin)) (.cv n))))
          (synWrex t X
            (synWbr (.cv t) (synCkqrel (synClefin)) (synCplc (.cv n) (synC1c)))))
        (synWrex z X (synWral y X (synWbr (.cv z) (synCkqrel (synClefin)) (.cv y)))))
      p0091 p0125
  have p0127 :=
    @gMpd
      (synWa (synWa (synWa
            (synWa (synW3a (.classMem X V) (synWss X (synCnnc)) (synWne X (synC0))) (.neg
                (synWrex z X
                  (synWral y X (synWbr (.cv z) (synCkqrel (synClefin)) (.cv y))))))
            (.classMem (.cv n) (synCnnc)))
          (.classMem (.cv n) (synCdif (synCvv) (synCima (synCkqrel (synClefin)) X))))
        (.classMem (synCplc (.cv n) (synC1c)) (synCima (synCkqrel (synClefin)) X)))
      (synWa (.neg (synWrex u X (synWbr (.cv u) (synCkqrel (synClefin)) (.cv n))))
        (synWrex t X (synWbr (.cv t) (synCkqrel (synClefin)) (synCplc (.cv n) (synC1c)))))
      (synWrex z X (synWral y X (synWbr (.cv z) (synCkqrel (synClefin)) (.cv y))))
      p0111 p0126
  have p0128 :=
    @gEx
      (synWa (synWa
          (synWa (synW3a (.classMem X V) (synWss X (synCnnc)) (synWne X (synC0))) (.neg
              (synWrex z X
                (synWral y X (synWbr (.cv z) (synCkqrel (synClefin)) (.cv y))))))
          (.classMem (.cv n) (synCnnc)))
        (.classMem (.cv n) (synCdif (synCvv) (synCima (synCkqrel (synClefin)) X))))
      (.classMem (synCplc (.cv n) (synC1c)) (synCima (synCkqrel (synClefin)) X))
      (synWrex z X (synWral y X (synWbr (.cv z) (synCkqrel (synClefin)) (.cv y))))
      p0127
  have p0129 :=
    @gCon3d
      (synWa (synWa
          (synWa (synW3a (.classMem X V) (synWss X (synCnnc)) (synWne X (synC0))) (.neg
              (synWrex z X
                (synWral y X (synWbr (.cv z) (synCkqrel (synClefin)) (.cv y))))))
          (.classMem (.cv n) (synCnnc)))
        (.classMem (.cv n) (synCdif (synCvv) (synCima (synCkqrel (synClefin)) X))))
      (.classMem (synCplc (.cv n) (synC1c)) (synCima (synCkqrel (synClefin)) X))
      (synWrex z X (synWral y X (synWbr (.cv z) (synCkqrel (synClefin)) (.cv y))))
      p0128
  have p0130 :=
    @gMpd
      (synWa (synWa
          (synWa (synW3a (.classMem X V) (synWss X (synCnnc)) (synWne X (synC0))) (.neg
              (synWrex z X
                (synWral y X (synWbr (.cv z) (synCkqrel (synClefin)) (.cv y))))))
          (.classMem (.cv n) (synCnnc)))
        (.classMem (.cv n) (synCdif (synCvv) (synCima (synCkqrel (synClefin)) X))))
      (.neg (synWrex z X (synWral y X (synWbr (.cv z) (synCkqrel (synClefin)) (.cv y)))))
      (.neg (.classMem (synCplc (.cv n) (synC1c)) (synCima (synCkqrel (synClefin)) X)))
      p0090 p0129
  have p0131 :=
    @gJca
      (synWa (synWa
          (synWa (synW3a (.classMem X V) (synWss X (synCnnc)) (synWne X (synC0))) (.neg
              (synWrex z X
                (synWral y X (synWbr (.cv z) (synCkqrel (synClefin)) (.cv y))))))
          (.classMem (.cv n) (synCnnc)))
        (.classMem (.cv n) (synCdif (synCvv) (synCima (synCkqrel (synClefin)) X))))
      (.classMem (synCplc (.cv n) (synC1c)) (synCvv))
      (.neg (.classMem (synCplc (.cv n) (synC1c)) (synCima (synCkqrel (synClefin)) X)))
      p0085 p0130
  have p0132 :=
    @gEldif (synCplc (.cv n) (synC1c)) (synCvv) (synCima (synCkqrel (synClefin)) X)
  have p0133 :=
    @gA1i
      (synWb (.classMem (synCplc (.cv n) (synC1c))
          (synCdif (synCvv) (synCima (synCkqrel (synClefin)) X)))
        (synWa (.classMem (synCplc (.cv n) (synC1c)) (synCvv)) (.neg
            (.classMem (synCplc (.cv n) (synC1c)) (synCima (synCkqrel (synClefin)) X)))))
      (synWa (synWa
          (synWa (synW3a (.classMem X V) (synWss X (synCnnc)) (synWne X (synC0))) (.neg
              (synWrex z X
                (synWral y X (synWbr (.cv z) (synCkqrel (synClefin)) (.cv y))))))
          (.classMem (.cv n) (synCnnc)))
        (.classMem (.cv n) (synCdif (synCvv) (synCima (synCkqrel (synClefin)) X))))
      p0132
  have p0134 :=
    @gMpbird
      (synWa (synWa
          (synWa (synW3a (.classMem X V) (synWss X (synCnnc)) (synWne X (synC0))) (.neg
              (synWrex z X
                (synWral y X (synWbr (.cv z) (synCkqrel (synClefin)) (.cv y))))))
          (.classMem (.cv n) (synCnnc)))
        (.classMem (.cv n) (synCdif (synCvv) (synCima (synCkqrel (synClefin)) X))))
      (.classMem (synCplc (.cv n) (synC1c))
        (synCdif (synCvv) (synCima (synCkqrel (synClefin)) X)))
      (synWa (.classMem (synCplc (.cv n) (synC1c)) (synCvv)) (.neg
          (.classMem (synCplc (.cv n) (synC1c)) (synCima (synCkqrel (synClefin)) X))))
      p0131 p0133
  have p0135 :=
    @gEx
      (synWa (synWa (synW3a (.classMem X V) (synWss X (synCnnc)) (synWne X (synC0)))
          (.neg (synWrex z X
              (synWral y X (synWbr (.cv z) (synCkqrel (synClefin)) (.cv y))))))
        (.classMem (.cv n) (synCnnc)))
      (.classMem (.cv n) (synCdif (synCvv) (synCima (synCkqrel (synClefin)) X)))
      (.classMem (synCplc (.cv n) (synC1c))
        (synCdif (synCvv) (synCima (synCkqrel (synClefin)) X)))
      p0134
  have p0136 :=
    @gRalrimiva
      (synWa (synW3a (.classMem X V) (synWss X (synCnnc)) (synWne X (synC0))) (.neg
          (synWrex z X (synWral y X (synWbr (.cv z) (synCkqrel (synClefin)) (.cv y))))))
      (.imp (.classMem (.cv n) (synCdif (synCvv) (synCima (synCkqrel (synClefin)) X)))
        (.classMem (synCplc (.cv n) (synC1c))
          (synCdif (synCvv) (synCima (synCkqrel (synClefin)) X))))
      n (synCnnc) dv_cache_0021 p0135
  have p0137 :=
    @gN3jca
      (synWa (synW3a (.classMem X V) (synWss X (synCnnc)) (synWne X (synC0))) (.neg
          (synWrex z X (synWral y X (synWbr (.cv z) (synCkqrel (synClefin)) (.cv y))))))
      (.classMem (synCdif (synCvv) (synCima (synCkqrel (synClefin)) X)) (synCvv))
      (.classMem (synC0c) (synCdif (synCvv) (synCima (synCkqrel (synClefin)) X)))
      (synWral n (synCnnc) (.imp
          (.classMem (.cv n) (synCdif (synCvv) (synCima (synCkqrel (synClefin)) X)))
          (.classMem (synCplc (.cv n) (synC1c))
            (synCdif (synCvv) (synCima (synCkqrel (synClefin)) X)))))
      p0061 p0078 p0136
  have p0138 :=
    @gPeano5 n (synCdif (synCvv) (synCima (synCkqrel (synClefin)) X)) (synCvv)
      dv_cache_0022
  have p0139 :=
    @gSyl
      (synWa (synW3a (.classMem X V) (synWss X (synCnnc)) (synWne X (synC0))) (.neg
          (synWrex z X (synWral y X (synWbr (.cv z) (synCkqrel (synClefin)) (.cv y))))))
      (synW3a (.classMem (synCdif (synCvv) (synCima (synCkqrel (synClefin)) X)) (synCvv))
        (.classMem (synC0c) (synCdif (synCvv) (synCima (synCkqrel (synClefin)) X)))
        (synWral n (synCnnc) (.imp (.classMem (.cv n)
              (synCdif (synCvv) (synCima (synCkqrel (synClefin)) X)))
            (.classMem (synCplc (.cv n) (synC1c))
              (synCdif (synCvv) (synCima (synCkqrel (synClefin)) X))))))
      (synWss (synCnnc) (synCdif (synCvv) (synCima (synCkqrel (synClefin)) X)))
      p0137 p0138
  have p0140 :=
    @gSyl
      (synWa (synWa (synW3a (.classMem X V) (synWss X (synCnnc)) (synWne X (synC0)))
          (.neg (synWrex z X
              (synWral y X (synWbr (.cv z) (synCkqrel (synClefin)) (.cv y))))))
        (.classMem (.cv t) X))
      (synWa (synW3a (.classMem X V) (synWss X (synCnnc)) (synWne X (synC0))) (.neg
          (synWrex z X (synWral y X (synWbr (.cv z) (synCkqrel (synClefin)) (.cv y))))))
      (synWss (synCnnc) (synCdif (synCvv) (synCima (synCkqrel (synClefin)) X)))
      p0007 p0139
  have p0148 :=
    @gSseldd
      (synWa (synWa (synW3a (.classMem X V) (synWss X (synCnnc)) (synWne X (synC0)))
          (.neg (synWrex z X
              (synWral y X (synWbr (.cv z) (synCkqrel (synClefin)) (.cv y))))))
        (.classMem (.cv t) X))
      (synCnnc) (synCdif (synCvv) (synCima (synCkqrel (synClefin)) X)) (.cv t) p0140
      p0013
  have p0149 := @gEldif (.cv t) (synCvv) (synCima (synCkqrel (synClefin)) X)
  have p0150 :=
    @gA1i
      (synWb (.classMem (.cv t) (synCdif (synCvv) (synCima (synCkqrel (synClefin)) X)))
        (synWa (.classMem (.cv t) (synCvv))
          (.neg (.classMem (.cv t) (synCima (synCkqrel (synClefin)) X)))))
      (synWa (synWa (synW3a (.classMem X V) (synWss X (synCnnc)) (synWne X (synC0)))
          (.neg (synWrex z X
              (synWral y X (synWbr (.cv z) (synCkqrel (synClefin)) (.cv y))))))
        (.classMem (.cv t) X))
      p0149
  have p0151 :=
    @gMpbid
      (synWa (synWa (synW3a (.classMem X V) (synWss X (synCnnc)) (synWne X (synC0)))
          (.neg (synWrex z X
              (synWral y X (synWbr (.cv z) (synCkqrel (synClefin)) (.cv y))))))
        (.classMem (.cv t) X))
      (.classMem (.cv t) (synCdif (synCvv) (synCima (synCkqrel (synClefin)) X)))
      (synWa (.classMem (.cv t) (synCvv))
        (.neg (.classMem (.cv t) (synCima (synCkqrel (synClefin)) X))))
      p0148 p0150
  have p0152 :=
    @gSimpr (.classMem (.cv t) (synCvv))
      (.neg (.classMem (.cv t) (synCima (synCkqrel (synClefin)) X)))
  have p0153 :=
    @gSyl
      (synWa (synWa (synW3a (.classMem X V) (synWss X (synCnnc)) (synWne X (synC0)))
          (.neg (synWrex z X
              (synWral y X (synWbr (.cv z) (synCkqrel (synClefin)) (.cv y))))))
        (.classMem (.cv t) X))
      (synWa (.classMem (.cv t) (synCvv))
        (.neg (.classMem (.cv t) (synCima (synCkqrel (synClefin)) X))))
      (.neg (.classMem (.cv t) (synCima (synCkqrel (synClefin)) X))) p0151 p0152
  have p0154 :=
    @gPm221d
      (synWa (synWa (synW3a (.classMem X V) (synWss X (synCnnc)) (synWne X (synC0)))
          (.neg (synWrex z X
              (synWral y X (synWbr (.cv z) (synCkqrel (synClefin)) (.cv y))))))
        (.classMem (.cv t) X))
      (.classMem (.cv t) (synCima (synCkqrel (synClefin)) X))
      (synWrex z X (synWral y X (synWbr (.cv z) (synCkqrel (synClefin)) (.cv y))))
      p0153
  have p0155 :=
    @gMpd
      (synWa (synWa (synW3a (.classMem X V) (synWss X (synCnnc)) (synWne X (synC0)))
          (.neg (synWrex z X
              (synWral y X (synWbr (.cv z) (synCkqrel (synClefin)) (.cv y))))))
        (.classMem (.cv t) X))
      (.classMem (.cv t) (synCima (synCkqrel (synClefin)) X))
      (synWrex z X (synWral y X (synWbr (.cv z) (synCkqrel (synClefin)) (.cv y))))
      p0046 p0154
  have p0156 :=
    @gEx
      (synWa (synW3a (.classMem X V) (synWss X (synCnnc)) (synWne X (synC0))) (.neg
          (synWrex z X (synWral y X (synWbr (.cv z) (synCkqrel (synClefin)) (.cv y))))))
      (.classMem (.cv t) X)
      (synWrex z X (synWral y X (synWbr (.cv z) (synCkqrel (synClefin)) (.cv y))))
      p0155
  have p0157 :=
    @gExlimdv
      (synWa (synW3a (.classMem X V) (synWss X (synCnnc)) (synWne X (synC0))) (.neg
          (synWrex z X (synWral y X (synWbr (.cv z) (synCkqrel (synClefin)) (.cv y))))))
      (.classMem (.cv t) X)
      (synWrex z X (synWral y X (synWbr (.cv z) (synCkqrel (synClefin)) (.cv y)))) t
      dv_cache_0023 dv_cache_0024 p0156
  have p0158 :=
    @gMpd
      (synWa (synW3a (.classMem X V) (synWss X (synCnnc)) (synWne X (synC0))) (.neg
          (synWrex z X (synWral y X (synWbr (.cv z) (synCkqrel (synClefin)) (.cv y))))))
      (synWex t (.classMem (.cv t) X))
      (synWrex z X (synWral y X (synWbr (.cv z) (synCkqrel (synClefin)) (.cv y))))
      p0005 p0157
  have p0159 :=
    @gEx (synW3a (.classMem X V) (synWss X (synCnnc)) (synWne X (synC0)))
      (.neg (synWrex z X (synWral y X (synWbr (.cv z) (synCkqrel (synClefin)) (.cv y)))))
      (synWrex z X (synWral y X (synWbr (.cv z) (synCkqrel (synClefin)) (.cv y))))
      p0158
  have p0160 :=
    @gPm218d (synW3a (.classMem X V) (synWss X (synCnnc)) (synWne X (synC0)))
      (synWrex z X (synWral y X (synWbr (.cv z) (synCkqrel (synClefin)) (.cv y))))
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

/-- Checked nominal proof certificate identified upstream as `g_finlefr`. -/
@[expose]
noncomputable def gFinlefr :
    Nominal.NPrf (synWbr (synCkqrel (synClefin)) (synCfound) (synCnnc)) :=
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
  have dv_cache_0001 : v ∉ ((synCvv)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0002 : w ∉ ((synCvv)).fv :=
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
  have dv_cache_0007 : v ∉ ((synWbr (.cv w) (synCkqrel (synClefin)) (.cv y))).fv :=
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
      ((synWa (synWa (synWa synWtru
              (synWa (synWss (.cv x) (synCnnc)) (synWne (.cv x) (synC0))))
            (.classMem (.cv w) (.cv x)))
          (synWral v (.cv x) (synWbr (.cv w) (synCkqrel (synClefin)) (.cv v))))).fv :=
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
      ((synWral y (.cv x) (.imp (synWbr (.cv y) (synCkqrel (synClefin)) (.cv w))
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
      ((synWrex z (.cv x) (synWral y (.cv x)
            (.imp (synWbr (.cv y) (synCkqrel (synClefin)) (.cv z))
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
      ((synWa synWtru (synWa (synWss (.cv x) (synCnnc)) (synWne (.cv x) (synC0))))).fv :=
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
  have dv_cache_0015 : x ∉ ((synCnnc)).fv :=
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
  have dv_cache_0016 : y ∉ ((synCnnc)).fv :=
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
  have dv_cache_0017 : z ∉ ((synCnnc)).fv :=
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
  have dv_cache_0018 : x ∉ ((synCkqrel (synClefin))).fv :=
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
  have dv_cache_0019 : y ∉ ((synCkqrel (synClefin))).fv :=
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
  have dv_cache_0020 : z ∉ ((synCkqrel (synClefin))).fv :=
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
  have dv_cache_0021 : x ∉ (synWtru).fv :=
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
  have p0000 := @gTru
  have p0001 := @gLefinex
  have p0002 := @gKqrelex (synClefin) p0001
  have p0003 := @gA1i (.classMem (synCkqrel (synClefin)) (synCvv)) synWtru p0002
  have p0004 := @gNncex
  have p0005 := @gA1i (.classMem (synCnnc) (synCvv)) synWtru p0004
  have p0006 := @gVex x
  have p0007 :=
    @gA1i (.classMem (.cv x) (synCvv))
      (synWa synWtru (synWa (synWss (.cv x) (synCnnc)) (synWne (.cv x) (synC0))))
      p0006
  have p0008 :=
    @gSimpr synWtru (synWa (synWss (.cv x) (synCnnc)) (synWne (.cv x) (synC0)))
  have p0009 := @gSimpl (synWss (.cv x) (synCnnc)) (synWne (.cv x) (synC0))
  have p0010 :=
    @gSyl
      (synWa synWtru (synWa (synWss (.cv x) (synCnnc)) (synWne (.cv x) (synC0))))
      (synWa (synWss (.cv x) (synCnnc)) (synWne (.cv x) (synC0)))
      (synWss (.cv x) (synCnnc)) p0008 p0009
  have p0011 :=
    @gSimpr synWtru (synWa (synWss (.cv x) (synCnnc)) (synWne (.cv x) (synC0)))
  have p0012 := @gSimpr (synWss (.cv x) (synCnnc)) (synWne (.cv x) (synC0))
  have p0013 :=
    @gSyl
      (synWa synWtru (synWa (synWss (.cv x) (synCnnc)) (synWne (.cv x) (synC0))))
      (synWa (synWss (.cv x) (synCnnc)) (synWne (.cv x) (synC0)))
      (synWne (.cv x) (synC0)) p0011 p0012
  have p0014 :=
    @gN3jca
      (synWa synWtru (synWa (synWss (.cv x) (synCnnc)) (synWne (.cv x) (synC0))))
      (.classMem (.cv x) (synCvv)) (synWss (.cv x) (synCnnc))
      (synWne (.cv x) (synC0)) p0007 p0010 p0013
  have p0015 :=
    @gFinleastnn v w (synCvv) (.cv x) dv_cache_0001 dv_cache_0002 dv_cache_0003
      dv_cache_0004 dv_cache_0005
  have p0016 :=
    @gSyl
      (synWa synWtru (synWa (synWss (.cv x) (synCnnc)) (synWne (.cv x) (synC0))))
      (synW3a (.classMem (.cv x) (synCvv)) (synWss (.cv x) (synCnnc))
        (synWne (.cv x) (synC0)))
      (synWrex w (.cv x)
        (synWral v (.cv x) (synWbr (.cv w) (synCkqrel (synClefin)) (.cv v))))
      p0014 p0015
  have p0017 :=
    @gSimpl
      (synWa (synWa synWtru (synWa (synWss (.cv x) (synCnnc)) (synWne (.cv x) (synC0))))
        (.classMem (.cv w) (.cv x)))
      (synWral v (.cv x) (synWbr (.cv w) (synCkqrel (synClefin)) (.cv v)))
  have p0018 :=
    @gSimpr
      (synWa synWtru (synWa (synWss (.cv x) (synCnnc)) (synWne (.cv x) (synC0))))
      (.classMem (.cv w) (.cv x))
  have p0019 :=
    @gSyl
      (synWa (synWa (synWa synWtru
            (synWa (synWss (.cv x) (synCnnc)) (synWne (.cv x) (synC0))))
          (.classMem (.cv w) (.cv x)))
        (synWral v (.cv x) (synWbr (.cv w) (synCkqrel (synClefin)) (.cv v))))
      (synWa (synWa synWtru (synWa (synWss (.cv x) (synCnnc)) (synWne (.cv x) (synC0))))
        (.classMem (.cv w) (.cv x)))
      (.classMem (.cv w) (.cv x)) p0017 p0018
  have p0020 := @gFinleor
  have p0021 := @gSopc (synCnnc) (synCkqrel (synClefin))
  have p0022 :=
    @gBiimpi (synWbr (synCkqrel (synClefin)) (synCstrict) (synCnnc))
      (synWa (synWbr (synCkqrel (synClefin)) (synCpartial) (synCnnc))
        (synWbr (synCkqrel (synClefin)) (synCconnex) (synCnnc)))
      p0021
  have p0023 := Nominal.mp p0020 p0022
  have p0024 :=
    @gSimpl (synWbr (synCkqrel (synClefin)) (synCpartial) (synCnnc))
      (synWbr (synCkqrel (synClefin)) (synCconnex) (synCnnc))
  have p0025 := Nominal.mp p0023 p0024
  have p0026 := @gPorta (synCnnc) (synCkqrel (synClefin))
  have p0027 :=
    @gBiimpi (synWbr (synCkqrel (synClefin)) (synCpartial) (synCnnc))
      (synW3a (synWbr (synCkqrel (synClefin)) (synCref) (synCnnc))
        (synWbr (synCkqrel (synClefin)) (synCtrans) (synCnnc))
        (synWbr (synCkqrel (synClefin)) (synCantisym) (synCnnc)))
      p0026
  have p0028 := Nominal.mp p0025 p0027
  have p0029 :=
    @gSimp3 (synWbr (synCkqrel (synClefin)) (synCref) (synCnnc))
      (synWbr (synCkqrel (synClefin)) (synCtrans) (synCnnc))
      (synWbr (synCkqrel (synClefin)) (synCantisym) (synCnnc))
  have p0030 := Nominal.mp p0028 p0029
  have p0031 :=
    @gA1i (synWbr (synCkqrel (synClefin)) (synCantisym) (synCnnc))
      (synWa (synWa (synWa (synWa (synWa synWtru
                (synWa (synWss (.cv x) (synCnnc)) (synWne (.cv x) (synC0))))
              (.classMem (.cv w) (.cv x)))
            (synWral v (.cv x) (synWbr (.cv w) (synCkqrel (synClefin)) (.cv v))))
          (.classMem (.cv y) (.cv x))) (synWbr (.cv y) (synCkqrel (synClefin)) (.cv w)))
      p0030
  have p0032 :=
    @gSimpl
      (synWa (synWa (synWa (synWa synWtru
              (synWa (synWss (.cv x) (synCnnc)) (synWne (.cv x) (synC0))))
            (.classMem (.cv w) (.cv x)))
          (synWral v (.cv x) (synWbr (.cv w) (synCkqrel (synClefin)) (.cv v))))
        (.classMem (.cv y) (.cv x)))
      (synWbr (.cv y) (synCkqrel (synClefin)) (.cv w))
  have p0033 :=
    @gSimpl
      (synWa (synWa (synWa synWtru
            (synWa (synWss (.cv x) (synCnnc)) (synWne (.cv x) (synC0))))
          (.classMem (.cv w) (.cv x)))
        (synWral v (.cv x) (synWbr (.cv w) (synCkqrel (synClefin)) (.cv v))))
      (.classMem (.cv y) (.cv x))
  have p0034 :=
    @gSimpl
      (synWa (synWa synWtru (synWa (synWss (.cv x) (synCnnc)) (synWne (.cv x) (synC0))))
        (.classMem (.cv w) (.cv x)))
      (synWral v (.cv x) (synWbr (.cv w) (synCkqrel (synClefin)) (.cv v)))
  have p0035 :=
    @gSimpl
      (synWa synWtru (synWa (synWss (.cv x) (synCnnc)) (synWne (.cv x) (synC0))))
      (.classMem (.cv w) (.cv x))
  have p0036 :=
    @gSimpr synWtru (synWa (synWss (.cv x) (synCnnc)) (synWne (.cv x) (synC0)))
  have p0037 := @gSimpl (synWss (.cv x) (synCnnc)) (synWne (.cv x) (synC0))
  have p0038 :=
    @gSyl
      (synWa synWtru (synWa (synWss (.cv x) (synCnnc)) (synWne (.cv x) (synC0))))
      (synWa (synWss (.cv x) (synCnnc)) (synWne (.cv x) (synC0)))
      (synWss (.cv x) (synCnnc)) p0036 p0037
  have p0039 :=
    @gSyl
      (synWa (synWa synWtru (synWa (synWss (.cv x) (synCnnc)) (synWne (.cv x) (synC0))))
        (.classMem (.cv w) (.cv x)))
      (synWa synWtru (synWa (synWss (.cv x) (synCnnc)) (synWne (.cv x) (synC0))))
      (synWss (.cv x) (synCnnc)) p0035 p0038
  have p0040 :=
    @gSyl
      (synWa (synWa (synWa synWtru
            (synWa (synWss (.cv x) (synCnnc)) (synWne (.cv x) (synC0))))
          (.classMem (.cv w) (.cv x)))
        (synWral v (.cv x) (synWbr (.cv w) (synCkqrel (synClefin)) (.cv v))))
      (synWa (synWa synWtru (synWa (synWss (.cv x) (synCnnc)) (synWne (.cv x) (synC0))))
        (.classMem (.cv w) (.cv x)))
      (synWss (.cv x) (synCnnc)) p0034 p0039
  have p0041 :=
    @gSyl
      (synWa (synWa (synWa (synWa synWtru
              (synWa (synWss (.cv x) (synCnnc)) (synWne (.cv x) (synC0))))
            (.classMem (.cv w) (.cv x)))
          (synWral v (.cv x) (synWbr (.cv w) (synCkqrel (synClefin)) (.cv v))))
        (.classMem (.cv y) (.cv x)))
      (synWa (synWa (synWa synWtru
            (synWa (synWss (.cv x) (synCnnc)) (synWne (.cv x) (synC0))))
          (.classMem (.cv w) (.cv x)))
        (synWral v (.cv x) (synWbr (.cv w) (synCkqrel (synClefin)) (.cv v))))
      (synWss (.cv x) (synCnnc)) p0033 p0040
  have p0042 :=
    @gSimpr
      (synWa (synWa (synWa synWtru
            (synWa (synWss (.cv x) (synCnnc)) (synWne (.cv x) (synC0))))
          (.classMem (.cv w) (.cv x)))
        (synWral v (.cv x) (synWbr (.cv w) (synCkqrel (synClefin)) (.cv v))))
      (.classMem (.cv y) (.cv x))
  have p0043 :=
    @gSseldd
      (synWa (synWa (synWa (synWa synWtru
              (synWa (synWss (.cv x) (synCnnc)) (synWne (.cv x) (synC0))))
            (.classMem (.cv w) (.cv x)))
          (synWral v (.cv x) (synWbr (.cv w) (synCkqrel (synClefin)) (.cv v))))
        (.classMem (.cv y) (.cv x)))
      (.cv x) (synCnnc) (.cv y) p0041 p0042
  have p0044 :=
    @gSyl
      (synWa (synWa (synWa (synWa (synWa synWtru
                (synWa (synWss (.cv x) (synCnnc)) (synWne (.cv x) (synC0))))
              (.classMem (.cv w) (.cv x)))
            (synWral v (.cv x) (synWbr (.cv w) (synCkqrel (synClefin)) (.cv v))))
          (.classMem (.cv y) (.cv x))) (synWbr (.cv y) (synCkqrel (synClefin)) (.cv w)))
      (synWa (synWa (synWa (synWa synWtru
              (synWa (synWss (.cv x) (synCnnc)) (synWne (.cv x) (synC0))))
            (.classMem (.cv w) (.cv x)))
          (synWral v (.cv x) (synWbr (.cv w) (synCkqrel (synClefin)) (.cv v))))
        (.classMem (.cv y) (.cv x)))
      (.classMem (.cv y) (synCnnc)) p0032 p0043
  have p0045 :=
    @gSimpl
      (synWa (synWa (synWa (synWa synWtru
              (synWa (synWss (.cv x) (synCnnc)) (synWne (.cv x) (synC0))))
            (.classMem (.cv w) (.cv x)))
          (synWral v (.cv x) (synWbr (.cv w) (synCkqrel (synClefin)) (.cv v))))
        (.classMem (.cv y) (.cv x)))
      (synWbr (.cv y) (synCkqrel (synClefin)) (.cv w))
  have p0046 :=
    @gSimpl
      (synWa (synWa (synWa synWtru
            (synWa (synWss (.cv x) (synCnnc)) (synWne (.cv x) (synC0))))
          (.classMem (.cv w) (.cv x)))
        (synWral v (.cv x) (synWbr (.cv w) (synCkqrel (synClefin)) (.cv v))))
      (.classMem (.cv y) (.cv x))
  have p0047 :=
    @gSimpl
      (synWa (synWa synWtru (synWa (synWss (.cv x) (synCnnc)) (synWne (.cv x) (synC0))))
        (.classMem (.cv w) (.cv x)))
      (synWral v (.cv x) (synWbr (.cv w) (synCkqrel (synClefin)) (.cv v)))
  have p0048 :=
    @gSimpl
      (synWa synWtru (synWa (synWss (.cv x) (synCnnc)) (synWne (.cv x) (synC0))))
      (.classMem (.cv w) (.cv x))
  have p0049 :=
    @gSimpr synWtru (synWa (synWss (.cv x) (synCnnc)) (synWne (.cv x) (synC0)))
  have p0050 := @gSimpl (synWss (.cv x) (synCnnc)) (synWne (.cv x) (synC0))
  have p0051 :=
    @gSyl
      (synWa synWtru (synWa (synWss (.cv x) (synCnnc)) (synWne (.cv x) (synC0))))
      (synWa (synWss (.cv x) (synCnnc)) (synWne (.cv x) (synC0)))
      (synWss (.cv x) (synCnnc)) p0049 p0050
  have p0052 :=
    @gSyl
      (synWa (synWa synWtru (synWa (synWss (.cv x) (synCnnc)) (synWne (.cv x) (synC0))))
        (.classMem (.cv w) (.cv x)))
      (synWa synWtru (synWa (synWss (.cv x) (synCnnc)) (synWne (.cv x) (synC0))))
      (synWss (.cv x) (synCnnc)) p0048 p0051
  have p0053 :=
    @gSimpr
      (synWa synWtru (synWa (synWss (.cv x) (synCnnc)) (synWne (.cv x) (synC0))))
      (.classMem (.cv w) (.cv x))
  have p0054 :=
    @gSseldd
      (synWa (synWa synWtru (synWa (synWss (.cv x) (synCnnc)) (synWne (.cv x) (synC0))))
        (.classMem (.cv w) (.cv x)))
      (.cv x) (synCnnc) (.cv w) p0052 p0053
  have p0055 :=
    @gSyl
      (synWa (synWa (synWa synWtru
            (synWa (synWss (.cv x) (synCnnc)) (synWne (.cv x) (synC0))))
          (.classMem (.cv w) (.cv x)))
        (synWral v (.cv x) (synWbr (.cv w) (synCkqrel (synClefin)) (.cv v))))
      (synWa (synWa synWtru (synWa (synWss (.cv x) (synCnnc)) (synWne (.cv x) (synC0))))
        (.classMem (.cv w) (.cv x)))
      (.classMem (.cv w) (synCnnc)) p0047 p0054
  have p0056 :=
    @gSyl
      (synWa (synWa (synWa (synWa synWtru
              (synWa (synWss (.cv x) (synCnnc)) (synWne (.cv x) (synC0))))
            (.classMem (.cv w) (.cv x)))
          (synWral v (.cv x) (synWbr (.cv w) (synCkqrel (synClefin)) (.cv v))))
        (.classMem (.cv y) (.cv x)))
      (synWa (synWa (synWa synWtru
            (synWa (synWss (.cv x) (synCnnc)) (synWne (.cv x) (synC0))))
          (.classMem (.cv w) (.cv x)))
        (synWral v (.cv x) (synWbr (.cv w) (synCkqrel (synClefin)) (.cv v))))
      (.classMem (.cv w) (synCnnc)) p0046 p0055
  have p0057 :=
    @gSyl
      (synWa (synWa (synWa (synWa (synWa synWtru
                (synWa (synWss (.cv x) (synCnnc)) (synWne (.cv x) (synC0))))
              (.classMem (.cv w) (.cv x)))
            (synWral v (.cv x) (synWbr (.cv w) (synCkqrel (synClefin)) (.cv v))))
          (.classMem (.cv y) (.cv x))) (synWbr (.cv y) (synCkqrel (synClefin)) (.cv w)))
      (synWa (synWa (synWa (synWa synWtru
              (synWa (synWss (.cv x) (synCnnc)) (synWne (.cv x) (synC0))))
            (.classMem (.cv w) (.cv x)))
          (synWral v (.cv x) (synWbr (.cv w) (synCkqrel (synClefin)) (.cv v))))
        (.classMem (.cv y) (.cv x)))
      (.classMem (.cv w) (synCnnc)) p0045 p0056
  have p0058 :=
    @gSimpr
      (synWa (synWa (synWa (synWa synWtru
              (synWa (synWss (.cv x) (synCnnc)) (synWne (.cv x) (synC0))))
            (.classMem (.cv w) (.cv x)))
          (synWral v (.cv x) (synWbr (.cv w) (synCkqrel (synClefin)) (.cv v))))
        (.classMem (.cv y) (.cv x)))
      (synWbr (.cv y) (synCkqrel (synClefin)) (.cv w))
  have p0059 :=
    @gSimpl
      (synWa (synWa (synWa (synWa synWtru
              (synWa (synWss (.cv x) (synCnnc)) (synWne (.cv x) (synC0))))
            (.classMem (.cv w) (.cv x)))
          (synWral v (.cv x) (synWbr (.cv w) (synCkqrel (synClefin)) (.cv v))))
        (.classMem (.cv y) (.cv x)))
      (synWbr (.cv y) (synCkqrel (synClefin)) (.cv w))
  have p0060 :=
    @gSimpl
      (synWa (synWa (synWa synWtru
            (synWa (synWss (.cv x) (synCnnc)) (synWne (.cv x) (synC0))))
          (.classMem (.cv w) (.cv x)))
        (synWral v (.cv x) (synWbr (.cv w) (synCkqrel (synClefin)) (.cv v))))
      (.classMem (.cv y) (.cv x))
  have p0061 :=
    @gSimpr
      (synWa (synWa synWtru (synWa (synWss (.cv x) (synCnnc)) (synWne (.cv x) (synC0))))
        (.classMem (.cv w) (.cv x)))
      (synWral v (.cv x) (synWbr (.cv w) (synCkqrel (synClefin)) (.cv v)))
  have p0062 :=
    @gSyl
      (synWa (synWa (synWa (synWa synWtru
              (synWa (synWss (.cv x) (synCnnc)) (synWne (.cv x) (synC0))))
            (.classMem (.cv w) (.cv x)))
          (synWral v (.cv x) (synWbr (.cv w) (synCkqrel (synClefin)) (.cv v))))
        (.classMem (.cv y) (.cv x)))
      (synWa (synWa (synWa synWtru
            (synWa (synWss (.cv x) (synCnnc)) (synWne (.cv x) (synC0))))
          (.classMem (.cv w) (.cv x)))
        (synWral v (.cv x) (synWbr (.cv w) (synCkqrel (synClefin)) (.cv v))))
      (synWral v (.cv x) (synWbr (.cv w) (synCkqrel (synClefin)) (.cv v))) p0060 p0061
  have p0063 :=
    @gSimpr
      (synWa (synWa (synWa synWtru
            (synWa (synWss (.cv x) (synCnnc)) (synWne (.cv x) (synC0))))
          (.classMem (.cv w) (.cv x)))
        (synWral v (.cv x) (synWbr (.cv w) (synCkqrel (synClefin)) (.cv v))))
      (.classMem (.cv y) (.cv x))
  have p0064 :=
    @gJca
      (synWa (synWa (synWa (synWa synWtru
              (synWa (synWss (.cv x) (synCnnc)) (synWne (.cv x) (synC0))))
            (.classMem (.cv w) (.cv x)))
          (synWral v (.cv x) (synWbr (.cv w) (synCkqrel (synClefin)) (.cv v))))
        (.classMem (.cv y) (.cv x)))
      (synWral v (.cv x) (synWbr (.cv w) (synCkqrel (synClefin)) (.cv v)))
      (.classMem (.cv y) (.cv x)) p0062 p0063
  have p0065 := @gBreq2 (.cv v) (.cv y) (.cv w) (synCkqrel (synClefin))
  have p0066 :=
    @gRspccva (synWbr (.cv w) (synCkqrel (synClefin)) (.cv v))
      (synWbr (.cv w) (synCkqrel (synClefin)) (.cv y)) v (.cv y) (.cv x) dv_cache_0006
      dv_cache_0003 dv_cache_0007 p0065
  have p0067 :=
    @gSyl
      (synWa (synWa (synWa (synWa synWtru
              (synWa (synWss (.cv x) (synCnnc)) (synWne (.cv x) (synC0))))
            (.classMem (.cv w) (.cv x)))
          (synWral v (.cv x) (synWbr (.cv w) (synCkqrel (synClefin)) (.cv v))))
        (.classMem (.cv y) (.cv x)))
      (synWa (synWral v (.cv x) (synWbr (.cv w) (synCkqrel (synClefin)) (.cv v)))
        (.classMem (.cv y) (.cv x)))
      (synWbr (.cv w) (synCkqrel (synClefin)) (.cv y)) p0064 p0066
  have p0068 :=
    @gSyl
      (synWa (synWa (synWa (synWa (synWa synWtru
                (synWa (synWss (.cv x) (synCnnc)) (synWne (.cv x) (synC0))))
              (.classMem (.cv w) (.cv x)))
            (synWral v (.cv x) (synWbr (.cv w) (synCkqrel (synClefin)) (.cv v))))
          (.classMem (.cv y) (.cv x))) (synWbr (.cv y) (synCkqrel (synClefin)) (.cv w)))
      (synWa (synWa (synWa (synWa synWtru
              (synWa (synWss (.cv x) (synCnnc)) (synWne (.cv x) (synC0))))
            (.classMem (.cv w) (.cv x)))
          (synWral v (.cv x) (synWbr (.cv w) (synCkqrel (synClefin)) (.cv v))))
        (.classMem (.cv y) (.cv x)))
      (synWbr (.cv w) (synCkqrel (synClefin)) (.cv y)) p0059 p0067
  have p0069 :=
    @gAntid
      (synWa (synWa (synWa (synWa (synWa synWtru
                (synWa (synWss (.cv x) (synCnnc)) (synWne (.cv x) (synC0))))
              (.classMem (.cv w) (.cv x)))
            (synWral v (.cv x) (synWbr (.cv w) (synCkqrel (synClefin)) (.cv v))))
          (.classMem (.cv y) (.cv x))) (synWbr (.cv y) (synCkqrel (synClefin)) (.cv w)))
      (synCnnc) (synCkqrel (synClefin)) (.cv y) (.cv w) p0031 p0044 p0057 p0058 p0068
  have p0070 :=
    @gEx
      (synWa (synWa (synWa (synWa synWtru
              (synWa (synWss (.cv x) (synCnnc)) (synWne (.cv x) (synC0))))
            (.classMem (.cv w) (.cv x)))
          (synWral v (.cv x) (synWbr (.cv w) (synCkqrel (synClefin)) (.cv v))))
        (.classMem (.cv y) (.cv x)))
      (synWbr (.cv y) (synCkqrel (synClefin)) (.cv w)) (.classEq (.cv y) (.cv w)) p0069
  have p0071 :=
    @gRalrimiva
      (synWa (synWa (synWa synWtru
            (synWa (synWss (.cv x) (synCnnc)) (synWne (.cv x) (synC0))))
          (.classMem (.cv w) (.cv x)))
        (synWral v (.cv x) (synWbr (.cv w) (synCkqrel (synClefin)) (.cv v))))
      (.imp (synWbr (.cv y) (synCkqrel (synClefin)) (.cv w)) (.classEq (.cv y) (.cv w)))
      y (.cv x) dv_cache_0008 p0070
  have p0072 :=
    @gJca
      (synWa (synWa (synWa synWtru
            (synWa (synWss (.cv x) (synCnnc)) (synWne (.cv x) (synC0))))
          (.classMem (.cv w) (.cv x)))
        (synWral v (.cv x) (synWbr (.cv w) (synCkqrel (synClefin)) (.cv v))))
      (.classMem (.cv w) (.cv x))
      (synWral y (.cv x) (.imp (synWbr (.cv y) (synCkqrel (synClefin)) (.cv w))
          (.classEq (.cv y) (.cv w))))
      p0019 p0071
  have p0073 := @gBreq2 (.cv z) (.cv w) (.cv y) (synCkqrel (synClefin))
  have p0074 := @gEqeq2 (.cv z) (.cv w) (.cv y)
  have p0075 :=
    @gImbi12d (.classEq (.cv z) (.cv w))
      (synWbr (.cv y) (synCkqrel (synClefin)) (.cv z))
      (synWbr (.cv y) (synCkqrel (synClefin)) (.cv w)) (.classEq (.cv y) (.cv z))
      (.classEq (.cv y) (.cv w)) p0073 p0074
  have p0076 :=
    @gRalbidv (.classEq (.cv z) (.cv w))
      (.imp (synWbr (.cv y) (synCkqrel (synClefin)) (.cv z)) (.classEq (.cv y) (.cv z)))
      (.imp (synWbr (.cv y) (synCkqrel (synClefin)) (.cv w)) (.classEq (.cv y) (.cv w)))
      y (.cv x) dv_cache_0009 p0075
  have p0077 :=
    @gRspcev
      (synWral y (.cv x) (.imp (synWbr (.cv y) (synCkqrel (synClefin)) (.cv z))
          (.classEq (.cv y) (.cv z))))
      (synWral y (.cv x) (.imp (synWbr (.cv y) (synCkqrel (synClefin)) (.cv w))
          (.classEq (.cv y) (.cv w))))
      z (.cv w) (.cv x) dv_cache_0010 dv_cache_0011 dv_cache_0012 p0076
  have p0078 :=
    @gSyl
      (synWa (synWa (synWa synWtru
            (synWa (synWss (.cv x) (synCnnc)) (synWne (.cv x) (synC0))))
          (.classMem (.cv w) (.cv x)))
        (synWral v (.cv x) (synWbr (.cv w) (synCkqrel (synClefin)) (.cv v))))
      (synWa (.classMem (.cv w) (.cv x)) (synWral y (.cv x)
          (.imp (synWbr (.cv y) (synCkqrel (synClefin)) (.cv w))
            (.classEq (.cv y) (.cv w)))))
      (synWrex z (.cv x) (synWral y (.cv x)
          (.imp (synWbr (.cv y) (synCkqrel (synClefin)) (.cv z))
            (.classEq (.cv y) (.cv z)))))
      p0072 p0077
  have p0079 :=
    @gEx
      (synWa (synWa synWtru (synWa (synWss (.cv x) (synCnnc)) (synWne (.cv x) (synC0))))
        (.classMem (.cv w) (.cv x)))
      (synWral v (.cv x) (synWbr (.cv w) (synCkqrel (synClefin)) (.cv v)))
      (synWrex z (.cv x) (synWral y (.cv x)
          (.imp (synWbr (.cv y) (synCkqrel (synClefin)) (.cv z))
            (.classEq (.cv y) (.cv z)))))
      p0078
  have p0080 :=
    @gRexlimdva
      (synWa synWtru (synWa (synWss (.cv x) (synCnnc)) (synWne (.cv x) (synC0))))
      (synWral v (.cv x) (synWbr (.cv w) (synCkqrel (synClefin)) (.cv v)))
      (synWrex z (.cv x) (synWral y (.cv x)
          (.imp (synWbr (.cv y) (synCkqrel (synClefin)) (.cv z))
            (.classEq (.cv y) (.cv z)))))
      w (.cv x) dv_cache_0013 dv_cache_0014 p0079
  have p0081 :=
    @gMpd
      (synWa synWtru (synWa (synWss (.cv x) (synCnnc)) (synWne (.cv x) (synC0))))
      (synWrex w (.cv x)
        (synWral v (.cv x) (synWbr (.cv w) (synCkqrel (synClefin)) (.cv v))))
      (synWrex z (.cv x) (synWral y (.cv x)
          (.imp (synWbr (.cv y) (synCkqrel (synClefin)) (.cv z))
            (.classEq (.cv y) (.cv z)))))
      p0016 p0080
  have p0082_e02_recanon :
    Nominal.NPrf
      (.imp (synWa synWtru (synWa (synWss (.cv x) (synCnnc)) (synWne (.cv x) (synC0))))
        (synWrex z (.cv x) (synWral y (.cv x)
            (.imp (synWbr (.cv y) (synCkqrel (synClefin)) (.cv z)) (.objEq y z))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWa synWtru synWrex synWex synWral synWbr synCop synCun synCnin
          synWnan synCcompl synCkqrel synCopab synCopk synCpr synCsn synClefin
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
    @gFrrd synWtru x y z (synCnnc) (synCkqrel (synClefin)) dv_cache_0015
      dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
      dv_cache_0022 dv_cache_0023 dv_cache_0024 p0003 p0005 p0082_e02_recanon
  have p0083 := Nominal.mp p0000 p0082
  exact p0083

/-- Checked nominal proof certificate identified upstream as `g_finlewe`. -/
@[expose]
noncomputable def gFinlewe :
    Nominal.NPrf (synWbr (synCkqrel (synClefin)) (synCwe) (synCnnc)) :=
  by
  have p0000 := @gTru
  have p0001 := @gFinleor
  have p0002 :=
    @gA1i (synWbr (synCkqrel (synClefin)) (synCstrict) (synCnnc)) synWtru p0001
  have p0003 := @gFinlefr
  have p0004 :=
    @gA1i (synWbr (synCkqrel (synClefin)) (synCfound) (synCnnc)) synWtru p0003
  have p0005 :=
    @gJca synWtru (synWbr (synCkqrel (synClefin)) (synCstrict) (synCnnc))
      (synWbr (synCkqrel (synClefin)) (synCfound) (synCnnc)) p0002 p0004
  have p0006 := Nominal.mp p0000 p0005
  have p0007 := (Nominal.classEqRefl (synCwe))
  have p0008 :=
    @gBreqi (synCkqrel (synClefin)) (synCnnc) (synCwe)
      (synCin (synCstrict) (synCfound)) p0007
  have p0009 := @gBrin (synCkqrel (synClefin)) (synCnnc) (synCstrict) (synCfound)
  have p0010 :=
    @gBitri (synWbr (synCkqrel (synClefin)) (synCwe) (synCnnc))
      (synWbr (synCkqrel (synClefin)) (synCin (synCstrict) (synCfound)) (synCnnc))
      (synWa (synWbr (synCkqrel (synClefin)) (synCstrict) (synCnnc))
        (synWbr (synCkqrel (synClefin)) (synCfound) (synCnnc)))
      p0008 p0009
  have p0011 :=
    @gMpbir (synWbr (synCkqrel (synClefin)) (synCwe) (synCnnc))
      (synWa (synWbr (synCkqrel (synClefin)) (synCstrict) (synCnnc))
        (synWbr (synCkqrel (synClefin)) (synCfound) (synCnnc)))
      p0006 p0010
  exact p0011

/-- Checked nominal proof certificate identified upstream as `g_wpporbit0`. -/
@[expose]
noncomputable def gWpporbit0 (F : Class) (I : Class) (_dv_F_I : Disjoint F.fv I.fv) :
    Nominal.NPrf
      (.imp (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
          (synWss (synCrn F) (synCdm F)))
        (.classEq (synCfv (synCfrec F I) (synC0c)) I)) :=
  by
  have p0000 := @gEqid (synCfrec F I)
  have p0001 :=
    @gSimp1 (.classMem F (synCfuns)) (.classMem I (synCdm F))
      (synWss (synCrn F) (synCdm F))
  have p0002 :=
    @gSimp2 (.classMem F (synCfuns)) (.classMem I (synCdm F))
      (synWss (synCrn F) (synCdm F))
  have p0003 :=
    @gSimp3 (.classMem F (synCfuns)) (.classMem I (synCdm F))
      (synWss (synCrn F) (synCdm F))
  have p0004 :=
    @gFrec0
      (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
        (synWss (synCrn F) (synCdm F)))
      (synCfrec F I) F I p0000 p0001 p0002 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_wpporbitsuc`. -/
@[expose]
noncomputable def gWpporbitsuc (F : Class) (I : Class) (N : Class)
    (_dv_F_I : Disjoint F.fv I.fv) (_dv_F_N : Disjoint F.fv N.fv)
    (_dv_I_N : Disjoint I.fv N.fv) :
    Nominal.NPrf
      (.imp (synWa (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
            (synWss (synCrn F) (synCdm F))) (.classMem N (synCnnc)))
        (.classEq (synCfv (synCfrec F I) (synCplc N (synC1c)))
          (synCfv F (synCfv (synCfrec F I) N)))) :=
  by
  have p0000 := @gEqid (synCfrec F I)
  have p0001 :=
    @gSimpl
      (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
        (synWss (synCrn F) (synCdm F)))
      (.classMem N (synCnnc))
  have p0002 :=
    @gSimp1 (.classMem F (synCfuns)) (.classMem I (synCdm F))
      (synWss (synCrn F) (synCdm F))
  have p0003 :=
    @gSyl
      (synWa (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
          (synWss (synCrn F) (synCdm F))) (.classMem N (synCnnc)))
      (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
        (synWss (synCrn F) (synCdm F)))
      (.classMem F (synCfuns)) p0001 p0002
  have p0005 :=
    @gSimp2 (.classMem F (synCfuns)) (.classMem I (synCdm F))
      (synWss (synCrn F) (synCdm F))
  have p0006 :=
    @gSyl
      (synWa (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
          (synWss (synCrn F) (synCdm F))) (.classMem N (synCnnc)))
      (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
        (synWss (synCrn F) (synCdm F)))
      (.classMem I (synCdm F)) p0001 p0005
  have p0008 :=
    @gSimp3 (.classMem F (synCfuns)) (.classMem I (synCdm F))
      (synWss (synCrn F) (synCdm F))
  have p0009 :=
    @gSyl
      (synWa (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
          (synWss (synCrn F) (synCdm F))) (.classMem N (synCnnc)))
      (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
        (synWss (synCrn F) (synCdm F)))
      (synWss (synCrn F) (synCdm F)) p0001 p0008
  have p0010 :=
    @gSimpr
      (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
        (synWss (synCrn F) (synCdm F)))
      (.classMem N (synCnnc))
  have p0011 :=
    @gFrecsuc
      (synWa (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
          (synWss (synCrn F) (synCdm F))) (.classMem N (synCnnc)))
      (synCfrec F I) F I N p0000 p0003 p0006 p0009 p0010
  exact p0011

/-- Checked nominal proof certificate identified upstream as `g_kqfinsucnle`. -/
@[expose]
noncomputable def gKqfinsucnle (A : Class) :
    Nominal.NPrf
      (.imp (.classMem A (synCnnc))
        (.neg (synWbr (synCplc A (synC1c)) (synCkqrel (synClefin)) A))) :=
  by
  have p0000 := @gElex A (synCnnc)
  have p0001 := @gId (.classMem A (synCnnc))
  have p0002 := @gNulnnn
  have p0003 :=
    @gA1i (.neg (.classMem (synC0) (synCnnc))) (.classMem A (synCnnc)) p0002
  have p0004 :=
    @gJca (.classMem A (synCnnc)) (.classMem A (synCnnc))
      (.neg (.classMem (synC0) (synCnnc))) p0001 p0003
  have p0005 := @gNelne2 A (synC0) (synCnnc)
  have p0006 :=
    @gSyl (.classMem A (synCnnc))
      (synWa (.classMem A (synCnnc)) (.neg (.classMem (synC0) (synCnnc))))
      (synWne A (synC0)) p0004 p0005
  have p0007 :=
    @gJca (.classMem A (synCnnc)) (.classMem A (synCvv)) (synWne A (synC0)) p0000
      p0006
  have p0008 := @gLtfinp1 A (synCvv)
  have p0009 :=
    @gSyl (.classMem A (synCnnc)) (synWa (.classMem A (synCvv)) (synWne A (synC0)))
      (.classMem (synCopk A (synCplc A (synC1c))) (synCltfin)) p0007 p0008
  have p0010 := @gNotnot1 (.classMem (synCopk A (synCplc A (synC1c))) (synCltfin))
  have p0011 :=
    @gSyl (.classMem A (synCnnc))
      (.classMem (synCopk A (synCplc A (synC1c))) (synCltfin))
      (.neg (.neg (.classMem (synCopk A (synCplc A (synC1c))) (synCltfin)))) p0009
      p0010
  have p0012 := @gPeano2 A
  have p0014 :=
    @gJca (.classMem A (synCnnc)) (.classMem (synCplc A (synC1c)) (synCnnc))
      (.classMem A (synCnnc)) p0012 p0001
  have p0015 := @gLenltfin (synCplc A (synC1c)) A
  have p0016 :=
    @gSyl (.classMem A (synCnnc))
      (synWa (.classMem (synCplc A (synC1c)) (synCnnc)) (.classMem A (synCnnc)))
      (synWb (.classMem (synCopk (synCplc A (synC1c)) A) (synClefin))
        (.neg (.classMem (synCopk A (synCplc A (synC1c))) (synCltfin))))
      p0014 p0015
  have p0017 :=
    @gMtbird (.classMem A (synCnnc))
      (.classMem (synCopk (synCplc A (synC1c)) A) (synClefin))
      (.neg (.classMem (synCopk A (synCplc A (synC1c))) (synCltfin))) p0011 p0016
  have p0019 := @gElex (synCplc A (synC1c)) (synCnnc)
  have p0020 :=
    @gSyl (.classMem A (synCnnc)) (.classMem (synCplc A (synC1c)) (synCnnc))
      (.classMem (synCplc A (synC1c)) (synCvv)) p0012 p0019
  have p0022 :=
    @gJca (.classMem A (synCnnc)) (.classMem (synCplc A (synC1c)) (synCvv))
      (.classMem A (synCvv)) p0020 p0000
  have p0023 := @gKqlefinbr (synCplc A (synC1c)) A (synCvv) (synCvv)
  have p0024 :=
    @gSyl (.classMem A (synCnnc))
      (synWa (.classMem (synCplc A (synC1c)) (synCvv)) (.classMem A (synCvv)))
      (synWb (synWbr (synCplc A (synC1c)) (synCkqrel (synClefin)) A)
        (.classMem (synCopk (synCplc A (synC1c)) A) (synClefin)))
      p0022 p0023
  have p0025 :=
    @gMtbird (.classMem A (synCnnc))
      (synWbr (synCplc A (synC1c)) (synCkqrel (synClefin)) A)
      (.classMem (synCopk (synCplc A (synC1c)) A) (synClefin)) p0017 p0024
  exact p0025


end NFChoice.DirectNominalPrf.WPPReplay

end
