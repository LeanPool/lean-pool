/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NominalWPPReplayChunk009StructuralBlock008

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NominalWPPReplayChunk009StructuralPart044`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_ltfintri (M : Class) (N : Class) :
    Nominal.NPrf
      (.imp (syn_w3a (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)) (syn_wne M (syn_c0)))
        (syn_w3o (.classMem (syn_copk M N) (syn_cltfin)) (.classEq M N)
          (.classMem (syn_copk N M) (syn_cltfin)))) :=
  by
  let proofSupport : Finset Var := M.fv ∪ N.fv
  let n : Var := freshVar proofSupport 0
  let k : Var := freshVar proofSupport 1
  let m : Var := freshVar proofSupport 2
  let p : Var := freshVar proofSupport 3
  have fresh_n : n ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_n_not_M : n ∉ M.fv := by
    intro h
    exact fresh_n (Finset.mem_union_left _ (h))
  have fresh_n_not_N : n ∉ N.fv := by
    intro h
    exact fresh_n (Finset.mem_union_right _ (h))
  have fresh_k : k ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_k_not_M : k ∉ M.fv := by
    intro h
    exact fresh_k (Finset.mem_union_left _ (h))
  have fresh_n_ne_k : n ≠ k :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_k_ne_n : k ≠ n := Ne.symm fresh_n_ne_k
  have fresh_n_ne_m : n ≠ m :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_m_ne_n : m ≠ n := Ne.symm fresh_n_ne_m
  have fresh_n_ne_p : n ≠ p :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_p_ne_n : p ≠ n := Ne.symm fresh_n_ne_p
  have fresh_k_ne_m : k ≠ m :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_m_ne_k : m ≠ k := Ne.symm fresh_k_ne_m
  have fresh_m_ne_p : m ≠ p :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_p_ne_m : p ≠ m := Ne.symm fresh_m_ne_p
  have p0000 := @g_opkeq2 (.cv n) N M
  have p0001 :=
    @g_eleq1d (.classEq (.cv n) N) (syn_copk M (.cv n)) (syn_copk M N) (syn_cltfin) p0000
  have p0002 := @g_eqeq2 (.cv n) N M
  have p0003 := @g_opkeq1 (.cv n) N M
  have p0004 :=
    @g_eleq1d (.classEq (.cv n) N) (syn_copk (.cv n) M) (syn_copk N M) (syn_cltfin) p0003
  have p0005 :=
    @g_n_3orbi123d (.classEq (.cv n) N) (.classMem (syn_copk M (.cv n)) (syn_cltfin))
      (.classMem (syn_copk M N) (syn_cltfin)) (.classEq M (.cv n)) (.classEq M N)
      (.classMem (syn_copk (.cv n) M) (syn_cltfin))
      (.classMem (syn_copk N M) (syn_cltfin)) p0001 p0002 p0004
  have p0006 :=
    @g_imbi2d (.classEq (.cv n) N)
      (syn_w3o (.classMem (syn_copk M (.cv n)) (syn_cltfin)) (.classEq M (.cv n))
        (.classMem (syn_copk (.cv n) M) (syn_cltfin)))
      (syn_w3o (.classMem (syn_copk M N) (syn_cltfin)) (.classEq M N)
        (.classMem (syn_copk N M) (syn_cltfin)))
      (syn_wne M (syn_c0)) p0005
  have p0007 :=
    @g_imbi2d (.classEq (.cv n) N)
      (.imp (syn_wne M (syn_c0))
        (syn_w3o (.classMem (syn_copk M (.cv n)) (syn_cltfin)) (.classEq M (.cv n))
          (.classMem (syn_copk (.cv n) M) (syn_cltfin))))
      (.imp (syn_wne M (syn_c0)) (syn_w3o (.classMem (syn_copk M N) (syn_cltfin)) (.classEq M N)
          (.classMem (syn_copk N M) (syn_cltfin))))
      (.classMem M (syn_cnnc)) p0006
  have p0008 := @g_ltfintrilem1 k n (show k ≠ n from (by exact fresh_k_ne_n))
  have p0009 := @g_neeq1 (.cv k) (syn_c0c) (syn_c0)
  have p0010 := @g_opkeq1 (.cv k) (syn_c0c) (.cv n)
  have p0011 :=
    @g_eleq1d (.classEq (.cv k) (syn_c0c)) (syn_copk (.cv k) (.cv n))
      (syn_copk (syn_c0c) (.cv n)) (syn_cltfin) p0010
  have p0012 := @g_eqeq1 (.cv k) (syn_c0c) (.cv n)
  have p0013 := @g_opkeq2 (.cv k) (syn_c0c) (.cv n)
  have p0014 :=
    @g_eleq1d (.classEq (.cv k) (syn_c0c)) (syn_copk (.cv n) (.cv k))
      (syn_copk (.cv n) (syn_c0c)) (syn_cltfin) p0013
  have p0015_e01_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv k) (syn_c0c)) (syn_wb (.objEq k n) (.classEq (syn_c0c) (.cv n)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_c0c syn_csn syn_c0 syn_cdif syn_cin syn_ccompl syn_cnin syn_wnan syn_wa
          syn_cvv syn_wb
        simp (config := { failIfUnchanged := false }) only []
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _)
      p0012
  have p0015 :=
    @g_n_3orbi123d (.classEq (.cv k) (syn_c0c))
      (.classMem (syn_copk (.cv k) (.cv n)) (syn_cltfin))
      (.classMem (syn_copk (syn_c0c) (.cv n)) (syn_cltfin)) (.objEq k n)
      (.classEq (syn_c0c) (.cv n)) (.classMem (syn_copk (.cv n) (.cv k)) (syn_cltfin))
      (.classMem (syn_copk (.cv n) (syn_c0c)) (syn_cltfin)) p0011 p0015_e01_recanon p0014
  have p0016 :=
    @g_imbi12d (.classEq (.cv k) (syn_c0c)) (syn_wne (.cv k) (syn_c0))
      (syn_wne (syn_c0c) (syn_c0))
      (syn_w3o (.classMem (syn_copk (.cv k) (.cv n)) (syn_cltfin)) (.objEq k n)
        (.classMem (syn_copk (.cv n) (.cv k)) (syn_cltfin)))
      (syn_w3o (.classMem (syn_copk (syn_c0c) (.cv n)) (syn_cltfin))
        (.classEq (syn_c0c) (.cv n)) (.classMem (syn_copk (.cv n) (syn_c0c)) (syn_cltfin)))
      p0009 p0015
  have p0017 :=
    @g_imbi2d (.classEq (.cv k) (syn_c0c))
      (.imp (syn_wne (.cv k) (syn_c0))
        (syn_w3o (.classMem (syn_copk (.cv k) (.cv n)) (syn_cltfin)) (.objEq k n)
          (.classMem (syn_copk (.cv n) (.cv k)) (syn_cltfin))))
      (.imp (syn_wne (syn_c0c) (syn_c0))
        (syn_w3o (.classMem (syn_copk (syn_c0c) (.cv n)) (syn_cltfin))
          (.classEq (syn_c0c) (.cv n)) (.classMem (syn_copk (.cv n) (syn_c0c)) (syn_cltfin))))
      (.classMem (.cv n) (syn_cnnc)) p0016
  have p0018 := @g_neeq1 (.cv k) (.cv m) (syn_c0)
  have p0019 := @g_opkeq1 (.cv k) (.cv m) (.cv n)
  have p0020_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq k m) (.classEq (syn_copk (.cv k) (.cv n)) (syn_copk (.cv m) (.cv n)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_copk syn_cpr syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_csn
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0019
  have p0020 :=
    @g_eleq1d (.objEq k m) (syn_copk (.cv k) (.cv n)) (syn_copk (.cv m) (.cv n))
      (syn_cltfin) p0020_e00_recanon
  have p0021 := @g_eqeq1 (.cv k) (.cv m) (.cv n)
  have p0022 := @g_opkeq2 (.cv k) (.cv m) (.cv n)
  have p0023_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq k m) (.classEq (syn_copk (.cv n) (.cv k)) (syn_copk (.cv n) (.cv m)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_copk syn_cpr syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_csn
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0022
  have p0023 :=
    @g_eleq1d (.objEq k m) (syn_copk (.cv n) (.cv k)) (syn_copk (.cv n) (.cv m))
      (syn_cltfin) p0023_e00_recanon
  have p0024_e01_recanon :
    Nominal.NPrf (.imp (.objEq k m) (syn_wb (.objEq k n) (.objEq m n))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
            · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
            · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _)
      p0021
  have p0024 :=
    @g_n_3orbi123d (.objEq k m) (.classMem (syn_copk (.cv k) (.cv n)) (syn_cltfin))
      (.classMem (syn_copk (.cv m) (.cv n)) (syn_cltfin)) (.objEq k n) (.objEq m n)
      (.classMem (syn_copk (.cv n) (.cv k)) (syn_cltfin))
      (.classMem (syn_copk (.cv n) (.cv m)) (syn_cltfin)) p0020 p0024_e01_recanon p0023
  have p0025_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq k m) (syn_wb (syn_wne (.cv k) (syn_c0)) (syn_wne (.cv m) (syn_c0)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wne syn_c0 syn_cdif syn_cin syn_ccompl syn_cnin syn_wnan syn_wa
          syn_cvv
        simp (config := { failIfUnchanged := false }) only []
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0018
  have p0025 :=
    @g_imbi12d (.objEq k m) (syn_wne (.cv k) (syn_c0)) (syn_wne (.cv m) (syn_c0))
      (syn_w3o (.classMem (syn_copk (.cv k) (.cv n)) (syn_cltfin)) (.objEq k n)
        (.classMem (syn_copk (.cv n) (.cv k)) (syn_cltfin)))
      (syn_w3o (.classMem (syn_copk (.cv m) (.cv n)) (syn_cltfin)) (.objEq m n)
        (.classMem (syn_copk (.cv n) (.cv m)) (syn_cltfin)))
      p0025_e00_recanon p0024
  have p0026 :=
    @g_imbi2d (.objEq k m)
      (.imp (syn_wne (.cv k) (syn_c0))
        (syn_w3o (.classMem (syn_copk (.cv k) (.cv n)) (syn_cltfin)) (.objEq k n)
          (.classMem (syn_copk (.cv n) (.cv k)) (syn_cltfin))))
      (.imp (syn_wne (.cv m) (syn_c0))
        (syn_w3o (.classMem (syn_copk (.cv m) (.cv n)) (syn_cltfin)) (.objEq m n)
          (.classMem (syn_copk (.cv n) (.cv m)) (syn_cltfin))))
      (.classMem (.cv n) (syn_cnnc)) p0025
  have p0027 := @g_neeq1 (.cv k) (syn_cplc (.cv m) (syn_c1c)) (syn_c0)
  have p0028 := @g_opkeq1 (.cv k) (syn_cplc (.cv m) (syn_c1c)) (.cv n)
  have p0029 :=
    @g_eleq1d (.classEq (.cv k) (syn_cplc (.cv m) (syn_c1c))) (syn_copk (.cv k) (.cv n))
      (syn_copk (syn_cplc (.cv m) (syn_c1c)) (.cv n)) (syn_cltfin) p0028
  have p0030 := @g_eqeq1 (.cv k) (syn_cplc (.cv m) (syn_c1c)) (.cv n)
  have p0031 := @g_opkeq2 (.cv k) (syn_cplc (.cv m) (syn_c1c)) (.cv n)
  have p0032 :=
    @g_eleq1d (.classEq (.cv k) (syn_cplc (.cv m) (syn_c1c))) (syn_copk (.cv n) (.cv k))
      (syn_copk (.cv n) (syn_cplc (.cv m) (syn_c1c))) (syn_cltfin) p0031
  have p0033_e01_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv k) (syn_cplc (.cv m) (syn_c1c)))
        (syn_wb (.objEq k n) (.classEq (syn_cplc (.cv m) (syn_c1c)) (.cv n)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_cplc syn_wrex syn_wex syn_wa syn_c1c syn_wb
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _)
      p0030
  have p0033 :=
    @g_n_3orbi123d (.classEq (.cv k) (syn_cplc (.cv m) (syn_c1c)))
      (.classMem (syn_copk (.cv k) (.cv n)) (syn_cltfin))
      (.classMem (syn_copk (syn_cplc (.cv m) (syn_c1c)) (.cv n)) (syn_cltfin))
      (.objEq k n) (.classEq (syn_cplc (.cv m) (syn_c1c)) (.cv n))
      (.classMem (syn_copk (.cv n) (.cv k)) (syn_cltfin))
      (.classMem (syn_copk (.cv n) (syn_cplc (.cv m) (syn_c1c))) (syn_cltfin)) p0029
      p0033_e01_recanon p0032
  have p0034 :=
    @g_imbi12d (.classEq (.cv k) (syn_cplc (.cv m) (syn_c1c))) (syn_wne (.cv k) (syn_c0))
      (syn_wne (syn_cplc (.cv m) (syn_c1c)) (syn_c0))
      (syn_w3o (.classMem (syn_copk (.cv k) (.cv n)) (syn_cltfin)) (.objEq k n)
        (.classMem (syn_copk (.cv n) (.cv k)) (syn_cltfin)))
      (syn_w3o (.classMem (syn_copk (syn_cplc (.cv m) (syn_c1c)) (.cv n)) (syn_cltfin))
        (.classEq (syn_cplc (.cv m) (syn_c1c)) (.cv n))
        (.classMem (syn_copk (.cv n) (syn_cplc (.cv m) (syn_c1c))) (syn_cltfin)))
      p0027 p0033
  have p0035 :=
    @g_imbi2d (.classEq (.cv k) (syn_cplc (.cv m) (syn_c1c)))
      (.imp (syn_wne (.cv k) (syn_c0))
        (syn_w3o (.classMem (syn_copk (.cv k) (.cv n)) (syn_cltfin)) (.objEq k n)
          (.classMem (syn_copk (.cv n) (.cv k)) (syn_cltfin))))
      (.imp (syn_wne (syn_cplc (.cv m) (syn_c1c)) (syn_c0))
        (syn_w3o (.classMem (syn_copk (syn_cplc (.cv m) (syn_c1c)) (.cv n)) (syn_cltfin))
          (.classEq (syn_cplc (.cv m) (syn_c1c)) (.cv n))
          (.classMem (syn_copk (.cv n) (syn_cplc (.cv m) (syn_c1c))) (syn_cltfin))))
      (.classMem (.cv n) (syn_cnnc)) p0034
  have p0036 := @g_neeq1 (.cv k) M (syn_c0)
  have p0037 := @g_opkeq1 (.cv k) M (.cv n)
  have p0038 :=
    @g_eleq1d (.classEq (.cv k) M) (syn_copk (.cv k) (.cv n)) (syn_copk M (.cv n))
      (syn_cltfin) p0037
  have p0039 := @g_eqeq1 (.cv k) M (.cv n)
  have p0040 := @g_opkeq2 (.cv k) M (.cv n)
  have p0041 :=
    @g_eleq1d (.classEq (.cv k) M) (syn_copk (.cv n) (.cv k)) (syn_copk (.cv n) M)
      (syn_cltfin) p0040
  have p0042_e01_recanon :
    Nominal.NPrf (.imp (.classEq (.cv k) M) (syn_wb (.objEq k n) (.classEq M (.cv n)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _)
      p0039
  have p0042 :=
    @g_n_3orbi123d (.classEq (.cv k) M)
      (.classMem (syn_copk (.cv k) (.cv n)) (syn_cltfin))
      (.classMem (syn_copk M (.cv n)) (syn_cltfin)) (.objEq k n) (.classEq M (.cv n))
      (.classMem (syn_copk (.cv n) (.cv k)) (syn_cltfin))
      (.classMem (syn_copk (.cv n) M) (syn_cltfin)) p0038 p0042_e01_recanon p0041
  have p0043 :=
    @g_imbi12d (.classEq (.cv k) M) (syn_wne (.cv k) (syn_c0)) (syn_wne M (syn_c0))
      (syn_w3o (.classMem (syn_copk (.cv k) (.cv n)) (syn_cltfin)) (.objEq k n)
        (.classMem (syn_copk (.cv n) (.cv k)) (syn_cltfin)))
      (syn_w3o (.classMem (syn_copk M (.cv n)) (syn_cltfin)) (.classEq M (.cv n))
        (.classMem (syn_copk (.cv n) M) (syn_cltfin)))
      p0036 p0042
  have p0044 :=
    @g_imbi2d (.classEq (.cv k) M)
      (.imp (syn_wne (.cv k) (syn_c0))
        (syn_w3o (.classMem (syn_copk (.cv k) (.cv n)) (syn_cltfin)) (.objEq k n)
          (.classMem (syn_copk (.cv n) (.cv k)) (syn_cltfin))))
      (.imp (syn_wne M (syn_c0))
        (syn_w3o (.classMem (syn_copk M (.cv n)) (syn_cltfin)) (.classEq M (.cv n))
          (.classMem (syn_copk (.cv n) M) (syn_cltfin))))
      (.classMem (.cv n) (syn_cnnc)) p0043
  have p0045 := @g_n_0cminle (.cv n)
  have p0046 :=
    @g_adantr (.classMem (.cv n) (syn_cnnc))
      (.classMem (syn_copk (syn_c0c) (.cv n)) (syn_clefin)) (syn_wne (syn_c0c) (syn_c0))
      p0045
  have p0047 := @g_n_0cex
  have p0048 := @g_lefinlteq (syn_c0c) (.cv n) (syn_cvv) (syn_cnnc)
  have p0049 :=
    @g_mp3an1 (.classMem (syn_c0c) (syn_cvv)) (.classMem (.cv n) (syn_cnnc))
      (syn_wne (syn_c0c) (syn_c0))
      (syn_wb (.classMem (syn_copk (syn_c0c) (.cv n)) (syn_clefin))
        (syn_wo (.classMem (syn_copk (syn_c0c) (.cv n)) (syn_cltfin))
          (.classEq (syn_c0c) (.cv n))))
      p0047 p0048
  have p0050 :=
    @g_orcom (.classMem (syn_copk (syn_c0c) (.cv n)) (syn_cltfin))
      (.classEq (syn_c0c) (.cv n))
  have p0051 :=
    @g_syl6bb (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wne (syn_c0c) (syn_c0)))
      (.classMem (syn_copk (syn_c0c) (.cv n)) (syn_clefin))
      (syn_wo (.classMem (syn_copk (syn_c0c) (.cv n)) (syn_cltfin))
        (.classEq (syn_c0c) (.cv n)))
      (syn_wo (.classEq (syn_c0c) (.cv n))
        (.classMem (syn_copk (syn_c0c) (.cv n)) (syn_cltfin)))
      p0049 p0050
  have p0052 :=
    @g_mpbid (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wne (syn_c0c) (syn_c0)))
      (.classMem (syn_copk (syn_c0c) (.cv n)) (syn_clefin))
      (syn_wo (.classEq (syn_c0c) (.cv n))
        (.classMem (syn_copk (syn_c0c) (.cv n)) (syn_cltfin)))
      p0046 p0051
  have p0053 :=
    @g_n_3mix2 (.classEq (syn_c0c) (.cv n))
      (.classMem (syn_copk (syn_c0c) (.cv n)) (syn_cltfin))
      (.classMem (syn_copk (.cv n) (syn_c0c)) (syn_cltfin))
  have p0054 :=
    @g_n_3mix1 (.classMem (syn_copk (syn_c0c) (.cv n)) (syn_cltfin))
      (.classEq (syn_c0c) (.cv n)) (.classMem (syn_copk (.cv n) (syn_c0c)) (syn_cltfin))
  have p0055 :=
    @g_jaoi (.classEq (syn_c0c) (.cv n))
      (syn_w3o (.classMem (syn_copk (syn_c0c) (.cv n)) (syn_cltfin))
        (.classEq (syn_c0c) (.cv n)) (.classMem (syn_copk (.cv n) (syn_c0c)) (syn_cltfin)))
      (.classMem (syn_copk (syn_c0c) (.cv n)) (syn_cltfin)) p0053 p0054
  have p0056 :=
    @g_syl (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wne (syn_c0c) (syn_c0)))
      (syn_wo (.classEq (syn_c0c) (.cv n))
        (.classMem (syn_copk (syn_c0c) (.cv n)) (syn_cltfin)))
      (syn_w3o (.classMem (syn_copk (syn_c0c) (.cv n)) (syn_cltfin))
        (.classEq (syn_c0c) (.cv n)) (.classMem (syn_copk (.cv n) (syn_c0c)) (syn_cltfin)))
      p0052 p0055
  have p0057 :=
    @g_ex (.classMem (.cv n) (syn_cnnc)) (syn_wne (syn_c0c) (syn_c0))
      (syn_w3o (.classMem (syn_copk (syn_c0c) (.cv n)) (syn_cltfin))
        (.classEq (syn_c0c) (.cv n)) (.classMem (syn_copk (.cv n) (syn_c0c)) (syn_cltfin)))
      p0056
  have p0058 := @g_addcnnul (.cv m) (syn_c1c)
  have p0059 :=
    @g_simpld (syn_wne (syn_cplc (.cv m) (syn_c1c)) (syn_c0)) (syn_wne (.cv m) (syn_c0))
      (syn_wne (syn_c1c) (syn_c0)) p0058
  have p0060 :=
    @g_n_3ad2ant3 (syn_wne (syn_cplc (.cv m) (syn_c1c)) (syn_c0))
      (.classMem (.cv m) (syn_cnnc)) (syn_wne (.cv m) (syn_c0))
      (.classMem (.cv n) (syn_cnnc)) p0059
  have p0061 := @g_addc32 (.cv m) (.cv p) (syn_c1c)
  have p0062 :=
    @g_eqeq2i (syn_cplc (syn_cplc (.cv m) (.cv p)) (syn_c1c))
      (syn_cplc (syn_cplc (.cv m) (syn_c1c)) (.cv p)) (.cv n) p0061
  have p0063 :=
    @g_rexbii (.classEq (.cv n) (syn_cplc (syn_cplc (.cv m) (.cv p)) (syn_c1c)))
      (.classEq (.cv n) (syn_cplc (syn_cplc (.cv m) (syn_c1c)) (.cv p))) p (syn_cnnc)
      p0062
  have p0064 :=
    @g_biimpi
      (syn_wrex p (syn_cnnc) (.classEq (.cv n) (syn_cplc (syn_cplc (.cv m) (.cv p)) (syn_c1c))))
      (syn_wrex p (syn_cnnc) (.classEq (.cv n) (syn_cplc (syn_cplc (.cv m) (syn_c1c)) (.cv p))))
      p0063
  have p0065 :=
    @g_adantl
      (syn_wrex p (syn_cnnc) (.classEq (.cv n) (syn_cplc (syn_cplc (.cv m) (.cv p)) (syn_c1c))))
      (syn_wrex p (syn_cnnc) (.classEq (.cv n) (syn_cplc (syn_cplc (.cv m) (syn_c1c)) (.cv p))))
      (syn_wne (.cv m) (syn_c0)) p0064
  have p0066 :=
    @g_a1i
      (.imp (syn_wa (syn_wne (.cv m) (syn_c0)) (syn_wrex p (syn_cnnc)
            (.classEq (.cv n) (syn_cplc (syn_cplc (.cv m) (.cv p)) (syn_c1c)))))
        (syn_wrex p (syn_cnnc)
          (.classEq (.cv n) (syn_cplc (syn_cplc (.cv m) (syn_c1c)) (.cv p)))))
      (syn_w3a (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc))
        (syn_wne (syn_cplc (.cv m) (syn_c1c)) (syn_c0)))
      p0065
  have freeVariableCertificate0 : p ∉ ((Class.cv m)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_p_ne_m, not_false_eq_true]
  have freeVariableCertificate1 : p ∉ ((Class.cv n)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_p_ne_n, not_false_eq_true]
  have p0067 :=
    @g_opkltfing p (.cv m) (.cv n) (syn_cnnc) (syn_cnnc) freeVariableCertificate0
      freeVariableCertificate1
  have p0068 :=
    @g_n_3adant3 (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc))
      (syn_wb (.classMem (syn_copk (.cv m) (.cv n)) (syn_cltfin))
        (syn_wa (syn_wne (.cv m) (syn_c0)) (syn_wrex p (syn_cnnc)
            (.classEq (.cv n) (syn_cplc (syn_cplc (.cv m) (.cv p)) (syn_c1c))))))
      (syn_wne (syn_cplc (.cv m) (syn_c1c)) (syn_c0)) p0067
  have p0069 :=
    @g_simp1 (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc))
      (syn_wne (syn_cplc (.cv m) (syn_c1c)) (syn_c0))
  have p0070 := @g_peano2 (.cv m)
  have p0071 :=
    @g_syl
      (syn_w3a (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc))
        (syn_wne (syn_cplc (.cv m) (syn_c1c)) (syn_c0)))
      (.classMem (.cv m) (syn_cnnc)) (.classMem (syn_cplc (.cv m) (syn_c1c)) (syn_cnnc))
      p0069 p0070
  have p0072 :=
    @g_simp2 (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc))
      (syn_wne (syn_cplc (.cv m) (syn_c1c)) (syn_c0))
  have freeVariableCertificate2 : p ∉ ((syn_cplc (.cv m) (syn_c1c))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_p_ne_m, or_false,
      not_false_eq_true]
  have p0073 :=
    @g_opklefing p (syn_cplc (.cv m) (syn_c1c)) (.cv n) (syn_cnnc) (syn_cnnc)
      freeVariableCertificate2 freeVariableCertificate1
  have p0074 :=
    @g_syl2anc
      (syn_w3a (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc))
        (syn_wne (syn_cplc (.cv m) (syn_c1c)) (syn_c0)))
      (.classMem (syn_cplc (.cv m) (syn_c1c)) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc))
      (syn_wb (.classMem (syn_copk (syn_cplc (.cv m) (syn_c1c)) (.cv n)) (syn_clefin))
        (syn_wrex p (syn_cnnc)
          (.classEq (.cv n) (syn_cplc (syn_cplc (.cv m) (syn_c1c)) (.cv p)))))
      p0071 p0072 p0073
  have p0075 :=
    @g_n_3imtr4d
      (syn_w3a (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc))
        (syn_wne (syn_cplc (.cv m) (syn_c1c)) (syn_c0)))
      (syn_wa (syn_wne (.cv m) (syn_c0)) (syn_wrex p (syn_cnnc)
          (.classEq (.cv n) (syn_cplc (syn_cplc (.cv m) (.cv p)) (syn_c1c)))))
      (syn_wrex p (syn_cnnc) (.classEq (.cv n) (syn_cplc (syn_cplc (.cv m) (syn_c1c)) (.cv p))))
      (.classMem (syn_copk (.cv m) (.cv n)) (syn_cltfin))
      (.classMem (syn_copk (syn_cplc (.cv m) (syn_c1c)) (.cv n)) (syn_clefin)) p0066 p0068
      p0074
  have p0076 := @g_lefinlteq (syn_cplc (.cv m) (syn_c1c)) (.cv n) (syn_cnnc) (syn_cnnc)
  have p0077 :=
    @g_syl3an1 (.classMem (.cv m) (syn_cnnc))
      (.classMem (syn_cplc (.cv m) (syn_c1c)) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc))
      (syn_wne (syn_cplc (.cv m) (syn_c1c)) (syn_c0))
      (syn_wb (.classMem (syn_copk (syn_cplc (.cv m) (syn_c1c)) (.cv n)) (syn_clefin))
        (syn_wo (.classMem (syn_copk (syn_cplc (.cv m) (syn_c1c)) (.cv n)) (syn_cltfin))
          (.classEq (syn_cplc (.cv m) (syn_c1c)) (.cv n))))
      p0070 p0076
  have p0078 :=
    @g_sylibd
      (syn_w3a (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc))
        (syn_wne (syn_cplc (.cv m) (syn_c1c)) (syn_c0)))
      (.classMem (syn_copk (.cv m) (.cv n)) (syn_cltfin))
      (.classMem (syn_copk (syn_cplc (.cv m) (syn_c1c)) (.cv n)) (syn_clefin))
      (syn_wo (.classMem (syn_copk (syn_cplc (.cv m) (syn_c1c)) (.cv n)) (syn_cltfin))
        (.classEq (syn_cplc (.cv m) (syn_c1c)) (.cv n)))
      p0075 p0077
  have p0079 :=
    @g_n_3mix1 (.classMem (syn_copk (syn_cplc (.cv m) (syn_c1c)) (.cv n)) (syn_cltfin))
      (.classEq (syn_cplc (.cv m) (syn_c1c)) (.cv n))
      (.classMem (syn_copk (.cv n) (syn_cplc (.cv m) (syn_c1c))) (syn_cltfin))
  have p0080 :=
    @g_n_3mix2 (.classEq (syn_cplc (.cv m) (syn_c1c)) (.cv n))
      (.classMem (syn_copk (syn_cplc (.cv m) (syn_c1c)) (.cv n)) (syn_cltfin))
      (.classMem (syn_copk (.cv n) (syn_cplc (.cv m) (syn_c1c))) (syn_cltfin))
  have p0081 :=
    @g_jaoi (.classMem (syn_copk (syn_cplc (.cv m) (syn_c1c)) (.cv n)) (syn_cltfin))
      (syn_w3o (.classMem (syn_copk (syn_cplc (.cv m) (syn_c1c)) (.cv n)) (syn_cltfin))
        (.classEq (syn_cplc (.cv m) (syn_c1c)) (.cv n))
        (.classMem (syn_copk (.cv n) (syn_cplc (.cv m) (syn_c1c))) (syn_cltfin)))
      (.classEq (syn_cplc (.cv m) (syn_c1c)) (.cv n)) p0079 p0080
  have p0082 :=
    @g_syl6
      (syn_w3a (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc))
        (syn_wne (syn_cplc (.cv m) (syn_c1c)) (syn_c0)))
      (.classMem (syn_copk (.cv m) (.cv n)) (syn_cltfin))
      (syn_wo (.classMem (syn_copk (syn_cplc (.cv m) (syn_c1c)) (.cv n)) (syn_cltfin))
        (.classEq (syn_cplc (.cv m) (syn_c1c)) (.cv n)))
      (syn_w3o (.classMem (syn_copk (syn_cplc (.cv m) (syn_c1c)) (.cv n)) (syn_cltfin))
        (.classEq (syn_cplc (.cv m) (syn_c1c)) (.cv n))
        (.classMem (syn_copk (.cv n) (syn_cplc (.cv m) (syn_c1c))) (syn_cltfin)))
      p0078 p0081
  have p0083 := @g_ltfinp1 (.cv m) (syn_cnnc)
  have p0084 :=
    @g_sylan2 (syn_wne (syn_cplc (.cv m) (syn_c1c)) (syn_c0))
      (.classMem (.cv m) (syn_cnnc)) (syn_wne (.cv m) (syn_c0))
      (.classMem (syn_copk (.cv m) (syn_cplc (.cv m) (syn_c1c))) (syn_cltfin)) p0059 p0083
  have p0085 :=
    @g_n_3adant2 (.classMem (.cv m) (syn_cnnc))
      (syn_wne (syn_cplc (.cv m) (syn_c1c)) (syn_c0))
      (.classMem (syn_copk (.cv m) (syn_cplc (.cv m) (syn_c1c))) (syn_cltfin))
      (.classMem (.cv n) (syn_cnnc)) p0084
  have p0086 := @g_opkeq1 (.cv m) (.cv n) (syn_cplc (.cv m) (syn_c1c))
  have p0087_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq m n) (.classEq (syn_copk (.cv m) (syn_cplc (.cv m) (syn_c1c)))
          (syn_copk (.cv n) (syn_cplc (.cv m) (syn_c1c))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_copk syn_cpr syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_csn
          syn_cplc syn_wrex syn_wex syn_c1c
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0086
  have p0087 :=
    @g_eleq1d (.objEq m n) (syn_copk (.cv m) (syn_cplc (.cv m) (syn_c1c)))
      (syn_copk (.cv n) (syn_cplc (.cv m) (syn_c1c))) (syn_cltfin) p0087_e00_recanon
  have p0088 :=
    @g_syl5ibcom
      (syn_w3a (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc))
        (syn_wne (syn_cplc (.cv m) (syn_c1c)) (syn_c0)))
      (.classMem (syn_copk (.cv m) (syn_cplc (.cv m) (syn_c1c))) (syn_cltfin))
      (.objEq m n)
      (.classMem (syn_copk (.cv n) (syn_cplc (.cv m) (syn_c1c))) (syn_cltfin)) p0085 p0087
  have p0089 :=
    @g_n_3mix3 (.classMem (syn_copk (.cv n) (syn_cplc (.cv m) (syn_c1c))) (syn_cltfin))
      (.classMem (syn_copk (syn_cplc (.cv m) (syn_c1c)) (.cv n)) (syn_cltfin))
      (.classEq (syn_cplc (.cv m) (syn_c1c)) (.cv n))
  have p0090 :=
    @g_syl6
      (syn_w3a (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc))
        (syn_wne (syn_cplc (.cv m) (syn_c1c)) (syn_c0)))
      (.objEq m n)
      (.classMem (syn_copk (.cv n) (syn_cplc (.cv m) (syn_c1c))) (syn_cltfin))
      (syn_w3o (.classMem (syn_copk (syn_cplc (.cv m) (syn_c1c)) (.cv n)) (syn_cltfin))
        (.classEq (syn_cplc (.cv m) (syn_c1c)) (.cv n))
        (.classMem (syn_copk (.cv n) (syn_cplc (.cv m) (syn_c1c))) (syn_cltfin)))
      p0088 p0089
  have p0091 := @g_ltfintr (.cv n) (.cv m) (syn_cplc (.cv m) (syn_c1c))
  have p0092 :=
    @g_syl3anc
      (syn_w3a (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc))
        (syn_wne (syn_cplc (.cv m) (syn_c1c)) (syn_c0)))
      (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv m) (syn_cnnc))
      (.classMem (syn_cplc (.cv m) (syn_c1c)) (syn_cnnc))
      (.imp (syn_wa (.classMem (syn_copk (.cv n) (.cv m)) (syn_cltfin))
          (.classMem (syn_copk (.cv m) (syn_cplc (.cv m) (syn_c1c))) (syn_cltfin)))
        (.classMem (syn_copk (.cv n) (syn_cplc (.cv m) (syn_c1c))) (syn_cltfin)))
      p0072 p0069 p0071 p0091
  have p0093 :=
    @g_mpan2d
      (syn_w3a (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc))
        (syn_wne (syn_cplc (.cv m) (syn_c1c)) (syn_c0)))
      (.classMem (syn_copk (.cv n) (.cv m)) (syn_cltfin))
      (.classMem (syn_copk (.cv m) (syn_cplc (.cv m) (syn_c1c))) (syn_cltfin))
      (.classMem (syn_copk (.cv n) (syn_cplc (.cv m) (syn_c1c))) (syn_cltfin)) p0085 p0092
  have p0094 :=
    @g_syl6
      (syn_w3a (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc))
        (syn_wne (syn_cplc (.cv m) (syn_c1c)) (syn_c0)))
      (.classMem (syn_copk (.cv n) (.cv m)) (syn_cltfin))
      (.classMem (syn_copk (.cv n) (syn_cplc (.cv m) (syn_c1c))) (syn_cltfin))
      (syn_w3o (.classMem (syn_copk (syn_cplc (.cv m) (syn_c1c)) (.cv n)) (syn_cltfin))
        (.classEq (syn_cplc (.cv m) (syn_c1c)) (.cv n))
        (.classMem (syn_copk (.cv n) (syn_cplc (.cv m) (syn_c1c))) (syn_cltfin)))
      p0093 p0089
  have p0095 :=
    @g_n_3jaod
      (syn_w3a (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc))
        (syn_wne (syn_cplc (.cv m) (syn_c1c)) (syn_c0)))
      (.classMem (syn_copk (.cv m) (.cv n)) (syn_cltfin))
      (syn_w3o (.classMem (syn_copk (syn_cplc (.cv m) (syn_c1c)) (.cv n)) (syn_cltfin))
        (.classEq (syn_cplc (.cv m) (syn_c1c)) (.cv n))
        (.classMem (syn_copk (.cv n) (syn_cplc (.cv m) (syn_c1c))) (syn_cltfin)))
      (.objEq m n) (.classMem (syn_copk (.cv n) (.cv m)) (syn_cltfin)) p0082 p0090 p0094
  have p0096 :=
    @g_embantd
      (syn_w3a (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc))
        (syn_wne (syn_cplc (.cv m) (syn_c1c)) (syn_c0)))
      (syn_wne (.cv m) (syn_c0))
      (syn_w3o (.classMem (syn_copk (.cv m) (.cv n)) (syn_cltfin)) (.objEq m n)
        (.classMem (syn_copk (.cv n) (.cv m)) (syn_cltfin)))
      (syn_w3o (.classMem (syn_copk (syn_cplc (.cv m) (syn_c1c)) (.cv n)) (syn_cltfin))
        (.classEq (syn_cplc (.cv m) (syn_c1c)) (.cv n))
        (.classMem (syn_copk (.cv n) (syn_cplc (.cv m) (syn_c1c))) (syn_cltfin)))
      p0060 p0095
  have p0097 :=
    @g_n_3expia (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc))
      (syn_wne (syn_cplc (.cv m) (syn_c1c)) (syn_c0))
      (.imp (.imp (syn_wne (.cv m) (syn_c0))
          (syn_w3o (.classMem (syn_copk (.cv m) (.cv n)) (syn_cltfin)) (.objEq m n)
            (.classMem (syn_copk (.cv n) (.cv m)) (syn_cltfin))))
        (syn_w3o (.classMem (syn_copk (syn_cplc (.cv m) (syn_c1c)) (.cv n)) (syn_cltfin))
          (.classEq (syn_cplc (.cv m) (syn_c1c)) (.cv n))
          (.classMem (syn_copk (.cv n) (syn_cplc (.cv m) (syn_c1c))) (syn_cltfin))))
      p0096
  have p0098 :=
    @g_com23 (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc)))
      (syn_wne (syn_cplc (.cv m) (syn_c1c)) (syn_c0))
      (.imp (syn_wne (.cv m) (syn_c0))
        (syn_w3o (.classMem (syn_copk (.cv m) (.cv n)) (syn_cltfin)) (.objEq m n)
          (.classMem (syn_copk (.cv n) (.cv m)) (syn_cltfin))))
      (syn_w3o (.classMem (syn_copk (syn_cplc (.cv m) (syn_c1c)) (.cv n)) (syn_cltfin))
        (.classEq (syn_cplc (.cv m) (syn_c1c)) (.cv n))
        (.classMem (syn_copk (.cv n) (syn_cplc (.cv m) (syn_c1c))) (syn_cltfin)))
      p0097
  have p0099 :=
    @g_ex (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc))
      (.imp (.imp (syn_wne (.cv m) (syn_c0))
          (syn_w3o (.classMem (syn_copk (.cv m) (.cv n)) (syn_cltfin)) (.objEq m n)
            (.classMem (syn_copk (.cv n) (.cv m)) (syn_cltfin))))
        (.imp (syn_wne (syn_cplc (.cv m) (syn_c1c)) (syn_c0)) (syn_w3o
            (.classMem (syn_copk (syn_cplc (.cv m) (syn_c1c)) (.cv n)) (syn_cltfin))
            (.classEq (syn_cplc (.cv m) (syn_c1c)) (.cv n))
            (.classMem (syn_copk (.cv n) (syn_cplc (.cv m) (syn_c1c))) (syn_cltfin)))))
      p0098
  have p0100 :=
    @g_a2d (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc))
      (.imp (syn_wne (.cv m) (syn_c0))
        (syn_w3o (.classMem (syn_copk (.cv m) (.cv n)) (syn_cltfin)) (.objEq m n)
          (.classMem (syn_copk (.cv n) (.cv m)) (syn_cltfin))))
      (.imp (syn_wne (syn_cplc (.cv m) (syn_c1c)) (syn_c0))
        (syn_w3o (.classMem (syn_copk (syn_cplc (.cv m) (syn_c1c)) (.cv n)) (syn_cltfin))
          (.classEq (syn_cplc (.cv m) (syn_c1c)) (.cv n))
          (.classMem (syn_copk (.cv n) (syn_cplc (.cv m) (syn_c1c))) (syn_cltfin))))
      p0099
  have freeVariableCertificate3 :
    k ∉
      ((Wff.imp (.classMem (.cv n) (syn_cnnc)) (.imp (syn_wne (.cv m) (syn_c0))
            (syn_w3o (.classMem (syn_copk (.cv m) (.cv n)) (syn_cltfin)) (.objEq m n)
              (.classMem (syn_copk (.cv n) (.cv m)) (syn_cltfin)))))).fv :=
    by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3o,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cltfin,
      NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_union, Finset.mem_insert,
      Finset.mem_singleton, Finset.notMem_empty, fresh_k_ne_n, fresh_k_ne_m, or_false,
      not_false_eq_true]
  have freeVariableCertificate4 :
    m ∉
      ((Wff.imp (.classMem (.cv n) (syn_cnnc)) (.imp (syn_wne (.cv k) (syn_c0))
            (syn_w3o (.classMem (syn_copk (.cv k) (.cv n)) (syn_cltfin)) (.objEq k n)
              (.classMem (syn_copk (.cv n) (.cv k)) (syn_cltfin)))))).fv :=
    by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3o,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cltfin,
      NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_union, Finset.mem_insert,
      Finset.mem_singleton, Finset.notMem_empty, fresh_m_ne_n, fresh_m_ne_k, or_false,
      not_false_eq_true]
  have freeVariableCertificate5 :
    k ∉
      ((Wff.imp (.classMem (.cv n) (syn_cnnc)) (.imp (syn_wne (syn_c0c) (syn_c0))
            (syn_w3o (.classMem (syn_copk (syn_c0c) (.cv n)) (syn_cltfin))
              (.classEq (syn_c0c) (.cv n))
              (.classMem (syn_copk (.cv n) (syn_c0c)) (syn_cltfin)))))).fv :=
    by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3o,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cltfin,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union, Finset.mem_singleton,
      Finset.notMem_empty, fresh_k_ne_n, or_false, not_false_eq_true]
  have freeVariableCertificate6 :
    k ∉
      ((Wff.imp (.classMem (.cv n) (syn_cnnc)) (.imp (syn_wne M (syn_c0))
            (syn_w3o (.classMem (syn_copk M (.cv n)) (syn_cltfin)) (.classEq M (.cv n))
              (.classMem (syn_copk (.cv n) M) (syn_cltfin)))))).fv :=
    by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3o,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cltfin,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union, Finset.mem_singleton,
      Finset.notMem_empty, fresh_k_ne_n, fresh_k_not_M, or_false, not_false_eq_true]
  have freeVariableCertificate7 :
    k ∉
      ((Wff.imp (.classMem (.cv n) (syn_cnnc))
          (.imp (syn_wne (syn_cplc (.cv m) (syn_c1c)) (syn_c0)) (syn_w3o
              (.classMem (syn_copk (syn_cplc (.cv m) (syn_c1c)) (.cv n)) (syn_cltfin))
              (.classEq (syn_cplc (.cv m) (syn_c1c)) (.cv n))
              (.classMem (syn_copk (.cv n) (syn_cplc (.cv m) (syn_c1c))) (syn_cltfin)))))).fv :=
    by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3o,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cltfin,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union, Finset.mem_singleton,
      Finset.notMem_empty, fresh_k_ne_n, fresh_k_ne_m, or_false, not_false_eq_true]
  have p0101 :=
    @g_finds
      (.imp (.classMem (.cv n) (syn_cnnc)) (.imp (syn_wne (.cv k) (syn_c0))
          (syn_w3o (.classMem (syn_copk (.cv k) (.cv n)) (syn_cltfin)) (.objEq k n)
            (.classMem (syn_copk (.cv n) (.cv k)) (syn_cltfin)))))
      (.imp (.classMem (.cv n) (syn_cnnc)) (.imp (syn_wne (syn_c0c) (syn_c0))
          (syn_w3o (.classMem (syn_copk (syn_c0c) (.cv n)) (syn_cltfin))
            (.classEq (syn_c0c) (.cv n))
            (.classMem (syn_copk (.cv n) (syn_c0c)) (syn_cltfin)))))
      (.imp (.classMem (.cv n) (syn_cnnc)) (.imp (syn_wne (.cv m) (syn_c0))
          (syn_w3o (.classMem (syn_copk (.cv m) (.cv n)) (syn_cltfin)) (.objEq m n)
            (.classMem (syn_copk (.cv n) (.cv m)) (syn_cltfin)))))
      (.imp (.classMem (.cv n) (syn_cnnc)) (.imp (syn_wne (syn_cplc (.cv m) (syn_c1c)) (syn_c0))
          (syn_w3o (.classMem (syn_copk (syn_cplc (.cv m) (syn_c1c)) (.cv n)) (syn_cltfin))
            (.classEq (syn_cplc (.cv m) (syn_c1c)) (.cv n))
            (.classMem (syn_copk (.cv n) (syn_cplc (.cv m) (syn_c1c))) (syn_cltfin)))))
      (.imp (.classMem (.cv n) (syn_cnnc)) (.imp (syn_wne M (syn_c0))
          (syn_w3o (.classMem (syn_copk M (.cv n)) (syn_cltfin)) (.classEq M (.cv n))
            (.classMem (syn_copk (.cv n) M) (syn_cltfin)))))
      k m M (by exact (show k ∉ (M).fv from (by exact fresh_k_not_M)))
      freeVariableCertificate3 freeVariableCertificate4 freeVariableCertificate5
      freeVariableCertificate6 freeVariableCertificate7
      (show k ≠ m from (by exact fresh_k_ne_m)) p0008 p0017 p0026 p0035 p0044 p0057 p0100
  have p0102 :=
    @g_com12 (.classMem M (syn_cnnc)) (.classMem (.cv n) (syn_cnnc))
      (.imp (syn_wne M (syn_c0))
        (syn_w3o (.classMem (syn_copk M (.cv n)) (syn_cltfin)) (.classEq M (.cv n))
          (.classMem (syn_copk (.cv n) M) (syn_cltfin))))
      p0101
  have freeVariableCertificate8 :
    n ∉
      ((Wff.imp (.classMem M (syn_cnnc)) (.imp (syn_wne M (syn_c0))
            (syn_w3o (.classMem (syn_copk M N) (syn_cltfin)) (.classEq M N)
              (.classMem (syn_copk N M) (syn_cltfin)))))).fv :=
    by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3o,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cltfin,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union, Finset.notMem_empty,
      fresh_n_not_M, fresh_n_not_N, or_false, not_false_eq_true]
  have p0103 :=
    @g_vtoclga
      (.imp (.classMem M (syn_cnnc)) (.imp (syn_wne M (syn_c0))
          (syn_w3o (.classMem (syn_copk M (.cv n)) (syn_cltfin)) (.classEq M (.cv n))
            (.classMem (syn_copk (.cv n) M) (syn_cltfin)))))
      (.imp (.classMem M (syn_cnnc)) (.imp (syn_wne M (syn_c0))
          (syn_w3o (.classMem (syn_copk M N) (syn_cltfin)) (.classEq M N)
            (.classMem (syn_copk N M) (syn_cltfin)))))
      n N (syn_cnnc) (by exact (show n ∉ (N).fv from (by exact fresh_n_not_N)))
      (by
        exact
          (show n ∉ ((syn_cnnc)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc];
              exact (show n ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
      freeVariableCertificate8 p0007 p0102
  have p0104 :=
    @g_com12 (.classMem N (syn_cnnc)) (.classMem M (syn_cnnc))
      (.imp (syn_wne M (syn_c0)) (syn_w3o (.classMem (syn_copk M N) (syn_cltfin)) (.classEq M N)
          (.classMem (syn_copk N M) (syn_cltfin))))
      p0103
  have p0105 :=
    @g_n_3imp (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)) (syn_wne M (syn_c0))
      (syn_w3o (.classMem (syn_copk M N) (syn_cltfin)) (.classEq M N)
        (.classMem (syn_copk N M) (syn_cltfin)))
      p0104
  exact p0105


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk009StructuralPart045`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_lefinrflx (A : Class) (V : Class) :
    Nominal.NPrf (.imp (.classMem A V) (.classMem (syn_copk A A) (syn_clefin))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ V.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have p0000 := @g_peano1
  have p0001 := @g_addcid1 A
  have p0002 := @g_eqcomi (syn_cplc A (syn_c0c)) A p0001
  have p0003 := @g_addceq2 (.cv x) (syn_c0c) A
  have p0004 :=
    @g_eqeq2d (.classEq (.cv x) (syn_c0c)) (syn_cplc A (.cv x)) (syn_cplc A (syn_c0c)) A
      p0003
  have freeVariableCertificate0 : x ∉ ((Wff.classEq A (syn_cplc A (syn_c0c)))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union,
      Finset.notMem_empty, fresh_x_not_A, or_false, not_false_eq_true]
  have p0005 :=
    @g_rspcev (.classEq A (syn_cplc A (.cv x))) (.classEq A (syn_cplc A (syn_c0c))) x
      (syn_c0c) (syn_cnnc)
      (by
        exact
          (show x ∉ ((syn_c0c)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c];
              exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
      (by
        exact
          (show x ∉ ((syn_cnnc)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc];
              exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
      freeVariableCertificate0 p0004
  have p0006 :=
    @g_mp2an (.classMem (syn_c0c) (syn_cnnc)) (.classEq A (syn_cplc A (syn_c0c)))
      (syn_wrex x (syn_cnnc) (.classEq A (syn_cplc A (.cv x)))) p0000 p0002 p0005
  have p0007 :=
    @g_opklefing x A A V V (by exact (show x ∉ (A).fv from (by exact fresh_x_not_A)))
      (by exact (show x ∉ (A).fv from (by exact fresh_x_not_A)))
  have p0008 :=
    @g_anidms (.classMem A V)
      (syn_wb (.classMem (syn_copk A A) (syn_clefin))
        (syn_wrex x (syn_cnnc) (.classEq A (syn_cplc A (.cv x)))))
      p0007
  have p0009 :=
    @g_mpbiri (.classMem A V) (.classMem (syn_copk A A) (syn_clefin))
      (syn_wrex x (syn_cnnc) (.classEq A (syn_cplc A (.cv x)))) p0006 p0008
  exact p0009

@[expose]
noncomputable def g_ltlefin (A : Class) (B : Class) (V : Class) (W : Class) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem A V) (.classMem B W))
        (.imp (.classMem (syn_copk A B) (syn_cltfin))
          (.classMem (syn_copk A B) (syn_clefin)))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ V.fv ∪ W.fv
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
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
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
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x := Ne.symm fresh_x_ne_y
  have p0000 := @g_addcass A (.cv x) (syn_c1c)
  have p0001 :=
    @g_eqeq2i (syn_cplc (syn_cplc A (.cv x)) (syn_c1c))
      (syn_cplc A (syn_cplc (.cv x) (syn_c1c))) B p0000
  have p0002 := @g_peano2 (.cv x)
  have p0003 := @g_addceq2 (.cv y) (syn_cplc (.cv x) (syn_c1c)) A
  have p0004 :=
    @g_eqeq2d (.classEq (.cv y) (syn_cplc (.cv x) (syn_c1c))) (syn_cplc A (.cv y))
      (syn_cplc A (syn_cplc (.cv x) (syn_c1c))) B p0003
  have freeVariableCertificate0 : y ∉ ((syn_cplc (.cv x) (syn_c1c))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_y_ne_x, or_false,
      not_false_eq_true]
  have freeVariableCertificate1 :
    y ∉ ((Wff.classEq B (syn_cplc A (syn_cplc (.cv x) (syn_c1c))))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_y_not_B, fresh_y_not_A,
      fresh_y_ne_x, or_false, not_false_eq_true]
  have p0005 :=
    @g_rspcev (.classEq B (syn_cplc A (.cv y)))
      (.classEq B (syn_cplc A (syn_cplc (.cv x) (syn_c1c)))) y
      (syn_cplc (.cv x) (syn_c1c)) (syn_cnnc) freeVariableCertificate0
      (by
        exact
          (show y ∉ ((syn_cnnc)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc];
              exact (show y ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
      freeVariableCertificate1 p0004
  have p0006 :=
    @g_sylan (.classMem (.cv x) (syn_cnnc))
      (.classMem (syn_cplc (.cv x) (syn_c1c)) (syn_cnnc))
      (.classEq B (syn_cplc A (syn_cplc (.cv x) (syn_c1c))))
      (syn_wrex y (syn_cnnc) (.classEq B (syn_cplc A (.cv y)))) p0002 p0005
  have p0007 :=
    @g_sylan2b (.classEq B (syn_cplc (syn_cplc A (.cv x)) (syn_c1c)))
      (.classMem (.cv x) (syn_cnnc))
      (.classEq B (syn_cplc A (syn_cplc (.cv x) (syn_c1c))))
      (syn_wrex y (syn_cnnc) (.classEq B (syn_cplc A (.cv y)))) p0001 p0006
  have freeVariableCertificate2 :
    x ∉ ((syn_wrex y (syn_cnnc) (.classEq B (syn_cplc A (.cv y))))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
      Finset.mem_singleton, Finset.notMem_empty, fresh_x_not_B, fresh_x_not_A,
      fresh_x_ne_y, or_false, and_false, not_false_eq_true]
  have p0008 :=
    @g_rexlimiva (.classEq B (syn_cplc (syn_cplc A (.cv x)) (syn_c1c)))
      (syn_wrex y (syn_cnnc) (.classEq B (syn_cplc A (.cv y)))) x (syn_cnnc)
      freeVariableCertificate2 p0007
  have p0009 :=
    @g_adantl
      (syn_wrex x (syn_cnnc) (.classEq B (syn_cplc (syn_cplc A (.cv x)) (syn_c1c))))
      (syn_wrex y (syn_cnnc) (.classEq B (syn_cplc A (.cv y)))) (syn_wne A (syn_c0)) p0008
  have p0010 :=
    @g_a1i
      (.imp (syn_wa (syn_wne A (syn_c0))
          (syn_wrex x (syn_cnnc) (.classEq B (syn_cplc (syn_cplc A (.cv x)) (syn_c1c)))))
        (syn_wrex y (syn_cnnc) (.classEq B (syn_cplc A (.cv y)))))
      (syn_wa (.classMem A V) (.classMem B W)) p0009
  have p0011 :=
    @g_opkltfing x A B V W (by exact (show x ∉ (A).fv from (by exact fresh_x_not_A)))
      (by exact (show x ∉ (B).fv from (by exact fresh_x_not_B)))
  have p0012 :=
    @g_opklefing y A B V W (by exact (show y ∉ (A).fv from (by exact fresh_y_not_A)))
      (by exact (show y ∉ (B).fv from (by exact fresh_y_not_B)))
  have p0013 :=
    @g_n_3imtr4d (syn_wa (.classMem A V) (.classMem B W))
      (syn_wa (syn_wne A (syn_c0))
        (syn_wrex x (syn_cnnc) (.classEq B (syn_cplc (syn_cplc A (.cv x)) (syn_c1c)))))
      (syn_wrex y (syn_cnnc) (.classEq B (syn_cplc A (.cv y))))
      (.classMem (syn_copk A B) (syn_cltfin)) (.classMem (syn_copk A B) (syn_clefin))
      p0010 p0011 p0012
  exact p0013

@[expose]
noncomputable def g_lenltfin (A : Class) (B : Class) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
        (syn_wb (.classMem (syn_copk A B) (syn_clefin))
          (.neg (.classMem (syn_copk B A) (syn_cltfin))))) :=
  by
  have p0000 := @g_ltfinirr A
  have p0001 :=
    @g_adantr (.classMem A (syn_cnnc)) (.neg (.classMem (syn_copk A A) (syn_cltfin)))
      (.classMem B (syn_cnnc)) p0000
  have p0002 :=
    @g_adantr (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
      (.neg (.classMem (syn_copk A A) (syn_cltfin)))
      (.classMem (syn_copk A B) (syn_clefin)) p0001
  have p0003 := @g_leltfintr A B A
  have p0004 :=
    @g_n_3anidm13 (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))
      (.imp (syn_wa (.classMem (syn_copk A B) (syn_clefin))
          (.classMem (syn_copk B A) (syn_cltfin))) (.classMem (syn_copk A A) (syn_cltfin)))
      p0003
  have p0005 :=
    @g_expdimp (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
      (.classMem (syn_copk A B) (syn_clefin)) (.classMem (syn_copk B A) (syn_cltfin))
      (.classMem (syn_copk A A) (syn_cltfin)) p0004
  have p0006 :=
    @g_mtod
      (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
        (.classMem (syn_copk A B) (syn_clefin)))
      (.classMem (syn_copk B A) (syn_cltfin)) (.classMem (syn_copk A A) (syn_cltfin))
      p0002 p0005
  have p0007 :=
    @g_ex (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
      (.classMem (syn_copk A B) (syn_clefin))
      (.neg (.classMem (syn_copk B A) (syn_cltfin))) p0006
  have p0008 := @g_nulge A (syn_cnnc)
  have p0009 :=
    @g_ancoms (.classMem (syn_c0) (syn_cnnc)) (.classMem A (syn_cnnc))
      (.classMem (syn_copk A (syn_c0)) (syn_clefin)) p0008
  have p0010 := @g_eleq1 B (syn_c0) (syn_cnnc)
  have p0011 :=
    @g_anbi2d (.classEq B (syn_c0)) (.classMem B (syn_cnnc))
      (.classMem (syn_c0) (syn_cnnc)) (.classMem A (syn_cnnc)) p0010
  have p0012 := @g_opkeq2 B (syn_c0) A
  have p0013 :=
    @g_eleq1d (.classEq B (syn_c0)) (syn_copk A B) (syn_copk A (syn_c0)) (syn_clefin)
      p0012
  have p0014 :=
    @g_imbi12d (.classEq B (syn_c0))
      (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
      (syn_wa (.classMem A (syn_cnnc)) (.classMem (syn_c0) (syn_cnnc)))
      (.classMem (syn_copk A B) (syn_clefin))
      (.classMem (syn_copk A (syn_c0)) (syn_clefin)) p0011 p0013
  have p0015 :=
    @g_mpbiri (.classEq B (syn_c0))
      (.imp (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
        (.classMem (syn_copk A B) (syn_clefin)))
      (.imp (syn_wa (.classMem A (syn_cnnc)) (.classMem (syn_c0) (syn_cnnc)))
        (.classMem (syn_copk A (syn_c0)) (syn_clefin)))
      p0009 p0014
  have p0016 :=
    @g_a1dd (.classEq B (syn_c0))
      (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
      (.classMem (syn_copk A B) (syn_clefin))
      (.neg (.classMem (syn_copk B A) (syn_cltfin))) p0015
  have p0017 :=
    @g_simplr (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)) (syn_wne B (syn_c0))
  have p0018 :=
    @g_simpll (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)) (syn_wne B (syn_c0))
  have p0019 :=
    @g_simpr (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
      (syn_wne B (syn_c0))
  have p0020 := @g_ltfintri B A
  have p0021 :=
    @g_syl3anc
      (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (syn_wne B (syn_c0)))
      (.classMem B (syn_cnnc)) (.classMem A (syn_cnnc)) (syn_wne B (syn_c0))
      (syn_w3o (.classMem (syn_copk B A) (syn_cltfin)) (.classEq B A)
        (.classMem (syn_copk A B) (syn_cltfin)))
      p0017 p0018 p0019 p0020
  have p0022 :=
    @g_n_3orass (.classMem (syn_copk B A) (syn_cltfin)) (.classEq B A)
      (.classMem (syn_copk A B) (syn_cltfin))
  have p0023 :=
    @g_sylib
      (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (syn_wne B (syn_c0)))
      (syn_w3o (.classMem (syn_copk B A) (syn_cltfin)) (.classEq B A)
        (.classMem (syn_copk A B) (syn_cltfin)))
      (syn_wo (.classMem (syn_copk B A) (syn_cltfin))
        (syn_wo (.classEq B A) (.classMem (syn_copk A B) (syn_cltfin))))
      p0021 p0022
  have p0024 :=
    @g_ord
      (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (syn_wne B (syn_c0)))
      (.classMem (syn_copk B A) (syn_cltfin))
      (syn_wo (.classEq B A) (.classMem (syn_copk A B) (syn_cltfin))) p0023
  have p0025 := @g_lefinrflx A (syn_cnnc)
  have p0026 :=
    @g_adantr (.classMem A (syn_cnnc)) (.classMem (syn_copk A A) (syn_clefin))
      (.classMem B (syn_cnnc)) p0025
  have p0027 := @g_opkeq2 B A A
  have p0028 := @g_eleq1d (.classEq B A) (syn_copk A B) (syn_copk A A) (syn_clefin) p0027
  have p0029 :=
    @g_syl5ibrcom (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
      (.classMem (syn_copk A B) (syn_clefin)) (.classEq B A)
      (.classMem (syn_copk A A) (syn_clefin)) p0026 p0028
  have p0030 :=
    @g_adantr (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
      (.imp (.classEq B A) (.classMem (syn_copk A B) (syn_clefin))) (syn_wne B (syn_c0))
      p0029
  have p0031 := @g_ltlefin A B (syn_cnnc) (syn_cnnc)
  have p0032 :=
    @g_adantr (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
      (.imp (.classMem (syn_copk A B) (syn_cltfin)) (.classMem (syn_copk A B) (syn_clefin)))
      (syn_wne B (syn_c0)) p0031
  have p0033 :=
    @g_jaod
      (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (syn_wne B (syn_c0)))
      (.classEq B A) (.classMem (syn_copk A B) (syn_clefin))
      (.classMem (syn_copk A B) (syn_cltfin)) p0030 p0032
  have p0034 :=
    @g_syld
      (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (syn_wne B (syn_c0)))
      (.neg (.classMem (syn_copk B A) (syn_cltfin)))
      (syn_wo (.classEq B A) (.classMem (syn_copk A B) (syn_cltfin)))
      (.classMem (syn_copk A B) (syn_clefin)) p0024 p0033
  have p0035 :=
    @g_expcom (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
      (syn_wne B (syn_c0))
      (.imp (.neg (.classMem (syn_copk B A) (syn_cltfin)))
        (.classMem (syn_copk A B) (syn_clefin)))
      p0034
  have p0036 :=
    @g_pm2_61ine
      (.imp (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
        (.imp (.neg (.classMem (syn_copk B A) (syn_cltfin)))
          (.classMem (syn_copk A B) (syn_clefin))))
      B (syn_c0) p0016 p0035
  have p0037 :=
    @g_impbid (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
      (.classMem (syn_copk A B) (syn_clefin))
      (.neg (.classMem (syn_copk B A) (syn_cltfin))) p0007 p0036
  exact p0037


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk009StructuralPart046`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_ssfin (A : Class) (B : Class) (V : Class) :
    Nominal.NPrf
      (.imp (syn_w3a (.classMem A V) (.classMem B (syn_cfin)) (syn_wss A B))
        (.classMem A (syn_cfin))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ V.fv
  let a : Var := freshVar proofSupport 0
  let b : Var := freshVar proofSupport 1
  let n : Var := freshVar proofSupport 2
  let m : Var := freshVar proofSupport 3
  let d : Var := freshVar proofSupport 4
  let k : Var := freshVar proofSupport 5
  let c : Var := freshVar proofSupport 6
  let t : Var := freshVar proofSupport 7
  let x : Var := freshVar proofSupport 8
  have fresh_a : a ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_a_not_A : a ∉ A.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_a_not_B : a ∉ B.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_b : b ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_b_not_B : b ∉ B.fv := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_a_ne_b : a ≠ b :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_b_ne_a : b ≠ a := Ne.symm fresh_a_ne_b
  have fresh_a_ne_n : a ≠ n :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_n_ne_a : n ≠ a := Ne.symm fresh_a_ne_n
  have fresh_a_ne_m : a ≠ m :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_m_ne_a : m ≠ a := Ne.symm fresh_a_ne_m
  have fresh_a_ne_d : a ≠ d :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 0) (j := 4) (by decide)
  have fresh_d_ne_a : d ≠ a := Ne.symm fresh_a_ne_d
  have fresh_a_ne_k : a ≠ k :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 0) (j := 5) (by decide)
  have fresh_k_ne_a : k ≠ a := Ne.symm fresh_a_ne_k
  have fresh_a_ne_c : a ≠ c :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 0) (j := 6) (by decide)
  have fresh_c_ne_a : c ≠ a := Ne.symm fresh_a_ne_c
  have fresh_a_ne_x : a ≠ x :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 8
    exact freshVar_injective proofSupport (i := 0) (j := 8) (by decide)
  have fresh_x_ne_a : x ≠ a := Ne.symm fresh_a_ne_x
  have fresh_b_ne_n : b ≠ n :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_n_ne_b : n ≠ b := Ne.symm fresh_b_ne_n
  have fresh_b_ne_m : b ≠ m :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_m_ne_b : m ≠ b := Ne.symm fresh_b_ne_m
  have fresh_b_ne_d : b ≠ d :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 1) (j := 4) (by decide)
  have fresh_d_ne_b : d ≠ b := Ne.symm fresh_b_ne_d
  have fresh_b_ne_k : b ≠ k :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 1) (j := 5) (by decide)
  have fresh_k_ne_b : k ≠ b := Ne.symm fresh_b_ne_k
  have fresh_b_ne_c : b ≠ c :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 1) (j := 6) (by decide)
  have fresh_c_ne_b : c ≠ b := Ne.symm fresh_b_ne_c
  have fresh_b_ne_t : b ≠ t :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 7
    exact freshVar_injective proofSupport (i := 1) (j := 7) (by decide)
  have fresh_t_ne_b : t ≠ b := Ne.symm fresh_b_ne_t
  have fresh_b_ne_x : b ≠ x :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 8
    exact freshVar_injective proofSupport (i := 1) (j := 8) (by decide)
  have fresh_x_ne_b : x ≠ b := Ne.symm fresh_b_ne_x
  have fresh_n_ne_m : n ≠ m :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_m_ne_n : m ≠ n := Ne.symm fresh_n_ne_m
  have fresh_m_ne_d : m ≠ d :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 3) (j := 4) (by decide)
  have fresh_m_ne_k : m ≠ k :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 3) (j := 5) (by decide)
  have fresh_k_ne_m : k ≠ m := Ne.symm fresh_m_ne_k
  have fresh_m_ne_c : m ≠ c :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 3) (j := 6) (by decide)
  have fresh_m_ne_t : m ≠ t :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 7
    exact freshVar_injective proofSupport (i := 3) (j := 7) (by decide)
  have fresh_t_ne_m : t ≠ m := Ne.symm fresh_m_ne_t
  have fresh_d_ne_k : d ≠ k :=
    by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 4) (j := 5) (by decide)
  have fresh_d_ne_c : d ≠ c :=
    by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 4) (j := 6) (by decide)
  have fresh_c_ne_d : c ≠ d := Ne.symm fresh_d_ne_c
  have fresh_d_ne_x : d ≠ x :=
    by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 8
    exact freshVar_injective proofSupport (i := 4) (j := 8) (by decide)
  have fresh_x_ne_d : x ≠ d := Ne.symm fresh_d_ne_x
  have fresh_k_ne_c : k ≠ c :=
    by
    change freshVar proofSupport 5 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 5) (j := 6) (by decide)
  have fresh_c_ne_k : c ≠ k := Ne.symm fresh_k_ne_c
  have fresh_k_ne_x : k ≠ x :=
    by
    change freshVar proofSupport 5 ≠ freshVar proofSupport 8
    exact freshVar_injective proofSupport (i := 5) (j := 8) (by decide)
  have fresh_x_ne_k : x ≠ k := Ne.symm fresh_k_ne_x
  have fresh_c_ne_x : c ≠ x :=
    by
    change freshVar proofSupport 6 ≠ freshVar proofSupport 8
    exact freshVar_injective proofSupport (i := 6) (j := 8) (by decide)
  have fresh_x_ne_c : x ≠ c := Ne.symm fresh_c_ne_x
  have p0000 := @g_sseq1 (.cv a) A B
  have p0001 := @g_eleq1 (.cv a) A (syn_cfin)
  have p0002 :=
    @g_imbi12d (.classEq (.cv a) A) (syn_wss (.cv a) B) (syn_wss A B)
      (.classMem (.cv a) (syn_cfin)) (.classMem A (syn_cfin)) p0000 p0001
  have p0003 :=
    @g_imbi2d (.classEq (.cv a) A)
      (.imp (syn_wss (.cv a) B) (.classMem (.cv a) (syn_cfin)))
      (.imp (syn_wss A B) (.classMem A (syn_cfin))) (.classMem B (syn_cfin)) p0002
  have p0004 := @g_sseq2 (.cv b) B (.cv a)
  have p0005 :=
    @g_imbi1d (.classEq (.cv b) B) (syn_wss (.cv a) (.cv b)) (syn_wss (.cv a) B)
      (.classMem (.cv a) (syn_cfin)) p0004
  have freeVariableCertificate0 : n ∉ ((Class.cv b)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_n_ne_b, not_false_eq_true]
  have p0006 := @g_elfin n (.cv b) freeVariableCertificate0
  have p0007 := @g_vex m
  have p0008 :=
    @g_elcompl (.cv m)
      (syn_cimak (syn_cin (syn_cssetk)
          (syn_cxpk (syn_cpw1 (syn_cimak (syn_cssetk) (syn_ccompl (syn_cfin)))) (syn_cvv)))
        (syn_c1c))
      p0007
  have p0009 :=
    @g_alcom
      (.imp (syn_wa (.objMem b m) (syn_wss (.cv a) (.cv b))) (.classMem (.cv a) (syn_cfin)))
      a b
  have p0010 :=
    @g_impexp (.objMem b m) (syn_wss (.cv a) (.cv b)) (.classMem (.cv a) (syn_cfin))
  have p0011 :=
    @g_albii
      (.imp (syn_wa (.objMem b m) (syn_wss (.cv a) (.cv b))) (.classMem (.cv a) (syn_cfin)))
      (.imp (.objMem b m) (.imp (syn_wss (.cv a) (.cv b)) (.classMem (.cv a) (syn_cfin))))
      a p0010
  have freeVariableCertificate1 : a ∉ ((Wff.objMem b m)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_objMem, Finset.mem_insert,
      Finset.mem_singleton, fresh_a_ne_b, fresh_a_ne_m, or_false, not_false_eq_true]
  have p0012 :=
    @g_n_19_21v (.objMem b m)
      (.imp (syn_wss (.cv a) (.cv b)) (.classMem (.cv a) (syn_cfin))) a
      freeVariableCertificate1
  have p0013 :=
    @g_bitri
      (.all a (.imp (syn_wa (.objMem b m) (syn_wss (.cv a) (.cv b)))
          (.classMem (.cv a) (syn_cfin))))
      (.all a (.imp (.objMem b m)
          (.imp (syn_wss (.cv a) (.cv b)) (.classMem (.cv a) (syn_cfin)))))
      (.imp (.objMem b m)
        (.all a (.imp (syn_wss (.cv a) (.cv b)) (.classMem (.cv a) (syn_cfin)))))
      p0011 p0012
  have p0014 :=
    @g_albii
      (.all a (.imp (syn_wa (.objMem b m) (syn_wss (.cv a) (.cv b)))
          (.classMem (.cv a) (syn_cfin))))
      (.imp (.objMem b m)
        (.all a (.imp (syn_wss (.cv a) (.cv b)) (.classMem (.cv a) (syn_cfin)))))
      b p0013
  have freeVariableCertificate2 :
    t ∉
      ((syn_cin (syn_cssetk)
          (syn_cxpk (syn_cpw1 (syn_cimak (syn_cssetk) (syn_ccompl (syn_cfin))))
            (syn_cvv)))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfin,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
      Finset.notMem_empty, or_false, not_false_eq_true]
  have freeVariableCertificate3 : t ∉ ((Class.cv m)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_t_ne_m, not_false_eq_true]
  have p0015 :=
    @g_elimak t
      (syn_cin (syn_cssetk)
        (syn_cxpk (syn_cpw1 (syn_cimak (syn_cssetk) (syn_ccompl (syn_cfin)))) (syn_cvv)))
      (syn_c1c) (.cv m) freeVariableCertificate2
      (by
        exact
          (show t ∉ ((syn_c1c)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c];
              exact (show t ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
      freeVariableCertificate3 p0007
  have p0016 :=
    (Nominal.biimpRefl (syn_wrex t (syn_c1c) (.classMem (syn_copk (.cv t) (.cv m))
          (syn_cin (syn_cssetk)
            (syn_cxpk (syn_cpw1 (syn_cimak (syn_cssetk) (syn_ccompl (syn_cfin)))) (syn_cvv))))))
  have freeVariableCertificate4 : b ∉ ((Class.cv t)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_b_ne_t, not_false_eq_true]
  have p0017 := @g_el1c b (.cv t) freeVariableCertificate4
  have p0018 :=
    @g_anbi1i (.classMem (.cv t) (syn_c1c))
      (syn_wex b (.classEq (.cv t) (syn_csn (.cv b))))
      (.classMem (syn_copk (.cv t) (.cv m)) (syn_cin (syn_cssetk)
          (syn_cxpk (syn_cpw1 (syn_cimak (syn_cssetk) (syn_ccompl (syn_cfin)))) (syn_cvv))))
      p0017
  have freeVariableCertificate5 :
    b ∉
      ((Wff.classMem (syn_copk (.cv t) (.cv m)) (syn_cin (syn_cssetk)
            (syn_cxpk (syn_cpw1 (syn_cimak (syn_cssetk) (syn_ccompl (syn_cfin))))
              (syn_cvv))))).fv :=
    by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfin,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_b_ne_t, fresh_b_ne_m, or_false,
      not_false_eq_true]
  have p0019 :=
    @g_n_19_41v (.classEq (.cv t) (syn_csn (.cv b)))
      (.classMem (syn_copk (.cv t) (.cv m)) (syn_cin (syn_cssetk)
          (syn_cxpk (syn_cpw1 (syn_cimak (syn_cssetk) (syn_ccompl (syn_cfin)))) (syn_cvv))))
      b freeVariableCertificate5
  have p0020 :=
    @g_bitr4i
      (syn_wa (.classMem (.cv t) (syn_c1c)) (.classMem (syn_copk (.cv t) (.cv m))
          (syn_cin (syn_cssetk)
            (syn_cxpk (syn_cpw1 (syn_cimak (syn_cssetk) (syn_ccompl (syn_cfin)))) (syn_cvv)))))
      (syn_wa (syn_wex b (.classEq (.cv t) (syn_csn (.cv b))))
        (.classMem (syn_copk (.cv t) (.cv m)) (syn_cin (syn_cssetk)
            (syn_cxpk (syn_cpw1 (syn_cimak (syn_cssetk) (syn_ccompl (syn_cfin)))) (syn_cvv)))))
      (syn_wex b (syn_wa (.classEq (.cv t) (syn_csn (.cv b)))
          (.classMem (syn_copk (.cv t) (.cv m)) (syn_cin (syn_cssetk)
              (syn_cxpk (syn_cpw1 (syn_cimak (syn_cssetk) (syn_ccompl (syn_cfin))))
                (syn_cvv))))))
      p0018 p0019
  have p0021 :=
    @g_exbii
      (syn_wa (.classMem (.cv t) (syn_c1c)) (.classMem (syn_copk (.cv t) (.cv m))
          (syn_cin (syn_cssetk)
            (syn_cxpk (syn_cpw1 (syn_cimak (syn_cssetk) (syn_ccompl (syn_cfin)))) (syn_cvv)))))
      (syn_wex b (syn_wa (.classEq (.cv t) (syn_csn (.cv b)))
          (.classMem (syn_copk (.cv t) (.cv m)) (syn_cin (syn_cssetk)
              (syn_cxpk (syn_cpw1 (syn_cimak (syn_cssetk) (syn_ccompl (syn_cfin))))
                (syn_cvv))))))
      t p0020
  have p0022 :=
    @g_excom
      (syn_wa (.classEq (.cv t) (syn_csn (.cv b))) (.classMem (syn_copk (.cv t) (.cv m))
          (syn_cin (syn_cssetk)
            (syn_cxpk (syn_cpw1 (syn_cimak (syn_cssetk) (syn_ccompl (syn_cfin)))) (syn_cvv)))))
      b t
  have p0023 :=
    @g_bitr4i
      (syn_wex t (syn_wa (.classMem (.cv t) (syn_c1c)) (.classMem (syn_copk (.cv t) (.cv m))
            (syn_cin (syn_cssetk)
              (syn_cxpk (syn_cpw1 (syn_cimak (syn_cssetk) (syn_ccompl (syn_cfin))))
                (syn_cvv))))))
      (syn_wex t (syn_wex b (syn_wa (.classEq (.cv t) (syn_csn (.cv b)))
            (.classMem (syn_copk (.cv t) (.cv m)) (syn_cin (syn_cssetk)
                (syn_cxpk (syn_cpw1 (syn_cimak (syn_cssetk) (syn_ccompl (syn_cfin))))
                  (syn_cvv)))))))
      (syn_wex b (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (.cv b)))
            (.classMem (syn_copk (.cv t) (.cv m)) (syn_cin (syn_cssetk)
                (syn_cxpk (syn_cpw1 (syn_cimak (syn_cssetk) (syn_ccompl (syn_cfin))))
                  (syn_cvv)))))))
      p0021 p0022
  have p0024 := @g_snex (.cv b)
  have p0025 := @g_opkeq1 (.cv t) (syn_csn (.cv b)) (.cv m)
  have p0026 :=
    @g_eleq1d (.classEq (.cv t) (syn_csn (.cv b))) (syn_copk (.cv t) (.cv m))
      (syn_copk (syn_csn (.cv b)) (.cv m))
      (syn_cin (syn_cssetk)
        (syn_cxpk (syn_cpw1 (syn_cimak (syn_cssetk) (syn_ccompl (syn_cfin)))) (syn_cvv)))
      p0025
  have freeVariableCertificate6 : t ∉ ((syn_csn (.cv b))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_t_ne_b,
      not_false_eq_true]
  have freeVariableCertificate7 :
    t ∉
      ((Wff.classMem (syn_copk (syn_csn (.cv b)) (.cv m)) (syn_cin (syn_cssetk)
            (syn_cxpk (syn_cpw1 (syn_cimak (syn_cssetk) (syn_ccompl (syn_cfin))))
              (syn_cvv))))).fv :=
    by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfin,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_t_ne_b, fresh_t_ne_m, or_false,
      not_false_eq_true]
  have p0027 :=
    @g_ceqsexv
      (.classMem (syn_copk (.cv t) (.cv m)) (syn_cin (syn_cssetk)
          (syn_cxpk (syn_cpw1 (syn_cimak (syn_cssetk) (syn_ccompl (syn_cfin)))) (syn_cvv))))
      (.classMem (syn_copk (syn_csn (.cv b)) (.cv m)) (syn_cin (syn_cssetk)
          (syn_cxpk (syn_cpw1 (syn_cimak (syn_cssetk) (syn_ccompl (syn_cfin)))) (syn_cvv))))
      t (syn_csn (.cv b)) freeVariableCertificate6 freeVariableCertificate7 p0024 p0026
  have p0028 :=
    @g_elin (syn_copk (syn_csn (.cv b)) (.cv m)) (syn_cssetk)
      (syn_cxpk (syn_cpw1 (syn_cimak (syn_cssetk) (syn_ccompl (syn_cfin)))) (syn_cvv))
  have p0029 := @g_vex b
  have p0030 := @g_elssetk (.cv b) (.cv m) p0029 p0007
  have p0031 :=
    @g_opkelxpk (syn_csn (.cv b)) (.cv m)
      (syn_cpw1 (syn_cimak (syn_cssetk) (syn_ccompl (syn_cfin)))) (syn_cvv) p0024 p0007
  have p0032 :=
    @g_mpbiran2
      (.classMem (syn_copk (syn_csn (.cv b)) (.cv m))
        (syn_cxpk (syn_cpw1 (syn_cimak (syn_cssetk) (syn_ccompl (syn_cfin)))) (syn_cvv)))
      (.classMem (syn_csn (.cv b)) (syn_cpw1 (syn_cimak (syn_cssetk) (syn_ccompl (syn_cfin)))))
      (.classMem (.cv m) (syn_cvv)) p0007 p0031
  have p0033 := @g_snelpw1 (.cv b) (syn_cimak (syn_cssetk) (syn_ccompl (syn_cfin)))
  have freeVariableCertificate8 : a ∉ ((syn_ccompl (syn_cfin))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfin, Finset.notMem_empty,
      not_false_eq_true]
  have freeVariableCertificate9 : a ∉ ((Class.cv b)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_a_ne_b, not_false_eq_true]
  have p0034 :=
    @g_elimak a (syn_cssetk) (syn_ccompl (syn_cfin)) (.cv b)
      (by
        exact
          (show a ∉ ((syn_cssetk)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk];
              exact (show a ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
      freeVariableCertificate8 freeVariableCertificate9 p0029
  have p0035 :=
    (Nominal.biimpRefl (syn_wrex a (syn_ccompl (syn_cfin))
        (.classMem (syn_copk (.cv a) (.cv b)) (syn_cssetk))))
  have p0036 :=
    @g_ancom (.classMem (.cv a) (syn_ccompl (syn_cfin)))
      (.classMem (syn_copk (.cv a) (.cv b)) (syn_cssetk))
  have p0037 := @g_vex a
  have p0038 := @g_opkelssetkg (.cv a) (.cv b) (syn_cvv) (syn_cvv)
  have p0039 :=
    @g_mp2an (.classMem (.cv a) (syn_cvv)) (.classMem (.cv b) (syn_cvv))
      (syn_wb (.classMem (syn_copk (.cv a) (.cv b)) (syn_cssetk)) (syn_wss (.cv a) (.cv b)))
      p0037 p0029 p0038
  have p0040 := @g_elcompl (.cv a) (syn_cfin) p0037
  have p0041 :=
    @g_anbi12i (.classMem (syn_copk (.cv a) (.cv b)) (syn_cssetk))
      (syn_wss (.cv a) (.cv b)) (.classMem (.cv a) (syn_ccompl (syn_cfin)))
      (.neg (.classMem (.cv a) (syn_cfin))) p0039 p0040
  have p0042 :=
    @g_bitri
      (syn_wa (.classMem (.cv a) (syn_ccompl (syn_cfin)))
        (.classMem (syn_copk (.cv a) (.cv b)) (syn_cssetk)))
      (syn_wa (.classMem (syn_copk (.cv a) (.cv b)) (syn_cssetk))
        (.classMem (.cv a) (syn_ccompl (syn_cfin))))
      (syn_wa (syn_wss (.cv a) (.cv b)) (.neg (.classMem (.cv a) (syn_cfin)))) p0036 p0041
  have p0043 :=
    @g_exbii
      (syn_wa (.classMem (.cv a) (syn_ccompl (syn_cfin)))
        (.classMem (syn_copk (.cv a) (.cv b)) (syn_cssetk)))
      (syn_wa (syn_wss (.cv a) (.cv b)) (.neg (.classMem (.cv a) (syn_cfin)))) a p0042
  have p0044 :=
    @g_bitri
      (syn_wrex a (syn_ccompl (syn_cfin)) (.classMem (syn_copk (.cv a) (.cv b)) (syn_cssetk)))
      (syn_wex a (syn_wa (.classMem (.cv a) (syn_ccompl (syn_cfin)))
          (.classMem (syn_copk (.cv a) (.cv b)) (syn_cssetk))))
      (syn_wex a (syn_wa (syn_wss (.cv a) (.cv b)) (.neg (.classMem (.cv a) (syn_cfin)))))
      p0035 p0043
  have p0045 := @g_exanali (syn_wss (.cv a) (.cv b)) (.classMem (.cv a) (syn_cfin)) a
  have p0046 :=
    @g_n_3bitri (.classMem (.cv b) (syn_cimak (syn_cssetk) (syn_ccompl (syn_cfin))))
      (syn_wrex a (syn_ccompl (syn_cfin)) (.classMem (syn_copk (.cv a) (.cv b)) (syn_cssetk)))
      (syn_wex a (syn_wa (syn_wss (.cv a) (.cv b)) (.neg (.classMem (.cv a) (syn_cfin)))))
      (.neg (.all a (.imp (syn_wss (.cv a) (.cv b)) (.classMem (.cv a) (syn_cfin)))))
      p0034 p0044 p0045
  have p0047 :=
    @g_n_3bitri
      (.classMem (syn_copk (syn_csn (.cv b)) (.cv m))
        (syn_cxpk (syn_cpw1 (syn_cimak (syn_cssetk) (syn_ccompl (syn_cfin)))) (syn_cvv)))
      (.classMem (syn_csn (.cv b)) (syn_cpw1 (syn_cimak (syn_cssetk) (syn_ccompl (syn_cfin)))))
      (.classMem (.cv b) (syn_cimak (syn_cssetk) (syn_ccompl (syn_cfin))))
      (.neg (.all a (.imp (syn_wss (.cv a) (.cv b)) (.classMem (.cv a) (syn_cfin)))))
      p0032 p0033 p0046
  have p0048_e00_recanon :
    Nominal.NPrf
      (syn_wb (.classMem (syn_copk (syn_csn (.cv b)) (.cv m)) (syn_cssetk)) (.objMem b m)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_copk syn_cpr syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_csn
          syn_cssetk syn_wex
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0030
  have p0048 :=
    @g_anbi12i (.classMem (syn_copk (syn_csn (.cv b)) (.cv m)) (syn_cssetk)) (.objMem b m)
      (.classMem (syn_copk (syn_csn (.cv b)) (.cv m))
        (syn_cxpk (syn_cpw1 (syn_cimak (syn_cssetk) (syn_ccompl (syn_cfin)))) (syn_cvv)))
      (.neg (.all a (.imp (syn_wss (.cv a) (.cv b)) (.classMem (.cv a) (syn_cfin)))))
      p0048_e00_recanon p0047
  have p0049 :=
    @g_n_3bitri
      (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (.cv b)))
          (.classMem (syn_copk (.cv t) (.cv m)) (syn_cin (syn_cssetk)
              (syn_cxpk (syn_cpw1 (syn_cimak (syn_cssetk) (syn_ccompl (syn_cfin))))
                (syn_cvv))))))
      (.classMem (syn_copk (syn_csn (.cv b)) (.cv m)) (syn_cin (syn_cssetk)
          (syn_cxpk (syn_cpw1 (syn_cimak (syn_cssetk) (syn_ccompl (syn_cfin)))) (syn_cvv))))
      (syn_wa (.classMem (syn_copk (syn_csn (.cv b)) (.cv m)) (syn_cssetk))
        (.classMem (syn_copk (syn_csn (.cv b)) (.cv m))
          (syn_cxpk (syn_cpw1 (syn_cimak (syn_cssetk) (syn_ccompl (syn_cfin)))) (syn_cvv))))
      (syn_wa (.objMem b m)
        (.neg (.all a (.imp (syn_wss (.cv a) (.cv b)) (.classMem (.cv a) (syn_cfin))))))
      p0027 p0028 p0048
  have p0050 :=
    @g_exbii
      (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (.cv b)))
          (.classMem (syn_copk (.cv t) (.cv m)) (syn_cin (syn_cssetk)
              (syn_cxpk (syn_cpw1 (syn_cimak (syn_cssetk) (syn_ccompl (syn_cfin))))
                (syn_cvv))))))
      (syn_wa (.objMem b m)
        (.neg (.all a (.imp (syn_wss (.cv a) (.cv b)) (.classMem (.cv a) (syn_cfin))))))
      b p0049
  have p0051 :=
    @g_n_3bitri
      (syn_wrex t (syn_c1c) (.classMem (syn_copk (.cv t) (.cv m)) (syn_cin (syn_cssetk)
            (syn_cxpk (syn_cpw1 (syn_cimak (syn_cssetk) (syn_ccompl (syn_cfin)))) (syn_cvv)))))
      (syn_wex t (syn_wa (.classMem (.cv t) (syn_c1c)) (.classMem (syn_copk (.cv t) (.cv m))
            (syn_cin (syn_cssetk)
              (syn_cxpk (syn_cpw1 (syn_cimak (syn_cssetk) (syn_ccompl (syn_cfin))))
                (syn_cvv))))))
      (syn_wex b (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (.cv b)))
            (.classMem (syn_copk (.cv t) (.cv m)) (syn_cin (syn_cssetk)
                (syn_cxpk (syn_cpw1 (syn_cimak (syn_cssetk) (syn_ccompl (syn_cfin))))
                  (syn_cvv)))))))
      (syn_wex b (syn_wa (.objMem b m) (.neg
            (.all a (.imp (syn_wss (.cv a) (.cv b)) (.classMem (.cv a) (syn_cfin)))))))
      p0016 p0023 p0050
  have p0052 :=
    @g_exanali (.objMem b m)
      (.all a (.imp (syn_wss (.cv a) (.cv b)) (.classMem (.cv a) (syn_cfin)))) b
  have p0053 :=
    @g_n_3bitri
      (.classMem (.cv m) (syn_cimak (syn_cin (syn_cssetk)
            (syn_cxpk (syn_cpw1 (syn_cimak (syn_cssetk) (syn_ccompl (syn_cfin)))) (syn_cvv)))
          (syn_c1c)))
      (syn_wrex t (syn_c1c) (.classMem (syn_copk (.cv t) (.cv m)) (syn_cin (syn_cssetk)
            (syn_cxpk (syn_cpw1 (syn_cimak (syn_cssetk) (syn_ccompl (syn_cfin)))) (syn_cvv)))))
      (syn_wex b (syn_wa (.objMem b m) (.neg
            (.all a (.imp (syn_wss (.cv a) (.cv b)) (.classMem (.cv a) (syn_cfin)))))))
      (.neg (.all b (.imp (.objMem b m)
            (.all a (.imp (syn_wss (.cv a) (.cv b)) (.classMem (.cv a) (syn_cfin)))))))
      p0015 p0051 p0052
  have p0054 :=
    @g_con2bii
      (.classMem (.cv m) (syn_cimak (syn_cin (syn_cssetk)
            (syn_cxpk (syn_cpw1 (syn_cimak (syn_cssetk) (syn_ccompl (syn_cfin)))) (syn_cvv)))
          (syn_c1c)))
      (.all b (.imp (.objMem b m)
          (.all a (.imp (syn_wss (.cv a) (.cv b)) (.classMem (.cv a) (syn_cfin))))))
      p0053
  have p0055 :=
    @g_n_3bitri
      (.all a (.all b (.imp (syn_wa (.objMem b m) (syn_wss (.cv a) (.cv b)))
            (.classMem (.cv a) (syn_cfin)))))
      (.all b (.all a (.imp (syn_wa (.objMem b m) (syn_wss (.cv a) (.cv b)))
            (.classMem (.cv a) (syn_cfin)))))
      (.all b (.imp (.objMem b m)
          (.all a (.imp (syn_wss (.cv a) (.cv b)) (.classMem (.cv a) (syn_cfin))))))
      (.neg (.classMem (.cv m) (syn_cimak (syn_cin (syn_cssetk)
              (syn_cxpk (syn_cpw1 (syn_cimak (syn_cssetk) (syn_ccompl (syn_cfin)))) (syn_cvv)))
            (syn_c1c))))
      p0009 p0014 p0054
  have p0056 :=
    @g_bitr4i
      (.classMem (.cv m) (syn_ccompl (syn_cimak (syn_cin (syn_cssetk)
              (syn_cxpk (syn_cpw1 (syn_cimak (syn_cssetk) (syn_ccompl (syn_cfin)))) (syn_cvv)))
            (syn_c1c))))
      (.neg (.classMem (.cv m) (syn_cimak (syn_cin (syn_cssetk)
              (syn_cxpk (syn_cpw1 (syn_cimak (syn_cssetk) (syn_ccompl (syn_cfin)))) (syn_cvv)))
            (syn_c1c))))
      (.all a (.all b (.imp (syn_wa (.objMem b m) (syn_wss (.cv a) (.cv b)))
            (.classMem (.cv a) (syn_cfin)))))
      p0008 p0055
  have freeVariableCertificate10 :
    m ∉
      ((syn_ccompl (syn_cimak (syn_cin (syn_cssetk)
              (syn_cxpk (syn_cpw1 (syn_cimak (syn_cssetk) (syn_ccompl (syn_cfin)))) (syn_cvv)))
            (syn_c1c)))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfin,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
      Finset.notMem_empty, or_false, not_false_eq_true]
  have p0057 :=
    @g_eqabi
      (.all a (.all b (.imp (syn_wa (.objMem b m) (syn_wss (.cv a) (.cv b)))
            (.classMem (.cv a) (syn_cfin)))))
      m
      (syn_ccompl (syn_cimak (syn_cin (syn_cssetk)
            (syn_cxpk (syn_cpw1 (syn_cimak (syn_cssetk) (syn_ccompl (syn_cfin)))) (syn_cvv)))
          (syn_c1c)))
      freeVariableCertificate10 p0056
  have p0058 := @g_ssetkex
  have p0060 := @g_finex
  have p0061 := @g_complex (syn_cfin) p0060
  have p0062 := @g_imakex (syn_cssetk) (syn_ccompl (syn_cfin)) p0058 p0061
  have p0063 := @g_pw1ex (syn_cimak (syn_cssetk) (syn_ccompl (syn_cfin))) p0062
  have p0064 := @g_vvex
  have p0065 :=
    @g_xpkex (syn_cpw1 (syn_cimak (syn_cssetk) (syn_ccompl (syn_cfin)))) (syn_cvv) p0063
      p0064
  have p0066 :=
    @g_inex (syn_cssetk)
      (syn_cxpk (syn_cpw1 (syn_cimak (syn_cssetk) (syn_ccompl (syn_cfin)))) (syn_cvv))
      p0058 p0065
  have p0067 := @g_n_1cex
  have p0068 :=
    @g_imakex
      (syn_cin (syn_cssetk)
        (syn_cxpk (syn_cpw1 (syn_cimak (syn_cssetk) (syn_ccompl (syn_cfin)))) (syn_cvv)))
      (syn_c1c) p0066 p0067
  have p0069 :=
    @g_complex
      (syn_cimak (syn_cin (syn_cssetk)
          (syn_cxpk (syn_cpw1 (syn_cimak (syn_cssetk) (syn_ccompl (syn_cfin)))) (syn_cvv)))
        (syn_c1c))
      p0068
  have p0070 :=
    @g_eqeltrri
      (syn_ccompl (syn_cimak (syn_cin (syn_cssetk)
            (syn_cxpk (syn_cpw1 (syn_cimak (syn_cssetk) (syn_ccompl (syn_cfin)))) (syn_cvv)))
          (syn_c1c)))
      (.cab m (.all a (.all b (.imp (syn_wa (.objMem b m) (syn_wss (.cv a) (.cv b)))
              (.classMem (.cv a) (syn_cfin))))))
      (syn_cvv) p0057 p0069
  have p0071 := @g_eleq2 (.cv m) (syn_c0c) (.cv b)
  have p0072 := (Nominal.classEqRefl (syn_c0c))
  have p0073 := @g_eleq2i (syn_c0c) (syn_csn (syn_c0)) (.cv b) p0072
  have p0074 := @g_elsnc (.cv b) (syn_c0) p0029
  have p0075 :=
    @g_bitri (.classMem (.cv b) (syn_c0c)) (.classMem (.cv b) (syn_csn (syn_c0)))
      (.classEq (.cv b) (syn_c0)) p0073 p0074
  have p0076_e00_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv m) (syn_c0c))
        (syn_wb (.objMem b m) (.classMem (.cv b) (syn_c0c)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_c0c syn_csn syn_c0 syn_cdif syn_cin syn_ccompl syn_cnin syn_wnan syn_wa
          syn_cvv syn_wb
        simp (config := { failIfUnchanged := false }) only []
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _)
      p0071
  have p0076 :=
    @g_syl6bb (.classEq (.cv m) (syn_c0c)) (.objMem b m) (.classMem (.cv b) (syn_c0c))
      (.classEq (.cv b) (syn_c0)) p0076_e00_recanon p0075
  have p0077 :=
    @g_anbi1d (.classEq (.cv m) (syn_c0c)) (.objMem b m) (.classEq (.cv b) (syn_c0))
      (syn_wss (.cv a) (.cv b)) p0076
  have p0078 :=
    @g_imbi1d (.classEq (.cv m) (syn_c0c))
      (syn_wa (.objMem b m) (syn_wss (.cv a) (.cv b)))
      (syn_wa (.classEq (.cv b) (syn_c0)) (syn_wss (.cv a) (.cv b)))
      (.classMem (.cv a) (syn_cfin)) p0077
  have freeVariableCertificate11 : a ∉ ((Wff.classEq (.cv m) (syn_c0c))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_a_ne_m, or_false,
      not_false_eq_true]
  have freeVariableCertificate12 : b ∉ ((Wff.classEq (.cv m) (syn_c0c))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_b_ne_m, or_false,
      not_false_eq_true]
  have p0079 :=
    @g_n_2albidv (.classEq (.cv m) (syn_c0c))
      (.imp (syn_wa (.objMem b m) (syn_wss (.cv a) (.cv b))) (.classMem (.cv a) (syn_cfin)))
      (.imp (syn_wa (.classEq (.cv b) (syn_c0)) (syn_wss (.cv a) (.cv b)))
        (.classMem (.cv a) (syn_cfin)))
      a b freeVariableCertificate11 freeVariableCertificate12 p0078
  have p0080 := @g_elequ2 m k b
  have p0081 :=
    @g_anbi1d (.objEq m k) (.objMem b m) (.objMem b k) (syn_wss (.cv a) (.cv b)) p0080
  have p0082 :=
    @g_imbi1d (.objEq m k) (syn_wa (.objMem b m) (syn_wss (.cv a) (.cv b)))
      (syn_wa (.objMem b k) (syn_wss (.cv a) (.cv b))) (.classMem (.cv a) (syn_cfin))
      p0081
  have freeVariableCertificate13 : a ∉ ((Wff.objEq m k)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_insert,
      Finset.mem_singleton, fresh_a_ne_m, fresh_a_ne_k, or_false, not_false_eq_true]
  have freeVariableCertificate14 : b ∉ ((Wff.objEq m k)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_insert,
      Finset.mem_singleton, fresh_b_ne_m, fresh_b_ne_k, or_false, not_false_eq_true]
  have p0083 :=
    @g_n_2albidv (.objEq m k)
      (.imp (syn_wa (.objMem b m) (syn_wss (.cv a) (.cv b))) (.classMem (.cv a) (syn_cfin)))
      (.imp (syn_wa (.objMem b k) (syn_wss (.cv a) (.cv b))) (.classMem (.cv a) (syn_cfin)))
      a b freeVariableCertificate13 freeVariableCertificate14 p0082
  have p0084 := @g_eleq1 (.cv b) (.cv d) (.cv k)
  have p0085_e00_recanon :
    Nominal.NPrf (.imp (.objEq b d) (syn_wb (.objMem b k) (.objMem d k))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
            · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
            · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _)
      p0084
  have p0085 :=
    @g_adantl (.objEq b d) (syn_wb (.objMem b k) (.objMem d k)) (.objEq a c)
      p0085_e00_recanon
  have p0086 := @g_sseq12 (.cv a) (.cv c) (.cv b) (.cv d)
  have p0087_e01_recanon :
    Nominal.NPrf
      (.imp (syn_wa (.objEq a c) (.objEq b d))
        (syn_wb (syn_wss (.cv a) (.cv b)) (syn_wss (.cv c) (.cv d)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wa syn_wb syn_wss syn_cin syn_ccompl syn_cnin syn_wnan
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0086
  have p0087 :=
    @g_anbi12d (syn_wa (.objEq a c) (.objEq b d)) (.objMem b k) (.objMem d k)
      (syn_wss (.cv a) (.cv b)) (syn_wss (.cv c) (.cv d)) p0085 p0087_e01_recanon
  have p0088 := @g_eleq1 (.cv a) (.cv c) (syn_cfin)
  have p0089_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq a c)
        (syn_wb (.classMem (.cv a) (syn_cfin)) (.classMem (.cv c) (syn_cfin)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cfin syn_cuni syn_wex syn_wa syn_cnnc syn_cint
        simp (config := { failIfUnchanged := false }) only []
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0088
  have p0089 :=
    @g_adantr (.objEq a c)
      (syn_wb (.classMem (.cv a) (syn_cfin)) (.classMem (.cv c) (syn_cfin))) (.objEq b d)
      p0089_e00_recanon
  have p0090 :=
    @g_imbi12d (syn_wa (.objEq a c) (.objEq b d))
      (syn_wa (.objMem b k) (syn_wss (.cv a) (.cv b)))
      (syn_wa (.objMem d k) (syn_wss (.cv c) (.cv d))) (.classMem (.cv a) (syn_cfin))
      (.classMem (.cv c) (syn_cfin)) p0087 p0089
  have freeVariableCertificate15 :
    d ∉
      ((Wff.imp (syn_wa (.objMem b k) (syn_wss (.cv a) (.cv b)))
          (.classMem (.cv a) (syn_cfin)))).fv :=
    by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
      NFChoice.Compiler.CoreFVSimp.fv_wff_objMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfin, Finset.mem_union,
      Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, fresh_d_ne_b,
      fresh_d_ne_k, fresh_d_ne_a, or_false, not_false_eq_true]
  have freeVariableCertificate16 :
    c ∉
      ((Wff.imp (syn_wa (.objMem b k) (syn_wss (.cv a) (.cv b)))
          (.classMem (.cv a) (syn_cfin)))).fv :=
    by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
      NFChoice.Compiler.CoreFVSimp.fv_wff_objMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfin, Finset.mem_union,
      Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, fresh_c_ne_b,
      fresh_c_ne_k, fresh_c_ne_a, or_false, not_false_eq_true]
  have freeVariableCertificate17 :
    a ∉
      ((Wff.imp (syn_wa (.objMem d k) (syn_wss (.cv c) (.cv d)))
          (.classMem (.cv c) (syn_cfin)))).fv :=
    by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
      NFChoice.Compiler.CoreFVSimp.fv_wff_objMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfin, Finset.mem_union,
      Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, fresh_a_ne_d,
      fresh_a_ne_k, fresh_a_ne_c, or_false, not_false_eq_true]
  have freeVariableCertificate18 :
    b ∉
      ((Wff.imp (syn_wa (.objMem d k) (syn_wss (.cv c) (.cv d)))
          (.classMem (.cv c) (syn_cfin)))).fv :=
    by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
      NFChoice.Compiler.CoreFVSimp.fv_wff_objMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfin, Finset.mem_union,
      Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, fresh_b_ne_d,
      fresh_b_ne_k, fresh_b_ne_c, or_false, not_false_eq_true]
  have p0091 :=
    @g_cbval2v
      (.imp (syn_wa (.objMem b k) (syn_wss (.cv a) (.cv b))) (.classMem (.cv a) (syn_cfin)))
      (.imp (syn_wa (.objMem d k) (syn_wss (.cv c) (.cv d))) (.classMem (.cv c) (syn_cfin)))
      a b c d freeVariableCertificate15 freeVariableCertificate16
      freeVariableCertificate17 freeVariableCertificate18
      (show d ≠ a from (by exact fresh_d_ne_a)) (show d ≠ c from (by exact fresh_d_ne_c))
      (show a ≠ b from (by exact fresh_a_ne_b)) (show b ≠ c from (by exact fresh_b_ne_c))
      p0090
  have p0092 :=
    @g_syl6bb (.objEq m k)
      (.all a (.all b (.imp (syn_wa (.objMem b m) (syn_wss (.cv a) (.cv b)))
            (.classMem (.cv a) (syn_cfin)))))
      (.all a (.all b (.imp (syn_wa (.objMem b k) (syn_wss (.cv a) (.cv b)))
            (.classMem (.cv a) (syn_cfin)))))
      (.all c (.all d (.imp (syn_wa (.objMem d k) (syn_wss (.cv c) (.cv d)))
            (.classMem (.cv c) (syn_cfin)))))
      p0083 p0091
  have p0093 := @g_eleq2 (.cv m) (syn_cplc (.cv k) (syn_c1c)) (.cv b)
  have p0094_e00_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv m) (syn_cplc (.cv k) (syn_c1c)))
        (syn_wb (.objMem b m) (.classMem (.cv b) (syn_cplc (.cv k) (syn_c1c))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_cplc syn_wrex syn_wex syn_wa syn_c1c syn_wb
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _)
      p0093
  have p0094 :=
    @g_anbi1d (.classEq (.cv m) (syn_cplc (.cv k) (syn_c1c))) (.objMem b m)
      (.classMem (.cv b) (syn_cplc (.cv k) (syn_c1c))) (syn_wss (.cv a) (.cv b))
      p0094_e00_recanon
  have p0095 :=
    @g_imbi1d (.classEq (.cv m) (syn_cplc (.cv k) (syn_c1c)))
      (syn_wa (.objMem b m) (syn_wss (.cv a) (.cv b)))
      (syn_wa (.classMem (.cv b) (syn_cplc (.cv k) (syn_c1c))) (syn_wss (.cv a) (.cv b)))
      (.classMem (.cv a) (syn_cfin)) p0094
  have freeVariableCertificate19 :
    a ∉ ((Wff.classEq (.cv m) (syn_cplc (.cv k) (syn_c1c)))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_a_ne_m, fresh_a_ne_k, or_false,
      not_false_eq_true]
  have freeVariableCertificate20 :
    b ∉ ((Wff.classEq (.cv m) (syn_cplc (.cv k) (syn_c1c)))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_b_ne_m, fresh_b_ne_k, or_false,
      not_false_eq_true]
  have p0096 :=
    @g_n_2albidv (.classEq (.cv m) (syn_cplc (.cv k) (syn_c1c)))
      (.imp (syn_wa (.objMem b m) (syn_wss (.cv a) (.cv b))) (.classMem (.cv a) (syn_cfin)))
      (.imp (syn_wa (.classMem (.cv b) (syn_cplc (.cv k) (syn_c1c))) (syn_wss (.cv a) (.cv b)))
        (.classMem (.cv a) (syn_cfin)))
      a b freeVariableCertificate19 freeVariableCertificate20 p0095
  have p0097 := @g_elequ2 m n b
  have p0098 :=
    @g_anbi1d (.objEq m n) (.objMem b m) (.objMem b n) (syn_wss (.cv a) (.cv b)) p0097
  have p0099 :=
    @g_imbi1d (.objEq m n) (syn_wa (.objMem b m) (syn_wss (.cv a) (.cv b)))
      (syn_wa (.objMem b n) (syn_wss (.cv a) (.cv b))) (.classMem (.cv a) (syn_cfin))
      p0098
  have freeVariableCertificate21 : a ∉ ((Wff.objEq m n)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_insert,
      Finset.mem_singleton, fresh_a_ne_m, fresh_a_ne_n, or_false, not_false_eq_true]
  have freeVariableCertificate22 : b ∉ ((Wff.objEq m n)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_insert,
      Finset.mem_singleton, fresh_b_ne_m, fresh_b_ne_n, or_false, not_false_eq_true]
  have p0100 :=
    @g_n_2albidv (.objEq m n)
      (.imp (syn_wa (.objMem b m) (syn_wss (.cv a) (.cv b))) (.classMem (.cv a) (syn_cfin)))
      (.imp (syn_wa (.objMem b n) (syn_wss (.cv a) (.cv b))) (.classMem (.cv a) (syn_cfin)))
      a b freeVariableCertificate21 freeVariableCertificate22 p0099
  have p0101 := @g_sseq2 (.cv b) (syn_c0) (.cv a)
  have p0102 :=
    @g_biimpa (.classEq (.cv b) (syn_c0)) (syn_wss (.cv a) (.cv b))
      (syn_wss (.cv a) (syn_c0)) p0101
  have p0103 := @g_ss0b (.cv a)
  have p0104 :=
    @g_sylib (syn_wa (.classEq (.cv b) (syn_c0)) (syn_wss (.cv a) (.cv b)))
      (syn_wss (.cv a) (syn_c0)) (.classEq (.cv a) (syn_c0)) p0102 p0103
  have p0105 := @g_n_0fin
  have p0106 :=
    @g_syl6eqel (syn_wa (.classEq (.cv b) (syn_c0)) (syn_wss (.cv a) (.cv b))) (.cv a)
      (syn_c0) (syn_cfin) p0104 p0105
  have p0107 :=
    @g_gen2
      (.imp (syn_wa (.classEq (.cv b) (syn_c0)) (syn_wss (.cv a) (.cv b)))
        (.classMem (.cv a) (syn_cfin)))
      a b p0106
  have p0108 := @g_sspss (.cv a) (.cv b)
  have freeVariableCertificate23 : x ∉ ((Class.cv a)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_x_ne_a, not_false_eq_true]
  have freeVariableCertificate24 : x ∉ ((Class.cv b)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_x_ne_b, not_false_eq_true]
  have p0109 :=
    @g_dfpss4 x (.cv a) (.cv b) freeVariableCertificate23 freeVariableCertificate24
  have p0110_e00_recanon :
    Nominal.NPrf
      (syn_wb (syn_wpss (.cv a) (.cv b))
        (syn_wa (syn_wss (.cv a) (.cv b)) (syn_wrex x (.cv b) (.neg (.objMem x a))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wpss syn_wa syn_wss syn_cin syn_ccompl syn_cnin syn_wnan syn_wne
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.all
              apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
              · apply Nominal.RecanonTransportDev.TRecanonWff.neg
                apply Nominal.RecanonTransportDev.TRecanonWff.neg
                exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.all
              apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
              · apply Nominal.RecanonTransportDev.TRecanonWff.neg
                apply Nominal.RecanonTransportDev.TRecanonWff.neg
                exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0109
  have p0110 :=
    @g_orbi1i (syn_wpss (.cv a) (.cv b))
      (syn_wa (syn_wss (.cv a) (.cv b)) (syn_wrex x (.cv b) (.neg (.objMem x a))))
      (.objEq a b) p0110_e00_recanon
  have p0111_e00_recanon :
    Nominal.NPrf
      (syn_wb (syn_wss (.cv a) (.cv b)) (syn_wo (syn_wpss (.cv a) (.cv b)) (.objEq a b))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wss syn_cin syn_ccompl syn_cnin syn_wnan syn_wa syn_wo syn_wpss
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0108
  have p0111 :=
    @g_bitri (syn_wss (.cv a) (.cv b)) (syn_wo (syn_wpss (.cv a) (.cv b)) (.objEq a b))
      (syn_wo (syn_wa (syn_wss (.cv a) (.cv b)) (syn_wrex x (.cv b) (.neg (.objMem x a))))
        (.objEq a b))
      p0111_e00_recanon p0110
  have p0112 :=
    @g_simp1 (.classMem (.cv k) (syn_cnnc)) (syn_wa (.objMem x b) (.neg (.objMem x a)))
      (syn_wa (syn_wss (.cv a) (.cv b)) (.classMem (.cv b) (syn_cplc (.cv k) (syn_c1c))))
  have p0113 := @g_vex x
  have p0114 := @g_snid (.cv x) p0113
  have p0115 := @g_eldif (.cv x) (.cv b) (syn_csn (.cv x))
  have p0116_e00_recanon :
    Nominal.NPrf
      (syn_wb (.classMem (.cv x) (syn_cdif (.cv b) (syn_csn (.cv x))))
        (syn_wa (.objMem x b) (.neg (.classMem (.cv x) (syn_csn (.cv x)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cdif syn_cin syn_ccompl syn_cnin syn_wnan syn_wa syn_csn
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0115
  have p0116 :=
    @g_simprbi (.classMem (.cv x) (syn_cdif (.cv b) (syn_csn (.cv x)))) (.objMem x b)
      (.neg (.classMem (.cv x) (syn_csn (.cv x)))) p0116_e00_recanon
  have p0117 :=
    @g_mt2 (.classMem (.cv x) (syn_cdif (.cv b) (syn_csn (.cv x))))
      (.classMem (.cv x) (syn_csn (.cv x))) p0114 p0116
  have p0118 :=
    @g_a1i (.neg (.classMem (.cv x) (syn_cdif (.cv b) (syn_csn (.cv x)))))
      (syn_w3a (.classMem (.cv k) (syn_cnnc)) (syn_wa (.objMem x b) (.neg (.objMem x a)))
        (syn_wa (syn_wss (.cv a) (.cv b)) (.classMem (.cv b) (syn_cplc (.cv k) (syn_c1c)))))
      p0117
  have p0119 := @g_undif1 (.cv b) (syn_csn (.cv x))
  have p0120 := @g_snssi (.cv x) (.cv b)
  have p0121 := @g_ssequn2 (syn_csn (.cv x)) (.cv b)
  have p0122_e00_recanon :
    Nominal.NPrf (.imp (.objMem x b) (syn_wss (syn_csn (.cv x)) (.cv b))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wss syn_cin syn_ccompl syn_cnin syn_wnan syn_wa syn_csn
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0120
  have p0122 :=
    @g_sylib (.objMem x b) (syn_wss (syn_csn (.cv x)) (.cv b))
      (.classEq (syn_cun (.cv b) (syn_csn (.cv x))) (.cv b)) p0122_e00_recanon p0121
  have p0123 :=
    @g_adantr (.objMem x b) (.classEq (syn_cun (.cv b) (syn_csn (.cv x))) (.cv b))
      (.neg (.objMem x a)) p0122
  have p0124 :=
    @g_n_3ad2ant2 (syn_wa (.objMem x b) (.neg (.objMem x a)))
      (.classMem (.cv k) (syn_cnnc))
      (.classEq (syn_cun (.cv b) (syn_csn (.cv x))) (.cv b))
      (syn_wa (syn_wss (.cv a) (.cv b)) (.classMem (.cv b) (syn_cplc (.cv k) (syn_c1c))))
      p0123
  have p0125 :=
    @g_syl5eq
      (syn_w3a (.classMem (.cv k) (syn_cnnc)) (syn_wa (.objMem x b) (.neg (.objMem x a)))
        (syn_wa (syn_wss (.cv a) (.cv b)) (.classMem (.cv b) (syn_cplc (.cv k) (syn_c1c)))))
      (syn_cun (syn_cdif (.cv b) (syn_csn (.cv x))) (syn_csn (.cv x)))
      (syn_cun (.cv b) (syn_csn (.cv x))) (.cv b) p0119 p0124
  have p0126 :=
    @g_simp3r (.classMem (.cv k) (syn_cnnc)) (syn_wa (.objMem x b) (.neg (.objMem x a)))
      (syn_wss (.cv a) (.cv b)) (.classMem (.cv b) (syn_cplc (.cv k) (syn_c1c)))
  have p0127 :=
    @g_eqeltrd
      (syn_w3a (.classMem (.cv k) (syn_cnnc)) (syn_wa (.objMem x b) (.neg (.objMem x a)))
        (syn_wa (syn_wss (.cv a) (.cv b)) (.classMem (.cv b) (syn_cplc (.cv k) (syn_c1c)))))
      (syn_cun (syn_cdif (.cv b) (syn_csn (.cv x))) (syn_csn (.cv x))) (.cv b)
      (syn_cplc (.cv k) (syn_c1c)) p0125 p0126
  have p0128 := @g_snex (.cv x)
  have p0129 := @g_difex (.cv b) (syn_csn (.cv x)) p0029 p0128
  have p0130 :=
    @g_nnsucelr (syn_cdif (.cv b) (syn_csn (.cv x))) (.cv k) (.cv x) p0129 p0113
  have p0131 :=
    @g_syl12anc
      (syn_w3a (.classMem (.cv k) (syn_cnnc)) (syn_wa (.objMem x b) (.neg (.objMem x a)))
        (syn_wa (syn_wss (.cv a) (.cv b)) (.classMem (.cv b) (syn_cplc (.cv k) (syn_c1c)))))
      (.classMem (.cv k) (syn_cnnc))
      (.neg (.classMem (.cv x) (syn_cdif (.cv b) (syn_csn (.cv x)))))
      (.classMem (syn_cun (syn_cdif (.cv b) (syn_csn (.cv x))) (syn_csn (.cv x)))
        (syn_cplc (.cv k) (syn_c1c)))
      (.classMem (syn_cdif (.cv b) (syn_csn (.cv x))) (.cv k)) p0112 p0118 p0127 p0130
  have p0132 := @g_inass (.cv a) (.cv b) (syn_ccompl (syn_csn (.cv x)))
  have p0133 :=
    (Nominal.classEqRefl (syn_cdif (syn_cin (.cv a) (.cv b)) (syn_csn (.cv x))))
  have p0134 := (Nominal.classEqRefl (syn_cdif (.cv b) (syn_csn (.cv x))))
  have p0135 :=
    @g_ineq2i (syn_cdif (.cv b) (syn_csn (.cv x)))
      (syn_cin (.cv b) (syn_ccompl (syn_csn (.cv x)))) (.cv a) p0134
  have p0136 :=
    @g_n_3eqtr4ri (syn_cin (syn_cin (.cv a) (.cv b)) (syn_ccompl (syn_csn (.cv x))))
      (syn_cin (.cv a) (syn_cin (.cv b) (syn_ccompl (syn_csn (.cv x)))))
      (syn_cdif (syn_cin (.cv a) (.cv b)) (syn_csn (.cv x)))
      (syn_cin (.cv a) (syn_cdif (.cv b) (syn_csn (.cv x)))) p0132 p0133 p0135
  have p0137 := (Nominal.biimpRefl (syn_wss (.cv a) (.cv b)))
  have p0138 :=
    @g_biimpi (syn_wss (.cv a) (.cv b)) (.classEq (syn_cin (.cv a) (.cv b)) (.cv a)) p0137
  have p0139 :=
    @g_adantr (syn_wss (.cv a) (.cv b)) (.classEq (syn_cin (.cv a) (.cv b)) (.cv a))
      (.classMem (.cv b) (syn_cplc (.cv k) (syn_c1c))) p0138
  have p0140 :=
    @g_n_3ad2ant3
      (syn_wa (syn_wss (.cv a) (.cv b)) (.classMem (.cv b) (syn_cplc (.cv k) (syn_c1c))))
      (.classMem (.cv k) (syn_cnnc)) (.classEq (syn_cin (.cv a) (.cv b)) (.cv a))
      (syn_wa (.objMem x b) (.neg (.objMem x a))) p0139
  have p0141 :=
    @g_difeq1d
      (syn_w3a (.classMem (.cv k) (syn_cnnc)) (syn_wa (.objMem x b) (.neg (.objMem x a)))
        (syn_wa (syn_wss (.cv a) (.cv b)) (.classMem (.cv b) (syn_cplc (.cv k) (syn_c1c)))))
      (syn_cin (.cv a) (.cv b)) (.cv a) (syn_csn (.cv x)) p0140
  have p0142 := @g_difsn (.cv x) (.cv a)
  have p0143_e00_recanon :
    Nominal.NPrf
      (.imp (.neg (.objMem x a)) (.classEq (syn_cdif (.cv a) (syn_csn (.cv x))) (.cv a))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_cdif syn_cin syn_ccompl syn_cnin syn_wnan syn_wa syn_csn
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0142
  have p0143 :=
    @g_adantl (.neg (.objMem x a)) (.classEq (syn_cdif (.cv a) (syn_csn (.cv x))) (.cv a))
      (.objMem x b) p0143_e00_recanon
  have p0144 :=
    @g_n_3ad2ant2 (syn_wa (.objMem x b) (.neg (.objMem x a)))
      (.classMem (.cv k) (syn_cnnc))
      (.classEq (syn_cdif (.cv a) (syn_csn (.cv x))) (.cv a))
      (syn_wa (syn_wss (.cv a) (.cv b)) (.classMem (.cv b) (syn_cplc (.cv k) (syn_c1c))))
      p0143
  have p0145 :=
    @g_eqtrd
      (syn_w3a (.classMem (.cv k) (syn_cnnc)) (syn_wa (.objMem x b) (.neg (.objMem x a)))
        (syn_wa (syn_wss (.cv a) (.cv b)) (.classMem (.cv b) (syn_cplc (.cv k) (syn_c1c)))))
      (syn_cdif (syn_cin (.cv a) (.cv b)) (syn_csn (.cv x)))
      (syn_cdif (.cv a) (syn_csn (.cv x))) (.cv a) p0141 p0144
  have p0146 :=
    @g_syl5eq
      (syn_w3a (.classMem (.cv k) (syn_cnnc)) (syn_wa (.objMem x b) (.neg (.objMem x a)))
        (syn_wa (syn_wss (.cv a) (.cv b)) (.classMem (.cv b) (syn_cplc (.cv k) (syn_c1c)))))
      (syn_cin (.cv a) (syn_cdif (.cv b) (syn_csn (.cv x))))
      (syn_cdif (syn_cin (.cv a) (.cv b)) (syn_csn (.cv x))) (.cv a) p0136 p0145
  have p0147 := (Nominal.biimpRefl (syn_wss (.cv a) (syn_cdif (.cv b) (syn_csn (.cv x)))))
  have p0148 :=
    @g_sylibr
      (syn_w3a (.classMem (.cv k) (syn_cnnc)) (syn_wa (.objMem x b) (.neg (.objMem x a)))
        (syn_wa (syn_wss (.cv a) (.cv b)) (.classMem (.cv b) (syn_cplc (.cv k) (syn_c1c)))))
      (.classEq (syn_cin (.cv a) (syn_cdif (.cv b) (syn_csn (.cv x)))) (.cv a))
      (syn_wss (.cv a) (syn_cdif (.cv b) (syn_csn (.cv x)))) p0146 p0147
  have p0149 :=
    @g_jca
      (syn_w3a (.classMem (.cv k) (syn_cnnc)) (syn_wa (.objMem x b) (.neg (.objMem x a)))
        (syn_wa (syn_wss (.cv a) (.cv b)) (.classMem (.cv b) (syn_cplc (.cv k) (syn_c1c)))))
      (.classMem (syn_cdif (.cv b) (syn_csn (.cv x))) (.cv k))
      (syn_wss (.cv a) (syn_cdif (.cv b) (syn_csn (.cv x)))) p0131 p0148
  have p0150 :=
    @g_n_3adant1r (.classMem (.cv k) (syn_cnnc))
      (syn_wa (.objMem x b) (.neg (.objMem x a)))
      (syn_wa (syn_wss (.cv a) (.cv b)) (.classMem (.cv b) (syn_cplc (.cv k) (syn_c1c))))
      (syn_wa (.classMem (syn_cdif (.cv b) (syn_csn (.cv x))) (.cv k))
        (syn_wss (.cv a) (syn_cdif (.cv b) (syn_csn (.cv x)))))
      (.all c (.all d (.imp (syn_wa (.objMem d k) (syn_wss (.cv c) (.cv d)))
            (.classMem (.cv c) (syn_cfin)))))
      p0149
  have p0151 := @g_eleq1 (.cv d) (syn_cdif (.cv b) (syn_csn (.cv x))) (.cv k)
  have p0152_e00_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv d) (syn_cdif (.cv b) (syn_csn (.cv x)))) (syn_wb (.objMem d k)
          (.classMem (syn_cdif (.cv b) (syn_csn (.cv x))) (.cv k)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_cdif syn_cin syn_ccompl syn_cnin syn_wnan syn_wa syn_csn syn_wb
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _)
      p0151
  have p0152 :=
    @g_adantl (.classEq (.cv d) (syn_cdif (.cv b) (syn_csn (.cv x))))
      (syn_wb (.objMem d k) (.classMem (syn_cdif (.cv b) (syn_csn (.cv x))) (.cv k)))
      (.objEq c a) p0152_e00_recanon
  have p0153 := @g_sseq12 (.cv c) (.cv a) (.cv d) (syn_cdif (.cv b) (syn_csn (.cv x)))
  have p0154_e01_recanon :
    Nominal.NPrf
      (.imp (syn_wa (.objEq c a) (.classEq (.cv d) (syn_cdif (.cv b) (syn_csn (.cv x)))))
        (syn_wb (syn_wss (.cv c) (.cv d))
          (syn_wss (.cv a) (syn_cdif (.cv b) (syn_csn (.cv x)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wa syn_cdif syn_cin syn_ccompl syn_cnin syn_wnan syn_csn syn_wb syn_wss
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0153
  have p0154 :=
    @g_anbi12d
      (syn_wa (.objEq c a) (.classEq (.cv d) (syn_cdif (.cv b) (syn_csn (.cv x)))))
      (.objMem d k) (.classMem (syn_cdif (.cv b) (syn_csn (.cv x))) (.cv k))
      (syn_wss (.cv c) (.cv d)) (syn_wss (.cv a) (syn_cdif (.cv b) (syn_csn (.cv x))))
      p0152 p0154_e01_recanon
  have p0155 := @g_eleq1 (.cv c) (.cv a) (syn_cfin)
  have p0156_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq c a)
        (syn_wb (.classMem (.cv c) (syn_cfin)) (.classMem (.cv a) (syn_cfin)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cfin syn_cuni syn_wex syn_wa syn_cnnc syn_cint
        simp (config := { failIfUnchanged := false }) only []
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0155
  have p0156 :=
    @g_adantr (.objEq c a)
      (syn_wb (.classMem (.cv c) (syn_cfin)) (.classMem (.cv a) (syn_cfin)))
      (.classEq (.cv d) (syn_cdif (.cv b) (syn_csn (.cv x)))) p0156_e00_recanon
  have p0157 :=
    @g_imbi12d
      (syn_wa (.objEq c a) (.classEq (.cv d) (syn_cdif (.cv b) (syn_csn (.cv x)))))
      (syn_wa (.objMem d k) (syn_wss (.cv c) (.cv d)))
      (syn_wa (.classMem (syn_cdif (.cv b) (syn_csn (.cv x))) (.cv k))
        (syn_wss (.cv a) (syn_cdif (.cv b) (syn_csn (.cv x)))))
      (.classMem (.cv c) (syn_cfin)) (.classMem (.cv a) (syn_cfin)) p0154 p0156
  have p0158_e00_recanon :
    Nominal.NPrf
      (.imp (syn_wa (.classEq (.cv c) (.cv a))
          (.classEq (.cv d) (syn_cdif (.cv b) (syn_csn (.cv x))))) (syn_wb
          (.imp (syn_wa (.objMem d k) (syn_wss (.cv c) (.cv d))) (.classMem (.cv c) (syn_cfin)))
          (.imp (syn_wa (.classMem (syn_cdif (.cv b) (syn_csn (.cv x))) (.cv k))
              (syn_wss (.cv a) (syn_cdif (.cv b) (syn_csn (.cv x)))))
            (.classMem (.cv a) (syn_cfin))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wa syn_cdif syn_cin syn_ccompl syn_cnin syn_wnan syn_csn syn_wb
          syn_cfin syn_cuni syn_wex syn_cnnc syn_cint
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0157
  have freeVariableCertificate25 : c ∉ ((Class.cv a)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_c_ne_a, not_false_eq_true]
  have freeVariableCertificate26 : d ∉ ((Class.cv a)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_d_ne_a, not_false_eq_true]
  have freeVariableCertificate27 : c ∉ ((syn_cdif (.cv b) (syn_csn (.cv x)))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
      Finset.mem_singleton, fresh_c_ne_b, fresh_c_ne_x, or_false, not_false_eq_true]
  have freeVariableCertificate28 : d ∉ ((syn_cdif (.cv b) (syn_csn (.cv x)))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
      Finset.mem_singleton, fresh_d_ne_b, fresh_d_ne_x, or_false, not_false_eq_true]
  have freeVariableCertificate29 :
    c ∉
      ((Wff.imp (syn_wa (.classMem (syn_cdif (.cv b) (syn_csn (.cv x))) (.cv k))
            (syn_wss (.cv a) (syn_cdif (.cv b) (syn_csn (.cv x)))))
          (.classMem (.cv a) (syn_cfin)))).fv :=
    by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfin, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_c_ne_b, fresh_c_ne_x, fresh_c_ne_k,
      fresh_c_ne_a, or_false, not_false_eq_true]
  have freeVariableCertificate30 :
    d ∉
      ((Wff.imp (syn_wa (.classMem (syn_cdif (.cv b) (syn_csn (.cv x))) (.cv k))
            (syn_wss (.cv a) (syn_cdif (.cv b) (syn_csn (.cv x)))))
          (.classMem (.cv a) (syn_cfin)))).fv :=
    by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfin, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_d_ne_b, fresh_d_ne_x, fresh_d_ne_k,
      fresh_d_ne_a, or_false, not_false_eq_true]
  have p0158 :=
    @g_spc2gv
      (.imp (syn_wa (.objMem d k) (syn_wss (.cv c) (.cv d))) (.classMem (.cv c) (syn_cfin)))
      (.imp (syn_wa (.classMem (syn_cdif (.cv b) (syn_csn (.cv x))) (.cv k))
          (syn_wss (.cv a) (syn_cdif (.cv b) (syn_csn (.cv x)))))
        (.classMem (.cv a) (syn_cfin)))
      c d (.cv a) (syn_cdif (.cv b) (syn_csn (.cv x))) (syn_cvv) (syn_cvv)
      freeVariableCertificate25 freeVariableCertificate26 freeVariableCertificate27
      freeVariableCertificate28 freeVariableCertificate29 freeVariableCertificate30
      (show c ≠ d from (by exact fresh_c_ne_d)) p0158_e00_recanon
  have p0159 :=
    @g_mp2an (.classMem (.cv a) (syn_cvv))
      (.classMem (syn_cdif (.cv b) (syn_csn (.cv x))) (syn_cvv))
      (.imp (.all c (.all d (.imp (syn_wa (.objMem d k) (syn_wss (.cv c) (.cv d)))
              (.classMem (.cv c) (syn_cfin))))) (.imp
          (syn_wa (.classMem (syn_cdif (.cv b) (syn_csn (.cv x))) (.cv k))
            (syn_wss (.cv a) (syn_cdif (.cv b) (syn_csn (.cv x)))))
          (.classMem (.cv a) (syn_cfin))))
      p0037 p0129 p0158
  have p0160 :=
    @g_adantl
      (.all c (.all d (.imp (syn_wa (.objMem d k) (syn_wss (.cv c) (.cv d)))
            (.classMem (.cv c) (syn_cfin)))))
      (.imp (syn_wa (.classMem (syn_cdif (.cv b) (syn_csn (.cv x))) (.cv k))
          (syn_wss (.cv a) (syn_cdif (.cv b) (syn_csn (.cv x)))))
        (.classMem (.cv a) (syn_cfin)))
      (.classMem (.cv k) (syn_cnnc)) p0159
  have p0161 :=
    @g_n_3ad2ant1
      (syn_wa (.classMem (.cv k) (syn_cnnc)) (.all c (.all d
            (.imp (syn_wa (.objMem d k) (syn_wss (.cv c) (.cv d)))
              (.classMem (.cv c) (syn_cfin))))))
      (syn_wa (.objMem x b) (.neg (.objMem x a)))
      (.imp (syn_wa (.classMem (syn_cdif (.cv b) (syn_csn (.cv x))) (.cv k))
          (syn_wss (.cv a) (syn_cdif (.cv b) (syn_csn (.cv x)))))
        (.classMem (.cv a) (syn_cfin)))
      (syn_wa (syn_wss (.cv a) (.cv b)) (.classMem (.cv b) (syn_cplc (.cv k) (syn_c1c))))
      p0160
  have p0162 :=
    @g_mpd
      (syn_w3a (syn_wa (.classMem (.cv k) (syn_cnnc)) (.all c (.all d
              (.imp (syn_wa (.objMem d k) (syn_wss (.cv c) (.cv d)))
                (.classMem (.cv c) (syn_cfin)))))) (syn_wa (.objMem x b) (.neg (.objMem x a)))
        (syn_wa (syn_wss (.cv a) (.cv b)) (.classMem (.cv b) (syn_cplc (.cv k) (syn_c1c)))))
      (syn_wa (.classMem (syn_cdif (.cv b) (syn_csn (.cv x))) (.cv k))
        (syn_wss (.cv a) (syn_cdif (.cv b) (syn_csn (.cv x)))))
      (.classMem (.cv a) (syn_cfin)) p0150 p0161
  have p0163 :=
    @g_n_3exp
      (syn_wa (.classMem (.cv k) (syn_cnnc)) (.all c (.all d
            (.imp (syn_wa (.objMem d k) (syn_wss (.cv c) (.cv d)))
              (.classMem (.cv c) (syn_cfin))))))
      (syn_wa (.objMem x b) (.neg (.objMem x a)))
      (syn_wa (syn_wss (.cv a) (.cv b)) (.classMem (.cv b) (syn_cplc (.cv k) (syn_c1c))))
      (.classMem (.cv a) (syn_cfin)) p0162
  have p0164 :=
    @g_exp5c
      (syn_wa (.classMem (.cv k) (syn_cnnc)) (.all c (.all d
            (.imp (syn_wa (.objMem d k) (syn_wss (.cv c) (.cv d)))
              (.classMem (.cv c) (syn_cfin))))))
      (.objMem x b) (.neg (.objMem x a)) (syn_wss (.cv a) (.cv b))
      (.classMem (.cv b) (syn_cplc (.cv k) (syn_c1c))) (.classMem (.cv a) (syn_cfin))
      p0163
  have p0165_e00_recanon :
    Nominal.NPrf
      (.imp (syn_wa (.classMem (.cv k) (syn_cnnc)) (.all c (.all d
              (.imp (syn_wa (.objMem d k) (syn_wss (.cv c) (.cv d)))
                (.classMem (.cv c) (syn_cfin)))))) (.imp (.classMem (.cv x) (.cv b))
          (.imp (.neg (.objMem x a)) (.imp (syn_wss (.cv a) (.cv b))
              (.imp (.classMem (.cv b) (syn_cplc (.cv k) (syn_c1c)))
                (.classMem (.cv a) (syn_cfin))))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wa syn_cnnc syn_cint syn_cfin syn_cuni syn_wex syn_wss syn_cin
          syn_ccompl syn_cnin syn_wnan syn_cplc syn_wrex syn_c1c
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.objMem_classMem _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0164
  have freeVariableCertificate31 :
    x ∉
      ((Wff.imp (syn_wss (.cv a) (.cv b)) (.imp (.classMem (.cv b) (syn_cplc (.cv k) (syn_c1c)))
            (.classMem (.cv a) (syn_cfin))))).fv :=
    by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfin, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_x_ne_a, fresh_x_ne_b, fresh_x_ne_k,
      or_false, not_false_eq_true]
  have freeVariableCertificate32 :
    x ∉
      ((syn_wa (.classMem (.cv k) (syn_cnnc)) (.all c (.all d
              (.imp (syn_wa (.objMem d k) (syn_wss (.cv c) (.cv d)))
                (.classMem (.cv c) (syn_cfin))))))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
      NFChoice.Compiler.CoreFVSimp.fv_wff_all, NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
      NFChoice.Compiler.CoreFVSimp.fv_wff_objMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfin, Finset.mem_union,
      Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty,
      fresh_x_ne_k, fresh_x_ne_d, fresh_x_ne_c, or_false, and_false, not_false_eq_true]
  have p0165 :=
    @g_rexlimdv
      (syn_wa (.classMem (.cv k) (syn_cnnc)) (.all c (.all d
            (.imp (syn_wa (.objMem d k) (syn_wss (.cv c) (.cv d)))
              (.classMem (.cv c) (syn_cfin))))))
      (.neg (.objMem x a))
      (.imp (syn_wss (.cv a) (.cv b)) (.imp (.classMem (.cv b) (syn_cplc (.cv k) (syn_c1c)))
          (.classMem (.cv a) (syn_cfin))))
      x (.cv b) freeVariableCertificate31 freeVariableCertificate32 p0165_e00_recanon
  have p0166 :=
    @g_com23
      (syn_wa (.classMem (.cv k) (syn_cnnc)) (.all c (.all d
            (.imp (syn_wa (.objMem d k) (syn_wss (.cv c) (.cv d)))
              (.classMem (.cv c) (syn_cfin))))))
      (syn_wrex x (.cv b) (.neg (.objMem x a))) (syn_wss (.cv a) (.cv b))
      (.imp (.classMem (.cv b) (syn_cplc (.cv k) (syn_c1c))) (.classMem (.cv a) (syn_cfin)))
      p0165
  have p0167 :=
    @g_imp3a
      (syn_wa (.classMem (.cv k) (syn_cnnc)) (.all c (.all d
            (.imp (syn_wa (.objMem d k) (syn_wss (.cv c) (.cv d)))
              (.classMem (.cv c) (syn_cfin))))))
      (syn_wss (.cv a) (.cv b)) (syn_wrex x (.cv b) (.neg (.objMem x a)))
      (.imp (.classMem (.cv b) (syn_cplc (.cv k) (syn_c1c))) (.classMem (.cv a) (syn_cfin)))
      p0166
  have p0168 := @g_peano2 (.cv k)
  have p0169 := @g_eleq2 (.cv x) (syn_cplc (.cv k) (syn_c1c)) (.cv b)
  have p0170_e00_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv x) (syn_cplc (.cv k) (syn_c1c)))
        (syn_wb (.objMem b x) (.classMem (.cv b) (syn_cplc (.cv k) (syn_c1c))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_cplc syn_wrex syn_wex syn_wa syn_c1c syn_wb
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _)
      p0169
  have freeVariableCertificate33 : x ∉ ((syn_cplc (.cv k) (syn_c1c))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_x_ne_k, or_false,
      not_false_eq_true]
  have freeVariableCertificate34 :
    x ∉ ((Wff.classMem (.cv b) (syn_cplc (.cv k) (syn_c1c)))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_x_ne_b, fresh_x_ne_k, or_false,
      not_false_eq_true]
  have p0170 :=
    @g_rspcev (.objMem b x) (.classMem (.cv b) (syn_cplc (.cv k) (syn_c1c))) x
      (syn_cplc (.cv k) (syn_c1c)) (syn_cnnc) freeVariableCertificate33
      (by
        exact
          (show x ∉ ((syn_cnnc)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc];
              exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
      freeVariableCertificate34 p0170_e00_recanon
  have p0171 := @g_elfin x (.cv b) freeVariableCertificate24
  have p0172_e01_recanon :
    Nominal.NPrf
      (syn_wb (.classMem (.cv b) (syn_cfin)) (syn_wrex x (syn_cnnc) (.objMem b x))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cfin syn_cuni syn_wex syn_wa syn_cnnc syn_cint syn_wrex
        simp (config := { failIfUnchanged := false }) only []
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0171
  have p0172 :=
    @g_sylibr
      (syn_wa (.classMem (syn_cplc (.cv k) (syn_c1c)) (syn_cnnc))
        (.classMem (.cv b) (syn_cplc (.cv k) (syn_c1c))))
      (syn_wrex x (syn_cnnc) (.objMem b x)) (.classMem (.cv b) (syn_cfin)) p0170
      p0172_e01_recanon
  have p0173 :=
    @g_ex (.classMem (syn_cplc (.cv k) (syn_c1c)) (syn_cnnc))
      (.classMem (.cv b) (syn_cplc (.cv k) (syn_c1c))) (.classMem (.cv b) (syn_cfin))
      p0172
  have p0174 :=
    @g_syl (.classMem (.cv k) (syn_cnnc))
      (.classMem (syn_cplc (.cv k) (syn_c1c)) (syn_cnnc))
      (.imp (.classMem (.cv b) (syn_cplc (.cv k) (syn_c1c))) (.classMem (.cv b) (syn_cfin)))
      p0168 p0173
  have p0175 := @g_eleq1 (.cv a) (.cv b) (syn_cfin)
  have p0176_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq a b)
        (syn_wb (.classMem (.cv a) (syn_cfin)) (.classMem (.cv b) (syn_cfin)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cfin syn_cuni syn_wex syn_wa syn_cnnc syn_cint
        simp (config := { failIfUnchanged := false }) only []
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0175
  have p0176 :=
    @g_biimprd (.objEq a b) (.classMem (.cv a) (syn_cfin)) (.classMem (.cv b) (syn_cfin))
      p0176_e00_recanon
  have p0177 :=
    @g_syl9 (.classMem (.cv k) (syn_cnnc))
      (.classMem (.cv b) (syn_cplc (.cv k) (syn_c1c))) (.classMem (.cv b) (syn_cfin))
      (.objEq a b) (.classMem (.cv a) (syn_cfin)) p0174 p0176
  have p0178 :=
    @g_adantr (.classMem (.cv k) (syn_cnnc))
      (.imp (.objEq a b) (.imp (.classMem (.cv b) (syn_cplc (.cv k) (syn_c1c)))
          (.classMem (.cv a) (syn_cfin))))
      (.all c (.all d (.imp (syn_wa (.objMem d k) (syn_wss (.cv c) (.cv d)))
            (.classMem (.cv c) (syn_cfin)))))
      p0177
  have p0179 :=
    @g_jaod
      (syn_wa (.classMem (.cv k) (syn_cnnc)) (.all c (.all d
            (.imp (syn_wa (.objMem d k) (syn_wss (.cv c) (.cv d)))
              (.classMem (.cv c) (syn_cfin))))))
      (syn_wa (syn_wss (.cv a) (.cv b)) (syn_wrex x (.cv b) (.neg (.objMem x a))))
      (.imp (.classMem (.cv b) (syn_cplc (.cv k) (syn_c1c))) (.classMem (.cv a) (syn_cfin)))
      (.objEq a b) p0167 p0178
  have p0180 :=
    @g_syl5bi (syn_wss (.cv a) (.cv b))
      (syn_wo (syn_wa (syn_wss (.cv a) (.cv b)) (syn_wrex x (.cv b) (.neg (.objMem x a))))
        (.objEq a b))
      (syn_wa (.classMem (.cv k) (syn_cnnc)) (.all c (.all d
            (.imp (syn_wa (.objMem d k) (syn_wss (.cv c) (.cv d)))
              (.classMem (.cv c) (syn_cfin))))))
      (.imp (.classMem (.cv b) (syn_cplc (.cv k) (syn_c1c))) (.classMem (.cv a) (syn_cfin)))
      p0111 p0179
  have p0181 :=
    @g_com23
      (syn_wa (.classMem (.cv k) (syn_cnnc)) (.all c (.all d
            (.imp (syn_wa (.objMem d k) (syn_wss (.cv c) (.cv d)))
              (.classMem (.cv c) (syn_cfin))))))
      (syn_wss (.cv a) (.cv b)) (.classMem (.cv b) (syn_cplc (.cv k) (syn_c1c)))
      (.classMem (.cv a) (syn_cfin)) p0180
  have p0182 :=
    @g_imp3a
      (syn_wa (.classMem (.cv k) (syn_cnnc)) (.all c (.all d
            (.imp (syn_wa (.objMem d k) (syn_wss (.cv c) (.cv d)))
              (.classMem (.cv c) (syn_cfin))))))
      (.classMem (.cv b) (syn_cplc (.cv k) (syn_c1c))) (syn_wss (.cv a) (.cv b))
      (.classMem (.cv a) (syn_cfin)) p0181
  have freeVariableCertificate35 :
    a ∉
      ((syn_wa (.classMem (.cv k) (syn_cnnc)) (.all c (.all d
              (.imp (syn_wa (.objMem d k) (syn_wss (.cv c) (.cv d)))
                (.classMem (.cv c) (syn_cfin))))))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
      NFChoice.Compiler.CoreFVSimp.fv_wff_all, NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
      NFChoice.Compiler.CoreFVSimp.fv_wff_objMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfin, Finset.mem_union,
      Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty,
      fresh_a_ne_k, fresh_a_ne_d, fresh_a_ne_c, or_false, and_false, not_false_eq_true]
  have freeVariableCertificate36 :
    b ∉
      ((syn_wa (.classMem (.cv k) (syn_cnnc)) (.all c (.all d
              (.imp (syn_wa (.objMem d k) (syn_wss (.cv c) (.cv d)))
                (.classMem (.cv c) (syn_cfin))))))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
      NFChoice.Compiler.CoreFVSimp.fv_wff_all, NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
      NFChoice.Compiler.CoreFVSimp.fv_wff_objMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfin, Finset.mem_union,
      Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty,
      fresh_b_ne_k, fresh_b_ne_d, fresh_b_ne_c, or_false, and_false, not_false_eq_true]
  have p0183 :=
    @g_alrimivv
      (syn_wa (.classMem (.cv k) (syn_cnnc)) (.all c (.all d
            (.imp (syn_wa (.objMem d k) (syn_wss (.cv c) (.cv d)))
              (.classMem (.cv c) (syn_cfin))))))
      (.imp (syn_wa (.classMem (.cv b) (syn_cplc (.cv k) (syn_c1c))) (syn_wss (.cv a) (.cv b)))
        (.classMem (.cv a) (syn_cfin)))
      a b freeVariableCertificate35 freeVariableCertificate36 p0182
  have p0184 :=
    @g_ex (.classMem (.cv k) (syn_cnnc))
      (.all c (.all d (.imp (syn_wa (.objMem d k) (syn_wss (.cv c) (.cv d)))
            (.classMem (.cv c) (syn_cfin)))))
      (.all a (.all b (.imp (syn_wa (.classMem (.cv b) (syn_cplc (.cv k) (syn_c1c)))
              (syn_wss (.cv a) (.cv b))) (.classMem (.cv a) (syn_cfin)))))
      p0183
  have p0185_e04_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv m) (.cv n)) (syn_wb (.all a (.all b
              (.imp (syn_wa (.objMem b m) (syn_wss (.cv a) (.cv b)))
                (.classMem (.cv a) (syn_cfin))))) (.all a (.all b
              (.imp (syn_wa (.objMem b n) (syn_wss (.cv a) (.cv b)))
                (.classMem (.cv a) (syn_cfin))))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wa syn_wss syn_cin syn_ccompl syn_cnin syn_wnan syn_cfin
          syn_cuni syn_wex syn_cnnc syn_cint
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0100
  have freeVariableCertificate37 : m ∉ ((Class.cv n)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_m_ne_n, not_false_eq_true]
  have freeVariableCertificate38 :
    m ∉
      ((Wff.all c (.all d (.imp (syn_wa (.objMem d k) (syn_wss (.cv c) (.cv d)))
              (.classMem (.cv c) (syn_cfin)))))).fv :=
    by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_all,
      NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
      NFChoice.Compiler.CoreFVSimp.fv_wff_objMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfin, Finset.mem_union,
      Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty,
      fresh_m_ne_d, fresh_m_ne_k, fresh_m_ne_c, or_false, and_false, not_false_eq_true]
  have freeVariableCertificate39 :
    k ∉
      ((Wff.all a (.all b (.imp (syn_wa (.objMem b m) (syn_wss (.cv a) (.cv b)))
              (.classMem (.cv a) (syn_cfin)))))).fv :=
    by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_all,
      NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
      NFChoice.Compiler.CoreFVSimp.fv_wff_objMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfin, Finset.mem_union,
      Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty,
      fresh_k_ne_b, fresh_k_ne_m, fresh_k_ne_a, or_false, and_false, not_false_eq_true]
  have freeVariableCertificate40 :
    m ∉
      ((Wff.all a (.all b (.imp (syn_wa (.classEq (.cv b) (syn_c0)) (syn_wss (.cv a) (.cv b)))
              (.classMem (.cv a) (syn_cfin)))))).fv :=
    by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_all,
      NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfin, Finset.mem_union,
      Finset.mem_erase, Finset.mem_singleton, Finset.notMem_empty, fresh_m_ne_b,
      fresh_m_ne_a, or_false, and_false, not_false_eq_true]
  have freeVariableCertificate41 :
    m ∉
      ((Wff.all a (.all b (.imp (syn_wa (.objMem b n) (syn_wss (.cv a) (.cv b)))
              (.classMem (.cv a) (syn_cfin)))))).fv :=
    by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_all,
      NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
      NFChoice.Compiler.CoreFVSimp.fv_wff_objMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfin, Finset.mem_union,
      Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty,
      fresh_m_ne_b, fresh_m_ne_n, fresh_m_ne_a, or_false, and_false, not_false_eq_true]
  have freeVariableCertificate42 :
    m ∉
      ((Wff.all a (.all b (.imp (syn_wa (.classMem (.cv b) (syn_cplc (.cv k) (syn_c1c)))
                (syn_wss (.cv a) (.cv b))) (.classMem (.cv a) (syn_cfin)))))).fv :=
    by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_all,
      NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfin, Finset.mem_union,
      Finset.mem_erase, Finset.mem_singleton, Finset.notMem_empty, fresh_m_ne_b,
      fresh_m_ne_k, fresh_m_ne_a, or_false, and_false, not_false_eq_true]
  have p0185 :=
    @g_finds
      (.all a (.all b (.imp (syn_wa (.objMem b m) (syn_wss (.cv a) (.cv b)))
            (.classMem (.cv a) (syn_cfin)))))
      (.all a (.all b (.imp (syn_wa (.classEq (.cv b) (syn_c0)) (syn_wss (.cv a) (.cv b)))
            (.classMem (.cv a) (syn_cfin)))))
      (.all c (.all d (.imp (syn_wa (.objMem d k) (syn_wss (.cv c) (.cv d)))
            (.classMem (.cv c) (syn_cfin)))))
      (.all a (.all b (.imp (syn_wa (.classMem (.cv b) (syn_cplc (.cv k) (syn_c1c)))
              (syn_wss (.cv a) (.cv b))) (.classMem (.cv a) (syn_cfin)))))
      (.all a (.all b (.imp (syn_wa (.objMem b n) (syn_wss (.cv a) (.cv b)))
            (.classMem (.cv a) (syn_cfin)))))
      m k (.cv n) freeVariableCertificate37 freeVariableCertificate38
      freeVariableCertificate39 freeVariableCertificate40 freeVariableCertificate41
      freeVariableCertificate42 (show m ≠ k from (by exact fresh_m_ne_k)) p0070 p0079
      p0092 p0096 p0185_e04_recanon p0107 p0184
  have p0186 :=
    @g_n_19_21bbi (.classMem (.cv n) (syn_cnnc))
      (.imp (syn_wa (.objMem b n) (syn_wss (.cv a) (.cv b))) (.classMem (.cv a) (syn_cfin)))
      a b p0185
  have p0187 :=
    @g_exp3a (.classMem (.cv n) (syn_cnnc)) (.objMem b n) (syn_wss (.cv a) (.cv b))
      (.classMem (.cv a) (syn_cfin)) p0186
  have freeVariableCertificate43 :
    n ∉ ((Wff.imp (syn_wss (.cv a) (.cv b)) (.classMem (.cv a) (syn_cfin)))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfin, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_n_ne_a, fresh_n_ne_b, or_false,
      not_false_eq_true]
  have p0188 :=
    @g_rexlimiv (.objMem b n)
      (.imp (syn_wss (.cv a) (.cv b)) (.classMem (.cv a) (syn_cfin))) n (syn_cnnc)
      freeVariableCertificate43 p0187
  have p0189_e00_recanon :
    Nominal.NPrf
      (syn_wb (.classMem (.cv b) (syn_cfin)) (syn_wrex n (syn_cnnc) (.objMem b n))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cfin syn_cuni syn_wex syn_wa syn_cnnc syn_cint syn_wrex
        simp (config := { failIfUnchanged := false }) only []
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0006
  have p0189 :=
    @g_sylbi (.classMem (.cv b) (syn_cfin)) (syn_wrex n (syn_cnnc) (.objMem b n))
      (.imp (syn_wss (.cv a) (.cv b)) (.classMem (.cv a) (syn_cfin))) p0189_e00_recanon
      p0188
  have freeVariableCertificate44 :
    b ∉ ((Wff.imp (syn_wss (.cv a) B) (.classMem (.cv a) (syn_cfin)))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfin, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_b_ne_a, fresh_b_not_B, or_false,
      not_false_eq_true]
  have p0190 :=
    @g_vtoclga (.imp (syn_wss (.cv a) (.cv b)) (.classMem (.cv a) (syn_cfin)))
      (.imp (syn_wss (.cv a) B) (.classMem (.cv a) (syn_cfin))) b B (syn_cfin)
      (by exact (show b ∉ (B).fv from (by exact fresh_b_not_B)))
      (by
        exact
          (show b ∉ ((syn_cfin)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfin];
              exact (show b ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
      freeVariableCertificate44 p0005 p0189
  have freeVariableCertificate45 :
    a ∉
      ((Wff.imp (.classMem B (syn_cfin)) (.imp (syn_wss A B) (.classMem A (syn_cfin))))).fv :=
    by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfin,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, Finset.mem_union,
      Finset.notMem_empty, fresh_a_not_B, fresh_a_not_A, or_false, not_false_eq_true]
  have p0191 :=
    @g_vtoclg
      (.imp (.classMem B (syn_cfin)) (.imp (syn_wss (.cv a) B) (.classMem (.cv a) (syn_cfin))))
      (.imp (.classMem B (syn_cfin)) (.imp (syn_wss A B) (.classMem A (syn_cfin)))) a A V
      (by exact (show a ∉ (A).fv from (by exact fresh_a_not_A))) freeVariableCertificate45
      p0003 p0190
  have p0192 :=
    @g_n_3imp (.classMem A V) (.classMem B (syn_cfin)) (syn_wss A B)
      (.classMem A (syn_cfin)) p0191
  exact p0192


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk009StructuralPart047`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_vfinnc (x : Var) (A : Class) (V : Class) (dv_A_x : x ∉ A.fv) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem A V) (.classMem (syn_cvv) (syn_cfin)))
        (syn_wreu x (syn_cnnc) (.classMem A (.cv x)))) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ A.fv ∪ V.fv
  let y : Var := freshVar proofSupport 0
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_ne_x : y ≠ x := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_x_ne_y : x ≠ y := Ne.symm fresh_y_ne_x
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have p0000 := @g_ssv A
  have p0001 := @g_ssfin A (syn_cvv) V
  have p0002 :=
    @g_mp3an3 (.classMem A V) (.classMem (syn_cvv) (syn_cfin)) (syn_wss A (syn_cvv))
      (.classMem A (syn_cfin)) p0000 p0001
  have p0003 := @g_elfin x A (by exact (show x ∉ (A).fv from (by exact dv_A_x)))
  have p0004 :=
    @g_sylib (syn_wa (.classMem A V) (.classMem (syn_cvv) (syn_cfin)))
      (.classMem A (syn_cfin)) (syn_wrex x (syn_cnnc) (.classMem A (.cv x))) p0002 p0003
  have p0005 := @g_nnceleq A (.cv x) (.cv y)
  have p0006_e00_recanon :
    Nominal.NPrf
      (.imp (syn_wa (syn_wa (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc)))
          (syn_wa (.classMem A (.cv x)) (.classMem A (.cv y)))) (.objEq x y)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wa
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _)
      p0005
  have p0006 :=
    @g_ex (syn_wa (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc)))
      (syn_wa (.classMem A (.cv x)) (.classMem A (.cv y))) (.objEq x y) p0006_e00_recanon
  have p0007 :=
    @g_rgen2a (.imp (syn_wa (.classMem A (.cv x)) (.classMem A (.cv y))) (.objEq x y)) x y
      (syn_cnnc)
      (by
        exact
          (show y ∉ ((syn_cnnc)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc];
              exact (show y ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
      p0006
  have p0008 :=
    @g_a1i
      (syn_wral x (syn_cnnc) (syn_wral y (syn_cnnc)
          (.imp (syn_wa (.classMem A (.cv x)) (.classMem A (.cv y))) (.objEq x y))))
      (syn_wa (.classMem A V) (.classMem (syn_cvv) (syn_cfin))) p0007
  have p0009 := @g_eleq2 (.cv x) (.cv y) A
  have p0010_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq x y) (syn_wb (.classMem A (.cv x)) (.classMem A (.cv y)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0009
  have freeVariableCertificate0 : y ∉ ((Wff.classMem A (.cv x))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      fresh_y_not_A, fresh_y_ne_x, or_false, not_false_eq_true]
  have freeVariableCertificate1 : x ∉ ((Wff.classMem A (.cv y))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      dv_A_x, fresh_x_ne_y, or_false, not_false_eq_true]
  have p0010 :=
    @g_reu4 (.classMem A (.cv x)) (.classMem A (.cv y)) x y (syn_cnnc)
      (by
        exact
          (show x ∉ ((syn_cnnc)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc];
              exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
      (by
        exact
          (show y ∉ ((syn_cnnc)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc];
              exact (show y ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
      freeVariableCertificate0 freeVariableCertificate1
      (show x ≠ y from (by exact fresh_x_ne_y)) p0010_e00_recanon
  have p0011 :=
    @g_sylanbrc (syn_wa (.classMem A V) (.classMem (syn_cvv) (syn_cfin)))
      (syn_wrex x (syn_cnnc) (.classMem A (.cv x)))
      (syn_wral x (syn_cnnc) (syn_wral y (syn_cnnc)
          (.imp (syn_wa (.classMem A (.cv x)) (.classMem A (.cv y))) (.objEq x y))))
      (syn_wreu x (syn_cnnc) (.classMem A (.cv x))) p0004 p0008 p0010
  exact p0011

@[expose]
noncomputable def g_ncfinex (A : Class) :
    Nominal.NPrf (.classMem (syn_cncfin A) (syn_cvv)) :=
  by
  let proofSupport : Finset Var := A.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (h)
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_ncfin x A
      (by exact (show x ∉ (A).fv from (by exact fresh_x_not_A)))
  have p0001 := @g_iotaex (syn_wa (.classMem (.cv x) (syn_cnnc)) (.classMem A (.cv x))) x
  have p0002 :=
    @g_eqeltri (syn_cncfin A)
      (syn_cio x (syn_wa (.classMem (.cv x) (syn_cnnc)) (.classMem A (.cv x)))) (syn_cvv)
      p0000 p0001
  exact p0002

@[expose]
noncomputable def g_ncfineq (A : Class) (B : Class) :
    Nominal.NPrf (.imp (.classEq A B) (.classEq (syn_cncfin A) (syn_cncfin B))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  let x : Var := freshVar proofSupport 0
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
  have p0000 := @g_eleq1 A B (.cv x)
  have p0001 :=
    @g_anbi2d (.classEq A B) (.classMem A (.cv x)) (.classMem B (.cv x))
      (.classMem (.cv x) (syn_cnnc)) p0000
  have freeVariableCertificate0 : x ∉ ((Wff.classEq A B)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union,
      fresh_x_not_A, fresh_x_not_B, or_false, not_false_eq_true]
  have p0002 :=
    @g_iotabidv (.classEq A B)
      (syn_wa (.classMem (.cv x) (syn_cnnc)) (.classMem A (.cv x)))
      (syn_wa (.classMem (.cv x) (syn_cnnc)) (.classMem B (.cv x))) x
      freeVariableCertificate0 p0001
  have p0003 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_ncfin x A
      (by exact (show x ∉ (A).fv from (by exact fresh_x_not_A)))
  have p0004 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_ncfin x B
      (by exact (show x ∉ (B).fv from (by exact fresh_x_not_B)))
  have p0005 :=
    @g_n_3eqtr4g (.classEq A B)
      (syn_cio x (syn_wa (.classMem (.cv x) (syn_cnnc)) (.classMem A (.cv x))))
      (syn_cio x (syn_wa (.classMem (.cv x) (syn_cnnc)) (.classMem B (.cv x))))
      (syn_cncfin A) (syn_cncfin B) p0002 p0003 p0004
  exact p0005

@[expose]
noncomputable def g_ncfinprop (A : Class) (V : Class) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem (syn_cvv) (syn_cfin)) (.classMem A V))
        (syn_wa (.classMem (syn_cncfin A) (syn_cnnc)) (.classMem A (syn_cncfin A)))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ V.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_ncfin x A
      (by exact (show x ∉ (A).fv from (by exact fresh_x_not_A)))
  have p0001 := @g_vfinnc x A V (by exact (show x ∉ (A).fv from (by exact fresh_x_not_A)))
  have p0002 :=
    @g_reiotacl (.classMem A (.cv x)) x (syn_cnnc)
      (by
        exact
          (show x ∉ ((syn_cnnc)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc];
              exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
  have p0003 :=
    @g_syl (syn_wa (.classMem A V) (.classMem (syn_cvv) (syn_cfin)))
      (syn_wreu x (syn_cnnc) (.classMem A (.cv x)))
      (.classMem (syn_cio x (syn_wa (.classMem (.cv x) (syn_cnnc)) (.classMem A (.cv x))))
        (syn_cnnc))
      p0001 p0002
  have p0004 :=
    @g_syl5eqel (syn_wa (.classMem A V) (.classMem (syn_cvv) (syn_cfin))) (syn_cncfin A)
      (syn_cio x (syn_wa (.classMem (.cv x) (syn_cnnc)) (.classMem A (.cv x)))) (syn_cnnc)
      p0000 p0003
  have p0005 :=
    @g_eqcomi (syn_cncfin A)
      (syn_cio x (syn_wa (.classMem (.cv x) (syn_cnnc)) (.classMem A (.cv x)))) p0000
  have p0006 := @g_eleq2 (.cv x) (syn_cncfin A) A
  have freeVariableCertificate0 : x ∉ ((Wff.classMem A (syn_cncfin A))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncfin, Finset.mem_union,
      fresh_x_not_A, or_false, not_false_eq_true]
  have p0007 :=
    @g_reiota2 (.classMem A (.cv x)) (.classMem A (syn_cncfin A)) x (syn_cnnc)
      (syn_cncfin A)
      (by
        exact
          (show x ∉ ((syn_cnnc)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc];
              exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
      (by
        exact
          (show x ∉ ((syn_cncfin A)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncfin];
              exact (show x ∉ (A).fv from (by exact fresh_x_not_A)))))
      freeVariableCertificate0 p0006
  have p0008 :=
    @g_syl2anc (syn_wa (.classMem A V) (.classMem (syn_cvv) (syn_cfin)))
      (.classMem (syn_cncfin A) (syn_cnnc)) (syn_wreu x (syn_cnnc) (.classMem A (.cv x)))
      (syn_wb (.classMem A (syn_cncfin A)) (.classEq
          (syn_cio x (syn_wa (.classMem (.cv x) (syn_cnnc)) (.classMem A (.cv x))))
          (syn_cncfin A)))
      p0004 p0001 p0007
  have p0009 :=
    @g_mpbiri (syn_wa (.classMem A V) (.classMem (syn_cvv) (syn_cfin)))
      (.classMem A (syn_cncfin A))
      (.classEq (syn_cio x (syn_wa (.classMem (.cv x) (syn_cnnc)) (.classMem A (.cv x))))
        (syn_cncfin A))
      p0005 p0008
  have p0010 :=
    @g_jca (syn_wa (.classMem A V) (.classMem (syn_cvv) (syn_cfin)))
      (.classMem (syn_cncfin A) (syn_cnnc)) (.classMem A (syn_cncfin A)) p0004 p0009
  have p0011 :=
    @g_ancoms (.classMem A V) (.classMem (syn_cvv) (syn_cfin))
      (syn_wa (.classMem (syn_cncfin A) (syn_cnnc)) (.classMem A (syn_cncfin A))) p0010
  exact p0011

@[expose]
noncomputable def g_ncfindi (A : Class) (B : Class) (V : Class) (W : Class) :
    Nominal.NPrf
      (.imp (syn_w3a (syn_wa (.classMem (syn_cvv) (syn_cfin)) (.classMem A V)) (.classMem B W)
          (.classEq (syn_cin A B) (syn_c0)))
        (.classEq (syn_cncfin (syn_cun A B)) (syn_cplc (syn_cncfin A) (syn_cncfin B)))) :=
  by
  have p0000 :=
    @g_simp1l (.classMem (syn_cvv) (syn_cfin)) (.classMem A V) (.classMem B W)
      (.classEq (syn_cin A B) (syn_c0))
  have p0001 :=
    @g_simp1r (.classMem (syn_cvv) (syn_cfin)) (.classMem A V) (.classMem B W)
      (.classEq (syn_cin A B) (syn_c0))
  have p0002 :=
    @g_simp2 (syn_wa (.classMem (syn_cvv) (syn_cfin)) (.classMem A V)) (.classMem B W)
      (.classEq (syn_cin A B) (syn_c0))
  have p0003 := @g_unexg A B V W
  have p0004 :=
    @g_syl2anc
      (syn_w3a (syn_wa (.classMem (syn_cvv) (syn_cfin)) (.classMem A V)) (.classMem B W)
        (.classEq (syn_cin A B) (syn_c0)))
      (.classMem A V) (.classMem B W) (.classMem (syn_cun A B) (syn_cvv)) p0001 p0002
      p0003
  have p0005 := @g_ncfinprop (syn_cun A B) (syn_cvv)
  have p0006 :=
    @g_syl2anc
      (syn_w3a (syn_wa (.classMem (syn_cvv) (syn_cfin)) (.classMem A V)) (.classMem B W)
        (.classEq (syn_cin A B) (syn_c0)))
      (.classMem (syn_cvv) (syn_cfin)) (.classMem (syn_cun A B) (syn_cvv))
      (syn_wa (.classMem (syn_cncfin (syn_cun A B)) (syn_cnnc))
        (.classMem (syn_cun A B) (syn_cncfin (syn_cun A B))))
      p0000 p0004 p0005
  have p0007 :=
    @g_simpld
      (syn_w3a (syn_wa (.classMem (syn_cvv) (syn_cfin)) (.classMem A V)) (.classMem B W)
        (.classEq (syn_cin A B) (syn_c0)))
      (.classMem (syn_cncfin (syn_cun A B)) (syn_cnnc))
      (.classMem (syn_cun A B) (syn_cncfin (syn_cun A B))) p0006
  have p0008 := @g_ncfinprop A V
  have p0009 :=
    @g_syl2anc
      (syn_w3a (syn_wa (.classMem (syn_cvv) (syn_cfin)) (.classMem A V)) (.classMem B W)
        (.classEq (syn_cin A B) (syn_c0)))
      (.classMem (syn_cvv) (syn_cfin)) (.classMem A V)
      (syn_wa (.classMem (syn_cncfin A) (syn_cnnc)) (.classMem A (syn_cncfin A))) p0000
      p0001 p0008
  have p0010 :=
    @g_simpld
      (syn_w3a (syn_wa (.classMem (syn_cvv) (syn_cfin)) (.classMem A V)) (.classMem B W)
        (.classEq (syn_cin A B) (syn_c0)))
      (.classMem (syn_cncfin A) (syn_cnnc)) (.classMem A (syn_cncfin A)) p0009
  have p0011 := @g_ncfinprop B W
  have p0012 :=
    @g_syl2anc
      (syn_w3a (syn_wa (.classMem (syn_cvv) (syn_cfin)) (.classMem A V)) (.classMem B W)
        (.classEq (syn_cin A B) (syn_c0)))
      (.classMem (syn_cvv) (syn_cfin)) (.classMem B W)
      (syn_wa (.classMem (syn_cncfin B) (syn_cnnc)) (.classMem B (syn_cncfin B))) p0000
      p0002 p0011
  have p0013 :=
    @g_simpld
      (syn_w3a (syn_wa (.classMem (syn_cvv) (syn_cfin)) (.classMem A V)) (.classMem B W)
        (.classEq (syn_cin A B) (syn_c0)))
      (.classMem (syn_cncfin B) (syn_cnnc)) (.classMem B (syn_cncfin B)) p0012
  have p0014 := @g_nncaddccl (syn_cncfin A) (syn_cncfin B)
  have p0015 :=
    @g_syl2anc
      (syn_w3a (syn_wa (.classMem (syn_cvv) (syn_cfin)) (.classMem A V)) (.classMem B W)
        (.classEq (syn_cin A B) (syn_c0)))
      (.classMem (syn_cncfin A) (syn_cnnc)) (.classMem (syn_cncfin B) (syn_cnnc))
      (.classMem (syn_cplc (syn_cncfin A) (syn_cncfin B)) (syn_cnnc)) p0010 p0013 p0014
  have p0016 :=
    @g_simprd
      (syn_w3a (syn_wa (.classMem (syn_cvv) (syn_cfin)) (.classMem A V)) (.classMem B W)
        (.classEq (syn_cin A B) (syn_c0)))
      (.classMem (syn_cncfin (syn_cun A B)) (syn_cnnc))
      (.classMem (syn_cun A B) (syn_cncfin (syn_cun A B))) p0006
  have p0017 :=
    @g_simprd
      (syn_w3a (syn_wa (.classMem (syn_cvv) (syn_cfin)) (.classMem A V)) (.classMem B W)
        (.classEq (syn_cin A B) (syn_c0)))
      (.classMem (syn_cncfin A) (syn_cnnc)) (.classMem A (syn_cncfin A)) p0009
  have p0018 :=
    @g_simprd
      (syn_w3a (syn_wa (.classMem (syn_cvv) (syn_cfin)) (.classMem A V)) (.classMem B W)
        (.classEq (syn_cin A B) (syn_c0)))
      (.classMem (syn_cncfin B) (syn_cnnc)) (.classMem B (syn_cncfin B)) p0012
  have p0019 :=
    @g_simp3 (syn_wa (.classMem (syn_cvv) (syn_cfin)) (.classMem A V)) (.classMem B W)
      (.classEq (syn_cin A B) (syn_c0))
  have p0020 := @g_eladdci A B (syn_cncfin A) (syn_cncfin B)
  have p0021 :=
    @g_syl3anc
      (syn_w3a (syn_wa (.classMem (syn_cvv) (syn_cfin)) (.classMem A V)) (.classMem B W)
        (.classEq (syn_cin A B) (syn_c0)))
      (.classMem A (syn_cncfin A)) (.classMem B (syn_cncfin B))
      (.classEq (syn_cin A B) (syn_c0))
      (.classMem (syn_cun A B) (syn_cplc (syn_cncfin A) (syn_cncfin B))) p0017 p0018 p0019
      p0020
  have p0022 :=
    @g_nnceleq (syn_cun A B) (syn_cncfin (syn_cun A B))
      (syn_cplc (syn_cncfin A) (syn_cncfin B))
  have p0023 :=
    @g_syl22anc
      (syn_w3a (syn_wa (.classMem (syn_cvv) (syn_cfin)) (.classMem A V)) (.classMem B W)
        (.classEq (syn_cin A B) (syn_c0)))
      (.classMem (syn_cncfin (syn_cun A B)) (syn_cnnc))
      (.classMem (syn_cplc (syn_cncfin A) (syn_cncfin B)) (syn_cnnc))
      (.classMem (syn_cun A B) (syn_cncfin (syn_cun A B)))
      (.classMem (syn_cun A B) (syn_cplc (syn_cncfin A) (syn_cncfin B)))
      (.classEq (syn_cncfin (syn_cun A B)) (syn_cplc (syn_cncfin A) (syn_cncfin B))) p0007
      p0015 p0016 p0021 p0022
  exact p0023

@[expose]
noncomputable def g_ncfinsn (A : Class) (V : Class) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem (syn_cvv) (syn_cfin)) (.classMem A V))
        (.classEq (syn_cncfin (syn_csn A)) (syn_c1c))) :=
  by
  have p0000 := @g_snex A
  have p0001 := @g_ncfinprop (syn_csn A) (syn_cvv)
  have p0002 :=
    @g_mpan2 (.classMem (syn_cvv) (syn_cfin)) (.classMem (syn_csn A) (syn_cvv))
      (syn_wa (.classMem (syn_cncfin (syn_csn A)) (syn_cnnc))
        (.classMem (syn_csn A) (syn_cncfin (syn_csn A))))
      p0000 p0001
  have p0003 :=
    @g_adantr (.classMem (syn_cvv) (syn_cfin))
      (syn_wa (.classMem (syn_cncfin (syn_csn A)) (syn_cnnc))
        (.classMem (syn_csn A) (syn_cncfin (syn_csn A))))
      (.classMem A V) p0002
  have p0004 :=
    @g_simpld (syn_wa (.classMem (syn_cvv) (syn_cfin)) (.classMem A V))
      (.classMem (syn_cncfin (syn_csn A)) (syn_cnnc))
      (.classMem (syn_csn A) (syn_cncfin (syn_csn A))) p0003
  have p0005 := @g_n_1cnnc
  have p0006 :=
    @g_a1i (.classMem (syn_c1c) (syn_cnnc))
      (syn_wa (.classMem (syn_cvv) (syn_cfin)) (.classMem A V)) p0005
  have p0007 :=
    @g_simprd (syn_wa (.classMem (syn_cvv) (syn_cfin)) (.classMem A V))
      (.classMem (syn_cncfin (syn_csn A)) (syn_cnnc))
      (.classMem (syn_csn A) (syn_cncfin (syn_csn A))) p0003
  have p0008 := @g_snel1cg A V
  have p0009 :=
    @g_adantl (.classMem A V) (.classMem (syn_csn A) (syn_c1c))
      (.classMem (syn_cvv) (syn_cfin)) p0008
  have p0010 := @g_nnceleq (syn_csn A) (syn_cncfin (syn_csn A)) (syn_c1c)
  have p0011 :=
    @g_syl22anc (syn_wa (.classMem (syn_cvv) (syn_cfin)) (.classMem A V))
      (.classMem (syn_cncfin (syn_csn A)) (syn_cnnc)) (.classMem (syn_c1c) (syn_cnnc))
      (.classMem (syn_csn A) (syn_cncfin (syn_csn A))) (.classMem (syn_csn A) (syn_c1c))
      (.classEq (syn_cncfin (syn_csn A)) (syn_c1c)) p0004 p0006 p0007 p0009 p0010
  exact p0011

@[expose]
noncomputable def g_eqpwrelk (A : Class) (B : Class)
    (hyp_eqpwrelk_1 : Nominal.NPrf (.classMem A (syn_cvv)))
    (hyp_eqpwrelk_2 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf
      (syn_wb (.classMem (syn_copk (syn_csn A) B) (syn_ccompl (syn_cimak
              (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_cssetk))))
              (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (.classEq B (syn_cpw A))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  let x : Var := freshVar proofSupport 0
  let t : Var := freshVar proofSupport 1
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
  have fresh_t : t ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_t_not_A : t ∉ A.fv := by
    intro h
    exact fresh_t (Finset.mem_union_left _ (h))
  have fresh_t_not_B : t ∉ B.fv := by
    intro h
    exact fresh_t (Finset.mem_union_right _ (h))
  have fresh_x_ne_t : x ≠ t :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_t_ne_x : t ≠ x := Ne.symm fresh_x_ne_t
  have p0000 := @g_opkex (syn_csn A) B
  have freeVariableCertificate0 :
    t ∉
      ((syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_cssetk))))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik, Finset.mem_union,
      Finset.notMem_empty, or_false, not_false_eq_true]
  have freeVariableCertificate1 : t ∉ ((syn_cpw1 (syn_cpw1 (syn_c1c)))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.notMem_empty,
      not_false_eq_true]
  have freeVariableCertificate2 : t ∉ ((syn_copk (syn_csn A) B)).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
      fresh_t_not_A, fresh_t_not_B, or_false, not_false_eq_true]
  have p0001 :=
    @g_elimak t
      (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_cssetk))))
      (syn_cpw1 (syn_cpw1 (syn_c1c))) (syn_copk (syn_csn A) B) freeVariableCertificate0
      freeVariableCertificate1 freeVariableCertificate2 p0000
  have freeVariableCertificate3 : x ∉ ((Class.cv t)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_x_ne_t, not_false_eq_true]
  have p0002 := @g_elpw121c x (.cv t) freeVariableCertificate3
  have p0003 :=
    @g_anbi1i (.classMem (.cv t) (syn_cpw1 (syn_cpw1 (syn_c1c))))
      (syn_wex x (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv x))))))
      (.classMem (syn_copk (.cv t) (syn_copk (syn_csn A) B))
        (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_cssetk)))))
      p0002
  have freeVariableCertificate4 :
    x ∉
      ((Wff.classMem (syn_copk (.cv t) (syn_copk (syn_csn A) B))
          (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_cssetk)))))).fv :=
    by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_x_ne_t, fresh_x_not_A,
      fresh_x_not_B, or_false, not_false_eq_true]
  have p0004 :=
    @g_n_19_41v (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv x)))))
      (.classMem (syn_copk (.cv t) (syn_copk (syn_csn A) B))
        (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_cssetk)))))
      x freeVariableCertificate4
  have p0005 :=
    @g_bitr4i
      (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_cpw1 (syn_c1c))))
        (.classMem (syn_copk (.cv t) (syn_copk (syn_csn A) B))
          (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_cssetk))))))
      (syn_wa (syn_wex x (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv x))))))
        (.classMem (syn_copk (.cv t) (syn_copk (syn_csn A) B))
          (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_cssetk))))))
      (syn_wex x (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv x)))))
          (.classMem (syn_copk (.cv t) (syn_copk (syn_csn A) B))
            (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_cssetk)))))))
      p0003 p0004
  have p0006 :=
    @g_exbii
      (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_cpw1 (syn_c1c))))
        (.classMem (syn_copk (.cv t) (syn_copk (syn_csn A) B))
          (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_cssetk))))))
      (syn_wex x (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv x)))))
          (.classMem (syn_copk (.cv t) (syn_copk (syn_csn A) B))
            (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_cssetk)))))))
      t p0005
  have p0007 :=
    (Nominal.biimpRefl (syn_wrex t (syn_cpw1 (syn_cpw1 (syn_c1c)))
        (.classMem (syn_copk (.cv t) (syn_copk (syn_csn A) B))
          (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_cssetk)))))))
  have p0008 :=
    @g_excom
      (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv x)))))
        (.classMem (syn_copk (.cv t) (syn_copk (syn_csn A) B))
          (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_cssetk))))))
      x t
  have p0009 :=
    @g_n_3bitr4i
      (syn_wex t (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_cpw1 (syn_c1c))))
          (.classMem (syn_copk (.cv t) (syn_copk (syn_csn A) B))
            (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_cssetk)))))))
      (syn_wex t (syn_wex x (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv x)))))
            (.classMem (syn_copk (.cv t) (syn_copk (syn_csn A) B))
              (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_cssetk))))))))
      (syn_wrex t (syn_cpw1 (syn_cpw1 (syn_c1c)))
        (.classMem (syn_copk (.cv t) (syn_copk (syn_csn A) B))
          (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_cssetk))))))
      (syn_wex x (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv x)))))
            (.classMem (syn_copk (.cv t) (syn_copk (syn_csn A) B))
              (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_cssetk))))))))
      p0006 p0007 p0008
  have p0010 := @g_snex (syn_csn (syn_csn (.cv x)))
  have p0011 :=
    @g_opkeq1 (.cv t) (syn_csn (syn_csn (syn_csn (.cv x)))) (syn_copk (syn_csn A) B)
  have p0012 :=
    @g_eleq1d (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv x)))))
      (syn_copk (.cv t) (syn_copk (syn_csn A) B))
      (syn_copk (syn_csn (syn_csn (syn_csn (.cv x)))) (syn_copk (syn_csn A) B))
      (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_cssetk)))) p0011
  have freeVariableCertificate5 : t ∉ ((syn_csn (syn_csn (syn_csn (.cv x))))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_t_ne_x,
      not_false_eq_true]
  have freeVariableCertificate6 :
    t ∉
      ((Wff.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv x)))) (syn_copk (syn_csn A) B))
          (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_cssetk)))))).fv :=
    by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_t_ne_x, fresh_t_not_A,
      fresh_t_not_B, or_false, not_false_eq_true]
  have p0013 :=
    @g_ceqsexv
      (.classMem (syn_copk (.cv t) (syn_copk (syn_csn A) B))
        (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_cssetk)))))
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv x)))) (syn_copk (syn_csn A) B))
        (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_cssetk)))))
      t (syn_csn (syn_csn (syn_csn (.cv x)))) freeVariableCertificate5
      freeVariableCertificate6 p0010 p0012
  have p0014 :=
    @g_elsymdif (syn_copk (syn_csn (syn_csn (syn_csn (.cv x)))) (syn_copk (syn_csn A) B))
      (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_cssetk)))
  have p0015 := @g_snex (.cv x)
  have p0016 := @g_snex A
  have p0017 :=
    @g_otkelins2k (syn_csn (.cv x)) (syn_csn A) B (syn_cssetk) p0015 p0016 hyp_eqpwrelk_2
  have p0018 := @g_vex x
  have p0019 := @g_elssetk (.cv x) B p0018 hyp_eqpwrelk_2
  have p0020 :=
    @g_bitri
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv x)))) (syn_copk (syn_csn A) B))
        (syn_cins2k (syn_cssetk)))
      (.classMem (syn_copk (syn_csn (.cv x)) B) (syn_cssetk)) (.classMem (.cv x) B) p0017
      p0019
  have p0021 :=
    @g_otkelins3k (syn_csn (.cv x)) (syn_csn A) B (syn_csik (syn_cssetk)) p0015 p0016
      hyp_eqpwrelk_2
  have p0022 := @g_opksnelsik (.cv x) A (syn_cssetk) p0018 hyp_eqpwrelk_1
  have p0023 := @g_opkelssetkg (.cv x) A (syn_cvv) (syn_cvv)
  have p0024 :=
    @g_mp2an (.classMem (.cv x) (syn_cvv)) (.classMem A (syn_cvv))
      (syn_wb (.classMem (syn_copk (.cv x) A) (syn_cssetk)) (syn_wss (.cv x) A)) p0018
      hyp_eqpwrelk_1 p0023
  have p0025 :=
    @g_n_3bitri
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv x)))) (syn_copk (syn_csn A) B))
        (syn_cins3k (syn_csik (syn_cssetk))))
      (.classMem (syn_copk (syn_csn (.cv x)) (syn_csn A)) (syn_csik (syn_cssetk)))
      (.classMem (syn_copk (.cv x) A) (syn_cssetk)) (syn_wss (.cv x) A) p0021 p0022 p0024
  have p0026 :=
    @g_bibi12i
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv x)))) (syn_copk (syn_csn A) B))
        (syn_cins2k (syn_cssetk)))
      (.classMem (.cv x) B)
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv x)))) (syn_copk (syn_csn A) B))
        (syn_cins3k (syn_csik (syn_cssetk))))
      (syn_wss (.cv x) A) p0020 p0025
  have p0027 :=
    @g_notbii
      (syn_wb (.classMem
          (syn_copk (syn_csn (syn_csn (syn_csn (.cv x)))) (syn_copk (syn_csn A) B))
          (syn_cins2k (syn_cssetk))) (.classMem
          (syn_copk (syn_csn (syn_csn (syn_csn (.cv x)))) (syn_copk (syn_csn A) B))
          (syn_cins3k (syn_csik (syn_cssetk)))))
      (syn_wb (.classMem (.cv x) B) (syn_wss (.cv x) A)) p0026
  have p0028 :=
    @g_n_3bitri
      (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv x)))))
          (.classMem (syn_copk (.cv t) (syn_copk (syn_csn A) B))
            (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_cssetk)))))))
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv x)))) (syn_copk (syn_csn A) B))
        (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_cssetk)))))
      (.neg (syn_wb (.classMem
            (syn_copk (syn_csn (syn_csn (syn_csn (.cv x)))) (syn_copk (syn_csn A) B))
            (syn_cins2k (syn_cssetk))) (.classMem
            (syn_copk (syn_csn (syn_csn (syn_csn (.cv x)))) (syn_copk (syn_csn A) B))
            (syn_cins3k (syn_csik (syn_cssetk))))))
      (.neg (syn_wb (.classMem (.cv x) B) (syn_wss (.cv x) A))) p0013 p0014 p0027
  have p0029 :=
    @g_exbii
      (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv x)))))
          (.classMem (syn_copk (.cv t) (syn_copk (syn_csn A) B))
            (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_cssetk)))))))
      (.neg (syn_wb (.classMem (.cv x) B) (syn_wss (.cv x) A))) x p0028
  have p0030 :=
    @g_n_3bitri
      (.classMem (syn_copk (syn_csn A) B) (syn_cimak
          (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_cssetk))))
          (syn_cpw1 (syn_cpw1 (syn_c1c)))))
      (syn_wrex t (syn_cpw1 (syn_cpw1 (syn_c1c)))
        (.classMem (syn_copk (.cv t) (syn_copk (syn_csn A) B))
          (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_cssetk))))))
      (syn_wex x (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv x)))))
            (.classMem (syn_copk (.cv t) (syn_copk (syn_csn A) B))
              (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_cssetk))))))))
      (syn_wex x (.neg (syn_wb (.classMem (.cv x) B) (syn_wss (.cv x) A)))) p0001 p0009
      p0029
  have p0031 :=
    @g_notbii
      (.classMem (syn_copk (syn_csn A) B) (syn_cimak
          (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_cssetk))))
          (syn_cpw1 (syn_cpw1 (syn_c1c)))))
      (syn_wex x (.neg (syn_wb (.classMem (.cv x) B) (syn_wss (.cv x) A)))) p0030
  have p0032 :=
    @g_elcompl (syn_copk (syn_csn A) B)
      (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_cssetk))))
        (syn_cpw1 (syn_cpw1 (syn_c1c))))
      p0000
  have p0033 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_pw x A
      (by exact (show x ∉ (A).fv from (by exact fresh_x_not_A)))
  have p0034 := @g_eqeq2i (syn_cpw A) (.cab x (syn_wss (.cv x) A)) B p0033
  have p0035 :=
    @g_eqabb (syn_wss (.cv x) A) x B
      (by exact (show x ∉ (B).fv from (by exact fresh_x_not_B)))
  have p0036 := @g_alex (syn_wb (.classMem (.cv x) B) (syn_wss (.cv x) A)) x
  have p0037 :=
    @g_n_3bitri (.classEq B (syn_cpw A)) (.classEq B (.cab x (syn_wss (.cv x) A)))
      (.all x (syn_wb (.classMem (.cv x) B) (syn_wss (.cv x) A)))
      (.neg (syn_wex x (.neg (syn_wb (.classMem (.cv x) B) (syn_wss (.cv x) A))))) p0034
      p0035 p0036
  have p0038 :=
    @g_n_3bitr4i
      (.neg (.classMem (syn_copk (syn_csn A) B) (syn_cimak
            (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_cssetk))))
            (syn_cpw1 (syn_cpw1 (syn_c1c))))))
      (.neg (syn_wex x (.neg (syn_wb (.classMem (.cv x) B) (syn_wss (.cv x) A)))))
      (.classMem (syn_copk (syn_csn A) B) (syn_ccompl (syn_cimak
            (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_cssetk))))
            (syn_cpw1 (syn_cpw1 (syn_c1c))))))
      (.classEq B (syn_cpw A)) p0031 p0032 p0037
  exact p0038

@[expose]
noncomputable def g_eqpw1relk (A : Class) (B : Class)
    (hyp_eqpw1relk_1 : Nominal.NPrf (.classMem A (syn_cvv)))
    (hyp_eqpw1relk_2 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf
      (syn_wb (.classMem (syn_copk A (syn_csn B))
          (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak
              (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk))))
              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (.classEq A (syn_cpw1 B))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  let x : Var := freshVar proofSupport 0
  let t : Var := freshVar proofSupport 1
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
  have fresh_t : t ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_t_not_A : t ∉ A.fv := by
    intro h
    exact fresh_t (Finset.mem_union_left _ (h))
  have fresh_t_not_B : t ∉ B.fv := by
    intro h
    exact fresh_t (Finset.mem_union_right _ (h))
  have fresh_x_ne_t : x ≠ t :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_t_ne_x : t ≠ x := Ne.symm fresh_x_ne_t
  have p0000 := @g_snex B
  have p0001 :=
    @g_opkelxpk A (syn_csn B) (syn_cpw (syn_c1c)) (syn_cvv) hyp_eqpw1relk_1 p0000
  have p0002 :=
    @g_mpbiran2
      (.classMem (syn_copk A (syn_csn B)) (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)))
      (.classMem A (syn_cpw (syn_c1c))) (.classMem (syn_csn B) (syn_cvv)) p0000 p0001
  have p0003 := @g_elpw A (syn_c1c) hyp_eqpw1relk_1
  have p0004 :=
    @g_bitri (.classMem (syn_copk A (syn_csn B)) (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)))
      (.classMem A (syn_cpw (syn_c1c))) (syn_wss A (syn_c1c)) p0002 p0003
  have p0005 := @g_opkex A (syn_csn B)
  have freeVariableCertificate0 :
    t ∉
      ((syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk))))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik, Finset.mem_union,
      Finset.notMem_empty, or_false, not_false_eq_true]
  have freeVariableCertificate1 : t ∉ ((syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.notMem_empty,
      not_false_eq_true]
  have freeVariableCertificate2 : t ∉ ((syn_copk A (syn_csn B))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
      fresh_t_not_A, fresh_t_not_B, or_false, not_false_eq_true]
  have p0006 :=
    @g_elimak t
      (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk))))
      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))) (syn_copk A (syn_csn B))
      freeVariableCertificate0 freeVariableCertificate1 freeVariableCertificate2 p0005
  have freeVariableCertificate3 : x ∉ ((Class.cv t)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_x_ne_t, not_false_eq_true]
  have p0007 := @g_elpw131c x (.cv t) freeVariableCertificate3
  have p0008 :=
    @g_anbi1i (.classMem (.cv t) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))
      (syn_wex x (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))
      (.classMem (syn_copk (.cv t) (syn_copk A (syn_csn B)))
        (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))))
      p0007
  have freeVariableCertificate4 :
    x ∉
      ((Wff.classMem (syn_copk (.cv t) (syn_copk A (syn_csn B)))
          (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))))).fv :=
    by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_x_ne_t, fresh_x_not_A,
      fresh_x_not_B, or_false, not_false_eq_true]
  have p0009 :=
    @g_n_19_41v (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))
      (.classMem (syn_copk (.cv t) (syn_copk A (syn_csn B)))
        (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))))
      x freeVariableCertificate4
  have p0010 :=
    @g_bitr4i
      (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))
        (.classMem (syn_copk (.cv t) (syn_copk A (syn_csn B)))
          (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk))))))
      (syn_wa (syn_wex x (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))
        (.classMem (syn_copk (.cv t) (syn_copk A (syn_csn B)))
          (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk))))))
      (syn_wex x (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))
          (.classMem (syn_copk (.cv t) (syn_copk A (syn_csn B)))
            (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))))))
      p0008 p0009
  have p0011 :=
    @g_exbii
      (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))
        (.classMem (syn_copk (.cv t) (syn_copk A (syn_csn B)))
          (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk))))))
      (syn_wex x (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))
          (.classMem (syn_copk (.cv t) (syn_copk A (syn_csn B)))
            (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))))))
      t p0010
  have p0012 :=
    (Nominal.biimpRefl (syn_wrex t (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))
        (.classMem (syn_copk (.cv t) (syn_copk A (syn_csn B)))
          (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))))))
  have p0013 :=
    @g_excom
      (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))
        (.classMem (syn_copk (.cv t) (syn_copk A (syn_csn B)))
          (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk))))))
      x t
  have p0014 :=
    @g_n_3bitr4i
      (syn_wex t (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))
          (.classMem (syn_copk (.cv t) (syn_copk A (syn_csn B)))
            (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))))))
      (syn_wex t (syn_wex x
          (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))
            (.classMem (syn_copk (.cv t) (syn_copk A (syn_csn B)))
              (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk))))))))
      (syn_wrex t (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))
        (.classMem (syn_copk (.cv t) (syn_copk A (syn_csn B)))
          (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk))))))
      (syn_wex x (syn_wex t
          (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))
            (.classMem (syn_copk (.cv t) (syn_copk A (syn_csn B)))
              (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk))))))))
      p0011 p0012 p0013
  have p0015 :=
    @g_bitri
      (.classMem (syn_copk A (syn_csn B)) (syn_cimak
          (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk))))
          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))
      (syn_wrex t (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))
        (.classMem (syn_copk (.cv t) (syn_copk A (syn_csn B)))
          (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk))))))
      (syn_wex x (syn_wex t
          (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))
            (.classMem (syn_copk (.cv t) (syn_copk A (syn_csn B)))
              (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk))))))))
      p0006 p0014
  have p0016 := @g_snex (syn_csn (syn_csn (syn_csn (.cv x))))
  have p0017 :=
    @g_opkeq1 (.cv t) (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))
      (syn_copk A (syn_csn B))
  have p0018 :=
    @g_eleq1d (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))
      (syn_copk (.cv t) (syn_copk A (syn_csn B)))
      (syn_copk (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))) (syn_copk A (syn_csn B)))
      (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) p0017
  have freeVariableCertificate5 :
    t ∉ ((syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_t_ne_x,
      not_false_eq_true]
  have freeVariableCertificate6 :
    t ∉
      ((Wff.classMem (syn_copk (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))
            (syn_copk A (syn_csn B))) (syn_csymdif (syn_cins3k (syn_cssetk))
            (syn_cins2k (syn_csik (syn_cssetk)))))).fv :=
    by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_t_ne_x, fresh_t_not_A,
      fresh_t_not_B, or_false, not_false_eq_true]
  have p0019 :=
    @g_ceqsexv
      (.classMem (syn_copk (.cv t) (syn_copk A (syn_csn B)))
        (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))))
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))
          (syn_copk A (syn_csn B)))
        (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))))
      t (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))) freeVariableCertificate5
      freeVariableCertificate6 p0016 p0018
  have p0020 :=
    @g_elsymdif
      (syn_copk (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))) (syn_copk A (syn_csn B)))
      (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))
  have p0021 := @g_snex (syn_csn (.cv x))
  have p0022 :=
    @g_otkelins3k (syn_csn (syn_csn (.cv x))) A (syn_csn B) (syn_cssetk) p0021
      hyp_eqpw1relk_1 p0000
  have p0023 := @g_snex (.cv x)
  have p0024 := @g_elssetk (syn_csn (.cv x)) A p0023 hyp_eqpw1relk_1
  have p0025 :=
    @g_bitri
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))
          (syn_copk A (syn_csn B))) (syn_cins3k (syn_cssetk)))
      (.classMem (syn_copk (syn_csn (syn_csn (.cv x))) A) (syn_cssetk))
      (.classMem (syn_csn (.cv x)) A) p0022 p0024
  have p0026 :=
    @g_otkelins2k (syn_csn (syn_csn (.cv x))) A (syn_csn B) (syn_csik (syn_cssetk)) p0021
      hyp_eqpw1relk_1 p0000
  have p0027 := @g_opksnelsik (syn_csn (.cv x)) B (syn_cssetk) p0023 hyp_eqpw1relk_2
  have p0028 := @g_vex x
  have p0029 := @g_elssetk (.cv x) B p0028 hyp_eqpw1relk_2
  have p0030 :=
    @g_bitri
      (.classMem (syn_copk (syn_csn (syn_csn (.cv x))) (syn_csn B)) (syn_csik (syn_cssetk)))
      (.classMem (syn_copk (syn_csn (.cv x)) B) (syn_cssetk)) (.classMem (.cv x) B) p0027
      p0029
  have p0031 :=
    @g_bitri
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))
          (syn_copk A (syn_csn B))) (syn_cins2k (syn_csik (syn_cssetk))))
      (.classMem (syn_copk (syn_csn (syn_csn (.cv x))) (syn_csn B)) (syn_csik (syn_cssetk)))
      (.classMem (.cv x) B) p0026 p0030
  have p0032 :=
    @g_bibi12i
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))
          (syn_copk A (syn_csn B))) (syn_cins3k (syn_cssetk)))
      (.classMem (syn_csn (.cv x)) A)
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))
          (syn_copk A (syn_csn B))) (syn_cins2k (syn_csik (syn_cssetk))))
      (.classMem (.cv x) B) p0025 p0031
  have p0033 :=
    @g_xchbinx
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))
          (syn_copk A (syn_csn B)))
        (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))))
      (syn_wb (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))
            (syn_copk A (syn_csn B))) (syn_cins3k (syn_cssetk))) (.classMem
          (syn_copk (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))) (syn_copk A (syn_csn B)))
          (syn_cins2k (syn_csik (syn_cssetk)))))
      (syn_wb (.classMem (syn_csn (.cv x)) A) (.classMem (.cv x) B)) p0020 p0032
  have p0034 :=
    @g_bitri
      (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))
          (.classMem (syn_copk (.cv t) (syn_copk A (syn_csn B)))
            (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))))))
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))
          (syn_copk A (syn_csn B)))
        (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))))
      (.neg (syn_wb (.classMem (syn_csn (.cv x)) A) (.classMem (.cv x) B))) p0019 p0033
  have p0035 :=
    @g_exbii
      (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))
          (.classMem (syn_copk (.cv t) (syn_copk A (syn_csn B)))
            (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))))))
      (.neg (syn_wb (.classMem (syn_csn (.cv x)) A) (.classMem (.cv x) B))) x p0034
  have p0036 := @g_exnal (syn_wb (.classMem (syn_csn (.cv x)) A) (.classMem (.cv x) B)) x
  have p0037 :=
    @g_n_3bitrri
      (.classMem (syn_copk A (syn_csn B)) (syn_cimak
          (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk))))
          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))
      (syn_wex x (syn_wex t
          (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))
            (.classMem (syn_copk (.cv t) (syn_copk A (syn_csn B)))
              (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk))))))))
      (syn_wex x (.neg (syn_wb (.classMem (syn_csn (.cv x)) A) (.classMem (.cv x) B))))
      (.neg (.all x (syn_wb (.classMem (syn_csn (.cv x)) A) (.classMem (.cv x) B)))) p0015
      p0035 p0036
  have p0038 :=
    @g_con1bii (.all x (syn_wb (.classMem (syn_csn (.cv x)) A) (.classMem (.cv x) B)))
      (.classMem (syn_copk A (syn_csn B)) (syn_cimak
          (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk))))
          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))
      p0037
  have p0039 :=
    @g_anbi12i
      (.classMem (syn_copk A (syn_csn B)) (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)))
      (syn_wss A (syn_c1c))
      (.neg (.classMem (syn_copk A (syn_csn B)) (syn_cimak
            (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk))))
            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
      (.all x (syn_wb (.classMem (syn_csn (.cv x)) A) (.classMem (.cv x) B))) p0004 p0038
  have p0040 :=
    @g_eldif (syn_copk A (syn_csn B)) (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv))
      (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk))))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))
  have p0041 :=
    @g_eqpw1 x A B (by exact (show x ∉ (A).fv from (by exact fresh_x_not_A)))
      (by exact (show x ∉ (B).fv from (by exact fresh_x_not_B)))
  have p0042 :=
    @g_n_3bitr4i
      (syn_wa (.classMem (syn_copk A (syn_csn B)) (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)))
        (.neg (.classMem (syn_copk A (syn_csn B)) (syn_cimak
              (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk))))
              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
      (syn_wa (syn_wss A (syn_c1c))
        (.all x (syn_wb (.classMem (syn_csn (.cv x)) A) (.classMem (.cv x) B))))
      (.classMem (syn_copk A (syn_csn B)) (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv))
          (syn_cimak
            (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk))))
            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
      (.classEq A (syn_cpw1 B)) p0039 p0040 p0041
  exact p0042


end NFChoice.DirectNominalPrf.WPPReplay

end
