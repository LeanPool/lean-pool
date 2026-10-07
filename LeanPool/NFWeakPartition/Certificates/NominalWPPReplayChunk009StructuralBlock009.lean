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

/-- Checked nominal proof certificate identified upstream as `g_ltfintri`. -/
@[expose]
noncomputable def gLtfintri (M : Class) (N : Class) :
    Nominal.NPrf
      (.imp (synW3a (.classMem M (synCnnc)) (.classMem N (synCnnc)) (synWne M (synC0)))
        (synW3o (.classMem (synCopk M N) (synCltfin)) (.classEq M N)
          (.classMem (synCopk N M) (synCltfin)))) :=
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
  have p0000 := @gOpkeq2 (.cv n) N M
  have p0001 :=
    @gEleq1d (.classEq (.cv n) N) (synCopk M (.cv n)) (synCopk M N) (synCltfin) p0000
  have p0002 := @gEqeq2 (.cv n) N M
  have p0003 := @gOpkeq1 (.cv n) N M
  have p0004 :=
    @gEleq1d (.classEq (.cv n) N) (synCopk (.cv n) M) (synCopk N M) (synCltfin) p0003
  have p0005 :=
    @gN3orbi123d (.classEq (.cv n) N) (.classMem (synCopk M (.cv n)) (synCltfin))
      (.classMem (synCopk M N) (synCltfin)) (.classEq M (.cv n)) (.classEq M N)
      (.classMem (synCopk (.cv n) M) (synCltfin))
      (.classMem (synCopk N M) (synCltfin)) p0001 p0002 p0004
  have p0006 :=
    @gImbi2d (.classEq (.cv n) N)
      (synW3o (.classMem (synCopk M (.cv n)) (synCltfin)) (.classEq M (.cv n))
        (.classMem (synCopk (.cv n) M) (synCltfin)))
      (synW3o (.classMem (synCopk M N) (synCltfin)) (.classEq M N)
        (.classMem (synCopk N M) (synCltfin)))
      (synWne M (synC0)) p0005
  have p0007 :=
    @gImbi2d (.classEq (.cv n) N)
      (.imp (synWne M (synC0))
        (synW3o (.classMem (synCopk M (.cv n)) (synCltfin)) (.classEq M (.cv n))
          (.classMem (synCopk (.cv n) M) (synCltfin))))
      (.imp (synWne M (synC0)) (synW3o (.classMem (synCopk M N) (synCltfin)) (.classEq M N)
          (.classMem (synCopk N M) (synCltfin))))
      (.classMem M (synCnnc)) p0006
  have p0008 := @gLtfintrilem1 k n (show k ≠ n from (by exact fresh_k_ne_n))
  have p0009 := @gNeeq1 (.cv k) (synC0c) (synC0)
  have p0010 := @gOpkeq1 (.cv k) (synC0c) (.cv n)
  have p0011 :=
    @gEleq1d (.classEq (.cv k) (synC0c)) (synCopk (.cv k) (.cv n))
      (synCopk (synC0c) (.cv n)) (synCltfin) p0010
  have p0012 := @gEqeq1 (.cv k) (synC0c) (.cv n)
  have p0013 := @gOpkeq2 (.cv k) (synC0c) (.cv n)
  have p0014 :=
    @gEleq1d (.classEq (.cv k) (synC0c)) (synCopk (.cv n) (.cv k))
      (synCopk (.cv n) (synC0c)) (synCltfin) p0013
  have p0015_e01_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv k) (synC0c)) (synWb (.objEq k n) (.classEq (synC0c) (.cv n)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synC0c synCsn synC0 synCdif synCin synCcompl synCnin synWnan synWa
          synCvv synWb
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
    @gN3orbi123d (.classEq (.cv k) (synC0c))
      (.classMem (synCopk (.cv k) (.cv n)) (synCltfin))
      (.classMem (synCopk (synC0c) (.cv n)) (synCltfin)) (.objEq k n)
      (.classEq (synC0c) (.cv n)) (.classMem (synCopk (.cv n) (.cv k)) (synCltfin))
      (.classMem (synCopk (.cv n) (synC0c)) (synCltfin)) p0011 p0015_e01_recanon p0014
  have p0016 :=
    @gImbi12d (.classEq (.cv k) (synC0c)) (synWne (.cv k) (synC0))
      (synWne (synC0c) (synC0))
      (synW3o (.classMem (synCopk (.cv k) (.cv n)) (synCltfin)) (.objEq k n)
        (.classMem (synCopk (.cv n) (.cv k)) (synCltfin)))
      (synW3o (.classMem (synCopk (synC0c) (.cv n)) (synCltfin))
        (.classEq (synC0c) (.cv n)) (.classMem (synCopk (.cv n) (synC0c)) (synCltfin)))
      p0009 p0015
  have p0017 :=
    @gImbi2d (.classEq (.cv k) (synC0c))
      (.imp (synWne (.cv k) (synC0))
        (synW3o (.classMem (synCopk (.cv k) (.cv n)) (synCltfin)) (.objEq k n)
          (.classMem (synCopk (.cv n) (.cv k)) (synCltfin))))
      (.imp (synWne (synC0c) (synC0))
        (synW3o (.classMem (synCopk (synC0c) (.cv n)) (synCltfin))
          (.classEq (synC0c) (.cv n)) (.classMem (synCopk (.cv n) (synC0c)) (synCltfin))))
      (.classMem (.cv n) (synCnnc)) p0016
  have p0018 := @gNeeq1 (.cv k) (.cv m) (synC0)
  have p0019 := @gOpkeq1 (.cv k) (.cv m) (.cv n)
  have p0020_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq k m) (.classEq (synCopk (.cv k) (.cv n)) (synCopk (.cv m) (.cv n)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synCopk synCpr synCun synCnin synWnan synWa synCcompl synCsn
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0019
  have p0020 :=
    @gEleq1d (.objEq k m) (synCopk (.cv k) (.cv n)) (synCopk (.cv m) (.cv n))
      (synCltfin) p0020_e00_recanon
  have p0021 := @gEqeq1 (.cv k) (.cv m) (.cv n)
  have p0022 := @gOpkeq2 (.cv k) (.cv m) (.cv n)
  have p0023_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq k m) (.classEq (synCopk (.cv n) (.cv k)) (synCopk (.cv n) (.cv m)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synCopk synCpr synCun synCnin synWnan synWa synCcompl synCsn
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0022
  have p0023 :=
    @gEleq1d (.objEq k m) (synCopk (.cv n) (.cv k)) (synCopk (.cv n) (.cv m))
      (synCltfin) p0023_e00_recanon
  have p0024_e01_recanon :
    Nominal.NPrf (.imp (.objEq k m) (synWb (.objEq k n) (.objEq m n))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb
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
    @gN3orbi123d (.objEq k m) (.classMem (synCopk (.cv k) (.cv n)) (synCltfin))
      (.classMem (synCopk (.cv m) (.cv n)) (synCltfin)) (.objEq k n) (.objEq m n)
      (.classMem (synCopk (.cv n) (.cv k)) (synCltfin))
      (.classMem (synCopk (.cv n) (.cv m)) (synCltfin)) p0020 p0024_e01_recanon p0023
  have p0025_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq k m) (synWb (synWne (.cv k) (synC0)) (synWne (.cv m) (synC0)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWne synC0 synCdif synCin synCcompl synCnin synWnan synWa
          synCvv
        simp (config := { failIfUnchanged := false }) only []
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0018
  have p0025 :=
    @gImbi12d (.objEq k m) (synWne (.cv k) (synC0)) (synWne (.cv m) (synC0))
      (synW3o (.classMem (synCopk (.cv k) (.cv n)) (synCltfin)) (.objEq k n)
        (.classMem (synCopk (.cv n) (.cv k)) (synCltfin)))
      (synW3o (.classMem (synCopk (.cv m) (.cv n)) (synCltfin)) (.objEq m n)
        (.classMem (synCopk (.cv n) (.cv m)) (synCltfin)))
      p0025_e00_recanon p0024
  have p0026 :=
    @gImbi2d (.objEq k m)
      (.imp (synWne (.cv k) (synC0))
        (synW3o (.classMem (synCopk (.cv k) (.cv n)) (synCltfin)) (.objEq k n)
          (.classMem (synCopk (.cv n) (.cv k)) (synCltfin))))
      (.imp (synWne (.cv m) (synC0))
        (synW3o (.classMem (synCopk (.cv m) (.cv n)) (synCltfin)) (.objEq m n)
          (.classMem (synCopk (.cv n) (.cv m)) (synCltfin))))
      (.classMem (.cv n) (synCnnc)) p0025
  have p0027 := @gNeeq1 (.cv k) (synCplc (.cv m) (synC1c)) (synC0)
  have p0028 := @gOpkeq1 (.cv k) (synCplc (.cv m) (synC1c)) (.cv n)
  have p0029 :=
    @gEleq1d (.classEq (.cv k) (synCplc (.cv m) (synC1c))) (synCopk (.cv k) (.cv n))
      (synCopk (synCplc (.cv m) (synC1c)) (.cv n)) (synCltfin) p0028
  have p0030 := @gEqeq1 (.cv k) (synCplc (.cv m) (synC1c)) (.cv n)
  have p0031 := @gOpkeq2 (.cv k) (synCplc (.cv m) (synC1c)) (.cv n)
  have p0032 :=
    @gEleq1d (.classEq (.cv k) (synCplc (.cv m) (synC1c))) (synCopk (.cv n) (.cv k))
      (synCopk (.cv n) (synCplc (.cv m) (synC1c))) (synCltfin) p0031
  have p0033_e01_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv k) (synCplc (.cv m) (synC1c)))
        (synWb (.objEq k n) (.classEq (synCplc (.cv m) (synC1c)) (.cv n)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synCplc synWrex synWex synWa synC1c synWb
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
    @gN3orbi123d (.classEq (.cv k) (synCplc (.cv m) (synC1c)))
      (.classMem (synCopk (.cv k) (.cv n)) (synCltfin))
      (.classMem (synCopk (synCplc (.cv m) (synC1c)) (.cv n)) (synCltfin))
      (.objEq k n) (.classEq (synCplc (.cv m) (synC1c)) (.cv n))
      (.classMem (synCopk (.cv n) (.cv k)) (synCltfin))
      (.classMem (synCopk (.cv n) (synCplc (.cv m) (synC1c))) (synCltfin)) p0029
      p0033_e01_recanon p0032
  have p0034 :=
    @gImbi12d (.classEq (.cv k) (synCplc (.cv m) (synC1c))) (synWne (.cv k) (synC0))
      (synWne (synCplc (.cv m) (synC1c)) (synC0))
      (synW3o (.classMem (synCopk (.cv k) (.cv n)) (synCltfin)) (.objEq k n)
        (.classMem (synCopk (.cv n) (.cv k)) (synCltfin)))
      (synW3o (.classMem (synCopk (synCplc (.cv m) (synC1c)) (.cv n)) (synCltfin))
        (.classEq (synCplc (.cv m) (synC1c)) (.cv n))
        (.classMem (synCopk (.cv n) (synCplc (.cv m) (synC1c))) (synCltfin)))
      p0027 p0033
  have p0035 :=
    @gImbi2d (.classEq (.cv k) (synCplc (.cv m) (synC1c)))
      (.imp (synWne (.cv k) (synC0))
        (synW3o (.classMem (synCopk (.cv k) (.cv n)) (synCltfin)) (.objEq k n)
          (.classMem (synCopk (.cv n) (.cv k)) (synCltfin))))
      (.imp (synWne (synCplc (.cv m) (synC1c)) (synC0))
        (synW3o (.classMem (synCopk (synCplc (.cv m) (synC1c)) (.cv n)) (synCltfin))
          (.classEq (synCplc (.cv m) (synC1c)) (.cv n))
          (.classMem (synCopk (.cv n) (synCplc (.cv m) (synC1c))) (synCltfin))))
      (.classMem (.cv n) (synCnnc)) p0034
  have p0036 := @gNeeq1 (.cv k) M (synC0)
  have p0037 := @gOpkeq1 (.cv k) M (.cv n)
  have p0038 :=
    @gEleq1d (.classEq (.cv k) M) (synCopk (.cv k) (.cv n)) (synCopk M (.cv n))
      (synCltfin) p0037
  have p0039 := @gEqeq1 (.cv k) M (.cv n)
  have p0040 := @gOpkeq2 (.cv k) M (.cv n)
  have p0041 :=
    @gEleq1d (.classEq (.cv k) M) (synCopk (.cv n) (.cv k)) (synCopk (.cv n) M)
      (synCltfin) p0040
  have p0042_e01_recanon :
    Nominal.NPrf (.imp (.classEq (.cv k) M) (synWb (.objEq k n) (.classEq M (.cv n)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb
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
    @gN3orbi123d (.classEq (.cv k) M)
      (.classMem (synCopk (.cv k) (.cv n)) (synCltfin))
      (.classMem (synCopk M (.cv n)) (synCltfin)) (.objEq k n) (.classEq M (.cv n))
      (.classMem (synCopk (.cv n) (.cv k)) (synCltfin))
      (.classMem (synCopk (.cv n) M) (synCltfin)) p0038 p0042_e01_recanon p0041
  have p0043 :=
    @gImbi12d (.classEq (.cv k) M) (synWne (.cv k) (synC0)) (synWne M (synC0))
      (synW3o (.classMem (synCopk (.cv k) (.cv n)) (synCltfin)) (.objEq k n)
        (.classMem (synCopk (.cv n) (.cv k)) (synCltfin)))
      (synW3o (.classMem (synCopk M (.cv n)) (synCltfin)) (.classEq M (.cv n))
        (.classMem (synCopk (.cv n) M) (synCltfin)))
      p0036 p0042
  have p0044 :=
    @gImbi2d (.classEq (.cv k) M)
      (.imp (synWne (.cv k) (synC0))
        (synW3o (.classMem (synCopk (.cv k) (.cv n)) (synCltfin)) (.objEq k n)
          (.classMem (synCopk (.cv n) (.cv k)) (synCltfin))))
      (.imp (synWne M (synC0))
        (synW3o (.classMem (synCopk M (.cv n)) (synCltfin)) (.classEq M (.cv n))
          (.classMem (synCopk (.cv n) M) (synCltfin))))
      (.classMem (.cv n) (synCnnc)) p0043
  have p0045 := @gN0cminle (.cv n)
  have p0046 :=
    @gAdantr (.classMem (.cv n) (synCnnc))
      (.classMem (synCopk (synC0c) (.cv n)) (synClefin)) (synWne (synC0c) (synC0))
      p0045
  have p0047 := @gN0cex
  have p0048 := @gLefinlteq (synC0c) (.cv n) (synCvv) (synCnnc)
  have p0049 :=
    @gMp3an1 (.classMem (synC0c) (synCvv)) (.classMem (.cv n) (synCnnc))
      (synWne (synC0c) (synC0))
      (synWb (.classMem (synCopk (synC0c) (.cv n)) (synClefin))
        (synWo (.classMem (synCopk (synC0c) (.cv n)) (synCltfin))
          (.classEq (synC0c) (.cv n))))
      p0047 p0048
  have p0050 :=
    @gOrcom (.classMem (synCopk (synC0c) (.cv n)) (synCltfin))
      (.classEq (synC0c) (.cv n))
  have p0051 :=
    @gSyl6bb (synWa (.classMem (.cv n) (synCnnc)) (synWne (synC0c) (synC0)))
      (.classMem (synCopk (synC0c) (.cv n)) (synClefin))
      (synWo (.classMem (synCopk (synC0c) (.cv n)) (synCltfin))
        (.classEq (synC0c) (.cv n)))
      (synWo (.classEq (synC0c) (.cv n))
        (.classMem (synCopk (synC0c) (.cv n)) (synCltfin)))
      p0049 p0050
  have p0052 :=
    @gMpbid (synWa (.classMem (.cv n) (synCnnc)) (synWne (synC0c) (synC0)))
      (.classMem (synCopk (synC0c) (.cv n)) (synClefin))
      (synWo (.classEq (synC0c) (.cv n))
        (.classMem (synCopk (synC0c) (.cv n)) (synCltfin)))
      p0046 p0051
  have p0053 :=
    @gN3mix2 (.classEq (synC0c) (.cv n))
      (.classMem (synCopk (synC0c) (.cv n)) (synCltfin))
      (.classMem (synCopk (.cv n) (synC0c)) (synCltfin))
  have p0054 :=
    @gN3mix1 (.classMem (synCopk (synC0c) (.cv n)) (synCltfin))
      (.classEq (synC0c) (.cv n)) (.classMem (synCopk (.cv n) (synC0c)) (synCltfin))
  have p0055 :=
    @gJaoi (.classEq (synC0c) (.cv n))
      (synW3o (.classMem (synCopk (synC0c) (.cv n)) (synCltfin))
        (.classEq (synC0c) (.cv n)) (.classMem (synCopk (.cv n) (synC0c)) (synCltfin)))
      (.classMem (synCopk (synC0c) (.cv n)) (synCltfin)) p0053 p0054
  have p0056 :=
    @gSyl (synWa (.classMem (.cv n) (synCnnc)) (synWne (synC0c) (synC0)))
      (synWo (.classEq (synC0c) (.cv n))
        (.classMem (synCopk (synC0c) (.cv n)) (synCltfin)))
      (synW3o (.classMem (synCopk (synC0c) (.cv n)) (synCltfin))
        (.classEq (synC0c) (.cv n)) (.classMem (synCopk (.cv n) (synC0c)) (synCltfin)))
      p0052 p0055
  have p0057 :=
    @gEx (.classMem (.cv n) (synCnnc)) (synWne (synC0c) (synC0))
      (synW3o (.classMem (synCopk (synC0c) (.cv n)) (synCltfin))
        (.classEq (synC0c) (.cv n)) (.classMem (synCopk (.cv n) (synC0c)) (synCltfin)))
      p0056
  have p0058 := @gAddcnnul (.cv m) (synC1c)
  have p0059 :=
    @gSimpld (synWne (synCplc (.cv m) (synC1c)) (synC0)) (synWne (.cv m) (synC0))
      (synWne (synC1c) (synC0)) p0058
  have p0060 :=
    @gN3ad2ant3 (synWne (synCplc (.cv m) (synC1c)) (synC0))
      (.classMem (.cv m) (synCnnc)) (synWne (.cv m) (synC0))
      (.classMem (.cv n) (synCnnc)) p0059
  have p0061 := @gAddc32 (.cv m) (.cv p) (synC1c)
  have p0062 :=
    @gEqeq2i (synCplc (synCplc (.cv m) (.cv p)) (synC1c))
      (synCplc (synCplc (.cv m) (synC1c)) (.cv p)) (.cv n) p0061
  have p0063 :=
    @gRexbii (.classEq (.cv n) (synCplc (synCplc (.cv m) (.cv p)) (synC1c)))
      (.classEq (.cv n) (synCplc (synCplc (.cv m) (synC1c)) (.cv p))) p (synCnnc)
      p0062
  have p0064 :=
    @gBiimpi
      (synWrex p (synCnnc) (.classEq (.cv n) (synCplc (synCplc (.cv m) (.cv p)) (synC1c))))
      (synWrex p (synCnnc) (.classEq (.cv n) (synCplc (synCplc (.cv m) (synC1c)) (.cv p))))
      p0063
  have p0065 :=
    @gAdantl
      (synWrex p (synCnnc) (.classEq (.cv n) (synCplc (synCplc (.cv m) (.cv p)) (synC1c))))
      (synWrex p (synCnnc) (.classEq (.cv n) (synCplc (synCplc (.cv m) (synC1c)) (.cv p))))
      (synWne (.cv m) (synC0)) p0064
  have p0066 :=
    @gA1i
      (.imp (synWa (synWne (.cv m) (synC0)) (synWrex p (synCnnc)
            (.classEq (.cv n) (synCplc (synCplc (.cv m) (.cv p)) (synC1c)))))
        (synWrex p (synCnnc)
          (.classEq (.cv n) (synCplc (synCplc (.cv m) (synC1c)) (.cv p)))))
      (synW3a (.classMem (.cv m) (synCnnc)) (.classMem (.cv n) (synCnnc))
        (synWne (synCplc (.cv m) (synC1c)) (synC0)))
      p0065
  have freeVariableCertificate0 : p ∉ ((Class.cv m)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_p_ne_m, not_false_eq_true]
  have freeVariableCertificate1 : p ∉ ((Class.cv n)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_p_ne_n, not_false_eq_true]
  have p0067 :=
    @gOpkltfing p (.cv m) (.cv n) (synCnnc) (synCnnc) freeVariableCertificate0
      freeVariableCertificate1
  have p0068 :=
    @gN3adant3 (.classMem (.cv m) (synCnnc)) (.classMem (.cv n) (synCnnc))
      (synWb (.classMem (synCopk (.cv m) (.cv n)) (synCltfin))
        (synWa (synWne (.cv m) (synC0)) (synWrex p (synCnnc)
            (.classEq (.cv n) (synCplc (synCplc (.cv m) (.cv p)) (synC1c))))))
      (synWne (synCplc (.cv m) (synC1c)) (synC0)) p0067
  have p0069 :=
    @gSimp1 (.classMem (.cv m) (synCnnc)) (.classMem (.cv n) (synCnnc))
      (synWne (synCplc (.cv m) (synC1c)) (synC0))
  have p0070 := @gPeano2 (.cv m)
  have p0071 :=
    @gSyl
      (synW3a (.classMem (.cv m) (synCnnc)) (.classMem (.cv n) (synCnnc))
        (synWne (synCplc (.cv m) (synC1c)) (synC0)))
      (.classMem (.cv m) (synCnnc)) (.classMem (synCplc (.cv m) (synC1c)) (synCnnc))
      p0069 p0070
  have p0072 :=
    @gSimp2 (.classMem (.cv m) (synCnnc)) (.classMem (.cv n) (synCnnc))
      (synWne (synCplc (.cv m) (synC1c)) (synC0))
  have freeVariableCertificate2 : p ∉ ((synCplc (.cv m) (synC1c))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_p_ne_m, or_false,
      not_false_eq_true]
  have p0073 :=
    @gOpklefing p (synCplc (.cv m) (synC1c)) (.cv n) (synCnnc) (synCnnc)
      freeVariableCertificate2 freeVariableCertificate1
  have p0074 :=
    @gSyl2anc
      (synW3a (.classMem (.cv m) (synCnnc)) (.classMem (.cv n) (synCnnc))
        (synWne (synCplc (.cv m) (synC1c)) (synC0)))
      (.classMem (synCplc (.cv m) (synC1c)) (synCnnc)) (.classMem (.cv n) (synCnnc))
      (synWb (.classMem (synCopk (synCplc (.cv m) (synC1c)) (.cv n)) (synClefin))
        (synWrex p (synCnnc)
          (.classEq (.cv n) (synCplc (synCplc (.cv m) (synC1c)) (.cv p)))))
      p0071 p0072 p0073
  have p0075 :=
    @gN3imtr4d
      (synW3a (.classMem (.cv m) (synCnnc)) (.classMem (.cv n) (synCnnc))
        (synWne (synCplc (.cv m) (synC1c)) (synC0)))
      (synWa (synWne (.cv m) (synC0)) (synWrex p (synCnnc)
          (.classEq (.cv n) (synCplc (synCplc (.cv m) (.cv p)) (synC1c)))))
      (synWrex p (synCnnc) (.classEq (.cv n) (synCplc (synCplc (.cv m) (synC1c)) (.cv p))))
      (.classMem (synCopk (.cv m) (.cv n)) (synCltfin))
      (.classMem (synCopk (synCplc (.cv m) (synC1c)) (.cv n)) (synClefin)) p0066 p0068
      p0074
  have p0076 := @gLefinlteq (synCplc (.cv m) (synC1c)) (.cv n) (synCnnc) (synCnnc)
  have p0077 :=
    @gSyl3an1 (.classMem (.cv m) (synCnnc))
      (.classMem (synCplc (.cv m) (synC1c)) (synCnnc)) (.classMem (.cv n) (synCnnc))
      (synWne (synCplc (.cv m) (synC1c)) (synC0))
      (synWb (.classMem (synCopk (synCplc (.cv m) (synC1c)) (.cv n)) (synClefin))
        (synWo (.classMem (synCopk (synCplc (.cv m) (synC1c)) (.cv n)) (synCltfin))
          (.classEq (synCplc (.cv m) (synC1c)) (.cv n))))
      p0070 p0076
  have p0078 :=
    @gSylibd
      (synW3a (.classMem (.cv m) (synCnnc)) (.classMem (.cv n) (synCnnc))
        (synWne (synCplc (.cv m) (synC1c)) (synC0)))
      (.classMem (synCopk (.cv m) (.cv n)) (synCltfin))
      (.classMem (synCopk (synCplc (.cv m) (synC1c)) (.cv n)) (synClefin))
      (synWo (.classMem (synCopk (synCplc (.cv m) (synC1c)) (.cv n)) (synCltfin))
        (.classEq (synCplc (.cv m) (synC1c)) (.cv n)))
      p0075 p0077
  have p0079 :=
    @gN3mix1 (.classMem (synCopk (synCplc (.cv m) (synC1c)) (.cv n)) (synCltfin))
      (.classEq (synCplc (.cv m) (synC1c)) (.cv n))
      (.classMem (synCopk (.cv n) (synCplc (.cv m) (synC1c))) (synCltfin))
  have p0080 :=
    @gN3mix2 (.classEq (synCplc (.cv m) (synC1c)) (.cv n))
      (.classMem (synCopk (synCplc (.cv m) (synC1c)) (.cv n)) (synCltfin))
      (.classMem (synCopk (.cv n) (synCplc (.cv m) (synC1c))) (synCltfin))
  have p0081 :=
    @gJaoi (.classMem (synCopk (synCplc (.cv m) (synC1c)) (.cv n)) (synCltfin))
      (synW3o (.classMem (synCopk (synCplc (.cv m) (synC1c)) (.cv n)) (synCltfin))
        (.classEq (synCplc (.cv m) (synC1c)) (.cv n))
        (.classMem (synCopk (.cv n) (synCplc (.cv m) (synC1c))) (synCltfin)))
      (.classEq (synCplc (.cv m) (synC1c)) (.cv n)) p0079 p0080
  have p0082 :=
    @gSyl6
      (synW3a (.classMem (.cv m) (synCnnc)) (.classMem (.cv n) (synCnnc))
        (synWne (synCplc (.cv m) (synC1c)) (synC0)))
      (.classMem (synCopk (.cv m) (.cv n)) (synCltfin))
      (synWo (.classMem (synCopk (synCplc (.cv m) (synC1c)) (.cv n)) (synCltfin))
        (.classEq (synCplc (.cv m) (synC1c)) (.cv n)))
      (synW3o (.classMem (synCopk (synCplc (.cv m) (synC1c)) (.cv n)) (synCltfin))
        (.classEq (synCplc (.cv m) (synC1c)) (.cv n))
        (.classMem (synCopk (.cv n) (synCplc (.cv m) (synC1c))) (synCltfin)))
      p0078 p0081
  have p0083 := @gLtfinp1 (.cv m) (synCnnc)
  have p0084 :=
    @gSylan2 (synWne (synCplc (.cv m) (synC1c)) (synC0))
      (.classMem (.cv m) (synCnnc)) (synWne (.cv m) (synC0))
      (.classMem (synCopk (.cv m) (synCplc (.cv m) (synC1c))) (synCltfin)) p0059 p0083
  have p0085 :=
    @gN3adant2 (.classMem (.cv m) (synCnnc))
      (synWne (synCplc (.cv m) (synC1c)) (synC0))
      (.classMem (synCopk (.cv m) (synCplc (.cv m) (synC1c))) (synCltfin))
      (.classMem (.cv n) (synCnnc)) p0084
  have p0086 := @gOpkeq1 (.cv m) (.cv n) (synCplc (.cv m) (synC1c))
  have p0087_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq m n) (.classEq (synCopk (.cv m) (synCplc (.cv m) (synC1c)))
          (synCopk (.cv n) (synCplc (.cv m) (synC1c))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synCopk synCpr synCun synCnin synWnan synWa synCcompl synCsn
          synCplc synWrex synWex synC1c
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0086
  have p0087 :=
    @gEleq1d (.objEq m n) (synCopk (.cv m) (synCplc (.cv m) (synC1c)))
      (synCopk (.cv n) (synCplc (.cv m) (synC1c))) (synCltfin) p0087_e00_recanon
  have p0088 :=
    @gSyl5ibcom
      (synW3a (.classMem (.cv m) (synCnnc)) (.classMem (.cv n) (synCnnc))
        (synWne (synCplc (.cv m) (synC1c)) (synC0)))
      (.classMem (synCopk (.cv m) (synCplc (.cv m) (synC1c))) (synCltfin))
      (.objEq m n)
      (.classMem (synCopk (.cv n) (synCplc (.cv m) (synC1c))) (synCltfin)) p0085 p0087
  have p0089 :=
    @gN3mix3 (.classMem (synCopk (.cv n) (synCplc (.cv m) (synC1c))) (synCltfin))
      (.classMem (synCopk (synCplc (.cv m) (synC1c)) (.cv n)) (synCltfin))
      (.classEq (synCplc (.cv m) (synC1c)) (.cv n))
  have p0090 :=
    @gSyl6
      (synW3a (.classMem (.cv m) (synCnnc)) (.classMem (.cv n) (synCnnc))
        (synWne (synCplc (.cv m) (synC1c)) (synC0)))
      (.objEq m n)
      (.classMem (synCopk (.cv n) (synCplc (.cv m) (synC1c))) (synCltfin))
      (synW3o (.classMem (synCopk (synCplc (.cv m) (synC1c)) (.cv n)) (synCltfin))
        (.classEq (synCplc (.cv m) (synC1c)) (.cv n))
        (.classMem (synCopk (.cv n) (synCplc (.cv m) (synC1c))) (synCltfin)))
      p0088 p0089
  have p0091 := @gLtfintr (.cv n) (.cv m) (synCplc (.cv m) (synC1c))
  have p0092 :=
    @gSyl3anc
      (synW3a (.classMem (.cv m) (synCnnc)) (.classMem (.cv n) (synCnnc))
        (synWne (synCplc (.cv m) (synC1c)) (synC0)))
      (.classMem (.cv n) (synCnnc)) (.classMem (.cv m) (synCnnc))
      (.classMem (synCplc (.cv m) (synC1c)) (synCnnc))
      (.imp (synWa (.classMem (synCopk (.cv n) (.cv m)) (synCltfin))
          (.classMem (synCopk (.cv m) (synCplc (.cv m) (synC1c))) (synCltfin)))
        (.classMem (synCopk (.cv n) (synCplc (.cv m) (synC1c))) (synCltfin)))
      p0072 p0069 p0071 p0091
  have p0093 :=
    @gMpan2d
      (synW3a (.classMem (.cv m) (synCnnc)) (.classMem (.cv n) (synCnnc))
        (synWne (synCplc (.cv m) (synC1c)) (synC0)))
      (.classMem (synCopk (.cv n) (.cv m)) (synCltfin))
      (.classMem (synCopk (.cv m) (synCplc (.cv m) (synC1c))) (synCltfin))
      (.classMem (synCopk (.cv n) (synCplc (.cv m) (synC1c))) (synCltfin)) p0085 p0092
  have p0094 :=
    @gSyl6
      (synW3a (.classMem (.cv m) (synCnnc)) (.classMem (.cv n) (synCnnc))
        (synWne (synCplc (.cv m) (synC1c)) (synC0)))
      (.classMem (synCopk (.cv n) (.cv m)) (synCltfin))
      (.classMem (synCopk (.cv n) (synCplc (.cv m) (synC1c))) (synCltfin))
      (synW3o (.classMem (synCopk (synCplc (.cv m) (synC1c)) (.cv n)) (synCltfin))
        (.classEq (synCplc (.cv m) (synC1c)) (.cv n))
        (.classMem (synCopk (.cv n) (synCplc (.cv m) (synC1c))) (synCltfin)))
      p0093 p0089
  have p0095 :=
    @gN3jaod
      (synW3a (.classMem (.cv m) (synCnnc)) (.classMem (.cv n) (synCnnc))
        (synWne (synCplc (.cv m) (synC1c)) (synC0)))
      (.classMem (synCopk (.cv m) (.cv n)) (synCltfin))
      (synW3o (.classMem (synCopk (synCplc (.cv m) (synC1c)) (.cv n)) (synCltfin))
        (.classEq (synCplc (.cv m) (synC1c)) (.cv n))
        (.classMem (synCopk (.cv n) (synCplc (.cv m) (synC1c))) (synCltfin)))
      (.objEq m n) (.classMem (synCopk (.cv n) (.cv m)) (synCltfin)) p0082 p0090 p0094
  have p0096 :=
    @gEmbantd
      (synW3a (.classMem (.cv m) (synCnnc)) (.classMem (.cv n) (synCnnc))
        (synWne (synCplc (.cv m) (synC1c)) (synC0)))
      (synWne (.cv m) (synC0))
      (synW3o (.classMem (synCopk (.cv m) (.cv n)) (synCltfin)) (.objEq m n)
        (.classMem (synCopk (.cv n) (.cv m)) (synCltfin)))
      (synW3o (.classMem (synCopk (synCplc (.cv m) (synC1c)) (.cv n)) (synCltfin))
        (.classEq (synCplc (.cv m) (synC1c)) (.cv n))
        (.classMem (synCopk (.cv n) (synCplc (.cv m) (synC1c))) (synCltfin)))
      p0060 p0095
  have p0097 :=
    @gN3expia (.classMem (.cv m) (synCnnc)) (.classMem (.cv n) (synCnnc))
      (synWne (synCplc (.cv m) (synC1c)) (synC0))
      (.imp (.imp (synWne (.cv m) (synC0))
          (synW3o (.classMem (synCopk (.cv m) (.cv n)) (synCltfin)) (.objEq m n)
            (.classMem (synCopk (.cv n) (.cv m)) (synCltfin))))
        (synW3o (.classMem (synCopk (synCplc (.cv m) (synC1c)) (.cv n)) (synCltfin))
          (.classEq (synCplc (.cv m) (synC1c)) (.cv n))
          (.classMem (synCopk (.cv n) (synCplc (.cv m) (synC1c))) (synCltfin))))
      p0096
  have p0098 :=
    @gCom23 (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv n) (synCnnc)))
      (synWne (synCplc (.cv m) (synC1c)) (synC0))
      (.imp (synWne (.cv m) (synC0))
        (synW3o (.classMem (synCopk (.cv m) (.cv n)) (synCltfin)) (.objEq m n)
          (.classMem (synCopk (.cv n) (.cv m)) (synCltfin))))
      (synW3o (.classMem (synCopk (synCplc (.cv m) (synC1c)) (.cv n)) (synCltfin))
        (.classEq (synCplc (.cv m) (synC1c)) (.cv n))
        (.classMem (synCopk (.cv n) (synCplc (.cv m) (synC1c))) (synCltfin)))
      p0097
  have p0099 :=
    @gEx (.classMem (.cv m) (synCnnc)) (.classMem (.cv n) (synCnnc))
      (.imp (.imp (synWne (.cv m) (synC0))
          (synW3o (.classMem (synCopk (.cv m) (.cv n)) (synCltfin)) (.objEq m n)
            (.classMem (synCopk (.cv n) (.cv m)) (synCltfin))))
        (.imp (synWne (synCplc (.cv m) (synC1c)) (synC0)) (synW3o
            (.classMem (synCopk (synCplc (.cv m) (synC1c)) (.cv n)) (synCltfin))
            (.classEq (synCplc (.cv m) (synC1c)) (.cv n))
            (.classMem (synCopk (.cv n) (synCplc (.cv m) (synC1c))) (synCltfin)))))
      p0098
  have p0100 :=
    @gA2d (.classMem (.cv m) (synCnnc)) (.classMem (.cv n) (synCnnc))
      (.imp (synWne (.cv m) (synC0))
        (synW3o (.classMem (synCopk (.cv m) (.cv n)) (synCltfin)) (.objEq m n)
          (.classMem (synCopk (.cv n) (.cv m)) (synCltfin))))
      (.imp (synWne (synCplc (.cv m) (synC1c)) (synC0))
        (synW3o (.classMem (synCopk (synCplc (.cv m) (synC1c)) (.cv n)) (synCltfin))
          (.classEq (synCplc (.cv m) (synC1c)) (.cv n))
          (.classMem (synCopk (.cv n) (synCplc (.cv m) (synC1c))) (synCltfin))))
      p0099
  have freeVariableCertificate3 :
    k ∉
      ((Wff.imp (.classMem (.cv n) (synCnnc)) (.imp (synWne (.cv m) (synC0))
            (synW3o (.classMem (synCopk (.cv m) (.cv n)) (synCltfin)) (.objEq m n)
              (.classMem (synCopk (.cv n) (.cv m)) (synCltfin)))))).fv :=
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
      ((Wff.imp (.classMem (.cv n) (synCnnc)) (.imp (synWne (.cv k) (synC0))
            (synW3o (.classMem (synCopk (.cv k) (.cv n)) (synCltfin)) (.objEq k n)
              (.classMem (synCopk (.cv n) (.cv k)) (synCltfin)))))).fv :=
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
      ((Wff.imp (.classMem (.cv n) (synCnnc)) (.imp (synWne (synC0c) (synC0))
            (synW3o (.classMem (synCopk (synC0c) (.cv n)) (synCltfin))
              (.classEq (synC0c) (.cv n))
              (.classMem (synCopk (.cv n) (synC0c)) (synCltfin)))))).fv :=
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
      ((Wff.imp (.classMem (.cv n) (synCnnc)) (.imp (synWne M (synC0))
            (synW3o (.classMem (synCopk M (.cv n)) (synCltfin)) (.classEq M (.cv n))
              (.classMem (synCopk (.cv n) M) (synCltfin)))))).fv :=
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
      ((Wff.imp (.classMem (.cv n) (synCnnc))
          (.imp (synWne (synCplc (.cv m) (synC1c)) (synC0)) (synW3o
              (.classMem (synCopk (synCplc (.cv m) (synC1c)) (.cv n)) (synCltfin))
              (.classEq (synCplc (.cv m) (synC1c)) (.cv n))
              (.classMem (synCopk (.cv n) (synCplc (.cv m) (synC1c))) (synCltfin)))))).fv :=
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
    @gFinds
      (.imp (.classMem (.cv n) (synCnnc)) (.imp (synWne (.cv k) (synC0))
          (synW3o (.classMem (synCopk (.cv k) (.cv n)) (synCltfin)) (.objEq k n)
            (.classMem (synCopk (.cv n) (.cv k)) (synCltfin)))))
      (.imp (.classMem (.cv n) (synCnnc)) (.imp (synWne (synC0c) (synC0))
          (synW3o (.classMem (synCopk (synC0c) (.cv n)) (synCltfin))
            (.classEq (synC0c) (.cv n))
            (.classMem (synCopk (.cv n) (synC0c)) (synCltfin)))))
      (.imp (.classMem (.cv n) (synCnnc)) (.imp (synWne (.cv m) (synC0))
          (synW3o (.classMem (synCopk (.cv m) (.cv n)) (synCltfin)) (.objEq m n)
            (.classMem (synCopk (.cv n) (.cv m)) (synCltfin)))))
      (.imp (.classMem (.cv n) (synCnnc)) (.imp (synWne (synCplc (.cv m) (synC1c)) (synC0))
          (synW3o (.classMem (synCopk (synCplc (.cv m) (synC1c)) (.cv n)) (synCltfin))
            (.classEq (synCplc (.cv m) (synC1c)) (.cv n))
            (.classMem (synCopk (.cv n) (synCplc (.cv m) (synC1c))) (synCltfin)))))
      (.imp (.classMem (.cv n) (synCnnc)) (.imp (synWne M (synC0))
          (synW3o (.classMem (synCopk M (.cv n)) (synCltfin)) (.classEq M (.cv n))
            (.classMem (synCopk (.cv n) M) (synCltfin)))))
      k m M (by exact (show k ∉ (M).fv from (by exact fresh_k_not_M)))
      freeVariableCertificate3 freeVariableCertificate4 freeVariableCertificate5
      freeVariableCertificate6 freeVariableCertificate7
      (show k ≠ m from (by exact fresh_k_ne_m)) p0008 p0017 p0026 p0035 p0044 p0057 p0100
  have p0102 :=
    @gCom12 (.classMem M (synCnnc)) (.classMem (.cv n) (synCnnc))
      (.imp (synWne M (synC0))
        (synW3o (.classMem (synCopk M (.cv n)) (synCltfin)) (.classEq M (.cv n))
          (.classMem (synCopk (.cv n) M) (synCltfin))))
      p0101
  have freeVariableCertificate8 :
    n ∉
      ((Wff.imp (.classMem M (synCnnc)) (.imp (synWne M (synC0))
            (synW3o (.classMem (synCopk M N) (synCltfin)) (.classEq M N)
              (.classMem (synCopk N M) (synCltfin)))))).fv :=
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
    @gVtoclga
      (.imp (.classMem M (synCnnc)) (.imp (synWne M (synC0))
          (synW3o (.classMem (synCopk M (.cv n)) (synCltfin)) (.classEq M (.cv n))
            (.classMem (synCopk (.cv n) M) (synCltfin)))))
      (.imp (.classMem M (synCnnc)) (.imp (synWne M (synC0))
          (synW3o (.classMem (synCopk M N) (synCltfin)) (.classEq M N)
            (.classMem (synCopk N M) (synCltfin)))))
      n N (synCnnc) (by exact (show n ∉ (N).fv from (by exact fresh_n_not_N)))
      (by
        exact
          (show n ∉ ((synCnnc)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc];
              exact (show n ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
      freeVariableCertificate8 p0007 p0102
  have p0104 :=
    @gCom12 (.classMem N (synCnnc)) (.classMem M (synCnnc))
      (.imp (synWne M (synC0)) (synW3o (.classMem (synCopk M N) (synCltfin)) (.classEq M N)
          (.classMem (synCopk N M) (synCltfin))))
      p0103
  have p0105 :=
    @gN3imp (.classMem M (synCnnc)) (.classMem N (synCnnc)) (synWne M (synC0))
      (synW3o (.classMem (synCopk M N) (synCltfin)) (.classEq M N)
        (.classMem (synCopk N M) (synCltfin)))
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

/-- Checked nominal proof certificate identified upstream as `g_lefinrflx`. -/
@[expose]
noncomputable def gLefinrflx (A : Class) (V : Class) :
    Nominal.NPrf (.imp (.classMem A V) (.classMem (synCopk A A) (synClefin))) :=
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
  have p0000 := @gPeano1
  have p0001 := @gAddcid1 A
  have p0002 := @gEqcomi (synCplc A (synC0c)) A p0001
  have p0003 := @gAddceq2 (.cv x) (synC0c) A
  have p0004 :=
    @gEqeq2d (.classEq (.cv x) (synC0c)) (synCplc A (.cv x)) (synCplc A (synC0c)) A
      p0003
  have freeVariableCertificate0 : x ∉ ((Wff.classEq A (synCplc A (synC0c)))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union,
      Finset.notMem_empty, fresh_x_not_A, or_false, not_false_eq_true]
  have p0005 :=
    @gRspcev (.classEq A (synCplc A (.cv x))) (.classEq A (synCplc A (synC0c))) x
      (synC0c) (synCnnc)
      (by
        exact
          (show x ∉ ((synC0c)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c];
              exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
      (by
        exact
          (show x ∉ ((synCnnc)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc];
              exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
      freeVariableCertificate0 p0004
  have p0006 :=
    @gMp2an (.classMem (synC0c) (synCnnc)) (.classEq A (synCplc A (synC0c)))
      (synWrex x (synCnnc) (.classEq A (synCplc A (.cv x)))) p0000 p0002 p0005
  have p0007 :=
    @gOpklefing x A A V V (by exact (show x ∉ (A).fv from (by exact fresh_x_not_A)))
      (by exact (show x ∉ (A).fv from (by exact fresh_x_not_A)))
  have p0008 :=
    @gAnidms (.classMem A V)
      (synWb (.classMem (synCopk A A) (synClefin))
        (synWrex x (synCnnc) (.classEq A (synCplc A (.cv x)))))
      p0007
  have p0009 :=
    @gMpbiri (.classMem A V) (.classMem (synCopk A A) (synClefin))
      (synWrex x (synCnnc) (.classEq A (synCplc A (.cv x)))) p0006 p0008
  exact p0009

/-- Checked nominal proof certificate identified upstream as `g_ltlefin`. -/
@[expose]
noncomputable def gLtlefin (A : Class) (B : Class) (V : Class) (W : Class) :
    Nominal.NPrf
      (.imp (synWa (.classMem A V) (.classMem B W))
        (.imp (.classMem (synCopk A B) (synCltfin))
          (.classMem (synCopk A B) (synClefin)))) :=
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
  have p0000 := @gAddcass A (.cv x) (synC1c)
  have p0001 :=
    @gEqeq2i (synCplc (synCplc A (.cv x)) (synC1c))
      (synCplc A (synCplc (.cv x) (synC1c))) B p0000
  have p0002 := @gPeano2 (.cv x)
  have p0003 := @gAddceq2 (.cv y) (synCplc (.cv x) (synC1c)) A
  have p0004 :=
    @gEqeq2d (.classEq (.cv y) (synCplc (.cv x) (synC1c))) (synCplc A (.cv y))
      (synCplc A (synCplc (.cv x) (synC1c))) B p0003
  have freeVariableCertificate0 : y ∉ ((synCplc (.cv x) (synC1c))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_y_ne_x, or_false,
      not_false_eq_true]
  have freeVariableCertificate1 :
    y ∉ ((Wff.classEq B (synCplc A (synCplc (.cv x) (synC1c))))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_y_not_B, fresh_y_not_A,
      fresh_y_ne_x, or_false, not_false_eq_true]
  have p0005 :=
    @gRspcev (.classEq B (synCplc A (.cv y)))
      (.classEq B (synCplc A (synCplc (.cv x) (synC1c)))) y
      (synCplc (.cv x) (synC1c)) (synCnnc) freeVariableCertificate0
      (by
        exact
          (show y ∉ ((synCnnc)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc];
              exact (show y ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
      freeVariableCertificate1 p0004
  have p0006 :=
    @gSylan (.classMem (.cv x) (synCnnc))
      (.classMem (synCplc (.cv x) (synC1c)) (synCnnc))
      (.classEq B (synCplc A (synCplc (.cv x) (synC1c))))
      (synWrex y (synCnnc) (.classEq B (synCplc A (.cv y)))) p0002 p0005
  have p0007 :=
    @gSylan2b (.classEq B (synCplc (synCplc A (.cv x)) (synC1c)))
      (.classMem (.cv x) (synCnnc))
      (.classEq B (synCplc A (synCplc (.cv x) (synC1c))))
      (synWrex y (synCnnc) (.classEq B (synCplc A (.cv y)))) p0001 p0006
  have freeVariableCertificate2 :
    x ∉ ((synWrex y (synCnnc) (.classEq B (synCplc A (.cv y))))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
      Finset.mem_singleton, Finset.notMem_empty, fresh_x_not_B, fresh_x_not_A,
      fresh_x_ne_y, or_false, and_false, not_false_eq_true]
  have p0008 :=
    @gRexlimiva (.classEq B (synCplc (synCplc A (.cv x)) (synC1c)))
      (synWrex y (synCnnc) (.classEq B (synCplc A (.cv y)))) x (synCnnc)
      freeVariableCertificate2 p0007
  have p0009 :=
    @gAdantl
      (synWrex x (synCnnc) (.classEq B (synCplc (synCplc A (.cv x)) (synC1c))))
      (synWrex y (synCnnc) (.classEq B (synCplc A (.cv y)))) (synWne A (synC0)) p0008
  have p0010 :=
    @gA1i
      (.imp (synWa (synWne A (synC0))
          (synWrex x (synCnnc) (.classEq B (synCplc (synCplc A (.cv x)) (synC1c)))))
        (synWrex y (synCnnc) (.classEq B (synCplc A (.cv y)))))
      (synWa (.classMem A V) (.classMem B W)) p0009
  have p0011 :=
    @gOpkltfing x A B V W (by exact (show x ∉ (A).fv from (by exact fresh_x_not_A)))
      (by exact (show x ∉ (B).fv from (by exact fresh_x_not_B)))
  have p0012 :=
    @gOpklefing y A B V W (by exact (show y ∉ (A).fv from (by exact fresh_y_not_A)))
      (by exact (show y ∉ (B).fv from (by exact fresh_y_not_B)))
  have p0013 :=
    @gN3imtr4d (synWa (.classMem A V) (.classMem B W))
      (synWa (synWne A (synC0))
        (synWrex x (synCnnc) (.classEq B (synCplc (synCplc A (.cv x)) (synC1c)))))
      (synWrex y (synCnnc) (.classEq B (synCplc A (.cv y))))
      (.classMem (synCopk A B) (synCltfin)) (.classMem (synCopk A B) (synClefin))
      p0010 p0011 p0012
  exact p0013

/-- Checked nominal proof certificate identified upstream as `g_lenltfin`. -/
@[expose]
noncomputable def gLenltfin (A : Class) (B : Class) :
    Nominal.NPrf
      (.imp (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
        (synWb (.classMem (synCopk A B) (synClefin))
          (.neg (.classMem (synCopk B A) (synCltfin))))) :=
  by
  have p0000 := @gLtfinirr A
  have p0001 :=
    @gAdantr (.classMem A (synCnnc)) (.neg (.classMem (synCopk A A) (synCltfin)))
      (.classMem B (synCnnc)) p0000
  have p0002 :=
    @gAdantr (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
      (.neg (.classMem (synCopk A A) (synCltfin)))
      (.classMem (synCopk A B) (synClefin)) p0001
  have p0003 := @gLeltfintr A B A
  have p0004 :=
    @gN3anidm13 (.classMem A (synCnnc)) (.classMem B (synCnnc))
      (.imp (synWa (.classMem (synCopk A B) (synClefin))
          (.classMem (synCopk B A) (synCltfin))) (.classMem (synCopk A A) (synCltfin)))
      p0003
  have p0005 :=
    @gExpdimp (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
      (.classMem (synCopk A B) (synClefin)) (.classMem (synCopk B A) (synCltfin))
      (.classMem (synCopk A A) (synCltfin)) p0004
  have p0006 :=
    @gMtod
      (synWa (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
        (.classMem (synCopk A B) (synClefin)))
      (.classMem (synCopk B A) (synCltfin)) (.classMem (synCopk A A) (synCltfin))
      p0002 p0005
  have p0007 :=
    @gEx (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
      (.classMem (synCopk A B) (synClefin))
      (.neg (.classMem (synCopk B A) (synCltfin))) p0006
  have p0008 := @gNulge A (synCnnc)
  have p0009 :=
    @gAncoms (.classMem (synC0) (synCnnc)) (.classMem A (synCnnc))
      (.classMem (synCopk A (synC0)) (synClefin)) p0008
  have p0010 := @gEleq1 B (synC0) (synCnnc)
  have p0011 :=
    @gAnbi2d (.classEq B (synC0)) (.classMem B (synCnnc))
      (.classMem (synC0) (synCnnc)) (.classMem A (synCnnc)) p0010
  have p0012 := @gOpkeq2 B (synC0) A
  have p0013 :=
    @gEleq1d (.classEq B (synC0)) (synCopk A B) (synCopk A (synC0)) (synClefin)
      p0012
  have p0014 :=
    @gImbi12d (.classEq B (synC0))
      (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
      (synWa (.classMem A (synCnnc)) (.classMem (synC0) (synCnnc)))
      (.classMem (synCopk A B) (synClefin))
      (.classMem (synCopk A (synC0)) (synClefin)) p0011 p0013
  have p0015 :=
    @gMpbiri (.classEq B (synC0))
      (.imp (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
        (.classMem (synCopk A B) (synClefin)))
      (.imp (synWa (.classMem A (synCnnc)) (.classMem (synC0) (synCnnc)))
        (.classMem (synCopk A (synC0)) (synClefin)))
      p0009 p0014
  have p0016 :=
    @gA1dd (.classEq B (synC0))
      (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
      (.classMem (synCopk A B) (synClefin))
      (.neg (.classMem (synCopk B A) (synCltfin))) p0015
  have p0017 :=
    @gSimplr (.classMem A (synCnnc)) (.classMem B (synCnnc)) (synWne B (synC0))
  have p0018 :=
    @gSimpll (.classMem A (synCnnc)) (.classMem B (synCnnc)) (synWne B (synC0))
  have p0019 :=
    @gSimpr (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
      (synWne B (synC0))
  have p0020 := @gLtfintri B A
  have p0021 :=
    @gSyl3anc
      (synWa (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc))) (synWne B (synC0)))
      (.classMem B (synCnnc)) (.classMem A (synCnnc)) (synWne B (synC0))
      (synW3o (.classMem (synCopk B A) (synCltfin)) (.classEq B A)
        (.classMem (synCopk A B) (synCltfin)))
      p0017 p0018 p0019 p0020
  have p0022 :=
    @gN3orass (.classMem (synCopk B A) (synCltfin)) (.classEq B A)
      (.classMem (synCopk A B) (synCltfin))
  have p0023 :=
    @gSylib
      (synWa (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc))) (synWne B (synC0)))
      (synW3o (.classMem (synCopk B A) (synCltfin)) (.classEq B A)
        (.classMem (synCopk A B) (synCltfin)))
      (synWo (.classMem (synCopk B A) (synCltfin))
        (synWo (.classEq B A) (.classMem (synCopk A B) (synCltfin))))
      p0021 p0022
  have p0024 :=
    @gOrd
      (synWa (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc))) (synWne B (synC0)))
      (.classMem (synCopk B A) (synCltfin))
      (synWo (.classEq B A) (.classMem (synCopk A B) (synCltfin))) p0023
  have p0025 := @gLefinrflx A (synCnnc)
  have p0026 :=
    @gAdantr (.classMem A (synCnnc)) (.classMem (synCopk A A) (synClefin))
      (.classMem B (synCnnc)) p0025
  have p0027 := @gOpkeq2 B A A
  have p0028 := @gEleq1d (.classEq B A) (synCopk A B) (synCopk A A) (synClefin) p0027
  have p0029 :=
    @gSyl5ibrcom (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
      (.classMem (synCopk A B) (synClefin)) (.classEq B A)
      (.classMem (synCopk A A) (synClefin)) p0026 p0028
  have p0030 :=
    @gAdantr (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
      (.imp (.classEq B A) (.classMem (synCopk A B) (synClefin))) (synWne B (synC0))
      p0029
  have p0031 := @gLtlefin A B (synCnnc) (synCnnc)
  have p0032 :=
    @gAdantr (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
      (.imp (.classMem (synCopk A B) (synCltfin)) (.classMem (synCopk A B) (synClefin)))
      (synWne B (synC0)) p0031
  have p0033 :=
    @gJaod
      (synWa (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc))) (synWne B (synC0)))
      (.classEq B A) (.classMem (synCopk A B) (synClefin))
      (.classMem (synCopk A B) (synCltfin)) p0030 p0032
  have p0034 :=
    @gSyld
      (synWa (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc))) (synWne B (synC0)))
      (.neg (.classMem (synCopk B A) (synCltfin)))
      (synWo (.classEq B A) (.classMem (synCopk A B) (synCltfin)))
      (.classMem (synCopk A B) (synClefin)) p0024 p0033
  have p0035 :=
    @gExpcom (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
      (synWne B (synC0))
      (.imp (.neg (.classMem (synCopk B A) (synCltfin)))
        (.classMem (synCopk A B) (synClefin)))
      p0034
  have p0036 :=
    @gPm261ine
      (.imp (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
        (.imp (.neg (.classMem (synCopk B A) (synCltfin)))
          (.classMem (synCopk A B) (synClefin))))
      B (synC0) p0016 p0035
  have p0037 :=
    @gImpbid (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
      (.classMem (synCopk A B) (synClefin))
      (.neg (.classMem (synCopk B A) (synCltfin))) p0007 p0036
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

/-- Checked nominal proof certificate identified upstream as `g_ssfin`. -/
@[expose]
noncomputable def gSsfin (A : Class) (B : Class) (V : Class) :
    Nominal.NPrf
      (.imp (synW3a (.classMem A V) (.classMem B (synCfin)) (synWss A B))
        (.classMem A (synCfin))) :=
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
  have p0000 := @gSseq1 (.cv a) A B
  have p0001 := @gEleq1 (.cv a) A (synCfin)
  have p0002 :=
    @gImbi12d (.classEq (.cv a) A) (synWss (.cv a) B) (synWss A B)
      (.classMem (.cv a) (synCfin)) (.classMem A (synCfin)) p0000 p0001
  have p0003 :=
    @gImbi2d (.classEq (.cv a) A)
      (.imp (synWss (.cv a) B) (.classMem (.cv a) (synCfin)))
      (.imp (synWss A B) (.classMem A (synCfin))) (.classMem B (synCfin)) p0002
  have p0004 := @gSseq2 (.cv b) B (.cv a)
  have p0005 :=
    @gImbi1d (.classEq (.cv b) B) (synWss (.cv a) (.cv b)) (synWss (.cv a) B)
      (.classMem (.cv a) (synCfin)) p0004
  have freeVariableCertificate0 : n ∉ ((Class.cv b)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_n_ne_b, not_false_eq_true]
  have p0006 := @gElfin n (.cv b) freeVariableCertificate0
  have p0007 := @gVex m
  have p0008 :=
    @gElcompl (.cv m)
      (synCimak (synCin (synCssetk)
          (synCxpk (synCpw1 (synCimak (synCssetk) (synCcompl (synCfin)))) (synCvv)))
        (synC1c))
      p0007
  have p0009 :=
    @gAlcom
      (.imp (synWa (.objMem b m) (synWss (.cv a) (.cv b))) (.classMem (.cv a) (synCfin)))
      a b
  have p0010 :=
    @gImpexp (.objMem b m) (synWss (.cv a) (.cv b)) (.classMem (.cv a) (synCfin))
  have p0011 :=
    @gAlbii
      (.imp (synWa (.objMem b m) (synWss (.cv a) (.cv b))) (.classMem (.cv a) (synCfin)))
      (.imp (.objMem b m) (.imp (synWss (.cv a) (.cv b)) (.classMem (.cv a) (synCfin))))
      a p0010
  have freeVariableCertificate1 : a ∉ ((Wff.objMem b m)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_objMem, Finset.mem_insert,
      Finset.mem_singleton, fresh_a_ne_b, fresh_a_ne_m, or_false, not_false_eq_true]
  have p0012 :=
    @gN1921v (.objMem b m)
      (.imp (synWss (.cv a) (.cv b)) (.classMem (.cv a) (synCfin))) a
      freeVariableCertificate1
  have p0013 :=
    @gBitri
      (.all a (.imp (synWa (.objMem b m) (synWss (.cv a) (.cv b)))
          (.classMem (.cv a) (synCfin))))
      (.all a (.imp (.objMem b m)
          (.imp (synWss (.cv a) (.cv b)) (.classMem (.cv a) (synCfin)))))
      (.imp (.objMem b m)
        (.all a (.imp (synWss (.cv a) (.cv b)) (.classMem (.cv a) (synCfin)))))
      p0011 p0012
  have p0014 :=
    @gAlbii
      (.all a (.imp (synWa (.objMem b m) (synWss (.cv a) (.cv b)))
          (.classMem (.cv a) (synCfin))))
      (.imp (.objMem b m)
        (.all a (.imp (synWss (.cv a) (.cv b)) (.classMem (.cv a) (synCfin)))))
      b p0013
  have freeVariableCertificate2 :
    t ∉
      ((synCin (synCssetk)
          (synCxpk (synCpw1 (synCimak (synCssetk) (synCcompl (synCfin))))
            (synCvv)))).fv :=
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
    @gElimak t
      (synCin (synCssetk)
        (synCxpk (synCpw1 (synCimak (synCssetk) (synCcompl (synCfin)))) (synCvv)))
      (synC1c) (.cv m) freeVariableCertificate2
      (by
        exact
          (show t ∉ ((synC1c)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c];
              exact (show t ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
      freeVariableCertificate3 p0007
  have p0016 :=
    (Nominal.biimpRefl (synWrex t (synC1c) (.classMem (synCopk (.cv t) (.cv m))
          (synCin (synCssetk)
            (synCxpk (synCpw1 (synCimak (synCssetk) (synCcompl (synCfin)))) (synCvv))))))
  have freeVariableCertificate4 : b ∉ ((Class.cv t)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_b_ne_t, not_false_eq_true]
  have p0017 := @gEl1c b (.cv t) freeVariableCertificate4
  have p0018 :=
    @gAnbi1i (.classMem (.cv t) (synC1c))
      (synWex b (.classEq (.cv t) (synCsn (.cv b))))
      (.classMem (synCopk (.cv t) (.cv m)) (synCin (synCssetk)
          (synCxpk (synCpw1 (synCimak (synCssetk) (synCcompl (synCfin)))) (synCvv))))
      p0017
  have freeVariableCertificate5 :
    b ∉
      ((Wff.classMem (synCopk (.cv t) (.cv m)) (synCin (synCssetk)
            (synCxpk (synCpw1 (synCimak (synCssetk) (synCcompl (synCfin))))
              (synCvv))))).fv :=
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
    @gN1941v (.classEq (.cv t) (synCsn (.cv b)))
      (.classMem (synCopk (.cv t) (.cv m)) (synCin (synCssetk)
          (synCxpk (synCpw1 (synCimak (synCssetk) (synCcompl (synCfin)))) (synCvv))))
      b freeVariableCertificate5
  have p0020 :=
    @gBitr4i
      (synWa (.classMem (.cv t) (synC1c)) (.classMem (synCopk (.cv t) (.cv m))
          (synCin (synCssetk)
            (synCxpk (synCpw1 (synCimak (synCssetk) (synCcompl (synCfin)))) (synCvv)))))
      (synWa (synWex b (.classEq (.cv t) (synCsn (.cv b))))
        (.classMem (synCopk (.cv t) (.cv m)) (synCin (synCssetk)
            (synCxpk (synCpw1 (synCimak (synCssetk) (synCcompl (synCfin)))) (synCvv)))))
      (synWex b (synWa (.classEq (.cv t) (synCsn (.cv b)))
          (.classMem (synCopk (.cv t) (.cv m)) (synCin (synCssetk)
              (synCxpk (synCpw1 (synCimak (synCssetk) (synCcompl (synCfin))))
                (synCvv))))))
      p0018 p0019
  have p0021 :=
    @gExbii
      (synWa (.classMem (.cv t) (synC1c)) (.classMem (synCopk (.cv t) (.cv m))
          (synCin (synCssetk)
            (synCxpk (synCpw1 (synCimak (synCssetk) (synCcompl (synCfin)))) (synCvv)))))
      (synWex b (synWa (.classEq (.cv t) (synCsn (.cv b)))
          (.classMem (synCopk (.cv t) (.cv m)) (synCin (synCssetk)
              (synCxpk (synCpw1 (synCimak (synCssetk) (synCcompl (synCfin))))
                (synCvv))))))
      t p0020
  have p0022 :=
    @gExcom
      (synWa (.classEq (.cv t) (synCsn (.cv b))) (.classMem (synCopk (.cv t) (.cv m))
          (synCin (synCssetk)
            (synCxpk (synCpw1 (synCimak (synCssetk) (synCcompl (synCfin)))) (synCvv)))))
      b t
  have p0023 :=
    @gBitr4i
      (synWex t (synWa (.classMem (.cv t) (synC1c)) (.classMem (synCopk (.cv t) (.cv m))
            (synCin (synCssetk)
              (synCxpk (synCpw1 (synCimak (synCssetk) (synCcompl (synCfin))))
                (synCvv))))))
      (synWex t (synWex b (synWa (.classEq (.cv t) (synCsn (.cv b)))
            (.classMem (synCopk (.cv t) (.cv m)) (synCin (synCssetk)
                (synCxpk (synCpw1 (synCimak (synCssetk) (synCcompl (synCfin))))
                  (synCvv)))))))
      (synWex b (synWex t (synWa (.classEq (.cv t) (synCsn (.cv b)))
            (.classMem (synCopk (.cv t) (.cv m)) (synCin (synCssetk)
                (synCxpk (synCpw1 (synCimak (synCssetk) (synCcompl (synCfin))))
                  (synCvv)))))))
      p0021 p0022
  have p0024 := @gSnex (.cv b)
  have p0025 := @gOpkeq1 (.cv t) (synCsn (.cv b)) (.cv m)
  have p0026 :=
    @gEleq1d (.classEq (.cv t) (synCsn (.cv b))) (synCopk (.cv t) (.cv m))
      (synCopk (synCsn (.cv b)) (.cv m))
      (synCin (synCssetk)
        (synCxpk (synCpw1 (synCimak (synCssetk) (synCcompl (synCfin)))) (synCvv)))
      p0025
  have freeVariableCertificate6 : t ∉ ((synCsn (.cv b))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_t_ne_b,
      not_false_eq_true]
  have freeVariableCertificate7 :
    t ∉
      ((Wff.classMem (synCopk (synCsn (.cv b)) (.cv m)) (synCin (synCssetk)
            (synCxpk (synCpw1 (synCimak (synCssetk) (synCcompl (synCfin))))
              (synCvv))))).fv :=
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
    @gCeqsexv
      (.classMem (synCopk (.cv t) (.cv m)) (synCin (synCssetk)
          (synCxpk (synCpw1 (synCimak (synCssetk) (synCcompl (synCfin)))) (synCvv))))
      (.classMem (synCopk (synCsn (.cv b)) (.cv m)) (synCin (synCssetk)
          (synCxpk (synCpw1 (synCimak (synCssetk) (synCcompl (synCfin)))) (synCvv))))
      t (synCsn (.cv b)) freeVariableCertificate6 freeVariableCertificate7 p0024 p0026
  have p0028 :=
    @gElin (synCopk (synCsn (.cv b)) (.cv m)) (synCssetk)
      (synCxpk (synCpw1 (synCimak (synCssetk) (synCcompl (synCfin)))) (synCvv))
  have p0029 := @gVex b
  have p0030 := @gElssetk (.cv b) (.cv m) p0029 p0007
  have p0031 :=
    @gOpkelxpk (synCsn (.cv b)) (.cv m)
      (synCpw1 (synCimak (synCssetk) (synCcompl (synCfin)))) (synCvv) p0024 p0007
  have p0032 :=
    @gMpbiran2
      (.classMem (synCopk (synCsn (.cv b)) (.cv m))
        (synCxpk (synCpw1 (synCimak (synCssetk) (synCcompl (synCfin)))) (synCvv)))
      (.classMem (synCsn (.cv b)) (synCpw1 (synCimak (synCssetk) (synCcompl (synCfin)))))
      (.classMem (.cv m) (synCvv)) p0007 p0031
  have p0033 := @gSnelpw1 (.cv b) (synCimak (synCssetk) (synCcompl (synCfin)))
  have freeVariableCertificate8 : a ∉ ((synCcompl (synCfin))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfin, Finset.notMem_empty,
      not_false_eq_true]
  have freeVariableCertificate9 : a ∉ ((Class.cv b)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_a_ne_b, not_false_eq_true]
  have p0034 :=
    @gElimak a (synCssetk) (synCcompl (synCfin)) (.cv b)
      (by
        exact
          (show a ∉ ((synCssetk)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk];
              exact (show a ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
      freeVariableCertificate8 freeVariableCertificate9 p0029
  have p0035 :=
    (Nominal.biimpRefl (synWrex a (synCcompl (synCfin))
        (.classMem (synCopk (.cv a) (.cv b)) (synCssetk))))
  have p0036 :=
    @gAncom (.classMem (.cv a) (synCcompl (synCfin)))
      (.classMem (synCopk (.cv a) (.cv b)) (synCssetk))
  have p0037 := @gVex a
  have p0038 := @gOpkelssetkg (.cv a) (.cv b) (synCvv) (synCvv)
  have p0039 :=
    @gMp2an (.classMem (.cv a) (synCvv)) (.classMem (.cv b) (synCvv))
      (synWb (.classMem (synCopk (.cv a) (.cv b)) (synCssetk)) (synWss (.cv a) (.cv b)))
      p0037 p0029 p0038
  have p0040 := @gElcompl (.cv a) (synCfin) p0037
  have p0041 :=
    @gAnbi12i (.classMem (synCopk (.cv a) (.cv b)) (synCssetk))
      (synWss (.cv a) (.cv b)) (.classMem (.cv a) (synCcompl (synCfin)))
      (.neg (.classMem (.cv a) (synCfin))) p0039 p0040
  have p0042 :=
    @gBitri
      (synWa (.classMem (.cv a) (synCcompl (synCfin)))
        (.classMem (synCopk (.cv a) (.cv b)) (synCssetk)))
      (synWa (.classMem (synCopk (.cv a) (.cv b)) (synCssetk))
        (.classMem (.cv a) (synCcompl (synCfin))))
      (synWa (synWss (.cv a) (.cv b)) (.neg (.classMem (.cv a) (synCfin)))) p0036 p0041
  have p0043 :=
    @gExbii
      (synWa (.classMem (.cv a) (synCcompl (synCfin)))
        (.classMem (synCopk (.cv a) (.cv b)) (synCssetk)))
      (synWa (synWss (.cv a) (.cv b)) (.neg (.classMem (.cv a) (synCfin)))) a p0042
  have p0044 :=
    @gBitri
      (synWrex a (synCcompl (synCfin)) (.classMem (synCopk (.cv a) (.cv b)) (synCssetk)))
      (synWex a (synWa (.classMem (.cv a) (synCcompl (synCfin)))
          (.classMem (synCopk (.cv a) (.cv b)) (synCssetk))))
      (synWex a (synWa (synWss (.cv a) (.cv b)) (.neg (.classMem (.cv a) (synCfin)))))
      p0035 p0043
  have p0045 := @gExanali (synWss (.cv a) (.cv b)) (.classMem (.cv a) (synCfin)) a
  have p0046 :=
    @gN3bitri (.classMem (.cv b) (synCimak (synCssetk) (synCcompl (synCfin))))
      (synWrex a (synCcompl (synCfin)) (.classMem (synCopk (.cv a) (.cv b)) (synCssetk)))
      (synWex a (synWa (synWss (.cv a) (.cv b)) (.neg (.classMem (.cv a) (synCfin)))))
      (.neg (.all a (.imp (synWss (.cv a) (.cv b)) (.classMem (.cv a) (synCfin)))))
      p0034 p0044 p0045
  have p0047 :=
    @gN3bitri
      (.classMem (synCopk (synCsn (.cv b)) (.cv m))
        (synCxpk (synCpw1 (synCimak (synCssetk) (synCcompl (synCfin)))) (synCvv)))
      (.classMem (synCsn (.cv b)) (synCpw1 (synCimak (synCssetk) (synCcompl (synCfin)))))
      (.classMem (.cv b) (synCimak (synCssetk) (synCcompl (synCfin))))
      (.neg (.all a (.imp (synWss (.cv a) (.cv b)) (.classMem (.cv a) (synCfin)))))
      p0032 p0033 p0046
  have p0048_e00_recanon :
    Nominal.NPrf
      (synWb (.classMem (synCopk (synCsn (.cv b)) (.cv m)) (synCssetk)) (.objMem b m)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCopk synCpr synCun synCnin synWnan synWa synCcompl synCsn
          synCssetk synWex
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
    @gAnbi12i (.classMem (synCopk (synCsn (.cv b)) (.cv m)) (synCssetk)) (.objMem b m)
      (.classMem (synCopk (synCsn (.cv b)) (.cv m))
        (synCxpk (synCpw1 (synCimak (synCssetk) (synCcompl (synCfin)))) (synCvv)))
      (.neg (.all a (.imp (synWss (.cv a) (.cv b)) (.classMem (.cv a) (synCfin)))))
      p0048_e00_recanon p0047
  have p0049 :=
    @gN3bitri
      (synWex t (synWa (.classEq (.cv t) (synCsn (.cv b)))
          (.classMem (synCopk (.cv t) (.cv m)) (synCin (synCssetk)
              (synCxpk (synCpw1 (synCimak (synCssetk) (synCcompl (synCfin))))
                (synCvv))))))
      (.classMem (synCopk (synCsn (.cv b)) (.cv m)) (synCin (synCssetk)
          (synCxpk (synCpw1 (synCimak (synCssetk) (synCcompl (synCfin)))) (synCvv))))
      (synWa (.classMem (synCopk (synCsn (.cv b)) (.cv m)) (synCssetk))
        (.classMem (synCopk (synCsn (.cv b)) (.cv m))
          (synCxpk (synCpw1 (synCimak (synCssetk) (synCcompl (synCfin)))) (synCvv))))
      (synWa (.objMem b m)
        (.neg (.all a (.imp (synWss (.cv a) (.cv b)) (.classMem (.cv a) (synCfin))))))
      p0027 p0028 p0048
  have p0050 :=
    @gExbii
      (synWex t (synWa (.classEq (.cv t) (synCsn (.cv b)))
          (.classMem (synCopk (.cv t) (.cv m)) (synCin (synCssetk)
              (synCxpk (synCpw1 (synCimak (synCssetk) (synCcompl (synCfin))))
                (synCvv))))))
      (synWa (.objMem b m)
        (.neg (.all a (.imp (synWss (.cv a) (.cv b)) (.classMem (.cv a) (synCfin))))))
      b p0049
  have p0051 :=
    @gN3bitri
      (synWrex t (synC1c) (.classMem (synCopk (.cv t) (.cv m)) (synCin (synCssetk)
            (synCxpk (synCpw1 (synCimak (synCssetk) (synCcompl (synCfin)))) (synCvv)))))
      (synWex t (synWa (.classMem (.cv t) (synC1c)) (.classMem (synCopk (.cv t) (.cv m))
            (synCin (synCssetk)
              (synCxpk (synCpw1 (synCimak (synCssetk) (synCcompl (synCfin))))
                (synCvv))))))
      (synWex b (synWex t (synWa (.classEq (.cv t) (synCsn (.cv b)))
            (.classMem (synCopk (.cv t) (.cv m)) (synCin (synCssetk)
                (synCxpk (synCpw1 (synCimak (synCssetk) (synCcompl (synCfin))))
                  (synCvv)))))))
      (synWex b (synWa (.objMem b m) (.neg
            (.all a (.imp (synWss (.cv a) (.cv b)) (.classMem (.cv a) (synCfin)))))))
      p0016 p0023 p0050
  have p0052 :=
    @gExanali (.objMem b m)
      (.all a (.imp (synWss (.cv a) (.cv b)) (.classMem (.cv a) (synCfin)))) b
  have p0053 :=
    @gN3bitri
      (.classMem (.cv m) (synCimak (synCin (synCssetk)
            (synCxpk (synCpw1 (synCimak (synCssetk) (synCcompl (synCfin)))) (synCvv)))
          (synC1c)))
      (synWrex t (synC1c) (.classMem (synCopk (.cv t) (.cv m)) (synCin (synCssetk)
            (synCxpk (synCpw1 (synCimak (synCssetk) (synCcompl (synCfin)))) (synCvv)))))
      (synWex b (synWa (.objMem b m) (.neg
            (.all a (.imp (synWss (.cv a) (.cv b)) (.classMem (.cv a) (synCfin)))))))
      (.neg (.all b (.imp (.objMem b m)
            (.all a (.imp (synWss (.cv a) (.cv b)) (.classMem (.cv a) (synCfin)))))))
      p0015 p0051 p0052
  have p0054 :=
    @gCon2bii
      (.classMem (.cv m) (synCimak (synCin (synCssetk)
            (synCxpk (synCpw1 (synCimak (synCssetk) (synCcompl (synCfin)))) (synCvv)))
          (synC1c)))
      (.all b (.imp (.objMem b m)
          (.all a (.imp (synWss (.cv a) (.cv b)) (.classMem (.cv a) (synCfin))))))
      p0053
  have p0055 :=
    @gN3bitri
      (.all a (.all b (.imp (synWa (.objMem b m) (synWss (.cv a) (.cv b)))
            (.classMem (.cv a) (synCfin)))))
      (.all b (.all a (.imp (synWa (.objMem b m) (synWss (.cv a) (.cv b)))
            (.classMem (.cv a) (synCfin)))))
      (.all b (.imp (.objMem b m)
          (.all a (.imp (synWss (.cv a) (.cv b)) (.classMem (.cv a) (synCfin))))))
      (.neg (.classMem (.cv m) (synCimak (synCin (synCssetk)
              (synCxpk (synCpw1 (synCimak (synCssetk) (synCcompl (synCfin)))) (synCvv)))
            (synC1c))))
      p0009 p0014 p0054
  have p0056 :=
    @gBitr4i
      (.classMem (.cv m) (synCcompl (synCimak (synCin (synCssetk)
              (synCxpk (synCpw1 (synCimak (synCssetk) (synCcompl (synCfin)))) (synCvv)))
            (synC1c))))
      (.neg (.classMem (.cv m) (synCimak (synCin (synCssetk)
              (synCxpk (synCpw1 (synCimak (synCssetk) (synCcompl (synCfin)))) (synCvv)))
            (synC1c))))
      (.all a (.all b (.imp (synWa (.objMem b m) (synWss (.cv a) (.cv b)))
            (.classMem (.cv a) (synCfin)))))
      p0008 p0055
  have freeVariableCertificate10 :
    m ∉
      ((synCcompl (synCimak (synCin (synCssetk)
              (synCxpk (synCpw1 (synCimak (synCssetk) (synCcompl (synCfin)))) (synCvv)))
            (synC1c)))).fv :=
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
    @gEqabi
      (.all a (.all b (.imp (synWa (.objMem b m) (synWss (.cv a) (.cv b)))
            (.classMem (.cv a) (synCfin)))))
      m
      (synCcompl (synCimak (synCin (synCssetk)
            (synCxpk (synCpw1 (synCimak (synCssetk) (synCcompl (synCfin)))) (synCvv)))
          (synC1c)))
      freeVariableCertificate10 p0056
  have p0058 := @gSsetkex
  have p0060 := @gFinex
  have p0061 := @gComplex (synCfin) p0060
  have p0062 := @gImakex (synCssetk) (synCcompl (synCfin)) p0058 p0061
  have p0063 := @gPw1ex (synCimak (synCssetk) (synCcompl (synCfin))) p0062
  have p0064 := @gVvex
  have p0065 :=
    @gXpkex (synCpw1 (synCimak (synCssetk) (synCcompl (synCfin)))) (synCvv) p0063
      p0064
  have p0066 :=
    @gInex (synCssetk)
      (synCxpk (synCpw1 (synCimak (synCssetk) (synCcompl (synCfin)))) (synCvv))
      p0058 p0065
  have p0067 := @gN1cex
  have p0068 :=
    @gImakex
      (synCin (synCssetk)
        (synCxpk (synCpw1 (synCimak (synCssetk) (synCcompl (synCfin)))) (synCvv)))
      (synC1c) p0066 p0067
  have p0069 :=
    @gComplex
      (synCimak (synCin (synCssetk)
          (synCxpk (synCpw1 (synCimak (synCssetk) (synCcompl (synCfin)))) (synCvv)))
        (synC1c))
      p0068
  have p0070 :=
    @gEqeltrri
      (synCcompl (synCimak (synCin (synCssetk)
            (synCxpk (synCpw1 (synCimak (synCssetk) (synCcompl (synCfin)))) (synCvv)))
          (synC1c)))
      (.cab m (.all a (.all b (.imp (synWa (.objMem b m) (synWss (.cv a) (.cv b)))
              (.classMem (.cv a) (synCfin))))))
      (synCvv) p0057 p0069
  have p0071 := @gEleq2 (.cv m) (synC0c) (.cv b)
  have p0072 := (Nominal.classEqRefl (synC0c))
  have p0073 := @gEleq2i (synC0c) (synCsn (synC0)) (.cv b) p0072
  have p0074 := @gElsnc (.cv b) (synC0) p0029
  have p0075 :=
    @gBitri (.classMem (.cv b) (synC0c)) (.classMem (.cv b) (synCsn (synC0)))
      (.classEq (.cv b) (synC0)) p0073 p0074
  have p0076_e00_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv m) (synC0c))
        (synWb (.objMem b m) (.classMem (.cv b) (synC0c)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synC0c synCsn synC0 synCdif synCin synCcompl synCnin synWnan synWa
          synCvv synWb
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
    @gSyl6bb (.classEq (.cv m) (synC0c)) (.objMem b m) (.classMem (.cv b) (synC0c))
      (.classEq (.cv b) (synC0)) p0076_e00_recanon p0075
  have p0077 :=
    @gAnbi1d (.classEq (.cv m) (synC0c)) (.objMem b m) (.classEq (.cv b) (synC0))
      (synWss (.cv a) (.cv b)) p0076
  have p0078 :=
    @gImbi1d (.classEq (.cv m) (synC0c))
      (synWa (.objMem b m) (synWss (.cv a) (.cv b)))
      (synWa (.classEq (.cv b) (synC0)) (synWss (.cv a) (.cv b)))
      (.classMem (.cv a) (synCfin)) p0077
  have freeVariableCertificate11 : a ∉ ((Wff.classEq (.cv m) (synC0c))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_a_ne_m, or_false,
      not_false_eq_true]
  have freeVariableCertificate12 : b ∉ ((Wff.classEq (.cv m) (synC0c))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_b_ne_m, or_false,
      not_false_eq_true]
  have p0079 :=
    @gN2albidv (.classEq (.cv m) (synC0c))
      (.imp (synWa (.objMem b m) (synWss (.cv a) (.cv b))) (.classMem (.cv a) (synCfin)))
      (.imp (synWa (.classEq (.cv b) (synC0)) (synWss (.cv a) (.cv b)))
        (.classMem (.cv a) (synCfin)))
      a b freeVariableCertificate11 freeVariableCertificate12 p0078
  have p0080 := @gElequ2 m k b
  have p0081 :=
    @gAnbi1d (.objEq m k) (.objMem b m) (.objMem b k) (synWss (.cv a) (.cv b)) p0080
  have p0082 :=
    @gImbi1d (.objEq m k) (synWa (.objMem b m) (synWss (.cv a) (.cv b)))
      (synWa (.objMem b k) (synWss (.cv a) (.cv b))) (.classMem (.cv a) (synCfin))
      p0081
  have freeVariableCertificate13 : a ∉ ((Wff.objEq m k)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_insert,
      Finset.mem_singleton, fresh_a_ne_m, fresh_a_ne_k, or_false, not_false_eq_true]
  have freeVariableCertificate14 : b ∉ ((Wff.objEq m k)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_insert,
      Finset.mem_singleton, fresh_b_ne_m, fresh_b_ne_k, or_false, not_false_eq_true]
  have p0083 :=
    @gN2albidv (.objEq m k)
      (.imp (synWa (.objMem b m) (synWss (.cv a) (.cv b))) (.classMem (.cv a) (synCfin)))
      (.imp (synWa (.objMem b k) (synWss (.cv a) (.cv b))) (.classMem (.cv a) (synCfin)))
      a b freeVariableCertificate13 freeVariableCertificate14 p0082
  have p0084 := @gEleq1 (.cv b) (.cv d) (.cv k)
  have p0085_e00_recanon :
    Nominal.NPrf (.imp (.objEq b d) (synWb (.objMem b k) (.objMem d k))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb
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
    @gAdantl (.objEq b d) (synWb (.objMem b k) (.objMem d k)) (.objEq a c)
      p0085_e00_recanon
  have p0086 := @gSseq12 (.cv a) (.cv c) (.cv b) (.cv d)
  have p0087_e01_recanon :
    Nominal.NPrf
      (.imp (synWa (.objEq a c) (.objEq b d))
        (synWb (synWss (.cv a) (.cv b)) (synWss (.cv c) (.cv d)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWa synWb synWss synCin synCcompl synCnin synWnan
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
    @gAnbi12d (synWa (.objEq a c) (.objEq b d)) (.objMem b k) (.objMem d k)
      (synWss (.cv a) (.cv b)) (synWss (.cv c) (.cv d)) p0085 p0087_e01_recanon
  have p0088 := @gEleq1 (.cv a) (.cv c) (synCfin)
  have p0089_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq a c)
        (synWb (.classMem (.cv a) (synCfin)) (.classMem (.cv c) (synCfin)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCfin synCuni synWex synWa synCnnc synCint
        simp (config := { failIfUnchanged := false }) only []
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0088
  have p0089 :=
    @gAdantr (.objEq a c)
      (synWb (.classMem (.cv a) (synCfin)) (.classMem (.cv c) (synCfin))) (.objEq b d)
      p0089_e00_recanon
  have p0090 :=
    @gImbi12d (synWa (.objEq a c) (.objEq b d))
      (synWa (.objMem b k) (synWss (.cv a) (.cv b)))
      (synWa (.objMem d k) (synWss (.cv c) (.cv d))) (.classMem (.cv a) (synCfin))
      (.classMem (.cv c) (synCfin)) p0087 p0089
  have freeVariableCertificate15 :
    d ∉
      ((Wff.imp (synWa (.objMem b k) (synWss (.cv a) (.cv b)))
          (.classMem (.cv a) (synCfin)))).fv :=
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
      ((Wff.imp (synWa (.objMem b k) (synWss (.cv a) (.cv b)))
          (.classMem (.cv a) (synCfin)))).fv :=
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
      ((Wff.imp (synWa (.objMem d k) (synWss (.cv c) (.cv d)))
          (.classMem (.cv c) (synCfin)))).fv :=
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
      ((Wff.imp (synWa (.objMem d k) (synWss (.cv c) (.cv d)))
          (.classMem (.cv c) (synCfin)))).fv :=
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
    @gCbval2v
      (.imp (synWa (.objMem b k) (synWss (.cv a) (.cv b))) (.classMem (.cv a) (synCfin)))
      (.imp (synWa (.objMem d k) (synWss (.cv c) (.cv d))) (.classMem (.cv c) (synCfin)))
      a b c d freeVariableCertificate15 freeVariableCertificate16
      freeVariableCertificate17 freeVariableCertificate18
      (show d ≠ a from (by exact fresh_d_ne_a)) (show d ≠ c from (by exact fresh_d_ne_c))
      (show a ≠ b from (by exact fresh_a_ne_b)) (show b ≠ c from (by exact fresh_b_ne_c))
      p0090
  have p0092 :=
    @gSyl6bb (.objEq m k)
      (.all a (.all b (.imp (synWa (.objMem b m) (synWss (.cv a) (.cv b)))
            (.classMem (.cv a) (synCfin)))))
      (.all a (.all b (.imp (synWa (.objMem b k) (synWss (.cv a) (.cv b)))
            (.classMem (.cv a) (synCfin)))))
      (.all c (.all d (.imp (synWa (.objMem d k) (synWss (.cv c) (.cv d)))
            (.classMem (.cv c) (synCfin)))))
      p0083 p0091
  have p0093 := @gEleq2 (.cv m) (synCplc (.cv k) (synC1c)) (.cv b)
  have p0094_e00_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv m) (synCplc (.cv k) (synC1c)))
        (synWb (.objMem b m) (.classMem (.cv b) (synCplc (.cv k) (synC1c))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synCplc synWrex synWex synWa synC1c synWb
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
    @gAnbi1d (.classEq (.cv m) (synCplc (.cv k) (synC1c))) (.objMem b m)
      (.classMem (.cv b) (synCplc (.cv k) (synC1c))) (synWss (.cv a) (.cv b))
      p0094_e00_recanon
  have p0095 :=
    @gImbi1d (.classEq (.cv m) (synCplc (.cv k) (synC1c)))
      (synWa (.objMem b m) (synWss (.cv a) (.cv b)))
      (synWa (.classMem (.cv b) (synCplc (.cv k) (synC1c))) (synWss (.cv a) (.cv b)))
      (.classMem (.cv a) (synCfin)) p0094
  have freeVariableCertificate19 :
    a ∉ ((Wff.classEq (.cv m) (synCplc (.cv k) (synC1c)))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_a_ne_m, fresh_a_ne_k, or_false,
      not_false_eq_true]
  have freeVariableCertificate20 :
    b ∉ ((Wff.classEq (.cv m) (synCplc (.cv k) (synC1c)))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_b_ne_m, fresh_b_ne_k, or_false,
      not_false_eq_true]
  have p0096 :=
    @gN2albidv (.classEq (.cv m) (synCplc (.cv k) (synC1c)))
      (.imp (synWa (.objMem b m) (synWss (.cv a) (.cv b))) (.classMem (.cv a) (synCfin)))
      (.imp (synWa (.classMem (.cv b) (synCplc (.cv k) (synC1c))) (synWss (.cv a) (.cv b)))
        (.classMem (.cv a) (synCfin)))
      a b freeVariableCertificate19 freeVariableCertificate20 p0095
  have p0097 := @gElequ2 m n b
  have p0098 :=
    @gAnbi1d (.objEq m n) (.objMem b m) (.objMem b n) (synWss (.cv a) (.cv b)) p0097
  have p0099 :=
    @gImbi1d (.objEq m n) (synWa (.objMem b m) (synWss (.cv a) (.cv b)))
      (synWa (.objMem b n) (synWss (.cv a) (.cv b))) (.classMem (.cv a) (synCfin))
      p0098
  have freeVariableCertificate21 : a ∉ ((Wff.objEq m n)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_insert,
      Finset.mem_singleton, fresh_a_ne_m, fresh_a_ne_n, or_false, not_false_eq_true]
  have freeVariableCertificate22 : b ∉ ((Wff.objEq m n)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_insert,
      Finset.mem_singleton, fresh_b_ne_m, fresh_b_ne_n, or_false, not_false_eq_true]
  have p0100 :=
    @gN2albidv (.objEq m n)
      (.imp (synWa (.objMem b m) (synWss (.cv a) (.cv b))) (.classMem (.cv a) (synCfin)))
      (.imp (synWa (.objMem b n) (synWss (.cv a) (.cv b))) (.classMem (.cv a) (synCfin)))
      a b freeVariableCertificate21 freeVariableCertificate22 p0099
  have p0101 := @gSseq2 (.cv b) (synC0) (.cv a)
  have p0102 :=
    @gBiimpa (.classEq (.cv b) (synC0)) (synWss (.cv a) (.cv b))
      (synWss (.cv a) (synC0)) p0101
  have p0103 := @gSs0b (.cv a)
  have p0104 :=
    @gSylib (synWa (.classEq (.cv b) (synC0)) (synWss (.cv a) (.cv b)))
      (synWss (.cv a) (synC0)) (.classEq (.cv a) (synC0)) p0102 p0103
  have p0105 := @gN0fin
  have p0106 :=
    @gSyl6eqel (synWa (.classEq (.cv b) (synC0)) (synWss (.cv a) (.cv b))) (.cv a)
      (synC0) (synCfin) p0104 p0105
  have p0107 :=
    @gGen2
      (.imp (synWa (.classEq (.cv b) (synC0)) (synWss (.cv a) (.cv b)))
        (.classMem (.cv a) (synCfin)))
      a b p0106
  have p0108 := @gSspss (.cv a) (.cv b)
  have freeVariableCertificate23 : x ∉ ((Class.cv a)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_x_ne_a, not_false_eq_true]
  have freeVariableCertificate24 : x ∉ ((Class.cv b)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_x_ne_b, not_false_eq_true]
  have p0109 :=
    @gDfpss4 x (.cv a) (.cv b) freeVariableCertificate23 freeVariableCertificate24
  have p0110_e00_recanon :
    Nominal.NPrf
      (synWb (synWpss (.cv a) (.cv b))
        (synWa (synWss (.cv a) (.cv b)) (synWrex x (.cv b) (.neg (.objMem x a))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWpss synWa synWss synCin synCcompl synCnin synWnan synWne
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
    @gOrbi1i (synWpss (.cv a) (.cv b))
      (synWa (synWss (.cv a) (.cv b)) (synWrex x (.cv b) (.neg (.objMem x a))))
      (.objEq a b) p0110_e00_recanon
  have p0111_e00_recanon :
    Nominal.NPrf
      (synWb (synWss (.cv a) (.cv b)) (synWo (synWpss (.cv a) (.cv b)) (.objEq a b))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWss synCin synCcompl synCnin synWnan synWa synWo synWpss
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
    @gBitri (synWss (.cv a) (.cv b)) (synWo (synWpss (.cv a) (.cv b)) (.objEq a b))
      (synWo (synWa (synWss (.cv a) (.cv b)) (synWrex x (.cv b) (.neg (.objMem x a))))
        (.objEq a b))
      p0111_e00_recanon p0110
  have p0112 :=
    @gSimp1 (.classMem (.cv k) (synCnnc)) (synWa (.objMem x b) (.neg (.objMem x a)))
      (synWa (synWss (.cv a) (.cv b)) (.classMem (.cv b) (synCplc (.cv k) (synC1c))))
  have p0113 := @gVex x
  have p0114 := @gSnid (.cv x) p0113
  have p0115 := @gEldif (.cv x) (.cv b) (synCsn (.cv x))
  have p0116_e00_recanon :
    Nominal.NPrf
      (synWb (.classMem (.cv x) (synCdif (.cv b) (synCsn (.cv x))))
        (synWa (.objMem x b) (.neg (.classMem (.cv x) (synCsn (.cv x)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCdif synCin synCcompl synCnin synWnan synWa synCsn
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
    @gSimprbi (.classMem (.cv x) (synCdif (.cv b) (synCsn (.cv x)))) (.objMem x b)
      (.neg (.classMem (.cv x) (synCsn (.cv x)))) p0116_e00_recanon
  have p0117 :=
    @gMt2 (.classMem (.cv x) (synCdif (.cv b) (synCsn (.cv x))))
      (.classMem (.cv x) (synCsn (.cv x))) p0114 p0116
  have p0118 :=
    @gA1i (.neg (.classMem (.cv x) (synCdif (.cv b) (synCsn (.cv x)))))
      (synW3a (.classMem (.cv k) (synCnnc)) (synWa (.objMem x b) (.neg (.objMem x a)))
        (synWa (synWss (.cv a) (.cv b)) (.classMem (.cv b) (synCplc (.cv k) (synC1c)))))
      p0117
  have p0119 := @gUndif1 (.cv b) (synCsn (.cv x))
  have p0120 := @gSnssi (.cv x) (.cv b)
  have p0121 := @gSsequn2 (synCsn (.cv x)) (.cv b)
  have p0122_e00_recanon :
    Nominal.NPrf (.imp (.objMem x b) (synWss (synCsn (.cv x)) (.cv b))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWss synCin synCcompl synCnin synWnan synWa synCsn
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0120
  have p0122 :=
    @gSylib (.objMem x b) (synWss (synCsn (.cv x)) (.cv b))
      (.classEq (synCun (.cv b) (synCsn (.cv x))) (.cv b)) p0122_e00_recanon p0121
  have p0123 :=
    @gAdantr (.objMem x b) (.classEq (synCun (.cv b) (synCsn (.cv x))) (.cv b))
      (.neg (.objMem x a)) p0122
  have p0124 :=
    @gN3ad2ant2 (synWa (.objMem x b) (.neg (.objMem x a)))
      (.classMem (.cv k) (synCnnc))
      (.classEq (synCun (.cv b) (synCsn (.cv x))) (.cv b))
      (synWa (synWss (.cv a) (.cv b)) (.classMem (.cv b) (synCplc (.cv k) (synC1c))))
      p0123
  have p0125 :=
    @gSyl5eq
      (synW3a (.classMem (.cv k) (synCnnc)) (synWa (.objMem x b) (.neg (.objMem x a)))
        (synWa (synWss (.cv a) (.cv b)) (.classMem (.cv b) (synCplc (.cv k) (synC1c)))))
      (synCun (synCdif (.cv b) (synCsn (.cv x))) (synCsn (.cv x)))
      (synCun (.cv b) (synCsn (.cv x))) (.cv b) p0119 p0124
  have p0126 :=
    @gSimp3r (.classMem (.cv k) (synCnnc)) (synWa (.objMem x b) (.neg (.objMem x a)))
      (synWss (.cv a) (.cv b)) (.classMem (.cv b) (synCplc (.cv k) (synC1c)))
  have p0127 :=
    @gEqeltrd
      (synW3a (.classMem (.cv k) (synCnnc)) (synWa (.objMem x b) (.neg (.objMem x a)))
        (synWa (synWss (.cv a) (.cv b)) (.classMem (.cv b) (synCplc (.cv k) (synC1c)))))
      (synCun (synCdif (.cv b) (synCsn (.cv x))) (synCsn (.cv x))) (.cv b)
      (synCplc (.cv k) (synC1c)) p0125 p0126
  have p0128 := @gSnex (.cv x)
  have p0129 := @gDifex (.cv b) (synCsn (.cv x)) p0029 p0128
  have p0130 :=
    @gNnsucelr (synCdif (.cv b) (synCsn (.cv x))) (.cv k) (.cv x) p0129 p0113
  have p0131 :=
    @gSyl12anc
      (synW3a (.classMem (.cv k) (synCnnc)) (synWa (.objMem x b) (.neg (.objMem x a)))
        (synWa (synWss (.cv a) (.cv b)) (.classMem (.cv b) (synCplc (.cv k) (synC1c)))))
      (.classMem (.cv k) (synCnnc))
      (.neg (.classMem (.cv x) (synCdif (.cv b) (synCsn (.cv x)))))
      (.classMem (synCun (synCdif (.cv b) (synCsn (.cv x))) (synCsn (.cv x)))
        (synCplc (.cv k) (synC1c)))
      (.classMem (synCdif (.cv b) (synCsn (.cv x))) (.cv k)) p0112 p0118 p0127 p0130
  have p0132 := @gInass (.cv a) (.cv b) (synCcompl (synCsn (.cv x)))
  have p0133 :=
    (Nominal.classEqRefl (synCdif (synCin (.cv a) (.cv b)) (synCsn (.cv x))))
  have p0134 := (Nominal.classEqRefl (synCdif (.cv b) (synCsn (.cv x))))
  have p0135 :=
    @gIneq2i (synCdif (.cv b) (synCsn (.cv x)))
      (synCin (.cv b) (synCcompl (synCsn (.cv x)))) (.cv a) p0134
  have p0136 :=
    @gN3eqtr4ri (synCin (synCin (.cv a) (.cv b)) (synCcompl (synCsn (.cv x))))
      (synCin (.cv a) (synCin (.cv b) (synCcompl (synCsn (.cv x)))))
      (synCdif (synCin (.cv a) (.cv b)) (synCsn (.cv x)))
      (synCin (.cv a) (synCdif (.cv b) (synCsn (.cv x)))) p0132 p0133 p0135
  have p0137 := (Nominal.biimpRefl (synWss (.cv a) (.cv b)))
  have p0138 :=
    @gBiimpi (synWss (.cv a) (.cv b)) (.classEq (synCin (.cv a) (.cv b)) (.cv a)) p0137
  have p0139 :=
    @gAdantr (synWss (.cv a) (.cv b)) (.classEq (synCin (.cv a) (.cv b)) (.cv a))
      (.classMem (.cv b) (synCplc (.cv k) (synC1c))) p0138
  have p0140 :=
    @gN3ad2ant3
      (synWa (synWss (.cv a) (.cv b)) (.classMem (.cv b) (synCplc (.cv k) (synC1c))))
      (.classMem (.cv k) (synCnnc)) (.classEq (synCin (.cv a) (.cv b)) (.cv a))
      (synWa (.objMem x b) (.neg (.objMem x a))) p0139
  have p0141 :=
    @gDifeq1d
      (synW3a (.classMem (.cv k) (synCnnc)) (synWa (.objMem x b) (.neg (.objMem x a)))
        (synWa (synWss (.cv a) (.cv b)) (.classMem (.cv b) (synCplc (.cv k) (synC1c)))))
      (synCin (.cv a) (.cv b)) (.cv a) (synCsn (.cv x)) p0140
  have p0142 := @gDifsn (.cv x) (.cv a)
  have p0143_e00_recanon :
    Nominal.NPrf
      (.imp (.neg (.objMem x a)) (.classEq (synCdif (.cv a) (synCsn (.cv x))) (.cv a))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synCdif synCin synCcompl synCnin synWnan synWa synCsn
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0142
  have p0143 :=
    @gAdantl (.neg (.objMem x a)) (.classEq (synCdif (.cv a) (synCsn (.cv x))) (.cv a))
      (.objMem x b) p0143_e00_recanon
  have p0144 :=
    @gN3ad2ant2 (synWa (.objMem x b) (.neg (.objMem x a)))
      (.classMem (.cv k) (synCnnc))
      (.classEq (synCdif (.cv a) (synCsn (.cv x))) (.cv a))
      (synWa (synWss (.cv a) (.cv b)) (.classMem (.cv b) (synCplc (.cv k) (synC1c))))
      p0143
  have p0145 :=
    @gEqtrd
      (synW3a (.classMem (.cv k) (synCnnc)) (synWa (.objMem x b) (.neg (.objMem x a)))
        (synWa (synWss (.cv a) (.cv b)) (.classMem (.cv b) (synCplc (.cv k) (synC1c)))))
      (synCdif (synCin (.cv a) (.cv b)) (synCsn (.cv x)))
      (synCdif (.cv a) (synCsn (.cv x))) (.cv a) p0141 p0144
  have p0146 :=
    @gSyl5eq
      (synW3a (.classMem (.cv k) (synCnnc)) (synWa (.objMem x b) (.neg (.objMem x a)))
        (synWa (synWss (.cv a) (.cv b)) (.classMem (.cv b) (synCplc (.cv k) (synC1c)))))
      (synCin (.cv a) (synCdif (.cv b) (synCsn (.cv x))))
      (synCdif (synCin (.cv a) (.cv b)) (synCsn (.cv x))) (.cv a) p0136 p0145
  have p0147 := (Nominal.biimpRefl (synWss (.cv a) (synCdif (.cv b) (synCsn (.cv x)))))
  have p0148 :=
    @gSylibr
      (synW3a (.classMem (.cv k) (synCnnc)) (synWa (.objMem x b) (.neg (.objMem x a)))
        (synWa (synWss (.cv a) (.cv b)) (.classMem (.cv b) (synCplc (.cv k) (synC1c)))))
      (.classEq (synCin (.cv a) (synCdif (.cv b) (synCsn (.cv x)))) (.cv a))
      (synWss (.cv a) (synCdif (.cv b) (synCsn (.cv x)))) p0146 p0147
  have p0149 :=
    @gJca
      (synW3a (.classMem (.cv k) (synCnnc)) (synWa (.objMem x b) (.neg (.objMem x a)))
        (synWa (synWss (.cv a) (.cv b)) (.classMem (.cv b) (synCplc (.cv k) (synC1c)))))
      (.classMem (synCdif (.cv b) (synCsn (.cv x))) (.cv k))
      (synWss (.cv a) (synCdif (.cv b) (synCsn (.cv x)))) p0131 p0148
  have p0150 :=
    @gN3adant1r (.classMem (.cv k) (synCnnc))
      (synWa (.objMem x b) (.neg (.objMem x a)))
      (synWa (synWss (.cv a) (.cv b)) (.classMem (.cv b) (synCplc (.cv k) (synC1c))))
      (synWa (.classMem (synCdif (.cv b) (synCsn (.cv x))) (.cv k))
        (synWss (.cv a) (synCdif (.cv b) (synCsn (.cv x)))))
      (.all c (.all d (.imp (synWa (.objMem d k) (synWss (.cv c) (.cv d)))
            (.classMem (.cv c) (synCfin)))))
      p0149
  have p0151 := @gEleq1 (.cv d) (synCdif (.cv b) (synCsn (.cv x))) (.cv k)
  have p0152_e00_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv d) (synCdif (.cv b) (synCsn (.cv x)))) (synWb (.objMem d k)
          (.classMem (synCdif (.cv b) (synCsn (.cv x))) (.cv k)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synCdif synCin synCcompl synCnin synWnan synWa synCsn synWb
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
    @gAdantl (.classEq (.cv d) (synCdif (.cv b) (synCsn (.cv x))))
      (synWb (.objMem d k) (.classMem (synCdif (.cv b) (synCsn (.cv x))) (.cv k)))
      (.objEq c a) p0152_e00_recanon
  have p0153 := @gSseq12 (.cv c) (.cv a) (.cv d) (synCdif (.cv b) (synCsn (.cv x)))
  have p0154_e01_recanon :
    Nominal.NPrf
      (.imp (synWa (.objEq c a) (.classEq (.cv d) (synCdif (.cv b) (synCsn (.cv x)))))
        (synWb (synWss (.cv c) (.cv d))
          (synWss (.cv a) (synCdif (.cv b) (synCsn (.cv x)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWa synCdif synCin synCcompl synCnin synWnan synCsn synWb synWss
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
    @gAnbi12d
      (synWa (.objEq c a) (.classEq (.cv d) (synCdif (.cv b) (synCsn (.cv x)))))
      (.objMem d k) (.classMem (synCdif (.cv b) (synCsn (.cv x))) (.cv k))
      (synWss (.cv c) (.cv d)) (synWss (.cv a) (synCdif (.cv b) (synCsn (.cv x))))
      p0152 p0154_e01_recanon
  have p0155 := @gEleq1 (.cv c) (.cv a) (synCfin)
  have p0156_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq c a)
        (synWb (.classMem (.cv c) (synCfin)) (.classMem (.cv a) (synCfin)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCfin synCuni synWex synWa synCnnc synCint
        simp (config := { failIfUnchanged := false }) only []
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0155
  have p0156 :=
    @gAdantr (.objEq c a)
      (synWb (.classMem (.cv c) (synCfin)) (.classMem (.cv a) (synCfin)))
      (.classEq (.cv d) (synCdif (.cv b) (synCsn (.cv x)))) p0156_e00_recanon
  have p0157 :=
    @gImbi12d
      (synWa (.objEq c a) (.classEq (.cv d) (synCdif (.cv b) (synCsn (.cv x)))))
      (synWa (.objMem d k) (synWss (.cv c) (.cv d)))
      (synWa (.classMem (synCdif (.cv b) (synCsn (.cv x))) (.cv k))
        (synWss (.cv a) (synCdif (.cv b) (synCsn (.cv x)))))
      (.classMem (.cv c) (synCfin)) (.classMem (.cv a) (synCfin)) p0154 p0156
  have p0158_e00_recanon :
    Nominal.NPrf
      (.imp (synWa (.classEq (.cv c) (.cv a))
          (.classEq (.cv d) (synCdif (.cv b) (synCsn (.cv x))))) (synWb
          (.imp (synWa (.objMem d k) (synWss (.cv c) (.cv d))) (.classMem (.cv c) (synCfin)))
          (.imp (synWa (.classMem (synCdif (.cv b) (synCsn (.cv x))) (.cv k))
              (synWss (.cv a) (synCdif (.cv b) (synCsn (.cv x)))))
            (.classMem (.cv a) (synCfin))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWa synCdif synCin synCcompl synCnin synWnan synCsn synWb
          synCfin synCuni synWex synCnnc synCint
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
  have freeVariableCertificate27 : c ∉ ((synCdif (.cv b) (synCsn (.cv x)))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
      Finset.mem_singleton, fresh_c_ne_b, fresh_c_ne_x, or_false, not_false_eq_true]
  have freeVariableCertificate28 : d ∉ ((synCdif (.cv b) (synCsn (.cv x)))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
      Finset.mem_singleton, fresh_d_ne_b, fresh_d_ne_x, or_false, not_false_eq_true]
  have freeVariableCertificate29 :
    c ∉
      ((Wff.imp (synWa (.classMem (synCdif (.cv b) (synCsn (.cv x))) (.cv k))
            (synWss (.cv a) (synCdif (.cv b) (synCsn (.cv x)))))
          (.classMem (.cv a) (synCfin)))).fv :=
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
      ((Wff.imp (synWa (.classMem (synCdif (.cv b) (synCsn (.cv x))) (.cv k))
            (synWss (.cv a) (synCdif (.cv b) (synCsn (.cv x)))))
          (.classMem (.cv a) (synCfin)))).fv :=
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
    @gSpc2gv
      (.imp (synWa (.objMem d k) (synWss (.cv c) (.cv d))) (.classMem (.cv c) (synCfin)))
      (.imp (synWa (.classMem (synCdif (.cv b) (synCsn (.cv x))) (.cv k))
          (synWss (.cv a) (synCdif (.cv b) (synCsn (.cv x)))))
        (.classMem (.cv a) (synCfin)))
      c d (.cv a) (synCdif (.cv b) (synCsn (.cv x))) (synCvv) (synCvv)
      freeVariableCertificate25 freeVariableCertificate26 freeVariableCertificate27
      freeVariableCertificate28 freeVariableCertificate29 freeVariableCertificate30
      (show c ≠ d from (by exact fresh_c_ne_d)) p0158_e00_recanon
  have p0159 :=
    @gMp2an (.classMem (.cv a) (synCvv))
      (.classMem (synCdif (.cv b) (synCsn (.cv x))) (synCvv))
      (.imp (.all c (.all d (.imp (synWa (.objMem d k) (synWss (.cv c) (.cv d)))
              (.classMem (.cv c) (synCfin))))) (.imp
          (synWa (.classMem (synCdif (.cv b) (synCsn (.cv x))) (.cv k))
            (synWss (.cv a) (synCdif (.cv b) (synCsn (.cv x)))))
          (.classMem (.cv a) (synCfin))))
      p0037 p0129 p0158
  have p0160 :=
    @gAdantl
      (.all c (.all d (.imp (synWa (.objMem d k) (synWss (.cv c) (.cv d)))
            (.classMem (.cv c) (synCfin)))))
      (.imp (synWa (.classMem (synCdif (.cv b) (synCsn (.cv x))) (.cv k))
          (synWss (.cv a) (synCdif (.cv b) (synCsn (.cv x)))))
        (.classMem (.cv a) (synCfin)))
      (.classMem (.cv k) (synCnnc)) p0159
  have p0161 :=
    @gN3ad2ant1
      (synWa (.classMem (.cv k) (synCnnc)) (.all c (.all d
            (.imp (synWa (.objMem d k) (synWss (.cv c) (.cv d)))
              (.classMem (.cv c) (synCfin))))))
      (synWa (.objMem x b) (.neg (.objMem x a)))
      (.imp (synWa (.classMem (synCdif (.cv b) (synCsn (.cv x))) (.cv k))
          (synWss (.cv a) (synCdif (.cv b) (synCsn (.cv x)))))
        (.classMem (.cv a) (synCfin)))
      (synWa (synWss (.cv a) (.cv b)) (.classMem (.cv b) (synCplc (.cv k) (synC1c))))
      p0160
  have p0162 :=
    @gMpd
      (synW3a (synWa (.classMem (.cv k) (synCnnc)) (.all c (.all d
              (.imp (synWa (.objMem d k) (synWss (.cv c) (.cv d)))
                (.classMem (.cv c) (synCfin)))))) (synWa (.objMem x b) (.neg (.objMem x a)))
        (synWa (synWss (.cv a) (.cv b)) (.classMem (.cv b) (synCplc (.cv k) (synC1c)))))
      (synWa (.classMem (synCdif (.cv b) (synCsn (.cv x))) (.cv k))
        (synWss (.cv a) (synCdif (.cv b) (synCsn (.cv x)))))
      (.classMem (.cv a) (synCfin)) p0150 p0161
  have p0163 :=
    @gN3exp
      (synWa (.classMem (.cv k) (synCnnc)) (.all c (.all d
            (.imp (synWa (.objMem d k) (synWss (.cv c) (.cv d)))
              (.classMem (.cv c) (synCfin))))))
      (synWa (.objMem x b) (.neg (.objMem x a)))
      (synWa (synWss (.cv a) (.cv b)) (.classMem (.cv b) (synCplc (.cv k) (synC1c))))
      (.classMem (.cv a) (synCfin)) p0162
  have p0164 :=
    @gExp5c
      (synWa (.classMem (.cv k) (synCnnc)) (.all c (.all d
            (.imp (synWa (.objMem d k) (synWss (.cv c) (.cv d)))
              (.classMem (.cv c) (synCfin))))))
      (.objMem x b) (.neg (.objMem x a)) (synWss (.cv a) (.cv b))
      (.classMem (.cv b) (synCplc (.cv k) (synC1c))) (.classMem (.cv a) (synCfin))
      p0163
  have p0165_e00_recanon :
    Nominal.NPrf
      (.imp (synWa (.classMem (.cv k) (synCnnc)) (.all c (.all d
              (.imp (synWa (.objMem d k) (synWss (.cv c) (.cv d)))
                (.classMem (.cv c) (synCfin)))))) (.imp (.classMem (.cv x) (.cv b))
          (.imp (.neg (.objMem x a)) (.imp (synWss (.cv a) (.cv b))
              (.imp (.classMem (.cv b) (synCplc (.cv k) (synC1c)))
                (.classMem (.cv a) (synCfin))))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWa synCnnc synCint synCfin synCuni synWex synWss synCin
          synCcompl synCnin synWnan synCplc synWrex synC1c
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
      ((Wff.imp (synWss (.cv a) (.cv b)) (.imp (.classMem (.cv b) (synCplc (.cv k) (synC1c)))
            (.classMem (.cv a) (synCfin))))).fv :=
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
      ((synWa (.classMem (.cv k) (synCnnc)) (.all c (.all d
              (.imp (synWa (.objMem d k) (synWss (.cv c) (.cv d)))
                (.classMem (.cv c) (synCfin))))))).fv :=
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
    @gRexlimdv
      (synWa (.classMem (.cv k) (synCnnc)) (.all c (.all d
            (.imp (synWa (.objMem d k) (synWss (.cv c) (.cv d)))
              (.classMem (.cv c) (synCfin))))))
      (.neg (.objMem x a))
      (.imp (synWss (.cv a) (.cv b)) (.imp (.classMem (.cv b) (synCplc (.cv k) (synC1c)))
          (.classMem (.cv a) (synCfin))))
      x (.cv b) freeVariableCertificate31 freeVariableCertificate32 p0165_e00_recanon
  have p0166 :=
    @gCom23
      (synWa (.classMem (.cv k) (synCnnc)) (.all c (.all d
            (.imp (synWa (.objMem d k) (synWss (.cv c) (.cv d)))
              (.classMem (.cv c) (synCfin))))))
      (synWrex x (.cv b) (.neg (.objMem x a))) (synWss (.cv a) (.cv b))
      (.imp (.classMem (.cv b) (synCplc (.cv k) (synC1c))) (.classMem (.cv a) (synCfin)))
      p0165
  have p0167 :=
    @gImp3a
      (synWa (.classMem (.cv k) (synCnnc)) (.all c (.all d
            (.imp (synWa (.objMem d k) (synWss (.cv c) (.cv d)))
              (.classMem (.cv c) (synCfin))))))
      (synWss (.cv a) (.cv b)) (synWrex x (.cv b) (.neg (.objMem x a)))
      (.imp (.classMem (.cv b) (synCplc (.cv k) (synC1c))) (.classMem (.cv a) (synCfin)))
      p0166
  have p0168 := @gPeano2 (.cv k)
  have p0169 := @gEleq2 (.cv x) (synCplc (.cv k) (synC1c)) (.cv b)
  have p0170_e00_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv x) (synCplc (.cv k) (synC1c)))
        (synWb (.objMem b x) (.classMem (.cv b) (synCplc (.cv k) (synC1c))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synCplc synWrex synWex synWa synC1c synWb
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
  have freeVariableCertificate33 : x ∉ ((synCplc (.cv k) (synC1c))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_x_ne_k, or_false,
      not_false_eq_true]
  have freeVariableCertificate34 :
    x ∉ ((Wff.classMem (.cv b) (synCplc (.cv k) (synC1c)))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_x_ne_b, fresh_x_ne_k, or_false,
      not_false_eq_true]
  have p0170 :=
    @gRspcev (.objMem b x) (.classMem (.cv b) (synCplc (.cv k) (synC1c))) x
      (synCplc (.cv k) (synC1c)) (synCnnc) freeVariableCertificate33
      (by
        exact
          (show x ∉ ((synCnnc)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc];
              exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
      freeVariableCertificate34 p0170_e00_recanon
  have p0171 := @gElfin x (.cv b) freeVariableCertificate24
  have p0172_e01_recanon :
    Nominal.NPrf
      (synWb (.classMem (.cv b) (synCfin)) (synWrex x (synCnnc) (.objMem b x))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCfin synCuni synWex synWa synCnnc synCint synWrex
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
    @gSylibr
      (synWa (.classMem (synCplc (.cv k) (synC1c)) (synCnnc))
        (.classMem (.cv b) (synCplc (.cv k) (synC1c))))
      (synWrex x (synCnnc) (.objMem b x)) (.classMem (.cv b) (synCfin)) p0170
      p0172_e01_recanon
  have p0173 :=
    @gEx (.classMem (synCplc (.cv k) (synC1c)) (synCnnc))
      (.classMem (.cv b) (synCplc (.cv k) (synC1c))) (.classMem (.cv b) (synCfin))
      p0172
  have p0174 :=
    @gSyl (.classMem (.cv k) (synCnnc))
      (.classMem (synCplc (.cv k) (synC1c)) (synCnnc))
      (.imp (.classMem (.cv b) (synCplc (.cv k) (synC1c))) (.classMem (.cv b) (synCfin)))
      p0168 p0173
  have p0175 := @gEleq1 (.cv a) (.cv b) (synCfin)
  have p0176_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq a b)
        (synWb (.classMem (.cv a) (synCfin)) (.classMem (.cv b) (synCfin)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCfin synCuni synWex synWa synCnnc synCint
        simp (config := { failIfUnchanged := false }) only []
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0175
  have p0176 :=
    @gBiimprd (.objEq a b) (.classMem (.cv a) (synCfin)) (.classMem (.cv b) (synCfin))
      p0176_e00_recanon
  have p0177 :=
    @gSyl9 (.classMem (.cv k) (synCnnc))
      (.classMem (.cv b) (synCplc (.cv k) (synC1c))) (.classMem (.cv b) (synCfin))
      (.objEq a b) (.classMem (.cv a) (synCfin)) p0174 p0176
  have p0178 :=
    @gAdantr (.classMem (.cv k) (synCnnc))
      (.imp (.objEq a b) (.imp (.classMem (.cv b) (synCplc (.cv k) (synC1c)))
          (.classMem (.cv a) (synCfin))))
      (.all c (.all d (.imp (synWa (.objMem d k) (synWss (.cv c) (.cv d)))
            (.classMem (.cv c) (synCfin)))))
      p0177
  have p0179 :=
    @gJaod
      (synWa (.classMem (.cv k) (synCnnc)) (.all c (.all d
            (.imp (synWa (.objMem d k) (synWss (.cv c) (.cv d)))
              (.classMem (.cv c) (synCfin))))))
      (synWa (synWss (.cv a) (.cv b)) (synWrex x (.cv b) (.neg (.objMem x a))))
      (.imp (.classMem (.cv b) (synCplc (.cv k) (synC1c))) (.classMem (.cv a) (synCfin)))
      (.objEq a b) p0167 p0178
  have p0180 :=
    @gSyl5bi (synWss (.cv a) (.cv b))
      (synWo (synWa (synWss (.cv a) (.cv b)) (synWrex x (.cv b) (.neg (.objMem x a))))
        (.objEq a b))
      (synWa (.classMem (.cv k) (synCnnc)) (.all c (.all d
            (.imp (synWa (.objMem d k) (synWss (.cv c) (.cv d)))
              (.classMem (.cv c) (synCfin))))))
      (.imp (.classMem (.cv b) (synCplc (.cv k) (synC1c))) (.classMem (.cv a) (synCfin)))
      p0111 p0179
  have p0181 :=
    @gCom23
      (synWa (.classMem (.cv k) (synCnnc)) (.all c (.all d
            (.imp (synWa (.objMem d k) (synWss (.cv c) (.cv d)))
              (.classMem (.cv c) (synCfin))))))
      (synWss (.cv a) (.cv b)) (.classMem (.cv b) (synCplc (.cv k) (synC1c)))
      (.classMem (.cv a) (synCfin)) p0180
  have p0182 :=
    @gImp3a
      (synWa (.classMem (.cv k) (synCnnc)) (.all c (.all d
            (.imp (synWa (.objMem d k) (synWss (.cv c) (.cv d)))
              (.classMem (.cv c) (synCfin))))))
      (.classMem (.cv b) (synCplc (.cv k) (synC1c))) (synWss (.cv a) (.cv b))
      (.classMem (.cv a) (synCfin)) p0181
  have freeVariableCertificate35 :
    a ∉
      ((synWa (.classMem (.cv k) (synCnnc)) (.all c (.all d
              (.imp (synWa (.objMem d k) (synWss (.cv c) (.cv d)))
                (.classMem (.cv c) (synCfin))))))).fv :=
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
      ((synWa (.classMem (.cv k) (synCnnc)) (.all c (.all d
              (.imp (synWa (.objMem d k) (synWss (.cv c) (.cv d)))
                (.classMem (.cv c) (synCfin))))))).fv :=
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
    @gAlrimivv
      (synWa (.classMem (.cv k) (synCnnc)) (.all c (.all d
            (.imp (synWa (.objMem d k) (synWss (.cv c) (.cv d)))
              (.classMem (.cv c) (synCfin))))))
      (.imp (synWa (.classMem (.cv b) (synCplc (.cv k) (synC1c))) (synWss (.cv a) (.cv b)))
        (.classMem (.cv a) (synCfin)))
      a b freeVariableCertificate35 freeVariableCertificate36 p0182
  have p0184 :=
    @gEx (.classMem (.cv k) (synCnnc))
      (.all c (.all d (.imp (synWa (.objMem d k) (synWss (.cv c) (.cv d)))
            (.classMem (.cv c) (synCfin)))))
      (.all a (.all b (.imp (synWa (.classMem (.cv b) (synCplc (.cv k) (synC1c)))
              (synWss (.cv a) (.cv b))) (.classMem (.cv a) (synCfin)))))
      p0183
  have p0185_e04_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv m) (.cv n)) (synWb (.all a (.all b
              (.imp (synWa (.objMem b m) (synWss (.cv a) (.cv b)))
                (.classMem (.cv a) (synCfin))))) (.all a (.all b
              (.imp (synWa (.objMem b n) (synWss (.cv a) (.cv b)))
                (.classMem (.cv a) (synCfin))))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWa synWss synCin synCcompl synCnin synWnan synCfin
          synCuni synWex synCnnc synCint
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
      ((Wff.all c (.all d (.imp (synWa (.objMem d k) (synWss (.cv c) (.cv d)))
              (.classMem (.cv c) (synCfin)))))).fv :=
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
      ((Wff.all a (.all b (.imp (synWa (.objMem b m) (synWss (.cv a) (.cv b)))
              (.classMem (.cv a) (synCfin)))))).fv :=
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
      ((Wff.all a (.all b (.imp (synWa (.classEq (.cv b) (synC0)) (synWss (.cv a) (.cv b)))
              (.classMem (.cv a) (synCfin)))))).fv :=
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
      ((Wff.all a (.all b (.imp (synWa (.objMem b n) (synWss (.cv a) (.cv b)))
              (.classMem (.cv a) (synCfin)))))).fv :=
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
      ((Wff.all a (.all b (.imp (synWa (.classMem (.cv b) (synCplc (.cv k) (synC1c)))
                (synWss (.cv a) (.cv b))) (.classMem (.cv a) (synCfin)))))).fv :=
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
    @gFinds
      (.all a (.all b (.imp (synWa (.objMem b m) (synWss (.cv a) (.cv b)))
            (.classMem (.cv a) (synCfin)))))
      (.all a (.all b (.imp (synWa (.classEq (.cv b) (synC0)) (synWss (.cv a) (.cv b)))
            (.classMem (.cv a) (synCfin)))))
      (.all c (.all d (.imp (synWa (.objMem d k) (synWss (.cv c) (.cv d)))
            (.classMem (.cv c) (synCfin)))))
      (.all a (.all b (.imp (synWa (.classMem (.cv b) (synCplc (.cv k) (synC1c)))
              (synWss (.cv a) (.cv b))) (.classMem (.cv a) (synCfin)))))
      (.all a (.all b (.imp (synWa (.objMem b n) (synWss (.cv a) (.cv b)))
            (.classMem (.cv a) (synCfin)))))
      m k (.cv n) freeVariableCertificate37 freeVariableCertificate38
      freeVariableCertificate39 freeVariableCertificate40 freeVariableCertificate41
      freeVariableCertificate42 (show m ≠ k from (by exact fresh_m_ne_k)) p0070 p0079
      p0092 p0096 p0185_e04_recanon p0107 p0184
  have p0186 :=
    @gN1921bbi (.classMem (.cv n) (synCnnc))
      (.imp (synWa (.objMem b n) (synWss (.cv a) (.cv b))) (.classMem (.cv a) (synCfin)))
      a b p0185
  have p0187 :=
    @gExp3a (.classMem (.cv n) (synCnnc)) (.objMem b n) (synWss (.cv a) (.cv b))
      (.classMem (.cv a) (synCfin)) p0186
  have freeVariableCertificate43 :
    n ∉ ((Wff.imp (synWss (.cv a) (.cv b)) (.classMem (.cv a) (synCfin)))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfin, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_n_ne_a, fresh_n_ne_b, or_false,
      not_false_eq_true]
  have p0188 :=
    @gRexlimiv (.objMem b n)
      (.imp (synWss (.cv a) (.cv b)) (.classMem (.cv a) (synCfin))) n (synCnnc)
      freeVariableCertificate43 p0187
  have p0189_e00_recanon :
    Nominal.NPrf
      (synWb (.classMem (.cv b) (synCfin)) (synWrex n (synCnnc) (.objMem b n))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCfin synCuni synWex synWa synCnnc synCint synWrex
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
    @gSylbi (.classMem (.cv b) (synCfin)) (synWrex n (synCnnc) (.objMem b n))
      (.imp (synWss (.cv a) (.cv b)) (.classMem (.cv a) (synCfin))) p0189_e00_recanon
      p0188
  have freeVariableCertificate44 :
    b ∉ ((Wff.imp (synWss (.cv a) B) (.classMem (.cv a) (synCfin)))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfin, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_b_ne_a, fresh_b_not_B, or_false,
      not_false_eq_true]
  have p0190 :=
    @gVtoclga (.imp (synWss (.cv a) (.cv b)) (.classMem (.cv a) (synCfin)))
      (.imp (synWss (.cv a) B) (.classMem (.cv a) (synCfin))) b B (synCfin)
      (by exact (show b ∉ (B).fv from (by exact fresh_b_not_B)))
      (by
        exact
          (show b ∉ ((synCfin)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfin];
              exact (show b ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
      freeVariableCertificate44 p0005 p0189
  have freeVariableCertificate45 :
    a ∉
      ((Wff.imp (.classMem B (synCfin)) (.imp (synWss A B) (.classMem A (synCfin))))).fv :=
    by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfin,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, Finset.mem_union,
      Finset.notMem_empty, fresh_a_not_B, fresh_a_not_A, or_false, not_false_eq_true]
  have p0191 :=
    @gVtoclg
      (.imp (.classMem B (synCfin)) (.imp (synWss (.cv a) B) (.classMem (.cv a) (synCfin))))
      (.imp (.classMem B (synCfin)) (.imp (synWss A B) (.classMem A (synCfin)))) a A V
      (by exact (show a ∉ (A).fv from (by exact fresh_a_not_A))) freeVariableCertificate45
      p0003 p0190
  have p0192 :=
    @gN3imp (.classMem A V) (.classMem B (synCfin)) (synWss A B)
      (.classMem A (synCfin)) p0191
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

/-- Checked nominal proof certificate identified upstream as `g_vfinnc`. -/
@[expose]
noncomputable def gVfinnc (x : Var) (A : Class) (V : Class) (dv_A_x : x ∉ A.fv) :
    Nominal.NPrf
      (.imp (synWa (.classMem A V) (.classMem (synCvv) (synCfin)))
        (synWreu x (synCnnc) (.classMem A (.cv x)))) :=
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
  have p0000 := @gSsv A
  have p0001 := @gSsfin A (synCvv) V
  have p0002 :=
    @gMp3an3 (.classMem A V) (.classMem (synCvv) (synCfin)) (synWss A (synCvv))
      (.classMem A (synCfin)) p0000 p0001
  have p0003 := @gElfin x A (by exact (show x ∉ (A).fv from (by exact dv_A_x)))
  have p0004 :=
    @gSylib (synWa (.classMem A V) (.classMem (synCvv) (synCfin)))
      (.classMem A (synCfin)) (synWrex x (synCnnc) (.classMem A (.cv x))) p0002 p0003
  have p0005 := @gNnceleq A (.cv x) (.cv y)
  have p0006_e00_recanon :
    Nominal.NPrf
      (.imp (synWa (synWa (.classMem (.cv x) (synCnnc)) (.classMem (.cv y) (synCnnc)))
          (synWa (.classMem A (.cv x)) (.classMem A (.cv y)))) (.objEq x y)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWa
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _)
      p0005
  have p0006 :=
    @gEx (synWa (.classMem (.cv x) (synCnnc)) (.classMem (.cv y) (synCnnc)))
      (synWa (.classMem A (.cv x)) (.classMem A (.cv y))) (.objEq x y) p0006_e00_recanon
  have p0007 :=
    @gRgen2a (.imp (synWa (.classMem A (.cv x)) (.classMem A (.cv y))) (.objEq x y)) x y
      (synCnnc)
      (by
        exact
          (show y ∉ ((synCnnc)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc];
              exact (show y ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
      p0006
  have p0008 :=
    @gA1i
      (synWral x (synCnnc) (synWral y (synCnnc)
          (.imp (synWa (.classMem A (.cv x)) (.classMem A (.cv y))) (.objEq x y))))
      (synWa (.classMem A V) (.classMem (synCvv) (synCfin))) p0007
  have p0009 := @gEleq2 (.cv x) (.cv y) A
  have p0010_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq x y) (synWb (.classMem A (.cv x)) (.classMem A (.cv y)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb
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
    @gReu4 (.classMem A (.cv x)) (.classMem A (.cv y)) x y (synCnnc)
      (by
        exact
          (show x ∉ ((synCnnc)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc];
              exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
      (by
        exact
          (show y ∉ ((synCnnc)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc];
              exact (show y ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
      freeVariableCertificate0 freeVariableCertificate1
      (show x ≠ y from (by exact fresh_x_ne_y)) p0010_e00_recanon
  have p0011 :=
    @gSylanbrc (synWa (.classMem A V) (.classMem (synCvv) (synCfin)))
      (synWrex x (synCnnc) (.classMem A (.cv x)))
      (synWral x (synCnnc) (synWral y (synCnnc)
          (.imp (synWa (.classMem A (.cv x)) (.classMem A (.cv y))) (.objEq x y))))
      (synWreu x (synCnnc) (.classMem A (.cv x))) p0004 p0008 p0010
  exact p0011

/-- Checked nominal proof certificate identified upstream as `g_ncfinex`. -/
@[expose]
noncomputable def gNcfinex (A : Class) :
    Nominal.NPrf (.classMem (synCncfin A) (synCvv)) :=
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
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfNcfin x A
      (by exact (show x ∉ (A).fv from (by exact fresh_x_not_A)))
  have p0001 := @gIotaex (synWa (.classMem (.cv x) (synCnnc)) (.classMem A (.cv x))) x
  have p0002 :=
    @gEqeltri (synCncfin A)
      (synCio x (synWa (.classMem (.cv x) (synCnnc)) (.classMem A (.cv x)))) (synCvv)
      p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_ncfineq`. -/
@[expose]
noncomputable def gNcfineq (A : Class) (B : Class) :
    Nominal.NPrf (.imp (.classEq A B) (.classEq (synCncfin A) (synCncfin B))) :=
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
  have p0000 := @gEleq1 A B (.cv x)
  have p0001 :=
    @gAnbi2d (.classEq A B) (.classMem A (.cv x)) (.classMem B (.cv x))
      (.classMem (.cv x) (synCnnc)) p0000
  have freeVariableCertificate0 : x ∉ ((Wff.classEq A B)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union,
      fresh_x_not_A, fresh_x_not_B, or_false, not_false_eq_true]
  have p0002 :=
    @gIotabidv (.classEq A B)
      (synWa (.classMem (.cv x) (synCnnc)) (.classMem A (.cv x)))
      (synWa (.classMem (.cv x) (synCnnc)) (.classMem B (.cv x))) x
      freeVariableCertificate0 p0001
  have p0003 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfNcfin x A
      (by exact (show x ∉ (A).fv from (by exact fresh_x_not_A)))
  have p0004 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfNcfin x B
      (by exact (show x ∉ (B).fv from (by exact fresh_x_not_B)))
  have p0005 :=
    @gN3eqtr4g (.classEq A B)
      (synCio x (synWa (.classMem (.cv x) (synCnnc)) (.classMem A (.cv x))))
      (synCio x (synWa (.classMem (.cv x) (synCnnc)) (.classMem B (.cv x))))
      (synCncfin A) (synCncfin B) p0002 p0003 p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_ncfinprop`. -/
@[expose]
noncomputable def gNcfinprop (A : Class) (V : Class) :
    Nominal.NPrf
      (.imp (synWa (.classMem (synCvv) (synCfin)) (.classMem A V))
        (synWa (.classMem (synCncfin A) (synCnnc)) (.classMem A (synCncfin A)))) :=
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
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfNcfin x A
      (by exact (show x ∉ (A).fv from (by exact fresh_x_not_A)))
  have p0001 := @gVfinnc x A V (by exact (show x ∉ (A).fv from (by exact fresh_x_not_A)))
  have p0002 :=
    @gReiotacl (.classMem A (.cv x)) x (synCnnc)
      (by
        exact
          (show x ∉ ((synCnnc)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc];
              exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
  have p0003 :=
    @gSyl (synWa (.classMem A V) (.classMem (synCvv) (synCfin)))
      (synWreu x (synCnnc) (.classMem A (.cv x)))
      (.classMem (synCio x (synWa (.classMem (.cv x) (synCnnc)) (.classMem A (.cv x))))
        (synCnnc))
      p0001 p0002
  have p0004 :=
    @gSyl5eqel (synWa (.classMem A V) (.classMem (synCvv) (synCfin))) (synCncfin A)
      (synCio x (synWa (.classMem (.cv x) (synCnnc)) (.classMem A (.cv x)))) (synCnnc)
      p0000 p0003
  have p0005 :=
    @gEqcomi (synCncfin A)
      (synCio x (synWa (.classMem (.cv x) (synCnnc)) (.classMem A (.cv x)))) p0000
  have p0006 := @gEleq2 (.cv x) (synCncfin A) A
  have freeVariableCertificate0 : x ∉ ((Wff.classMem A (synCncfin A))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncfin, Finset.mem_union,
      fresh_x_not_A, or_false, not_false_eq_true]
  have p0007 :=
    @gReiota2 (.classMem A (.cv x)) (.classMem A (synCncfin A)) x (synCnnc)
      (synCncfin A)
      (by
        exact
          (show x ∉ ((synCnnc)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc];
              exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
      (by
        exact
          (show x ∉ ((synCncfin A)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncfin];
              exact (show x ∉ (A).fv from (by exact fresh_x_not_A)))))
      freeVariableCertificate0 p0006
  have p0008 :=
    @gSyl2anc (synWa (.classMem A V) (.classMem (synCvv) (synCfin)))
      (.classMem (synCncfin A) (synCnnc)) (synWreu x (synCnnc) (.classMem A (.cv x)))
      (synWb (.classMem A (synCncfin A)) (.classEq
          (synCio x (synWa (.classMem (.cv x) (synCnnc)) (.classMem A (.cv x))))
          (synCncfin A)))
      p0004 p0001 p0007
  have p0009 :=
    @gMpbiri (synWa (.classMem A V) (.classMem (synCvv) (synCfin)))
      (.classMem A (synCncfin A))
      (.classEq (synCio x (synWa (.classMem (.cv x) (synCnnc)) (.classMem A (.cv x))))
        (synCncfin A))
      p0005 p0008
  have p0010 :=
    @gJca (synWa (.classMem A V) (.classMem (synCvv) (synCfin)))
      (.classMem (synCncfin A) (synCnnc)) (.classMem A (synCncfin A)) p0004 p0009
  have p0011 :=
    @gAncoms (.classMem A V) (.classMem (synCvv) (synCfin))
      (synWa (.classMem (synCncfin A) (synCnnc)) (.classMem A (synCncfin A))) p0010
  exact p0011

/-- Checked nominal proof certificate identified upstream as `g_ncfindi`. -/
@[expose]
noncomputable def gNcfindi (A : Class) (B : Class) (V : Class) (W : Class) :
    Nominal.NPrf
      (.imp (synW3a (synWa (.classMem (synCvv) (synCfin)) (.classMem A V)) (.classMem B W)
          (.classEq (synCin A B) (synC0)))
        (.classEq (synCncfin (synCun A B)) (synCplc (synCncfin A) (synCncfin B)))) :=
  by
  have p0000 :=
    @gSimp1l (.classMem (synCvv) (synCfin)) (.classMem A V) (.classMem B W)
      (.classEq (synCin A B) (synC0))
  have p0001 :=
    @gSimp1r (.classMem (synCvv) (synCfin)) (.classMem A V) (.classMem B W)
      (.classEq (synCin A B) (synC0))
  have p0002 :=
    @gSimp2 (synWa (.classMem (synCvv) (synCfin)) (.classMem A V)) (.classMem B W)
      (.classEq (synCin A B) (synC0))
  have p0003 := @gUnexg A B V W
  have p0004 :=
    @gSyl2anc
      (synW3a (synWa (.classMem (synCvv) (synCfin)) (.classMem A V)) (.classMem B W)
        (.classEq (synCin A B) (synC0)))
      (.classMem A V) (.classMem B W) (.classMem (synCun A B) (synCvv)) p0001 p0002
      p0003
  have p0005 := @gNcfinprop (synCun A B) (synCvv)
  have p0006 :=
    @gSyl2anc
      (synW3a (synWa (.classMem (synCvv) (synCfin)) (.classMem A V)) (.classMem B W)
        (.classEq (synCin A B) (synC0)))
      (.classMem (synCvv) (synCfin)) (.classMem (synCun A B) (synCvv))
      (synWa (.classMem (synCncfin (synCun A B)) (synCnnc))
        (.classMem (synCun A B) (synCncfin (synCun A B))))
      p0000 p0004 p0005
  have p0007 :=
    @gSimpld
      (synW3a (synWa (.classMem (synCvv) (synCfin)) (.classMem A V)) (.classMem B W)
        (.classEq (synCin A B) (synC0)))
      (.classMem (synCncfin (synCun A B)) (synCnnc))
      (.classMem (synCun A B) (synCncfin (synCun A B))) p0006
  have p0008 := @gNcfinprop A V
  have p0009 :=
    @gSyl2anc
      (synW3a (synWa (.classMem (synCvv) (synCfin)) (.classMem A V)) (.classMem B W)
        (.classEq (synCin A B) (synC0)))
      (.classMem (synCvv) (synCfin)) (.classMem A V)
      (synWa (.classMem (synCncfin A) (synCnnc)) (.classMem A (synCncfin A))) p0000
      p0001 p0008
  have p0010 :=
    @gSimpld
      (synW3a (synWa (.classMem (synCvv) (synCfin)) (.classMem A V)) (.classMem B W)
        (.classEq (synCin A B) (synC0)))
      (.classMem (synCncfin A) (synCnnc)) (.classMem A (synCncfin A)) p0009
  have p0011 := @gNcfinprop B W
  have p0012 :=
    @gSyl2anc
      (synW3a (synWa (.classMem (synCvv) (synCfin)) (.classMem A V)) (.classMem B W)
        (.classEq (synCin A B) (synC0)))
      (.classMem (synCvv) (synCfin)) (.classMem B W)
      (synWa (.classMem (synCncfin B) (synCnnc)) (.classMem B (synCncfin B))) p0000
      p0002 p0011
  have p0013 :=
    @gSimpld
      (synW3a (synWa (.classMem (synCvv) (synCfin)) (.classMem A V)) (.classMem B W)
        (.classEq (synCin A B) (synC0)))
      (.classMem (synCncfin B) (synCnnc)) (.classMem B (synCncfin B)) p0012
  have p0014 := @gNncaddccl (synCncfin A) (synCncfin B)
  have p0015 :=
    @gSyl2anc
      (synW3a (synWa (.classMem (synCvv) (synCfin)) (.classMem A V)) (.classMem B W)
        (.classEq (synCin A B) (synC0)))
      (.classMem (synCncfin A) (synCnnc)) (.classMem (synCncfin B) (synCnnc))
      (.classMem (synCplc (synCncfin A) (synCncfin B)) (synCnnc)) p0010 p0013 p0014
  have p0016 :=
    @gSimprd
      (synW3a (synWa (.classMem (synCvv) (synCfin)) (.classMem A V)) (.classMem B W)
        (.classEq (synCin A B) (synC0)))
      (.classMem (synCncfin (synCun A B)) (synCnnc))
      (.classMem (synCun A B) (synCncfin (synCun A B))) p0006
  have p0017 :=
    @gSimprd
      (synW3a (synWa (.classMem (synCvv) (synCfin)) (.classMem A V)) (.classMem B W)
        (.classEq (synCin A B) (synC0)))
      (.classMem (synCncfin A) (synCnnc)) (.classMem A (synCncfin A)) p0009
  have p0018 :=
    @gSimprd
      (synW3a (synWa (.classMem (synCvv) (synCfin)) (.classMem A V)) (.classMem B W)
        (.classEq (synCin A B) (synC0)))
      (.classMem (synCncfin B) (synCnnc)) (.classMem B (synCncfin B)) p0012
  have p0019 :=
    @gSimp3 (synWa (.classMem (synCvv) (synCfin)) (.classMem A V)) (.classMem B W)
      (.classEq (synCin A B) (synC0))
  have p0020 := @gEladdci A B (synCncfin A) (synCncfin B)
  have p0021 :=
    @gSyl3anc
      (synW3a (synWa (.classMem (synCvv) (synCfin)) (.classMem A V)) (.classMem B W)
        (.classEq (synCin A B) (synC0)))
      (.classMem A (synCncfin A)) (.classMem B (synCncfin B))
      (.classEq (synCin A B) (synC0))
      (.classMem (synCun A B) (synCplc (synCncfin A) (synCncfin B))) p0017 p0018 p0019
      p0020
  have p0022 :=
    @gNnceleq (synCun A B) (synCncfin (synCun A B))
      (synCplc (synCncfin A) (synCncfin B))
  have p0023 :=
    @gSyl22anc
      (synW3a (synWa (.classMem (synCvv) (synCfin)) (.classMem A V)) (.classMem B W)
        (.classEq (synCin A B) (synC0)))
      (.classMem (synCncfin (synCun A B)) (synCnnc))
      (.classMem (synCplc (synCncfin A) (synCncfin B)) (synCnnc))
      (.classMem (synCun A B) (synCncfin (synCun A B)))
      (.classMem (synCun A B) (synCplc (synCncfin A) (synCncfin B)))
      (.classEq (synCncfin (synCun A B)) (synCplc (synCncfin A) (synCncfin B))) p0007
      p0015 p0016 p0021 p0022
  exact p0023

/-- Checked nominal proof certificate identified upstream as `g_ncfinsn`. -/
@[expose]
noncomputable def gNcfinsn (A : Class) (V : Class) :
    Nominal.NPrf
      (.imp (synWa (.classMem (synCvv) (synCfin)) (.classMem A V))
        (.classEq (synCncfin (synCsn A)) (synC1c))) :=
  by
  have p0000 := @gSnex A
  have p0001 := @gNcfinprop (synCsn A) (synCvv)
  have p0002 :=
    @gMpan2 (.classMem (synCvv) (synCfin)) (.classMem (synCsn A) (synCvv))
      (synWa (.classMem (synCncfin (synCsn A)) (synCnnc))
        (.classMem (synCsn A) (synCncfin (synCsn A))))
      p0000 p0001
  have p0003 :=
    @gAdantr (.classMem (synCvv) (synCfin))
      (synWa (.classMem (synCncfin (synCsn A)) (synCnnc))
        (.classMem (synCsn A) (synCncfin (synCsn A))))
      (.classMem A V) p0002
  have p0004 :=
    @gSimpld (synWa (.classMem (synCvv) (synCfin)) (.classMem A V))
      (.classMem (synCncfin (synCsn A)) (synCnnc))
      (.classMem (synCsn A) (synCncfin (synCsn A))) p0003
  have p0005 := @gN1cnnc
  have p0006 :=
    @gA1i (.classMem (synC1c) (synCnnc))
      (synWa (.classMem (synCvv) (synCfin)) (.classMem A V)) p0005
  have p0007 :=
    @gSimprd (synWa (.classMem (synCvv) (synCfin)) (.classMem A V))
      (.classMem (synCncfin (synCsn A)) (synCnnc))
      (.classMem (synCsn A) (synCncfin (synCsn A))) p0003
  have p0008 := @gSnel1cg A V
  have p0009 :=
    @gAdantl (.classMem A V) (.classMem (synCsn A) (synC1c))
      (.classMem (synCvv) (synCfin)) p0008
  have p0010 := @gNnceleq (synCsn A) (synCncfin (synCsn A)) (synC1c)
  have p0011 :=
    @gSyl22anc (synWa (.classMem (synCvv) (synCfin)) (.classMem A V))
      (.classMem (synCncfin (synCsn A)) (synCnnc)) (.classMem (synC1c) (synCnnc))
      (.classMem (synCsn A) (synCncfin (synCsn A))) (.classMem (synCsn A) (synC1c))
      (.classEq (synCncfin (synCsn A)) (synC1c)) p0004 p0006 p0007 p0009 p0010
  exact p0011

/-- Checked nominal proof certificate identified upstream as `g_eqpwrelk`. -/
@[expose]
noncomputable def gEqpwrelk (A : Class) (B : Class)
    (hyp_eqpwrelk_1 : Nominal.NPrf (.classMem A (synCvv)))
    (hyp_eqpwrelk_2 : Nominal.NPrf (.classMem B (synCvv))) :
    Nominal.NPrf
      (synWb (.classMem (synCopk (synCsn A) B) (synCcompl (synCimak
              (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCsik (synCssetk))))
              (synCpw1 (synCpw1 (synC1c)))))) (.classEq B (synCpw A))) :=
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
  have p0000 := @gOpkex (synCsn A) B
  have freeVariableCertificate0 :
    t ∉
      ((synCsymdif (synCins2k (synCssetk)) (synCins3k (synCsik (synCssetk))))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik, Finset.mem_union,
      Finset.notMem_empty, or_false, not_false_eq_true]
  have freeVariableCertificate1 : t ∉ ((synCpw1 (synCpw1 (synC1c)))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.notMem_empty,
      not_false_eq_true]
  have freeVariableCertificate2 : t ∉ ((synCopk (synCsn A) B)).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
      fresh_t_not_A, fresh_t_not_B, or_false, not_false_eq_true]
  have p0001 :=
    @gElimak t
      (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCsik (synCssetk))))
      (synCpw1 (synCpw1 (synC1c))) (synCopk (synCsn A) B) freeVariableCertificate0
      freeVariableCertificate1 freeVariableCertificate2 p0000
  have freeVariableCertificate3 : x ∉ ((Class.cv t)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_x_ne_t, not_false_eq_true]
  have p0002 := @gElpw121c x (.cv t) freeVariableCertificate3
  have p0003 :=
    @gAnbi1i (.classMem (.cv t) (synCpw1 (synCpw1 (synC1c))))
      (synWex x (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv x))))))
      (.classMem (synCopk (.cv t) (synCopk (synCsn A) B))
        (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCsik (synCssetk)))))
      p0002
  have freeVariableCertificate4 :
    x ∉
      ((Wff.classMem (synCopk (.cv t) (synCopk (synCsn A) B))
          (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCsik (synCssetk)))))).fv :=
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
    @gN1941v (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv x)))))
      (.classMem (synCopk (.cv t) (synCopk (synCsn A) B))
        (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCsik (synCssetk)))))
      x freeVariableCertificate4
  have p0005 :=
    @gBitr4i
      (synWa (.classMem (.cv t) (synCpw1 (synCpw1 (synC1c))))
        (.classMem (synCopk (.cv t) (synCopk (synCsn A) B))
          (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCsik (synCssetk))))))
      (synWa (synWex x (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv x))))))
        (.classMem (synCopk (.cv t) (synCopk (synCsn A) B))
          (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCsik (synCssetk))))))
      (synWex x (synWa (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv x)))))
          (.classMem (synCopk (.cv t) (synCopk (synCsn A) B))
            (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCsik (synCssetk)))))))
      p0003 p0004
  have p0006 :=
    @gExbii
      (synWa (.classMem (.cv t) (synCpw1 (synCpw1 (synC1c))))
        (.classMem (synCopk (.cv t) (synCopk (synCsn A) B))
          (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCsik (synCssetk))))))
      (synWex x (synWa (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv x)))))
          (.classMem (synCopk (.cv t) (synCopk (synCsn A) B))
            (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCsik (synCssetk)))))))
      t p0005
  have p0007 :=
    (Nominal.biimpRefl (synWrex t (synCpw1 (synCpw1 (synC1c)))
        (.classMem (synCopk (.cv t) (synCopk (synCsn A) B))
          (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCsik (synCssetk)))))))
  have p0008 :=
    @gExcom
      (synWa (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv x)))))
        (.classMem (synCopk (.cv t) (synCopk (synCsn A) B))
          (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCsik (synCssetk))))))
      x t
  have p0009 :=
    @gN3bitr4i
      (synWex t (synWa (.classMem (.cv t) (synCpw1 (synCpw1 (synC1c))))
          (.classMem (synCopk (.cv t) (synCopk (synCsn A) B))
            (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCsik (synCssetk)))))))
      (synWex t (synWex x (synWa (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv x)))))
            (.classMem (synCopk (.cv t) (synCopk (synCsn A) B))
              (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCsik (synCssetk))))))))
      (synWrex t (synCpw1 (synCpw1 (synC1c)))
        (.classMem (synCopk (.cv t) (synCopk (synCsn A) B))
          (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCsik (synCssetk))))))
      (synWex x (synWex t (synWa (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv x)))))
            (.classMem (synCopk (.cv t) (synCopk (synCsn A) B))
              (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCsik (synCssetk))))))))
      p0006 p0007 p0008
  have p0010 := @gSnex (synCsn (synCsn (.cv x)))
  have p0011 :=
    @gOpkeq1 (.cv t) (synCsn (synCsn (synCsn (.cv x)))) (synCopk (synCsn A) B)
  have p0012 :=
    @gEleq1d (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv x)))))
      (synCopk (.cv t) (synCopk (synCsn A) B))
      (synCopk (synCsn (synCsn (synCsn (.cv x)))) (synCopk (synCsn A) B))
      (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCsik (synCssetk)))) p0011
  have freeVariableCertificate5 : t ∉ ((synCsn (synCsn (synCsn (.cv x))))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_t_ne_x,
      not_false_eq_true]
  have freeVariableCertificate6 :
    t ∉
      ((Wff.classMem (synCopk (synCsn (synCsn (synCsn (.cv x)))) (synCopk (synCsn A) B))
          (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCsik (synCssetk)))))).fv :=
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
    @gCeqsexv
      (.classMem (synCopk (.cv t) (synCopk (synCsn A) B))
        (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCsik (synCssetk)))))
      (.classMem (synCopk (synCsn (synCsn (synCsn (.cv x)))) (synCopk (synCsn A) B))
        (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCsik (synCssetk)))))
      t (synCsn (synCsn (synCsn (.cv x)))) freeVariableCertificate5
      freeVariableCertificate6 p0010 p0012
  have p0014 :=
    @gElsymdif (synCopk (synCsn (synCsn (synCsn (.cv x)))) (synCopk (synCsn A) B))
      (synCins2k (synCssetk)) (synCins3k (synCsik (synCssetk)))
  have p0015 := @gSnex (.cv x)
  have p0016 := @gSnex A
  have p0017 :=
    @gOtkelins2k (synCsn (.cv x)) (synCsn A) B (synCssetk) p0015 p0016 hyp_eqpwrelk_2
  have p0018 := @gVex x
  have p0019 := @gElssetk (.cv x) B p0018 hyp_eqpwrelk_2
  have p0020 :=
    @gBitri
      (.classMem (synCopk (synCsn (synCsn (synCsn (.cv x)))) (synCopk (synCsn A) B))
        (synCins2k (synCssetk)))
      (.classMem (synCopk (synCsn (.cv x)) B) (synCssetk)) (.classMem (.cv x) B) p0017
      p0019
  have p0021 :=
    @gOtkelins3k (synCsn (.cv x)) (synCsn A) B (synCsik (synCssetk)) p0015 p0016
      hyp_eqpwrelk_2
  have p0022 := @gOpksnelsik (.cv x) A (synCssetk) p0018 hyp_eqpwrelk_1
  have p0023 := @gOpkelssetkg (.cv x) A (synCvv) (synCvv)
  have p0024 :=
    @gMp2an (.classMem (.cv x) (synCvv)) (.classMem A (synCvv))
      (synWb (.classMem (synCopk (.cv x) A) (synCssetk)) (synWss (.cv x) A)) p0018
      hyp_eqpwrelk_1 p0023
  have p0025 :=
    @gN3bitri
      (.classMem (synCopk (synCsn (synCsn (synCsn (.cv x)))) (synCopk (synCsn A) B))
        (synCins3k (synCsik (synCssetk))))
      (.classMem (synCopk (synCsn (.cv x)) (synCsn A)) (synCsik (synCssetk)))
      (.classMem (synCopk (.cv x) A) (synCssetk)) (synWss (.cv x) A) p0021 p0022 p0024
  have p0026 :=
    @gBibi12i
      (.classMem (synCopk (synCsn (synCsn (synCsn (.cv x)))) (synCopk (synCsn A) B))
        (synCins2k (synCssetk)))
      (.classMem (.cv x) B)
      (.classMem (synCopk (synCsn (synCsn (synCsn (.cv x)))) (synCopk (synCsn A) B))
        (synCins3k (synCsik (synCssetk))))
      (synWss (.cv x) A) p0020 p0025
  have p0027 :=
    @gNotbii
      (synWb (.classMem
          (synCopk (synCsn (synCsn (synCsn (.cv x)))) (synCopk (synCsn A) B))
          (synCins2k (synCssetk))) (.classMem
          (synCopk (synCsn (synCsn (synCsn (.cv x)))) (synCopk (synCsn A) B))
          (synCins3k (synCsik (synCssetk)))))
      (synWb (.classMem (.cv x) B) (synWss (.cv x) A)) p0026
  have p0028 :=
    @gN3bitri
      (synWex t (synWa (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv x)))))
          (.classMem (synCopk (.cv t) (synCopk (synCsn A) B))
            (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCsik (synCssetk)))))))
      (.classMem (synCopk (synCsn (synCsn (synCsn (.cv x)))) (synCopk (synCsn A) B))
        (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCsik (synCssetk)))))
      (.neg (synWb (.classMem
            (synCopk (synCsn (synCsn (synCsn (.cv x)))) (synCopk (synCsn A) B))
            (synCins2k (synCssetk))) (.classMem
            (synCopk (synCsn (synCsn (synCsn (.cv x)))) (synCopk (synCsn A) B))
            (synCins3k (synCsik (synCssetk))))))
      (.neg (synWb (.classMem (.cv x) B) (synWss (.cv x) A))) p0013 p0014 p0027
  have p0029 :=
    @gExbii
      (synWex t (synWa (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv x)))))
          (.classMem (synCopk (.cv t) (synCopk (synCsn A) B))
            (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCsik (synCssetk)))))))
      (.neg (synWb (.classMem (.cv x) B) (synWss (.cv x) A))) x p0028
  have p0030 :=
    @gN3bitri
      (.classMem (synCopk (synCsn A) B) (synCimak
          (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCsik (synCssetk))))
          (synCpw1 (synCpw1 (synC1c)))))
      (synWrex t (synCpw1 (synCpw1 (synC1c)))
        (.classMem (synCopk (.cv t) (synCopk (synCsn A) B))
          (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCsik (synCssetk))))))
      (synWex x (synWex t (synWa (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv x)))))
            (.classMem (synCopk (.cv t) (synCopk (synCsn A) B))
              (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCsik (synCssetk))))))))
      (synWex x (.neg (synWb (.classMem (.cv x) B) (synWss (.cv x) A)))) p0001 p0009
      p0029
  have p0031 :=
    @gNotbii
      (.classMem (synCopk (synCsn A) B) (synCimak
          (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCsik (synCssetk))))
          (synCpw1 (synCpw1 (synC1c)))))
      (synWex x (.neg (synWb (.classMem (.cv x) B) (synWss (.cv x) A)))) p0030
  have p0032 :=
    @gElcompl (synCopk (synCsn A) B)
      (synCimak (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCsik (synCssetk))))
        (synCpw1 (synCpw1 (synC1c))))
      p0000
  have p0033 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfPw x A
      (by exact (show x ∉ (A).fv from (by exact fresh_x_not_A)))
  have p0034 := @gEqeq2i (synCpw A) (.cab x (synWss (.cv x) A)) B p0033
  have p0035 :=
    @gEqabb (synWss (.cv x) A) x B
      (by exact (show x ∉ (B).fv from (by exact fresh_x_not_B)))
  have p0036 := @gAlex (synWb (.classMem (.cv x) B) (synWss (.cv x) A)) x
  have p0037 :=
    @gN3bitri (.classEq B (synCpw A)) (.classEq B (.cab x (synWss (.cv x) A)))
      (.all x (synWb (.classMem (.cv x) B) (synWss (.cv x) A)))
      (.neg (synWex x (.neg (synWb (.classMem (.cv x) B) (synWss (.cv x) A))))) p0034
      p0035 p0036
  have p0038 :=
    @gN3bitr4i
      (.neg (.classMem (synCopk (synCsn A) B) (synCimak
            (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCsik (synCssetk))))
            (synCpw1 (synCpw1 (synC1c))))))
      (.neg (synWex x (.neg (synWb (.classMem (.cv x) B) (synWss (.cv x) A)))))
      (.classMem (synCopk (synCsn A) B) (synCcompl (synCimak
            (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCsik (synCssetk))))
            (synCpw1 (synCpw1 (synC1c))))))
      (.classEq B (synCpw A)) p0031 p0032 p0037
  exact p0038

/-- Checked nominal proof certificate identified upstream as `g_eqpw1relk`. -/
@[expose]
noncomputable def gEqpw1relk (A : Class) (B : Class)
    (hyp_eqpw1relk_1 : Nominal.NPrf (.classMem A (synCvv)))
    (hyp_eqpw1relk_2 : Nominal.NPrf (.classMem B (synCvv))) :
    Nominal.NPrf
      (synWb (.classMem (synCopk A (synCsn B))
          (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak
              (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk))))
              (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (.classEq A (synCpw1 B))) :=
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
  have p0000 := @gSnex B
  have p0001 :=
    @gOpkelxpk A (synCsn B) (synCpw (synC1c)) (synCvv) hyp_eqpw1relk_1 p0000
  have p0002 :=
    @gMpbiran2
      (.classMem (synCopk A (synCsn B)) (synCxpk (synCpw (synC1c)) (synCvv)))
      (.classMem A (synCpw (synC1c))) (.classMem (synCsn B) (synCvv)) p0000 p0001
  have p0003 := @gElpw A (synC1c) hyp_eqpw1relk_1
  have p0004 :=
    @gBitri (.classMem (synCopk A (synCsn B)) (synCxpk (synCpw (synC1c)) (synCvv)))
      (.classMem A (synCpw (synC1c))) (synWss A (synC1c)) p0002 p0003
  have p0005 := @gOpkex A (synCsn B)
  have freeVariableCertificate0 :
    t ∉
      ((synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk))))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik, Finset.mem_union,
      Finset.notMem_empty, or_false, not_false_eq_true]
  have freeVariableCertificate1 : t ∉ ((synCpw1 (synCpw1 (synCpw1 (synC1c))))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.notMem_empty,
      not_false_eq_true]
  have freeVariableCertificate2 : t ∉ ((synCopk A (synCsn B))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
      fresh_t_not_A, fresh_t_not_B, or_false, not_false_eq_true]
  have p0006 :=
    @gElimak t
      (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk))))
      (synCpw1 (synCpw1 (synCpw1 (synC1c)))) (synCopk A (synCsn B))
      freeVariableCertificate0 freeVariableCertificate1 freeVariableCertificate2 p0005
  have freeVariableCertificate3 : x ∉ ((Class.cv t)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_x_ne_t, not_false_eq_true]
  have p0007 := @gElpw131c x (.cv t) freeVariableCertificate3
  have p0008 :=
    @gAnbi1i (.classMem (.cv t) (synCpw1 (synCpw1 (synCpw1 (synC1c)))))
      (synWex x (.classEq (.cv t) (synCsn (synCsn (synCsn (synCsn (.cv x)))))))
      (.classMem (synCopk (.cv t) (synCopk A (synCsn B)))
        (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk)))))
      p0007
  have freeVariableCertificate4 :
    x ∉
      ((Wff.classMem (synCopk (.cv t) (synCopk A (synCsn B)))
          (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk)))))).fv :=
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
    @gN1941v (.classEq (.cv t) (synCsn (synCsn (synCsn (synCsn (.cv x))))))
      (.classMem (synCopk (.cv t) (synCopk A (synCsn B)))
        (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk)))))
      x freeVariableCertificate4
  have p0010 :=
    @gBitr4i
      (synWa (.classMem (.cv t) (synCpw1 (synCpw1 (synCpw1 (synC1c)))))
        (.classMem (synCopk (.cv t) (synCopk A (synCsn B)))
          (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk))))))
      (synWa (synWex x (.classEq (.cv t) (synCsn (synCsn (synCsn (synCsn (.cv x)))))))
        (.classMem (synCopk (.cv t) (synCopk A (synCsn B)))
          (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk))))))
      (synWex x (synWa (.classEq (.cv t) (synCsn (synCsn (synCsn (synCsn (.cv x))))))
          (.classMem (synCopk (.cv t) (synCopk A (synCsn B)))
            (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk)))))))
      p0008 p0009
  have p0011 :=
    @gExbii
      (synWa (.classMem (.cv t) (synCpw1 (synCpw1 (synCpw1 (synC1c)))))
        (.classMem (synCopk (.cv t) (synCopk A (synCsn B)))
          (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk))))))
      (synWex x (synWa (.classEq (.cv t) (synCsn (synCsn (synCsn (synCsn (.cv x))))))
          (.classMem (synCopk (.cv t) (synCopk A (synCsn B)))
            (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk)))))))
      t p0010
  have p0012 :=
    (Nominal.biimpRefl (synWrex t (synCpw1 (synCpw1 (synCpw1 (synC1c))))
        (.classMem (synCopk (.cv t) (synCopk A (synCsn B)))
          (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk)))))))
  have p0013 :=
    @gExcom
      (synWa (.classEq (.cv t) (synCsn (synCsn (synCsn (synCsn (.cv x))))))
        (.classMem (synCopk (.cv t) (synCopk A (synCsn B)))
          (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk))))))
      x t
  have p0014 :=
    @gN3bitr4i
      (synWex t (synWa (.classMem (.cv t) (synCpw1 (synCpw1 (synCpw1 (synC1c)))))
          (.classMem (synCopk (.cv t) (synCopk A (synCsn B)))
            (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk)))))))
      (synWex t (synWex x
          (synWa (.classEq (.cv t) (synCsn (synCsn (synCsn (synCsn (.cv x))))))
            (.classMem (synCopk (.cv t) (synCopk A (synCsn B)))
              (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk))))))))
      (synWrex t (synCpw1 (synCpw1 (synCpw1 (synC1c))))
        (.classMem (synCopk (.cv t) (synCopk A (synCsn B)))
          (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk))))))
      (synWex x (synWex t
          (synWa (.classEq (.cv t) (synCsn (synCsn (synCsn (synCsn (.cv x))))))
            (.classMem (synCopk (.cv t) (synCopk A (synCsn B)))
              (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk))))))))
      p0011 p0012 p0013
  have p0015 :=
    @gBitri
      (.classMem (synCopk A (synCsn B)) (synCimak
          (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk))))
          (synCpw1 (synCpw1 (synCpw1 (synC1c))))))
      (synWrex t (synCpw1 (synCpw1 (synCpw1 (synC1c))))
        (.classMem (synCopk (.cv t) (synCopk A (synCsn B)))
          (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk))))))
      (synWex x (synWex t
          (synWa (.classEq (.cv t) (synCsn (synCsn (synCsn (synCsn (.cv x))))))
            (.classMem (synCopk (.cv t) (synCopk A (synCsn B)))
              (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk))))))))
      p0006 p0014
  have p0016 := @gSnex (synCsn (synCsn (synCsn (.cv x))))
  have p0017 :=
    @gOpkeq1 (.cv t) (synCsn (synCsn (synCsn (synCsn (.cv x)))))
      (synCopk A (synCsn B))
  have p0018 :=
    @gEleq1d (.classEq (.cv t) (synCsn (synCsn (synCsn (synCsn (.cv x))))))
      (synCopk (.cv t) (synCopk A (synCsn B)))
      (synCopk (synCsn (synCsn (synCsn (synCsn (.cv x))))) (synCopk A (synCsn B)))
      (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk)))) p0017
  have freeVariableCertificate5 :
    t ∉ ((synCsn (synCsn (synCsn (synCsn (.cv x)))))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_t_ne_x,
      not_false_eq_true]
  have freeVariableCertificate6 :
    t ∉
      ((Wff.classMem (synCopk (synCsn (synCsn (synCsn (synCsn (.cv x)))))
            (synCopk A (synCsn B))) (synCsymdif (synCins3k (synCssetk))
            (synCins2k (synCsik (synCssetk)))))).fv :=
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
    @gCeqsexv
      (.classMem (synCopk (.cv t) (synCopk A (synCsn B)))
        (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk)))))
      (.classMem (synCopk (synCsn (synCsn (synCsn (synCsn (.cv x)))))
          (synCopk A (synCsn B)))
        (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk)))))
      t (synCsn (synCsn (synCsn (synCsn (.cv x))))) freeVariableCertificate5
      freeVariableCertificate6 p0016 p0018
  have p0020 :=
    @gElsymdif
      (synCopk (synCsn (synCsn (synCsn (synCsn (.cv x))))) (synCopk A (synCsn B)))
      (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk)))
  have p0021 := @gSnex (synCsn (.cv x))
  have p0022 :=
    @gOtkelins3k (synCsn (synCsn (.cv x))) A (synCsn B) (synCssetk) p0021
      hyp_eqpw1relk_1 p0000
  have p0023 := @gSnex (.cv x)
  have p0024 := @gElssetk (synCsn (.cv x)) A p0023 hyp_eqpw1relk_1
  have p0025 :=
    @gBitri
      (.classMem (synCopk (synCsn (synCsn (synCsn (synCsn (.cv x)))))
          (synCopk A (synCsn B))) (synCins3k (synCssetk)))
      (.classMem (synCopk (synCsn (synCsn (.cv x))) A) (synCssetk))
      (.classMem (synCsn (.cv x)) A) p0022 p0024
  have p0026 :=
    @gOtkelins2k (synCsn (synCsn (.cv x))) A (synCsn B) (synCsik (synCssetk)) p0021
      hyp_eqpw1relk_1 p0000
  have p0027 := @gOpksnelsik (synCsn (.cv x)) B (synCssetk) p0023 hyp_eqpw1relk_2
  have p0028 := @gVex x
  have p0029 := @gElssetk (.cv x) B p0028 hyp_eqpw1relk_2
  have p0030 :=
    @gBitri
      (.classMem (synCopk (synCsn (synCsn (.cv x))) (synCsn B)) (synCsik (synCssetk)))
      (.classMem (synCopk (synCsn (.cv x)) B) (synCssetk)) (.classMem (.cv x) B) p0027
      p0029
  have p0031 :=
    @gBitri
      (.classMem (synCopk (synCsn (synCsn (synCsn (synCsn (.cv x)))))
          (synCopk A (synCsn B))) (synCins2k (synCsik (synCssetk))))
      (.classMem (synCopk (synCsn (synCsn (.cv x))) (synCsn B)) (synCsik (synCssetk)))
      (.classMem (.cv x) B) p0026 p0030
  have p0032 :=
    @gBibi12i
      (.classMem (synCopk (synCsn (synCsn (synCsn (synCsn (.cv x)))))
          (synCopk A (synCsn B))) (synCins3k (synCssetk)))
      (.classMem (synCsn (.cv x)) A)
      (.classMem (synCopk (synCsn (synCsn (synCsn (synCsn (.cv x)))))
          (synCopk A (synCsn B))) (synCins2k (synCsik (synCssetk))))
      (.classMem (.cv x) B) p0025 p0031
  have p0033 :=
    @gXchbinx
      (.classMem (synCopk (synCsn (synCsn (synCsn (synCsn (.cv x)))))
          (synCopk A (synCsn B)))
        (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk)))))
      (synWb (.classMem (synCopk (synCsn (synCsn (synCsn (synCsn (.cv x)))))
            (synCopk A (synCsn B))) (synCins3k (synCssetk))) (.classMem
          (synCopk (synCsn (synCsn (synCsn (synCsn (.cv x))))) (synCopk A (synCsn B)))
          (synCins2k (synCsik (synCssetk)))))
      (synWb (.classMem (synCsn (.cv x)) A) (.classMem (.cv x) B)) p0020 p0032
  have p0034 :=
    @gBitri
      (synWex t (synWa (.classEq (.cv t) (synCsn (synCsn (synCsn (synCsn (.cv x))))))
          (.classMem (synCopk (.cv t) (synCopk A (synCsn B)))
            (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk)))))))
      (.classMem (synCopk (synCsn (synCsn (synCsn (synCsn (.cv x)))))
          (synCopk A (synCsn B)))
        (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk)))))
      (.neg (synWb (.classMem (synCsn (.cv x)) A) (.classMem (.cv x) B))) p0019 p0033
  have p0035 :=
    @gExbii
      (synWex t (synWa (.classEq (.cv t) (synCsn (synCsn (synCsn (synCsn (.cv x))))))
          (.classMem (synCopk (.cv t) (synCopk A (synCsn B)))
            (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk)))))))
      (.neg (synWb (.classMem (synCsn (.cv x)) A) (.classMem (.cv x) B))) x p0034
  have p0036 := @gExnal (synWb (.classMem (synCsn (.cv x)) A) (.classMem (.cv x) B)) x
  have p0037 :=
    @gN3bitrri
      (.classMem (synCopk A (synCsn B)) (synCimak
          (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk))))
          (synCpw1 (synCpw1 (synCpw1 (synC1c))))))
      (synWex x (synWex t
          (synWa (.classEq (.cv t) (synCsn (synCsn (synCsn (synCsn (.cv x))))))
            (.classMem (synCopk (.cv t) (synCopk A (synCsn B)))
              (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk))))))))
      (synWex x (.neg (synWb (.classMem (synCsn (.cv x)) A) (.classMem (.cv x) B))))
      (.neg (.all x (synWb (.classMem (synCsn (.cv x)) A) (.classMem (.cv x) B)))) p0015
      p0035 p0036
  have p0038 :=
    @gCon1bii (.all x (synWb (.classMem (synCsn (.cv x)) A) (.classMem (.cv x) B)))
      (.classMem (synCopk A (synCsn B)) (synCimak
          (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk))))
          (synCpw1 (synCpw1 (synCpw1 (synC1c))))))
      p0037
  have p0039 :=
    @gAnbi12i
      (.classMem (synCopk A (synCsn B)) (synCxpk (synCpw (synC1c)) (synCvv)))
      (synWss A (synC1c))
      (.neg (.classMem (synCopk A (synCsn B)) (synCimak
            (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk))))
            (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
      (.all x (synWb (.classMem (synCsn (.cv x)) A) (.classMem (.cv x) B))) p0004 p0038
  have p0040 :=
    @gEldif (synCopk A (synCsn B)) (synCxpk (synCpw (synC1c)) (synCvv))
      (synCimak (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk))))
        (synCpw1 (synCpw1 (synCpw1 (synC1c)))))
  have p0041 :=
    @gEqpw1 x A B (by exact (show x ∉ (A).fv from (by exact fresh_x_not_A)))
      (by exact (show x ∉ (B).fv from (by exact fresh_x_not_B)))
  have p0042 :=
    @gN3bitr4i
      (synWa (.classMem (synCopk A (synCsn B)) (synCxpk (synCpw (synC1c)) (synCvv)))
        (.neg (.classMem (synCopk A (synCsn B)) (synCimak
              (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk))))
              (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
      (synWa (synWss A (synC1c))
        (.all x (synWb (.classMem (synCsn (.cv x)) A) (.classMem (.cv x) B))))
      (.classMem (synCopk A (synCsn B)) (synCdif (synCxpk (synCpw (synC1c)) (synCvv))
          (synCimak
            (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk))))
            (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
      (.classEq A (synCpw1 B)) p0039 p0040 p0041
  exact p0042


end NFChoice.DirectNominalPrf.WPPReplay

end
