/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NominalWPPReplayChunk009StructuralBlock006

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NominalWPPReplayChunk009StructuralPart035`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_nndisjeq`. -/
@[expose]
noncomputable def gNndisjeq (M : Class) (N : Class) :
    Nominal.NPrf
      (.imp (synWa (.classMem M (synCnnc)) (.classMem N (synCnnc)))
        (synWo (.classEq (synCin M N) (synC0)) (.classEq M N))) :=
  by
  let proofSupport : Finset Var := M.fv ∪ N.fv
  let n : Var := freshVar proofSupport 0
  let p : Var := freshVar proofSupport 1
  let m : Var := freshVar proofSupport 2
  let q : Var := freshVar proofSupport 3
  let a : Var := freshVar proofSupport 4
  let b : Var := freshVar proofSupport 5
  let x : Var := freshVar proofSupport 6
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
  have fresh_p : p ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_p_not_M : p ∉ M.fv := by
    intro h
    exact fresh_p (Finset.mem_union_left _ (h))
  have fresh_n_ne_p : n ≠ p :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_p_ne_n : p ≠ n := Ne.symm fresh_n_ne_p
  have fresh_n_ne_m : n ≠ m :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_m_ne_n : m ≠ n := Ne.symm fresh_n_ne_m
  have fresh_n_ne_q : n ≠ q :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_q_ne_n : q ≠ n := Ne.symm fresh_n_ne_q
  have fresh_n_ne_a : n ≠ a :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 0) (j := 4) (by decide)
  have fresh_a_ne_n : a ≠ n := Ne.symm fresh_n_ne_a
  have fresh_n_ne_b : n ≠ b :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 0) (j := 5) (by decide)
  have fresh_b_ne_n : b ≠ n := Ne.symm fresh_n_ne_b
  have fresh_n_ne_x : n ≠ x :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 0) (j := 6) (by decide)
  have fresh_x_ne_n : x ≠ n := Ne.symm fresh_n_ne_x
  have fresh_p_ne_m : p ≠ m :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_m_ne_p : m ≠ p := Ne.symm fresh_p_ne_m
  have fresh_p_ne_q : p ≠ q :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_q_ne_p : q ≠ p := Ne.symm fresh_p_ne_q
  have fresh_p_ne_b : p ≠ b :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 1) (j := 5) (by decide)
  have fresh_p_ne_x : p ≠ x :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 1) (j := 6) (by decide)
  have fresh_m_ne_q : m ≠ q :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_q_ne_m : q ≠ m := Ne.symm fresh_m_ne_q
  have fresh_m_ne_a : m ≠ a :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 2) (j := 4) (by decide)
  have fresh_a_ne_m : a ≠ m := Ne.symm fresh_m_ne_a
  have fresh_m_ne_b : m ≠ b :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 2) (j := 5) (by decide)
  have fresh_b_ne_m : b ≠ m := Ne.symm fresh_m_ne_b
  have fresh_m_ne_x : m ≠ x :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 2) (j := 6) (by decide)
  have fresh_x_ne_m : x ≠ m := Ne.symm fresh_m_ne_x
  have fresh_q_ne_a : q ≠ a :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 3) (j := 4) (by decide)
  have fresh_a_ne_q : a ≠ q := Ne.symm fresh_q_ne_a
  have fresh_q_ne_b : q ≠ b :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 3) (j := 5) (by decide)
  have fresh_b_ne_q : b ≠ q := Ne.symm fresh_q_ne_b
  have fresh_q_ne_x : q ≠ x :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 3) (j := 6) (by decide)
  have fresh_x_ne_q : x ≠ q := Ne.symm fresh_q_ne_x
  have fresh_a_ne_b : a ≠ b :=
    by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 4) (j := 5) (by decide)
  have fresh_b_ne_a : b ≠ a := Ne.symm fresh_a_ne_b
  have fresh_a_ne_x : a ≠ x :=
    by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 4) (j := 6) (by decide)
  have fresh_x_ne_a : x ≠ a := Ne.symm fresh_a_ne_x
  have fresh_b_ne_x : b ≠ x :=
    by
    change freshVar proofSupport 5 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 5) (j := 6) (by decide)
  have p0000 := @gVex p
  have p0001 :=
    @gElcompl (.cv p)
      (synCimak (synCcompl (synCun (synCcompl
              (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                (synCpw1 (synCpw1 (synC1c))))) (synCidk))) (synCnnc))
      p0000
  have freeVariableCertificate0 :
    n ∉
      ((synCcompl (synCun (synCcompl
              (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                (synCpw1 (synCpw1 (synC1c))))) (synCidk)))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cidk, Finset.mem_union,
      Finset.notMem_empty, or_false, not_false_eq_true]
  have freeVariableCertificate1 : n ∉ ((Class.cv p)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_n_ne_p, not_false_eq_true]
  have p0002 :=
    @gElimak n
      (synCcompl (synCun (synCcompl
            (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
              (synCpw1 (synCpw1 (synC1c))))) (synCidk)))
      (synCnnc) (.cv p) freeVariableCertificate0
      (by
        exact
          (show n ∉ ((synCnnc)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc];
              exact (show n ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
      freeVariableCertificate1 p0000
  have p0003 := @gOpkex (.cv n) (.cv p)
  have p0004 :=
    @gElcompl (synCopk (.cv n) (.cv p))
      (synCun (synCcompl
          (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
            (synCpw1 (synCpw1 (synC1c))))) (synCidk))
      p0003
  have p0005 :=
    @gElun (synCopk (.cv n) (.cv p))
      (synCcompl (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
          (synCpw1 (synCpw1 (synC1c)))))
      (synCidk)
  have p0006 := @gVex n
  have p0007 := @gNdisjrelk (.cv n) (.cv p) p0006 p0000
  have p0008 :=
    @gNotbii
      (.classMem (synCopk (.cv n) (.cv p))
        (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
          (synCpw1 (synCpw1 (synC1c)))))
      (synWne (synCin (.cv n) (.cv p)) (synC0)) p0007
  have p0009 :=
    @gElcompl (synCopk (.cv n) (.cv p))
      (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
        (synCpw1 (synCpw1 (synC1c))))
      p0003
  have p0010 := (Nominal.biimpRefl (synWne (synCin (.cv n) (.cv p)) (synC0)))
  have p0011 :=
    @gCon2bii (synWne (synCin (.cv n) (.cv p)) (synC0))
      (.classEq (synCin (.cv n) (.cv p)) (synC0)) p0010
  have p0012 :=
    @gN3bitr4i
      (.neg (.classMem (synCopk (.cv n) (.cv p))
          (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
            (synCpw1 (synCpw1 (synC1c))))))
      (.neg (synWne (synCin (.cv n) (.cv p)) (synC0)))
      (.classMem (synCopk (.cv n) (.cv p)) (synCcompl
          (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
            (synCpw1 (synCpw1 (synC1c))))))
      (.classEq (synCin (.cv n) (.cv p)) (synC0)) p0008 p0009 p0011
  have p0013 := @gOpkelidkg (.cv n) (.cv p) (synCvv) (synCvv)
  have p0014_e02_recanon :
    Nominal.NPrf
      (.imp (synWa (.classMem (.cv n) (synCvv)) (.classMem (.cv p) (synCvv)))
        (synWb (.classMem (synCopk (.cv n) (.cv p)) (synCidk)) (.objEq n p))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWa synCvv synWb synCopk synCpr synCun synCnin synWnan synCcompl
          synCsn synCidk synWex
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0013
  have p0014 :=
    @gMp2an (.classMem (.cv n) (synCvv)) (.classMem (.cv p) (synCvv))
      (synWb (.classMem (synCopk (.cv n) (.cv p)) (synCidk)) (.objEq n p)) p0006 p0000
      p0014_e02_recanon
  have p0015 :=
    @gOrbi12i
      (.classMem (synCopk (.cv n) (.cv p)) (synCcompl
          (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
            (synCpw1 (synCpw1 (synC1c))))))
      (.classEq (synCin (.cv n) (.cv p)) (synC0))
      (.classMem (synCopk (.cv n) (.cv p)) (synCidk)) (.objEq n p) p0012 p0014
  have p0016 := @gIncom (.cv n) (.cv p)
  have p0017 :=
    @gEqeq1i (synCin (.cv n) (.cv p)) (synCin (.cv p) (.cv n)) (synC0) p0016
  have p0018 := @gEqcom (.cv n) (.cv p)
  have p0019_e01_recanon : Nominal.NPrf (synWb (.objEq n p) (.objEq p n)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _)
      p0018
  have p0019 :=
    @gOrbi12i (.classEq (synCin (.cv n) (.cv p)) (synC0))
      (.classEq (synCin (.cv p) (.cv n)) (synC0)) (.objEq n p) (.objEq p n) p0017
      p0019_e01_recanon
  have p0020 :=
    @gN3bitri
      (.classMem (synCopk (.cv n) (.cv p)) (synCun (synCcompl
            (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
              (synCpw1 (synCpw1 (synC1c))))) (synCidk)))
      (synWo (.classMem (synCopk (.cv n) (.cv p)) (synCcompl
            (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
              (synCpw1 (synCpw1 (synC1c))))))
        (.classMem (synCopk (.cv n) (.cv p)) (synCidk)))
      (synWo (.classEq (synCin (.cv n) (.cv p)) (synC0)) (.objEq n p))
      (synWo (.classEq (synCin (.cv p) (.cv n)) (synC0)) (.objEq p n)) p0005 p0015
      p0019
  have p0021 :=
    @gXchbinx
      (.classMem (synCopk (.cv n) (.cv p)) (synCcompl (synCun (synCcompl
              (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                (synCpw1 (synCpw1 (synC1c))))) (synCidk))))
      (.classMem (synCopk (.cv n) (.cv p)) (synCun (synCcompl
            (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
              (synCpw1 (synCpw1 (synC1c))))) (synCidk)))
      (synWo (.classEq (synCin (.cv p) (.cv n)) (synC0)) (.objEq p n)) p0004 p0020
  have p0022 :=
    @gRexbii
      (.classMem (synCopk (.cv n) (.cv p)) (synCcompl (synCun (synCcompl
              (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                (synCpw1 (synCpw1 (synC1c))))) (synCidk))))
      (.neg (synWo (.classEq (synCin (.cv p) (.cv n)) (synC0)) (.objEq p n))) n
      (synCnnc) p0021
  have p0023 :=
    @gRexnal (synWo (.classEq (synCin (.cv p) (.cv n)) (synC0)) (.objEq p n)) n
      (synCnnc)
  have p0024 :=
    @gN3bitri
      (.classMem (.cv p) (synCimak (synCcompl (synCun (synCcompl
                (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                  (synCpw1 (synCpw1 (synC1c))))) (synCidk))) (synCnnc)))
      (synWrex n (synCnnc) (.classMem (synCopk (.cv n) (.cv p)) (synCcompl (synCun
              (synCcompl
                (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                  (synCpw1 (synCpw1 (synC1c))))) (synCidk)))))
      (synWrex n (synCnnc)
        (.neg (synWo (.classEq (synCin (.cv p) (.cv n)) (synC0)) (.objEq p n))))
      (.neg (synWral n (synCnnc)
          (synWo (.classEq (synCin (.cv p) (.cv n)) (synC0)) (.objEq p n))))
      p0002 p0022 p0023
  have p0025 :=
    @gCon2bii
      (.classMem (.cv p) (synCimak (synCcompl (synCun (synCcompl
                (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                  (synCpw1 (synCpw1 (synC1c))))) (synCidk))) (synCnnc)))
      (synWral n (synCnnc)
        (synWo (.classEq (synCin (.cv p) (.cv n)) (synC0)) (.objEq p n)))
      p0024
  have p0026 :=
    @gBitr4i
      (.classMem (.cv p) (synCcompl (synCimak (synCcompl (synCun (synCcompl
                  (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                    (synCpw1 (synCpw1 (synC1c))))) (synCidk))) (synCnnc))))
      (.neg (.classMem (.cv p) (synCimak (synCcompl (synCun (synCcompl
                  (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                    (synCpw1 (synCpw1 (synC1c))))) (synCidk))) (synCnnc))))
      (synWral n (synCnnc)
        (synWo (.classEq (synCin (.cv p) (.cv n)) (synC0)) (.objEq p n)))
      p0001 p0025
  have freeVariableCertificate2 :
    p ∉
      ((synCcompl (synCimak (synCcompl (synCun (synCcompl
                  (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                    (synCpw1 (synCpw1 (synC1c))))) (synCidk))) (synCnnc)))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cidk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union,
      Finset.notMem_empty, or_false, not_false_eq_true]
  have p0027 :=
    @gEqabi
      (synWral n (synCnnc)
        (synWo (.classEq (synCin (.cv p) (.cv n)) (synC0)) (.objEq p n)))
      p
      (synCcompl (synCimak (synCcompl (synCun (synCcompl
                (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                  (synCpw1 (synCpw1 (synC1c))))) (synCidk))) (synCnnc)))
      freeVariableCertificate2 p0026
  have p0028 := @gSsetkex
  have p0029 := @gIns3kex (synCssetk) p0028
  have p0031 := @gIns2kex (synCssetk) p0028
  have p0032 := @gInex (synCins3k (synCssetk)) (synCins2k (synCssetk)) p0029 p0031
  have p0033 := @gN1cex
  have p0034 := @gPw1ex (synC1c) p0033
  have p0035 := @gPw1ex (synCpw1 (synC1c)) p0034
  have p0036 :=
    @gImakex (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
      (synCpw1 (synCpw1 (synC1c))) p0032 p0035
  have p0037 :=
    @gComplex
      (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
        (synCpw1 (synCpw1 (synC1c))))
      p0036
  have p0038 := @gIdkex
  have p0039 :=
    @gUnex
      (synCcompl (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
          (synCpw1 (synCpw1 (synC1c)))))
      (synCidk) p0037 p0038
  have p0040 :=
    @gComplex
      (synCun (synCcompl
          (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
            (synCpw1 (synCpw1 (synC1c))))) (synCidk))
      p0039
  have p0041 := @gNncex
  have p0042 :=
    @gImakex
      (synCcompl (synCun (synCcompl
            (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
              (synCpw1 (synCpw1 (synC1c))))) (synCidk)))
      (synCnnc) p0040 p0041
  have p0043 :=
    @gComplex
      (synCimak (synCcompl (synCun (synCcompl
              (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                (synCpw1 (synCpw1 (synC1c))))) (synCidk))) (synCnnc))
      p0042
  have p0044 :=
    @gEqeltrri
      (synCcompl (synCimak (synCcompl (synCun (synCcompl
                (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                  (synCpw1 (synCpw1 (synC1c))))) (synCidk))) (synCnnc)))
      (.cab p (synWral n (synCnnc)
          (synWo (.classEq (synCin (.cv p) (.cv n)) (synC0)) (.objEq p n))))
      (synCvv) p0027 p0043
  have p0045 := (Nominal.classEqRefl (synC0c))
  have p0046 := @gEqeq2i (synC0c) (synCsn (synC0)) (.cv p) p0045
  have p0047 :=
    @gBiimpi (.classEq (.cv p) (synC0c)) (.classEq (.cv p) (synCsn (synC0))) p0046
  have p0048 :=
    @gIneq1d (.classEq (.cv p) (synC0c)) (.cv p) (synCsn (synC0)) (.cv n) p0047
  have p0049 :=
    @gEqeq1d (.classEq (.cv p) (synC0c)) (synCin (.cv p) (.cv n))
      (synCin (synCsn (synC0)) (.cv n)) (synC0) p0048
  have p0050 := @gIncom (synCsn (synC0)) (.cv n)
  have p0051 :=
    @gEqeq1i (synCin (synCsn (synC0)) (.cv n)) (synCin (.cv n) (synCsn (synC0)))
      (synC0) p0050
  have p0052 := @gDisjsn (.cv n) (synC0)
  have p0053 :=
    @gBitri (.classEq (synCin (synCsn (synC0)) (.cv n)) (synC0))
      (.classEq (synCin (.cv n) (synCsn (synC0))) (synC0))
      (.neg (.classMem (synC0) (.cv n))) p0051 p0052
  have p0054 :=
    @gSyl6bb (.classEq (.cv p) (synC0c)) (.classEq (synCin (.cv p) (.cv n)) (synC0))
      (.classEq (synCin (synCsn (synC0)) (.cv n)) (synC0))
      (.neg (.classMem (synC0) (.cv n))) p0049 p0053
  have p0055 := @gEqeq1 (.cv p) (synC0c) (.cv n)
  have p0056 := @gEqcom (synC0c) (.cv n)
  have p0057_e00_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv p) (synC0c)) (synWb (.objEq p n) (.classEq (synC0c) (.cv n)))) :=
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
      p0055
  have p0057 :=
    @gSyl6bb (.classEq (.cv p) (synC0c)) (.objEq p n) (.classEq (synC0c) (.cv n))
      (.classEq (.cv n) (synC0c)) p0057_e00_recanon p0056
  have p0058 :=
    @gOrbi12d (.classEq (.cv p) (synC0c)) (.classEq (synCin (.cv p) (.cv n)) (synC0))
      (.neg (.classMem (synC0) (.cv n))) (.objEq p n) (.classEq (.cv n) (synC0c)) p0054
      p0057
  have freeVariableCertificate3 : n ∉ ((Wff.classEq (.cv p) (synC0c))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_n_ne_p, or_false,
      not_false_eq_true]
  have p0059 :=
    @gRalbidv (.classEq (.cv p) (synC0c))
      (synWo (.classEq (synCin (.cv p) (.cv n)) (synC0)) (.objEq p n))
      (synWo (.neg (.classMem (synC0) (.cv n))) (.classEq (.cv n) (synC0c))) n
      (synCnnc) freeVariableCertificate3 p0058
  have p0060 := @gIneq1 (.cv p) (.cv m) (.cv n)
  have p0061_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq p m) (.classEq (synCin (.cv p) (.cv n)) (synCin (.cv m) (.cv n)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synCin synCcompl synCnin synWnan synWa
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0060
  have p0061 :=
    @gEqeq1d (.objEq p m) (synCin (.cv p) (.cv n)) (synCin (.cv m) (.cv n)) (synC0)
      p0061_e00_recanon
  have p0062 := @gEqeq1 (.cv p) (.cv m) (.cv n)
  have p0063_e01_recanon :
    Nominal.NPrf (.imp (.objEq p m) (synWb (.objEq p n) (.objEq m n))) :=
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
      p0062
  have p0063 :=
    @gOrbi12d (.objEq p m) (.classEq (synCin (.cv p) (.cv n)) (synC0))
      (.classEq (synCin (.cv m) (.cv n)) (synC0)) (.objEq p n) (.objEq m n) p0061
      p0063_e01_recanon
  have freeVariableCertificate4 : n ∉ ((Wff.objEq p m)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_insert,
      Finset.mem_singleton, fresh_n_ne_p, fresh_n_ne_m, or_false, not_false_eq_true]
  have p0064 :=
    @gRalbidv (.objEq p m)
      (synWo (.classEq (synCin (.cv p) (.cv n)) (synC0)) (.objEq p n))
      (synWo (.classEq (synCin (.cv m) (.cv n)) (synC0)) (.objEq m n)) n (synCnnc)
      freeVariableCertificate4 p0063
  have p0065 := @gIneq2 (.cv n) (.cv q) (.cv m)
  have p0066_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq n q) (.classEq (synCin (.cv m) (.cv n)) (synCin (.cv m) (.cv q)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synCin synCcompl synCnin synWnan synWa
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0065
  have p0066 :=
    @gEqeq1d (.objEq n q) (synCin (.cv m) (.cv n)) (synCin (.cv m) (.cv q)) (synC0)
      p0066_e00_recanon
  have p0067 := @gEquequ2 n q m
  have p0068 :=
    @gOrbi12d (.objEq n q) (.classEq (synCin (.cv m) (.cv n)) (synC0))
      (.classEq (synCin (.cv m) (.cv q)) (synC0)) (.objEq m n) (.objEq m q) p0066 p0067
  have freeVariableCertificate5 :
    q ∉ ((synWo (.classEq (synCin (.cv m) (.cv n)) (synC0)) (.objEq m n))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wo,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
      NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_union, Finset.mem_insert,
      Finset.mem_singleton, Finset.notMem_empty, fresh_q_ne_m, fresh_q_ne_n, or_false,
      not_false_eq_true]
  have freeVariableCertificate6 :
    n ∉ ((synWo (.classEq (synCin (.cv m) (.cv q)) (synC0)) (.objEq m q))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wo,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
      NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_union, Finset.mem_insert,
      Finset.mem_singleton, Finset.notMem_empty, fresh_n_ne_m, fresh_n_ne_q, or_false,
      not_false_eq_true]
  have p0069 :=
    @gCbvralv (synWo (.classEq (synCin (.cv m) (.cv n)) (synC0)) (.objEq m n))
      (synWo (.classEq (synCin (.cv m) (.cv q)) (synC0)) (.objEq m q)) n q (synCnnc)
      (by
        exact
          (show n ∉ ((synCnnc)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc];
              exact (show n ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
      (by
        exact
          (show q ∉ ((synCnnc)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc];
              exact (show q ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
      freeVariableCertificate5 freeVariableCertificate6 p0068
  have p0070 :=
    @gSyl6bb (.objEq p m)
      (synWral n (synCnnc)
        (synWo (.classEq (synCin (.cv p) (.cv n)) (synC0)) (.objEq p n)))
      (synWral n (synCnnc)
        (synWo (.classEq (synCin (.cv m) (.cv n)) (synC0)) (.objEq m n)))
      (synWral q (synCnnc)
        (synWo (.classEq (synCin (.cv m) (.cv q)) (synC0)) (.objEq m q)))
      p0064 p0069
  have p0071 := @gIneq1 (.cv p) (synCplc (.cv m) (synC1c)) (.cv n)
  have p0072 :=
    @gEqeq1d (.classEq (.cv p) (synCplc (.cv m) (synC1c))) (synCin (.cv p) (.cv n))
      (synCin (synCplc (.cv m) (synC1c)) (.cv n)) (synC0) p0071
  have p0073 := @gEqeq1 (.cv p) (synCplc (.cv m) (synC1c)) (.cv n)
  have p0074_e01_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv p) (synCplc (.cv m) (synC1c)))
        (synWb (.objEq p n) (.classEq (synCplc (.cv m) (synC1c)) (.cv n)))) :=
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
      p0073
  have p0074 :=
    @gOrbi12d (.classEq (.cv p) (synCplc (.cv m) (synC1c)))
      (.classEq (synCin (.cv p) (.cv n)) (synC0))
      (.classEq (synCin (synCplc (.cv m) (synC1c)) (.cv n)) (synC0)) (.objEq p n)
      (.classEq (synCplc (.cv m) (synC1c)) (.cv n)) p0072 p0074_e01_recanon
  have freeVariableCertificate7 :
    n ∉ ((Wff.classEq (.cv p) (synCplc (.cv m) (synC1c)))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_n_ne_p, fresh_n_ne_m, or_false,
      not_false_eq_true]
  have p0075 :=
    @gRalbidv (.classEq (.cv p) (synCplc (.cv m) (synC1c)))
      (synWo (.classEq (synCin (.cv p) (.cv n)) (synC0)) (.objEq p n))
      (synWo (.classEq (synCin (synCplc (.cv m) (synC1c)) (.cv n)) (synC0))
        (.classEq (synCplc (.cv m) (synC1c)) (.cv n)))
      n (synCnnc) freeVariableCertificate7 p0074
  have p0076 := @gIneq1 (.cv p) M (.cv n)
  have p0077 :=
    @gEqeq1d (.classEq (.cv p) M) (synCin (.cv p) (.cv n)) (synCin M (.cv n)) (synC0)
      p0076
  have p0078 := @gEqeq1 (.cv p) M (.cv n)
  have p0079_e01_recanon :
    Nominal.NPrf (.imp (.classEq (.cv p) M) (synWb (.objEq p n) (.classEq M (.cv n)))) :=
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
      p0078
  have p0079 :=
    @gOrbi12d (.classEq (.cv p) M) (.classEq (synCin (.cv p) (.cv n)) (synC0))
      (.classEq (synCin M (.cv n)) (synC0)) (.objEq p n) (.classEq M (.cv n)) p0077
      p0079_e01_recanon
  have freeVariableCertificate8 : n ∉ ((Wff.classEq (.cv p) M)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      fresh_n_ne_p, fresh_n_not_M, or_false, not_false_eq_true]
  have p0080 :=
    @gRalbidv (.classEq (.cv p) M)
      (synWo (.classEq (synCin (.cv p) (.cv n)) (synC0)) (.objEq p n))
      (synWo (.classEq (synCin M (.cv n)) (synC0)) (.classEq M (.cv n))) n (synCnnc)
      freeVariableCertificate8 p0079
  have freeVariableCertificate9 : m ∉ ((Class.cv n)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_m_ne_n, not_false_eq_true]
  have p0081 := @gNnc0suc m (.cv n) freeVariableCertificate9
  have p0082 := @gN0nelsuc (.cv m)
  have p0083 := @gEleq2 (.cv n) (synCplc (.cv m) (synC1c)) (synC0)
  have p0084 :=
    @gBiimpcd (.classEq (.cv n) (synCplc (.cv m) (synC1c)))
      (.classMem (synC0) (.cv n)) (.classMem (synC0) (synCplc (.cv m) (synC1c))) p0083
  have p0085 :=
    @gMtoi (.classMem (synC0) (.cv n)) (.classEq (.cv n) (synCplc (.cv m) (synC1c)))
      (.classMem (synC0) (synCplc (.cv m) (synC1c))) p0082 p0084
  have p0086 :=
    @gAdantr (.classMem (synC0) (.cv n))
      (.neg (.classEq (.cv n) (synCplc (.cv m) (synC1c))))
      (.classMem (.cv m) (synCnnc)) p0085
  have freeVariableCertificate10 : m ∉ ((Wff.classMem (synC0) (.cv n))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      Finset.notMem_empty, fresh_m_ne_n, or_false, not_false_eq_true]
  have p0087 :=
    @gNrexdv (.classMem (synC0) (.cv n)) (.classEq (.cv n) (synCplc (.cv m) (synC1c)))
      m (synCnnc) freeVariableCertificate10 p0086
  have p0088 :=
    @gOrel2 (synWrex m (synCnnc) (.classEq (.cv n) (synCplc (.cv m) (synC1c))))
      (.classEq (.cv n) (synC0c))
  have p0089 :=
    @gSyl (.classMem (synC0) (.cv n))
      (.neg (synWrex m (synCnnc) (.classEq (.cv n) (synCplc (.cv m) (synC1c)))))
      (.imp (synWo (.classEq (.cv n) (synC0c))
          (synWrex m (synCnnc) (.classEq (.cv n) (synCplc (.cv m) (synC1c)))))
        (.classEq (.cv n) (synC0c)))
      p0087 p0088
  have p0090 :=
    @gCom12 (.classMem (synC0) (.cv n))
      (synWo (.classEq (.cv n) (synC0c))
        (synWrex m (synCnnc) (.classEq (.cv n) (synCplc (.cv m) (synC1c)))))
      (.classEq (.cv n) (synC0c)) p0089
  have p0091 :=
    @gSylbi (.classMem (.cv n) (synCnnc))
      (synWo (.classEq (.cv n) (synC0c))
        (synWrex m (synCnnc) (.classEq (.cv n) (synCplc (.cv m) (synC1c)))))
      (.imp (.classMem (synC0) (.cv n)) (.classEq (.cv n) (synC0c))) p0081 p0090
  have p0092 := @gImor (.classMem (synC0) (.cv n)) (.classEq (.cv n) (synC0c))
  have p0093 :=
    @gSylib (.classMem (.cv n) (synCnnc))
      (.imp (.classMem (synC0) (.cv n)) (.classEq (.cv n) (synC0c)))
      (synWo (.neg (.classMem (synC0) (.cv n))) (.classEq (.cv n) (synC0c))) p0091
      p0092
  have p0094 :=
    @gRgen (synWo (.neg (.classMem (synC0) (.cv n))) (.classEq (.cv n) (synC0c))) n
      (synCnnc) p0093
  have freeVariableCertificate11 :
    a ∉ ((synCin (synCplc (.cv m) (synC1c)) (.cv n))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_a_ne_m, fresh_a_ne_n, or_false,
      not_false_eq_true]
  have p0095 :=
    @gNeq0 a (synCin (synCplc (.cv m) (synC1c)) (.cv n)) freeVariableCertificate11
  have p0096 := @gElin (.cv a) (synCplc (.cv m) (synC1c)) (.cv n)
  have freeVariableCertificate12 : b ∉ ((Class.cv a)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_b_ne_a, not_false_eq_true]
  have freeVariableCertificate13 : x ∉ ((Class.cv a)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_x_ne_a, not_false_eq_true]
  have freeVariableCertificate14 : b ∉ ((Class.cv m)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_b_ne_m, not_false_eq_true]
  have p0097 :=
    @gElsuc x (.cv a) (.cv m) b freeVariableCertificate12 freeVariableCertificate13
      freeVariableCertificate14 (show b ≠ x from (by exact fresh_b_ne_x))
  have p0098 := @gVex x
  have p0099 := @gElcompl (.cv x) (.cv b) p0098
  have p0100_e00_recanon :
    Nominal.NPrf (synWb (.classMem (.cv x) (synCcompl (.cv b))) (.neg (.objMem x b))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCcompl synCnin synWnan synWa
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0099
  have p0100 :=
    @gAnbi2i (.classMem (.cv x) (synCcompl (.cv b))) (.neg (.objMem x b)) (.objMem b m)
      p0100_e00_recanon
  have p0101 :=
    @gSimp1r (.classMem (.cv m) (synCnnc)) (.classMem (.cv n) (synCnnc))
      (synWral q (synCnnc)
        (synWo (.classEq (synCin (.cv m) (.cv q)) (synC0)) (.objEq m q)))
      (synWa (.objMem b m) (.neg (.objMem x b)))
  have freeVariableCertificate15 : p ∉ ((Class.cv n)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_p_ne_n, not_false_eq_true]
  have p0102 := @gNnc0suc p (.cv n) freeVariableCertificate15
  have p0103 :=
    @gSylib
      (synW3a (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv n) (synCnnc)))
        (synWral q (synCnnc)
          (synWo (.classEq (synCin (.cv m) (.cv q)) (synC0)) (.objEq m q)))
        (synWa (.objMem b m) (.neg (.objMem x b))))
      (.classMem (.cv n) (synCnnc))
      (synWo (.classEq (.cv n) (synC0c))
        (synWrex p (synCnnc) (.classEq (.cv n) (synCplc (.cv p) (synC1c)))))
      p0101 p0102
  have p0104 := @gSsun2 (synCsn (.cv x)) (.cv b)
  have p0105 := @gSnid (.cv x) p0098
  have p0106 :=
    @gSselii (synCsn (.cv x)) (synCun (.cv b) (synCsn (.cv x))) (.cv x) p0104 p0105
  have p0107 := @gN0i (synCun (.cv b) (synCsn (.cv x))) (.cv x)
  have p0108 := Nominal.mp p0106 p0107
  have p0109 := (Nominal.classEqRefl (synC0c))
  have p0110 :=
    @gEleq2i (synC0c) (synCsn (synC0)) (synCun (.cv b) (synCsn (.cv x))) p0109
  have p0111 := @gVex b
  have p0112 := @gSnex (.cv x)
  have p0113 := @gUnex (.cv b) (synCsn (.cv x)) p0111 p0112
  have p0114 := @gElsnc (synCun (.cv b) (synCsn (.cv x))) (synC0) p0113
  have p0115 :=
    @gBitri (.classMem (synCun (.cv b) (synCsn (.cv x))) (synC0c))
      (.classMem (synCun (.cv b) (synCsn (.cv x))) (synCsn (synC0)))
      (.classEq (synCun (.cv b) (synCsn (.cv x))) (synC0)) p0110 p0114
  have p0116 :=
    @gMtbir (.classMem (synCun (.cv b) (synCsn (.cv x))) (synC0c))
      (.classEq (synCun (.cv b) (synCsn (.cv x))) (synC0)) p0108 p0115
  have p0117 := @gEleq2 (.cv n) (synC0c) (synCun (.cv b) (synCsn (.cv x)))
  have p0118 :=
    @gBiimpcd (.classEq (.cv n) (synC0c))
      (.classMem (synCun (.cv b) (synCsn (.cv x))) (.cv n))
      (.classMem (synCun (.cv b) (synCsn (.cv x))) (synC0c)) p0117
  have p0119 :=
    @gMtoi (.classMem (synCun (.cv b) (synCsn (.cv x))) (.cv n))
      (.classEq (.cv n) (synC0c))
      (.classMem (synCun (.cv b) (synCsn (.cv x))) (synC0c)) p0116 p0118
  have p0120 :=
    @gAdantl (.classMem (synCun (.cv b) (synCsn (.cv x))) (.cv n))
      (.neg (.classEq (.cv n) (synC0c)))
      (synW3a (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv n) (synCnnc)))
        (synWral q (synCnnc)
          (synWo (.classEq (synCin (.cv m) (.cv q)) (synC0)) (.objEq m q)))
        (synWa (.objMem b m) (.neg (.objMem x b))))
      p0119
  have p0121 :=
    @gOrel1 (.classEq (.cv n) (synC0c))
      (synWrex p (synCnnc) (.classEq (.cv n) (synCplc (.cv p) (synC1c))))
  have p0122 :=
    @gSyl
      (synWa (synW3a (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv n) (synCnnc)))
          (synWral q (synCnnc)
            (synWo (.classEq (synCin (.cv m) (.cv q)) (synC0)) (.objEq m q)))
          (synWa (.objMem b m) (.neg (.objMem x b))))
        (.classMem (synCun (.cv b) (synCsn (.cv x))) (.cv n)))
      (.neg (.classEq (.cv n) (synC0c)))
      (.imp (synWo (.classEq (.cv n) (synC0c))
          (synWrex p (synCnnc) (.classEq (.cv n) (synCplc (.cv p) (synC1c)))))
        (synWrex p (synCnnc) (.classEq (.cv n) (synCplc (.cv p) (synC1c)))))
      p0120 p0121
  have p0123 :=
    @gSimpll (.classMem (.cv p) (synCnnc))
      (synW3a (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv n) (synCnnc)))
        (synWral q (synCnnc)
          (synWo (.classEq (synCin (.cv m) (.cv q)) (synC0)) (.objEq m q)))
        (synWa (.objMem b m) (.neg (.objMem x b))))
      (.classMem (synCun (.cv b) (synCsn (.cv x))) (synCplc (.cv p) (synC1c)))
  have p0124 :=
    @gSimpr3r (.objMem b m) (.neg (.objMem x b))
      (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv n) (synCnnc)))
      (synWral q (synCnnc)
        (synWo (.classEq (synCin (.cv m) (.cv q)) (synC0)) (.objEq m q)))
      (.classMem (.cv p) (synCnnc))
  have p0125 :=
    @gAdantr
      (synWa (.classMem (.cv p) (synCnnc))
        (synW3a (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv n) (synCnnc)))
          (synWral q (synCnnc)
            (synWo (.classEq (synCin (.cv m) (.cv q)) (synC0)) (.objEq m q)))
          (synWa (.objMem b m) (.neg (.objMem x b)))))
      (.neg (.objMem x b))
      (.classMem (synCun (.cv b) (synCsn (.cv x))) (synCplc (.cv p) (synC1c))) p0124
  have p0126 :=
    @gSimpr
      (synWa (.classMem (.cv p) (synCnnc))
        (synW3a (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv n) (synCnnc)))
          (synWral q (synCnnc)
            (synWo (.classEq (synCin (.cv m) (.cv q)) (synC0)) (.objEq m q)))
          (synWa (.objMem b m) (.neg (.objMem x b)))))
      (.classMem (synCun (.cv b) (synCsn (.cv x))) (synCplc (.cv p) (synC1c)))
  have p0127 := @gNnsucelr (.cv b) (.cv p) (.cv x) p0111 p0098
  have p0128_e03_recanon :
    Nominal.NPrf
      (.imp (synWa (.classMem (.cv p) (synCnnc)) (synWa (.neg (.objMem x b))
            (.classMem (synCun (.cv b) (synCsn (.cv x))) (synCplc (.cv p) (synC1c)))))
        (.objMem b p)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWa synCnnc synCint
        simp (config := { failIfUnchanged := false }) only []
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _)
      p0127
  have p0128 :=
    @gSyl12anc
      (synWa (synWa (.classMem (.cv p) (synCnnc))
          (synW3a (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv n) (synCnnc)))
            (synWral q (synCnnc)
              (synWo (.classEq (synCin (.cv m) (.cv q)) (synC0)) (.objEq m q)))
            (synWa (.objMem b m) (.neg (.objMem x b)))))
        (.classMem (synCun (.cv b) (synCsn (.cv x))) (synCplc (.cv p) (synC1c))))
      (.classMem (.cv p) (synCnnc)) (.neg (.objMem x b))
      (.classMem (synCun (.cv b) (synCsn (.cv x))) (synCplc (.cv p) (synC1c)))
      (.objMem b p) p0123 p0125 p0126 p0128_e03_recanon
  have p0129 :=
    @gEx
      (synWa (.classMem (.cv p) (synCnnc))
        (synW3a (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv n) (synCnnc)))
          (synWral q (synCnnc)
            (synWo (.classEq (synCin (.cv m) (.cv q)) (synC0)) (.objEq m q)))
          (synWa (.objMem b m) (.neg (.objMem x b)))))
      (.classMem (synCun (.cv b) (synCsn (.cv x))) (synCplc (.cv p) (synC1c)))
      (.objMem b p) p0128
  have p0130 := @gIneq2 (.cv q) (.cv p) (.cv m)
  have p0131_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq q p) (.classEq (synCin (.cv m) (.cv q)) (synCin (.cv m) (.cv p)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synCin synCcompl synCnin synWnan synWa
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0130
  have p0131 :=
    @gEqeq1d (.objEq q p) (synCin (.cv m) (.cv q)) (synCin (.cv m) (.cv p)) (synC0)
      p0131_e00_recanon
  have p0132 := @gEquequ2 q p m
  have p0133 :=
    @gOrbi12d (.objEq q p) (.classEq (synCin (.cv m) (.cv q)) (synC0))
      (.classEq (synCin (.cv m) (.cv p)) (synC0)) (.objEq m q) (.objEq m p) p0131 p0132
  have p0134_e00_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv q) (.cv p))
        (synWb (synWo (.classEq (synCin (.cv m) (.cv q)) (synC0)) (.objEq m q))
          (synWo (.classEq (synCin (.cv m) (.cv p)) (synC0)) (.objEq m p)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWo synCin synCcompl synCnin synWnan synWa synC0 synCdif
          synCvv
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0133
  have freeVariableCertificate16 : q ∉ ((Class.cv p)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_q_ne_p, not_false_eq_true]
  have freeVariableCertificate17 :
    q ∉ ((synWo (.classEq (synCin (.cv m) (.cv p)) (synC0)) (.objEq m p))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wo,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
      NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_union, Finset.mem_insert,
      Finset.mem_singleton, Finset.notMem_empty, fresh_q_ne_m, fresh_q_ne_p, or_false,
      not_false_eq_true]
  have p0134 :=
    @gRspccv (synWo (.classEq (synCin (.cv m) (.cv q)) (synC0)) (.objEq m q))
      (synWo (.classEq (synCin (.cv m) (.cv p)) (synC0)) (.objEq m p)) q (.cv p)
      (synCnnc) freeVariableCertificate16
      (by
        exact
          (show q ∉ ((synCnnc)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc];
              exact (show q ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
      freeVariableCertificate17 p0134_e00_recanon
  have p0135 := @gElin (.cv b) (.cv m) (.cv p)
  have p0136 := @gN0i (synCin (.cv m) (.cv p)) (.cv b)
  have p0137_e00_recanon :
    Nominal.NPrf
      (synWb (.classMem (.cv b) (synCin (.cv m) (.cv p)))
        (synWa (.objMem b m) (.objMem b p))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCin synCcompl synCnin synWnan synWa
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0135
  have p0137 :=
    @gSylbir (synWa (.objMem b m) (.objMem b p))
      (.classMem (.cv b) (synCin (.cv m) (.cv p)))
      (.neg (.classEq (synCin (.cv m) (.cv p)) (synC0))) p0137_e00_recanon p0136
  have p0138 := @gPm253 (.classEq (synCin (.cv m) (.cv p)) (synC0)) (.objEq m p)
  have p0139 :=
    @gSyl5 (synWa (.objMem b m) (.objMem b p))
      (.neg (.classEq (synCin (.cv m) (.cv p)) (synC0)))
      (synWo (.classEq (synCin (.cv m) (.cv p)) (synC0)) (.objEq m p)) (.objEq m p)
      p0137 p0138
  have p0140 :=
    @gExp3a (synWo (.classEq (synCin (.cv m) (.cv p)) (synC0)) (.objEq m p))
      (.objMem b m) (.objMem b p) (.objEq m p) p0139
  have p0141 :=
    @gSyl6
      (synWral q (synCnnc)
        (synWo (.classEq (synCin (.cv m) (.cv q)) (synC0)) (.objEq m q)))
      (.classMem (.cv p) (synCnnc))
      (synWo (.classEq (synCin (.cv m) (.cv p)) (synC0)) (.objEq m p))
      (.imp (.objMem b m) (.imp (.objMem b p) (.objEq m p))) p0134 p0140
  have p0142 :=
    @gCom23
      (synWral q (synCnnc)
        (synWo (.classEq (synCin (.cv m) (.cv q)) (synC0)) (.objEq m q)))
      (.classMem (.cv p) (synCnnc)) (.objMem b m) (.imp (.objMem b p) (.objEq m p)) p0141
  have p0143 :=
    @gImp
      (synWral q (synCnnc)
        (synWo (.classEq (synCin (.cv m) (.cv q)) (synC0)) (.objEq m q)))
      (.objMem b m)
      (.imp (.classMem (.cv p) (synCnnc)) (.imp (.objMem b p) (.objEq m p))) p0142
  have p0144 :=
    @gAdantrr
      (synWral q (synCnnc)
        (synWo (.classEq (synCin (.cv m) (.cv q)) (synC0)) (.objEq m q)))
      (.objMem b m)
      (.imp (.classMem (.cv p) (synCnnc)) (.imp (.objMem b p) (.objEq m p)))
      (.neg (.objMem x b)) p0143
  have p0145 :=
    @gN3adant1
      (synWral q (synCnnc)
        (synWo (.classEq (synCin (.cv m) (.cv q)) (synC0)) (.objEq m q)))
      (synWa (.objMem b m) (.neg (.objMem x b)))
      (.imp (.classMem (.cv p) (synCnnc)) (.imp (.objMem b p) (.objEq m p)))
      (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv n) (synCnnc))) p0144
  have p0146 :=
    @gImpcom
      (synW3a (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv n) (synCnnc)))
        (synWral q (synCnnc)
          (synWo (.classEq (synCin (.cv m) (.cv q)) (synC0)) (.objEq m q)))
        (synWa (.objMem b m) (.neg (.objMem x b))))
      (.classMem (.cv p) (synCnnc)) (.imp (.objMem b p) (.objEq m p)) p0145
  have p0147 :=
    @gSyld
      (synWa (.classMem (.cv p) (synCnnc))
        (synW3a (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv n) (synCnnc)))
          (synWral q (synCnnc)
            (synWo (.classEq (synCin (.cv m) (.cv q)) (synC0)) (.objEq m q)))
          (synWa (.objMem b m) (.neg (.objMem x b)))))
      (.classMem (synCun (.cv b) (synCsn (.cv x))) (synCplc (.cv p) (synC1c)))
      (.objMem b p) (.objEq m p) p0129 p0146
  have p0148 :=
    @gEx (.classMem (.cv p) (synCnnc))
      (synW3a (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv n) (synCnnc)))
        (synWral q (synCnnc)
          (synWo (.classEq (synCin (.cv m) (.cv q)) (synC0)) (.objEq m q)))
        (synWa (.objMem b m) (.neg (.objMem x b))))
      (.imp (.classMem (synCun (.cv b) (synCsn (.cv x))) (synCplc (.cv p) (synC1c)))
        (.objEq m p))
      p0147
  have p0149 :=
    @gCom3l (.classMem (.cv p) (synCnnc))
      (synW3a (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv n) (synCnnc)))
        (synWral q (synCnnc)
          (synWo (.classEq (synCin (.cv m) (.cv q)) (synC0)) (.objEq m q)))
        (synWa (.objMem b m) (.neg (.objMem x b))))
      (.classMem (synCun (.cv b) (synCsn (.cv x))) (synCplc (.cv p) (synC1c)))
      (.objEq m p) p0148
  have p0150 :=
    @gImp
      (synW3a (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv n) (synCnnc)))
        (synWral q (synCnnc)
          (synWo (.classEq (synCin (.cv m) (.cv q)) (synC0)) (.objEq m q)))
        (synWa (.objMem b m) (.neg (.objMem x b))))
      (.classMem (synCun (.cv b) (synCsn (.cv x))) (synCplc (.cv p) (synC1c)))
      (.imp (.classMem (.cv p) (synCnnc)) (.objEq m p)) p0149
  have p0151 := @gAddceq1 (.cv m) (.cv p) (synC1c)
  have p0152_e01_recanon :
    Nominal.NPrf
      (.imp (.objEq m p)
        (.classEq (synCplc (.cv m) (synC1c)) (synCplc (.cv p) (synC1c)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synCplc synWrex synWex synWa synC1c
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0151
  have p0152 :=
    @gSyl6
      (synWa (synW3a (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv n) (synCnnc)))
          (synWral q (synCnnc)
            (synWo (.classEq (synCin (.cv m) (.cv q)) (synC0)) (.objEq m q)))
          (synWa (.objMem b m) (.neg (.objMem x b))))
        (.classMem (synCun (.cv b) (synCsn (.cv x))) (synCplc (.cv p) (synC1c))))
      (.classMem (.cv p) (synCnnc)) (.objEq m p)
      (.classEq (synCplc (.cv m) (synC1c)) (synCplc (.cv p) (synC1c))) p0150
      p0152_e01_recanon
  have p0153 :=
    @gEleq2 (.cv n) (synCplc (.cv p) (synC1c)) (synCun (.cv b) (synCsn (.cv x)))
  have p0154 :=
    @gAnbi2d (.classEq (.cv n) (synCplc (.cv p) (synC1c)))
      (.classMem (synCun (.cv b) (synCsn (.cv x))) (.cv n))
      (.classMem (synCun (.cv b) (synCsn (.cv x))) (synCplc (.cv p) (synC1c)))
      (synW3a (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv n) (synCnnc)))
        (synWral q (synCnnc)
          (synWo (.classEq (synCin (.cv m) (.cv q)) (synC0)) (.objEq m q)))
        (synWa (.objMem b m) (.neg (.objMem x b))))
      p0153
  have p0155 := @gEqeq2 (.cv n) (synCplc (.cv p) (synC1c)) (synCplc (.cv m) (synC1c))
  have p0156 :=
    @gImbi2d (.classEq (.cv n) (synCplc (.cv p) (synC1c)))
      (.classEq (synCplc (.cv m) (synC1c)) (.cv n))
      (.classEq (synCplc (.cv m) (synC1c)) (synCplc (.cv p) (synC1c)))
      (.classMem (.cv p) (synCnnc)) p0155
  have p0157 :=
    @gImbi12d (.classEq (.cv n) (synCplc (.cv p) (synC1c)))
      (synWa (synW3a (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv n) (synCnnc)))
          (synWral q (synCnnc)
            (synWo (.classEq (synCin (.cv m) (.cv q)) (synC0)) (.objEq m q)))
          (synWa (.objMem b m) (.neg (.objMem x b))))
        (.classMem (synCun (.cv b) (synCsn (.cv x))) (.cv n)))
      (synWa (synW3a (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv n) (synCnnc)))
          (synWral q (synCnnc)
            (synWo (.classEq (synCin (.cv m) (.cv q)) (synC0)) (.objEq m q)))
          (synWa (.objMem b m) (.neg (.objMem x b))))
        (.classMem (synCun (.cv b) (synCsn (.cv x))) (synCplc (.cv p) (synC1c))))
      (.imp (.classMem (.cv p) (synCnnc)) (.classEq (synCplc (.cv m) (synC1c)) (.cv n)))
      (.imp (.classMem (.cv p) (synCnnc))
        (.classEq (synCplc (.cv m) (synC1c)) (synCplc (.cv p) (synC1c))))
      p0154 p0156
  have p0158 :=
    @gMpbiri (.classEq (.cv n) (synCplc (.cv p) (synC1c)))
      (.imp (synWa
          (synW3a (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv n) (synCnnc)))
            (synWral q (synCnnc)
              (synWo (.classEq (synCin (.cv m) (.cv q)) (synC0)) (.objEq m q)))
            (synWa (.objMem b m) (.neg (.objMem x b))))
          (.classMem (synCun (.cv b) (synCsn (.cv x))) (.cv n)))
        (.imp (.classMem (.cv p) (synCnnc)) (.classEq (synCplc (.cv m) (synC1c)) (.cv n))))
      (.imp (synWa
          (synW3a (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv n) (synCnnc)))
            (synWral q (synCnnc)
              (synWo (.classEq (synCin (.cv m) (.cv q)) (synC0)) (.objEq m q)))
            (synWa (.objMem b m) (.neg (.objMem x b))))
          (.classMem (synCun (.cv b) (synCsn (.cv x))) (synCplc (.cv p) (synC1c))))
        (.imp (.classMem (.cv p) (synCnnc))
          (.classEq (synCplc (.cv m) (synC1c)) (synCplc (.cv p) (synC1c)))))
      p0152 p0157
  have p0159 :=
    @gCom3l (.classEq (.cv n) (synCplc (.cv p) (synC1c)))
      (synWa (synW3a (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv n) (synCnnc)))
          (synWral q (synCnnc)
            (synWo (.classEq (synCin (.cv m) (.cv q)) (synC0)) (.objEq m q)))
          (synWa (.objMem b m) (.neg (.objMem x b))))
        (.classMem (synCun (.cv b) (synCsn (.cv x))) (.cv n)))
      (.classMem (.cv p) (synCnnc)) (.classEq (synCplc (.cv m) (synC1c)) (.cv n)) p0158
  have freeVariableCertificate18 :
    p ∉ ((Wff.classEq (synCplc (.cv m) (synC1c)) (.cv n))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_p_ne_m, fresh_p_ne_n, or_false,
      not_false_eq_true]
  have freeVariableCertificate19 :
    p ∉
      ((synWa (synW3a (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv n) (synCnnc)))
            (synWral q (synCnnc)
              (synWo (.classEq (synCin (.cv m) (.cv q)) (synC0)) (.objEq m q)))
            (synWa (.objMem b m) (.neg (.objMem x b))))
          (.classMem (synCun (.cv b) (synCsn (.cv x))) (.cv n)))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a,
      NFChoice.Compiler.CoreFVSimp.fv_wff_objMem, NFChoice.Compiler.CoreFVSimp.fv_wff_neg,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wo,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
      NFChoice.Compiler.CoreFVSimp.fv_wff_objEq,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
      Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty,
      fresh_p_ne_b, fresh_p_ne_m, fresh_p_ne_x, fresh_p_ne_n, fresh_p_ne_q, or_false,
      and_false, not_false_eq_true]
  have p0160 :=
    @gRexlimdv
      (synWa (synW3a (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv n) (synCnnc)))
          (synWral q (synCnnc)
            (synWo (.classEq (synCin (.cv m) (.cv q)) (synC0)) (.objEq m q)))
          (synWa (.objMem b m) (.neg (.objMem x b))))
        (.classMem (synCun (.cv b) (synCsn (.cv x))) (.cv n)))
      (.classEq (.cv n) (synCplc (.cv p) (synC1c)))
      (.classEq (synCplc (.cv m) (synC1c)) (.cv n)) p (synCnnc)
      freeVariableCertificate18 freeVariableCertificate19 p0159
  have p0161 :=
    @gSyld
      (synWa (synW3a (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv n) (synCnnc)))
          (synWral q (synCnnc)
            (synWo (.classEq (synCin (.cv m) (.cv q)) (synC0)) (.objEq m q)))
          (synWa (.objMem b m) (.neg (.objMem x b))))
        (.classMem (synCun (.cv b) (synCsn (.cv x))) (.cv n)))
      (synWo (.classEq (.cv n) (synC0c))
        (synWrex p (synCnnc) (.classEq (.cv n) (synCplc (.cv p) (synC1c)))))
      (synWrex p (synCnnc) (.classEq (.cv n) (synCplc (.cv p) (synC1c))))
      (.classEq (synCplc (.cv m) (synC1c)) (.cv n)) p0122 p0160
  have p0162 :=
    @gEx
      (synW3a (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv n) (synCnnc)))
        (synWral q (synCnnc)
          (synWo (.classEq (synCin (.cv m) (.cv q)) (synC0)) (.objEq m q)))
        (synWa (.objMem b m) (.neg (.objMem x b))))
      (.classMem (synCun (.cv b) (synCsn (.cv x))) (.cv n))
      (.imp (synWo (.classEq (.cv n) (synC0c))
          (synWrex p (synCnnc) (.classEq (.cv n) (synCplc (.cv p) (synC1c)))))
        (.classEq (synCplc (.cv m) (synC1c)) (.cv n)))
      p0161
  have p0163 :=
    @gMpid
      (synW3a (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv n) (synCnnc)))
        (synWral q (synCnnc)
          (synWo (.classEq (synCin (.cv m) (.cv q)) (synC0)) (.objEq m q)))
        (synWa (.objMem b m) (.neg (.objMem x b))))
      (.classMem (synCun (.cv b) (synCsn (.cv x))) (.cv n))
      (synWo (.classEq (.cv n) (synC0c))
        (synWrex p (synCnnc) (.classEq (.cv n) (synCplc (.cv p) (synC1c)))))
      (.classEq (synCplc (.cv m) (synC1c)) (.cv n)) p0103 p0162
  have p0164 :=
    @gN3expa (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv n) (synCnnc)))
      (synWral q (synCnnc)
        (synWo (.classEq (synCin (.cv m) (.cv q)) (synC0)) (.objEq m q)))
      (synWa (.objMem b m) (.neg (.objMem x b)))
      (.imp (.classMem (synCun (.cv b) (synCsn (.cv x))) (.cv n))
        (.classEq (synCplc (.cv m) (synC1c)) (.cv n)))
      p0163
  have p0165 := @gEleq1 (.cv a) (synCun (.cv b) (synCsn (.cv x))) (.cv n)
  have p0166_e00_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv a) (synCun (.cv b) (synCsn (.cv x))))
        (synWb (.objMem a n) (.classMem (synCun (.cv b) (synCsn (.cv x))) (.cv n)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synCun synCnin synWnan synWa synCcompl synCsn synWb
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
      p0165
  have p0166 :=
    @gImbi1d (.classEq (.cv a) (synCun (.cv b) (synCsn (.cv x)))) (.objMem a n)
      (.classMem (synCun (.cv b) (synCsn (.cv x))) (.cv n))
      (.classEq (synCplc (.cv m) (synC1c)) (.cv n)) p0166_e00_recanon
  have p0167 :=
    @gSyl5ibrcom
      (synWa (synWa (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv n) (synCnnc)))
          (synWral q (synCnnc)
            (synWo (.classEq (synCin (.cv m) (.cv q)) (synC0)) (.objEq m q))))
        (synWa (.objMem b m) (.neg (.objMem x b))))
      (.imp (.objMem a n) (.classEq (synCplc (.cv m) (synC1c)) (.cv n)))
      (.classEq (.cv a) (synCun (.cv b) (synCsn (.cv x))))
      (.imp (.classMem (synCun (.cv b) (synCsn (.cv x))) (.cv n))
        (.classEq (synCplc (.cv m) (synC1c)) (.cv n)))
      p0164 p0166
  have p0168 :=
    @gSylan2b (synWa (.objMem b m) (.classMem (.cv x) (synCcompl (.cv b))))
      (synWa (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv n) (synCnnc)))
        (synWral q (synCnnc)
          (synWo (.classEq (synCin (.cv m) (.cv q)) (synC0)) (.objEq m q))))
      (synWa (.objMem b m) (.neg (.objMem x b)))
      (.imp (.classEq (.cv a) (synCun (.cv b) (synCsn (.cv x))))
        (.imp (.objMem a n) (.classEq (synCplc (.cv m) (synC1c)) (.cv n))))
      p0100 p0167
  have p0169_e00_recanon :
    Nominal.NPrf
      (.imp (synWa
          (synWa (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv n) (synCnnc)))
            (synWral q (synCnnc)
              (synWo (.classEq (synCin (.cv m) (.cv q)) (synC0)) (.objEq m q))))
          (synWa (.classMem (.cv b) (.cv m)) (.classMem (.cv x) (synCcompl (.cv b)))))
        (.imp (.classEq (.cv a) (synCun (.cv b) (synCsn (.cv x))))
          (.imp (.objMem a n) (.classEq (synCplc (.cv m) (synC1c)) (.cv n))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWa synCun synCnin synWnan synCcompl synCsn synCplc synWrex
          synWex synC1c
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.objMem_classMem _ _
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0168
  have freeVariableCertificate20 : x ∉ ((Class.cv m)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_x_ne_m, not_false_eq_true]
  have freeVariableCertificate21 :
    b ∉ ((Wff.imp (.objMem a n) (.classEq (synCplc (.cv m) (synC1c)) (.cv n)))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
      NFChoice.Compiler.CoreFVSimp.fv_wff_objMem,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
      Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, fresh_b_ne_a,
      fresh_b_ne_n, fresh_b_ne_m, or_false, not_false_eq_true]
  have freeVariableCertificate22 :
    x ∉ ((Wff.imp (.objMem a n) (.classEq (synCplc (.cv m) (synC1c)) (.cv n)))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
      NFChoice.Compiler.CoreFVSimp.fv_wff_objMem,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
      Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, fresh_x_ne_a,
      fresh_x_ne_n, fresh_x_ne_m, or_false, not_false_eq_true]
  have freeVariableCertificate23 :
    b ∉
      ((synWa (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv n) (synCnnc)))
          (synWral q (synCnnc)
            (synWo (.classEq (synCin (.cv m) (.cv q)) (synC0)) (.objEq m q))))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wo,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
      NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_union, Finset.mem_erase,
      Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, fresh_b_ne_m,
      fresh_b_ne_n, fresh_b_ne_q, or_false, and_false, not_false_eq_true]
  have freeVariableCertificate24 :
    x ∉
      ((synWa (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv n) (synCnnc)))
          (synWral q (synCnnc)
            (synWo (.classEq (synCin (.cv m) (.cv q)) (synC0)) (.objEq m q))))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wo,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
      NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_union, Finset.mem_erase,
      Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, fresh_x_ne_m,
      fresh_x_ne_n, fresh_x_ne_q, or_false, and_false, not_false_eq_true]
  have p0169 :=
    @gRexlimdvva
      (synWa (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv n) (synCnnc)))
        (synWral q (synCnnc)
          (synWo (.classEq (synCin (.cv m) (.cv q)) (synC0)) (.objEq m q))))
      (.classEq (.cv a) (synCun (.cv b) (synCsn (.cv x))))
      (.imp (.objMem a n) (.classEq (synCplc (.cv m) (synC1c)) (.cv n))) b x (.cv m)
      (synCcompl (.cv b)) freeVariableCertificate20 freeVariableCertificate21
      freeVariableCertificate22 freeVariableCertificate23 freeVariableCertificate24
      (show b ≠ x from (by exact fresh_b_ne_x)) p0169_e00_recanon
  have p0170 :=
    @gSyl5bi (.classMem (.cv a) (synCplc (.cv m) (synC1c)))
      (synWrex b (.cv m) (synWrex x (synCcompl (.cv b))
          (.classEq (.cv a) (synCun (.cv b) (synCsn (.cv x))))))
      (synWa (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv n) (synCnnc)))
        (synWral q (synCnnc)
          (synWo (.classEq (synCin (.cv m) (.cv q)) (synC0)) (.objEq m q))))
      (.imp (.objMem a n) (.classEq (synCplc (.cv m) (synC1c)) (.cv n))) p0097 p0169
  have p0171 :=
    @gImp3a
      (synWa (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv n) (synCnnc)))
        (synWral q (synCnnc)
          (synWo (.classEq (synCin (.cv m) (.cv q)) (synC0)) (.objEq m q))))
      (.classMem (.cv a) (synCplc (.cv m) (synC1c))) (.objMem a n)
      (.classEq (synCplc (.cv m) (synC1c)) (.cv n)) p0170
  have p0172_e00_recanon :
    Nominal.NPrf
      (synWb (.classMem (.cv a) (synCin (synCplc (.cv m) (synC1c)) (.cv n)))
        (synWa (.classMem (.cv a) (synCplc (.cv m) (synC1c))) (.objMem a n))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCin synCcompl synCnin synWnan synWa synCplc synWrex
          synWex synC1c
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
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0096
  have p0172 :=
    @gSyl5bi (.classMem (.cv a) (synCin (synCplc (.cv m) (synC1c)) (.cv n)))
      (synWa (.classMem (.cv a) (synCplc (.cv m) (synC1c))) (.objMem a n))
      (synWa (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv n) (synCnnc)))
        (synWral q (synCnnc)
          (synWo (.classEq (synCin (.cv m) (.cv q)) (synC0)) (.objEq m q))))
      (.classEq (synCplc (.cv m) (synC1c)) (.cv n)) p0172_e00_recanon p0171
  have freeVariableCertificate25 :
    a ∉ ((Wff.classEq (synCplc (.cv m) (synC1c)) (.cv n))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_a_ne_m, fresh_a_ne_n, or_false,
      not_false_eq_true]
  have freeVariableCertificate26 :
    a ∉
      ((synWa (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv n) (synCnnc)))
          (synWral q (synCnnc)
            (synWo (.classEq (synCin (.cv m) (.cv q)) (synC0)) (.objEq m q))))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wo,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
      NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_union, Finset.mem_erase,
      Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, fresh_a_ne_m,
      fresh_a_ne_n, fresh_a_ne_q, or_false, and_false, not_false_eq_true]
  have p0173 :=
    @gExlimdv
      (synWa (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv n) (synCnnc)))
        (synWral q (synCnnc)
          (synWo (.classEq (synCin (.cv m) (.cv q)) (synC0)) (.objEq m q))))
      (.classMem (.cv a) (synCin (synCplc (.cv m) (synC1c)) (.cv n)))
      (.classEq (synCplc (.cv m) (synC1c)) (.cv n)) a freeVariableCertificate25
      freeVariableCertificate26 p0172
  have p0174 :=
    @gSyl5bi (.neg (.classEq (synCin (synCplc (.cv m) (synC1c)) (.cv n)) (synC0)))
      (synWex a (.classMem (.cv a) (synCin (synCplc (.cv m) (synC1c)) (.cv n))))
      (synWa (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv n) (synCnnc)))
        (synWral q (synCnnc)
          (synWo (.classEq (synCin (.cv m) (.cv q)) (synC0)) (.objEq m q))))
      (.classEq (synCplc (.cv m) (synC1c)) (.cv n)) p0095 p0173
  have p0175 :=
    @gOrrd
      (synWa (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv n) (synCnnc)))
        (synWral q (synCnnc)
          (synWo (.classEq (synCin (.cv m) (.cv q)) (synC0)) (.objEq m q))))
      (.classEq (synCin (synCplc (.cv m) (synC1c)) (.cv n)) (synC0))
      (.classEq (synCplc (.cv m) (synC1c)) (.cv n)) p0174
  have p0176 :=
    @gExp31 (.classMem (.cv m) (synCnnc)) (.classMem (.cv n) (synCnnc))
      (synWral q (synCnnc)
        (synWo (.classEq (synCin (.cv m) (.cv q)) (synC0)) (.objEq m q)))
      (synWo (.classEq (synCin (synCplc (.cv m) (synC1c)) (.cv n)) (synC0))
        (.classEq (synCplc (.cv m) (synC1c)) (.cv n)))
      p0175
  have p0177 :=
    @gCom23 (.classMem (.cv m) (synCnnc)) (.classMem (.cv n) (synCnnc))
      (synWral q (synCnnc)
        (synWo (.classEq (synCin (.cv m) (.cv q)) (synC0)) (.objEq m q)))
      (synWo (.classEq (synCin (synCplc (.cv m) (synC1c)) (.cv n)) (synC0))
        (.classEq (synCplc (.cv m) (synC1c)) (.cv n)))
      p0176
  have freeVariableCertificate27 : n ∉ ((Wff.classMem (.cv m) (synCnnc))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_n_ne_m, or_false,
      not_false_eq_true]
  have freeVariableCertificate28 :
    n ∉
      ((synWral q (synCnnc)
          (synWo (.classEq (synCin (.cv m) (.cv q)) (synC0)) (.objEq m q)))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wo,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
      NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_union, Finset.mem_erase,
      Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, fresh_n_ne_m,
      fresh_n_ne_q, or_false, and_false, not_false_eq_true]
  have p0178 :=
    @gRalrimdv (.classMem (.cv m) (synCnnc))
      (synWral q (synCnnc)
        (synWo (.classEq (synCin (.cv m) (.cv q)) (synC0)) (.objEq m q)))
      (synWo (.classEq (synCin (synCplc (.cv m) (synC1c)) (.cv n)) (synC0))
        (.classEq (synCplc (.cv m) (synC1c)) (.cv n)))
      n (synCnnc) freeVariableCertificate27 freeVariableCertificate28 p0177
  have freeVariableCertificate29 :
    p ∉
      ((synWral q (synCnnc)
          (synWo (.classEq (synCin (.cv m) (.cv q)) (synC0)) (.objEq m q)))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wo,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
      NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_union, Finset.mem_erase,
      Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, fresh_p_ne_m,
      fresh_p_ne_q, or_false, and_false, not_false_eq_true]
  have freeVariableCertificate30 :
    m ∉
      ((synWral n (synCnnc)
          (synWo (.classEq (synCin (.cv p) (.cv n)) (synC0)) (.objEq p n)))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wo,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
      NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_union, Finset.mem_erase,
      Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, fresh_m_ne_p,
      fresh_m_ne_n, or_false, and_false, not_false_eq_true]
  have freeVariableCertificate31 :
    p ∉
      ((synWral n (synCnnc) (synWo (.neg (.classMem (synC0) (.cv n)))
            (.classEq (.cv n) (synC0c))))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wo,
      NFChoice.Compiler.CoreFVSimp.fv_wff_neg,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union,
      Finset.mem_erase, Finset.mem_singleton, Finset.notMem_empty, fresh_p_ne_n, or_false,
      and_false, not_false_eq_true]
  have freeVariableCertificate32 :
    p ∉
      ((synWral n (synCnnc)
          (synWo (.classEq (synCin M (.cv n)) (synC0)) (.classEq M (.cv n))))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wo,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union,
      Finset.mem_erase, Finset.mem_singleton, Finset.notMem_empty, fresh_p_not_M,
      fresh_p_ne_n, or_false, and_false, not_false_eq_true]
  have freeVariableCertificate33 :
    p ∉
      ((synWral n (synCnnc)
          (synWo (.classEq (synCin (synCplc (.cv m) (synC1c)) (.cv n)) (synC0))
            (.classEq (synCplc (.cv m) (synC1c)) (.cv n))))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wo,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union,
      Finset.mem_erase, Finset.mem_singleton, Finset.notMem_empty, fresh_p_ne_m,
      fresh_p_ne_n, or_false, and_false, not_false_eq_true]
  have p0179 :=
    @gFinds
      (synWral n (synCnnc)
        (synWo (.classEq (synCin (.cv p) (.cv n)) (synC0)) (.objEq p n)))
      (synWral n (synCnnc)
        (synWo (.neg (.classMem (synC0) (.cv n))) (.classEq (.cv n) (synC0c))))
      (synWral q (synCnnc)
        (synWo (.classEq (synCin (.cv m) (.cv q)) (synC0)) (.objEq m q)))
      (synWral n (synCnnc)
        (synWo (.classEq (synCin (synCplc (.cv m) (synC1c)) (.cv n)) (synC0))
          (.classEq (synCplc (.cv m) (synC1c)) (.cv n))))
      (synWral n (synCnnc)
        (synWo (.classEq (synCin M (.cv n)) (synC0)) (.classEq M (.cv n))))
      p m M (by exact (show p ∉ (M).fv from (by exact fresh_p_not_M)))
      freeVariableCertificate29 freeVariableCertificate30 freeVariableCertificate31
      freeVariableCertificate32 freeVariableCertificate33
      (show p ≠ m from (by exact fresh_p_ne_m)) p0044 p0059 p0070 p0075 p0080 p0094 p0178
  have p0180 := @gIneq2 (.cv n) N M
  have p0181 :=
    @gEqeq1d (.classEq (.cv n) N) (synCin M (.cv n)) (synCin M N) (synC0) p0180
  have p0182 := @gEqeq2 (.cv n) N M
  have p0183 :=
    @gOrbi12d (.classEq (.cv n) N) (.classEq (synCin M (.cv n)) (synC0))
      (.classEq (synCin M N) (synC0)) (.classEq M (.cv n)) (.classEq M N) p0181 p0182
  have freeVariableCertificate34 :
    n ∉ ((synWo (.classEq (synCin M N) (synC0)) (.classEq M N))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wo,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union,
      Finset.notMem_empty, fresh_n_not_M, fresh_n_not_N, or_false, not_false_eq_true]
  have p0184 :=
    @gRspccv (synWo (.classEq (synCin M (.cv n)) (synC0)) (.classEq M (.cv n)))
      (synWo (.classEq (synCin M N) (synC0)) (.classEq M N)) n N (synCnnc)
      (by exact (show n ∉ (N).fv from (by exact fresh_n_not_N)))
      (by
        exact
          (show n ∉ ((synCnnc)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc];
              exact (show n ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
      freeVariableCertificate34 p0183
  have p0185 :=
    @gSyl (.classMem M (synCnnc))
      (synWral n (synCnnc)
        (synWo (.classEq (synCin M (.cv n)) (synC0)) (.classEq M (.cv n))))
      (.imp (.classMem N (synCnnc)) (synWo (.classEq (synCin M N) (synC0)) (.classEq M N)))
      p0179 p0184
  have p0186 :=
    @gImp (.classMem M (synCnnc)) (.classMem N (synCnnc))
      (synWo (.classEq (synCin M N) (synC0)) (.classEq M N)) p0185
  exact p0186


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk009StructuralPart036`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_nnceleq`. -/
@[expose]
noncomputable def gNnceleq (A : Class) (M : Class) (N : Class) :
    Nominal.NPrf
      (.imp (synWa (synWa (.classMem M (synCnnc)) (.classMem N (synCnnc)))
          (synWa (.classMem A M) (.classMem A N))) (.classEq M N)) :=
  by
  have p0000 := @gElin A M N
  have p0001 := @gN0i (synCin M N) A
  have p0002 :=
    @gSylbir (synWa (.classMem A M) (.classMem A N)) (.classMem A (synCin M N))
      (.neg (.classEq (synCin M N) (synC0))) p0000 p0001
  have p0003 :=
    @gAdantl (synWa (.classMem A M) (.classMem A N))
      (.neg (.classEq (synCin M N) (synC0)))
      (synWa (.classMem M (synCnnc)) (.classMem N (synCnnc))) p0002
  have p0004 := @gNndisjeq M N
  have p0005 :=
    @gAdantr (synWa (.classMem M (synCnnc)) (.classMem N (synCnnc)))
      (synWo (.classEq (synCin M N) (synC0)) (.classEq M N))
      (synWa (.classMem A M) (.classMem A N)) p0004
  have p0006 := @gOrel1 (.classEq (synCin M N) (synC0)) (.classEq M N)
  have p0007 :=
    @gSylc
      (synWa (synWa (.classMem M (synCnnc)) (.classMem N (synCnnc)))
        (synWa (.classMem A M) (.classMem A N)))
      (.neg (.classEq (synCin M N) (synC0)))
      (synWo (.classEq (synCin M N) (synC0)) (.classEq M N)) (.classEq M N) p0003 p0005
      p0006
  exact p0007

/-- Checked nominal proof certificate identified upstream as `g_opklefing`. -/
@[expose]
noncomputable def gOpklefing (x : Var) (A : Class) (B : Class) (V : Class) (W : Class)
    (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv) :
    Nominal.NPrf
      (.imp (synWa (.classMem A V) (.classMem B W))
        (synWb (.classMem (synCopk A B) (synClefin))
          (synWrex x (synCnnc) (.classEq B (synCplc A (.cv x)))))) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ A.fv ∪ B.fv ∪ V.fv ∪ W.fv
  let z : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let w : Var := freshVar proofSupport 2
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z_ne_x : z ≠ x := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))
  have fresh_x_ne_z : x ≠ z := Ne.symm fresh_z_ne_x
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_z_not_B : z ∉ B.fv := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_ne_x : y ≠ x := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))
  have fresh_x_ne_y : x ≠ y := Ne.symm fresh_y_ne_x
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_w : w ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_w_ne_x : w ≠ x := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))
  have fresh_x_ne_w : x ≠ w := Ne.symm fresh_w_ne_x
  have fresh_w_not_A : w ∉ A.fv := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_w_not_B : w ∉ B.fv := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_z_ne_y : z ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_z : y ≠ z := Ne.symm fresh_z_ne_y
  have fresh_z_ne_w : z ≠ w :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_w_ne_z : w ≠ z := Ne.symm fresh_z_ne_w
  have fresh_y_ne_w : y ≠ w :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_w_ne_y : w ≠ y := Ne.symm fresh_y_ne_w
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfLefin w y z x
      (show x ≠ w from (by exact fresh_x_ne_w)) (show x ≠ y from (by exact fresh_x_ne_y))
      (show x ≠ z from (by exact fresh_x_ne_z)) (show w ≠ y from (by exact fresh_w_ne_y))
      (show w ≠ z from (by exact fresh_w_ne_z)) (show y ≠ z from (by exact fresh_y_ne_z))
  have p0001 := @gAddceq1 (.cv y) A (.cv x)
  have p0002 :=
    @gEqeq2d (.classEq (.cv y) A) (synCplc (.cv y) (.cv x)) (synCplc A (.cv x)) (.cv z)
      p0001
  have freeVariableCertificate0 : x ∉ ((Wff.classEq (.cv y) A)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      fresh_x_ne_y, dv_A_x, or_false, not_false_eq_true]
  have p0003 :=
    @gRexbidv (.classEq (.cv y) A) (.classEq (.cv z) (synCplc (.cv y) (.cv x)))
      (.classEq (.cv z) (synCplc A (.cv x))) x (synCnnc) freeVariableCertificate0 p0002
  have p0004 := @gEqeq1 (.cv z) B (synCplc A (.cv x))
  have freeVariableCertificate1 : x ∉ ((Wff.classEq (.cv z) B)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      fresh_x_ne_z, dv_B_x, or_false, not_false_eq_true]
  have p0005 :=
    @gRexbidv (.classEq (.cv z) B) (.classEq (.cv z) (synCplc A (.cv x)))
      (.classEq B (synCplc A (.cv x))) x (synCnnc) freeVariableCertificate1 p0004
  have freeVariableCertificate2 :
    z ∉ ((synWrex x (synCnnc) (.classEq B (synCplc A (.cv x))))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
      Finset.mem_singleton, Finset.notMem_empty, fresh_z_not_B, fresh_z_not_A,
      fresh_z_ne_x, or_false, and_false, not_false_eq_true]
  have freeVariableCertificate3 :
    w ∉ ((synWrex x (synCnnc) (.classEq (.cv z) (synCplc (.cv y) (.cv x))))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, Finset.mem_union,
      Finset.mem_erase, Finset.mem_singleton, Finset.notMem_empty, fresh_w_ne_z,
      fresh_w_ne_y, fresh_w_ne_x, or_false, and_false, not_false_eq_true]
  have freeVariableCertificate4 :
    y ∉ ((synWrex x (synCnnc) (.classEq (.cv z) (synCplc A (.cv x))))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, Finset.mem_union,
      Finset.mem_erase, Finset.mem_singleton, Finset.notMem_empty, fresh_y_ne_z,
      fresh_y_not_A, fresh_y_ne_x, or_false, and_false, not_false_eq_true]
  have p0006 :=
    @gOpkelopkabg (synWrex x (synCnnc) (.classEq (.cv z) (synCplc (.cv y) (.cv x))))
      (synWrex x (synCnnc) (.classEq (.cv z) (synCplc A (.cv x))))
      (synWrex x (synCnnc) (.classEq B (synCplc A (.cv x)))) w y z (synClefin) A B V W
      (by
        exact
          (show y ∉ ((synClefin)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin];
              exact (show y ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
      (by
        exact
          (show z ∉ ((synClefin)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin];
              exact (show z ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
      (by exact (show w ∉ (A).fv from (by exact fresh_w_not_A)))
      (by exact (show y ∉ (A).fv from (by exact fresh_y_not_A)))
      (by exact (show z ∉ (A).fv from (by exact fresh_z_not_A)))
      (by exact (show w ∉ (B).fv from (by exact fresh_w_not_B)))
      (by exact (show y ∉ (B).fv from (by exact fresh_y_not_B)))
      (by exact (show z ∉ (B).fv from (by exact fresh_z_not_B))) freeVariableCertificate2
      freeVariableCertificate3 freeVariableCertificate4
      (show w ≠ y from (by exact fresh_w_ne_y)) (show w ≠ z from (by exact fresh_w_ne_z))
      (show y ≠ z from (by exact fresh_y_ne_z)) p0000 p0003 p0005
  exact p0006

/-- Checked nominal proof certificate identified upstream as `g_opkltfing`. -/
@[expose]
noncomputable def gOpkltfing (x : Var) (A : Class) (B : Class) (V : Class) (W : Class)
    (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv) :
    Nominal.NPrf
      (.imp (synWa (.classMem A V) (.classMem B W))
        (synWb (.classMem (synCopk A B) (synCltfin)) (synWa (synWne A (synC0))
            (synWrex x (synCnnc) (.classEq B (synCplc (synCplc A (.cv x)) (synC1c))))))) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ A.fv ∪ B.fv ∪ V.fv ∪ W.fv
  let z : Var := freshVar proofSupport 0
  let w : Var := freshVar proofSupport 1
  let y : Var := freshVar proofSupport 2
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z_ne_x : z ≠ x := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))
  have fresh_x_ne_z : x ≠ z := Ne.symm fresh_z_ne_x
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_z_not_B : z ∉ B.fv := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_w : w ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_w_ne_x : w ≠ x := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))
  have fresh_x_ne_w : x ≠ w := Ne.symm fresh_w_ne_x
  have fresh_w_not_A : w ∉ A.fv := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_w_not_B : w ∉ B.fv := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_y_ne_x : y ≠ x := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))
  have fresh_x_ne_y : x ≠ y := Ne.symm fresh_y_ne_x
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_z_ne_w : z ≠ w :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_z_ne_y : z ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_y_ne_z : y ≠ z := Ne.symm fresh_z_ne_y
  have fresh_w_ne_y : w ≠ y :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_y_ne_w : y ≠ w := Ne.symm fresh_w_ne_y
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfLtfin y z w x
      (show z ≠ w from (by exact fresh_z_ne_w)) (show z ≠ x from (by exact fresh_z_ne_x))
      (show z ≠ y from (by exact fresh_z_ne_y)) (show w ≠ x from (by exact fresh_w_ne_x))
      (show w ≠ y from (by exact fresh_w_ne_y)) (show x ≠ y from (by exact fresh_x_ne_y))
  have p0001 := @gNeeq1 (.cv z) A (synC0)
  have p0002 := @gAddceq1 (.cv z) A (.cv x)
  have p0003 :=
    @gAddceq1d (.classEq (.cv z) A) (synCplc (.cv z) (.cv x)) (synCplc A (.cv x))
      (synC1c) p0002
  have p0004 :=
    @gEqeq2d (.classEq (.cv z) A) (synCplc (synCplc (.cv z) (.cv x)) (synC1c))
      (synCplc (synCplc A (.cv x)) (synC1c)) (.cv w) p0003
  have freeVariableCertificate0 : x ∉ ((Wff.classEq (.cv z) A)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      fresh_x_ne_z, dv_A_x, or_false, not_false_eq_true]
  have p0005 :=
    @gRexbidv (.classEq (.cv z) A)
      (.classEq (.cv w) (synCplc (synCplc (.cv z) (.cv x)) (synC1c)))
      (.classEq (.cv w) (synCplc (synCplc A (.cv x)) (synC1c))) x (synCnnc)
      freeVariableCertificate0 p0004
  have p0006 :=
    @gAnbi12d (.classEq (.cv z) A) (synWne (.cv z) (synC0)) (synWne A (synC0))
      (synWrex x (synCnnc) (.classEq (.cv w) (synCplc (synCplc (.cv z) (.cv x)) (synC1c))))
      (synWrex x (synCnnc) (.classEq (.cv w) (synCplc (synCplc A (.cv x)) (synC1c))))
      p0001 p0005
  have p0007 := @gEqeq1 (.cv w) B (synCplc (synCplc A (.cv x)) (synC1c))
  have freeVariableCertificate1 : x ∉ ((Wff.classEq (.cv w) B)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      fresh_x_ne_w, dv_B_x, or_false, not_false_eq_true]
  have p0008 :=
    @gRexbidv (.classEq (.cv w) B)
      (.classEq (.cv w) (synCplc (synCplc A (.cv x)) (synC1c)))
      (.classEq B (synCplc (synCplc A (.cv x)) (synC1c))) x (synCnnc)
      freeVariableCertificate1 p0007
  have p0009 :=
    @gAnbi2d (.classEq (.cv w) B)
      (synWrex x (synCnnc) (.classEq (.cv w) (synCplc (synCplc A (.cv x)) (synC1c))))
      (synWrex x (synCnnc) (.classEq B (synCplc (synCplc A (.cv x)) (synC1c))))
      (synWne A (synC0)) p0008
  have freeVariableCertificate2 :
    w ∉
      ((synWa (synWne A (synC0)) (synWrex x (synCnnc)
            (.classEq B (synCplc (synCplc A (.cv x)) (synC1c)))))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
      Finset.mem_erase, Finset.mem_singleton, Finset.notMem_empty, fresh_w_not_A,
      fresh_w_not_B, fresh_w_ne_x, or_false, and_false, not_false_eq_true]
  have freeVariableCertificate3 :
    y ∉
      ((synWa (synWne (.cv z) (synC0)) (synWrex x (synCnnc)
            (.classEq (.cv w) (synCplc (synCplc (.cv z) (.cv x)) (synC1c)))))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
      Finset.mem_erase, Finset.mem_singleton, Finset.notMem_empty, fresh_y_ne_z,
      fresh_y_ne_w, fresh_y_ne_x, or_false, and_false, not_false_eq_true]
  have freeVariableCertificate4 :
    z ∉
      ((synWa (synWne A (synC0)) (synWrex x (synCnnc)
            (.classEq (.cv w) (synCplc (synCplc A (.cv x)) (synC1c)))))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
      Finset.mem_erase, Finset.mem_singleton, Finset.notMem_empty, fresh_z_not_A,
      fresh_z_ne_w, fresh_z_ne_x, or_false, and_false, not_false_eq_true]
  have p0010 :=
    @gOpkelopkabg
      (synWa (synWne (.cv z) (synC0)) (synWrex x (synCnnc)
          (.classEq (.cv w) (synCplc (synCplc (.cv z) (.cv x)) (synC1c)))))
      (synWa (synWne A (synC0)) (synWrex x (synCnnc)
          (.classEq (.cv w) (synCplc (synCplc A (.cv x)) (synC1c)))))
      (synWa (synWne A (synC0))
        (synWrex x (synCnnc) (.classEq B (synCplc (synCplc A (.cv x)) (synC1c)))))
      y z w (synCltfin) A B V W
      (by
        exact
          (show z ∉ ((synCltfin)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cltfin];
              exact (show z ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
      (by
        exact
          (show w ∉ ((synCltfin)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cltfin];
              exact (show w ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
      (by exact (show y ∉ (A).fv from (by exact fresh_y_not_A)))
      (by exact (show z ∉ (A).fv from (by exact fresh_z_not_A)))
      (by exact (show w ∉ (A).fv from (by exact fresh_w_not_A)))
      (by exact (show y ∉ (B).fv from (by exact fresh_y_not_B)))
      (by exact (show z ∉ (B).fv from (by exact fresh_z_not_B)))
      (by exact (show w ∉ (B).fv from (by exact fresh_w_not_B))) freeVariableCertificate2
      freeVariableCertificate3 freeVariableCertificate4
      (show y ≠ z from (by exact fresh_y_ne_z)) (show y ≠ w from (by exact fresh_y_ne_w))
      (show z ≠ w from (by exact fresh_z_ne_w)) p0000 p0006 p0009
  exact p0010

/-- Checked nominal proof certificate identified upstream as `g_lefinaddc`. -/
@[expose]
noncomputable def gLefinaddc (A : Class) (N : Class) (V : Class) :
    Nominal.NPrf
      (.imp (synWa (.classMem A V) (.classMem N (synCnnc)))
        (.classMem (synCopk A (synCplc A N)) (synClefin))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ N.fv ∪ V.fv
  let n : Var := freshVar proofSupport 0
  have fresh_n : n ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_n_not_A : n ∉ A.fv := by
    intro h
    exact fresh_n (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_n_not_N : n ∉ N.fv := by
    intro h
    exact fresh_n (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have p0000 := @gEqid (synCplc A N)
  have p0001 := @gAddceq2 (.cv n) N A
  have p0002 :=
    @gEqeq2d (.classEq (.cv n) N) (synCplc A (.cv n)) (synCplc A N) (synCplc A N)
      p0001
  have freeVariableCertificate0 : n ∉ ((Wff.classEq (synCplc A N) (synCplc A N))).fv :=
    by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, Finset.mem_union,
      fresh_n_not_A, fresh_n_not_N, or_false, not_false_eq_true]
  have p0003 :=
    @gRspcev (.classEq (synCplc A N) (synCplc A (.cv n)))
      (.classEq (synCplc A N) (synCplc A N)) n N (synCnnc)
      (by exact (show n ∉ (N).fv from (by exact fresh_n_not_N)))
      (by
        exact
          (show n ∉ ((synCnnc)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc];
              exact (show n ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
      freeVariableCertificate0 p0002
  have p0004 :=
    @gMpan2 (.classMem N (synCnnc)) (.classEq (synCplc A N) (synCplc A N))
      (synWrex n (synCnnc) (.classEq (synCplc A N) (synCplc A (.cv n)))) p0000 p0003
  have p0005 :=
    @gAdantl (.classMem N (synCnnc))
      (synWrex n (synCnnc) (.classEq (synCplc A N) (synCplc A (.cv n))))
      (.classMem A V) p0004
  have p0006 := @gAddcexg A N V (synCnnc)
  have freeVariableCertificate1 : n ∉ ((synCplc A N)).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, Finset.mem_union,
      fresh_n_not_A, fresh_n_not_N, or_false, not_false_eq_true]
  have p0007 :=
    @gOpklefing n A (synCplc A N) V (synCvv)
      (by exact (show n ∉ (A).fv from (by exact fresh_n_not_A))) freeVariableCertificate1
  have p0008 :=
    @gSyldan (.classMem A V) (.classMem N (synCnnc))
      (.classMem (synCplc A N) (synCvv))
      (synWb (.classMem (synCopk A (synCplc A N)) (synClefin))
        (synWrex n (synCnnc) (.classEq (synCplc A N) (synCplc A (.cv n)))))
      p0006 p0007
  have p0009 :=
    @gMpbird (synWa (.classMem A V) (.classMem N (synCnnc)))
      (.classMem (synCopk A (synCplc A N)) (synClefin))
      (synWrex n (synCnnc) (.classEq (synCplc A N) (synCplc A (.cv n)))) p0005 p0008
  exact p0009

/-- Checked nominal proof certificate identified upstream as `g_prepeano4`. -/
@[expose]
noncomputable def gPrepeano4 (M : Class) (N : Class) :
    Nominal.NPrf
      (.imp (synWa (synWa (.classMem M (synCnnc)) (.classMem N (synCnnc)))
          (synWa (.classEq (synCplc M (synC1c)) (synCplc N (synC1c)))
            (synWne (synCplc M (synC1c)) (synC0)))) (.classEq M N)) :=
  by
  let proofSupport : Finset Var := M.fv ∪ N.fv
  let a : Var := freshVar proofSupport 0
  let b : Var := freshVar proofSupport 1
  let x : Var := freshVar proofSupport 2
  have fresh_a : a ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_a_not_M : a ∉ M.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (h))
  have fresh_a_not_N : a ∉ N.fv := by
    intro h
    exact fresh_a (Finset.mem_union_right _ (h))
  have fresh_b : b ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_b_not_M : b ∉ M.fv := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (h))
  have fresh_b_not_N : b ∉ N.fv := by
    intro h
    exact fresh_b (Finset.mem_union_right _ (h))
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_x_not_M : x ∉ M.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_not_N : x ∉ N.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_a_ne_b : a ≠ b :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_b_ne_a : b ≠ a := Ne.symm fresh_a_ne_b
  have fresh_a_ne_x : a ≠ x :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_x_ne_a : x ≠ a := Ne.symm fresh_a_ne_x
  have fresh_b_ne_x : b ≠ x :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have freeVariableCertificate0 : a ∉ ((synCplc M (synC1c))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
      Finset.notMem_empty, fresh_a_not_M, or_false, not_false_eq_true]
  have p0000 := @gN0 a (synCplc M (synC1c)) freeVariableCertificate0
  have freeVariableCertificate1 : b ∉ ((Class.cv a)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_b_ne_a, not_false_eq_true]
  have freeVariableCertificate2 : x ∉ ((Class.cv a)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_x_ne_a, not_false_eq_true]
  have p0001 :=
    @gElsuc x (.cv a) M b freeVariableCertificate1 freeVariableCertificate2
      (by exact (show b ∉ (M).fv from (by exact fresh_b_not_M)))
      (show b ≠ x from (by exact fresh_b_ne_x))
  have p0002 :=
    @gSimplll (.classMem M (synCnnc)) (.classMem N (synCnnc))
      (.classEq (synCplc M (synC1c)) (synCplc N (synC1c)))
      (synWa (.classMem (.cv b) M) (.classMem (.cv x) (synCcompl (.cv b))))
  have p0003 :=
    @gSimpllr (.classMem M (synCnnc)) (.classMem N (synCnnc))
      (.classEq (synCplc M (synC1c)) (synCplc N (synC1c)))
      (synWa (.classMem (.cv b) M) (.classMem (.cv x) (synCcompl (.cv b))))
  have p0004 :=
    @gSimprl
      (synWa (synWa (.classMem M (synCnnc)) (.classMem N (synCnnc)))
        (.classEq (synCplc M (synC1c)) (synCplc N (synC1c))))
      (.classMem (.cv b) M) (.classMem (.cv x) (synCcompl (.cv b)))
  have p0005 :=
    @gSimprr
      (synWa (synWa (.classMem M (synCnnc)) (.classMem N (synCnnc)))
        (.classEq (synCplc M (synC1c)) (synCplc N (synC1c))))
      (.classMem (.cv b) M) (.classMem (.cv x) (synCcompl (.cv b)))
  have p0006 := @gVex x
  have p0007 := @gElcompl (.cv x) (.cv b) p0006
  have p0008_e01_recanon :
    Nominal.NPrf (synWb (.classMem (.cv x) (synCcompl (.cv b))) (.neg (.objMem x b))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCcompl synCnin synWnan synWa
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0007
  have p0008 :=
    @gSylib
      (synWa (synWa (synWa (.classMem M (synCnnc)) (.classMem N (synCnnc)))
          (.classEq (synCplc M (synC1c)) (synCplc N (synC1c))))
        (synWa (.classMem (.cv b) M) (.classMem (.cv x) (synCcompl (.cv b)))))
      (.classMem (.cv x) (synCcompl (.cv b))) (.neg (.objMem x b)) p0005
      p0008_e01_recanon
  have p0009 := @gElsuci (.cv b) M (.cv x) p0006
  have p0010_e00_recanon :
    Nominal.NPrf (synWb (.classMem (.cv x) (synCcompl (.cv b))) (.neg (.objMem x b))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCcompl synCnin synWnan synWa
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0007
  have p0010_e01_recanon :
    Nominal.NPrf
      (.imp (synWa (.classMem (.cv b) M) (.neg (.objMem x b)))
        (.classMem (synCun (.cv b) (synCsn (.cv x))) (synCplc M (synC1c)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWa synCun synCnin synWnan synCcompl synCsn synCplc synWrex
          synWex synC1c
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0009
  have p0010 :=
    @gSylan2b (.classMem (.cv x) (synCcompl (.cv b))) (.classMem (.cv b) M)
      (.neg (.objMem x b))
      (.classMem (synCun (.cv b) (synCsn (.cv x))) (synCplc M (synC1c)))
      p0010_e00_recanon p0010_e01_recanon
  have p0011 :=
    @gAdantl (synWa (.classMem (.cv b) M) (.classMem (.cv x) (synCcompl (.cv b))))
      (.classMem (synCun (.cv b) (synCsn (.cv x))) (synCplc M (synC1c)))
      (synWa (synWa (.classMem M (synCnnc)) (.classMem N (synCnnc)))
        (.classEq (synCplc M (synC1c)) (synCplc N (synC1c))))
      p0010
  have p0012 :=
    @gSimplr (synWa (.classMem M (synCnnc)) (.classMem N (synCnnc)))
      (.classEq (synCplc M (synC1c)) (synCplc N (synC1c)))
      (synWa (.classMem (.cv b) M) (.classMem (.cv x) (synCcompl (.cv b))))
  have p0013 :=
    @gEleqtrd
      (synWa (synWa (synWa (.classMem M (synCnnc)) (.classMem N (synCnnc)))
          (.classEq (synCplc M (synC1c)) (synCplc N (synC1c))))
        (synWa (.classMem (.cv b) M) (.classMem (.cv x) (synCcompl (.cv b)))))
      (synCun (.cv b) (synCsn (.cv x))) (synCplc M (synC1c)) (synCplc N (synC1c))
      p0011 p0012
  have p0014 := @gVex b
  have p0015 := @gNnsucelr (.cv b) N (.cv x) p0014 p0006
  have p0016_e03_recanon :
    Nominal.NPrf
      (.imp (synWa (.classMem N (synCnnc)) (synWa (.neg (.objMem x b))
            (.classMem (synCun (.cv b) (synCsn (.cv x))) (synCplc N (synC1c)))))
        (.classMem (.cv b) N)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWa synCnnc synCint
        simp (config := { failIfUnchanged := false }) only []
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0015
  have p0016 :=
    @gSyl12anc
      (synWa (synWa (synWa (.classMem M (synCnnc)) (.classMem N (synCnnc)))
          (.classEq (synCplc M (synC1c)) (synCplc N (synC1c))))
        (synWa (.classMem (.cv b) M) (.classMem (.cv x) (synCcompl (.cv b)))))
      (.classMem N (synCnnc)) (.neg (.objMem x b))
      (.classMem (synCun (.cv b) (synCsn (.cv x))) (synCplc N (synC1c)))
      (.classMem (.cv b) N) p0003 p0008 p0013 p0016_e03_recanon
  have p0017 := @gNnceleq (.cv b) M N
  have p0018 :=
    @gSyl22anc
      (synWa (synWa (synWa (.classMem M (synCnnc)) (.classMem N (synCnnc)))
          (.classEq (synCplc M (synC1c)) (synCplc N (synC1c))))
        (synWa (.classMem (.cv b) M) (.classMem (.cv x) (synCcompl (.cv b)))))
      (.classMem M (synCnnc)) (.classMem N (synCnnc)) (.classMem (.cv b) M)
      (.classMem (.cv b) N) (.classEq M N) p0002 p0003 p0004 p0016 p0017
  have p0019 :=
    @gA1d
      (synWa (synWa (synWa (.classMem M (synCnnc)) (.classMem N (synCnnc)))
          (.classEq (synCplc M (synC1c)) (synCplc N (synC1c))))
        (synWa (.classMem (.cv b) M) (.classMem (.cv x) (synCcompl (.cv b)))))
      (.classEq M N) (.classEq (.cv a) (synCun (.cv b) (synCsn (.cv x)))) p0018
  have freeVariableCertificate3 : b ∉ ((Wff.classEq M N)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union,
      fresh_b_not_M, fresh_b_not_N, or_false, not_false_eq_true]
  have freeVariableCertificate4 : x ∉ ((Wff.classEq M N)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union,
      fresh_x_not_M, fresh_x_not_N, or_false, not_false_eq_true]
  have freeVariableCertificate5 :
    b ∉
      ((synWa (synWa (.classMem M (synCnnc)) (.classMem N (synCnnc)))
          (.classEq (synCplc M (synC1c)) (synCplc N (synC1c))))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
      Finset.notMem_empty, fresh_b_not_M, fresh_b_not_N, or_false, not_false_eq_true]
  have freeVariableCertificate6 :
    x ∉
      ((synWa (synWa (.classMem M (synCnnc)) (.classMem N (synCnnc)))
          (.classEq (synCplc M (synC1c)) (synCplc N (synC1c))))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
      Finset.notMem_empty, fresh_x_not_M, fresh_x_not_N, or_false, not_false_eq_true]
  have p0020 :=
    @gRexlimdvva
      (synWa (synWa (.classMem M (synCnnc)) (.classMem N (synCnnc)))
        (.classEq (synCplc M (synC1c)) (synCplc N (synC1c))))
      (.classEq (.cv a) (synCun (.cv b) (synCsn (.cv x)))) (.classEq M N) b x M
      (synCcompl (.cv b)) (by exact (show x ∉ (M).fv from (by exact fresh_x_not_M)))
      freeVariableCertificate3 freeVariableCertificate4 freeVariableCertificate5
      freeVariableCertificate6 (show b ≠ x from (by exact fresh_b_ne_x)) p0019
  have p0021 :=
    @gSyl5bi (.classMem (.cv a) (synCplc M (synC1c)))
      (synWrex b M (synWrex x (synCcompl (.cv b))
          (.classEq (.cv a) (synCun (.cv b) (synCsn (.cv x))))))
      (synWa (synWa (.classMem M (synCnnc)) (.classMem N (synCnnc)))
        (.classEq (synCplc M (synC1c)) (synCplc N (synC1c))))
      (.classEq M N) p0001 p0020
  have freeVariableCertificate7 : a ∉ ((Wff.classEq M N)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union,
      fresh_a_not_M, fresh_a_not_N, or_false, not_false_eq_true]
  have freeVariableCertificate8 :
    a ∉
      ((synWa (synWa (.classMem M (synCnnc)) (.classMem N (synCnnc)))
          (.classEq (synCplc M (synC1c)) (synCplc N (synC1c))))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
      Finset.notMem_empty, fresh_a_not_M, fresh_a_not_N, or_false, not_false_eq_true]
  have p0022 :=
    @gExlimdv
      (synWa (synWa (.classMem M (synCnnc)) (.classMem N (synCnnc)))
        (.classEq (synCplc M (synC1c)) (synCplc N (synC1c))))
      (.classMem (.cv a) (synCplc M (synC1c))) (.classEq M N) a freeVariableCertificate7
      freeVariableCertificate8 p0021
  have p0023 :=
    @gSyl5bi (synWne (synCplc M (synC1c)) (synC0))
      (synWex a (.classMem (.cv a) (synCplc M (synC1c))))
      (synWa (synWa (.classMem M (synCnnc)) (.classMem N (synCnnc)))
        (.classEq (synCplc M (synC1c)) (synCplc N (synC1c))))
      (.classEq M N) p0000 p0022
  have p0024 :=
    @gImpr (synWa (.classMem M (synCnnc)) (.classMem N (synCnnc)))
      (.classEq (synCplc M (synC1c)) (synCplc N (synC1c)))
      (synWne (synCplc M (synC1c)) (synC0)) (.classEq M N) p0023
  exact p0024


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk009StructuralPart037`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_addcnul1`. -/
@[expose]
noncomputable def gAddcnul1 (A : Class) :
    Nominal.NPrf (.classEq (synCplc A (synC0)) (synC0)) :=
  by
  let proofSupport : Finset Var := A.fv
  let a : Var := freshVar proofSupport 0
  let b : Var := freshVar proofSupport 1
  let c : Var := freshVar proofSupport 2
  have fresh_a : a ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_a_not_A : a ∉ A.fv := by
    intro h
    exact fresh_a (h)
  have fresh_b : b ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_b_not_A : b ∉ A.fv := by
    intro h
    exact fresh_b (h)
  have fresh_c : c ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_c_not_A : c ∉ A.fv := by
    intro h
    exact fresh_c (h)
  have fresh_a_ne_b : a ≠ b :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_b_ne_a : b ≠ a := Ne.symm fresh_a_ne_b
  have fresh_a_ne_c : a ≠ c :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_c_ne_a : c ≠ a := Ne.symm fresh_a_ne_c
  have fresh_b_ne_c : b ≠ c :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have freeVariableCertificate0 : a ∉ ((synCplc A (synC0))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union,
      Finset.notMem_empty, fresh_a_not_A, or_false, not_false_eq_true]
  have p0000 := @gEq0 a (synCplc A (synC0)) freeVariableCertificate0
  have p0001 :=
    @gRex0
      (synWa (.classEq (synCin (.cv b) (.cv c)) (synC0))
        (.classEq (.cv a) (synCun (.cv b) (.cv c))))
      c
  have p0002 :=
    @gA1i
      (.neg (synWrex c (synC0) (synWa (.classEq (synCin (.cv b) (.cv c)) (synC0))
            (.classEq (.cv a) (synCun (.cv b) (.cv c))))))
      (.classMem (.cv b) A) p0001
  have p0003 :=
    @gNrex
      (synWrex c (synC0) (synWa (.classEq (synCin (.cv b) (.cv c)) (synC0))
          (.classEq (.cv a) (synCun (.cv b) (.cv c)))))
      b A p0002
  have freeVariableCertificate1 : b ∉ ((Class.cv a)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_b_ne_a, not_false_eq_true]
  have freeVariableCertificate2 : c ∉ ((Class.cv a)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_c_ne_a, not_false_eq_true]
  have p0004 :=
    @gEladdc (.cv a) A (synC0) b c freeVariableCertificate1 freeVariableCertificate2
      (by exact (show b ∉ (A).fv from (by exact fresh_b_not_A)))
      (by exact (show c ∉ (A).fv from (by exact fresh_c_not_A)))
      (by
        exact
          (show b ∉ ((synC0)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0];
              exact (show b ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
      (by
        exact
          (show c ∉ ((synC0)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0];
              exact (show c ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
      (show b ≠ c from (by exact fresh_b_ne_c))
  have p0005 :=
    @gMtbir (.classMem (.cv a) (synCplc A (synC0)))
      (synWrex b A (synWrex c (synC0) (synWa (.classEq (synCin (.cv b) (.cv c)) (synC0))
            (.classEq (.cv a) (synCun (.cv b) (.cv c))))))
      p0003 p0004
  have p0006 :=
    @gMpgbir (.classEq (synCplc A (synC0)) (synC0))
      (.neg (.classMem (.cv a) (synCplc A (synC0)))) a p0000 p0005
  exact p0006

/-- Checked nominal proof certificate identified upstream as `g_addcnnul`. -/
@[expose]
noncomputable def gAddcnnul (A : Class) (B : Class) :
    Nominal.NPrf
      (.imp (synWne (synCplc A B) (synC0))
        (synWa (synWne A (synC0)) (synWne B (synC0)))) :=
  by
  have p0000 := @gAddceq1 A (synC0) B
  have p0001 := @gAddccom (synC0) B
  have p0002 := @gAddcnul1 B
  have p0003 := @gEqtri (synCplc (synC0) B) (synCplc B (synC0)) (synC0) p0001 p0002
  have p0004 :=
    @gSyl6eq (.classEq A (synC0)) (synCplc A B) (synCplc (synC0) B) (synC0) p0000
      p0003
  have p0005 := @gNecon3i A (synC0) (synCplc A B) (synC0) p0004
  have p0006 := @gAddceq2 B (synC0) A
  have p0007 := @gAddcnul1 A
  have p0008 :=
    @gSyl6eq (.classEq B (synC0)) (synCplc A B) (synCplc A (synC0)) (synC0) p0006
      p0007
  have p0009 := @gNecon3i B (synC0) (synCplc A B) (synC0) p0008
  have p0010 :=
    @gJca (synWne (synCplc A B) (synC0)) (synWne A (synC0)) (synWne B (synC0))
      p0005 p0009
  exact p0010


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk009StructuralPart038`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_preaddccan2lem1`. -/
@[expose]
noncomputable def gPreaddccan2lem1 (P : Class) (m : Var) (N : Class) (dv_N_m : m ∉ N.fv)
    (dv_P_m : m ∉ P.fv) :
    Nominal.NPrf
      (.imp (synWa (.classMem N (synCnnc)) (.classMem P (synCnnc))) (.classMem (.cab m (.imp
              (synWa (synWne (synCplc (.cv m) N) (synC0))
                (.classEq (synCplc (.cv m) N) (synCplc (.cv m) P))) (.classEq N P)))
          (synCvv))) :=
  by
  let proofSupport : Finset Var := P.fv ∪ ({ m } : Finset Var) ∪ N.fv
  let n : Var := freshVar proofSupport 0
  let p : Var := freshVar proofSupport 1
  let t : Var := freshVar proofSupport 2
  have fresh_n : n ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_n_not_P : n ∉ P.fv := by
    intro h
    exact fresh_n (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_n_ne_m : n ≠ m := by
    intro h
    exact
      fresh_n
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_m_ne_n : m ≠ n := Ne.symm fresh_n_ne_m
  have fresh_n_not_N : n ∉ N.fv := by
    intro h
    exact fresh_n (Finset.mem_union_right _ (h))
  have fresh_p : p ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_p_not_P : p ∉ P.fv := by
    intro h
    exact fresh_p (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_p_ne_m : p ≠ m := by
    intro h
    exact
      fresh_p
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_m_ne_p : m ≠ p := Ne.symm fresh_p_ne_m
  have fresh_p_not_N : p ∉ N.fv := by
    intro h
    exact fresh_p (Finset.mem_union_right _ (h))
  have fresh_t : t ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_t_ne_m : t ≠ m := by
    intro h
    exact
      fresh_t
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_n_ne_p : n ≠ p :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_n_ne_t : n ≠ t :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_t_ne_n : t ≠ n := Ne.symm fresh_n_ne_t
  have fresh_p_ne_t : p ≠ t :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_t_ne_p : t ≠ p := Ne.symm fresh_p_ne_t
  have p0000 := @gAddceq2 (.cv n) N (.cv m)
  have p0001 :=
    @gNeeq1d (.classEq (.cv n) N) (synCplc (.cv m) (.cv n)) (synCplc (.cv m) N)
      (synC0) p0000
  have p0002 :=
    @gEqeq1d (.classEq (.cv n) N) (synCplc (.cv m) (.cv n)) (synCplc (.cv m) N)
      (synCplc (.cv m) (.cv p)) p0000
  have p0003 :=
    @gAnbi12d (.classEq (.cv n) N) (synWne (synCplc (.cv m) (.cv n)) (synC0))
      (synWne (synCplc (.cv m) N) (synC0))
      (.classEq (synCplc (.cv m) (.cv n)) (synCplc (.cv m) (.cv p)))
      (.classEq (synCplc (.cv m) N) (synCplc (.cv m) (.cv p))) p0001 p0002
  have p0004 :=
    @gImbi1d (.classEq (.cv n) N)
      (synWa (synWne (synCplc (.cv m) (.cv n)) (synC0))
        (.classEq (synCplc (.cv m) (.cv n)) (synCplc (.cv m) (.cv p))))
      (synWa (synWne (synCplc (.cv m) N) (synC0))
        (.classEq (synCplc (.cv m) N) (synCplc (.cv m) (.cv p))))
      (.classEq N P) p0003
  have freeVariableCertificate0 : m ∉ ((Wff.classEq (.cv n) N)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      fresh_m_ne_n, dv_N_m, or_false, not_false_eq_true]
  have p0005 :=
    @gAbbidv (.classEq (.cv n) N)
      (.imp (synWa (synWne (synCplc (.cv m) (.cv n)) (synC0))
          (.classEq (synCplc (.cv m) (.cv n)) (synCplc (.cv m) (.cv p)))) (.classEq N P))
      (.imp (synWa (synWne (synCplc (.cv m) N) (synC0))
          (.classEq (synCplc (.cv m) N) (synCplc (.cv m) (.cv p)))) (.classEq N P))
      m freeVariableCertificate0 p0004
  have p0006 :=
    @gEleq1d (.classEq (.cv n) N)
      (.cab m (.imp (synWa (synWne (synCplc (.cv m) (.cv n)) (synC0))
            (.classEq (synCplc (.cv m) (.cv n)) (synCplc (.cv m) (.cv p)))) (.classEq N P)))
      (.cab m (.imp (synWa (synWne (synCplc (.cv m) N) (synC0))
            (.classEq (synCplc (.cv m) N) (synCplc (.cv m) (.cv p)))) (.classEq N P)))
      (synCvv) p0005
  have p0007 := @gAddceq2 (.cv p) P (.cv m)
  have p0008 :=
    @gEqeq2d (.classEq (.cv p) P) (synCplc (.cv m) (.cv p)) (synCplc (.cv m) P)
      (synCplc (.cv m) N) p0007
  have p0009 :=
    @gAnbi2d (.classEq (.cv p) P)
      (.classEq (synCplc (.cv m) N) (synCplc (.cv m) (.cv p)))
      (.classEq (synCplc (.cv m) N) (synCplc (.cv m) P))
      (synWne (synCplc (.cv m) N) (synC0)) p0008
  have p0010 :=
    @gImbi1d (.classEq (.cv p) P)
      (synWa (synWne (synCplc (.cv m) N) (synC0))
        (.classEq (synCplc (.cv m) N) (synCplc (.cv m) (.cv p))))
      (synWa (synWne (synCplc (.cv m) N) (synC0))
        (.classEq (synCplc (.cv m) N) (synCplc (.cv m) P)))
      (.classEq N P) p0009
  have freeVariableCertificate1 : m ∉ ((Wff.classEq (.cv p) P)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      fresh_m_ne_p, dv_P_m, or_false, not_false_eq_true]
  have p0011 :=
    @gAbbidv (.classEq (.cv p) P)
      (.imp (synWa (synWne (synCplc (.cv m) N) (synC0))
          (.classEq (synCplc (.cv m) N) (synCplc (.cv m) (.cv p)))) (.classEq N P))
      (.imp (synWa (synWne (synCplc (.cv m) N) (synC0))
          (.classEq (synCplc (.cv m) N) (synCplc (.cv m) P))) (.classEq N P))
      m freeVariableCertificate1 p0010
  have p0012 :=
    @gEleq1d (.classEq (.cv p) P)
      (.cab m (.imp (synWa (synWne (synCplc (.cv m) N) (synC0))
            (.classEq (synCplc (.cv m) N) (synCplc (.cv m) (.cv p)))) (.classEq N P)))
      (.cab m (.imp (synWa (synWne (synCplc (.cv m) N) (synC0))
            (.classEq (synCplc (.cv m) N) (synCplc (.cv m) P))) (.classEq N P)))
      (synCvv) p0011
  have p0013 :=
    @gImor
      (synWa (synWne (synCplc (.cv m) (.cv n)) (synC0))
        (.classEq (synCplc (.cv m) (.cv n)) (synCplc (.cv m) (.cv p))))
      (.classEq N P)
  have p0014 :=
    @gAbbii
      (.imp (synWa (synWne (synCplc (.cv m) (.cv n)) (synC0))
          (.classEq (synCplc (.cv m) (.cv n)) (synCplc (.cv m) (.cv p)))) (.classEq N P))
      (synWo (.neg (synWa (synWne (synCplc (.cv m) (.cv n)) (synC0))
            (.classEq (synCplc (.cv m) (.cv n)) (synCplc (.cv m) (.cv p))))) (.classEq N P))
      m p0013
  have p0015 :=
    @gUnab
      (.neg (synWa (synWne (synCplc (.cv m) (.cv n)) (synC0))
          (.classEq (synCplc (.cv m) (.cv n)) (synCplc (.cv m) (.cv p)))))
      (.classEq N P) m
  have p0016 :=
    @gEqtr4i
      (.cab m (.imp (synWa (synWne (synCplc (.cv m) (.cv n)) (synC0))
            (.classEq (synCplc (.cv m) (.cv n)) (synCplc (.cv m) (.cv p)))) (.classEq N P)))
      (.cab m (synWo (.neg (synWa (synWne (synCplc (.cv m) (.cv n)) (synC0))
              (.classEq (synCplc (.cv m) (.cv n)) (synCplc (.cv m) (.cv p)))))
          (.classEq N P)))
      (synCun (.cab m (.neg (synWa (synWne (synCplc (.cv m) (.cv n)) (synC0))
              (.classEq (synCplc (.cv m) (.cv n)) (synCplc (.cv m) (.cv p))))))
        (.cab m (.classEq N P)))
      p0014 p0015
  have p0017 := @gVex m
  have p0018 :=
    @gElcompl (.cv m)
      (synCin (synCcompl (synCimak (synCcnvk (synCimagek (synCimak (synCdif (synCins3k
                      (synCcompl (synCimak
                          (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                          (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                      (synCsymdif (synCins2k (synCins2k (synCssetk)))
                        (synCun (synCins2k (synCins3k (synCssetk)))
                          (synCins3k (synCsik (synCsik (synCssetk))))))
                      (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                  (synCpw1 (synCpw1 (.cv n)))))) (synCsn (synC0)))) (synCimak (synCcnvk
            (synCin (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak
                          (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                          (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                      (synCsymdif (synCins2k (synCins2k (synCssetk)))
                        (synCun (synCins2k (synCins3k (synCssetk)))
                          (synCins3k (synCsik (synCsik (synCssetk))))))
                      (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                  (synCpw1 (synCpw1 (.cv n))))) (synCimagek (synCimak (synCdif (synCins3k
                      (synCcompl (synCimak
                          (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                          (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                      (synCsymdif (synCins2k (synCins2k (synCssetk)))
                        (synCun (synCins2k (synCins3k (synCssetk)))
                          (synCins3k (synCsik (synCsik (synCssetk))))))
                      (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                  (synCpw1 (synCpw1 (.cv p))))))) (synCvv)))
      p0017
  have p0019 :=
    @gElin (.cv m)
      (synCcompl (synCimak (synCcnvk (synCimagek (synCimak (synCdif (synCins3k
                    (synCcompl (synCimak
                        (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                        (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                    (synCsymdif (synCins2k (synCins2k (synCssetk)))
                      (synCun (synCins2k (synCins3k (synCssetk)))
                        (synCins3k (synCsik (synCsik (synCssetk))))))
                    (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                (synCpw1 (synCpw1 (.cv n)))))) (synCsn (synC0))))
      (synCimak (synCcnvk (synCin (synCimagek (synCimak (synCdif (synCins3k (synCcompl
                      (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                        (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                    (synCsymdif (synCins2k (synCins2k (synCssetk)))
                      (synCun (synCins2k (synCins3k (synCssetk)))
                        (synCins3k (synCsik (synCsik (synCssetk))))))
                    (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                (synCpw1 (synCpw1 (.cv n))))) (synCimagek (synCimak (synCdif (synCins3k
                    (synCcompl (synCimak
                        (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                        (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                    (synCsymdif (synCins2k (synCins2k (synCssetk)))
                      (synCun (synCins2k (synCins3k (synCssetk)))
                        (synCins3k (synCsik (synCsik (synCssetk))))))
                    (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                (synCpw1 (synCpw1 (.cv p))))))) (synCvv))
  have p0020 := @gN0ex
  have p0021 :=
    @gOpkelcnvk (synC0) (.cv m)
      (synCimagek (synCimak (synCdif (synCins3k (synCcompl
                (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                  (synCpw1 (synCpw1 (synC1c)))))) (synCimak
              (synCsymdif (synCins2k (synCins2k (synCssetk)))
                (synCun (synCins2k (synCins3k (synCssetk)))
                  (synCins3k (synCsik (synCsik (synCssetk))))))
              (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
          (synCpw1 (synCpw1 (.cv n)))))
      p0020 p0017
  have p0023 :=
    @gElimaksn
      (synCcnvk (synCimagek (synCimak (synCdif (synCins3k (synCcompl
                  (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                    (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                (synCsymdif (synCins2k (synCins2k (synCssetk)))
                  (synCun (synCins2k (synCins3k (synCssetk)))
                    (synCins3k (synCsik (synCsik (synCssetk))))))
                (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
            (synCpw1 (synCpw1 (.cv n))))))
      (synC0) (.cv m) p0020 p0017
  have p0024 := @gDfaddc2 (.cv m) (.cv n)
  have p0025 :=
    @gEqeq2i (synCplc (.cv m) (.cv n))
      (synCimak (synCimak (synCdif (synCins3k (synCcompl
                (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                  (synCpw1 (synCpw1 (synC1c)))))) (synCimak
              (synCsymdif (synCins2k (synCins2k (synCssetk)))
                (synCun (synCins2k (synCins3k (synCssetk)))
                  (synCins3k (synCsik (synCsik (synCssetk))))))
              (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
          (synCpw1 (synCpw1 (.cv n)))) (.cv m))
      (synC0) p0024
  have p0026 := @gEqcom (synCplc (.cv m) (.cv n)) (synC0)
  have p0028 :=
    @gOpkelimagek (.cv m) (synC0)
      (synCimak (synCdif (synCins3k (synCcompl
              (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                (synCpw1 (synCpw1 (synC1c)))))) (synCimak
            (synCsymdif (synCins2k (synCins2k (synCssetk)))
              (synCun (synCins2k (synCins3k (synCssetk)))
                (synCins3k (synCsik (synCsik (synCssetk))))))
            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
        (synCpw1 (synCpw1 (.cv n))))
      p0017 p0020
  have p0029 :=
    @gN3bitr4i (.classEq (synC0) (synCplc (.cv m) (.cv n)))
      (.classEq (synC0) (synCimak (synCimak (synCdif (synCins3k (synCcompl
                  (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                    (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                (synCsymdif (synCins2k (synCins2k (synCssetk)))
                  (synCun (synCins2k (synCins3k (synCssetk)))
                    (synCins3k (synCsik (synCsik (synCssetk))))))
                (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
            (synCpw1 (synCpw1 (.cv n)))) (.cv m)))
      (.classEq (synCplc (.cv m) (.cv n)) (synC0))
      (.classMem (synCopk (.cv m) (synC0)) (synCimagek (synCimak (synCdif (synCins3k
                (synCcompl
                  (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                    (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                (synCsymdif (synCins2k (synCins2k (synCssetk)))
                  (synCun (synCins2k (synCins3k (synCssetk)))
                    (synCins3k (synCsik (synCsik (synCssetk))))))
                (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
            (synCpw1 (synCpw1 (.cv n))))))
      p0025 p0026 p0028
  have p0030 :=
    @gN3bitr4i
      (.classMem (synCopk (synC0) (.cv m)) (synCcnvk (synCimagek (synCimak (synCdif
                (synCins3k (synCcompl (synCimak
                      (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                      (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                  (synCsymdif (synCins2k (synCins2k (synCssetk)))
                    (synCun (synCins2k (synCins3k (synCssetk)))
                      (synCins3k (synCsik (synCsik (synCssetk))))))
                  (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
              (synCpw1 (synCpw1 (.cv n)))))))
      (.classMem (synCopk (.cv m) (synC0)) (synCimagek (synCimak (synCdif (synCins3k
                (synCcompl
                  (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                    (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                (synCsymdif (synCins2k (synCins2k (synCssetk)))
                  (synCun (synCins2k (synCins3k (synCssetk)))
                    (synCins3k (synCsik (synCsik (synCssetk))))))
                (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
            (synCpw1 (synCpw1 (.cv n))))))
      (.classMem (.cv m) (synCimak (synCcnvk (synCimagek (synCimak (synCdif (synCins3k
                    (synCcompl (synCimak
                        (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                        (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                    (synCsymdif (synCins2k (synCins2k (synCssetk)))
                      (synCun (synCins2k (synCins3k (synCssetk)))
                        (synCins3k (synCsik (synCsik (synCssetk))))))
                    (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                (synCpw1 (synCpw1 (.cv n)))))) (synCsn (synC0))))
      (.classEq (synCplc (.cv m) (.cv n)) (synC0)) p0021 p0023 p0029
  have p0031 :=
    @gNotbii
      (.classMem (.cv m) (synCimak (synCcnvk (synCimagek (synCimak (synCdif (synCins3k
                    (synCcompl (synCimak
                        (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                        (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                    (synCsymdif (synCins2k (synCins2k (synCssetk)))
                      (synCun (synCins2k (synCins3k (synCssetk)))
                        (synCins3k (synCsik (synCsik (synCssetk))))))
                    (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                (synCpw1 (synCpw1 (.cv n)))))) (synCsn (synC0))))
      (.classEq (synCplc (.cv m) (.cv n)) (synC0)) p0030
  have p0032 :=
    @gElcompl (.cv m)
      (synCimak (synCcnvk (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak
                      (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                      (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                  (synCsymdif (synCins2k (synCins2k (synCssetk)))
                    (synCun (synCins2k (synCins3k (synCssetk)))
                      (synCins3k (synCsik (synCsik (synCssetk))))))
                  (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
              (synCpw1 (synCpw1 (.cv n)))))) (synCsn (synC0)))
      p0017
  have p0033 := (Nominal.biimpRefl (synWne (synCplc (.cv m) (.cv n)) (synC0)))
  have p0034 :=
    @gN3bitr4i
      (.neg (.classMem (.cv m) (synCimak (synCcnvk (synCimagek (synCimak (synCdif
                    (synCins3k (synCcompl (synCimak
                          (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                          (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                      (synCsymdif (synCins2k (synCins2k (synCssetk)))
                        (synCun (synCins2k (synCins3k (synCssetk)))
                          (synCins3k (synCsik (synCsik (synCssetk))))))
                      (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                  (synCpw1 (synCpw1 (.cv n)))))) (synCsn (synC0)))))
      (.neg (.classEq (synCplc (.cv m) (.cv n)) (synC0)))
      (.classMem (.cv m) (synCcompl (synCimak (synCcnvk (synCimagek (synCimak (synCdif
                    (synCins3k (synCcompl (synCimak
                          (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                          (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                      (synCsymdif (synCins2k (synCins2k (synCssetk)))
                        (synCun (synCins2k (synCins3k (synCssetk)))
                          (synCins3k (synCsik (synCsik (synCssetk))))))
                      (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                  (synCpw1 (synCpw1 (.cv n)))))) (synCsn (synC0)))))
      (synWne (synCplc (.cv m) (.cv n)) (synC0)) p0031 p0032 p0033
  have p0035 :=
    @gRexv
      (.classMem (synCopk (.cv t) (.cv m)) (synCcnvk (synCin (synCimagek (synCimak
                (synCdif (synCins3k (synCcompl (synCimak
                        (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                        (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                    (synCsymdif (synCins2k (synCins2k (synCssetk)))
                      (synCun (synCins2k (synCins3k (synCssetk)))
                        (synCins3k (synCsik (synCsik (synCssetk))))))
                    (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                (synCpw1 (synCpw1 (.cv n))))) (synCimagek (synCimak (synCdif (synCins3k
                    (synCcompl (synCimak
                        (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                        (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                    (synCsymdif (synCins2k (synCins2k (synCssetk)))
                      (synCun (synCins2k (synCins3k (synCssetk)))
                        (synCins3k (synCsik (synCsik (synCssetk))))))
                    (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                (synCpw1 (synCpw1 (.cv p))))))))
      t
  have p0036 := @gVex t
  have p0037 :=
    @gOpkelcnvk (.cv t) (.cv m)
      (synCin (synCimagek (synCimak (synCdif (synCins3k (synCcompl
                  (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                    (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                (synCsymdif (synCins2k (synCins2k (synCssetk)))
                  (synCun (synCins2k (synCins3k (synCssetk)))
                    (synCins3k (synCsik (synCsik (synCssetk))))))
                (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
            (synCpw1 (synCpw1 (.cv n))))) (synCimagek (synCimak (synCdif (synCins3k
                (synCcompl
                  (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                    (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                (synCsymdif (synCins2k (synCins2k (synCssetk)))
                  (synCun (synCins2k (synCins3k (synCssetk)))
                    (synCins3k (synCsik (synCsik (synCssetk))))))
                (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
            (synCpw1 (synCpw1 (.cv p))))))
      p0036 p0017
  have p0038 :=
    @gElin (synCopk (.cv m) (.cv t))
      (synCimagek (synCimak (synCdif (synCins3k (synCcompl
                (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                  (synCpw1 (synCpw1 (synC1c)))))) (synCimak
              (synCsymdif (synCins2k (synCins2k (synCssetk)))
                (synCun (synCins2k (synCins3k (synCssetk)))
                  (synCins3k (synCsik (synCsik (synCssetk))))))
              (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
          (synCpw1 (synCpw1 (.cv n)))))
      (synCimagek (synCimak (synCdif (synCins3k (synCcompl
                (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                  (synCpw1 (synCpw1 (synC1c)))))) (synCimak
              (synCsymdif (synCins2k (synCins2k (synCssetk)))
                (synCun (synCins2k (synCins3k (synCssetk)))
                  (synCins3k (synCsik (synCsik (synCssetk))))))
              (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
          (synCpw1 (synCpw1 (.cv p)))))
  have p0039 :=
    @gOpkelimagek (.cv m) (.cv t)
      (synCimak (synCdif (synCins3k (synCcompl
              (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                (synCpw1 (synCpw1 (synC1c)))))) (synCimak
            (synCsymdif (synCins2k (synCins2k (synCssetk)))
              (synCun (synCins2k (synCins3k (synCssetk)))
                (synCins3k (synCsik (synCsik (synCssetk))))))
            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
        (synCpw1 (synCpw1 (.cv n))))
      p0017 p0036
  have p0040 :=
    @gEqeq2i (synCplc (.cv m) (.cv n))
      (synCimak (synCimak (synCdif (synCins3k (synCcompl
                (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                  (synCpw1 (synCpw1 (synC1c)))))) (synCimak
              (synCsymdif (synCins2k (synCins2k (synCssetk)))
                (synCun (synCins2k (synCins3k (synCssetk)))
                  (synCins3k (synCsik (synCsik (synCssetk))))))
              (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
          (synCpw1 (synCpw1 (.cv n)))) (.cv m))
      (.cv t) p0024
  have p0041 :=
    @gBitr4i
      (.classMem (synCopk (.cv m) (.cv t)) (synCimagek (synCimak (synCdif (synCins3k
                (synCcompl
                  (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                    (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                (synCsymdif (synCins2k (synCins2k (synCssetk)))
                  (synCun (synCins2k (synCins3k (synCssetk)))
                    (synCins3k (synCsik (synCsik (synCssetk))))))
                (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
            (synCpw1 (synCpw1 (.cv n))))))
      (.classEq (.cv t) (synCimak (synCimak (synCdif (synCins3k (synCcompl
                  (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                    (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                (synCsymdif (synCins2k (synCins2k (synCssetk)))
                  (synCun (synCins2k (synCins3k (synCssetk)))
                    (synCins3k (synCsik (synCsik (synCssetk))))))
                (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
            (synCpw1 (synCpw1 (.cv n)))) (.cv m)))
      (.classEq (.cv t) (synCplc (.cv m) (.cv n))) p0039 p0040
  have p0042 :=
    @gOpkelimagek (.cv m) (.cv t)
      (synCimak (synCdif (synCins3k (synCcompl
              (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                (synCpw1 (synCpw1 (synC1c)))))) (synCimak
            (synCsymdif (synCins2k (synCins2k (synCssetk)))
              (synCun (synCins2k (synCins3k (synCssetk)))
                (synCins3k (synCsik (synCsik (synCssetk))))))
            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
        (synCpw1 (synCpw1 (.cv p))))
      p0017 p0036
  have p0043 := @gDfaddc2 (.cv m) (.cv p)
  have p0044 :=
    @gEqeq2i (synCplc (.cv m) (.cv p))
      (synCimak (synCimak (synCdif (synCins3k (synCcompl
                (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                  (synCpw1 (synCpw1 (synC1c)))))) (synCimak
              (synCsymdif (synCins2k (synCins2k (synCssetk)))
                (synCun (synCins2k (synCins3k (synCssetk)))
                  (synCins3k (synCsik (synCsik (synCssetk))))))
              (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
          (synCpw1 (synCpw1 (.cv p)))) (.cv m))
      (.cv t) p0043
  have p0045 :=
    @gBitr4i
      (.classMem (synCopk (.cv m) (.cv t)) (synCimagek (synCimak (synCdif (synCins3k
                (synCcompl
                  (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                    (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                (synCsymdif (synCins2k (synCins2k (synCssetk)))
                  (synCun (synCins2k (synCins3k (synCssetk)))
                    (synCins3k (synCsik (synCsik (synCssetk))))))
                (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
            (synCpw1 (synCpw1 (.cv p))))))
      (.classEq (.cv t) (synCimak (synCimak (synCdif (synCins3k (synCcompl
                  (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                    (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                (synCsymdif (synCins2k (synCins2k (synCssetk)))
                  (synCun (synCins2k (synCins3k (synCssetk)))
                    (synCins3k (synCsik (synCsik (synCssetk))))))
                (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
            (synCpw1 (synCpw1 (.cv p)))) (.cv m)))
      (.classEq (.cv t) (synCplc (.cv m) (.cv p))) p0042 p0044
  have p0046 :=
    @gAnbi12i
      (.classMem (synCopk (.cv m) (.cv t)) (synCimagek (synCimak (synCdif (synCins3k
                (synCcompl
                  (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                    (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                (synCsymdif (synCins2k (synCins2k (synCssetk)))
                  (synCun (synCins2k (synCins3k (synCssetk)))
                    (synCins3k (synCsik (synCsik (synCssetk))))))
                (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
            (synCpw1 (synCpw1 (.cv n))))))
      (.classEq (.cv t) (synCplc (.cv m) (.cv n)))
      (.classMem (synCopk (.cv m) (.cv t)) (synCimagek (synCimak (synCdif (synCins3k
                (synCcompl
                  (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                    (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                (synCsymdif (synCins2k (synCins2k (synCssetk)))
                  (synCun (synCins2k (synCins3k (synCssetk)))
                    (synCins3k (synCsik (synCsik (synCssetk))))))
                (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
            (synCpw1 (synCpw1 (.cv p))))))
      (.classEq (.cv t) (synCplc (.cv m) (.cv p))) p0041 p0045
  have p0047 :=
    @gBitri
      (.classMem (synCopk (.cv m) (.cv t)) (synCin (synCimagek (synCimak (synCdif
                (synCins3k (synCcompl (synCimak
                      (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                      (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                  (synCsymdif (synCins2k (synCins2k (synCssetk)))
                    (synCun (synCins2k (synCins3k (synCssetk)))
                      (synCins3k (synCsik (synCsik (synCssetk))))))
                  (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
              (synCpw1 (synCpw1 (.cv n))))) (synCimagek (synCimak (synCdif (synCins3k
                  (synCcompl (synCimak
                      (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                      (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                  (synCsymdif (synCins2k (synCins2k (synCssetk)))
                    (synCun (synCins2k (synCins3k (synCssetk)))
                      (synCins3k (synCsik (synCsik (synCssetk))))))
                  (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
              (synCpw1 (synCpw1 (.cv p)))))))
      (synWa (.classMem (synCopk (.cv m) (.cv t)) (synCimagek (synCimak (synCdif
                (synCins3k (synCcompl (synCimak
                      (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                      (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                  (synCsymdif (synCins2k (synCins2k (synCssetk)))
                    (synCun (synCins2k (synCins3k (synCssetk)))
                      (synCins3k (synCsik (synCsik (synCssetk))))))
                  (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
              (synCpw1 (synCpw1 (.cv n)))))) (.classMem (synCopk (.cv m) (.cv t))
          (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak
                      (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                      (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                  (synCsymdif (synCins2k (synCins2k (synCssetk)))
                    (synCun (synCins2k (synCins3k (synCssetk)))
                      (synCins3k (synCsik (synCsik (synCssetk))))))
                  (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
              (synCpw1 (synCpw1 (.cv p)))))))
      (synWa (.classEq (.cv t) (synCplc (.cv m) (.cv n)))
        (.classEq (.cv t) (synCplc (.cv m) (.cv p))))
      p0038 p0046
  have p0048 :=
    @gBitri
      (.classMem (synCopk (.cv t) (.cv m)) (synCcnvk (synCin (synCimagek (synCimak
                (synCdif (synCins3k (synCcompl (synCimak
                        (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                        (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                    (synCsymdif (synCins2k (synCins2k (synCssetk)))
                      (synCun (synCins2k (synCins3k (synCssetk)))
                        (synCins3k (synCsik (synCsik (synCssetk))))))
                    (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                (synCpw1 (synCpw1 (.cv n))))) (synCimagek (synCimak (synCdif (synCins3k
                    (synCcompl (synCimak
                        (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                        (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                    (synCsymdif (synCins2k (synCins2k (synCssetk)))
                      (synCun (synCins2k (synCins3k (synCssetk)))
                        (synCins3k (synCsik (synCsik (synCssetk))))))
                    (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                (synCpw1 (synCpw1 (.cv p))))))))
      (.classMem (synCopk (.cv m) (.cv t)) (synCin (synCimagek (synCimak (synCdif
                (synCins3k (synCcompl (synCimak
                      (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                      (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                  (synCsymdif (synCins2k (synCins2k (synCssetk)))
                    (synCun (synCins2k (synCins3k (synCssetk)))
                      (synCins3k (synCsik (synCsik (synCssetk))))))
                  (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
              (synCpw1 (synCpw1 (.cv n))))) (synCimagek (synCimak (synCdif (synCins3k
                  (synCcompl (synCimak
                      (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                      (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                  (synCsymdif (synCins2k (synCins2k (synCssetk)))
                    (synCun (synCins2k (synCins3k (synCssetk)))
                      (synCins3k (synCsik (synCsik (synCssetk))))))
                  (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
              (synCpw1 (synCpw1 (.cv p)))))))
      (synWa (.classEq (.cv t) (synCplc (.cv m) (.cv n)))
        (.classEq (.cv t) (synCplc (.cv m) (.cv p))))
      p0037 p0047
  have p0049 :=
    @gExbii
      (.classMem (synCopk (.cv t) (.cv m)) (synCcnvk (synCin (synCimagek (synCimak
                (synCdif (synCins3k (synCcompl (synCimak
                        (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                        (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                    (synCsymdif (synCins2k (synCins2k (synCssetk)))
                      (synCun (synCins2k (synCins3k (synCssetk)))
                        (synCins3k (synCsik (synCsik (synCssetk))))))
                    (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                (synCpw1 (synCpw1 (.cv n))))) (synCimagek (synCimak (synCdif (synCins3k
                    (synCcompl (synCimak
                        (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                        (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                    (synCsymdif (synCins2k (synCins2k (synCssetk)))
                      (synCun (synCins2k (synCins3k (synCssetk)))
                        (synCins3k (synCsik (synCsik (synCssetk))))))
                    (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                (synCpw1 (synCpw1 (.cv p))))))))
      (synWa (.classEq (.cv t) (synCplc (.cv m) (.cv n)))
        (.classEq (.cv t) (synCplc (.cv m) (.cv p))))
      t p0048
  have p0050 :=
    @gBitri
      (synWrex t (synCvv) (.classMem (synCopk (.cv t) (.cv m)) (synCcnvk (synCin
              (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak
                          (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                          (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                      (synCsymdif (synCins2k (synCins2k (synCssetk)))
                        (synCun (synCins2k (synCins3k (synCssetk)))
                          (synCins3k (synCsik (synCsik (synCssetk))))))
                      (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                  (synCpw1 (synCpw1 (.cv n))))) (synCimagek (synCimak (synCdif (synCins3k
                      (synCcompl (synCimak
                          (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                          (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                      (synCsymdif (synCins2k (synCins2k (synCssetk)))
                        (synCun (synCins2k (synCins3k (synCssetk)))
                          (synCins3k (synCsik (synCsik (synCssetk))))))
                      (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                  (synCpw1 (synCpw1 (.cv p)))))))))
      (synWex t (.classMem (synCopk (.cv t) (.cv m)) (synCcnvk (synCin (synCimagek
                (synCimak (synCdif (synCins3k (synCcompl (synCimak
                          (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                          (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                      (synCsymdif (synCins2k (synCins2k (synCssetk)))
                        (synCun (synCins2k (synCins3k (synCssetk)))
                          (synCins3k (synCsik (synCsik (synCssetk))))))
                      (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                  (synCpw1 (synCpw1 (.cv n))))) (synCimagek (synCimak (synCdif (synCins3k
                      (synCcompl (synCimak
                          (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                          (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                      (synCsymdif (synCins2k (synCins2k (synCssetk)))
                        (synCun (synCins2k (synCins3k (synCssetk)))
                          (synCins3k (synCsik (synCsik (synCssetk))))))
                      (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                  (synCpw1 (synCpw1 (.cv p)))))))))
      (synWex t (synWa (.classEq (.cv t) (synCplc (.cv m) (.cv n)))
          (.classEq (.cv t) (synCplc (.cv m) (.cv p)))))
      p0035 p0049
  have freeVariableCertificate2 :
    t ∉
      ((synCcnvk (synCin (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak
                        (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                        (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                    (synCsymdif (synCins2k (synCins2k (synCssetk)))
                      (synCun (synCins2k (synCins3k (synCssetk)))
                        (synCins3k (synCsik (synCsik (synCssetk))))))
                    (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                (synCpw1 (synCpw1 (.cv n))))) (synCimagek (synCimak (synCdif (synCins3k
                    (synCcompl (synCimak
                        (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                        (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                    (synCsymdif (synCins2k (synCins2k (synCssetk)))
                      (synCun (synCins2k (synCins3k (synCssetk)))
                        (synCins3k (synCsik (synCsik (synCssetk))))))
                    (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                (synCpw1 (synCpw1 (.cv p)))))))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimagek,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      Finset.notMem_empty, fresh_t_ne_n, fresh_t_ne_p, or_false, not_false_eq_true]
  have freeVariableCertificate3 : t ∉ ((Class.cv m)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_t_ne_m, not_false_eq_true]
  have p0051 :=
    @gElimak t
      (synCcnvk (synCin (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak
                      (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                      (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                  (synCsymdif (synCins2k (synCins2k (synCssetk)))
                    (synCun (synCins2k (synCins3k (synCssetk)))
                      (synCins3k (synCsik (synCsik (synCssetk))))))
                  (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
              (synCpw1 (synCpw1 (.cv n))))) (synCimagek (synCimak (synCdif (synCins3k
                  (synCcompl (synCimak
                      (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                      (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                  (synCsymdif (synCins2k (synCins2k (synCssetk)))
                    (synCun (synCins2k (synCins3k (synCssetk)))
                      (synCins3k (synCsik (synCsik (synCssetk))))))
                  (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
              (synCpw1 (synCpw1 (.cv p)))))))
      (synCvv) (.cv m) freeVariableCertificate2
      (by
        exact
          (show t ∉ ((synCvv)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv];
              exact (show t ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
      freeVariableCertificate3 p0017
  have p0052 := @gVex n
  have p0053 := @gAddcex (.cv m) (.cv n) p0017 p0052
  have freeVariableCertificate4 : t ∉ ((synCplc (.cv m) (.cv n))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      fresh_t_ne_m, fresh_t_ne_n, or_false, not_false_eq_true]
  have freeVariableCertificate5 : t ∉ ((synCplc (.cv m) (.cv p))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      fresh_t_ne_m, fresh_t_ne_p, or_false, not_false_eq_true]
  have p0054 :=
    @gEqvinc t (synCplc (.cv m) (.cv n)) (synCplc (.cv m) (.cv p))
      freeVariableCertificate4 freeVariableCertificate5 p0053
  have p0055 :=
    @gN3bitr4i
      (synWrex t (synCvv) (.classMem (synCopk (.cv t) (.cv m)) (synCcnvk (synCin
              (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak
                          (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                          (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                      (synCsymdif (synCins2k (synCins2k (synCssetk)))
                        (synCun (synCins2k (synCins3k (synCssetk)))
                          (synCins3k (synCsik (synCsik (synCssetk))))))
                      (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                  (synCpw1 (synCpw1 (.cv n))))) (synCimagek (synCimak (synCdif (synCins3k
                      (synCcompl (synCimak
                          (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                          (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                      (synCsymdif (synCins2k (synCins2k (synCssetk)))
                        (synCun (synCins2k (synCins3k (synCssetk)))
                          (synCins3k (synCsik (synCsik (synCssetk))))))
                      (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                  (synCpw1 (synCpw1 (.cv p)))))))))
      (synWex t (synWa (.classEq (.cv t) (synCplc (.cv m) (.cv n)))
          (.classEq (.cv t) (synCplc (.cv m) (.cv p)))))
      (.classMem (.cv m) (synCimak (synCcnvk (synCin (synCimagek (synCimak (synCdif
                    (synCins3k (synCcompl (synCimak
                          (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                          (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                      (synCsymdif (synCins2k (synCins2k (synCssetk)))
                        (synCun (synCins2k (synCins3k (synCssetk)))
                          (synCins3k (synCsik (synCsik (synCssetk))))))
                      (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                  (synCpw1 (synCpw1 (.cv n))))) (synCimagek (synCimak (synCdif (synCins3k
                      (synCcompl (synCimak
                          (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                          (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                      (synCsymdif (synCins2k (synCins2k (synCssetk)))
                        (synCun (synCins2k (synCins3k (synCssetk)))
                          (synCins3k (synCsik (synCsik (synCssetk))))))
                      (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                  (synCpw1 (synCpw1 (.cv p))))))) (synCvv)))
      (.classEq (synCplc (.cv m) (.cv n)) (synCplc (.cv m) (.cv p))) p0050 p0051 p0054
  have p0056 :=
    @gAnbi12i
      (.classMem (.cv m) (synCcompl (synCimak (synCcnvk (synCimagek (synCimak (synCdif
                    (synCins3k (synCcompl (synCimak
                          (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                          (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                      (synCsymdif (synCins2k (synCins2k (synCssetk)))
                        (synCun (synCins2k (synCins3k (synCssetk)))
                          (synCins3k (synCsik (synCsik (synCssetk))))))
                      (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                  (synCpw1 (synCpw1 (.cv n)))))) (synCsn (synC0)))))
      (synWne (synCplc (.cv m) (.cv n)) (synC0))
      (.classMem (.cv m) (synCimak (synCcnvk (synCin (synCimagek (synCimak (synCdif
                    (synCins3k (synCcompl (synCimak
                          (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                          (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                      (synCsymdif (synCins2k (synCins2k (synCssetk)))
                        (synCun (synCins2k (synCins3k (synCssetk)))
                          (synCins3k (synCsik (synCsik (synCssetk))))))
                      (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                  (synCpw1 (synCpw1 (.cv n))))) (synCimagek (synCimak (synCdif (synCins3k
                      (synCcompl (synCimak
                          (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                          (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                      (synCsymdif (synCins2k (synCins2k (synCssetk)))
                        (synCun (synCins2k (synCins3k (synCssetk)))
                          (synCins3k (synCsik (synCsik (synCssetk))))))
                      (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                  (synCpw1 (synCpw1 (.cv p))))))) (synCvv)))
      (.classEq (synCplc (.cv m) (.cv n)) (synCplc (.cv m) (.cv p))) p0034 p0055
  have p0057 :=
    @gBitri
      (.classMem (.cv m) (synCin (synCcompl (synCimak (synCcnvk (synCimagek (synCimak
                    (synCdif (synCins3k (synCcompl (synCimak
                            (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                            (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                        (synCsymdif (synCins2k (synCins2k (synCssetk)))
                          (synCun (synCins2k (synCins3k (synCssetk)))
                            (synCins3k (synCsik (synCsik (synCssetk))))))
                        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                    (synCpw1 (synCpw1 (.cv n)))))) (synCsn (synC0)))) (synCimak (synCcnvk
              (synCin (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak
                            (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                            (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                        (synCsymdif (synCins2k (synCins2k (synCssetk)))
                          (synCun (synCins2k (synCins3k (synCssetk)))
                            (synCins3k (synCsik (synCsik (synCssetk))))))
                        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                    (synCpw1 (synCpw1 (.cv n))))) (synCimagek (synCimak (synCdif
                      (synCins3k (synCcompl (synCimak
                            (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                            (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                        (synCsymdif (synCins2k (synCins2k (synCssetk)))
                          (synCun (synCins2k (synCins3k (synCssetk)))
                            (synCins3k (synCsik (synCsik (synCssetk))))))
                        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                    (synCpw1 (synCpw1 (.cv p))))))) (synCvv))))
      (synWa (.classMem (.cv m) (synCcompl (synCimak (synCcnvk (synCimagek (synCimak
                    (synCdif (synCins3k (synCcompl (synCimak
                            (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                            (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                        (synCsymdif (synCins2k (synCins2k (synCssetk)))
                          (synCun (synCins2k (synCins3k (synCssetk)))
                            (synCins3k (synCsik (synCsik (synCssetk))))))
                        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                    (synCpw1 (synCpw1 (.cv n)))))) (synCsn (synC0))))) (.classMem (.cv m)
          (synCimak (synCcnvk (synCin (synCimagek (synCimak (synCdif (synCins3k
                        (synCcompl (synCimak
                            (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                            (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                        (synCsymdif (synCins2k (synCins2k (synCssetk)))
                          (synCun (synCins2k (synCins3k (synCssetk)))
                            (synCins3k (synCsik (synCsik (synCssetk))))))
                        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                    (synCpw1 (synCpw1 (.cv n))))) (synCimagek (synCimak (synCdif
                      (synCins3k (synCcompl (synCimak
                            (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                            (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                        (synCsymdif (synCins2k (synCins2k (synCssetk)))
                          (synCun (synCins2k (synCins3k (synCssetk)))
                            (synCins3k (synCsik (synCsik (synCssetk))))))
                        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                    (synCpw1 (synCpw1 (.cv p))))))) (synCvv))))
      (synWa (synWne (synCplc (.cv m) (.cv n)) (synC0))
        (.classEq (synCplc (.cv m) (.cv n)) (synCplc (.cv m) (.cv p))))
      p0019 p0056
  have p0058 :=
    @gNotbii
      (.classMem (.cv m) (synCin (synCcompl (synCimak (synCcnvk (synCimagek (synCimak
                    (synCdif (synCins3k (synCcompl (synCimak
                            (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                            (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                        (synCsymdif (synCins2k (synCins2k (synCssetk)))
                          (synCun (synCins2k (synCins3k (synCssetk)))
                            (synCins3k (synCsik (synCsik (synCssetk))))))
                        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                    (synCpw1 (synCpw1 (.cv n)))))) (synCsn (synC0)))) (synCimak (synCcnvk
              (synCin (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak
                            (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                            (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                        (synCsymdif (synCins2k (synCins2k (synCssetk)))
                          (synCun (synCins2k (synCins3k (synCssetk)))
                            (synCins3k (synCsik (synCsik (synCssetk))))))
                        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                    (synCpw1 (synCpw1 (.cv n))))) (synCimagek (synCimak (synCdif
                      (synCins3k (synCcompl (synCimak
                            (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                            (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                        (synCsymdif (synCins2k (synCins2k (synCssetk)))
                          (synCun (synCins2k (synCins3k (synCssetk)))
                            (synCins3k (synCsik (synCsik (synCssetk))))))
                        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                    (synCpw1 (synCpw1 (.cv p))))))) (synCvv))))
      (synWa (synWne (synCplc (.cv m) (.cv n)) (synC0))
        (.classEq (synCplc (.cv m) (.cv n)) (synCplc (.cv m) (.cv p))))
      p0057
  have p0059 :=
    @gBitri
      (.classMem (.cv m) (synCcompl (synCin (synCcompl (synCimak (synCcnvk (synCimagek
                    (synCimak (synCdif (synCins3k (synCcompl (synCimak
                              (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                              (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                          (synCsymdif (synCins2k (synCins2k (synCssetk)))
                            (synCun (synCins2k (synCins3k (synCssetk)))
                              (synCins3k (synCsik (synCsik (synCssetk))))))
                          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                      (synCpw1 (synCpw1 (.cv n)))))) (synCsn (synC0)))) (synCimak
              (synCcnvk (synCin (synCimagek (synCimak (synCdif (synCins3k (synCcompl
                            (synCimak (synCin (synCins3k (synCssetk))
                                (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                        (synCimak (synCsymdif (synCins2k (synCins2k (synCssetk)))
                            (synCun (synCins2k (synCins3k (synCssetk)))
                              (synCins3k (synCsik (synCsik (synCssetk))))))
                          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                      (synCpw1 (synCpw1 (.cv n))))) (synCimagek (synCimak (synCdif
                        (synCins3k (synCcompl (synCimak (synCin (synCins3k (synCssetk))
                                (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                        (synCimak (synCsymdif (synCins2k (synCins2k (synCssetk)))
                            (synCun (synCins2k (synCins3k (synCssetk)))
                              (synCins3k (synCsik (synCsik (synCssetk))))))
                          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                      (synCpw1 (synCpw1 (.cv p))))))) (synCvv)))))
      (.neg (.classMem (.cv m) (synCin (synCcompl (synCimak (synCcnvk (synCimagek
                    (synCimak (synCdif (synCins3k (synCcompl (synCimak
                              (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                              (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                          (synCsymdif (synCins2k (synCins2k (synCssetk)))
                            (synCun (synCins2k (synCins3k (synCssetk)))
                              (synCins3k (synCsik (synCsik (synCssetk))))))
                          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                      (synCpw1 (synCpw1 (.cv n)))))) (synCsn (synC0)))) (synCimak
              (synCcnvk (synCin (synCimagek (synCimak (synCdif (synCins3k (synCcompl
                            (synCimak (synCin (synCins3k (synCssetk))
                                (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                        (synCimak (synCsymdif (synCins2k (synCins2k (synCssetk)))
                            (synCun (synCins2k (synCins3k (synCssetk)))
                              (synCins3k (synCsik (synCsik (synCssetk))))))
                          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                      (synCpw1 (synCpw1 (.cv n))))) (synCimagek (synCimak (synCdif
                        (synCins3k (synCcompl (synCimak (synCin (synCins3k (synCssetk))
                                (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                        (synCimak (synCsymdif (synCins2k (synCins2k (synCssetk)))
                            (synCun (synCins2k (synCins3k (synCssetk)))
                              (synCins3k (synCsik (synCsik (synCssetk))))))
                          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                      (synCpw1 (synCpw1 (.cv p))))))) (synCvv)))))
      (.neg (synWa (synWne (synCplc (.cv m) (.cv n)) (synC0))
          (.classEq (synCplc (.cv m) (.cv n)) (synCplc (.cv m) (.cv p)))))
      p0018 p0058
  have freeVariableCertificate6 :
    m ∉
      ((synCcompl (synCin (synCcompl (synCimak (synCcnvk (synCimagek (synCimak (synCdif
                        (synCins3k (synCcompl (synCimak (synCin (synCins3k (synCssetk))
                                (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                        (synCimak (synCsymdif (synCins2k (synCins2k (synCssetk)))
                            (synCun (synCins2k (synCins3k (synCssetk)))
                              (synCins3k (synCsik (synCsik (synCssetk))))))
                          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                      (synCpw1 (synCpw1 (.cv n)))))) (synCsn (synC0)))) (synCimak
              (synCcnvk (synCin (synCimagek (synCimak (synCdif (synCins3k (synCcompl
                            (synCimak (synCin (synCins3k (synCssetk))
                                (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                        (synCimak (synCsymdif (synCins2k (synCins2k (synCssetk)))
                            (synCun (synCins2k (synCins3k (synCssetk)))
                              (synCins3k (synCsik (synCsik (synCssetk))))))
                          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                      (synCpw1 (synCpw1 (.cv n))))) (synCimagek (synCimak (synCdif
                        (synCins3k (synCcompl (synCimak (synCin (synCins3k (synCssetk))
                                (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                        (synCimak (synCsymdif (synCins2k (synCins2k (synCssetk)))
                            (synCun (synCins2k (synCins3k (synCssetk)))
                              (synCins3k (synCsik (synCsik (synCssetk))))))
                          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                      (synCpw1 (synCpw1 (.cv p))))))) (synCvv))))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimagek,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_m_ne_n, fresh_m_ne_p, or_false,
      not_false_eq_true]
  have p0060 :=
    @gEqabi
      (.neg (synWa (synWne (synCplc (.cv m) (.cv n)) (synC0))
          (.classEq (synCplc (.cv m) (.cv n)) (synCplc (.cv m) (.cv p)))))
      m
      (synCcompl (synCin (synCcompl (synCimak (synCcnvk (synCimagek (synCimak (synCdif
                      (synCins3k (synCcompl (synCimak
                            (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                            (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                        (synCsymdif (synCins2k (synCins2k (synCssetk)))
                          (synCun (synCins2k (synCins3k (synCssetk)))
                            (synCins3k (synCsik (synCsik (synCssetk))))))
                        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                    (synCpw1 (synCpw1 (.cv n)))))) (synCsn (synC0)))) (synCimak (synCcnvk
              (synCin (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak
                            (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                            (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                        (synCsymdif (synCins2k (synCins2k (synCssetk)))
                          (synCun (synCins2k (synCins3k (synCssetk)))
                            (synCins3k (synCsik (synCsik (synCssetk))))))
                        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                    (synCpw1 (synCpw1 (.cv n))))) (synCimagek (synCimak (synCdif
                      (synCins3k (synCcompl (synCimak
                            (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                            (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                        (synCsymdif (synCins2k (synCins2k (synCssetk)))
                          (synCun (synCins2k (synCins3k (synCssetk)))
                            (synCins3k (synCsik (synCsik (synCssetk))))))
                        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                    (synCpw1 (synCpw1 (.cv p))))))) (synCvv))))
      freeVariableCertificate6 p0059
  have p0061 := @gAddcexlem
  have p0062 := @gPw1ex (.cv n) p0052
  have p0063 := @gPw1ex (synCpw1 (.cv n)) p0062
  have p0064 :=
    @gImakex
      (synCdif (synCins3k (synCcompl
            (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
              (synCpw1 (synCpw1 (synC1c)))))) (synCimak
          (synCsymdif (synCins2k (synCins2k (synCssetk)))
            (synCun (synCins2k (synCins3k (synCssetk)))
              (synCins3k (synCsik (synCsik (synCssetk))))))
          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
      (synCpw1 (synCpw1 (.cv n))) p0061 p0063
  have p0065 :=
    @gImagekex
      (synCimak (synCdif (synCins3k (synCcompl
              (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                (synCpw1 (synCpw1 (synC1c)))))) (synCimak
            (synCsymdif (synCins2k (synCins2k (synCssetk)))
              (synCun (synCins2k (synCins3k (synCssetk)))
                (synCins3k (synCsik (synCsik (synCssetk))))))
            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
        (synCpw1 (synCpw1 (.cv n))))
      p0064
  have p0066 :=
    @gCnvkex
      (synCimagek (synCimak (synCdif (synCins3k (synCcompl
                (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                  (synCpw1 (synCpw1 (synC1c)))))) (synCimak
              (synCsymdif (synCins2k (synCins2k (synCssetk)))
                (synCun (synCins2k (synCins3k (synCssetk)))
                  (synCins3k (synCsik (synCsik (synCssetk))))))
              (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
          (synCpw1 (synCpw1 (.cv n)))))
      p0065
  have p0067 := @gSnex (synC0)
  have p0068 :=
    @gImakex
      (synCcnvk (synCimagek (synCimak (synCdif (synCins3k (synCcompl
                  (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                    (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                (synCsymdif (synCins2k (synCins2k (synCssetk)))
                  (synCun (synCins2k (synCins3k (synCssetk)))
                    (synCins3k (synCsik (synCsik (synCssetk))))))
                (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
            (synCpw1 (synCpw1 (.cv n))))))
      (synCsn (synC0)) p0066 p0067
  have p0069 :=
    @gComplex
      (synCimak (synCcnvk (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak
                      (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                      (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                  (synCsymdif (synCins2k (synCins2k (synCssetk)))
                    (synCun (synCins2k (synCins3k (synCssetk)))
                      (synCins3k (synCsik (synCsik (synCssetk))))))
                  (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
              (synCpw1 (synCpw1 (.cv n)))))) (synCsn (synC0)))
      p0068
  have p0071 := @gVex p
  have p0072 := @gPw1ex (.cv p) p0071
  have p0073 := @gPw1ex (synCpw1 (.cv p)) p0072
  have p0074 :=
    @gImakex
      (synCdif (synCins3k (synCcompl
            (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
              (synCpw1 (synCpw1 (synC1c)))))) (synCimak
          (synCsymdif (synCins2k (synCins2k (synCssetk)))
            (synCun (synCins2k (synCins3k (synCssetk)))
              (synCins3k (synCsik (synCsik (synCssetk))))))
          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
      (synCpw1 (synCpw1 (.cv p))) p0061 p0073
  have p0075 :=
    @gImagekex
      (synCimak (synCdif (synCins3k (synCcompl
              (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                (synCpw1 (synCpw1 (synC1c)))))) (synCimak
            (synCsymdif (synCins2k (synCins2k (synCssetk)))
              (synCun (synCins2k (synCins3k (synCssetk)))
                (synCins3k (synCsik (synCsik (synCssetk))))))
            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
        (synCpw1 (synCpw1 (.cv p))))
      p0074
  have p0076 :=
    @gInex
      (synCimagek (synCimak (synCdif (synCins3k (synCcompl
                (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                  (synCpw1 (synCpw1 (synC1c)))))) (synCimak
              (synCsymdif (synCins2k (synCins2k (synCssetk)))
                (synCun (synCins2k (synCins3k (synCssetk)))
                  (synCins3k (synCsik (synCsik (synCssetk))))))
              (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
          (synCpw1 (synCpw1 (.cv n)))))
      (synCimagek (synCimak (synCdif (synCins3k (synCcompl
                (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                  (synCpw1 (synCpw1 (synC1c)))))) (synCimak
              (synCsymdif (synCins2k (synCins2k (synCssetk)))
                (synCun (synCins2k (synCins3k (synCssetk)))
                  (synCins3k (synCsik (synCsik (synCssetk))))))
              (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
          (synCpw1 (synCpw1 (.cv p)))))
      p0065 p0075
  have p0077 :=
    @gCnvkex
      (synCin (synCimagek (synCimak (synCdif (synCins3k (synCcompl
                  (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                    (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                (synCsymdif (synCins2k (synCins2k (synCssetk)))
                  (synCun (synCins2k (synCins3k (synCssetk)))
                    (synCins3k (synCsik (synCsik (synCssetk))))))
                (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
            (synCpw1 (synCpw1 (.cv n))))) (synCimagek (synCimak (synCdif (synCins3k
                (synCcompl
                  (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                    (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                (synCsymdif (synCins2k (synCins2k (synCssetk)))
                  (synCun (synCins2k (synCins3k (synCssetk)))
                    (synCins3k (synCsik (synCsik (synCssetk))))))
                (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
            (synCpw1 (synCpw1 (.cv p))))))
      p0076
  have p0078 := @gVvex
  have p0079 :=
    @gImakex
      (synCcnvk (synCin (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak
                      (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                      (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                  (synCsymdif (synCins2k (synCins2k (synCssetk)))
                    (synCun (synCins2k (synCins3k (synCssetk)))
                      (synCins3k (synCsik (synCsik (synCssetk))))))
                  (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
              (synCpw1 (synCpw1 (.cv n))))) (synCimagek (synCimak (synCdif (synCins3k
                  (synCcompl (synCimak
                      (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                      (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                  (synCsymdif (synCins2k (synCins2k (synCssetk)))
                    (synCun (synCins2k (synCins3k (synCssetk)))
                      (synCins3k (synCsik (synCsik (synCssetk))))))
                  (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
              (synCpw1 (synCpw1 (.cv p)))))))
      (synCvv) p0077 p0078
  have p0080 :=
    @gInex
      (synCcompl (synCimak (synCcnvk (synCimagek (synCimak (synCdif (synCins3k
                    (synCcompl (synCimak
                        (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                        (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                    (synCsymdif (synCins2k (synCins2k (synCssetk)))
                      (synCun (synCins2k (synCins3k (synCssetk)))
                        (synCins3k (synCsik (synCsik (synCssetk))))))
                    (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                (synCpw1 (synCpw1 (.cv n)))))) (synCsn (synC0))))
      (synCimak (synCcnvk (synCin (synCimagek (synCimak (synCdif (synCins3k (synCcompl
                      (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                        (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                    (synCsymdif (synCins2k (synCins2k (synCssetk)))
                      (synCun (synCins2k (synCins3k (synCssetk)))
                        (synCins3k (synCsik (synCsik (synCssetk))))))
                    (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                (synCpw1 (synCpw1 (.cv n))))) (synCimagek (synCimak (synCdif (synCins3k
                    (synCcompl (synCimak
                        (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                        (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                    (synCsymdif (synCins2k (synCins2k (synCssetk)))
                      (synCun (synCins2k (synCins3k (synCssetk)))
                        (synCins3k (synCsik (synCsik (synCssetk))))))
                    (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                (synCpw1 (synCpw1 (.cv p))))))) (synCvv))
      p0069 p0079
  have p0081 :=
    @gComplex
      (synCin (synCcompl (synCimak (synCcnvk (synCimagek (synCimak (synCdif (synCins3k
                      (synCcompl (synCimak
                          (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                          (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                      (synCsymdif (synCins2k (synCins2k (synCssetk)))
                        (synCun (synCins2k (synCins3k (synCssetk)))
                          (synCins3k (synCsik (synCsik (synCssetk))))))
                      (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                  (synCpw1 (synCpw1 (.cv n)))))) (synCsn (synC0)))) (synCimak (synCcnvk
            (synCin (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak
                          (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                          (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                      (synCsymdif (synCins2k (synCins2k (synCssetk)))
                        (synCun (synCins2k (synCins3k (synCssetk)))
                          (synCins3k (synCsik (synCsik (synCssetk))))))
                      (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                  (synCpw1 (synCpw1 (.cv n))))) (synCimagek (synCimak (synCdif (synCins3k
                      (synCcompl (synCimak
                          (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                          (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                      (synCsymdif (synCins2k (synCins2k (synCssetk)))
                        (synCun (synCins2k (synCins3k (synCssetk)))
                          (synCins3k (synCsik (synCsik (synCssetk))))))
                      (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                  (synCpw1 (synCpw1 (.cv p))))))) (synCvv)))
      p0080
  have p0082 :=
    @gEqeltrri
      (synCcompl (synCin (synCcompl (synCimak (synCcnvk (synCimagek (synCimak (synCdif
                      (synCins3k (synCcompl (synCimak
                            (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                            (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                        (synCsymdif (synCins2k (synCins2k (synCssetk)))
                          (synCun (synCins2k (synCins3k (synCssetk)))
                            (synCins3k (synCsik (synCsik (synCssetk))))))
                        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                    (synCpw1 (synCpw1 (.cv n)))))) (synCsn (synC0)))) (synCimak (synCcnvk
              (synCin (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak
                            (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                            (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                        (synCsymdif (synCins2k (synCins2k (synCssetk)))
                          (synCun (synCins2k (synCins3k (synCssetk)))
                            (synCins3k (synCsik (synCsik (synCssetk))))))
                        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                    (synCpw1 (synCpw1 (.cv n))))) (synCimagek (synCimak (synCdif
                      (synCins3k (synCcompl (synCimak
                            (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                            (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                        (synCsymdif (synCins2k (synCins2k (synCssetk)))
                          (synCun (synCins2k (synCins3k (synCssetk)))
                            (synCins3k (synCsik (synCsik (synCssetk))))))
                        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                    (synCpw1 (synCpw1 (.cv p))))))) (synCvv))))
      (.cab m (.neg (synWa (synWne (synCplc (.cv m) (.cv n)) (synC0))
            (.classEq (synCplc (.cv m) (.cv n)) (synCplc (.cv m) (.cv p))))))
      (synCvv) p0060 p0081
  have freeVariableCertificate7 : m ∉ ((Wff.classEq N P)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union, dv_N_m,
      dv_P_m, or_false, not_false_eq_true]
  have p0083 := @gAbexv (.classEq N P) m freeVariableCertificate7
  have p0084 :=
    @gUnex
      (.cab m (.neg (synWa (synWne (synCplc (.cv m) (.cv n)) (synC0))
            (.classEq (synCplc (.cv m) (.cv n)) (synCplc (.cv m) (.cv p))))))
      (.cab m (.classEq N P)) p0082 p0083
  have p0085 :=
    @gEqeltri
      (.cab m (.imp (synWa (synWne (synCplc (.cv m) (.cv n)) (synC0))
            (.classEq (synCplc (.cv m) (.cv n)) (synCplc (.cv m) (.cv p)))) (.classEq N P)))
      (synCun (.cab m (.neg (synWa (synWne (synCplc (.cv m) (.cv n)) (synC0))
              (.classEq (synCplc (.cv m) (.cv n)) (synCplc (.cv m) (.cv p))))))
        (.cab m (.classEq N P)))
      (synCvv) p0016 p0084
  have freeVariableCertificate8 :
    p ∉
      ((Wff.classMem (.cab m (.imp (synWa (synWne (synCplc (.cv m) N) (synC0))
                (.classEq (synCplc (.cv m) N) (synCplc (.cv m) P))) (.classEq N P)))
          (synCvv))).fv :=
    by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CoreFVSimp.fv_class_cab, NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
      Finset.mem_erase, Finset.mem_singleton, Finset.notMem_empty, fresh_p_ne_m,
      fresh_p_not_N, fresh_p_not_P, or_false, and_false, not_false_eq_true]
  have freeVariableCertificate9 :
    n ∉
      ((Wff.classMem (.cab m (.imp (synWa (synWne (synCplc (.cv m) N) (synC0))
                (.classEq (synCplc (.cv m) N) (synCplc (.cv m) (.cv p)))) (.classEq N P)))
          (synCvv))).fv :=
    by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CoreFVSimp.fv_class_cab, NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
      Finset.mem_erase, Finset.mem_singleton, Finset.notMem_empty, fresh_n_ne_m,
      fresh_n_not_N, fresh_n_ne_p, fresh_n_not_P, or_false, and_false, not_false_eq_true]
  have p0086 :=
    @gVtocl2g
      (.classMem (.cab m (.imp (synWa (synWne (synCplc (.cv m) (.cv n)) (synC0))
              (.classEq (synCplc (.cv m) (.cv n)) (synCplc (.cv m) (.cv p)))) (.classEq N P)))
        (synCvv))
      (.classMem (.cab m (.imp (synWa (synWne (synCplc (.cv m) N) (synC0))
              (.classEq (synCplc (.cv m) N) (synCplc (.cv m) (.cv p)))) (.classEq N P)))
        (synCvv))
      (.classMem (.cab m (.imp (synWa (synWne (synCplc (.cv m) N) (synC0))
              (.classEq (synCplc (.cv m) N) (synCplc (.cv m) P))) (.classEq N P))) (synCvv))
      n p N P (synCnnc) (synCnnc)
      (by exact (show n ∉ (N).fv from (by exact fresh_n_not_N)))
      (by exact (show p ∉ (N).fv from (by exact fresh_p_not_N)))
      (by exact (show p ∉ (P).fv from (by exact fresh_p_not_P))) freeVariableCertificate8
      freeVariableCertificate9 p0006 p0012 p0085
  exact p0086


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk009StructuralPart039`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_preaddccan2`. -/
@[expose]
noncomputable def gPreaddccan2 (P : Class) (M : Class) (N : Class) :
    Nominal.NPrf
      (.imp (synWa (synW3a (.classMem M (synCnnc)) (.classMem N (synCnnc))
            (.classMem P (synCnnc))) (synWne (synCplc M N) (synC0)))
        (synWb (.classEq (synCplc M N) (synCplc M P)) (.classEq N P))) :=
  by
  let proofSupport : Finset Var := P.fv ∪ M.fv ∪ N.fv
  let m : Var := freshVar proofSupport 0
  let k : Var := freshVar proofSupport 1
  have fresh_m : m ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_m_not_P : m ∉ P.fv := by
    intro h
    exact fresh_m (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_m_not_M : m ∉ M.fv := by
    intro h
    exact fresh_m (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_m_not_N : m ∉ N.fv := by
    intro h
    exact fresh_m (Finset.mem_union_right _ (h))
  have fresh_k : k ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_k_not_P : k ∉ P.fv := by
    intro h
    exact fresh_k (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_k_not_N : k ∉ N.fv := by
    intro h
    exact fresh_k (Finset.mem_union_right _ (h))
  have fresh_m_ne_k : m ≠ k :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_k_ne_m : k ≠ m := Ne.symm fresh_m_ne_k
  have p0000 :=
    @gPreaddccan2lem1 P m N (by exact (show m ∉ (N).fv from (by exact fresh_m_not_N)))
      (by exact (show m ∉ (P).fv from (by exact fresh_m_not_P)))
  have p0001 := @gAddceq1 (.cv m) (synC0c) N
  have p0002 :=
    @gNeeq1d (.classEq (.cv m) (synC0c)) (synCplc (.cv m) N) (synCplc (synC0c) N)
      (synC0) p0001
  have p0003 := @gAddceq1 (.cv m) (synC0c) P
  have p0004 :=
    @gEqeq12d (.classEq (.cv m) (synC0c)) (synCplc (.cv m) N) (synCplc (synC0c) N)
      (synCplc (.cv m) P) (synCplc (synC0c) P) p0001 p0003
  have p0005 :=
    @gAnbi12d (.classEq (.cv m) (synC0c)) (synWne (synCplc (.cv m) N) (synC0))
      (synWne (synCplc (synC0c) N) (synC0))
      (.classEq (synCplc (.cv m) N) (synCplc (.cv m) P))
      (.classEq (synCplc (synC0c) N) (synCplc (synC0c) P)) p0002 p0004
  have p0006 :=
    @gImbi1d (.classEq (.cv m) (synC0c))
      (synWa (synWne (synCplc (.cv m) N) (synC0))
        (.classEq (synCplc (.cv m) N) (synCplc (.cv m) P)))
      (synWa (synWne (synCplc (synC0c) N) (synC0))
        (.classEq (synCplc (synC0c) N) (synCplc (synC0c) P)))
      (.classEq N P) p0005
  have p0007 := @gAddceq1 (.cv m) (.cv k) N
  have p0008_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq m k) (.classEq (synCplc (.cv m) N) (synCplc (.cv k) N))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synCplc synWrex synWex synWa
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0007
  have p0008 :=
    @gNeeq1d (.objEq m k) (synCplc (.cv m) N) (synCplc (.cv k) N) (synC0)
      p0008_e00_recanon
  have p0009 := @gAddceq1 (.cv m) (.cv k) P
  have p0010_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq m k) (.classEq (synCplc (.cv m) N) (synCplc (.cv k) N))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synCplc synWrex synWex synWa
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0007
  have p0010_e01_recanon :
    Nominal.NPrf
      (.imp (.objEq m k) (.classEq (synCplc (.cv m) P) (synCplc (.cv k) P))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synCplc synWrex synWex synWa
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0009
  have p0010 :=
    @gEqeq12d (.objEq m k) (synCplc (.cv m) N) (synCplc (.cv k) N) (synCplc (.cv m) P)
      (synCplc (.cv k) P) p0010_e00_recanon p0010_e01_recanon
  have p0011 :=
    @gAnbi12d (.objEq m k) (synWne (synCplc (.cv m) N) (synC0))
      (synWne (synCplc (.cv k) N) (synC0))
      (.classEq (synCplc (.cv m) N) (synCplc (.cv m) P))
      (.classEq (synCplc (.cv k) N) (synCplc (.cv k) P)) p0008 p0010
  have p0012 :=
    @gImbi1d (.objEq m k)
      (synWa (synWne (synCplc (.cv m) N) (synC0))
        (.classEq (synCplc (.cv m) N) (synCplc (.cv m) P)))
      (synWa (synWne (synCplc (.cv k) N) (synC0))
        (.classEq (synCplc (.cv k) N) (synCplc (.cv k) P)))
      (.classEq N P) p0011
  have p0013 := @gAddceq1 (.cv m) (synCplc (.cv k) (synC1c)) N
  have p0014 := @gAddc32 (.cv k) (synC1c) N
  have p0015 :=
    @gSyl6eq (.classEq (.cv m) (synCplc (.cv k) (synC1c))) (synCplc (.cv m) N)
      (synCplc (synCplc (.cv k) (synC1c)) N) (synCplc (synCplc (.cv k) N) (synC1c))
      p0013 p0014
  have p0016 :=
    @gNeeq1d (.classEq (.cv m) (synCplc (.cv k) (synC1c))) (synCplc (.cv m) N)
      (synCplc (synCplc (.cv k) N) (synC1c)) (synC0) p0015
  have p0017 := @gAddceq1 (.cv m) (synCplc (.cv k) (synC1c)) P
  have p0018 := @gAddc32 (.cv k) (synC1c) P
  have p0019 :=
    @gSyl6eq (.classEq (.cv m) (synCplc (.cv k) (synC1c))) (synCplc (.cv m) P)
      (synCplc (synCplc (.cv k) (synC1c)) P) (synCplc (synCplc (.cv k) P) (synC1c))
      p0017 p0018
  have p0020 :=
    @gEqeq12d (.classEq (.cv m) (synCplc (.cv k) (synC1c))) (synCplc (.cv m) N)
      (synCplc (synCplc (.cv k) N) (synC1c)) (synCplc (.cv m) P)
      (synCplc (synCplc (.cv k) P) (synC1c)) p0015 p0019
  have p0021 :=
    @gAnbi12d (.classEq (.cv m) (synCplc (.cv k) (synC1c)))
      (synWne (synCplc (.cv m) N) (synC0))
      (synWne (synCplc (synCplc (.cv k) N) (synC1c)) (synC0))
      (.classEq (synCplc (.cv m) N) (synCplc (.cv m) P))
      (.classEq (synCplc (synCplc (.cv k) N) (synC1c))
        (synCplc (synCplc (.cv k) P) (synC1c)))
      p0016 p0020
  have p0022 :=
    @gImbi1d (.classEq (.cv m) (synCplc (.cv k) (synC1c)))
      (synWa (synWne (synCplc (.cv m) N) (synC0))
        (.classEq (synCplc (.cv m) N) (synCplc (.cv m) P)))
      (synWa (synWne (synCplc (synCplc (.cv k) N) (synC1c)) (synC0))
        (.classEq (synCplc (synCplc (.cv k) N) (synC1c))
          (synCplc (synCplc (.cv k) P) (synC1c))))
      (.classEq N P) p0021
  have p0023 := @gAddceq1 (.cv m) M N
  have p0024 :=
    @gNeeq1d (.classEq (.cv m) M) (synCplc (.cv m) N) (synCplc M N) (synC0) p0023
  have p0025 := @gAddceq1 (.cv m) M P
  have p0026 :=
    @gEqeq12d (.classEq (.cv m) M) (synCplc (.cv m) N) (synCplc M N)
      (synCplc (.cv m) P) (synCplc M P) p0023 p0025
  have p0027 :=
    @gAnbi12d (.classEq (.cv m) M) (synWne (synCplc (.cv m) N) (synC0))
      (synWne (synCplc M N) (synC0))
      (.classEq (synCplc (.cv m) N) (synCplc (.cv m) P))
      (.classEq (synCplc M N) (synCplc M P)) p0024 p0026
  have p0028 :=
    @gImbi1d (.classEq (.cv m) M)
      (synWa (synWne (synCplc (.cv m) N) (synC0))
        (.classEq (synCplc (.cv m) N) (synCplc (.cv m) P)))
      (synWa (synWne (synCplc M N) (synC0)) (.classEq (synCplc M N) (synCplc M P)))
      (.classEq N P) p0027
  have p0029 := @gAddcid2 N
  have p0030 := @gAddcid2 P
  have p0031 := @gEqeq12i (synCplc (synC0c) N) N (synCplc (synC0c) P) P p0029 p0030
  have p0032 :=
    @gBiimpi (.classEq (synCplc (synC0c) N) (synCplc (synC0c) P)) (.classEq N P)
      p0031
  have p0033 :=
    @gAdantl (.classEq (synCplc (synC0c) N) (synCplc (synC0c) P)) (.classEq N P)
      (synWne (synCplc (synC0c) N) (synC0)) p0032
  have p0034 :=
    @gA1i
      (.imp (synWa (synWne (synCplc (synC0c) N) (synC0))
          (.classEq (synCplc (synC0c) N) (synCplc (synC0c) P))) (.classEq N P))
      (synWa (.classMem N (synCnnc)) (.classMem P (synCnnc))) p0033
  have p0035 := @gAddcnnul (synCplc (.cv k) N) (synC1c)
  have p0036 :=
    @gSimpld (synWne (synCplc (synCplc (.cv k) N) (synC1c)) (synC0))
      (synWne (synCplc (.cv k) N) (synC0)) (synWne (synC1c) (synC0)) p0035
  have p0037 :=
    @gAd2antrl (synWne (synCplc (synCplc (.cv k) N) (synC1c)) (synC0))
      (synWne (synCplc (.cv k) N) (synC0))
      (synWa (.classMem (.cv k) (synCnnc))
        (synWa (.classMem N (synCnnc)) (.classMem P (synCnnc))))
      (.classEq (synCplc (synCplc (.cv k) N) (synC1c))
        (synCplc (synCplc (.cv k) P) (synC1c)))
      p0036
  have p0038 :=
    @gSimpll (.classMem (.cv k) (synCnnc))
      (synWa (.classMem N (synCnnc)) (.classMem P (synCnnc)))
      (synWa (synWne (synCplc (synCplc (.cv k) N) (synC1c)) (synC0))
        (.classEq (synCplc (synCplc (.cv k) N) (synC1c))
          (synCplc (synCplc (.cv k) P) (synC1c))))
  have p0039 :=
    @gSimplrl (.classMem (.cv k) (synCnnc)) (.classMem N (synCnnc))
      (.classMem P (synCnnc))
      (synWa (synWne (synCplc (synCplc (.cv k) N) (synC1c)) (synC0))
        (.classEq (synCplc (synCplc (.cv k) N) (synC1c))
          (synCplc (synCplc (.cv k) P) (synC1c))))
  have p0040 := @gNncaddccl (.cv k) N
  have p0041 :=
    @gSyl2anc
      (synWa (synWa (.classMem (.cv k) (synCnnc))
          (synWa (.classMem N (synCnnc)) (.classMem P (synCnnc))))
        (synWa (synWne (synCplc (synCplc (.cv k) N) (synC1c)) (synC0))
          (.classEq (synCplc (synCplc (.cv k) N) (synC1c))
            (synCplc (synCplc (.cv k) P) (synC1c)))))
      (.classMem (.cv k) (synCnnc)) (.classMem N (synCnnc))
      (.classMem (synCplc (.cv k) N) (synCnnc)) p0038 p0039 p0040
  have p0042 :=
    @gSimplrr (.classMem (.cv k) (synCnnc)) (.classMem N (synCnnc))
      (.classMem P (synCnnc))
      (synWa (synWne (synCplc (synCplc (.cv k) N) (synC1c)) (synC0))
        (.classEq (synCplc (synCplc (.cv k) N) (synC1c))
          (synCplc (synCplc (.cv k) P) (synC1c))))
  have p0043 := @gNncaddccl (.cv k) P
  have p0044 :=
    @gSyl2anc
      (synWa (synWa (.classMem (.cv k) (synCnnc))
          (synWa (.classMem N (synCnnc)) (.classMem P (synCnnc))))
        (synWa (synWne (synCplc (synCplc (.cv k) N) (synC1c)) (synC0))
          (.classEq (synCplc (synCplc (.cv k) N) (synC1c))
            (synCplc (synCplc (.cv k) P) (synC1c)))))
      (.classMem (.cv k) (synCnnc)) (.classMem P (synCnnc))
      (.classMem (synCplc (.cv k) P) (synCnnc)) p0038 p0042 p0043
  have p0045 :=
    @gSimprr
      (synWa (.classMem (.cv k) (synCnnc))
        (synWa (.classMem N (synCnnc)) (.classMem P (synCnnc))))
      (synWne (synCplc (synCplc (.cv k) N) (synC1c)) (synC0))
      (.classEq (synCplc (synCplc (.cv k) N) (synC1c))
        (synCplc (synCplc (.cv k) P) (synC1c)))
  have p0046 :=
    @gSimprl
      (synWa (.classMem (.cv k) (synCnnc))
        (synWa (.classMem N (synCnnc)) (.classMem P (synCnnc))))
      (synWne (synCplc (synCplc (.cv k) N) (synC1c)) (synC0))
      (.classEq (synCplc (synCplc (.cv k) N) (synC1c))
        (synCplc (synCplc (.cv k) P) (synC1c)))
  have p0047 := @gPrepeano4 (synCplc (.cv k) N) (synCplc (.cv k) P)
  have p0048 :=
    @gSyl22anc
      (synWa (synWa (.classMem (.cv k) (synCnnc))
          (synWa (.classMem N (synCnnc)) (.classMem P (synCnnc))))
        (synWa (synWne (synCplc (synCplc (.cv k) N) (synC1c)) (synC0))
          (.classEq (synCplc (synCplc (.cv k) N) (synC1c))
            (synCplc (synCplc (.cv k) P) (synC1c)))))
      (.classMem (synCplc (.cv k) N) (synCnnc))
      (.classMem (synCplc (.cv k) P) (synCnnc))
      (.classEq (synCplc (synCplc (.cv k) N) (synC1c))
        (synCplc (synCplc (.cv k) P) (synC1c)))
      (synWne (synCplc (synCplc (.cv k) N) (synC1c)) (synC0))
      (.classEq (synCplc (.cv k) N) (synCplc (.cv k) P)) p0041 p0044 p0045 p0046 p0047
  have p0049 :=
    @gJca
      (synWa (synWa (.classMem (.cv k) (synCnnc))
          (synWa (.classMem N (synCnnc)) (.classMem P (synCnnc))))
        (synWa (synWne (synCplc (synCplc (.cv k) N) (synC1c)) (synC0))
          (.classEq (synCplc (synCplc (.cv k) N) (synC1c))
            (synCplc (synCplc (.cv k) P) (synC1c)))))
      (synWne (synCplc (.cv k) N) (synC0))
      (.classEq (synCplc (.cv k) N) (synCplc (.cv k) P)) p0037 p0048
  have p0050 :=
    @gEx
      (synWa (.classMem (.cv k) (synCnnc))
        (synWa (.classMem N (synCnnc)) (.classMem P (synCnnc))))
      (synWa (synWne (synCplc (synCplc (.cv k) N) (synC1c)) (synC0))
        (.classEq (synCplc (synCplc (.cv k) N) (synC1c))
          (synCplc (synCplc (.cv k) P) (synC1c))))
      (synWa (synWne (synCplc (.cv k) N) (synC0))
        (.classEq (synCplc (.cv k) N) (synCplc (.cv k) P)))
      p0049
  have p0051 :=
    @gImim1d
      (synWa (.classMem (.cv k) (synCnnc))
        (synWa (.classMem N (synCnnc)) (.classMem P (synCnnc))))
      (synWa (synWne (synCplc (synCplc (.cv k) N) (synC1c)) (synC0))
        (.classEq (synCplc (synCplc (.cv k) N) (synC1c))
          (synCplc (synCplc (.cv k) P) (synC1c))))
      (synWa (synWne (synCplc (.cv k) N) (synC0))
        (.classEq (synCplc (.cv k) N) (synCplc (.cv k) P)))
      (.classEq N P) p0050
  have freeVariableCertificate0 :
    m ∉
      ((Wff.imp (synWa (synWne (synCplc (.cv k) N) (synC0))
            (.classEq (synCplc (.cv k) N) (synCplc (.cv k) P))) (.classEq N P))).fv :=
    by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union, Finset.mem_singleton,
      Finset.notMem_empty, fresh_m_ne_k, fresh_m_not_N, fresh_m_not_P, or_false,
      not_false_eq_true]
  have freeVariableCertificate1 :
    k ∉ ((synWa (.classMem N (synCnnc)) (.classMem P (synCnnc)))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union,
      Finset.notMem_empty, fresh_k_not_N, fresh_k_not_P, or_false, not_false_eq_true]
  have freeVariableCertificate2 :
    k ∉
      ((Wff.imp (synWa (synWne (synCplc (.cv m) N) (synC0))
            (.classEq (synCplc (.cv m) N) (synCplc (.cv m) P))) (.classEq N P))).fv :=
    by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union, Finset.mem_singleton,
      Finset.notMem_empty, fresh_k_ne_m, fresh_k_not_N, fresh_k_not_P, or_false,
      not_false_eq_true]
  have freeVariableCertificate3 :
    m ∉
      ((Wff.imp (synWa (synWne (synCplc (synC0c) N) (synC0))
            (.classEq (synCplc (synC0c) N) (synCplc (synC0c) P))) (.classEq N P))).fv :=
    by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union, Finset.notMem_empty,
      fresh_m_not_N, fresh_m_not_P, or_false, not_false_eq_true]
  have freeVariableCertificate4 :
    m ∉
      ((Wff.imp (synWa (synWne (synCplc M N) (synC0))
            (.classEq (synCplc M N) (synCplc M P))) (.classEq N P))).fv :=
    by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union, Finset.notMem_empty,
      fresh_m_not_M, fresh_m_not_N, fresh_m_not_P, or_false, not_false_eq_true]
  have freeVariableCertificate5 :
    m ∉
      ((Wff.imp (synWa (synWne (synCplc (synCplc (.cv k) N) (synC1c)) (synC0))
            (.classEq (synCplc (synCplc (.cv k) N) (synC1c))
              (synCplc (synCplc (.cv k) P) (synC1c)))) (.classEq N P))).fv :=
    by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union, Finset.mem_singleton,
      Finset.notMem_empty, fresh_m_ne_k, fresh_m_not_N, fresh_m_not_P, or_false,
      not_false_eq_true]
  have p0052 :=
    @gFindsd
      (.imp (synWa (synWne (synCplc (.cv m) N) (synC0))
          (.classEq (synCplc (.cv m) N) (synCplc (.cv m) P))) (.classEq N P))
      (.imp (synWa (synWne (synCplc (synC0c) N) (synC0))
          (.classEq (synCplc (synC0c) N) (synCplc (synC0c) P))) (.classEq N P))
      (.imp (synWa (synWne (synCplc (.cv k) N) (synC0))
          (.classEq (synCplc (.cv k) N) (synCplc (.cv k) P))) (.classEq N P))
      (.imp (synWa (synWne (synCplc (synCplc (.cv k) N) (synC1c)) (synC0))
          (.classEq (synCplc (synCplc (.cv k) N) (synC1c))
            (synCplc (synCplc (.cv k) P) (synC1c)))) (.classEq N P))
      (.imp (synWa (synWne (synCplc M N) (synC0)) (.classEq (synCplc M N) (synCplc M P)))
        (.classEq N P))
      (synWa (.classMem N (synCnnc)) (.classMem P (synCnnc))) m k M (synCvv)
      (by exact (show m ∉ (M).fv from (by exact fresh_m_not_M))) freeVariableCertificate0
      freeVariableCertificate1 freeVariableCertificate2 freeVariableCertificate3
      freeVariableCertificate4 freeVariableCertificate5
      (show m ≠ k from (by exact fresh_m_ne_k)) p0000 p0006 p0012 p0022 p0028 p0034 p0051
  have p0053 :=
    @gN3impb (.classMem M (synCnnc)) (.classMem N (synCnnc)) (.classMem P (synCnnc))
      (.imp (synWa (synWne (synCplc M N) (synC0)) (.classEq (synCplc M N) (synCplc M P)))
        (.classEq N P))
      p0052
  have p0054 :=
    @gExpdimp
      (synW3a (.classMem M (synCnnc)) (.classMem N (synCnnc)) (.classMem P (synCnnc)))
      (synWne (synCplc M N) (synC0)) (.classEq (synCplc M N) (synCplc M P))
      (.classEq N P) p0053
  have p0055 := @gAddceq2 N P M
  have p0056 :=
    @gImpbid1
      (synWa (synW3a (.classMem M (synCnnc)) (.classMem N (synCnnc))
          (.classMem P (synCnnc))) (synWne (synCplc M N) (synC0)))
      (.classEq (synCplc M N) (synCplc M P)) (.classEq N P) p0054 p0055
  exact p0056

/-- Checked nominal proof certificate identified upstream as `g_nulge`. -/
@[expose]
noncomputable def gNulge (A : Class) (V : Class) :
    Nominal.NPrf
      (.imp (synWa (.classMem (synC0) (synCnnc)) (.classMem A V))
        (.classMem (synCopk A (synC0)) (synClefin))) :=
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
  have p0000 := @gAddcnul1 A
  have p0001 := @gEqcomi (synCplc A (synC0)) (synC0) p0000
  have p0002 := @gAddceq2 (.cv x) (synC0) A
  have p0003 :=
    @gEqeq2d (.classEq (.cv x) (synC0)) (synCplc A (.cv x)) (synCplc A (synC0))
      (synC0) p0002
  have freeVariableCertificate0 : x ∉ ((Wff.classEq (synC0) (synCplc A (synC0)))).fv :=
    by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, Finset.mem_union,
      Finset.notMem_empty, fresh_x_not_A, or_false, not_false_eq_true]
  have p0004 :=
    @gRspcev (.classEq (synC0) (synCplc A (.cv x)))
      (.classEq (synC0) (synCplc A (synC0))) x (synC0) (synCnnc)
      (by
        exact
          (show x ∉ ((synC0)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0];
              exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
      (by
        exact
          (show x ∉ ((synCnnc)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc];
              exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
      freeVariableCertificate0 p0003
  have p0005 :=
    @gMpan2 (.classMem (synC0) (synCnnc)) (.classEq (synC0) (synCplc A (synC0)))
      (synWrex x (synCnnc) (.classEq (synC0) (synCplc A (.cv x)))) p0001 p0004
  have p0006 :=
    @gAdantr (.classMem (synC0) (synCnnc))
      (synWrex x (synCnnc) (.classEq (synC0) (synCplc A (.cv x)))) (.classMem A V)
      p0005
  have p0007 :=
    @gOpklefing x A (synC0) V (synCnnc)
      (by exact (show x ∉ (A).fv from (by exact fresh_x_not_A)))
      (by
        exact
          (show x ∉ ((synC0)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0];
              exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
  have p0008 :=
    @gAncoms (.classMem A V) (.classMem (synC0) (synCnnc))
      (synWb (.classMem (synCopk A (synC0)) (synClefin))
        (synWrex x (synCnnc) (.classEq (synC0) (synCplc A (.cv x)))))
      p0007
  have p0009 :=
    @gMpbird (synWa (.classMem (synC0) (synCnnc)) (.classMem A V))
      (.classMem (synCopk A (synC0)) (synClefin))
      (synWrex x (synCnnc) (.classEq (synC0) (synCplc A (.cv x)))) p0006 p0008
  exact p0009

/-- Checked nominal proof certificate identified upstream as `g_ltfinirr`. -/
@[expose]
noncomputable def gLtfinirr (A : Class) :
    Nominal.NPrf
      (.imp (.classMem A (synCnnc)) (.neg (.classMem (synCopk A A) (synCltfin)))) :=
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
  have p0000 := @gN0cnsuc (.cv x)
  have p0001 := @gNecomi (synCplc (.cv x) (synC1c)) (synC0c) p0000
  have p0002 := (Nominal.biimpRefl (synWne (synC0c) (synCplc (.cv x) (synC1c))))
  have p0003 :=
    @gMpbi (synWne (synC0c) (synCplc (.cv x) (synC1c)))
      (.neg (.classEq (synC0c) (synCplc (.cv x) (synC1c)))) p0001 p0002
  have p0004 := @gAddcid1 A
  have p0005 := @gEqcomi (synCplc A (synC0c)) A p0004
  have p0006 := @gAddcass A (.cv x) (synC1c)
  have p0007 :=
    @gEqeq12i A (synCplc A (synC0c)) (synCplc (synCplc A (.cv x)) (synC1c))
      (synCplc A (synCplc (.cv x) (synC1c))) p0005 p0006
  have p0008 :=
    @gSimpll (.classMem A (synCnnc)) (synWne A (synC0)) (.classMem (.cv x) (synCnnc))
  have p0009 := @gPeano1
  have p0010 :=
    @gA1i (.classMem (synC0c) (synCnnc))
      (synWa (synWa (.classMem A (synCnnc)) (synWne A (synC0)))
        (.classMem (.cv x) (synCnnc)))
      p0009
  have p0011 := @gPeano2 (.cv x)
  have p0012 :=
    @gAdantl (.classMem (.cv x) (synCnnc))
      (.classMem (synCplc (.cv x) (synC1c)) (synCnnc))
      (synWa (.classMem A (synCnnc)) (synWne A (synC0))) p0011
  have p0013 := @gNeeq1i (synCplc A (synC0c)) A (synC0) p0004
  have p0014 :=
    @gBiimpri (synWne (synCplc A (synC0c)) (synC0)) (synWne A (synC0)) p0013
  have p0015 :=
    @gAd2antlr (synWne A (synC0)) (synWne (synCplc A (synC0c)) (synC0))
      (.classMem A (synCnnc)) (.classMem (.cv x) (synCnnc)) p0014
  have p0016 := @gPreaddccan2 (synCplc (.cv x) (synC1c)) A (synC0c)
  have p0017 :=
    @gSyl31anc
      (synWa (synWa (.classMem A (synCnnc)) (synWne A (synC0)))
        (.classMem (.cv x) (synCnnc)))
      (.classMem A (synCnnc)) (.classMem (synC0c) (synCnnc))
      (.classMem (synCplc (.cv x) (synC1c)) (synCnnc))
      (synWne (synCplc A (synC0c)) (synC0))
      (synWb (.classEq (synCplc A (synC0c)) (synCplc A (synCplc (.cv x) (synC1c))))
        (.classEq (synC0c) (synCplc (.cv x) (synC1c))))
      p0008 p0010 p0012 p0015 p0016
  have p0018 :=
    @gSyl5bb (.classEq A (synCplc (synCplc A (.cv x)) (synC1c)))
      (.classEq (synCplc A (synC0c)) (synCplc A (synCplc (.cv x) (synC1c))))
      (synWa (synWa (.classMem A (synCnnc)) (synWne A (synC0)))
        (.classMem (.cv x) (synCnnc)))
      (.classEq (synC0c) (synCplc (.cv x) (synC1c))) p0007 p0017
  have p0019 :=
    @gMtbiri
      (synWa (synWa (.classMem A (synCnnc)) (synWne A (synC0)))
        (.classMem (.cv x) (synCnnc)))
      (.classEq A (synCplc (synCplc A (.cv x)) (synC1c)))
      (.classEq (synC0c) (synCplc (.cv x) (synC1c))) p0003 p0018
  have freeVariableCertificate0 :
    x ∉ ((synWa (.classMem A (synCnnc)) (synWne A (synC0)))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union,
      Finset.notMem_empty, fresh_x_not_A, or_false, not_false_eq_true]
  have p0020 :=
    @gNrexdv (synWa (.classMem A (synCnnc)) (synWne A (synC0)))
      (.classEq A (synCplc (synCplc A (.cv x)) (synC1c))) x (synCnnc)
      freeVariableCertificate0 p0019
  have p0021 :=
    @gEx (.classMem A (synCnnc)) (synWne A (synC0))
      (.neg (synWrex x (synCnnc) (.classEq A (synCplc (synCplc A (.cv x)) (synC1c)))))
      p0020
  have p0022 :=
    @gImnan (synWne A (synC0))
      (synWrex x (synCnnc) (.classEq A (synCplc (synCplc A (.cv x)) (synC1c))))
  have p0023 :=
    @gSylib (.classMem A (synCnnc))
      (.imp (synWne A (synC0)) (.neg
          (synWrex x (synCnnc) (.classEq A (synCplc (synCplc A (.cv x)) (synC1c))))))
      (.neg (synWa (synWne A (synC0))
          (synWrex x (synCnnc) (.classEq A (synCplc (synCplc A (.cv x)) (synC1c))))))
      p0021 p0022
  have p0024 :=
    @gOpkltfing x A A (synCnnc) (synCnnc)
      (by exact (show x ∉ (A).fv from (by exact fresh_x_not_A)))
      (by exact (show x ∉ (A).fv from (by exact fresh_x_not_A)))
  have p0025 :=
    @gAnidms (.classMem A (synCnnc))
      (synWb (.classMem (synCopk A A) (synCltfin)) (synWa (synWne A (synC0))
          (synWrex x (synCnnc) (.classEq A (synCplc (synCplc A (.cv x)) (synC1c))))))
      p0024
  have p0026 :=
    @gMtbird (.classMem A (synCnnc)) (.classMem (synCopk A A) (synCltfin))
      (synWa (synWne A (synC0))
        (synWrex x (synCnnc) (.classEq A (synCplc (synCplc A (.cv x)) (synC1c)))))
      p0023 p0025
  exact p0026


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk009StructuralPart040`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_leltfintr`. -/
@[expose]
noncomputable def gLeltfintr (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf
      (.imp (synW3a (.classMem A (synCnnc)) (.classMem B (synCnnc)) (.classMem C (synCnnc)))
        (.imp (synWa (.classMem (synCopk A B) (synClefin))
            (.classMem (synCopk B C) (synCltfin)))
          (.classMem (synCopk A C) (synCltfin)))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let z : Var := freshVar proofSupport 2
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_C : x ∉ C.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_y_not_C : y ∉ C.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_z_not_C : z ∉ C.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
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
  have fresh_y_ne_z : y ≠ z :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_z_ne_y : z ≠ y := Ne.symm fresh_y_ne_z
  have p0000 :=
    @gOpklefing x A B (synCnnc) (synCnnc)
      (by exact (show x ∉ (A).fv from (by exact fresh_x_not_A)))
      (by exact (show x ∉ (B).fv from (by exact fresh_x_not_B)))
  have p0001 :=
    @gN3adant3 (.classMem A (synCnnc)) (.classMem B (synCnnc))
      (synWb (.classMem (synCopk A B) (synClefin))
        (synWrex x (synCnnc) (.classEq B (synCplc A (.cv x)))))
      (.classMem C (synCnnc)) p0000
  have p0002 := @gAddcnnul A (.cv x)
  have p0003 :=
    @gSimpld (synWne (synCplc A (.cv x)) (synC0)) (synWne A (synC0))
      (synWne (.cv x) (synC0)) p0002
  have p0004 :=
    @gA1i (.imp (synWne (synCplc A (.cv x)) (synC0)) (synWne A (synC0)))
      (synWa (synWa (.classMem A (synCnnc)) (.classMem C (synCnnc)))
        (.classMem (.cv x) (synCnnc)))
      p0003
  have p0005 := @gNncaddccl (.cv x) (.cv y)
  have p0006 :=
    @gN3adant1 (.classMem (.cv x) (synCnnc)) (.classMem (.cv y) (synCnnc))
      (.classMem (synCplc (.cv x) (.cv y)) (synCnnc)) (.classMem A (synCnnc)) p0005
  have p0007 := @gAddcass A (.cv x) (.cv y)
  have p0008 :=
    @gAddceq1 (synCplc (synCplc A (.cv x)) (.cv y))
      (synCplc A (synCplc (.cv x) (.cv y))) (synC1c)
  have p0009 := Nominal.mp p0007 p0008
  have p0010 :=
    @gA1i
      (.classEq (synCplc (synCplc (synCplc A (.cv x)) (.cv y)) (synC1c))
        (synCplc (synCplc A (synCplc (.cv x) (.cv y))) (synC1c)))
      (synW3a (.classMem A (synCnnc)) (.classMem (.cv x) (synCnnc))
        (.classMem (.cv y) (synCnnc)))
      p0009
  have p0011 := @gAddceq2 (.cv z) (synCplc (.cv x) (.cv y)) A
  have p0012 :=
    @gAddceq1 (synCplc A (.cv z)) (synCplc A (synCplc (.cv x) (.cv y))) (synC1c)
  have p0013 :=
    @gSyl (.classEq (.cv z) (synCplc (.cv x) (.cv y)))
      (.classEq (synCplc A (.cv z)) (synCplc A (synCplc (.cv x) (.cv y))))
      (.classEq (synCplc (synCplc A (.cv z)) (synC1c))
        (synCplc (synCplc A (synCplc (.cv x) (.cv y))) (synC1c)))
      p0011 p0012
  have p0014 :=
    @gEqeq2d (.classEq (.cv z) (synCplc (.cv x) (.cv y)))
      (synCplc (synCplc A (.cv z)) (synC1c))
      (synCplc (synCplc A (synCplc (.cv x) (.cv y))) (synC1c))
      (synCplc (synCplc (synCplc A (.cv x)) (.cv y)) (synC1c)) p0013
  have freeVariableCertificate0 : z ∉ ((synCplc (.cv x) (.cv y))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      fresh_z_ne_x, fresh_z_ne_y, or_false, not_false_eq_true]
  have freeVariableCertificate1 :
    z ∉
      ((Wff.classEq (synCplc (synCplc (synCplc A (.cv x)) (.cv y)) (synC1c))
          (synCplc (synCplc A (synCplc (.cv x) (.cv y))) (synC1c)))).fv :=
    by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_z_not_A, fresh_z_ne_x,
      fresh_z_ne_y, or_false, not_false_eq_true]
  have p0015 :=
    @gRspcev
      (.classEq (synCplc (synCplc (synCplc A (.cv x)) (.cv y)) (synC1c))
        (synCplc (synCplc A (.cv z)) (synC1c)))
      (.classEq (synCplc (synCplc (synCplc A (.cv x)) (.cv y)) (synC1c))
        (synCplc (synCplc A (synCplc (.cv x) (.cv y))) (synC1c)))
      z (synCplc (.cv x) (.cv y)) (synCnnc) freeVariableCertificate0
      (by
        exact
          (show z ∉ ((synCnnc)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc];
              exact (show z ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
      freeVariableCertificate1 p0014
  have p0016 :=
    @gSyl2anc
      (synW3a (.classMem A (synCnnc)) (.classMem (.cv x) (synCnnc))
        (.classMem (.cv y) (synCnnc)))
      (.classMem (synCplc (.cv x) (.cv y)) (synCnnc))
      (.classEq (synCplc (synCplc (synCplc A (.cv x)) (.cv y)) (synC1c))
        (synCplc (synCplc A (synCplc (.cv x) (.cv y))) (synC1c)))
      (synWrex z (synCnnc)
        (.classEq (synCplc (synCplc (synCplc A (.cv x)) (.cv y)) (synC1c))
          (synCplc (synCplc A (.cv z)) (synC1c))))
      p0006 p0010 p0015
  have p0017 :=
    @gEqeq1 C (synCplc (synCplc (synCplc A (.cv x)) (.cv y)) (synC1c))
      (synCplc (synCplc A (.cv z)) (synC1c))
  have freeVariableCertificate2 :
    z ∉
      ((Wff.classEq C (synCplc (synCplc (synCplc A (.cv x)) (.cv y)) (synC1c)))).fv :=
    by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_z_not_C, fresh_z_not_A,
      fresh_z_ne_x, fresh_z_ne_y, or_false, not_false_eq_true]
  have p0018 :=
    @gRexbidv (.classEq C (synCplc (synCplc (synCplc A (.cv x)) (.cv y)) (synC1c)))
      (.classEq C (synCplc (synCplc A (.cv z)) (synC1c)))
      (.classEq (synCplc (synCplc (synCplc A (.cv x)) (.cv y)) (synC1c))
        (synCplc (synCplc A (.cv z)) (synC1c)))
      z (synCnnc) freeVariableCertificate2 p0017
  have p0019 :=
    @gSyl5ibrcom
      (synW3a (.classMem A (synCnnc)) (.classMem (.cv x) (synCnnc))
        (.classMem (.cv y) (synCnnc)))
      (synWrex z (synCnnc) (.classEq C (synCplc (synCplc A (.cv z)) (synC1c))))
      (.classEq C (synCplc (synCplc (synCplc A (.cv x)) (.cv y)) (synC1c)))
      (synWrex z (synCnnc)
        (.classEq (synCplc (synCplc (synCplc A (.cv x)) (.cv y)) (synC1c))
          (synCplc (synCplc A (.cv z)) (synC1c))))
      p0016 p0018
  have p0020 :=
    @gN3expa (.classMem A (synCnnc)) (.classMem (.cv x) (synCnnc))
      (.classMem (.cv y) (synCnnc))
      (.imp (.classEq C (synCplc (synCplc (synCplc A (.cv x)) (.cv y)) (synC1c)))
        (synWrex z (synCnnc) (.classEq C (synCplc (synCplc A (.cv z)) (synC1c)))))
      p0019
  have p0021 :=
    @gAdantllr (.classMem A (synCnnc)) (.classMem (.cv x) (synCnnc))
      (.classMem (.cv y) (synCnnc))
      (.imp (.classEq C (synCplc (synCplc (synCplc A (.cv x)) (.cv y)) (synC1c)))
        (synWrex z (synCnnc) (.classEq C (synCplc (synCplc A (.cv z)) (synC1c)))))
      (.classMem C (synCnnc)) p0020
  have freeVariableCertificate3 :
    y ∉
      ((synWrex z (synCnnc) (.classEq C (synCplc (synCplc A (.cv z)) (synC1c))))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
      Finset.mem_erase, Finset.mem_singleton, Finset.notMem_empty, fresh_y_not_C,
      fresh_y_not_A, fresh_y_ne_z, or_false, and_false, not_false_eq_true]
  have freeVariableCertificate4 :
    y ∉
      ((synWa (synWa (.classMem A (synCnnc)) (.classMem C (synCnnc)))
          (.classMem (.cv x) (synCnnc)))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      Finset.notMem_empty, fresh_y_not_A, fresh_y_not_C, fresh_y_ne_x, or_false,
      not_false_eq_true]
  have p0022 :=
    @gRexlimdva
      (synWa (synWa (.classMem A (synCnnc)) (.classMem C (synCnnc)))
        (.classMem (.cv x) (synCnnc)))
      (.classEq C (synCplc (synCplc (synCplc A (.cv x)) (.cv y)) (synC1c)))
      (synWrex z (synCnnc) (.classEq C (synCplc (synCplc A (.cv z)) (synC1c)))) y
      (synCnnc) freeVariableCertificate3 freeVariableCertificate4 p0021
  have p0023 :=
    @gAnim12d
      (synWa (synWa (.classMem A (synCnnc)) (.classMem C (synCnnc)))
        (.classMem (.cv x) (synCnnc)))
      (synWne (synCplc A (.cv x)) (synC0)) (synWne A (synC0))
      (synWrex y (synCnnc)
        (.classEq C (synCplc (synCplc (synCplc A (.cv x)) (.cv y)) (synC1c))))
      (synWrex z (synCnnc) (.classEq C (synCplc (synCplc A (.cv z)) (synC1c)))) p0004
      p0022
  have p0024 := @gAddcexg A (.cv x) (synCnnc) (synCnnc)
  have p0025 :=
    @gAdantlr (.classMem A (synCnnc)) (.classMem (.cv x) (synCnnc))
      (.classMem (synCplc A (.cv x)) (synCvv)) (.classMem C (synCnnc)) p0024
  have p0026 :=
    @gSimplr (.classMem A (synCnnc)) (.classMem C (synCnnc))
      (.classMem (.cv x) (synCnnc))
  have freeVariableCertificate5 : y ∉ ((synCplc A (.cv x))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      fresh_y_not_A, fresh_y_ne_x, or_false, not_false_eq_true]
  have p0027 :=
    @gOpkltfing y (synCplc A (.cv x)) C (synCvv) (synCnnc) freeVariableCertificate5
      (by exact (show y ∉ (C).fv from (by exact fresh_y_not_C)))
  have p0028 :=
    @gSyl2anc
      (synWa (synWa (.classMem A (synCnnc)) (.classMem C (synCnnc)))
        (.classMem (.cv x) (synCnnc)))
      (.classMem (synCplc A (.cv x)) (synCvv)) (.classMem C (synCnnc))
      (synWb (.classMem (synCopk (synCplc A (.cv x)) C) (synCltfin))
        (synWa (synWne (synCplc A (.cv x)) (synC0)) (synWrex y (synCnnc)
            (.classEq C (synCplc (synCplc (synCplc A (.cv x)) (.cv y)) (synC1c))))))
      p0025 p0026 p0027
  have p0029 :=
    @gOpkltfing z A C (synCnnc) (synCnnc)
      (by exact (show z ∉ (A).fv from (by exact fresh_z_not_A)))
      (by exact (show z ∉ (C).fv from (by exact fresh_z_not_C)))
  have p0030 :=
    @gAdantr (synWa (.classMem A (synCnnc)) (.classMem C (synCnnc)))
      (synWb (.classMem (synCopk A C) (synCltfin)) (synWa (synWne A (synC0))
          (synWrex z (synCnnc) (.classEq C (synCplc (synCplc A (.cv z)) (synC1c))))))
      (.classMem (.cv x) (synCnnc)) p0029
  have p0031 :=
    @gN3imtr4d
      (synWa (synWa (.classMem A (synCnnc)) (.classMem C (synCnnc)))
        (.classMem (.cv x) (synCnnc)))
      (synWa (synWne (synCplc A (.cv x)) (synC0)) (synWrex y (synCnnc)
          (.classEq C (synCplc (synCplc (synCplc A (.cv x)) (.cv y)) (synC1c)))))
      (synWa (synWne A (synC0))
        (synWrex z (synCnnc) (.classEq C (synCplc (synCplc A (.cv z)) (synC1c)))))
      (.classMem (synCopk (synCplc A (.cv x)) C) (synCltfin))
      (.classMem (synCopk A C) (synCltfin)) p0023 p0028 p0030
  have p0032 := @gOpkeq1 B (synCplc A (.cv x)) C
  have p0033 :=
    @gEleq1d (.classEq B (synCplc A (.cv x))) (synCopk B C)
      (synCopk (synCplc A (.cv x)) C) (synCltfin) p0032
  have p0034 :=
    @gImbi1d (.classEq B (synCplc A (.cv x))) (.classMem (synCopk B C) (synCltfin))
      (.classMem (synCopk (synCplc A (.cv x)) C) (synCltfin))
      (.classMem (synCopk A C) (synCltfin)) p0033
  have p0035 :=
    @gSyl5ibrcom
      (synWa (synWa (.classMem A (synCnnc)) (.classMem C (synCnnc)))
        (.classMem (.cv x) (synCnnc)))
      (.imp (.classMem (synCopk B C) (synCltfin)) (.classMem (synCopk A C) (synCltfin)))
      (.classEq B (synCplc A (.cv x)))
      (.imp (.classMem (synCopk (synCplc A (.cv x)) C) (synCltfin))
        (.classMem (synCopk A C) (synCltfin)))
      p0031 p0034
  have freeVariableCertificate6 :
    x ∉
      ((Wff.imp (.classMem (synCopk B C) (synCltfin))
          (.classMem (synCopk A C) (synCltfin)))).fv :=
    by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cltfin, Finset.mem_union,
      Finset.notMem_empty, fresh_x_not_B, fresh_x_not_C, fresh_x_not_A, or_false,
      not_false_eq_true]
  have freeVariableCertificate7 :
    x ∉ ((synWa (.classMem A (synCnnc)) (.classMem C (synCnnc)))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union,
      Finset.notMem_empty, fresh_x_not_A, fresh_x_not_C, or_false, not_false_eq_true]
  have p0036 :=
    @gRexlimdva (synWa (.classMem A (synCnnc)) (.classMem C (synCnnc)))
      (.classEq B (synCplc A (.cv x)))
      (.imp (.classMem (synCopk B C) (synCltfin)) (.classMem (synCopk A C) (synCltfin)))
      x (synCnnc) freeVariableCertificate6 freeVariableCertificate7 p0035
  have p0037 :=
    @gN3adant2 (.classMem A (synCnnc)) (.classMem C (synCnnc))
      (.imp (synWrex x (synCnnc) (.classEq B (synCplc A (.cv x))))
        (.imp (.classMem (synCopk B C) (synCltfin)) (.classMem (synCopk A C) (synCltfin))))
      (.classMem B (synCnnc)) p0036
  have p0038 :=
    @gSylbid
      (synW3a (.classMem A (synCnnc)) (.classMem B (synCnnc)) (.classMem C (synCnnc)))
      (.classMem (synCopk A B) (synClefin))
      (synWrex x (synCnnc) (.classEq B (synCplc A (.cv x))))
      (.imp (.classMem (synCopk B C) (synCltfin)) (.classMem (synCopk A C) (synCltfin)))
      p0001 p0037
  have p0039 :=
    @gImp3a
      (synW3a (.classMem A (synCnnc)) (.classMem B (synCnnc)) (.classMem C (synCnnc)))
      (.classMem (synCopk A B) (synClefin)) (.classMem (synCopk B C) (synCltfin))
      (.classMem (synCopk A C) (synCltfin)) p0038
  exact p0039

/-- Checked nominal proof certificate identified upstream as `g_ltfintr`. -/
@[expose]
noncomputable def gLtfintr (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf
      (.imp (synW3a (.classMem A (synCnnc)) (.classMem B (synCnnc)) (.classMem C (synCnnc)))
        (.imp (synWa (.classMem (synCopk A B) (synCltfin))
            (.classMem (synCopk B C) (synCltfin)))
          (.classMem (synCopk A C) (synCltfin)))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let z : Var := freshVar proofSupport 2
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_C : x ∉ C.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_C : y ∉ C.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_z_not_C : z ∉ C.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
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
  have fresh_y_ne_z : y ≠ z :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_z_ne_y : z ≠ y := Ne.symm fresh_y_ne_z
  have p0000 :=
    @gAn4 (synWne A (synC0))
      (synWrex x (synCnnc) (.classEq B (synCplc (synCplc A (.cv x)) (synC1c))))
      (synWne B (synC0))
      (synWrex y (synCnnc) (.classEq C (synCplc (synCplc B (.cv y)) (synC1c))))
  have p0001 := @gSimpl (synWne A (synC0)) (synWne B (synC0))
  have p0002 :=
    @gA1i (.imp (synWa (synWne A (synC0)) (synWne B (synC0))) (synWne A (synC0)))
      (synW3a (.classMem A (synCnnc)) (.classMem B (synCnnc)) (.classMem C (synCnnc)))
      p0001
  have freeVariableCertificate0 :
    y ∉ ((Wff.classEq B (synCplc (synCplc A (.cv x)) (synC1c)))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_y_not_B, fresh_y_not_A,
      fresh_y_ne_x, or_false, not_false_eq_true]
  have freeVariableCertificate1 :
    x ∉ ((Wff.classEq C (synCplc (synCplc B (.cv y)) (synC1c)))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_x_not_C, fresh_x_not_B,
      fresh_x_ne_y, or_false, not_false_eq_true]
  have p0003 :=
    @gReeanv (.classEq B (synCplc (synCplc A (.cv x)) (synC1c)))
      (.classEq C (synCplc (synCplc B (.cv y)) (synC1c))) x y (synCnnc) (synCnnc)
      (by
        exact
          (show y ∉ ((synCnnc)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc];
              exact (show y ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
      (by
        exact
          (show x ∉ ((synCnnc)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc];
              exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
      freeVariableCertificate0 freeVariableCertificate1
      (show x ≠ y from (by exact fresh_x_ne_y))
  have p0004 := @gAddccom (synC1c) (.cv y)
  have p0005 := @gPeano2 (.cv y)
  have p0006 :=
    @gSyl5eqel (.classMem (.cv y) (synCnnc)) (synCplc (synC1c) (.cv y))
      (synCplc (.cv y) (synC1c)) (synCnnc) p0004 p0005
  have p0007 := @gNncaddccl (.cv x) (synCplc (synC1c) (.cv y))
  have p0008 :=
    @gSylan2 (.classMem (.cv y) (synCnnc)) (.classMem (.cv x) (synCnnc))
      (.classMem (synCplc (synC1c) (.cv y)) (synCnnc))
      (.classMem (synCplc (.cv x) (synCplc (synC1c) (.cv y))) (synCnnc)) p0006 p0007
  have p0009 :=
    @gAdantl (synWa (.classMem (.cv x) (synCnnc)) (.classMem (.cv y) (synCnnc)))
      (.classMem (synCplc (.cv x) (synCplc (synC1c) (.cv y))) (synCnnc))
      (synW3a (.classMem A (synCnnc)) (.classMem B (synCnnc)) (.classMem C (synCnnc)))
      p0008
  have p0010 := @gAddceq1 B (synCplc (synCplc A (.cv x)) (synC1c)) (.cv y)
  have p0011 :=
    @gAddceq1 (synCplc B (.cv y))
      (synCplc (synCplc (synCplc A (.cv x)) (synC1c)) (.cv y)) (synC1c)
  have p0012 :=
    @gSyl (.classEq B (synCplc (synCplc A (.cv x)) (synC1c)))
      (.classEq (synCplc B (.cv y))
        (synCplc (synCplc (synCplc A (.cv x)) (synC1c)) (.cv y)))
      (.classEq (synCplc (synCplc B (.cv y)) (synC1c))
        (synCplc (synCplc (synCplc (synCplc A (.cv x)) (synC1c)) (.cv y)) (synC1c)))
      p0010 p0011
  have p0013 :=
    @gEqeq2d (.classEq B (synCplc (synCplc A (.cv x)) (synC1c)))
      (synCplc (synCplc B (.cv y)) (synC1c))
      (synCplc (synCplc (synCplc (synCplc A (.cv x)) (synC1c)) (.cv y)) (synC1c)) C
      p0012
  have p0014 :=
    @gBiimpa (.classEq B (synCplc (synCplc A (.cv x)) (synC1c)))
      (.classEq C (synCplc (synCplc B (.cv y)) (synC1c)))
      (.classEq C
        (synCplc (synCplc (synCplc (synCplc A (.cv x)) (synC1c)) (.cv y)) (synC1c)))
      p0013
  have p0015 := @gAddceq2 (.cv z) (synCplc (.cv x) (synCplc (synC1c) (.cv y))) A
  have p0016 := @gAddcass (synCplc A (.cv x)) (synC1c) (.cv y)
  have p0017 := @gAddcass A (.cv x) (synCplc (synC1c) (.cv y))
  have p0018 :=
    @gEqtri (synCplc (synCplc (synCplc A (.cv x)) (synC1c)) (.cv y))
      (synCplc (synCplc A (.cv x)) (synCplc (synC1c) (.cv y)))
      (synCplc A (synCplc (.cv x) (synCplc (synC1c) (.cv y)))) p0016 p0017
  have p0019 :=
    @gSyl6eqr (.classEq (.cv z) (synCplc (.cv x) (synCplc (synC1c) (.cv y))))
      (synCplc A (.cv z)) (synCplc A (synCplc (.cv x) (synCplc (synC1c) (.cv y))))
      (synCplc (synCplc (synCplc A (.cv x)) (synC1c)) (.cv y)) p0015 p0018
  have p0020 :=
    @gAddceq1 (synCplc A (.cv z))
      (synCplc (synCplc (synCplc A (.cv x)) (synC1c)) (.cv y)) (synC1c)
  have p0021 :=
    @gSyl (.classEq (.cv z) (synCplc (.cv x) (synCplc (synC1c) (.cv y))))
      (.classEq (synCplc A (.cv z))
        (synCplc (synCplc (synCplc A (.cv x)) (synC1c)) (.cv y)))
      (.classEq (synCplc (synCplc A (.cv z)) (synC1c))
        (synCplc (synCplc (synCplc (synCplc A (.cv x)) (synC1c)) (.cv y)) (synC1c)))
      p0019 p0020
  have p0022 :=
    @gEqeq2d (.classEq (.cv z) (synCplc (.cv x) (synCplc (synC1c) (.cv y))))
      (synCplc (synCplc A (.cv z)) (synC1c))
      (synCplc (synCplc (synCplc (synCplc A (.cv x)) (synC1c)) (.cv y)) (synC1c)) C
      p0021
  have freeVariableCertificate2 :
    z ∉ ((synCplc (.cv x) (synCplc (synC1c) (.cv y)))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_z_ne_x, fresh_z_ne_y, or_false,
      not_false_eq_true]
  have freeVariableCertificate3 :
    z ∉
      ((Wff.classEq C (synCplc (synCplc (synCplc (synCplc A (.cv x)) (synC1c)) (.cv y))
            (synC1c)))).fv :=
    by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_z_not_C, fresh_z_not_A,
      fresh_z_ne_x, fresh_z_ne_y, or_false, not_false_eq_true]
  have p0023 :=
    @gRspcev (.classEq C (synCplc (synCplc A (.cv z)) (synC1c)))
      (.classEq C
        (synCplc (synCplc (synCplc (synCplc A (.cv x)) (synC1c)) (.cv y)) (synC1c)))
      z (synCplc (.cv x) (synCplc (synC1c) (.cv y))) (synCnnc)
      freeVariableCertificate2
      (by
        exact
          (show z ∉ ((synCnnc)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc];
              exact (show z ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
      freeVariableCertificate3 p0022
  have p0024 :=
    @gEx (.classMem (synCplc (.cv x) (synCplc (synC1c) (.cv y))) (synCnnc))
      (.classEq C
        (synCplc (synCplc (synCplc (synCplc A (.cv x)) (synC1c)) (.cv y)) (synC1c)))
      (synWrex z (synCnnc) (.classEq C (synCplc (synCplc A (.cv z)) (synC1c)))) p0023
  have p0025 :=
    @gSyl2im
      (synWa (synW3a (.classMem A (synCnnc)) (.classMem B (synCnnc))
          (.classMem C (synCnnc)))
        (synWa (.classMem (.cv x) (synCnnc)) (.classMem (.cv y) (synCnnc))))
      (.classMem (synCplc (.cv x) (synCplc (synC1c) (.cv y))) (synCnnc))
      (synWa (.classEq B (synCplc (synCplc A (.cv x)) (synC1c)))
        (.classEq C (synCplc (synCplc B (.cv y)) (synC1c))))
      (.classEq C
        (synCplc (synCplc (synCplc (synCplc A (.cv x)) (synC1c)) (.cv y)) (synC1c)))
      (synWrex z (synCnnc) (.classEq C (synCplc (synCplc A (.cv z)) (synC1c)))) p0009
      p0014 p0024
  have freeVariableCertificate4 :
    x ∉
      ((synWrex z (synCnnc) (.classEq C (synCplc (synCplc A (.cv z)) (synC1c))))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
      Finset.mem_erase, Finset.mem_singleton, Finset.notMem_empty, fresh_x_not_C,
      fresh_x_not_A, fresh_x_ne_z, or_false, and_false, not_false_eq_true]
  have freeVariableCertificate5 :
    y ∉
      ((synWrex z (synCnnc) (.classEq C (synCplc (synCplc A (.cv z)) (synC1c))))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
      Finset.mem_erase, Finset.mem_singleton, Finset.notMem_empty, fresh_y_not_C,
      fresh_y_not_A, fresh_y_ne_z, or_false, and_false, not_false_eq_true]
  have freeVariableCertificate6 :
    x ∉
      ((synW3a (.classMem A (synCnnc)) (.classMem B (synCnnc))
          (.classMem C (synCnnc)))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union,
      Finset.notMem_empty, fresh_x_not_C, fresh_x_not_A, fresh_x_not_B, or_false,
      not_false_eq_true]
  have freeVariableCertificate7 :
    y ∉
      ((synW3a (.classMem A (synCnnc)) (.classMem B (synCnnc))
          (.classMem C (synCnnc)))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union,
      Finset.notMem_empty, fresh_y_not_C, fresh_y_not_A, fresh_y_not_B, or_false,
      not_false_eq_true]
  have p0026 :=
    @gRexlimdvva
      (synW3a (.classMem A (synCnnc)) (.classMem B (synCnnc)) (.classMem C (synCnnc)))
      (synWa (.classEq B (synCplc (synCplc A (.cv x)) (synC1c)))
        (.classEq C (synCplc (synCplc B (.cv y)) (synC1c))))
      (synWrex z (synCnnc) (.classEq C (synCplc (synCplc A (.cv z)) (synC1c)))) x y
      (synCnnc) (synCnnc)
      (by
        exact
          (show y ∉ ((synCnnc)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc];
              exact (show y ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
      freeVariableCertificate4 freeVariableCertificate5 freeVariableCertificate6
      freeVariableCertificate7 (show x ≠ y from (by exact fresh_x_ne_y)) p0025
  have p0027 :=
    @gSyl5bir
      (synWa (synWrex x (synCnnc) (.classEq B (synCplc (synCplc A (.cv x)) (synC1c))))
        (synWrex y (synCnnc) (.classEq C (synCplc (synCplc B (.cv y)) (synC1c)))))
      (synWrex x (synCnnc) (synWrex y (synCnnc)
          (synWa (.classEq B (synCplc (synCplc A (.cv x)) (synC1c)))
            (.classEq C (synCplc (synCplc B (.cv y)) (synC1c))))))
      (synW3a (.classMem A (synCnnc)) (.classMem B (synCnnc)) (.classMem C (synCnnc)))
      (synWrex z (synCnnc) (.classEq C (synCplc (synCplc A (.cv z)) (synC1c)))) p0003
      p0026
  have p0028 :=
    @gAnim12d
      (synW3a (.classMem A (synCnnc)) (.classMem B (synCnnc)) (.classMem C (synCnnc)))
      (synWa (synWne A (synC0)) (synWne B (synC0))) (synWne A (synC0))
      (synWa (synWrex x (synCnnc) (.classEq B (synCplc (synCplc A (.cv x)) (synC1c))))
        (synWrex y (synCnnc) (.classEq C (synCplc (synCplc B (.cv y)) (synC1c)))))
      (synWrex z (synCnnc) (.classEq C (synCplc (synCplc A (.cv z)) (synC1c)))) p0002
      p0027
  have p0029 :=
    @gSyl5bi
      (synWa (synWa (synWne A (synC0))
          (synWrex x (synCnnc) (.classEq B (synCplc (synCplc A (.cv x)) (synC1c)))))
        (synWa (synWne B (synC0))
          (synWrex y (synCnnc) (.classEq C (synCplc (synCplc B (.cv y)) (synC1c))))))
      (synWa (synWa (synWne A (synC0)) (synWne B (synC0))) (synWa
          (synWrex x (synCnnc) (.classEq B (synCplc (synCplc A (.cv x)) (synC1c))))
          (synWrex y (synCnnc) (.classEq C (synCplc (synCplc B (.cv y)) (synC1c))))))
      (synW3a (.classMem A (synCnnc)) (.classMem B (synCnnc)) (.classMem C (synCnnc)))
      (synWa (synWne A (synC0))
        (synWrex z (synCnnc) (.classEq C (synCplc (synCplc A (.cv z)) (synC1c)))))
      p0000 p0028
  have p0030 :=
    @gOpkltfing x A B (synCnnc) (synCnnc)
      (by exact (show x ∉ (A).fv from (by exact fresh_x_not_A)))
      (by exact (show x ∉ (B).fv from (by exact fresh_x_not_B)))
  have p0031 :=
    @gN3adant3 (.classMem A (synCnnc)) (.classMem B (synCnnc))
      (synWb (.classMem (synCopk A B) (synCltfin)) (synWa (synWne A (synC0))
          (synWrex x (synCnnc) (.classEq B (synCplc (synCplc A (.cv x)) (synC1c))))))
      (.classMem C (synCnnc)) p0030
  have p0032 :=
    @gOpkltfing y B C (synCnnc) (synCnnc)
      (by exact (show y ∉ (B).fv from (by exact fresh_y_not_B)))
      (by exact (show y ∉ (C).fv from (by exact fresh_y_not_C)))
  have p0033 :=
    @gN3adant1 (.classMem B (synCnnc)) (.classMem C (synCnnc))
      (synWb (.classMem (synCopk B C) (synCltfin)) (synWa (synWne B (synC0))
          (synWrex y (synCnnc) (.classEq C (synCplc (synCplc B (.cv y)) (synC1c))))))
      (.classMem A (synCnnc)) p0032
  have p0034 :=
    @gAnbi12d
      (synW3a (.classMem A (synCnnc)) (.classMem B (synCnnc)) (.classMem C (synCnnc)))
      (.classMem (synCopk A B) (synCltfin))
      (synWa (synWne A (synC0))
        (synWrex x (synCnnc) (.classEq B (synCplc (synCplc A (.cv x)) (synC1c)))))
      (.classMem (synCopk B C) (synCltfin))
      (synWa (synWne B (synC0))
        (synWrex y (synCnnc) (.classEq C (synCplc (synCplc B (.cv y)) (synC1c)))))
      p0031 p0033
  have p0035 :=
    @gOpkltfing z A C (synCnnc) (synCnnc)
      (by exact (show z ∉ (A).fv from (by exact fresh_z_not_A)))
      (by exact (show z ∉ (C).fv from (by exact fresh_z_not_C)))
  have p0036 :=
    @gN3adant2 (.classMem A (synCnnc)) (.classMem C (synCnnc))
      (synWb (.classMem (synCopk A C) (synCltfin)) (synWa (synWne A (synC0))
          (synWrex z (synCnnc) (.classEq C (synCplc (synCplc A (.cv z)) (synC1c))))))
      (.classMem B (synCnnc)) p0035
  have p0037 :=
    @gN3imtr4d
      (synW3a (.classMem A (synCnnc)) (.classMem B (synCnnc)) (.classMem C (synCnnc)))
      (synWa (synWa (synWne A (synC0))
          (synWrex x (synCnnc) (.classEq B (synCplc (synCplc A (.cv x)) (synC1c)))))
        (synWa (synWne B (synC0))
          (synWrex y (synCnnc) (.classEq C (synCplc (synCplc B (.cv y)) (synC1c))))))
      (synWa (synWne A (synC0))
        (synWrex z (synCnnc) (.classEq C (synCplc (synCplc A (.cv z)) (synC1c)))))
      (synWa (.classMem (synCopk A B) (synCltfin)) (.classMem (synCopk B C) (synCltfin)))
      (.classMem (synCopk A C) (synCltfin)) p0029 p0034 p0036
  exact p0037

/-- Checked nominal proof certificate identified upstream as `g_ltfinasym`. -/
@[expose]
noncomputable def gLtfinasym (A : Class) (B : Class) :
    Nominal.NPrf
      (.imp (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
        (.imp (.classMem (synCopk A B) (synCltfin))
          (.neg (.classMem (synCopk B A) (synCltfin))))) :=
  by
  have p0000 := @gLtfinirr A
  have p0001 :=
    @gAd2antrr (.classMem A (synCnnc)) (.neg (.classMem (synCopk A A) (synCltfin)))
      (.classMem B (synCnnc)) (.classMem (synCopk A B) (synCltfin)) p0000
  have p0002 := @gLtfintr A B A
  have p0003 :=
    @gN3anidm13 (.classMem A (synCnnc)) (.classMem B (synCnnc))
      (.imp (synWa (.classMem (synCopk A B) (synCltfin))
          (.classMem (synCopk B A) (synCltfin))) (.classMem (synCopk A A) (synCltfin)))
      p0002
  have p0004 :=
    @gExpdimp (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
      (.classMem (synCopk A B) (synCltfin)) (.classMem (synCopk B A) (synCltfin))
      (.classMem (synCopk A A) (synCltfin)) p0003
  have p0005 :=
    @gMtod
      (synWa (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
        (.classMem (synCopk A B) (synCltfin)))
      (.classMem (synCopk B A) (synCltfin)) (.classMem (synCopk A A) (synCltfin))
      p0001 p0004
  have p0006 :=
    @gEx (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
      (.classMem (synCopk A B) (synCltfin))
      (.neg (.classMem (synCopk B A) (synCltfin))) p0005
  exact p0006

/-- Checked nominal proof certificate identified upstream as `g_n_0cminle`. -/
@[expose]
noncomputable def gN0cminle (A : Class) :
    Nominal.NPrf
      (.imp (.classMem A (synCnnc)) (.classMem (synCopk (synC0c) A) (synClefin))) :=
  by
  have p0000 := @gAddcid2 A
  have p0001 := @gOpkeq2i (synCplc (synC0c) A) A (synC0c) p0000
  have p0002 := @gPeano1
  have p0003 := @gLefinaddc (synC0c) A (synCnnc)
  have p0004 :=
    @gMpan (.classMem (synC0c) (synCnnc)) (.classMem A (synCnnc))
      (.classMem (synCopk (synC0c) (synCplc (synC0c) A)) (synClefin)) p0002 p0003
  have p0005 :=
    @gSyl5eqelr (.classMem A (synCnnc)) (synCopk (synC0c) A)
      (synCopk (synC0c) (synCplc (synC0c) A)) (synClefin) p0001 p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_ltfinp1`. -/
@[expose]
noncomputable def gLtfinp1 (A : Class) (V : Class) :
    Nominal.NPrf
      (.imp (synWa (.classMem A V) (synWne A (synC0)))
        (.classMem (synCopk A (synCplc A (synC1c))) (synCltfin))) :=
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
  have p0000 := @gSimpr (.classMem A V) (synWne A (synC0))
  have p0001 := @gPeano1
  have p0002 := @gAddcid1 A
  have p0003 := @gAddceq1i (synCplc A (synC0c)) A (synC1c) p0002
  have p0004 :=
    @gEqcomi (synCplc (synCplc A (synC0c)) (synC1c)) (synCplc A (synC1c)) p0003
  have p0005 := @gAddceq2 (.cv x) (synC0c) A
  have p0006 :=
    @gAddceq1d (.classEq (.cv x) (synC0c)) (synCplc A (.cv x)) (synCplc A (synC0c))
      (synC1c) p0005
  have p0007 :=
    @gEqeq2d (.classEq (.cv x) (synC0c)) (synCplc (synCplc A (.cv x)) (synC1c))
      (synCplc (synCplc A (synC0c)) (synC1c)) (synCplc A (synC1c)) p0006
  have freeVariableCertificate0 :
    x ∉
      ((Wff.classEq (synCplc A (synC1c)) (synCplc (synCplc A (synC0c)) (synC1c)))).fv :=
    by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union,
      Finset.notMem_empty, fresh_x_not_A, or_false, not_false_eq_true]
  have p0008 :=
    @gRspcev (.classEq (synCplc A (synC1c)) (synCplc (synCplc A (.cv x)) (synC1c)))
      (.classEq (synCplc A (synC1c)) (synCplc (synCplc A (synC0c)) (synC1c))) x
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
      freeVariableCertificate0 p0007
  have p0009 :=
    @gMp2an (.classMem (synC0c) (synCnnc))
      (.classEq (synCplc A (synC1c)) (synCplc (synCplc A (synC0c)) (synC1c)))
      (synWrex x (synCnnc)
        (.classEq (synCplc A (synC1c)) (synCplc (synCplc A (.cv x)) (synC1c))))
      p0001 p0004 p0008
  have p0010 :=
    @gJctir (synWa (.classMem A V) (synWne A (synC0))) (synWne A (synC0))
      (synWrex x (synCnnc)
        (.classEq (synCplc A (synC1c)) (synCplc (synCplc A (.cv x)) (synC1c))))
      p0000 p0009
  have p0011 := @gN1cex
  have p0012 := @gAddcexg A (synC1c) V (synCvv)
  have p0013 :=
    @gMpan2 (.classMem A V) (.classMem (synC1c) (synCvv))
      (.classMem (synCplc A (synC1c)) (synCvv)) p0011 p0012
  have freeVariableCertificate1 : x ∉ ((synCplc A (synC1c))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
      Finset.notMem_empty, fresh_x_not_A, or_false, not_false_eq_true]
  have p0014 :=
    @gOpkltfing x A (synCplc A (synC1c)) V (synCvv)
      (by exact (show x ∉ (A).fv from (by exact fresh_x_not_A))) freeVariableCertificate1
  have p0015 :=
    @gMpdan (.classMem A V) (.classMem (synCplc A (synC1c)) (synCvv))
      (synWb (.classMem (synCopk A (synCplc A (synC1c))) (synCltfin))
        (synWa (synWne A (synC0)) (synWrex x (synCnnc)
            (.classEq (synCplc A (synC1c)) (synCplc (synCplc A (.cv x)) (synC1c))))))
      p0013 p0014
  have p0016 :=
    @gAdantr (.classMem A V)
      (synWb (.classMem (synCopk A (synCplc A (synC1c))) (synCltfin))
        (synWa (synWne A (synC0)) (synWrex x (synCnnc)
            (.classEq (synCplc A (synC1c)) (synCplc (synCplc A (.cv x)) (synC1c))))))
      (synWne A (synC0)) p0015
  have p0017 :=
    @gMpbird (synWa (.classMem A V) (synWne A (synC0)))
      (.classMem (synCopk A (synCplc A (synC1c))) (synCltfin))
      (synWa (synWne A (synC0)) (synWrex x (synCnnc)
          (.classEq (synCplc A (synC1c)) (synCplc (synCplc A (.cv x)) (synC1c)))))
      p0010 p0016
  exact p0017


end NFChoice.DirectNominalPrf.WPPReplay

end
