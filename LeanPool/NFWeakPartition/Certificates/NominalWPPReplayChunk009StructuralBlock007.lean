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

@[expose]
noncomputable def g_nndisjeq (M : Class) (N : Class) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)))
        (syn_wo (.classEq (syn_cin M N) (syn_c0)) (.classEq M N))) :=
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
  have p0000 := @g_vex p
  have p0001 :=
    @g_elcompl (.cv p)
      (syn_cimak (syn_ccompl (syn_cun (syn_ccompl
              (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cidk))) (syn_cnnc))
      p0000
  have freeVariableCertificate0 :
    n ∉
      ((syn_ccompl (syn_cun (syn_ccompl
              (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cidk)))).fv :=
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
    @g_elimak n
      (syn_ccompl (syn_cun (syn_ccompl
            (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
              (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cidk)))
      (syn_cnnc) (.cv p) freeVariableCertificate0
      (by
        exact
          (show n ∉ ((syn_cnnc)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc];
              exact (show n ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
      freeVariableCertificate1 p0000
  have p0003 := @g_opkex (.cv n) (.cv p)
  have p0004 :=
    @g_elcompl (syn_copk (.cv n) (.cv p))
      (syn_cun (syn_ccompl
          (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
            (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cidk))
      p0003
  have p0005 :=
    @g_elun (syn_copk (.cv n) (.cv p))
      (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
          (syn_cpw1 (syn_cpw1 (syn_c1c)))))
      (syn_cidk)
  have p0006 := @g_vex n
  have p0007 := @g_ndisjrelk (.cv n) (.cv p) p0006 p0000
  have p0008 :=
    @g_notbii
      (.classMem (syn_copk (.cv n) (.cv p))
        (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
          (syn_cpw1 (syn_cpw1 (syn_c1c)))))
      (syn_wne (syn_cin (.cv n) (.cv p)) (syn_c0)) p0007
  have p0009 :=
    @g_elcompl (syn_copk (.cv n) (.cv p))
      (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c))))
      p0003
  have p0010 := (Nominal.biimpRefl (syn_wne (syn_cin (.cv n) (.cv p)) (syn_c0)))
  have p0011 :=
    @g_con2bii (syn_wne (syn_cin (.cv n) (.cv p)) (syn_c0))
      (.classEq (syn_cin (.cv n) (.cv p)) (syn_c0)) p0010
  have p0012 :=
    @g_n_3bitr4i
      (.neg (.classMem (syn_copk (.cv n) (.cv p))
          (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
            (syn_cpw1 (syn_cpw1 (syn_c1c))))))
      (.neg (syn_wne (syn_cin (.cv n) (.cv p)) (syn_c0)))
      (.classMem (syn_copk (.cv n) (.cv p)) (syn_ccompl
          (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
            (syn_cpw1 (syn_cpw1 (syn_c1c))))))
      (.classEq (syn_cin (.cv n) (.cv p)) (syn_c0)) p0008 p0009 p0011
  have p0013 := @g_opkelidkg (.cv n) (.cv p) (syn_cvv) (syn_cvv)
  have p0014_e02_recanon :
    Nominal.NPrf
      (.imp (syn_wa (.classMem (.cv n) (syn_cvv)) (.classMem (.cv p) (syn_cvv)))
        (syn_wb (.classMem (syn_copk (.cv n) (.cv p)) (syn_cidk)) (.objEq n p))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wa syn_cvv syn_wb syn_copk syn_cpr syn_cun syn_cnin syn_wnan syn_ccompl
          syn_csn syn_cidk syn_wex
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
    @g_mp2an (.classMem (.cv n) (syn_cvv)) (.classMem (.cv p) (syn_cvv))
      (syn_wb (.classMem (syn_copk (.cv n) (.cv p)) (syn_cidk)) (.objEq n p)) p0006 p0000
      p0014_e02_recanon
  have p0015 :=
    @g_orbi12i
      (.classMem (syn_copk (.cv n) (.cv p)) (syn_ccompl
          (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
            (syn_cpw1 (syn_cpw1 (syn_c1c))))))
      (.classEq (syn_cin (.cv n) (.cv p)) (syn_c0))
      (.classMem (syn_copk (.cv n) (.cv p)) (syn_cidk)) (.objEq n p) p0012 p0014
  have p0016 := @g_incom (.cv n) (.cv p)
  have p0017 :=
    @g_eqeq1i (syn_cin (.cv n) (.cv p)) (syn_cin (.cv p) (.cv n)) (syn_c0) p0016
  have p0018 := @g_eqcom (.cv n) (.cv p)
  have p0019_e01_recanon : Nominal.NPrf (syn_wb (.objEq n p) (.objEq p n)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb
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
    @g_orbi12i (.classEq (syn_cin (.cv n) (.cv p)) (syn_c0))
      (.classEq (syn_cin (.cv p) (.cv n)) (syn_c0)) (.objEq n p) (.objEq p n) p0017
      p0019_e01_recanon
  have p0020 :=
    @g_n_3bitri
      (.classMem (syn_copk (.cv n) (.cv p)) (syn_cun (syn_ccompl
            (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
              (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cidk)))
      (syn_wo (.classMem (syn_copk (.cv n) (.cv p)) (syn_ccompl
            (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
              (syn_cpw1 (syn_cpw1 (syn_c1c))))))
        (.classMem (syn_copk (.cv n) (.cv p)) (syn_cidk)))
      (syn_wo (.classEq (syn_cin (.cv n) (.cv p)) (syn_c0)) (.objEq n p))
      (syn_wo (.classEq (syn_cin (.cv p) (.cv n)) (syn_c0)) (.objEq p n)) p0005 p0015
      p0019
  have p0021 :=
    @g_xchbinx
      (.classMem (syn_copk (.cv n) (.cv p)) (syn_ccompl (syn_cun (syn_ccompl
              (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cidk))))
      (.classMem (syn_copk (.cv n) (.cv p)) (syn_cun (syn_ccompl
            (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
              (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cidk)))
      (syn_wo (.classEq (syn_cin (.cv p) (.cv n)) (syn_c0)) (.objEq p n)) p0004 p0020
  have p0022 :=
    @g_rexbii
      (.classMem (syn_copk (.cv n) (.cv p)) (syn_ccompl (syn_cun (syn_ccompl
              (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cidk))))
      (.neg (syn_wo (.classEq (syn_cin (.cv p) (.cv n)) (syn_c0)) (.objEq p n))) n
      (syn_cnnc) p0021
  have p0023 :=
    @g_rexnal (syn_wo (.classEq (syn_cin (.cv p) (.cv n)) (syn_c0)) (.objEq p n)) n
      (syn_cnnc)
  have p0024 :=
    @g_n_3bitri
      (.classMem (.cv p) (syn_cimak (syn_ccompl (syn_cun (syn_ccompl
                (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                  (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cidk))) (syn_cnnc)))
      (syn_wrex n (syn_cnnc) (.classMem (syn_copk (.cv n) (.cv p)) (syn_ccompl (syn_cun
              (syn_ccompl
                (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                  (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cidk)))))
      (syn_wrex n (syn_cnnc)
        (.neg (syn_wo (.classEq (syn_cin (.cv p) (.cv n)) (syn_c0)) (.objEq p n))))
      (.neg (syn_wral n (syn_cnnc)
          (syn_wo (.classEq (syn_cin (.cv p) (.cv n)) (syn_c0)) (.objEq p n))))
      p0002 p0022 p0023
  have p0025 :=
    @g_con2bii
      (.classMem (.cv p) (syn_cimak (syn_ccompl (syn_cun (syn_ccompl
                (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                  (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cidk))) (syn_cnnc)))
      (syn_wral n (syn_cnnc)
        (syn_wo (.classEq (syn_cin (.cv p) (.cv n)) (syn_c0)) (.objEq p n)))
      p0024
  have p0026 :=
    @g_bitr4i
      (.classMem (.cv p) (syn_ccompl (syn_cimak (syn_ccompl (syn_cun (syn_ccompl
                  (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                    (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cidk))) (syn_cnnc))))
      (.neg (.classMem (.cv p) (syn_cimak (syn_ccompl (syn_cun (syn_ccompl
                  (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                    (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cidk))) (syn_cnnc))))
      (syn_wral n (syn_cnnc)
        (syn_wo (.classEq (syn_cin (.cv p) (.cv n)) (syn_c0)) (.objEq p n)))
      p0001 p0025
  have freeVariableCertificate2 :
    p ∉
      ((syn_ccompl (syn_cimak (syn_ccompl (syn_cun (syn_ccompl
                  (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                    (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cidk))) (syn_cnnc)))).fv :=
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
    @g_eqabi
      (syn_wral n (syn_cnnc)
        (syn_wo (.classEq (syn_cin (.cv p) (.cv n)) (syn_c0)) (.objEq p n)))
      p
      (syn_ccompl (syn_cimak (syn_ccompl (syn_cun (syn_ccompl
                (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                  (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cidk))) (syn_cnnc)))
      freeVariableCertificate2 p0026
  have p0028 := @g_ssetkex
  have p0029 := @g_ins3kex (syn_cssetk) p0028
  have p0031 := @g_ins2kex (syn_cssetk) p0028
  have p0032 := @g_inex (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)) p0029 p0031
  have p0033 := @g_n_1cex
  have p0034 := @g_pw1ex (syn_c1c) p0033
  have p0035 := @g_pw1ex (syn_cpw1 (syn_c1c)) p0034
  have p0036 :=
    @g_imakex (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
      (syn_cpw1 (syn_cpw1 (syn_c1c))) p0032 p0035
  have p0037 :=
    @g_complex
      (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c))))
      p0036
  have p0038 := @g_idkex
  have p0039 :=
    @g_unex
      (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
          (syn_cpw1 (syn_cpw1 (syn_c1c)))))
      (syn_cidk) p0037 p0038
  have p0040 :=
    @g_complex
      (syn_cun (syn_ccompl
          (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
            (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cidk))
      p0039
  have p0041 := @g_nncex
  have p0042 :=
    @g_imakex
      (syn_ccompl (syn_cun (syn_ccompl
            (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
              (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cidk)))
      (syn_cnnc) p0040 p0041
  have p0043 :=
    @g_complex
      (syn_cimak (syn_ccompl (syn_cun (syn_ccompl
              (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cidk))) (syn_cnnc))
      p0042
  have p0044 :=
    @g_eqeltrri
      (syn_ccompl (syn_cimak (syn_ccompl (syn_cun (syn_ccompl
                (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                  (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cidk))) (syn_cnnc)))
      (.cab p (syn_wral n (syn_cnnc)
          (syn_wo (.classEq (syn_cin (.cv p) (.cv n)) (syn_c0)) (.objEq p n))))
      (syn_cvv) p0027 p0043
  have p0045 := (Nominal.classEqRefl (syn_c0c))
  have p0046 := @g_eqeq2i (syn_c0c) (syn_csn (syn_c0)) (.cv p) p0045
  have p0047 :=
    @g_biimpi (.classEq (.cv p) (syn_c0c)) (.classEq (.cv p) (syn_csn (syn_c0))) p0046
  have p0048 :=
    @g_ineq1d (.classEq (.cv p) (syn_c0c)) (.cv p) (syn_csn (syn_c0)) (.cv n) p0047
  have p0049 :=
    @g_eqeq1d (.classEq (.cv p) (syn_c0c)) (syn_cin (.cv p) (.cv n))
      (syn_cin (syn_csn (syn_c0)) (.cv n)) (syn_c0) p0048
  have p0050 := @g_incom (syn_csn (syn_c0)) (.cv n)
  have p0051 :=
    @g_eqeq1i (syn_cin (syn_csn (syn_c0)) (.cv n)) (syn_cin (.cv n) (syn_csn (syn_c0)))
      (syn_c0) p0050
  have p0052 := @g_disjsn (.cv n) (syn_c0)
  have p0053 :=
    @g_bitri (.classEq (syn_cin (syn_csn (syn_c0)) (.cv n)) (syn_c0))
      (.classEq (syn_cin (.cv n) (syn_csn (syn_c0))) (syn_c0))
      (.neg (.classMem (syn_c0) (.cv n))) p0051 p0052
  have p0054 :=
    @g_syl6bb (.classEq (.cv p) (syn_c0c)) (.classEq (syn_cin (.cv p) (.cv n)) (syn_c0))
      (.classEq (syn_cin (syn_csn (syn_c0)) (.cv n)) (syn_c0))
      (.neg (.classMem (syn_c0) (.cv n))) p0049 p0053
  have p0055 := @g_eqeq1 (.cv p) (syn_c0c) (.cv n)
  have p0056 := @g_eqcom (syn_c0c) (.cv n)
  have p0057_e00_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv p) (syn_c0c)) (syn_wb (.objEq p n) (.classEq (syn_c0c) (.cv n)))) :=
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
      p0055
  have p0057 :=
    @g_syl6bb (.classEq (.cv p) (syn_c0c)) (.objEq p n) (.classEq (syn_c0c) (.cv n))
      (.classEq (.cv n) (syn_c0c)) p0057_e00_recanon p0056
  have p0058 :=
    @g_orbi12d (.classEq (.cv p) (syn_c0c)) (.classEq (syn_cin (.cv p) (.cv n)) (syn_c0))
      (.neg (.classMem (syn_c0) (.cv n))) (.objEq p n) (.classEq (.cv n) (syn_c0c)) p0054
      p0057
  have freeVariableCertificate3 : n ∉ ((Wff.classEq (.cv p) (syn_c0c))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_n_ne_p, or_false,
      not_false_eq_true]
  have p0059 :=
    @g_ralbidv (.classEq (.cv p) (syn_c0c))
      (syn_wo (.classEq (syn_cin (.cv p) (.cv n)) (syn_c0)) (.objEq p n))
      (syn_wo (.neg (.classMem (syn_c0) (.cv n))) (.classEq (.cv n) (syn_c0c))) n
      (syn_cnnc) freeVariableCertificate3 p0058
  have p0060 := @g_ineq1 (.cv p) (.cv m) (.cv n)
  have p0061_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq p m) (.classEq (syn_cin (.cv p) (.cv n)) (syn_cin (.cv m) (.cv n)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_cin syn_ccompl syn_cnin syn_wnan syn_wa
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0060
  have p0061 :=
    @g_eqeq1d (.objEq p m) (syn_cin (.cv p) (.cv n)) (syn_cin (.cv m) (.cv n)) (syn_c0)
      p0061_e00_recanon
  have p0062 := @g_eqeq1 (.cv p) (.cv m) (.cv n)
  have p0063_e01_recanon :
    Nominal.NPrf (.imp (.objEq p m) (syn_wb (.objEq p n) (.objEq m n))) :=
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
      p0062
  have p0063 :=
    @g_orbi12d (.objEq p m) (.classEq (syn_cin (.cv p) (.cv n)) (syn_c0))
      (.classEq (syn_cin (.cv m) (.cv n)) (syn_c0)) (.objEq p n) (.objEq m n) p0061
      p0063_e01_recanon
  have freeVariableCertificate4 : n ∉ ((Wff.objEq p m)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_insert,
      Finset.mem_singleton, fresh_n_ne_p, fresh_n_ne_m, or_false, not_false_eq_true]
  have p0064 :=
    @g_ralbidv (.objEq p m)
      (syn_wo (.classEq (syn_cin (.cv p) (.cv n)) (syn_c0)) (.objEq p n))
      (syn_wo (.classEq (syn_cin (.cv m) (.cv n)) (syn_c0)) (.objEq m n)) n (syn_cnnc)
      freeVariableCertificate4 p0063
  have p0065 := @g_ineq2 (.cv n) (.cv q) (.cv m)
  have p0066_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq n q) (.classEq (syn_cin (.cv m) (.cv n)) (syn_cin (.cv m) (.cv q)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_cin syn_ccompl syn_cnin syn_wnan syn_wa
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0065
  have p0066 :=
    @g_eqeq1d (.objEq n q) (syn_cin (.cv m) (.cv n)) (syn_cin (.cv m) (.cv q)) (syn_c0)
      p0066_e00_recanon
  have p0067 := @g_equequ2 n q m
  have p0068 :=
    @g_orbi12d (.objEq n q) (.classEq (syn_cin (.cv m) (.cv n)) (syn_c0))
      (.classEq (syn_cin (.cv m) (.cv q)) (syn_c0)) (.objEq m n) (.objEq m q) p0066 p0067
  have freeVariableCertificate5 :
    q ∉ ((syn_wo (.classEq (syn_cin (.cv m) (.cv n)) (syn_c0)) (.objEq m n))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wo,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
      NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_union, Finset.mem_insert,
      Finset.mem_singleton, Finset.notMem_empty, fresh_q_ne_m, fresh_q_ne_n, or_false,
      not_false_eq_true]
  have freeVariableCertificate6 :
    n ∉ ((syn_wo (.classEq (syn_cin (.cv m) (.cv q)) (syn_c0)) (.objEq m q))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wo,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
      NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_union, Finset.mem_insert,
      Finset.mem_singleton, Finset.notMem_empty, fresh_n_ne_m, fresh_n_ne_q, or_false,
      not_false_eq_true]
  have p0069 :=
    @g_cbvralv (syn_wo (.classEq (syn_cin (.cv m) (.cv n)) (syn_c0)) (.objEq m n))
      (syn_wo (.classEq (syn_cin (.cv m) (.cv q)) (syn_c0)) (.objEq m q)) n q (syn_cnnc)
      (by
        exact
          (show n ∉ ((syn_cnnc)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc];
              exact (show n ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
      (by
        exact
          (show q ∉ ((syn_cnnc)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc];
              exact (show q ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
      freeVariableCertificate5 freeVariableCertificate6 p0068
  have p0070 :=
    @g_syl6bb (.objEq p m)
      (syn_wral n (syn_cnnc)
        (syn_wo (.classEq (syn_cin (.cv p) (.cv n)) (syn_c0)) (.objEq p n)))
      (syn_wral n (syn_cnnc)
        (syn_wo (.classEq (syn_cin (.cv m) (.cv n)) (syn_c0)) (.objEq m n)))
      (syn_wral q (syn_cnnc)
        (syn_wo (.classEq (syn_cin (.cv m) (.cv q)) (syn_c0)) (.objEq m q)))
      p0064 p0069
  have p0071 := @g_ineq1 (.cv p) (syn_cplc (.cv m) (syn_c1c)) (.cv n)
  have p0072 :=
    @g_eqeq1d (.classEq (.cv p) (syn_cplc (.cv m) (syn_c1c))) (syn_cin (.cv p) (.cv n))
      (syn_cin (syn_cplc (.cv m) (syn_c1c)) (.cv n)) (syn_c0) p0071
  have p0073 := @g_eqeq1 (.cv p) (syn_cplc (.cv m) (syn_c1c)) (.cv n)
  have p0074_e01_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv p) (syn_cplc (.cv m) (syn_c1c)))
        (syn_wb (.objEq p n) (.classEq (syn_cplc (.cv m) (syn_c1c)) (.cv n)))) :=
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
      p0073
  have p0074 :=
    @g_orbi12d (.classEq (.cv p) (syn_cplc (.cv m) (syn_c1c)))
      (.classEq (syn_cin (.cv p) (.cv n)) (syn_c0))
      (.classEq (syn_cin (syn_cplc (.cv m) (syn_c1c)) (.cv n)) (syn_c0)) (.objEq p n)
      (.classEq (syn_cplc (.cv m) (syn_c1c)) (.cv n)) p0072 p0074_e01_recanon
  have freeVariableCertificate7 :
    n ∉ ((Wff.classEq (.cv p) (syn_cplc (.cv m) (syn_c1c)))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_n_ne_p, fresh_n_ne_m, or_false,
      not_false_eq_true]
  have p0075 :=
    @g_ralbidv (.classEq (.cv p) (syn_cplc (.cv m) (syn_c1c)))
      (syn_wo (.classEq (syn_cin (.cv p) (.cv n)) (syn_c0)) (.objEq p n))
      (syn_wo (.classEq (syn_cin (syn_cplc (.cv m) (syn_c1c)) (.cv n)) (syn_c0))
        (.classEq (syn_cplc (.cv m) (syn_c1c)) (.cv n)))
      n (syn_cnnc) freeVariableCertificate7 p0074
  have p0076 := @g_ineq1 (.cv p) M (.cv n)
  have p0077 :=
    @g_eqeq1d (.classEq (.cv p) M) (syn_cin (.cv p) (.cv n)) (syn_cin M (.cv n)) (syn_c0)
      p0076
  have p0078 := @g_eqeq1 (.cv p) M (.cv n)
  have p0079_e01_recanon :
    Nominal.NPrf (.imp (.classEq (.cv p) M) (syn_wb (.objEq p n) (.classEq M (.cv n)))) :=
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
      p0078
  have p0079 :=
    @g_orbi12d (.classEq (.cv p) M) (.classEq (syn_cin (.cv p) (.cv n)) (syn_c0))
      (.classEq (syn_cin M (.cv n)) (syn_c0)) (.objEq p n) (.classEq M (.cv n)) p0077
      p0079_e01_recanon
  have freeVariableCertificate8 : n ∉ ((Wff.classEq (.cv p) M)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      fresh_n_ne_p, fresh_n_not_M, or_false, not_false_eq_true]
  have p0080 :=
    @g_ralbidv (.classEq (.cv p) M)
      (syn_wo (.classEq (syn_cin (.cv p) (.cv n)) (syn_c0)) (.objEq p n))
      (syn_wo (.classEq (syn_cin M (.cv n)) (syn_c0)) (.classEq M (.cv n))) n (syn_cnnc)
      freeVariableCertificate8 p0079
  have freeVariableCertificate9 : m ∉ ((Class.cv n)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_m_ne_n, not_false_eq_true]
  have p0081 := @g_nnc0suc m (.cv n) freeVariableCertificate9
  have p0082 := @g_n_0nelsuc (.cv m)
  have p0083 := @g_eleq2 (.cv n) (syn_cplc (.cv m) (syn_c1c)) (syn_c0)
  have p0084 :=
    @g_biimpcd (.classEq (.cv n) (syn_cplc (.cv m) (syn_c1c)))
      (.classMem (syn_c0) (.cv n)) (.classMem (syn_c0) (syn_cplc (.cv m) (syn_c1c))) p0083
  have p0085 :=
    @g_mtoi (.classMem (syn_c0) (.cv n)) (.classEq (.cv n) (syn_cplc (.cv m) (syn_c1c)))
      (.classMem (syn_c0) (syn_cplc (.cv m) (syn_c1c))) p0082 p0084
  have p0086 :=
    @g_adantr (.classMem (syn_c0) (.cv n))
      (.neg (.classEq (.cv n) (syn_cplc (.cv m) (syn_c1c))))
      (.classMem (.cv m) (syn_cnnc)) p0085
  have freeVariableCertificate10 : m ∉ ((Wff.classMem (syn_c0) (.cv n))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      Finset.notMem_empty, fresh_m_ne_n, or_false, not_false_eq_true]
  have p0087 :=
    @g_nrexdv (.classMem (syn_c0) (.cv n)) (.classEq (.cv n) (syn_cplc (.cv m) (syn_c1c)))
      m (syn_cnnc) freeVariableCertificate10 p0086
  have p0088 :=
    @g_orel2 (syn_wrex m (syn_cnnc) (.classEq (.cv n) (syn_cplc (.cv m) (syn_c1c))))
      (.classEq (.cv n) (syn_c0c))
  have p0089 :=
    @g_syl (.classMem (syn_c0) (.cv n))
      (.neg (syn_wrex m (syn_cnnc) (.classEq (.cv n) (syn_cplc (.cv m) (syn_c1c)))))
      (.imp (syn_wo (.classEq (.cv n) (syn_c0c))
          (syn_wrex m (syn_cnnc) (.classEq (.cv n) (syn_cplc (.cv m) (syn_c1c)))))
        (.classEq (.cv n) (syn_c0c)))
      p0087 p0088
  have p0090 :=
    @g_com12 (.classMem (syn_c0) (.cv n))
      (syn_wo (.classEq (.cv n) (syn_c0c))
        (syn_wrex m (syn_cnnc) (.classEq (.cv n) (syn_cplc (.cv m) (syn_c1c)))))
      (.classEq (.cv n) (syn_c0c)) p0089
  have p0091 :=
    @g_sylbi (.classMem (.cv n) (syn_cnnc))
      (syn_wo (.classEq (.cv n) (syn_c0c))
        (syn_wrex m (syn_cnnc) (.classEq (.cv n) (syn_cplc (.cv m) (syn_c1c)))))
      (.imp (.classMem (syn_c0) (.cv n)) (.classEq (.cv n) (syn_c0c))) p0081 p0090
  have p0092 := @g_imor (.classMem (syn_c0) (.cv n)) (.classEq (.cv n) (syn_c0c))
  have p0093 :=
    @g_sylib (.classMem (.cv n) (syn_cnnc))
      (.imp (.classMem (syn_c0) (.cv n)) (.classEq (.cv n) (syn_c0c)))
      (syn_wo (.neg (.classMem (syn_c0) (.cv n))) (.classEq (.cv n) (syn_c0c))) p0091
      p0092
  have p0094 :=
    @g_rgen (syn_wo (.neg (.classMem (syn_c0) (.cv n))) (.classEq (.cv n) (syn_c0c))) n
      (syn_cnnc) p0093
  have freeVariableCertificate11 :
    a ∉ ((syn_cin (syn_cplc (.cv m) (syn_c1c)) (.cv n))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_a_ne_m, fresh_a_ne_n, or_false,
      not_false_eq_true]
  have p0095 :=
    @g_neq0 a (syn_cin (syn_cplc (.cv m) (syn_c1c)) (.cv n)) freeVariableCertificate11
  have p0096 := @g_elin (.cv a) (syn_cplc (.cv m) (syn_c1c)) (.cv n)
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
    @g_elsuc x (.cv a) (.cv m) b freeVariableCertificate12 freeVariableCertificate13
      freeVariableCertificate14 (show b ≠ x from (by exact fresh_b_ne_x))
  have p0098 := @g_vex x
  have p0099 := @g_elcompl (.cv x) (.cv b) p0098
  have p0100_e00_recanon :
    Nominal.NPrf (syn_wb (.classMem (.cv x) (syn_ccompl (.cv b))) (.neg (.objMem x b))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_ccompl syn_cnin syn_wnan syn_wa
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
    @g_anbi2i (.classMem (.cv x) (syn_ccompl (.cv b))) (.neg (.objMem x b)) (.objMem b m)
      p0100_e00_recanon
  have p0101 :=
    @g_simp1r (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc))
      (syn_wral q (syn_cnnc)
        (syn_wo (.classEq (syn_cin (.cv m) (.cv q)) (syn_c0)) (.objEq m q)))
      (syn_wa (.objMem b m) (.neg (.objMem x b)))
  have freeVariableCertificate15 : p ∉ ((Class.cv n)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_p_ne_n, not_false_eq_true]
  have p0102 := @g_nnc0suc p (.cv n) freeVariableCertificate15
  have p0103 :=
    @g_sylib
      (syn_w3a (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc)))
        (syn_wral q (syn_cnnc)
          (syn_wo (.classEq (syn_cin (.cv m) (.cv q)) (syn_c0)) (.objEq m q)))
        (syn_wa (.objMem b m) (.neg (.objMem x b))))
      (.classMem (.cv n) (syn_cnnc))
      (syn_wo (.classEq (.cv n) (syn_c0c))
        (syn_wrex p (syn_cnnc) (.classEq (.cv n) (syn_cplc (.cv p) (syn_c1c)))))
      p0101 p0102
  have p0104 := @g_ssun2 (syn_csn (.cv x)) (.cv b)
  have p0105 := @g_snid (.cv x) p0098
  have p0106 :=
    @g_sselii (syn_csn (.cv x)) (syn_cun (.cv b) (syn_csn (.cv x))) (.cv x) p0104 p0105
  have p0107 := @g_n0i (syn_cun (.cv b) (syn_csn (.cv x))) (.cv x)
  have p0108 := Nominal.mp p0106 p0107
  have p0109 := (Nominal.classEqRefl (syn_c0c))
  have p0110 :=
    @g_eleq2i (syn_c0c) (syn_csn (syn_c0)) (syn_cun (.cv b) (syn_csn (.cv x))) p0109
  have p0111 := @g_vex b
  have p0112 := @g_snex (.cv x)
  have p0113 := @g_unex (.cv b) (syn_csn (.cv x)) p0111 p0112
  have p0114 := @g_elsnc (syn_cun (.cv b) (syn_csn (.cv x))) (syn_c0) p0113
  have p0115 :=
    @g_bitri (.classMem (syn_cun (.cv b) (syn_csn (.cv x))) (syn_c0c))
      (.classMem (syn_cun (.cv b) (syn_csn (.cv x))) (syn_csn (syn_c0)))
      (.classEq (syn_cun (.cv b) (syn_csn (.cv x))) (syn_c0)) p0110 p0114
  have p0116 :=
    @g_mtbir (.classMem (syn_cun (.cv b) (syn_csn (.cv x))) (syn_c0c))
      (.classEq (syn_cun (.cv b) (syn_csn (.cv x))) (syn_c0)) p0108 p0115
  have p0117 := @g_eleq2 (.cv n) (syn_c0c) (syn_cun (.cv b) (syn_csn (.cv x)))
  have p0118 :=
    @g_biimpcd (.classEq (.cv n) (syn_c0c))
      (.classMem (syn_cun (.cv b) (syn_csn (.cv x))) (.cv n))
      (.classMem (syn_cun (.cv b) (syn_csn (.cv x))) (syn_c0c)) p0117
  have p0119 :=
    @g_mtoi (.classMem (syn_cun (.cv b) (syn_csn (.cv x))) (.cv n))
      (.classEq (.cv n) (syn_c0c))
      (.classMem (syn_cun (.cv b) (syn_csn (.cv x))) (syn_c0c)) p0116 p0118
  have p0120 :=
    @g_adantl (.classMem (syn_cun (.cv b) (syn_csn (.cv x))) (.cv n))
      (.neg (.classEq (.cv n) (syn_c0c)))
      (syn_w3a (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc)))
        (syn_wral q (syn_cnnc)
          (syn_wo (.classEq (syn_cin (.cv m) (.cv q)) (syn_c0)) (.objEq m q)))
        (syn_wa (.objMem b m) (.neg (.objMem x b))))
      p0119
  have p0121 :=
    @g_orel1 (.classEq (.cv n) (syn_c0c))
      (syn_wrex p (syn_cnnc) (.classEq (.cv n) (syn_cplc (.cv p) (syn_c1c))))
  have p0122 :=
    @g_syl
      (syn_wa (syn_w3a (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc)))
          (syn_wral q (syn_cnnc)
            (syn_wo (.classEq (syn_cin (.cv m) (.cv q)) (syn_c0)) (.objEq m q)))
          (syn_wa (.objMem b m) (.neg (.objMem x b))))
        (.classMem (syn_cun (.cv b) (syn_csn (.cv x))) (.cv n)))
      (.neg (.classEq (.cv n) (syn_c0c)))
      (.imp (syn_wo (.classEq (.cv n) (syn_c0c))
          (syn_wrex p (syn_cnnc) (.classEq (.cv n) (syn_cplc (.cv p) (syn_c1c)))))
        (syn_wrex p (syn_cnnc) (.classEq (.cv n) (syn_cplc (.cv p) (syn_c1c)))))
      p0120 p0121
  have p0123 :=
    @g_simpll (.classMem (.cv p) (syn_cnnc))
      (syn_w3a (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc)))
        (syn_wral q (syn_cnnc)
          (syn_wo (.classEq (syn_cin (.cv m) (.cv q)) (syn_c0)) (.objEq m q)))
        (syn_wa (.objMem b m) (.neg (.objMem x b))))
      (.classMem (syn_cun (.cv b) (syn_csn (.cv x))) (syn_cplc (.cv p) (syn_c1c)))
  have p0124 :=
    @g_simpr3r (.objMem b m) (.neg (.objMem x b))
      (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc)))
      (syn_wral q (syn_cnnc)
        (syn_wo (.classEq (syn_cin (.cv m) (.cv q)) (syn_c0)) (.objEq m q)))
      (.classMem (.cv p) (syn_cnnc))
  have p0125 :=
    @g_adantr
      (syn_wa (.classMem (.cv p) (syn_cnnc))
        (syn_w3a (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc)))
          (syn_wral q (syn_cnnc)
            (syn_wo (.classEq (syn_cin (.cv m) (.cv q)) (syn_c0)) (.objEq m q)))
          (syn_wa (.objMem b m) (.neg (.objMem x b)))))
      (.neg (.objMem x b))
      (.classMem (syn_cun (.cv b) (syn_csn (.cv x))) (syn_cplc (.cv p) (syn_c1c))) p0124
  have p0126 :=
    @g_simpr
      (syn_wa (.classMem (.cv p) (syn_cnnc))
        (syn_w3a (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc)))
          (syn_wral q (syn_cnnc)
            (syn_wo (.classEq (syn_cin (.cv m) (.cv q)) (syn_c0)) (.objEq m q)))
          (syn_wa (.objMem b m) (.neg (.objMem x b)))))
      (.classMem (syn_cun (.cv b) (syn_csn (.cv x))) (syn_cplc (.cv p) (syn_c1c)))
  have p0127 := @g_nnsucelr (.cv b) (.cv p) (.cv x) p0111 p0098
  have p0128_e03_recanon :
    Nominal.NPrf
      (.imp (syn_wa (.classMem (.cv p) (syn_cnnc)) (syn_wa (.neg (.objMem x b))
            (.classMem (syn_cun (.cv b) (syn_csn (.cv x))) (syn_cplc (.cv p) (syn_c1c)))))
        (.objMem b p)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wa syn_cnnc syn_cint
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
    @g_syl12anc
      (syn_wa (syn_wa (.classMem (.cv p) (syn_cnnc))
          (syn_w3a (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc)))
            (syn_wral q (syn_cnnc)
              (syn_wo (.classEq (syn_cin (.cv m) (.cv q)) (syn_c0)) (.objEq m q)))
            (syn_wa (.objMem b m) (.neg (.objMem x b)))))
        (.classMem (syn_cun (.cv b) (syn_csn (.cv x))) (syn_cplc (.cv p) (syn_c1c))))
      (.classMem (.cv p) (syn_cnnc)) (.neg (.objMem x b))
      (.classMem (syn_cun (.cv b) (syn_csn (.cv x))) (syn_cplc (.cv p) (syn_c1c)))
      (.objMem b p) p0123 p0125 p0126 p0128_e03_recanon
  have p0129 :=
    @g_ex
      (syn_wa (.classMem (.cv p) (syn_cnnc))
        (syn_w3a (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc)))
          (syn_wral q (syn_cnnc)
            (syn_wo (.classEq (syn_cin (.cv m) (.cv q)) (syn_c0)) (.objEq m q)))
          (syn_wa (.objMem b m) (.neg (.objMem x b)))))
      (.classMem (syn_cun (.cv b) (syn_csn (.cv x))) (syn_cplc (.cv p) (syn_c1c)))
      (.objMem b p) p0128
  have p0130 := @g_ineq2 (.cv q) (.cv p) (.cv m)
  have p0131_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq q p) (.classEq (syn_cin (.cv m) (.cv q)) (syn_cin (.cv m) (.cv p)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_cin syn_ccompl syn_cnin syn_wnan syn_wa
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0130
  have p0131 :=
    @g_eqeq1d (.objEq q p) (syn_cin (.cv m) (.cv q)) (syn_cin (.cv m) (.cv p)) (syn_c0)
      p0131_e00_recanon
  have p0132 := @g_equequ2 q p m
  have p0133 :=
    @g_orbi12d (.objEq q p) (.classEq (syn_cin (.cv m) (.cv q)) (syn_c0))
      (.classEq (syn_cin (.cv m) (.cv p)) (syn_c0)) (.objEq m q) (.objEq m p) p0131 p0132
  have p0134_e00_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv q) (.cv p))
        (syn_wb (syn_wo (.classEq (syn_cin (.cv m) (.cv q)) (syn_c0)) (.objEq m q))
          (syn_wo (.classEq (syn_cin (.cv m) (.cv p)) (syn_c0)) (.objEq m p)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wo syn_cin syn_ccompl syn_cnin syn_wnan syn_wa syn_c0 syn_cdif
          syn_cvv
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
    q ∉ ((syn_wo (.classEq (syn_cin (.cv m) (.cv p)) (syn_c0)) (.objEq m p))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wo,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
      NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_union, Finset.mem_insert,
      Finset.mem_singleton, Finset.notMem_empty, fresh_q_ne_m, fresh_q_ne_p, or_false,
      not_false_eq_true]
  have p0134 :=
    @g_rspccv (syn_wo (.classEq (syn_cin (.cv m) (.cv q)) (syn_c0)) (.objEq m q))
      (syn_wo (.classEq (syn_cin (.cv m) (.cv p)) (syn_c0)) (.objEq m p)) q (.cv p)
      (syn_cnnc) freeVariableCertificate16
      (by
        exact
          (show q ∉ ((syn_cnnc)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc];
              exact (show q ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
      freeVariableCertificate17 p0134_e00_recanon
  have p0135 := @g_elin (.cv b) (.cv m) (.cv p)
  have p0136 := @g_n0i (syn_cin (.cv m) (.cv p)) (.cv b)
  have p0137_e00_recanon :
    Nominal.NPrf
      (syn_wb (.classMem (.cv b) (syn_cin (.cv m) (.cv p)))
        (syn_wa (.objMem b m) (.objMem b p))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cin syn_ccompl syn_cnin syn_wnan syn_wa
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
    @g_sylbir (syn_wa (.objMem b m) (.objMem b p))
      (.classMem (.cv b) (syn_cin (.cv m) (.cv p)))
      (.neg (.classEq (syn_cin (.cv m) (.cv p)) (syn_c0))) p0137_e00_recanon p0136
  have p0138 := @g_pm2_53 (.classEq (syn_cin (.cv m) (.cv p)) (syn_c0)) (.objEq m p)
  have p0139 :=
    @g_syl5 (syn_wa (.objMem b m) (.objMem b p))
      (.neg (.classEq (syn_cin (.cv m) (.cv p)) (syn_c0)))
      (syn_wo (.classEq (syn_cin (.cv m) (.cv p)) (syn_c0)) (.objEq m p)) (.objEq m p)
      p0137 p0138
  have p0140 :=
    @g_exp3a (syn_wo (.classEq (syn_cin (.cv m) (.cv p)) (syn_c0)) (.objEq m p))
      (.objMem b m) (.objMem b p) (.objEq m p) p0139
  have p0141 :=
    @g_syl6
      (syn_wral q (syn_cnnc)
        (syn_wo (.classEq (syn_cin (.cv m) (.cv q)) (syn_c0)) (.objEq m q)))
      (.classMem (.cv p) (syn_cnnc))
      (syn_wo (.classEq (syn_cin (.cv m) (.cv p)) (syn_c0)) (.objEq m p))
      (.imp (.objMem b m) (.imp (.objMem b p) (.objEq m p))) p0134 p0140
  have p0142 :=
    @g_com23
      (syn_wral q (syn_cnnc)
        (syn_wo (.classEq (syn_cin (.cv m) (.cv q)) (syn_c0)) (.objEq m q)))
      (.classMem (.cv p) (syn_cnnc)) (.objMem b m) (.imp (.objMem b p) (.objEq m p)) p0141
  have p0143 :=
    @g_imp
      (syn_wral q (syn_cnnc)
        (syn_wo (.classEq (syn_cin (.cv m) (.cv q)) (syn_c0)) (.objEq m q)))
      (.objMem b m)
      (.imp (.classMem (.cv p) (syn_cnnc)) (.imp (.objMem b p) (.objEq m p))) p0142
  have p0144 :=
    @g_adantrr
      (syn_wral q (syn_cnnc)
        (syn_wo (.classEq (syn_cin (.cv m) (.cv q)) (syn_c0)) (.objEq m q)))
      (.objMem b m)
      (.imp (.classMem (.cv p) (syn_cnnc)) (.imp (.objMem b p) (.objEq m p)))
      (.neg (.objMem x b)) p0143
  have p0145 :=
    @g_n_3adant1
      (syn_wral q (syn_cnnc)
        (syn_wo (.classEq (syn_cin (.cv m) (.cv q)) (syn_c0)) (.objEq m q)))
      (syn_wa (.objMem b m) (.neg (.objMem x b)))
      (.imp (.classMem (.cv p) (syn_cnnc)) (.imp (.objMem b p) (.objEq m p)))
      (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc))) p0144
  have p0146 :=
    @g_impcom
      (syn_w3a (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc)))
        (syn_wral q (syn_cnnc)
          (syn_wo (.classEq (syn_cin (.cv m) (.cv q)) (syn_c0)) (.objEq m q)))
        (syn_wa (.objMem b m) (.neg (.objMem x b))))
      (.classMem (.cv p) (syn_cnnc)) (.imp (.objMem b p) (.objEq m p)) p0145
  have p0147 :=
    @g_syld
      (syn_wa (.classMem (.cv p) (syn_cnnc))
        (syn_w3a (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc)))
          (syn_wral q (syn_cnnc)
            (syn_wo (.classEq (syn_cin (.cv m) (.cv q)) (syn_c0)) (.objEq m q)))
          (syn_wa (.objMem b m) (.neg (.objMem x b)))))
      (.classMem (syn_cun (.cv b) (syn_csn (.cv x))) (syn_cplc (.cv p) (syn_c1c)))
      (.objMem b p) (.objEq m p) p0129 p0146
  have p0148 :=
    @g_ex (.classMem (.cv p) (syn_cnnc))
      (syn_w3a (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc)))
        (syn_wral q (syn_cnnc)
          (syn_wo (.classEq (syn_cin (.cv m) (.cv q)) (syn_c0)) (.objEq m q)))
        (syn_wa (.objMem b m) (.neg (.objMem x b))))
      (.imp (.classMem (syn_cun (.cv b) (syn_csn (.cv x))) (syn_cplc (.cv p) (syn_c1c)))
        (.objEq m p))
      p0147
  have p0149 :=
    @g_com3l (.classMem (.cv p) (syn_cnnc))
      (syn_w3a (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc)))
        (syn_wral q (syn_cnnc)
          (syn_wo (.classEq (syn_cin (.cv m) (.cv q)) (syn_c0)) (.objEq m q)))
        (syn_wa (.objMem b m) (.neg (.objMem x b))))
      (.classMem (syn_cun (.cv b) (syn_csn (.cv x))) (syn_cplc (.cv p) (syn_c1c)))
      (.objEq m p) p0148
  have p0150 :=
    @g_imp
      (syn_w3a (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc)))
        (syn_wral q (syn_cnnc)
          (syn_wo (.classEq (syn_cin (.cv m) (.cv q)) (syn_c0)) (.objEq m q)))
        (syn_wa (.objMem b m) (.neg (.objMem x b))))
      (.classMem (syn_cun (.cv b) (syn_csn (.cv x))) (syn_cplc (.cv p) (syn_c1c)))
      (.imp (.classMem (.cv p) (syn_cnnc)) (.objEq m p)) p0149
  have p0151 := @g_addceq1 (.cv m) (.cv p) (syn_c1c)
  have p0152_e01_recanon :
    Nominal.NPrf
      (.imp (.objEq m p)
        (.classEq (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv p) (syn_c1c)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_cplc syn_wrex syn_wex syn_wa syn_c1c
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0151
  have p0152 :=
    @g_syl6
      (syn_wa (syn_w3a (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc)))
          (syn_wral q (syn_cnnc)
            (syn_wo (.classEq (syn_cin (.cv m) (.cv q)) (syn_c0)) (.objEq m q)))
          (syn_wa (.objMem b m) (.neg (.objMem x b))))
        (.classMem (syn_cun (.cv b) (syn_csn (.cv x))) (syn_cplc (.cv p) (syn_c1c))))
      (.classMem (.cv p) (syn_cnnc)) (.objEq m p)
      (.classEq (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv p) (syn_c1c))) p0150
      p0152_e01_recanon
  have p0153 :=
    @g_eleq2 (.cv n) (syn_cplc (.cv p) (syn_c1c)) (syn_cun (.cv b) (syn_csn (.cv x)))
  have p0154 :=
    @g_anbi2d (.classEq (.cv n) (syn_cplc (.cv p) (syn_c1c)))
      (.classMem (syn_cun (.cv b) (syn_csn (.cv x))) (.cv n))
      (.classMem (syn_cun (.cv b) (syn_csn (.cv x))) (syn_cplc (.cv p) (syn_c1c)))
      (syn_w3a (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc)))
        (syn_wral q (syn_cnnc)
          (syn_wo (.classEq (syn_cin (.cv m) (.cv q)) (syn_c0)) (.objEq m q)))
        (syn_wa (.objMem b m) (.neg (.objMem x b))))
      p0153
  have p0155 := @g_eqeq2 (.cv n) (syn_cplc (.cv p) (syn_c1c)) (syn_cplc (.cv m) (syn_c1c))
  have p0156 :=
    @g_imbi2d (.classEq (.cv n) (syn_cplc (.cv p) (syn_c1c)))
      (.classEq (syn_cplc (.cv m) (syn_c1c)) (.cv n))
      (.classEq (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv p) (syn_c1c)))
      (.classMem (.cv p) (syn_cnnc)) p0155
  have p0157 :=
    @g_imbi12d (.classEq (.cv n) (syn_cplc (.cv p) (syn_c1c)))
      (syn_wa (syn_w3a (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc)))
          (syn_wral q (syn_cnnc)
            (syn_wo (.classEq (syn_cin (.cv m) (.cv q)) (syn_c0)) (.objEq m q)))
          (syn_wa (.objMem b m) (.neg (.objMem x b))))
        (.classMem (syn_cun (.cv b) (syn_csn (.cv x))) (.cv n)))
      (syn_wa (syn_w3a (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc)))
          (syn_wral q (syn_cnnc)
            (syn_wo (.classEq (syn_cin (.cv m) (.cv q)) (syn_c0)) (.objEq m q)))
          (syn_wa (.objMem b m) (.neg (.objMem x b))))
        (.classMem (syn_cun (.cv b) (syn_csn (.cv x))) (syn_cplc (.cv p) (syn_c1c))))
      (.imp (.classMem (.cv p) (syn_cnnc)) (.classEq (syn_cplc (.cv m) (syn_c1c)) (.cv n)))
      (.imp (.classMem (.cv p) (syn_cnnc))
        (.classEq (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv p) (syn_c1c))))
      p0154 p0156
  have p0158 :=
    @g_mpbiri (.classEq (.cv n) (syn_cplc (.cv p) (syn_c1c)))
      (.imp (syn_wa
          (syn_w3a (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc)))
            (syn_wral q (syn_cnnc)
              (syn_wo (.classEq (syn_cin (.cv m) (.cv q)) (syn_c0)) (.objEq m q)))
            (syn_wa (.objMem b m) (.neg (.objMem x b))))
          (.classMem (syn_cun (.cv b) (syn_csn (.cv x))) (.cv n)))
        (.imp (.classMem (.cv p) (syn_cnnc)) (.classEq (syn_cplc (.cv m) (syn_c1c)) (.cv n))))
      (.imp (syn_wa
          (syn_w3a (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc)))
            (syn_wral q (syn_cnnc)
              (syn_wo (.classEq (syn_cin (.cv m) (.cv q)) (syn_c0)) (.objEq m q)))
            (syn_wa (.objMem b m) (.neg (.objMem x b))))
          (.classMem (syn_cun (.cv b) (syn_csn (.cv x))) (syn_cplc (.cv p) (syn_c1c))))
        (.imp (.classMem (.cv p) (syn_cnnc))
          (.classEq (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv p) (syn_c1c)))))
      p0152 p0157
  have p0159 :=
    @g_com3l (.classEq (.cv n) (syn_cplc (.cv p) (syn_c1c)))
      (syn_wa (syn_w3a (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc)))
          (syn_wral q (syn_cnnc)
            (syn_wo (.classEq (syn_cin (.cv m) (.cv q)) (syn_c0)) (.objEq m q)))
          (syn_wa (.objMem b m) (.neg (.objMem x b))))
        (.classMem (syn_cun (.cv b) (syn_csn (.cv x))) (.cv n)))
      (.classMem (.cv p) (syn_cnnc)) (.classEq (syn_cplc (.cv m) (syn_c1c)) (.cv n)) p0158
  have freeVariableCertificate18 :
    p ∉ ((Wff.classEq (syn_cplc (.cv m) (syn_c1c)) (.cv n))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_p_ne_m, fresh_p_ne_n, or_false,
      not_false_eq_true]
  have freeVariableCertificate19 :
    p ∉
      ((syn_wa (syn_w3a (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc)))
            (syn_wral q (syn_cnnc)
              (syn_wo (.classEq (syn_cin (.cv m) (.cv q)) (syn_c0)) (.objEq m q)))
            (syn_wa (.objMem b m) (.neg (.objMem x b))))
          (.classMem (syn_cun (.cv b) (syn_csn (.cv x))) (.cv n)))).fv :=
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
    @g_rexlimdv
      (syn_wa (syn_w3a (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc)))
          (syn_wral q (syn_cnnc)
            (syn_wo (.classEq (syn_cin (.cv m) (.cv q)) (syn_c0)) (.objEq m q)))
          (syn_wa (.objMem b m) (.neg (.objMem x b))))
        (.classMem (syn_cun (.cv b) (syn_csn (.cv x))) (.cv n)))
      (.classEq (.cv n) (syn_cplc (.cv p) (syn_c1c)))
      (.classEq (syn_cplc (.cv m) (syn_c1c)) (.cv n)) p (syn_cnnc)
      freeVariableCertificate18 freeVariableCertificate19 p0159
  have p0161 :=
    @g_syld
      (syn_wa (syn_w3a (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc)))
          (syn_wral q (syn_cnnc)
            (syn_wo (.classEq (syn_cin (.cv m) (.cv q)) (syn_c0)) (.objEq m q)))
          (syn_wa (.objMem b m) (.neg (.objMem x b))))
        (.classMem (syn_cun (.cv b) (syn_csn (.cv x))) (.cv n)))
      (syn_wo (.classEq (.cv n) (syn_c0c))
        (syn_wrex p (syn_cnnc) (.classEq (.cv n) (syn_cplc (.cv p) (syn_c1c)))))
      (syn_wrex p (syn_cnnc) (.classEq (.cv n) (syn_cplc (.cv p) (syn_c1c))))
      (.classEq (syn_cplc (.cv m) (syn_c1c)) (.cv n)) p0122 p0160
  have p0162 :=
    @g_ex
      (syn_w3a (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc)))
        (syn_wral q (syn_cnnc)
          (syn_wo (.classEq (syn_cin (.cv m) (.cv q)) (syn_c0)) (.objEq m q)))
        (syn_wa (.objMem b m) (.neg (.objMem x b))))
      (.classMem (syn_cun (.cv b) (syn_csn (.cv x))) (.cv n))
      (.imp (syn_wo (.classEq (.cv n) (syn_c0c))
          (syn_wrex p (syn_cnnc) (.classEq (.cv n) (syn_cplc (.cv p) (syn_c1c)))))
        (.classEq (syn_cplc (.cv m) (syn_c1c)) (.cv n)))
      p0161
  have p0163 :=
    @g_mpid
      (syn_w3a (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc)))
        (syn_wral q (syn_cnnc)
          (syn_wo (.classEq (syn_cin (.cv m) (.cv q)) (syn_c0)) (.objEq m q)))
        (syn_wa (.objMem b m) (.neg (.objMem x b))))
      (.classMem (syn_cun (.cv b) (syn_csn (.cv x))) (.cv n))
      (syn_wo (.classEq (.cv n) (syn_c0c))
        (syn_wrex p (syn_cnnc) (.classEq (.cv n) (syn_cplc (.cv p) (syn_c1c)))))
      (.classEq (syn_cplc (.cv m) (syn_c1c)) (.cv n)) p0103 p0162
  have p0164 :=
    @g_n_3expa (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc)))
      (syn_wral q (syn_cnnc)
        (syn_wo (.classEq (syn_cin (.cv m) (.cv q)) (syn_c0)) (.objEq m q)))
      (syn_wa (.objMem b m) (.neg (.objMem x b)))
      (.imp (.classMem (syn_cun (.cv b) (syn_csn (.cv x))) (.cv n))
        (.classEq (syn_cplc (.cv m) (syn_c1c)) (.cv n)))
      p0163
  have p0165 := @g_eleq1 (.cv a) (syn_cun (.cv b) (syn_csn (.cv x))) (.cv n)
  have p0166_e00_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv a) (syn_cun (.cv b) (syn_csn (.cv x))))
        (syn_wb (.objMem a n) (.classMem (syn_cun (.cv b) (syn_csn (.cv x))) (.cv n)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_csn syn_wb
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
    @g_imbi1d (.classEq (.cv a) (syn_cun (.cv b) (syn_csn (.cv x)))) (.objMem a n)
      (.classMem (syn_cun (.cv b) (syn_csn (.cv x))) (.cv n))
      (.classEq (syn_cplc (.cv m) (syn_c1c)) (.cv n)) p0166_e00_recanon
  have p0167 :=
    @g_syl5ibrcom
      (syn_wa (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc)))
          (syn_wral q (syn_cnnc)
            (syn_wo (.classEq (syn_cin (.cv m) (.cv q)) (syn_c0)) (.objEq m q))))
        (syn_wa (.objMem b m) (.neg (.objMem x b))))
      (.imp (.objMem a n) (.classEq (syn_cplc (.cv m) (syn_c1c)) (.cv n)))
      (.classEq (.cv a) (syn_cun (.cv b) (syn_csn (.cv x))))
      (.imp (.classMem (syn_cun (.cv b) (syn_csn (.cv x))) (.cv n))
        (.classEq (syn_cplc (.cv m) (syn_c1c)) (.cv n)))
      p0164 p0166
  have p0168 :=
    @g_sylan2b (syn_wa (.objMem b m) (.classMem (.cv x) (syn_ccompl (.cv b))))
      (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc)))
        (syn_wral q (syn_cnnc)
          (syn_wo (.classEq (syn_cin (.cv m) (.cv q)) (syn_c0)) (.objEq m q))))
      (syn_wa (.objMem b m) (.neg (.objMem x b)))
      (.imp (.classEq (.cv a) (syn_cun (.cv b) (syn_csn (.cv x))))
        (.imp (.objMem a n) (.classEq (syn_cplc (.cv m) (syn_c1c)) (.cv n))))
      p0100 p0167
  have p0169_e00_recanon :
    Nominal.NPrf
      (.imp (syn_wa
          (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc)))
            (syn_wral q (syn_cnnc)
              (syn_wo (.classEq (syn_cin (.cv m) (.cv q)) (syn_c0)) (.objEq m q))))
          (syn_wa (.classMem (.cv b) (.cv m)) (.classMem (.cv x) (syn_ccompl (.cv b)))))
        (.imp (.classEq (.cv a) (syn_cun (.cv b) (syn_csn (.cv x))))
          (.imp (.objMem a n) (.classEq (syn_cplc (.cv m) (syn_c1c)) (.cv n))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wa syn_cun syn_cnin syn_wnan syn_ccompl syn_csn syn_cplc syn_wrex
          syn_wex syn_c1c
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
    b ∉ ((Wff.imp (.objMem a n) (.classEq (syn_cplc (.cv m) (syn_c1c)) (.cv n)))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
      NFChoice.Compiler.CoreFVSimp.fv_wff_objMem,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
      Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, fresh_b_ne_a,
      fresh_b_ne_n, fresh_b_ne_m, or_false, not_false_eq_true]
  have freeVariableCertificate22 :
    x ∉ ((Wff.imp (.objMem a n) (.classEq (syn_cplc (.cv m) (syn_c1c)) (.cv n)))).fv := by
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
      ((syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc)))
          (syn_wral q (syn_cnnc)
            (syn_wo (.classEq (syn_cin (.cv m) (.cv q)) (syn_c0)) (.objEq m q))))).fv :=
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
      ((syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc)))
          (syn_wral q (syn_cnnc)
            (syn_wo (.classEq (syn_cin (.cv m) (.cv q)) (syn_c0)) (.objEq m q))))).fv :=
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
    @g_rexlimdvva
      (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc)))
        (syn_wral q (syn_cnnc)
          (syn_wo (.classEq (syn_cin (.cv m) (.cv q)) (syn_c0)) (.objEq m q))))
      (.classEq (.cv a) (syn_cun (.cv b) (syn_csn (.cv x))))
      (.imp (.objMem a n) (.classEq (syn_cplc (.cv m) (syn_c1c)) (.cv n))) b x (.cv m)
      (syn_ccompl (.cv b)) freeVariableCertificate20 freeVariableCertificate21
      freeVariableCertificate22 freeVariableCertificate23 freeVariableCertificate24
      (show b ≠ x from (by exact fresh_b_ne_x)) p0169_e00_recanon
  have p0170 :=
    @g_syl5bi (.classMem (.cv a) (syn_cplc (.cv m) (syn_c1c)))
      (syn_wrex b (.cv m) (syn_wrex x (syn_ccompl (.cv b))
          (.classEq (.cv a) (syn_cun (.cv b) (syn_csn (.cv x))))))
      (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc)))
        (syn_wral q (syn_cnnc)
          (syn_wo (.classEq (syn_cin (.cv m) (.cv q)) (syn_c0)) (.objEq m q))))
      (.imp (.objMem a n) (.classEq (syn_cplc (.cv m) (syn_c1c)) (.cv n))) p0097 p0169
  have p0171 :=
    @g_imp3a
      (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc)))
        (syn_wral q (syn_cnnc)
          (syn_wo (.classEq (syn_cin (.cv m) (.cv q)) (syn_c0)) (.objEq m q))))
      (.classMem (.cv a) (syn_cplc (.cv m) (syn_c1c))) (.objMem a n)
      (.classEq (syn_cplc (.cv m) (syn_c1c)) (.cv n)) p0170
  have p0172_e00_recanon :
    Nominal.NPrf
      (syn_wb (.classMem (.cv a) (syn_cin (syn_cplc (.cv m) (syn_c1c)) (.cv n)))
        (syn_wa (.classMem (.cv a) (syn_cplc (.cv m) (syn_c1c))) (.objMem a n))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cin syn_ccompl syn_cnin syn_wnan syn_wa syn_cplc syn_wrex
          syn_wex syn_c1c
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
    @g_syl5bi (.classMem (.cv a) (syn_cin (syn_cplc (.cv m) (syn_c1c)) (.cv n)))
      (syn_wa (.classMem (.cv a) (syn_cplc (.cv m) (syn_c1c))) (.objMem a n))
      (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc)))
        (syn_wral q (syn_cnnc)
          (syn_wo (.classEq (syn_cin (.cv m) (.cv q)) (syn_c0)) (.objEq m q))))
      (.classEq (syn_cplc (.cv m) (syn_c1c)) (.cv n)) p0172_e00_recanon p0171
  have freeVariableCertificate25 :
    a ∉ ((Wff.classEq (syn_cplc (.cv m) (syn_c1c)) (.cv n))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_a_ne_m, fresh_a_ne_n, or_false,
      not_false_eq_true]
  have freeVariableCertificate26 :
    a ∉
      ((syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc)))
          (syn_wral q (syn_cnnc)
            (syn_wo (.classEq (syn_cin (.cv m) (.cv q)) (syn_c0)) (.objEq m q))))).fv :=
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
    @g_exlimdv
      (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc)))
        (syn_wral q (syn_cnnc)
          (syn_wo (.classEq (syn_cin (.cv m) (.cv q)) (syn_c0)) (.objEq m q))))
      (.classMem (.cv a) (syn_cin (syn_cplc (.cv m) (syn_c1c)) (.cv n)))
      (.classEq (syn_cplc (.cv m) (syn_c1c)) (.cv n)) a freeVariableCertificate25
      freeVariableCertificate26 p0172
  have p0174 :=
    @g_syl5bi (.neg (.classEq (syn_cin (syn_cplc (.cv m) (syn_c1c)) (.cv n)) (syn_c0)))
      (syn_wex a (.classMem (.cv a) (syn_cin (syn_cplc (.cv m) (syn_c1c)) (.cv n))))
      (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc)))
        (syn_wral q (syn_cnnc)
          (syn_wo (.classEq (syn_cin (.cv m) (.cv q)) (syn_c0)) (.objEq m q))))
      (.classEq (syn_cplc (.cv m) (syn_c1c)) (.cv n)) p0095 p0173
  have p0175 :=
    @g_orrd
      (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc)))
        (syn_wral q (syn_cnnc)
          (syn_wo (.classEq (syn_cin (.cv m) (.cv q)) (syn_c0)) (.objEq m q))))
      (.classEq (syn_cin (syn_cplc (.cv m) (syn_c1c)) (.cv n)) (syn_c0))
      (.classEq (syn_cplc (.cv m) (syn_c1c)) (.cv n)) p0174
  have p0176 :=
    @g_exp31 (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc))
      (syn_wral q (syn_cnnc)
        (syn_wo (.classEq (syn_cin (.cv m) (.cv q)) (syn_c0)) (.objEq m q)))
      (syn_wo (.classEq (syn_cin (syn_cplc (.cv m) (syn_c1c)) (.cv n)) (syn_c0))
        (.classEq (syn_cplc (.cv m) (syn_c1c)) (.cv n)))
      p0175
  have p0177 :=
    @g_com23 (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc))
      (syn_wral q (syn_cnnc)
        (syn_wo (.classEq (syn_cin (.cv m) (.cv q)) (syn_c0)) (.objEq m q)))
      (syn_wo (.classEq (syn_cin (syn_cplc (.cv m) (syn_c1c)) (.cv n)) (syn_c0))
        (.classEq (syn_cplc (.cv m) (syn_c1c)) (.cv n)))
      p0176
  have freeVariableCertificate27 : n ∉ ((Wff.classMem (.cv m) (syn_cnnc))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_n_ne_m, or_false,
      not_false_eq_true]
  have freeVariableCertificate28 :
    n ∉
      ((syn_wral q (syn_cnnc)
          (syn_wo (.classEq (syn_cin (.cv m) (.cv q)) (syn_c0)) (.objEq m q)))).fv :=
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
    @g_ralrimdv (.classMem (.cv m) (syn_cnnc))
      (syn_wral q (syn_cnnc)
        (syn_wo (.classEq (syn_cin (.cv m) (.cv q)) (syn_c0)) (.objEq m q)))
      (syn_wo (.classEq (syn_cin (syn_cplc (.cv m) (syn_c1c)) (.cv n)) (syn_c0))
        (.classEq (syn_cplc (.cv m) (syn_c1c)) (.cv n)))
      n (syn_cnnc) freeVariableCertificate27 freeVariableCertificate28 p0177
  have freeVariableCertificate29 :
    p ∉
      ((syn_wral q (syn_cnnc)
          (syn_wo (.classEq (syn_cin (.cv m) (.cv q)) (syn_c0)) (.objEq m q)))).fv :=
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
      ((syn_wral n (syn_cnnc)
          (syn_wo (.classEq (syn_cin (.cv p) (.cv n)) (syn_c0)) (.objEq p n)))).fv :=
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
      ((syn_wral n (syn_cnnc) (syn_wo (.neg (.classMem (syn_c0) (.cv n)))
            (.classEq (.cv n) (syn_c0c))))).fv :=
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
      ((syn_wral n (syn_cnnc)
          (syn_wo (.classEq (syn_cin M (.cv n)) (syn_c0)) (.classEq M (.cv n))))).fv :=
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
      ((syn_wral n (syn_cnnc)
          (syn_wo (.classEq (syn_cin (syn_cplc (.cv m) (syn_c1c)) (.cv n)) (syn_c0))
            (.classEq (syn_cplc (.cv m) (syn_c1c)) (.cv n))))).fv :=
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
    @g_finds
      (syn_wral n (syn_cnnc)
        (syn_wo (.classEq (syn_cin (.cv p) (.cv n)) (syn_c0)) (.objEq p n)))
      (syn_wral n (syn_cnnc)
        (syn_wo (.neg (.classMem (syn_c0) (.cv n))) (.classEq (.cv n) (syn_c0c))))
      (syn_wral q (syn_cnnc)
        (syn_wo (.classEq (syn_cin (.cv m) (.cv q)) (syn_c0)) (.objEq m q)))
      (syn_wral n (syn_cnnc)
        (syn_wo (.classEq (syn_cin (syn_cplc (.cv m) (syn_c1c)) (.cv n)) (syn_c0))
          (.classEq (syn_cplc (.cv m) (syn_c1c)) (.cv n))))
      (syn_wral n (syn_cnnc)
        (syn_wo (.classEq (syn_cin M (.cv n)) (syn_c0)) (.classEq M (.cv n))))
      p m M (by exact (show p ∉ (M).fv from (by exact fresh_p_not_M)))
      freeVariableCertificate29 freeVariableCertificate30 freeVariableCertificate31
      freeVariableCertificate32 freeVariableCertificate33
      (show p ≠ m from (by exact fresh_p_ne_m)) p0044 p0059 p0070 p0075 p0080 p0094 p0178
  have p0180 := @g_ineq2 (.cv n) N M
  have p0181 :=
    @g_eqeq1d (.classEq (.cv n) N) (syn_cin M (.cv n)) (syn_cin M N) (syn_c0) p0180
  have p0182 := @g_eqeq2 (.cv n) N M
  have p0183 :=
    @g_orbi12d (.classEq (.cv n) N) (.classEq (syn_cin M (.cv n)) (syn_c0))
      (.classEq (syn_cin M N) (syn_c0)) (.classEq M (.cv n)) (.classEq M N) p0181 p0182
  have freeVariableCertificate34 :
    n ∉ ((syn_wo (.classEq (syn_cin M N) (syn_c0)) (.classEq M N))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wo,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union,
      Finset.notMem_empty, fresh_n_not_M, fresh_n_not_N, or_false, not_false_eq_true]
  have p0184 :=
    @g_rspccv (syn_wo (.classEq (syn_cin M (.cv n)) (syn_c0)) (.classEq M (.cv n)))
      (syn_wo (.classEq (syn_cin M N) (syn_c0)) (.classEq M N)) n N (syn_cnnc)
      (by exact (show n ∉ (N).fv from (by exact fresh_n_not_N)))
      (by
        exact
          (show n ∉ ((syn_cnnc)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc];
              exact (show n ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
      freeVariableCertificate34 p0183
  have p0185 :=
    @g_syl (.classMem M (syn_cnnc))
      (syn_wral n (syn_cnnc)
        (syn_wo (.classEq (syn_cin M (.cv n)) (syn_c0)) (.classEq M (.cv n))))
      (.imp (.classMem N (syn_cnnc)) (syn_wo (.classEq (syn_cin M N) (syn_c0)) (.classEq M N)))
      p0179 p0184
  have p0186 :=
    @g_imp (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))
      (syn_wo (.classEq (syn_cin M N) (syn_c0)) (.classEq M N)) p0185
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

@[expose]
noncomputable def g_nnceleq (A : Class) (M : Class) (N : Class) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)))
          (syn_wa (.classMem A M) (.classMem A N))) (.classEq M N)) :=
  by
  have p0000 := @g_elin A M N
  have p0001 := @g_n0i (syn_cin M N) A
  have p0002 :=
    @g_sylbir (syn_wa (.classMem A M) (.classMem A N)) (.classMem A (syn_cin M N))
      (.neg (.classEq (syn_cin M N) (syn_c0))) p0000 p0001
  have p0003 :=
    @g_adantl (syn_wa (.classMem A M) (.classMem A N))
      (.neg (.classEq (syn_cin M N) (syn_c0)))
      (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))) p0002
  have p0004 := @g_nndisjeq M N
  have p0005 :=
    @g_adantr (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)))
      (syn_wo (.classEq (syn_cin M N) (syn_c0)) (.classEq M N))
      (syn_wa (.classMem A M) (.classMem A N)) p0004
  have p0006 := @g_orel1 (.classEq (syn_cin M N) (syn_c0)) (.classEq M N)
  have p0007 :=
    @g_sylc
      (syn_wa (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)))
        (syn_wa (.classMem A M) (.classMem A N)))
      (.neg (.classEq (syn_cin M N) (syn_c0)))
      (syn_wo (.classEq (syn_cin M N) (syn_c0)) (.classEq M N)) (.classEq M N) p0003 p0005
      p0006
  exact p0007

@[expose]
noncomputable def g_opklefing (x : Var) (A : Class) (B : Class) (V : Class) (W : Class)
    (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem A V) (.classMem B W))
        (syn_wb (.classMem (syn_copk A B) (syn_clefin))
          (syn_wrex x (syn_cnnc) (.classEq B (syn_cplc A (.cv x)))))) :=
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
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_lefin w y z x
      (show x ≠ w from (by exact fresh_x_ne_w)) (show x ≠ y from (by exact fresh_x_ne_y))
      (show x ≠ z from (by exact fresh_x_ne_z)) (show w ≠ y from (by exact fresh_w_ne_y))
      (show w ≠ z from (by exact fresh_w_ne_z)) (show y ≠ z from (by exact fresh_y_ne_z))
  have p0001 := @g_addceq1 (.cv y) A (.cv x)
  have p0002 :=
    @g_eqeq2d (.classEq (.cv y) A) (syn_cplc (.cv y) (.cv x)) (syn_cplc A (.cv x)) (.cv z)
      p0001
  have freeVariableCertificate0 : x ∉ ((Wff.classEq (.cv y) A)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      fresh_x_ne_y, dv_A_x, or_false, not_false_eq_true]
  have p0003 :=
    @g_rexbidv (.classEq (.cv y) A) (.classEq (.cv z) (syn_cplc (.cv y) (.cv x)))
      (.classEq (.cv z) (syn_cplc A (.cv x))) x (syn_cnnc) freeVariableCertificate0 p0002
  have p0004 := @g_eqeq1 (.cv z) B (syn_cplc A (.cv x))
  have freeVariableCertificate1 : x ∉ ((Wff.classEq (.cv z) B)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      fresh_x_ne_z, dv_B_x, or_false, not_false_eq_true]
  have p0005 :=
    @g_rexbidv (.classEq (.cv z) B) (.classEq (.cv z) (syn_cplc A (.cv x)))
      (.classEq B (syn_cplc A (.cv x))) x (syn_cnnc) freeVariableCertificate1 p0004
  have freeVariableCertificate2 :
    z ∉ ((syn_wrex x (syn_cnnc) (.classEq B (syn_cplc A (.cv x))))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
      Finset.mem_singleton, Finset.notMem_empty, fresh_z_not_B, fresh_z_not_A,
      fresh_z_ne_x, or_false, and_false, not_false_eq_true]
  have freeVariableCertificate3 :
    w ∉ ((syn_wrex x (syn_cnnc) (.classEq (.cv z) (syn_cplc (.cv y) (.cv x))))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, Finset.mem_union,
      Finset.mem_erase, Finset.mem_singleton, Finset.notMem_empty, fresh_w_ne_z,
      fresh_w_ne_y, fresh_w_ne_x, or_false, and_false, not_false_eq_true]
  have freeVariableCertificate4 :
    y ∉ ((syn_wrex x (syn_cnnc) (.classEq (.cv z) (syn_cplc A (.cv x))))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, Finset.mem_union,
      Finset.mem_erase, Finset.mem_singleton, Finset.notMem_empty, fresh_y_ne_z,
      fresh_y_not_A, fresh_y_ne_x, or_false, and_false, not_false_eq_true]
  have p0006 :=
    @g_opkelopkabg (syn_wrex x (syn_cnnc) (.classEq (.cv z) (syn_cplc (.cv y) (.cv x))))
      (syn_wrex x (syn_cnnc) (.classEq (.cv z) (syn_cplc A (.cv x))))
      (syn_wrex x (syn_cnnc) (.classEq B (syn_cplc A (.cv x)))) w y z (syn_clefin) A B V W
      (by
        exact
          (show y ∉ ((syn_clefin)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin];
              exact (show y ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
      (by
        exact
          (show z ∉ ((syn_clefin)).fv from
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

@[expose]
noncomputable def g_opkltfing (x : Var) (A : Class) (B : Class) (V : Class) (W : Class)
    (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem A V) (.classMem B W))
        (syn_wb (.classMem (syn_copk A B) (syn_cltfin)) (syn_wa (syn_wne A (syn_c0))
            (syn_wrex x (syn_cnnc) (.classEq B (syn_cplc (syn_cplc A (.cv x)) (syn_c1c))))))) :=
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
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_ltfin y z w x
      (show z ≠ w from (by exact fresh_z_ne_w)) (show z ≠ x from (by exact fresh_z_ne_x))
      (show z ≠ y from (by exact fresh_z_ne_y)) (show w ≠ x from (by exact fresh_w_ne_x))
      (show w ≠ y from (by exact fresh_w_ne_y)) (show x ≠ y from (by exact fresh_x_ne_y))
  have p0001 := @g_neeq1 (.cv z) A (syn_c0)
  have p0002 := @g_addceq1 (.cv z) A (.cv x)
  have p0003 :=
    @g_addceq1d (.classEq (.cv z) A) (syn_cplc (.cv z) (.cv x)) (syn_cplc A (.cv x))
      (syn_c1c) p0002
  have p0004 :=
    @g_eqeq2d (.classEq (.cv z) A) (syn_cplc (syn_cplc (.cv z) (.cv x)) (syn_c1c))
      (syn_cplc (syn_cplc A (.cv x)) (syn_c1c)) (.cv w) p0003
  have freeVariableCertificate0 : x ∉ ((Wff.classEq (.cv z) A)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      fresh_x_ne_z, dv_A_x, or_false, not_false_eq_true]
  have p0005 :=
    @g_rexbidv (.classEq (.cv z) A)
      (.classEq (.cv w) (syn_cplc (syn_cplc (.cv z) (.cv x)) (syn_c1c)))
      (.classEq (.cv w) (syn_cplc (syn_cplc A (.cv x)) (syn_c1c))) x (syn_cnnc)
      freeVariableCertificate0 p0004
  have p0006 :=
    @g_anbi12d (.classEq (.cv z) A) (syn_wne (.cv z) (syn_c0)) (syn_wne A (syn_c0))
      (syn_wrex x (syn_cnnc) (.classEq (.cv w) (syn_cplc (syn_cplc (.cv z) (.cv x)) (syn_c1c))))
      (syn_wrex x (syn_cnnc) (.classEq (.cv w) (syn_cplc (syn_cplc A (.cv x)) (syn_c1c))))
      p0001 p0005
  have p0007 := @g_eqeq1 (.cv w) B (syn_cplc (syn_cplc A (.cv x)) (syn_c1c))
  have freeVariableCertificate1 : x ∉ ((Wff.classEq (.cv w) B)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      fresh_x_ne_w, dv_B_x, or_false, not_false_eq_true]
  have p0008 :=
    @g_rexbidv (.classEq (.cv w) B)
      (.classEq (.cv w) (syn_cplc (syn_cplc A (.cv x)) (syn_c1c)))
      (.classEq B (syn_cplc (syn_cplc A (.cv x)) (syn_c1c))) x (syn_cnnc)
      freeVariableCertificate1 p0007
  have p0009 :=
    @g_anbi2d (.classEq (.cv w) B)
      (syn_wrex x (syn_cnnc) (.classEq (.cv w) (syn_cplc (syn_cplc A (.cv x)) (syn_c1c))))
      (syn_wrex x (syn_cnnc) (.classEq B (syn_cplc (syn_cplc A (.cv x)) (syn_c1c))))
      (syn_wne A (syn_c0)) p0008
  have freeVariableCertificate2 :
    w ∉
      ((syn_wa (syn_wne A (syn_c0)) (syn_wrex x (syn_cnnc)
            (.classEq B (syn_cplc (syn_cplc A (.cv x)) (syn_c1c)))))).fv :=
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
      ((syn_wa (syn_wne (.cv z) (syn_c0)) (syn_wrex x (syn_cnnc)
            (.classEq (.cv w) (syn_cplc (syn_cplc (.cv z) (.cv x)) (syn_c1c)))))).fv :=
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
      ((syn_wa (syn_wne A (syn_c0)) (syn_wrex x (syn_cnnc)
            (.classEq (.cv w) (syn_cplc (syn_cplc A (.cv x)) (syn_c1c)))))).fv :=
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
    @g_opkelopkabg
      (syn_wa (syn_wne (.cv z) (syn_c0)) (syn_wrex x (syn_cnnc)
          (.classEq (.cv w) (syn_cplc (syn_cplc (.cv z) (.cv x)) (syn_c1c)))))
      (syn_wa (syn_wne A (syn_c0)) (syn_wrex x (syn_cnnc)
          (.classEq (.cv w) (syn_cplc (syn_cplc A (.cv x)) (syn_c1c)))))
      (syn_wa (syn_wne A (syn_c0))
        (syn_wrex x (syn_cnnc) (.classEq B (syn_cplc (syn_cplc A (.cv x)) (syn_c1c)))))
      y z w (syn_cltfin) A B V W
      (by
        exact
          (show z ∉ ((syn_cltfin)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cltfin];
              exact (show z ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
      (by
        exact
          (show w ∉ ((syn_cltfin)).fv from
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

@[expose]
noncomputable def g_lefinaddc (A : Class) (N : Class) (V : Class) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem A V) (.classMem N (syn_cnnc)))
        (.classMem (syn_copk A (syn_cplc A N)) (syn_clefin))) :=
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
  have p0000 := @g_eqid (syn_cplc A N)
  have p0001 := @g_addceq2 (.cv n) N A
  have p0002 :=
    @g_eqeq2d (.classEq (.cv n) N) (syn_cplc A (.cv n)) (syn_cplc A N) (syn_cplc A N)
      p0001
  have freeVariableCertificate0 : n ∉ ((Wff.classEq (syn_cplc A N) (syn_cplc A N))).fv :=
    by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, Finset.mem_union,
      fresh_n_not_A, fresh_n_not_N, or_false, not_false_eq_true]
  have p0003 :=
    @g_rspcev (.classEq (syn_cplc A N) (syn_cplc A (.cv n)))
      (.classEq (syn_cplc A N) (syn_cplc A N)) n N (syn_cnnc)
      (by exact (show n ∉ (N).fv from (by exact fresh_n_not_N)))
      (by
        exact
          (show n ∉ ((syn_cnnc)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc];
              exact (show n ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
      freeVariableCertificate0 p0002
  have p0004 :=
    @g_mpan2 (.classMem N (syn_cnnc)) (.classEq (syn_cplc A N) (syn_cplc A N))
      (syn_wrex n (syn_cnnc) (.classEq (syn_cplc A N) (syn_cplc A (.cv n)))) p0000 p0003
  have p0005 :=
    @g_adantl (.classMem N (syn_cnnc))
      (syn_wrex n (syn_cnnc) (.classEq (syn_cplc A N) (syn_cplc A (.cv n))))
      (.classMem A V) p0004
  have p0006 := @g_addcexg A N V (syn_cnnc)
  have freeVariableCertificate1 : n ∉ ((syn_cplc A N)).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, Finset.mem_union,
      fresh_n_not_A, fresh_n_not_N, or_false, not_false_eq_true]
  have p0007 :=
    @g_opklefing n A (syn_cplc A N) V (syn_cvv)
      (by exact (show n ∉ (A).fv from (by exact fresh_n_not_A))) freeVariableCertificate1
  have p0008 :=
    @g_syldan (.classMem A V) (.classMem N (syn_cnnc))
      (.classMem (syn_cplc A N) (syn_cvv))
      (syn_wb (.classMem (syn_copk A (syn_cplc A N)) (syn_clefin))
        (syn_wrex n (syn_cnnc) (.classEq (syn_cplc A N) (syn_cplc A (.cv n)))))
      p0006 p0007
  have p0009 :=
    @g_mpbird (syn_wa (.classMem A V) (.classMem N (syn_cnnc)))
      (.classMem (syn_copk A (syn_cplc A N)) (syn_clefin))
      (syn_wrex n (syn_cnnc) (.classEq (syn_cplc A N) (syn_cplc A (.cv n)))) p0005 p0008
  exact p0009

@[expose]
noncomputable def g_prepeano4 (M : Class) (N : Class) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)))
          (syn_wa (.classEq (syn_cplc M (syn_c1c)) (syn_cplc N (syn_c1c)))
            (syn_wne (syn_cplc M (syn_c1c)) (syn_c0)))) (.classEq M N)) :=
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
  have freeVariableCertificate0 : a ∉ ((syn_cplc M (syn_c1c))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
      Finset.notMem_empty, fresh_a_not_M, or_false, not_false_eq_true]
  have p0000 := @g_n0 a (syn_cplc M (syn_c1c)) freeVariableCertificate0
  have freeVariableCertificate1 : b ∉ ((Class.cv a)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_b_ne_a, not_false_eq_true]
  have freeVariableCertificate2 : x ∉ ((Class.cv a)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_x_ne_a, not_false_eq_true]
  have p0001 :=
    @g_elsuc x (.cv a) M b freeVariableCertificate1 freeVariableCertificate2
      (by exact (show b ∉ (M).fv from (by exact fresh_b_not_M)))
      (show b ≠ x from (by exact fresh_b_ne_x))
  have p0002 :=
    @g_simplll (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))
      (.classEq (syn_cplc M (syn_c1c)) (syn_cplc N (syn_c1c)))
      (syn_wa (.classMem (.cv b) M) (.classMem (.cv x) (syn_ccompl (.cv b))))
  have p0003 :=
    @g_simpllr (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))
      (.classEq (syn_cplc M (syn_c1c)) (syn_cplc N (syn_c1c)))
      (syn_wa (.classMem (.cv b) M) (.classMem (.cv x) (syn_ccompl (.cv b))))
  have p0004 :=
    @g_simprl
      (syn_wa (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)))
        (.classEq (syn_cplc M (syn_c1c)) (syn_cplc N (syn_c1c))))
      (.classMem (.cv b) M) (.classMem (.cv x) (syn_ccompl (.cv b)))
  have p0005 :=
    @g_simprr
      (syn_wa (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)))
        (.classEq (syn_cplc M (syn_c1c)) (syn_cplc N (syn_c1c))))
      (.classMem (.cv b) M) (.classMem (.cv x) (syn_ccompl (.cv b)))
  have p0006 := @g_vex x
  have p0007 := @g_elcompl (.cv x) (.cv b) p0006
  have p0008_e01_recanon :
    Nominal.NPrf (syn_wb (.classMem (.cv x) (syn_ccompl (.cv b))) (.neg (.objMem x b))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_ccompl syn_cnin syn_wnan syn_wa
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
    @g_sylib
      (syn_wa (syn_wa (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)))
          (.classEq (syn_cplc M (syn_c1c)) (syn_cplc N (syn_c1c))))
        (syn_wa (.classMem (.cv b) M) (.classMem (.cv x) (syn_ccompl (.cv b)))))
      (.classMem (.cv x) (syn_ccompl (.cv b))) (.neg (.objMem x b)) p0005
      p0008_e01_recanon
  have p0009 := @g_elsuci (.cv b) M (.cv x) p0006
  have p0010_e00_recanon :
    Nominal.NPrf (syn_wb (.classMem (.cv x) (syn_ccompl (.cv b))) (.neg (.objMem x b))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_ccompl syn_cnin syn_wnan syn_wa
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
      (.imp (syn_wa (.classMem (.cv b) M) (.neg (.objMem x b)))
        (.classMem (syn_cun (.cv b) (syn_csn (.cv x))) (syn_cplc M (syn_c1c)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wa syn_cun syn_cnin syn_wnan syn_ccompl syn_csn syn_cplc syn_wrex
          syn_wex syn_c1c
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
    @g_sylan2b (.classMem (.cv x) (syn_ccompl (.cv b))) (.classMem (.cv b) M)
      (.neg (.objMem x b))
      (.classMem (syn_cun (.cv b) (syn_csn (.cv x))) (syn_cplc M (syn_c1c)))
      p0010_e00_recanon p0010_e01_recanon
  have p0011 :=
    @g_adantl (syn_wa (.classMem (.cv b) M) (.classMem (.cv x) (syn_ccompl (.cv b))))
      (.classMem (syn_cun (.cv b) (syn_csn (.cv x))) (syn_cplc M (syn_c1c)))
      (syn_wa (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)))
        (.classEq (syn_cplc M (syn_c1c)) (syn_cplc N (syn_c1c))))
      p0010
  have p0012 :=
    @g_simplr (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)))
      (.classEq (syn_cplc M (syn_c1c)) (syn_cplc N (syn_c1c)))
      (syn_wa (.classMem (.cv b) M) (.classMem (.cv x) (syn_ccompl (.cv b))))
  have p0013 :=
    @g_eleqtrd
      (syn_wa (syn_wa (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)))
          (.classEq (syn_cplc M (syn_c1c)) (syn_cplc N (syn_c1c))))
        (syn_wa (.classMem (.cv b) M) (.classMem (.cv x) (syn_ccompl (.cv b)))))
      (syn_cun (.cv b) (syn_csn (.cv x))) (syn_cplc M (syn_c1c)) (syn_cplc N (syn_c1c))
      p0011 p0012
  have p0014 := @g_vex b
  have p0015 := @g_nnsucelr (.cv b) N (.cv x) p0014 p0006
  have p0016_e03_recanon :
    Nominal.NPrf
      (.imp (syn_wa (.classMem N (syn_cnnc)) (syn_wa (.neg (.objMem x b))
            (.classMem (syn_cun (.cv b) (syn_csn (.cv x))) (syn_cplc N (syn_c1c)))))
        (.classMem (.cv b) N)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wa syn_cnnc syn_cint
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
    @g_syl12anc
      (syn_wa (syn_wa (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)))
          (.classEq (syn_cplc M (syn_c1c)) (syn_cplc N (syn_c1c))))
        (syn_wa (.classMem (.cv b) M) (.classMem (.cv x) (syn_ccompl (.cv b)))))
      (.classMem N (syn_cnnc)) (.neg (.objMem x b))
      (.classMem (syn_cun (.cv b) (syn_csn (.cv x))) (syn_cplc N (syn_c1c)))
      (.classMem (.cv b) N) p0003 p0008 p0013 p0016_e03_recanon
  have p0017 := @g_nnceleq (.cv b) M N
  have p0018 :=
    @g_syl22anc
      (syn_wa (syn_wa (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)))
          (.classEq (syn_cplc M (syn_c1c)) (syn_cplc N (syn_c1c))))
        (syn_wa (.classMem (.cv b) M) (.classMem (.cv x) (syn_ccompl (.cv b)))))
      (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)) (.classMem (.cv b) M)
      (.classMem (.cv b) N) (.classEq M N) p0002 p0003 p0004 p0016 p0017
  have p0019 :=
    @g_a1d
      (syn_wa (syn_wa (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)))
          (.classEq (syn_cplc M (syn_c1c)) (syn_cplc N (syn_c1c))))
        (syn_wa (.classMem (.cv b) M) (.classMem (.cv x) (syn_ccompl (.cv b)))))
      (.classEq M N) (.classEq (.cv a) (syn_cun (.cv b) (syn_csn (.cv x)))) p0018
  have freeVariableCertificate3 : b ∉ ((Wff.classEq M N)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union,
      fresh_b_not_M, fresh_b_not_N, or_false, not_false_eq_true]
  have freeVariableCertificate4 : x ∉ ((Wff.classEq M N)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union,
      fresh_x_not_M, fresh_x_not_N, or_false, not_false_eq_true]
  have freeVariableCertificate5 :
    b ∉
      ((syn_wa (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)))
          (.classEq (syn_cplc M (syn_c1c)) (syn_cplc N (syn_c1c))))).fv :=
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
      ((syn_wa (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)))
          (.classEq (syn_cplc M (syn_c1c)) (syn_cplc N (syn_c1c))))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
      Finset.notMem_empty, fresh_x_not_M, fresh_x_not_N, or_false, not_false_eq_true]
  have p0020 :=
    @g_rexlimdvva
      (syn_wa (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)))
        (.classEq (syn_cplc M (syn_c1c)) (syn_cplc N (syn_c1c))))
      (.classEq (.cv a) (syn_cun (.cv b) (syn_csn (.cv x)))) (.classEq M N) b x M
      (syn_ccompl (.cv b)) (by exact (show x ∉ (M).fv from (by exact fresh_x_not_M)))
      freeVariableCertificate3 freeVariableCertificate4 freeVariableCertificate5
      freeVariableCertificate6 (show b ≠ x from (by exact fresh_b_ne_x)) p0019
  have p0021 :=
    @g_syl5bi (.classMem (.cv a) (syn_cplc M (syn_c1c)))
      (syn_wrex b M (syn_wrex x (syn_ccompl (.cv b))
          (.classEq (.cv a) (syn_cun (.cv b) (syn_csn (.cv x))))))
      (syn_wa (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)))
        (.classEq (syn_cplc M (syn_c1c)) (syn_cplc N (syn_c1c))))
      (.classEq M N) p0001 p0020
  have freeVariableCertificate7 : a ∉ ((Wff.classEq M N)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union,
      fresh_a_not_M, fresh_a_not_N, or_false, not_false_eq_true]
  have freeVariableCertificate8 :
    a ∉
      ((syn_wa (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)))
          (.classEq (syn_cplc M (syn_c1c)) (syn_cplc N (syn_c1c))))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
      Finset.notMem_empty, fresh_a_not_M, fresh_a_not_N, or_false, not_false_eq_true]
  have p0022 :=
    @g_exlimdv
      (syn_wa (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)))
        (.classEq (syn_cplc M (syn_c1c)) (syn_cplc N (syn_c1c))))
      (.classMem (.cv a) (syn_cplc M (syn_c1c))) (.classEq M N) a freeVariableCertificate7
      freeVariableCertificate8 p0021
  have p0023 :=
    @g_syl5bi (syn_wne (syn_cplc M (syn_c1c)) (syn_c0))
      (syn_wex a (.classMem (.cv a) (syn_cplc M (syn_c1c))))
      (syn_wa (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)))
        (.classEq (syn_cplc M (syn_c1c)) (syn_cplc N (syn_c1c))))
      (.classEq M N) p0000 p0022
  have p0024 :=
    @g_impr (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)))
      (.classEq (syn_cplc M (syn_c1c)) (syn_cplc N (syn_c1c)))
      (syn_wne (syn_cplc M (syn_c1c)) (syn_c0)) (.classEq M N) p0023
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

@[expose]
noncomputable def g_addcnul1 (A : Class) :
    Nominal.NPrf (.classEq (syn_cplc A (syn_c0)) (syn_c0)) :=
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
  have freeVariableCertificate0 : a ∉ ((syn_cplc A (syn_c0))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union,
      Finset.notMem_empty, fresh_a_not_A, or_false, not_false_eq_true]
  have p0000 := @g_eq0 a (syn_cplc A (syn_c0)) freeVariableCertificate0
  have p0001 :=
    @g_rex0
      (syn_wa (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0))
        (.classEq (.cv a) (syn_cun (.cv b) (.cv c))))
      c
  have p0002 :=
    @g_a1i
      (.neg (syn_wrex c (syn_c0) (syn_wa (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0))
            (.classEq (.cv a) (syn_cun (.cv b) (.cv c))))))
      (.classMem (.cv b) A) p0001
  have p0003 :=
    @g_nrex
      (syn_wrex c (syn_c0) (syn_wa (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0))
          (.classEq (.cv a) (syn_cun (.cv b) (.cv c)))))
      b A p0002
  have freeVariableCertificate1 : b ∉ ((Class.cv a)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_b_ne_a, not_false_eq_true]
  have freeVariableCertificate2 : c ∉ ((Class.cv a)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_c_ne_a, not_false_eq_true]
  have p0004 :=
    @g_eladdc (.cv a) A (syn_c0) b c freeVariableCertificate1 freeVariableCertificate2
      (by exact (show b ∉ (A).fv from (by exact fresh_b_not_A)))
      (by exact (show c ∉ (A).fv from (by exact fresh_c_not_A)))
      (by
        exact
          (show b ∉ ((syn_c0)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0];
              exact (show b ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
      (by
        exact
          (show c ∉ ((syn_c0)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0];
              exact (show c ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
      (show b ≠ c from (by exact fresh_b_ne_c))
  have p0005 :=
    @g_mtbir (.classMem (.cv a) (syn_cplc A (syn_c0)))
      (syn_wrex b A (syn_wrex c (syn_c0) (syn_wa (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0))
            (.classEq (.cv a) (syn_cun (.cv b) (.cv c))))))
      p0003 p0004
  have p0006 :=
    @g_mpgbir (.classEq (syn_cplc A (syn_c0)) (syn_c0))
      (.neg (.classMem (.cv a) (syn_cplc A (syn_c0)))) a p0000 p0005
  exact p0006

@[expose]
noncomputable def g_addcnnul (A : Class) (B : Class) :
    Nominal.NPrf
      (.imp (syn_wne (syn_cplc A B) (syn_c0))
        (syn_wa (syn_wne A (syn_c0)) (syn_wne B (syn_c0)))) :=
  by
  have p0000 := @g_addceq1 A (syn_c0) B
  have p0001 := @g_addccom (syn_c0) B
  have p0002 := @g_addcnul1 B
  have p0003 := @g_eqtri (syn_cplc (syn_c0) B) (syn_cplc B (syn_c0)) (syn_c0) p0001 p0002
  have p0004 :=
    @g_syl6eq (.classEq A (syn_c0)) (syn_cplc A B) (syn_cplc (syn_c0) B) (syn_c0) p0000
      p0003
  have p0005 := @g_necon3i A (syn_c0) (syn_cplc A B) (syn_c0) p0004
  have p0006 := @g_addceq2 B (syn_c0) A
  have p0007 := @g_addcnul1 A
  have p0008 :=
    @g_syl6eq (.classEq B (syn_c0)) (syn_cplc A B) (syn_cplc A (syn_c0)) (syn_c0) p0006
      p0007
  have p0009 := @g_necon3i B (syn_c0) (syn_cplc A B) (syn_c0) p0008
  have p0010 :=
    @g_jca (syn_wne (syn_cplc A B) (syn_c0)) (syn_wne A (syn_c0)) (syn_wne B (syn_c0))
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

@[expose]
noncomputable def g_preaddccan2lem1 (P : Class) (m : Var) (N : Class) (dv_N_m : m ∉ N.fv)
    (dv_P_m : m ∉ P.fv) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem N (syn_cnnc)) (.classMem P (syn_cnnc))) (.classMem (.cab m (.imp
              (syn_wa (syn_wne (syn_cplc (.cv m) N) (syn_c0))
                (.classEq (syn_cplc (.cv m) N) (syn_cplc (.cv m) P))) (.classEq N P)))
          (syn_cvv))) :=
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
  have p0000 := @g_addceq2 (.cv n) N (.cv m)
  have p0001 :=
    @g_neeq1d (.classEq (.cv n) N) (syn_cplc (.cv m) (.cv n)) (syn_cplc (.cv m) N)
      (syn_c0) p0000
  have p0002 :=
    @g_eqeq1d (.classEq (.cv n) N) (syn_cplc (.cv m) (.cv n)) (syn_cplc (.cv m) N)
      (syn_cplc (.cv m) (.cv p)) p0000
  have p0003 :=
    @g_anbi12d (.classEq (.cv n) N) (syn_wne (syn_cplc (.cv m) (.cv n)) (syn_c0))
      (syn_wne (syn_cplc (.cv m) N) (syn_c0))
      (.classEq (syn_cplc (.cv m) (.cv n)) (syn_cplc (.cv m) (.cv p)))
      (.classEq (syn_cplc (.cv m) N) (syn_cplc (.cv m) (.cv p))) p0001 p0002
  have p0004 :=
    @g_imbi1d (.classEq (.cv n) N)
      (syn_wa (syn_wne (syn_cplc (.cv m) (.cv n)) (syn_c0))
        (.classEq (syn_cplc (.cv m) (.cv n)) (syn_cplc (.cv m) (.cv p))))
      (syn_wa (syn_wne (syn_cplc (.cv m) N) (syn_c0))
        (.classEq (syn_cplc (.cv m) N) (syn_cplc (.cv m) (.cv p))))
      (.classEq N P) p0003
  have freeVariableCertificate0 : m ∉ ((Wff.classEq (.cv n) N)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      fresh_m_ne_n, dv_N_m, or_false, not_false_eq_true]
  have p0005 :=
    @g_abbidv (.classEq (.cv n) N)
      (.imp (syn_wa (syn_wne (syn_cplc (.cv m) (.cv n)) (syn_c0))
          (.classEq (syn_cplc (.cv m) (.cv n)) (syn_cplc (.cv m) (.cv p)))) (.classEq N P))
      (.imp (syn_wa (syn_wne (syn_cplc (.cv m) N) (syn_c0))
          (.classEq (syn_cplc (.cv m) N) (syn_cplc (.cv m) (.cv p)))) (.classEq N P))
      m freeVariableCertificate0 p0004
  have p0006 :=
    @g_eleq1d (.classEq (.cv n) N)
      (.cab m (.imp (syn_wa (syn_wne (syn_cplc (.cv m) (.cv n)) (syn_c0))
            (.classEq (syn_cplc (.cv m) (.cv n)) (syn_cplc (.cv m) (.cv p)))) (.classEq N P)))
      (.cab m (.imp (syn_wa (syn_wne (syn_cplc (.cv m) N) (syn_c0))
            (.classEq (syn_cplc (.cv m) N) (syn_cplc (.cv m) (.cv p)))) (.classEq N P)))
      (syn_cvv) p0005
  have p0007 := @g_addceq2 (.cv p) P (.cv m)
  have p0008 :=
    @g_eqeq2d (.classEq (.cv p) P) (syn_cplc (.cv m) (.cv p)) (syn_cplc (.cv m) P)
      (syn_cplc (.cv m) N) p0007
  have p0009 :=
    @g_anbi2d (.classEq (.cv p) P)
      (.classEq (syn_cplc (.cv m) N) (syn_cplc (.cv m) (.cv p)))
      (.classEq (syn_cplc (.cv m) N) (syn_cplc (.cv m) P))
      (syn_wne (syn_cplc (.cv m) N) (syn_c0)) p0008
  have p0010 :=
    @g_imbi1d (.classEq (.cv p) P)
      (syn_wa (syn_wne (syn_cplc (.cv m) N) (syn_c0))
        (.classEq (syn_cplc (.cv m) N) (syn_cplc (.cv m) (.cv p))))
      (syn_wa (syn_wne (syn_cplc (.cv m) N) (syn_c0))
        (.classEq (syn_cplc (.cv m) N) (syn_cplc (.cv m) P)))
      (.classEq N P) p0009
  have freeVariableCertificate1 : m ∉ ((Wff.classEq (.cv p) P)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      fresh_m_ne_p, dv_P_m, or_false, not_false_eq_true]
  have p0011 :=
    @g_abbidv (.classEq (.cv p) P)
      (.imp (syn_wa (syn_wne (syn_cplc (.cv m) N) (syn_c0))
          (.classEq (syn_cplc (.cv m) N) (syn_cplc (.cv m) (.cv p)))) (.classEq N P))
      (.imp (syn_wa (syn_wne (syn_cplc (.cv m) N) (syn_c0))
          (.classEq (syn_cplc (.cv m) N) (syn_cplc (.cv m) P))) (.classEq N P))
      m freeVariableCertificate1 p0010
  have p0012 :=
    @g_eleq1d (.classEq (.cv p) P)
      (.cab m (.imp (syn_wa (syn_wne (syn_cplc (.cv m) N) (syn_c0))
            (.classEq (syn_cplc (.cv m) N) (syn_cplc (.cv m) (.cv p)))) (.classEq N P)))
      (.cab m (.imp (syn_wa (syn_wne (syn_cplc (.cv m) N) (syn_c0))
            (.classEq (syn_cplc (.cv m) N) (syn_cplc (.cv m) P))) (.classEq N P)))
      (syn_cvv) p0011
  have p0013 :=
    @g_imor
      (syn_wa (syn_wne (syn_cplc (.cv m) (.cv n)) (syn_c0))
        (.classEq (syn_cplc (.cv m) (.cv n)) (syn_cplc (.cv m) (.cv p))))
      (.classEq N P)
  have p0014 :=
    @g_abbii
      (.imp (syn_wa (syn_wne (syn_cplc (.cv m) (.cv n)) (syn_c0))
          (.classEq (syn_cplc (.cv m) (.cv n)) (syn_cplc (.cv m) (.cv p)))) (.classEq N P))
      (syn_wo (.neg (syn_wa (syn_wne (syn_cplc (.cv m) (.cv n)) (syn_c0))
            (.classEq (syn_cplc (.cv m) (.cv n)) (syn_cplc (.cv m) (.cv p))))) (.classEq N P))
      m p0013
  have p0015 :=
    @g_unab
      (.neg (syn_wa (syn_wne (syn_cplc (.cv m) (.cv n)) (syn_c0))
          (.classEq (syn_cplc (.cv m) (.cv n)) (syn_cplc (.cv m) (.cv p)))))
      (.classEq N P) m
  have p0016 :=
    @g_eqtr4i
      (.cab m (.imp (syn_wa (syn_wne (syn_cplc (.cv m) (.cv n)) (syn_c0))
            (.classEq (syn_cplc (.cv m) (.cv n)) (syn_cplc (.cv m) (.cv p)))) (.classEq N P)))
      (.cab m (syn_wo (.neg (syn_wa (syn_wne (syn_cplc (.cv m) (.cv n)) (syn_c0))
              (.classEq (syn_cplc (.cv m) (.cv n)) (syn_cplc (.cv m) (.cv p)))))
          (.classEq N P)))
      (syn_cun (.cab m (.neg (syn_wa (syn_wne (syn_cplc (.cv m) (.cv n)) (syn_c0))
              (.classEq (syn_cplc (.cv m) (.cv n)) (syn_cplc (.cv m) (.cv p))))))
        (.cab m (.classEq N P)))
      p0014 p0015
  have p0017 := @g_vex m
  have p0018 :=
    @g_elcompl (.cv m)
      (syn_cin (syn_ccompl (syn_cimak (syn_ccnvk (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k
                      (syn_ccompl (syn_cimak
                          (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                          (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                      (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                        (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                          (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                  (syn_cpw1 (syn_cpw1 (.cv n)))))) (syn_csn (syn_c0)))) (syn_cimak (syn_ccnvk
            (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                          (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                          (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                      (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                        (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                          (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                  (syn_cpw1 (syn_cpw1 (.cv n))))) (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k
                      (syn_ccompl (syn_cimak
                          (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                          (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                      (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                        (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                          (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                  (syn_cpw1 (syn_cpw1 (.cv p))))))) (syn_cvv)))
      p0017
  have p0019 :=
    @g_elin (.cv m)
      (syn_ccompl (syn_cimak (syn_ccnvk (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k
                    (syn_ccompl (syn_cimak
                        (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                    (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                      (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                        (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                    (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                (syn_cpw1 (syn_cpw1 (.cv n)))))) (syn_csn (syn_c0))))
      (syn_cimak (syn_ccnvk (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
                      (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                    (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                      (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                        (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                    (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                (syn_cpw1 (syn_cpw1 (.cv n))))) (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k
                    (syn_ccompl (syn_cimak
                        (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                    (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                      (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                        (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                    (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                (syn_cpw1 (syn_cpw1 (.cv p))))))) (syn_cvv))
  have p0020 := @g_n_0ex
  have p0021 :=
    @g_opkelcnvk (syn_c0) (.cv m)
      (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
                (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
              (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                  (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
          (syn_cpw1 (syn_cpw1 (.cv n)))))
      p0020 p0017
  have p0023 :=
    @g_elimaksn
      (syn_ccnvk (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
                  (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                    (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                  (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                    (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
            (syn_cpw1 (syn_cpw1 (.cv n))))))
      (syn_c0) (.cv m) p0020 p0017
  have p0024 := @g_dfaddc2 (.cv m) (.cv n)
  have p0025 :=
    @g_eqeq2i (syn_cplc (.cv m) (.cv n))
      (syn_cimak (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
                (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
              (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                  (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
          (syn_cpw1 (syn_cpw1 (.cv n)))) (.cv m))
      (syn_c0) p0024
  have p0026 := @g_eqcom (syn_cplc (.cv m) (.cv n)) (syn_c0)
  have p0028 :=
    @g_opkelimagek (.cv m) (syn_c0)
      (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
              (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
            (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
              (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
        (syn_cpw1 (syn_cpw1 (.cv n))))
      p0017 p0020
  have p0029 :=
    @g_n_3bitr4i (.classEq (syn_c0) (syn_cplc (.cv m) (.cv n)))
      (.classEq (syn_c0) (syn_cimak (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
                  (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                    (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                  (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                    (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
            (syn_cpw1 (syn_cpw1 (.cv n)))) (.cv m)))
      (.classEq (syn_cplc (.cv m) (.cv n)) (syn_c0))
      (.classMem (syn_copk (.cv m) (syn_c0)) (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k
                (syn_ccompl
                  (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                    (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                  (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                    (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
            (syn_cpw1 (syn_cpw1 (.cv n))))))
      p0025 p0026 p0028
  have p0030 :=
    @g_n_3bitr4i
      (.classMem (syn_copk (syn_c0) (.cv m)) (syn_ccnvk (syn_cimagek (syn_cimak (syn_cdif
                (syn_cins3k (syn_ccompl (syn_cimak
                      (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                  (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                    (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                      (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
              (syn_cpw1 (syn_cpw1 (.cv n)))))))
      (.classMem (syn_copk (.cv m) (syn_c0)) (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k
                (syn_ccompl
                  (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                    (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                  (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                    (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
            (syn_cpw1 (syn_cpw1 (.cv n))))))
      (.classMem (.cv m) (syn_cimak (syn_ccnvk (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k
                    (syn_ccompl (syn_cimak
                        (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                    (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                      (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                        (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                    (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                (syn_cpw1 (syn_cpw1 (.cv n)))))) (syn_csn (syn_c0))))
      (.classEq (syn_cplc (.cv m) (.cv n)) (syn_c0)) p0021 p0023 p0029
  have p0031 :=
    @g_notbii
      (.classMem (.cv m) (syn_cimak (syn_ccnvk (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k
                    (syn_ccompl (syn_cimak
                        (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                    (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                      (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                        (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                    (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                (syn_cpw1 (syn_cpw1 (.cv n)))))) (syn_csn (syn_c0))))
      (.classEq (syn_cplc (.cv m) (.cv n)) (syn_c0)) p0030
  have p0032 :=
    @g_elcompl (.cv m)
      (syn_cimak (syn_ccnvk (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                      (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                  (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                    (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                      (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
              (syn_cpw1 (syn_cpw1 (.cv n)))))) (syn_csn (syn_c0)))
      p0017
  have p0033 := (Nominal.biimpRefl (syn_wne (syn_cplc (.cv m) (.cv n)) (syn_c0)))
  have p0034 :=
    @g_n_3bitr4i
      (.neg (.classMem (.cv m) (syn_cimak (syn_ccnvk (syn_cimagek (syn_cimak (syn_cdif
                    (syn_cins3k (syn_ccompl (syn_cimak
                          (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                          (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                      (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                        (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                          (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                  (syn_cpw1 (syn_cpw1 (.cv n)))))) (syn_csn (syn_c0)))))
      (.neg (.classEq (syn_cplc (.cv m) (.cv n)) (syn_c0)))
      (.classMem (.cv m) (syn_ccompl (syn_cimak (syn_ccnvk (syn_cimagek (syn_cimak (syn_cdif
                    (syn_cins3k (syn_ccompl (syn_cimak
                          (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                          (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                      (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                        (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                          (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                  (syn_cpw1 (syn_cpw1 (.cv n)))))) (syn_csn (syn_c0)))))
      (syn_wne (syn_cplc (.cv m) (.cv n)) (syn_c0)) p0031 p0032 p0033
  have p0035 :=
    @g_rexv
      (.classMem (syn_copk (.cv t) (.cv m)) (syn_ccnvk (syn_cin (syn_cimagek (syn_cimak
                (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                        (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                    (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                      (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                        (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                    (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                (syn_cpw1 (syn_cpw1 (.cv n))))) (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k
                    (syn_ccompl (syn_cimak
                        (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                    (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                      (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                        (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                    (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                (syn_cpw1 (syn_cpw1 (.cv p))))))))
      t
  have p0036 := @g_vex t
  have p0037 :=
    @g_opkelcnvk (.cv t) (.cv m)
      (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
                  (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                    (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                  (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                    (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
            (syn_cpw1 (syn_cpw1 (.cv n))))) (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k
                (syn_ccompl
                  (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                    (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                  (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                    (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
            (syn_cpw1 (syn_cpw1 (.cv p))))))
      p0036 p0017
  have p0038 :=
    @g_elin (syn_copk (.cv m) (.cv t))
      (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
                (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
              (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                  (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
          (syn_cpw1 (syn_cpw1 (.cv n)))))
      (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
                (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
              (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                  (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
          (syn_cpw1 (syn_cpw1 (.cv p)))))
  have p0039 :=
    @g_opkelimagek (.cv m) (.cv t)
      (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
              (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
            (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
              (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
        (syn_cpw1 (syn_cpw1 (.cv n))))
      p0017 p0036
  have p0040 :=
    @g_eqeq2i (syn_cplc (.cv m) (.cv n))
      (syn_cimak (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
                (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
              (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                  (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
          (syn_cpw1 (syn_cpw1 (.cv n)))) (.cv m))
      (.cv t) p0024
  have p0041 :=
    @g_bitr4i
      (.classMem (syn_copk (.cv m) (.cv t)) (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k
                (syn_ccompl
                  (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                    (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                  (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                    (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
            (syn_cpw1 (syn_cpw1 (.cv n))))))
      (.classEq (.cv t) (syn_cimak (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
                  (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                    (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                  (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                    (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
            (syn_cpw1 (syn_cpw1 (.cv n)))) (.cv m)))
      (.classEq (.cv t) (syn_cplc (.cv m) (.cv n))) p0039 p0040
  have p0042 :=
    @g_opkelimagek (.cv m) (.cv t)
      (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
              (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
            (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
              (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
        (syn_cpw1 (syn_cpw1 (.cv p))))
      p0017 p0036
  have p0043 := @g_dfaddc2 (.cv m) (.cv p)
  have p0044 :=
    @g_eqeq2i (syn_cplc (.cv m) (.cv p))
      (syn_cimak (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
                (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
              (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                  (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
          (syn_cpw1 (syn_cpw1 (.cv p)))) (.cv m))
      (.cv t) p0043
  have p0045 :=
    @g_bitr4i
      (.classMem (syn_copk (.cv m) (.cv t)) (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k
                (syn_ccompl
                  (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                    (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                  (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                    (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
            (syn_cpw1 (syn_cpw1 (.cv p))))))
      (.classEq (.cv t) (syn_cimak (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
                  (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                    (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                  (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                    (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
            (syn_cpw1 (syn_cpw1 (.cv p)))) (.cv m)))
      (.classEq (.cv t) (syn_cplc (.cv m) (.cv p))) p0042 p0044
  have p0046 :=
    @g_anbi12i
      (.classMem (syn_copk (.cv m) (.cv t)) (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k
                (syn_ccompl
                  (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                    (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                  (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                    (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
            (syn_cpw1 (syn_cpw1 (.cv n))))))
      (.classEq (.cv t) (syn_cplc (.cv m) (.cv n)))
      (.classMem (syn_copk (.cv m) (.cv t)) (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k
                (syn_ccompl
                  (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                    (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                  (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                    (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
            (syn_cpw1 (syn_cpw1 (.cv p))))))
      (.classEq (.cv t) (syn_cplc (.cv m) (.cv p))) p0041 p0045
  have p0047 :=
    @g_bitri
      (.classMem (syn_copk (.cv m) (.cv t)) (syn_cin (syn_cimagek (syn_cimak (syn_cdif
                (syn_cins3k (syn_ccompl (syn_cimak
                      (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                  (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                    (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                      (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
              (syn_cpw1 (syn_cpw1 (.cv n))))) (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k
                  (syn_ccompl (syn_cimak
                      (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                  (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                    (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                      (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
              (syn_cpw1 (syn_cpw1 (.cv p)))))))
      (syn_wa (.classMem (syn_copk (.cv m) (.cv t)) (syn_cimagek (syn_cimak (syn_cdif
                (syn_cins3k (syn_ccompl (syn_cimak
                      (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                  (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                    (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                      (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
              (syn_cpw1 (syn_cpw1 (.cv n)))))) (.classMem (syn_copk (.cv m) (.cv t))
          (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                      (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                  (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                    (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                      (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
              (syn_cpw1 (syn_cpw1 (.cv p)))))))
      (syn_wa (.classEq (.cv t) (syn_cplc (.cv m) (.cv n)))
        (.classEq (.cv t) (syn_cplc (.cv m) (.cv p))))
      p0038 p0046
  have p0048 :=
    @g_bitri
      (.classMem (syn_copk (.cv t) (.cv m)) (syn_ccnvk (syn_cin (syn_cimagek (syn_cimak
                (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                        (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                    (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                      (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                        (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                    (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                (syn_cpw1 (syn_cpw1 (.cv n))))) (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k
                    (syn_ccompl (syn_cimak
                        (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                    (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                      (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                        (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                    (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                (syn_cpw1 (syn_cpw1 (.cv p))))))))
      (.classMem (syn_copk (.cv m) (.cv t)) (syn_cin (syn_cimagek (syn_cimak (syn_cdif
                (syn_cins3k (syn_ccompl (syn_cimak
                      (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                  (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                    (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                      (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
              (syn_cpw1 (syn_cpw1 (.cv n))))) (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k
                  (syn_ccompl (syn_cimak
                      (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                  (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                    (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                      (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
              (syn_cpw1 (syn_cpw1 (.cv p)))))))
      (syn_wa (.classEq (.cv t) (syn_cplc (.cv m) (.cv n)))
        (.classEq (.cv t) (syn_cplc (.cv m) (.cv p))))
      p0037 p0047
  have p0049 :=
    @g_exbii
      (.classMem (syn_copk (.cv t) (.cv m)) (syn_ccnvk (syn_cin (syn_cimagek (syn_cimak
                (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                        (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                    (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                      (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                        (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                    (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                (syn_cpw1 (syn_cpw1 (.cv n))))) (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k
                    (syn_ccompl (syn_cimak
                        (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                    (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                      (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                        (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                    (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                (syn_cpw1 (syn_cpw1 (.cv p))))))))
      (syn_wa (.classEq (.cv t) (syn_cplc (.cv m) (.cv n)))
        (.classEq (.cv t) (syn_cplc (.cv m) (.cv p))))
      t p0048
  have p0050 :=
    @g_bitri
      (syn_wrex t (syn_cvv) (.classMem (syn_copk (.cv t) (.cv m)) (syn_ccnvk (syn_cin
              (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                          (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                          (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                      (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                        (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                          (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                  (syn_cpw1 (syn_cpw1 (.cv n))))) (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k
                      (syn_ccompl (syn_cimak
                          (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                          (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                      (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                        (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                          (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                  (syn_cpw1 (syn_cpw1 (.cv p)))))))))
      (syn_wex t (.classMem (syn_copk (.cv t) (.cv m)) (syn_ccnvk (syn_cin (syn_cimagek
                (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                          (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                          (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                      (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                        (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                          (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                  (syn_cpw1 (syn_cpw1 (.cv n))))) (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k
                      (syn_ccompl (syn_cimak
                          (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                          (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                      (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                        (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                          (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                  (syn_cpw1 (syn_cpw1 (.cv p)))))))))
      (syn_wex t (syn_wa (.classEq (.cv t) (syn_cplc (.cv m) (.cv n)))
          (.classEq (.cv t) (syn_cplc (.cv m) (.cv p)))))
      p0035 p0049
  have freeVariableCertificate2 :
    t ∉
      ((syn_ccnvk (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                        (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                    (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                      (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                        (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                    (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                (syn_cpw1 (syn_cpw1 (.cv n))))) (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k
                    (syn_ccompl (syn_cimak
                        (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                    (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                      (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                        (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                    (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                (syn_cpw1 (syn_cpw1 (.cv p)))))))).fv :=
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
    @g_elimak t
      (syn_ccnvk (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                      (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                  (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                    (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                      (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
              (syn_cpw1 (syn_cpw1 (.cv n))))) (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k
                  (syn_ccompl (syn_cimak
                      (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                  (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                    (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                      (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
              (syn_cpw1 (syn_cpw1 (.cv p)))))))
      (syn_cvv) (.cv m) freeVariableCertificate2
      (by
        exact
          (show t ∉ ((syn_cvv)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv];
              exact (show t ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
      freeVariableCertificate3 p0017
  have p0052 := @g_vex n
  have p0053 := @g_addcex (.cv m) (.cv n) p0017 p0052
  have freeVariableCertificate4 : t ∉ ((syn_cplc (.cv m) (.cv n))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      fresh_t_ne_m, fresh_t_ne_n, or_false, not_false_eq_true]
  have freeVariableCertificate5 : t ∉ ((syn_cplc (.cv m) (.cv p))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      fresh_t_ne_m, fresh_t_ne_p, or_false, not_false_eq_true]
  have p0054 :=
    @g_eqvinc t (syn_cplc (.cv m) (.cv n)) (syn_cplc (.cv m) (.cv p))
      freeVariableCertificate4 freeVariableCertificate5 p0053
  have p0055 :=
    @g_n_3bitr4i
      (syn_wrex t (syn_cvv) (.classMem (syn_copk (.cv t) (.cv m)) (syn_ccnvk (syn_cin
              (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                          (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                          (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                      (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                        (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                          (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                  (syn_cpw1 (syn_cpw1 (.cv n))))) (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k
                      (syn_ccompl (syn_cimak
                          (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                          (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                      (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                        (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                          (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                  (syn_cpw1 (syn_cpw1 (.cv p)))))))))
      (syn_wex t (syn_wa (.classEq (.cv t) (syn_cplc (.cv m) (.cv n)))
          (.classEq (.cv t) (syn_cplc (.cv m) (.cv p)))))
      (.classMem (.cv m) (syn_cimak (syn_ccnvk (syn_cin (syn_cimagek (syn_cimak (syn_cdif
                    (syn_cins3k (syn_ccompl (syn_cimak
                          (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                          (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                      (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                        (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                          (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                  (syn_cpw1 (syn_cpw1 (.cv n))))) (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k
                      (syn_ccompl (syn_cimak
                          (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                          (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                      (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                        (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                          (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                  (syn_cpw1 (syn_cpw1 (.cv p))))))) (syn_cvv)))
      (.classEq (syn_cplc (.cv m) (.cv n)) (syn_cplc (.cv m) (.cv p))) p0050 p0051 p0054
  have p0056 :=
    @g_anbi12i
      (.classMem (.cv m) (syn_ccompl (syn_cimak (syn_ccnvk (syn_cimagek (syn_cimak (syn_cdif
                    (syn_cins3k (syn_ccompl (syn_cimak
                          (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                          (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                      (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                        (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                          (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                  (syn_cpw1 (syn_cpw1 (.cv n)))))) (syn_csn (syn_c0)))))
      (syn_wne (syn_cplc (.cv m) (.cv n)) (syn_c0))
      (.classMem (.cv m) (syn_cimak (syn_ccnvk (syn_cin (syn_cimagek (syn_cimak (syn_cdif
                    (syn_cins3k (syn_ccompl (syn_cimak
                          (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                          (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                      (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                        (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                          (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                  (syn_cpw1 (syn_cpw1 (.cv n))))) (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k
                      (syn_ccompl (syn_cimak
                          (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                          (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                      (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                        (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                          (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                  (syn_cpw1 (syn_cpw1 (.cv p))))))) (syn_cvv)))
      (.classEq (syn_cplc (.cv m) (.cv n)) (syn_cplc (.cv m) (.cv p))) p0034 p0055
  have p0057 :=
    @g_bitri
      (.classMem (.cv m) (syn_cin (syn_ccompl (syn_cimak (syn_ccnvk (syn_cimagek (syn_cimak
                    (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                            (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                            (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                        (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                          (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                            (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                    (syn_cpw1 (syn_cpw1 (.cv n)))))) (syn_csn (syn_c0)))) (syn_cimak (syn_ccnvk
              (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                            (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                            (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                        (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                          (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                            (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                    (syn_cpw1 (syn_cpw1 (.cv n))))) (syn_cimagek (syn_cimak (syn_cdif
                      (syn_cins3k (syn_ccompl (syn_cimak
                            (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                            (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                        (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                          (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                            (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                    (syn_cpw1 (syn_cpw1 (.cv p))))))) (syn_cvv))))
      (syn_wa (.classMem (.cv m) (syn_ccompl (syn_cimak (syn_ccnvk (syn_cimagek (syn_cimak
                    (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                            (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                            (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                        (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                          (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                            (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                    (syn_cpw1 (syn_cpw1 (.cv n)))))) (syn_csn (syn_c0))))) (.classMem (.cv m)
          (syn_cimak (syn_ccnvk (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k
                        (syn_ccompl (syn_cimak
                            (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                            (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                        (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                          (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                            (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                    (syn_cpw1 (syn_cpw1 (.cv n))))) (syn_cimagek (syn_cimak (syn_cdif
                      (syn_cins3k (syn_ccompl (syn_cimak
                            (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                            (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                        (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                          (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                            (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                    (syn_cpw1 (syn_cpw1 (.cv p))))))) (syn_cvv))))
      (syn_wa (syn_wne (syn_cplc (.cv m) (.cv n)) (syn_c0))
        (.classEq (syn_cplc (.cv m) (.cv n)) (syn_cplc (.cv m) (.cv p))))
      p0019 p0056
  have p0058 :=
    @g_notbii
      (.classMem (.cv m) (syn_cin (syn_ccompl (syn_cimak (syn_ccnvk (syn_cimagek (syn_cimak
                    (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                            (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                            (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                        (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                          (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                            (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                    (syn_cpw1 (syn_cpw1 (.cv n)))))) (syn_csn (syn_c0)))) (syn_cimak (syn_ccnvk
              (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                            (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                            (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                        (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                          (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                            (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                    (syn_cpw1 (syn_cpw1 (.cv n))))) (syn_cimagek (syn_cimak (syn_cdif
                      (syn_cins3k (syn_ccompl (syn_cimak
                            (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                            (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                        (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                          (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                            (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                    (syn_cpw1 (syn_cpw1 (.cv p))))))) (syn_cvv))))
      (syn_wa (syn_wne (syn_cplc (.cv m) (.cv n)) (syn_c0))
        (.classEq (syn_cplc (.cv m) (.cv n)) (syn_cplc (.cv m) (.cv p))))
      p0057
  have p0059 :=
    @g_bitri
      (.classMem (.cv m) (syn_ccompl (syn_cin (syn_ccompl (syn_cimak (syn_ccnvk (syn_cimagek
                    (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                              (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                              (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                          (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                            (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                              (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                      (syn_cpw1 (syn_cpw1 (.cv n)))))) (syn_csn (syn_c0)))) (syn_cimak
              (syn_ccnvk (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
                            (syn_cimak (syn_cin (syn_cins3k (syn_cssetk))
                                (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                        (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                            (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                              (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                      (syn_cpw1 (syn_cpw1 (.cv n))))) (syn_cimagek (syn_cimak (syn_cdif
                        (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk))
                                (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                        (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                            (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                              (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                      (syn_cpw1 (syn_cpw1 (.cv p))))))) (syn_cvv)))))
      (.neg (.classMem (.cv m) (syn_cin (syn_ccompl (syn_cimak (syn_ccnvk (syn_cimagek
                    (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                              (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                              (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                          (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                            (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                              (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                      (syn_cpw1 (syn_cpw1 (.cv n)))))) (syn_csn (syn_c0)))) (syn_cimak
              (syn_ccnvk (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
                            (syn_cimak (syn_cin (syn_cins3k (syn_cssetk))
                                (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                        (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                            (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                              (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                      (syn_cpw1 (syn_cpw1 (.cv n))))) (syn_cimagek (syn_cimak (syn_cdif
                        (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk))
                                (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                        (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                            (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                              (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                      (syn_cpw1 (syn_cpw1 (.cv p))))))) (syn_cvv)))))
      (.neg (syn_wa (syn_wne (syn_cplc (.cv m) (.cv n)) (syn_c0))
          (.classEq (syn_cplc (.cv m) (.cv n)) (syn_cplc (.cv m) (.cv p)))))
      p0018 p0058
  have freeVariableCertificate6 :
    m ∉
      ((syn_ccompl (syn_cin (syn_ccompl (syn_cimak (syn_ccnvk (syn_cimagek (syn_cimak (syn_cdif
                        (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk))
                                (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                        (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                            (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                              (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                      (syn_cpw1 (syn_cpw1 (.cv n)))))) (syn_csn (syn_c0)))) (syn_cimak
              (syn_ccnvk (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
                            (syn_cimak (syn_cin (syn_cins3k (syn_cssetk))
                                (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                        (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                            (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                              (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                      (syn_cpw1 (syn_cpw1 (.cv n))))) (syn_cimagek (syn_cimak (syn_cdif
                        (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk))
                                (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                        (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                            (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                              (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                      (syn_cpw1 (syn_cpw1 (.cv p))))))) (syn_cvv))))).fv :=
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
    @g_eqabi
      (.neg (syn_wa (syn_wne (syn_cplc (.cv m) (.cv n)) (syn_c0))
          (.classEq (syn_cplc (.cv m) (.cv n)) (syn_cplc (.cv m) (.cv p)))))
      m
      (syn_ccompl (syn_cin (syn_ccompl (syn_cimak (syn_ccnvk (syn_cimagek (syn_cimak (syn_cdif
                      (syn_cins3k (syn_ccompl (syn_cimak
                            (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                            (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                        (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                          (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                            (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                    (syn_cpw1 (syn_cpw1 (.cv n)))))) (syn_csn (syn_c0)))) (syn_cimak (syn_ccnvk
              (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                            (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                            (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                        (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                          (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                            (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                    (syn_cpw1 (syn_cpw1 (.cv n))))) (syn_cimagek (syn_cimak (syn_cdif
                      (syn_cins3k (syn_ccompl (syn_cimak
                            (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                            (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                        (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                          (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                            (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                    (syn_cpw1 (syn_cpw1 (.cv p))))))) (syn_cvv))))
      freeVariableCertificate6 p0059
  have p0061 := @g_addcexlem
  have p0062 := @g_pw1ex (.cv n) p0052
  have p0063 := @g_pw1ex (syn_cpw1 (.cv n)) p0062
  have p0064 :=
    @g_imakex
      (syn_cdif (syn_cins3k (syn_ccompl
            (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
              (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
          (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
            (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
              (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
      (syn_cpw1 (syn_cpw1 (.cv n))) p0061 p0063
  have p0065 :=
    @g_imagekex
      (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
              (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
            (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
              (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
        (syn_cpw1 (syn_cpw1 (.cv n))))
      p0064
  have p0066 :=
    @g_cnvkex
      (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
                (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
              (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                  (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
          (syn_cpw1 (syn_cpw1 (.cv n)))))
      p0065
  have p0067 := @g_snex (syn_c0)
  have p0068 :=
    @g_imakex
      (syn_ccnvk (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
                  (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                    (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                  (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                    (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
            (syn_cpw1 (syn_cpw1 (.cv n))))))
      (syn_csn (syn_c0)) p0066 p0067
  have p0069 :=
    @g_complex
      (syn_cimak (syn_ccnvk (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                      (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                  (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                    (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                      (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
              (syn_cpw1 (syn_cpw1 (.cv n)))))) (syn_csn (syn_c0)))
      p0068
  have p0071 := @g_vex p
  have p0072 := @g_pw1ex (.cv p) p0071
  have p0073 := @g_pw1ex (syn_cpw1 (.cv p)) p0072
  have p0074 :=
    @g_imakex
      (syn_cdif (syn_cins3k (syn_ccompl
            (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
              (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
          (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
            (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
              (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
      (syn_cpw1 (syn_cpw1 (.cv p))) p0061 p0073
  have p0075 :=
    @g_imagekex
      (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
              (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
            (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
              (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
        (syn_cpw1 (syn_cpw1 (.cv p))))
      p0074
  have p0076 :=
    @g_inex
      (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
                (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
              (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                  (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
          (syn_cpw1 (syn_cpw1 (.cv n)))))
      (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
                (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
              (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                  (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
          (syn_cpw1 (syn_cpw1 (.cv p)))))
      p0065 p0075
  have p0077 :=
    @g_cnvkex
      (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
                  (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                    (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                  (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                    (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
            (syn_cpw1 (syn_cpw1 (.cv n))))) (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k
                (syn_ccompl
                  (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                    (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                  (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                    (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
            (syn_cpw1 (syn_cpw1 (.cv p))))))
      p0076
  have p0078 := @g_vvex
  have p0079 :=
    @g_imakex
      (syn_ccnvk (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                      (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                  (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                    (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                      (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
              (syn_cpw1 (syn_cpw1 (.cv n))))) (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k
                  (syn_ccompl (syn_cimak
                      (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                  (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                    (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                      (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
              (syn_cpw1 (syn_cpw1 (.cv p)))))))
      (syn_cvv) p0077 p0078
  have p0080 :=
    @g_inex
      (syn_ccompl (syn_cimak (syn_ccnvk (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k
                    (syn_ccompl (syn_cimak
                        (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                    (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                      (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                        (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                    (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                (syn_cpw1 (syn_cpw1 (.cv n)))))) (syn_csn (syn_c0))))
      (syn_cimak (syn_ccnvk (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
                      (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                    (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                      (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                        (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                    (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                (syn_cpw1 (syn_cpw1 (.cv n))))) (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k
                    (syn_ccompl (syn_cimak
                        (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                    (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                      (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                        (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                    (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                (syn_cpw1 (syn_cpw1 (.cv p))))))) (syn_cvv))
      p0069 p0079
  have p0081 :=
    @g_complex
      (syn_cin (syn_ccompl (syn_cimak (syn_ccnvk (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k
                      (syn_ccompl (syn_cimak
                          (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                          (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                      (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                        (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                          (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                  (syn_cpw1 (syn_cpw1 (.cv n)))))) (syn_csn (syn_c0)))) (syn_cimak (syn_ccnvk
            (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                          (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                          (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                      (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                        (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                          (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                  (syn_cpw1 (syn_cpw1 (.cv n))))) (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k
                      (syn_ccompl (syn_cimak
                          (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                          (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                      (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                        (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                          (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                  (syn_cpw1 (syn_cpw1 (.cv p))))))) (syn_cvv)))
      p0080
  have p0082 :=
    @g_eqeltrri
      (syn_ccompl (syn_cin (syn_ccompl (syn_cimak (syn_ccnvk (syn_cimagek (syn_cimak (syn_cdif
                      (syn_cins3k (syn_ccompl (syn_cimak
                            (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                            (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                        (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                          (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                            (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                    (syn_cpw1 (syn_cpw1 (.cv n)))))) (syn_csn (syn_c0)))) (syn_cimak (syn_ccnvk
              (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                            (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                            (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                        (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                          (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                            (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                    (syn_cpw1 (syn_cpw1 (.cv n))))) (syn_cimagek (syn_cimak (syn_cdif
                      (syn_cins3k (syn_ccompl (syn_cimak
                            (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                            (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                        (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                          (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                            (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                    (syn_cpw1 (syn_cpw1 (.cv p))))))) (syn_cvv))))
      (.cab m (.neg (syn_wa (syn_wne (syn_cplc (.cv m) (.cv n)) (syn_c0))
            (.classEq (syn_cplc (.cv m) (.cv n)) (syn_cplc (.cv m) (.cv p))))))
      (syn_cvv) p0060 p0081
  have freeVariableCertificate7 : m ∉ ((Wff.classEq N P)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union, dv_N_m,
      dv_P_m, or_false, not_false_eq_true]
  have p0083 := @g_abexv (.classEq N P) m freeVariableCertificate7
  have p0084 :=
    @g_unex
      (.cab m (.neg (syn_wa (syn_wne (syn_cplc (.cv m) (.cv n)) (syn_c0))
            (.classEq (syn_cplc (.cv m) (.cv n)) (syn_cplc (.cv m) (.cv p))))))
      (.cab m (.classEq N P)) p0082 p0083
  have p0085 :=
    @g_eqeltri
      (.cab m (.imp (syn_wa (syn_wne (syn_cplc (.cv m) (.cv n)) (syn_c0))
            (.classEq (syn_cplc (.cv m) (.cv n)) (syn_cplc (.cv m) (.cv p)))) (.classEq N P)))
      (syn_cun (.cab m (.neg (syn_wa (syn_wne (syn_cplc (.cv m) (.cv n)) (syn_c0))
              (.classEq (syn_cplc (.cv m) (.cv n)) (syn_cplc (.cv m) (.cv p))))))
        (.cab m (.classEq N P)))
      (syn_cvv) p0016 p0084
  have freeVariableCertificate8 :
    p ∉
      ((Wff.classMem (.cab m (.imp (syn_wa (syn_wne (syn_cplc (.cv m) N) (syn_c0))
                (.classEq (syn_cplc (.cv m) N) (syn_cplc (.cv m) P))) (.classEq N P)))
          (syn_cvv))).fv :=
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
      ((Wff.classMem (.cab m (.imp (syn_wa (syn_wne (syn_cplc (.cv m) N) (syn_c0))
                (.classEq (syn_cplc (.cv m) N) (syn_cplc (.cv m) (.cv p)))) (.classEq N P)))
          (syn_cvv))).fv :=
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
    @g_vtocl2g
      (.classMem (.cab m (.imp (syn_wa (syn_wne (syn_cplc (.cv m) (.cv n)) (syn_c0))
              (.classEq (syn_cplc (.cv m) (.cv n)) (syn_cplc (.cv m) (.cv p)))) (.classEq N P)))
        (syn_cvv))
      (.classMem (.cab m (.imp (syn_wa (syn_wne (syn_cplc (.cv m) N) (syn_c0))
              (.classEq (syn_cplc (.cv m) N) (syn_cplc (.cv m) (.cv p)))) (.classEq N P)))
        (syn_cvv))
      (.classMem (.cab m (.imp (syn_wa (syn_wne (syn_cplc (.cv m) N) (syn_c0))
              (.classEq (syn_cplc (.cv m) N) (syn_cplc (.cv m) P))) (.classEq N P))) (syn_cvv))
      n p N P (syn_cnnc) (syn_cnnc)
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

@[expose]
noncomputable def g_preaddccan2 (P : Class) (M : Class) (N : Class) :
    Nominal.NPrf
      (.imp (syn_wa (syn_w3a (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))
            (.classMem P (syn_cnnc))) (syn_wne (syn_cplc M N) (syn_c0)))
        (syn_wb (.classEq (syn_cplc M N) (syn_cplc M P)) (.classEq N P))) :=
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
    @g_preaddccan2lem1 P m N (by exact (show m ∉ (N).fv from (by exact fresh_m_not_N)))
      (by exact (show m ∉ (P).fv from (by exact fresh_m_not_P)))
  have p0001 := @g_addceq1 (.cv m) (syn_c0c) N
  have p0002 :=
    @g_neeq1d (.classEq (.cv m) (syn_c0c)) (syn_cplc (.cv m) N) (syn_cplc (syn_c0c) N)
      (syn_c0) p0001
  have p0003 := @g_addceq1 (.cv m) (syn_c0c) P
  have p0004 :=
    @g_eqeq12d (.classEq (.cv m) (syn_c0c)) (syn_cplc (.cv m) N) (syn_cplc (syn_c0c) N)
      (syn_cplc (.cv m) P) (syn_cplc (syn_c0c) P) p0001 p0003
  have p0005 :=
    @g_anbi12d (.classEq (.cv m) (syn_c0c)) (syn_wne (syn_cplc (.cv m) N) (syn_c0))
      (syn_wne (syn_cplc (syn_c0c) N) (syn_c0))
      (.classEq (syn_cplc (.cv m) N) (syn_cplc (.cv m) P))
      (.classEq (syn_cplc (syn_c0c) N) (syn_cplc (syn_c0c) P)) p0002 p0004
  have p0006 :=
    @g_imbi1d (.classEq (.cv m) (syn_c0c))
      (syn_wa (syn_wne (syn_cplc (.cv m) N) (syn_c0))
        (.classEq (syn_cplc (.cv m) N) (syn_cplc (.cv m) P)))
      (syn_wa (syn_wne (syn_cplc (syn_c0c) N) (syn_c0))
        (.classEq (syn_cplc (syn_c0c) N) (syn_cplc (syn_c0c) P)))
      (.classEq N P) p0005
  have p0007 := @g_addceq1 (.cv m) (.cv k) N
  have p0008_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq m k) (.classEq (syn_cplc (.cv m) N) (syn_cplc (.cv k) N))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_cplc syn_wrex syn_wex syn_wa
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0007
  have p0008 :=
    @g_neeq1d (.objEq m k) (syn_cplc (.cv m) N) (syn_cplc (.cv k) N) (syn_c0)
      p0008_e00_recanon
  have p0009 := @g_addceq1 (.cv m) (.cv k) P
  have p0010_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq m k) (.classEq (syn_cplc (.cv m) N) (syn_cplc (.cv k) N))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_cplc syn_wrex syn_wex syn_wa
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0007
  have p0010_e01_recanon :
    Nominal.NPrf
      (.imp (.objEq m k) (.classEq (syn_cplc (.cv m) P) (syn_cplc (.cv k) P))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_cplc syn_wrex syn_wex syn_wa
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0009
  have p0010 :=
    @g_eqeq12d (.objEq m k) (syn_cplc (.cv m) N) (syn_cplc (.cv k) N) (syn_cplc (.cv m) P)
      (syn_cplc (.cv k) P) p0010_e00_recanon p0010_e01_recanon
  have p0011 :=
    @g_anbi12d (.objEq m k) (syn_wne (syn_cplc (.cv m) N) (syn_c0))
      (syn_wne (syn_cplc (.cv k) N) (syn_c0))
      (.classEq (syn_cplc (.cv m) N) (syn_cplc (.cv m) P))
      (.classEq (syn_cplc (.cv k) N) (syn_cplc (.cv k) P)) p0008 p0010
  have p0012 :=
    @g_imbi1d (.objEq m k)
      (syn_wa (syn_wne (syn_cplc (.cv m) N) (syn_c0))
        (.classEq (syn_cplc (.cv m) N) (syn_cplc (.cv m) P)))
      (syn_wa (syn_wne (syn_cplc (.cv k) N) (syn_c0))
        (.classEq (syn_cplc (.cv k) N) (syn_cplc (.cv k) P)))
      (.classEq N P) p0011
  have p0013 := @g_addceq1 (.cv m) (syn_cplc (.cv k) (syn_c1c)) N
  have p0014 := @g_addc32 (.cv k) (syn_c1c) N
  have p0015 :=
    @g_syl6eq (.classEq (.cv m) (syn_cplc (.cv k) (syn_c1c))) (syn_cplc (.cv m) N)
      (syn_cplc (syn_cplc (.cv k) (syn_c1c)) N) (syn_cplc (syn_cplc (.cv k) N) (syn_c1c))
      p0013 p0014
  have p0016 :=
    @g_neeq1d (.classEq (.cv m) (syn_cplc (.cv k) (syn_c1c))) (syn_cplc (.cv m) N)
      (syn_cplc (syn_cplc (.cv k) N) (syn_c1c)) (syn_c0) p0015
  have p0017 := @g_addceq1 (.cv m) (syn_cplc (.cv k) (syn_c1c)) P
  have p0018 := @g_addc32 (.cv k) (syn_c1c) P
  have p0019 :=
    @g_syl6eq (.classEq (.cv m) (syn_cplc (.cv k) (syn_c1c))) (syn_cplc (.cv m) P)
      (syn_cplc (syn_cplc (.cv k) (syn_c1c)) P) (syn_cplc (syn_cplc (.cv k) P) (syn_c1c))
      p0017 p0018
  have p0020 :=
    @g_eqeq12d (.classEq (.cv m) (syn_cplc (.cv k) (syn_c1c))) (syn_cplc (.cv m) N)
      (syn_cplc (syn_cplc (.cv k) N) (syn_c1c)) (syn_cplc (.cv m) P)
      (syn_cplc (syn_cplc (.cv k) P) (syn_c1c)) p0015 p0019
  have p0021 :=
    @g_anbi12d (.classEq (.cv m) (syn_cplc (.cv k) (syn_c1c)))
      (syn_wne (syn_cplc (.cv m) N) (syn_c0))
      (syn_wne (syn_cplc (syn_cplc (.cv k) N) (syn_c1c)) (syn_c0))
      (.classEq (syn_cplc (.cv m) N) (syn_cplc (.cv m) P))
      (.classEq (syn_cplc (syn_cplc (.cv k) N) (syn_c1c))
        (syn_cplc (syn_cplc (.cv k) P) (syn_c1c)))
      p0016 p0020
  have p0022 :=
    @g_imbi1d (.classEq (.cv m) (syn_cplc (.cv k) (syn_c1c)))
      (syn_wa (syn_wne (syn_cplc (.cv m) N) (syn_c0))
        (.classEq (syn_cplc (.cv m) N) (syn_cplc (.cv m) P)))
      (syn_wa (syn_wne (syn_cplc (syn_cplc (.cv k) N) (syn_c1c)) (syn_c0))
        (.classEq (syn_cplc (syn_cplc (.cv k) N) (syn_c1c))
          (syn_cplc (syn_cplc (.cv k) P) (syn_c1c))))
      (.classEq N P) p0021
  have p0023 := @g_addceq1 (.cv m) M N
  have p0024 :=
    @g_neeq1d (.classEq (.cv m) M) (syn_cplc (.cv m) N) (syn_cplc M N) (syn_c0) p0023
  have p0025 := @g_addceq1 (.cv m) M P
  have p0026 :=
    @g_eqeq12d (.classEq (.cv m) M) (syn_cplc (.cv m) N) (syn_cplc M N)
      (syn_cplc (.cv m) P) (syn_cplc M P) p0023 p0025
  have p0027 :=
    @g_anbi12d (.classEq (.cv m) M) (syn_wne (syn_cplc (.cv m) N) (syn_c0))
      (syn_wne (syn_cplc M N) (syn_c0))
      (.classEq (syn_cplc (.cv m) N) (syn_cplc (.cv m) P))
      (.classEq (syn_cplc M N) (syn_cplc M P)) p0024 p0026
  have p0028 :=
    @g_imbi1d (.classEq (.cv m) M)
      (syn_wa (syn_wne (syn_cplc (.cv m) N) (syn_c0))
        (.classEq (syn_cplc (.cv m) N) (syn_cplc (.cv m) P)))
      (syn_wa (syn_wne (syn_cplc M N) (syn_c0)) (.classEq (syn_cplc M N) (syn_cplc M P)))
      (.classEq N P) p0027
  have p0029 := @g_addcid2 N
  have p0030 := @g_addcid2 P
  have p0031 := @g_eqeq12i (syn_cplc (syn_c0c) N) N (syn_cplc (syn_c0c) P) P p0029 p0030
  have p0032 :=
    @g_biimpi (.classEq (syn_cplc (syn_c0c) N) (syn_cplc (syn_c0c) P)) (.classEq N P)
      p0031
  have p0033 :=
    @g_adantl (.classEq (syn_cplc (syn_c0c) N) (syn_cplc (syn_c0c) P)) (.classEq N P)
      (syn_wne (syn_cplc (syn_c0c) N) (syn_c0)) p0032
  have p0034 :=
    @g_a1i
      (.imp (syn_wa (syn_wne (syn_cplc (syn_c0c) N) (syn_c0))
          (.classEq (syn_cplc (syn_c0c) N) (syn_cplc (syn_c0c) P))) (.classEq N P))
      (syn_wa (.classMem N (syn_cnnc)) (.classMem P (syn_cnnc))) p0033
  have p0035 := @g_addcnnul (syn_cplc (.cv k) N) (syn_c1c)
  have p0036 :=
    @g_simpld (syn_wne (syn_cplc (syn_cplc (.cv k) N) (syn_c1c)) (syn_c0))
      (syn_wne (syn_cplc (.cv k) N) (syn_c0)) (syn_wne (syn_c1c) (syn_c0)) p0035
  have p0037 :=
    @g_ad2antrl (syn_wne (syn_cplc (syn_cplc (.cv k) N) (syn_c1c)) (syn_c0))
      (syn_wne (syn_cplc (.cv k) N) (syn_c0))
      (syn_wa (.classMem (.cv k) (syn_cnnc))
        (syn_wa (.classMem N (syn_cnnc)) (.classMem P (syn_cnnc))))
      (.classEq (syn_cplc (syn_cplc (.cv k) N) (syn_c1c))
        (syn_cplc (syn_cplc (.cv k) P) (syn_c1c)))
      p0036
  have p0038 :=
    @g_simpll (.classMem (.cv k) (syn_cnnc))
      (syn_wa (.classMem N (syn_cnnc)) (.classMem P (syn_cnnc)))
      (syn_wa (syn_wne (syn_cplc (syn_cplc (.cv k) N) (syn_c1c)) (syn_c0))
        (.classEq (syn_cplc (syn_cplc (.cv k) N) (syn_c1c))
          (syn_cplc (syn_cplc (.cv k) P) (syn_c1c))))
  have p0039 :=
    @g_simplrl (.classMem (.cv k) (syn_cnnc)) (.classMem N (syn_cnnc))
      (.classMem P (syn_cnnc))
      (syn_wa (syn_wne (syn_cplc (syn_cplc (.cv k) N) (syn_c1c)) (syn_c0))
        (.classEq (syn_cplc (syn_cplc (.cv k) N) (syn_c1c))
          (syn_cplc (syn_cplc (.cv k) P) (syn_c1c))))
  have p0040 := @g_nncaddccl (.cv k) N
  have p0041 :=
    @g_syl2anc
      (syn_wa (syn_wa (.classMem (.cv k) (syn_cnnc))
          (syn_wa (.classMem N (syn_cnnc)) (.classMem P (syn_cnnc))))
        (syn_wa (syn_wne (syn_cplc (syn_cplc (.cv k) N) (syn_c1c)) (syn_c0))
          (.classEq (syn_cplc (syn_cplc (.cv k) N) (syn_c1c))
            (syn_cplc (syn_cplc (.cv k) P) (syn_c1c)))))
      (.classMem (.cv k) (syn_cnnc)) (.classMem N (syn_cnnc))
      (.classMem (syn_cplc (.cv k) N) (syn_cnnc)) p0038 p0039 p0040
  have p0042 :=
    @g_simplrr (.classMem (.cv k) (syn_cnnc)) (.classMem N (syn_cnnc))
      (.classMem P (syn_cnnc))
      (syn_wa (syn_wne (syn_cplc (syn_cplc (.cv k) N) (syn_c1c)) (syn_c0))
        (.classEq (syn_cplc (syn_cplc (.cv k) N) (syn_c1c))
          (syn_cplc (syn_cplc (.cv k) P) (syn_c1c))))
  have p0043 := @g_nncaddccl (.cv k) P
  have p0044 :=
    @g_syl2anc
      (syn_wa (syn_wa (.classMem (.cv k) (syn_cnnc))
          (syn_wa (.classMem N (syn_cnnc)) (.classMem P (syn_cnnc))))
        (syn_wa (syn_wne (syn_cplc (syn_cplc (.cv k) N) (syn_c1c)) (syn_c0))
          (.classEq (syn_cplc (syn_cplc (.cv k) N) (syn_c1c))
            (syn_cplc (syn_cplc (.cv k) P) (syn_c1c)))))
      (.classMem (.cv k) (syn_cnnc)) (.classMem P (syn_cnnc))
      (.classMem (syn_cplc (.cv k) P) (syn_cnnc)) p0038 p0042 p0043
  have p0045 :=
    @g_simprr
      (syn_wa (.classMem (.cv k) (syn_cnnc))
        (syn_wa (.classMem N (syn_cnnc)) (.classMem P (syn_cnnc))))
      (syn_wne (syn_cplc (syn_cplc (.cv k) N) (syn_c1c)) (syn_c0))
      (.classEq (syn_cplc (syn_cplc (.cv k) N) (syn_c1c))
        (syn_cplc (syn_cplc (.cv k) P) (syn_c1c)))
  have p0046 :=
    @g_simprl
      (syn_wa (.classMem (.cv k) (syn_cnnc))
        (syn_wa (.classMem N (syn_cnnc)) (.classMem P (syn_cnnc))))
      (syn_wne (syn_cplc (syn_cplc (.cv k) N) (syn_c1c)) (syn_c0))
      (.classEq (syn_cplc (syn_cplc (.cv k) N) (syn_c1c))
        (syn_cplc (syn_cplc (.cv k) P) (syn_c1c)))
  have p0047 := @g_prepeano4 (syn_cplc (.cv k) N) (syn_cplc (.cv k) P)
  have p0048 :=
    @g_syl22anc
      (syn_wa (syn_wa (.classMem (.cv k) (syn_cnnc))
          (syn_wa (.classMem N (syn_cnnc)) (.classMem P (syn_cnnc))))
        (syn_wa (syn_wne (syn_cplc (syn_cplc (.cv k) N) (syn_c1c)) (syn_c0))
          (.classEq (syn_cplc (syn_cplc (.cv k) N) (syn_c1c))
            (syn_cplc (syn_cplc (.cv k) P) (syn_c1c)))))
      (.classMem (syn_cplc (.cv k) N) (syn_cnnc))
      (.classMem (syn_cplc (.cv k) P) (syn_cnnc))
      (.classEq (syn_cplc (syn_cplc (.cv k) N) (syn_c1c))
        (syn_cplc (syn_cplc (.cv k) P) (syn_c1c)))
      (syn_wne (syn_cplc (syn_cplc (.cv k) N) (syn_c1c)) (syn_c0))
      (.classEq (syn_cplc (.cv k) N) (syn_cplc (.cv k) P)) p0041 p0044 p0045 p0046 p0047
  have p0049 :=
    @g_jca
      (syn_wa (syn_wa (.classMem (.cv k) (syn_cnnc))
          (syn_wa (.classMem N (syn_cnnc)) (.classMem P (syn_cnnc))))
        (syn_wa (syn_wne (syn_cplc (syn_cplc (.cv k) N) (syn_c1c)) (syn_c0))
          (.classEq (syn_cplc (syn_cplc (.cv k) N) (syn_c1c))
            (syn_cplc (syn_cplc (.cv k) P) (syn_c1c)))))
      (syn_wne (syn_cplc (.cv k) N) (syn_c0))
      (.classEq (syn_cplc (.cv k) N) (syn_cplc (.cv k) P)) p0037 p0048
  have p0050 :=
    @g_ex
      (syn_wa (.classMem (.cv k) (syn_cnnc))
        (syn_wa (.classMem N (syn_cnnc)) (.classMem P (syn_cnnc))))
      (syn_wa (syn_wne (syn_cplc (syn_cplc (.cv k) N) (syn_c1c)) (syn_c0))
        (.classEq (syn_cplc (syn_cplc (.cv k) N) (syn_c1c))
          (syn_cplc (syn_cplc (.cv k) P) (syn_c1c))))
      (syn_wa (syn_wne (syn_cplc (.cv k) N) (syn_c0))
        (.classEq (syn_cplc (.cv k) N) (syn_cplc (.cv k) P)))
      p0049
  have p0051 :=
    @g_imim1d
      (syn_wa (.classMem (.cv k) (syn_cnnc))
        (syn_wa (.classMem N (syn_cnnc)) (.classMem P (syn_cnnc))))
      (syn_wa (syn_wne (syn_cplc (syn_cplc (.cv k) N) (syn_c1c)) (syn_c0))
        (.classEq (syn_cplc (syn_cplc (.cv k) N) (syn_c1c))
          (syn_cplc (syn_cplc (.cv k) P) (syn_c1c))))
      (syn_wa (syn_wne (syn_cplc (.cv k) N) (syn_c0))
        (.classEq (syn_cplc (.cv k) N) (syn_cplc (.cv k) P)))
      (.classEq N P) p0050
  have freeVariableCertificate0 :
    m ∉
      ((Wff.imp (syn_wa (syn_wne (syn_cplc (.cv k) N) (syn_c0))
            (.classEq (syn_cplc (.cv k) N) (syn_cplc (.cv k) P))) (.classEq N P))).fv :=
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
    k ∉ ((syn_wa (.classMem N (syn_cnnc)) (.classMem P (syn_cnnc)))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union,
      Finset.notMem_empty, fresh_k_not_N, fresh_k_not_P, or_false, not_false_eq_true]
  have freeVariableCertificate2 :
    k ∉
      ((Wff.imp (syn_wa (syn_wne (syn_cplc (.cv m) N) (syn_c0))
            (.classEq (syn_cplc (.cv m) N) (syn_cplc (.cv m) P))) (.classEq N P))).fv :=
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
      ((Wff.imp (syn_wa (syn_wne (syn_cplc (syn_c0c) N) (syn_c0))
            (.classEq (syn_cplc (syn_c0c) N) (syn_cplc (syn_c0c) P))) (.classEq N P))).fv :=
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
      ((Wff.imp (syn_wa (syn_wne (syn_cplc M N) (syn_c0))
            (.classEq (syn_cplc M N) (syn_cplc M P))) (.classEq N P))).fv :=
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
      ((Wff.imp (syn_wa (syn_wne (syn_cplc (syn_cplc (.cv k) N) (syn_c1c)) (syn_c0))
            (.classEq (syn_cplc (syn_cplc (.cv k) N) (syn_c1c))
              (syn_cplc (syn_cplc (.cv k) P) (syn_c1c)))) (.classEq N P))).fv :=
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
    @g_findsd
      (.imp (syn_wa (syn_wne (syn_cplc (.cv m) N) (syn_c0))
          (.classEq (syn_cplc (.cv m) N) (syn_cplc (.cv m) P))) (.classEq N P))
      (.imp (syn_wa (syn_wne (syn_cplc (syn_c0c) N) (syn_c0))
          (.classEq (syn_cplc (syn_c0c) N) (syn_cplc (syn_c0c) P))) (.classEq N P))
      (.imp (syn_wa (syn_wne (syn_cplc (.cv k) N) (syn_c0))
          (.classEq (syn_cplc (.cv k) N) (syn_cplc (.cv k) P))) (.classEq N P))
      (.imp (syn_wa (syn_wne (syn_cplc (syn_cplc (.cv k) N) (syn_c1c)) (syn_c0))
          (.classEq (syn_cplc (syn_cplc (.cv k) N) (syn_c1c))
            (syn_cplc (syn_cplc (.cv k) P) (syn_c1c)))) (.classEq N P))
      (.imp (syn_wa (syn_wne (syn_cplc M N) (syn_c0)) (.classEq (syn_cplc M N) (syn_cplc M P)))
        (.classEq N P))
      (syn_wa (.classMem N (syn_cnnc)) (.classMem P (syn_cnnc))) m k M (syn_cvv)
      (by exact (show m ∉ (M).fv from (by exact fresh_m_not_M))) freeVariableCertificate0
      freeVariableCertificate1 freeVariableCertificate2 freeVariableCertificate3
      freeVariableCertificate4 freeVariableCertificate5
      (show m ≠ k from (by exact fresh_m_ne_k)) p0000 p0006 p0012 p0022 p0028 p0034 p0051
  have p0053 :=
    @g_n_3impb (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)) (.classMem P (syn_cnnc))
      (.imp (syn_wa (syn_wne (syn_cplc M N) (syn_c0)) (.classEq (syn_cplc M N) (syn_cplc M P)))
        (.classEq N P))
      p0052
  have p0054 :=
    @g_expdimp
      (syn_w3a (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)) (.classMem P (syn_cnnc)))
      (syn_wne (syn_cplc M N) (syn_c0)) (.classEq (syn_cplc M N) (syn_cplc M P))
      (.classEq N P) p0053
  have p0055 := @g_addceq2 N P M
  have p0056 :=
    @g_impbid1
      (syn_wa (syn_w3a (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))
          (.classMem P (syn_cnnc))) (syn_wne (syn_cplc M N) (syn_c0)))
      (.classEq (syn_cplc M N) (syn_cplc M P)) (.classEq N P) p0054 p0055
  exact p0056

@[expose]
noncomputable def g_nulge (A : Class) (V : Class) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem (syn_c0) (syn_cnnc)) (.classMem A V))
        (.classMem (syn_copk A (syn_c0)) (syn_clefin))) :=
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
  have p0000 := @g_addcnul1 A
  have p0001 := @g_eqcomi (syn_cplc A (syn_c0)) (syn_c0) p0000
  have p0002 := @g_addceq2 (.cv x) (syn_c0) A
  have p0003 :=
    @g_eqeq2d (.classEq (.cv x) (syn_c0)) (syn_cplc A (.cv x)) (syn_cplc A (syn_c0))
      (syn_c0) p0002
  have freeVariableCertificate0 : x ∉ ((Wff.classEq (syn_c0) (syn_cplc A (syn_c0)))).fv :=
    by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, Finset.mem_union,
      Finset.notMem_empty, fresh_x_not_A, or_false, not_false_eq_true]
  have p0004 :=
    @g_rspcev (.classEq (syn_c0) (syn_cplc A (.cv x)))
      (.classEq (syn_c0) (syn_cplc A (syn_c0))) x (syn_c0) (syn_cnnc)
      (by
        exact
          (show x ∉ ((syn_c0)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0];
              exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
      (by
        exact
          (show x ∉ ((syn_cnnc)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc];
              exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
      freeVariableCertificate0 p0003
  have p0005 :=
    @g_mpan2 (.classMem (syn_c0) (syn_cnnc)) (.classEq (syn_c0) (syn_cplc A (syn_c0)))
      (syn_wrex x (syn_cnnc) (.classEq (syn_c0) (syn_cplc A (.cv x)))) p0001 p0004
  have p0006 :=
    @g_adantr (.classMem (syn_c0) (syn_cnnc))
      (syn_wrex x (syn_cnnc) (.classEq (syn_c0) (syn_cplc A (.cv x)))) (.classMem A V)
      p0005
  have p0007 :=
    @g_opklefing x A (syn_c0) V (syn_cnnc)
      (by exact (show x ∉ (A).fv from (by exact fresh_x_not_A)))
      (by
        exact
          (show x ∉ ((syn_c0)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0];
              exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
  have p0008 :=
    @g_ancoms (.classMem A V) (.classMem (syn_c0) (syn_cnnc))
      (syn_wb (.classMem (syn_copk A (syn_c0)) (syn_clefin))
        (syn_wrex x (syn_cnnc) (.classEq (syn_c0) (syn_cplc A (.cv x)))))
      p0007
  have p0009 :=
    @g_mpbird (syn_wa (.classMem (syn_c0) (syn_cnnc)) (.classMem A V))
      (.classMem (syn_copk A (syn_c0)) (syn_clefin))
      (syn_wrex x (syn_cnnc) (.classEq (syn_c0) (syn_cplc A (.cv x)))) p0006 p0008
  exact p0009

@[expose]
noncomputable def g_ltfinirr (A : Class) :
    Nominal.NPrf
      (.imp (.classMem A (syn_cnnc)) (.neg (.classMem (syn_copk A A) (syn_cltfin)))) :=
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
  have p0000 := @g_n_0cnsuc (.cv x)
  have p0001 := @g_necomi (syn_cplc (.cv x) (syn_c1c)) (syn_c0c) p0000
  have p0002 := (Nominal.biimpRefl (syn_wne (syn_c0c) (syn_cplc (.cv x) (syn_c1c))))
  have p0003 :=
    @g_mpbi (syn_wne (syn_c0c) (syn_cplc (.cv x) (syn_c1c)))
      (.neg (.classEq (syn_c0c) (syn_cplc (.cv x) (syn_c1c)))) p0001 p0002
  have p0004 := @g_addcid1 A
  have p0005 := @g_eqcomi (syn_cplc A (syn_c0c)) A p0004
  have p0006 := @g_addcass A (.cv x) (syn_c1c)
  have p0007 :=
    @g_eqeq12i A (syn_cplc A (syn_c0c)) (syn_cplc (syn_cplc A (.cv x)) (syn_c1c))
      (syn_cplc A (syn_cplc (.cv x) (syn_c1c))) p0005 p0006
  have p0008 :=
    @g_simpll (.classMem A (syn_cnnc)) (syn_wne A (syn_c0)) (.classMem (.cv x) (syn_cnnc))
  have p0009 := @g_peano1
  have p0010 :=
    @g_a1i (.classMem (syn_c0c) (syn_cnnc))
      (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wne A (syn_c0)))
        (.classMem (.cv x) (syn_cnnc)))
      p0009
  have p0011 := @g_peano2 (.cv x)
  have p0012 :=
    @g_adantl (.classMem (.cv x) (syn_cnnc))
      (.classMem (syn_cplc (.cv x) (syn_c1c)) (syn_cnnc))
      (syn_wa (.classMem A (syn_cnnc)) (syn_wne A (syn_c0))) p0011
  have p0013 := @g_neeq1i (syn_cplc A (syn_c0c)) A (syn_c0) p0004
  have p0014 :=
    @g_biimpri (syn_wne (syn_cplc A (syn_c0c)) (syn_c0)) (syn_wne A (syn_c0)) p0013
  have p0015 :=
    @g_ad2antlr (syn_wne A (syn_c0)) (syn_wne (syn_cplc A (syn_c0c)) (syn_c0))
      (.classMem A (syn_cnnc)) (.classMem (.cv x) (syn_cnnc)) p0014
  have p0016 := @g_preaddccan2 (syn_cplc (.cv x) (syn_c1c)) A (syn_c0c)
  have p0017 :=
    @g_syl31anc
      (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wne A (syn_c0)))
        (.classMem (.cv x) (syn_cnnc)))
      (.classMem A (syn_cnnc)) (.classMem (syn_c0c) (syn_cnnc))
      (.classMem (syn_cplc (.cv x) (syn_c1c)) (syn_cnnc))
      (syn_wne (syn_cplc A (syn_c0c)) (syn_c0))
      (syn_wb (.classEq (syn_cplc A (syn_c0c)) (syn_cplc A (syn_cplc (.cv x) (syn_c1c))))
        (.classEq (syn_c0c) (syn_cplc (.cv x) (syn_c1c))))
      p0008 p0010 p0012 p0015 p0016
  have p0018 :=
    @g_syl5bb (.classEq A (syn_cplc (syn_cplc A (.cv x)) (syn_c1c)))
      (.classEq (syn_cplc A (syn_c0c)) (syn_cplc A (syn_cplc (.cv x) (syn_c1c))))
      (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wne A (syn_c0)))
        (.classMem (.cv x) (syn_cnnc)))
      (.classEq (syn_c0c) (syn_cplc (.cv x) (syn_c1c))) p0007 p0017
  have p0019 :=
    @g_mtbiri
      (syn_wa (syn_wa (.classMem A (syn_cnnc)) (syn_wne A (syn_c0)))
        (.classMem (.cv x) (syn_cnnc)))
      (.classEq A (syn_cplc (syn_cplc A (.cv x)) (syn_c1c)))
      (.classEq (syn_c0c) (syn_cplc (.cv x) (syn_c1c))) p0003 p0018
  have freeVariableCertificate0 :
    x ∉ ((syn_wa (.classMem A (syn_cnnc)) (syn_wne A (syn_c0)))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union,
      Finset.notMem_empty, fresh_x_not_A, or_false, not_false_eq_true]
  have p0020 :=
    @g_nrexdv (syn_wa (.classMem A (syn_cnnc)) (syn_wne A (syn_c0)))
      (.classEq A (syn_cplc (syn_cplc A (.cv x)) (syn_c1c))) x (syn_cnnc)
      freeVariableCertificate0 p0019
  have p0021 :=
    @g_ex (.classMem A (syn_cnnc)) (syn_wne A (syn_c0))
      (.neg (syn_wrex x (syn_cnnc) (.classEq A (syn_cplc (syn_cplc A (.cv x)) (syn_c1c)))))
      p0020
  have p0022 :=
    @g_imnan (syn_wne A (syn_c0))
      (syn_wrex x (syn_cnnc) (.classEq A (syn_cplc (syn_cplc A (.cv x)) (syn_c1c))))
  have p0023 :=
    @g_sylib (.classMem A (syn_cnnc))
      (.imp (syn_wne A (syn_c0)) (.neg
          (syn_wrex x (syn_cnnc) (.classEq A (syn_cplc (syn_cplc A (.cv x)) (syn_c1c))))))
      (.neg (syn_wa (syn_wne A (syn_c0))
          (syn_wrex x (syn_cnnc) (.classEq A (syn_cplc (syn_cplc A (.cv x)) (syn_c1c))))))
      p0021 p0022
  have p0024 :=
    @g_opkltfing x A A (syn_cnnc) (syn_cnnc)
      (by exact (show x ∉ (A).fv from (by exact fresh_x_not_A)))
      (by exact (show x ∉ (A).fv from (by exact fresh_x_not_A)))
  have p0025 :=
    @g_anidms (.classMem A (syn_cnnc))
      (syn_wb (.classMem (syn_copk A A) (syn_cltfin)) (syn_wa (syn_wne A (syn_c0))
          (syn_wrex x (syn_cnnc) (.classEq A (syn_cplc (syn_cplc A (.cv x)) (syn_c1c))))))
      p0024
  have p0026 :=
    @g_mtbird (.classMem A (syn_cnnc)) (.classMem (syn_copk A A) (syn_cltfin))
      (syn_wa (syn_wne A (syn_c0))
        (syn_wrex x (syn_cnnc) (.classEq A (syn_cplc (syn_cplc A (.cv x)) (syn_c1c)))))
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

@[expose]
noncomputable def g_leltfintr (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf
      (.imp (syn_w3a (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)) (.classMem C (syn_cnnc)))
        (.imp (syn_wa (.classMem (syn_copk A B) (syn_clefin))
            (.classMem (syn_copk B C) (syn_cltfin)))
          (.classMem (syn_copk A C) (syn_cltfin)))) :=
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
    @g_opklefing x A B (syn_cnnc) (syn_cnnc)
      (by exact (show x ∉ (A).fv from (by exact fresh_x_not_A)))
      (by exact (show x ∉ (B).fv from (by exact fresh_x_not_B)))
  have p0001 :=
    @g_n_3adant3 (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))
      (syn_wb (.classMem (syn_copk A B) (syn_clefin))
        (syn_wrex x (syn_cnnc) (.classEq B (syn_cplc A (.cv x)))))
      (.classMem C (syn_cnnc)) p0000
  have p0002 := @g_addcnnul A (.cv x)
  have p0003 :=
    @g_simpld (syn_wne (syn_cplc A (.cv x)) (syn_c0)) (syn_wne A (syn_c0))
      (syn_wne (.cv x) (syn_c0)) p0002
  have p0004 :=
    @g_a1i (.imp (syn_wne (syn_cplc A (.cv x)) (syn_c0)) (syn_wne A (syn_c0)))
      (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem C (syn_cnnc)))
        (.classMem (.cv x) (syn_cnnc)))
      p0003
  have p0005 := @g_nncaddccl (.cv x) (.cv y)
  have p0006 :=
    @g_n_3adant1 (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc))
      (.classMem (syn_cplc (.cv x) (.cv y)) (syn_cnnc)) (.classMem A (syn_cnnc)) p0005
  have p0007 := @g_addcass A (.cv x) (.cv y)
  have p0008 :=
    @g_addceq1 (syn_cplc (syn_cplc A (.cv x)) (.cv y))
      (syn_cplc A (syn_cplc (.cv x) (.cv y))) (syn_c1c)
  have p0009 := Nominal.mp p0007 p0008
  have p0010 :=
    @g_a1i
      (.classEq (syn_cplc (syn_cplc (syn_cplc A (.cv x)) (.cv y)) (syn_c1c))
        (syn_cplc (syn_cplc A (syn_cplc (.cv x) (.cv y))) (syn_c1c)))
      (syn_w3a (.classMem A (syn_cnnc)) (.classMem (.cv x) (syn_cnnc))
        (.classMem (.cv y) (syn_cnnc)))
      p0009
  have p0011 := @g_addceq2 (.cv z) (syn_cplc (.cv x) (.cv y)) A
  have p0012 :=
    @g_addceq1 (syn_cplc A (.cv z)) (syn_cplc A (syn_cplc (.cv x) (.cv y))) (syn_c1c)
  have p0013 :=
    @g_syl (.classEq (.cv z) (syn_cplc (.cv x) (.cv y)))
      (.classEq (syn_cplc A (.cv z)) (syn_cplc A (syn_cplc (.cv x) (.cv y))))
      (.classEq (syn_cplc (syn_cplc A (.cv z)) (syn_c1c))
        (syn_cplc (syn_cplc A (syn_cplc (.cv x) (.cv y))) (syn_c1c)))
      p0011 p0012
  have p0014 :=
    @g_eqeq2d (.classEq (.cv z) (syn_cplc (.cv x) (.cv y)))
      (syn_cplc (syn_cplc A (.cv z)) (syn_c1c))
      (syn_cplc (syn_cplc A (syn_cplc (.cv x) (.cv y))) (syn_c1c))
      (syn_cplc (syn_cplc (syn_cplc A (.cv x)) (.cv y)) (syn_c1c)) p0013
  have freeVariableCertificate0 : z ∉ ((syn_cplc (.cv x) (.cv y))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      fresh_z_ne_x, fresh_z_ne_y, or_false, not_false_eq_true]
  have freeVariableCertificate1 :
    z ∉
      ((Wff.classEq (syn_cplc (syn_cplc (syn_cplc A (.cv x)) (.cv y)) (syn_c1c))
          (syn_cplc (syn_cplc A (syn_cplc (.cv x) (.cv y))) (syn_c1c)))).fv :=
    by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_z_not_A, fresh_z_ne_x,
      fresh_z_ne_y, or_false, not_false_eq_true]
  have p0015 :=
    @g_rspcev
      (.classEq (syn_cplc (syn_cplc (syn_cplc A (.cv x)) (.cv y)) (syn_c1c))
        (syn_cplc (syn_cplc A (.cv z)) (syn_c1c)))
      (.classEq (syn_cplc (syn_cplc (syn_cplc A (.cv x)) (.cv y)) (syn_c1c))
        (syn_cplc (syn_cplc A (syn_cplc (.cv x) (.cv y))) (syn_c1c)))
      z (syn_cplc (.cv x) (.cv y)) (syn_cnnc) freeVariableCertificate0
      (by
        exact
          (show z ∉ ((syn_cnnc)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc];
              exact (show z ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
      freeVariableCertificate1 p0014
  have p0016 :=
    @g_syl2anc
      (syn_w3a (.classMem A (syn_cnnc)) (.classMem (.cv x) (syn_cnnc))
        (.classMem (.cv y) (syn_cnnc)))
      (.classMem (syn_cplc (.cv x) (.cv y)) (syn_cnnc))
      (.classEq (syn_cplc (syn_cplc (syn_cplc A (.cv x)) (.cv y)) (syn_c1c))
        (syn_cplc (syn_cplc A (syn_cplc (.cv x) (.cv y))) (syn_c1c)))
      (syn_wrex z (syn_cnnc)
        (.classEq (syn_cplc (syn_cplc (syn_cplc A (.cv x)) (.cv y)) (syn_c1c))
          (syn_cplc (syn_cplc A (.cv z)) (syn_c1c))))
      p0006 p0010 p0015
  have p0017 :=
    @g_eqeq1 C (syn_cplc (syn_cplc (syn_cplc A (.cv x)) (.cv y)) (syn_c1c))
      (syn_cplc (syn_cplc A (.cv z)) (syn_c1c))
  have freeVariableCertificate2 :
    z ∉
      ((Wff.classEq C (syn_cplc (syn_cplc (syn_cplc A (.cv x)) (.cv y)) (syn_c1c)))).fv :=
    by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_z_not_C, fresh_z_not_A,
      fresh_z_ne_x, fresh_z_ne_y, or_false, not_false_eq_true]
  have p0018 :=
    @g_rexbidv (.classEq C (syn_cplc (syn_cplc (syn_cplc A (.cv x)) (.cv y)) (syn_c1c)))
      (.classEq C (syn_cplc (syn_cplc A (.cv z)) (syn_c1c)))
      (.classEq (syn_cplc (syn_cplc (syn_cplc A (.cv x)) (.cv y)) (syn_c1c))
        (syn_cplc (syn_cplc A (.cv z)) (syn_c1c)))
      z (syn_cnnc) freeVariableCertificate2 p0017
  have p0019 :=
    @g_syl5ibrcom
      (syn_w3a (.classMem A (syn_cnnc)) (.classMem (.cv x) (syn_cnnc))
        (.classMem (.cv y) (syn_cnnc)))
      (syn_wrex z (syn_cnnc) (.classEq C (syn_cplc (syn_cplc A (.cv z)) (syn_c1c))))
      (.classEq C (syn_cplc (syn_cplc (syn_cplc A (.cv x)) (.cv y)) (syn_c1c)))
      (syn_wrex z (syn_cnnc)
        (.classEq (syn_cplc (syn_cplc (syn_cplc A (.cv x)) (.cv y)) (syn_c1c))
          (syn_cplc (syn_cplc A (.cv z)) (syn_c1c))))
      p0016 p0018
  have p0020 :=
    @g_n_3expa (.classMem A (syn_cnnc)) (.classMem (.cv x) (syn_cnnc))
      (.classMem (.cv y) (syn_cnnc))
      (.imp (.classEq C (syn_cplc (syn_cplc (syn_cplc A (.cv x)) (.cv y)) (syn_c1c)))
        (syn_wrex z (syn_cnnc) (.classEq C (syn_cplc (syn_cplc A (.cv z)) (syn_c1c)))))
      p0019
  have p0021 :=
    @g_adantllr (.classMem A (syn_cnnc)) (.classMem (.cv x) (syn_cnnc))
      (.classMem (.cv y) (syn_cnnc))
      (.imp (.classEq C (syn_cplc (syn_cplc (syn_cplc A (.cv x)) (.cv y)) (syn_c1c)))
        (syn_wrex z (syn_cnnc) (.classEq C (syn_cplc (syn_cplc A (.cv z)) (syn_c1c)))))
      (.classMem C (syn_cnnc)) p0020
  have freeVariableCertificate3 :
    y ∉
      ((syn_wrex z (syn_cnnc) (.classEq C (syn_cplc (syn_cplc A (.cv z)) (syn_c1c))))).fv :=
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
      ((syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem C (syn_cnnc)))
          (.classMem (.cv x) (syn_cnnc)))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      Finset.notMem_empty, fresh_y_not_A, fresh_y_not_C, fresh_y_ne_x, or_false,
      not_false_eq_true]
  have p0022 :=
    @g_rexlimdva
      (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem C (syn_cnnc)))
        (.classMem (.cv x) (syn_cnnc)))
      (.classEq C (syn_cplc (syn_cplc (syn_cplc A (.cv x)) (.cv y)) (syn_c1c)))
      (syn_wrex z (syn_cnnc) (.classEq C (syn_cplc (syn_cplc A (.cv z)) (syn_c1c)))) y
      (syn_cnnc) freeVariableCertificate3 freeVariableCertificate4 p0021
  have p0023 :=
    @g_anim12d
      (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem C (syn_cnnc)))
        (.classMem (.cv x) (syn_cnnc)))
      (syn_wne (syn_cplc A (.cv x)) (syn_c0)) (syn_wne A (syn_c0))
      (syn_wrex y (syn_cnnc)
        (.classEq C (syn_cplc (syn_cplc (syn_cplc A (.cv x)) (.cv y)) (syn_c1c))))
      (syn_wrex z (syn_cnnc) (.classEq C (syn_cplc (syn_cplc A (.cv z)) (syn_c1c)))) p0004
      p0022
  have p0024 := @g_addcexg A (.cv x) (syn_cnnc) (syn_cnnc)
  have p0025 :=
    @g_adantlr (.classMem A (syn_cnnc)) (.classMem (.cv x) (syn_cnnc))
      (.classMem (syn_cplc A (.cv x)) (syn_cvv)) (.classMem C (syn_cnnc)) p0024
  have p0026 :=
    @g_simplr (.classMem A (syn_cnnc)) (.classMem C (syn_cnnc))
      (.classMem (.cv x) (syn_cnnc))
  have freeVariableCertificate5 : y ∉ ((syn_cplc A (.cv x))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      fresh_y_not_A, fresh_y_ne_x, or_false, not_false_eq_true]
  have p0027 :=
    @g_opkltfing y (syn_cplc A (.cv x)) C (syn_cvv) (syn_cnnc) freeVariableCertificate5
      (by exact (show y ∉ (C).fv from (by exact fresh_y_not_C)))
  have p0028 :=
    @g_syl2anc
      (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem C (syn_cnnc)))
        (.classMem (.cv x) (syn_cnnc)))
      (.classMem (syn_cplc A (.cv x)) (syn_cvv)) (.classMem C (syn_cnnc))
      (syn_wb (.classMem (syn_copk (syn_cplc A (.cv x)) C) (syn_cltfin))
        (syn_wa (syn_wne (syn_cplc A (.cv x)) (syn_c0)) (syn_wrex y (syn_cnnc)
            (.classEq C (syn_cplc (syn_cplc (syn_cplc A (.cv x)) (.cv y)) (syn_c1c))))))
      p0025 p0026 p0027
  have p0029 :=
    @g_opkltfing z A C (syn_cnnc) (syn_cnnc)
      (by exact (show z ∉ (A).fv from (by exact fresh_z_not_A)))
      (by exact (show z ∉ (C).fv from (by exact fresh_z_not_C)))
  have p0030 :=
    @g_adantr (syn_wa (.classMem A (syn_cnnc)) (.classMem C (syn_cnnc)))
      (syn_wb (.classMem (syn_copk A C) (syn_cltfin)) (syn_wa (syn_wne A (syn_c0))
          (syn_wrex z (syn_cnnc) (.classEq C (syn_cplc (syn_cplc A (.cv z)) (syn_c1c))))))
      (.classMem (.cv x) (syn_cnnc)) p0029
  have p0031 :=
    @g_n_3imtr4d
      (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem C (syn_cnnc)))
        (.classMem (.cv x) (syn_cnnc)))
      (syn_wa (syn_wne (syn_cplc A (.cv x)) (syn_c0)) (syn_wrex y (syn_cnnc)
          (.classEq C (syn_cplc (syn_cplc (syn_cplc A (.cv x)) (.cv y)) (syn_c1c)))))
      (syn_wa (syn_wne A (syn_c0))
        (syn_wrex z (syn_cnnc) (.classEq C (syn_cplc (syn_cplc A (.cv z)) (syn_c1c)))))
      (.classMem (syn_copk (syn_cplc A (.cv x)) C) (syn_cltfin))
      (.classMem (syn_copk A C) (syn_cltfin)) p0023 p0028 p0030
  have p0032 := @g_opkeq1 B (syn_cplc A (.cv x)) C
  have p0033 :=
    @g_eleq1d (.classEq B (syn_cplc A (.cv x))) (syn_copk B C)
      (syn_copk (syn_cplc A (.cv x)) C) (syn_cltfin) p0032
  have p0034 :=
    @g_imbi1d (.classEq B (syn_cplc A (.cv x))) (.classMem (syn_copk B C) (syn_cltfin))
      (.classMem (syn_copk (syn_cplc A (.cv x)) C) (syn_cltfin))
      (.classMem (syn_copk A C) (syn_cltfin)) p0033
  have p0035 :=
    @g_syl5ibrcom
      (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem C (syn_cnnc)))
        (.classMem (.cv x) (syn_cnnc)))
      (.imp (.classMem (syn_copk B C) (syn_cltfin)) (.classMem (syn_copk A C) (syn_cltfin)))
      (.classEq B (syn_cplc A (.cv x)))
      (.imp (.classMem (syn_copk (syn_cplc A (.cv x)) C) (syn_cltfin))
        (.classMem (syn_copk A C) (syn_cltfin)))
      p0031 p0034
  have freeVariableCertificate6 :
    x ∉
      ((Wff.imp (.classMem (syn_copk B C) (syn_cltfin))
          (.classMem (syn_copk A C) (syn_cltfin)))).fv :=
    by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cltfin, Finset.mem_union,
      Finset.notMem_empty, fresh_x_not_B, fresh_x_not_C, fresh_x_not_A, or_false,
      not_false_eq_true]
  have freeVariableCertificate7 :
    x ∉ ((syn_wa (.classMem A (syn_cnnc)) (.classMem C (syn_cnnc)))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union,
      Finset.notMem_empty, fresh_x_not_A, fresh_x_not_C, or_false, not_false_eq_true]
  have p0036 :=
    @g_rexlimdva (syn_wa (.classMem A (syn_cnnc)) (.classMem C (syn_cnnc)))
      (.classEq B (syn_cplc A (.cv x)))
      (.imp (.classMem (syn_copk B C) (syn_cltfin)) (.classMem (syn_copk A C) (syn_cltfin)))
      x (syn_cnnc) freeVariableCertificate6 freeVariableCertificate7 p0035
  have p0037 :=
    @g_n_3adant2 (.classMem A (syn_cnnc)) (.classMem C (syn_cnnc))
      (.imp (syn_wrex x (syn_cnnc) (.classEq B (syn_cplc A (.cv x))))
        (.imp (.classMem (syn_copk B C) (syn_cltfin)) (.classMem (syn_copk A C) (syn_cltfin))))
      (.classMem B (syn_cnnc)) p0036
  have p0038 :=
    @g_sylbid
      (syn_w3a (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)) (.classMem C (syn_cnnc)))
      (.classMem (syn_copk A B) (syn_clefin))
      (syn_wrex x (syn_cnnc) (.classEq B (syn_cplc A (.cv x))))
      (.imp (.classMem (syn_copk B C) (syn_cltfin)) (.classMem (syn_copk A C) (syn_cltfin)))
      p0001 p0037
  have p0039 :=
    @g_imp3a
      (syn_w3a (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)) (.classMem C (syn_cnnc)))
      (.classMem (syn_copk A B) (syn_clefin)) (.classMem (syn_copk B C) (syn_cltfin))
      (.classMem (syn_copk A C) (syn_cltfin)) p0038
  exact p0039

@[expose]
noncomputable def g_ltfintr (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf
      (.imp (syn_w3a (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)) (.classMem C (syn_cnnc)))
        (.imp (syn_wa (.classMem (syn_copk A B) (syn_cltfin))
            (.classMem (syn_copk B C) (syn_cltfin)))
          (.classMem (syn_copk A C) (syn_cltfin)))) :=
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
    @g_an4 (syn_wne A (syn_c0))
      (syn_wrex x (syn_cnnc) (.classEq B (syn_cplc (syn_cplc A (.cv x)) (syn_c1c))))
      (syn_wne B (syn_c0))
      (syn_wrex y (syn_cnnc) (.classEq C (syn_cplc (syn_cplc B (.cv y)) (syn_c1c))))
  have p0001 := @g_simpl (syn_wne A (syn_c0)) (syn_wne B (syn_c0))
  have p0002 :=
    @g_a1i (.imp (syn_wa (syn_wne A (syn_c0)) (syn_wne B (syn_c0))) (syn_wne A (syn_c0)))
      (syn_w3a (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)) (.classMem C (syn_cnnc)))
      p0001
  have freeVariableCertificate0 :
    y ∉ ((Wff.classEq B (syn_cplc (syn_cplc A (.cv x)) (syn_c1c)))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_y_not_B, fresh_y_not_A,
      fresh_y_ne_x, or_false, not_false_eq_true]
  have freeVariableCertificate1 :
    x ∉ ((Wff.classEq C (syn_cplc (syn_cplc B (.cv y)) (syn_c1c)))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_x_not_C, fresh_x_not_B,
      fresh_x_ne_y, or_false, not_false_eq_true]
  have p0003 :=
    @g_reeanv (.classEq B (syn_cplc (syn_cplc A (.cv x)) (syn_c1c)))
      (.classEq C (syn_cplc (syn_cplc B (.cv y)) (syn_c1c))) x y (syn_cnnc) (syn_cnnc)
      (by
        exact
          (show y ∉ ((syn_cnnc)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc];
              exact (show y ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
      (by
        exact
          (show x ∉ ((syn_cnnc)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc];
              exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
      freeVariableCertificate0 freeVariableCertificate1
      (show x ≠ y from (by exact fresh_x_ne_y))
  have p0004 := @g_addccom (syn_c1c) (.cv y)
  have p0005 := @g_peano2 (.cv y)
  have p0006 :=
    @g_syl5eqel (.classMem (.cv y) (syn_cnnc)) (syn_cplc (syn_c1c) (.cv y))
      (syn_cplc (.cv y) (syn_c1c)) (syn_cnnc) p0004 p0005
  have p0007 := @g_nncaddccl (.cv x) (syn_cplc (syn_c1c) (.cv y))
  have p0008 :=
    @g_sylan2 (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv x) (syn_cnnc))
      (.classMem (syn_cplc (syn_c1c) (.cv y)) (syn_cnnc))
      (.classMem (syn_cplc (.cv x) (syn_cplc (syn_c1c) (.cv y))) (syn_cnnc)) p0006 p0007
  have p0009 :=
    @g_adantl (syn_wa (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc)))
      (.classMem (syn_cplc (.cv x) (syn_cplc (syn_c1c) (.cv y))) (syn_cnnc))
      (syn_w3a (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)) (.classMem C (syn_cnnc)))
      p0008
  have p0010 := @g_addceq1 B (syn_cplc (syn_cplc A (.cv x)) (syn_c1c)) (.cv y)
  have p0011 :=
    @g_addceq1 (syn_cplc B (.cv y))
      (syn_cplc (syn_cplc (syn_cplc A (.cv x)) (syn_c1c)) (.cv y)) (syn_c1c)
  have p0012 :=
    @g_syl (.classEq B (syn_cplc (syn_cplc A (.cv x)) (syn_c1c)))
      (.classEq (syn_cplc B (.cv y))
        (syn_cplc (syn_cplc (syn_cplc A (.cv x)) (syn_c1c)) (.cv y)))
      (.classEq (syn_cplc (syn_cplc B (.cv y)) (syn_c1c))
        (syn_cplc (syn_cplc (syn_cplc (syn_cplc A (.cv x)) (syn_c1c)) (.cv y)) (syn_c1c)))
      p0010 p0011
  have p0013 :=
    @g_eqeq2d (.classEq B (syn_cplc (syn_cplc A (.cv x)) (syn_c1c)))
      (syn_cplc (syn_cplc B (.cv y)) (syn_c1c))
      (syn_cplc (syn_cplc (syn_cplc (syn_cplc A (.cv x)) (syn_c1c)) (.cv y)) (syn_c1c)) C
      p0012
  have p0014 :=
    @g_biimpa (.classEq B (syn_cplc (syn_cplc A (.cv x)) (syn_c1c)))
      (.classEq C (syn_cplc (syn_cplc B (.cv y)) (syn_c1c)))
      (.classEq C
        (syn_cplc (syn_cplc (syn_cplc (syn_cplc A (.cv x)) (syn_c1c)) (.cv y)) (syn_c1c)))
      p0013
  have p0015 := @g_addceq2 (.cv z) (syn_cplc (.cv x) (syn_cplc (syn_c1c) (.cv y))) A
  have p0016 := @g_addcass (syn_cplc A (.cv x)) (syn_c1c) (.cv y)
  have p0017 := @g_addcass A (.cv x) (syn_cplc (syn_c1c) (.cv y))
  have p0018 :=
    @g_eqtri (syn_cplc (syn_cplc (syn_cplc A (.cv x)) (syn_c1c)) (.cv y))
      (syn_cplc (syn_cplc A (.cv x)) (syn_cplc (syn_c1c) (.cv y)))
      (syn_cplc A (syn_cplc (.cv x) (syn_cplc (syn_c1c) (.cv y)))) p0016 p0017
  have p0019 :=
    @g_syl6eqr (.classEq (.cv z) (syn_cplc (.cv x) (syn_cplc (syn_c1c) (.cv y))))
      (syn_cplc A (.cv z)) (syn_cplc A (syn_cplc (.cv x) (syn_cplc (syn_c1c) (.cv y))))
      (syn_cplc (syn_cplc (syn_cplc A (.cv x)) (syn_c1c)) (.cv y)) p0015 p0018
  have p0020 :=
    @g_addceq1 (syn_cplc A (.cv z))
      (syn_cplc (syn_cplc (syn_cplc A (.cv x)) (syn_c1c)) (.cv y)) (syn_c1c)
  have p0021 :=
    @g_syl (.classEq (.cv z) (syn_cplc (.cv x) (syn_cplc (syn_c1c) (.cv y))))
      (.classEq (syn_cplc A (.cv z))
        (syn_cplc (syn_cplc (syn_cplc A (.cv x)) (syn_c1c)) (.cv y)))
      (.classEq (syn_cplc (syn_cplc A (.cv z)) (syn_c1c))
        (syn_cplc (syn_cplc (syn_cplc (syn_cplc A (.cv x)) (syn_c1c)) (.cv y)) (syn_c1c)))
      p0019 p0020
  have p0022 :=
    @g_eqeq2d (.classEq (.cv z) (syn_cplc (.cv x) (syn_cplc (syn_c1c) (.cv y))))
      (syn_cplc (syn_cplc A (.cv z)) (syn_c1c))
      (syn_cplc (syn_cplc (syn_cplc (syn_cplc A (.cv x)) (syn_c1c)) (.cv y)) (syn_c1c)) C
      p0021
  have freeVariableCertificate2 :
    z ∉ ((syn_cplc (.cv x) (syn_cplc (syn_c1c) (.cv y)))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_z_ne_x, fresh_z_ne_y, or_false,
      not_false_eq_true]
  have freeVariableCertificate3 :
    z ∉
      ((Wff.classEq C (syn_cplc (syn_cplc (syn_cplc (syn_cplc A (.cv x)) (syn_c1c)) (.cv y))
            (syn_c1c)))).fv :=
    by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_z_not_C, fresh_z_not_A,
      fresh_z_ne_x, fresh_z_ne_y, or_false, not_false_eq_true]
  have p0023 :=
    @g_rspcev (.classEq C (syn_cplc (syn_cplc A (.cv z)) (syn_c1c)))
      (.classEq C
        (syn_cplc (syn_cplc (syn_cplc (syn_cplc A (.cv x)) (syn_c1c)) (.cv y)) (syn_c1c)))
      z (syn_cplc (.cv x) (syn_cplc (syn_c1c) (.cv y))) (syn_cnnc)
      freeVariableCertificate2
      (by
        exact
          (show z ∉ ((syn_cnnc)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc];
              exact (show z ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
      freeVariableCertificate3 p0022
  have p0024 :=
    @g_ex (.classMem (syn_cplc (.cv x) (syn_cplc (syn_c1c) (.cv y))) (syn_cnnc))
      (.classEq C
        (syn_cplc (syn_cplc (syn_cplc (syn_cplc A (.cv x)) (syn_c1c)) (.cv y)) (syn_c1c)))
      (syn_wrex z (syn_cnnc) (.classEq C (syn_cplc (syn_cplc A (.cv z)) (syn_c1c)))) p0023
  have p0025 :=
    @g_syl2im
      (syn_wa (syn_w3a (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))
          (.classMem C (syn_cnnc)))
        (syn_wa (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv y) (syn_cnnc))))
      (.classMem (syn_cplc (.cv x) (syn_cplc (syn_c1c) (.cv y))) (syn_cnnc))
      (syn_wa (.classEq B (syn_cplc (syn_cplc A (.cv x)) (syn_c1c)))
        (.classEq C (syn_cplc (syn_cplc B (.cv y)) (syn_c1c))))
      (.classEq C
        (syn_cplc (syn_cplc (syn_cplc (syn_cplc A (.cv x)) (syn_c1c)) (.cv y)) (syn_c1c)))
      (syn_wrex z (syn_cnnc) (.classEq C (syn_cplc (syn_cplc A (.cv z)) (syn_c1c)))) p0009
      p0014 p0024
  have freeVariableCertificate4 :
    x ∉
      ((syn_wrex z (syn_cnnc) (.classEq C (syn_cplc (syn_cplc A (.cv z)) (syn_c1c))))).fv :=
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
      ((syn_wrex z (syn_cnnc) (.classEq C (syn_cplc (syn_cplc A (.cv z)) (syn_c1c))))).fv :=
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
      ((syn_w3a (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))
          (.classMem C (syn_cnnc)))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union,
      Finset.notMem_empty, fresh_x_not_C, fresh_x_not_A, fresh_x_not_B, or_false,
      not_false_eq_true]
  have freeVariableCertificate7 :
    y ∉
      ((syn_w3a (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))
          (.classMem C (syn_cnnc)))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union,
      Finset.notMem_empty, fresh_y_not_C, fresh_y_not_A, fresh_y_not_B, or_false,
      not_false_eq_true]
  have p0026 :=
    @g_rexlimdvva
      (syn_w3a (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)) (.classMem C (syn_cnnc)))
      (syn_wa (.classEq B (syn_cplc (syn_cplc A (.cv x)) (syn_c1c)))
        (.classEq C (syn_cplc (syn_cplc B (.cv y)) (syn_c1c))))
      (syn_wrex z (syn_cnnc) (.classEq C (syn_cplc (syn_cplc A (.cv z)) (syn_c1c)))) x y
      (syn_cnnc) (syn_cnnc)
      (by
        exact
          (show y ∉ ((syn_cnnc)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc];
              exact (show y ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
      freeVariableCertificate4 freeVariableCertificate5 freeVariableCertificate6
      freeVariableCertificate7 (show x ≠ y from (by exact fresh_x_ne_y)) p0025
  have p0027 :=
    @g_syl5bir
      (syn_wa (syn_wrex x (syn_cnnc) (.classEq B (syn_cplc (syn_cplc A (.cv x)) (syn_c1c))))
        (syn_wrex y (syn_cnnc) (.classEq C (syn_cplc (syn_cplc B (.cv y)) (syn_c1c)))))
      (syn_wrex x (syn_cnnc) (syn_wrex y (syn_cnnc)
          (syn_wa (.classEq B (syn_cplc (syn_cplc A (.cv x)) (syn_c1c)))
            (.classEq C (syn_cplc (syn_cplc B (.cv y)) (syn_c1c))))))
      (syn_w3a (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)) (.classMem C (syn_cnnc)))
      (syn_wrex z (syn_cnnc) (.classEq C (syn_cplc (syn_cplc A (.cv z)) (syn_c1c)))) p0003
      p0026
  have p0028 :=
    @g_anim12d
      (syn_w3a (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)) (.classMem C (syn_cnnc)))
      (syn_wa (syn_wne A (syn_c0)) (syn_wne B (syn_c0))) (syn_wne A (syn_c0))
      (syn_wa (syn_wrex x (syn_cnnc) (.classEq B (syn_cplc (syn_cplc A (.cv x)) (syn_c1c))))
        (syn_wrex y (syn_cnnc) (.classEq C (syn_cplc (syn_cplc B (.cv y)) (syn_c1c)))))
      (syn_wrex z (syn_cnnc) (.classEq C (syn_cplc (syn_cplc A (.cv z)) (syn_c1c)))) p0002
      p0027
  have p0029 :=
    @g_syl5bi
      (syn_wa (syn_wa (syn_wne A (syn_c0))
          (syn_wrex x (syn_cnnc) (.classEq B (syn_cplc (syn_cplc A (.cv x)) (syn_c1c)))))
        (syn_wa (syn_wne B (syn_c0))
          (syn_wrex y (syn_cnnc) (.classEq C (syn_cplc (syn_cplc B (.cv y)) (syn_c1c))))))
      (syn_wa (syn_wa (syn_wne A (syn_c0)) (syn_wne B (syn_c0))) (syn_wa
          (syn_wrex x (syn_cnnc) (.classEq B (syn_cplc (syn_cplc A (.cv x)) (syn_c1c))))
          (syn_wrex y (syn_cnnc) (.classEq C (syn_cplc (syn_cplc B (.cv y)) (syn_c1c))))))
      (syn_w3a (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)) (.classMem C (syn_cnnc)))
      (syn_wa (syn_wne A (syn_c0))
        (syn_wrex z (syn_cnnc) (.classEq C (syn_cplc (syn_cplc A (.cv z)) (syn_c1c)))))
      p0000 p0028
  have p0030 :=
    @g_opkltfing x A B (syn_cnnc) (syn_cnnc)
      (by exact (show x ∉ (A).fv from (by exact fresh_x_not_A)))
      (by exact (show x ∉ (B).fv from (by exact fresh_x_not_B)))
  have p0031 :=
    @g_n_3adant3 (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))
      (syn_wb (.classMem (syn_copk A B) (syn_cltfin)) (syn_wa (syn_wne A (syn_c0))
          (syn_wrex x (syn_cnnc) (.classEq B (syn_cplc (syn_cplc A (.cv x)) (syn_c1c))))))
      (.classMem C (syn_cnnc)) p0030
  have p0032 :=
    @g_opkltfing y B C (syn_cnnc) (syn_cnnc)
      (by exact (show y ∉ (B).fv from (by exact fresh_y_not_B)))
      (by exact (show y ∉ (C).fv from (by exact fresh_y_not_C)))
  have p0033 :=
    @g_n_3adant1 (.classMem B (syn_cnnc)) (.classMem C (syn_cnnc))
      (syn_wb (.classMem (syn_copk B C) (syn_cltfin)) (syn_wa (syn_wne B (syn_c0))
          (syn_wrex y (syn_cnnc) (.classEq C (syn_cplc (syn_cplc B (.cv y)) (syn_c1c))))))
      (.classMem A (syn_cnnc)) p0032
  have p0034 :=
    @g_anbi12d
      (syn_w3a (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)) (.classMem C (syn_cnnc)))
      (.classMem (syn_copk A B) (syn_cltfin))
      (syn_wa (syn_wne A (syn_c0))
        (syn_wrex x (syn_cnnc) (.classEq B (syn_cplc (syn_cplc A (.cv x)) (syn_c1c)))))
      (.classMem (syn_copk B C) (syn_cltfin))
      (syn_wa (syn_wne B (syn_c0))
        (syn_wrex y (syn_cnnc) (.classEq C (syn_cplc (syn_cplc B (.cv y)) (syn_c1c)))))
      p0031 p0033
  have p0035 :=
    @g_opkltfing z A C (syn_cnnc) (syn_cnnc)
      (by exact (show z ∉ (A).fv from (by exact fresh_z_not_A)))
      (by exact (show z ∉ (C).fv from (by exact fresh_z_not_C)))
  have p0036 :=
    @g_n_3adant2 (.classMem A (syn_cnnc)) (.classMem C (syn_cnnc))
      (syn_wb (.classMem (syn_copk A C) (syn_cltfin)) (syn_wa (syn_wne A (syn_c0))
          (syn_wrex z (syn_cnnc) (.classEq C (syn_cplc (syn_cplc A (.cv z)) (syn_c1c))))))
      (.classMem B (syn_cnnc)) p0035
  have p0037 :=
    @g_n_3imtr4d
      (syn_w3a (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)) (.classMem C (syn_cnnc)))
      (syn_wa (syn_wa (syn_wne A (syn_c0))
          (syn_wrex x (syn_cnnc) (.classEq B (syn_cplc (syn_cplc A (.cv x)) (syn_c1c)))))
        (syn_wa (syn_wne B (syn_c0))
          (syn_wrex y (syn_cnnc) (.classEq C (syn_cplc (syn_cplc B (.cv y)) (syn_c1c))))))
      (syn_wa (syn_wne A (syn_c0))
        (syn_wrex z (syn_cnnc) (.classEq C (syn_cplc (syn_cplc A (.cv z)) (syn_c1c)))))
      (syn_wa (.classMem (syn_copk A B) (syn_cltfin)) (.classMem (syn_copk B C) (syn_cltfin)))
      (.classMem (syn_copk A C) (syn_cltfin)) p0029 p0034 p0036
  exact p0037

@[expose]
noncomputable def g_ltfinasym (A : Class) (B : Class) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
        (.imp (.classMem (syn_copk A B) (syn_cltfin))
          (.neg (.classMem (syn_copk B A) (syn_cltfin))))) :=
  by
  have p0000 := @g_ltfinirr A
  have p0001 :=
    @g_ad2antrr (.classMem A (syn_cnnc)) (.neg (.classMem (syn_copk A A) (syn_cltfin)))
      (.classMem B (syn_cnnc)) (.classMem (syn_copk A B) (syn_cltfin)) p0000
  have p0002 := @g_ltfintr A B A
  have p0003 :=
    @g_n_3anidm13 (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))
      (.imp (syn_wa (.classMem (syn_copk A B) (syn_cltfin))
          (.classMem (syn_copk B A) (syn_cltfin))) (.classMem (syn_copk A A) (syn_cltfin)))
      p0002
  have p0004 :=
    @g_expdimp (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
      (.classMem (syn_copk A B) (syn_cltfin)) (.classMem (syn_copk B A) (syn_cltfin))
      (.classMem (syn_copk A A) (syn_cltfin)) p0003
  have p0005 :=
    @g_mtod
      (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
        (.classMem (syn_copk A B) (syn_cltfin)))
      (.classMem (syn_copk B A) (syn_cltfin)) (.classMem (syn_copk A A) (syn_cltfin))
      p0001 p0004
  have p0006 :=
    @g_ex (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
      (.classMem (syn_copk A B) (syn_cltfin))
      (.neg (.classMem (syn_copk B A) (syn_cltfin))) p0005
  exact p0006

@[expose]
noncomputable def g_n_0cminle (A : Class) :
    Nominal.NPrf
      (.imp (.classMem A (syn_cnnc)) (.classMem (syn_copk (syn_c0c) A) (syn_clefin))) :=
  by
  have p0000 := @g_addcid2 A
  have p0001 := @g_opkeq2i (syn_cplc (syn_c0c) A) A (syn_c0c) p0000
  have p0002 := @g_peano1
  have p0003 := @g_lefinaddc (syn_c0c) A (syn_cnnc)
  have p0004 :=
    @g_mpan (.classMem (syn_c0c) (syn_cnnc)) (.classMem A (syn_cnnc))
      (.classMem (syn_copk (syn_c0c) (syn_cplc (syn_c0c) A)) (syn_clefin)) p0002 p0003
  have p0005 :=
    @g_syl5eqelr (.classMem A (syn_cnnc)) (syn_copk (syn_c0c) A)
      (syn_copk (syn_c0c) (syn_cplc (syn_c0c) A)) (syn_clefin) p0001 p0004
  exact p0005

@[expose]
noncomputable def g_ltfinp1 (A : Class) (V : Class) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem A V) (syn_wne A (syn_c0)))
        (.classMem (syn_copk A (syn_cplc A (syn_c1c))) (syn_cltfin))) :=
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
  have p0000 := @g_simpr (.classMem A V) (syn_wne A (syn_c0))
  have p0001 := @g_peano1
  have p0002 := @g_addcid1 A
  have p0003 := @g_addceq1i (syn_cplc A (syn_c0c)) A (syn_c1c) p0002
  have p0004 :=
    @g_eqcomi (syn_cplc (syn_cplc A (syn_c0c)) (syn_c1c)) (syn_cplc A (syn_c1c)) p0003
  have p0005 := @g_addceq2 (.cv x) (syn_c0c) A
  have p0006 :=
    @g_addceq1d (.classEq (.cv x) (syn_c0c)) (syn_cplc A (.cv x)) (syn_cplc A (syn_c0c))
      (syn_c1c) p0005
  have p0007 :=
    @g_eqeq2d (.classEq (.cv x) (syn_c0c)) (syn_cplc (syn_cplc A (.cv x)) (syn_c1c))
      (syn_cplc (syn_cplc A (syn_c0c)) (syn_c1c)) (syn_cplc A (syn_c1c)) p0006
  have freeVariableCertificate0 :
    x ∉
      ((Wff.classEq (syn_cplc A (syn_c1c)) (syn_cplc (syn_cplc A (syn_c0c)) (syn_c1c)))).fv :=
    by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union,
      Finset.notMem_empty, fresh_x_not_A, or_false, not_false_eq_true]
  have p0008 :=
    @g_rspcev (.classEq (syn_cplc A (syn_c1c)) (syn_cplc (syn_cplc A (.cv x)) (syn_c1c)))
      (.classEq (syn_cplc A (syn_c1c)) (syn_cplc (syn_cplc A (syn_c0c)) (syn_c1c))) x
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
      freeVariableCertificate0 p0007
  have p0009 :=
    @g_mp2an (.classMem (syn_c0c) (syn_cnnc))
      (.classEq (syn_cplc A (syn_c1c)) (syn_cplc (syn_cplc A (syn_c0c)) (syn_c1c)))
      (syn_wrex x (syn_cnnc)
        (.classEq (syn_cplc A (syn_c1c)) (syn_cplc (syn_cplc A (.cv x)) (syn_c1c))))
      p0001 p0004 p0008
  have p0010 :=
    @g_jctir (syn_wa (.classMem A V) (syn_wne A (syn_c0))) (syn_wne A (syn_c0))
      (syn_wrex x (syn_cnnc)
        (.classEq (syn_cplc A (syn_c1c)) (syn_cplc (syn_cplc A (.cv x)) (syn_c1c))))
      p0000 p0009
  have p0011 := @g_n_1cex
  have p0012 := @g_addcexg A (syn_c1c) V (syn_cvv)
  have p0013 :=
    @g_mpan2 (.classMem A V) (.classMem (syn_c1c) (syn_cvv))
      (.classMem (syn_cplc A (syn_c1c)) (syn_cvv)) p0011 p0012
  have freeVariableCertificate1 : x ∉ ((syn_cplc A (syn_c1c))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
      Finset.notMem_empty, fresh_x_not_A, or_false, not_false_eq_true]
  have p0014 :=
    @g_opkltfing x A (syn_cplc A (syn_c1c)) V (syn_cvv)
      (by exact (show x ∉ (A).fv from (by exact fresh_x_not_A))) freeVariableCertificate1
  have p0015 :=
    @g_mpdan (.classMem A V) (.classMem (syn_cplc A (syn_c1c)) (syn_cvv))
      (syn_wb (.classMem (syn_copk A (syn_cplc A (syn_c1c))) (syn_cltfin))
        (syn_wa (syn_wne A (syn_c0)) (syn_wrex x (syn_cnnc)
            (.classEq (syn_cplc A (syn_c1c)) (syn_cplc (syn_cplc A (.cv x)) (syn_c1c))))))
      p0013 p0014
  have p0016 :=
    @g_adantr (.classMem A V)
      (syn_wb (.classMem (syn_copk A (syn_cplc A (syn_c1c))) (syn_cltfin))
        (syn_wa (syn_wne A (syn_c0)) (syn_wrex x (syn_cnnc)
            (.classEq (syn_cplc A (syn_c1c)) (syn_cplc (syn_cplc A (.cv x)) (syn_c1c))))))
      (syn_wne A (syn_c0)) p0015
  have p0017 :=
    @g_mpbird (syn_wa (.classMem A V) (syn_wne A (syn_c0)))
      (.classMem (syn_copk A (syn_cplc A (syn_c1c))) (syn_cltfin))
      (syn_wa (syn_wne A (syn_c0)) (syn_wrex x (syn_cnnc)
          (.classEq (syn_cplc A (syn_c1c)) (syn_cplc (syn_cplc A (.cv x)) (syn_c1c)))))
      p0010 p0016
  exact p0017


end NFChoice.DirectNominalPrf.WPPReplay

end
