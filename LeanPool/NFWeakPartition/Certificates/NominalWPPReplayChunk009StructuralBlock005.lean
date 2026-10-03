/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NominalWPPReplayChunk009StructuralBlock004

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NominalWPPReplayChunk009StructuralPart025`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_nncex : Nominal.NPrf (.classMem (syn_cnnc) (syn_cvv)) :=
  by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let x : Var := freshVar proofSupport 0
  have p0000 := @g_dfnnc2 x
  have p0001 :=
    @g_setswithex x (syn_c0c)
      (by
        exact
          (show x ∉ ((syn_c0c)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c];
              exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
  have p0002 := @g_ssetkex
  have p0004 := @g_addcexlem
  have p0005 := @g_n_1cex
  have p0006 := @g_pw1ex (syn_c1c) p0005
  have p0007 := @g_pw1ex (syn_cpw1 (syn_c1c)) p0006
  have p0008 :=
    @g_imakex
      (syn_cdif (syn_cins3k (syn_ccompl
            (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
              (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
          (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
            (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
              (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
      (syn_cpw1 (syn_cpw1 (syn_c1c))) p0004 p0007
  have p0009 :=
    @g_imagekex
      (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
              (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
            (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
              (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
        (syn_cpw1 (syn_cpw1 (syn_c1c))))
      p0008
  have p0010 :=
    @g_sikex
      (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
                (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
              (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                  (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
          (syn_cpw1 (syn_cpw1 (syn_c1c)))))
      p0009
  have p0011 :=
    @g_cokex (syn_cssetk)
      (syn_csik (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
                  (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                    (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                  (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                    (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
            (syn_cpw1 (syn_cpw1 (syn_c1c))))))
      p0002 p0010
  have p0012 :=
    @g_difex (syn_cssetk)
      (syn_ccomk (syn_cssetk) (syn_csik (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k
                  (syn_ccompl (syn_cimak
                      (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                  (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                    (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                      (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
              (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
      p0002 p0011
  have p0014 :=
    @g_imakex
      (syn_cdif (syn_cssetk) (syn_ccomk (syn_cssetk) (syn_csik (syn_cimagek (syn_cimak (syn_cdif
                  (syn_cins3k (syn_ccompl (syn_cimak
                        (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                    (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                      (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                        (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                    (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
      (syn_c1c) p0012 p0005
  have p0015 :=
    @g_difex (.cab x (.classMem (syn_c0c) (.cv x)))
      (syn_cimak (syn_cdif (syn_cssetk) (syn_ccomk (syn_cssetk) (syn_csik (syn_cimagek
                (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                          (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                          (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                      (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                        (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                          (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_c1c))
      p0001 p0014
  have p0016 :=
    @g_intex
      (syn_cdif (.cab x (.classMem (syn_c0c) (.cv x))) (syn_cimak (syn_cdif (syn_cssetk)
            (syn_ccomk (syn_cssetk) (syn_csik (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k
                        (syn_ccompl (syn_cimak
                            (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                            (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                        (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                          (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                            (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                    (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_c1c)))
      p0015
  have p0017 :=
    @g_eqeltri (syn_cnnc)
      (syn_cint (syn_cdif (.cab x (.classMem (syn_c0c) (.cv x))) (syn_cimak
            (syn_cdif (syn_cssetk) (syn_ccomk (syn_cssetk) (syn_csik (syn_cimagek (syn_cimak
                      (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                              (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                              (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                          (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                            (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                              (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_c1c))))
      (syn_cvv) p0000 p0016
  exact p0017

@[expose]
noncomputable def g_finex : Nominal.NPrf (.classMem (syn_cfin) (syn_cvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_cfin))
  have p0001 := @g_nncex
  have p0002 := @g_uniex (syn_cnnc) p0001
  have p0003 := @g_eqeltri (syn_cfin) (syn_cuni (syn_cnnc)) (syn_cvv) p0000 p0002
  exact p0003

@[expose]
noncomputable def g_eladdc (A : Class) (M : Class) (N : Class) (b : Var) (c : Var)
    (dv_A_b : b ∉ A.fv) (dv_A_c : c ∉ A.fv) (dv_M_b : b ∉ M.fv) (dv_M_c : c ∉ M.fv)
    (dv_N_b : b ∉ N.fv) (dv_N_c : c ∉ N.fv) (dv_b_c : b ≠ c) :
    Nominal.NPrf
      (syn_wb (.classMem A (syn_cplc M N)) (syn_wrex b M (syn_wrex c N
            (syn_wa (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0))
              (.classEq A (syn_cun (.cv b) (.cv c))))))) :=
  by
  let proofSupport : Finset Var :=
    A.fv ∪ M.fv ∪ N.fv ∪ ({ b } : Finset Var) ∪ ({ c } : Finset Var)
  let a : Var := freshVar proofSupport 0
  have fresh_a : a ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_a_not_A : a ∉ A.fv := by
    intro h
    exact
      fresh_a
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))))
  have fresh_a_not_M : a ∉ M.fv := by
    intro h
    exact
      fresh_a
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_a_not_N : a ∉ N.fv := by
    intro h
    exact
      fresh_a
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_a_ne_b : a ≠ b := by
    intro h
    exact
      fresh_a
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_b_ne_a : b ≠ a := Ne.symm fresh_a_ne_b
  have fresh_a_ne_c : a ≠ c := by
    intro h
    exact fresh_a (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_c_ne_a : c ≠ a := Ne.symm fresh_a_ne_c
  have p0000 := @g_elex A (syn_cplc M N)
  have p0001 := @g_id (.classEq A (syn_cun (.cv b) (.cv c)))
  have p0002 := @g_vex b
  have p0003 := @g_vex c
  have p0004 := @g_unex (.cv b) (.cv c) p0002 p0003
  have p0005 :=
    @g_syl6eqel (.classEq A (syn_cun (.cv b) (.cv c))) A (syn_cun (.cv b) (.cv c))
      (syn_cvv) p0001 p0004
  have p0006 :=
    @g_adantl (.classEq A (syn_cun (.cv b) (.cv c))) (.classMem A (syn_cvv))
      (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0)) p0005
  have freeVariableCertificate0 : c ∉ ((Wff.classMem A (syn_cvv))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
      Finset.notMem_empty, dv_A_c, or_false, not_false_eq_true]
  have p0007 :=
    @g_rexlimivw
      (syn_wa (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0))
        (.classEq A (syn_cun (.cv b) (.cv c))))
      (.classMem A (syn_cvv)) c N freeVariableCertificate0 p0006
  have freeVariableCertificate1 : b ∉ ((Wff.classMem A (syn_cvv))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
      Finset.notMem_empty, dv_A_b, or_false, not_false_eq_true]
  have p0008 :=
    @g_rexlimivw
      (syn_wrex c N (syn_wa (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0))
          (.classEq A (syn_cun (.cv b) (.cv c)))))
      (.classMem A (syn_cvv)) b M freeVariableCertificate1 p0007
  have p0009 := @g_eqeq1 (.cv a) A (syn_cun (.cv b) (.cv c))
  have p0010 :=
    @g_anbi2d (.classEq (.cv a) A) (.classEq (.cv a) (syn_cun (.cv b) (.cv c)))
      (.classEq A (syn_cun (.cv b) (.cv c))) (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0))
      p0009
  have freeVariableCertificate2 : b ∉ ((Wff.classEq (.cv a) A)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      fresh_b_ne_a, dv_A_b, or_false, not_false_eq_true]
  have freeVariableCertificate3 : c ∉ ((Wff.classEq (.cv a) A)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      fresh_c_ne_a, dv_A_c, or_false, not_false_eq_true]
  have p0011 :=
    @g_n_2rexbidv (.classEq (.cv a) A)
      (syn_wa (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0))
        (.classEq (.cv a) (syn_cun (.cv b) (.cv c))))
      (syn_wa (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0))
        (.classEq A (syn_cun (.cv b) (.cv c))))
      b c M N freeVariableCertificate2 freeVariableCertificate3 p0010
  have p0012 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_addc a b c M N
      (by exact (show a ∉ (M).fv from (by exact fresh_a_not_M)))
      (by exact (show b ∉ (M).fv from (by exact dv_M_b)))
      (by exact (show c ∉ (M).fv from (by exact dv_M_c)))
      (by exact (show a ∉ (N).fv from (by exact fresh_a_not_N)))
      (by exact (show b ∉ (N).fv from (by exact dv_N_b)))
      (by exact (show c ∉ (N).fv from (by exact dv_N_c)))
      (show a ≠ b from (by exact fresh_a_ne_b)) (show a ≠ c from (by exact fresh_a_ne_c))
      (show b ≠ c from (by exact dv_b_c))
  have freeVariableCertificate4 :
    a ∉
      ((syn_wrex b M (syn_wrex c N (syn_wa (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0))
              (.classEq A (syn_cun (.cv b) (.cv c))))))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, Finset.mem_union,
      Finset.mem_erase, Finset.mem_singleton, Finset.notMem_empty, fresh_a_not_M,
      fresh_a_not_N, fresh_a_ne_b, fresh_a_ne_c, fresh_a_not_A, or_false, and_false,
      not_false_eq_true]
  have p0013 :=
    @g_elab2g
      (syn_wrex b M (syn_wrex c N (syn_wa (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0))
            (.classEq (.cv a) (syn_cun (.cv b) (.cv c))))))
      (syn_wrex b M (syn_wrex c N (syn_wa (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0))
            (.classEq A (syn_cun (.cv b) (.cv c))))))
      a A (syn_cplc M N) (syn_cvv)
      (by exact (show a ∉ (A).fv from (by exact fresh_a_not_A))) freeVariableCertificate4
      p0011 p0012
  have p0014 :=
    @g_pm5_21nii (.classMem A (syn_cplc M N)) (.classMem A (syn_cvv))
      (syn_wrex b M (syn_wrex c N (syn_wa (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0))
            (.classEq A (syn_cun (.cv b) (.cv c))))))
      p0000 p0008 p0013
  exact p0014

@[expose]
noncomputable def g_eladdci (A : Class) (B : Class) (M : Class) (N : Class) :
    Nominal.NPrf
      (.imp (syn_w3a (.classMem A M) (.classMem B N) (.classEq (syn_cin A B) (syn_c0)))
        (.classMem (syn_cun A B) (syn_cplc M N))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ M.fv ∪ N.fv
  let a : Var := freshVar proofSupport 0
  let b : Var := freshVar proofSupport 1
  have fresh_a : a ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_a_not_A : a ∉ A.fv := by
    intro h
    exact
      fresh_a
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_a_not_B : a ∉ B.fv := by
    intro h
    exact
      fresh_a
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_a_not_M : a ∉ M.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_a_not_N : a ∉ N.fv := by
    intro h
    exact fresh_a (Finset.mem_union_right _ (h))
  have fresh_b : b ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_b_not_A : b ∉ A.fv := by
    intro h
    exact
      fresh_b
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_b_not_B : b ∉ B.fv := by
    intro h
    exact
      fresh_b
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_b_not_M : b ∉ M.fv := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_b_not_N : b ∉ N.fv := by
    intro h
    exact fresh_b (Finset.mem_union_right _ (h))
  have fresh_a_ne_b : a ≠ b :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have p0000 := @g_eqid (syn_cun A B)
  have p0001 := @g_ineq1 (.cv a) A (.cv b)
  have p0002 :=
    @g_eqeq1d (.classEq (.cv a) A) (syn_cin (.cv a) (.cv b)) (syn_cin A (.cv b)) (syn_c0)
      p0001
  have p0003 := @g_uneq1 (.cv a) A (.cv b)
  have p0004 :=
    @g_eqeq2d (.classEq (.cv a) A) (syn_cun (.cv a) (.cv b)) (syn_cun A (.cv b))
      (syn_cun A B) p0003
  have p0005 :=
    @g_anbi12d (.classEq (.cv a) A) (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0))
      (.classEq (syn_cin A (.cv b)) (syn_c0))
      (.classEq (syn_cun A B) (syn_cun (.cv a) (.cv b)))
      (.classEq (syn_cun A B) (syn_cun A (.cv b))) p0002 p0004
  have p0006 := @g_ineq2 (.cv b) B A
  have p0007 :=
    @g_eqeq1d (.classEq (.cv b) B) (syn_cin A (.cv b)) (syn_cin A B) (syn_c0) p0006
  have p0008 := @g_uneq2 (.cv b) B A
  have p0009 :=
    @g_eqeq2d (.classEq (.cv b) B) (syn_cun A (.cv b)) (syn_cun A B) (syn_cun A B) p0008
  have p0010 :=
    @g_anbi12d (.classEq (.cv b) B) (.classEq (syn_cin A (.cv b)) (syn_c0))
      (.classEq (syn_cin A B) (syn_c0)) (.classEq (syn_cun A B) (syn_cun A (.cv b)))
      (.classEq (syn_cun A B) (syn_cun A B)) p0007 p0009
  have freeVariableCertificate0 :
    a ∉
      ((syn_wa (.classEq (syn_cin A (.cv b)) (syn_c0))
          (.classEq (syn_cun A B) (syn_cun A (.cv b))))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_a_not_A, fresh_a_ne_b,
      fresh_a_not_B, or_false, not_false_eq_true]
  have freeVariableCertificate1 :
    b ∉
      ((syn_wa (.classEq (syn_cin A B) (syn_c0)) (.classEq (syn_cun A B) (syn_cun A B)))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, Finset.mem_union,
      Finset.notMem_empty, fresh_b_not_A, fresh_b_not_B, or_false, not_false_eq_true]
  have p0011 :=
    @g_rspc2ev
      (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0))
        (.classEq (syn_cun A B) (syn_cun (.cv a) (.cv b))))
      (syn_wa (.classEq (syn_cin A B) (syn_c0)) (.classEq (syn_cun A B) (syn_cun A B)))
      (syn_wa (.classEq (syn_cin A (.cv b)) (syn_c0))
        (.classEq (syn_cun A B) (syn_cun A (.cv b))))
      a b A B M N (by exact (show a ∉ (A).fv from (by exact fresh_a_not_A)))
      (by exact (show b ∉ (A).fv from (by exact fresh_b_not_A)))
      (by exact (show b ∉ (B).fv from (by exact fresh_b_not_B)))
      (by exact (show a ∉ (M).fv from (by exact fresh_a_not_M)))
      (by exact (show a ∉ (N).fv from (by exact fresh_a_not_N)))
      (by exact (show b ∉ (N).fv from (by exact fresh_b_not_N))) freeVariableCertificate0
      freeVariableCertificate1 (show a ≠ b from (by exact fresh_a_ne_b)) p0005 p0010
  have p0012 :=
    @g_n_3expa (.classMem A M) (.classMem B N)
      (syn_wa (.classEq (syn_cin A B) (syn_c0)) (.classEq (syn_cun A B) (syn_cun A B)))
      (syn_wrex a M (syn_wrex b N (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0))
            (.classEq (syn_cun A B) (syn_cun (.cv a) (.cv b))))))
      p0011
  have p0013 :=
    @g_mpanr2 (syn_wa (.classMem A M) (.classMem B N)) (.classEq (syn_cin A B) (syn_c0))
      (.classEq (syn_cun A B) (syn_cun A B))
      (syn_wrex a M (syn_wrex b N (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0))
            (.classEq (syn_cun A B) (syn_cun (.cv a) (.cv b))))))
      p0000 p0012
  have p0014 :=
    @g_n_3impa (.classMem A M) (.classMem B N) (.classEq (syn_cin A B) (syn_c0))
      (syn_wrex a M (syn_wrex b N (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0))
            (.classEq (syn_cun A B) (syn_cun (.cv a) (.cv b))))))
      p0013
  have freeVariableCertificate2 : a ∉ ((syn_cun A B)).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, Finset.mem_union,
      fresh_a_not_A, fresh_a_not_B, or_false, not_false_eq_true]
  have freeVariableCertificate3 : b ∉ ((syn_cun A B)).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, Finset.mem_union,
      fresh_b_not_A, fresh_b_not_B, or_false, not_false_eq_true]
  have p0015 :=
    @g_eladdc (syn_cun A B) M N a b freeVariableCertificate2 freeVariableCertificate3
      (by exact (show a ∉ (M).fv from (by exact fresh_a_not_M)))
      (by exact (show b ∉ (M).fv from (by exact fresh_b_not_M)))
      (by exact (show a ∉ (N).fv from (by exact fresh_a_not_N)))
      (by exact (show b ∉ (N).fv from (by exact fresh_b_not_N)))
      (show a ≠ b from (by exact fresh_a_ne_b))
  have p0016 :=
    @g_sylibr (syn_w3a (.classMem A M) (.classMem B N) (.classEq (syn_cin A B) (syn_c0)))
      (syn_wrex a M (syn_wrex b N (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0))
            (.classEq (syn_cun A B) (syn_cun (.cv a) (.cv b))))))
      (.classMem (syn_cun A B) (syn_cplc M N)) p0014 p0015
  exact p0016

@[expose]
noncomputable def g_n_0nelsuc (A : Class) :
    Nominal.NPrf (.neg (.classMem (syn_c0) (syn_cplc A (syn_c1c)))) :=
  by
  let proofSupport : Finset Var := A.fv
  let n : Var := freshVar proofSupport 0
  let m : Var := freshVar proofSupport 1
  have fresh_n : n ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_n_not_A : n ∉ A.fv := by
    intro h
    exact fresh_n (h)
  have fresh_m : m ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_m_not_A : m ∉ A.fv := by
    intro h
    exact fresh_m (h)
  have fresh_n_ne_m : n ≠ m :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have freeVariableCertificate0 : n ∉ ((Class.cv m)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_n_ne_m, not_false_eq_true]
  have p0000 := @g_el1c n (.cv m) freeVariableCertificate0
  have p0001 := @g_vex n
  have p0002 := @g_snid (.cv n) p0001
  have p0003 := @g_n0i (syn_csn (.cv n)) (.cv n)
  have p0004 := Nominal.mp p0002 p0003
  have p0005 := @g_eqeq1 (.cv m) (syn_csn (.cv n)) (syn_c0)
  have p0006 :=
    @g_mtbiri (.classEq (.cv m) (syn_csn (.cv n))) (.classEq (.cv m) (syn_c0))
      (.classEq (syn_csn (.cv n)) (syn_c0)) p0004 p0005
  have freeVariableCertificate1 : n ∉ ((Wff.neg (.classEq (.cv m) (syn_c0)))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_neg,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_n_ne_m, or_false,
      not_false_eq_true]
  have p0007 :=
    @g_exlimiv (.classEq (.cv m) (syn_csn (.cv n))) (.neg (.classEq (.cv m) (syn_c0))) n
      freeVariableCertificate1 p0006
  have p0008 :=
    @g_sylbi (.classMem (.cv m) (syn_c1c))
      (syn_wex n (.classEq (.cv m) (syn_csn (.cv n)))) (.neg (.classEq (.cv m) (syn_c0)))
      p0000 p0007
  have p0009 := @g_simpr (.classEq (.cv n) (syn_c0)) (.classEq (.cv m) (syn_c0))
  have p0010 :=
    @g_nsyl (.classMem (.cv m) (syn_c1c)) (.classEq (.cv m) (syn_c0))
      (syn_wa (.classEq (.cv n) (syn_c0)) (.classEq (.cv m) (syn_c0))) p0008 p0009
  have p0011 := @g_un00 (.cv n) (.cv m)
  have p0012 := @g_eqcom (syn_cun (.cv n) (.cv m)) (syn_c0)
  have p0013 :=
    @g_bitri (syn_wa (.classEq (.cv n) (syn_c0)) (.classEq (.cv m) (syn_c0)))
      (.classEq (syn_cun (.cv n) (.cv m)) (syn_c0))
      (.classEq (syn_c0) (syn_cun (.cv n) (.cv m))) p0011 p0012
  have p0014 :=
    @g_notbii (syn_wa (.classEq (.cv n) (syn_c0)) (.classEq (.cv m) (syn_c0)))
      (.classEq (syn_c0) (syn_cun (.cv n) (.cv m))) p0013
  have p0015 :=
    @g_sylib (.classMem (.cv m) (syn_c1c))
      (.neg (syn_wa (.classEq (.cv n) (syn_c0)) (.classEq (.cv m) (syn_c0))))
      (.neg (.classEq (syn_c0) (syn_cun (.cv n) (.cv m)))) p0010 p0014
  have p0016 :=
    @g_simpr (.classEq (syn_cin (.cv n) (.cv m)) (syn_c0))
      (.classEq (syn_c0) (syn_cun (.cv n) (.cv m)))
  have p0017 :=
    @g_nsyl (.classMem (.cv m) (syn_c1c)) (.classEq (syn_c0) (syn_cun (.cv n) (.cv m)))
      (syn_wa (.classEq (syn_cin (.cv n) (.cv m)) (syn_c0))
        (.classEq (syn_c0) (syn_cun (.cv n) (.cv m))))
      p0015 p0016
  have p0018 :=
    @g_nrex
      (syn_wa (.classEq (syn_cin (.cv n) (.cv m)) (syn_c0))
        (.classEq (syn_c0) (syn_cun (.cv n) (.cv m))))
      m (syn_c1c) p0017
  have p0019 :=
    @g_a1i
      (.neg (syn_wrex m (syn_c1c) (syn_wa (.classEq (syn_cin (.cv n) (.cv m)) (syn_c0))
            (.classEq (syn_c0) (syn_cun (.cv n) (.cv m))))))
      (.classMem (.cv n) A) p0018
  have p0020 :=
    @g_nrex
      (syn_wrex m (syn_c1c) (syn_wa (.classEq (syn_cin (.cv n) (.cv m)) (syn_c0))
          (.classEq (syn_c0) (syn_cun (.cv n) (.cv m)))))
      n A p0019
  have p0021 :=
    @g_eladdc (syn_c0) A (syn_c1c) n m
      (by
        exact
          (show n ∉ ((syn_c0)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0];
              exact (show n ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
      (by
        exact
          (show m ∉ ((syn_c0)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0];
              exact (show m ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
      (by exact (show n ∉ (A).fv from (by exact fresh_n_not_A)))
      (by exact (show m ∉ (A).fv from (by exact fresh_m_not_A)))
      (by
        exact
          (show n ∉ ((syn_c1c)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c];
              exact (show n ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
      (by
        exact
          (show m ∉ ((syn_c1c)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c];
              exact (show m ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
      (show n ≠ m from (by exact fresh_n_ne_m))
  have p0022 :=
    @g_mtbir (.classMem (syn_c0) (syn_cplc A (syn_c1c)))
      (syn_wrex n A (syn_wrex m (syn_c1c) (syn_wa (.classEq (syn_cin (.cv n) (.cv m)) (syn_c0))
            (.classEq (syn_c0) (syn_cun (.cv n) (.cv m))))))
      p0020 p0021
  exact p0022

@[expose]
noncomputable def g_n_0cnsuc (A : Class) :
    Nominal.NPrf (syn_wne (syn_cplc A (syn_c1c)) (syn_c0c)) :=
  by
  have p0000 := @g_n_0nelsuc A
  have p0001 := @g_n_0ex
  have p0002 := @g_snid (syn_c0) p0001
  have p0003 := (Nominal.classEqRefl (syn_c0c))
  have p0004 := @g_eleqtrri (syn_c0) (syn_csn (syn_c0)) (syn_c0c) p0002 p0003
  have p0005 := @g_eleq2 (syn_cplc A (syn_c1c)) (syn_c0c) (syn_c0)
  have p0006 :=
    @g_mpbiri (.classEq (syn_cplc A (syn_c1c)) (syn_c0c))
      (.classMem (syn_c0) (syn_cplc A (syn_c1c))) (.classMem (syn_c0) (syn_c0c)) p0004
      p0005
  have p0007 :=
    @g_mto (.classEq (syn_cplc A (syn_c1c)) (syn_c0c))
      (.classMem (syn_c0) (syn_cplc A (syn_c1c))) p0000 p0006
  have p0008 := (Nominal.biimpRefl (syn_wne (syn_cplc A (syn_c1c)) (syn_c0c)))
  have p0009 :=
    @g_mpbir (syn_wne (syn_cplc A (syn_c1c)) (syn_c0c))
      (.neg (.classEq (syn_cplc A (syn_c1c)) (syn_c0c))) p0007 p0008
  exact p0009

@[expose]
noncomputable def g_peano1 : Nominal.NPrf (.classMem (syn_c0c) (syn_cnnc)) :=
  by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_nnc y x
      (show x ≠ y from (by exact fresh_x_ne_y))
  have p0001 :=
    @g_eleq2i (syn_cnnc)
      (syn_cint (.cab x (syn_wa (.classMem (syn_c0c) (.cv x))
            (syn_wral y (.cv x) (.classMem (syn_cplc (.cv y) (syn_c1c)) (.cv x))))))
      (syn_c0c) p0000
  have p0002 := @g_n_0cex
  have p0003 :=
    @g_elintab
      (syn_wa (.classMem (syn_c0c) (.cv x))
        (syn_wral y (.cv x) (.classMem (syn_cplc (.cv y) (syn_c1c)) (.cv x))))
      x (syn_c0c)
      (by
        exact
          (show x ∉ ((syn_c0c)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c];
              exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
      p0002
  have p0004 :=
    @g_bitri (.classMem (syn_c0c) (syn_cnnc))
      (.classMem (syn_c0c) (syn_cint (.cab x (syn_wa (.classMem (syn_c0c) (.cv x))
              (syn_wral y (.cv x) (.classMem (syn_cplc (.cv y) (syn_c1c)) (.cv x)))))))
      (.all x (.imp (syn_wa (.classMem (syn_c0c) (.cv x))
            (syn_wral y (.cv x) (.classMem (syn_cplc (.cv y) (syn_c1c)) (.cv x))))
          (.classMem (syn_c0c) (.cv x))))
      p0001 p0003
  have p0005 :=
    @g_simpl (.classMem (syn_c0c) (.cv x))
      (syn_wral y (.cv x) (.classMem (syn_cplc (.cv y) (syn_c1c)) (.cv x)))
  have p0006 :=
    @g_mpgbir (.classMem (syn_c0c) (syn_cnnc))
      (.imp (syn_wa (.classMem (syn_c0c) (.cv x))
          (syn_wral y (.cv x) (.classMem (syn_cplc (.cv y) (syn_c1c)) (.cv x))))
        (.classMem (syn_c0c) (.cv x)))
      x p0004 p0005
  exact p0006

@[expose]
noncomputable def g_peano2 (A : Class) :
    Nominal.NPrf
      (.imp (.classMem A (syn_cnnc)) (.classMem (syn_cplc A (syn_c1c)) (syn_cnnc))) :=
  by
  let proofSupport : Finset Var := A.fv
  let a : Var := freshVar proofSupport 0
  let x : Var := freshVar proofSupport 1
  let y : Var := freshVar proofSupport 2
  have fresh_a : a ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_a_not_A : a ∉ A.fv := by
    intro h
    exact fresh_a (h)
  have fresh_a_ne_x : a ≠ x :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_x_ne_a : x ≠ a := Ne.symm fresh_a_ne_x
  have fresh_a_ne_y : a ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_y_ne_a : y ≠ a := Ne.symm fresh_a_ne_y
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_y_ne_x : y ≠ x := Ne.symm fresh_x_ne_y
  have p0000 := @g_addceq1 (.cv a) A (syn_c1c)
  have p0001 :=
    @g_eleq1d (.classEq (.cv a) A) (syn_cplc (.cv a) (syn_c1c)) (syn_cplc A (syn_c1c))
      (syn_cnnc) p0000
  have p0002 := @g_addceq1 (.cv y) (.cv a) (syn_c1c)
  have p0003_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq y a)
        (.classEq (syn_cplc (.cv y) (syn_c1c)) (syn_cplc (.cv a) (syn_c1c)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_cplc syn_wrex syn_wex syn_wa syn_c1c
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0002
  have p0003 :=
    @g_eleq1d (.objEq y a) (syn_cplc (.cv y) (syn_c1c)) (syn_cplc (.cv a) (syn_c1c))
      (.cv x) p0003_e00_recanon
  have p0004_e00_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv y) (.cv a)) (syn_wb (.classMem (syn_cplc (.cv y) (syn_c1c)) (.cv x))
          (.classMem (syn_cplc (.cv a) (syn_c1c)) (.cv x)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cplc syn_wrex syn_wex syn_wa syn_c1c
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0003
  have freeVariableCertificate0 : y ∉ ((Class.cv a)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_y_ne_a, not_false_eq_true]
  have freeVariableCertificate1 : y ∉ ((Class.cv x)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_y_ne_x, not_false_eq_true]
  have freeVariableCertificate2 :
    y ∉ ((Wff.classMem (syn_cplc (.cv a) (syn_c1c)) (.cv x))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_y_ne_a, fresh_y_ne_x, or_false,
      not_false_eq_true]
  have p0004 :=
    @g_rspccv (.classMem (syn_cplc (.cv y) (syn_c1c)) (.cv x))
      (.classMem (syn_cplc (.cv a) (syn_c1c)) (.cv x)) y (.cv a) (.cv x)
      freeVariableCertificate0 freeVariableCertificate1 freeVariableCertificate2
      p0004_e00_recanon
  have p0005_e00_recanon :
    Nominal.NPrf
      (.imp (syn_wral y (.cv x) (.classMem (syn_cplc (.cv y) (syn_c1c)) (.cv x)))
        (.imp (.objMem a x) (.classMem (syn_cplc (.cv a) (syn_c1c)) (.cv x)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wral syn_cplc syn_wrex syn_wex syn_wa syn_c1c
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0004
  have p0005 :=
    @g_adantl (syn_wral y (.cv x) (.classMem (syn_cplc (.cv y) (syn_c1c)) (.cv x)))
      (.imp (.objMem a x) (.classMem (syn_cplc (.cv a) (syn_c1c)) (.cv x)))
      (.classMem (syn_c0c) (.cv x)) p0005_e00_recanon
  have p0006 :=
    @g_a2i
      (syn_wa (.classMem (syn_c0c) (.cv x))
        (syn_wral y (.cv x) (.classMem (syn_cplc (.cv y) (syn_c1c)) (.cv x))))
      (.objMem a x) (.classMem (syn_cplc (.cv a) (syn_c1c)) (.cv x)) p0005
  have p0007 :=
    @g_alimi
      (.imp (syn_wa (.classMem (syn_c0c) (.cv x))
          (syn_wral y (.cv x) (.classMem (syn_cplc (.cv y) (syn_c1c)) (.cv x)))) (.objMem a x))
      (.imp (syn_wa (.classMem (syn_c0c) (.cv x))
          (syn_wral y (.cv x) (.classMem (syn_cplc (.cv y) (syn_c1c)) (.cv x))))
        (.classMem (syn_cplc (.cv a) (syn_c1c)) (.cv x)))
      x p0006
  have p0008 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_nnc y x
      (show x ≠ y from (by exact fresh_x_ne_y))
  have p0009 :=
    @g_eleq2i (syn_cnnc)
      (syn_cint (.cab x (syn_wa (.classMem (syn_c0c) (.cv x))
            (syn_wral y (.cv x) (.classMem (syn_cplc (.cv y) (syn_c1c)) (.cv x))))))
      (.cv a) p0008
  have p0010 := @g_vex a
  have freeVariableCertificate3 : x ∉ ((Class.cv a)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_x_ne_a, not_false_eq_true]
  have p0011 :=
    @g_elintab
      (syn_wa (.classMem (syn_c0c) (.cv x))
        (syn_wral y (.cv x) (.classMem (syn_cplc (.cv y) (syn_c1c)) (.cv x))))
      x (.cv a) freeVariableCertificate3 p0010
  have p0012_e01_recanon :
    Nominal.NPrf
      (syn_wb (.classMem (.cv a) (syn_cint (.cab x (syn_wa (.classMem (syn_c0c) (.cv x))
                (syn_wral y (.cv x) (.classMem (syn_cplc (.cv y) (syn_c1c)) (.cv x)))))))
        (.all x (.imp (syn_wa (.classMem (syn_c0c) (.cv x))
              (syn_wral y (.cv x) (.classMem (syn_cplc (.cv y) (syn_c1c)) (.cv x))))
            (.objMem a x)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cint syn_wa syn_c0c syn_csn syn_c0 syn_cdif syn_cin syn_ccompl
          syn_cnin syn_wnan syn_cvv syn_wral syn_cplc syn_wrex syn_wex syn_c1c
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cab]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0011
  have p0012 :=
    @g_bitri (.classMem (.cv a) (syn_cnnc))
      (.classMem (.cv a) (syn_cint (.cab x (syn_wa (.classMem (syn_c0c) (.cv x))
              (syn_wral y (.cv x) (.classMem (syn_cplc (.cv y) (syn_c1c)) (.cv x)))))))
      (.all x (.imp (syn_wa (.classMem (syn_c0c) (.cv x))
            (syn_wral y (.cv x) (.classMem (syn_cplc (.cv y) (syn_c1c)) (.cv x))))
          (.objMem a x)))
      p0009 p0012_e01_recanon
  have p0013 :=
    @g_eleq2i (syn_cnnc)
      (syn_cint (.cab x (syn_wa (.classMem (syn_c0c) (.cv x))
            (syn_wral y (.cv x) (.classMem (syn_cplc (.cv y) (syn_c1c)) (.cv x))))))
      (syn_cplc (.cv a) (syn_c1c)) p0008
  have p0014 := @g_n_1cex
  have p0015 := @g_addcex (.cv a) (syn_c1c) p0010 p0014
  have freeVariableCertificate4 : x ∉ ((syn_cplc (.cv a) (syn_c1c))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_x_ne_a, or_false,
      not_false_eq_true]
  have p0016 :=
    @g_elintab
      (syn_wa (.classMem (syn_c0c) (.cv x))
        (syn_wral y (.cv x) (.classMem (syn_cplc (.cv y) (syn_c1c)) (.cv x))))
      x (syn_cplc (.cv a) (syn_c1c)) freeVariableCertificate4 p0015
  have p0017 :=
    @g_bitri (.classMem (syn_cplc (.cv a) (syn_c1c)) (syn_cnnc))
      (.classMem (syn_cplc (.cv a) (syn_c1c)) (syn_cint (.cab x
            (syn_wa (.classMem (syn_c0c) (.cv x))
              (syn_wral y (.cv x) (.classMem (syn_cplc (.cv y) (syn_c1c)) (.cv x)))))))
      (.all x (.imp (syn_wa (.classMem (syn_c0c) (.cv x))
            (syn_wral y (.cv x) (.classMem (syn_cplc (.cv y) (syn_c1c)) (.cv x))))
          (.classMem (syn_cplc (.cv a) (syn_c1c)) (.cv x))))
      p0013 p0016
  have p0018 :=
    @g_n_3imtr4i
      (.all x (.imp (syn_wa (.classMem (syn_c0c) (.cv x))
            (syn_wral y (.cv x) (.classMem (syn_cplc (.cv y) (syn_c1c)) (.cv x))))
          (.objMem a x)))
      (.all x (.imp (syn_wa (.classMem (syn_c0c) (.cv x))
            (syn_wral y (.cv x) (.classMem (syn_cplc (.cv y) (syn_c1c)) (.cv x))))
          (.classMem (syn_cplc (.cv a) (syn_c1c)) (.cv x))))
      (.classMem (.cv a) (syn_cnnc)) (.classMem (syn_cplc (.cv a) (syn_c1c)) (syn_cnnc))
      p0007 p0012 p0017
  have freeVariableCertificate5 :
    a ∉ ((Wff.classMem (syn_cplc A (syn_c1c)) (syn_cnnc))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union,
      Finset.notMem_empty, fresh_a_not_A, or_false, not_false_eq_true]
  have p0019 :=
    @g_vtoclga (.classMem (syn_cplc (.cv a) (syn_c1c)) (syn_cnnc))
      (.classMem (syn_cplc A (syn_c1c)) (syn_cnnc)) a A (syn_cnnc)
      (by exact (show a ∉ (A).fv from (by exact fresh_a_not_A)))
      (by
        exact
          (show a ∉ ((syn_cnnc)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc];
              exact (show a ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
      freeVariableCertificate5 p0001 p0018
  exact p0019

@[expose]
noncomputable def g_peano3 (A : Class) :
    Nominal.NPrf
      (.imp (.classMem A (syn_cnnc)) (syn_wne (syn_cplc A (syn_c1c)) (syn_c0c))) :=
  by
  have p0000 := @g_n_0cnsuc A
  have p0001 :=
    @g_a1i (syn_wne (syn_cplc A (syn_c1c)) (syn_c0c)) (.classMem A (syn_cnnc)) p0000
  exact p0001

@[expose]
noncomputable def g_addcid1 (A : Class) :
    Nominal.NPrf (.classEq (syn_cplc A (syn_c0c)) A) :=
  by
  let proofSupport : Finset Var := A.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let z : Var := freshVar proofSupport 2
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (h)
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (h)
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (h)
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
  have p0000 := (Nominal.classEqRefl (syn_c0c))
  have p0001 := @g_addceq2i (syn_c0c) (syn_csn (syn_c0)) A p0000
  have p0002 := @g_n_0ex
  have p0003 := @g_ineq2 (.cv z) (syn_c0) (.cv y)
  have p0004 :=
    @g_eqeq1d (.classEq (.cv z) (syn_c0)) (syn_cin (.cv y) (.cv z))
      (syn_cin (.cv y) (syn_c0)) (syn_c0) p0003
  have p0005 := @g_uneq2 (.cv z) (syn_c0) (.cv y)
  have p0006 :=
    @g_eqeq2d (.classEq (.cv z) (syn_c0)) (syn_cun (.cv y) (.cv z))
      (syn_cun (.cv y) (syn_c0)) (.cv x) p0005
  have p0007 :=
    @g_anbi12d (.classEq (.cv z) (syn_c0)) (.classEq (syn_cin (.cv y) (.cv z)) (syn_c0))
      (.classEq (syn_cin (.cv y) (syn_c0)) (syn_c0))
      (.classEq (.cv x) (syn_cun (.cv y) (.cv z)))
      (.classEq (.cv x) (syn_cun (.cv y) (syn_c0))) p0004 p0006
  have p0008 := @g_in0 (.cv y)
  have p0009 :=
    @g_biantrur (.classEq (syn_cin (.cv y) (syn_c0)) (syn_c0))
      (.classEq (.cv x) (syn_cun (.cv y) (syn_c0))) p0008
  have p0010 :=
    @g_syl6bbr (.classEq (.cv z) (syn_c0))
      (syn_wa (.classEq (syn_cin (.cv y) (.cv z)) (syn_c0))
        (.classEq (.cv x) (syn_cun (.cv y) (.cv z))))
      (syn_wa (.classEq (syn_cin (.cv y) (syn_c0)) (syn_c0))
        (.classEq (.cv x) (syn_cun (.cv y) (syn_c0))))
      (.classEq (.cv x) (syn_cun (.cv y) (syn_c0))) p0007 p0009
  have freeVariableCertificate0 :
    z ∉ ((Wff.classEq (.cv x) (syn_cun (.cv y) (syn_c0)))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_z_ne_x, fresh_z_ne_y, or_false,
      not_false_eq_true]
  have p0011 :=
    @g_rexsn
      (syn_wa (.classEq (syn_cin (.cv y) (.cv z)) (syn_c0))
        (.classEq (.cv x) (syn_cun (.cv y) (.cv z))))
      (.classEq (.cv x) (syn_cun (.cv y) (syn_c0))) z (syn_c0)
      (by
        exact
          (show z ∉ ((syn_c0)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0];
              exact (show z ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
      freeVariableCertificate0 p0002 p0010
  have p0012 := @g_un0 (.cv y)
  have p0013 := @g_eqeq2i (syn_cun (.cv y) (syn_c0)) (.cv y) (.cv x) p0012
  have p0014 := @g_equcom x y
  have p0015_e01_recanon :
    Nominal.NPrf (syn_wb (.classEq (.cv x) (syn_cun (.cv y) (syn_c0))) (.objEq x y)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_c0 syn_cdif syn_cin
          syn_cvv
        simp (config := { failIfUnchanged := false }) only []
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0013
  have p0015 :=
    @g_n_3bitri
      (syn_wrex z (syn_csn (syn_c0)) (syn_wa (.classEq (syn_cin (.cv y) (.cv z)) (syn_c0))
          (.classEq (.cv x) (syn_cun (.cv y) (.cv z)))))
      (.classEq (.cv x) (syn_cun (.cv y) (syn_c0))) (.objEq x y) (.objEq y x) p0011
      p0015_e01_recanon p0014
  have p0016 :=
    @g_rexbii
      (syn_wrex z (syn_csn (syn_c0)) (syn_wa (.classEq (syn_cin (.cv y) (.cv z)) (syn_c0))
          (.classEq (.cv x) (syn_cun (.cv y) (.cv z)))))
      (.objEq y x) y A p0015
  have freeVariableCertificate1 : y ∉ ((Class.cv x)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_y_ne_x, not_false_eq_true]
  have freeVariableCertificate2 : z ∉ ((Class.cv x)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_z_ne_x, not_false_eq_true]
  have freeVariableCertificate3 : y ∉ ((syn_csn (syn_c0))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.notMem_empty,
      not_false_eq_true]
  have freeVariableCertificate4 : z ∉ ((syn_csn (syn_c0))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.notMem_empty,
      not_false_eq_true]
  have p0017 :=
    @g_eladdc (.cv x) A (syn_csn (syn_c0)) y z freeVariableCertificate1
      freeVariableCertificate2 (by exact (show y ∉ (A).fv from (by exact fresh_y_not_A)))
      (by exact (show z ∉ (A).fv from (by exact fresh_z_not_A))) freeVariableCertificate3
      freeVariableCertificate4 (show y ≠ z from (by exact fresh_y_ne_z))
  have p0018 :=
    @g_risset y (.cv x) A freeVariableCertificate1
      (by exact (show y ∉ (A).fv from (by exact fresh_y_not_A)))
  have p0019_e02_recanon :
    Nominal.NPrf (syn_wb (.classMem (.cv x) A) (syn_wrex y A (.objEq y x))) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [syn_wb, syn_wrex, syn_wex, syn_wa]
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
              exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0018
  have p0019 :=
    @g_n_3bitr4i
      (syn_wrex y A (syn_wrex z (syn_csn (syn_c0))
          (syn_wa (.classEq (syn_cin (.cv y) (.cv z)) (syn_c0))
            (.classEq (.cv x) (syn_cun (.cv y) (.cv z))))))
      (syn_wrex y A (.objEq y x)) (.classMem (.cv x) (syn_cplc A (syn_csn (syn_c0))))
      (.classMem (.cv x) A) p0016 p0017 p0019_e02_recanon
  have freeVariableCertificate5 : x ∉ ((syn_cplc A (syn_csn (syn_c0)))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union,
      Finset.notMem_empty, fresh_x_not_A, or_false, not_false_eq_true]
  have p0020 :=
    @g_eqriv x (syn_cplc A (syn_csn (syn_c0))) A freeVariableCertificate5
      (by exact (show x ∉ (A).fv from (by exact fresh_x_not_A))) p0019
  have p0021 :=
    @g_eqtri (syn_cplc A (syn_c0c)) (syn_cplc A (syn_csn (syn_c0))) A p0001 p0020
  exact p0021


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk009StructuralPart026`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_addccom (A : Class) (B : Class) :
    Nominal.NPrf (.classEq (syn_cplc A B) (syn_cplc B A)) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  let y : Var := freshVar proofSupport 0
  let z : Var := freshVar proofSupport 1
  let x : Var := freshVar proofSupport 2
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (h))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (h))
  have fresh_z_not_B : z ∉ B.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y_ne_z : y ≠ z :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_z_ne_y : z ≠ y := Ne.symm fresh_y_ne_z
  have fresh_y_ne_x : y ≠ x :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_x_ne_y : x ≠ y := Ne.symm fresh_y_ne_x
  have fresh_z_ne_x : z ≠ x :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_x_ne_z : x ≠ z := Ne.symm fresh_z_ne_x
  have p0000 := @g_incom (.cv y) (.cv z)
  have p0001 :=
    @g_eqeq1i (syn_cin (.cv y) (.cv z)) (syn_cin (.cv z) (.cv y)) (syn_c0) p0000
  have p0002 := @g_uncom (.cv y) (.cv z)
  have p0003 :=
    @g_eqeq2i (syn_cun (.cv y) (.cv z)) (syn_cun (.cv z) (.cv y)) (.cv x) p0002
  have p0004 :=
    @g_anbi12i (.classEq (syn_cin (.cv y) (.cv z)) (syn_c0))
      (.classEq (syn_cin (.cv z) (.cv y)) (syn_c0))
      (.classEq (.cv x) (syn_cun (.cv y) (.cv z)))
      (.classEq (.cv x) (syn_cun (.cv z) (.cv y))) p0001 p0003
  have p0005 :=
    @g_n_2rexbii
      (syn_wa (.classEq (syn_cin (.cv y) (.cv z)) (syn_c0))
        (.classEq (.cv x) (syn_cun (.cv y) (.cv z))))
      (syn_wa (.classEq (syn_cin (.cv z) (.cv y)) (syn_c0))
        (.classEq (.cv x) (syn_cun (.cv z) (.cv y))))
      y z A B p0004
  have p0006 :=
    @g_rexcom
      (syn_wa (.classEq (syn_cin (.cv z) (.cv y)) (syn_c0))
        (.classEq (.cv x) (syn_cun (.cv z) (.cv y))))
      y z A B (by exact (show z ∉ (A).fv from (by exact fresh_z_not_A)))
      (by exact (show y ∉ (B).fv from (by exact fresh_y_not_B)))
      (show y ≠ z from (by exact fresh_y_ne_z))
  have p0007 :=
    @g_bitri
      (syn_wrex y A (syn_wrex z B (syn_wa (.classEq (syn_cin (.cv y) (.cv z)) (syn_c0))
            (.classEq (.cv x) (syn_cun (.cv y) (.cv z))))))
      (syn_wrex y A (syn_wrex z B (syn_wa (.classEq (syn_cin (.cv z) (.cv y)) (syn_c0))
            (.classEq (.cv x) (syn_cun (.cv z) (.cv y))))))
      (syn_wrex z B (syn_wrex y A (syn_wa (.classEq (syn_cin (.cv z) (.cv y)) (syn_c0))
            (.classEq (.cv x) (syn_cun (.cv z) (.cv y))))))
      p0005 p0006
  have p0008 :=
    @g_abbii
      (syn_wrex y A (syn_wrex z B (syn_wa (.classEq (syn_cin (.cv y) (.cv z)) (syn_c0))
            (.classEq (.cv x) (syn_cun (.cv y) (.cv z))))))
      (syn_wrex z B (syn_wrex y A (syn_wa (.classEq (syn_cin (.cv z) (.cv y)) (syn_c0))
            (.classEq (.cv x) (syn_cun (.cv z) (.cv y))))))
      x p0007
  have p0009 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_addc x y z A B
      (by exact (show x ∉ (A).fv from (by exact fresh_x_not_A)))
      (by exact (show y ∉ (A).fv from (by exact fresh_y_not_A)))
      (by exact (show z ∉ (A).fv from (by exact fresh_z_not_A)))
      (by exact (show x ∉ (B).fv from (by exact fresh_x_not_B)))
      (by exact (show y ∉ (B).fv from (by exact fresh_y_not_B)))
      (by exact (show z ∉ (B).fv from (by exact fresh_z_not_B)))
      (show x ≠ y from (by exact fresh_x_ne_y)) (show x ≠ z from (by exact fresh_x_ne_z))
      (show y ≠ z from (by exact fresh_y_ne_z))
  have p0010 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_addc x z y B A
      (by exact (show x ∉ (B).fv from (by exact fresh_x_not_B)))
      (by exact (show z ∉ (B).fv from (by exact fresh_z_not_B)))
      (by exact (show y ∉ (B).fv from (by exact fresh_y_not_B)))
      (by exact (show x ∉ (A).fv from (by exact fresh_x_not_A)))
      (by exact (show z ∉ (A).fv from (by exact fresh_z_not_A)))
      (by exact (show y ∉ (A).fv from (by exact fresh_y_not_A)))
      (show x ≠ z from (by exact fresh_x_ne_z)) (show x ≠ y from (by exact fresh_x_ne_y))
      (show z ≠ y from (by exact fresh_z_ne_y))
  have p0011 :=
    @g_n_3eqtr4i
      (.cab x (syn_wrex y A (syn_wrex z B (syn_wa (.classEq (syn_cin (.cv y) (.cv z)) (syn_c0))
              (.classEq (.cv x) (syn_cun (.cv y) (.cv z)))))))
      (.cab x (syn_wrex z B (syn_wrex y A (syn_wa (.classEq (syn_cin (.cv z) (.cv y)) (syn_c0))
              (.classEq (.cv x) (syn_cun (.cv z) (.cv y)))))))
      (syn_cplc A B) (syn_cplc B A) p0008 p0009 p0010
  exact p0011

@[expose]
noncomputable def g_addcid2 (A : Class) :
    Nominal.NPrf (.classEq (syn_cplc (syn_c0c) A) A) :=
  by
  have p0000 := @g_addccom (syn_c0c) A
  have p0001 := @g_addcid1 A
  have p0002 := @g_eqtri (syn_cplc (syn_c0c) A) (syn_cplc A (syn_c0c)) A p0000 p0001
  exact p0002

@[expose]
noncomputable def g_n_1cnnc : Nominal.NPrf (.classMem (syn_c1c) (syn_cnnc)) :=
  by
  have p0000 := @g_addcid1 (syn_c1c)
  have p0001 := @g_addccom (syn_c1c) (syn_c0c)
  have p0002 :=
    @g_eqtr3i (syn_cplc (syn_c1c) (syn_c0c)) (syn_c1c) (syn_cplc (syn_c0c) (syn_c1c))
      p0000 p0001
  have p0003 := @g_peano1
  have p0004 := @g_peano2 (syn_c0c)
  have p0005 := Nominal.mp p0003 p0004
  have p0006 := @g_eqeltri (syn_c1c) (syn_cplc (syn_c0c) (syn_c1c)) (syn_cnnc) p0002 p0005
  exact p0006

@[expose]
noncomputable def g_peano5 (x : Var) (A : Class) (V : Class) (dv_A_x : x ∉ A.fv) :
    Nominal.NPrf
      (.imp (syn_w3a (.classMem A V) (.classMem (syn_c0c) A) (syn_wral x (syn_cnnc)
            (.imp (.classMem (.cv x) A) (.classMem (syn_cplc (.cv x) (syn_c1c)) A))))
        (syn_wss (syn_cnnc) A)) :=
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
  have p0000 := @g_nncex
  have p0001 := @g_inexg (syn_cnnc) A (syn_cvv) V
  have p0002 :=
    @g_mpan (.classMem (syn_cnnc) (syn_cvv)) (.classMem A V)
      (.classMem (syn_cin (syn_cnnc) A) (syn_cvv)) p0000 p0001
  have p0003 := @g_peano1
  have p0004 := @g_elin (syn_c0c) (syn_cnnc) A
  have p0005 :=
    @g_biimpri (.classMem (syn_c0c) (syn_cin (syn_cnnc) A))
      (syn_wa (.classMem (syn_c0c) (syn_cnnc)) (.classMem (syn_c0c) A)) p0004
  have p0006 :=
    @g_mpan (.classMem (syn_c0c) (syn_cnnc)) (.classMem (syn_c0c) A)
      (.classMem (syn_c0c) (syn_cin (syn_cnnc) A)) p0003 p0005
  have p0007 := @g_elin (.cv x) (syn_cnnc) A
  have p0008 :=
    @g_imbi1i (.classMem (.cv x) (syn_cin (syn_cnnc) A))
      (syn_wa (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv x) A))
      (.classMem (syn_cplc (.cv x) (syn_c1c)) A) p0007
  have p0009 :=
    @g_impexp (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv x) A)
      (.classMem (syn_cplc (.cv x) (syn_c1c)) A)
  have p0010 :=
    @g_bitri
      (.imp (.classMem (.cv x) (syn_cin (syn_cnnc) A))
        (.classMem (syn_cplc (.cv x) (syn_c1c)) A))
      (.imp (syn_wa (.classMem (.cv x) (syn_cnnc)) (.classMem (.cv x) A))
        (.classMem (syn_cplc (.cv x) (syn_c1c)) A))
      (.imp (.classMem (.cv x) (syn_cnnc))
        (.imp (.classMem (.cv x) A) (.classMem (syn_cplc (.cv x) (syn_c1c)) A)))
      p0008 p0009
  have p0011 := @g_inss1 (syn_cnnc) A
  have p0012 := @g_sseli (syn_cin (syn_cnnc) A) (syn_cnnc) (.cv x) p0011
  have p0013 := @g_peano2 (.cv x)
  have p0014 :=
    @g_syl (.classMem (.cv x) (syn_cin (syn_cnnc) A)) (.classMem (.cv x) (syn_cnnc))
      (.classMem (syn_cplc (.cv x) (syn_c1c)) (syn_cnnc)) p0012 p0013
  have p0015 := @g_elin (syn_cplc (.cv x) (syn_c1c)) (syn_cnnc) A
  have p0016 :=
    @g_biimpri (.classMem (syn_cplc (.cv x) (syn_c1c)) (syn_cin (syn_cnnc) A))
      (syn_wa (.classMem (syn_cplc (.cv x) (syn_c1c)) (syn_cnnc))
        (.classMem (syn_cplc (.cv x) (syn_c1c)) A))
      p0015
  have p0017 :=
    @g_a1i
      (.imp (syn_wa (.classMem (syn_cplc (.cv x) (syn_c1c)) (syn_cnnc))
          (.classMem (syn_cplc (.cv x) (syn_c1c)) A))
        (.classMem (syn_cplc (.cv x) (syn_c1c)) (syn_cin (syn_cnnc) A)))
      (.classMem (.cv x) (syn_cin (syn_cnnc) A)) p0016
  have p0018 :=
    @g_mpand (.classMem (.cv x) (syn_cin (syn_cnnc) A))
      (.classMem (syn_cplc (.cv x) (syn_c1c)) (syn_cnnc))
      (.classMem (syn_cplc (.cv x) (syn_c1c)) A)
      (.classMem (syn_cplc (.cv x) (syn_c1c)) (syn_cin (syn_cnnc) A)) p0014 p0017
  have p0019 :=
    @g_a2i (.classMem (.cv x) (syn_cin (syn_cnnc) A))
      (.classMem (syn_cplc (.cv x) (syn_c1c)) A)
      (.classMem (syn_cplc (.cv x) (syn_c1c)) (syn_cin (syn_cnnc) A)) p0018
  have p0020 :=
    @g_sylbir
      (.imp (.classMem (.cv x) (syn_cnnc))
        (.imp (.classMem (.cv x) A) (.classMem (syn_cplc (.cv x) (syn_c1c)) A)))
      (.imp (.classMem (.cv x) (syn_cin (syn_cnnc) A))
        (.classMem (syn_cplc (.cv x) (syn_c1c)) A))
      (.imp (.classMem (.cv x) (syn_cin (syn_cnnc) A))
        (.classMem (syn_cplc (.cv x) (syn_c1c)) (syn_cin (syn_cnnc) A)))
      p0010 p0019
  have p0021 :=
    @g_ralimi2 (.imp (.classMem (.cv x) A) (.classMem (syn_cplc (.cv x) (syn_c1c)) A))
      (.classMem (syn_cplc (.cv x) (syn_c1c)) (syn_cin (syn_cnnc) A)) x (syn_cnnc)
      (syn_cin (syn_cnnc) A) p0020
  have p0022 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_nnc x y
      (show y ≠ x from (by exact fresh_y_ne_x))
  have p0023 := @g_eleq2 (.cv y) (syn_cin (syn_cnnc) A) (syn_c0c)
  have p0024 := @g_eleq2 (.cv y) (syn_cin (syn_cnnc) A) (syn_cplc (.cv x) (syn_c1c))
  have freeVariableCertificate0 : x ∉ ((Class.cv y)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_x_ne_y, not_false_eq_true]
  have freeVariableCertificate1 : x ∉ ((syn_cin (syn_cnnc) A)).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union,
      Finset.notMem_empty, dv_A_x, or_false, not_false_eq_true]
  have p0025 :=
    @g_raleqbi1dv (.classMem (syn_cplc (.cv x) (syn_c1c)) (.cv y))
      (.classMem (syn_cplc (.cv x) (syn_c1c)) (syn_cin (syn_cnnc) A)) x (.cv y)
      (syn_cin (syn_cnnc) A) freeVariableCertificate0 freeVariableCertificate1 p0024
  have p0026 :=
    @g_anbi12d (.classEq (.cv y) (syn_cin (syn_cnnc) A)) (.classMem (syn_c0c) (.cv y))
      (.classMem (syn_c0c) (syn_cin (syn_cnnc) A))
      (syn_wral x (.cv y) (.classMem (syn_cplc (.cv x) (syn_c1c)) (.cv y)))
      (syn_wral x (syn_cin (syn_cnnc) A)
        (.classMem (syn_cplc (.cv x) (syn_c1c)) (syn_cin (syn_cnnc) A)))
      p0023 p0025
  have freeVariableCertificate2 : y ∉ ((syn_cin (syn_cnnc) A)).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union,
      Finset.notMem_empty, fresh_y_not_A, or_false, not_false_eq_true]
  have freeVariableCertificate3 :
    y ∉
      ((syn_wa (.classMem (syn_c0c) (syn_cin (syn_cnnc) A)) (syn_wral x (syn_cin (syn_cnnc) A)
            (.classMem (syn_cplc (.cv x) (syn_c1c)) (syn_cin (syn_cnnc) A))))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
      Finset.mem_erase, Finset.mem_singleton, Finset.notMem_empty, fresh_y_not_A,
      fresh_y_ne_x, or_false, and_false, not_false_eq_true]
  have p0027 :=
    @g_elabg
      (syn_wa (.classMem (syn_c0c) (.cv y))
        (syn_wral x (.cv y) (.classMem (syn_cplc (.cv x) (syn_c1c)) (.cv y))))
      (syn_wa (.classMem (syn_c0c) (syn_cin (syn_cnnc) A)) (syn_wral x (syn_cin (syn_cnnc) A)
          (.classMem (syn_cplc (.cv x) (syn_c1c)) (syn_cin (syn_cnnc) A))))
      y (syn_cin (syn_cnnc) A) (syn_cvv) freeVariableCertificate2 freeVariableCertificate3
      p0026
  have p0028 :=
    @g_biimprd (.classMem (syn_cin (syn_cnnc) A) (syn_cvv))
      (.classMem (syn_cin (syn_cnnc) A) (.cab y (syn_wa (.classMem (syn_c0c) (.cv y))
            (syn_wral x (.cv y) (.classMem (syn_cplc (.cv x) (syn_c1c)) (.cv y))))))
      (syn_wa (.classMem (syn_c0c) (syn_cin (syn_cnnc) A)) (syn_wral x (syn_cin (syn_cnnc) A)
          (.classMem (syn_cplc (.cv x) (syn_c1c)) (syn_cin (syn_cnnc) A))))
      p0027
  have p0029 :=
    @g_n_3impib (.classMem (syn_cin (syn_cnnc) A) (syn_cvv))
      (.classMem (syn_c0c) (syn_cin (syn_cnnc) A))
      (syn_wral x (syn_cin (syn_cnnc) A)
        (.classMem (syn_cplc (.cv x) (syn_c1c)) (syn_cin (syn_cnnc) A)))
      (.classMem (syn_cin (syn_cnnc) A) (.cab y (syn_wa (.classMem (syn_c0c) (.cv y))
            (syn_wral x (.cv y) (.classMem (syn_cplc (.cv x) (syn_c1c)) (.cv y))))))
      p0028
  have p0030 :=
    @g_intss1 (syn_cin (syn_cnnc) A)
      (.cab y (syn_wa (.classMem (syn_c0c) (.cv y))
          (syn_wral x (.cv y) (.classMem (syn_cplc (.cv x) (syn_c1c)) (.cv y)))))
  have p0031 :=
    @g_syl
      (syn_w3a (.classMem (syn_cin (syn_cnnc) A) (syn_cvv))
        (.classMem (syn_c0c) (syn_cin (syn_cnnc) A)) (syn_wral x (syn_cin (syn_cnnc) A)
          (.classMem (syn_cplc (.cv x) (syn_c1c)) (syn_cin (syn_cnnc) A))))
      (.classMem (syn_cin (syn_cnnc) A) (.cab y (syn_wa (.classMem (syn_c0c) (.cv y))
            (syn_wral x (.cv y) (.classMem (syn_cplc (.cv x) (syn_c1c)) (.cv y))))))
      (syn_wss (syn_cint (.cab y (syn_wa (.classMem (syn_c0c) (.cv y))
              (syn_wral x (.cv y) (.classMem (syn_cplc (.cv x) (syn_c1c)) (.cv y))))))
        (syn_cin (syn_cnnc) A))
      p0029 p0030
  have p0032 :=
    @g_syl5eqss
      (syn_w3a (.classMem (syn_cin (syn_cnnc) A) (syn_cvv))
        (.classMem (syn_c0c) (syn_cin (syn_cnnc) A)) (syn_wral x (syn_cin (syn_cnnc) A)
          (.classMem (syn_cplc (.cv x) (syn_c1c)) (syn_cin (syn_cnnc) A))))
      (syn_cnnc)
      (syn_cint (.cab y (syn_wa (.classMem (syn_c0c) (.cv y))
            (syn_wral x (.cv y) (.classMem (syn_cplc (.cv x) (syn_c1c)) (.cv y))))))
      (syn_cin (syn_cnnc) A) p0022 p0031
  have p0033 := @g_inss2 (syn_cnnc) A
  have p0034 :=
    @g_syl6ss
      (syn_w3a (.classMem (syn_cin (syn_cnnc) A) (syn_cvv))
        (.classMem (syn_c0c) (syn_cin (syn_cnnc) A)) (syn_wral x (syn_cin (syn_cnnc) A)
          (.classMem (syn_cplc (.cv x) (syn_c1c)) (syn_cin (syn_cnnc) A))))
      (syn_cnnc) (syn_cin (syn_cnnc) A) A p0032 p0033
  have p0035 :=
    @g_syl3an (.classMem A V) (.classMem (syn_cin (syn_cnnc) A) (syn_cvv))
      (.classMem (syn_c0c) A) (.classMem (syn_c0c) (syn_cin (syn_cnnc) A))
      (syn_wral x (syn_cnnc)
        (.imp (.classMem (.cv x) A) (.classMem (syn_cplc (.cv x) (syn_c1c)) A)))
      (syn_wral x (syn_cin (syn_cnnc) A)
        (.classMem (syn_cplc (.cv x) (syn_c1c)) (syn_cin (syn_cnnc) A)))
      (syn_wss (syn_cnnc) A) p0002 p0006 p0021 p0034
  exact p0035

@[expose]
noncomputable def g_findsd (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (et : Wff) (x : Var) (y : Var) (A : Class) (V : Class) (dv_A_x : x ∉ A.fv)
    (dv_ch_x : x ∉ ch.fv) (dv_et_y : y ∉ et.fv) (dv_ph_y : y ∉ ph.fv)
    (dv_ps_x : x ∉ ps.fv) (dv_ta_x : x ∉ ta.fv) (dv_th_x : x ∉ th.fv) (dv_x_y : x ≠ y)
    (hyp_findsd_1 : Nominal.NPrf (.imp et (.classMem (.cab x ph) V)))
    (hyp_findsd_2 : Nominal.NPrf (.imp (.classEq (.cv x) (syn_c0c)) (syn_wb ph ps)))
    (hyp_findsd_3 : Nominal.NPrf (.imp (.objEq x y) (syn_wb ph ch)))
    (hyp_findsd_4 :
      Nominal.NPrf (.imp (.classEq (.cv x) (syn_cplc (.cv y) (syn_c1c))) (syn_wb ph th)))
    (hyp_findsd_5 : Nominal.NPrf (.imp (.classEq (.cv x) A) (syn_wb ph ta)))
    (hyp_findsd_6 : Nominal.NPrf (.imp et ps))
    (hyp_findsd_7 :
      Nominal.NPrf (.imp (syn_wa (.classMem (.cv y) (syn_cnnc)) et) (.imp ch th))) :
    Nominal.NPrf (.imp (syn_wa (.classMem A (syn_cnnc)) et) ta) :=
  by
  have p0000 := @g_n_0cex
  have p0001 :=
    @g_elab ph ps x (syn_c0c)
      (by
        exact
          (show x ∉ ((syn_c0c)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c];
              exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
      (by exact (show x ∉ (ps).fv from (by exact dv_ps_x))) p0000 hyp_findsd_2
  have p0002 := @g_sylibr et ps (.classMem (syn_c0c) (.cab x ph)) hyp_findsd_6 p0001
  have p0003 := @g_vex y
  have p0004_e01_recanon :
    Nominal.NPrf (.imp (.classEq (.cv x) (.cv y)) (syn_wb ph ch)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      hyp_findsd_3
  have freeVariableCertificate0 : x ∉ ((Class.cv y)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, dv_x_y,
      not_false_eq_true]
  have p0004 :=
    @g_elab ph ch x (.cv y) freeVariableCertificate0
      (by exact (show x ∉ (ch).fv from (by exact dv_ch_x))) p0003 p0004_e01_recanon
  have p0005 := @g_n_1cex
  have p0006 := @g_addcex (.cv y) (syn_c1c) p0003 p0005
  have freeVariableCertificate1 : x ∉ ((syn_cplc (.cv y) (syn_c1c))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, dv_x_y, or_false, not_false_eq_true]
  have p0007 :=
    @g_elab ph th x (syn_cplc (.cv y) (syn_c1c)) freeVariableCertificate1
      (by exact (show x ∉ (th).fv from (by exact dv_th_x))) p0006 hyp_findsd_4
  have p0008 :=
    @g_n_3imtr4g (syn_wa (.classMem (.cv y) (syn_cnnc)) et) ch th
      (.classMem (.cv y) (.cab x ph)) (.classMem (syn_cplc (.cv y) (syn_c1c)) (.cab x ph))
      hyp_findsd_7 p0004 p0007
  have p0009 :=
    @g_ancoms (.classMem (.cv y) (syn_cnnc)) et
      (.imp (.classMem (.cv y) (.cab x ph))
        (.classMem (syn_cplc (.cv y) (syn_c1c)) (.cab x ph)))
      p0008
  have p0010 :=
    @g_ralrimiva et
      (.imp (.classMem (.cv y) (.cab x ph))
        (.classMem (syn_cplc (.cv y) (syn_c1c)) (.cab x ph)))
      y (syn_cnnc) (by exact (show y ∉ (et).fv from (by exact dv_et_y))) p0009
  have freeVariableCertificate2 : y ∉ ((Class.cab x ph)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cab, Finset.mem_erase, dv_ph_y,
      and_false, not_false_eq_true]
  have p0011 := @g_peano5 y (.cab x ph) V freeVariableCertificate2
  have p0012 :=
    @g_syl3anc et (.classMem (.cab x ph) V) (.classMem (syn_c0c) (.cab x ph))
      (syn_wral y (syn_cnnc) (.imp (.classMem (.cv y) (.cab x ph))
          (.classMem (syn_cplc (.cv y) (syn_c1c)) (.cab x ph))))
      (syn_wss (syn_cnnc) (.cab x ph)) hyp_findsd_1 p0002 p0010 p0011
  have p0013 := @g_sseld et (syn_cnnc) (.cab x ph) A p0012
  have p0014 := @g_impcom et (.classMem A (syn_cnnc)) (.classMem A (.cab x ph)) p0013
  have p0015 :=
    @g_elabg ph ta x A (syn_cnnc) (by exact (show x ∉ (A).fv from (by exact dv_A_x)))
      (by exact (show x ∉ (ta).fv from (by exact dv_ta_x))) hyp_findsd_5
  have p0016 :=
    @g_adantr (.classMem A (syn_cnnc)) (syn_wb (.classMem A (.cab x ph)) ta) et p0015
  have p0017 :=
    @g_mpbid (syn_wa (.classMem A (syn_cnnc)) et) (.classMem A (.cab x ph)) ta p0014 p0016
  exact p0017

@[expose]
noncomputable def g_finds (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff) (x : Var)
    (y : Var) (A : Class) (dv_A_x : x ∉ A.fv) (dv_ch_x : x ∉ ch.fv) (dv_ph_y : y ∉ ph.fv)
    (dv_ps_x : x ∉ ps.fv) (dv_ta_x : x ∉ ta.fv) (dv_th_x : x ∉ th.fv) (dv_x_y : x ≠ y)
    (hyp_finds_1 : Nominal.NPrf (.classMem (.cab x ph) (syn_cvv)))
    (hyp_finds_2 : Nominal.NPrf (.imp (.classEq (.cv x) (syn_c0c)) (syn_wb ph ps)))
    (hyp_finds_3 : Nominal.NPrf (.imp (.objEq x y) (syn_wb ph ch)))
    (hyp_finds_4 :
      Nominal.NPrf (.imp (.classEq (.cv x) (syn_cplc (.cv y) (syn_c1c))) (syn_wb ph th)))
    (hyp_finds_5 : Nominal.NPrf (.imp (.classEq (.cv x) A) (syn_wb ph ta)))
    (hyp_finds_6 : Nominal.NPrf ps)
    (hyp_finds_7 : Nominal.NPrf (.imp (.classMem (.cv y) (syn_cnnc)) (.imp ch th))) :
    Nominal.NPrf (.imp (.classMem A (syn_cnnc)) ta) :=
  by
  have p0000 := @g_tru
  have p0001 := @g_a1i (.classMem (.cab x ph) (syn_cvv)) syn_wtru hyp_finds_1
  have p0002 := @g_a1i ps syn_wtru hyp_finds_6
  have p0003 := @g_adantr (.classMem (.cv y) (syn_cnnc)) (.imp ch th) syn_wtru hyp_finds_7
  have p0004 :=
    @g_findsd ph ps ch th ta syn_wtru x y A (syn_cvv)
      (by exact (show x ∉ (A).fv from (by exact dv_A_x)))
      (by exact (show x ∉ (ch).fv from (by exact dv_ch_x)))
      (by
        exact
          (show y ∉ (syn_wtru).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wtru];
              exact (show y ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
      (by exact (show y ∉ (ph).fv from (by exact dv_ph_y)))
      (by exact (show x ∉ (ps).fv from (by exact dv_ps_x)))
      (by exact (show x ∉ (ta).fv from (by exact dv_ta_x)))
      (by exact (show x ∉ (th).fv from (by exact dv_th_x)))
      (show x ≠ y from (by exact dv_x_y)) p0001 hyp_finds_2 hyp_finds_3 hyp_finds_4
      hyp_finds_5 p0002 p0003
  have p0005 := @g_mpan2 (.classMem A (syn_cnnc)) syn_wtru ta p0000 p0004
  exact p0005


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk009StructuralPart027`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_nnc0suc (x : Var) (A : Class) (dv_A_x : x ∉ A.fv) :
    Nominal.NPrf
      (syn_wb (.classMem A (syn_cnnc)) (syn_wo (.classEq A (syn_c0c))
          (syn_wrex x (syn_cnnc) (.classEq A (syn_cplc (.cv x) (syn_c1c)))))) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ A.fv
  let n : Var := freshVar proofSupport 0
  let m : Var := freshVar proofSupport 1
  have fresh_n : n ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_n_ne_x : n ≠ x := by
    intro h
    exact fresh_n (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))
  have fresh_x_ne_n : x ≠ n := Ne.symm fresh_n_ne_x
  have fresh_n_not_A : n ∉ A.fv := by
    intro h
    exact fresh_n (Finset.mem_union_right _ (h))
  have fresh_m : m ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_m_ne_x : m ≠ x := by
    intro h
    exact fresh_m (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))
  have fresh_x_ne_m : x ≠ m := Ne.symm fresh_m_ne_x
  have fresh_n_ne_m : n ≠ m :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_m_ne_n : m ≠ n := Ne.symm fresh_n_ne_m
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_sn n (syn_c0c)
      (by
        exact
          (show n ∉ ((syn_c0c)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c];
              exact (show n ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
  have p0001 := @g_vex n
  have freeVariableCertificate0 :
    x ∉
      ((syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
                  (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                    (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                  (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                    (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
            (syn_cpw1 (syn_cpw1 (syn_c1c)))))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimagek,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik, Finset.mem_union,
      Finset.notMem_empty, or_false, not_false_eq_true]
  have freeVariableCertificate1 : x ∉ ((Class.cv n)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_x_ne_n, not_false_eq_true]
  have p0002 :=
    @g_elimak x
      (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
                (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
              (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                  (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
          (syn_cpw1 (syn_cpw1 (syn_c1c)))))
      (syn_cnnc) (.cv n) freeVariableCertificate0
      (by
        exact
          (show x ∉ ((syn_cnnc)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc];
              exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
      freeVariableCertificate1 p0001
  have p0003 := @g_vex x
  have p0004 :=
    @g_opkelimagekg (.cv x) (.cv n)
      (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
              (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
            (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
              (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
        (syn_cpw1 (syn_cpw1 (syn_c1c))))
      (syn_cvv) (syn_cvv)
  have p0005 :=
    @g_mp2an (.classMem (.cv x) (syn_cvv)) (.classMem (.cv n) (syn_cvv))
      (syn_wb (.classMem (syn_copk (.cv x) (.cv n)) (syn_cimagek (syn_cimak (syn_cdif
                (syn_cins3k (syn_ccompl (syn_cimak
                      (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                  (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                    (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                      (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
              (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (.classEq (.cv n) (syn_cimak (syn_cimak
              (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                      (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                  (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                    (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                      (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
              (syn_cpw1 (syn_cpw1 (syn_c1c)))) (.cv x))))
      p0003 p0001 p0004
  have p0006 := @g_dfaddc2 (.cv x) (syn_c1c)
  have p0007 :=
    @g_eqeq2i (syn_cplc (.cv x) (syn_c1c))
      (syn_cimak (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
                (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
              (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                  (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
          (syn_cpw1 (syn_cpw1 (syn_c1c)))) (.cv x))
      (.cv n) p0006
  have p0008 :=
    @g_bitr4i
      (.classMem (syn_copk (.cv x) (.cv n)) (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k
                (syn_ccompl
                  (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                    (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                  (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                    (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
            (syn_cpw1 (syn_cpw1 (syn_c1c))))))
      (.classEq (.cv n) (syn_cimak (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
                  (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                    (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                  (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                    (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
            (syn_cpw1 (syn_cpw1 (syn_c1c)))) (.cv x)))
      (.classEq (.cv n) (syn_cplc (.cv x) (syn_c1c))) p0005 p0007
  have p0009 :=
    @g_rexbii
      (.classMem (syn_copk (.cv x) (.cv n)) (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k
                (syn_ccompl
                  (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                    (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                  (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                    (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
            (syn_cpw1 (syn_cpw1 (syn_c1c))))))
      (.classEq (.cv n) (syn_cplc (.cv x) (syn_c1c))) x (syn_cnnc) p0008
  have p0010 :=
    @g_bitri
      (.classMem (.cv n) (syn_cimak (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
                    (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                  (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                    (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                      (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
              (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cnnc)))
      (syn_wrex x (syn_cnnc) (.classMem (syn_copk (.cv x) (.cv n)) (syn_cimagek (syn_cimak
              (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                      (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                  (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                    (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                      (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
              (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
      (syn_wrex x (syn_cnnc) (.classEq (.cv n) (syn_cplc (.cv x) (syn_c1c)))) p0002 p0009
  have freeVariableCertificate2 :
    n ∉
      ((syn_cimak (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                      (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                  (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                    (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                      (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
              (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cnnc))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimagek,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union,
      Finset.notMem_empty, or_false, not_false_eq_true]
  have p0011 :=
    @g_eqabi (syn_wrex x (syn_cnnc) (.classEq (.cv n) (syn_cplc (.cv x) (syn_c1c)))) n
      (syn_cimak (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
                  (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                    (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                  (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                    (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
            (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cnnc))
      freeVariableCertificate2 p0010
  have p0012 :=
    @g_uneq12i (syn_csn (syn_c0c)) (.cab n (.classEq (.cv n) (syn_c0c)))
      (syn_cimak (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
                  (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                    (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                  (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                    (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
            (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cnnc))
      (.cab n (syn_wrex x (syn_cnnc) (.classEq (.cv n) (syn_cplc (.cv x) (syn_c1c)))))
      p0000 p0011
  have p0013 :=
    @g_unab (.classEq (.cv n) (syn_c0c))
      (syn_wrex x (syn_cnnc) (.classEq (.cv n) (syn_cplc (.cv x) (syn_c1c)))) n
  have p0014 :=
    @g_eqtri
      (syn_cun (syn_csn (syn_c0c)) (syn_cimak (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k
                  (syn_ccompl (syn_cimak
                      (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                  (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                    (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                      (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
              (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cnnc)))
      (syn_cun (.cab n (.classEq (.cv n) (syn_c0c)))
        (.cab n (syn_wrex x (syn_cnnc) (.classEq (.cv n) (syn_cplc (.cv x) (syn_c1c))))))
      (.cab n (syn_wo (.classEq (.cv n) (syn_c0c))
          (syn_wrex x (syn_cnnc) (.classEq (.cv n) (syn_cplc (.cv x) (syn_c1c))))))
      p0012 p0013
  have p0015 := @g_snex (syn_c0c)
  have p0016 := @g_addcexlem
  have p0017 := @g_n_1cex
  have p0018 := @g_pw1ex (syn_c1c) p0017
  have p0019 := @g_pw1ex (syn_cpw1 (syn_c1c)) p0018
  have p0020 :=
    @g_imakex
      (syn_cdif (syn_cins3k (syn_ccompl
            (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
              (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
          (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
            (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
              (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
      (syn_cpw1 (syn_cpw1 (syn_c1c))) p0016 p0019
  have p0021 :=
    @g_imagekex
      (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
              (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
            (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
              (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
        (syn_cpw1 (syn_cpw1 (syn_c1c))))
      p0020
  have p0022 := @g_nncex
  have p0023 :=
    @g_imakex
      (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
                (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
              (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                  (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
          (syn_cpw1 (syn_cpw1 (syn_c1c)))))
      (syn_cnnc) p0021 p0022
  have p0024 :=
    @g_unex (syn_csn (syn_c0c))
      (syn_cimak (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
                  (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                    (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                  (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                    (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
            (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cnnc))
      p0015 p0023
  have p0025 :=
    @g_eqeltrri
      (syn_cun (syn_csn (syn_c0c)) (syn_cimak (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k
                  (syn_ccompl (syn_cimak
                      (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                  (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                    (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                      (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
              (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cnnc)))
      (.cab n (syn_wo (.classEq (.cv n) (syn_c0c))
          (syn_wrex x (syn_cnnc) (.classEq (.cv n) (syn_cplc (.cv x) (syn_c1c))))))
      (syn_cvv) p0014 p0024
  have p0026 := @g_eqeq1 (.cv n) (syn_c0c) (syn_c0c)
  have p0027 := @g_eqeq1 (.cv n) (syn_c0c) (syn_cplc (.cv x) (syn_c1c))
  have freeVariableCertificate3 : x ∉ ((Wff.classEq (.cv n) (syn_c0c))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_x_ne_n, or_false,
      not_false_eq_true]
  have p0028 :=
    @g_rexbidv (.classEq (.cv n) (syn_c0c))
      (.classEq (.cv n) (syn_cplc (.cv x) (syn_c1c)))
      (.classEq (syn_c0c) (syn_cplc (.cv x) (syn_c1c))) x (syn_cnnc)
      freeVariableCertificate3 p0027
  have p0029 :=
    @g_orbi12d (.classEq (.cv n) (syn_c0c)) (.classEq (.cv n) (syn_c0c))
      (.classEq (syn_c0c) (syn_c0c))
      (syn_wrex x (syn_cnnc) (.classEq (.cv n) (syn_cplc (.cv x) (syn_c1c))))
      (syn_wrex x (syn_cnnc) (.classEq (syn_c0c) (syn_cplc (.cv x) (syn_c1c)))) p0026
      p0028
  have p0030 := @g_eqeq1 (.cv n) (.cv m) (syn_c0c)
  have p0031 := @g_eqeq1 (.cv n) (.cv m) (syn_cplc (.cv x) (syn_c1c))
  have p0032_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq n m) (syn_wb (.classEq (.cv n) (syn_cplc (.cv x) (syn_c1c)))
          (.classEq (.cv m) (syn_cplc (.cv x) (syn_c1c))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cplc syn_wrex syn_wex syn_wa syn_c1c
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0031
  have freeVariableCertificate4 : x ∉ ((Wff.objEq n m)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_insert,
      Finset.mem_singleton, fresh_x_ne_n, fresh_x_ne_m, or_false, not_false_eq_true]
  have p0032 :=
    @g_rexbidv (.objEq n m) (.classEq (.cv n) (syn_cplc (.cv x) (syn_c1c)))
      (.classEq (.cv m) (syn_cplc (.cv x) (syn_c1c))) x (syn_cnnc)
      freeVariableCertificate4 p0032_e00_recanon
  have p0033_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq n m) (syn_wb (.classEq (.cv n) (syn_c0c)) (.classEq (.cv m) (syn_c0c)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_c0c syn_csn syn_c0 syn_cdif syn_cin syn_ccompl syn_cnin syn_wnan
          syn_wa syn_cvv
        simp (config := { failIfUnchanged := false }) only []
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0030
  have p0033 :=
    @g_orbi12d (.objEq n m) (.classEq (.cv n) (syn_c0c)) (.classEq (.cv m) (syn_c0c))
      (syn_wrex x (syn_cnnc) (.classEq (.cv n) (syn_cplc (.cv x) (syn_c1c))))
      (syn_wrex x (syn_cnnc) (.classEq (.cv m) (syn_cplc (.cv x) (syn_c1c))))
      p0033_e00_recanon p0032
  have p0034 := @g_eqeq1 (.cv n) (syn_cplc (.cv m) (syn_c1c)) (syn_c0c)
  have p0035 := @g_eqeq1 (.cv n) (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv x) (syn_c1c))
  have freeVariableCertificate5 :
    x ∉ ((Wff.classEq (.cv n) (syn_cplc (.cv m) (syn_c1c)))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_x_ne_n, fresh_x_ne_m, or_false,
      not_false_eq_true]
  have p0036 :=
    @g_rexbidv (.classEq (.cv n) (syn_cplc (.cv m) (syn_c1c)))
      (.classEq (.cv n) (syn_cplc (.cv x) (syn_c1c)))
      (.classEq (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv x) (syn_c1c))) x (syn_cnnc)
      freeVariableCertificate5 p0035
  have p0037 :=
    @g_orbi12d (.classEq (.cv n) (syn_cplc (.cv m) (syn_c1c)))
      (.classEq (.cv n) (syn_c0c)) (.classEq (syn_cplc (.cv m) (syn_c1c)) (syn_c0c))
      (syn_wrex x (syn_cnnc) (.classEq (.cv n) (syn_cplc (.cv x) (syn_c1c))))
      (syn_wrex x (syn_cnnc)
        (.classEq (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv x) (syn_c1c))))
      p0034 p0036
  have p0038 := @g_eqeq1 (.cv n) A (syn_c0c)
  have p0039 := @g_eqeq1 (.cv n) A (syn_cplc (.cv x) (syn_c1c))
  have freeVariableCertificate6 : x ∉ ((Wff.classEq (.cv n) A)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      fresh_x_ne_n, dv_A_x, or_false, not_false_eq_true]
  have p0040 :=
    @g_rexbidv (.classEq (.cv n) A) (.classEq (.cv n) (syn_cplc (.cv x) (syn_c1c)))
      (.classEq A (syn_cplc (.cv x) (syn_c1c))) x (syn_cnnc) freeVariableCertificate6
      p0039
  have p0041 :=
    @g_orbi12d (.classEq (.cv n) A) (.classEq (.cv n) (syn_c0c)) (.classEq A (syn_c0c))
      (syn_wrex x (syn_cnnc) (.classEq (.cv n) (syn_cplc (.cv x) (syn_c1c))))
      (syn_wrex x (syn_cnnc) (.classEq A (syn_cplc (.cv x) (syn_c1c)))) p0038 p0040
  have p0042 := @g_eqid (syn_c0c)
  have p0043 :=
    @g_orci (.classEq (syn_c0c) (syn_c0c))
      (syn_wrex x (syn_cnnc) (.classEq (syn_c0c) (syn_cplc (.cv x) (syn_c1c)))) p0042
  have p0044 := @g_eqid (syn_cplc (.cv m) (syn_c1c))
  have p0045 := @g_addceq1 (.cv x) (.cv m) (syn_c1c)
  have p0046_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq x m)
        (.classEq (syn_cplc (.cv x) (syn_c1c)) (syn_cplc (.cv m) (syn_c1c)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_cplc syn_wrex syn_wex syn_wa syn_c1c
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0045
  have p0046 :=
    @g_eqeq2d (.objEq x m) (syn_cplc (.cv x) (syn_c1c)) (syn_cplc (.cv m) (syn_c1c))
      (syn_cplc (.cv m) (syn_c1c)) p0046_e00_recanon
  have p0047_e00_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv x) (.cv m))
        (syn_wb (.classEq (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv x) (syn_c1c)))
          (.classEq (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv m) (syn_c1c))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cplc syn_wrex syn_wex syn_wa syn_c1c
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0046
  have freeVariableCertificate7 : x ∉ ((Class.cv m)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_x_ne_m, not_false_eq_true]
  have freeVariableCertificate8 :
    x ∉ ((Wff.classEq (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv m) (syn_c1c)))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_x_ne_m, or_false,
      not_false_eq_true]
  have p0047 :=
    @g_rspcev (.classEq (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv x) (syn_c1c)))
      (.classEq (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv m) (syn_c1c))) x (.cv m)
      (syn_cnnc) freeVariableCertificate7
      (by
        exact
          (show x ∉ ((syn_cnnc)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc];
              exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
      freeVariableCertificate8 p0047_e00_recanon
  have p0048 :=
    @g_mpan2 (.classMem (.cv m) (syn_cnnc))
      (.classEq (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv m) (syn_c1c)))
      (syn_wrex x (syn_cnnc)
        (.classEq (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv x) (syn_c1c))))
      p0044 p0047
  have p0049 :=
    @g_olcd (.classMem (.cv m) (syn_cnnc))
      (syn_wrex x (syn_cnnc)
        (.classEq (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv x) (syn_c1c))))
      (.classEq (syn_cplc (.cv m) (syn_c1c)) (syn_c0c)) p0048
  have p0050 :=
    @g_a1d (.classMem (.cv m) (syn_cnnc))
      (syn_wo (.classEq (syn_cplc (.cv m) (syn_c1c)) (syn_c0c)) (syn_wrex x (syn_cnnc)
          (.classEq (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv x) (syn_c1c)))))
      (syn_wo (.classEq (.cv m) (syn_c0c))
        (syn_wrex x (syn_cnnc) (.classEq (.cv m) (syn_cplc (.cv x) (syn_c1c)))))
      p0049
  have freeVariableCertificate9 :
    n ∉
      ((syn_wo (.classEq (.cv m) (syn_c0c))
          (syn_wrex x (syn_cnnc) (.classEq (.cv m) (syn_cplc (.cv x) (syn_c1c)))))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wo,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
      Finset.mem_erase, Finset.mem_singleton, Finset.notMem_empty, fresh_n_ne_m,
      fresh_n_ne_x, or_false, and_false, not_false_eq_true]
  have freeVariableCertificate10 :
    m ∉
      ((syn_wo (.classEq (.cv n) (syn_c0c))
          (syn_wrex x (syn_cnnc) (.classEq (.cv n) (syn_cplc (.cv x) (syn_c1c)))))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wo,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
      Finset.mem_erase, Finset.mem_singleton, Finset.notMem_empty, fresh_m_ne_n,
      fresh_m_ne_x, or_false, and_false, not_false_eq_true]
  have freeVariableCertificate11 :
    n ∉
      ((syn_wo (.classEq (syn_c0c) (syn_c0c)) (syn_wrex x (syn_cnnc)
            (.classEq (syn_c0c) (syn_cplc (.cv x) (syn_c1c)))))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wo,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
      Finset.mem_erase, Finset.mem_singleton, Finset.notMem_empty, fresh_n_ne_x, or_false,
      and_false, not_false_eq_true]
  have freeVariableCertificate12 :
    n ∉
      ((syn_wo (.classEq A (syn_c0c))
          (syn_wrex x (syn_cnnc) (.classEq A (syn_cplc (.cv x) (syn_c1c)))))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wo,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
      Finset.mem_erase, Finset.mem_singleton, Finset.notMem_empty, fresh_n_not_A,
      fresh_n_ne_x, or_false, and_false, not_false_eq_true]
  have freeVariableCertificate13 :
    n ∉
      ((syn_wo (.classEq (syn_cplc (.cv m) (syn_c1c)) (syn_c0c)) (syn_wrex x (syn_cnnc)
            (.classEq (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv x) (syn_c1c)))))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wo,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union,
      Finset.mem_erase, Finset.mem_singleton, Finset.notMem_empty, fresh_n_ne_m,
      fresh_n_ne_x, or_false, and_false, not_false_eq_true]
  have p0051 :=
    @g_finds
      (syn_wo (.classEq (.cv n) (syn_c0c))
        (syn_wrex x (syn_cnnc) (.classEq (.cv n) (syn_cplc (.cv x) (syn_c1c)))))
      (syn_wo (.classEq (syn_c0c) (syn_c0c))
        (syn_wrex x (syn_cnnc) (.classEq (syn_c0c) (syn_cplc (.cv x) (syn_c1c)))))
      (syn_wo (.classEq (.cv m) (syn_c0c))
        (syn_wrex x (syn_cnnc) (.classEq (.cv m) (syn_cplc (.cv x) (syn_c1c)))))
      (syn_wo (.classEq (syn_cplc (.cv m) (syn_c1c)) (syn_c0c)) (syn_wrex x (syn_cnnc)
          (.classEq (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv x) (syn_c1c)))))
      (syn_wo (.classEq A (syn_c0c))
        (syn_wrex x (syn_cnnc) (.classEq A (syn_cplc (.cv x) (syn_c1c)))))
      n m A (by exact (show n ∉ (A).fv from (by exact fresh_n_not_A)))
      freeVariableCertificate9 freeVariableCertificate10 freeVariableCertificate11
      freeVariableCertificate12 freeVariableCertificate13
      (show n ≠ m from (by exact fresh_n_ne_m)) p0025 p0029 p0033 p0037 p0041 p0043 p0050
  have p0052 := @g_peano1
  have p0053 := @g_eleq1 A (syn_c0c) (syn_cnnc)
  have p0054 :=
    @g_mpbiri (.classEq A (syn_c0c)) (.classMem A (syn_cnnc))
      (.classMem (syn_c0c) (syn_cnnc)) p0052 p0053
  have p0055 := @g_peano2 (.cv x)
  have p0056 := @g_eleq1 A (syn_cplc (.cv x) (syn_c1c)) (syn_cnnc)
  have p0057 :=
    @g_syl5ibrcom (.classMem (.cv x) (syn_cnnc)) (.classMem A (syn_cnnc))
      (.classEq A (syn_cplc (.cv x) (syn_c1c)))
      (.classMem (syn_cplc (.cv x) (syn_c1c)) (syn_cnnc)) p0055 p0056
  have freeVariableCertificate14 : x ∉ ((Wff.classMem A (syn_cnnc))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union,
      Finset.notMem_empty, dv_A_x, or_false, not_false_eq_true]
  have p0058 :=
    @g_rexlimiv (.classEq A (syn_cplc (.cv x) (syn_c1c))) (.classMem A (syn_cnnc)) x
      (syn_cnnc) freeVariableCertificate14 p0057
  have p0059 :=
    @g_jaoi (.classEq A (syn_c0c)) (.classMem A (syn_cnnc))
      (syn_wrex x (syn_cnnc) (.classEq A (syn_cplc (.cv x) (syn_c1c)))) p0054 p0058
  have p0060 :=
    @g_impbii (.classMem A (syn_cnnc))
      (syn_wo (.classEq A (syn_c0c))
        (syn_wrex x (syn_cnnc) (.classEq A (syn_cplc (.cv x) (syn_c1c)))))
      p0051 p0059
  exact p0060


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk009StructuralPart028`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_elsuc (x : Var) (A : Class) (M : Class) (b : Var) (dv_A_b : b ∉ A.fv)
    (dv_A_x : x ∉ A.fv) (dv_M_b : b ∉ M.fv) (dv_b_x : b ≠ x) :
    Nominal.NPrf
      (syn_wb (.classMem A (syn_cplc M (syn_c1c))) (syn_wrex b M
          (syn_wrex x (syn_ccompl (.cv b))
            (.classEq A (syn_cun (.cv b) (syn_csn (.cv x))))))) :=
  by
  let proofSupport : Finset Var :=
    ({ x } : Finset Var) ∪ A.fv ∪ M.fv ∪ ({ b } : Finset Var)
  let y : Var := freshVar proofSupport 0
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
  have fresh_x_ne_y : x ≠ y := Ne.symm fresh_y_ne_x
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_y_not_M : y ∉ M.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_ne_b : y ≠ b := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_b_ne_y : b ≠ y := Ne.symm fresh_y_ne_b
  have p0000 :=
    @g_eladdc A M (syn_c1c) b y (by exact (show b ∉ (A).fv from (by exact dv_A_b)))
      (by exact (show y ∉ (A).fv from (by exact fresh_y_not_A)))
      (by exact (show b ∉ (M).fv from (by exact dv_M_b)))
      (by exact (show y ∉ (M).fv from (by exact fresh_y_not_M)))
      (by
        exact
          (show b ∉ ((syn_c1c)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c];
              exact (show b ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
      (by
        exact
          (show y ∉ ((syn_c1c)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c];
              exact (show y ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
      (show b ≠ y from (by exact fresh_b_ne_y))
  have p0001 := @g_snex (.cv x)
  have p0002 := @g_ineq2 (.cv y) (syn_csn (.cv x)) (.cv b)
  have p0003 :=
    @g_eqeq1d (.classEq (.cv y) (syn_csn (.cv x))) (syn_cin (.cv b) (.cv y))
      (syn_cin (.cv b) (syn_csn (.cv x))) (syn_c0) p0002
  have p0004 := @g_uneq2 (.cv y) (syn_csn (.cv x)) (.cv b)
  have p0005 :=
    @g_eqeq2d (.classEq (.cv y) (syn_csn (.cv x))) (syn_cun (.cv b) (.cv y))
      (syn_cun (.cv b) (syn_csn (.cv x))) A p0004
  have p0006 :=
    @g_anbi12d (.classEq (.cv y) (syn_csn (.cv x)))
      (.classEq (syn_cin (.cv b) (.cv y)) (syn_c0))
      (.classEq (syn_cin (.cv b) (syn_csn (.cv x))) (syn_c0))
      (.classEq A (syn_cun (.cv b) (.cv y)))
      (.classEq A (syn_cun (.cv b) (syn_csn (.cv x)))) p0003 p0005
  have freeVariableCertificate0 : y ∉ ((syn_csn (.cv x))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_y_ne_x,
      not_false_eq_true]
  have freeVariableCertificate1 :
    y ∉
      ((syn_wa (.classEq (syn_cin (.cv b) (syn_csn (.cv x))) (syn_c0))
          (.classEq A (syn_cun (.cv b) (syn_csn (.cv x)))))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_y_ne_b, fresh_y_ne_x,
      fresh_y_not_A, or_false, not_false_eq_true]
  have p0007 :=
    @g_ceqsexv
      (syn_wa (.classEq (syn_cin (.cv b) (.cv y)) (syn_c0))
        (.classEq A (syn_cun (.cv b) (.cv y))))
      (syn_wa (.classEq (syn_cin (.cv b) (syn_csn (.cv x))) (syn_c0))
        (.classEq A (syn_cun (.cv b) (syn_csn (.cv x)))))
      y (syn_csn (.cv x)) freeVariableCertificate0 freeVariableCertificate1 p0001 p0006
  have p0008 := @g_disjsn (.cv b) (.cv x)
  have p0009 := @g_vex x
  have p0010 := @g_elcompl (.cv x) (.cv b) p0009
  have p0011_e00_recanon :
    Nominal.NPrf
      (syn_wb (.classEq (syn_cin (.cv b) (syn_csn (.cv x))) (syn_c0)) (.neg (.objMem x b))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cin syn_ccompl syn_cnin syn_wnan syn_wa syn_csn syn_c0 syn_cdif
          syn_cvv
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
      p0008
  have p0011_e01_recanon :
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
      p0010
  have p0011 :=
    @g_bitr4i (.classEq (syn_cin (.cv b) (syn_csn (.cv x))) (syn_c0)) (.neg (.objMem x b))
      (.classMem (.cv x) (syn_ccompl (.cv b))) p0011_e00_recanon p0011_e01_recanon
  have p0012 :=
    @g_anbi1i (.classEq (syn_cin (.cv b) (syn_csn (.cv x))) (syn_c0))
      (.classMem (.cv x) (syn_ccompl (.cv b)))
      (.classEq A (syn_cun (.cv b) (syn_csn (.cv x)))) p0011
  have p0013 :=
    @g_bitri
      (syn_wex y (syn_wa (.classEq (.cv y) (syn_csn (.cv x)))
          (syn_wa (.classEq (syn_cin (.cv b) (.cv y)) (syn_c0))
            (.classEq A (syn_cun (.cv b) (.cv y))))))
      (syn_wa (.classEq (syn_cin (.cv b) (syn_csn (.cv x))) (syn_c0))
        (.classEq A (syn_cun (.cv b) (syn_csn (.cv x)))))
      (syn_wa (.classMem (.cv x) (syn_ccompl (.cv b)))
        (.classEq A (syn_cun (.cv b) (syn_csn (.cv x)))))
      p0007 p0012
  have p0014 :=
    @g_exbii
      (syn_wex y (syn_wa (.classEq (.cv y) (syn_csn (.cv x)))
          (syn_wa (.classEq (syn_cin (.cv b) (.cv y)) (syn_c0))
            (.classEq A (syn_cun (.cv b) (.cv y))))))
      (syn_wa (.classMem (.cv x) (syn_ccompl (.cv b)))
        (.classEq A (syn_cun (.cv b) (syn_csn (.cv x)))))
      x p0013
  have p0015 :=
    (Nominal.biimpRefl (syn_wrex y (syn_c1c)
        (syn_wa (.classEq (syn_cin (.cv b) (.cv y)) (syn_c0))
          (.classEq A (syn_cun (.cv b) (.cv y))))))
  have freeVariableCertificate2 : x ∉ ((Class.cv y)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_x_ne_y, not_false_eq_true]
  have p0016 := @g_el1c x (.cv y) freeVariableCertificate2
  have p0017 :=
    @g_anbi1i (.classMem (.cv y) (syn_c1c))
      (syn_wex x (.classEq (.cv y) (syn_csn (.cv x))))
      (syn_wa (.classEq (syn_cin (.cv b) (.cv y)) (syn_c0))
        (.classEq A (syn_cun (.cv b) (.cv y))))
      p0016
  have freeVariableCertificate3 :
    x ∉
      ((syn_wa (.classEq (syn_cin (.cv b) (.cv y)) (syn_c0))
          (.classEq A (syn_cun (.cv b) (.cv y))))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_x_ne_y, dv_A_x, (Ne.symm dv_b_x),
      or_false, not_false_eq_true]
  have p0018 :=
    @g_n_19_41v (.classEq (.cv y) (syn_csn (.cv x)))
      (syn_wa (.classEq (syn_cin (.cv b) (.cv y)) (syn_c0))
        (.classEq A (syn_cun (.cv b) (.cv y))))
      x freeVariableCertificate3
  have p0019 :=
    @g_bitr4i
      (syn_wa (.classMem (.cv y) (syn_c1c))
        (syn_wa (.classEq (syn_cin (.cv b) (.cv y)) (syn_c0))
          (.classEq A (syn_cun (.cv b) (.cv y)))))
      (syn_wa (syn_wex x (.classEq (.cv y) (syn_csn (.cv x))))
        (syn_wa (.classEq (syn_cin (.cv b) (.cv y)) (syn_c0))
          (.classEq A (syn_cun (.cv b) (.cv y)))))
      (syn_wex x (syn_wa (.classEq (.cv y) (syn_csn (.cv x)))
          (syn_wa (.classEq (syn_cin (.cv b) (.cv y)) (syn_c0))
            (.classEq A (syn_cun (.cv b) (.cv y))))))
      p0017 p0018
  have p0020 :=
    @g_exbii
      (syn_wa (.classMem (.cv y) (syn_c1c))
        (syn_wa (.classEq (syn_cin (.cv b) (.cv y)) (syn_c0))
          (.classEq A (syn_cun (.cv b) (.cv y)))))
      (syn_wex x (syn_wa (.classEq (.cv y) (syn_csn (.cv x)))
          (syn_wa (.classEq (syn_cin (.cv b) (.cv y)) (syn_c0))
            (.classEq A (syn_cun (.cv b) (.cv y))))))
      y p0019
  have p0021 :=
    @g_excom
      (syn_wa (.classEq (.cv y) (syn_csn (.cv x)))
        (syn_wa (.classEq (syn_cin (.cv b) (.cv y)) (syn_c0))
          (.classEq A (syn_cun (.cv b) (.cv y)))))
      y x
  have p0022 :=
    @g_bitri
      (syn_wex y (syn_wa (.classMem (.cv y) (syn_c1c))
          (syn_wa (.classEq (syn_cin (.cv b) (.cv y)) (syn_c0))
            (.classEq A (syn_cun (.cv b) (.cv y))))))
      (syn_wex y (syn_wex x (syn_wa (.classEq (.cv y) (syn_csn (.cv x)))
            (syn_wa (.classEq (syn_cin (.cv b) (.cv y)) (syn_c0))
              (.classEq A (syn_cun (.cv b) (.cv y)))))))
      (syn_wex x (syn_wex y (syn_wa (.classEq (.cv y) (syn_csn (.cv x)))
            (syn_wa (.classEq (syn_cin (.cv b) (.cv y)) (syn_c0))
              (.classEq A (syn_cun (.cv b) (.cv y)))))))
      p0020 p0021
  have p0023 :=
    @g_bitri
      (syn_wrex y (syn_c1c) (syn_wa (.classEq (syn_cin (.cv b) (.cv y)) (syn_c0))
          (.classEq A (syn_cun (.cv b) (.cv y)))))
      (syn_wex y (syn_wa (.classMem (.cv y) (syn_c1c))
          (syn_wa (.classEq (syn_cin (.cv b) (.cv y)) (syn_c0))
            (.classEq A (syn_cun (.cv b) (.cv y))))))
      (syn_wex x (syn_wex y (syn_wa (.classEq (.cv y) (syn_csn (.cv x)))
            (syn_wa (.classEq (syn_cin (.cv b) (.cv y)) (syn_c0))
              (.classEq A (syn_cun (.cv b) (.cv y)))))))
      p0015 p0022
  have p0024 :=
    (Nominal.biimpRefl
      (syn_wrex x (syn_ccompl (.cv b)) (.classEq A (syn_cun (.cv b) (syn_csn (.cv x))))))
  have p0025 :=
    @g_n_3bitr4i
      (syn_wex x (syn_wex y (syn_wa (.classEq (.cv y) (syn_csn (.cv x)))
            (syn_wa (.classEq (syn_cin (.cv b) (.cv y)) (syn_c0))
              (.classEq A (syn_cun (.cv b) (.cv y)))))))
      (syn_wex x (syn_wa (.classMem (.cv x) (syn_ccompl (.cv b)))
          (.classEq A (syn_cun (.cv b) (syn_csn (.cv x))))))
      (syn_wrex y (syn_c1c) (syn_wa (.classEq (syn_cin (.cv b) (.cv y)) (syn_c0))
          (.classEq A (syn_cun (.cv b) (.cv y)))))
      (syn_wrex x (syn_ccompl (.cv b)) (.classEq A (syn_cun (.cv b) (syn_csn (.cv x)))))
      p0014 p0023 p0024
  have p0026 :=
    @g_rexbii
      (syn_wrex y (syn_c1c) (syn_wa (.classEq (syn_cin (.cv b) (.cv y)) (syn_c0))
          (.classEq A (syn_cun (.cv b) (.cv y)))))
      (syn_wrex x (syn_ccompl (.cv b)) (.classEq A (syn_cun (.cv b) (syn_csn (.cv x))))) b
      M p0025
  have p0027 :=
    @g_bitri (.classMem A (syn_cplc M (syn_c1c)))
      (syn_wrex b M (syn_wrex y (syn_c1c) (syn_wa (.classEq (syn_cin (.cv b) (.cv y)) (syn_c0))
            (.classEq A (syn_cun (.cv b) (.cv y))))))
      (syn_wrex b M (syn_wrex x (syn_ccompl (.cv b))
          (.classEq A (syn_cun (.cv b) (syn_csn (.cv x))))))
      p0000 p0026
  exact p0027

@[expose]
noncomputable def g_elsuci (A : Class) (N : Class) (X : Class)
    (hyp_elsuci_1 : Nominal.NPrf (.classMem X (syn_cvv))) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem A N) (.neg (.classMem X A)))
        (.classMem (syn_cun A (syn_csn X)) (syn_cplc N (syn_c1c)))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ N.fv ∪ X.fv
  let a : Var := freshVar proofSupport 0
  let x : Var := freshVar proofSupport 1
  have fresh_a : a ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_a_not_A : a ∉ A.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_a_not_N : a ∉ N.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_a_not_X : a ∉ X.fv := by
    intro h
    exact fresh_a (Finset.mem_union_right _ (h))
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_x_not_X : x ∉ X.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_a_ne_x : a ≠ x :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_x_ne_a : x ≠ a := Ne.symm fresh_a_ne_x
  have p0000 := @g_elcompl X A hyp_elsuci_1
  have p0001 := @g_eqid (syn_cun A (syn_csn X))
  have p0002 := @g_sneq (.cv x) X
  have p0003 := @g_uneq2d (.classEq (.cv x) X) (syn_csn (.cv x)) (syn_csn X) A p0002
  have p0004 :=
    @g_eqeq2d (.classEq (.cv x) X) (syn_cun A (syn_csn (.cv x))) (syn_cun A (syn_csn X))
      (syn_cun A (syn_csn X)) p0003
  have freeVariableCertificate0 :
    x ∉ ((Wff.classEq (syn_cun A (syn_csn X)) (syn_cun A (syn_csn X)))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
      fresh_x_not_A, fresh_x_not_X, or_false, not_false_eq_true]
  have p0005 :=
    @g_rspcev (.classEq (syn_cun A (syn_csn X)) (syn_cun A (syn_csn (.cv x))))
      (.classEq (syn_cun A (syn_csn X)) (syn_cun A (syn_csn X))) x X (syn_ccompl A)
      (by exact (show x ∉ (X).fv from (by exact fresh_x_not_X)))
      (by
        exact
          (show x ∉ ((syn_ccompl A)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl];
              exact (show x ∉ (A).fv from (by exact fresh_x_not_A)))))
      freeVariableCertificate0 p0004
  have p0006 :=
    @g_mpan2 (.classMem X (syn_ccompl A))
      (.classEq (syn_cun A (syn_csn X)) (syn_cun A (syn_csn X)))
      (syn_wrex x (syn_ccompl A)
        (.classEq (syn_cun A (syn_csn X)) (syn_cun A (syn_csn (.cv x)))))
      p0001 p0005
  have p0007 :=
    @g_sylbir (.neg (.classMem X A)) (.classMem X (syn_ccompl A))
      (syn_wrex x (syn_ccompl A)
        (.classEq (syn_cun A (syn_csn X)) (syn_cun A (syn_csn (.cv x)))))
      p0000 p0006
  have p0008 := @g_compleq (.cv a) A
  have p0009 := @g_uneq1 (.cv a) A (syn_csn (.cv x))
  have p0010 :=
    @g_eqeq2d (.classEq (.cv a) A) (syn_cun (.cv a) (syn_csn (.cv x)))
      (syn_cun A (syn_csn (.cv x))) (syn_cun A (syn_csn X)) p0009
  have freeVariableCertificate1 : x ∉ ((syn_ccompl (.cv a))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_x_ne_a,
      not_false_eq_true]
  have freeVariableCertificate2 : x ∉ ((Wff.classEq (.cv a) A)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      fresh_x_ne_a, fresh_x_not_A, or_false, not_false_eq_true]
  have p0011 :=
    @g_rexeqbidv (.classEq (.cv a) A)
      (.classEq (syn_cun A (syn_csn X)) (syn_cun (.cv a) (syn_csn (.cv x))))
      (.classEq (syn_cun A (syn_csn X)) (syn_cun A (syn_csn (.cv x)))) x
      (syn_ccompl (.cv a)) (syn_ccompl A) freeVariableCertificate1
      (by
        exact
          (show x ∉ ((syn_ccompl A)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl];
              exact (show x ∉ (A).fv from (by exact fresh_x_not_A)))))
      freeVariableCertificate2 p0008 p0010
  have freeVariableCertificate3 :
    a ∉
      ((syn_wrex x (syn_ccompl A)
          (.classEq (syn_cun A (syn_csn X)) (syn_cun A (syn_csn (.cv x)))))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
      Finset.mem_singleton, fresh_a_not_A, fresh_a_not_X, fresh_a_ne_x, or_false,
      and_false, not_false_eq_true]
  have p0012 :=
    @g_rspcev
      (syn_wrex x (syn_ccompl (.cv a))
        (.classEq (syn_cun A (syn_csn X)) (syn_cun (.cv a) (syn_csn (.cv x)))))
      (syn_wrex x (syn_ccompl A)
        (.classEq (syn_cun A (syn_csn X)) (syn_cun A (syn_csn (.cv x)))))
      a A N (by exact (show a ∉ (A).fv from (by exact fresh_a_not_A)))
      (by exact (show a ∉ (N).fv from (by exact fresh_a_not_N))) freeVariableCertificate3
      p0011
  have p0013 :=
    @g_sylan2 (.neg (.classMem X A)) (.classMem A N)
      (syn_wrex x (syn_ccompl A)
        (.classEq (syn_cun A (syn_csn X)) (syn_cun A (syn_csn (.cv x)))))
      (syn_wrex a N (syn_wrex x (syn_ccompl (.cv a))
          (.classEq (syn_cun A (syn_csn X)) (syn_cun (.cv a) (syn_csn (.cv x))))))
      p0007 p0012
  have freeVariableCertificate4 : a ∉ ((syn_cun A (syn_csn X))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
      fresh_a_not_A, fresh_a_not_X, or_false, not_false_eq_true]
  have freeVariableCertificate5 : x ∉ ((syn_cun A (syn_csn X))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
      fresh_x_not_A, fresh_x_not_X, or_false, not_false_eq_true]
  have p0014 :=
    @g_elsuc x (syn_cun A (syn_csn X)) N a freeVariableCertificate4
      freeVariableCertificate5 (by exact (show a ∉ (N).fv from (by exact fresh_a_not_N)))
      (show a ≠ x from (by exact fresh_a_ne_x))
  have p0015 :=
    @g_sylibr (syn_wa (.classMem A N) (.neg (.classMem X A)))
      (syn_wrex a N (syn_wrex x (syn_ccompl (.cv a))
          (.classEq (syn_cun A (syn_csn X)) (syn_cun (.cv a) (syn_csn (.cv x))))))
      (.classMem (syn_cun A (syn_csn X)) (syn_cplc N (syn_c1c))) p0013 p0014
  exact p0015


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk009StructuralPart029`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_addcass (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.classEq (syn_cplc (syn_cplc A B) C) (syn_cplc A (syn_cplc B C))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv
  let x : Var := freshVar proofSupport 0
  let a : Var := freshVar proofSupport 1
  let b : Var := freshVar proofSupport 2
  let d : Var := freshVar proofSupport 3
  let c : Var := freshVar proofSupport 4
  let e : Var := freshVar proofSupport 5
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
  have fresh_a : a ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_a_not_A : a ∉ A.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_a_not_B : a ∉ B.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_a_not_C : a ∉ C.fv := by
    intro h
    exact fresh_a (Finset.mem_union_right _ (h))
  have fresh_b : b ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_b_not_A : b ∉ A.fv := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_b_not_B : b ∉ B.fv := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_b_not_C : b ∉ C.fv := by
    intro h
    exact fresh_b (Finset.mem_union_right _ (h))
  have fresh_d : d ∉ proofSupport :=
    by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_d_not_A : d ∉ A.fv := by
    intro h
    exact fresh_d (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_d_not_B : d ∉ B.fv := by
    intro h
    exact fresh_d (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_d_not_C : d ∉ C.fv := by
    intro h
    exact fresh_d (Finset.mem_union_right _ (h))
  have fresh_c : c ∉ proofSupport :=
    by
    change freshVar proofSupport 4 ∉ proofSupport
    exact freshVar_not_mem proofSupport 4
  have fresh_c_not_A : c ∉ A.fv := by
    intro h
    exact fresh_c (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_c_not_B : c ∉ B.fv := by
    intro h
    exact fresh_c (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_c_not_C : c ∉ C.fv := by
    intro h
    exact fresh_c (Finset.mem_union_right _ (h))
  have fresh_e : e ∉ proofSupport :=
    by
    change freshVar proofSupport 5 ∉ proofSupport
    exact freshVar_not_mem proofSupport 5
  have fresh_e_not_A : e ∉ A.fv := by
    intro h
    exact fresh_e (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_e_not_B : e ∉ B.fv := by
    intro h
    exact fresh_e (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_e_not_C : e ∉ C.fv := by
    intro h
    exact fresh_e (Finset.mem_union_right _ (h))
  have fresh_x_ne_a : x ≠ a :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_a_ne_x : a ≠ x := Ne.symm fresh_x_ne_a
  have fresh_x_ne_b : x ≠ b :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_b_ne_x : b ≠ x := Ne.symm fresh_x_ne_b
  have fresh_x_ne_d : x ≠ d :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_d_ne_x : d ≠ x := Ne.symm fresh_x_ne_d
  have fresh_x_ne_c : x ≠ c :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 0) (j := 4) (by decide)
  have fresh_c_ne_x : c ≠ x := Ne.symm fresh_x_ne_c
  have fresh_x_ne_e : x ≠ e :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 0) (j := 5) (by decide)
  have fresh_e_ne_x : e ≠ x := Ne.symm fresh_x_ne_e
  have fresh_a_ne_b : a ≠ b :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_b_ne_a : b ≠ a := Ne.symm fresh_a_ne_b
  have fresh_a_ne_d : a ≠ d :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_d_ne_a : d ≠ a := Ne.symm fresh_a_ne_d
  have fresh_a_ne_c : a ≠ c :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 1) (j := 4) (by decide)
  have fresh_c_ne_a : c ≠ a := Ne.symm fresh_a_ne_c
  have fresh_a_ne_e : a ≠ e :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 1) (j := 5) (by decide)
  have fresh_e_ne_a : e ≠ a := Ne.symm fresh_a_ne_e
  have fresh_b_ne_d : b ≠ d :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_d_ne_b : d ≠ b := Ne.symm fresh_b_ne_d
  have fresh_b_ne_c : b ≠ c :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 2) (j := 4) (by decide)
  have fresh_c_ne_b : c ≠ b := Ne.symm fresh_b_ne_c
  have fresh_b_ne_e : b ≠ e :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 2) (j := 5) (by decide)
  have fresh_e_ne_b : e ≠ b := Ne.symm fresh_b_ne_e
  have fresh_d_ne_c : d ≠ c :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 3) (j := 4) (by decide)
  have fresh_c_ne_d : c ≠ d := Ne.symm fresh_d_ne_c
  have fresh_c_ne_e : c ≠ e :=
    by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 4) (j := 5) (by decide)
  have fresh_e_ne_c : e ≠ c := Ne.symm fresh_c_ne_e
  have p0000 :=
    @g_ancom (.classEq (syn_cin (.cv a) (.cv c)) (syn_c0))
      (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0))
  have p0001 :=
    @g_anbi2i
      (syn_wa (.classEq (syn_cin (.cv a) (.cv c)) (syn_c0))
        (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0)))
      (syn_wa (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0))
        (.classEq (syn_cin (.cv a) (.cv c)) (syn_c0)))
      (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0)) p0000
  have p0002 :=
    @g_an12 (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0))
      (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0))
      (.classEq (syn_cin (.cv a) (.cv c)) (syn_c0))
  have p0003 :=
    @g_bitri
      (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0))
        (syn_wa (.classEq (syn_cin (.cv a) (.cv c)) (syn_c0))
          (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0))))
      (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0))
        (syn_wa (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0))
          (.classEq (syn_cin (.cv a) (.cv c)) (syn_c0))))
      (syn_wa (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0))
        (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0))
          (.classEq (syn_cin (.cv a) (.cv c)) (syn_c0))))
      p0001 p0002
  have p0004 := @g_indir (.cv a) (.cv b) (.cv c)
  have p0005 :=
    @g_eqeq1i (syn_cin (syn_cun (.cv a) (.cv b)) (.cv c))
      (syn_cun (syn_cin (.cv a) (.cv c)) (syn_cin (.cv b) (.cv c))) (syn_c0) p0004
  have p0006 := @g_un00 (syn_cin (.cv a) (.cv c)) (syn_cin (.cv b) (.cv c))
  have p0007 :=
    @g_bitr4i (.classEq (syn_cin (syn_cun (.cv a) (.cv b)) (.cv c)) (syn_c0))
      (.classEq (syn_cun (syn_cin (.cv a) (.cv c)) (syn_cin (.cv b) (.cv c))) (syn_c0))
      (syn_wa (.classEq (syn_cin (.cv a) (.cv c)) (syn_c0))
        (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0)))
      p0005 p0006
  have p0008 :=
    @g_anbi2i (.classEq (syn_cin (syn_cun (.cv a) (.cv b)) (.cv c)) (syn_c0))
      (syn_wa (.classEq (syn_cin (.cv a) (.cv c)) (syn_c0))
        (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0)))
      (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0)) p0007
  have p0009 := @g_indi (.cv a) (.cv b) (.cv c)
  have p0010 :=
    @g_eqeq1i (syn_cin (.cv a) (syn_cun (.cv b) (.cv c)))
      (syn_cun (syn_cin (.cv a) (.cv b)) (syn_cin (.cv a) (.cv c))) (syn_c0) p0009
  have p0011 := @g_un00 (syn_cin (.cv a) (.cv b)) (syn_cin (.cv a) (.cv c))
  have p0012 :=
    @g_bitr4i (.classEq (syn_cin (.cv a) (syn_cun (.cv b) (.cv c))) (syn_c0))
      (.classEq (syn_cun (syn_cin (.cv a) (.cv b)) (syn_cin (.cv a) (.cv c))) (syn_c0))
      (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0))
        (.classEq (syn_cin (.cv a) (.cv c)) (syn_c0)))
      p0010 p0011
  have p0013 :=
    @g_anbi2i (.classEq (syn_cin (.cv a) (syn_cun (.cv b) (.cv c))) (syn_c0))
      (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0))
        (.classEq (syn_cin (.cv a) (.cv c)) (syn_c0)))
      (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0)) p0012
  have p0014 :=
    @g_n_3bitr4i
      (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0))
        (syn_wa (.classEq (syn_cin (.cv a) (.cv c)) (syn_c0))
          (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0))))
      (syn_wa (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0))
        (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0))
          (.classEq (syn_cin (.cv a) (.cv c)) (syn_c0))))
      (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0))
        (.classEq (syn_cin (syn_cun (.cv a) (.cv b)) (.cv c)) (syn_c0)))
      (syn_wa (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0))
        (.classEq (syn_cin (.cv a) (syn_cun (.cv b) (.cv c))) (syn_c0)))
      p0003 p0008 p0013
  have p0015 := @g_unass (.cv a) (.cv b) (.cv c)
  have p0016 :=
    @g_eqeq2i (syn_cun (syn_cun (.cv a) (.cv b)) (.cv c))
      (syn_cun (.cv a) (syn_cun (.cv b) (.cv c))) (.cv x) p0015
  have p0017 :=
    @g_anbi12i
      (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0))
        (.classEq (syn_cin (syn_cun (.cv a) (.cv b)) (.cv c)) (syn_c0)))
      (syn_wa (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0))
        (.classEq (syn_cin (.cv a) (syn_cun (.cv b) (.cv c))) (syn_c0)))
      (.classEq (.cv x) (syn_cun (syn_cun (.cv a) (.cv b)) (.cv c)))
      (.classEq (.cv x) (syn_cun (.cv a) (syn_cun (.cv b) (.cv c)))) p0014 p0016
  have p0018 :=
    @g_anass (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0))
      (.classEq (syn_cin (syn_cun (.cv a) (.cv b)) (.cv c)) (syn_c0))
      (.classEq (.cv x) (syn_cun (syn_cun (.cv a) (.cv b)) (.cv c)))
  have p0019 :=
    @g_anass (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0))
      (.classEq (syn_cin (.cv a) (syn_cun (.cv b) (.cv c))) (syn_c0))
      (.classEq (.cv x) (syn_cun (.cv a) (syn_cun (.cv b) (.cv c))))
  have p0020 :=
    @g_n_3bitr3i
      (syn_wa (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0))
          (.classEq (syn_cin (syn_cun (.cv a) (.cv b)) (.cv c)) (syn_c0)))
        (.classEq (.cv x) (syn_cun (syn_cun (.cv a) (.cv b)) (.cv c))))
      (syn_wa (syn_wa (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0))
          (.classEq (syn_cin (.cv a) (syn_cun (.cv b) (.cv c))) (syn_c0)))
        (.classEq (.cv x) (syn_cun (.cv a) (syn_cun (.cv b) (.cv c)))))
      (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0))
        (syn_wa (.classEq (syn_cin (syn_cun (.cv a) (.cv b)) (.cv c)) (syn_c0))
          (.classEq (.cv x) (syn_cun (syn_cun (.cv a) (.cv b)) (.cv c)))))
      (syn_wa (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0))
        (syn_wa (.classEq (syn_cin (.cv a) (syn_cun (.cv b) (.cv c))) (syn_c0))
          (.classEq (.cv x) (syn_cun (.cv a) (syn_cun (.cv b) (.cv c))))))
      p0017 p0018 p0019
  have p0021 :=
    @g_anass (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0))
      (.classEq (.cv d) (syn_cun (.cv a) (.cv b)))
      (syn_wa (.classEq (syn_cin (.cv d) (.cv c)) (syn_c0))
        (.classEq (.cv x) (syn_cun (.cv d) (.cv c))))
  have p0022 :=
    @g_an12 (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0))
      (.classEq (.cv d) (syn_cun (.cv a) (.cv b)))
      (syn_wa (.classEq (syn_cin (.cv d) (.cv c)) (syn_c0))
        (.classEq (.cv x) (syn_cun (.cv d) (.cv c))))
  have p0023 :=
    @g_bitri
      (syn_wa (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0))
          (.classEq (.cv d) (syn_cun (.cv a) (.cv b))))
        (syn_wa (.classEq (syn_cin (.cv d) (.cv c)) (syn_c0))
          (.classEq (.cv x) (syn_cun (.cv d) (.cv c)))))
      (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0))
        (syn_wa (.classEq (.cv d) (syn_cun (.cv a) (.cv b)))
          (syn_wa (.classEq (syn_cin (.cv d) (.cv c)) (syn_c0))
            (.classEq (.cv x) (syn_cun (.cv d) (.cv c))))))
      (syn_wa (.classEq (.cv d) (syn_cun (.cv a) (.cv b)))
        (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0))
          (syn_wa (.classEq (syn_cin (.cv d) (.cv c)) (syn_c0))
            (.classEq (.cv x) (syn_cun (.cv d) (.cv c))))))
      p0021 p0022
  have p0024 :=
    @g_exbii
      (syn_wa (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0))
          (.classEq (.cv d) (syn_cun (.cv a) (.cv b))))
        (syn_wa (.classEq (syn_cin (.cv d) (.cv c)) (syn_c0))
          (.classEq (.cv x) (syn_cun (.cv d) (.cv c)))))
      (syn_wa (.classEq (.cv d) (syn_cun (.cv a) (.cv b)))
        (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0))
          (syn_wa (.classEq (syn_cin (.cv d) (.cv c)) (syn_c0))
            (.classEq (.cv x) (syn_cun (.cv d) (.cv c))))))
      d p0023
  have p0025 := @g_vex a
  have p0026 := @g_vex b
  have p0027 := @g_unex (.cv a) (.cv b) p0025 p0026
  have p0028 := @g_ineq1 (.cv d) (syn_cun (.cv a) (.cv b)) (.cv c)
  have p0029 :=
    @g_eqeq1d (.classEq (.cv d) (syn_cun (.cv a) (.cv b))) (syn_cin (.cv d) (.cv c))
      (syn_cin (syn_cun (.cv a) (.cv b)) (.cv c)) (syn_c0) p0028
  have p0030 := @g_uneq1 (.cv d) (syn_cun (.cv a) (.cv b)) (.cv c)
  have p0031 :=
    @g_eqeq2d (.classEq (.cv d) (syn_cun (.cv a) (.cv b))) (syn_cun (.cv d) (.cv c))
      (syn_cun (syn_cun (.cv a) (.cv b)) (.cv c)) (.cv x) p0030
  have p0032 :=
    @g_anbi12d (.classEq (.cv d) (syn_cun (.cv a) (.cv b)))
      (.classEq (syn_cin (.cv d) (.cv c)) (syn_c0))
      (.classEq (syn_cin (syn_cun (.cv a) (.cv b)) (.cv c)) (syn_c0))
      (.classEq (.cv x) (syn_cun (.cv d) (.cv c)))
      (.classEq (.cv x) (syn_cun (syn_cun (.cv a) (.cv b)) (.cv c))) p0029 p0031
  have p0033 :=
    @g_anbi2d (.classEq (.cv d) (syn_cun (.cv a) (.cv b)))
      (syn_wa (.classEq (syn_cin (.cv d) (.cv c)) (syn_c0))
        (.classEq (.cv x) (syn_cun (.cv d) (.cv c))))
      (syn_wa (.classEq (syn_cin (syn_cun (.cv a) (.cv b)) (.cv c)) (syn_c0))
        (.classEq (.cv x) (syn_cun (syn_cun (.cv a) (.cv b)) (.cv c))))
      (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0)) p0032
  have freeVariableCertificate0 : d ∉ ((syn_cun (.cv a) (.cv b))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      fresh_d_ne_a, fresh_d_ne_b, or_false, not_false_eq_true]
  have freeVariableCertificate1 :
    d ∉
      ((syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0))
          (syn_wa (.classEq (syn_cin (syn_cun (.cv a) (.cv b)) (.cv c)) (syn_c0))
            (.classEq (.cv x) (syn_cun (syn_cun (.cv a) (.cv b)) (.cv c)))))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_d_ne_a, fresh_d_ne_b, fresh_d_ne_c,
      fresh_d_ne_x, or_false, not_false_eq_true]
  have p0034 :=
    @g_ceqsexv
      (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0))
        (syn_wa (.classEq (syn_cin (.cv d) (.cv c)) (syn_c0))
          (.classEq (.cv x) (syn_cun (.cv d) (.cv c)))))
      (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0))
        (syn_wa (.classEq (syn_cin (syn_cun (.cv a) (.cv b)) (.cv c)) (syn_c0))
          (.classEq (.cv x) (syn_cun (syn_cun (.cv a) (.cv b)) (.cv c)))))
      d (syn_cun (.cv a) (.cv b)) freeVariableCertificate0 freeVariableCertificate1 p0027
      p0033
  have p0035 :=
    @g_bitri
      (syn_wex d (syn_wa (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0))
            (.classEq (.cv d) (syn_cun (.cv a) (.cv b))))
          (syn_wa (.classEq (syn_cin (.cv d) (.cv c)) (syn_c0))
            (.classEq (.cv x) (syn_cun (.cv d) (.cv c))))))
      (syn_wex d (syn_wa (.classEq (.cv d) (syn_cun (.cv a) (.cv b)))
          (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0))
            (syn_wa (.classEq (syn_cin (.cv d) (.cv c)) (syn_c0))
              (.classEq (.cv x) (syn_cun (.cv d) (.cv c)))))))
      (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0))
        (syn_wa (.classEq (syn_cin (syn_cun (.cv a) (.cv b)) (.cv c)) (syn_c0))
          (.classEq (.cv x) (syn_cun (syn_cun (.cv a) (.cv b)) (.cv c)))))
      p0024 p0034
  have p0036 :=
    @g_anass (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0))
      (.classEq (.cv e) (syn_cun (.cv b) (.cv c)))
      (syn_wa (.classEq (syn_cin (.cv a) (.cv e)) (syn_c0))
        (.classEq (.cv x) (syn_cun (.cv a) (.cv e))))
  have p0037 :=
    @g_an12 (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0))
      (.classEq (.cv e) (syn_cun (.cv b) (.cv c)))
      (syn_wa (.classEq (syn_cin (.cv a) (.cv e)) (syn_c0))
        (.classEq (.cv x) (syn_cun (.cv a) (.cv e))))
  have p0038 :=
    @g_bitri
      (syn_wa (syn_wa (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0))
          (.classEq (.cv e) (syn_cun (.cv b) (.cv c))))
        (syn_wa (.classEq (syn_cin (.cv a) (.cv e)) (syn_c0))
          (.classEq (.cv x) (syn_cun (.cv a) (.cv e)))))
      (syn_wa (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0))
        (syn_wa (.classEq (.cv e) (syn_cun (.cv b) (.cv c)))
          (syn_wa (.classEq (syn_cin (.cv a) (.cv e)) (syn_c0))
            (.classEq (.cv x) (syn_cun (.cv a) (.cv e))))))
      (syn_wa (.classEq (.cv e) (syn_cun (.cv b) (.cv c)))
        (syn_wa (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0))
          (syn_wa (.classEq (syn_cin (.cv a) (.cv e)) (syn_c0))
            (.classEq (.cv x) (syn_cun (.cv a) (.cv e))))))
      p0036 p0037
  have p0039 :=
    @g_exbii
      (syn_wa (syn_wa (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0))
          (.classEq (.cv e) (syn_cun (.cv b) (.cv c))))
        (syn_wa (.classEq (syn_cin (.cv a) (.cv e)) (syn_c0))
          (.classEq (.cv x) (syn_cun (.cv a) (.cv e)))))
      (syn_wa (.classEq (.cv e) (syn_cun (.cv b) (.cv c)))
        (syn_wa (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0))
          (syn_wa (.classEq (syn_cin (.cv a) (.cv e)) (syn_c0))
            (.classEq (.cv x) (syn_cun (.cv a) (.cv e))))))
      e p0038
  have p0040 := @g_vex c
  have p0041 := @g_unex (.cv b) (.cv c) p0026 p0040
  have p0042 := @g_ineq2 (.cv e) (syn_cun (.cv b) (.cv c)) (.cv a)
  have p0043 :=
    @g_eqeq1d (.classEq (.cv e) (syn_cun (.cv b) (.cv c))) (syn_cin (.cv a) (.cv e))
      (syn_cin (.cv a) (syn_cun (.cv b) (.cv c))) (syn_c0) p0042
  have p0044 := @g_uneq2 (.cv e) (syn_cun (.cv b) (.cv c)) (.cv a)
  have p0045 :=
    @g_eqeq2d (.classEq (.cv e) (syn_cun (.cv b) (.cv c))) (syn_cun (.cv a) (.cv e))
      (syn_cun (.cv a) (syn_cun (.cv b) (.cv c))) (.cv x) p0044
  have p0046 :=
    @g_anbi12d (.classEq (.cv e) (syn_cun (.cv b) (.cv c)))
      (.classEq (syn_cin (.cv a) (.cv e)) (syn_c0))
      (.classEq (syn_cin (.cv a) (syn_cun (.cv b) (.cv c))) (syn_c0))
      (.classEq (.cv x) (syn_cun (.cv a) (.cv e)))
      (.classEq (.cv x) (syn_cun (.cv a) (syn_cun (.cv b) (.cv c)))) p0043 p0045
  have p0047 :=
    @g_anbi2d (.classEq (.cv e) (syn_cun (.cv b) (.cv c)))
      (syn_wa (.classEq (syn_cin (.cv a) (.cv e)) (syn_c0))
        (.classEq (.cv x) (syn_cun (.cv a) (.cv e))))
      (syn_wa (.classEq (syn_cin (.cv a) (syn_cun (.cv b) (.cv c))) (syn_c0))
        (.classEq (.cv x) (syn_cun (.cv a) (syn_cun (.cv b) (.cv c)))))
      (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0)) p0046
  have freeVariableCertificate2 : e ∉ ((syn_cun (.cv b) (.cv c))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      fresh_e_ne_b, fresh_e_ne_c, or_false, not_false_eq_true]
  have freeVariableCertificate3 :
    e ∉
      ((syn_wa (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0))
          (syn_wa (.classEq (syn_cin (.cv a) (syn_cun (.cv b) (.cv c))) (syn_c0))
            (.classEq (.cv x) (syn_cun (.cv a) (syn_cun (.cv b) (.cv c))))))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_e_ne_b, fresh_e_ne_c, fresh_e_ne_a,
      fresh_e_ne_x, or_false, not_false_eq_true]
  have p0048 :=
    @g_ceqsexv
      (syn_wa (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0))
        (syn_wa (.classEq (syn_cin (.cv a) (.cv e)) (syn_c0))
          (.classEq (.cv x) (syn_cun (.cv a) (.cv e)))))
      (syn_wa (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0))
        (syn_wa (.classEq (syn_cin (.cv a) (syn_cun (.cv b) (.cv c))) (syn_c0))
          (.classEq (.cv x) (syn_cun (.cv a) (syn_cun (.cv b) (.cv c))))))
      e (syn_cun (.cv b) (.cv c)) freeVariableCertificate2 freeVariableCertificate3 p0041
      p0047
  have p0049 :=
    @g_bitri
      (syn_wex e (syn_wa (syn_wa (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0))
            (.classEq (.cv e) (syn_cun (.cv b) (.cv c))))
          (syn_wa (.classEq (syn_cin (.cv a) (.cv e)) (syn_c0))
            (.classEq (.cv x) (syn_cun (.cv a) (.cv e))))))
      (syn_wex e (syn_wa (.classEq (.cv e) (syn_cun (.cv b) (.cv c)))
          (syn_wa (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0))
            (syn_wa (.classEq (syn_cin (.cv a) (.cv e)) (syn_c0))
              (.classEq (.cv x) (syn_cun (.cv a) (.cv e)))))))
      (syn_wa (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0))
        (syn_wa (.classEq (syn_cin (.cv a) (syn_cun (.cv b) (.cv c))) (syn_c0))
          (.classEq (.cv x) (syn_cun (.cv a) (syn_cun (.cv b) (.cv c))))))
      p0039 p0048
  have p0050 :=
    @g_n_3bitr4i
      (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0))
        (syn_wa (.classEq (syn_cin (syn_cun (.cv a) (.cv b)) (.cv c)) (syn_c0))
          (.classEq (.cv x) (syn_cun (syn_cun (.cv a) (.cv b)) (.cv c)))))
      (syn_wa (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0))
        (syn_wa (.classEq (syn_cin (.cv a) (syn_cun (.cv b) (.cv c))) (syn_c0))
          (.classEq (.cv x) (syn_cun (.cv a) (syn_cun (.cv b) (.cv c))))))
      (syn_wex d (syn_wa (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0))
            (.classEq (.cv d) (syn_cun (.cv a) (.cv b))))
          (syn_wa (.classEq (syn_cin (.cv d) (.cv c)) (syn_c0))
            (.classEq (.cv x) (syn_cun (.cv d) (.cv c))))))
      (syn_wex e (syn_wa (syn_wa (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0))
            (.classEq (.cv e) (syn_cun (.cv b) (.cv c))))
          (syn_wa (.classEq (syn_cin (.cv a) (.cv e)) (syn_c0))
            (.classEq (.cv x) (syn_cun (.cv a) (.cv e))))))
      p0020 p0035 p0049
  have p0051 :=
    @g_rexbii
      (syn_wex d (syn_wa (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0))
            (.classEq (.cv d) (syn_cun (.cv a) (.cv b))))
          (syn_wa (.classEq (syn_cin (.cv d) (.cv c)) (syn_c0))
            (.classEq (.cv x) (syn_cun (.cv d) (.cv c))))))
      (syn_wex e (syn_wa (syn_wa (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0))
            (.classEq (.cv e) (syn_cun (.cv b) (.cv c))))
          (syn_wa (.classEq (syn_cin (.cv a) (.cv e)) (syn_c0))
            (.classEq (.cv x) (syn_cun (.cv a) (.cv e))))))
      c C p0050
  have p0052 :=
    @g_n_2rexbii
      (syn_wrex c C (syn_wex d (syn_wa (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0))
              (.classEq (.cv d) (syn_cun (.cv a) (.cv b))))
            (syn_wa (.classEq (syn_cin (.cv d) (.cv c)) (syn_c0))
              (.classEq (.cv x) (syn_cun (.cv d) (.cv c)))))))
      (syn_wrex c C (syn_wex e (syn_wa (syn_wa (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0))
              (.classEq (.cv e) (syn_cun (.cv b) (.cv c))))
            (syn_wa (.classEq (syn_cin (.cv a) (.cv e)) (syn_c0))
              (.classEq (.cv x) (syn_cun (.cv a) (.cv e)))))))
      a b A B p0051
  have freeVariableCertificate4 : d ∉ ((Class.cv x)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_d_ne_x, not_false_eq_true]
  have freeVariableCertificate5 : c ∉ ((Class.cv x)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_c_ne_x, not_false_eq_true]
  have freeVariableCertificate6 : d ∉ ((syn_cplc A B)).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, Finset.mem_union,
      fresh_d_not_A, fresh_d_not_B, or_false, not_false_eq_true]
  have freeVariableCertificate7 : c ∉ ((syn_cplc A B)).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, Finset.mem_union,
      fresh_c_not_A, fresh_c_not_B, or_false, not_false_eq_true]
  have p0053 :=
    @g_eladdc (.cv x) (syn_cplc A B) C d c freeVariableCertificate4
      freeVariableCertificate5 freeVariableCertificate6 freeVariableCertificate7
      (by exact (show d ∉ (C).fv from (by exact fresh_d_not_C)))
      (by exact (show c ∉ (C).fv from (by exact fresh_c_not_C)))
      (show d ≠ c from (by exact fresh_d_ne_c))
  have p0054 :=
    (Nominal.biimpRefl (syn_wrex d (syn_cplc A B) (syn_wrex c C
          (syn_wa (.classEq (syn_cin (.cv d) (.cv c)) (syn_c0))
            (.classEq (.cv x) (syn_cun (.cv d) (.cv c)))))))
  have p0055 :=
    @g_rexcom4
      (syn_wrex b B (syn_wa (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0))
            (.classEq (.cv d) (syn_cun (.cv a) (.cv b)))) (syn_wrex c C
            (syn_wa (.classEq (syn_cin (.cv d) (.cv c)) (syn_c0))
              (.classEq (.cv x) (syn_cun (.cv d) (.cv c)))))))
      a d A (by exact (show d ∉ (A).fv from (by exact fresh_d_not_A)))
      (show a ≠ d from (by exact fresh_a_ne_d))
  have p0056 :=
    @g_rexcom4
      (syn_wa (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0))
          (.classEq (.cv d) (syn_cun (.cv a) (.cv b))))
        (syn_wa (.classEq (syn_cin (.cv d) (.cv c)) (syn_c0))
          (.classEq (.cv x) (syn_cun (.cv d) (.cv c)))))
      c d C (by exact (show d ∉ (C).fv from (by exact fresh_d_not_C)))
      (show c ≠ d from (by exact fresh_c_ne_d))
  have freeVariableCertificate8 :
    c ∉
      ((syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0))
          (.classEq (.cv d) (syn_cun (.cv a) (.cv b))))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_c_ne_a, fresh_c_ne_b, fresh_c_ne_d,
      or_false, not_false_eq_true]
  have p0057 :=
    @g_r19_42v
      (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0))
        (.classEq (.cv d) (syn_cun (.cv a) (.cv b))))
      (syn_wa (.classEq (syn_cin (.cv d) (.cv c)) (syn_c0))
        (.classEq (.cv x) (syn_cun (.cv d) (.cv c))))
      c C freeVariableCertificate8
  have p0058 :=
    @g_exbii
      (syn_wrex c C (syn_wa (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0))
            (.classEq (.cv d) (syn_cun (.cv a) (.cv b))))
          (syn_wa (.classEq (syn_cin (.cv d) (.cv c)) (syn_c0))
            (.classEq (.cv x) (syn_cun (.cv d) (.cv c))))))
      (syn_wa (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0))
          (.classEq (.cv d) (syn_cun (.cv a) (.cv b)))) (syn_wrex c C
          (syn_wa (.classEq (syn_cin (.cv d) (.cv c)) (syn_c0))
            (.classEq (.cv x) (syn_cun (.cv d) (.cv c))))))
      d p0057
  have p0059 :=
    @g_bitri
      (syn_wrex c C (syn_wex d (syn_wa (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0))
              (.classEq (.cv d) (syn_cun (.cv a) (.cv b))))
            (syn_wa (.classEq (syn_cin (.cv d) (.cv c)) (syn_c0))
              (.classEq (.cv x) (syn_cun (.cv d) (.cv c)))))))
      (syn_wex d (syn_wrex c C (syn_wa (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0))
              (.classEq (.cv d) (syn_cun (.cv a) (.cv b))))
            (syn_wa (.classEq (syn_cin (.cv d) (.cv c)) (syn_c0))
              (.classEq (.cv x) (syn_cun (.cv d) (.cv c)))))))
      (syn_wex d (syn_wa (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0))
            (.classEq (.cv d) (syn_cun (.cv a) (.cv b)))) (syn_wrex c C
            (syn_wa (.classEq (syn_cin (.cv d) (.cv c)) (syn_c0))
              (.classEq (.cv x) (syn_cun (.cv d) (.cv c)))))))
      p0056 p0058
  have p0060 :=
    @g_rexbii
      (syn_wrex c C (syn_wex d (syn_wa (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0))
              (.classEq (.cv d) (syn_cun (.cv a) (.cv b))))
            (syn_wa (.classEq (syn_cin (.cv d) (.cv c)) (syn_c0))
              (.classEq (.cv x) (syn_cun (.cv d) (.cv c)))))))
      (syn_wex d (syn_wa (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0))
            (.classEq (.cv d) (syn_cun (.cv a) (.cv b)))) (syn_wrex c C
            (syn_wa (.classEq (syn_cin (.cv d) (.cv c)) (syn_c0))
              (.classEq (.cv x) (syn_cun (.cv d) (.cv c)))))))
      b B p0059
  have p0061 :=
    @g_rexcom4
      (syn_wa (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0))
          (.classEq (.cv d) (syn_cun (.cv a) (.cv b)))) (syn_wrex c C
          (syn_wa (.classEq (syn_cin (.cv d) (.cv c)) (syn_c0))
            (.classEq (.cv x) (syn_cun (.cv d) (.cv c))))))
      b d B (by exact (show d ∉ (B).fv from (by exact fresh_d_not_B)))
      (show b ≠ d from (by exact fresh_b_ne_d))
  have p0062 :=
    @g_bitri
      (syn_wrex b B (syn_wrex c C (syn_wex d (syn_wa
              (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0))
                (.classEq (.cv d) (syn_cun (.cv a) (.cv b))))
              (syn_wa (.classEq (syn_cin (.cv d) (.cv c)) (syn_c0))
                (.classEq (.cv x) (syn_cun (.cv d) (.cv c))))))))
      (syn_wrex b B (syn_wex d (syn_wa (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0))
              (.classEq (.cv d) (syn_cun (.cv a) (.cv b)))) (syn_wrex c C
              (syn_wa (.classEq (syn_cin (.cv d) (.cv c)) (syn_c0))
                (.classEq (.cv x) (syn_cun (.cv d) (.cv c))))))))
      (syn_wex d (syn_wrex b B (syn_wa (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0))
              (.classEq (.cv d) (syn_cun (.cv a) (.cv b)))) (syn_wrex c C
              (syn_wa (.classEq (syn_cin (.cv d) (.cv c)) (syn_c0))
                (.classEq (.cv x) (syn_cun (.cv d) (.cv c))))))))
      p0060 p0061
  have p0063 :=
    @g_rexbii
      (syn_wrex b B (syn_wrex c C (syn_wex d (syn_wa
              (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0))
                (.classEq (.cv d) (syn_cun (.cv a) (.cv b))))
              (syn_wa (.classEq (syn_cin (.cv d) (.cv c)) (syn_c0))
                (.classEq (.cv x) (syn_cun (.cv d) (.cv c))))))))
      (syn_wex d (syn_wrex b B (syn_wa (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0))
              (.classEq (.cv d) (syn_cun (.cv a) (.cv b)))) (syn_wrex c C
              (syn_wa (.classEq (syn_cin (.cv d) (.cv c)) (syn_c0))
                (.classEq (.cv x) (syn_cun (.cv d) (.cv c))))))))
      a A p0062
  have freeVariableCertificate9 :
    a ∉
      ((syn_wrex c C (syn_wa (.classEq (syn_cin (.cv d) (.cv c)) (syn_c0))
            (.classEq (.cv x) (syn_cun (.cv d) (.cv c)))))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, Finset.mem_union,
      Finset.mem_erase, Finset.mem_singleton, Finset.notMem_empty, fresh_a_not_C,
      fresh_a_ne_d, fresh_a_ne_c, fresh_a_ne_x, or_false, and_false, not_false_eq_true]
  have p0064 :=
    @g_r19_41v
      (syn_wrex b B (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0))
          (.classEq (.cv d) (syn_cun (.cv a) (.cv b)))))
      (syn_wrex c C (syn_wa (.classEq (syn_cin (.cv d) (.cv c)) (syn_c0))
          (.classEq (.cv x) (syn_cun (.cv d) (.cv c)))))
      a A freeVariableCertificate9
  have freeVariableCertificate10 :
    b ∉
      ((syn_wrex c C (syn_wa (.classEq (syn_cin (.cv d) (.cv c)) (syn_c0))
            (.classEq (.cv x) (syn_cun (.cv d) (.cv c)))))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, Finset.mem_union,
      Finset.mem_erase, Finset.mem_singleton, Finset.notMem_empty, fresh_b_not_C,
      fresh_b_ne_d, fresh_b_ne_c, fresh_b_ne_x, or_false, and_false, not_false_eq_true]
  have p0065 :=
    @g_r19_41v
      (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0))
        (.classEq (.cv d) (syn_cun (.cv a) (.cv b))))
      (syn_wrex c C (syn_wa (.classEq (syn_cin (.cv d) (.cv c)) (syn_c0))
          (.classEq (.cv x) (syn_cun (.cv d) (.cv c)))))
      b B freeVariableCertificate10
  have p0066 :=
    @g_rexbii
      (syn_wrex b B (syn_wa (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0))
            (.classEq (.cv d) (syn_cun (.cv a) (.cv b)))) (syn_wrex c C
            (syn_wa (.classEq (syn_cin (.cv d) (.cv c)) (syn_c0))
              (.classEq (.cv x) (syn_cun (.cv d) (.cv c)))))))
      (syn_wa (syn_wrex b B (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0))
            (.classEq (.cv d) (syn_cun (.cv a) (.cv b))))) (syn_wrex c C
          (syn_wa (.classEq (syn_cin (.cv d) (.cv c)) (syn_c0))
            (.classEq (.cv x) (syn_cun (.cv d) (.cv c))))))
      a A p0065
  have freeVariableCertificate11 : a ∉ ((Class.cv d)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_a_ne_d, not_false_eq_true]
  have freeVariableCertificate12 : b ∉ ((Class.cv d)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_b_ne_d, not_false_eq_true]
  have p0067 :=
    @g_eladdc (.cv d) A B a b freeVariableCertificate11 freeVariableCertificate12
      (by exact (show a ∉ (A).fv from (by exact fresh_a_not_A)))
      (by exact (show b ∉ (A).fv from (by exact fresh_b_not_A)))
      (by exact (show a ∉ (B).fv from (by exact fresh_a_not_B)))
      (by exact (show b ∉ (B).fv from (by exact fresh_b_not_B)))
      (show a ≠ b from (by exact fresh_a_ne_b))
  have p0068 :=
    @g_anbi1i (.classMem (.cv d) (syn_cplc A B))
      (syn_wrex a A (syn_wrex b B (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0))
            (.classEq (.cv d) (syn_cun (.cv a) (.cv b))))))
      (syn_wrex c C (syn_wa (.classEq (syn_cin (.cv d) (.cv c)) (syn_c0))
          (.classEq (.cv x) (syn_cun (.cv d) (.cv c)))))
      p0067
  have p0069 :=
    @g_n_3bitr4ri
      (syn_wrex a A (syn_wa (syn_wrex b B (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0))
              (.classEq (.cv d) (syn_cun (.cv a) (.cv b))))) (syn_wrex c C
            (syn_wa (.classEq (syn_cin (.cv d) (.cv c)) (syn_c0))
              (.classEq (.cv x) (syn_cun (.cv d) (.cv c)))))))
      (syn_wa (syn_wrex a A (syn_wrex b B (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0))
              (.classEq (.cv d) (syn_cun (.cv a) (.cv b)))))) (syn_wrex c C
          (syn_wa (.classEq (syn_cin (.cv d) (.cv c)) (syn_c0))
            (.classEq (.cv x) (syn_cun (.cv d) (.cv c))))))
      (syn_wrex a A (syn_wrex b B (syn_wa (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0))
              (.classEq (.cv d) (syn_cun (.cv a) (.cv b)))) (syn_wrex c C
              (syn_wa (.classEq (syn_cin (.cv d) (.cv c)) (syn_c0))
                (.classEq (.cv x) (syn_cun (.cv d) (.cv c))))))))
      (syn_wa (.classMem (.cv d) (syn_cplc A B)) (syn_wrex c C
          (syn_wa (.classEq (syn_cin (.cv d) (.cv c)) (syn_c0))
            (.classEq (.cv x) (syn_cun (.cv d) (.cv c))))))
      p0064 p0066 p0068
  have p0070 :=
    @g_exbii
      (syn_wa (.classMem (.cv d) (syn_cplc A B)) (syn_wrex c C
          (syn_wa (.classEq (syn_cin (.cv d) (.cv c)) (syn_c0))
            (.classEq (.cv x) (syn_cun (.cv d) (.cv c))))))
      (syn_wrex a A (syn_wrex b B (syn_wa (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0))
              (.classEq (.cv d) (syn_cun (.cv a) (.cv b)))) (syn_wrex c C
              (syn_wa (.classEq (syn_cin (.cv d) (.cv c)) (syn_c0))
                (.classEq (.cv x) (syn_cun (.cv d) (.cv c))))))))
      d p0069
  have p0071 :=
    @g_n_3bitr4ri
      (syn_wrex a A (syn_wex d (syn_wrex b B (syn_wa
              (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0))
                (.classEq (.cv d) (syn_cun (.cv a) (.cv b)))) (syn_wrex c C
                (syn_wa (.classEq (syn_cin (.cv d) (.cv c)) (syn_c0))
                  (.classEq (.cv x) (syn_cun (.cv d) (.cv c)))))))))
      (syn_wex d (syn_wrex a A (syn_wrex b B (syn_wa
              (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0))
                (.classEq (.cv d) (syn_cun (.cv a) (.cv b)))) (syn_wrex c C
                (syn_wa (.classEq (syn_cin (.cv d) (.cv c)) (syn_c0))
                  (.classEq (.cv x) (syn_cun (.cv d) (.cv c)))))))))
      (syn_wrex a A (syn_wrex b B (syn_wrex c C (syn_wex d (syn_wa
                (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0))
                  (.classEq (.cv d) (syn_cun (.cv a) (.cv b))))
                (syn_wa (.classEq (syn_cin (.cv d) (.cv c)) (syn_c0))
                  (.classEq (.cv x) (syn_cun (.cv d) (.cv c)))))))))
      (syn_wex d (syn_wa (.classMem (.cv d) (syn_cplc A B)) (syn_wrex c C
            (syn_wa (.classEq (syn_cin (.cv d) (.cv c)) (syn_c0))
              (.classEq (.cv x) (syn_cun (.cv d) (.cv c)))))))
      p0055 p0063 p0070
  have p0072 :=
    @g_bitri
      (syn_wrex d (syn_cplc A B) (syn_wrex c C
          (syn_wa (.classEq (syn_cin (.cv d) (.cv c)) (syn_c0))
            (.classEq (.cv x) (syn_cun (.cv d) (.cv c))))))
      (syn_wex d (syn_wa (.classMem (.cv d) (syn_cplc A B)) (syn_wrex c C
            (syn_wa (.classEq (syn_cin (.cv d) (.cv c)) (syn_c0))
              (.classEq (.cv x) (syn_cun (.cv d) (.cv c)))))))
      (syn_wrex a A (syn_wrex b B (syn_wrex c C (syn_wex d (syn_wa
                (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0))
                  (.classEq (.cv d) (syn_cun (.cv a) (.cv b))))
                (syn_wa (.classEq (syn_cin (.cv d) (.cv c)) (syn_c0))
                  (.classEq (.cv x) (syn_cun (.cv d) (.cv c)))))))))
      p0054 p0071
  have p0073 :=
    @g_bitri (.classMem (.cv x) (syn_cplc (syn_cplc A B) C))
      (syn_wrex d (syn_cplc A B) (syn_wrex c C
          (syn_wa (.classEq (syn_cin (.cv d) (.cv c)) (syn_c0))
            (.classEq (.cv x) (syn_cun (.cv d) (.cv c))))))
      (syn_wrex a A (syn_wrex b B (syn_wrex c C (syn_wex d (syn_wa
                (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0))
                  (.classEq (.cv d) (syn_cun (.cv a) (.cv b))))
                (syn_wa (.classEq (syn_cin (.cv d) (.cv c)) (syn_c0))
                  (.classEq (.cv x) (syn_cun (.cv d) (.cv c)))))))))
      p0053 p0072
  have freeVariableCertificate13 : a ∉ ((Class.cv x)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_a_ne_x, not_false_eq_true]
  have freeVariableCertificate14 : e ∉ ((Class.cv x)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_e_ne_x, not_false_eq_true]
  have freeVariableCertificate15 : a ∉ ((syn_cplc B C)).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, Finset.mem_union,
      fresh_a_not_B, fresh_a_not_C, or_false, not_false_eq_true]
  have freeVariableCertificate16 : e ∉ ((syn_cplc B C)).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, Finset.mem_union,
      fresh_e_not_B, fresh_e_not_C, or_false, not_false_eq_true]
  have p0074 :=
    @g_eladdc (.cv x) A (syn_cplc B C) a e freeVariableCertificate13
      freeVariableCertificate14 (by exact (show a ∉ (A).fv from (by exact fresh_a_not_A)))
      (by exact (show e ∉ (A).fv from (by exact fresh_e_not_A))) freeVariableCertificate15
      freeVariableCertificate16 (show a ≠ e from (by exact fresh_a_ne_e))
  have p0075 :=
    (Nominal.biimpRefl (syn_wrex e (syn_cplc B C)
        (syn_wa (.classEq (syn_cin (.cv a) (.cv e)) (syn_c0))
          (.classEq (.cv x) (syn_cun (.cv a) (.cv e))))))
  have p0076 :=
    @g_rexcom4
      (syn_wrex c C (syn_wa (syn_wa (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0))
            (.classEq (.cv e) (syn_cun (.cv b) (.cv c))))
          (syn_wa (.classEq (syn_cin (.cv a) (.cv e)) (syn_c0))
            (.classEq (.cv x) (syn_cun (.cv a) (.cv e))))))
      b e B (by exact (show e ∉ (B).fv from (by exact fresh_e_not_B)))
      (show b ≠ e from (by exact fresh_b_ne_e))
  have p0077 :=
    @g_rexcom4
      (syn_wa (syn_wa (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0))
          (.classEq (.cv e) (syn_cun (.cv b) (.cv c))))
        (syn_wa (.classEq (syn_cin (.cv a) (.cv e)) (syn_c0))
          (.classEq (.cv x) (syn_cun (.cv a) (.cv e)))))
      c e C (by exact (show e ∉ (C).fv from (by exact fresh_e_not_C)))
      (show c ≠ e from (by exact fresh_c_ne_e))
  have p0078 :=
    @g_rexbii
      (syn_wrex c C (syn_wex e (syn_wa (syn_wa (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0))
              (.classEq (.cv e) (syn_cun (.cv b) (.cv c))))
            (syn_wa (.classEq (syn_cin (.cv a) (.cv e)) (syn_c0))
              (.classEq (.cv x) (syn_cun (.cv a) (.cv e)))))))
      (syn_wex e (syn_wrex c C (syn_wa (syn_wa (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0))
              (.classEq (.cv e) (syn_cun (.cv b) (.cv c))))
            (syn_wa (.classEq (syn_cin (.cv a) (.cv e)) (syn_c0))
              (.classEq (.cv x) (syn_cun (.cv a) (.cv e)))))))
      b B p0077
  have freeVariableCertificate17 :
    b ∉
      ((syn_wa (.classEq (syn_cin (.cv a) (.cv e)) (syn_c0))
          (.classEq (.cv x) (syn_cun (.cv a) (.cv e))))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_b_ne_a, fresh_b_ne_e, fresh_b_ne_x,
      or_false, not_false_eq_true]
  have p0079 :=
    @g_r19_41v
      (syn_wrex c C (syn_wa (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0))
          (.classEq (.cv e) (syn_cun (.cv b) (.cv c)))))
      (syn_wa (.classEq (syn_cin (.cv a) (.cv e)) (syn_c0))
        (.classEq (.cv x) (syn_cun (.cv a) (.cv e))))
      b B freeVariableCertificate17
  have freeVariableCertificate18 :
    c ∉
      ((syn_wa (.classEq (syn_cin (.cv a) (.cv e)) (syn_c0))
          (.classEq (.cv x) (syn_cun (.cv a) (.cv e))))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_c_ne_a, fresh_c_ne_e, fresh_c_ne_x,
      or_false, not_false_eq_true]
  have p0080 :=
    @g_r19_41v
      (syn_wa (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0))
        (.classEq (.cv e) (syn_cun (.cv b) (.cv c))))
      (syn_wa (.classEq (syn_cin (.cv a) (.cv e)) (syn_c0))
        (.classEq (.cv x) (syn_cun (.cv a) (.cv e))))
      c C freeVariableCertificate18
  have p0081 :=
    @g_rexbii
      (syn_wrex c C (syn_wa (syn_wa (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0))
            (.classEq (.cv e) (syn_cun (.cv b) (.cv c))))
          (syn_wa (.classEq (syn_cin (.cv a) (.cv e)) (syn_c0))
            (.classEq (.cv x) (syn_cun (.cv a) (.cv e))))))
      (syn_wa (syn_wrex c C (syn_wa (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0))
            (.classEq (.cv e) (syn_cun (.cv b) (.cv c)))))
        (syn_wa (.classEq (syn_cin (.cv a) (.cv e)) (syn_c0))
          (.classEq (.cv x) (syn_cun (.cv a) (.cv e)))))
      b B p0080
  have freeVariableCertificate19 : b ∉ ((Class.cv e)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_b_ne_e, not_false_eq_true]
  have freeVariableCertificate20 : c ∉ ((Class.cv e)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_c_ne_e, not_false_eq_true]
  have p0082 :=
    @g_eladdc (.cv e) B C b c freeVariableCertificate19 freeVariableCertificate20
      (by exact (show b ∉ (B).fv from (by exact fresh_b_not_B)))
      (by exact (show c ∉ (B).fv from (by exact fresh_c_not_B)))
      (by exact (show b ∉ (C).fv from (by exact fresh_b_not_C)))
      (by exact (show c ∉ (C).fv from (by exact fresh_c_not_C)))
      (show b ≠ c from (by exact fresh_b_ne_c))
  have p0083 :=
    @g_anbi1i (.classMem (.cv e) (syn_cplc B C))
      (syn_wrex b B (syn_wrex c C (syn_wa (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0))
            (.classEq (.cv e) (syn_cun (.cv b) (.cv c))))))
      (syn_wa (.classEq (syn_cin (.cv a) (.cv e)) (syn_c0))
        (.classEq (.cv x) (syn_cun (.cv a) (.cv e))))
      p0082
  have p0084 :=
    @g_n_3bitr4ri
      (syn_wrex b B (syn_wa (syn_wrex c C (syn_wa (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0))
              (.classEq (.cv e) (syn_cun (.cv b) (.cv c)))))
          (syn_wa (.classEq (syn_cin (.cv a) (.cv e)) (syn_c0))
            (.classEq (.cv x) (syn_cun (.cv a) (.cv e))))))
      (syn_wa (syn_wrex b B (syn_wrex c C (syn_wa (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0))
              (.classEq (.cv e) (syn_cun (.cv b) (.cv c))))))
        (syn_wa (.classEq (syn_cin (.cv a) (.cv e)) (syn_c0))
          (.classEq (.cv x) (syn_cun (.cv a) (.cv e)))))
      (syn_wrex b B (syn_wrex c C (syn_wa (syn_wa (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0))
              (.classEq (.cv e) (syn_cun (.cv b) (.cv c))))
            (syn_wa (.classEq (syn_cin (.cv a) (.cv e)) (syn_c0))
              (.classEq (.cv x) (syn_cun (.cv a) (.cv e)))))))
      (syn_wa (.classMem (.cv e) (syn_cplc B C))
        (syn_wa (.classEq (syn_cin (.cv a) (.cv e)) (syn_c0))
          (.classEq (.cv x) (syn_cun (.cv a) (.cv e)))))
      p0079 p0081 p0083
  have p0085 :=
    @g_exbii
      (syn_wa (.classMem (.cv e) (syn_cplc B C))
        (syn_wa (.classEq (syn_cin (.cv a) (.cv e)) (syn_c0))
          (.classEq (.cv x) (syn_cun (.cv a) (.cv e)))))
      (syn_wrex b B (syn_wrex c C (syn_wa (syn_wa (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0))
              (.classEq (.cv e) (syn_cun (.cv b) (.cv c))))
            (syn_wa (.classEq (syn_cin (.cv a) (.cv e)) (syn_c0))
              (.classEq (.cv x) (syn_cun (.cv a) (.cv e)))))))
      e p0084
  have p0086 :=
    @g_n_3bitr4ri
      (syn_wrex b B (syn_wex e (syn_wrex c C (syn_wa
              (syn_wa (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0))
                (.classEq (.cv e) (syn_cun (.cv b) (.cv c))))
              (syn_wa (.classEq (syn_cin (.cv a) (.cv e)) (syn_c0))
                (.classEq (.cv x) (syn_cun (.cv a) (.cv e))))))))
      (syn_wex e (syn_wrex b B (syn_wrex c C (syn_wa
              (syn_wa (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0))
                (.classEq (.cv e) (syn_cun (.cv b) (.cv c))))
              (syn_wa (.classEq (syn_cin (.cv a) (.cv e)) (syn_c0))
                (.classEq (.cv x) (syn_cun (.cv a) (.cv e))))))))
      (syn_wrex b B (syn_wrex c C (syn_wex e (syn_wa
              (syn_wa (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0))
                (.classEq (.cv e) (syn_cun (.cv b) (.cv c))))
              (syn_wa (.classEq (syn_cin (.cv a) (.cv e)) (syn_c0))
                (.classEq (.cv x) (syn_cun (.cv a) (.cv e))))))))
      (syn_wex e (syn_wa (.classMem (.cv e) (syn_cplc B C))
          (syn_wa (.classEq (syn_cin (.cv a) (.cv e)) (syn_c0))
            (.classEq (.cv x) (syn_cun (.cv a) (.cv e))))))
      p0076 p0078 p0085
  have p0087 :=
    @g_bitri
      (syn_wrex e (syn_cplc B C) (syn_wa (.classEq (syn_cin (.cv a) (.cv e)) (syn_c0))
          (.classEq (.cv x) (syn_cun (.cv a) (.cv e)))))
      (syn_wex e (syn_wa (.classMem (.cv e) (syn_cplc B C))
          (syn_wa (.classEq (syn_cin (.cv a) (.cv e)) (syn_c0))
            (.classEq (.cv x) (syn_cun (.cv a) (.cv e))))))
      (syn_wrex b B (syn_wrex c C (syn_wex e (syn_wa
              (syn_wa (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0))
                (.classEq (.cv e) (syn_cun (.cv b) (.cv c))))
              (syn_wa (.classEq (syn_cin (.cv a) (.cv e)) (syn_c0))
                (.classEq (.cv x) (syn_cun (.cv a) (.cv e))))))))
      p0075 p0086
  have p0088 :=
    @g_rexbii
      (syn_wrex e (syn_cplc B C) (syn_wa (.classEq (syn_cin (.cv a) (.cv e)) (syn_c0))
          (.classEq (.cv x) (syn_cun (.cv a) (.cv e)))))
      (syn_wrex b B (syn_wrex c C (syn_wex e (syn_wa
              (syn_wa (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0))
                (.classEq (.cv e) (syn_cun (.cv b) (.cv c))))
              (syn_wa (.classEq (syn_cin (.cv a) (.cv e)) (syn_c0))
                (.classEq (.cv x) (syn_cun (.cv a) (.cv e))))))))
      a A p0087
  have p0089 :=
    @g_bitri (.classMem (.cv x) (syn_cplc A (syn_cplc B C)))
      (syn_wrex a A (syn_wrex e (syn_cplc B C)
          (syn_wa (.classEq (syn_cin (.cv a) (.cv e)) (syn_c0))
            (.classEq (.cv x) (syn_cun (.cv a) (.cv e))))))
      (syn_wrex a A (syn_wrex b B (syn_wrex c C (syn_wex e (syn_wa
                (syn_wa (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0))
                  (.classEq (.cv e) (syn_cun (.cv b) (.cv c))))
                (syn_wa (.classEq (syn_cin (.cv a) (.cv e)) (syn_c0))
                  (.classEq (.cv x) (syn_cun (.cv a) (.cv e)))))))))
      p0074 p0088
  have p0090 :=
    @g_n_3bitr4i
      (syn_wrex a A (syn_wrex b B (syn_wrex c C (syn_wex d (syn_wa
                (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0))
                  (.classEq (.cv d) (syn_cun (.cv a) (.cv b))))
                (syn_wa (.classEq (syn_cin (.cv d) (.cv c)) (syn_c0))
                  (.classEq (.cv x) (syn_cun (.cv d) (.cv c)))))))))
      (syn_wrex a A (syn_wrex b B (syn_wrex c C (syn_wex e (syn_wa
                (syn_wa (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0))
                  (.classEq (.cv e) (syn_cun (.cv b) (.cv c))))
                (syn_wa (.classEq (syn_cin (.cv a) (.cv e)) (syn_c0))
                  (.classEq (.cv x) (syn_cun (.cv a) (.cv e)))))))))
      (.classMem (.cv x) (syn_cplc (syn_cplc A B) C))
      (.classMem (.cv x) (syn_cplc A (syn_cplc B C))) p0052 p0073 p0089
  have freeVariableCertificate21 : x ∉ ((syn_cplc (syn_cplc A B) C)).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, Finset.mem_union,
      fresh_x_not_A, fresh_x_not_B, fresh_x_not_C, or_false, not_false_eq_true]
  have freeVariableCertificate22 : x ∉ ((syn_cplc A (syn_cplc B C))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, Finset.mem_union,
      fresh_x_not_A, fresh_x_not_B, fresh_x_not_C, or_false, not_false_eq_true]
  have p0091 :=
    @g_eqriv x (syn_cplc (syn_cplc A B) C) (syn_cplc A (syn_cplc B C))
      freeVariableCertificate21 freeVariableCertificate22 p0090
  exact p0091


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk009StructuralPart030`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_addc32 (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.classEq (syn_cplc (syn_cplc A B) C) (syn_cplc (syn_cplc A C) B)) :=
  by
  have p0000 := @g_addccom B C
  have p0001 := @g_addceq2i (syn_cplc B C) (syn_cplc C B) A p0000
  have p0002 := @g_addcass A B C
  have p0003 := @g_addcass A C B
  have p0004 :=
    @g_n_3eqtr4i (syn_cplc A (syn_cplc B C)) (syn_cplc A (syn_cplc C B))
      (syn_cplc (syn_cplc A B) C) (syn_cplc (syn_cplc A C) B) p0001 p0002 p0003
  exact p0004

@[expose]
noncomputable def g_addc4 (A : Class) (B : Class) (C : Class) (D : Class) :
    Nominal.NPrf
      (.classEq (syn_cplc (syn_cplc A B) (syn_cplc C D))
        (syn_cplc (syn_cplc A C) (syn_cplc B D))) :=
  by
  have p0000 := @g_addc32 A B C
  have p0001 :=
    @g_addceq1i (syn_cplc (syn_cplc A B) C) (syn_cplc (syn_cplc A C) B) D p0000
  have p0002 := @g_addcass (syn_cplc A B) C D
  have p0003 := @g_addcass (syn_cplc A C) B D
  have p0004 :=
    @g_n_3eqtr3i (syn_cplc (syn_cplc (syn_cplc A B) C) D)
      (syn_cplc (syn_cplc (syn_cplc A C) B) D) (syn_cplc (syn_cplc A B) (syn_cplc C D))
      (syn_cplc (syn_cplc A C) (syn_cplc B D)) p0001 p0002 p0003
  exact p0004

@[expose]
noncomputable def g_addc6 (A : Class) (B : Class) (C : Class) (D : Class) (E : Class)
    (F : Class) :
    Nominal.NPrf
      (.classEq (syn_cplc (syn_cplc (syn_cplc A B) (syn_cplc C D)) (syn_cplc E F))
        (syn_cplc (syn_cplc (syn_cplc A C) E) (syn_cplc (syn_cplc B D) F))) :=
  by
  have p0000 := @g_addc4 A B C D
  have p0001 :=
    @g_addceq1i (syn_cplc (syn_cplc A B) (syn_cplc C D))
      (syn_cplc (syn_cplc A C) (syn_cplc B D)) E p0000
  have p0002 := @g_addc32 (syn_cplc A C) (syn_cplc B D) E
  have p0003 :=
    @g_eqtri (syn_cplc (syn_cplc (syn_cplc A B) (syn_cplc C D)) E)
      (syn_cplc (syn_cplc (syn_cplc A C) (syn_cplc B D)) E)
      (syn_cplc (syn_cplc (syn_cplc A C) E) (syn_cplc B D)) p0001 p0002
  have p0004 :=
    @g_addceq1i (syn_cplc (syn_cplc (syn_cplc A B) (syn_cplc C D)) E)
      (syn_cplc (syn_cplc (syn_cplc A C) E) (syn_cplc B D)) F p0003
  have p0005 := @g_addcass (syn_cplc (syn_cplc A B) (syn_cplc C D)) E F
  have p0006 := @g_addcass (syn_cplc (syn_cplc A C) E) (syn_cplc B D) F
  have p0007 :=
    @g_n_3eqtr3i (syn_cplc (syn_cplc (syn_cplc (syn_cplc A B) (syn_cplc C D)) E) F)
      (syn_cplc (syn_cplc (syn_cplc (syn_cplc A C) E) (syn_cplc B D)) F)
      (syn_cplc (syn_cplc (syn_cplc A B) (syn_cplc C D)) (syn_cplc E F))
      (syn_cplc (syn_cplc (syn_cplc A C) E) (syn_cplc (syn_cplc B D) F)) p0004 p0005 p0006
  exact p0007

@[expose]
noncomputable def g_nncaddccl (A : Class) (B : Class) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
        (.classMem (syn_cplc A B) (syn_cnnc))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  let a : Var := freshVar proofSupport 0
  let b : Var := freshVar proofSupport 1
  let c : Var := freshVar proofSupport 2
  let x : Var := freshVar proofSupport 3
  have fresh_a : a ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_a_not_A : a ∉ A.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (h))
  have fresh_a_not_B : a ∉ B.fv := by
    intro h
    exact fresh_a (Finset.mem_union_right _ (h))
  have fresh_b : b ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_b_not_B : b ∉ B.fv := by
    intro h
    exact fresh_b (Finset.mem_union_right _ (h))
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
  have fresh_a_ne_x : a ≠ x :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_x_ne_a : x ≠ a := Ne.symm fresh_a_ne_x
  have fresh_b_ne_c : b ≠ c :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_c_ne_b : c ≠ b := Ne.symm fresh_b_ne_c
  have fresh_b_ne_x : b ≠ x :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_x_ne_b : x ≠ b := Ne.symm fresh_b_ne_x
  have p0000 := @g_addceq1 (.cv a) A B
  have p0001 :=
    @g_eleq1d (.classEq (.cv a) A) (syn_cplc (.cv a) B) (syn_cplc A B) (syn_cnnc) p0000
  have p0002 :=
    @g_imbi2d (.classEq (.cv a) A) (.classMem (syn_cplc (.cv a) B) (syn_cnnc))
      (.classMem (syn_cplc A B) (syn_cnnc)) (.classMem B (syn_cnnc)) p0001
  have p0003 :=
    @g_unab (.neg (.classMem (.cv a) (syn_cnnc)))
      (.classMem (syn_cplc (.cv a) (.cv b)) (syn_cnnc)) b
  have p0004 := @g_vex b
  have p0005 := @g_vex x
  have p0006 :=
    @g_opkelimagekg (.cv b) (.cv x)
      (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
              (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
            (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
              (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
        (syn_cpw1 (syn_cpw1 (.cv a))))
      (syn_cvv) (syn_cvv)
  have p0007 :=
    @g_mp2an (.classMem (.cv b) (syn_cvv)) (.classMem (.cv x) (syn_cvv))
      (syn_wb (.classMem (syn_copk (.cv b) (.cv x)) (syn_cimagek (syn_cimak (syn_cdif
                (syn_cins3k (syn_ccompl (syn_cimak
                      (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                  (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                    (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                      (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
              (syn_cpw1 (syn_cpw1 (.cv a)))))) (.classEq (.cv x) (syn_cimak (syn_cimak (syn_cdif
                (syn_cins3k (syn_ccompl (syn_cimak
                      (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                  (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                    (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                      (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
              (syn_cpw1 (syn_cpw1 (.cv a)))) (.cv b))))
      p0004 p0005 p0006
  have p0008 :=
    @g_opkelcnvk (.cv x) (.cv b)
      (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
                (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
              (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                  (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
          (syn_cpw1 (syn_cpw1 (.cv a)))))
      p0005 p0004
  have p0009 := @g_addccom (.cv a) (.cv b)
  have p0010 := @g_dfaddc2 (.cv b) (.cv a)
  have p0011 :=
    @g_eqtri (syn_cplc (.cv a) (.cv b)) (syn_cplc (.cv b) (.cv a))
      (syn_cimak (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
                (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
              (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                  (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
          (syn_cpw1 (syn_cpw1 (.cv a)))) (.cv b))
      p0009 p0010
  have p0012 :=
    @g_eqeq2i (syn_cplc (.cv a) (.cv b))
      (syn_cimak (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
                (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
              (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                  (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
          (syn_cpw1 (syn_cpw1 (.cv a)))) (.cv b))
      (.cv x) p0011
  have p0013 :=
    @g_n_3bitr4i
      (.classMem (syn_copk (.cv b) (.cv x)) (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k
                (syn_ccompl
                  (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                    (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                  (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                    (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
            (syn_cpw1 (syn_cpw1 (.cv a))))))
      (.classEq (.cv x) (syn_cimak (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
                  (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                    (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                  (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                    (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
            (syn_cpw1 (syn_cpw1 (.cv a)))) (.cv b)))
      (.classMem (syn_copk (.cv x) (.cv b)) (syn_ccnvk (syn_cimagek (syn_cimak (syn_cdif
                (syn_cins3k (syn_ccompl (syn_cimak
                      (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                  (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                    (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                      (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
              (syn_cpw1 (syn_cpw1 (.cv a)))))))
      (.classEq (.cv x) (syn_cplc (.cv a) (.cv b))) p0007 p0008 p0012
  have p0014 :=
    @g_rexbii
      (.classMem (syn_copk (.cv x) (.cv b)) (syn_ccnvk (syn_cimagek (syn_cimak (syn_cdif
                (syn_cins3k (syn_ccompl (syn_cimak
                      (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                  (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                    (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                      (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
              (syn_cpw1 (syn_cpw1 (.cv a)))))))
      (.classEq (.cv x) (syn_cplc (.cv a) (.cv b))) x (syn_cnnc) p0013
  have freeVariableCertificate0 :
    x ∉
      ((syn_ccnvk (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                      (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                  (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                    (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                      (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
              (syn_cpw1 (syn_cpw1 (.cv a))))))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimagek,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      Finset.notMem_empty, fresh_x_ne_a, or_false, not_false_eq_true]
  have freeVariableCertificate1 : x ∉ ((Class.cv b)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_x_ne_b, not_false_eq_true]
  have p0015 :=
    @g_elimak x
      (syn_ccnvk (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
                  (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                    (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                  (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                    (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
            (syn_cpw1 (syn_cpw1 (.cv a))))))
      (syn_cnnc) (.cv b) freeVariableCertificate0
      (by
        exact
          (show x ∉ ((syn_cnnc)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc];
              exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
      freeVariableCertificate1 p0004
  have freeVariableCertificate2 : x ∉ ((syn_cplc (.cv a) (.cv b))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      fresh_x_ne_a, fresh_x_ne_b, or_false, not_false_eq_true]
  have p0016 :=
    @g_risset x (syn_cplc (.cv a) (.cv b)) (syn_cnnc) freeVariableCertificate2
      (by
        exact
          (show x ∉ ((syn_cnnc)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc];
              exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
  have p0017 :=
    @g_n_3bitr4i
      (syn_wrex x (syn_cnnc) (.classMem (syn_copk (.cv x) (.cv b)) (syn_ccnvk (syn_cimagek
              (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                        (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                    (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                      (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                        (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                    (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                (syn_cpw1 (syn_cpw1 (.cv a))))))))
      (syn_wrex x (syn_cnnc) (.classEq (.cv x) (syn_cplc (.cv a) (.cv b))))
      (.classMem (.cv b) (syn_cimak (syn_ccnvk (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k
                    (syn_ccompl (syn_cimak
                        (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                    (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                      (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                        (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                    (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                (syn_cpw1 (syn_cpw1 (.cv a)))))) (syn_cnnc)))
      (.classMem (syn_cplc (.cv a) (.cv b)) (syn_cnnc)) p0014 p0015 p0016
  have freeVariableCertificate3 :
    b ∉
      ((syn_cimak (syn_ccnvk (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
                      (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                    (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                      (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                        (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                    (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                (syn_cpw1 (syn_cpw1 (.cv a)))))) (syn_cnnc))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimagek,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_b_ne_a, or_false,
      not_false_eq_true]
  have p0018 :=
    @g_eqabi (.classMem (syn_cplc (.cv a) (.cv b)) (syn_cnnc)) b
      (syn_cimak (syn_ccnvk (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                      (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                  (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                    (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                      (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
              (syn_cpw1 (syn_cpw1 (.cv a)))))) (syn_cnnc))
      freeVariableCertificate3 p0017
  have p0019 :=
    @g_uneq2i
      (syn_cimak (syn_ccnvk (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                      (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                  (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                    (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                      (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
              (syn_cpw1 (syn_cpw1 (.cv a)))))) (syn_cnnc))
      (.cab b (.classMem (syn_cplc (.cv a) (.cv b)) (syn_cnnc)))
      (.cab b (.neg (.classMem (.cv a) (syn_cnnc)))) p0018
  have p0020 :=
    @g_imor (.classMem (.cv a) (syn_cnnc))
      (.classMem (syn_cplc (.cv a) (.cv b)) (syn_cnnc))
  have p0021 :=
    @g_abbii
      (.imp (.classMem (.cv a) (syn_cnnc)) (.classMem (syn_cplc (.cv a) (.cv b)) (syn_cnnc)))
      (syn_wo (.neg (.classMem (.cv a) (syn_cnnc)))
        (.classMem (syn_cplc (.cv a) (.cv b)) (syn_cnnc)))
      b p0020
  have p0022 :=
    @g_n_3eqtr4i
      (syn_cun (.cab b (.neg (.classMem (.cv a) (syn_cnnc))))
        (.cab b (.classMem (syn_cplc (.cv a) (.cv b)) (syn_cnnc))))
      (.cab b (syn_wo (.neg (.classMem (.cv a) (syn_cnnc)))
          (.classMem (syn_cplc (.cv a) (.cv b)) (syn_cnnc))))
      (syn_cun (.cab b (.neg (.classMem (.cv a) (syn_cnnc)))) (syn_cimak (syn_ccnvk (syn_cimagek
              (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                        (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                    (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                      (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                        (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                    (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                (syn_cpw1 (syn_cpw1 (.cv a)))))) (syn_cnnc)))
      (.cab b (.imp (.classMem (.cv a) (syn_cnnc))
          (.classMem (syn_cplc (.cv a) (.cv b)) (syn_cnnc))))
      p0003 p0019 p0021
  have freeVariableCertificate4 : b ∉ ((Wff.neg (.classMem (.cv a) (syn_cnnc)))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_neg,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_b_ne_a, or_false,
      not_false_eq_true]
  have p0023 := @g_abexv (.neg (.classMem (.cv a) (syn_cnnc))) b freeVariableCertificate4
  have p0024 := @g_addcexlem
  have p0025 := @g_vex a
  have p0026 := @g_pw1ex (.cv a) p0025
  have p0027 := @g_pw1ex (syn_cpw1 (.cv a)) p0026
  have p0028 :=
    @g_imakex
      (syn_cdif (syn_cins3k (syn_ccompl
            (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
              (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
          (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
            (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
              (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
      (syn_cpw1 (syn_cpw1 (.cv a))) p0024 p0027
  have p0029 :=
    @g_imagekex
      (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
              (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
            (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
              (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
        (syn_cpw1 (syn_cpw1 (.cv a))))
      p0028
  have p0030 :=
    @g_cnvkex
      (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
                (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
              (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                  (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
          (syn_cpw1 (syn_cpw1 (.cv a)))))
      p0029
  have p0031 := @g_nncex
  have p0032 :=
    @g_imakex
      (syn_ccnvk (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
                  (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                    (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                  (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                    (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
            (syn_cpw1 (syn_cpw1 (.cv a))))))
      (syn_cnnc) p0030 p0031
  have p0033 :=
    @g_unex (.cab b (.neg (.classMem (.cv a) (syn_cnnc))))
      (syn_cimak (syn_ccnvk (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                      (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                  (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                    (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                      (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
              (syn_cpw1 (syn_cpw1 (.cv a)))))) (syn_cnnc))
      p0023 p0032
  have p0034 :=
    @g_eqeltrri
      (syn_cun (.cab b (.neg (.classMem (.cv a) (syn_cnnc)))) (syn_cimak (syn_ccnvk (syn_cimagek
              (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                        (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                    (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                      (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                        (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                    (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                (syn_cpw1 (syn_cpw1 (.cv a)))))) (syn_cnnc)))
      (.cab b (.imp (.classMem (.cv a) (syn_cnnc))
          (.classMem (syn_cplc (.cv a) (.cv b)) (syn_cnnc))))
      (syn_cvv) p0022 p0033
  have p0035 := @g_addceq2 (.cv b) (syn_c0c) (.cv a)
  have p0036 :=
    @g_eleq1d (.classEq (.cv b) (syn_c0c)) (syn_cplc (.cv a) (.cv b))
      (syn_cplc (.cv a) (syn_c0c)) (syn_cnnc) p0035
  have p0037 :=
    @g_imbi2d (.classEq (.cv b) (syn_c0c))
      (.classMem (syn_cplc (.cv a) (.cv b)) (syn_cnnc))
      (.classMem (syn_cplc (.cv a) (syn_c0c)) (syn_cnnc)) (.classMem (.cv a) (syn_cnnc))
      p0036
  have p0038 := @g_addceq2 (.cv b) (.cv c) (.cv a)
  have p0039_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq b c) (.classEq (syn_cplc (.cv a) (.cv b)) (syn_cplc (.cv a) (.cv c)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_cplc syn_wrex syn_wex syn_wa
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0038
  have p0039 :=
    @g_eleq1d (.objEq b c) (syn_cplc (.cv a) (.cv b)) (syn_cplc (.cv a) (.cv c))
      (syn_cnnc) p0039_e00_recanon
  have p0040 :=
    @g_imbi2d (.objEq b c) (.classMem (syn_cplc (.cv a) (.cv b)) (syn_cnnc))
      (.classMem (syn_cplc (.cv a) (.cv c)) (syn_cnnc)) (.classMem (.cv a) (syn_cnnc))
      p0039
  have p0041 := @g_addceq2 (.cv b) (syn_cplc (.cv c) (syn_c1c)) (.cv a)
  have p0042 :=
    @g_eleq1d (.classEq (.cv b) (syn_cplc (.cv c) (syn_c1c))) (syn_cplc (.cv a) (.cv b))
      (syn_cplc (.cv a) (syn_cplc (.cv c) (syn_c1c))) (syn_cnnc) p0041
  have p0043 :=
    @g_imbi2d (.classEq (.cv b) (syn_cplc (.cv c) (syn_c1c)))
      (.classMem (syn_cplc (.cv a) (.cv b)) (syn_cnnc))
      (.classMem (syn_cplc (.cv a) (syn_cplc (.cv c) (syn_c1c))) (syn_cnnc))
      (.classMem (.cv a) (syn_cnnc)) p0042
  have p0044 := @g_addceq2 (.cv b) B (.cv a)
  have p0045 :=
    @g_eleq1d (.classEq (.cv b) B) (syn_cplc (.cv a) (.cv b)) (syn_cplc (.cv a) B)
      (syn_cnnc) p0044
  have p0046 :=
    @g_imbi2d (.classEq (.cv b) B) (.classMem (syn_cplc (.cv a) (.cv b)) (syn_cnnc))
      (.classMem (syn_cplc (.cv a) B) (syn_cnnc)) (.classMem (.cv a) (syn_cnnc)) p0045
  have p0047 := @g_addcid1 (.cv a)
  have p0048 := @g_id (.classMem (.cv a) (syn_cnnc))
  have p0049 :=
    @g_syl5eqel (.classMem (.cv a) (syn_cnnc)) (syn_cplc (.cv a) (syn_c0c)) (.cv a)
      (syn_cnnc) p0047 p0048
  have p0050 := @g_addcass (.cv a) (.cv c) (syn_c1c)
  have p0051 := @g_peano2 (syn_cplc (.cv a) (.cv c))
  have p0052 :=
    @g_syl5eqelr (.classMem (syn_cplc (.cv a) (.cv c)) (syn_cnnc))
      (syn_cplc (.cv a) (syn_cplc (.cv c) (syn_c1c)))
      (syn_cplc (syn_cplc (.cv a) (.cv c)) (syn_c1c)) (syn_cnnc) p0050 p0051
  have p0053 :=
    @g_imim2i (.classMem (syn_cplc (.cv a) (.cv c)) (syn_cnnc))
      (.classMem (syn_cplc (.cv a) (syn_cplc (.cv c) (syn_c1c))) (syn_cnnc))
      (.classMem (.cv a) (syn_cnnc)) p0052
  have p0054 :=
    @g_a1i
      (.imp (.imp (.classMem (.cv a) (syn_cnnc))
          (.classMem (syn_cplc (.cv a) (.cv c)) (syn_cnnc)))
        (.imp (.classMem (.cv a) (syn_cnnc))
          (.classMem (syn_cplc (.cv a) (syn_cplc (.cv c) (syn_c1c))) (syn_cnnc))))
      (.classMem (.cv c) (syn_cnnc)) p0053
  have freeVariableCertificate5 :
    b ∉
      ((Wff.imp (.classMem (.cv a) (syn_cnnc))
          (.classMem (syn_cplc (.cv a) (.cv c)) (syn_cnnc)))).fv :=
    by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_b_ne_a, fresh_b_ne_c, or_false,
      not_false_eq_true]
  have freeVariableCertificate6 :
    c ∉
      ((Wff.imp (.classMem (.cv a) (syn_cnnc))
          (.classMem (syn_cplc (.cv a) (.cv b)) (syn_cnnc)))).fv :=
    by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_c_ne_a, fresh_c_ne_b, or_false,
      not_false_eq_true]
  have freeVariableCertificate7 :
    b ∉
      ((Wff.imp (.classMem (.cv a) (syn_cnnc))
          (.classMem (syn_cplc (.cv a) (syn_c0c)) (syn_cnnc)))).fv :=
    by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_b_ne_a, or_false,
      not_false_eq_true]
  have freeVariableCertificate8 :
    b ∉
      ((Wff.imp (.classMem (.cv a) (syn_cnnc))
          (.classMem (syn_cplc (.cv a) B) (syn_cnnc)))).fv :=
    by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_b_ne_a, fresh_b_not_B, or_false,
      not_false_eq_true]
  have freeVariableCertificate9 :
    b ∉
      ((Wff.imp (.classMem (.cv a) (syn_cnnc))
          (.classMem (syn_cplc (.cv a) (syn_cplc (.cv c) (syn_c1c))) (syn_cnnc)))).fv :=
    by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_b_ne_a, fresh_b_ne_c, or_false,
      not_false_eq_true]
  have p0055 :=
    @g_finds
      (.imp (.classMem (.cv a) (syn_cnnc)) (.classMem (syn_cplc (.cv a) (.cv b)) (syn_cnnc)))
      (.imp (.classMem (.cv a) (syn_cnnc)) (.classMem (syn_cplc (.cv a) (syn_c0c)) (syn_cnnc)))
      (.imp (.classMem (.cv a) (syn_cnnc)) (.classMem (syn_cplc (.cv a) (.cv c)) (syn_cnnc)))
      (.imp (.classMem (.cv a) (syn_cnnc))
        (.classMem (syn_cplc (.cv a) (syn_cplc (.cv c) (syn_c1c))) (syn_cnnc)))
      (.imp (.classMem (.cv a) (syn_cnnc)) (.classMem (syn_cplc (.cv a) B) (syn_cnnc))) b
      c B (by exact (show b ∉ (B).fv from (by exact fresh_b_not_B)))
      freeVariableCertificate5 freeVariableCertificate6 freeVariableCertificate7
      freeVariableCertificate8 freeVariableCertificate9
      (show b ≠ c from (by exact fresh_b_ne_c)) p0034 p0037 p0040 p0043 p0046 p0049 p0054
  have p0056 :=
    @g_com12 (.classMem B (syn_cnnc)) (.classMem (.cv a) (syn_cnnc))
      (.classMem (syn_cplc (.cv a) B) (syn_cnnc)) p0055
  have freeVariableCertificate10 :
    a ∉ ((Wff.imp (.classMem B (syn_cnnc)) (.classMem (syn_cplc A B) (syn_cnnc)))).fv :=
    by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, Finset.mem_union,
      Finset.notMem_empty, fresh_a_not_B, fresh_a_not_A, or_false, not_false_eq_true]
  have p0057 :=
    @g_vtoclga (.imp (.classMem B (syn_cnnc)) (.classMem (syn_cplc (.cv a) B) (syn_cnnc)))
      (.imp (.classMem B (syn_cnnc)) (.classMem (syn_cplc A B) (syn_cnnc))) a A (syn_cnnc)
      (by exact (show a ∉ (A).fv from (by exact fresh_a_not_A)))
      (by
        exact
          (show a ∉ ((syn_cnnc)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc];
              exact (show a ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
      freeVariableCertificate10 p0002 p0056
  have p0058 :=
    @g_imp (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))
      (.classMem (syn_cplc A B) (syn_cnnc)) p0057
  exact p0058

@[expose]
noncomputable def g_elfin (x : Var) (A : Class) (dv_A_x : x ∉ A.fv) :
    Nominal.NPrf
      (syn_wb (.classMem A (syn_cfin)) (syn_wrex x (syn_cnnc) (.classMem A (.cv x)))) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_cfin))
  have p0001 := @g_eleq2i (syn_cfin) (syn_cuni (syn_cnnc)) A p0000
  have p0002 :=
    @g_eluni2 x A (syn_cnnc) (by exact (show x ∉ (A).fv from (by exact dv_A_x)))
      (by
        exact
          (show x ∉ ((syn_cnnc)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc];
              exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
  have p0003 :=
    @g_bitri (.classMem A (syn_cfin)) (.classMem A (syn_cuni (syn_cnnc)))
      (syn_wrex x (syn_cnnc) (.classMem A (.cv x))) p0001 p0002
  exact p0003

@[expose]
noncomputable def g_el0c (A : Class) :
    Nominal.NPrf (syn_wb (.classMem A (syn_c0c)) (.classEq A (syn_c0))) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_c0c))
  have p0001 := @g_eleq2i (syn_c0c) (syn_csn (syn_c0)) A p0000
  have p0002 := @g_n_0ex
  have p0003 := @g_elsnc2 A (syn_c0) p0002
  have p0004 :=
    @g_bitri (.classMem A (syn_c0c)) (.classMem A (syn_csn (syn_c0)))
      (.classEq A (syn_c0)) p0001 p0003
  exact p0004

@[expose]
noncomputable def g_nulel0c : Nominal.NPrf (.classMem (syn_c0) (syn_c0c)) :=
  by
  have p0000 := @g_eqid (syn_c0)
  have p0001 := @g_el0c (syn_c0)
  have p0002 :=
    @g_mpbir (.classMem (syn_c0) (syn_c0c)) (.classEq (syn_c0) (syn_c0)) p0000 p0001
  exact p0002


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk009StructuralPart031`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_n_0fin : Nominal.NPrf (.classMem (syn_c0) (syn_cfin)) :=
  by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let n : Var := freshVar proofSupport 0
  have p0000 := @g_peano1
  have p0001 := @g_eqid (syn_c0)
  have p0002 := @g_el0c (syn_c0)
  have p0003 :=
    @g_mpbir (.classMem (syn_c0) (syn_c0c)) (.classEq (syn_c0) (syn_c0)) p0001 p0002
  have p0004 := @g_eleq2 (.cv n) (syn_c0c) (syn_c0)
  have freeVariableCertificate0 : n ∉ ((Wff.classMem (syn_c0) (syn_c0c))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union,
      Finset.notMem_empty, or_false, not_false_eq_true]
  have p0005 :=
    @g_rspcev (.classMem (syn_c0) (.cv n)) (.classMem (syn_c0) (syn_c0c)) n (syn_c0c)
      (syn_cnnc)
      (by
        exact
          (show n ∉ ((syn_c0c)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c];
              exact (show n ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
      (by
        exact
          (show n ∉ ((syn_cnnc)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc];
              exact (show n ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
      freeVariableCertificate0 p0004
  have p0006 :=
    @g_mp2an (.classMem (syn_c0c) (syn_cnnc)) (.classMem (syn_c0) (syn_c0c))
      (syn_wrex n (syn_cnnc) (.classMem (syn_c0) (.cv n))) p0000 p0003 p0005
  have p0007 :=
    @g_elfin n (syn_c0)
      (by
        exact
          (show n ∉ ((syn_c0)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0];
              exact (show n ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
  have p0008 :=
    @g_mpbir (.classMem (syn_c0) (syn_cfin))
      (syn_wrex n (syn_cnnc) (.classMem (syn_c0) (.cv n))) p0006 p0007
  exact p0008


end NFChoice.DirectNominalPrf.WPPReplay

end
