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

/-- Checked nominal proof certificate identified upstream as `g_nncex`. -/
@[expose]
noncomputable def gNncex : Nominal.NPrf (.classMem (synCnnc) (synCvv)) :=
  by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let x : Var := freshVar proofSupport 0
  have p0000 := @gDfnnc2 x
  have p0001 :=
    @gSetswithex x (synC0c)
      (by
        exact
          (show x ∉ ((synC0c)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c];
              exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
  have p0002 := @gSsetkex
  have p0004 := @gAddcexlem
  have p0005 := @gN1cex
  have p0006 := @gPw1ex (synC1c) p0005
  have p0007 := @gPw1ex (synCpw1 (synC1c)) p0006
  have p0008 :=
    @gImakex
      (synCdif (synCins3k (synCcompl
            (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
              (synCpw1 (synCpw1 (synC1c)))))) (synCimak
          (synCsymdif (synCins2k (synCins2k (synCssetk)))
            (synCun (synCins2k (synCins3k (synCssetk)))
              (synCins3k (synCsik (synCsik (synCssetk))))))
          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
      (synCpw1 (synCpw1 (synC1c))) p0004 p0007
  have p0009 :=
    @gImagekex
      (synCimak (synCdif (synCins3k (synCcompl
              (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                (synCpw1 (synCpw1 (synC1c)))))) (synCimak
            (synCsymdif (synCins2k (synCins2k (synCssetk)))
              (synCun (synCins2k (synCins3k (synCssetk)))
                (synCins3k (synCsik (synCsik (synCssetk))))))
            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
        (synCpw1 (synCpw1 (synC1c))))
      p0008
  have p0010 :=
    @gSikex
      (synCimagek (synCimak (synCdif (synCins3k (synCcompl
                (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                  (synCpw1 (synCpw1 (synC1c)))))) (synCimak
              (synCsymdif (synCins2k (synCins2k (synCssetk)))
                (synCun (synCins2k (synCins3k (synCssetk)))
                  (synCins3k (synCsik (synCsik (synCssetk))))))
              (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
          (synCpw1 (synCpw1 (synC1c)))))
      p0009
  have p0011 :=
    @gCokex (synCssetk)
      (synCsik (synCimagek (synCimak (synCdif (synCins3k (synCcompl
                  (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                    (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                (synCsymdif (synCins2k (synCins2k (synCssetk)))
                  (synCun (synCins2k (synCins3k (synCssetk)))
                    (synCins3k (synCsik (synCsik (synCssetk))))))
                (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
            (synCpw1 (synCpw1 (synC1c))))))
      p0002 p0010
  have p0012 :=
    @gDifex (synCssetk)
      (synCcomk (synCssetk) (synCsik (synCimagek (synCimak (synCdif (synCins3k
                  (synCcompl (synCimak
                      (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                      (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                  (synCsymdif (synCins2k (synCins2k (synCssetk)))
                    (synCun (synCins2k (synCins3k (synCssetk)))
                      (synCins3k (synCsik (synCsik (synCssetk))))))
                  (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
              (synCpw1 (synCpw1 (synC1c)))))))
      p0002 p0011
  have p0014 :=
    @gImakex
      (synCdif (synCssetk) (synCcomk (synCssetk) (synCsik (synCimagek (synCimak (synCdif
                  (synCins3k (synCcompl (synCimak
                        (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                        (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                    (synCsymdif (synCins2k (synCins2k (synCssetk)))
                      (synCun (synCins2k (synCins3k (synCssetk)))
                        (synCins3k (synCsik (synCsik (synCssetk))))))
                    (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                (synCpw1 (synCpw1 (synC1c))))))))
      (synC1c) p0012 p0005
  have p0015 :=
    @gDifex (.cab x (.classMem (synC0c) (.cv x)))
      (synCimak (synCdif (synCssetk) (synCcomk (synCssetk) (synCsik (synCimagek
                (synCimak (synCdif (synCins3k (synCcompl (synCimak
                          (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                          (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                      (synCsymdif (synCins2k (synCins2k (synCssetk)))
                        (synCun (synCins2k (synCins3k (synCssetk)))
                          (synCins3k (synCsik (synCsik (synCssetk))))))
                      (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                  (synCpw1 (synCpw1 (synC1c)))))))) (synC1c))
      p0001 p0014
  have p0016 :=
    @gIntex
      (synCdif (.cab x (.classMem (synC0c) (.cv x))) (synCimak (synCdif (synCssetk)
            (synCcomk (synCssetk) (synCsik (synCimagek (synCimak (synCdif (synCins3k
                        (synCcompl (synCimak
                            (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                            (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                        (synCsymdif (synCins2k (synCins2k (synCssetk)))
                          (synCun (synCins2k (synCins3k (synCssetk)))
                            (synCins3k (synCsik (synCsik (synCssetk))))))
                        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                    (synCpw1 (synCpw1 (synC1c)))))))) (synC1c)))
      p0015
  have p0017 :=
    @gEqeltri (synCnnc)
      (synCint (synCdif (.cab x (.classMem (synC0c) (.cv x))) (synCimak
            (synCdif (synCssetk) (synCcomk (synCssetk) (synCsik (synCimagek (synCimak
                      (synCdif (synCins3k (synCcompl (synCimak
                              (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                              (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                          (synCsymdif (synCins2k (synCins2k (synCssetk)))
                            (synCun (synCins2k (synCins3k (synCssetk)))
                              (synCins3k (synCsik (synCsik (synCssetk))))))
                          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                      (synCpw1 (synCpw1 (synC1c)))))))) (synC1c))))
      (synCvv) p0000 p0016
  exact p0017

/-- Checked nominal proof certificate identified upstream as `g_finex`. -/
@[expose]
noncomputable def gFinex : Nominal.NPrf (.classMem (synCfin) (synCvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (synCfin))
  have p0001 := @gNncex
  have p0002 := @gUniex (synCnnc) p0001
  have p0003 := @gEqeltri (synCfin) (synCuni (synCnnc)) (synCvv) p0000 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_eladdc`. -/
@[expose]
noncomputable def gEladdc (A : Class) (M : Class) (N : Class) (b : Var) (c : Var)
    (dv_A_b : b ∉ A.fv) (dv_A_c : c ∉ A.fv) (dv_M_b : b ∉ M.fv) (dv_M_c : c ∉ M.fv)
    (dv_N_b : b ∉ N.fv) (dv_N_c : c ∉ N.fv) (dv_b_c : b ≠ c) :
    Nominal.NPrf
      (synWb (.classMem A (synCplc M N)) (synWrex b M (synWrex c N
            (synWa (.classEq (synCin (.cv b) (.cv c)) (synC0))
              (.classEq A (synCun (.cv b) (.cv c))))))) :=
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
  have p0000 := @gElex A (synCplc M N)
  have p0001 := @gId (.classEq A (synCun (.cv b) (.cv c)))
  have p0002 := @gVex b
  have p0003 := @gVex c
  have p0004 := @gUnex (.cv b) (.cv c) p0002 p0003
  have p0005 :=
    @gSyl6eqel (.classEq A (synCun (.cv b) (.cv c))) A (synCun (.cv b) (.cv c))
      (synCvv) p0001 p0004
  have p0006 :=
    @gAdantl (.classEq A (synCun (.cv b) (.cv c))) (.classMem A (synCvv))
      (.classEq (synCin (.cv b) (.cv c)) (synC0)) p0005
  have freeVariableCertificate0 : c ∉ ((Wff.classMem A (synCvv))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
      Finset.notMem_empty, dv_A_c, or_false, not_false_eq_true]
  have p0007 :=
    @gRexlimivw
      (synWa (.classEq (synCin (.cv b) (.cv c)) (synC0))
        (.classEq A (synCun (.cv b) (.cv c))))
      (.classMem A (synCvv)) c N freeVariableCertificate0 p0006
  have freeVariableCertificate1 : b ∉ ((Wff.classMem A (synCvv))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
      Finset.notMem_empty, dv_A_b, or_false, not_false_eq_true]
  have p0008 :=
    @gRexlimivw
      (synWrex c N (synWa (.classEq (synCin (.cv b) (.cv c)) (synC0))
          (.classEq A (synCun (.cv b) (.cv c)))))
      (.classMem A (synCvv)) b M freeVariableCertificate1 p0007
  have p0009 := @gEqeq1 (.cv a) A (synCun (.cv b) (.cv c))
  have p0010 :=
    @gAnbi2d (.classEq (.cv a) A) (.classEq (.cv a) (synCun (.cv b) (.cv c)))
      (.classEq A (synCun (.cv b) (.cv c))) (.classEq (synCin (.cv b) (.cv c)) (synC0))
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
    @gN2rexbidv (.classEq (.cv a) A)
      (synWa (.classEq (synCin (.cv b) (.cv c)) (synC0))
        (.classEq (.cv a) (synCun (.cv b) (.cv c))))
      (synWa (.classEq (synCin (.cv b) (.cv c)) (synC0))
        (.classEq A (synCun (.cv b) (.cv c))))
      b c M N freeVariableCertificate2 freeVariableCertificate3 p0010
  have p0012 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfAddc a b c M N
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
      ((synWrex b M (synWrex c N (synWa (.classEq (synCin (.cv b) (.cv c)) (synC0))
              (.classEq A (synCun (.cv b) (.cv c))))))).fv :=
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
    @gElab2g
      (synWrex b M (synWrex c N (synWa (.classEq (synCin (.cv b) (.cv c)) (synC0))
            (.classEq (.cv a) (synCun (.cv b) (.cv c))))))
      (synWrex b M (synWrex c N (synWa (.classEq (synCin (.cv b) (.cv c)) (synC0))
            (.classEq A (synCun (.cv b) (.cv c))))))
      a A (synCplc M N) (synCvv)
      (by exact (show a ∉ (A).fv from (by exact fresh_a_not_A))) freeVariableCertificate4
      p0011 p0012
  have p0014 :=
    @gPm521nii (.classMem A (synCplc M N)) (.classMem A (synCvv))
      (synWrex b M (synWrex c N (synWa (.classEq (synCin (.cv b) (.cv c)) (synC0))
            (.classEq A (synCun (.cv b) (.cv c))))))
      p0000 p0008 p0013
  exact p0014

/-- Checked nominal proof certificate identified upstream as `g_eladdci`. -/
@[expose]
noncomputable def gEladdci (A : Class) (B : Class) (M : Class) (N : Class) :
    Nominal.NPrf
      (.imp (synW3a (.classMem A M) (.classMem B N) (.classEq (synCin A B) (synC0)))
        (.classMem (synCun A B) (synCplc M N))) :=
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
  have p0000 := @gEqid (synCun A B)
  have p0001 := @gIneq1 (.cv a) A (.cv b)
  have p0002 :=
    @gEqeq1d (.classEq (.cv a) A) (synCin (.cv a) (.cv b)) (synCin A (.cv b)) (synC0)
      p0001
  have p0003 := @gUneq1 (.cv a) A (.cv b)
  have p0004 :=
    @gEqeq2d (.classEq (.cv a) A) (synCun (.cv a) (.cv b)) (synCun A (.cv b))
      (synCun A B) p0003
  have p0005 :=
    @gAnbi12d (.classEq (.cv a) A) (.classEq (synCin (.cv a) (.cv b)) (synC0))
      (.classEq (synCin A (.cv b)) (synC0))
      (.classEq (synCun A B) (synCun (.cv a) (.cv b)))
      (.classEq (synCun A B) (synCun A (.cv b))) p0002 p0004
  have p0006 := @gIneq2 (.cv b) B A
  have p0007 :=
    @gEqeq1d (.classEq (.cv b) B) (synCin A (.cv b)) (synCin A B) (synC0) p0006
  have p0008 := @gUneq2 (.cv b) B A
  have p0009 :=
    @gEqeq2d (.classEq (.cv b) B) (synCun A (.cv b)) (synCun A B) (synCun A B) p0008
  have p0010 :=
    @gAnbi12d (.classEq (.cv b) B) (.classEq (synCin A (.cv b)) (synC0))
      (.classEq (synCin A B) (synC0)) (.classEq (synCun A B) (synCun A (.cv b)))
      (.classEq (synCun A B) (synCun A B)) p0007 p0009
  have freeVariableCertificate0 :
    a ∉
      ((synWa (.classEq (synCin A (.cv b)) (synC0))
          (.classEq (synCun A B) (synCun A (.cv b))))).fv :=
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
      ((synWa (.classEq (synCin A B) (synC0)) (.classEq (synCun A B) (synCun A B)))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, Finset.mem_union,
      Finset.notMem_empty, fresh_b_not_A, fresh_b_not_B, or_false, not_false_eq_true]
  have p0011 :=
    @gRspc2ev
      (synWa (.classEq (synCin (.cv a) (.cv b)) (synC0))
        (.classEq (synCun A B) (synCun (.cv a) (.cv b))))
      (synWa (.classEq (synCin A B) (synC0)) (.classEq (synCun A B) (synCun A B)))
      (synWa (.classEq (synCin A (.cv b)) (synC0))
        (.classEq (synCun A B) (synCun A (.cv b))))
      a b A B M N (by exact (show a ∉ (A).fv from (by exact fresh_a_not_A)))
      (by exact (show b ∉ (A).fv from (by exact fresh_b_not_A)))
      (by exact (show b ∉ (B).fv from (by exact fresh_b_not_B)))
      (by exact (show a ∉ (M).fv from (by exact fresh_a_not_M)))
      (by exact (show a ∉ (N).fv from (by exact fresh_a_not_N)))
      (by exact (show b ∉ (N).fv from (by exact fresh_b_not_N))) freeVariableCertificate0
      freeVariableCertificate1 (show a ≠ b from (by exact fresh_a_ne_b)) p0005 p0010
  have p0012 :=
    @gN3expa (.classMem A M) (.classMem B N)
      (synWa (.classEq (synCin A B) (synC0)) (.classEq (synCun A B) (synCun A B)))
      (synWrex a M (synWrex b N (synWa (.classEq (synCin (.cv a) (.cv b)) (synC0))
            (.classEq (synCun A B) (synCun (.cv a) (.cv b))))))
      p0011
  have p0013 :=
    @gMpanr2 (synWa (.classMem A M) (.classMem B N)) (.classEq (synCin A B) (synC0))
      (.classEq (synCun A B) (synCun A B))
      (synWrex a M (synWrex b N (synWa (.classEq (synCin (.cv a) (.cv b)) (synC0))
            (.classEq (synCun A B) (synCun (.cv a) (.cv b))))))
      p0000 p0012
  have p0014 :=
    @gN3impa (.classMem A M) (.classMem B N) (.classEq (synCin A B) (synC0))
      (synWrex a M (synWrex b N (synWa (.classEq (synCin (.cv a) (.cv b)) (synC0))
            (.classEq (synCun A B) (synCun (.cv a) (.cv b))))))
      p0013
  have freeVariableCertificate2 : a ∉ ((synCun A B)).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, Finset.mem_union,
      fresh_a_not_A, fresh_a_not_B, or_false, not_false_eq_true]
  have freeVariableCertificate3 : b ∉ ((synCun A B)).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, Finset.mem_union,
      fresh_b_not_A, fresh_b_not_B, or_false, not_false_eq_true]
  have p0015 :=
    @gEladdc (synCun A B) M N a b freeVariableCertificate2 freeVariableCertificate3
      (by exact (show a ∉ (M).fv from (by exact fresh_a_not_M)))
      (by exact (show b ∉ (M).fv from (by exact fresh_b_not_M)))
      (by exact (show a ∉ (N).fv from (by exact fresh_a_not_N)))
      (by exact (show b ∉ (N).fv from (by exact fresh_b_not_N)))
      (show a ≠ b from (by exact fresh_a_ne_b))
  have p0016 :=
    @gSylibr (synW3a (.classMem A M) (.classMem B N) (.classEq (synCin A B) (synC0)))
      (synWrex a M (synWrex b N (synWa (.classEq (synCin (.cv a) (.cv b)) (synC0))
            (.classEq (synCun A B) (synCun (.cv a) (.cv b))))))
      (.classMem (synCun A B) (synCplc M N)) p0014 p0015
  exact p0016

/-- Checked nominal proof certificate identified upstream as `g_n_0nelsuc`. -/
@[expose]
noncomputable def gN0nelsuc (A : Class) :
    Nominal.NPrf (.neg (.classMem (synC0) (synCplc A (synC1c)))) :=
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
  have p0000 := @gEl1c n (.cv m) freeVariableCertificate0
  have p0001 := @gVex n
  have p0002 := @gSnid (.cv n) p0001
  have p0003 := @gN0i (synCsn (.cv n)) (.cv n)
  have p0004 := Nominal.mp p0002 p0003
  have p0005 := @gEqeq1 (.cv m) (synCsn (.cv n)) (synC0)
  have p0006 :=
    @gMtbiri (.classEq (.cv m) (synCsn (.cv n))) (.classEq (.cv m) (synC0))
      (.classEq (synCsn (.cv n)) (synC0)) p0004 p0005
  have freeVariableCertificate1 : n ∉ ((Wff.neg (.classEq (.cv m) (synC0)))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_neg,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_n_ne_m, or_false,
      not_false_eq_true]
  have p0007 :=
    @gExlimiv (.classEq (.cv m) (synCsn (.cv n))) (.neg (.classEq (.cv m) (synC0))) n
      freeVariableCertificate1 p0006
  have p0008 :=
    @gSylbi (.classMem (.cv m) (synC1c))
      (synWex n (.classEq (.cv m) (synCsn (.cv n)))) (.neg (.classEq (.cv m) (synC0)))
      p0000 p0007
  have p0009 := @gSimpr (.classEq (.cv n) (synC0)) (.classEq (.cv m) (synC0))
  have p0010 :=
    @gNsyl (.classMem (.cv m) (synC1c)) (.classEq (.cv m) (synC0))
      (synWa (.classEq (.cv n) (synC0)) (.classEq (.cv m) (synC0))) p0008 p0009
  have p0011 := @gUn00 (.cv n) (.cv m)
  have p0012 := @gEqcom (synCun (.cv n) (.cv m)) (synC0)
  have p0013 :=
    @gBitri (synWa (.classEq (.cv n) (synC0)) (.classEq (.cv m) (synC0)))
      (.classEq (synCun (.cv n) (.cv m)) (synC0))
      (.classEq (synC0) (synCun (.cv n) (.cv m))) p0011 p0012
  have p0014 :=
    @gNotbii (synWa (.classEq (.cv n) (synC0)) (.classEq (.cv m) (synC0)))
      (.classEq (synC0) (synCun (.cv n) (.cv m))) p0013
  have p0015 :=
    @gSylib (.classMem (.cv m) (synC1c))
      (.neg (synWa (.classEq (.cv n) (synC0)) (.classEq (.cv m) (synC0))))
      (.neg (.classEq (synC0) (synCun (.cv n) (.cv m)))) p0010 p0014
  have p0016 :=
    @gSimpr (.classEq (synCin (.cv n) (.cv m)) (synC0))
      (.classEq (synC0) (synCun (.cv n) (.cv m)))
  have p0017 :=
    @gNsyl (.classMem (.cv m) (synC1c)) (.classEq (synC0) (synCun (.cv n) (.cv m)))
      (synWa (.classEq (synCin (.cv n) (.cv m)) (synC0))
        (.classEq (synC0) (synCun (.cv n) (.cv m))))
      p0015 p0016
  have p0018 :=
    @gNrex
      (synWa (.classEq (synCin (.cv n) (.cv m)) (synC0))
        (.classEq (synC0) (synCun (.cv n) (.cv m))))
      m (synC1c) p0017
  have p0019 :=
    @gA1i
      (.neg (synWrex m (synC1c) (synWa (.classEq (synCin (.cv n) (.cv m)) (synC0))
            (.classEq (synC0) (synCun (.cv n) (.cv m))))))
      (.classMem (.cv n) A) p0018
  have p0020 :=
    @gNrex
      (synWrex m (synC1c) (synWa (.classEq (synCin (.cv n) (.cv m)) (synC0))
          (.classEq (synC0) (synCun (.cv n) (.cv m)))))
      n A p0019
  have p0021 :=
    @gEladdc (synC0) A (synC1c) n m
      (by
        exact
          (show n ∉ ((synC0)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0];
              exact (show n ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
      (by
        exact
          (show m ∉ ((synC0)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0];
              exact (show m ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
      (by exact (show n ∉ (A).fv from (by exact fresh_n_not_A)))
      (by exact (show m ∉ (A).fv from (by exact fresh_m_not_A)))
      (by
        exact
          (show n ∉ ((synC1c)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c];
              exact (show n ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
      (by
        exact
          (show m ∉ ((synC1c)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c];
              exact (show m ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
      (show n ≠ m from (by exact fresh_n_ne_m))
  have p0022 :=
    @gMtbir (.classMem (synC0) (synCplc A (synC1c)))
      (synWrex n A (synWrex m (synC1c) (synWa (.classEq (synCin (.cv n) (.cv m)) (synC0))
            (.classEq (synC0) (synCun (.cv n) (.cv m))))))
      p0020 p0021
  exact p0022

/-- Checked nominal proof certificate identified upstream as `g_n_0cnsuc`. -/
@[expose]
noncomputable def gN0cnsuc (A : Class) :
    Nominal.NPrf (synWne (synCplc A (synC1c)) (synC0c)) :=
  by
  have p0000 := @gN0nelsuc A
  have p0001 := @gN0ex
  have p0002 := @gSnid (synC0) p0001
  have p0003 := (Nominal.classEqRefl (synC0c))
  have p0004 := @gEleqtrri (synC0) (synCsn (synC0)) (synC0c) p0002 p0003
  have p0005 := @gEleq2 (synCplc A (synC1c)) (synC0c) (synC0)
  have p0006 :=
    @gMpbiri (.classEq (synCplc A (synC1c)) (synC0c))
      (.classMem (synC0) (synCplc A (synC1c))) (.classMem (synC0) (synC0c)) p0004
      p0005
  have p0007 :=
    @gMto (.classEq (synCplc A (synC1c)) (synC0c))
      (.classMem (synC0) (synCplc A (synC1c))) p0000 p0006
  have p0008 := (Nominal.biimpRefl (synWne (synCplc A (synC1c)) (synC0c)))
  have p0009 :=
    @gMpbir (synWne (synCplc A (synC1c)) (synC0c))
      (.neg (.classEq (synCplc A (synC1c)) (synC0c))) p0007 p0008
  exact p0009

/-- Checked nominal proof certificate identified upstream as `g_peano1`. -/
@[expose]
noncomputable def gPeano1 : Nominal.NPrf (.classMem (synC0c) (synCnnc)) :=
  by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfNnc y x
      (show x ≠ y from (by exact fresh_x_ne_y))
  have p0001 :=
    @gEleq2i (synCnnc)
      (synCint (.cab x (synWa (.classMem (synC0c) (.cv x))
            (synWral y (.cv x) (.classMem (synCplc (.cv y) (synC1c)) (.cv x))))))
      (synC0c) p0000
  have p0002 := @gN0cex
  have p0003 :=
    @gElintab
      (synWa (.classMem (synC0c) (.cv x))
        (synWral y (.cv x) (.classMem (synCplc (.cv y) (synC1c)) (.cv x))))
      x (synC0c)
      (by
        exact
          (show x ∉ ((synC0c)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c];
              exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
      p0002
  have p0004 :=
    @gBitri (.classMem (synC0c) (synCnnc))
      (.classMem (synC0c) (synCint (.cab x (synWa (.classMem (synC0c) (.cv x))
              (synWral y (.cv x) (.classMem (synCplc (.cv y) (synC1c)) (.cv x)))))))
      (.all x (.imp (synWa (.classMem (synC0c) (.cv x))
            (synWral y (.cv x) (.classMem (synCplc (.cv y) (synC1c)) (.cv x))))
          (.classMem (synC0c) (.cv x))))
      p0001 p0003
  have p0005 :=
    @gSimpl (.classMem (synC0c) (.cv x))
      (synWral y (.cv x) (.classMem (synCplc (.cv y) (synC1c)) (.cv x)))
  have p0006 :=
    @gMpgbir (.classMem (synC0c) (synCnnc))
      (.imp (synWa (.classMem (synC0c) (.cv x))
          (synWral y (.cv x) (.classMem (synCplc (.cv y) (synC1c)) (.cv x))))
        (.classMem (synC0c) (.cv x)))
      x p0004 p0005
  exact p0006

/-- Checked nominal proof certificate identified upstream as `g_peano2`. -/
@[expose]
noncomputable def gPeano2 (A : Class) :
    Nominal.NPrf
      (.imp (.classMem A (synCnnc)) (.classMem (synCplc A (synC1c)) (synCnnc))) :=
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
  have p0000 := @gAddceq1 (.cv a) A (synC1c)
  have p0001 :=
    @gEleq1d (.classEq (.cv a) A) (synCplc (.cv a) (synC1c)) (synCplc A (synC1c))
      (synCnnc) p0000
  have p0002 := @gAddceq1 (.cv y) (.cv a) (synC1c)
  have p0003_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq y a)
        (.classEq (synCplc (.cv y) (synC1c)) (synCplc (.cv a) (synC1c)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synCplc synWrex synWex synWa synC1c
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0002
  have p0003 :=
    @gEleq1d (.objEq y a) (synCplc (.cv y) (synC1c)) (synCplc (.cv a) (synC1c))
      (.cv x) p0003_e00_recanon
  have p0004_e00_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv y) (.cv a)) (synWb (.classMem (synCplc (.cv y) (synC1c)) (.cv x))
          (.classMem (synCplc (.cv a) (synC1c)) (.cv x)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCplc synWrex synWex synWa synC1c
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
    y ∉ ((Wff.classMem (synCplc (.cv a) (synC1c)) (.cv x))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_y_ne_a, fresh_y_ne_x, or_false,
      not_false_eq_true]
  have p0004 :=
    @gRspccv (.classMem (synCplc (.cv y) (synC1c)) (.cv x))
      (.classMem (synCplc (.cv a) (synC1c)) (.cv x)) y (.cv a) (.cv x)
      freeVariableCertificate0 freeVariableCertificate1 freeVariableCertificate2
      p0004_e00_recanon
  have p0005_e00_recanon :
    Nominal.NPrf
      (.imp (synWral y (.cv x) (.classMem (synCplc (.cv y) (synC1c)) (.cv x)))
        (.imp (.objMem a x) (.classMem (synCplc (.cv a) (synC1c)) (.cv x)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWral synCplc synWrex synWex synWa synC1c
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0004
  have p0005 :=
    @gAdantl (synWral y (.cv x) (.classMem (synCplc (.cv y) (synC1c)) (.cv x)))
      (.imp (.objMem a x) (.classMem (synCplc (.cv a) (synC1c)) (.cv x)))
      (.classMem (synC0c) (.cv x)) p0005_e00_recanon
  have p0006 :=
    @gA2i
      (synWa (.classMem (synC0c) (.cv x))
        (synWral y (.cv x) (.classMem (synCplc (.cv y) (synC1c)) (.cv x))))
      (.objMem a x) (.classMem (synCplc (.cv a) (synC1c)) (.cv x)) p0005
  have p0007 :=
    @gAlimi
      (.imp (synWa (.classMem (synC0c) (.cv x))
          (synWral y (.cv x) (.classMem (synCplc (.cv y) (synC1c)) (.cv x)))) (.objMem a x))
      (.imp (synWa (.classMem (synC0c) (.cv x))
          (synWral y (.cv x) (.classMem (synCplc (.cv y) (synC1c)) (.cv x))))
        (.classMem (synCplc (.cv a) (synC1c)) (.cv x)))
      x p0006
  have p0008 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfNnc y x
      (show x ≠ y from (by exact fresh_x_ne_y))
  have p0009 :=
    @gEleq2i (synCnnc)
      (synCint (.cab x (synWa (.classMem (synC0c) (.cv x))
            (synWral y (.cv x) (.classMem (synCplc (.cv y) (synC1c)) (.cv x))))))
      (.cv a) p0008
  have p0010 := @gVex a
  have freeVariableCertificate3 : x ∉ ((Class.cv a)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_x_ne_a, not_false_eq_true]
  have p0011 :=
    @gElintab
      (synWa (.classMem (synC0c) (.cv x))
        (synWral y (.cv x) (.classMem (synCplc (.cv y) (synC1c)) (.cv x))))
      x (.cv a) freeVariableCertificate3 p0010
  have p0012_e01_recanon :
    Nominal.NPrf
      (synWb (.classMem (.cv a) (synCint (.cab x (synWa (.classMem (synC0c) (.cv x))
                (synWral y (.cv x) (.classMem (synCplc (.cv y) (synC1c)) (.cv x)))))))
        (.all x (.imp (synWa (.classMem (synC0c) (.cv x))
              (synWral y (.cv x) (.classMem (synCplc (.cv y) (synC1c)) (.cv x))))
            (.objMem a x)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCint synWa synC0c synCsn synC0 synCdif synCin synCcompl
          synCnin synWnan synCvv synWral synCplc synWrex synWex synC1c
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
    @gBitri (.classMem (.cv a) (synCnnc))
      (.classMem (.cv a) (synCint (.cab x (synWa (.classMem (synC0c) (.cv x))
              (synWral y (.cv x) (.classMem (synCplc (.cv y) (synC1c)) (.cv x)))))))
      (.all x (.imp (synWa (.classMem (synC0c) (.cv x))
            (synWral y (.cv x) (.classMem (synCplc (.cv y) (synC1c)) (.cv x))))
          (.objMem a x)))
      p0009 p0012_e01_recanon
  have p0013 :=
    @gEleq2i (synCnnc)
      (synCint (.cab x (synWa (.classMem (synC0c) (.cv x))
            (synWral y (.cv x) (.classMem (synCplc (.cv y) (synC1c)) (.cv x))))))
      (synCplc (.cv a) (synC1c)) p0008
  have p0014 := @gN1cex
  have p0015 := @gAddcex (.cv a) (synC1c) p0010 p0014
  have freeVariableCertificate4 : x ∉ ((synCplc (.cv a) (synC1c))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_x_ne_a, or_false,
      not_false_eq_true]
  have p0016 :=
    @gElintab
      (synWa (.classMem (synC0c) (.cv x))
        (synWral y (.cv x) (.classMem (synCplc (.cv y) (synC1c)) (.cv x))))
      x (synCplc (.cv a) (synC1c)) freeVariableCertificate4 p0015
  have p0017 :=
    @gBitri (.classMem (synCplc (.cv a) (synC1c)) (synCnnc))
      (.classMem (synCplc (.cv a) (synC1c)) (synCint (.cab x
            (synWa (.classMem (synC0c) (.cv x))
              (synWral y (.cv x) (.classMem (synCplc (.cv y) (synC1c)) (.cv x)))))))
      (.all x (.imp (synWa (.classMem (synC0c) (.cv x))
            (synWral y (.cv x) (.classMem (synCplc (.cv y) (synC1c)) (.cv x))))
          (.classMem (synCplc (.cv a) (synC1c)) (.cv x))))
      p0013 p0016
  have p0018 :=
    @gN3imtr4i
      (.all x (.imp (synWa (.classMem (synC0c) (.cv x))
            (synWral y (.cv x) (.classMem (synCplc (.cv y) (synC1c)) (.cv x))))
          (.objMem a x)))
      (.all x (.imp (synWa (.classMem (synC0c) (.cv x))
            (synWral y (.cv x) (.classMem (synCplc (.cv y) (synC1c)) (.cv x))))
          (.classMem (synCplc (.cv a) (synC1c)) (.cv x))))
      (.classMem (.cv a) (synCnnc)) (.classMem (synCplc (.cv a) (synC1c)) (synCnnc))
      p0007 p0012 p0017
  have freeVariableCertificate5 :
    a ∉ ((Wff.classMem (synCplc A (synC1c)) (synCnnc))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union,
      Finset.notMem_empty, fresh_a_not_A, or_false, not_false_eq_true]
  have p0019 :=
    @gVtoclga (.classMem (synCplc (.cv a) (synC1c)) (synCnnc))
      (.classMem (synCplc A (synC1c)) (synCnnc)) a A (synCnnc)
      (by exact (show a ∉ (A).fv from (by exact fresh_a_not_A)))
      (by
        exact
          (show a ∉ ((synCnnc)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc];
              exact (show a ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
      freeVariableCertificate5 p0001 p0018
  exact p0019

/-- Checked nominal proof certificate identified upstream as `g_peano3`. -/
@[expose]
noncomputable def gPeano3 (A : Class) :
    Nominal.NPrf
      (.imp (.classMem A (synCnnc)) (synWne (synCplc A (synC1c)) (synC0c))) :=
  by
  have p0000 := @gN0cnsuc A
  have p0001 :=
    @gA1i (synWne (synCplc A (synC1c)) (synC0c)) (.classMem A (synCnnc)) p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_addcid1`. -/
@[expose]
noncomputable def gAddcid1 (A : Class) :
    Nominal.NPrf (.classEq (synCplc A (synC0c)) A) :=
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
  have p0000 := (Nominal.classEqRefl (synC0c))
  have p0001 := @gAddceq2i (synC0c) (synCsn (synC0)) A p0000
  have p0002 := @gN0ex
  have p0003 := @gIneq2 (.cv z) (synC0) (.cv y)
  have p0004 :=
    @gEqeq1d (.classEq (.cv z) (synC0)) (synCin (.cv y) (.cv z))
      (synCin (.cv y) (synC0)) (synC0) p0003
  have p0005 := @gUneq2 (.cv z) (synC0) (.cv y)
  have p0006 :=
    @gEqeq2d (.classEq (.cv z) (synC0)) (synCun (.cv y) (.cv z))
      (synCun (.cv y) (synC0)) (.cv x) p0005
  have p0007 :=
    @gAnbi12d (.classEq (.cv z) (synC0)) (.classEq (synCin (.cv y) (.cv z)) (synC0))
      (.classEq (synCin (.cv y) (synC0)) (synC0))
      (.classEq (.cv x) (synCun (.cv y) (.cv z)))
      (.classEq (.cv x) (synCun (.cv y) (synC0))) p0004 p0006
  have p0008 := @gIn0 (.cv y)
  have p0009 :=
    @gBiantrur (.classEq (synCin (.cv y) (synC0)) (synC0))
      (.classEq (.cv x) (synCun (.cv y) (synC0))) p0008
  have p0010 :=
    @gSyl6bbr (.classEq (.cv z) (synC0))
      (synWa (.classEq (synCin (.cv y) (.cv z)) (synC0))
        (.classEq (.cv x) (synCun (.cv y) (.cv z))))
      (synWa (.classEq (synCin (.cv y) (synC0)) (synC0))
        (.classEq (.cv x) (synCun (.cv y) (synC0))))
      (.classEq (.cv x) (synCun (.cv y) (synC0))) p0007 p0009
  have freeVariableCertificate0 :
    z ∉ ((Wff.classEq (.cv x) (synCun (.cv y) (synC0)))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_z_ne_x, fresh_z_ne_y, or_false,
      not_false_eq_true]
  have p0011 :=
    @gRexsn
      (synWa (.classEq (synCin (.cv y) (.cv z)) (synC0))
        (.classEq (.cv x) (synCun (.cv y) (.cv z))))
      (.classEq (.cv x) (synCun (.cv y) (synC0))) z (synC0)
      (by
        exact
          (show z ∉ ((synC0)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0];
              exact (show z ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
      freeVariableCertificate0 p0002 p0010
  have p0012 := @gUn0 (.cv y)
  have p0013 := @gEqeq2i (synCun (.cv y) (synC0)) (.cv y) (.cv x) p0012
  have p0014 := @gEqucom x y
  have p0015_e01_recanon :
    Nominal.NPrf (synWb (.classEq (.cv x) (synCun (.cv y) (synC0))) (.objEq x y)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCun synCnin synWnan synWa synCcompl synC0 synCdif synCin
          synCvv
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
    @gN3bitri
      (synWrex z (synCsn (synC0)) (synWa (.classEq (synCin (.cv y) (.cv z)) (synC0))
          (.classEq (.cv x) (synCun (.cv y) (.cv z)))))
      (.classEq (.cv x) (synCun (.cv y) (synC0))) (.objEq x y) (.objEq y x) p0011
      p0015_e01_recanon p0014
  have p0016 :=
    @gRexbii
      (synWrex z (synCsn (synC0)) (synWa (.classEq (synCin (.cv y) (.cv z)) (synC0))
          (.classEq (.cv x) (synCun (.cv y) (.cv z)))))
      (.objEq y x) y A p0015
  have freeVariableCertificate1 : y ∉ ((Class.cv x)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_y_ne_x, not_false_eq_true]
  have freeVariableCertificate2 : z ∉ ((Class.cv x)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_z_ne_x, not_false_eq_true]
  have freeVariableCertificate3 : y ∉ ((synCsn (synC0))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.notMem_empty,
      not_false_eq_true]
  have freeVariableCertificate4 : z ∉ ((synCsn (synC0))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.notMem_empty,
      not_false_eq_true]
  have p0017 :=
    @gEladdc (.cv x) A (synCsn (synC0)) y z freeVariableCertificate1
      freeVariableCertificate2 (by exact (show y ∉ (A).fv from (by exact fresh_y_not_A)))
      (by exact (show z ∉ (A).fv from (by exact fresh_z_not_A))) freeVariableCertificate3
      freeVariableCertificate4 (show y ≠ z from (by exact fresh_y_ne_z))
  have p0018 :=
    @gRisset y (.cv x) A freeVariableCertificate1
      (by exact (show y ∉ (A).fv from (by exact fresh_y_not_A)))
  have p0019_e02_recanon :
    Nominal.NPrf (synWb (.classMem (.cv x) A) (synWrex y A (.objEq y x))) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [synWb, synWrex, synWex, synWa]
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
    @gN3bitr4i
      (synWrex y A (synWrex z (synCsn (synC0))
          (synWa (.classEq (synCin (.cv y) (.cv z)) (synC0))
            (.classEq (.cv x) (synCun (.cv y) (.cv z))))))
      (synWrex y A (.objEq y x)) (.classMem (.cv x) (synCplc A (synCsn (synC0))))
      (.classMem (.cv x) A) p0016 p0017 p0019_e02_recanon
  have freeVariableCertificate5 : x ∉ ((synCplc A (synCsn (synC0)))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union,
      Finset.notMem_empty, fresh_x_not_A, or_false, not_false_eq_true]
  have p0020 :=
    @gEqriv x (synCplc A (synCsn (synC0))) A freeVariableCertificate5
      (by exact (show x ∉ (A).fv from (by exact fresh_x_not_A))) p0019
  have p0021 :=
    @gEqtri (synCplc A (synC0c)) (synCplc A (synCsn (synC0))) A p0001 p0020
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

/-- Checked nominal proof certificate identified upstream as `g_addccom`. -/
@[expose]
noncomputable def gAddccom (A : Class) (B : Class) :
    Nominal.NPrf (.classEq (synCplc A B) (synCplc B A)) :=
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
  have p0000 := @gIncom (.cv y) (.cv z)
  have p0001 :=
    @gEqeq1i (synCin (.cv y) (.cv z)) (synCin (.cv z) (.cv y)) (synC0) p0000
  have p0002 := @gUncom (.cv y) (.cv z)
  have p0003 :=
    @gEqeq2i (synCun (.cv y) (.cv z)) (synCun (.cv z) (.cv y)) (.cv x) p0002
  have p0004 :=
    @gAnbi12i (.classEq (synCin (.cv y) (.cv z)) (synC0))
      (.classEq (synCin (.cv z) (.cv y)) (synC0))
      (.classEq (.cv x) (synCun (.cv y) (.cv z)))
      (.classEq (.cv x) (synCun (.cv z) (.cv y))) p0001 p0003
  have p0005 :=
    @gN2rexbii
      (synWa (.classEq (synCin (.cv y) (.cv z)) (synC0))
        (.classEq (.cv x) (synCun (.cv y) (.cv z))))
      (synWa (.classEq (synCin (.cv z) (.cv y)) (synC0))
        (.classEq (.cv x) (synCun (.cv z) (.cv y))))
      y z A B p0004
  have p0006 :=
    @gRexcom
      (synWa (.classEq (synCin (.cv z) (.cv y)) (synC0))
        (.classEq (.cv x) (synCun (.cv z) (.cv y))))
      y z A B (by exact (show z ∉ (A).fv from (by exact fresh_z_not_A)))
      (by exact (show y ∉ (B).fv from (by exact fresh_y_not_B)))
      (show y ≠ z from (by exact fresh_y_ne_z))
  have p0007 :=
    @gBitri
      (synWrex y A (synWrex z B (synWa (.classEq (synCin (.cv y) (.cv z)) (synC0))
            (.classEq (.cv x) (synCun (.cv y) (.cv z))))))
      (synWrex y A (synWrex z B (synWa (.classEq (synCin (.cv z) (.cv y)) (synC0))
            (.classEq (.cv x) (synCun (.cv z) (.cv y))))))
      (synWrex z B (synWrex y A (synWa (.classEq (synCin (.cv z) (.cv y)) (synC0))
            (.classEq (.cv x) (synCun (.cv z) (.cv y))))))
      p0005 p0006
  have p0008 :=
    @gAbbii
      (synWrex y A (synWrex z B (synWa (.classEq (synCin (.cv y) (.cv z)) (synC0))
            (.classEq (.cv x) (synCun (.cv y) (.cv z))))))
      (synWrex z B (synWrex y A (synWa (.classEq (synCin (.cv z) (.cv y)) (synC0))
            (.classEq (.cv x) (synCun (.cv z) (.cv y))))))
      x p0007
  have p0009 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfAddc x y z A B
      (by exact (show x ∉ (A).fv from (by exact fresh_x_not_A)))
      (by exact (show y ∉ (A).fv from (by exact fresh_y_not_A)))
      (by exact (show z ∉ (A).fv from (by exact fresh_z_not_A)))
      (by exact (show x ∉ (B).fv from (by exact fresh_x_not_B)))
      (by exact (show y ∉ (B).fv from (by exact fresh_y_not_B)))
      (by exact (show z ∉ (B).fv from (by exact fresh_z_not_B)))
      (show x ≠ y from (by exact fresh_x_ne_y)) (show x ≠ z from (by exact fresh_x_ne_z))
      (show y ≠ z from (by exact fresh_y_ne_z))
  have p0010 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfAddc x z y B A
      (by exact (show x ∉ (B).fv from (by exact fresh_x_not_B)))
      (by exact (show z ∉ (B).fv from (by exact fresh_z_not_B)))
      (by exact (show y ∉ (B).fv from (by exact fresh_y_not_B)))
      (by exact (show x ∉ (A).fv from (by exact fresh_x_not_A)))
      (by exact (show z ∉ (A).fv from (by exact fresh_z_not_A)))
      (by exact (show y ∉ (A).fv from (by exact fresh_y_not_A)))
      (show x ≠ z from (by exact fresh_x_ne_z)) (show x ≠ y from (by exact fresh_x_ne_y))
      (show z ≠ y from (by exact fresh_z_ne_y))
  have p0011 :=
    @gN3eqtr4i
      (.cab x (synWrex y A (synWrex z B (synWa (.classEq (synCin (.cv y) (.cv z)) (synC0))
              (.classEq (.cv x) (synCun (.cv y) (.cv z)))))))
      (.cab x (synWrex z B (synWrex y A (synWa (.classEq (synCin (.cv z) (.cv y)) (synC0))
              (.classEq (.cv x) (synCun (.cv z) (.cv y)))))))
      (synCplc A B) (synCplc B A) p0008 p0009 p0010
  exact p0011

/-- Checked nominal proof certificate identified upstream as `g_addcid2`. -/
@[expose]
noncomputable def gAddcid2 (A : Class) :
    Nominal.NPrf (.classEq (synCplc (synC0c) A) A) :=
  by
  have p0000 := @gAddccom (synC0c) A
  have p0001 := @gAddcid1 A
  have p0002 := @gEqtri (synCplc (synC0c) A) (synCplc A (synC0c)) A p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_n_1cnnc`. -/
@[expose]
noncomputable def gN1cnnc : Nominal.NPrf (.classMem (synC1c) (synCnnc)) :=
  by
  have p0000 := @gAddcid1 (synC1c)
  have p0001 := @gAddccom (synC1c) (synC0c)
  have p0002 :=
    @gEqtr3i (synCplc (synC1c) (synC0c)) (synC1c) (synCplc (synC0c) (synC1c))
      p0000 p0001
  have p0003 := @gPeano1
  have p0004 := @gPeano2 (synC0c)
  have p0005 := Nominal.mp p0003 p0004
  have p0006 := @gEqeltri (synC1c) (synCplc (synC0c) (synC1c)) (synCnnc) p0002 p0005
  exact p0006

/-- Checked nominal proof certificate identified upstream as `g_peano5`. -/
@[expose]
noncomputable def gPeano5 (x : Var) (A : Class) (V : Class) (dv_A_x : x ∉ A.fv) :
    Nominal.NPrf
      (.imp (synW3a (.classMem A V) (.classMem (synC0c) A) (synWral x (synCnnc)
            (.imp (.classMem (.cv x) A) (.classMem (synCplc (.cv x) (synC1c)) A))))
        (synWss (synCnnc) A)) :=
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
  have p0000 := @gNncex
  have p0001 := @gInexg (synCnnc) A (synCvv) V
  have p0002 :=
    @gMpan (.classMem (synCnnc) (synCvv)) (.classMem A V)
      (.classMem (synCin (synCnnc) A) (synCvv)) p0000 p0001
  have p0003 := @gPeano1
  have p0004 := @gElin (synC0c) (synCnnc) A
  have p0005 :=
    @gBiimpri (.classMem (synC0c) (synCin (synCnnc) A))
      (synWa (.classMem (synC0c) (synCnnc)) (.classMem (synC0c) A)) p0004
  have p0006 :=
    @gMpan (.classMem (synC0c) (synCnnc)) (.classMem (synC0c) A)
      (.classMem (synC0c) (synCin (synCnnc) A)) p0003 p0005
  have p0007 := @gElin (.cv x) (synCnnc) A
  have p0008 :=
    @gImbi1i (.classMem (.cv x) (synCin (synCnnc) A))
      (synWa (.classMem (.cv x) (synCnnc)) (.classMem (.cv x) A))
      (.classMem (synCplc (.cv x) (synC1c)) A) p0007
  have p0009 :=
    @gImpexp (.classMem (.cv x) (synCnnc)) (.classMem (.cv x) A)
      (.classMem (synCplc (.cv x) (synC1c)) A)
  have p0010 :=
    @gBitri
      (.imp (.classMem (.cv x) (synCin (synCnnc) A))
        (.classMem (synCplc (.cv x) (synC1c)) A))
      (.imp (synWa (.classMem (.cv x) (synCnnc)) (.classMem (.cv x) A))
        (.classMem (synCplc (.cv x) (synC1c)) A))
      (.imp (.classMem (.cv x) (synCnnc))
        (.imp (.classMem (.cv x) A) (.classMem (synCplc (.cv x) (synC1c)) A)))
      p0008 p0009
  have p0011 := @gInss1 (synCnnc) A
  have p0012 := @gSseli (synCin (synCnnc) A) (synCnnc) (.cv x) p0011
  have p0013 := @gPeano2 (.cv x)
  have p0014 :=
    @gSyl (.classMem (.cv x) (synCin (synCnnc) A)) (.classMem (.cv x) (synCnnc))
      (.classMem (synCplc (.cv x) (synC1c)) (synCnnc)) p0012 p0013
  have p0015 := @gElin (synCplc (.cv x) (synC1c)) (synCnnc) A
  have p0016 :=
    @gBiimpri (.classMem (synCplc (.cv x) (synC1c)) (synCin (synCnnc) A))
      (synWa (.classMem (synCplc (.cv x) (synC1c)) (synCnnc))
        (.classMem (synCplc (.cv x) (synC1c)) A))
      p0015
  have p0017 :=
    @gA1i
      (.imp (synWa (.classMem (synCplc (.cv x) (synC1c)) (synCnnc))
          (.classMem (synCplc (.cv x) (synC1c)) A))
        (.classMem (synCplc (.cv x) (synC1c)) (synCin (synCnnc) A)))
      (.classMem (.cv x) (synCin (synCnnc) A)) p0016
  have p0018 :=
    @gMpand (.classMem (.cv x) (synCin (synCnnc) A))
      (.classMem (synCplc (.cv x) (synC1c)) (synCnnc))
      (.classMem (synCplc (.cv x) (synC1c)) A)
      (.classMem (synCplc (.cv x) (synC1c)) (synCin (synCnnc) A)) p0014 p0017
  have p0019 :=
    @gA2i (.classMem (.cv x) (synCin (synCnnc) A))
      (.classMem (synCplc (.cv x) (synC1c)) A)
      (.classMem (synCplc (.cv x) (synC1c)) (synCin (synCnnc) A)) p0018
  have p0020 :=
    @gSylbir
      (.imp (.classMem (.cv x) (synCnnc))
        (.imp (.classMem (.cv x) A) (.classMem (synCplc (.cv x) (synC1c)) A)))
      (.imp (.classMem (.cv x) (synCin (synCnnc) A))
        (.classMem (synCplc (.cv x) (synC1c)) A))
      (.imp (.classMem (.cv x) (synCin (synCnnc) A))
        (.classMem (synCplc (.cv x) (synC1c)) (synCin (synCnnc) A)))
      p0010 p0019
  have p0021 :=
    @gRalimi2 (.imp (.classMem (.cv x) A) (.classMem (synCplc (.cv x) (synC1c)) A))
      (.classMem (synCplc (.cv x) (synC1c)) (synCin (synCnnc) A)) x (synCnnc)
      (synCin (synCnnc) A) p0020
  have p0022 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfNnc x y
      (show y ≠ x from (by exact fresh_y_ne_x))
  have p0023 := @gEleq2 (.cv y) (synCin (synCnnc) A) (synC0c)
  have p0024 := @gEleq2 (.cv y) (synCin (synCnnc) A) (synCplc (.cv x) (synC1c))
  have freeVariableCertificate0 : x ∉ ((Class.cv y)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_x_ne_y, not_false_eq_true]
  have freeVariableCertificate1 : x ∉ ((synCin (synCnnc) A)).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union,
      Finset.notMem_empty, dv_A_x, or_false, not_false_eq_true]
  have p0025 :=
    @gRaleqbi1dv (.classMem (synCplc (.cv x) (synC1c)) (.cv y))
      (.classMem (synCplc (.cv x) (synC1c)) (synCin (synCnnc) A)) x (.cv y)
      (synCin (synCnnc) A) freeVariableCertificate0 freeVariableCertificate1 p0024
  have p0026 :=
    @gAnbi12d (.classEq (.cv y) (synCin (synCnnc) A)) (.classMem (synC0c) (.cv y))
      (.classMem (synC0c) (synCin (synCnnc) A))
      (synWral x (.cv y) (.classMem (synCplc (.cv x) (synC1c)) (.cv y)))
      (synWral x (synCin (synCnnc) A)
        (.classMem (synCplc (.cv x) (synC1c)) (synCin (synCnnc) A)))
      p0023 p0025
  have freeVariableCertificate2 : y ∉ ((synCin (synCnnc) A)).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union,
      Finset.notMem_empty, fresh_y_not_A, or_false, not_false_eq_true]
  have freeVariableCertificate3 :
    y ∉
      ((synWa (.classMem (synC0c) (synCin (synCnnc) A)) (synWral x (synCin (synCnnc) A)
            (.classMem (synCplc (.cv x) (synC1c)) (synCin (synCnnc) A))))).fv :=
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
    @gElabg
      (synWa (.classMem (synC0c) (.cv y))
        (synWral x (.cv y) (.classMem (synCplc (.cv x) (synC1c)) (.cv y))))
      (synWa (.classMem (synC0c) (synCin (synCnnc) A)) (synWral x (synCin (synCnnc) A)
          (.classMem (synCplc (.cv x) (synC1c)) (synCin (synCnnc) A))))
      y (synCin (synCnnc) A) (synCvv) freeVariableCertificate2 freeVariableCertificate3
      p0026
  have p0028 :=
    @gBiimprd (.classMem (synCin (synCnnc) A) (synCvv))
      (.classMem (synCin (synCnnc) A) (.cab y (synWa (.classMem (synC0c) (.cv y))
            (synWral x (.cv y) (.classMem (synCplc (.cv x) (synC1c)) (.cv y))))))
      (synWa (.classMem (synC0c) (synCin (synCnnc) A)) (synWral x (synCin (synCnnc) A)
          (.classMem (synCplc (.cv x) (synC1c)) (synCin (synCnnc) A))))
      p0027
  have p0029 :=
    @gN3impib (.classMem (synCin (synCnnc) A) (synCvv))
      (.classMem (synC0c) (synCin (synCnnc) A))
      (synWral x (synCin (synCnnc) A)
        (.classMem (synCplc (.cv x) (synC1c)) (synCin (synCnnc) A)))
      (.classMem (synCin (synCnnc) A) (.cab y (synWa (.classMem (synC0c) (.cv y))
            (synWral x (.cv y) (.classMem (synCplc (.cv x) (synC1c)) (.cv y))))))
      p0028
  have p0030 :=
    @gIntss1 (synCin (synCnnc) A)
      (.cab y (synWa (.classMem (synC0c) (.cv y))
          (synWral x (.cv y) (.classMem (synCplc (.cv x) (synC1c)) (.cv y)))))
  have p0031 :=
    @gSyl
      (synW3a (.classMem (synCin (synCnnc) A) (synCvv))
        (.classMem (synC0c) (synCin (synCnnc) A)) (synWral x (synCin (synCnnc) A)
          (.classMem (synCplc (.cv x) (synC1c)) (synCin (synCnnc) A))))
      (.classMem (synCin (synCnnc) A) (.cab y (synWa (.classMem (synC0c) (.cv y))
            (synWral x (.cv y) (.classMem (synCplc (.cv x) (synC1c)) (.cv y))))))
      (synWss (synCint (.cab y (synWa (.classMem (synC0c) (.cv y))
              (synWral x (.cv y) (.classMem (synCplc (.cv x) (synC1c)) (.cv y))))))
        (synCin (synCnnc) A))
      p0029 p0030
  have p0032 :=
    @gSyl5eqss
      (synW3a (.classMem (synCin (synCnnc) A) (synCvv))
        (.classMem (synC0c) (synCin (synCnnc) A)) (synWral x (synCin (synCnnc) A)
          (.classMem (synCplc (.cv x) (synC1c)) (synCin (synCnnc) A))))
      (synCnnc)
      (synCint (.cab y (synWa (.classMem (synC0c) (.cv y))
            (synWral x (.cv y) (.classMem (synCplc (.cv x) (synC1c)) (.cv y))))))
      (synCin (synCnnc) A) p0022 p0031
  have p0033 := @gInss2 (synCnnc) A
  have p0034 :=
    @gSyl6ss
      (synW3a (.classMem (synCin (synCnnc) A) (synCvv))
        (.classMem (synC0c) (synCin (synCnnc) A)) (synWral x (synCin (synCnnc) A)
          (.classMem (synCplc (.cv x) (synC1c)) (synCin (synCnnc) A))))
      (synCnnc) (synCin (synCnnc) A) A p0032 p0033
  have p0035 :=
    @gSyl3an (.classMem A V) (.classMem (synCin (synCnnc) A) (synCvv))
      (.classMem (synC0c) A) (.classMem (synC0c) (synCin (synCnnc) A))
      (synWral x (synCnnc)
        (.imp (.classMem (.cv x) A) (.classMem (synCplc (.cv x) (synC1c)) A)))
      (synWral x (synCin (synCnnc) A)
        (.classMem (synCplc (.cv x) (synC1c)) (synCin (synCnnc) A)))
      (synWss (synCnnc) A) p0002 p0006 p0021 p0034
  exact p0035

/-- Checked nominal proof certificate identified upstream as `g_findsd`. -/
@[expose]
noncomputable def gFindsd (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff)
    (et : Wff) (x : Var) (y : Var) (A : Class) (V : Class) (dv_A_x : x ∉ A.fv)
    (dv_ch_x : x ∉ ch.fv) (dv_et_y : y ∉ et.fv) (dv_ph_y : y ∉ ph.fv)
    (dv_ps_x : x ∉ ps.fv) (dv_ta_x : x ∉ ta.fv) (dv_th_x : x ∉ th.fv) (dv_x_y : x ≠ y)
    (hyp_findsd_1 : Nominal.NPrf (.imp et (.classMem (.cab x ph) V)))
    (hyp_findsd_2 : Nominal.NPrf (.imp (.classEq (.cv x) (synC0c)) (synWb ph ps)))
    (hyp_findsd_3 : Nominal.NPrf (.imp (.objEq x y) (synWb ph ch)))
    (hyp_findsd_4 :
      Nominal.NPrf (.imp (.classEq (.cv x) (synCplc (.cv y) (synC1c))) (synWb ph th)))
    (hyp_findsd_5 : Nominal.NPrf (.imp (.classEq (.cv x) A) (synWb ph ta)))
    (hyp_findsd_6 : Nominal.NPrf (.imp et ps))
    (hyp_findsd_7 :
      Nominal.NPrf (.imp (synWa (.classMem (.cv y) (synCnnc)) et) (.imp ch th))) :
    Nominal.NPrf (.imp (synWa (.classMem A (synCnnc)) et) ta) :=
  by
  have p0000 := @gN0cex
  have p0001 :=
    @gElab ph ps x (synC0c)
      (by
        exact
          (show x ∉ ((synC0c)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c];
              exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
      (by exact (show x ∉ (ps).fv from (by exact dv_ps_x))) p0000 hyp_findsd_2
  have p0002 := @gSylibr et ps (.classMem (synC0c) (.cab x ph)) hyp_findsd_6 p0001
  have p0003 := @gVex y
  have p0004_e01_recanon :
    Nominal.NPrf (.imp (.classEq (.cv x) (.cv y)) (synWb ph ch)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      hyp_findsd_3
  have freeVariableCertificate0 : x ∉ ((Class.cv y)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, dv_x_y,
      not_false_eq_true]
  have p0004 :=
    @gElab ph ch x (.cv y) freeVariableCertificate0
      (by exact (show x ∉ (ch).fv from (by exact dv_ch_x))) p0003 p0004_e01_recanon
  have p0005 := @gN1cex
  have p0006 := @gAddcex (.cv y) (synC1c) p0003 p0005
  have freeVariableCertificate1 : x ∉ ((synCplc (.cv y) (synC1c))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, dv_x_y, or_false, not_false_eq_true]
  have p0007 :=
    @gElab ph th x (synCplc (.cv y) (synC1c)) freeVariableCertificate1
      (by exact (show x ∉ (th).fv from (by exact dv_th_x))) p0006 hyp_findsd_4
  have p0008 :=
    @gN3imtr4g (synWa (.classMem (.cv y) (synCnnc)) et) ch th
      (.classMem (.cv y) (.cab x ph)) (.classMem (synCplc (.cv y) (synC1c)) (.cab x ph))
      hyp_findsd_7 p0004 p0007
  have p0009 :=
    @gAncoms (.classMem (.cv y) (synCnnc)) et
      (.imp (.classMem (.cv y) (.cab x ph))
        (.classMem (synCplc (.cv y) (synC1c)) (.cab x ph)))
      p0008
  have p0010 :=
    @gRalrimiva et
      (.imp (.classMem (.cv y) (.cab x ph))
        (.classMem (synCplc (.cv y) (synC1c)) (.cab x ph)))
      y (synCnnc) (by exact (show y ∉ (et).fv from (by exact dv_et_y))) p0009
  have freeVariableCertificate2 : y ∉ ((Class.cab x ph)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cab, Finset.mem_erase, dv_ph_y,
      and_false, not_false_eq_true]
  have p0011 := @gPeano5 y (.cab x ph) V freeVariableCertificate2
  have p0012 :=
    @gSyl3anc et (.classMem (.cab x ph) V) (.classMem (synC0c) (.cab x ph))
      (synWral y (synCnnc) (.imp (.classMem (.cv y) (.cab x ph))
          (.classMem (synCplc (.cv y) (synC1c)) (.cab x ph))))
      (synWss (synCnnc) (.cab x ph)) hyp_findsd_1 p0002 p0010 p0011
  have p0013 := @gSseld et (synCnnc) (.cab x ph) A p0012
  have p0014 := @gImpcom et (.classMem A (synCnnc)) (.classMem A (.cab x ph)) p0013
  have p0015 :=
    @gElabg ph ta x A (synCnnc) (by exact (show x ∉ (A).fv from (by exact dv_A_x)))
      (by exact (show x ∉ (ta).fv from (by exact dv_ta_x))) hyp_findsd_5
  have p0016 :=
    @gAdantr (.classMem A (synCnnc)) (synWb (.classMem A (.cab x ph)) ta) et p0015
  have p0017 :=
    @gMpbid (synWa (.classMem A (synCnnc)) et) (.classMem A (.cab x ph)) ta p0014 p0016
  exact p0017

/-- Checked nominal proof certificate identified upstream as `g_finds`. -/
@[expose]
noncomputable def gFinds (ph : Wff) (ps : Wff) (ch : Wff) (th : Wff) (ta : Wff) (x : Var)
    (y : Var) (A : Class) (dv_A_x : x ∉ A.fv) (dv_ch_x : x ∉ ch.fv) (dv_ph_y : y ∉ ph.fv)
    (dv_ps_x : x ∉ ps.fv) (dv_ta_x : x ∉ ta.fv) (dv_th_x : x ∉ th.fv) (dv_x_y : x ≠ y)
    (hyp_finds_1 : Nominal.NPrf (.classMem (.cab x ph) (synCvv)))
    (hyp_finds_2 : Nominal.NPrf (.imp (.classEq (.cv x) (synC0c)) (synWb ph ps)))
    (hyp_finds_3 : Nominal.NPrf (.imp (.objEq x y) (synWb ph ch)))
    (hyp_finds_4 :
      Nominal.NPrf (.imp (.classEq (.cv x) (synCplc (.cv y) (synC1c))) (synWb ph th)))
    (hyp_finds_5 : Nominal.NPrf (.imp (.classEq (.cv x) A) (synWb ph ta)))
    (hyp_finds_6 : Nominal.NPrf ps)
    (hyp_finds_7 : Nominal.NPrf (.imp (.classMem (.cv y) (synCnnc)) (.imp ch th))) :
    Nominal.NPrf (.imp (.classMem A (synCnnc)) ta) :=
  by
  have p0000 := @gTru
  have p0001 := @gA1i (.classMem (.cab x ph) (synCvv)) synWtru hyp_finds_1
  have p0002 := @gA1i ps synWtru hyp_finds_6
  have p0003 := @gAdantr (.classMem (.cv y) (synCnnc)) (.imp ch th) synWtru hyp_finds_7
  have p0004 :=
    @gFindsd ph ps ch th ta synWtru x y A (synCvv)
      (by exact (show x ∉ (A).fv from (by exact dv_A_x)))
      (by exact (show x ∉ (ch).fv from (by exact dv_ch_x)))
      (by
        exact
          (show y ∉ (synWtru).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wtru];
              exact (show y ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
      (by exact (show y ∉ (ph).fv from (by exact dv_ph_y)))
      (by exact (show x ∉ (ps).fv from (by exact dv_ps_x)))
      (by exact (show x ∉ (ta).fv from (by exact dv_ta_x)))
      (by exact (show x ∉ (th).fv from (by exact dv_th_x)))
      (show x ≠ y from (by exact dv_x_y)) p0001 hyp_finds_2 hyp_finds_3 hyp_finds_4
      hyp_finds_5 p0002 p0003
  have p0005 := @gMpan2 (.classMem A (synCnnc)) synWtru ta p0000 p0004
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

/-- Checked nominal proof certificate identified upstream as `g_nnc0suc`. -/
@[expose]
noncomputable def gNnc0suc (x : Var) (A : Class) (dv_A_x : x ∉ A.fv) :
    Nominal.NPrf
      (synWb (.classMem A (synCnnc)) (synWo (.classEq A (synC0c))
          (synWrex x (synCnnc) (.classEq A (synCplc (.cv x) (synC1c)))))) :=
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
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfSn n (synC0c)
      (by
        exact
          (show n ∉ ((synC0c)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c];
              exact (show n ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
  have p0001 := @gVex n
  have freeVariableCertificate0 :
    x ∉
      ((synCimagek (synCimak (synCdif (synCins3k (synCcompl
                  (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                    (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                (synCsymdif (synCins2k (synCins2k (synCssetk)))
                  (synCun (synCins2k (synCins3k (synCssetk)))
                    (synCins3k (synCsik (synCsik (synCssetk))))))
                (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
            (synCpw1 (synCpw1 (synC1c)))))).fv :=
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
    @gElimak x
      (synCimagek (synCimak (synCdif (synCins3k (synCcompl
                (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                  (synCpw1 (synCpw1 (synC1c)))))) (synCimak
              (synCsymdif (synCins2k (synCins2k (synCssetk)))
                (synCun (synCins2k (synCins3k (synCssetk)))
                  (synCins3k (synCsik (synCsik (synCssetk))))))
              (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
          (synCpw1 (synCpw1 (synC1c)))))
      (synCnnc) (.cv n) freeVariableCertificate0
      (by
        exact
          (show x ∉ ((synCnnc)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc];
              exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
      freeVariableCertificate1 p0001
  have p0003 := @gVex x
  have p0004 :=
    @gOpkelimagekg (.cv x) (.cv n)
      (synCimak (synCdif (synCins3k (synCcompl
              (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                (synCpw1 (synCpw1 (synC1c)))))) (synCimak
            (synCsymdif (synCins2k (synCins2k (synCssetk)))
              (synCun (synCins2k (synCins3k (synCssetk)))
                (synCins3k (synCsik (synCsik (synCssetk))))))
            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
        (synCpw1 (synCpw1 (synC1c))))
      (synCvv) (synCvv)
  have p0005 :=
    @gMp2an (.classMem (.cv x) (synCvv)) (.classMem (.cv n) (synCvv))
      (synWb (.classMem (synCopk (.cv x) (.cv n)) (synCimagek (synCimak (synCdif
                (synCins3k (synCcompl (synCimak
                      (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                      (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                  (synCsymdif (synCins2k (synCins2k (synCssetk)))
                    (synCun (synCins2k (synCins3k (synCssetk)))
                      (synCins3k (synCsik (synCsik (synCssetk))))))
                  (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
              (synCpw1 (synCpw1 (synC1c)))))) (.classEq (.cv n) (synCimak (synCimak
              (synCdif (synCins3k (synCcompl (synCimak
                      (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                      (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                  (synCsymdif (synCins2k (synCins2k (synCssetk)))
                    (synCun (synCins2k (synCins3k (synCssetk)))
                      (synCins3k (synCsik (synCsik (synCssetk))))))
                  (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
              (synCpw1 (synCpw1 (synC1c)))) (.cv x))))
      p0003 p0001 p0004
  have p0006 := @gDfaddc2 (.cv x) (synC1c)
  have p0007 :=
    @gEqeq2i (synCplc (.cv x) (synC1c))
      (synCimak (synCimak (synCdif (synCins3k (synCcompl
                (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                  (synCpw1 (synCpw1 (synC1c)))))) (synCimak
              (synCsymdif (synCins2k (synCins2k (synCssetk)))
                (synCun (synCins2k (synCins3k (synCssetk)))
                  (synCins3k (synCsik (synCsik (synCssetk))))))
              (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
          (synCpw1 (synCpw1 (synC1c)))) (.cv x))
      (.cv n) p0006
  have p0008 :=
    @gBitr4i
      (.classMem (synCopk (.cv x) (.cv n)) (synCimagek (synCimak (synCdif (synCins3k
                (synCcompl
                  (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                    (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                (synCsymdif (synCins2k (synCins2k (synCssetk)))
                  (synCun (synCins2k (synCins3k (synCssetk)))
                    (synCins3k (synCsik (synCsik (synCssetk))))))
                (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
            (synCpw1 (synCpw1 (synC1c))))))
      (.classEq (.cv n) (synCimak (synCimak (synCdif (synCins3k (synCcompl
                  (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                    (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                (synCsymdif (synCins2k (synCins2k (synCssetk)))
                  (synCun (synCins2k (synCins3k (synCssetk)))
                    (synCins3k (synCsik (synCsik (synCssetk))))))
                (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
            (synCpw1 (synCpw1 (synC1c)))) (.cv x)))
      (.classEq (.cv n) (synCplc (.cv x) (synC1c))) p0005 p0007
  have p0009 :=
    @gRexbii
      (.classMem (synCopk (.cv x) (.cv n)) (synCimagek (synCimak (synCdif (synCins3k
                (synCcompl
                  (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                    (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                (synCsymdif (synCins2k (synCins2k (synCssetk)))
                  (synCun (synCins2k (synCins3k (synCssetk)))
                    (synCins3k (synCsik (synCsik (synCssetk))))))
                (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
            (synCpw1 (synCpw1 (synC1c))))))
      (.classEq (.cv n) (synCplc (.cv x) (synC1c))) x (synCnnc) p0008
  have p0010 :=
    @gBitri
      (.classMem (.cv n) (synCimak (synCimagek (synCimak (synCdif (synCins3k (synCcompl
                    (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                      (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                  (synCsymdif (synCins2k (synCins2k (synCssetk)))
                    (synCun (synCins2k (synCins3k (synCssetk)))
                      (synCins3k (synCsik (synCsik (synCssetk))))))
                  (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
              (synCpw1 (synCpw1 (synC1c))))) (synCnnc)))
      (synWrex x (synCnnc) (.classMem (synCopk (.cv x) (.cv n)) (synCimagek (synCimak
              (synCdif (synCins3k (synCcompl (synCimak
                      (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                      (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                  (synCsymdif (synCins2k (synCins2k (synCssetk)))
                    (synCun (synCins2k (synCins3k (synCssetk)))
                      (synCins3k (synCsik (synCsik (synCssetk))))))
                  (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
              (synCpw1 (synCpw1 (synC1c)))))))
      (synWrex x (synCnnc) (.classEq (.cv n) (synCplc (.cv x) (synC1c)))) p0002 p0009
  have freeVariableCertificate2 :
    n ∉
      ((synCimak (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak
                      (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                      (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                  (synCsymdif (synCins2k (synCins2k (synCssetk)))
                    (synCun (synCins2k (synCins3k (synCssetk)))
                      (synCins3k (synCsik (synCsik (synCssetk))))))
                  (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
              (synCpw1 (synCpw1 (synC1c))))) (synCnnc))).fv :=
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
    @gEqabi (synWrex x (synCnnc) (.classEq (.cv n) (synCplc (.cv x) (synC1c)))) n
      (synCimak (synCimagek (synCimak (synCdif (synCins3k (synCcompl
                  (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                    (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                (synCsymdif (synCins2k (synCins2k (synCssetk)))
                  (synCun (synCins2k (synCins3k (synCssetk)))
                    (synCins3k (synCsik (synCsik (synCssetk))))))
                (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
            (synCpw1 (synCpw1 (synC1c))))) (synCnnc))
      freeVariableCertificate2 p0010
  have p0012 :=
    @gUneq12i (synCsn (synC0c)) (.cab n (.classEq (.cv n) (synC0c)))
      (synCimak (synCimagek (synCimak (synCdif (synCins3k (synCcompl
                  (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                    (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                (synCsymdif (synCins2k (synCins2k (synCssetk)))
                  (synCun (synCins2k (synCins3k (synCssetk)))
                    (synCins3k (synCsik (synCsik (synCssetk))))))
                (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
            (synCpw1 (synCpw1 (synC1c))))) (synCnnc))
      (.cab n (synWrex x (synCnnc) (.classEq (.cv n) (synCplc (.cv x) (synC1c)))))
      p0000 p0011
  have p0013 :=
    @gUnab (.classEq (.cv n) (synC0c))
      (synWrex x (synCnnc) (.classEq (.cv n) (synCplc (.cv x) (synC1c)))) n
  have p0014 :=
    @gEqtri
      (synCun (synCsn (synC0c)) (synCimak (synCimagek (synCimak (synCdif (synCins3k
                  (synCcompl (synCimak
                      (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                      (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                  (synCsymdif (synCins2k (synCins2k (synCssetk)))
                    (synCun (synCins2k (synCins3k (synCssetk)))
                      (synCins3k (synCsik (synCsik (synCssetk))))))
                  (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
              (synCpw1 (synCpw1 (synC1c))))) (synCnnc)))
      (synCun (.cab n (.classEq (.cv n) (synC0c)))
        (.cab n (synWrex x (synCnnc) (.classEq (.cv n) (synCplc (.cv x) (synC1c))))))
      (.cab n (synWo (.classEq (.cv n) (synC0c))
          (synWrex x (synCnnc) (.classEq (.cv n) (synCplc (.cv x) (synC1c))))))
      p0012 p0013
  have p0015 := @gSnex (synC0c)
  have p0016 := @gAddcexlem
  have p0017 := @gN1cex
  have p0018 := @gPw1ex (synC1c) p0017
  have p0019 := @gPw1ex (synCpw1 (synC1c)) p0018
  have p0020 :=
    @gImakex
      (synCdif (synCins3k (synCcompl
            (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
              (synCpw1 (synCpw1 (synC1c)))))) (synCimak
          (synCsymdif (synCins2k (synCins2k (synCssetk)))
            (synCun (synCins2k (synCins3k (synCssetk)))
              (synCins3k (synCsik (synCsik (synCssetk))))))
          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
      (synCpw1 (synCpw1 (synC1c))) p0016 p0019
  have p0021 :=
    @gImagekex
      (synCimak (synCdif (synCins3k (synCcompl
              (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                (synCpw1 (synCpw1 (synC1c)))))) (synCimak
            (synCsymdif (synCins2k (synCins2k (synCssetk)))
              (synCun (synCins2k (synCins3k (synCssetk)))
                (synCins3k (synCsik (synCsik (synCssetk))))))
            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
        (synCpw1 (synCpw1 (synC1c))))
      p0020
  have p0022 := @gNncex
  have p0023 :=
    @gImakex
      (synCimagek (synCimak (synCdif (synCins3k (synCcompl
                (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                  (synCpw1 (synCpw1 (synC1c)))))) (synCimak
              (synCsymdif (synCins2k (synCins2k (synCssetk)))
                (synCun (synCins2k (synCins3k (synCssetk)))
                  (synCins3k (synCsik (synCsik (synCssetk))))))
              (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
          (synCpw1 (synCpw1 (synC1c)))))
      (synCnnc) p0021 p0022
  have p0024 :=
    @gUnex (synCsn (synC0c))
      (synCimak (synCimagek (synCimak (synCdif (synCins3k (synCcompl
                  (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                    (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                (synCsymdif (synCins2k (synCins2k (synCssetk)))
                  (synCun (synCins2k (synCins3k (synCssetk)))
                    (synCins3k (synCsik (synCsik (synCssetk))))))
                (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
            (synCpw1 (synCpw1 (synC1c))))) (synCnnc))
      p0015 p0023
  have p0025 :=
    @gEqeltrri
      (synCun (synCsn (synC0c)) (synCimak (synCimagek (synCimak (synCdif (synCins3k
                  (synCcompl (synCimak
                      (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                      (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                  (synCsymdif (synCins2k (synCins2k (synCssetk)))
                    (synCun (synCins2k (synCins3k (synCssetk)))
                      (synCins3k (synCsik (synCsik (synCssetk))))))
                  (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
              (synCpw1 (synCpw1 (synC1c))))) (synCnnc)))
      (.cab n (synWo (.classEq (.cv n) (synC0c))
          (synWrex x (synCnnc) (.classEq (.cv n) (synCplc (.cv x) (synC1c))))))
      (synCvv) p0014 p0024
  have p0026 := @gEqeq1 (.cv n) (synC0c) (synC0c)
  have p0027 := @gEqeq1 (.cv n) (synC0c) (synCplc (.cv x) (synC1c))
  have freeVariableCertificate3 : x ∉ ((Wff.classEq (.cv n) (synC0c))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_x_ne_n, or_false,
      not_false_eq_true]
  have p0028 :=
    @gRexbidv (.classEq (.cv n) (synC0c))
      (.classEq (.cv n) (synCplc (.cv x) (synC1c)))
      (.classEq (synC0c) (synCplc (.cv x) (synC1c))) x (synCnnc)
      freeVariableCertificate3 p0027
  have p0029 :=
    @gOrbi12d (.classEq (.cv n) (synC0c)) (.classEq (.cv n) (synC0c))
      (.classEq (synC0c) (synC0c))
      (synWrex x (synCnnc) (.classEq (.cv n) (synCplc (.cv x) (synC1c))))
      (synWrex x (synCnnc) (.classEq (synC0c) (synCplc (.cv x) (synC1c)))) p0026
      p0028
  have p0030 := @gEqeq1 (.cv n) (.cv m) (synC0c)
  have p0031 := @gEqeq1 (.cv n) (.cv m) (synCplc (.cv x) (synC1c))
  have p0032_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq n m) (synWb (.classEq (.cv n) (synCplc (.cv x) (synC1c)))
          (.classEq (.cv m) (synCplc (.cv x) (synC1c))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCplc synWrex synWex synWa synC1c
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
    @gRexbidv (.objEq n m) (.classEq (.cv n) (synCplc (.cv x) (synC1c)))
      (.classEq (.cv m) (synCplc (.cv x) (synC1c))) x (synCnnc)
      freeVariableCertificate4 p0032_e00_recanon
  have p0033_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq n m) (synWb (.classEq (.cv n) (synC0c)) (.classEq (.cv m) (synC0c)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synC0c synCsn synC0 synCdif synCin synCcompl synCnin synWnan
          synWa synCvv
        simp (config := { failIfUnchanged := false }) only []
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0030
  have p0033 :=
    @gOrbi12d (.objEq n m) (.classEq (.cv n) (synC0c)) (.classEq (.cv m) (synC0c))
      (synWrex x (synCnnc) (.classEq (.cv n) (synCplc (.cv x) (synC1c))))
      (synWrex x (synCnnc) (.classEq (.cv m) (synCplc (.cv x) (synC1c))))
      p0033_e00_recanon p0032
  have p0034 := @gEqeq1 (.cv n) (synCplc (.cv m) (synC1c)) (synC0c)
  have p0035 := @gEqeq1 (.cv n) (synCplc (.cv m) (synC1c)) (synCplc (.cv x) (synC1c))
  have freeVariableCertificate5 :
    x ∉ ((Wff.classEq (.cv n) (synCplc (.cv m) (synC1c)))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_x_ne_n, fresh_x_ne_m, or_false,
      not_false_eq_true]
  have p0036 :=
    @gRexbidv (.classEq (.cv n) (synCplc (.cv m) (synC1c)))
      (.classEq (.cv n) (synCplc (.cv x) (synC1c)))
      (.classEq (synCplc (.cv m) (synC1c)) (synCplc (.cv x) (synC1c))) x (synCnnc)
      freeVariableCertificate5 p0035
  have p0037 :=
    @gOrbi12d (.classEq (.cv n) (synCplc (.cv m) (synC1c)))
      (.classEq (.cv n) (synC0c)) (.classEq (synCplc (.cv m) (synC1c)) (synC0c))
      (synWrex x (synCnnc) (.classEq (.cv n) (synCplc (.cv x) (synC1c))))
      (synWrex x (synCnnc)
        (.classEq (synCplc (.cv m) (synC1c)) (synCplc (.cv x) (synC1c))))
      p0034 p0036
  have p0038 := @gEqeq1 (.cv n) A (synC0c)
  have p0039 := @gEqeq1 (.cv n) A (synCplc (.cv x) (synC1c))
  have freeVariableCertificate6 : x ∉ ((Wff.classEq (.cv n) A)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      fresh_x_ne_n, dv_A_x, or_false, not_false_eq_true]
  have p0040 :=
    @gRexbidv (.classEq (.cv n) A) (.classEq (.cv n) (synCplc (.cv x) (synC1c)))
      (.classEq A (synCplc (.cv x) (synC1c))) x (synCnnc) freeVariableCertificate6
      p0039
  have p0041 :=
    @gOrbi12d (.classEq (.cv n) A) (.classEq (.cv n) (synC0c)) (.classEq A (synC0c))
      (synWrex x (synCnnc) (.classEq (.cv n) (synCplc (.cv x) (synC1c))))
      (synWrex x (synCnnc) (.classEq A (synCplc (.cv x) (synC1c)))) p0038 p0040
  have p0042 := @gEqid (synC0c)
  have p0043 :=
    @gOrci (.classEq (synC0c) (synC0c))
      (synWrex x (synCnnc) (.classEq (synC0c) (synCplc (.cv x) (synC1c)))) p0042
  have p0044 := @gEqid (synCplc (.cv m) (synC1c))
  have p0045 := @gAddceq1 (.cv x) (.cv m) (synC1c)
  have p0046_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq x m)
        (.classEq (synCplc (.cv x) (synC1c)) (synCplc (.cv m) (synC1c)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synCplc synWrex synWex synWa synC1c
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0045
  have p0046 :=
    @gEqeq2d (.objEq x m) (synCplc (.cv x) (synC1c)) (synCplc (.cv m) (synC1c))
      (synCplc (.cv m) (synC1c)) p0046_e00_recanon
  have p0047_e00_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv x) (.cv m))
        (synWb (.classEq (synCplc (.cv m) (synC1c)) (synCplc (.cv x) (synC1c)))
          (.classEq (synCplc (.cv m) (synC1c)) (synCplc (.cv m) (synC1c))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCplc synWrex synWex synWa synC1c
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
    x ∉ ((Wff.classEq (synCplc (.cv m) (synC1c)) (synCplc (.cv m) (synC1c)))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_x_ne_m, or_false,
      not_false_eq_true]
  have p0047 :=
    @gRspcev (.classEq (synCplc (.cv m) (synC1c)) (synCplc (.cv x) (synC1c)))
      (.classEq (synCplc (.cv m) (synC1c)) (synCplc (.cv m) (synC1c))) x (.cv m)
      (synCnnc) freeVariableCertificate7
      (by
        exact
          (show x ∉ ((synCnnc)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc];
              exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
      freeVariableCertificate8 p0047_e00_recanon
  have p0048 :=
    @gMpan2 (.classMem (.cv m) (synCnnc))
      (.classEq (synCplc (.cv m) (synC1c)) (synCplc (.cv m) (synC1c)))
      (synWrex x (synCnnc)
        (.classEq (synCplc (.cv m) (synC1c)) (synCplc (.cv x) (synC1c))))
      p0044 p0047
  have p0049 :=
    @gOlcd (.classMem (.cv m) (synCnnc))
      (synWrex x (synCnnc)
        (.classEq (synCplc (.cv m) (synC1c)) (synCplc (.cv x) (synC1c))))
      (.classEq (synCplc (.cv m) (synC1c)) (synC0c)) p0048
  have p0050 :=
    @gA1d (.classMem (.cv m) (synCnnc))
      (synWo (.classEq (synCplc (.cv m) (synC1c)) (synC0c)) (synWrex x (synCnnc)
          (.classEq (synCplc (.cv m) (synC1c)) (synCplc (.cv x) (synC1c)))))
      (synWo (.classEq (.cv m) (synC0c))
        (synWrex x (synCnnc) (.classEq (.cv m) (synCplc (.cv x) (synC1c)))))
      p0049
  have freeVariableCertificate9 :
    n ∉
      ((synWo (.classEq (.cv m) (synC0c))
          (synWrex x (synCnnc) (.classEq (.cv m) (synCplc (.cv x) (synC1c)))))).fv :=
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
      ((synWo (.classEq (.cv n) (synC0c))
          (synWrex x (synCnnc) (.classEq (.cv n) (synCplc (.cv x) (synC1c)))))).fv :=
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
      ((synWo (.classEq (synC0c) (synC0c)) (synWrex x (synCnnc)
            (.classEq (synC0c) (synCplc (.cv x) (synC1c)))))).fv :=
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
      ((synWo (.classEq A (synC0c))
          (synWrex x (synCnnc) (.classEq A (synCplc (.cv x) (synC1c)))))).fv :=
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
      ((synWo (.classEq (synCplc (.cv m) (synC1c)) (synC0c)) (synWrex x (synCnnc)
            (.classEq (synCplc (.cv m) (synC1c)) (synCplc (.cv x) (synC1c)))))).fv :=
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
    @gFinds
      (synWo (.classEq (.cv n) (synC0c))
        (synWrex x (synCnnc) (.classEq (.cv n) (synCplc (.cv x) (synC1c)))))
      (synWo (.classEq (synC0c) (synC0c))
        (synWrex x (synCnnc) (.classEq (synC0c) (synCplc (.cv x) (synC1c)))))
      (synWo (.classEq (.cv m) (synC0c))
        (synWrex x (synCnnc) (.classEq (.cv m) (synCplc (.cv x) (synC1c)))))
      (synWo (.classEq (synCplc (.cv m) (synC1c)) (synC0c)) (synWrex x (synCnnc)
          (.classEq (synCplc (.cv m) (synC1c)) (synCplc (.cv x) (synC1c)))))
      (synWo (.classEq A (synC0c))
        (synWrex x (synCnnc) (.classEq A (synCplc (.cv x) (synC1c)))))
      n m A (by exact (show n ∉ (A).fv from (by exact fresh_n_not_A)))
      freeVariableCertificate9 freeVariableCertificate10 freeVariableCertificate11
      freeVariableCertificate12 freeVariableCertificate13
      (show n ≠ m from (by exact fresh_n_ne_m)) p0025 p0029 p0033 p0037 p0041 p0043 p0050
  have p0052 := @gPeano1
  have p0053 := @gEleq1 A (synC0c) (synCnnc)
  have p0054 :=
    @gMpbiri (.classEq A (synC0c)) (.classMem A (synCnnc))
      (.classMem (synC0c) (synCnnc)) p0052 p0053
  have p0055 := @gPeano2 (.cv x)
  have p0056 := @gEleq1 A (synCplc (.cv x) (synC1c)) (synCnnc)
  have p0057 :=
    @gSyl5ibrcom (.classMem (.cv x) (synCnnc)) (.classMem A (synCnnc))
      (.classEq A (synCplc (.cv x) (synC1c)))
      (.classMem (synCplc (.cv x) (synC1c)) (synCnnc)) p0055 p0056
  have freeVariableCertificate14 : x ∉ ((Wff.classMem A (synCnnc))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union,
      Finset.notMem_empty, dv_A_x, or_false, not_false_eq_true]
  have p0058 :=
    @gRexlimiv (.classEq A (synCplc (.cv x) (synC1c))) (.classMem A (synCnnc)) x
      (synCnnc) freeVariableCertificate14 p0057
  have p0059 :=
    @gJaoi (.classEq A (synC0c)) (.classMem A (synCnnc))
      (synWrex x (synCnnc) (.classEq A (synCplc (.cv x) (synC1c)))) p0054 p0058
  have p0060 :=
    @gImpbii (.classMem A (synCnnc))
      (synWo (.classEq A (synC0c))
        (synWrex x (synCnnc) (.classEq A (synCplc (.cv x) (synC1c)))))
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

/-- Checked nominal proof certificate identified upstream as `g_elsuc`. -/
@[expose]
noncomputable def gElsuc (x : Var) (A : Class) (M : Class) (b : Var) (dv_A_b : b ∉ A.fv)
    (dv_A_x : x ∉ A.fv) (dv_M_b : b ∉ M.fv) (dv_b_x : b ≠ x) :
    Nominal.NPrf
      (synWb (.classMem A (synCplc M (synC1c))) (synWrex b M
          (synWrex x (synCcompl (.cv b))
            (.classEq A (synCun (.cv b) (synCsn (.cv x))))))) :=
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
    @gEladdc A M (synC1c) b y (by exact (show b ∉ (A).fv from (by exact dv_A_b)))
      (by exact (show y ∉ (A).fv from (by exact fresh_y_not_A)))
      (by exact (show b ∉ (M).fv from (by exact dv_M_b)))
      (by exact (show y ∉ (M).fv from (by exact fresh_y_not_M)))
      (by
        exact
          (show b ∉ ((synC1c)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c];
              exact (show b ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
      (by
        exact
          (show y ∉ ((synC1c)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c];
              exact (show y ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
      (show b ≠ y from (by exact fresh_b_ne_y))
  have p0001 := @gSnex (.cv x)
  have p0002 := @gIneq2 (.cv y) (synCsn (.cv x)) (.cv b)
  have p0003 :=
    @gEqeq1d (.classEq (.cv y) (synCsn (.cv x))) (synCin (.cv b) (.cv y))
      (synCin (.cv b) (synCsn (.cv x))) (synC0) p0002
  have p0004 := @gUneq2 (.cv y) (synCsn (.cv x)) (.cv b)
  have p0005 :=
    @gEqeq2d (.classEq (.cv y) (synCsn (.cv x))) (synCun (.cv b) (.cv y))
      (synCun (.cv b) (synCsn (.cv x))) A p0004
  have p0006 :=
    @gAnbi12d (.classEq (.cv y) (synCsn (.cv x)))
      (.classEq (synCin (.cv b) (.cv y)) (synC0))
      (.classEq (synCin (.cv b) (synCsn (.cv x))) (synC0))
      (.classEq A (synCun (.cv b) (.cv y)))
      (.classEq A (synCun (.cv b) (synCsn (.cv x)))) p0003 p0005
  have freeVariableCertificate0 : y ∉ ((synCsn (.cv x))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_y_ne_x,
      not_false_eq_true]
  have freeVariableCertificate1 :
    y ∉
      ((synWa (.classEq (synCin (.cv b) (synCsn (.cv x))) (synC0))
          (.classEq A (synCun (.cv b) (synCsn (.cv x)))))).fv :=
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
    @gCeqsexv
      (synWa (.classEq (synCin (.cv b) (.cv y)) (synC0))
        (.classEq A (synCun (.cv b) (.cv y))))
      (synWa (.classEq (synCin (.cv b) (synCsn (.cv x))) (synC0))
        (.classEq A (synCun (.cv b) (synCsn (.cv x)))))
      y (synCsn (.cv x)) freeVariableCertificate0 freeVariableCertificate1 p0001 p0006
  have p0008 := @gDisjsn (.cv b) (.cv x)
  have p0009 := @gVex x
  have p0010 := @gElcompl (.cv x) (.cv b) p0009
  have p0011_e00_recanon :
    Nominal.NPrf
      (synWb (.classEq (synCin (.cv b) (synCsn (.cv x))) (synC0)) (.neg (.objMem x b))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCin synCcompl synCnin synWnan synWa synCsn synC0 synCdif
          synCvv
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
      p0010
  have p0011 :=
    @gBitr4i (.classEq (synCin (.cv b) (synCsn (.cv x))) (synC0)) (.neg (.objMem x b))
      (.classMem (.cv x) (synCcompl (.cv b))) p0011_e00_recanon p0011_e01_recanon
  have p0012 :=
    @gAnbi1i (.classEq (synCin (.cv b) (synCsn (.cv x))) (synC0))
      (.classMem (.cv x) (synCcompl (.cv b)))
      (.classEq A (synCun (.cv b) (synCsn (.cv x)))) p0011
  have p0013 :=
    @gBitri
      (synWex y (synWa (.classEq (.cv y) (synCsn (.cv x)))
          (synWa (.classEq (synCin (.cv b) (.cv y)) (synC0))
            (.classEq A (synCun (.cv b) (.cv y))))))
      (synWa (.classEq (synCin (.cv b) (synCsn (.cv x))) (synC0))
        (.classEq A (synCun (.cv b) (synCsn (.cv x)))))
      (synWa (.classMem (.cv x) (synCcompl (.cv b)))
        (.classEq A (synCun (.cv b) (synCsn (.cv x)))))
      p0007 p0012
  have p0014 :=
    @gExbii
      (synWex y (synWa (.classEq (.cv y) (synCsn (.cv x)))
          (synWa (.classEq (synCin (.cv b) (.cv y)) (synC0))
            (.classEq A (synCun (.cv b) (.cv y))))))
      (synWa (.classMem (.cv x) (synCcompl (.cv b)))
        (.classEq A (synCun (.cv b) (synCsn (.cv x)))))
      x p0013
  have p0015 :=
    (Nominal.biimpRefl (synWrex y (synC1c)
        (synWa (.classEq (synCin (.cv b) (.cv y)) (synC0))
          (.classEq A (synCun (.cv b) (.cv y))))))
  have freeVariableCertificate2 : x ∉ ((Class.cv y)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_x_ne_y, not_false_eq_true]
  have p0016 := @gEl1c x (.cv y) freeVariableCertificate2
  have p0017 :=
    @gAnbi1i (.classMem (.cv y) (synC1c))
      (synWex x (.classEq (.cv y) (synCsn (.cv x))))
      (synWa (.classEq (synCin (.cv b) (.cv y)) (synC0))
        (.classEq A (synCun (.cv b) (.cv y))))
      p0016
  have freeVariableCertificate3 :
    x ∉
      ((synWa (.classEq (synCin (.cv b) (.cv y)) (synC0))
          (.classEq A (synCun (.cv b) (.cv y))))).fv :=
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
    @gN1941v (.classEq (.cv y) (synCsn (.cv x)))
      (synWa (.classEq (synCin (.cv b) (.cv y)) (synC0))
        (.classEq A (synCun (.cv b) (.cv y))))
      x freeVariableCertificate3
  have p0019 :=
    @gBitr4i
      (synWa (.classMem (.cv y) (synC1c))
        (synWa (.classEq (synCin (.cv b) (.cv y)) (synC0))
          (.classEq A (synCun (.cv b) (.cv y)))))
      (synWa (synWex x (.classEq (.cv y) (synCsn (.cv x))))
        (synWa (.classEq (synCin (.cv b) (.cv y)) (synC0))
          (.classEq A (synCun (.cv b) (.cv y)))))
      (synWex x (synWa (.classEq (.cv y) (synCsn (.cv x)))
          (synWa (.classEq (synCin (.cv b) (.cv y)) (synC0))
            (.classEq A (synCun (.cv b) (.cv y))))))
      p0017 p0018
  have p0020 :=
    @gExbii
      (synWa (.classMem (.cv y) (synC1c))
        (synWa (.classEq (synCin (.cv b) (.cv y)) (synC0))
          (.classEq A (synCun (.cv b) (.cv y)))))
      (synWex x (synWa (.classEq (.cv y) (synCsn (.cv x)))
          (synWa (.classEq (synCin (.cv b) (.cv y)) (synC0))
            (.classEq A (synCun (.cv b) (.cv y))))))
      y p0019
  have p0021 :=
    @gExcom
      (synWa (.classEq (.cv y) (synCsn (.cv x)))
        (synWa (.classEq (synCin (.cv b) (.cv y)) (synC0))
          (.classEq A (synCun (.cv b) (.cv y)))))
      y x
  have p0022 :=
    @gBitri
      (synWex y (synWa (.classMem (.cv y) (synC1c))
          (synWa (.classEq (synCin (.cv b) (.cv y)) (synC0))
            (.classEq A (synCun (.cv b) (.cv y))))))
      (synWex y (synWex x (synWa (.classEq (.cv y) (synCsn (.cv x)))
            (synWa (.classEq (synCin (.cv b) (.cv y)) (synC0))
              (.classEq A (synCun (.cv b) (.cv y)))))))
      (synWex x (synWex y (synWa (.classEq (.cv y) (synCsn (.cv x)))
            (synWa (.classEq (synCin (.cv b) (.cv y)) (synC0))
              (.classEq A (synCun (.cv b) (.cv y)))))))
      p0020 p0021
  have p0023 :=
    @gBitri
      (synWrex y (synC1c) (synWa (.classEq (synCin (.cv b) (.cv y)) (synC0))
          (.classEq A (synCun (.cv b) (.cv y)))))
      (synWex y (synWa (.classMem (.cv y) (synC1c))
          (synWa (.classEq (synCin (.cv b) (.cv y)) (synC0))
            (.classEq A (synCun (.cv b) (.cv y))))))
      (synWex x (synWex y (synWa (.classEq (.cv y) (synCsn (.cv x)))
            (synWa (.classEq (synCin (.cv b) (.cv y)) (synC0))
              (.classEq A (synCun (.cv b) (.cv y)))))))
      p0015 p0022
  have p0024 :=
    (Nominal.biimpRefl
      (synWrex x (synCcompl (.cv b)) (.classEq A (synCun (.cv b) (synCsn (.cv x))))))
  have p0025 :=
    @gN3bitr4i
      (synWex x (synWex y (synWa (.classEq (.cv y) (synCsn (.cv x)))
            (synWa (.classEq (synCin (.cv b) (.cv y)) (synC0))
              (.classEq A (synCun (.cv b) (.cv y)))))))
      (synWex x (synWa (.classMem (.cv x) (synCcompl (.cv b)))
          (.classEq A (synCun (.cv b) (synCsn (.cv x))))))
      (synWrex y (synC1c) (synWa (.classEq (synCin (.cv b) (.cv y)) (synC0))
          (.classEq A (synCun (.cv b) (.cv y)))))
      (synWrex x (synCcompl (.cv b)) (.classEq A (synCun (.cv b) (synCsn (.cv x)))))
      p0014 p0023 p0024
  have p0026 :=
    @gRexbii
      (synWrex y (synC1c) (synWa (.classEq (synCin (.cv b) (.cv y)) (synC0))
          (.classEq A (synCun (.cv b) (.cv y)))))
      (synWrex x (synCcompl (.cv b)) (.classEq A (synCun (.cv b) (synCsn (.cv x))))) b
      M p0025
  have p0027 :=
    @gBitri (.classMem A (synCplc M (synC1c)))
      (synWrex b M (synWrex y (synC1c) (synWa (.classEq (synCin (.cv b) (.cv y)) (synC0))
            (.classEq A (synCun (.cv b) (.cv y))))))
      (synWrex b M (synWrex x (synCcompl (.cv b))
          (.classEq A (synCun (.cv b) (synCsn (.cv x))))))
      p0000 p0026
  exact p0027

/-- Checked nominal proof certificate identified upstream as `g_elsuci`. -/
@[expose]
noncomputable def gElsuci (A : Class) (N : Class) (X : Class)
    (hyp_elsuci_1 : Nominal.NPrf (.classMem X (synCvv))) :
    Nominal.NPrf
      (.imp (synWa (.classMem A N) (.neg (.classMem X A)))
        (.classMem (synCun A (synCsn X)) (synCplc N (synC1c)))) :=
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
  have p0000 := @gElcompl X A hyp_elsuci_1
  have p0001 := @gEqid (synCun A (synCsn X))
  have p0002 := @gSneq (.cv x) X
  have p0003 := @gUneq2d (.classEq (.cv x) X) (synCsn (.cv x)) (synCsn X) A p0002
  have p0004 :=
    @gEqeq2d (.classEq (.cv x) X) (synCun A (synCsn (.cv x))) (synCun A (synCsn X))
      (synCun A (synCsn X)) p0003
  have freeVariableCertificate0 :
    x ∉ ((Wff.classEq (synCun A (synCsn X)) (synCun A (synCsn X)))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
      fresh_x_not_A, fresh_x_not_X, or_false, not_false_eq_true]
  have p0005 :=
    @gRspcev (.classEq (synCun A (synCsn X)) (synCun A (synCsn (.cv x))))
      (.classEq (synCun A (synCsn X)) (synCun A (synCsn X))) x X (synCcompl A)
      (by exact (show x ∉ (X).fv from (by exact fresh_x_not_X)))
      (by
        exact
          (show x ∉ ((synCcompl A)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl];
              exact (show x ∉ (A).fv from (by exact fresh_x_not_A)))))
      freeVariableCertificate0 p0004
  have p0006 :=
    @gMpan2 (.classMem X (synCcompl A))
      (.classEq (synCun A (synCsn X)) (synCun A (synCsn X)))
      (synWrex x (synCcompl A)
        (.classEq (synCun A (synCsn X)) (synCun A (synCsn (.cv x)))))
      p0001 p0005
  have p0007 :=
    @gSylbir (.neg (.classMem X A)) (.classMem X (synCcompl A))
      (synWrex x (synCcompl A)
        (.classEq (synCun A (synCsn X)) (synCun A (synCsn (.cv x)))))
      p0000 p0006
  have p0008 := @gCompleq (.cv a) A
  have p0009 := @gUneq1 (.cv a) A (synCsn (.cv x))
  have p0010 :=
    @gEqeq2d (.classEq (.cv a) A) (synCun (.cv a) (synCsn (.cv x)))
      (synCun A (synCsn (.cv x))) (synCun A (synCsn X)) p0009
  have freeVariableCertificate1 : x ∉ ((synCcompl (.cv a))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_x_ne_a,
      not_false_eq_true]
  have freeVariableCertificate2 : x ∉ ((Wff.classEq (.cv a) A)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      fresh_x_ne_a, fresh_x_not_A, or_false, not_false_eq_true]
  have p0011 :=
    @gRexeqbidv (.classEq (.cv a) A)
      (.classEq (synCun A (synCsn X)) (synCun (.cv a) (synCsn (.cv x))))
      (.classEq (synCun A (synCsn X)) (synCun A (synCsn (.cv x)))) x
      (synCcompl (.cv a)) (synCcompl A) freeVariableCertificate1
      (by
        exact
          (show x ∉ ((synCcompl A)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl];
              exact (show x ∉ (A).fv from (by exact fresh_x_not_A)))))
      freeVariableCertificate2 p0008 p0010
  have freeVariableCertificate3 :
    a ∉
      ((synWrex x (synCcompl A)
          (.classEq (synCun A (synCsn X)) (synCun A (synCsn (.cv x)))))).fv :=
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
    @gRspcev
      (synWrex x (synCcompl (.cv a))
        (.classEq (synCun A (synCsn X)) (synCun (.cv a) (synCsn (.cv x)))))
      (synWrex x (synCcompl A)
        (.classEq (synCun A (synCsn X)) (synCun A (synCsn (.cv x)))))
      a A N (by exact (show a ∉ (A).fv from (by exact fresh_a_not_A)))
      (by exact (show a ∉ (N).fv from (by exact fresh_a_not_N))) freeVariableCertificate3
      p0011
  have p0013 :=
    @gSylan2 (.neg (.classMem X A)) (.classMem A N)
      (synWrex x (synCcompl A)
        (.classEq (synCun A (synCsn X)) (synCun A (synCsn (.cv x)))))
      (synWrex a N (synWrex x (synCcompl (.cv a))
          (.classEq (synCun A (synCsn X)) (synCun (.cv a) (synCsn (.cv x))))))
      p0007 p0012
  have freeVariableCertificate4 : a ∉ ((synCun A (synCsn X))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
      fresh_a_not_A, fresh_a_not_X, or_false, not_false_eq_true]
  have freeVariableCertificate5 : x ∉ ((synCun A (synCsn X))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
      fresh_x_not_A, fresh_x_not_X, or_false, not_false_eq_true]
  have p0014 :=
    @gElsuc x (synCun A (synCsn X)) N a freeVariableCertificate4
      freeVariableCertificate5 (by exact (show a ∉ (N).fv from (by exact fresh_a_not_N)))
      (show a ≠ x from (by exact fresh_a_ne_x))
  have p0015 :=
    @gSylibr (synWa (.classMem A N) (.neg (.classMem X A)))
      (synWrex a N (synWrex x (synCcompl (.cv a))
          (.classEq (synCun A (synCsn X)) (synCun (.cv a) (synCsn (.cv x))))))
      (.classMem (synCun A (synCsn X)) (synCplc N (synC1c))) p0013 p0014
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

/-- Checked nominal proof certificate identified upstream as `g_addcass`. -/
@[expose]
noncomputable def gAddcass (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.classEq (synCplc (synCplc A B) C) (synCplc A (synCplc B C))) :=
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
    @gAncom (.classEq (synCin (.cv a) (.cv c)) (synC0))
      (.classEq (synCin (.cv b) (.cv c)) (synC0))
  have p0001 :=
    @gAnbi2i
      (synWa (.classEq (synCin (.cv a) (.cv c)) (synC0))
        (.classEq (synCin (.cv b) (.cv c)) (synC0)))
      (synWa (.classEq (synCin (.cv b) (.cv c)) (synC0))
        (.classEq (synCin (.cv a) (.cv c)) (synC0)))
      (.classEq (synCin (.cv a) (.cv b)) (synC0)) p0000
  have p0002 :=
    @gAn12 (.classEq (synCin (.cv a) (.cv b)) (synC0))
      (.classEq (synCin (.cv b) (.cv c)) (synC0))
      (.classEq (synCin (.cv a) (.cv c)) (synC0))
  have p0003 :=
    @gBitri
      (synWa (.classEq (synCin (.cv a) (.cv b)) (synC0))
        (synWa (.classEq (synCin (.cv a) (.cv c)) (synC0))
          (.classEq (synCin (.cv b) (.cv c)) (synC0))))
      (synWa (.classEq (synCin (.cv a) (.cv b)) (synC0))
        (synWa (.classEq (synCin (.cv b) (.cv c)) (synC0))
          (.classEq (synCin (.cv a) (.cv c)) (synC0))))
      (synWa (.classEq (synCin (.cv b) (.cv c)) (synC0))
        (synWa (.classEq (synCin (.cv a) (.cv b)) (synC0))
          (.classEq (synCin (.cv a) (.cv c)) (synC0))))
      p0001 p0002
  have p0004 := @gIndir (.cv a) (.cv b) (.cv c)
  have p0005 :=
    @gEqeq1i (synCin (synCun (.cv a) (.cv b)) (.cv c))
      (synCun (synCin (.cv a) (.cv c)) (synCin (.cv b) (.cv c))) (synC0) p0004
  have p0006 := @gUn00 (synCin (.cv a) (.cv c)) (synCin (.cv b) (.cv c))
  have p0007 :=
    @gBitr4i (.classEq (synCin (synCun (.cv a) (.cv b)) (.cv c)) (synC0))
      (.classEq (synCun (synCin (.cv a) (.cv c)) (synCin (.cv b) (.cv c))) (synC0))
      (synWa (.classEq (synCin (.cv a) (.cv c)) (synC0))
        (.classEq (synCin (.cv b) (.cv c)) (synC0)))
      p0005 p0006
  have p0008 :=
    @gAnbi2i (.classEq (synCin (synCun (.cv a) (.cv b)) (.cv c)) (synC0))
      (synWa (.classEq (synCin (.cv a) (.cv c)) (synC0))
        (.classEq (synCin (.cv b) (.cv c)) (synC0)))
      (.classEq (synCin (.cv a) (.cv b)) (synC0)) p0007
  have p0009 := @gIndi (.cv a) (.cv b) (.cv c)
  have p0010 :=
    @gEqeq1i (synCin (.cv a) (synCun (.cv b) (.cv c)))
      (synCun (synCin (.cv a) (.cv b)) (synCin (.cv a) (.cv c))) (synC0) p0009
  have p0011 := @gUn00 (synCin (.cv a) (.cv b)) (synCin (.cv a) (.cv c))
  have p0012 :=
    @gBitr4i (.classEq (synCin (.cv a) (synCun (.cv b) (.cv c))) (synC0))
      (.classEq (synCun (synCin (.cv a) (.cv b)) (synCin (.cv a) (.cv c))) (synC0))
      (synWa (.classEq (synCin (.cv a) (.cv b)) (synC0))
        (.classEq (synCin (.cv a) (.cv c)) (synC0)))
      p0010 p0011
  have p0013 :=
    @gAnbi2i (.classEq (synCin (.cv a) (synCun (.cv b) (.cv c))) (synC0))
      (synWa (.classEq (synCin (.cv a) (.cv b)) (synC0))
        (.classEq (synCin (.cv a) (.cv c)) (synC0)))
      (.classEq (synCin (.cv b) (.cv c)) (synC0)) p0012
  have p0014 :=
    @gN3bitr4i
      (synWa (.classEq (synCin (.cv a) (.cv b)) (synC0))
        (synWa (.classEq (synCin (.cv a) (.cv c)) (synC0))
          (.classEq (synCin (.cv b) (.cv c)) (synC0))))
      (synWa (.classEq (synCin (.cv b) (.cv c)) (synC0))
        (synWa (.classEq (synCin (.cv a) (.cv b)) (synC0))
          (.classEq (synCin (.cv a) (.cv c)) (synC0))))
      (synWa (.classEq (synCin (.cv a) (.cv b)) (synC0))
        (.classEq (synCin (synCun (.cv a) (.cv b)) (.cv c)) (synC0)))
      (synWa (.classEq (synCin (.cv b) (.cv c)) (synC0))
        (.classEq (synCin (.cv a) (synCun (.cv b) (.cv c))) (synC0)))
      p0003 p0008 p0013
  have p0015 := @gUnass (.cv a) (.cv b) (.cv c)
  have p0016 :=
    @gEqeq2i (synCun (synCun (.cv a) (.cv b)) (.cv c))
      (synCun (.cv a) (synCun (.cv b) (.cv c))) (.cv x) p0015
  have p0017 :=
    @gAnbi12i
      (synWa (.classEq (synCin (.cv a) (.cv b)) (synC0))
        (.classEq (synCin (synCun (.cv a) (.cv b)) (.cv c)) (synC0)))
      (synWa (.classEq (synCin (.cv b) (.cv c)) (synC0))
        (.classEq (synCin (.cv a) (synCun (.cv b) (.cv c))) (synC0)))
      (.classEq (.cv x) (synCun (synCun (.cv a) (.cv b)) (.cv c)))
      (.classEq (.cv x) (synCun (.cv a) (synCun (.cv b) (.cv c)))) p0014 p0016
  have p0018 :=
    @gAnass (.classEq (synCin (.cv a) (.cv b)) (synC0))
      (.classEq (synCin (synCun (.cv a) (.cv b)) (.cv c)) (synC0))
      (.classEq (.cv x) (synCun (synCun (.cv a) (.cv b)) (.cv c)))
  have p0019 :=
    @gAnass (.classEq (synCin (.cv b) (.cv c)) (synC0))
      (.classEq (synCin (.cv a) (synCun (.cv b) (.cv c))) (synC0))
      (.classEq (.cv x) (synCun (.cv a) (synCun (.cv b) (.cv c))))
  have p0020 :=
    @gN3bitr3i
      (synWa (synWa (.classEq (synCin (.cv a) (.cv b)) (synC0))
          (.classEq (synCin (synCun (.cv a) (.cv b)) (.cv c)) (synC0)))
        (.classEq (.cv x) (synCun (synCun (.cv a) (.cv b)) (.cv c))))
      (synWa (synWa (.classEq (synCin (.cv b) (.cv c)) (synC0))
          (.classEq (synCin (.cv a) (synCun (.cv b) (.cv c))) (synC0)))
        (.classEq (.cv x) (synCun (.cv a) (synCun (.cv b) (.cv c)))))
      (synWa (.classEq (synCin (.cv a) (.cv b)) (synC0))
        (synWa (.classEq (synCin (synCun (.cv a) (.cv b)) (.cv c)) (synC0))
          (.classEq (.cv x) (synCun (synCun (.cv a) (.cv b)) (.cv c)))))
      (synWa (.classEq (synCin (.cv b) (.cv c)) (synC0))
        (synWa (.classEq (synCin (.cv a) (synCun (.cv b) (.cv c))) (synC0))
          (.classEq (.cv x) (synCun (.cv a) (synCun (.cv b) (.cv c))))))
      p0017 p0018 p0019
  have p0021 :=
    @gAnass (.classEq (synCin (.cv a) (.cv b)) (synC0))
      (.classEq (.cv d) (synCun (.cv a) (.cv b)))
      (synWa (.classEq (synCin (.cv d) (.cv c)) (synC0))
        (.classEq (.cv x) (synCun (.cv d) (.cv c))))
  have p0022 :=
    @gAn12 (.classEq (synCin (.cv a) (.cv b)) (synC0))
      (.classEq (.cv d) (synCun (.cv a) (.cv b)))
      (synWa (.classEq (synCin (.cv d) (.cv c)) (synC0))
        (.classEq (.cv x) (synCun (.cv d) (.cv c))))
  have p0023 :=
    @gBitri
      (synWa (synWa (.classEq (synCin (.cv a) (.cv b)) (synC0))
          (.classEq (.cv d) (synCun (.cv a) (.cv b))))
        (synWa (.classEq (synCin (.cv d) (.cv c)) (synC0))
          (.classEq (.cv x) (synCun (.cv d) (.cv c)))))
      (synWa (.classEq (synCin (.cv a) (.cv b)) (synC0))
        (synWa (.classEq (.cv d) (synCun (.cv a) (.cv b)))
          (synWa (.classEq (synCin (.cv d) (.cv c)) (synC0))
            (.classEq (.cv x) (synCun (.cv d) (.cv c))))))
      (synWa (.classEq (.cv d) (synCun (.cv a) (.cv b)))
        (synWa (.classEq (synCin (.cv a) (.cv b)) (synC0))
          (synWa (.classEq (synCin (.cv d) (.cv c)) (synC0))
            (.classEq (.cv x) (synCun (.cv d) (.cv c))))))
      p0021 p0022
  have p0024 :=
    @gExbii
      (synWa (synWa (.classEq (synCin (.cv a) (.cv b)) (synC0))
          (.classEq (.cv d) (synCun (.cv a) (.cv b))))
        (synWa (.classEq (synCin (.cv d) (.cv c)) (synC0))
          (.classEq (.cv x) (synCun (.cv d) (.cv c)))))
      (synWa (.classEq (.cv d) (synCun (.cv a) (.cv b)))
        (synWa (.classEq (synCin (.cv a) (.cv b)) (synC0))
          (synWa (.classEq (synCin (.cv d) (.cv c)) (synC0))
            (.classEq (.cv x) (synCun (.cv d) (.cv c))))))
      d p0023
  have p0025 := @gVex a
  have p0026 := @gVex b
  have p0027 := @gUnex (.cv a) (.cv b) p0025 p0026
  have p0028 := @gIneq1 (.cv d) (synCun (.cv a) (.cv b)) (.cv c)
  have p0029 :=
    @gEqeq1d (.classEq (.cv d) (synCun (.cv a) (.cv b))) (synCin (.cv d) (.cv c))
      (synCin (synCun (.cv a) (.cv b)) (.cv c)) (synC0) p0028
  have p0030 := @gUneq1 (.cv d) (synCun (.cv a) (.cv b)) (.cv c)
  have p0031 :=
    @gEqeq2d (.classEq (.cv d) (synCun (.cv a) (.cv b))) (synCun (.cv d) (.cv c))
      (synCun (synCun (.cv a) (.cv b)) (.cv c)) (.cv x) p0030
  have p0032 :=
    @gAnbi12d (.classEq (.cv d) (synCun (.cv a) (.cv b)))
      (.classEq (synCin (.cv d) (.cv c)) (synC0))
      (.classEq (synCin (synCun (.cv a) (.cv b)) (.cv c)) (synC0))
      (.classEq (.cv x) (synCun (.cv d) (.cv c)))
      (.classEq (.cv x) (synCun (synCun (.cv a) (.cv b)) (.cv c))) p0029 p0031
  have p0033 :=
    @gAnbi2d (.classEq (.cv d) (synCun (.cv a) (.cv b)))
      (synWa (.classEq (synCin (.cv d) (.cv c)) (synC0))
        (.classEq (.cv x) (synCun (.cv d) (.cv c))))
      (synWa (.classEq (synCin (synCun (.cv a) (.cv b)) (.cv c)) (synC0))
        (.classEq (.cv x) (synCun (synCun (.cv a) (.cv b)) (.cv c))))
      (.classEq (synCin (.cv a) (.cv b)) (synC0)) p0032
  have freeVariableCertificate0 : d ∉ ((synCun (.cv a) (.cv b))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      fresh_d_ne_a, fresh_d_ne_b, or_false, not_false_eq_true]
  have freeVariableCertificate1 :
    d ∉
      ((synWa (.classEq (synCin (.cv a) (.cv b)) (synC0))
          (synWa (.classEq (synCin (synCun (.cv a) (.cv b)) (.cv c)) (synC0))
            (.classEq (.cv x) (synCun (synCun (.cv a) (.cv b)) (.cv c)))))).fv :=
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
    @gCeqsexv
      (synWa (.classEq (synCin (.cv a) (.cv b)) (synC0))
        (synWa (.classEq (synCin (.cv d) (.cv c)) (synC0))
          (.classEq (.cv x) (synCun (.cv d) (.cv c)))))
      (synWa (.classEq (synCin (.cv a) (.cv b)) (synC0))
        (synWa (.classEq (synCin (synCun (.cv a) (.cv b)) (.cv c)) (synC0))
          (.classEq (.cv x) (synCun (synCun (.cv a) (.cv b)) (.cv c)))))
      d (synCun (.cv a) (.cv b)) freeVariableCertificate0 freeVariableCertificate1 p0027
      p0033
  have p0035 :=
    @gBitri
      (synWex d (synWa (synWa (.classEq (synCin (.cv a) (.cv b)) (synC0))
            (.classEq (.cv d) (synCun (.cv a) (.cv b))))
          (synWa (.classEq (synCin (.cv d) (.cv c)) (synC0))
            (.classEq (.cv x) (synCun (.cv d) (.cv c))))))
      (synWex d (synWa (.classEq (.cv d) (synCun (.cv a) (.cv b)))
          (synWa (.classEq (synCin (.cv a) (.cv b)) (synC0))
            (synWa (.classEq (synCin (.cv d) (.cv c)) (synC0))
              (.classEq (.cv x) (synCun (.cv d) (.cv c)))))))
      (synWa (.classEq (synCin (.cv a) (.cv b)) (synC0))
        (synWa (.classEq (synCin (synCun (.cv a) (.cv b)) (.cv c)) (synC0))
          (.classEq (.cv x) (synCun (synCun (.cv a) (.cv b)) (.cv c)))))
      p0024 p0034
  have p0036 :=
    @gAnass (.classEq (synCin (.cv b) (.cv c)) (synC0))
      (.classEq (.cv e) (synCun (.cv b) (.cv c)))
      (synWa (.classEq (synCin (.cv a) (.cv e)) (synC0))
        (.classEq (.cv x) (synCun (.cv a) (.cv e))))
  have p0037 :=
    @gAn12 (.classEq (synCin (.cv b) (.cv c)) (synC0))
      (.classEq (.cv e) (synCun (.cv b) (.cv c)))
      (synWa (.classEq (synCin (.cv a) (.cv e)) (synC0))
        (.classEq (.cv x) (synCun (.cv a) (.cv e))))
  have p0038 :=
    @gBitri
      (synWa (synWa (.classEq (synCin (.cv b) (.cv c)) (synC0))
          (.classEq (.cv e) (synCun (.cv b) (.cv c))))
        (synWa (.classEq (synCin (.cv a) (.cv e)) (synC0))
          (.classEq (.cv x) (synCun (.cv a) (.cv e)))))
      (synWa (.classEq (synCin (.cv b) (.cv c)) (synC0))
        (synWa (.classEq (.cv e) (synCun (.cv b) (.cv c)))
          (synWa (.classEq (synCin (.cv a) (.cv e)) (synC0))
            (.classEq (.cv x) (synCun (.cv a) (.cv e))))))
      (synWa (.classEq (.cv e) (synCun (.cv b) (.cv c)))
        (synWa (.classEq (synCin (.cv b) (.cv c)) (synC0))
          (synWa (.classEq (synCin (.cv a) (.cv e)) (synC0))
            (.classEq (.cv x) (synCun (.cv a) (.cv e))))))
      p0036 p0037
  have p0039 :=
    @gExbii
      (synWa (synWa (.classEq (synCin (.cv b) (.cv c)) (synC0))
          (.classEq (.cv e) (synCun (.cv b) (.cv c))))
        (synWa (.classEq (synCin (.cv a) (.cv e)) (synC0))
          (.classEq (.cv x) (synCun (.cv a) (.cv e)))))
      (synWa (.classEq (.cv e) (synCun (.cv b) (.cv c)))
        (synWa (.classEq (synCin (.cv b) (.cv c)) (synC0))
          (synWa (.classEq (synCin (.cv a) (.cv e)) (synC0))
            (.classEq (.cv x) (synCun (.cv a) (.cv e))))))
      e p0038
  have p0040 := @gVex c
  have p0041 := @gUnex (.cv b) (.cv c) p0026 p0040
  have p0042 := @gIneq2 (.cv e) (synCun (.cv b) (.cv c)) (.cv a)
  have p0043 :=
    @gEqeq1d (.classEq (.cv e) (synCun (.cv b) (.cv c))) (synCin (.cv a) (.cv e))
      (synCin (.cv a) (synCun (.cv b) (.cv c))) (synC0) p0042
  have p0044 := @gUneq2 (.cv e) (synCun (.cv b) (.cv c)) (.cv a)
  have p0045 :=
    @gEqeq2d (.classEq (.cv e) (synCun (.cv b) (.cv c))) (synCun (.cv a) (.cv e))
      (synCun (.cv a) (synCun (.cv b) (.cv c))) (.cv x) p0044
  have p0046 :=
    @gAnbi12d (.classEq (.cv e) (synCun (.cv b) (.cv c)))
      (.classEq (synCin (.cv a) (.cv e)) (synC0))
      (.classEq (synCin (.cv a) (synCun (.cv b) (.cv c))) (synC0))
      (.classEq (.cv x) (synCun (.cv a) (.cv e)))
      (.classEq (.cv x) (synCun (.cv a) (synCun (.cv b) (.cv c)))) p0043 p0045
  have p0047 :=
    @gAnbi2d (.classEq (.cv e) (synCun (.cv b) (.cv c)))
      (synWa (.classEq (synCin (.cv a) (.cv e)) (synC0))
        (.classEq (.cv x) (synCun (.cv a) (.cv e))))
      (synWa (.classEq (synCin (.cv a) (synCun (.cv b) (.cv c))) (synC0))
        (.classEq (.cv x) (synCun (.cv a) (synCun (.cv b) (.cv c)))))
      (.classEq (synCin (.cv b) (.cv c)) (synC0)) p0046
  have freeVariableCertificate2 : e ∉ ((synCun (.cv b) (.cv c))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      fresh_e_ne_b, fresh_e_ne_c, or_false, not_false_eq_true]
  have freeVariableCertificate3 :
    e ∉
      ((synWa (.classEq (synCin (.cv b) (.cv c)) (synC0))
          (synWa (.classEq (synCin (.cv a) (synCun (.cv b) (.cv c))) (synC0))
            (.classEq (.cv x) (synCun (.cv a) (synCun (.cv b) (.cv c))))))).fv :=
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
    @gCeqsexv
      (synWa (.classEq (synCin (.cv b) (.cv c)) (synC0))
        (synWa (.classEq (synCin (.cv a) (.cv e)) (synC0))
          (.classEq (.cv x) (synCun (.cv a) (.cv e)))))
      (synWa (.classEq (synCin (.cv b) (.cv c)) (synC0))
        (synWa (.classEq (synCin (.cv a) (synCun (.cv b) (.cv c))) (synC0))
          (.classEq (.cv x) (synCun (.cv a) (synCun (.cv b) (.cv c))))))
      e (synCun (.cv b) (.cv c)) freeVariableCertificate2 freeVariableCertificate3 p0041
      p0047
  have p0049 :=
    @gBitri
      (synWex e (synWa (synWa (.classEq (synCin (.cv b) (.cv c)) (synC0))
            (.classEq (.cv e) (synCun (.cv b) (.cv c))))
          (synWa (.classEq (synCin (.cv a) (.cv e)) (synC0))
            (.classEq (.cv x) (synCun (.cv a) (.cv e))))))
      (synWex e (synWa (.classEq (.cv e) (synCun (.cv b) (.cv c)))
          (synWa (.classEq (synCin (.cv b) (.cv c)) (synC0))
            (synWa (.classEq (synCin (.cv a) (.cv e)) (synC0))
              (.classEq (.cv x) (synCun (.cv a) (.cv e)))))))
      (synWa (.classEq (synCin (.cv b) (.cv c)) (synC0))
        (synWa (.classEq (synCin (.cv a) (synCun (.cv b) (.cv c))) (synC0))
          (.classEq (.cv x) (synCun (.cv a) (synCun (.cv b) (.cv c))))))
      p0039 p0048
  have p0050 :=
    @gN3bitr4i
      (synWa (.classEq (synCin (.cv a) (.cv b)) (synC0))
        (synWa (.classEq (synCin (synCun (.cv a) (.cv b)) (.cv c)) (synC0))
          (.classEq (.cv x) (synCun (synCun (.cv a) (.cv b)) (.cv c)))))
      (synWa (.classEq (synCin (.cv b) (.cv c)) (synC0))
        (synWa (.classEq (synCin (.cv a) (synCun (.cv b) (.cv c))) (synC0))
          (.classEq (.cv x) (synCun (.cv a) (synCun (.cv b) (.cv c))))))
      (synWex d (synWa (synWa (.classEq (synCin (.cv a) (.cv b)) (synC0))
            (.classEq (.cv d) (synCun (.cv a) (.cv b))))
          (synWa (.classEq (synCin (.cv d) (.cv c)) (synC0))
            (.classEq (.cv x) (synCun (.cv d) (.cv c))))))
      (synWex e (synWa (synWa (.classEq (synCin (.cv b) (.cv c)) (synC0))
            (.classEq (.cv e) (synCun (.cv b) (.cv c))))
          (synWa (.classEq (synCin (.cv a) (.cv e)) (synC0))
            (.classEq (.cv x) (synCun (.cv a) (.cv e))))))
      p0020 p0035 p0049
  have p0051 :=
    @gRexbii
      (synWex d (synWa (synWa (.classEq (synCin (.cv a) (.cv b)) (synC0))
            (.classEq (.cv d) (synCun (.cv a) (.cv b))))
          (synWa (.classEq (synCin (.cv d) (.cv c)) (synC0))
            (.classEq (.cv x) (synCun (.cv d) (.cv c))))))
      (synWex e (synWa (synWa (.classEq (synCin (.cv b) (.cv c)) (synC0))
            (.classEq (.cv e) (synCun (.cv b) (.cv c))))
          (synWa (.classEq (synCin (.cv a) (.cv e)) (synC0))
            (.classEq (.cv x) (synCun (.cv a) (.cv e))))))
      c C p0050
  have p0052 :=
    @gN2rexbii
      (synWrex c C (synWex d (synWa (synWa (.classEq (synCin (.cv a) (.cv b)) (synC0))
              (.classEq (.cv d) (synCun (.cv a) (.cv b))))
            (synWa (.classEq (synCin (.cv d) (.cv c)) (synC0))
              (.classEq (.cv x) (synCun (.cv d) (.cv c)))))))
      (synWrex c C (synWex e (synWa (synWa (.classEq (synCin (.cv b) (.cv c)) (synC0))
              (.classEq (.cv e) (synCun (.cv b) (.cv c))))
            (synWa (.classEq (synCin (.cv a) (.cv e)) (synC0))
              (.classEq (.cv x) (synCun (.cv a) (.cv e)))))))
      a b A B p0051
  have freeVariableCertificate4 : d ∉ ((Class.cv x)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_d_ne_x, not_false_eq_true]
  have freeVariableCertificate5 : c ∉ ((Class.cv x)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_c_ne_x, not_false_eq_true]
  have freeVariableCertificate6 : d ∉ ((synCplc A B)).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, Finset.mem_union,
      fresh_d_not_A, fresh_d_not_B, or_false, not_false_eq_true]
  have freeVariableCertificate7 : c ∉ ((synCplc A B)).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, Finset.mem_union,
      fresh_c_not_A, fresh_c_not_B, or_false, not_false_eq_true]
  have p0053 :=
    @gEladdc (.cv x) (synCplc A B) C d c freeVariableCertificate4
      freeVariableCertificate5 freeVariableCertificate6 freeVariableCertificate7
      (by exact (show d ∉ (C).fv from (by exact fresh_d_not_C)))
      (by exact (show c ∉ (C).fv from (by exact fresh_c_not_C)))
      (show d ≠ c from (by exact fresh_d_ne_c))
  have p0054 :=
    (Nominal.biimpRefl (synWrex d (synCplc A B) (synWrex c C
          (synWa (.classEq (synCin (.cv d) (.cv c)) (synC0))
            (.classEq (.cv x) (synCun (.cv d) (.cv c)))))))
  have p0055 :=
    @gRexcom4
      (synWrex b B (synWa (synWa (.classEq (synCin (.cv a) (.cv b)) (synC0))
            (.classEq (.cv d) (synCun (.cv a) (.cv b)))) (synWrex c C
            (synWa (.classEq (synCin (.cv d) (.cv c)) (synC0))
              (.classEq (.cv x) (synCun (.cv d) (.cv c)))))))
      a d A (by exact (show d ∉ (A).fv from (by exact fresh_d_not_A)))
      (show a ≠ d from (by exact fresh_a_ne_d))
  have p0056 :=
    @gRexcom4
      (synWa (synWa (.classEq (synCin (.cv a) (.cv b)) (synC0))
          (.classEq (.cv d) (synCun (.cv a) (.cv b))))
        (synWa (.classEq (synCin (.cv d) (.cv c)) (synC0))
          (.classEq (.cv x) (synCun (.cv d) (.cv c)))))
      c d C (by exact (show d ∉ (C).fv from (by exact fresh_d_not_C)))
      (show c ≠ d from (by exact fresh_c_ne_d))
  have freeVariableCertificate8 :
    c ∉
      ((synWa (.classEq (synCin (.cv a) (.cv b)) (synC0))
          (.classEq (.cv d) (synCun (.cv a) (.cv b))))).fv :=
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
    @gR1942v
      (synWa (.classEq (synCin (.cv a) (.cv b)) (synC0))
        (.classEq (.cv d) (synCun (.cv a) (.cv b))))
      (synWa (.classEq (synCin (.cv d) (.cv c)) (synC0))
        (.classEq (.cv x) (synCun (.cv d) (.cv c))))
      c C freeVariableCertificate8
  have p0058 :=
    @gExbii
      (synWrex c C (synWa (synWa (.classEq (synCin (.cv a) (.cv b)) (synC0))
            (.classEq (.cv d) (synCun (.cv a) (.cv b))))
          (synWa (.classEq (synCin (.cv d) (.cv c)) (synC0))
            (.classEq (.cv x) (synCun (.cv d) (.cv c))))))
      (synWa (synWa (.classEq (synCin (.cv a) (.cv b)) (synC0))
          (.classEq (.cv d) (synCun (.cv a) (.cv b)))) (synWrex c C
          (synWa (.classEq (synCin (.cv d) (.cv c)) (synC0))
            (.classEq (.cv x) (synCun (.cv d) (.cv c))))))
      d p0057
  have p0059 :=
    @gBitri
      (synWrex c C (synWex d (synWa (synWa (.classEq (synCin (.cv a) (.cv b)) (synC0))
              (.classEq (.cv d) (synCun (.cv a) (.cv b))))
            (synWa (.classEq (synCin (.cv d) (.cv c)) (synC0))
              (.classEq (.cv x) (synCun (.cv d) (.cv c)))))))
      (synWex d (synWrex c C (synWa (synWa (.classEq (synCin (.cv a) (.cv b)) (synC0))
              (.classEq (.cv d) (synCun (.cv a) (.cv b))))
            (synWa (.classEq (synCin (.cv d) (.cv c)) (synC0))
              (.classEq (.cv x) (synCun (.cv d) (.cv c)))))))
      (synWex d (synWa (synWa (.classEq (synCin (.cv a) (.cv b)) (synC0))
            (.classEq (.cv d) (synCun (.cv a) (.cv b)))) (synWrex c C
            (synWa (.classEq (synCin (.cv d) (.cv c)) (synC0))
              (.classEq (.cv x) (synCun (.cv d) (.cv c)))))))
      p0056 p0058
  have p0060 :=
    @gRexbii
      (synWrex c C (synWex d (synWa (synWa (.classEq (synCin (.cv a) (.cv b)) (synC0))
              (.classEq (.cv d) (synCun (.cv a) (.cv b))))
            (synWa (.classEq (synCin (.cv d) (.cv c)) (synC0))
              (.classEq (.cv x) (synCun (.cv d) (.cv c)))))))
      (synWex d (synWa (synWa (.classEq (synCin (.cv a) (.cv b)) (synC0))
            (.classEq (.cv d) (synCun (.cv a) (.cv b)))) (synWrex c C
            (synWa (.classEq (synCin (.cv d) (.cv c)) (synC0))
              (.classEq (.cv x) (synCun (.cv d) (.cv c)))))))
      b B p0059
  have p0061 :=
    @gRexcom4
      (synWa (synWa (.classEq (synCin (.cv a) (.cv b)) (synC0))
          (.classEq (.cv d) (synCun (.cv a) (.cv b)))) (synWrex c C
          (synWa (.classEq (synCin (.cv d) (.cv c)) (synC0))
            (.classEq (.cv x) (synCun (.cv d) (.cv c))))))
      b d B (by exact (show d ∉ (B).fv from (by exact fresh_d_not_B)))
      (show b ≠ d from (by exact fresh_b_ne_d))
  have p0062 :=
    @gBitri
      (synWrex b B (synWrex c C (synWex d (synWa
              (synWa (.classEq (synCin (.cv a) (.cv b)) (synC0))
                (.classEq (.cv d) (synCun (.cv a) (.cv b))))
              (synWa (.classEq (synCin (.cv d) (.cv c)) (synC0))
                (.classEq (.cv x) (synCun (.cv d) (.cv c))))))))
      (synWrex b B (synWex d (synWa (synWa (.classEq (synCin (.cv a) (.cv b)) (synC0))
              (.classEq (.cv d) (synCun (.cv a) (.cv b)))) (synWrex c C
              (synWa (.classEq (synCin (.cv d) (.cv c)) (synC0))
                (.classEq (.cv x) (synCun (.cv d) (.cv c))))))))
      (synWex d (synWrex b B (synWa (synWa (.classEq (synCin (.cv a) (.cv b)) (synC0))
              (.classEq (.cv d) (synCun (.cv a) (.cv b)))) (synWrex c C
              (synWa (.classEq (synCin (.cv d) (.cv c)) (synC0))
                (.classEq (.cv x) (synCun (.cv d) (.cv c))))))))
      p0060 p0061
  have p0063 :=
    @gRexbii
      (synWrex b B (synWrex c C (synWex d (synWa
              (synWa (.classEq (synCin (.cv a) (.cv b)) (synC0))
                (.classEq (.cv d) (synCun (.cv a) (.cv b))))
              (synWa (.classEq (synCin (.cv d) (.cv c)) (synC0))
                (.classEq (.cv x) (synCun (.cv d) (.cv c))))))))
      (synWex d (synWrex b B (synWa (synWa (.classEq (synCin (.cv a) (.cv b)) (synC0))
              (.classEq (.cv d) (synCun (.cv a) (.cv b)))) (synWrex c C
              (synWa (.classEq (synCin (.cv d) (.cv c)) (synC0))
                (.classEq (.cv x) (synCun (.cv d) (.cv c))))))))
      a A p0062
  have freeVariableCertificate9 :
    a ∉
      ((synWrex c C (synWa (.classEq (synCin (.cv d) (.cv c)) (synC0))
            (.classEq (.cv x) (synCun (.cv d) (.cv c)))))).fv :=
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
    @gR1941v
      (synWrex b B (synWa (.classEq (synCin (.cv a) (.cv b)) (synC0))
          (.classEq (.cv d) (synCun (.cv a) (.cv b)))))
      (synWrex c C (synWa (.classEq (synCin (.cv d) (.cv c)) (synC0))
          (.classEq (.cv x) (synCun (.cv d) (.cv c)))))
      a A freeVariableCertificate9
  have freeVariableCertificate10 :
    b ∉
      ((synWrex c C (synWa (.classEq (synCin (.cv d) (.cv c)) (synC0))
            (.classEq (.cv x) (synCun (.cv d) (.cv c)))))).fv :=
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
    @gR1941v
      (synWa (.classEq (synCin (.cv a) (.cv b)) (synC0))
        (.classEq (.cv d) (synCun (.cv a) (.cv b))))
      (synWrex c C (synWa (.classEq (synCin (.cv d) (.cv c)) (synC0))
          (.classEq (.cv x) (synCun (.cv d) (.cv c)))))
      b B freeVariableCertificate10
  have p0066 :=
    @gRexbii
      (synWrex b B (synWa (synWa (.classEq (synCin (.cv a) (.cv b)) (synC0))
            (.classEq (.cv d) (synCun (.cv a) (.cv b)))) (synWrex c C
            (synWa (.classEq (synCin (.cv d) (.cv c)) (synC0))
              (.classEq (.cv x) (synCun (.cv d) (.cv c)))))))
      (synWa (synWrex b B (synWa (.classEq (synCin (.cv a) (.cv b)) (synC0))
            (.classEq (.cv d) (synCun (.cv a) (.cv b))))) (synWrex c C
          (synWa (.classEq (synCin (.cv d) (.cv c)) (synC0))
            (.classEq (.cv x) (synCun (.cv d) (.cv c))))))
      a A p0065
  have freeVariableCertificate11 : a ∉ ((Class.cv d)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_a_ne_d, not_false_eq_true]
  have freeVariableCertificate12 : b ∉ ((Class.cv d)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_b_ne_d, not_false_eq_true]
  have p0067 :=
    @gEladdc (.cv d) A B a b freeVariableCertificate11 freeVariableCertificate12
      (by exact (show a ∉ (A).fv from (by exact fresh_a_not_A)))
      (by exact (show b ∉ (A).fv from (by exact fresh_b_not_A)))
      (by exact (show a ∉ (B).fv from (by exact fresh_a_not_B)))
      (by exact (show b ∉ (B).fv from (by exact fresh_b_not_B)))
      (show a ≠ b from (by exact fresh_a_ne_b))
  have p0068 :=
    @gAnbi1i (.classMem (.cv d) (synCplc A B))
      (synWrex a A (synWrex b B (synWa (.classEq (synCin (.cv a) (.cv b)) (synC0))
            (.classEq (.cv d) (synCun (.cv a) (.cv b))))))
      (synWrex c C (synWa (.classEq (synCin (.cv d) (.cv c)) (synC0))
          (.classEq (.cv x) (synCun (.cv d) (.cv c)))))
      p0067
  have p0069 :=
    @gN3bitr4ri
      (synWrex a A (synWa (synWrex b B (synWa (.classEq (synCin (.cv a) (.cv b)) (synC0))
              (.classEq (.cv d) (synCun (.cv a) (.cv b))))) (synWrex c C
            (synWa (.classEq (synCin (.cv d) (.cv c)) (synC0))
              (.classEq (.cv x) (synCun (.cv d) (.cv c)))))))
      (synWa (synWrex a A (synWrex b B (synWa (.classEq (synCin (.cv a) (.cv b)) (synC0))
              (.classEq (.cv d) (synCun (.cv a) (.cv b)))))) (synWrex c C
          (synWa (.classEq (synCin (.cv d) (.cv c)) (synC0))
            (.classEq (.cv x) (synCun (.cv d) (.cv c))))))
      (synWrex a A (synWrex b B (synWa (synWa (.classEq (synCin (.cv a) (.cv b)) (synC0))
              (.classEq (.cv d) (synCun (.cv a) (.cv b)))) (synWrex c C
              (synWa (.classEq (synCin (.cv d) (.cv c)) (synC0))
                (.classEq (.cv x) (synCun (.cv d) (.cv c))))))))
      (synWa (.classMem (.cv d) (synCplc A B)) (synWrex c C
          (synWa (.classEq (synCin (.cv d) (.cv c)) (synC0))
            (.classEq (.cv x) (synCun (.cv d) (.cv c))))))
      p0064 p0066 p0068
  have p0070 :=
    @gExbii
      (synWa (.classMem (.cv d) (synCplc A B)) (synWrex c C
          (synWa (.classEq (synCin (.cv d) (.cv c)) (synC0))
            (.classEq (.cv x) (synCun (.cv d) (.cv c))))))
      (synWrex a A (synWrex b B (synWa (synWa (.classEq (synCin (.cv a) (.cv b)) (synC0))
              (.classEq (.cv d) (synCun (.cv a) (.cv b)))) (synWrex c C
              (synWa (.classEq (synCin (.cv d) (.cv c)) (synC0))
                (.classEq (.cv x) (synCun (.cv d) (.cv c))))))))
      d p0069
  have p0071 :=
    @gN3bitr4ri
      (synWrex a A (synWex d (synWrex b B (synWa
              (synWa (.classEq (synCin (.cv a) (.cv b)) (synC0))
                (.classEq (.cv d) (synCun (.cv a) (.cv b)))) (synWrex c C
                (synWa (.classEq (synCin (.cv d) (.cv c)) (synC0))
                  (.classEq (.cv x) (synCun (.cv d) (.cv c)))))))))
      (synWex d (synWrex a A (synWrex b B (synWa
              (synWa (.classEq (synCin (.cv a) (.cv b)) (synC0))
                (.classEq (.cv d) (synCun (.cv a) (.cv b)))) (synWrex c C
                (synWa (.classEq (synCin (.cv d) (.cv c)) (synC0))
                  (.classEq (.cv x) (synCun (.cv d) (.cv c)))))))))
      (synWrex a A (synWrex b B (synWrex c C (synWex d (synWa
                (synWa (.classEq (synCin (.cv a) (.cv b)) (synC0))
                  (.classEq (.cv d) (synCun (.cv a) (.cv b))))
                (synWa (.classEq (synCin (.cv d) (.cv c)) (synC0))
                  (.classEq (.cv x) (synCun (.cv d) (.cv c)))))))))
      (synWex d (synWa (.classMem (.cv d) (synCplc A B)) (synWrex c C
            (synWa (.classEq (synCin (.cv d) (.cv c)) (synC0))
              (.classEq (.cv x) (synCun (.cv d) (.cv c)))))))
      p0055 p0063 p0070
  have p0072 :=
    @gBitri
      (synWrex d (synCplc A B) (synWrex c C
          (synWa (.classEq (synCin (.cv d) (.cv c)) (synC0))
            (.classEq (.cv x) (synCun (.cv d) (.cv c))))))
      (synWex d (synWa (.classMem (.cv d) (synCplc A B)) (synWrex c C
            (synWa (.classEq (synCin (.cv d) (.cv c)) (synC0))
              (.classEq (.cv x) (synCun (.cv d) (.cv c)))))))
      (synWrex a A (synWrex b B (synWrex c C (synWex d (synWa
                (synWa (.classEq (synCin (.cv a) (.cv b)) (synC0))
                  (.classEq (.cv d) (synCun (.cv a) (.cv b))))
                (synWa (.classEq (synCin (.cv d) (.cv c)) (synC0))
                  (.classEq (.cv x) (synCun (.cv d) (.cv c)))))))))
      p0054 p0071
  have p0073 :=
    @gBitri (.classMem (.cv x) (synCplc (synCplc A B) C))
      (synWrex d (synCplc A B) (synWrex c C
          (synWa (.classEq (synCin (.cv d) (.cv c)) (synC0))
            (.classEq (.cv x) (synCun (.cv d) (.cv c))))))
      (synWrex a A (synWrex b B (synWrex c C (synWex d (synWa
                (synWa (.classEq (synCin (.cv a) (.cv b)) (synC0))
                  (.classEq (.cv d) (synCun (.cv a) (.cv b))))
                (synWa (.classEq (synCin (.cv d) (.cv c)) (synC0))
                  (.classEq (.cv x) (synCun (.cv d) (.cv c)))))))))
      p0053 p0072
  have freeVariableCertificate13 : a ∉ ((Class.cv x)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_a_ne_x, not_false_eq_true]
  have freeVariableCertificate14 : e ∉ ((Class.cv x)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_e_ne_x, not_false_eq_true]
  have freeVariableCertificate15 : a ∉ ((synCplc B C)).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, Finset.mem_union,
      fresh_a_not_B, fresh_a_not_C, or_false, not_false_eq_true]
  have freeVariableCertificate16 : e ∉ ((synCplc B C)).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, Finset.mem_union,
      fresh_e_not_B, fresh_e_not_C, or_false, not_false_eq_true]
  have p0074 :=
    @gEladdc (.cv x) A (synCplc B C) a e freeVariableCertificate13
      freeVariableCertificate14 (by exact (show a ∉ (A).fv from (by exact fresh_a_not_A)))
      (by exact (show e ∉ (A).fv from (by exact fresh_e_not_A))) freeVariableCertificate15
      freeVariableCertificate16 (show a ≠ e from (by exact fresh_a_ne_e))
  have p0075 :=
    (Nominal.biimpRefl (synWrex e (synCplc B C)
        (synWa (.classEq (synCin (.cv a) (.cv e)) (synC0))
          (.classEq (.cv x) (synCun (.cv a) (.cv e))))))
  have p0076 :=
    @gRexcom4
      (synWrex c C (synWa (synWa (.classEq (synCin (.cv b) (.cv c)) (synC0))
            (.classEq (.cv e) (synCun (.cv b) (.cv c))))
          (synWa (.classEq (synCin (.cv a) (.cv e)) (synC0))
            (.classEq (.cv x) (synCun (.cv a) (.cv e))))))
      b e B (by exact (show e ∉ (B).fv from (by exact fresh_e_not_B)))
      (show b ≠ e from (by exact fresh_b_ne_e))
  have p0077 :=
    @gRexcom4
      (synWa (synWa (.classEq (synCin (.cv b) (.cv c)) (synC0))
          (.classEq (.cv e) (synCun (.cv b) (.cv c))))
        (synWa (.classEq (synCin (.cv a) (.cv e)) (synC0))
          (.classEq (.cv x) (synCun (.cv a) (.cv e)))))
      c e C (by exact (show e ∉ (C).fv from (by exact fresh_e_not_C)))
      (show c ≠ e from (by exact fresh_c_ne_e))
  have p0078 :=
    @gRexbii
      (synWrex c C (synWex e (synWa (synWa (.classEq (synCin (.cv b) (.cv c)) (synC0))
              (.classEq (.cv e) (synCun (.cv b) (.cv c))))
            (synWa (.classEq (synCin (.cv a) (.cv e)) (synC0))
              (.classEq (.cv x) (synCun (.cv a) (.cv e)))))))
      (synWex e (synWrex c C (synWa (synWa (.classEq (synCin (.cv b) (.cv c)) (synC0))
              (.classEq (.cv e) (synCun (.cv b) (.cv c))))
            (synWa (.classEq (synCin (.cv a) (.cv e)) (synC0))
              (.classEq (.cv x) (synCun (.cv a) (.cv e)))))))
      b B p0077
  have freeVariableCertificate17 :
    b ∉
      ((synWa (.classEq (synCin (.cv a) (.cv e)) (synC0))
          (.classEq (.cv x) (synCun (.cv a) (.cv e))))).fv :=
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
    @gR1941v
      (synWrex c C (synWa (.classEq (synCin (.cv b) (.cv c)) (synC0))
          (.classEq (.cv e) (synCun (.cv b) (.cv c)))))
      (synWa (.classEq (synCin (.cv a) (.cv e)) (synC0))
        (.classEq (.cv x) (synCun (.cv a) (.cv e))))
      b B freeVariableCertificate17
  have freeVariableCertificate18 :
    c ∉
      ((synWa (.classEq (synCin (.cv a) (.cv e)) (synC0))
          (.classEq (.cv x) (synCun (.cv a) (.cv e))))).fv :=
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
    @gR1941v
      (synWa (.classEq (synCin (.cv b) (.cv c)) (synC0))
        (.classEq (.cv e) (synCun (.cv b) (.cv c))))
      (synWa (.classEq (synCin (.cv a) (.cv e)) (synC0))
        (.classEq (.cv x) (synCun (.cv a) (.cv e))))
      c C freeVariableCertificate18
  have p0081 :=
    @gRexbii
      (synWrex c C (synWa (synWa (.classEq (synCin (.cv b) (.cv c)) (synC0))
            (.classEq (.cv e) (synCun (.cv b) (.cv c))))
          (synWa (.classEq (synCin (.cv a) (.cv e)) (synC0))
            (.classEq (.cv x) (synCun (.cv a) (.cv e))))))
      (synWa (synWrex c C (synWa (.classEq (synCin (.cv b) (.cv c)) (synC0))
            (.classEq (.cv e) (synCun (.cv b) (.cv c)))))
        (synWa (.classEq (synCin (.cv a) (.cv e)) (synC0))
          (.classEq (.cv x) (synCun (.cv a) (.cv e)))))
      b B p0080
  have freeVariableCertificate19 : b ∉ ((Class.cv e)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_b_ne_e, not_false_eq_true]
  have freeVariableCertificate20 : c ∉ ((Class.cv e)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_c_ne_e, not_false_eq_true]
  have p0082 :=
    @gEladdc (.cv e) B C b c freeVariableCertificate19 freeVariableCertificate20
      (by exact (show b ∉ (B).fv from (by exact fresh_b_not_B)))
      (by exact (show c ∉ (B).fv from (by exact fresh_c_not_B)))
      (by exact (show b ∉ (C).fv from (by exact fresh_b_not_C)))
      (by exact (show c ∉ (C).fv from (by exact fresh_c_not_C)))
      (show b ≠ c from (by exact fresh_b_ne_c))
  have p0083 :=
    @gAnbi1i (.classMem (.cv e) (synCplc B C))
      (synWrex b B (synWrex c C (synWa (.classEq (synCin (.cv b) (.cv c)) (synC0))
            (.classEq (.cv e) (synCun (.cv b) (.cv c))))))
      (synWa (.classEq (synCin (.cv a) (.cv e)) (synC0))
        (.classEq (.cv x) (synCun (.cv a) (.cv e))))
      p0082
  have p0084 :=
    @gN3bitr4ri
      (synWrex b B (synWa (synWrex c C (synWa (.classEq (synCin (.cv b) (.cv c)) (synC0))
              (.classEq (.cv e) (synCun (.cv b) (.cv c)))))
          (synWa (.classEq (synCin (.cv a) (.cv e)) (synC0))
            (.classEq (.cv x) (synCun (.cv a) (.cv e))))))
      (synWa (synWrex b B (synWrex c C (synWa (.classEq (synCin (.cv b) (.cv c)) (synC0))
              (.classEq (.cv e) (synCun (.cv b) (.cv c))))))
        (synWa (.classEq (synCin (.cv a) (.cv e)) (synC0))
          (.classEq (.cv x) (synCun (.cv a) (.cv e)))))
      (synWrex b B (synWrex c C (synWa (synWa (.classEq (synCin (.cv b) (.cv c)) (synC0))
              (.classEq (.cv e) (synCun (.cv b) (.cv c))))
            (synWa (.classEq (synCin (.cv a) (.cv e)) (synC0))
              (.classEq (.cv x) (synCun (.cv a) (.cv e)))))))
      (synWa (.classMem (.cv e) (synCplc B C))
        (synWa (.classEq (synCin (.cv a) (.cv e)) (synC0))
          (.classEq (.cv x) (synCun (.cv a) (.cv e)))))
      p0079 p0081 p0083
  have p0085 :=
    @gExbii
      (synWa (.classMem (.cv e) (synCplc B C))
        (synWa (.classEq (synCin (.cv a) (.cv e)) (synC0))
          (.classEq (.cv x) (synCun (.cv a) (.cv e)))))
      (synWrex b B (synWrex c C (synWa (synWa (.classEq (synCin (.cv b) (.cv c)) (synC0))
              (.classEq (.cv e) (synCun (.cv b) (.cv c))))
            (synWa (.classEq (synCin (.cv a) (.cv e)) (synC0))
              (.classEq (.cv x) (synCun (.cv a) (.cv e)))))))
      e p0084
  have p0086 :=
    @gN3bitr4ri
      (synWrex b B (synWex e (synWrex c C (synWa
              (synWa (.classEq (synCin (.cv b) (.cv c)) (synC0))
                (.classEq (.cv e) (synCun (.cv b) (.cv c))))
              (synWa (.classEq (synCin (.cv a) (.cv e)) (synC0))
                (.classEq (.cv x) (synCun (.cv a) (.cv e))))))))
      (synWex e (synWrex b B (synWrex c C (synWa
              (synWa (.classEq (synCin (.cv b) (.cv c)) (synC0))
                (.classEq (.cv e) (synCun (.cv b) (.cv c))))
              (synWa (.classEq (synCin (.cv a) (.cv e)) (synC0))
                (.classEq (.cv x) (synCun (.cv a) (.cv e))))))))
      (synWrex b B (synWrex c C (synWex e (synWa
              (synWa (.classEq (synCin (.cv b) (.cv c)) (synC0))
                (.classEq (.cv e) (synCun (.cv b) (.cv c))))
              (synWa (.classEq (synCin (.cv a) (.cv e)) (synC0))
                (.classEq (.cv x) (synCun (.cv a) (.cv e))))))))
      (synWex e (synWa (.classMem (.cv e) (synCplc B C))
          (synWa (.classEq (synCin (.cv a) (.cv e)) (synC0))
            (.classEq (.cv x) (synCun (.cv a) (.cv e))))))
      p0076 p0078 p0085
  have p0087 :=
    @gBitri
      (synWrex e (synCplc B C) (synWa (.classEq (synCin (.cv a) (.cv e)) (synC0))
          (.classEq (.cv x) (synCun (.cv a) (.cv e)))))
      (synWex e (synWa (.classMem (.cv e) (synCplc B C))
          (synWa (.classEq (synCin (.cv a) (.cv e)) (synC0))
            (.classEq (.cv x) (synCun (.cv a) (.cv e))))))
      (synWrex b B (synWrex c C (synWex e (synWa
              (synWa (.classEq (synCin (.cv b) (.cv c)) (synC0))
                (.classEq (.cv e) (synCun (.cv b) (.cv c))))
              (synWa (.classEq (synCin (.cv a) (.cv e)) (synC0))
                (.classEq (.cv x) (synCun (.cv a) (.cv e))))))))
      p0075 p0086
  have p0088 :=
    @gRexbii
      (synWrex e (synCplc B C) (synWa (.classEq (synCin (.cv a) (.cv e)) (synC0))
          (.classEq (.cv x) (synCun (.cv a) (.cv e)))))
      (synWrex b B (synWrex c C (synWex e (synWa
              (synWa (.classEq (synCin (.cv b) (.cv c)) (synC0))
                (.classEq (.cv e) (synCun (.cv b) (.cv c))))
              (synWa (.classEq (synCin (.cv a) (.cv e)) (synC0))
                (.classEq (.cv x) (synCun (.cv a) (.cv e))))))))
      a A p0087
  have p0089 :=
    @gBitri (.classMem (.cv x) (synCplc A (synCplc B C)))
      (synWrex a A (synWrex e (synCplc B C)
          (synWa (.classEq (synCin (.cv a) (.cv e)) (synC0))
            (.classEq (.cv x) (synCun (.cv a) (.cv e))))))
      (synWrex a A (synWrex b B (synWrex c C (synWex e (synWa
                (synWa (.classEq (synCin (.cv b) (.cv c)) (synC0))
                  (.classEq (.cv e) (synCun (.cv b) (.cv c))))
                (synWa (.classEq (synCin (.cv a) (.cv e)) (synC0))
                  (.classEq (.cv x) (synCun (.cv a) (.cv e)))))))))
      p0074 p0088
  have p0090 :=
    @gN3bitr4i
      (synWrex a A (synWrex b B (synWrex c C (synWex d (synWa
                (synWa (.classEq (synCin (.cv a) (.cv b)) (synC0))
                  (.classEq (.cv d) (synCun (.cv a) (.cv b))))
                (synWa (.classEq (synCin (.cv d) (.cv c)) (synC0))
                  (.classEq (.cv x) (synCun (.cv d) (.cv c)))))))))
      (synWrex a A (synWrex b B (synWrex c C (synWex e (synWa
                (synWa (.classEq (synCin (.cv b) (.cv c)) (synC0))
                  (.classEq (.cv e) (synCun (.cv b) (.cv c))))
                (synWa (.classEq (synCin (.cv a) (.cv e)) (synC0))
                  (.classEq (.cv x) (synCun (.cv a) (.cv e)))))))))
      (.classMem (.cv x) (synCplc (synCplc A B) C))
      (.classMem (.cv x) (synCplc A (synCplc B C))) p0052 p0073 p0089
  have freeVariableCertificate21 : x ∉ ((synCplc (synCplc A B) C)).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, Finset.mem_union,
      fresh_x_not_A, fresh_x_not_B, fresh_x_not_C, or_false, not_false_eq_true]
  have freeVariableCertificate22 : x ∉ ((synCplc A (synCplc B C))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, Finset.mem_union,
      fresh_x_not_A, fresh_x_not_B, fresh_x_not_C, or_false, not_false_eq_true]
  have p0091 :=
    @gEqriv x (synCplc (synCplc A B) C) (synCplc A (synCplc B C))
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

/-- Checked nominal proof certificate identified upstream as `g_addc32`. -/
@[expose]
noncomputable def gAddc32 (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.classEq (synCplc (synCplc A B) C) (synCplc (synCplc A C) B)) :=
  by
  have p0000 := @gAddccom B C
  have p0001 := @gAddceq2i (synCplc B C) (synCplc C B) A p0000
  have p0002 := @gAddcass A B C
  have p0003 := @gAddcass A C B
  have p0004 :=
    @gN3eqtr4i (synCplc A (synCplc B C)) (synCplc A (synCplc C B))
      (synCplc (synCplc A B) C) (synCplc (synCplc A C) B) p0001 p0002 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_addc4`. -/
@[expose]
noncomputable def gAddc4 (A : Class) (B : Class) (C : Class) (D : Class) :
    Nominal.NPrf
      (.classEq (synCplc (synCplc A B) (synCplc C D))
        (synCplc (synCplc A C) (synCplc B D))) :=
  by
  have p0000 := @gAddc32 A B C
  have p0001 :=
    @gAddceq1i (synCplc (synCplc A B) C) (synCplc (synCplc A C) B) D p0000
  have p0002 := @gAddcass (synCplc A B) C D
  have p0003 := @gAddcass (synCplc A C) B D
  have p0004 :=
    @gN3eqtr3i (synCplc (synCplc (synCplc A B) C) D)
      (synCplc (synCplc (synCplc A C) B) D) (synCplc (synCplc A B) (synCplc C D))
      (synCplc (synCplc A C) (synCplc B D)) p0001 p0002 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_addc6`. -/
@[expose]
noncomputable def gAddc6 (A : Class) (B : Class) (C : Class) (D : Class) (E : Class)
    (F : Class) :
    Nominal.NPrf
      (.classEq (synCplc (synCplc (synCplc A B) (synCplc C D)) (synCplc E F))
        (synCplc (synCplc (synCplc A C) E) (synCplc (synCplc B D) F))) :=
  by
  have p0000 := @gAddc4 A B C D
  have p0001 :=
    @gAddceq1i (synCplc (synCplc A B) (synCplc C D))
      (synCplc (synCplc A C) (synCplc B D)) E p0000
  have p0002 := @gAddc32 (synCplc A C) (synCplc B D) E
  have p0003 :=
    @gEqtri (synCplc (synCplc (synCplc A B) (synCplc C D)) E)
      (synCplc (synCplc (synCplc A C) (synCplc B D)) E)
      (synCplc (synCplc (synCplc A C) E) (synCplc B D)) p0001 p0002
  have p0004 :=
    @gAddceq1i (synCplc (synCplc (synCplc A B) (synCplc C D)) E)
      (synCplc (synCplc (synCplc A C) E) (synCplc B D)) F p0003
  have p0005 := @gAddcass (synCplc (synCplc A B) (synCplc C D)) E F
  have p0006 := @gAddcass (synCplc (synCplc A C) E) (synCplc B D) F
  have p0007 :=
    @gN3eqtr3i (synCplc (synCplc (synCplc (synCplc A B) (synCplc C D)) E) F)
      (synCplc (synCplc (synCplc (synCplc A C) E) (synCplc B D)) F)
      (synCplc (synCplc (synCplc A B) (synCplc C D)) (synCplc E F))
      (synCplc (synCplc (synCplc A C) E) (synCplc (synCplc B D) F)) p0004 p0005 p0006
  exact p0007

/-- Checked nominal proof certificate identified upstream as `g_nncaddccl`. -/
@[expose]
noncomputable def gNncaddccl (A : Class) (B : Class) :
    Nominal.NPrf
      (.imp (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
        (.classMem (synCplc A B) (synCnnc))) :=
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
  have p0000 := @gAddceq1 (.cv a) A B
  have p0001 :=
    @gEleq1d (.classEq (.cv a) A) (synCplc (.cv a) B) (synCplc A B) (synCnnc) p0000
  have p0002 :=
    @gImbi2d (.classEq (.cv a) A) (.classMem (synCplc (.cv a) B) (synCnnc))
      (.classMem (synCplc A B) (synCnnc)) (.classMem B (synCnnc)) p0001
  have p0003 :=
    @gUnab (.neg (.classMem (.cv a) (synCnnc)))
      (.classMem (synCplc (.cv a) (.cv b)) (synCnnc)) b
  have p0004 := @gVex b
  have p0005 := @gVex x
  have p0006 :=
    @gOpkelimagekg (.cv b) (.cv x)
      (synCimak (synCdif (synCins3k (synCcompl
              (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                (synCpw1 (synCpw1 (synC1c)))))) (synCimak
            (synCsymdif (synCins2k (synCins2k (synCssetk)))
              (synCun (synCins2k (synCins3k (synCssetk)))
                (synCins3k (synCsik (synCsik (synCssetk))))))
            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
        (synCpw1 (synCpw1 (.cv a))))
      (synCvv) (synCvv)
  have p0007 :=
    @gMp2an (.classMem (.cv b) (synCvv)) (.classMem (.cv x) (synCvv))
      (synWb (.classMem (synCopk (.cv b) (.cv x)) (synCimagek (synCimak (synCdif
                (synCins3k (synCcompl (synCimak
                      (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                      (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                  (synCsymdif (synCins2k (synCins2k (synCssetk)))
                    (synCun (synCins2k (synCins3k (synCssetk)))
                      (synCins3k (synCsik (synCsik (synCssetk))))))
                  (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
              (synCpw1 (synCpw1 (.cv a)))))) (.classEq (.cv x) (synCimak (synCimak (synCdif
                (synCins3k (synCcompl (synCimak
                      (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                      (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                  (synCsymdif (synCins2k (synCins2k (synCssetk)))
                    (synCun (synCins2k (synCins3k (synCssetk)))
                      (synCins3k (synCsik (synCsik (synCssetk))))))
                  (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
              (synCpw1 (synCpw1 (.cv a)))) (.cv b))))
      p0004 p0005 p0006
  have p0008 :=
    @gOpkelcnvk (.cv x) (.cv b)
      (synCimagek (synCimak (synCdif (synCins3k (synCcompl
                (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                  (synCpw1 (synCpw1 (synC1c)))))) (synCimak
              (synCsymdif (synCins2k (synCins2k (synCssetk)))
                (synCun (synCins2k (synCins3k (synCssetk)))
                  (synCins3k (synCsik (synCsik (synCssetk))))))
              (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
          (synCpw1 (synCpw1 (.cv a)))))
      p0005 p0004
  have p0009 := @gAddccom (.cv a) (.cv b)
  have p0010 := @gDfaddc2 (.cv b) (.cv a)
  have p0011 :=
    @gEqtri (synCplc (.cv a) (.cv b)) (synCplc (.cv b) (.cv a))
      (synCimak (synCimak (synCdif (synCins3k (synCcompl
                (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                  (synCpw1 (synCpw1 (synC1c)))))) (synCimak
              (synCsymdif (synCins2k (synCins2k (synCssetk)))
                (synCun (synCins2k (synCins3k (synCssetk)))
                  (synCins3k (synCsik (synCsik (synCssetk))))))
              (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
          (synCpw1 (synCpw1 (.cv a)))) (.cv b))
      p0009 p0010
  have p0012 :=
    @gEqeq2i (synCplc (.cv a) (.cv b))
      (synCimak (synCimak (synCdif (synCins3k (synCcompl
                (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                  (synCpw1 (synCpw1 (synC1c)))))) (synCimak
              (synCsymdif (synCins2k (synCins2k (synCssetk)))
                (synCun (synCins2k (synCins3k (synCssetk)))
                  (synCins3k (synCsik (synCsik (synCssetk))))))
              (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
          (synCpw1 (synCpw1 (.cv a)))) (.cv b))
      (.cv x) p0011
  have p0013 :=
    @gN3bitr4i
      (.classMem (synCopk (.cv b) (.cv x)) (synCimagek (synCimak (synCdif (synCins3k
                (synCcompl
                  (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                    (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                (synCsymdif (synCins2k (synCins2k (synCssetk)))
                  (synCun (synCins2k (synCins3k (synCssetk)))
                    (synCins3k (synCsik (synCsik (synCssetk))))))
                (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
            (synCpw1 (synCpw1 (.cv a))))))
      (.classEq (.cv x) (synCimak (synCimak (synCdif (synCins3k (synCcompl
                  (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                    (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                (synCsymdif (synCins2k (synCins2k (synCssetk)))
                  (synCun (synCins2k (synCins3k (synCssetk)))
                    (synCins3k (synCsik (synCsik (synCssetk))))))
                (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
            (synCpw1 (synCpw1 (.cv a)))) (.cv b)))
      (.classMem (synCopk (.cv x) (.cv b)) (synCcnvk (synCimagek (synCimak (synCdif
                (synCins3k (synCcompl (synCimak
                      (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                      (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                  (synCsymdif (synCins2k (synCins2k (synCssetk)))
                    (synCun (synCins2k (synCins3k (synCssetk)))
                      (synCins3k (synCsik (synCsik (synCssetk))))))
                  (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
              (synCpw1 (synCpw1 (.cv a)))))))
      (.classEq (.cv x) (synCplc (.cv a) (.cv b))) p0007 p0008 p0012
  have p0014 :=
    @gRexbii
      (.classMem (synCopk (.cv x) (.cv b)) (synCcnvk (synCimagek (synCimak (synCdif
                (synCins3k (synCcompl (synCimak
                      (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                      (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                  (synCsymdif (synCins2k (synCins2k (synCssetk)))
                    (synCun (synCins2k (synCins3k (synCssetk)))
                      (synCins3k (synCsik (synCsik (synCssetk))))))
                  (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
              (synCpw1 (synCpw1 (.cv a)))))))
      (.classEq (.cv x) (synCplc (.cv a) (.cv b))) x (synCnnc) p0013
  have freeVariableCertificate0 :
    x ∉
      ((synCcnvk (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak
                      (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                      (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                  (synCsymdif (synCins2k (synCins2k (synCssetk)))
                    (synCun (synCins2k (synCins3k (synCssetk)))
                      (synCins3k (synCsik (synCsik (synCssetk))))))
                  (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
              (synCpw1 (synCpw1 (.cv a))))))).fv :=
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
    @gElimak x
      (synCcnvk (synCimagek (synCimak (synCdif (synCins3k (synCcompl
                  (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                    (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                (synCsymdif (synCins2k (synCins2k (synCssetk)))
                  (synCun (synCins2k (synCins3k (synCssetk)))
                    (synCins3k (synCsik (synCsik (synCssetk))))))
                (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
            (synCpw1 (synCpw1 (.cv a))))))
      (synCnnc) (.cv b) freeVariableCertificate0
      (by
        exact
          (show x ∉ ((synCnnc)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc];
              exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
      freeVariableCertificate1 p0004
  have freeVariableCertificate2 : x ∉ ((synCplc (.cv a) (.cv b))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      fresh_x_ne_a, fresh_x_ne_b, or_false, not_false_eq_true]
  have p0016 :=
    @gRisset x (synCplc (.cv a) (.cv b)) (synCnnc) freeVariableCertificate2
      (by
        exact
          (show x ∉ ((synCnnc)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc];
              exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
  have p0017 :=
    @gN3bitr4i
      (synWrex x (synCnnc) (.classMem (synCopk (.cv x) (.cv b)) (synCcnvk (synCimagek
              (synCimak (synCdif (synCins3k (synCcompl (synCimak
                        (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                        (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                    (synCsymdif (synCins2k (synCins2k (synCssetk)))
                      (synCun (synCins2k (synCins3k (synCssetk)))
                        (synCins3k (synCsik (synCsik (synCssetk))))))
                    (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                (synCpw1 (synCpw1 (.cv a))))))))
      (synWrex x (synCnnc) (.classEq (.cv x) (synCplc (.cv a) (.cv b))))
      (.classMem (.cv b) (synCimak (synCcnvk (synCimagek (synCimak (synCdif (synCins3k
                    (synCcompl (synCimak
                        (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                        (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                    (synCsymdif (synCins2k (synCins2k (synCssetk)))
                      (synCun (synCins2k (synCins3k (synCssetk)))
                        (synCins3k (synCsik (synCsik (synCssetk))))))
                    (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                (synCpw1 (synCpw1 (.cv a)))))) (synCnnc)))
      (.classMem (synCplc (.cv a) (.cv b)) (synCnnc)) p0014 p0015 p0016
  have freeVariableCertificate3 :
    b ∉
      ((synCimak (synCcnvk (synCimagek (synCimak (synCdif (synCins3k (synCcompl
                      (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                        (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                    (synCsymdif (synCins2k (synCins2k (synCssetk)))
                      (synCun (synCins2k (synCins3k (synCssetk)))
                        (synCins3k (synCsik (synCsik (synCssetk))))))
                    (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                (synCpw1 (synCpw1 (.cv a)))))) (synCnnc))).fv :=
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
    @gEqabi (.classMem (synCplc (.cv a) (.cv b)) (synCnnc)) b
      (synCimak (synCcnvk (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak
                      (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                      (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                  (synCsymdif (synCins2k (synCins2k (synCssetk)))
                    (synCun (synCins2k (synCins3k (synCssetk)))
                      (synCins3k (synCsik (synCsik (synCssetk))))))
                  (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
              (synCpw1 (synCpw1 (.cv a)))))) (synCnnc))
      freeVariableCertificate3 p0017
  have p0019 :=
    @gUneq2i
      (synCimak (synCcnvk (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak
                      (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                      (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                  (synCsymdif (synCins2k (synCins2k (synCssetk)))
                    (synCun (synCins2k (synCins3k (synCssetk)))
                      (synCins3k (synCsik (synCsik (synCssetk))))))
                  (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
              (synCpw1 (synCpw1 (.cv a)))))) (synCnnc))
      (.cab b (.classMem (synCplc (.cv a) (.cv b)) (synCnnc)))
      (.cab b (.neg (.classMem (.cv a) (synCnnc)))) p0018
  have p0020 :=
    @gImor (.classMem (.cv a) (synCnnc))
      (.classMem (synCplc (.cv a) (.cv b)) (synCnnc))
  have p0021 :=
    @gAbbii
      (.imp (.classMem (.cv a) (synCnnc)) (.classMem (synCplc (.cv a) (.cv b)) (synCnnc)))
      (synWo (.neg (.classMem (.cv a) (synCnnc)))
        (.classMem (synCplc (.cv a) (.cv b)) (synCnnc)))
      b p0020
  have p0022 :=
    @gN3eqtr4i
      (synCun (.cab b (.neg (.classMem (.cv a) (synCnnc))))
        (.cab b (.classMem (synCplc (.cv a) (.cv b)) (synCnnc))))
      (.cab b (synWo (.neg (.classMem (.cv a) (synCnnc)))
          (.classMem (synCplc (.cv a) (.cv b)) (synCnnc))))
      (synCun (.cab b (.neg (.classMem (.cv a) (synCnnc)))) (synCimak (synCcnvk (synCimagek
              (synCimak (synCdif (synCins3k (synCcompl (synCimak
                        (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                        (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                    (synCsymdif (synCins2k (synCins2k (synCssetk)))
                      (synCun (synCins2k (synCins3k (synCssetk)))
                        (synCins3k (synCsik (synCsik (synCssetk))))))
                    (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                (synCpw1 (synCpw1 (.cv a)))))) (synCnnc)))
      (.cab b (.imp (.classMem (.cv a) (synCnnc))
          (.classMem (synCplc (.cv a) (.cv b)) (synCnnc))))
      p0003 p0019 p0021
  have freeVariableCertificate4 : b ∉ ((Wff.neg (.classMem (.cv a) (synCnnc)))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_neg,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_b_ne_a, or_false,
      not_false_eq_true]
  have p0023 := @gAbexv (.neg (.classMem (.cv a) (synCnnc))) b freeVariableCertificate4
  have p0024 := @gAddcexlem
  have p0025 := @gVex a
  have p0026 := @gPw1ex (.cv a) p0025
  have p0027 := @gPw1ex (synCpw1 (.cv a)) p0026
  have p0028 :=
    @gImakex
      (synCdif (synCins3k (synCcompl
            (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
              (synCpw1 (synCpw1 (synC1c)))))) (synCimak
          (synCsymdif (synCins2k (synCins2k (synCssetk)))
            (synCun (synCins2k (synCins3k (synCssetk)))
              (synCins3k (synCsik (synCsik (synCssetk))))))
          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
      (synCpw1 (synCpw1 (.cv a))) p0024 p0027
  have p0029 :=
    @gImagekex
      (synCimak (synCdif (synCins3k (synCcompl
              (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                (synCpw1 (synCpw1 (synC1c)))))) (synCimak
            (synCsymdif (synCins2k (synCins2k (synCssetk)))
              (synCun (synCins2k (synCins3k (synCssetk)))
                (synCins3k (synCsik (synCsik (synCssetk))))))
            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
        (synCpw1 (synCpw1 (.cv a))))
      p0028
  have p0030 :=
    @gCnvkex
      (synCimagek (synCimak (synCdif (synCins3k (synCcompl
                (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                  (synCpw1 (synCpw1 (synC1c)))))) (synCimak
              (synCsymdif (synCins2k (synCins2k (synCssetk)))
                (synCun (synCins2k (synCins3k (synCssetk)))
                  (synCins3k (synCsik (synCsik (synCssetk))))))
              (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
          (synCpw1 (synCpw1 (.cv a)))))
      p0029
  have p0031 := @gNncex
  have p0032 :=
    @gImakex
      (synCcnvk (synCimagek (synCimak (synCdif (synCins3k (synCcompl
                  (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                    (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                (synCsymdif (synCins2k (synCins2k (synCssetk)))
                  (synCun (synCins2k (synCins3k (synCssetk)))
                    (synCins3k (synCsik (synCsik (synCssetk))))))
                (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
            (synCpw1 (synCpw1 (.cv a))))))
      (synCnnc) p0030 p0031
  have p0033 :=
    @gUnex (.cab b (.neg (.classMem (.cv a) (synCnnc))))
      (synCimak (synCcnvk (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak
                      (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                      (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                  (synCsymdif (synCins2k (synCins2k (synCssetk)))
                    (synCun (synCins2k (synCins3k (synCssetk)))
                      (synCins3k (synCsik (synCsik (synCssetk))))))
                  (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
              (synCpw1 (synCpw1 (.cv a)))))) (synCnnc))
      p0023 p0032
  have p0034 :=
    @gEqeltrri
      (synCun (.cab b (.neg (.classMem (.cv a) (synCnnc)))) (synCimak (synCcnvk (synCimagek
              (synCimak (synCdif (synCins3k (synCcompl (synCimak
                        (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                        (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                    (synCsymdif (synCins2k (synCins2k (synCssetk)))
                      (synCun (synCins2k (synCins3k (synCssetk)))
                        (synCins3k (synCsik (synCsik (synCssetk))))))
                    (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                (synCpw1 (synCpw1 (.cv a)))))) (synCnnc)))
      (.cab b (.imp (.classMem (.cv a) (synCnnc))
          (.classMem (synCplc (.cv a) (.cv b)) (synCnnc))))
      (synCvv) p0022 p0033
  have p0035 := @gAddceq2 (.cv b) (synC0c) (.cv a)
  have p0036 :=
    @gEleq1d (.classEq (.cv b) (synC0c)) (synCplc (.cv a) (.cv b))
      (synCplc (.cv a) (synC0c)) (synCnnc) p0035
  have p0037 :=
    @gImbi2d (.classEq (.cv b) (synC0c))
      (.classMem (synCplc (.cv a) (.cv b)) (synCnnc))
      (.classMem (synCplc (.cv a) (synC0c)) (synCnnc)) (.classMem (.cv a) (synCnnc))
      p0036
  have p0038 := @gAddceq2 (.cv b) (.cv c) (.cv a)
  have p0039_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq b c) (.classEq (synCplc (.cv a) (.cv b)) (synCplc (.cv a) (.cv c)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synCplc synWrex synWex synWa
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0038
  have p0039 :=
    @gEleq1d (.objEq b c) (synCplc (.cv a) (.cv b)) (synCplc (.cv a) (.cv c))
      (synCnnc) p0039_e00_recanon
  have p0040 :=
    @gImbi2d (.objEq b c) (.classMem (synCplc (.cv a) (.cv b)) (synCnnc))
      (.classMem (synCplc (.cv a) (.cv c)) (synCnnc)) (.classMem (.cv a) (synCnnc))
      p0039
  have p0041 := @gAddceq2 (.cv b) (synCplc (.cv c) (synC1c)) (.cv a)
  have p0042 :=
    @gEleq1d (.classEq (.cv b) (synCplc (.cv c) (synC1c))) (synCplc (.cv a) (.cv b))
      (synCplc (.cv a) (synCplc (.cv c) (synC1c))) (synCnnc) p0041
  have p0043 :=
    @gImbi2d (.classEq (.cv b) (synCplc (.cv c) (synC1c)))
      (.classMem (synCplc (.cv a) (.cv b)) (synCnnc))
      (.classMem (synCplc (.cv a) (synCplc (.cv c) (synC1c))) (synCnnc))
      (.classMem (.cv a) (synCnnc)) p0042
  have p0044 := @gAddceq2 (.cv b) B (.cv a)
  have p0045 :=
    @gEleq1d (.classEq (.cv b) B) (synCplc (.cv a) (.cv b)) (synCplc (.cv a) B)
      (synCnnc) p0044
  have p0046 :=
    @gImbi2d (.classEq (.cv b) B) (.classMem (synCplc (.cv a) (.cv b)) (synCnnc))
      (.classMem (synCplc (.cv a) B) (synCnnc)) (.classMem (.cv a) (synCnnc)) p0045
  have p0047 := @gAddcid1 (.cv a)
  have p0048 := @gId (.classMem (.cv a) (synCnnc))
  have p0049 :=
    @gSyl5eqel (.classMem (.cv a) (synCnnc)) (synCplc (.cv a) (synC0c)) (.cv a)
      (synCnnc) p0047 p0048
  have p0050 := @gAddcass (.cv a) (.cv c) (synC1c)
  have p0051 := @gPeano2 (synCplc (.cv a) (.cv c))
  have p0052 :=
    @gSyl5eqelr (.classMem (synCplc (.cv a) (.cv c)) (synCnnc))
      (synCplc (.cv a) (synCplc (.cv c) (synC1c)))
      (synCplc (synCplc (.cv a) (.cv c)) (synC1c)) (synCnnc) p0050 p0051
  have p0053 :=
    @gImim2i (.classMem (synCplc (.cv a) (.cv c)) (synCnnc))
      (.classMem (synCplc (.cv a) (synCplc (.cv c) (synC1c))) (synCnnc))
      (.classMem (.cv a) (synCnnc)) p0052
  have p0054 :=
    @gA1i
      (.imp (.imp (.classMem (.cv a) (synCnnc))
          (.classMem (synCplc (.cv a) (.cv c)) (synCnnc)))
        (.imp (.classMem (.cv a) (synCnnc))
          (.classMem (synCplc (.cv a) (synCplc (.cv c) (synC1c))) (synCnnc))))
      (.classMem (.cv c) (synCnnc)) p0053
  have freeVariableCertificate5 :
    b ∉
      ((Wff.imp (.classMem (.cv a) (synCnnc))
          (.classMem (synCplc (.cv a) (.cv c)) (synCnnc)))).fv :=
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
      ((Wff.imp (.classMem (.cv a) (synCnnc))
          (.classMem (synCplc (.cv a) (.cv b)) (synCnnc)))).fv :=
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
      ((Wff.imp (.classMem (.cv a) (synCnnc))
          (.classMem (synCplc (.cv a) (synC0c)) (synCnnc)))).fv :=
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
      ((Wff.imp (.classMem (.cv a) (synCnnc))
          (.classMem (synCplc (.cv a) B) (synCnnc)))).fv :=
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
      ((Wff.imp (.classMem (.cv a) (synCnnc))
          (.classMem (synCplc (.cv a) (synCplc (.cv c) (synC1c))) (synCnnc)))).fv :=
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
    @gFinds
      (.imp (.classMem (.cv a) (synCnnc)) (.classMem (synCplc (.cv a) (.cv b)) (synCnnc)))
      (.imp (.classMem (.cv a) (synCnnc)) (.classMem (synCplc (.cv a) (synC0c)) (synCnnc)))
      (.imp (.classMem (.cv a) (synCnnc)) (.classMem (synCplc (.cv a) (.cv c)) (synCnnc)))
      (.imp (.classMem (.cv a) (synCnnc))
        (.classMem (synCplc (.cv a) (synCplc (.cv c) (synC1c))) (synCnnc)))
      (.imp (.classMem (.cv a) (synCnnc)) (.classMem (synCplc (.cv a) B) (synCnnc))) b
      c B (by exact (show b ∉ (B).fv from (by exact fresh_b_not_B)))
      freeVariableCertificate5 freeVariableCertificate6 freeVariableCertificate7
      freeVariableCertificate8 freeVariableCertificate9
      (show b ≠ c from (by exact fresh_b_ne_c)) p0034 p0037 p0040 p0043 p0046 p0049 p0054
  have p0056 :=
    @gCom12 (.classMem B (synCnnc)) (.classMem (.cv a) (synCnnc))
      (.classMem (synCplc (.cv a) B) (synCnnc)) p0055
  have freeVariableCertificate10 :
    a ∉ ((Wff.imp (.classMem B (synCnnc)) (.classMem (synCplc A B) (synCnnc)))).fv :=
    by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, Finset.mem_union,
      Finset.notMem_empty, fresh_a_not_B, fresh_a_not_A, or_false, not_false_eq_true]
  have p0057 :=
    @gVtoclga (.imp (.classMem B (synCnnc)) (.classMem (synCplc (.cv a) B) (synCnnc)))
      (.imp (.classMem B (synCnnc)) (.classMem (synCplc A B) (synCnnc))) a A (synCnnc)
      (by exact (show a ∉ (A).fv from (by exact fresh_a_not_A)))
      (by
        exact
          (show a ∉ ((synCnnc)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc];
              exact (show a ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
      freeVariableCertificate10 p0002 p0056
  have p0058 :=
    @gImp (.classMem A (synCnnc)) (.classMem B (synCnnc))
      (.classMem (synCplc A B) (synCnnc)) p0057
  exact p0058

/-- Checked nominal proof certificate identified upstream as `g_elfin`. -/
@[expose]
noncomputable def gElfin (x : Var) (A : Class) (dv_A_x : x ∉ A.fv) :
    Nominal.NPrf
      (synWb (.classMem A (synCfin)) (synWrex x (synCnnc) (.classMem A (.cv x)))) :=
  by
  have p0000 := (Nominal.classEqRefl (synCfin))
  have p0001 := @gEleq2i (synCfin) (synCuni (synCnnc)) A p0000
  have p0002 :=
    @gEluni2 x A (synCnnc) (by exact (show x ∉ (A).fv from (by exact dv_A_x)))
      (by
        exact
          (show x ∉ ((synCnnc)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc];
              exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
  have p0003 :=
    @gBitri (.classMem A (synCfin)) (.classMem A (synCuni (synCnnc)))
      (synWrex x (synCnnc) (.classMem A (.cv x))) p0001 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_el0c`. -/
@[expose]
noncomputable def gEl0c (A : Class) :
    Nominal.NPrf (synWb (.classMem A (synC0c)) (.classEq A (synC0))) :=
  by
  have p0000 := (Nominal.classEqRefl (synC0c))
  have p0001 := @gEleq2i (synC0c) (synCsn (synC0)) A p0000
  have p0002 := @gN0ex
  have p0003 := @gElsnc2 A (synC0) p0002
  have p0004 :=
    @gBitri (.classMem A (synC0c)) (.classMem A (synCsn (synC0)))
      (.classEq A (synC0)) p0001 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_nulel0c`. -/
@[expose]
noncomputable def gNulel0c : Nominal.NPrf (.classMem (synC0) (synC0c)) :=
  by
  have p0000 := @gEqid (synC0)
  have p0001 := @gEl0c (synC0)
  have p0002 :=
    @gMpbir (.classMem (synC0) (synC0c)) (.classEq (synC0) (synC0)) p0000 p0001
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

/-- Checked nominal proof certificate identified upstream as `g_n_0fin`. -/
@[expose]
noncomputable def gN0fin : Nominal.NPrf (.classMem (synC0) (synCfin)) :=
  by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let n : Var := freshVar proofSupport 0
  have p0000 := @gPeano1
  have p0001 := @gEqid (synC0)
  have p0002 := @gEl0c (synC0)
  have p0003 :=
    @gMpbir (.classMem (synC0) (synC0c)) (.classEq (synC0) (synC0)) p0001 p0002
  have p0004 := @gEleq2 (.cv n) (synC0c) (synC0)
  have freeVariableCertificate0 : n ∉ ((Wff.classMem (synC0) (synC0c))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union,
      Finset.notMem_empty, or_false, not_false_eq_true]
  have p0005 :=
    @gRspcev (.classMem (synC0) (.cv n)) (.classMem (synC0) (synC0c)) n (synC0c)
      (synCnnc)
      (by
        exact
          (show n ∉ ((synC0c)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c];
              exact (show n ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
      (by
        exact
          (show n ∉ ((synCnnc)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc];
              exact (show n ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
      freeVariableCertificate0 p0004
  have p0006 :=
    @gMp2an (.classMem (synC0c) (synCnnc)) (.classMem (synC0) (synC0c))
      (synWrex n (synCnnc) (.classMem (synC0) (.cv n))) p0000 p0003 p0005
  have p0007 :=
    @gElfin n (synC0)
      (by
        exact
          (show n ∉ ((synC0)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0];
              exact (show n ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
  have p0008 :=
    @gMpbir (.classMem (synC0) (synCfin))
      (synWrex n (synCnnc) (.classMem (synC0) (.cv n))) p0006 p0007
  exact p0008


end NFChoice.DirectNominalPrf.WPPReplay

end
