/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NominalWPPReplayChunk010Compact001Block004

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NominalWPPReplayChunk010Compact001Part012`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_srelkex`. -/
@[expose]
noncomputable def gSrelkex :
    Nominal.NPrf
      (.classMem (synCin (synCxpk (synCnnc) (synCnnc)) (synCimak (synCin (synCins3k
                (synCimak (synCin (synCins3k (synCsik
                        (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak
                            (synCsymdif (synCins3k (synCssetk))
                              (synCins2k (synCsik (synCssetk))))
                            (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                    (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))) (synCins2k
                (synCimak (synCin (synCins3k (synCsik (synCcompl (synCimak
                            (synCsymdif (synCins3k (synCssetk))
                              (synCins2k (synCsik (synCssetk))))
                            (synCpw1 (synCpw1 (synC1c))))))) (synCins2k (synCssetk)))
                  (synCpw1 (synCpw1 (synC1c))))))
            (synCpw1 (synCpw1 (synCpw1 (synC1c)))))) (synCvv)) :=
  by
  have p0000 := @gNncex
  have p0002 := @gXpkex (synCnnc) (synCnnc) p0000 p0000
  have p0003 := @gN1cex
  have p0004 := @gPwex (synC1c) p0003
  have p0005 := @gVvex
  have p0006 := @gXpkex (synCpw (synC1c)) (synCvv) p0004 p0005
  have p0007 := @gSsetkex
  have p0008 := @gIns3kex (synCssetk) p0007
  have p0010 := @gSikex (synCssetk) p0007
  have p0011 := @gIns2kex (synCsik (synCssetk)) p0010
  have p0012 :=
    @gSymdifex (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk))) p0008 p0011
  have p0014 := @gPw1ex (synC1c) p0003
  have p0015 := @gPw1ex (synCpw1 (synC1c)) p0014
  have p0016 := @gPw1ex (synCpw1 (synCpw1 (synC1c))) p0015
  have p0017 :=
    @gImakex (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk))))
      (synCpw1 (synCpw1 (synCpw1 (synC1c)))) p0012 p0016
  have p0018 :=
    @gDifex (synCxpk (synCpw (synC1c)) (synCvv))
      (synCimak (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk))))
        (synCpw1 (synCpw1 (synCpw1 (synC1c)))))
      p0006 p0017
  have p0019 :=
    @gSikex
      (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak
          (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk))))
          (synCpw1 (synCpw1 (synCpw1 (synC1c))))))
      p0018
  have p0020 :=
    @gIns3kex
      (synCsik (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak
            (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk))))
            (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
      p0019
  have p0022 := @gIns2kex (synCssetk) p0007
  have p0023 :=
    @gInex
      (synCins3k (synCsik (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak
              (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk))))
              (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
      (synCins2k (synCssetk)) p0020 p0022
  have p0024 :=
    @gImakex
      (synCin (synCins3k (synCsik (synCdif (synCxpk (synCpw (synC1c)) (synCvv))
              (synCimak (synCsymdif (synCins3k (synCssetk))
                  (synCins2k (synCsik (synCssetk))))
                (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))) (synCins2k (synCssetk)))
      (synCpw1 (synCpw1 (synC1c))) p0023 p0015
  have p0025 :=
    @gIns3kex
      (synCimak (synCin (synCins3k (synCsik
              (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak
                  (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk))))
                  (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))) (synCins2k (synCssetk)))
        (synCpw1 (synCpw1 (synC1c))))
      p0024
  have p0026 :=
    @gImakex (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk))))
      (synCpw1 (synCpw1 (synC1c))) p0012 p0015
  have p0027 :=
    @gComplex
      (synCimak (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk))))
        (synCpw1 (synCpw1 (synC1c))))
      p0026
  have p0028 :=
    @gSikex
      (synCcompl (synCimak
          (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk))))
          (synCpw1 (synCpw1 (synC1c)))))
      p0027
  have p0029 :=
    @gIns3kex
      (synCsik (synCcompl (synCimak
            (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk))))
            (synCpw1 (synCpw1 (synC1c))))))
      p0028
  have p0030 :=
    @gInex
      (synCins3k (synCsik (synCcompl (synCimak
              (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk))))
              (synCpw1 (synCpw1 (synC1c)))))))
      (synCins2k (synCssetk)) p0029 p0022
  have p0031 :=
    @gImakex
      (synCin (synCins3k (synCsik (synCcompl (synCimak
                (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk))))
                (synCpw1 (synCpw1 (synC1c))))))) (synCins2k (synCssetk)))
      (synCpw1 (synCpw1 (synC1c))) p0030 p0015
  have p0032 :=
    @gIns2kex
      (synCimak (synCin (synCins3k (synCsik (synCcompl (synCimak
                  (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk))))
                  (synCpw1 (synCpw1 (synC1c))))))) (synCins2k (synCssetk)))
        (synCpw1 (synCpw1 (synC1c))))
      p0031
  have p0033 :=
    @gInex
      (synCins3k (synCimak (synCin (synCins3k (synCsik
                (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak
                    (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk))))
                    (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))) (synCins2k (synCssetk)))
          (synCpw1 (synCpw1 (synC1c)))))
      (synCins2k (synCimak (synCin (synCins3k (synCsik (synCcompl (synCimak
                    (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk))))
                    (synCpw1 (synCpw1 (synC1c))))))) (synCins2k (synCssetk)))
          (synCpw1 (synCpw1 (synC1c)))))
      p0025 p0032
  have p0034 :=
    @gImakex
      (synCin (synCins3k (synCimak (synCin (synCins3k (synCsik
                  (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak
                      (synCsymdif (synCins3k (synCssetk))
                        (synCins2k (synCsik (synCssetk))))
                      (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))) (synCins2k (synCssetk)))
            (synCpw1 (synCpw1 (synC1c))))) (synCins2k (synCimak (synCin (synCins3k
                (synCsik (synCcompl (synCimak (synCsymdif (synCins3k (synCssetk))
                        (synCins2k (synCsik (synCssetk))))
                      (synCpw1 (synCpw1 (synC1c))))))) (synCins2k (synCssetk)))
            (synCpw1 (synCpw1 (synC1c))))))
      (synCpw1 (synCpw1 (synCpw1 (synC1c)))) p0033 p0016
  have p0035 :=
    @gInex (synCxpk (synCnnc) (synCnnc))
      (synCimak (synCin (synCins3k (synCimak (synCin (synCins3k (synCsik
                    (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak
                        (synCsymdif (synCins3k (synCssetk))
                          (synCins2k (synCsik (synCssetk))))
                        (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))) (synCins2k
            (synCimak (synCin (synCins3k (synCsik (synCcompl (synCimak
                        (synCsymdif (synCins3k (synCssetk))
                          (synCins2k (synCsik (synCssetk))))
                        (synCpw1 (synCpw1 (synC1c))))))) (synCins2k (synCssetk)))
              (synCpw1 (synCpw1 (synC1c)))))) (synCpw1 (synCpw1 (synCpw1 (synC1c)))))
      p0002 p0034
  exact p0035

/-- Checked nominal proof certificate identified upstream as `g_sfineq1`. -/
@[expose]
noncomputable def gSfineq1 (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (.classEq A B) (synWb (synWsfin A C) (synWsfin B C))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv
  let y : Var := freshVar proofSupport 0
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_C : y ∉ C.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have dv_cache_0001 : y ∉ ((Wff.classEq A B)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union,
          fresh_y_not_A, fresh_y_not_B, or_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ (A).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_A, not_false_eq_true])
  have dv_cache_0003 : y ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_C, not_false_eq_true])
  have dv_cache_0004 : y ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_B, not_false_eq_true])
  have p0000 := @gEleq1 A B (synCnnc)
  have p0001 := @gEleq2 A B (synCpw1 (.cv y))
  have p0002 :=
    @gAnbi1d (.classEq A B) (.classMem (synCpw1 (.cv y)) A)
      (.classMem (synCpw1 (.cv y)) B) (.classMem (synCpw (.cv y)) C) p0001
  have p0003 :=
    @gExbidv (.classEq A B)
      (synWa (.classMem (synCpw1 (.cv y)) A) (.classMem (synCpw (.cv y)) C))
      (synWa (.classMem (synCpw1 (.cv y)) B) (.classMem (synCpw (.cv y)) C)) y
      dv_cache_0001 p0002
  have p0004 :=
    @gN3anbi13d (.classEq A B) (.classMem A (synCnnc)) (.classMem B (synCnnc))
      (synWex y (synWa (.classMem (synCpw1 (.cv y)) A) (.classMem (synCpw (.cv y)) C)))
      (synWex y (synWa (.classMem (synCpw1 (.cv y)) B) (.classMem (synCpw (.cv y)) C)))
      (.classMem C (synCnnc)) p0000 p0003
  have p0005 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfSfin A C y
      dv_cache_0002 dv_cache_0003
  have p0006 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfSfin B C y
      dv_cache_0004 dv_cache_0003
  have p0007 :=
    @gN3bitr4g (.classEq A B)
      (synW3a (.classMem A (synCnnc)) (.classMem C (synCnnc)) (synWex y
          (synWa (.classMem (synCpw1 (.cv y)) A) (.classMem (synCpw (.cv y)) C))))
      (synW3a (.classMem B (synCnnc)) (.classMem C (synCnnc)) (synWex y
          (synWa (.classMem (synCpw1 (.cv y)) B) (.classMem (synCpw (.cv y)) C))))
      (synWsfin A C) (synWsfin B C) p0004 p0005 p0006
  exact p0007

/-- Checked nominal proof certificate identified upstream as `g_sfineq2`. -/
@[expose]
noncomputable def gSfineq2 (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (.classEq A B) (synWb (synWsfin C A) (synWsfin C B))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv
  let y : Var := freshVar proofSupport 0
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_C : y ∉ C.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have dv_cache_0001 : y ∉ ((Wff.classEq A B)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union,
          fresh_y_not_A, fresh_y_not_B, or_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ (C).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_C, not_false_eq_true])
  have dv_cache_0003 : y ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_A, not_false_eq_true])
  have dv_cache_0004 : y ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_B, not_false_eq_true])
  have p0000 := @gEleq1 A B (synCnnc)
  have p0001 := @gEleq2 A B (synCpw (.cv y))
  have p0002 :=
    @gAnbi2d (.classEq A B) (.classMem (synCpw (.cv y)) A)
      (.classMem (synCpw (.cv y)) B) (.classMem (synCpw1 (.cv y)) C) p0001
  have p0003 :=
    @gExbidv (.classEq A B)
      (synWa (.classMem (synCpw1 (.cv y)) C) (.classMem (synCpw (.cv y)) A))
      (synWa (.classMem (synCpw1 (.cv y)) C) (.classMem (synCpw (.cv y)) B)) y
      dv_cache_0001 p0002
  have p0004 :=
    @gN3anbi23d (.classEq A B) (.classMem A (synCnnc)) (.classMem B (synCnnc))
      (synWex y (synWa (.classMem (synCpw1 (.cv y)) C) (.classMem (synCpw (.cv y)) A)))
      (synWex y (synWa (.classMem (synCpw1 (.cv y)) C) (.classMem (synCpw (.cv y)) B)))
      (.classMem C (synCnnc)) p0000 p0003
  have p0005 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfSfin C A y
      dv_cache_0002 dv_cache_0003
  have p0006 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfSfin C B y
      dv_cache_0002 dv_cache_0004
  have p0007 :=
    @gN3bitr4g (.classEq A B)
      (synW3a (.classMem C (synCnnc)) (.classMem A (synCnnc)) (synWex y
          (synWa (.classMem (synCpw1 (.cv y)) C) (.classMem (synCpw (.cv y)) A))))
      (synW3a (.classMem C (synCnnc)) (.classMem B (synCnnc)) (synWex y
          (synWa (.classMem (synCpw1 (.cv y)) C) (.classMem (synCpw (.cv y)) B))))
      (synWsfin C A) (synWsfin C B) p0004 p0005 p0006
  exact p0007

/-- Checked nominal proof certificate identified upstream as `g_sfin01`. -/
@[expose]
noncomputable def gSfin01 : Nominal.NPrf (synWsfin (synC0c) (synC1c)) :=
  by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let a : Var := freshVar proofSupport 0
  have dv_cache_0001 : a ∉ ((synC0)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0002 :
    a ∉
      ((synWa (.classEq (synCpw1 (synC0)) (synC0))
          (.classMem (synCsn (synC0)) (synC1c)))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0003 : a ∉ ((synC0c)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0004 : a ∉ ((synC1c)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          compact_fv_not_mem_empty, not_false_eq_true])
  have p0000 := @gPeano1
  have p0001 := @gN1cnnc
  have p0002 := @gPw10
  have p0003 := @gN0ex
  have p0004 := @gSnel1c (synC0) p0003
  have p0006 := @gEl0c (synCpw1 (.cv a))
  have p0007 := @gPw1eq (.cv a) (synC0)
  have p0008 :=
    @gEqeq1d (.classEq (.cv a) (synC0)) (synCpw1 (.cv a)) (synCpw1 (synC0)) (synC0)
      p0007
  have p0009 :=
    @gSyl5bb (.classMem (synCpw1 (.cv a)) (synC0c))
      (.classEq (synCpw1 (.cv a)) (synC0)) (.classEq (.cv a) (synC0))
      (.classEq (synCpw1 (synC0)) (synC0)) p0006 p0008
  have p0010 := @gPweq (.cv a) (synC0)
  have p0011 := @gPw0
  have p0012 :=
    @gSyl6eq (.classEq (.cv a) (synC0)) (synCpw (.cv a)) (synCpw (synC0))
      (synCsn (synC0)) p0010 p0011
  have p0013 :=
    @gEleq1d (.classEq (.cv a) (synC0)) (synCpw (.cv a)) (synCsn (synC0)) (synC1c)
      p0012
  have p0014 :=
    @gAnbi12d (.classEq (.cv a) (synC0)) (.classMem (synCpw1 (.cv a)) (synC0c))
      (.classEq (synCpw1 (synC0)) (synC0)) (.classMem (synCpw (.cv a)) (synC1c))
      (.classMem (synCsn (synC0)) (synC1c)) p0009 p0013
  have p0015 :=
    @gSpcev
      (synWa (.classMem (synCpw1 (.cv a)) (synC0c)) (.classMem (synCpw (.cv a)) (synC1c)))
      (synWa (.classEq (synCpw1 (synC0)) (synC0)) (.classMem (synCsn (synC0)) (synC1c)))
      a (synC0) dv_cache_0001 dv_cache_0002 p0003 p0014
  have p0016 :=
    @gMp2an (.classEq (synCpw1 (synC0)) (synC0))
      (.classMem (synCsn (synC0)) (synC1c))
      (synWex a (synWa (.classMem (synCpw1 (.cv a)) (synC0c))
          (.classMem (synCpw (.cv a)) (synC1c))))
      p0002 p0004 p0015
  have p0017 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfSfin (synC0c)
      (synC1c) a dv_cache_0003 dv_cache_0004
  have p0018 :=
    @gMpbir3an (synWsfin (synC0c) (synC1c)) (.classMem (synC0c) (synCnnc))
      (.classMem (synC1c) (synCnnc))
      (synWex a (synWa (.classMem (synCpw1 (.cv a)) (synC0c))
          (.classMem (synCpw (.cv a)) (synC1c))))
      p0000 p0001 p0016 p0017
  exact p0018

/-- Checked nominal proof certificate identified upstream as `g_sfin112`. -/
@[expose]
noncomputable def gSfin112 (P : Class) (M : Class) (N : Class) :
    Nominal.NPrf (.imp (synWa (synWsfin M N) (synWsfin M P)) (.classEq N P)) :=
  by
  let proofSupport : Finset Var := P.fv ∪ M.fv ∪ N.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let n : Var := freshVar proofSupport 2
  let k : Var := freshVar proofSupport 3
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_P : x ∉ P.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_x_not_M : x ∉ M.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_N : x ∉ N.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_P : y ∉ P.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_y_not_M : y ∉ M.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_N : y ∉ N.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_n : n ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_n_not_P : n ∉ P.fv := by
    intro h
    exact fresh_n (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_n_not_M : n ∉ M.fv := by
    intro h
    exact fresh_n (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_n_not_N : n ∉ N.fv := by
    intro h
    exact fresh_n (Finset.mem_union_right _ (h))
  have fresh_k : k ∉ proofSupport :=
    by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_k_not_P : k ∉ P.fv := by
    intro h
    exact fresh_k (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_k_not_M : k ∉ M.fv := by
    intro h
    exact fresh_k (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_k_not_N : k ∉ N.fv := by
    intro h
    exact fresh_k (Finset.mem_union_right _ (h))
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x := Ne.symm fresh_x_ne_y
  have fresh_x_ne_n : x ≠ n :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_n_ne_x : n ≠ x := Ne.symm fresh_x_ne_n
  have fresh_x_ne_k : x ≠ k :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_k_ne_x : k ≠ x := Ne.symm fresh_x_ne_k
  have fresh_y_ne_n : y ≠ n :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_n_ne_y : n ≠ y := Ne.symm fresh_y_ne_n
  have fresh_y_ne_k : y ≠ k :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_k_ne_y : k ≠ y := Ne.symm fresh_y_ne_k
  have fresh_n_ne_k : n ≠ k :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_k_ne_n : k ≠ n := Ne.symm fresh_n_ne_k
  have dv_cache_0001 :
    y ∉ ((synWa (.classMem (synCpw1 (.cv x)) M) (.classMem (synCpw (.cv x)) N))).fv :=
    by
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_x, fresh_y_not_M, fresh_y_not_N, or_false,
          not_false_eq_true])
  have dv_cache_0002 :
    x ∉ ((synWa (.classMem (synCpw1 (.cv y)) M) (.classMem (synCpw (.cv y)) P))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_y, fresh_x_not_M, fresh_x_not_P, or_false,
          not_false_eq_true])
  have dv_cache_0003 : x ∉ (M).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_M, not_false_eq_true])
  have dv_cache_0004 : x ∉ (N).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_N, not_false_eq_true])
  have dv_cache_0005 : y ∉ (M).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_M, not_false_eq_true])
  have dv_cache_0006 : y ∉ (P).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_P, not_false_eq_true])
  have dv_cache_0007 : n ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_n_ne_x, not_false_eq_true])
  have dv_cache_0008 : n ∉ ((Class.cv y)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_n_ne_y, not_false_eq_true])
  have dv_cache_0009 : k ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_k_ne_x, not_false_eq_true])
  have dv_cache_0010 : k ∉ ((Class.cv y)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_k_ne_y, not_false_eq_true])
  have dv_cache_0011 : k ∉ ((Class.cv n)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_k_ne_n, not_false_eq_true])
  have dv_cache_0012 : k ∉ ((Wff.classEq N P)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union,
          fresh_k_not_N, fresh_k_not_P, or_false, not_false_eq_true])
  have dv_cache_0013 :
    k ∉
      ((synWa (synWa (synWa (.classMem M (synCnnc)) (.classMem M (synCnnc)))
            (synWa (.classMem N (synCnnc)) (.classMem P (synCnnc)))) (synWa
            (synWa (.classMem (synCpw1 (.cv x)) M) (.classMem (synCpw (.cv x)) N))
            (synWa (.classMem (synCpw1 (.cv y)) M) (.classMem (synCpw (.cv y)) P))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact
      (by
        have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, Finset.mem_union,
          Finset.mem_singleton, fresh_k_not_M, fresh_k_not_N, fresh_k_not_P, fresh_k_ne_x,
          fresh_k_ne_y, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0014 : n ∉ ((Wff.classEq N P)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union,
          fresh_n_not_N, fresh_n_not_P, or_false, not_false_eq_true])
  have dv_cache_0015 :
    n ∉
      ((synWa (synWa (synWa (.classMem M (synCnnc)) (.classMem M (synCnnc)))
            (synWa (.classMem N (synCnnc)) (.classMem P (synCnnc)))) (synWa
            (synWa (.classMem (synCpw1 (.cv x)) M) (.classMem (synCpw (.cv x)) N))
            (synWa (.classMem (synCpw1 (.cv y)) M) (.classMem (synCpw (.cv y)) P))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, Finset.mem_union,
          Finset.mem_singleton, fresh_n_not_M, fresh_n_not_N, fresh_n_not_P, fresh_n_ne_x,
          fresh_n_ne_y, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0016 : x ∉ ((Wff.classEq N P)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union,
          fresh_x_not_N, fresh_x_not_P, or_false, not_false_eq_true])
  have dv_cache_0017 : y ∉ ((Wff.classEq N P)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union,
          fresh_y_not_N, fresh_y_not_P, or_false, not_false_eq_true])
  have dv_cache_0018 :
    x ∉
      ((synWa (synWa (.classMem M (synCnnc)) (.classMem M (synCnnc)))
          (synWa (.classMem N (synCnnc)) (.classMem P (synCnnc))))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union,
          fresh_x_not_M, fresh_x_not_N, fresh_x_not_P, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0019 :
    y ∉
      ((synWa (synWa (.classMem M (synCnnc)) (.classMem M (synCnnc)))
          (synWa (.classMem N (synCnnc)) (.classMem P (synCnnc))))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union,
          fresh_y_not_M, fresh_y_not_N, fresh_y_not_P, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have p0000 :=
    @gN3an6 (.classMem M (synCnnc)) (.classMem M (synCnnc)) (.classMem N (synCnnc))
      (.classMem P (synCnnc))
      (synWex x (synWa (.classMem (synCpw1 (.cv x)) M) (.classMem (synCpw (.cv x)) N)))
      (synWex y (synWa (.classMem (synCpw1 (.cv y)) M) (.classMem (synCpw (.cv y)) P)))
  have p0001 :=
    @gEeanv (synWa (.classMem (synCpw1 (.cv x)) M) (.classMem (synCpw (.cv x)) N))
      (synWa (.classMem (synCpw1 (.cv y)) M) (.classMem (synCpw (.cv y)) P)) x y
      dv_cache_0001 dv_cache_0002
  have p0002 :=
    @gN3anbi3i
      (synWex x (synWex y (synWa
            (synWa (.classMem (synCpw1 (.cv x)) M) (.classMem (synCpw (.cv x)) N))
            (synWa (.classMem (synCpw1 (.cv y)) M) (.classMem (synCpw (.cv y)) P)))))
      (synWa (synWex x
          (synWa (.classMem (synCpw1 (.cv x)) M) (.classMem (synCpw (.cv x)) N))) (synWex y
          (synWa (.classMem (synCpw1 (.cv y)) M) (.classMem (synCpw (.cv y)) P))))
      (synWa (.classMem M (synCnnc)) (.classMem M (synCnnc)))
      (synWa (.classMem N (synCnnc)) (.classMem P (synCnnc))) p0001
  have p0003 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfSfin M N x
      dv_cache_0003 dv_cache_0004
  have p0004 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfSfin M P y
      dv_cache_0005 dv_cache_0006
  have p0005 :=
    @gAnbi12i (synWsfin M N)
      (synW3a (.classMem M (synCnnc)) (.classMem N (synCnnc)) (synWex x
          (synWa (.classMem (synCpw1 (.cv x)) M) (.classMem (synCpw (.cv x)) N))))
      (synWsfin M P)
      (synW3a (.classMem M (synCnnc)) (.classMem P (synCnnc)) (synWex y
          (synWa (.classMem (synCpw1 (.cv y)) M) (.classMem (synCpw (.cv y)) P))))
      p0003 p0004
  have p0006 :=
    @gN3bitr4ri
      (synW3a (synWa (.classMem M (synCnnc)) (.classMem M (synCnnc)))
        (synWa (.classMem N (synCnnc)) (.classMem P (synCnnc))) (synWa (synWex x
            (synWa (.classMem (synCpw1 (.cv x)) M) (.classMem (synCpw (.cv x)) N)))
          (synWex y
            (synWa (.classMem (synCpw1 (.cv y)) M) (.classMem (synCpw (.cv y)) P)))))
      (synWa (synW3a (.classMem M (synCnnc)) (.classMem N (synCnnc)) (synWex x
            (synWa (.classMem (synCpw1 (.cv x)) M) (.classMem (synCpw (.cv x)) N))))
        (synW3a (.classMem M (synCnnc)) (.classMem P (synCnnc)) (synWex y
            (synWa (.classMem (synCpw1 (.cv y)) M) (.classMem (synCpw (.cv y)) P)))))
      (synW3a (synWa (.classMem M (synCnnc)) (.classMem M (synCnnc)))
        (synWa (.classMem N (synCnnc)) (.classMem P (synCnnc))) (synWex x (synWex y (synWa
              (synWa (.classMem (synCpw1 (.cv x)) M) (.classMem (synCpw (.cv x)) N))
              (synWa (.classMem (synCpw1 (.cv y)) M) (.classMem (synCpw (.cv y)) P))))))
      (synWa (synWsfin M N) (synWsfin M P)) p0000 p0002 p0005
  have p0007 :=
    @gSimpllr (.classMem M (synCnnc)) (.classMem M (synCnnc))
      (synWa (.classMem N (synCnnc)) (.classMem P (synCnnc)))
      (synWa (synWa (.classMem (synCpw1 (.cv x)) M) (.classMem (synCpw (.cv x)) N))
        (synWa (.classMem (synCpw1 (.cv y)) M) (.classMem (synCpw (.cv y)) P)))
  have p0008 :=
    @gSimprll
      (synWa (synWa (.classMem M (synCnnc)) (.classMem M (synCnnc)))
        (synWa (.classMem N (synCnnc)) (.classMem P (synCnnc))))
      (.classMem (synCpw1 (.cv x)) M) (.classMem (synCpw (.cv x)) N)
      (synWa (.classMem (synCpw1 (.cv y)) M) (.classMem (synCpw (.cv y)) P))
  have p0009 :=
    @gSimprrl
      (synWa (synWa (.classMem M (synCnnc)) (.classMem M (synCnnc)))
        (synWa (.classMem N (synCnnc)) (.classMem P (synCnnc))))
      (synWa (.classMem (synCpw1 (.cv x)) M) (.classMem (synCpw (.cv x)) N))
      (.classMem (synCpw1 (.cv y)) M) (.classMem (synCpw (.cv y)) P)
  have p0010 := @gNcfinlower (.cv x) (.cv y) n M dv_cache_0007 dv_cache_0008
  have p0011_e03_recanon :
    Nominal.NPrf
      (.imp (synW3a (.classMem M (synCnnc)) (.classMem (synCpw1 (.cv x)) M)
          (.classMem (synCpw1 (.cv y)) M))
        (synWrex n (synCnnc) (synWa (.objMem x n) (.objMem y n)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synW3a synWa synCnnc synCint synCpw1 synCin synCcompl synCnin
          synWnan synCpw synWss synC1c synWex synCsn synWrex
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
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _)
      p0010
  have p0011 :=
    @gSyl3anc
      (synWa (synWa (synWa (.classMem M (synCnnc)) (.classMem M (synCnnc)))
          (synWa (.classMem N (synCnnc)) (.classMem P (synCnnc))))
        (synWa (synWa (.classMem (synCpw1 (.cv x)) M) (.classMem (synCpw (.cv x)) N))
          (synWa (.classMem (synCpw1 (.cv y)) M) (.classMem (synCpw (.cv y)) P))))
      (.classMem M (synCnnc)) (.classMem (synCpw1 (.cv x)) M)
      (.classMem (synCpw1 (.cv y)) M)
      (synWrex n (synCnnc) (synWa (.objMem x n) (.objMem y n))) p0007 p0008 p0009
      p0011_e03_recanon
  have p0012 :=
    @gNnpweq (.cv x) (.cv y) k (.cv n) dv_cache_0009 dv_cache_0010 dv_cache_0011
  have p0013_e00_recanon :
    Nominal.NPrf
      (.imp (synW3a (.classMem (.cv n) (synCnnc)) (.objMem x n) (.objMem y n))
        (synWrex k (synCnnc) (synWa (.classMem (synCpw (.cv x)) (.cv k))
            (.classMem (synCpw (.cv y)) (.cv k))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synW3a synWa synCnnc synCint synWrex synWex
        simp (config := { failIfUnchanged := false }) only []
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0012
  have p0013 :=
    @gN3expb (.classMem (.cv n) (synCnnc)) (.objMem x n) (.objMem y n)
      (synWrex k (synCnnc) (synWa (.classMem (synCpw (.cv x)) (.cv k))
          (.classMem (synCpw (.cv y)) (.cv k))))
      p0013_e00_recanon
  have p0014 :=
    @gSimp1rl (.classMem N (synCnnc)) (.classMem P (synCnnc))
      (synWa (.classMem M (synCnnc)) (.classMem M (synCnnc)))
      (synWa (synWa (.classMem (synCpw1 (.cv x)) M) (.classMem (synCpw (.cv x)) N))
        (synWa (.classMem (synCpw1 (.cv y)) M) (.classMem (synCpw (.cv y)) P)))
      (synWa (.classMem (.cv k) (synCnnc)) (synWa (.classMem (synCpw (.cv x)) (.cv k))
          (.classMem (synCpw (.cv y)) (.cv k))))
  have p0015 :=
    @gSimp3l
      (synWa (synWa (.classMem M (synCnnc)) (.classMem M (synCnnc)))
        (synWa (.classMem N (synCnnc)) (.classMem P (synCnnc))))
      (synWa (synWa (.classMem (synCpw1 (.cv x)) M) (.classMem (synCpw (.cv x)) N))
        (synWa (.classMem (synCpw1 (.cv y)) M) (.classMem (synCpw (.cv y)) P)))
      (.classMem (.cv k) (synCnnc))
      (synWa (.classMem (synCpw (.cv x)) (.cv k)) (.classMem (synCpw (.cv y)) (.cv k)))
  have p0016 :=
    @gSimp2lr (.classMem (synCpw1 (.cv x)) M) (.classMem (synCpw (.cv x)) N)
      (synWa (.classMem (synCpw1 (.cv y)) M) (.classMem (synCpw (.cv y)) P))
      (synWa (synWa (.classMem M (synCnnc)) (.classMem M (synCnnc)))
        (synWa (.classMem N (synCnnc)) (.classMem P (synCnnc))))
      (synWa (.classMem (.cv k) (synCnnc)) (synWa (.classMem (synCpw (.cv x)) (.cv k))
          (.classMem (synCpw (.cv y)) (.cv k))))
  have p0017 :=
    @gSimp3rl (.classMem (synCpw (.cv x)) (.cv k)) (.classMem (synCpw (.cv y)) (.cv k))
      (.classMem (.cv k) (synCnnc))
      (synWa (synWa (.classMem M (synCnnc)) (.classMem M (synCnnc)))
        (synWa (.classMem N (synCnnc)) (.classMem P (synCnnc))))
      (synWa (synWa (.classMem (synCpw1 (.cv x)) M) (.classMem (synCpw (.cv x)) N))
        (synWa (.classMem (synCpw1 (.cv y)) M) (.classMem (synCpw (.cv y)) P)))
  have p0018 := @gNnceleq (synCpw (.cv x)) N (.cv k)
  have p0019 :=
    @gSyl22anc
      (synW3a (synWa (synWa (.classMem M (synCnnc)) (.classMem M (synCnnc)))
          (synWa (.classMem N (synCnnc)) (.classMem P (synCnnc))))
        (synWa (synWa (.classMem (synCpw1 (.cv x)) M) (.classMem (synCpw (.cv x)) N))
          (synWa (.classMem (synCpw1 (.cv y)) M) (.classMem (synCpw (.cv y)) P)))
        (synWa (.classMem (.cv k) (synCnnc)) (synWa (.classMem (synCpw (.cv x)) (.cv k))
            (.classMem (synCpw (.cv y)) (.cv k)))))
      (.classMem N (synCnnc)) (.classMem (.cv k) (synCnnc))
      (.classMem (synCpw (.cv x)) N) (.classMem (synCpw (.cv x)) (.cv k))
      (.classEq N (.cv k)) p0014 p0015 p0016 p0017 p0018
  have p0020 :=
    @gSimp1rr (.classMem N (synCnnc)) (.classMem P (synCnnc))
      (synWa (.classMem M (synCnnc)) (.classMem M (synCnnc)))
      (synWa (synWa (.classMem (synCpw1 (.cv x)) M) (.classMem (synCpw (.cv x)) N))
        (synWa (.classMem (synCpw1 (.cv y)) M) (.classMem (synCpw (.cv y)) P)))
      (synWa (.classMem (.cv k) (synCnnc)) (synWa (.classMem (synCpw (.cv x)) (.cv k))
          (.classMem (synCpw (.cv y)) (.cv k))))
  have p0021 :=
    @gSimp2rr (.classMem (synCpw1 (.cv y)) M) (.classMem (synCpw (.cv y)) P)
      (synWa (.classMem (synCpw1 (.cv x)) M) (.classMem (synCpw (.cv x)) N))
      (synWa (synWa (.classMem M (synCnnc)) (.classMem M (synCnnc)))
        (synWa (.classMem N (synCnnc)) (.classMem P (synCnnc))))
      (synWa (.classMem (.cv k) (synCnnc)) (synWa (.classMem (synCpw (.cv x)) (.cv k))
          (.classMem (synCpw (.cv y)) (.cv k))))
  have p0022 :=
    @gSimp3rr (.classMem (synCpw (.cv x)) (.cv k)) (.classMem (synCpw (.cv y)) (.cv k))
      (.classMem (.cv k) (synCnnc))
      (synWa (synWa (.classMem M (synCnnc)) (.classMem M (synCnnc)))
        (synWa (.classMem N (synCnnc)) (.classMem P (synCnnc))))
      (synWa (synWa (.classMem (synCpw1 (.cv x)) M) (.classMem (synCpw (.cv x)) N))
        (synWa (.classMem (synCpw1 (.cv y)) M) (.classMem (synCpw (.cv y)) P)))
  have p0023 := @gNnceleq (synCpw (.cv y)) P (.cv k)
  have p0024 :=
    @gSyl22anc
      (synW3a (synWa (synWa (.classMem M (synCnnc)) (.classMem M (synCnnc)))
          (synWa (.classMem N (synCnnc)) (.classMem P (synCnnc))))
        (synWa (synWa (.classMem (synCpw1 (.cv x)) M) (.classMem (synCpw (.cv x)) N))
          (synWa (.classMem (synCpw1 (.cv y)) M) (.classMem (synCpw (.cv y)) P)))
        (synWa (.classMem (.cv k) (synCnnc)) (synWa (.classMem (synCpw (.cv x)) (.cv k))
            (.classMem (synCpw (.cv y)) (.cv k)))))
      (.classMem P (synCnnc)) (.classMem (.cv k) (synCnnc))
      (.classMem (synCpw (.cv y)) P) (.classMem (synCpw (.cv y)) (.cv k))
      (.classEq P (.cv k)) p0020 p0015 p0021 p0022 p0023
  have p0025 :=
    @gEqtr4d
      (synW3a (synWa (synWa (.classMem M (synCnnc)) (.classMem M (synCnnc)))
          (synWa (.classMem N (synCnnc)) (.classMem P (synCnnc))))
        (synWa (synWa (.classMem (synCpw1 (.cv x)) M) (.classMem (synCpw (.cv x)) N))
          (synWa (.classMem (synCpw1 (.cv y)) M) (.classMem (synCpw (.cv y)) P)))
        (synWa (.classMem (.cv k) (synCnnc)) (synWa (.classMem (synCpw (.cv x)) (.cv k))
            (.classMem (synCpw (.cv y)) (.cv k)))))
      N (.cv k) P p0019 p0024
  have p0026 :=
    @gN3expa
      (synWa (synWa (.classMem M (synCnnc)) (.classMem M (synCnnc)))
        (synWa (.classMem N (synCnnc)) (.classMem P (synCnnc))))
      (synWa (synWa (.classMem (synCpw1 (.cv x)) M) (.classMem (synCpw (.cv x)) N))
        (synWa (.classMem (synCpw1 (.cv y)) M) (.classMem (synCpw (.cv y)) P)))
      (synWa (.classMem (.cv k) (synCnnc)) (synWa (.classMem (synCpw (.cv x)) (.cv k))
          (.classMem (synCpw (.cv y)) (.cv k))))
      (.classEq N P) p0025
  have p0027 :=
    @gExpr
      (synWa (synWa (synWa (.classMem M (synCnnc)) (.classMem M (synCnnc)))
          (synWa (.classMem N (synCnnc)) (.classMem P (synCnnc))))
        (synWa (synWa (.classMem (synCpw1 (.cv x)) M) (.classMem (synCpw (.cv x)) N))
          (synWa (.classMem (synCpw1 (.cv y)) M) (.classMem (synCpw (.cv y)) P))))
      (.classMem (.cv k) (synCnnc))
      (synWa (.classMem (synCpw (.cv x)) (.cv k)) (.classMem (synCpw (.cv y)) (.cv k)))
      (.classEq N P) p0026
  have p0028 :=
    @gRexlimdva
      (synWa (synWa (synWa (.classMem M (synCnnc)) (.classMem M (synCnnc)))
          (synWa (.classMem N (synCnnc)) (.classMem P (synCnnc))))
        (synWa (synWa (.classMem (synCpw1 (.cv x)) M) (.classMem (synCpw (.cv x)) N))
          (synWa (.classMem (synCpw1 (.cv y)) M) (.classMem (synCpw (.cv y)) P))))
      (synWa (.classMem (synCpw (.cv x)) (.cv k)) (.classMem (synCpw (.cv y)) (.cv k)))
      (.classEq N P) k (synCnnc) dv_cache_0012 dv_cache_0013 p0027
  have p0029 :=
    @gSyl5 (synWa (.classMem (.cv n) (synCnnc)) (synWa (.objMem x n) (.objMem y n)))
      (synWrex k (synCnnc) (synWa (.classMem (synCpw (.cv x)) (.cv k))
          (.classMem (synCpw (.cv y)) (.cv k))))
      (synWa (synWa (synWa (.classMem M (synCnnc)) (.classMem M (synCnnc)))
          (synWa (.classMem N (synCnnc)) (.classMem P (synCnnc))))
        (synWa (synWa (.classMem (synCpw1 (.cv x)) M) (.classMem (synCpw (.cv x)) N))
          (synWa (.classMem (synCpw1 (.cv y)) M) (.classMem (synCpw (.cv y)) P))))
      (.classEq N P) p0013 p0028
  have p0030 :=
    @gExp3a
      (synWa (synWa (synWa (.classMem M (synCnnc)) (.classMem M (synCnnc)))
          (synWa (.classMem N (synCnnc)) (.classMem P (synCnnc))))
        (synWa (synWa (.classMem (synCpw1 (.cv x)) M) (.classMem (synCpw (.cv x)) N))
          (synWa (.classMem (synCpw1 (.cv y)) M) (.classMem (synCpw (.cv y)) P))))
      (.classMem (.cv n) (synCnnc)) (synWa (.objMem x n) (.objMem y n)) (.classEq N P)
      p0029
  have p0031 :=
    @gRexlimdv
      (synWa (synWa (synWa (.classMem M (synCnnc)) (.classMem M (synCnnc)))
          (synWa (.classMem N (synCnnc)) (.classMem P (synCnnc))))
        (synWa (synWa (.classMem (synCpw1 (.cv x)) M) (.classMem (synCpw (.cv x)) N))
          (synWa (.classMem (synCpw1 (.cv y)) M) (.classMem (synCpw (.cv y)) P))))
      (synWa (.objMem x n) (.objMem y n)) (.classEq N P) n (synCnnc) dv_cache_0014
      dv_cache_0015 p0030
  have p0032 :=
    @gMpd
      (synWa (synWa (synWa (.classMem M (synCnnc)) (.classMem M (synCnnc)))
          (synWa (.classMem N (synCnnc)) (.classMem P (synCnnc))))
        (synWa (synWa (.classMem (synCpw1 (.cv x)) M) (.classMem (synCpw (.cv x)) N))
          (synWa (.classMem (synCpw1 (.cv y)) M) (.classMem (synCpw (.cv y)) P))))
      (synWrex n (synCnnc) (synWa (.objMem x n) (.objMem y n))) (.classEq N P) p0011
      p0031
  have p0033 :=
    @gEx
      (synWa (synWa (.classMem M (synCnnc)) (.classMem M (synCnnc)))
        (synWa (.classMem N (synCnnc)) (.classMem P (synCnnc))))
      (synWa (synWa (.classMem (synCpw1 (.cv x)) M) (.classMem (synCpw (.cv x)) N))
        (synWa (.classMem (synCpw1 (.cv y)) M) (.classMem (synCpw (.cv y)) P)))
      (.classEq N P) p0032
  have p0034 :=
    @gExlimdvv
      (synWa (synWa (.classMem M (synCnnc)) (.classMem M (synCnnc)))
        (synWa (.classMem N (synCnnc)) (.classMem P (synCnnc))))
      (synWa (synWa (.classMem (synCpw1 (.cv x)) M) (.classMem (synCpw (.cv x)) N))
        (synWa (.classMem (synCpw1 (.cv y)) M) (.classMem (synCpw (.cv y)) P)))
      (.classEq N P) x y dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 p0033
  have p0035 :=
    @gN3impia (synWa (.classMem M (synCnnc)) (.classMem M (synCnnc)))
      (synWa (.classMem N (synCnnc)) (.classMem P (synCnnc)))
      (synWex x (synWex y (synWa
            (synWa (.classMem (synCpw1 (.cv x)) M) (.classMem (synCpw (.cv x)) N))
            (synWa (.classMem (synCpw1 (.cv y)) M) (.classMem (synCpw (.cv y)) P)))))
      (.classEq N P) p0034
  have p0036 :=
    @gSylbi (synWa (synWsfin M N) (synWsfin M P))
      (synW3a (synWa (.classMem M (synCnnc)) (.classMem M (synCnnc)))
        (synWa (.classMem N (synCnnc)) (.classMem P (synCnnc))) (synWex x (synWex y (synWa
              (synWa (.classMem (synCpw1 (.cv x)) M) (.classMem (synCpw (.cv x)) N))
              (synWa (.classMem (synCpw1 (.cv y)) M) (.classMem (synCpw (.cv y)) P))))))
      (.classEq N P) p0006 p0035
  exact p0036


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk010Compact001Part013`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_sfindbl`. -/
@[expose]
noncomputable def gSfindbl (A : Class) (n : Var) (M : Class) (dv_M_n : n ∉ M.fv) :
    Nominal.NPrf
      (.imp (synWa (.classMem M (synCnnc)) (.classMem (synCpw1 A) (synCplc M (synC1c))))
        (synWrex n (synCnnc) (synWa (synWsfin M (.cv n))
            (synWsfin (synCplc M (synC1c)) (synCplc (.cv n) (.cv n)))))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ ({ n } : Finset Var) ∪ M.fv
  let b : Var := freshVar proofSupport 0
  let x : Var := freshVar proofSupport 1
  let y : Var := freshVar proofSupport 2
  let z : Var := freshVar proofSupport 3
  let k : Var := freshVar proofSupport 4
  let a : Var := freshVar proofSupport 5
  have fresh_b : b ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_b_not_A : b ∉ A.fv := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_b_ne_n : b ≠ n := by
    intro h
    exact
      fresh_b
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_b_not_M : b ∉ M.fv := by
    intro h
    exact fresh_b (Finset.mem_union_right _ (h))
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_x_ne_n : x ≠ n := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_x_not_M : x ∉ M.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_y_ne_n : y ≠ n := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_n_ne_y : n ≠ y := Ne.symm fresh_y_ne_n
  have fresh_y_not_M : y ∉ M.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_z_ne_n : z ≠ n := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_n_ne_z : n ≠ z := Ne.symm fresh_z_ne_n
  have fresh_z_not_M : z ∉ M.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have fresh_k : k ∉ proofSupport :=
    by
    change freshVar proofSupport 4 ∉ proofSupport
    exact freshVar_not_mem proofSupport 4
  have fresh_k_ne_n : k ≠ n := by
    intro h
    exact
      fresh_k
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_n_ne_k : n ≠ k := Ne.symm fresh_k_ne_n
  have fresh_k_not_M : k ∉ M.fv := by
    intro h
    exact fresh_k (Finset.mem_union_right _ (h))
  have fresh_a : a ∉ proofSupport :=
    by
    change freshVar proofSupport 5 ∉ proofSupport
    exact freshVar_not_mem proofSupport 5
  have fresh_a_ne_n : a ≠ n := by
    intro h
    exact
      fresh_a
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_a_not_M : a ∉ M.fv := by
    intro h
    exact fresh_a (Finset.mem_union_right _ (h))
  have fresh_b_ne_x : b ≠ x :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_b_ne_y : b ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_y_ne_b : y ≠ b := Ne.symm fresh_b_ne_y
  have fresh_b_ne_z : b ≠ z :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_z_ne_b : z ≠ b := Ne.symm fresh_b_ne_z
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_y_ne_x : y ≠ x := Ne.symm fresh_x_ne_y
  have fresh_x_ne_z : x ≠ z :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_z_ne_x : z ≠ x := Ne.symm fresh_x_ne_z
  have fresh_y_ne_z : y ≠ z :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_y_ne_k : y ≠ k :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 2) (j := 4) (by decide)
  have fresh_k_ne_y : k ≠ y := Ne.symm fresh_y_ne_k
  have fresh_y_ne_a : y ≠ a :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 2) (j := 5) (by decide)
  have fresh_a_ne_y : a ≠ y := Ne.symm fresh_y_ne_a
  have fresh_z_ne_k : z ≠ k :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 3) (j := 4) (by decide)
  have fresh_k_ne_z : k ≠ z := Ne.symm fresh_z_ne_k
  have fresh_z_ne_a : z ≠ a :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 3) (j := 5) (by decide)
  have fresh_a_ne_z : a ≠ z := Ne.symm fresh_z_ne_a
  have dv_cache_0001 : b ∉ ((synCpw1 A)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, fresh_b_not_A,
          not_false_eq_true])
  have dv_cache_0002 : x ∉ ((synCpw1 A)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, fresh_x_not_A,
          not_false_eq_true])
  have dv_cache_0003 : b ∉ (M).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_b_not_M, not_false_eq_true])
  have dv_cache_0004 : b ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show b ≠ x from (by exact fresh_b_ne_x))
  have dv_cache_0005 : y ∉ ((Class.cv b)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_y_ne_b, not_false_eq_true])
  have dv_cache_0006 : z ∉ ((Class.cv b)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_z_ne_b, not_false_eq_true])
  have dv_cache_0007 : y ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_y_ne_x, not_false_eq_true])
  have dv_cache_0008 : z ∉ ((Class.cv x)).fv :=
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
          fresh_z_ne_x, not_false_eq_true])
  have dv_cache_0009 : y ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_A, not_false_eq_true])
  have dv_cache_0010 : z ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_A, not_false_eq_true])
  have dv_cache_0011 : y ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (show y ≠ z from (by exact fresh_y_ne_z))
  have dv_cache_0012 : k ∉ ((Class.cv y)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_k_ne_y, not_false_eq_true])
  have dv_cache_0013 : n ∉ ((Class.cv y)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_n_ne_y, not_false_eq_true])
  have dv_cache_0014 : n ∉ ((Class.cv k)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_n_ne_k, not_false_eq_true])
  have dv_cache_0015 : a ∉ ((Class.cv y)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_a_ne_y, not_false_eq_true])
  have dv_cache_0016 :
    a ∉
      ((synWa (.classMem (synCpw1 (.cv y)) M) (.classMem (synCpw (.cv y)) (.cv n)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, Finset.mem_union,
          Finset.mem_singleton, fresh_a_ne_y, fresh_a_not_M, fresh_a_ne_n, or_false,
          not_false_eq_true])
  have dv_cache_0017 : a ∉ (M).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_a_not_M, not_false_eq_true])
  have dv_cache_0018 : a ∉ ((Class.cv n)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_a_ne_n, not_false_eq_true])
  have dv_cache_0019 : a ∉ ((synCun (.cv y) (synCsn (.cv z)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
          Finset.mem_singleton, fresh_a_ne_y, fresh_a_ne_z, or_false, not_false_eq_true])
  have dv_cache_0020 :
    a ∉
      ((synWa (.classMem (synCpw1 (synCun (.cv y) (synCsn (.cv z)))) (synCplc M (synC1c)))
          (.classMem (synCpw (synCun (.cv y) (synCsn (.cv z))))
            (synCplc (.cv n) (.cv n))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, Finset.mem_union,
          Finset.mem_singleton, fresh_a_ne_y, fresh_a_ne_z, fresh_a_not_M, fresh_a_ne_n,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0021 : a ∉ ((synCplc M (synC1c))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          fresh_a_not_M, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0022 : a ∉ ((synCplc (.cv n) (.cv n))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_a_ne_n, or_false, not_false_eq_true])
  have dv_cache_0023 :
    n ∉
      ((synW3a (.classMem M (synCnnc))
          (synWa (.classMem (synCpw1 (.cv y)) M) (.neg (.objMem z y)))
          (synWa (.classMem (.cv k) (synCnnc)) (synWa (.objMem y k) (.objMem y k))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_wff_neg,
          NFChoice.Compiler.CoreFVSimp.fv_wff_objMem, Finset.mem_union, Finset.mem_insert,
          Finset.mem_singleton, fresh_n_ne_k, fresh_n_ne_y, dv_M_n, fresh_n_ne_z,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0024 :
    k ∉
      ((synWrex n (synCnnc) (synWa (synWsfin M (.cv n))
            (synWsfin (synCplc M (synC1c)) (synCplc (.cv n) (.cv n)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
    exact
      (by
        have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wsfin,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_k_not_M, fresh_k_ne_n,
          compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0025 :
    k ∉
      ((synWa (.classMem M (synCnnc))
          (synWa (.classMem (synCpw1 (.cv y)) M) (.neg (.objMem z y))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024
    exact
      (by
        have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_wff_neg,
          NFChoice.Compiler.CoreFVSimp.fv_wff_objMem, Finset.mem_union, Finset.mem_insert,
          Finset.mem_singleton, fresh_k_not_M, fresh_k_ne_y, fresh_k_ne_z,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0026 :
    y ∉
      ((synWrex n (synCnnc) (synWa (synWsfin M (.cv n))
            (synWsfin (synCplc M (synC1c)) (synCplc (.cv n) (.cv n)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wsfin,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_y_not_M, fresh_y_ne_n,
          compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0027 :
    z ∉
      ((synWrex n (synCnnc) (synWa (synWsfin M (.cv n))
            (synWsfin (synCplc M (synC1c)) (synCplc (.cv n) (.cv n)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wsfin,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_z_not_M, fresh_z_ne_n,
          compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0028 :
    y ∉
      ((synWa (.classMem M (synCnnc))
          (synWa (.classMem (.cv b) M) (.classMem (.cv x) (synCcompl (.cv b)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl, Finset.mem_union,
          Finset.mem_singleton, fresh_y_not_M, fresh_y_ne_b, fresh_y_ne_x,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0029 :
    z ∉
      ((synWa (.classMem M (synCnnc))
          (synWa (.classMem (.cv b) M) (.classMem (.cv x) (synCcompl (.cv b)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl, Finset.mem_union,
          Finset.mem_singleton, fresh_z_not_M, fresh_z_ne_b, fresh_z_ne_x,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0030 : x ∉ (M).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_M, not_false_eq_true])
  have dv_cache_0031 :
    b ∉
      ((synWrex n (synCnnc) (synWa (synWsfin M (.cv n))
            (synWsfin (synCplc M (synC1c)) (synCplc (.cv n) (.cv n)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wsfin,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_b_not_M, fresh_b_ne_n,
          compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0032 :
    x ∉
      ((synWrex n (synCnnc) (synWa (synWsfin M (.cv n))
            (synWsfin (synCplc M (synC1c)) (synCplc (.cv n) (.cv n)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wsfin,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_x_not_M, fresh_x_ne_n,
          compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0033 : b ∉ ((Wff.classMem M (synCnnc))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union,
          fresh_b_not_M, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0034 : x ∉ ((Wff.classMem M (synCnnc))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union,
          fresh_x_not_M, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have p0000 :=
    @gElsuc x (synCpw1 A) M b dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
  have p0001 := @gVex b
  have p0002 := @gVex x
  have p0003 :=
    @gPw1eqadj y z (.cv b) (.cv x) A dv_cache_0005 dv_cache_0006 dv_cache_0007
      dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 p0001 p0002
  have p0004 := @gEleq1 (.cv b) (synCpw1 (.cv y)) M
  have p0005 :=
    @gAdantr (.classEq (.cv b) (synCpw1 (.cv y)))
      (synWb (.classMem (.cv b) M) (.classMem (synCpw1 (.cv y)) M))
      (.classEq (.cv x) (synCsn (.cv z))) p0004
  have p0006 := @gCompleq (.cv b) (synCpw1 (.cv y))
  have p0007 :=
    @gEleq12 (.cv x) (synCsn (.cv z)) (synCcompl (.cv b))
      (synCcompl (synCpw1 (.cv y)))
  have p0008 := @gSnex (.cv z)
  have p0009 := @gElcompl (synCsn (.cv z)) (synCpw1 (.cv y)) p0008
  have p0010 := @gSnelpw1 (.cv z) (.cv y)
  have p0011_e01_recanon :
    Nominal.NPrf
      (synWb (.classMem (synCsn (.cv z)) (synCpw1 (.cv y))) (.objMem z y)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCsn synCpw1 synCin synCcompl synCnin synWnan synWa synCpw
          synWss synC1c synWex
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
      p0010
  have p0011 :=
    @gXchbinx (.classMem (synCsn (.cv z)) (synCcompl (synCpw1 (.cv y))))
      (.classMem (synCsn (.cv z)) (synCpw1 (.cv y))) (.objMem z y) p0009
      p0011_e01_recanon
  have p0012 :=
    @gSyl6bb
      (synWa (.classEq (.cv x) (synCsn (.cv z)))
        (.classEq (synCcompl (.cv b)) (synCcompl (synCpw1 (.cv y)))))
      (.classMem (.cv x) (synCcompl (.cv b)))
      (.classMem (synCsn (.cv z)) (synCcompl (synCpw1 (.cv y)))) (.neg (.objMem z y))
      p0007 p0011
  have p0013 :=
    @gSylan2 (.classEq (.cv b) (synCpw1 (.cv y))) (.classEq (.cv x) (synCsn (.cv z)))
      (.classEq (synCcompl (.cv b)) (synCcompl (synCpw1 (.cv y))))
      (synWb (.classMem (.cv x) (synCcompl (.cv b))) (.neg (.objMem z y))) p0006 p0012
  have p0014 :=
    @gAncoms (.classEq (.cv x) (synCsn (.cv z))) (.classEq (.cv b) (synCpw1 (.cv y)))
      (synWb (.classMem (.cv x) (synCcompl (.cv b))) (.neg (.objMem z y))) p0013
  have p0015 :=
    @gAnbi12d
      (synWa (.classEq (.cv b) (synCpw1 (.cv y))) (.classEq (.cv x) (synCsn (.cv z))))
      (.classMem (.cv b) M) (.classMem (synCpw1 (.cv y)) M)
      (.classMem (.cv x) (synCcompl (.cv b))) (.neg (.objMem z y)) p0005 p0014
  have p0016 :=
    @gAnbi2d
      (synWa (.classEq (.cv b) (synCpw1 (.cv y))) (.classEq (.cv x) (synCsn (.cv z))))
      (synWa (.classMem (.cv b) M) (.classMem (.cv x) (synCcompl (.cv b))))
      (synWa (.classMem (synCpw1 (.cv y)) M) (.neg (.objMem z y)))
      (.classMem M (synCnnc)) p0015
  have p0017 := @gNcfinlower (.cv y) (.cv y) k M dv_cache_0012 dv_cache_0012
  have p0018_e00_recanon :
    Nominal.NPrf
      (.imp (synW3a (.classMem M (synCnnc)) (.classMem (synCpw1 (.cv y)) M)
          (.classMem (synCpw1 (.cv y)) M))
        (synWrex k (synCnnc) (synWa (.objMem y k) (.objMem y k)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synW3a synWa synCnnc synCint synCpw1 synCin synCcompl synCnin
          synWnan synCpw synWss synC1c synWex synCsn synWrex
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
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _)
      p0017
  have p0018 :=
    @gN3anidm23 (.classMem M (synCnnc)) (.classMem (synCpw1 (.cv y)) M)
      (synWrex k (synCnnc) (synWa (.objMem y k) (.objMem y k))) p0018_e00_recanon
  have p0019 :=
    @gAdantrr (.classMem M (synCnnc)) (.classMem (synCpw1 (.cv y)) M)
      (synWrex k (synCnnc) (synWa (.objMem y k) (.objMem y k))) (.neg (.objMem z y))
      p0018
  have p0020 :=
    @gSimp3l (.classMem M (synCnnc))
      (synWa (.classMem (synCpw1 (.cv y)) M) (.neg (.objMem z y)))
      (.classMem (.cv k) (synCnnc)) (synWa (.objMem y k) (.objMem y k))
  have p0021 :=
    @gSimp3rr (.objMem y k) (.objMem y k) (.classMem (.cv k) (synCnnc))
      (.classMem M (synCnnc))
      (synWa (.classMem (synCpw1 (.cv y)) M) (.neg (.objMem z y)))
  have p0022 :=
    @gNnpweq (.cv y) (.cv y) n (.cv k) dv_cache_0013 dv_cache_0013 dv_cache_0014
  have p0023_e03_recanon :
    Nominal.NPrf
      (.imp (synW3a (.classMem (.cv k) (synCnnc)) (.objMem y k) (.objMem y k))
        (synWrex n (synCnnc) (synWa (.classMem (synCpw (.cv y)) (.cv n))
            (.classMem (synCpw (.cv y)) (.cv n))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synW3a synWa synCnnc synCint synWrex synWex
        simp (config := { failIfUnchanged := false }) only []
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0022
  have p0023 :=
    @gSyl3anc
      (synW3a (.classMem M (synCnnc))
        (synWa (.classMem (synCpw1 (.cv y)) M) (.neg (.objMem z y)))
        (synWa (.classMem (.cv k) (synCnnc)) (synWa (.objMem y k) (.objMem y k))))
      (.classMem (.cv k) (synCnnc)) (.objMem y k) (.objMem y k)
      (synWrex n (synCnnc) (synWa (.classMem (synCpw (.cv y)) (.cv n))
          (.classMem (synCpw (.cv y)) (.cv n))))
      p0020 p0021 p0021 p0023_e03_recanon
  have p0024 :=
    @gSimpl1 (.classMem M (synCnnc))
      (synWa (.classMem (synCpw1 (.cv y)) M) (.neg (.objMem z y)))
      (synWa (.classMem (.cv k) (synCnnc)) (synWa (.objMem y k) (.objMem y k)))
      (synWa (.classMem (.cv n) (synCnnc)) (synWa (.classMem (synCpw (.cv y)) (.cv n))
          (.classMem (synCpw (.cv y)) (.cv n))))
  have p0025 :=
    @gSimprl
      (synW3a (.classMem M (synCnnc))
        (synWa (.classMem (synCpw1 (.cv y)) M) (.neg (.objMem z y)))
        (synWa (.classMem (.cv k) (synCnnc)) (synWa (.objMem y k) (.objMem y k))))
      (.classMem (.cv n) (synCnnc))
      (synWa (.classMem (synCpw (.cv y)) (.cv n)) (.classMem (synCpw (.cv y)) (.cv n)))
  have p0026 :=
    @gSimpl2l (.classMem (synCpw1 (.cv y)) M) (.neg (.objMem z y))
      (.classMem M (synCnnc))
      (synWa (.classMem (.cv k) (synCnnc)) (synWa (.objMem y k) (.objMem y k)))
      (synWa (.classMem (.cv n) (synCnnc)) (synWa (.classMem (synCpw (.cv y)) (.cv n))
          (.classMem (synCpw (.cv y)) (.cv n))))
  have p0027 :=
    @gSimprrr
      (synW3a (.classMem M (synCnnc))
        (synWa (.classMem (synCpw1 (.cv y)) M) (.neg (.objMem z y)))
        (synWa (.classMem (.cv k) (synCnnc)) (synWa (.objMem y k) (.objMem y k))))
      (.classMem (.cv n) (synCnnc)) (.classMem (synCpw (.cv y)) (.cv n))
      (.classMem (synCpw (.cv y)) (.cv n))
  have p0028 := @gVex y
  have p0029 := @gPw1eq (.cv a) (.cv y)
  have p0030_e00_recanon :
    Nominal.NPrf (.imp (.objEq a y) (.classEq (synCpw1 (.cv a)) (synCpw1 (.cv y)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synCpw1 synCin synCcompl synCnin synWnan synWa synCpw synWss
          synC1c synWex synCsn
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0029
  have p0030 :=
    @gEleq1d (.objEq a y) (synCpw1 (.cv a)) (synCpw1 (.cv y)) M p0030_e00_recanon
  have p0031 := @gPweq (.cv a) (.cv y)
  have p0032_e00_recanon :
    Nominal.NPrf (.imp (.objEq a y) (.classEq (synCpw (.cv a)) (synCpw (.cv y)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synCpw synWss synCin synCcompl synCnin synWnan synWa
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0031
  have p0032 :=
    @gEleq1d (.objEq a y) (synCpw (.cv a)) (synCpw (.cv y)) (.cv n) p0032_e00_recanon
  have p0033 :=
    @gAnbi12d (.objEq a y) (.classMem (synCpw1 (.cv a)) M)
      (.classMem (synCpw1 (.cv y)) M) (.classMem (synCpw (.cv a)) (.cv n))
      (.classMem (synCpw (.cv y)) (.cv n)) p0030 p0032
  have p0034_e01_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv a) (.cv y)) (synWb
          (synWa (.classMem (synCpw1 (.cv a)) M) (.classMem (synCpw (.cv a)) (.cv n)))
          (synWa (.classMem (synCpw1 (.cv y)) M) (.classMem (synCpw (.cv y)) (.cv n))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWa synCpw1 synCin synCcompl synCnin synWnan synCpw synWss
          synC1c synWex synCsn
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0033
  have p0034 :=
    @gSpcev
      (synWa (.classMem (synCpw1 (.cv a)) M) (.classMem (synCpw (.cv a)) (.cv n)))
      (synWa (.classMem (synCpw1 (.cv y)) M) (.classMem (synCpw (.cv y)) (.cv n))) a
      (.cv y) dv_cache_0015 dv_cache_0016 p0028 p0034_e01_recanon
  have p0035 :=
    @gSyl2anc
      (synWa (synW3a (.classMem M (synCnnc))
          (synWa (.classMem (synCpw1 (.cv y)) M) (.neg (.objMem z y)))
          (synWa (.classMem (.cv k) (synCnnc)) (synWa (.objMem y k) (.objMem y k))))
        (synWa (.classMem (.cv n) (synCnnc)) (synWa (.classMem (synCpw (.cv y)) (.cv n))
            (.classMem (synCpw (.cv y)) (.cv n)))))
      (.classMem (synCpw1 (.cv y)) M) (.classMem (synCpw (.cv y)) (.cv n))
      (synWex a
        (synWa (.classMem (synCpw1 (.cv a)) M) (.classMem (synCpw (.cv a)) (.cv n))))
      p0026 p0027 p0034
  have p0036 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfSfin M (.cv n) a
      dv_cache_0017 dv_cache_0018
  have p0037 :=
    @gSyl3anbrc
      (synWa (synW3a (.classMem M (synCnnc))
          (synWa (.classMem (synCpw1 (.cv y)) M) (.neg (.objMem z y)))
          (synWa (.classMem (.cv k) (synCnnc)) (synWa (.objMem y k) (.objMem y k))))
        (synWa (.classMem (.cv n) (synCnnc)) (synWa (.classMem (synCpw (.cv y)) (.cv n))
            (.classMem (synCpw (.cv y)) (.cv n)))))
      (.classMem M (synCnnc)) (.classMem (.cv n) (synCnnc))
      (synWex a
        (synWa (.classMem (synCpw1 (.cv a)) M) (.classMem (synCpw (.cv a)) (.cv n))))
      (synWsfin M (.cv n)) p0024 p0025 p0035 p0036
  have p0038 := @gPeano2 M
  have p0039 :=
    @gSyl
      (synWa (synW3a (.classMem M (synCnnc))
          (synWa (.classMem (synCpw1 (.cv y)) M) (.neg (.objMem z y)))
          (synWa (.classMem (.cv k) (synCnnc)) (synWa (.objMem y k) (.objMem y k))))
        (synWa (.classMem (.cv n) (synCnnc)) (synWa (.classMem (synCpw (.cv y)) (.cv n))
            (.classMem (synCpw (.cv y)) (.cv n)))))
      (.classMem M (synCnnc)) (.classMem (synCplc M (synC1c)) (synCnnc)) p0024 p0038
  have p0040 := @gNncaddccl (.cv n) (.cv n)
  have p0041 :=
    @gAnidms (.classMem (.cv n) (synCnnc))
      (.classMem (synCplc (.cv n) (.cv n)) (synCnnc)) p0040
  have p0042 :=
    @gSyl
      (synWa (synW3a (.classMem M (synCnnc))
          (synWa (.classMem (synCpw1 (.cv y)) M) (.neg (.objMem z y)))
          (synWa (.classMem (.cv k) (synCnnc)) (synWa (.objMem y k) (.objMem y k))))
        (synWa (.classMem (.cv n) (synCnnc)) (synWa (.classMem (synCpw (.cv y)) (.cv n))
            (.classMem (synCpw (.cv y)) (.cv n)))))
      (.classMem (.cv n) (synCnnc)) (.classMem (synCplc (.cv n) (.cv n)) (synCnnc))
      p0025 p0041
  have p0043 := @gPw1un (.cv y) (synCsn (.cv z))
  have p0044 := @gVex z
  have p0045 := @gPw1sn (.cv z) p0044
  have p0046 :=
    @gUneq2i (synCpw1 (synCsn (.cv z))) (synCsn (synCsn (.cv z))) (synCpw1 (.cv y))
      p0045
  have p0047 :=
    @gEqtri (synCpw1 (synCun (.cv y) (synCsn (.cv z))))
      (synCun (synCpw1 (.cv y)) (synCpw1 (synCsn (.cv z))))
      (synCun (synCpw1 (.cv y)) (synCsn (synCsn (.cv z)))) p0043 p0046
  have p0048 :=
    @gSimpl2r (.classMem (synCpw1 (.cv y)) M) (.neg (.objMem z y))
      (.classMem M (synCnnc))
      (synWa (.classMem (.cv k) (synCnnc)) (synWa (.objMem y k) (.objMem y k)))
      (synWa (.classMem (.cv n) (synCnnc)) (synWa (.classMem (synCpw (.cv y)) (.cv n))
          (.classMem (synCpw (.cv y)) (.cv n))))
  have p0049_e01_recanon :
    Nominal.NPrf
      (synWb (.classMem (synCsn (.cv z)) (synCpw1 (.cv y))) (.objMem z y)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCsn synCpw1 synCin synCcompl synCnin synWnan synWa synCpw
          synWss synC1c synWex
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
      p0010
  have p0049 :=
    @gSylnibr
      (synWa (synW3a (.classMem M (synCnnc))
          (synWa (.classMem (synCpw1 (.cv y)) M) (.neg (.objMem z y)))
          (synWa (.classMem (.cv k) (synCnnc)) (synWa (.objMem y k) (.objMem y k))))
        (synWa (.classMem (.cv n) (synCnnc)) (synWa (.classMem (synCpw (.cv y)) (.cv n))
            (.classMem (synCpw (.cv y)) (.cv n)))))
      (.objMem z y) (.classMem (synCsn (.cv z)) (synCpw1 (.cv y))) p0048
      p0049_e01_recanon
  have p0050 := @gElsuci (synCpw1 (.cv y)) M (synCsn (.cv z)) p0008
  have p0051 :=
    @gSyl2anc
      (synWa (synW3a (.classMem M (synCnnc))
          (synWa (.classMem (synCpw1 (.cv y)) M) (.neg (.objMem z y)))
          (synWa (.classMem (.cv k) (synCnnc)) (synWa (.objMem y k) (.objMem y k))))
        (synWa (.classMem (.cv n) (synCnnc)) (synWa (.classMem (synCpw (.cv y)) (.cv n))
            (.classMem (synCpw (.cv y)) (.cv n)))))
      (.classMem (synCpw1 (.cv y)) M)
      (.neg (.classMem (synCsn (.cv z)) (synCpw1 (.cv y))))
      (.classMem (synCun (synCpw1 (.cv y)) (synCsn (synCsn (.cv z))))
        (synCplc M (synC1c)))
      p0026 p0049 p0050
  have p0052 :=
    @gSyl5eqel
      (synWa (synW3a (.classMem M (synCnnc))
          (synWa (.classMem (synCpw1 (.cv y)) M) (.neg (.objMem z y)))
          (synWa (.classMem (.cv k) (synCnnc)) (synWa (.objMem y k) (.objMem y k))))
        (synWa (.classMem (.cv n) (synCnnc)) (synWa (.classMem (synCpw (.cv y)) (.cv n))
            (.classMem (synCpw (.cv y)) (.cv n)))))
      (synCpw1 (synCun (.cv y) (synCsn (.cv z))))
      (synCun (synCpw1 (.cv y)) (synCsn (synCsn (.cv z)))) (synCplc M (synC1c))
      p0047 p0051
  have p0053 :=
    @gSimpl3l (.classMem (.cv k) (synCnnc)) (synWa (.objMem y k) (.objMem y k))
      (.classMem M (synCnnc))
      (synWa (.classMem (synCpw1 (.cv y)) M) (.neg (.objMem z y)))
      (synWa (.classMem (.cv n) (synCnnc)) (synWa (.classMem (synCpw (.cv y)) (.cv n))
          (.classMem (synCpw (.cv y)) (.cv n))))
  have p0054 :=
    @gAdantr
      (synW3a (.classMem M (synCnnc))
        (synWa (.classMem (synCpw1 (.cv y)) M) (.neg (.objMem z y)))
        (synWa (.classMem (.cv k) (synCnnc)) (synWa (.objMem y k) (.objMem y k))))
      (.objMem y k)
      (synWa (.classMem (.cv n) (synCnnc)) (synWa (.classMem (synCpw (.cv y)) (.cv n))
          (.classMem (synCpw (.cv y)) (.cv n))))
      p0021
  have p0055 := @gElcompl (.cv z) (.cv y) p0044
  have p0056_e01_recanon :
    Nominal.NPrf (synWb (.classMem (.cv z) (synCcompl (.cv y))) (.neg (.objMem z y))) :=
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
      p0055
  have p0056 :=
    @gSylibr
      (synWa (synW3a (.classMem M (synCnnc))
          (synWa (.classMem (synCpw1 (.cv y)) M) (.neg (.objMem z y)))
          (synWa (.classMem (.cv k) (synCnnc)) (synWa (.objMem y k) (.objMem y k))))
        (synWa (.classMem (.cv n) (synCnnc)) (synWa (.classMem (synCpw (.cv y)) (.cv n))
            (.classMem (synCpw (.cv y)) (.cv n)))))
      (.neg (.objMem z y)) (.classMem (.cv z) (synCcompl (.cv y))) p0048
      p0056_e01_recanon
  have p0057 := @gNnadjoinpw (.cv y) (.cv k) (.cv n) (.cv z)
  have p0058_e05_recanon :
    Nominal.NPrf
      (.imp (synW3a (synWa (.classMem (.cv k) (synCnnc)) (.classMem (.cv n) (synCnnc)))
          (synWa (.objMem y k) (.classMem (.cv z) (synCcompl (.cv y))))
          (.classMem (synCpw (.cv y)) (.cv n)))
        (.classMem (synCpw (synCun (.cv y) (synCsn (.cv z)))) (synCplc (.cv n) (.cv n)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synW3a synWa synCpw synWss synCin synCcompl synCnin synWnan
          synCplc synWrex synWex
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0057
  have p0058 :=
    @gSyl221anc
      (synWa (synW3a (.classMem M (synCnnc))
          (synWa (.classMem (synCpw1 (.cv y)) M) (.neg (.objMem z y)))
          (synWa (.classMem (.cv k) (synCnnc)) (synWa (.objMem y k) (.objMem y k))))
        (synWa (.classMem (.cv n) (synCnnc)) (synWa (.classMem (synCpw (.cv y)) (.cv n))
            (.classMem (synCpw (.cv y)) (.cv n)))))
      (.classMem (.cv k) (synCnnc)) (.classMem (.cv n) (synCnnc)) (.objMem y k)
      (.classMem (.cv z) (synCcompl (.cv y))) (.classMem (synCpw (.cv y)) (.cv n))
      (.classMem (synCpw (synCun (.cv y) (synCsn (.cv z)))) (synCplc (.cv n) (.cv n)))
      p0053 p0025 p0054 p0056 p0027 p0058_e05_recanon
  have p0059 := @gUnex (.cv y) (synCsn (.cv z)) p0028 p0008
  have p0060 := @gPw1eq (.cv a) (synCun (.cv y) (synCsn (.cv z)))
  have p0061 :=
    @gEleq1d (.classEq (.cv a) (synCun (.cv y) (synCsn (.cv z)))) (synCpw1 (.cv a))
      (synCpw1 (synCun (.cv y) (synCsn (.cv z)))) (synCplc M (synC1c)) p0060
  have p0062 := @gPweq (.cv a) (synCun (.cv y) (synCsn (.cv z)))
  have p0063 :=
    @gEleq1d (.classEq (.cv a) (synCun (.cv y) (synCsn (.cv z)))) (synCpw (.cv a))
      (synCpw (synCun (.cv y) (synCsn (.cv z)))) (synCplc (.cv n) (.cv n)) p0062
  have p0064 :=
    @gAnbi12d (.classEq (.cv a) (synCun (.cv y) (synCsn (.cv z))))
      (.classMem (synCpw1 (.cv a)) (synCplc M (synC1c)))
      (.classMem (synCpw1 (synCun (.cv y) (synCsn (.cv z)))) (synCplc M (synC1c)))
      (.classMem (synCpw (.cv a)) (synCplc (.cv n) (.cv n)))
      (.classMem (synCpw (synCun (.cv y) (synCsn (.cv z)))) (synCplc (.cv n) (.cv n)))
      p0061 p0063
  have p0065 :=
    @gSpcev
      (synWa (.classMem (synCpw1 (.cv a)) (synCplc M (synC1c)))
        (.classMem (synCpw (.cv a)) (synCplc (.cv n) (.cv n))))
      (synWa (.classMem (synCpw1 (synCun (.cv y) (synCsn (.cv z)))) (synCplc M (synC1c)))
        (.classMem (synCpw (synCun (.cv y) (synCsn (.cv z)))) (synCplc (.cv n) (.cv n))))
      a (synCun (.cv y) (synCsn (.cv z))) dv_cache_0019 dv_cache_0020 p0059 p0064
  have p0066 :=
    @gSyl2anc
      (synWa (synW3a (.classMem M (synCnnc))
          (synWa (.classMem (synCpw1 (.cv y)) M) (.neg (.objMem z y)))
          (synWa (.classMem (.cv k) (synCnnc)) (synWa (.objMem y k) (.objMem y k))))
        (synWa (.classMem (.cv n) (synCnnc)) (synWa (.classMem (synCpw (.cv y)) (.cv n))
            (.classMem (synCpw (.cv y)) (.cv n)))))
      (.classMem (synCpw1 (synCun (.cv y) (synCsn (.cv z)))) (synCplc M (synC1c)))
      (.classMem (synCpw (synCun (.cv y) (synCsn (.cv z)))) (synCplc (.cv n) (.cv n)))
      (synWex a (synWa (.classMem (synCpw1 (.cv a)) (synCplc M (synC1c)))
          (.classMem (synCpw (.cv a)) (synCplc (.cv n) (.cv n)))))
      p0052 p0058 p0065
  have p0067 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfSfin
      (synCplc M (synC1c)) (synCplc (.cv n) (.cv n)) a dv_cache_0021 dv_cache_0022
  have p0068 :=
    @gSyl3anbrc
      (synWa (synW3a (.classMem M (synCnnc))
          (synWa (.classMem (synCpw1 (.cv y)) M) (.neg (.objMem z y)))
          (synWa (.classMem (.cv k) (synCnnc)) (synWa (.objMem y k) (.objMem y k))))
        (synWa (.classMem (.cv n) (synCnnc)) (synWa (.classMem (synCpw (.cv y)) (.cv n))
            (.classMem (synCpw (.cv y)) (.cv n)))))
      (.classMem (synCplc M (synC1c)) (synCnnc))
      (.classMem (synCplc (.cv n) (.cv n)) (synCnnc))
      (synWex a (synWa (.classMem (synCpw1 (.cv a)) (synCplc M (synC1c)))
          (.classMem (synCpw (.cv a)) (synCplc (.cv n) (.cv n)))))
      (synWsfin (synCplc M (synC1c)) (synCplc (.cv n) (.cv n))) p0039 p0042 p0066
      p0067
  have p0069 :=
    @gJca
      (synWa (synW3a (.classMem M (synCnnc))
          (synWa (.classMem (synCpw1 (.cv y)) M) (.neg (.objMem z y)))
          (synWa (.classMem (.cv k) (synCnnc)) (synWa (.objMem y k) (.objMem y k))))
        (synWa (.classMem (.cv n) (synCnnc)) (synWa (.classMem (synCpw (.cv y)) (.cv n))
            (.classMem (synCpw (.cv y)) (.cv n)))))
      (synWsfin M (.cv n)) (synWsfin (synCplc M (synC1c)) (synCplc (.cv n) (.cv n)))
      p0037 p0068
  have p0070 :=
    @gExpr
      (synW3a (.classMem M (synCnnc))
        (synWa (.classMem (synCpw1 (.cv y)) M) (.neg (.objMem z y)))
        (synWa (.classMem (.cv k) (synCnnc)) (synWa (.objMem y k) (.objMem y k))))
      (.classMem (.cv n) (synCnnc))
      (synWa (.classMem (synCpw (.cv y)) (.cv n)) (.classMem (synCpw (.cv y)) (.cv n)))
      (synWa (synWsfin M (.cv n))
        (synWsfin (synCplc M (synC1c)) (synCplc (.cv n) (.cv n))))
      p0069
  have p0071 :=
    @gReximdva
      (synW3a (.classMem M (synCnnc))
        (synWa (.classMem (synCpw1 (.cv y)) M) (.neg (.objMem z y)))
        (synWa (.classMem (.cv k) (synCnnc)) (synWa (.objMem y k) (.objMem y k))))
      (synWa (.classMem (synCpw (.cv y)) (.cv n)) (.classMem (synCpw (.cv y)) (.cv n)))
      (synWa (synWsfin M (.cv n))
        (synWsfin (synCplc M (synC1c)) (synCplc (.cv n) (.cv n))))
      n (synCnnc) dv_cache_0023 p0070
  have p0072 :=
    @gMpd
      (synW3a (.classMem M (synCnnc))
        (synWa (.classMem (synCpw1 (.cv y)) M) (.neg (.objMem z y)))
        (synWa (.classMem (.cv k) (synCnnc)) (synWa (.objMem y k) (.objMem y k))))
      (synWrex n (synCnnc) (synWa (.classMem (synCpw (.cv y)) (.cv n))
          (.classMem (synCpw (.cv y)) (.cv n))))
      (synWrex n (synCnnc) (synWa (synWsfin M (.cv n))
          (synWsfin (synCplc M (synC1c)) (synCplc (.cv n) (.cv n)))))
      p0023 p0071
  have p0073 :=
    @gN3expa (.classMem M (synCnnc))
      (synWa (.classMem (synCpw1 (.cv y)) M) (.neg (.objMem z y)))
      (synWa (.classMem (.cv k) (synCnnc)) (synWa (.objMem y k) (.objMem y k)))
      (synWrex n (synCnnc) (synWa (synWsfin M (.cv n))
          (synWsfin (synCplc M (synC1c)) (synCplc (.cv n) (.cv n)))))
      p0072
  have p0074 :=
    @gExpr
      (synWa (.classMem M (synCnnc))
        (synWa (.classMem (synCpw1 (.cv y)) M) (.neg (.objMem z y))))
      (.classMem (.cv k) (synCnnc)) (synWa (.objMem y k) (.objMem y k))
      (synWrex n (synCnnc) (synWa (synWsfin M (.cv n))
          (synWsfin (synCplc M (synC1c)) (synCplc (.cv n) (.cv n)))))
      p0073
  have p0075 :=
    @gRexlimdva
      (synWa (.classMem M (synCnnc))
        (synWa (.classMem (synCpw1 (.cv y)) M) (.neg (.objMem z y))))
      (synWa (.objMem y k) (.objMem y k))
      (synWrex n (synCnnc) (synWa (synWsfin M (.cv n))
          (synWsfin (synCplc M (synC1c)) (synCplc (.cv n) (.cv n)))))
      k (synCnnc) dv_cache_0024 dv_cache_0025 p0074
  have p0076 :=
    @gMpd
      (synWa (.classMem M (synCnnc))
        (synWa (.classMem (synCpw1 (.cv y)) M) (.neg (.objMem z y))))
      (synWrex k (synCnnc) (synWa (.objMem y k) (.objMem y k)))
      (synWrex n (synCnnc) (synWa (synWsfin M (.cv n))
          (synWsfin (synCplc M (synC1c)) (synCplc (.cv n) (.cv n)))))
      p0019 p0075
  have p0077 :=
    @gSyl6bi
      (synWa (.classEq (.cv b) (synCpw1 (.cv y))) (.classEq (.cv x) (synCsn (.cv z))))
      (synWa (.classMem M (synCnnc))
        (synWa (.classMem (.cv b) M) (.classMem (.cv x) (synCcompl (.cv b)))))
      (synWa (.classMem M (synCnnc))
        (synWa (.classMem (synCpw1 (.cv y)) M) (.neg (.objMem z y))))
      (synWrex n (synCnnc) (synWa (synWsfin M (.cv n))
          (synWsfin (synCplc M (synC1c)) (synCplc (.cv n) (.cv n)))))
      p0016 p0076
  have p0078 :=
    @gN3adant1 (.classEq (.cv b) (synCpw1 (.cv y)))
      (.classEq (.cv x) (synCsn (.cv z)))
      (.imp (synWa (.classMem M (synCnnc))
          (synWa (.classMem (.cv b) M) (.classMem (.cv x) (synCcompl (.cv b)))))
        (synWrex n (synCnnc) (synWa (synWsfin M (.cv n))
            (synWsfin (synCplc M (synC1c)) (synCplc (.cv n) (.cv n))))))
      (.classEq A (synCun (.cv y) (synCsn (.cv z)))) p0077
  have p0079 :=
    @gCom12
      (synW3a (.classEq A (synCun (.cv y) (synCsn (.cv z))))
        (.classEq (.cv b) (synCpw1 (.cv y))) (.classEq (.cv x) (synCsn (.cv z))))
      (synWa (.classMem M (synCnnc))
        (synWa (.classMem (.cv b) M) (.classMem (.cv x) (synCcompl (.cv b)))))
      (synWrex n (synCnnc) (synWa (synWsfin M (.cv n))
          (synWsfin (synCplc M (synC1c)) (synCplc (.cv n) (.cv n)))))
      p0078
  have p0080 :=
    @gExlimdvv
      (synWa (.classMem M (synCnnc))
        (synWa (.classMem (.cv b) M) (.classMem (.cv x) (synCcompl (.cv b)))))
      (synW3a (.classEq A (synCun (.cv y) (synCsn (.cv z))))
        (.classEq (.cv b) (synCpw1 (.cv y))) (.classEq (.cv x) (synCsn (.cv z))))
      (synWrex n (synCnnc) (synWa (synWsfin M (.cv n))
          (synWsfin (synCplc M (synC1c)) (synCplc (.cv n) (.cv n)))))
      y z dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 p0079
  have p0081 :=
    @gSyl5bi (.classEq (synCpw1 A) (synCun (.cv b) (synCsn (.cv x))))
      (synWex y (synWex z (synW3a (.classEq A (synCun (.cv y) (synCsn (.cv z))))
            (.classEq (.cv b) (synCpw1 (.cv y))) (.classEq (.cv x) (synCsn (.cv z))))))
      (synWa (.classMem M (synCnnc))
        (synWa (.classMem (.cv b) M) (.classMem (.cv x) (synCcompl (.cv b)))))
      (synWrex n (synCnnc) (synWa (synWsfin M (.cv n))
          (synWsfin (synCplc M (synC1c)) (synCplc (.cv n) (.cv n)))))
      p0003 p0080
  have p0082 :=
    @gRexlimdvva (.classMem M (synCnnc))
      (.classEq (synCpw1 A) (synCun (.cv b) (synCsn (.cv x))))
      (synWrex n (synCnnc) (synWa (synWsfin M (.cv n))
          (synWsfin (synCplc M (synC1c)) (synCplc (.cv n) (.cv n)))))
      b x M (synCcompl (.cv b)) dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033
      dv_cache_0034 dv_cache_0004 p0081
  have p0083 :=
    @gImp (.classMem M (synCnnc))
      (synWrex b M (synWrex x (synCcompl (.cv b))
          (.classEq (synCpw1 A) (synCun (.cv b) (synCsn (.cv x))))))
      (synWrex n (synCnnc) (synWa (synWsfin M (.cv n))
          (synWsfin (synCplc M (synC1c)) (synCplc (.cv n) (.cv n)))))
      p0082
  have p0084 :=
    @gSylan2b (.classMem (synCpw1 A) (synCplc M (synC1c))) (.classMem M (synCnnc))
      (synWrex b M (synWrex x (synCcompl (.cv b))
          (.classEq (synCpw1 A) (synCun (.cv b) (synCsn (.cv x))))))
      (synWrex n (synCnnc) (synWa (synWsfin M (.cv n))
          (synWsfin (synCplc M (synC1c)) (synCplc (.cv n) (.cv n)))))
      p0000 p0083
  exact p0084


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk010Compact001Part014`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_sfintfinlem1`. -/
@[expose]
noncomputable def gSfintfinlem1 (m : Var) (n : Var) (dv_m_n : m ≠ n) :
    Nominal.NPrf
      (.classMem (.cab m (.all n (.imp (synWsfin (.cv m) (.cv n))
              (synWsfin (synCtfin (.cv m)) (synCtfin (.cv n)))))) (synCvv)) :=
  by
  let proofSupport : Finset Var := ({ m } : Finset Var) ∪ ({ n } : Finset Var)
  let t : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let x : Var := freshVar proofSupport 2
  have fresh_t : t ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_t_ne_m : t ≠ m := by
    intro h
    exact fresh_t (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))
  have fresh_t_ne_n : t ≠ n := by
    intro h
    exact fresh_t (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_n_ne_t : n ≠ t := Ne.symm fresh_t_ne_n
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_ne_m : y ≠ m := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))
  have fresh_y_ne_n : y ≠ n := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_x_ne_m : x ≠ m := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))
  have fresh_t_ne_y : t ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_t : y ≠ t := Ne.symm fresh_t_ne_y
  have fresh_t_ne_x : t ≠ x :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_x_ne_t : x ≠ t := Ne.symm fresh_t_ne_x
  have fresh_y_ne_x : y ≠ x :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_x_ne_y : x ≠ y := Ne.symm fresh_y_ne_x
  have dv_cache_0001 :
    t ∉
      ((synCcnvk (synCdif (synCsik (synCin (synCxpk (synCnnc) (synCnnc)) (synCimak
                  (synCin (synCins3k (synCimak (synCin (synCins3k (synCsik
                              (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak
                                  (synCsymdif (synCins3k (synCssetk))
                                    (synCins2k (synCsik (synCssetk))))
                                  (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                          (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))
                    (synCins2k (synCimak (synCin (synCins3k (synCsik (synCcompl (synCimak
                                  (synCsymdif (synCins3k (synCssetk))
                                    (synCins2k (synCsik (synCssetk))))
                                  (synCpw1 (synCpw1 (synC1c))))))) (synCins2k (synCssetk)))
                        (synCpw1 (synCpw1 (synC1c))))))
                  (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCimak (synCin (synCins2k
                  (synCcnvk (synCun (synCxpk (synCsn (synCsn (synC0))) (synCsn (synC0)))
                      (synCdif (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk))
                              (synCins3k (synCimak
                                  (synCdif (synCins3k (synCcnvk (synCssetk))) (synCins2k
                                      (synCimak (synCsymdif (synCins2k
        (synCin (synCxpk (synCnnc) (synCvv)) (synCimak (synCin
        (synCins2k (synCsik (synCssetk))) (synCins3k (synCimak (synCin (synCins3k
        (synCsik (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak (synCsymdif
        (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk)))) (synCpw1 (synCpw1
        (synCpw1 (synC1c)))))))) (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
        (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCins3k (synCidk)))
                                        (synCpw1 (synC1c))))) (synCpw1 (synC1c)))))
                            (synCpw1 (synCpw1 (synC1c)))))
                        (synCxpk (synCsn (synCsn (synC0))) (synCvv)))))) (synCins3k
                  (synCimak (synCin (synCins2k (synCcnvk (synCun
                            (synCxpk (synCsn (synCsn (synC0))) (synCsn (synC0))) (synCdif
                              (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk))
                                    (synCins3k (synCimak
                                        (synCdif (synCins3k (synCcnvk (synCssetk)))
        (synCins2k (synCimak (synCsymdif (synCins2k (synCin (synCxpk (synCnnc) (synCvv))
        (synCimak (synCin (synCins2k (synCsik (synCssetk))) (synCins3k (synCimak (synCin
        (synCins3k (synCsik (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak
        (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk)))) (synCpw1
        (synCpw1 (synCpw1 (synC1c)))))))) (synCins2k (synCssetk))) (synCpw1
        (synCpw1 (synC1c)))))) (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
        (synCins3k (synCidk))) (synCpw1 (synC1c))))) (synCpw1 (synC1c)))))
                                  (synCpw1 (synCpw1 (synC1c)))))
                              (synCxpk (synCsn (synCsn (synC0))) (synCvv)))))) (synCins3k
                        (synCin (synCxpk (synCnnc) (synCnnc)) (synCimak (synCin
                              (synCins3k (synCimak (synCin (synCins3k (synCsik
                                        (synCdif (synCxpk (synCpw (synC1c)) (synCvv))
        (synCimak (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk))))
        (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))) (synCins2k (synCssetk)))
                                  (synCpw1 (synCpw1 (synC1c))))) (synCins2k (synCimak
                                  (synCin (synCins3k (synCsik (synCcompl (synCimak
        (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk))))
        (synCpw1 (synCpw1 (synC1c))))))) (synCins2k (synCssetk)))
                                  (synCpw1 (synCpw1 (synC1c))))))
                            (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                    (synCpw1 (synC1c))))) (synCpw1 (synC1c)))))).fv :=
    by
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cidk, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0002 : t ∉ ((synC1c)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0003 : t ∉ ((synCsn (.cv m))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_t_ne_m,
          not_false_eq_true])
  have dv_cache_0004 : n ∉ ((Class.cv t)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_n_ne_t, not_false_eq_true])
  have dv_cache_0005 :
    n ∉
      ((Wff.classMem (synCopk (.cv t) (synCsn (.cv m))) (synCcnvk (synCdif (synCsik
                (synCin (synCxpk (synCnnc) (synCnnc)) (synCimak (synCin (synCins3k
                        (synCimak (synCin (synCins3k (synCsik
                                (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak
                                    (synCsymdif (synCins3k (synCssetk))
                                      (synCins2k (synCsik (synCssetk))))
                                    (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                            (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))
                      (synCins2k (synCimak (synCin (synCins3k (synCsik (synCcompl
                                  (synCimak (synCsymdif (synCins3k (synCssetk))
                                      (synCins2k (synCsik (synCssetk))))
                                    (synCpw1 (synCpw1 (synC1c)))))))
                            (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                    (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCimak (synCin
                  (synCins2k (synCcnvk
                      (synCun (synCxpk (synCsn (synCsn (synC0))) (synCsn (synC0)))
                        (synCdif (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk))
                                (synCins3k (synCimak
                                    (synCdif (synCins3k (synCcnvk (synCssetk))) (synCins2k
                                        (synCimak (synCsymdif (synCins2k
        (synCin (synCxpk (synCnnc) (synCvv)) (synCimak (synCin
        (synCins2k (synCsik (synCssetk))) (synCins3k (synCimak (synCin (synCins3k
        (synCsik (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak (synCsymdif
        (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk)))) (synCpw1 (synCpw1
        (synCpw1 (synC1c)))))))) (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
        (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCins3k (synCidk)))
        (synCpw1 (synC1c))))) (synCpw1 (synC1c))))) (synCpw1 (synCpw1 (synC1c)))))
                          (synCxpk (synCsn (synCsn (synC0))) (synCvv)))))) (synCins3k
                    (synCimak (synCin (synCins2k (synCcnvk (synCun
                              (synCxpk (synCsn (synCsn (synC0))) (synCsn (synC0)))
                              (synCdif (synCcompl (synCimak
                                    (synCsymdif (synCins2k (synCssetk)) (synCins3k
                                        (synCimak
        (synCdif (synCins3k (synCcnvk (synCssetk))) (synCins2k (synCimak (synCsymdif
        (synCins2k (synCin (synCxpk (synCnnc) (synCvv)) (synCimak (synCin (synCins2k
        (synCsik (synCssetk))) (synCins3k (synCimak (synCin (synCins3k (synCsik (synCdif
        (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak (synCsymdif (synCins3k
        (synCssetk)) (synCins2k (synCsik (synCssetk)))) (synCpw1 (synCpw1 (synCpw1
        (synC1c)))))))) (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))) (synCpw1
        (synCpw1 (synCpw1 (synC1c))))))) (synCins3k (synCidk))) (synCpw1 (synC1c)))))
        (synCpw1 (synC1c))))) (synCpw1 (synCpw1 (synC1c)))))
                                (synCxpk (synCsn (synCsn (synC0))) (synCvv))))))
                        (synCins3k (synCin (synCxpk (synCnnc) (synCnnc)) (synCimak
                              (synCin (synCins3k (synCimak (synCin (synCins3k (synCsik
        (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak
        (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk)))) (synCpw1
        (synCpw1 (synCpw1 (synC1c)))))))) (synCins2k (synCssetk)))
                                    (synCpw1 (synCpw1 (synC1c))))) (synCins2k (synCimak
                                    (synCin (synCins3k (synCsik (synCcompl (synCimak
        (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk))))
        (synCpw1 (synCpw1 (synC1c))))))) (synCins2k (synCssetk)))
                                    (synCpw1 (synCpw1 (synC1c))))))
                              (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                      (synCpw1 (synC1c))))) (synCpw1 (synC1c))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cidk, Finset.mem_union,
          Finset.mem_singleton, fresh_n_ne_t, (Ne.symm dv_m_n), compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0006 : t ∉ ((synCsn (.cv n))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_t_ne_n,
          not_false_eq_true])
  have dv_cache_0007 :
    t ∉
      ((Wff.classMem (synCopk (synCsn (.cv n)) (synCsn (.cv m))) (synCcnvk (synCdif
              (synCsik (synCin (synCxpk (synCnnc) (synCnnc)) (synCimak (synCin
                      (synCins3k (synCimak (synCin (synCins3k (synCsik
                                (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak
                                    (synCsymdif (synCins3k (synCssetk))
                                      (synCins2k (synCsik (synCssetk))))
                                    (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                            (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))
                      (synCins2k (synCimak (synCin (synCins3k (synCsik (synCcompl
                                  (synCimak (synCsymdif (synCins3k (synCssetk))
                                      (synCins2k (synCsik (synCssetk))))
                                    (synCpw1 (synCpw1 (synC1c)))))))
                            (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                    (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCimak (synCin
                  (synCins2k (synCcnvk
                      (synCun (synCxpk (synCsn (synCsn (synC0))) (synCsn (synC0)))
                        (synCdif (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk))
                                (synCins3k (synCimak
                                    (synCdif (synCins3k (synCcnvk (synCssetk))) (synCins2k
                                        (synCimak (synCsymdif (synCins2k
        (synCin (synCxpk (synCnnc) (synCvv)) (synCimak (synCin
        (synCins2k (synCsik (synCssetk))) (synCins3k (synCimak (synCin (synCins3k
        (synCsik (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak (synCsymdif
        (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk)))) (synCpw1 (synCpw1
        (synCpw1 (synC1c)))))))) (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
        (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCins3k (synCidk)))
        (synCpw1 (synC1c))))) (synCpw1 (synC1c))))) (synCpw1 (synCpw1 (synC1c)))))
                          (synCxpk (synCsn (synCsn (synC0))) (synCvv)))))) (synCins3k
                    (synCimak (synCin (synCins2k (synCcnvk (synCun
                              (synCxpk (synCsn (synCsn (synC0))) (synCsn (synC0)))
                              (synCdif (synCcompl (synCimak
                                    (synCsymdif (synCins2k (synCssetk)) (synCins3k
                                        (synCimak
        (synCdif (synCins3k (synCcnvk (synCssetk))) (synCins2k (synCimak (synCsymdif
        (synCins2k (synCin (synCxpk (synCnnc) (synCvv)) (synCimak (synCin (synCins2k
        (synCsik (synCssetk))) (synCins3k (synCimak (synCin (synCins3k (synCsik (synCdif
        (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak (synCsymdif (synCins3k
        (synCssetk)) (synCins2k (synCsik (synCssetk)))) (synCpw1 (synCpw1 (synCpw1
        (synC1c)))))))) (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))) (synCpw1
        (synCpw1 (synCpw1 (synC1c))))))) (synCins3k (synCidk))) (synCpw1 (synC1c)))))
        (synCpw1 (synC1c))))) (synCpw1 (synCpw1 (synC1c)))))
                                (synCxpk (synCsn (synCsn (synC0))) (synCvv))))))
                        (synCins3k (synCin (synCxpk (synCnnc) (synCnnc)) (synCimak
                              (synCin (synCins3k (synCimak (synCin (synCins3k (synCsik
        (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak
        (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk)))) (synCpw1
        (synCpw1 (synCpw1 (synC1c)))))))) (synCins2k (synCssetk)))
                                    (synCpw1 (synCpw1 (synC1c))))) (synCins2k (synCimak
                                    (synCin (synCins3k (synCsik (synCcompl (synCimak
        (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk))))
        (synCpw1 (synCpw1 (synC1c))))))) (synCins2k (synCssetk)))
                                    (synCpw1 (synCpw1 (synC1c))))))
                              (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                      (synCpw1 (synC1c))))) (synCpw1 (synC1c))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cidk, Finset.mem_union,
          Finset.mem_singleton, fresh_t_ne_n, fresh_t_ne_m, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0008 :
    t ∉
      ((synCin (synCins2k (synCcnvk
              (synCun (synCxpk (synCsn (synCsn (synC0))) (synCsn (synC0))) (synCdif
                  (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk)) (synCins3k
                          (synCimak (synCdif (synCins3k (synCcnvk (synCssetk))) (synCins2k
                                (synCimak (synCsymdif (synCins2k
                                      (synCin (synCxpk (synCnnc) (synCvv)) (synCimak
        (synCin (synCins2k (synCsik (synCssetk))) (synCins3k (synCimak (synCin
        (synCins3k (synCsik (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak
        (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk)))) (synCpw1
        (synCpw1 (synCpw1 (synC1c)))))))) (synCins2k (synCssetk)))
        (synCpw1 (synCpw1 (synC1c)))))) (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                                    (synCins3k (synCidk))) (synCpw1 (synC1c)))))
                            (synCpw1 (synC1c))))) (synCpw1 (synCpw1 (synC1c)))))
                  (synCxpk (synCsn (synCsn (synC0))) (synCvv)))))) (synCins3k (synCimak
              (synCin (synCins2k (synCcnvk
                    (synCun (synCxpk (synCsn (synCsn (synC0))) (synCsn (synC0)))
                      (synCdif (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk))
                              (synCins3k (synCimak
                                  (synCdif (synCins3k (synCcnvk (synCssetk))) (synCins2k
                                      (synCimak (synCsymdif (synCins2k
        (synCin (synCxpk (synCnnc) (synCvv)) (synCimak (synCin
        (synCins2k (synCsik (synCssetk))) (synCins3k (synCimak (synCin (synCins3k
        (synCsik (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak (synCsymdif
        (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk)))) (synCpw1 (synCpw1
        (synCpw1 (synC1c)))))))) (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
        (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCins3k (synCidk)))
                                        (synCpw1 (synC1c))))) (synCpw1 (synC1c)))))
                            (synCpw1 (synCpw1 (synC1c)))))
                        (synCxpk (synCsn (synCsn (synC0))) (synCvv)))))) (synCins3k
                  (synCin (synCxpk (synCnnc) (synCnnc)) (synCimak (synCin (synCins3k
                          (synCimak (synCin (synCins3k (synCsik
                                  (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak
                                      (synCsymdif (synCins3k (synCssetk))
                                        (synCins2k (synCsik (synCssetk))))
                                      (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                              (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))
                        (synCins2k (synCimak (synCin (synCins3k (synCsik (synCcompl
                                    (synCimak (synCsymdif (synCins3k (synCssetk))
                                        (synCins2k (synCsik (synCssetk))))
                                      (synCpw1 (synCpw1 (synC1c)))))))
                              (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                      (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
              (synCpw1 (synC1c)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cidk, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0009 : t ∉ ((synCpw1 (synC1c))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, compact_fv_not_mem_empty,
          not_false_eq_true])
  have dv_cache_0010 : t ∉ ((synCopk (synCsn (.cv m)) (synCsn (.cv n)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_t_ne_m, fresh_t_ne_n, or_false, not_false_eq_true])
  have dv_cache_0011 : y ∉ ((Class.cv t)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_y_ne_t, not_false_eq_true])
  have dv_cache_0012 :
    y ∉
      ((Wff.classMem (synCopk (.cv t) (synCopk (synCsn (.cv m)) (synCsn (.cv n)))) (synCin
            (synCins2k (synCcnvk
                (synCun (synCxpk (synCsn (synCsn (synC0))) (synCsn (synC0))) (synCdif
                    (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk)) (synCins3k
                            (synCimak (synCdif (synCins3k (synCcnvk (synCssetk)))
                                (synCins2k (synCimak (synCsymdif (synCins2k
                                        (synCin (synCxpk (synCnnc) (synCvv)) (synCimak
        (synCin (synCins2k (synCsik (synCssetk))) (synCins3k (synCimak (synCin
        (synCins3k (synCsik (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak
        (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk)))) (synCpw1
        (synCpw1 (synCpw1 (synC1c)))))))) (synCins2k (synCssetk)))
        (synCpw1 (synCpw1 (synC1c)))))) (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                                      (synCins3k (synCidk))) (synCpw1 (synC1c)))))
                              (synCpw1 (synC1c))))) (synCpw1 (synCpw1 (synC1c)))))
                    (synCxpk (synCsn (synCsn (synC0))) (synCvv)))))) (synCins3k (synCimak
                (synCin (synCins2k (synCcnvk
                      (synCun (synCxpk (synCsn (synCsn (synC0))) (synCsn (synC0)))
                        (synCdif (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk))
                                (synCins3k (synCimak
                                    (synCdif (synCins3k (synCcnvk (synCssetk))) (synCins2k
                                        (synCimak (synCsymdif (synCins2k
        (synCin (synCxpk (synCnnc) (synCvv)) (synCimak (synCin
        (synCins2k (synCsik (synCssetk))) (synCins3k (synCimak (synCin (synCins3k
        (synCsik (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak (synCsymdif
        (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk)))) (synCpw1 (synCpw1
        (synCpw1 (synC1c)))))))) (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
        (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCins3k (synCidk)))
        (synCpw1 (synC1c))))) (synCpw1 (synC1c))))) (synCpw1 (synCpw1 (synC1c)))))
                          (synCxpk (synCsn (synCsn (synC0))) (synCvv)))))) (synCins3k
                    (synCin (synCxpk (synCnnc) (synCnnc)) (synCimak (synCin (synCins3k
                            (synCimak (synCin (synCins3k (synCsik
                                    (synCdif (synCxpk (synCpw (synC1c)) (synCvv))
                                      (synCimak (synCsymdif (synCins3k (synCssetk))
        (synCins2k (synCsik (synCssetk)))) (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                                (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))
                          (synCins2k (synCimak (synCin (synCins3k (synCsik (synCcompl
                                      (synCimak (synCsymdif (synCins3k (synCssetk))
        (synCins2k (synCsik (synCssetk)))) (synCpw1 (synCpw1 (synC1c)))))))
                                (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                        (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                (synCpw1 (synC1c))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cidk, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_t, fresh_y_ne_m, fresh_y_ne_n,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0013 : t ∉ ((synCsn (synCsn (.cv y)))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_t_ne_y,
          not_false_eq_true])
  have dv_cache_0014 :
    t ∉
      ((Wff.classMem (synCopk (synCsn (synCsn (.cv y)))
            (synCopk (synCsn (.cv m)) (synCsn (.cv n)))) (synCin (synCins2k (synCcnvk
                (synCun (synCxpk (synCsn (synCsn (synC0))) (synCsn (synC0))) (synCdif
                    (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk)) (synCins3k
                            (synCimak (synCdif (synCins3k (synCcnvk (synCssetk)))
                                (synCins2k (synCimak (synCsymdif (synCins2k
                                        (synCin (synCxpk (synCnnc) (synCvv)) (synCimak
        (synCin (synCins2k (synCsik (synCssetk))) (synCins3k (synCimak (synCin
        (synCins3k (synCsik (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak
        (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk)))) (synCpw1
        (synCpw1 (synCpw1 (synC1c)))))))) (synCins2k (synCssetk)))
        (synCpw1 (synCpw1 (synC1c)))))) (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                                      (synCins3k (synCidk))) (synCpw1 (synC1c)))))
                              (synCpw1 (synC1c))))) (synCpw1 (synCpw1 (synC1c)))))
                    (synCxpk (synCsn (synCsn (synC0))) (synCvv)))))) (synCins3k (synCimak
                (synCin (synCins2k (synCcnvk
                      (synCun (synCxpk (synCsn (synCsn (synC0))) (synCsn (synC0)))
                        (synCdif (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk))
                                (synCins3k (synCimak
                                    (synCdif (synCins3k (synCcnvk (synCssetk))) (synCins2k
                                        (synCimak (synCsymdif (synCins2k
        (synCin (synCxpk (synCnnc) (synCvv)) (synCimak (synCin
        (synCins2k (synCsik (synCssetk))) (synCins3k (synCimak (synCin (synCins3k
        (synCsik (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak (synCsymdif
        (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk)))) (synCpw1 (synCpw1
        (synCpw1 (synC1c)))))))) (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
        (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCins3k (synCidk)))
        (synCpw1 (synC1c))))) (synCpw1 (synC1c))))) (synCpw1 (synCpw1 (synC1c)))))
                          (synCxpk (synCsn (synCsn (synC0))) (synCvv)))))) (synCins3k
                    (synCin (synCxpk (synCnnc) (synCnnc)) (synCimak (synCin (synCins3k
                            (synCimak (synCin (synCins3k (synCsik
                                    (synCdif (synCxpk (synCpw (synC1c)) (synCvv))
                                      (synCimak (synCsymdif (synCins3k (synCssetk))
        (synCins2k (synCsik (synCssetk)))) (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                                (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))
                          (synCins2k (synCimak (synCin (synCins3k (synCsik (synCcompl
                                      (synCimak (synCsymdif (synCins3k (synCssetk))
        (synCins2k (synCsik (synCssetk)))) (synCpw1 (synCpw1 (synC1c)))))))
                                (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                        (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                (synCpw1 (synC1c))))))).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cidk, Finset.mem_union,
          Finset.mem_singleton, fresh_t_ne_y, fresh_t_ne_m, fresh_t_ne_n,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0015 :
    t ∉
      ((synCin (synCins2k (synCcnvk
              (synCun (synCxpk (synCsn (synCsn (synC0))) (synCsn (synC0))) (synCdif
                  (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk)) (synCins3k
                          (synCimak (synCdif (synCins3k (synCcnvk (synCssetk))) (synCins2k
                                (synCimak (synCsymdif (synCins2k
                                      (synCin (synCxpk (synCnnc) (synCvv)) (synCimak
        (synCin (synCins2k (synCsik (synCssetk))) (synCins3k (synCimak (synCin
        (synCins3k (synCsik (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak
        (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk)))) (synCpw1
        (synCpw1 (synCpw1 (synC1c)))))))) (synCins2k (synCssetk)))
        (synCpw1 (synCpw1 (synC1c)))))) (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                                    (synCins3k (synCidk))) (synCpw1 (synC1c)))))
                            (synCpw1 (synC1c))))) (synCpw1 (synCpw1 (synC1c)))))
                  (synCxpk (synCsn (synCsn (synC0))) (synCvv)))))) (synCins3k
            (synCin (synCxpk (synCnnc) (synCnnc)) (synCimak (synCin (synCins3k (synCimak
                      (synCin (synCins3k (synCsik
                            (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak
                                (synCsymdif (synCins3k (synCssetk))
                                  (synCins2k (synCsik (synCssetk))))
                                (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                        (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))) (synCins2k
                    (synCimak (synCin (synCins3k (synCsik (synCcompl (synCimak
                                (synCsymdif (synCins3k (synCssetk))
                                  (synCins2k (synCsik (synCssetk))))
                                (synCpw1 (synCpw1 (synC1c))))))) (synCins2k (synCssetk)))
                      (synCpw1 (synCpw1 (synC1c))))))
                (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cidk, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0016 : t ∉ ((synCopk (.cv y) (synCsn (.cv m)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
          Finset.mem_singleton, fresh_t_ne_y, fresh_t_ne_m, or_false, not_false_eq_true])
  have dv_cache_0017 : x ∉ ((Class.cv t)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_x_ne_t, not_false_eq_true])
  have dv_cache_0018 :
    x ∉
      ((Wff.classMem (synCopk (.cv t) (synCopk (.cv y) (synCsn (.cv m)))) (synCin
            (synCins2k (synCcnvk
                (synCun (synCxpk (synCsn (synCsn (synC0))) (synCsn (synC0))) (synCdif
                    (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk)) (synCins3k
                            (synCimak (synCdif (synCins3k (synCcnvk (synCssetk)))
                                (synCins2k (synCimak (synCsymdif (synCins2k
                                        (synCin (synCxpk (synCnnc) (synCvv)) (synCimak
        (synCin (synCins2k (synCsik (synCssetk))) (synCins3k (synCimak (synCin
        (synCins3k (synCsik (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak
        (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk)))) (synCpw1
        (synCpw1 (synCpw1 (synC1c)))))))) (synCins2k (synCssetk)))
        (synCpw1 (synCpw1 (synC1c)))))) (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                                      (synCins3k (synCidk))) (synCpw1 (synC1c)))))
                              (synCpw1 (synC1c))))) (synCpw1 (synCpw1 (synC1c)))))
                    (synCxpk (synCsn (synCsn (synC0))) (synCvv)))))) (synCins3k
              (synCin (synCxpk (synCnnc) (synCnnc)) (synCimak (synCin (synCins3k
                      (synCimak (synCin (synCins3k (synCsik
                              (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak
                                  (synCsymdif (synCins3k (synCssetk))
                                    (synCins2k (synCsik (synCssetk))))
                                  (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                          (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))
                    (synCins2k (synCimak (synCin (synCins3k (synCsik (synCcompl (synCimak
                                  (synCsymdif (synCins3k (synCssetk))
                                    (synCins2k (synCsik (synCssetk))))
                                  (synCpw1 (synCpw1 (synC1c))))))) (synCins2k (synCssetk)))
                        (synCpw1 (synCpw1 (synC1c))))))
                  (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))))).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cidk, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_t, fresh_x_ne_y, fresh_x_ne_m,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0019 : t ∉ ((synCsn (synCsn (.cv x)))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_t_ne_x,
          not_false_eq_true])
  have dv_cache_0020 :
    t ∉
      ((Wff.classMem (synCopk (synCsn (synCsn (.cv x))) (synCopk (.cv y) (synCsn (.cv m))))
          (synCin (synCins2k (synCcnvk
                (synCun (synCxpk (synCsn (synCsn (synC0))) (synCsn (synC0))) (synCdif
                    (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk)) (synCins3k
                            (synCimak (synCdif (synCins3k (synCcnvk (synCssetk)))
                                (synCins2k (synCimak (synCsymdif (synCins2k
                                        (synCin (synCxpk (synCnnc) (synCvv)) (synCimak
        (synCin (synCins2k (synCsik (synCssetk))) (synCins3k (synCimak (synCin
        (synCins3k (synCsik (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak
        (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk)))) (synCpw1
        (synCpw1 (synCpw1 (synC1c)))))))) (synCins2k (synCssetk)))
        (synCpw1 (synCpw1 (synC1c)))))) (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                                      (synCins3k (synCidk))) (synCpw1 (synC1c)))))
                              (synCpw1 (synC1c))))) (synCpw1 (synCpw1 (synC1c)))))
                    (synCxpk (synCsn (synCsn (synC0))) (synCvv)))))) (synCins3k
              (synCin (synCxpk (synCnnc) (synCnnc)) (synCimak (synCin (synCins3k
                      (synCimak (synCin (synCins3k (synCsik
                              (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak
                                  (synCsymdif (synCins3k (synCssetk))
                                    (synCins2k (synCsik (synCssetk))))
                                  (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                          (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))
                    (synCins2k (synCimak (synCin (synCins3k (synCsik (synCcompl (synCimak
                                  (synCsymdif (synCins3k (synCssetk))
                                    (synCins2k (synCsik (synCssetk))))
                                  (synCpw1 (synCpw1 (synC1c))))))) (synCins2k (synCssetk)))
                        (synCpw1 (synCpw1 (synC1c))))))
                  (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))))).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cidk, Finset.mem_union,
          Finset.mem_singleton, fresh_t_ne_x, fresh_t_ne_y, fresh_t_ne_m,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0021 : x ∉ ((synCtfin (.cv m))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_x_ne_m,
          not_false_eq_true])
  have dv_cache_0022 : x ∉ ((synWsfin (synCtfin (.cv m)) (.cv y))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wsfin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_m, fresh_x_ne_y, or_false, not_false_eq_true])
  have dv_cache_0023 : y ∉ ((synCtfin (.cv n))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_y_ne_n,
          not_false_eq_true])
  have dv_cache_0024 : y ∉ ((synWsfin (synCtfin (.cv m)) (synCtfin (.cv n)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wsfin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_m, fresh_y_ne_n, or_false, not_false_eq_true])
  have dv_cache_0025 :
    m ∉
      ((synCuni1 (synCcompl (synCimak (synCcnvk (synCdif (synCsik
                    (synCin (synCxpk (synCnnc) (synCnnc)) (synCimak (synCin (synCins3k
                            (synCimak (synCin (synCins3k (synCsik
                                    (synCdif (synCxpk (synCpw (synC1c)) (synCvv))
                                      (synCimak (synCsymdif (synCins3k (synCssetk))
        (synCins2k (synCsik (synCssetk)))) (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                                (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))
                          (synCins2k (synCimak (synCin (synCins3k (synCsik (synCcompl
                                      (synCimak (synCsymdif (synCins3k (synCssetk))
        (synCins2k (synCsik (synCssetk)))) (synCpw1 (synCpw1 (synC1c)))))))
                                (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                        (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCimak (synCin
                      (synCins2k (synCcnvk (synCun
                            (synCxpk (synCsn (synCsn (synC0))) (synCsn (synC0))) (synCdif
                              (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk))
                                    (synCins3k (synCimak
                                        (synCdif (synCins3k (synCcnvk (synCssetk)))
        (synCins2k (synCimak (synCsymdif (synCins2k (synCin (synCxpk (synCnnc) (synCvv))
        (synCimak (synCin (synCins2k (synCsik (synCssetk))) (synCins3k (synCimak (synCin
        (synCins3k (synCsik (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak
        (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk)))) (synCpw1
        (synCpw1 (synCpw1 (synC1c)))))))) (synCins2k (synCssetk))) (synCpw1
        (synCpw1 (synC1c)))))) (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
        (synCins3k (synCidk))) (synCpw1 (synC1c))))) (synCpw1 (synC1c)))))
                                  (synCpw1 (synCpw1 (synC1c)))))
                              (synCxpk (synCsn (synCsn (synC0))) (synCvv)))))) (synCins3k
                        (synCimak (synCin (synCins2k (synCcnvk (synCun
                                  (synCxpk (synCsn (synCsn (synC0))) (synCsn (synC0)))
                                  (synCdif (synCcompl (synCimak
                                        (synCsymdif (synCins2k (synCssetk)) (synCins3k
        (synCimak (synCdif (synCins3k (synCcnvk (synCssetk))) (synCins2k (synCimak
        (synCsymdif (synCins2k (synCin (synCxpk (synCnnc) (synCvv)) (synCimak (synCin
        (synCins2k (synCsik (synCssetk))) (synCins3k (synCimak (synCin (synCins3k
        (synCsik (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak (synCsymdif
        (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk)))) (synCpw1 (synCpw1
        (synCpw1 (synC1c)))))))) (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
        (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCins3k (synCidk)))
        (synCpw1 (synC1c))))) (synCpw1 (synC1c))))) (synCpw1 (synCpw1 (synC1c)))))
                                    (synCxpk (synCsn (synCsn (synC0))) (synCvv))))))
                            (synCins3k (synCin (synCxpk (synCnnc) (synCnnc)) (synCimak
                                  (synCin (synCins3k (synCimak (synCin (synCins3k (synCsik
        (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak
        (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk)))) (synCpw1
        (synCpw1 (synCpw1 (synC1c)))))))) (synCins2k (synCssetk)))
                                        (synCpw1 (synCpw1 (synC1c))))) (synCins2k (synCimak
                                        (synCin (synCins3k (synCsik (synCcompl (synCimak
        (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk))))
        (synCpw1 (synCpw1 (synC1c))))))) (synCins2k (synCssetk)))
                                        (synCpw1 (synCpw1 (synC1c))))))
                                  (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                          (synCpw1 (synC1c))))) (synCpw1 (synC1c))))) (synC1c))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024
    exact
      (by
        have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cidk, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  let syntaxClass0000 : Class :=
    (synCimak (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk))))
      (synCpw1 (synCpw1 (synCpw1 (synC1c)))))
  let syntaxClass0001 : Class :=
    (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) syntaxClass0000)
  let syntaxClass0002 : Class := (synCsik syntaxClass0001)
  let syntaxClass0003 : Class := (synCins3k syntaxClass0002)
  let syntaxClass0004 : Class := (synCin syntaxClass0003 (synCins2k (synCssetk)))
  let syntaxClass0005 : Class :=
    (synCimak syntaxClass0004 (synCpw1 (synCpw1 (synC1c))))
  let syntaxClass0006 : Class := (synCins3k syntaxClass0005)
  let syntaxClass0007 : Class :=
    (synCimak (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk))))
      (synCpw1 (synCpw1 (synC1c))))
  let syntaxClass0008 : Class := (synCcompl syntaxClass0007)
  let syntaxClass0009 : Class := (synCsik syntaxClass0008)
  let syntaxClass0010 : Class := (synCins3k syntaxClass0009)
  let syntaxClass0011 : Class := (synCin syntaxClass0010 (synCins2k (synCssetk)))
  let syntaxClass0012 : Class :=
    (synCimak syntaxClass0011 (synCpw1 (synCpw1 (synC1c))))
  let syntaxClass0013 : Class := (synCins2k syntaxClass0012)
  let syntaxClass0014 : Class := (synCin syntaxClass0006 syntaxClass0013)
  let syntaxClass0015 : Class :=
    (synCimak syntaxClass0014 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))
  let syntaxClass0016 : Class :=
    (synCin (synCxpk (synCnnc) (synCnnc)) syntaxClass0015)
  let syntaxClass0017 : Class := (synCsik syntaxClass0016)
  let syntaxClass0018 : Class :=
    (synCin (synCins2k (synCsik (synCssetk))) syntaxClass0006)
  let syntaxClass0019 : Class :=
    (synCimak syntaxClass0018 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))
  let syntaxClass0020 : Class := (synCin (synCxpk (synCnnc) (synCvv)) syntaxClass0019)
  let syntaxClass0021 : Class := (synCins2k syntaxClass0020)
  let syntaxClass0022 : Class := (synCsymdif syntaxClass0021 (synCins3k (synCidk)))
  let syntaxClass0023 : Class := (synCimak syntaxClass0022 (synCpw1 (synC1c)))
  let syntaxClass0024 : Class := (synCins2k syntaxClass0023)
  let syntaxClass0025 : Class :=
    (synCdif (synCins3k (synCcnvk (synCssetk))) syntaxClass0024)
  let syntaxClass0026 : Class := (synCimak syntaxClass0025 (synCpw1 (synC1c)))
  let syntaxClass0027 : Class := (synCins3k syntaxClass0026)
  let syntaxClass0028 : Class := (synCsymdif (synCins2k (synCssetk)) syntaxClass0027)
  let syntaxClass0029 : Class :=
    (synCimak syntaxClass0028 (synCpw1 (synCpw1 (synC1c))))
  let syntaxClass0030 : Class := (synCcompl syntaxClass0029)
  let syntaxClass0031 : Class :=
    (synCdif syntaxClass0030 (synCxpk (synCsn (synCsn (synC0))) (synCvv)))
  let syntaxClass0032 : Class :=
    (synCun (synCxpk (synCsn (synCsn (synC0))) (synCsn (synC0))) syntaxClass0031)
  let syntaxClass0033 : Class := (synCcnvk syntaxClass0032)
  let syntaxClass0034 : Class := (synCins2k syntaxClass0033)
  let syntaxClass0035 : Class := (synCins3k syntaxClass0016)
  let syntaxClass0036 : Class := (synCin syntaxClass0034 syntaxClass0035)
  let syntaxClass0037 : Class := (synCimak syntaxClass0036 (synCpw1 (synC1c)))
  let syntaxClass0038 : Class := (synCins3k syntaxClass0037)
  let syntaxClass0039 : Class := (synCin syntaxClass0034 syntaxClass0038)
  let syntaxClass0040 : Class := (synCimak syntaxClass0039 (synCpw1 (synC1c)))
  let syntaxClass0041 : Class := (synCdif syntaxClass0017 syntaxClass0040)
  let syntaxClass0042 : Class := (synCcnvk syntaxClass0041)
  let syntaxClass0043 : Class := (synCimak syntaxClass0042 (synC1c))
  let syntaxClass0044 : Class := (synCcompl syntaxClass0043)
  let syntaxFormula0045 : Wff :=
    (.classMem (synCopk (.cv t) (synCsn (.cv m))) syntaxClass0042)
  let syntaxFormula0046 : Wff := (synWa (.classMem (.cv t) (synC1c)) syntaxFormula0045)
  let syntaxFormula0047 : Wff :=
    (synWa (.classEq (.cv t) (synCsn (.cv n))) syntaxFormula0045)
  let syntaxFormula0048 : Wff := (synWex n syntaxFormula0047)
  let syntaxFormula0049 : Wff := (synWrex t (synC1c) syntaxFormula0045)
  let syntaxFormula0050 : Wff := (synWex t syntaxFormula0047)
  let syntaxFormula0051 : Wff := (synWex n syntaxFormula0050)
  let syntaxFormula0052 : Wff :=
    (.classMem (synCopk (synCsn (.cv n)) (synCsn (.cv m))) syntaxClass0042)
  let syntaxFormula0053 : Wff :=
    (.classMem (synCopk (synCsn (.cv m)) (synCsn (.cv n))) syntaxClass0017)
  let syntaxFormula0054 : Wff :=
    (.classMem (synCopk (.cv t) (synCopk (synCsn (.cv m)) (synCsn (.cv n))))
      syntaxClass0039)
  let syntaxFormula0055 : Wff := (synWrex t (synCpw1 (synC1c)) syntaxFormula0054)
  let syntaxFormula0056 : Wff :=
    (synWa (.classMem (.cv t) (synCpw1 (synC1c))) syntaxFormula0054)
  let syntaxFormula0057 : Wff :=
    (synWa (.classEq (.cv t) (synCsn (synCsn (.cv y)))) syntaxFormula0054)
  let syntaxFormula0058 : Wff := (synWex y syntaxFormula0057)
  let syntaxFormula0059 : Wff := (synWex t syntaxFormula0056)
  let syntaxFormula0060 : Wff := (synWex t syntaxFormula0057)
  let syntaxFormula0061 : Wff := (synWex y syntaxFormula0060)
  let syntaxFormula0062 : Wff :=
    (.classMem (synCopk (synCsn (.cv m)) (synCsn (.cv n))) syntaxClass0040)
  let syntaxClass0063 : Class :=
    (synCopk (synCsn (synCsn (.cv y))) (synCopk (synCsn (.cv m)) (synCsn (.cv n))))
  let syntaxFormula0064 : Wff := (.classMem syntaxClass0063 syntaxClass0039)
  let syntaxFormula0065 : Wff := (.classMem syntaxClass0063 syntaxClass0034)
  let syntaxFormula0066 : Wff :=
    (.classMem (synCopk (.cv t) (synCopk (.cv y) (synCsn (.cv m)))) syntaxClass0036)
  let syntaxFormula0067 : Wff :=
    (synWa (.classMem (.cv t) (synCpw1 (synC1c))) syntaxFormula0066)
  let syntaxFormula0068 : Wff :=
    (synWa (.classEq (.cv t) (synCsn (synCsn (.cv x)))) syntaxFormula0066)
  let syntaxFormula0069 : Wff := (synWex x syntaxFormula0068)
  let syntaxFormula0070 : Wff := (synWrex t (synCpw1 (synC1c)) syntaxFormula0066)
  let syntaxFormula0071 : Wff := (synWex t syntaxFormula0068)
  let syntaxFormula0072 : Wff := (synWex x syntaxFormula0071)
  let syntaxFormula0073 : Wff :=
    (.classMem (synCopk (synCsn (synCsn (.cv x))) (synCopk (.cv y) (synCsn (.cv m))))
      syntaxClass0036)
  let syntaxFormula0074 : Wff :=
    (.classMem (synCopk (synCsn (synCsn (.cv x))) (synCopk (.cv y) (synCsn (.cv m))))
      syntaxClass0034)
  let syntaxFormula0075 : Wff :=
    (.classMem (synCopk (synCsn (synCsn (.cv x))) (synCopk (.cv y) (synCsn (.cv m))))
      syntaxClass0035)
  let syntaxFormula0076 : Wff :=
    (.classMem (synCopk (.cv y) (synCsn (.cv m))) syntaxClass0037)
  let syntaxFormula0077 : Wff := (.classMem syntaxClass0063 syntaxClass0038)
  let syntaxFormula0078 : Wff := (.neg syntaxFormula0062)
  let syntaxFormula0079 : Wff :=
    (.classMem (synCopk (synCsn (.cv m)) (synCsn (.cv n))) syntaxClass0041)
  let syntaxFormula0080 : Wff :=
    (.imp (synWsfin (.cv m) (.cv n)) (synWsfin (synCtfin (.cv m)) (synCtfin (.cv n))))
  let syntaxFormula0081 : Wff := (.neg syntaxFormula0080)
  let syntaxFormula0082 : Wff := (.classMem (synCsn (.cv m)) syntaxClass0043)
  let syntaxFormula0083 : Wff := (synWex n syntaxFormula0081)
  let syntaxFormula0084 : Wff := (.classMem (synCsn (.cv m)) syntaxClass0044)
  let syntaxFormula0085 : Wff := (.all n syntaxFormula0080)
  let syntaxClass0086 : Class := (synCuni1 syntaxClass0044)
  have p0000 := @gVex m
  have p0001 := @gEluni1 (.cv m) syntaxClass0044 p0000
  have p0002 := @gSnex (.cv m)
  have p0003 :=
    @gElimak t syntaxClass0042 (synC1c) (synCsn (.cv m)) dv_cache_0001 dv_cache_0002
      dv_cache_0003 p0002
  have p0004 := @gEl1c n (.cv t) dv_cache_0004
  have p0005 :=
    @gAnbi1i (.classMem (.cv t) (synC1c))
      (synWex n (.classEq (.cv t) (synCsn (.cv n)))) syntaxFormula0045 p0004
  have p0006 :=
    @gN1941v (.classEq (.cv t) (synCsn (.cv n))) syntaxFormula0045 n dv_cache_0005
  have p0007 :=
    @gBitr4i syntaxFormula0046
      (synWa (synWex n (.classEq (.cv t) (synCsn (.cv n)))) syntaxFormula0045)
      syntaxFormula0048 p0005 p0006
  have p0008 := @gExbii syntaxFormula0046 syntaxFormula0048 t p0007
  have p0009 := (Nominal.biimpRefl syntaxFormula0049)
  have p0010 := @gExcom syntaxFormula0047 n t
  have p0011 :=
    @gN3bitr4i (synWex t syntaxFormula0046) (synWex t syntaxFormula0048)
      syntaxFormula0049 syntaxFormula0051 p0008 p0009 p0010
  have p0012 := @gSnex (.cv n)
  have p0013 := @gOpkeq1 (.cv t) (synCsn (.cv n)) (synCsn (.cv m))
  have p0014 :=
    @gEleq1d (.classEq (.cv t) (synCsn (.cv n))) (synCopk (.cv t) (synCsn (.cv m)))
      (synCopk (synCsn (.cv n)) (synCsn (.cv m))) syntaxClass0042 p0013
  have p0015 :=
    @gCeqsexv syntaxFormula0045 syntaxFormula0052 t (synCsn (.cv n)) dv_cache_0006
      dv_cache_0007 p0012 p0014
  have p0016 :=
    @gOpkelcnvk (synCsn (.cv n)) (synCsn (.cv m)) syntaxClass0041 p0012 p0002
  have p0017 :=
    @gEldif (synCopk (synCsn (.cv m)) (synCsn (.cv n))) syntaxClass0017
      syntaxClass0040
  have p0018 := @gVex n
  have p0019 := @gOpksnelsik (.cv m) (.cv n) syntaxClass0016 p0000 p0018
  have p0020 := @gSrelk (.cv m) (.cv n) p0000 p0018
  have p0021 :=
    @gBitri syntaxFormula0053 (.classMem (synCopk (.cv m) (.cv n)) syntaxClass0016)
      (synWsfin (.cv m) (.cv n)) p0019 p0020
  have p0022 := @gOpkex (synCsn (.cv m)) (synCsn (.cv n))
  have p0023 :=
    @gElimak t syntaxClass0039 (synCpw1 (synC1c))
      (synCopk (synCsn (.cv m)) (synCsn (.cv n))) dv_cache_0008 dv_cache_0009
      dv_cache_0010 p0022
  have p0024 := (Nominal.biimpRefl syntaxFormula0055)
  have p0025 := @gElpw11c y (.cv t) dv_cache_0011
  have p0026 :=
    @gAnbi1i (.classMem (.cv t) (synCpw1 (synC1c)))
      (synWex y (.classEq (.cv t) (synCsn (synCsn (.cv y))))) syntaxFormula0054 p0025
  have p0027 :=
    @gN1941v (.classEq (.cv t) (synCsn (synCsn (.cv y)))) syntaxFormula0054 y
      dv_cache_0012
  have p0028 :=
    @gBitr4i syntaxFormula0056
      (synWa (synWex y (.classEq (.cv t) (synCsn (synCsn (.cv y))))) syntaxFormula0054)
      syntaxFormula0058 p0026 p0027
  have p0029 := @gExbii syntaxFormula0056 syntaxFormula0058 t p0028
  have p0030 := @gExcom syntaxFormula0057 y t
  have p0031 :=
    @gBitr4i syntaxFormula0059 (synWex t syntaxFormula0058) syntaxFormula0061 p0029
      p0030
  have p0032 :=
    @gN3bitri syntaxFormula0062 syntaxFormula0055 syntaxFormula0059 syntaxFormula0061
      p0023 p0024 p0031
  have p0033 := @gSnex (synCsn (.cv y))
  have p0034 :=
    @gOpkeq1 (.cv t) (synCsn (synCsn (.cv y)))
      (synCopk (synCsn (.cv m)) (synCsn (.cv n)))
  have p0035 :=
    @gEleq1d (.classEq (.cv t) (synCsn (synCsn (.cv y))))
      (synCopk (.cv t) (synCopk (synCsn (.cv m)) (synCsn (.cv n)))) syntaxClass0063
      syntaxClass0039 p0034
  have p0036 :=
    @gCeqsexv syntaxFormula0054 syntaxFormula0064 t (synCsn (synCsn (.cv y)))
      dv_cache_0013 dv_cache_0014 p0033 p0035
  have p0037 := @gElin syntaxClass0063 syntaxClass0034 syntaxClass0038
  have p0038 := @gVex y
  have p0039 :=
    @gOtkelins2k (.cv y) (synCsn (.cv m)) (synCsn (.cv n)) syntaxClass0033 p0038 p0002
      p0012
  have p0040 := @gOpkelcnvk (.cv y) (synCsn (.cv n)) syntaxClass0032 p0038 p0012
  have p0041 := @gEqtfinrelk (.cv n) (.cv y) p0018 p0038
  have p0042 :=
    @gN3bitri syntaxFormula0065
      (.classMem (synCopk (.cv y) (synCsn (.cv n))) syntaxClass0033)
      (.classMem (synCopk (synCsn (.cv n)) (.cv y)) syntaxClass0032)
      (.classEq (.cv y) (synCtfin (.cv n))) p0039 p0040 p0041
  have p0043 :=
    @gOtkelins3k (.cv y) (synCsn (.cv m)) (synCsn (.cv n)) syntaxClass0037 p0038 p0002
      p0012
  have p0044 := @gOpkex (.cv y) (synCsn (.cv m))
  have p0045 :=
    @gElimak t syntaxClass0036 (synCpw1 (synC1c)) (synCopk (.cv y) (synCsn (.cv m)))
      dv_cache_0015 dv_cache_0009 dv_cache_0016 p0044
  have p0046 := @gElpw11c x (.cv t) dv_cache_0017
  have p0047 :=
    @gAnbi1i (.classMem (.cv t) (synCpw1 (synC1c)))
      (synWex x (.classEq (.cv t) (synCsn (synCsn (.cv x))))) syntaxFormula0066 p0046
  have p0048 :=
    @gN1941v (.classEq (.cv t) (synCsn (synCsn (.cv x)))) syntaxFormula0066 x
      dv_cache_0018
  have p0049 :=
    @gBitr4i syntaxFormula0067
      (synWa (synWex x (.classEq (.cv t) (synCsn (synCsn (.cv x))))) syntaxFormula0066)
      syntaxFormula0069 p0047 p0048
  have p0050 := @gExbii syntaxFormula0067 syntaxFormula0069 t p0049
  have p0051 := (Nominal.biimpRefl syntaxFormula0070)
  have p0052 := @gExcom syntaxFormula0068 x t
  have p0053 :=
    @gN3bitr4i (synWex t syntaxFormula0067) (synWex t syntaxFormula0069)
      syntaxFormula0070 syntaxFormula0072 p0050 p0051 p0052
  have p0054 := @gSnex (synCsn (.cv x))
  have p0055 :=
    @gOpkeq1 (.cv t) (synCsn (synCsn (.cv x))) (synCopk (.cv y) (synCsn (.cv m)))
  have p0056 :=
    @gEleq1d (.classEq (.cv t) (synCsn (synCsn (.cv x))))
      (synCopk (.cv t) (synCopk (.cv y) (synCsn (.cv m))))
      (synCopk (synCsn (synCsn (.cv x))) (synCopk (.cv y) (synCsn (.cv m))))
      syntaxClass0036 p0055
  have p0057 :=
    @gCeqsexv syntaxFormula0066 syntaxFormula0073 t (synCsn (synCsn (.cv x)))
      dv_cache_0019 dv_cache_0020 p0054 p0056
  have p0058 :=
    @gElin (synCopk (synCsn (synCsn (.cv x))) (synCopk (.cv y) (synCsn (.cv m))))
      syntaxClass0034 syntaxClass0035
  have p0059 := @gVex x
  have p0060 :=
    @gOtkelins2k (.cv x) (.cv y) (synCsn (.cv m)) syntaxClass0033 p0059 p0038 p0002
  have p0061 := @gOpkelcnvk (.cv x) (synCsn (.cv m)) syntaxClass0032 p0059 p0002
  have p0062 := @gEqtfinrelk (.cv m) (.cv x) p0000 p0059
  have p0063 :=
    @gN3bitri syntaxFormula0074
      (.classMem (synCopk (.cv x) (synCsn (.cv m))) syntaxClass0033)
      (.classMem (synCopk (synCsn (.cv m)) (.cv x)) syntaxClass0032)
      (.classEq (.cv x) (synCtfin (.cv m))) p0060 p0061 p0062
  have p0064 :=
    @gOtkelins3k (.cv x) (.cv y) (synCsn (.cv m)) syntaxClass0016 p0059 p0038 p0002
  have p0065 := @gSrelk (.cv x) (.cv y) p0059 p0038
  have p0066 :=
    @gBitri syntaxFormula0075 (.classMem (synCopk (.cv x) (.cv y)) syntaxClass0016)
      (synWsfin (.cv x) (.cv y)) p0064 p0065
  have p0067 :=
    @gAnbi12i syntaxFormula0074 (.classEq (.cv x) (synCtfin (.cv m))) syntaxFormula0075
      (synWsfin (.cv x) (.cv y)) p0063 p0066
  have p0068 :=
    @gN3bitri syntaxFormula0071 syntaxFormula0073
      (synWa syntaxFormula0074 syntaxFormula0075)
      (synWa (.classEq (.cv x) (synCtfin (.cv m))) (synWsfin (.cv x) (.cv y))) p0057
      p0058 p0067
  have p0069 :=
    @gExbii syntaxFormula0071
      (synWa (.classEq (.cv x) (synCtfin (.cv m))) (synWsfin (.cv x) (.cv y))) x p0068
  have p0070 :=
    @gN3bitri syntaxFormula0076 syntaxFormula0070 syntaxFormula0072
      (synWex x (synWa (.classEq (.cv x) (synCtfin (.cv m))) (synWsfin (.cv x) (.cv y))))
      p0045 p0053 p0069
  have p0071 := @gTfinex (.cv m)
  have p0072 := @gSfineq1 (.cv x) (synCtfin (.cv m)) (.cv y)
  have p0073 :=
    @gCeqsexv (synWsfin (.cv x) (.cv y)) (synWsfin (synCtfin (.cv m)) (.cv y)) x
      (synCtfin (.cv m)) dv_cache_0021 dv_cache_0022 p0071 p0072
  have p0074 :=
    @gN3bitri syntaxFormula0077 syntaxFormula0076
      (synWex x (synWa (.classEq (.cv x) (synCtfin (.cv m))) (synWsfin (.cv x) (.cv y))))
      (synWsfin (synCtfin (.cv m)) (.cv y)) p0043 p0070 p0073
  have p0075 :=
    @gAnbi12i syntaxFormula0065 (.classEq (.cv y) (synCtfin (.cv n))) syntaxFormula0077
      (synWsfin (synCtfin (.cv m)) (.cv y)) p0042 p0074
  have p0076 :=
    @gN3bitri syntaxFormula0060 syntaxFormula0064
      (synWa syntaxFormula0065 syntaxFormula0077)
      (synWa (.classEq (.cv y) (synCtfin (.cv n))) (synWsfin (synCtfin (.cv m)) (.cv y)))
      p0036 p0037 p0075
  have p0077 :=
    @gExbii syntaxFormula0060
      (synWa (.classEq (.cv y) (synCtfin (.cv n))) (synWsfin (synCtfin (.cv m)) (.cv y)))
      y p0076
  have p0078 := @gTfinex (.cv n)
  have p0079 := @gSfineq2 (.cv y) (synCtfin (.cv n)) (synCtfin (.cv m))
  have p0080 :=
    @gCeqsexv (synWsfin (synCtfin (.cv m)) (.cv y))
      (synWsfin (synCtfin (.cv m)) (synCtfin (.cv n))) y (synCtfin (.cv n))
      dv_cache_0023 dv_cache_0024 p0078 p0079
  have p0081 :=
    @gN3bitri syntaxFormula0062 syntaxFormula0061
      (synWex y (synWa (.classEq (.cv y) (synCtfin (.cv n)))
          (synWsfin (synCtfin (.cv m)) (.cv y))))
      (synWsfin (synCtfin (.cv m)) (synCtfin (.cv n))) p0032 p0077 p0080
  have p0082 :=
    @gNotbii syntaxFormula0062 (synWsfin (synCtfin (.cv m)) (synCtfin (.cv n))) p0081
  have p0083 :=
    @gAnbi12i syntaxFormula0053 (synWsfin (.cv m) (.cv n)) syntaxFormula0078
      (.neg (synWsfin (synCtfin (.cv m)) (synCtfin (.cv n)))) p0021 p0082
  have p0084 :=
    @gAnnim (synWsfin (.cv m) (.cv n))
      (synWsfin (synCtfin (.cv m)) (synCtfin (.cv n)))
  have p0085 :=
    @gN3bitri syntaxFormula0079 (synWa syntaxFormula0053 syntaxFormula0078)
      (synWa (synWsfin (.cv m) (.cv n))
        (.neg (synWsfin (synCtfin (.cv m)) (synCtfin (.cv n)))))
      syntaxFormula0081 p0017 p0083 p0084
  have p0086 :=
    @gN3bitri syntaxFormula0050 syntaxFormula0052 syntaxFormula0079 syntaxFormula0081
      p0015 p0016 p0085
  have p0087 := @gExbii syntaxFormula0050 syntaxFormula0081 n p0086
  have p0088 :=
    @gN3bitri syntaxFormula0082 syntaxFormula0049 syntaxFormula0051 syntaxFormula0083
      p0003 p0011 p0087
  have p0089 := @gNotbii syntaxFormula0082 syntaxFormula0083 p0088
  have p0090 := @gElcompl (synCsn (.cv m)) syntaxClass0043 p0002
  have p0091 := @gAlex syntaxFormula0080 n
  have p0092 :=
    @gN3bitr4i (.neg syntaxFormula0082) (.neg syntaxFormula0083) syntaxFormula0084
      syntaxFormula0085 p0089 p0090 p0091
  have p0093 :=
    @gBitri (.classMem (.cv m) syntaxClass0086) syntaxFormula0084 syntaxFormula0085 p0001
      p0092
  have p0094 := @gEqabi syntaxFormula0085 m syntaxClass0086 dv_cache_0025 p0093
  have p0095 := @gSrelkex
  have p0096 := @gSikex syntaxClass0016 p0095
  have p0097 := @gTfinrelkex
  have p0098 := @gCnvkex syntaxClass0032 p0097
  have p0099 := @gIns2kex syntaxClass0033 p0098
  have p0101 := @gIns3kex syntaxClass0016 p0095
  have p0102 := @gInex syntaxClass0034 syntaxClass0035 p0099 p0101
  have p0103 := @gN1cex
  have p0104 := @gPw1ex (synC1c) p0103
  have p0105 := @gImakex syntaxClass0036 (synCpw1 (synC1c)) p0102 p0104
  have p0106 := @gIns3kex syntaxClass0037 p0105
  have p0107 := @gInex syntaxClass0034 syntaxClass0038 p0099 p0106
  have p0108 := @gImakex syntaxClass0039 (synCpw1 (synC1c)) p0107 p0104
  have p0109 := @gDifex syntaxClass0017 syntaxClass0040 p0096 p0108
  have p0110 := @gCnvkex syntaxClass0041 p0109
  have p0112 := @gImakex syntaxClass0042 (synC1c) p0110 p0103
  have p0113 := @gComplex syntaxClass0043 p0112
  have p0114 := @gUni1ex syntaxClass0044 p0113
  have p0115 :=
    @gEqeltrri syntaxClass0086 (.cab m syntaxFormula0085) (synCvv) p0094 p0114
  exact p0115


end NFChoice.DirectNominalPrf.WPPReplay

end
