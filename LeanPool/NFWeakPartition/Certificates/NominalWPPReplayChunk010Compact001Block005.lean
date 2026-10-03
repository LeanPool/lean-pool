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

@[expose]
noncomputable def g_srelkex :
    Nominal.NPrf
      (.classMem (syn_cin (syn_cxpk (syn_cnnc) (syn_cnnc)) (syn_cimak (syn_cin (syn_cins3k
                (syn_cimak (syn_cin (syn_cins3k (syn_csik
                        (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak
                            (syn_csymdif (syn_cins3k (syn_cssetk))
                              (syn_cins2k (syn_csik (syn_cssetk))))
                            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                    (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cins2k
                (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
                            (syn_csymdif (syn_cins3k (syn_cssetk))
                              (syn_cins2k (syn_csik (syn_cssetk))))
                            (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins2k (syn_cssetk)))
                  (syn_cpw1 (syn_cpw1 (syn_c1c))))))
            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cvv)) :=
  by
  have p0000 := @g_nncex
  have p0002 := @g_xpkex (syn_cnnc) (syn_cnnc) p0000 p0000
  have p0003 := @g_n_1cex
  have p0004 := @g_pwex (syn_c1c) p0003
  have p0005 := @g_vvex
  have p0006 := @g_xpkex (syn_cpw (syn_c1c)) (syn_cvv) p0004 p0005
  have p0007 := @g_ssetkex
  have p0008 := @g_ins3kex (syn_cssetk) p0007
  have p0010 := @g_sikex (syn_cssetk) p0007
  have p0011 := @g_ins2kex (syn_csik (syn_cssetk)) p0010
  have p0012 :=
    @g_symdifex (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk))) p0008 p0011
  have p0014 := @g_pw1ex (syn_c1c) p0003
  have p0015 := @g_pw1ex (syn_cpw1 (syn_c1c)) p0014
  have p0016 := @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_c1c))) p0015
  have p0017 :=
    @g_imakex (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk))))
      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))) p0012 p0016
  have p0018 :=
    @g_difex (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv))
      (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk))))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))
      p0006 p0017
  have p0019 :=
    @g_sikex
      (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak
          (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk))))
          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))
      p0018
  have p0020 :=
    @g_ins3kex
      (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak
            (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk))))
            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
      p0019
  have p0022 := @g_ins2kex (syn_cssetk) p0007
  have p0023 :=
    @g_inex
      (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak
              (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk))))
              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
      (syn_cins2k (syn_cssetk)) p0020 p0022
  have p0024 :=
    @g_imakex
      (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv))
              (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk))
                  (syn_cins2k (syn_csik (syn_cssetk))))
                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk)))
      (syn_cpw1 (syn_cpw1 (syn_c1c))) p0023 p0015
  have p0025 :=
    @g_ins3kex
      (syn_cimak (syn_cin (syn_cins3k (syn_csik
              (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak
                  (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk))))
                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c))))
      p0024
  have p0026 :=
    @g_imakex (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk))))
      (syn_cpw1 (syn_cpw1 (syn_c1c))) p0012 p0015
  have p0027 :=
    @g_complex
      (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk))))
        (syn_cpw1 (syn_cpw1 (syn_c1c))))
      p0026
  have p0028 :=
    @g_sikex
      (syn_ccompl (syn_cimak
          (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk))))
          (syn_cpw1 (syn_cpw1 (syn_c1c)))))
      p0027
  have p0029 :=
    @g_ins3kex
      (syn_csik (syn_ccompl (syn_cimak
            (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk))))
            (syn_cpw1 (syn_cpw1 (syn_c1c))))))
      p0028
  have p0030 :=
    @g_inex
      (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
              (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk))))
              (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
      (syn_cins2k (syn_cssetk)) p0029 p0022
  have p0031 :=
    @g_imakex
      (syn_cin (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
                (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk))))
                (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins2k (syn_cssetk)))
      (syn_cpw1 (syn_cpw1 (syn_c1c))) p0030 p0015
  have p0032 :=
    @g_ins2kex
      (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
                  (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk))))
                  (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c))))
      p0031
  have p0033 :=
    @g_inex
      (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik
                (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak
                    (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk))))
                    (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk)))
          (syn_cpw1 (syn_cpw1 (syn_c1c)))))
      (syn_cins2k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
                    (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk))))
                    (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins2k (syn_cssetk)))
          (syn_cpw1 (syn_cpw1 (syn_c1c)))))
      p0025 p0032
  have p0034 :=
    @g_imakex
      (syn_cin (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik
                  (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak
                      (syn_csymdif (syn_cins3k (syn_cssetk))
                        (syn_cins2k (syn_csik (syn_cssetk))))
                      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk)))
            (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cins2k (syn_cimak (syn_cin (syn_cins3k
                (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk))
                        (syn_cins2k (syn_csik (syn_cssetk))))
                      (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins2k (syn_cssetk)))
            (syn_cpw1 (syn_cpw1 (syn_c1c))))))
      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))) p0033 p0016
  have p0035 :=
    @g_inex (syn_cxpk (syn_cnnc) (syn_cnnc))
      (syn_cimak (syn_cin (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik
                    (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak
                        (syn_csymdif (syn_cins3k (syn_cssetk))
                          (syn_cins2k (syn_csik (syn_cssetk))))
                        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cins2k
            (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
                        (syn_csymdif (syn_cins3k (syn_cssetk))
                          (syn_cins2k (syn_csik (syn_cssetk))))
                        (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins2k (syn_cssetk)))
              (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))
      p0002 p0034
  exact p0035

@[expose]
noncomputable def g_sfineq1 (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (.classEq A B) (syn_wb (syn_wsfin A C) (syn_wsfin B C))) :=
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
  have p0000 := @g_eleq1 A B (syn_cnnc)
  have p0001 := @g_eleq2 A B (syn_cpw1 (.cv y))
  have p0002 :=
    @g_anbi1d (.classEq A B) (.classMem (syn_cpw1 (.cv y)) A)
      (.classMem (syn_cpw1 (.cv y)) B) (.classMem (syn_cpw (.cv y)) C) p0001
  have p0003 :=
    @g_exbidv (.classEq A B)
      (syn_wa (.classMem (syn_cpw1 (.cv y)) A) (.classMem (syn_cpw (.cv y)) C))
      (syn_wa (.classMem (syn_cpw1 (.cv y)) B) (.classMem (syn_cpw (.cv y)) C)) y
      dv_cache_0001 p0002
  have p0004 :=
    @g_n_3anbi13d (.classEq A B) (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))
      (syn_wex y (syn_wa (.classMem (syn_cpw1 (.cv y)) A) (.classMem (syn_cpw (.cv y)) C)))
      (syn_wex y (syn_wa (.classMem (syn_cpw1 (.cv y)) B) (.classMem (syn_cpw (.cv y)) C)))
      (.classMem C (syn_cnnc)) p0000 p0003
  have p0005 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_sfin A C y
      dv_cache_0002 dv_cache_0003
  have p0006 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_sfin B C y
      dv_cache_0004 dv_cache_0003
  have p0007 :=
    @g_n_3bitr4g (.classEq A B)
      (syn_w3a (.classMem A (syn_cnnc)) (.classMem C (syn_cnnc)) (syn_wex y
          (syn_wa (.classMem (syn_cpw1 (.cv y)) A) (.classMem (syn_cpw (.cv y)) C))))
      (syn_w3a (.classMem B (syn_cnnc)) (.classMem C (syn_cnnc)) (syn_wex y
          (syn_wa (.classMem (syn_cpw1 (.cv y)) B) (.classMem (syn_cpw (.cv y)) C))))
      (syn_wsfin A C) (syn_wsfin B C) p0004 p0005 p0006
  exact p0007

@[expose]
noncomputable def g_sfineq2 (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (.classEq A B) (syn_wb (syn_wsfin C A) (syn_wsfin C B))) :=
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
  have p0000 := @g_eleq1 A B (syn_cnnc)
  have p0001 := @g_eleq2 A B (syn_cpw (.cv y))
  have p0002 :=
    @g_anbi2d (.classEq A B) (.classMem (syn_cpw (.cv y)) A)
      (.classMem (syn_cpw (.cv y)) B) (.classMem (syn_cpw1 (.cv y)) C) p0001
  have p0003 :=
    @g_exbidv (.classEq A B)
      (syn_wa (.classMem (syn_cpw1 (.cv y)) C) (.classMem (syn_cpw (.cv y)) A))
      (syn_wa (.classMem (syn_cpw1 (.cv y)) C) (.classMem (syn_cpw (.cv y)) B)) y
      dv_cache_0001 p0002
  have p0004 :=
    @g_n_3anbi23d (.classEq A B) (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))
      (syn_wex y (syn_wa (.classMem (syn_cpw1 (.cv y)) C) (.classMem (syn_cpw (.cv y)) A)))
      (syn_wex y (syn_wa (.classMem (syn_cpw1 (.cv y)) C) (.classMem (syn_cpw (.cv y)) B)))
      (.classMem C (syn_cnnc)) p0000 p0003
  have p0005 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_sfin C A y
      dv_cache_0002 dv_cache_0003
  have p0006 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_sfin C B y
      dv_cache_0002 dv_cache_0004
  have p0007 :=
    @g_n_3bitr4g (.classEq A B)
      (syn_w3a (.classMem C (syn_cnnc)) (.classMem A (syn_cnnc)) (syn_wex y
          (syn_wa (.classMem (syn_cpw1 (.cv y)) C) (.classMem (syn_cpw (.cv y)) A))))
      (syn_w3a (.classMem C (syn_cnnc)) (.classMem B (syn_cnnc)) (syn_wex y
          (syn_wa (.classMem (syn_cpw1 (.cv y)) C) (.classMem (syn_cpw (.cv y)) B))))
      (syn_wsfin C A) (syn_wsfin C B) p0004 p0005 p0006
  exact p0007

@[expose]
noncomputable def g_sfin01 : Nominal.NPrf (syn_wsfin (syn_c0c) (syn_c1c)) :=
  by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let a : Var := freshVar proofSupport 0
  have dv_cache_0001 : a ∉ ((syn_c0)).fv := by
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
      ((syn_wa (.classEq (syn_cpw1 (syn_c0)) (syn_c0))
          (.classMem (syn_csn (syn_c0)) (syn_c1c)))).fv :=
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
  have dv_cache_0003 : a ∉ ((syn_c0c)).fv :=
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
  have dv_cache_0004 : a ∉ ((syn_c1c)).fv :=
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
  have p0000 := @g_peano1
  have p0001 := @g_n_1cnnc
  have p0002 := @g_pw10
  have p0003 := @g_n_0ex
  have p0004 := @g_snel1c (syn_c0) p0003
  have p0006 := @g_el0c (syn_cpw1 (.cv a))
  have p0007 := @g_pw1eq (.cv a) (syn_c0)
  have p0008 :=
    @g_eqeq1d (.classEq (.cv a) (syn_c0)) (syn_cpw1 (.cv a)) (syn_cpw1 (syn_c0)) (syn_c0)
      p0007
  have p0009 :=
    @g_syl5bb (.classMem (syn_cpw1 (.cv a)) (syn_c0c))
      (.classEq (syn_cpw1 (.cv a)) (syn_c0)) (.classEq (.cv a) (syn_c0))
      (.classEq (syn_cpw1 (syn_c0)) (syn_c0)) p0006 p0008
  have p0010 := @g_pweq (.cv a) (syn_c0)
  have p0011 := @g_pw0
  have p0012 :=
    @g_syl6eq (.classEq (.cv a) (syn_c0)) (syn_cpw (.cv a)) (syn_cpw (syn_c0))
      (syn_csn (syn_c0)) p0010 p0011
  have p0013 :=
    @g_eleq1d (.classEq (.cv a) (syn_c0)) (syn_cpw (.cv a)) (syn_csn (syn_c0)) (syn_c1c)
      p0012
  have p0014 :=
    @g_anbi12d (.classEq (.cv a) (syn_c0)) (.classMem (syn_cpw1 (.cv a)) (syn_c0c))
      (.classEq (syn_cpw1 (syn_c0)) (syn_c0)) (.classMem (syn_cpw (.cv a)) (syn_c1c))
      (.classMem (syn_csn (syn_c0)) (syn_c1c)) p0009 p0013
  have p0015 :=
    @g_spcev
      (syn_wa (.classMem (syn_cpw1 (.cv a)) (syn_c0c)) (.classMem (syn_cpw (.cv a)) (syn_c1c)))
      (syn_wa (.classEq (syn_cpw1 (syn_c0)) (syn_c0)) (.classMem (syn_csn (syn_c0)) (syn_c1c)))
      a (syn_c0) dv_cache_0001 dv_cache_0002 p0003 p0014
  have p0016 :=
    @g_mp2an (.classEq (syn_cpw1 (syn_c0)) (syn_c0))
      (.classMem (syn_csn (syn_c0)) (syn_c1c))
      (syn_wex a (syn_wa (.classMem (syn_cpw1 (.cv a)) (syn_c0c))
          (.classMem (syn_cpw (.cv a)) (syn_c1c))))
      p0002 p0004 p0015
  have p0017 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_sfin (syn_c0c)
      (syn_c1c) a dv_cache_0003 dv_cache_0004
  have p0018 :=
    @g_mpbir3an (syn_wsfin (syn_c0c) (syn_c1c)) (.classMem (syn_c0c) (syn_cnnc))
      (.classMem (syn_c1c) (syn_cnnc))
      (syn_wex a (syn_wa (.classMem (syn_cpw1 (.cv a)) (syn_c0c))
          (.classMem (syn_cpw (.cv a)) (syn_c1c))))
      p0000 p0001 p0016 p0017
  exact p0018

@[expose]
noncomputable def g_sfin112 (P : Class) (M : Class) (N : Class) :
    Nominal.NPrf (.imp (syn_wa (syn_wsfin M N) (syn_wsfin M P)) (.classEq N P)) :=
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
    y ∉ ((syn_wa (.classMem (syn_cpw1 (.cv x)) M) (.classMem (syn_cpw (.cv x)) N))).fv :=
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
    x ∉ ((syn_wa (.classMem (syn_cpw1 (.cv y)) M) (.classMem (syn_cpw (.cv y)) P))).fv :=
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
      ((syn_wa (syn_wa (syn_wa (.classMem M (syn_cnnc)) (.classMem M (syn_cnnc)))
            (syn_wa (.classMem N (syn_cnnc)) (.classMem P (syn_cnnc)))) (syn_wa
            (syn_wa (.classMem (syn_cpw1 (.cv x)) M) (.classMem (syn_cpw (.cv x)) N))
            (syn_wa (.classMem (syn_cpw1 (.cv y)) M) (.classMem (syn_cpw (.cv y)) P))))).fv :=
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
      ((syn_wa (syn_wa (syn_wa (.classMem M (syn_cnnc)) (.classMem M (syn_cnnc)))
            (syn_wa (.classMem N (syn_cnnc)) (.classMem P (syn_cnnc)))) (syn_wa
            (syn_wa (.classMem (syn_cpw1 (.cv x)) M) (.classMem (syn_cpw (.cv x)) N))
            (syn_wa (.classMem (syn_cpw1 (.cv y)) M) (.classMem (syn_cpw (.cv y)) P))))).fv :=
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
      ((syn_wa (syn_wa (.classMem M (syn_cnnc)) (.classMem M (syn_cnnc)))
          (syn_wa (.classMem N (syn_cnnc)) (.classMem P (syn_cnnc))))).fv :=
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
      ((syn_wa (syn_wa (.classMem M (syn_cnnc)) (.classMem M (syn_cnnc)))
          (syn_wa (.classMem N (syn_cnnc)) (.classMem P (syn_cnnc))))).fv :=
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
    @g_n_3an6 (.classMem M (syn_cnnc)) (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))
      (.classMem P (syn_cnnc))
      (syn_wex x (syn_wa (.classMem (syn_cpw1 (.cv x)) M) (.classMem (syn_cpw (.cv x)) N)))
      (syn_wex y (syn_wa (.classMem (syn_cpw1 (.cv y)) M) (.classMem (syn_cpw (.cv y)) P)))
  have p0001 :=
    @g_eeanv (syn_wa (.classMem (syn_cpw1 (.cv x)) M) (.classMem (syn_cpw (.cv x)) N))
      (syn_wa (.classMem (syn_cpw1 (.cv y)) M) (.classMem (syn_cpw (.cv y)) P)) x y
      dv_cache_0001 dv_cache_0002
  have p0002 :=
    @g_n_3anbi3i
      (syn_wex x (syn_wex y (syn_wa
            (syn_wa (.classMem (syn_cpw1 (.cv x)) M) (.classMem (syn_cpw (.cv x)) N))
            (syn_wa (.classMem (syn_cpw1 (.cv y)) M) (.classMem (syn_cpw (.cv y)) P)))))
      (syn_wa (syn_wex x
          (syn_wa (.classMem (syn_cpw1 (.cv x)) M) (.classMem (syn_cpw (.cv x)) N))) (syn_wex y
          (syn_wa (.classMem (syn_cpw1 (.cv y)) M) (.classMem (syn_cpw (.cv y)) P))))
      (syn_wa (.classMem M (syn_cnnc)) (.classMem M (syn_cnnc)))
      (syn_wa (.classMem N (syn_cnnc)) (.classMem P (syn_cnnc))) p0001
  have p0003 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_sfin M N x
      dv_cache_0003 dv_cache_0004
  have p0004 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_sfin M P y
      dv_cache_0005 dv_cache_0006
  have p0005 :=
    @g_anbi12i (syn_wsfin M N)
      (syn_w3a (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)) (syn_wex x
          (syn_wa (.classMem (syn_cpw1 (.cv x)) M) (.classMem (syn_cpw (.cv x)) N))))
      (syn_wsfin M P)
      (syn_w3a (.classMem M (syn_cnnc)) (.classMem P (syn_cnnc)) (syn_wex y
          (syn_wa (.classMem (syn_cpw1 (.cv y)) M) (.classMem (syn_cpw (.cv y)) P))))
      p0003 p0004
  have p0006 :=
    @g_n_3bitr4ri
      (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem M (syn_cnnc)))
        (syn_wa (.classMem N (syn_cnnc)) (.classMem P (syn_cnnc))) (syn_wa (syn_wex x
            (syn_wa (.classMem (syn_cpw1 (.cv x)) M) (.classMem (syn_cpw (.cv x)) N)))
          (syn_wex y
            (syn_wa (.classMem (syn_cpw1 (.cv y)) M) (.classMem (syn_cpw (.cv y)) P)))))
      (syn_wa (syn_w3a (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)) (syn_wex x
            (syn_wa (.classMem (syn_cpw1 (.cv x)) M) (.classMem (syn_cpw (.cv x)) N))))
        (syn_w3a (.classMem M (syn_cnnc)) (.classMem P (syn_cnnc)) (syn_wex y
            (syn_wa (.classMem (syn_cpw1 (.cv y)) M) (.classMem (syn_cpw (.cv y)) P)))))
      (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem M (syn_cnnc)))
        (syn_wa (.classMem N (syn_cnnc)) (.classMem P (syn_cnnc))) (syn_wex x (syn_wex y (syn_wa
              (syn_wa (.classMem (syn_cpw1 (.cv x)) M) (.classMem (syn_cpw (.cv x)) N))
              (syn_wa (.classMem (syn_cpw1 (.cv y)) M) (.classMem (syn_cpw (.cv y)) P))))))
      (syn_wa (syn_wsfin M N) (syn_wsfin M P)) p0000 p0002 p0005
  have p0007 :=
    @g_simpllr (.classMem M (syn_cnnc)) (.classMem M (syn_cnnc))
      (syn_wa (.classMem N (syn_cnnc)) (.classMem P (syn_cnnc)))
      (syn_wa (syn_wa (.classMem (syn_cpw1 (.cv x)) M) (.classMem (syn_cpw (.cv x)) N))
        (syn_wa (.classMem (syn_cpw1 (.cv y)) M) (.classMem (syn_cpw (.cv y)) P)))
  have p0008 :=
    @g_simprll
      (syn_wa (syn_wa (.classMem M (syn_cnnc)) (.classMem M (syn_cnnc)))
        (syn_wa (.classMem N (syn_cnnc)) (.classMem P (syn_cnnc))))
      (.classMem (syn_cpw1 (.cv x)) M) (.classMem (syn_cpw (.cv x)) N)
      (syn_wa (.classMem (syn_cpw1 (.cv y)) M) (.classMem (syn_cpw (.cv y)) P))
  have p0009 :=
    @g_simprrl
      (syn_wa (syn_wa (.classMem M (syn_cnnc)) (.classMem M (syn_cnnc)))
        (syn_wa (.classMem N (syn_cnnc)) (.classMem P (syn_cnnc))))
      (syn_wa (.classMem (syn_cpw1 (.cv x)) M) (.classMem (syn_cpw (.cv x)) N))
      (.classMem (syn_cpw1 (.cv y)) M) (.classMem (syn_cpw (.cv y)) P)
  have p0010 := @g_ncfinlower (.cv x) (.cv y) n M dv_cache_0007 dv_cache_0008
  have p0011_e03_recanon :
    Nominal.NPrf
      (.imp (syn_w3a (.classMem M (syn_cnnc)) (.classMem (syn_cpw1 (.cv x)) M)
          (.classMem (syn_cpw1 (.cv y)) M))
        (syn_wrex n (syn_cnnc) (syn_wa (.objMem x n) (.objMem y n)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_w3a syn_wa syn_cnnc syn_cint syn_cpw1 syn_cin syn_ccompl syn_cnin
          syn_wnan syn_cpw syn_wss syn_c1c syn_wex syn_csn syn_wrex
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
    @g_syl3anc
      (syn_wa (syn_wa (syn_wa (.classMem M (syn_cnnc)) (.classMem M (syn_cnnc)))
          (syn_wa (.classMem N (syn_cnnc)) (.classMem P (syn_cnnc))))
        (syn_wa (syn_wa (.classMem (syn_cpw1 (.cv x)) M) (.classMem (syn_cpw (.cv x)) N))
          (syn_wa (.classMem (syn_cpw1 (.cv y)) M) (.classMem (syn_cpw (.cv y)) P))))
      (.classMem M (syn_cnnc)) (.classMem (syn_cpw1 (.cv x)) M)
      (.classMem (syn_cpw1 (.cv y)) M)
      (syn_wrex n (syn_cnnc) (syn_wa (.objMem x n) (.objMem y n))) p0007 p0008 p0009
      p0011_e03_recanon
  have p0012 :=
    @g_nnpweq (.cv x) (.cv y) k (.cv n) dv_cache_0009 dv_cache_0010 dv_cache_0011
  have p0013_e00_recanon :
    Nominal.NPrf
      (.imp (syn_w3a (.classMem (.cv n) (syn_cnnc)) (.objMem x n) (.objMem y n))
        (syn_wrex k (syn_cnnc) (syn_wa (.classMem (syn_cpw (.cv x)) (.cv k))
            (.classMem (syn_cpw (.cv y)) (.cv k))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_w3a syn_wa syn_cnnc syn_cint syn_wrex syn_wex
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
    @g_n_3expb (.classMem (.cv n) (syn_cnnc)) (.objMem x n) (.objMem y n)
      (syn_wrex k (syn_cnnc) (syn_wa (.classMem (syn_cpw (.cv x)) (.cv k))
          (.classMem (syn_cpw (.cv y)) (.cv k))))
      p0013_e00_recanon
  have p0014 :=
    @g_simp1rl (.classMem N (syn_cnnc)) (.classMem P (syn_cnnc))
      (syn_wa (.classMem M (syn_cnnc)) (.classMem M (syn_cnnc)))
      (syn_wa (syn_wa (.classMem (syn_cpw1 (.cv x)) M) (.classMem (syn_cpw (.cv x)) N))
        (syn_wa (.classMem (syn_cpw1 (.cv y)) M) (.classMem (syn_cpw (.cv y)) P)))
      (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem (syn_cpw (.cv x)) (.cv k))
          (.classMem (syn_cpw (.cv y)) (.cv k))))
  have p0015 :=
    @g_simp3l
      (syn_wa (syn_wa (.classMem M (syn_cnnc)) (.classMem M (syn_cnnc)))
        (syn_wa (.classMem N (syn_cnnc)) (.classMem P (syn_cnnc))))
      (syn_wa (syn_wa (.classMem (syn_cpw1 (.cv x)) M) (.classMem (syn_cpw (.cv x)) N))
        (syn_wa (.classMem (syn_cpw1 (.cv y)) M) (.classMem (syn_cpw (.cv y)) P)))
      (.classMem (.cv k) (syn_cnnc))
      (syn_wa (.classMem (syn_cpw (.cv x)) (.cv k)) (.classMem (syn_cpw (.cv y)) (.cv k)))
  have p0016 :=
    @g_simp2lr (.classMem (syn_cpw1 (.cv x)) M) (.classMem (syn_cpw (.cv x)) N)
      (syn_wa (.classMem (syn_cpw1 (.cv y)) M) (.classMem (syn_cpw (.cv y)) P))
      (syn_wa (syn_wa (.classMem M (syn_cnnc)) (.classMem M (syn_cnnc)))
        (syn_wa (.classMem N (syn_cnnc)) (.classMem P (syn_cnnc))))
      (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem (syn_cpw (.cv x)) (.cv k))
          (.classMem (syn_cpw (.cv y)) (.cv k))))
  have p0017 :=
    @g_simp3rl (.classMem (syn_cpw (.cv x)) (.cv k)) (.classMem (syn_cpw (.cv y)) (.cv k))
      (.classMem (.cv k) (syn_cnnc))
      (syn_wa (syn_wa (.classMem M (syn_cnnc)) (.classMem M (syn_cnnc)))
        (syn_wa (.classMem N (syn_cnnc)) (.classMem P (syn_cnnc))))
      (syn_wa (syn_wa (.classMem (syn_cpw1 (.cv x)) M) (.classMem (syn_cpw (.cv x)) N))
        (syn_wa (.classMem (syn_cpw1 (.cv y)) M) (.classMem (syn_cpw (.cv y)) P)))
  have p0018 := @g_nnceleq (syn_cpw (.cv x)) N (.cv k)
  have p0019 :=
    @g_syl22anc
      (syn_w3a (syn_wa (syn_wa (.classMem M (syn_cnnc)) (.classMem M (syn_cnnc)))
          (syn_wa (.classMem N (syn_cnnc)) (.classMem P (syn_cnnc))))
        (syn_wa (syn_wa (.classMem (syn_cpw1 (.cv x)) M) (.classMem (syn_cpw (.cv x)) N))
          (syn_wa (.classMem (syn_cpw1 (.cv y)) M) (.classMem (syn_cpw (.cv y)) P)))
        (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem (syn_cpw (.cv x)) (.cv k))
            (.classMem (syn_cpw (.cv y)) (.cv k)))))
      (.classMem N (syn_cnnc)) (.classMem (.cv k) (syn_cnnc))
      (.classMem (syn_cpw (.cv x)) N) (.classMem (syn_cpw (.cv x)) (.cv k))
      (.classEq N (.cv k)) p0014 p0015 p0016 p0017 p0018
  have p0020 :=
    @g_simp1rr (.classMem N (syn_cnnc)) (.classMem P (syn_cnnc))
      (syn_wa (.classMem M (syn_cnnc)) (.classMem M (syn_cnnc)))
      (syn_wa (syn_wa (.classMem (syn_cpw1 (.cv x)) M) (.classMem (syn_cpw (.cv x)) N))
        (syn_wa (.classMem (syn_cpw1 (.cv y)) M) (.classMem (syn_cpw (.cv y)) P)))
      (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem (syn_cpw (.cv x)) (.cv k))
          (.classMem (syn_cpw (.cv y)) (.cv k))))
  have p0021 :=
    @g_simp2rr (.classMem (syn_cpw1 (.cv y)) M) (.classMem (syn_cpw (.cv y)) P)
      (syn_wa (.classMem (syn_cpw1 (.cv x)) M) (.classMem (syn_cpw (.cv x)) N))
      (syn_wa (syn_wa (.classMem M (syn_cnnc)) (.classMem M (syn_cnnc)))
        (syn_wa (.classMem N (syn_cnnc)) (.classMem P (syn_cnnc))))
      (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem (syn_cpw (.cv x)) (.cv k))
          (.classMem (syn_cpw (.cv y)) (.cv k))))
  have p0022 :=
    @g_simp3rr (.classMem (syn_cpw (.cv x)) (.cv k)) (.classMem (syn_cpw (.cv y)) (.cv k))
      (.classMem (.cv k) (syn_cnnc))
      (syn_wa (syn_wa (.classMem M (syn_cnnc)) (.classMem M (syn_cnnc)))
        (syn_wa (.classMem N (syn_cnnc)) (.classMem P (syn_cnnc))))
      (syn_wa (syn_wa (.classMem (syn_cpw1 (.cv x)) M) (.classMem (syn_cpw (.cv x)) N))
        (syn_wa (.classMem (syn_cpw1 (.cv y)) M) (.classMem (syn_cpw (.cv y)) P)))
  have p0023 := @g_nnceleq (syn_cpw (.cv y)) P (.cv k)
  have p0024 :=
    @g_syl22anc
      (syn_w3a (syn_wa (syn_wa (.classMem M (syn_cnnc)) (.classMem M (syn_cnnc)))
          (syn_wa (.classMem N (syn_cnnc)) (.classMem P (syn_cnnc))))
        (syn_wa (syn_wa (.classMem (syn_cpw1 (.cv x)) M) (.classMem (syn_cpw (.cv x)) N))
          (syn_wa (.classMem (syn_cpw1 (.cv y)) M) (.classMem (syn_cpw (.cv y)) P)))
        (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem (syn_cpw (.cv x)) (.cv k))
            (.classMem (syn_cpw (.cv y)) (.cv k)))))
      (.classMem P (syn_cnnc)) (.classMem (.cv k) (syn_cnnc))
      (.classMem (syn_cpw (.cv y)) P) (.classMem (syn_cpw (.cv y)) (.cv k))
      (.classEq P (.cv k)) p0020 p0015 p0021 p0022 p0023
  have p0025 :=
    @g_eqtr4d
      (syn_w3a (syn_wa (syn_wa (.classMem M (syn_cnnc)) (.classMem M (syn_cnnc)))
          (syn_wa (.classMem N (syn_cnnc)) (.classMem P (syn_cnnc))))
        (syn_wa (syn_wa (.classMem (syn_cpw1 (.cv x)) M) (.classMem (syn_cpw (.cv x)) N))
          (syn_wa (.classMem (syn_cpw1 (.cv y)) M) (.classMem (syn_cpw (.cv y)) P)))
        (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem (syn_cpw (.cv x)) (.cv k))
            (.classMem (syn_cpw (.cv y)) (.cv k)))))
      N (.cv k) P p0019 p0024
  have p0026 :=
    @g_n_3expa
      (syn_wa (syn_wa (.classMem M (syn_cnnc)) (.classMem M (syn_cnnc)))
        (syn_wa (.classMem N (syn_cnnc)) (.classMem P (syn_cnnc))))
      (syn_wa (syn_wa (.classMem (syn_cpw1 (.cv x)) M) (.classMem (syn_cpw (.cv x)) N))
        (syn_wa (.classMem (syn_cpw1 (.cv y)) M) (.classMem (syn_cpw (.cv y)) P)))
      (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.classMem (syn_cpw (.cv x)) (.cv k))
          (.classMem (syn_cpw (.cv y)) (.cv k))))
      (.classEq N P) p0025
  have p0027 :=
    @g_expr
      (syn_wa (syn_wa (syn_wa (.classMem M (syn_cnnc)) (.classMem M (syn_cnnc)))
          (syn_wa (.classMem N (syn_cnnc)) (.classMem P (syn_cnnc))))
        (syn_wa (syn_wa (.classMem (syn_cpw1 (.cv x)) M) (.classMem (syn_cpw (.cv x)) N))
          (syn_wa (.classMem (syn_cpw1 (.cv y)) M) (.classMem (syn_cpw (.cv y)) P))))
      (.classMem (.cv k) (syn_cnnc))
      (syn_wa (.classMem (syn_cpw (.cv x)) (.cv k)) (.classMem (syn_cpw (.cv y)) (.cv k)))
      (.classEq N P) p0026
  have p0028 :=
    @g_rexlimdva
      (syn_wa (syn_wa (syn_wa (.classMem M (syn_cnnc)) (.classMem M (syn_cnnc)))
          (syn_wa (.classMem N (syn_cnnc)) (.classMem P (syn_cnnc))))
        (syn_wa (syn_wa (.classMem (syn_cpw1 (.cv x)) M) (.classMem (syn_cpw (.cv x)) N))
          (syn_wa (.classMem (syn_cpw1 (.cv y)) M) (.classMem (syn_cpw (.cv y)) P))))
      (syn_wa (.classMem (syn_cpw (.cv x)) (.cv k)) (.classMem (syn_cpw (.cv y)) (.cv k)))
      (.classEq N P) k (syn_cnnc) dv_cache_0012 dv_cache_0013 p0027
  have p0029 :=
    @g_syl5 (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wa (.objMem x n) (.objMem y n)))
      (syn_wrex k (syn_cnnc) (syn_wa (.classMem (syn_cpw (.cv x)) (.cv k))
          (.classMem (syn_cpw (.cv y)) (.cv k))))
      (syn_wa (syn_wa (syn_wa (.classMem M (syn_cnnc)) (.classMem M (syn_cnnc)))
          (syn_wa (.classMem N (syn_cnnc)) (.classMem P (syn_cnnc))))
        (syn_wa (syn_wa (.classMem (syn_cpw1 (.cv x)) M) (.classMem (syn_cpw (.cv x)) N))
          (syn_wa (.classMem (syn_cpw1 (.cv y)) M) (.classMem (syn_cpw (.cv y)) P))))
      (.classEq N P) p0013 p0028
  have p0030 :=
    @g_exp3a
      (syn_wa (syn_wa (syn_wa (.classMem M (syn_cnnc)) (.classMem M (syn_cnnc)))
          (syn_wa (.classMem N (syn_cnnc)) (.classMem P (syn_cnnc))))
        (syn_wa (syn_wa (.classMem (syn_cpw1 (.cv x)) M) (.classMem (syn_cpw (.cv x)) N))
          (syn_wa (.classMem (syn_cpw1 (.cv y)) M) (.classMem (syn_cpw (.cv y)) P))))
      (.classMem (.cv n) (syn_cnnc)) (syn_wa (.objMem x n) (.objMem y n)) (.classEq N P)
      p0029
  have p0031 :=
    @g_rexlimdv
      (syn_wa (syn_wa (syn_wa (.classMem M (syn_cnnc)) (.classMem M (syn_cnnc)))
          (syn_wa (.classMem N (syn_cnnc)) (.classMem P (syn_cnnc))))
        (syn_wa (syn_wa (.classMem (syn_cpw1 (.cv x)) M) (.classMem (syn_cpw (.cv x)) N))
          (syn_wa (.classMem (syn_cpw1 (.cv y)) M) (.classMem (syn_cpw (.cv y)) P))))
      (syn_wa (.objMem x n) (.objMem y n)) (.classEq N P) n (syn_cnnc) dv_cache_0014
      dv_cache_0015 p0030
  have p0032 :=
    @g_mpd
      (syn_wa (syn_wa (syn_wa (.classMem M (syn_cnnc)) (.classMem M (syn_cnnc)))
          (syn_wa (.classMem N (syn_cnnc)) (.classMem P (syn_cnnc))))
        (syn_wa (syn_wa (.classMem (syn_cpw1 (.cv x)) M) (.classMem (syn_cpw (.cv x)) N))
          (syn_wa (.classMem (syn_cpw1 (.cv y)) M) (.classMem (syn_cpw (.cv y)) P))))
      (syn_wrex n (syn_cnnc) (syn_wa (.objMem x n) (.objMem y n))) (.classEq N P) p0011
      p0031
  have p0033 :=
    @g_ex
      (syn_wa (syn_wa (.classMem M (syn_cnnc)) (.classMem M (syn_cnnc)))
        (syn_wa (.classMem N (syn_cnnc)) (.classMem P (syn_cnnc))))
      (syn_wa (syn_wa (.classMem (syn_cpw1 (.cv x)) M) (.classMem (syn_cpw (.cv x)) N))
        (syn_wa (.classMem (syn_cpw1 (.cv y)) M) (.classMem (syn_cpw (.cv y)) P)))
      (.classEq N P) p0032
  have p0034 :=
    @g_exlimdvv
      (syn_wa (syn_wa (.classMem M (syn_cnnc)) (.classMem M (syn_cnnc)))
        (syn_wa (.classMem N (syn_cnnc)) (.classMem P (syn_cnnc))))
      (syn_wa (syn_wa (.classMem (syn_cpw1 (.cv x)) M) (.classMem (syn_cpw (.cv x)) N))
        (syn_wa (.classMem (syn_cpw1 (.cv y)) M) (.classMem (syn_cpw (.cv y)) P)))
      (.classEq N P) x y dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 p0033
  have p0035 :=
    @g_n_3impia (syn_wa (.classMem M (syn_cnnc)) (.classMem M (syn_cnnc)))
      (syn_wa (.classMem N (syn_cnnc)) (.classMem P (syn_cnnc)))
      (syn_wex x (syn_wex y (syn_wa
            (syn_wa (.classMem (syn_cpw1 (.cv x)) M) (.classMem (syn_cpw (.cv x)) N))
            (syn_wa (.classMem (syn_cpw1 (.cv y)) M) (.classMem (syn_cpw (.cv y)) P)))))
      (.classEq N P) p0034
  have p0036 :=
    @g_sylbi (syn_wa (syn_wsfin M N) (syn_wsfin M P))
      (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem M (syn_cnnc)))
        (syn_wa (.classMem N (syn_cnnc)) (.classMem P (syn_cnnc))) (syn_wex x (syn_wex y (syn_wa
              (syn_wa (.classMem (syn_cpw1 (.cv x)) M) (.classMem (syn_cpw (.cv x)) N))
              (syn_wa (.classMem (syn_cpw1 (.cv y)) M) (.classMem (syn_cpw (.cv y)) P))))))
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

@[expose]
noncomputable def g_sfindbl (A : Class) (n : Var) (M : Class) (dv_M_n : n ∉ M.fv) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem M (syn_cnnc)) (.classMem (syn_cpw1 A) (syn_cplc M (syn_c1c))))
        (syn_wrex n (syn_cnnc) (syn_wa (syn_wsfin M (.cv n))
            (syn_wsfin (syn_cplc M (syn_c1c)) (syn_cplc (.cv n) (.cv n)))))) :=
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
  have dv_cache_0001 : b ∉ ((syn_cpw1 A)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, fresh_b_not_A,
          not_false_eq_true])
  have dv_cache_0002 : x ∉ ((syn_cpw1 A)).fv :=
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
      ((syn_wa (.classMem (syn_cpw1 (.cv y)) M) (.classMem (syn_cpw (.cv y)) (.cv n)))).fv :=
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
  have dv_cache_0019 : a ∉ ((syn_cun (.cv y) (syn_csn (.cv z)))).fv :=
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
      ((syn_wa (.classMem (syn_cpw1 (syn_cun (.cv y) (syn_csn (.cv z)))) (syn_cplc M (syn_c1c)))
          (.classMem (syn_cpw (syn_cun (.cv y) (syn_csn (.cv z))))
            (syn_cplc (.cv n) (.cv n))))).fv :=
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
  have dv_cache_0021 : a ∉ ((syn_cplc M (syn_c1c))).fv :=
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
  have dv_cache_0022 : a ∉ ((syn_cplc (.cv n) (.cv n))).fv :=
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
      ((syn_w3a (.classMem M (syn_cnnc))
          (syn_wa (.classMem (syn_cpw1 (.cv y)) M) (.neg (.objMem z y)))
          (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.objMem y k) (.objMem y k))))).fv :=
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
      ((syn_wrex n (syn_cnnc) (syn_wa (syn_wsfin M (.cv n))
            (syn_wsfin (syn_cplc M (syn_c1c)) (syn_cplc (.cv n) (.cv n)))))).fv :=
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
      ((syn_wa (.classMem M (syn_cnnc))
          (syn_wa (.classMem (syn_cpw1 (.cv y)) M) (.neg (.objMem z y))))).fv :=
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
      ((syn_wrex n (syn_cnnc) (syn_wa (syn_wsfin M (.cv n))
            (syn_wsfin (syn_cplc M (syn_c1c)) (syn_cplc (.cv n) (.cv n)))))).fv :=
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
      ((syn_wrex n (syn_cnnc) (syn_wa (syn_wsfin M (.cv n))
            (syn_wsfin (syn_cplc M (syn_c1c)) (syn_cplc (.cv n) (.cv n)))))).fv :=
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
      ((syn_wa (.classMem M (syn_cnnc))
          (syn_wa (.classMem (.cv b) M) (.classMem (.cv x) (syn_ccompl (.cv b)))))).fv :=
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
      ((syn_wa (.classMem M (syn_cnnc))
          (syn_wa (.classMem (.cv b) M) (.classMem (.cv x) (syn_ccompl (.cv b)))))).fv :=
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
      ((syn_wrex n (syn_cnnc) (syn_wa (syn_wsfin M (.cv n))
            (syn_wsfin (syn_cplc M (syn_c1c)) (syn_cplc (.cv n) (.cv n)))))).fv :=
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
      ((syn_wrex n (syn_cnnc) (syn_wa (syn_wsfin M (.cv n))
            (syn_wsfin (syn_cplc M (syn_c1c)) (syn_cplc (.cv n) (.cv n)))))).fv :=
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
  have dv_cache_0033 : b ∉ ((Wff.classMem M (syn_cnnc))).fv :=
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
  have dv_cache_0034 : x ∉ ((Wff.classMem M (syn_cnnc))).fv :=
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
    @g_elsuc x (syn_cpw1 A) M b dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
  have p0001 := @g_vex b
  have p0002 := @g_vex x
  have p0003 :=
    @g_pw1eqadj y z (.cv b) (.cv x) A dv_cache_0005 dv_cache_0006 dv_cache_0007
      dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 p0001 p0002
  have p0004 := @g_eleq1 (.cv b) (syn_cpw1 (.cv y)) M
  have p0005 :=
    @g_adantr (.classEq (.cv b) (syn_cpw1 (.cv y)))
      (syn_wb (.classMem (.cv b) M) (.classMem (syn_cpw1 (.cv y)) M))
      (.classEq (.cv x) (syn_csn (.cv z))) p0004
  have p0006 := @g_compleq (.cv b) (syn_cpw1 (.cv y))
  have p0007 :=
    @g_eleq12 (.cv x) (syn_csn (.cv z)) (syn_ccompl (.cv b))
      (syn_ccompl (syn_cpw1 (.cv y)))
  have p0008 := @g_snex (.cv z)
  have p0009 := @g_elcompl (syn_csn (.cv z)) (syn_cpw1 (.cv y)) p0008
  have p0010 := @g_snelpw1 (.cv z) (.cv y)
  have p0011_e01_recanon :
    Nominal.NPrf
      (syn_wb (.classMem (syn_csn (.cv z)) (syn_cpw1 (.cv y))) (.objMem z y)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_csn syn_cpw1 syn_cin syn_ccompl syn_cnin syn_wnan syn_wa syn_cpw
          syn_wss syn_c1c syn_wex
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
    @g_xchbinx (.classMem (syn_csn (.cv z)) (syn_ccompl (syn_cpw1 (.cv y))))
      (.classMem (syn_csn (.cv z)) (syn_cpw1 (.cv y))) (.objMem z y) p0009
      p0011_e01_recanon
  have p0012 :=
    @g_syl6bb
      (syn_wa (.classEq (.cv x) (syn_csn (.cv z)))
        (.classEq (syn_ccompl (.cv b)) (syn_ccompl (syn_cpw1 (.cv y)))))
      (.classMem (.cv x) (syn_ccompl (.cv b)))
      (.classMem (syn_csn (.cv z)) (syn_ccompl (syn_cpw1 (.cv y)))) (.neg (.objMem z y))
      p0007 p0011
  have p0013 :=
    @g_sylan2 (.classEq (.cv b) (syn_cpw1 (.cv y))) (.classEq (.cv x) (syn_csn (.cv z)))
      (.classEq (syn_ccompl (.cv b)) (syn_ccompl (syn_cpw1 (.cv y))))
      (syn_wb (.classMem (.cv x) (syn_ccompl (.cv b))) (.neg (.objMem z y))) p0006 p0012
  have p0014 :=
    @g_ancoms (.classEq (.cv x) (syn_csn (.cv z))) (.classEq (.cv b) (syn_cpw1 (.cv y)))
      (syn_wb (.classMem (.cv x) (syn_ccompl (.cv b))) (.neg (.objMem z y))) p0013
  have p0015 :=
    @g_anbi12d
      (syn_wa (.classEq (.cv b) (syn_cpw1 (.cv y))) (.classEq (.cv x) (syn_csn (.cv z))))
      (.classMem (.cv b) M) (.classMem (syn_cpw1 (.cv y)) M)
      (.classMem (.cv x) (syn_ccompl (.cv b))) (.neg (.objMem z y)) p0005 p0014
  have p0016 :=
    @g_anbi2d
      (syn_wa (.classEq (.cv b) (syn_cpw1 (.cv y))) (.classEq (.cv x) (syn_csn (.cv z))))
      (syn_wa (.classMem (.cv b) M) (.classMem (.cv x) (syn_ccompl (.cv b))))
      (syn_wa (.classMem (syn_cpw1 (.cv y)) M) (.neg (.objMem z y)))
      (.classMem M (syn_cnnc)) p0015
  have p0017 := @g_ncfinlower (.cv y) (.cv y) k M dv_cache_0012 dv_cache_0012
  have p0018_e00_recanon :
    Nominal.NPrf
      (.imp (syn_w3a (.classMem M (syn_cnnc)) (.classMem (syn_cpw1 (.cv y)) M)
          (.classMem (syn_cpw1 (.cv y)) M))
        (syn_wrex k (syn_cnnc) (syn_wa (.objMem y k) (.objMem y k)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_w3a syn_wa syn_cnnc syn_cint syn_cpw1 syn_cin syn_ccompl syn_cnin
          syn_wnan syn_cpw syn_wss syn_c1c syn_wex syn_csn syn_wrex
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
    @g_n_3anidm23 (.classMem M (syn_cnnc)) (.classMem (syn_cpw1 (.cv y)) M)
      (syn_wrex k (syn_cnnc) (syn_wa (.objMem y k) (.objMem y k))) p0018_e00_recanon
  have p0019 :=
    @g_adantrr (.classMem M (syn_cnnc)) (.classMem (syn_cpw1 (.cv y)) M)
      (syn_wrex k (syn_cnnc) (syn_wa (.objMem y k) (.objMem y k))) (.neg (.objMem z y))
      p0018
  have p0020 :=
    @g_simp3l (.classMem M (syn_cnnc))
      (syn_wa (.classMem (syn_cpw1 (.cv y)) M) (.neg (.objMem z y)))
      (.classMem (.cv k) (syn_cnnc)) (syn_wa (.objMem y k) (.objMem y k))
  have p0021 :=
    @g_simp3rr (.objMem y k) (.objMem y k) (.classMem (.cv k) (syn_cnnc))
      (.classMem M (syn_cnnc))
      (syn_wa (.classMem (syn_cpw1 (.cv y)) M) (.neg (.objMem z y)))
  have p0022 :=
    @g_nnpweq (.cv y) (.cv y) n (.cv k) dv_cache_0013 dv_cache_0013 dv_cache_0014
  have p0023_e03_recanon :
    Nominal.NPrf
      (.imp (syn_w3a (.classMem (.cv k) (syn_cnnc)) (.objMem y k) (.objMem y k))
        (syn_wrex n (syn_cnnc) (syn_wa (.classMem (syn_cpw (.cv y)) (.cv n))
            (.classMem (syn_cpw (.cv y)) (.cv n))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_w3a syn_wa syn_cnnc syn_cint syn_wrex syn_wex
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
    @g_syl3anc
      (syn_w3a (.classMem M (syn_cnnc))
        (syn_wa (.classMem (syn_cpw1 (.cv y)) M) (.neg (.objMem z y)))
        (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.objMem y k) (.objMem y k))))
      (.classMem (.cv k) (syn_cnnc)) (.objMem y k) (.objMem y k)
      (syn_wrex n (syn_cnnc) (syn_wa (.classMem (syn_cpw (.cv y)) (.cv n))
          (.classMem (syn_cpw (.cv y)) (.cv n))))
      p0020 p0021 p0021 p0023_e03_recanon
  have p0024 :=
    @g_simpl1 (.classMem M (syn_cnnc))
      (syn_wa (.classMem (syn_cpw1 (.cv y)) M) (.neg (.objMem z y)))
      (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.objMem y k) (.objMem y k)))
      (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wa (.classMem (syn_cpw (.cv y)) (.cv n))
          (.classMem (syn_cpw (.cv y)) (.cv n))))
  have p0025 :=
    @g_simprl
      (syn_w3a (.classMem M (syn_cnnc))
        (syn_wa (.classMem (syn_cpw1 (.cv y)) M) (.neg (.objMem z y)))
        (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.objMem y k) (.objMem y k))))
      (.classMem (.cv n) (syn_cnnc))
      (syn_wa (.classMem (syn_cpw (.cv y)) (.cv n)) (.classMem (syn_cpw (.cv y)) (.cv n)))
  have p0026 :=
    @g_simpl2l (.classMem (syn_cpw1 (.cv y)) M) (.neg (.objMem z y))
      (.classMem M (syn_cnnc))
      (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.objMem y k) (.objMem y k)))
      (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wa (.classMem (syn_cpw (.cv y)) (.cv n))
          (.classMem (syn_cpw (.cv y)) (.cv n))))
  have p0027 :=
    @g_simprrr
      (syn_w3a (.classMem M (syn_cnnc))
        (syn_wa (.classMem (syn_cpw1 (.cv y)) M) (.neg (.objMem z y)))
        (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.objMem y k) (.objMem y k))))
      (.classMem (.cv n) (syn_cnnc)) (.classMem (syn_cpw (.cv y)) (.cv n))
      (.classMem (syn_cpw (.cv y)) (.cv n))
  have p0028 := @g_vex y
  have p0029 := @g_pw1eq (.cv a) (.cv y)
  have p0030_e00_recanon :
    Nominal.NPrf (.imp (.objEq a y) (.classEq (syn_cpw1 (.cv a)) (syn_cpw1 (.cv y)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_cpw1 syn_cin syn_ccompl syn_cnin syn_wnan syn_wa syn_cpw syn_wss
          syn_c1c syn_wex syn_csn
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0029
  have p0030 :=
    @g_eleq1d (.objEq a y) (syn_cpw1 (.cv a)) (syn_cpw1 (.cv y)) M p0030_e00_recanon
  have p0031 := @g_pweq (.cv a) (.cv y)
  have p0032_e00_recanon :
    Nominal.NPrf (.imp (.objEq a y) (.classEq (syn_cpw (.cv a)) (syn_cpw (.cv y)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_cpw syn_wss syn_cin syn_ccompl syn_cnin syn_wnan syn_wa
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0031
  have p0032 :=
    @g_eleq1d (.objEq a y) (syn_cpw (.cv a)) (syn_cpw (.cv y)) (.cv n) p0032_e00_recanon
  have p0033 :=
    @g_anbi12d (.objEq a y) (.classMem (syn_cpw1 (.cv a)) M)
      (.classMem (syn_cpw1 (.cv y)) M) (.classMem (syn_cpw (.cv a)) (.cv n))
      (.classMem (syn_cpw (.cv y)) (.cv n)) p0030 p0032
  have p0034_e01_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv a) (.cv y)) (syn_wb
          (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw (.cv a)) (.cv n)))
          (syn_wa (.classMem (syn_cpw1 (.cv y)) M) (.classMem (syn_cpw (.cv y)) (.cv n))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wa syn_cpw1 syn_cin syn_ccompl syn_cnin syn_wnan syn_cpw syn_wss
          syn_c1c syn_wex syn_csn
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0033
  have p0034 :=
    @g_spcev
      (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw (.cv a)) (.cv n)))
      (syn_wa (.classMem (syn_cpw1 (.cv y)) M) (.classMem (syn_cpw (.cv y)) (.cv n))) a
      (.cv y) dv_cache_0015 dv_cache_0016 p0028 p0034_e01_recanon
  have p0035 :=
    @g_syl2anc
      (syn_wa (syn_w3a (.classMem M (syn_cnnc))
          (syn_wa (.classMem (syn_cpw1 (.cv y)) M) (.neg (.objMem z y)))
          (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.objMem y k) (.objMem y k))))
        (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wa (.classMem (syn_cpw (.cv y)) (.cv n))
            (.classMem (syn_cpw (.cv y)) (.cv n)))))
      (.classMem (syn_cpw1 (.cv y)) M) (.classMem (syn_cpw (.cv y)) (.cv n))
      (syn_wex a
        (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw (.cv a)) (.cv n))))
      p0026 p0027 p0034
  have p0036 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_sfin M (.cv n) a
      dv_cache_0017 dv_cache_0018
  have p0037 :=
    @g_syl3anbrc
      (syn_wa (syn_w3a (.classMem M (syn_cnnc))
          (syn_wa (.classMem (syn_cpw1 (.cv y)) M) (.neg (.objMem z y)))
          (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.objMem y k) (.objMem y k))))
        (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wa (.classMem (syn_cpw (.cv y)) (.cv n))
            (.classMem (syn_cpw (.cv y)) (.cv n)))))
      (.classMem M (syn_cnnc)) (.classMem (.cv n) (syn_cnnc))
      (syn_wex a
        (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw (.cv a)) (.cv n))))
      (syn_wsfin M (.cv n)) p0024 p0025 p0035 p0036
  have p0038 := @g_peano2 M
  have p0039 :=
    @g_syl
      (syn_wa (syn_w3a (.classMem M (syn_cnnc))
          (syn_wa (.classMem (syn_cpw1 (.cv y)) M) (.neg (.objMem z y)))
          (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.objMem y k) (.objMem y k))))
        (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wa (.classMem (syn_cpw (.cv y)) (.cv n))
            (.classMem (syn_cpw (.cv y)) (.cv n)))))
      (.classMem M (syn_cnnc)) (.classMem (syn_cplc M (syn_c1c)) (syn_cnnc)) p0024 p0038
  have p0040 := @g_nncaddccl (.cv n) (.cv n)
  have p0041 :=
    @g_anidms (.classMem (.cv n) (syn_cnnc))
      (.classMem (syn_cplc (.cv n) (.cv n)) (syn_cnnc)) p0040
  have p0042 :=
    @g_syl
      (syn_wa (syn_w3a (.classMem M (syn_cnnc))
          (syn_wa (.classMem (syn_cpw1 (.cv y)) M) (.neg (.objMem z y)))
          (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.objMem y k) (.objMem y k))))
        (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wa (.classMem (syn_cpw (.cv y)) (.cv n))
            (.classMem (syn_cpw (.cv y)) (.cv n)))))
      (.classMem (.cv n) (syn_cnnc)) (.classMem (syn_cplc (.cv n) (.cv n)) (syn_cnnc))
      p0025 p0041
  have p0043 := @g_pw1un (.cv y) (syn_csn (.cv z))
  have p0044 := @g_vex z
  have p0045 := @g_pw1sn (.cv z) p0044
  have p0046 :=
    @g_uneq2i (syn_cpw1 (syn_csn (.cv z))) (syn_csn (syn_csn (.cv z))) (syn_cpw1 (.cv y))
      p0045
  have p0047 :=
    @g_eqtri (syn_cpw1 (syn_cun (.cv y) (syn_csn (.cv z))))
      (syn_cun (syn_cpw1 (.cv y)) (syn_cpw1 (syn_csn (.cv z))))
      (syn_cun (syn_cpw1 (.cv y)) (syn_csn (syn_csn (.cv z)))) p0043 p0046
  have p0048 :=
    @g_simpl2r (.classMem (syn_cpw1 (.cv y)) M) (.neg (.objMem z y))
      (.classMem M (syn_cnnc))
      (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.objMem y k) (.objMem y k)))
      (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wa (.classMem (syn_cpw (.cv y)) (.cv n))
          (.classMem (syn_cpw (.cv y)) (.cv n))))
  have p0049_e01_recanon :
    Nominal.NPrf
      (syn_wb (.classMem (syn_csn (.cv z)) (syn_cpw1 (.cv y))) (.objMem z y)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_csn syn_cpw1 syn_cin syn_ccompl syn_cnin syn_wnan syn_wa syn_cpw
          syn_wss syn_c1c syn_wex
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
    @g_sylnibr
      (syn_wa (syn_w3a (.classMem M (syn_cnnc))
          (syn_wa (.classMem (syn_cpw1 (.cv y)) M) (.neg (.objMem z y)))
          (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.objMem y k) (.objMem y k))))
        (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wa (.classMem (syn_cpw (.cv y)) (.cv n))
            (.classMem (syn_cpw (.cv y)) (.cv n)))))
      (.objMem z y) (.classMem (syn_csn (.cv z)) (syn_cpw1 (.cv y))) p0048
      p0049_e01_recanon
  have p0050 := @g_elsuci (syn_cpw1 (.cv y)) M (syn_csn (.cv z)) p0008
  have p0051 :=
    @g_syl2anc
      (syn_wa (syn_w3a (.classMem M (syn_cnnc))
          (syn_wa (.classMem (syn_cpw1 (.cv y)) M) (.neg (.objMem z y)))
          (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.objMem y k) (.objMem y k))))
        (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wa (.classMem (syn_cpw (.cv y)) (.cv n))
            (.classMem (syn_cpw (.cv y)) (.cv n)))))
      (.classMem (syn_cpw1 (.cv y)) M)
      (.neg (.classMem (syn_csn (.cv z)) (syn_cpw1 (.cv y))))
      (.classMem (syn_cun (syn_cpw1 (.cv y)) (syn_csn (syn_csn (.cv z))))
        (syn_cplc M (syn_c1c)))
      p0026 p0049 p0050
  have p0052 :=
    @g_syl5eqel
      (syn_wa (syn_w3a (.classMem M (syn_cnnc))
          (syn_wa (.classMem (syn_cpw1 (.cv y)) M) (.neg (.objMem z y)))
          (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.objMem y k) (.objMem y k))))
        (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wa (.classMem (syn_cpw (.cv y)) (.cv n))
            (.classMem (syn_cpw (.cv y)) (.cv n)))))
      (syn_cpw1 (syn_cun (.cv y) (syn_csn (.cv z))))
      (syn_cun (syn_cpw1 (.cv y)) (syn_csn (syn_csn (.cv z)))) (syn_cplc M (syn_c1c))
      p0047 p0051
  have p0053 :=
    @g_simpl3l (.classMem (.cv k) (syn_cnnc)) (syn_wa (.objMem y k) (.objMem y k))
      (.classMem M (syn_cnnc))
      (syn_wa (.classMem (syn_cpw1 (.cv y)) M) (.neg (.objMem z y)))
      (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wa (.classMem (syn_cpw (.cv y)) (.cv n))
          (.classMem (syn_cpw (.cv y)) (.cv n))))
  have p0054 :=
    @g_adantr
      (syn_w3a (.classMem M (syn_cnnc))
        (syn_wa (.classMem (syn_cpw1 (.cv y)) M) (.neg (.objMem z y)))
        (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.objMem y k) (.objMem y k))))
      (.objMem y k)
      (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wa (.classMem (syn_cpw (.cv y)) (.cv n))
          (.classMem (syn_cpw (.cv y)) (.cv n))))
      p0021
  have p0055 := @g_elcompl (.cv z) (.cv y) p0044
  have p0056_e01_recanon :
    Nominal.NPrf (syn_wb (.classMem (.cv z) (syn_ccompl (.cv y))) (.neg (.objMem z y))) :=
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
      p0055
  have p0056 :=
    @g_sylibr
      (syn_wa (syn_w3a (.classMem M (syn_cnnc))
          (syn_wa (.classMem (syn_cpw1 (.cv y)) M) (.neg (.objMem z y)))
          (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.objMem y k) (.objMem y k))))
        (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wa (.classMem (syn_cpw (.cv y)) (.cv n))
            (.classMem (syn_cpw (.cv y)) (.cv n)))))
      (.neg (.objMem z y)) (.classMem (.cv z) (syn_ccompl (.cv y))) p0048
      p0056_e01_recanon
  have p0057 := @g_nnadjoinpw (.cv y) (.cv k) (.cv n) (.cv z)
  have p0058_e05_recanon :
    Nominal.NPrf
      (.imp (syn_w3a (syn_wa (.classMem (.cv k) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc)))
          (syn_wa (.objMem y k) (.classMem (.cv z) (syn_ccompl (.cv y))))
          (.classMem (syn_cpw (.cv y)) (.cv n)))
        (.classMem (syn_cpw (syn_cun (.cv y) (syn_csn (.cv z)))) (syn_cplc (.cv n) (.cv n)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_w3a syn_wa syn_cpw syn_wss syn_cin syn_ccompl syn_cnin syn_wnan
          syn_cplc syn_wrex syn_wex
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
    @g_syl221anc
      (syn_wa (syn_w3a (.classMem M (syn_cnnc))
          (syn_wa (.classMem (syn_cpw1 (.cv y)) M) (.neg (.objMem z y)))
          (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.objMem y k) (.objMem y k))))
        (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wa (.classMem (syn_cpw (.cv y)) (.cv n))
            (.classMem (syn_cpw (.cv y)) (.cv n)))))
      (.classMem (.cv k) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc)) (.objMem y k)
      (.classMem (.cv z) (syn_ccompl (.cv y))) (.classMem (syn_cpw (.cv y)) (.cv n))
      (.classMem (syn_cpw (syn_cun (.cv y) (syn_csn (.cv z)))) (syn_cplc (.cv n) (.cv n)))
      p0053 p0025 p0054 p0056 p0027 p0058_e05_recanon
  have p0059 := @g_unex (.cv y) (syn_csn (.cv z)) p0028 p0008
  have p0060 := @g_pw1eq (.cv a) (syn_cun (.cv y) (syn_csn (.cv z)))
  have p0061 :=
    @g_eleq1d (.classEq (.cv a) (syn_cun (.cv y) (syn_csn (.cv z)))) (syn_cpw1 (.cv a))
      (syn_cpw1 (syn_cun (.cv y) (syn_csn (.cv z)))) (syn_cplc M (syn_c1c)) p0060
  have p0062 := @g_pweq (.cv a) (syn_cun (.cv y) (syn_csn (.cv z)))
  have p0063 :=
    @g_eleq1d (.classEq (.cv a) (syn_cun (.cv y) (syn_csn (.cv z)))) (syn_cpw (.cv a))
      (syn_cpw (syn_cun (.cv y) (syn_csn (.cv z)))) (syn_cplc (.cv n) (.cv n)) p0062
  have p0064 :=
    @g_anbi12d (.classEq (.cv a) (syn_cun (.cv y) (syn_csn (.cv z))))
      (.classMem (syn_cpw1 (.cv a)) (syn_cplc M (syn_c1c)))
      (.classMem (syn_cpw1 (syn_cun (.cv y) (syn_csn (.cv z)))) (syn_cplc M (syn_c1c)))
      (.classMem (syn_cpw (.cv a)) (syn_cplc (.cv n) (.cv n)))
      (.classMem (syn_cpw (syn_cun (.cv y) (syn_csn (.cv z)))) (syn_cplc (.cv n) (.cv n)))
      p0061 p0063
  have p0065 :=
    @g_spcev
      (syn_wa (.classMem (syn_cpw1 (.cv a)) (syn_cplc M (syn_c1c)))
        (.classMem (syn_cpw (.cv a)) (syn_cplc (.cv n) (.cv n))))
      (syn_wa (.classMem (syn_cpw1 (syn_cun (.cv y) (syn_csn (.cv z)))) (syn_cplc M (syn_c1c)))
        (.classMem (syn_cpw (syn_cun (.cv y) (syn_csn (.cv z)))) (syn_cplc (.cv n) (.cv n))))
      a (syn_cun (.cv y) (syn_csn (.cv z))) dv_cache_0019 dv_cache_0020 p0059 p0064
  have p0066 :=
    @g_syl2anc
      (syn_wa (syn_w3a (.classMem M (syn_cnnc))
          (syn_wa (.classMem (syn_cpw1 (.cv y)) M) (.neg (.objMem z y)))
          (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.objMem y k) (.objMem y k))))
        (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wa (.classMem (syn_cpw (.cv y)) (.cv n))
            (.classMem (syn_cpw (.cv y)) (.cv n)))))
      (.classMem (syn_cpw1 (syn_cun (.cv y) (syn_csn (.cv z)))) (syn_cplc M (syn_c1c)))
      (.classMem (syn_cpw (syn_cun (.cv y) (syn_csn (.cv z)))) (syn_cplc (.cv n) (.cv n)))
      (syn_wex a (syn_wa (.classMem (syn_cpw1 (.cv a)) (syn_cplc M (syn_c1c)))
          (.classMem (syn_cpw (.cv a)) (syn_cplc (.cv n) (.cv n)))))
      p0052 p0058 p0065
  have p0067 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_sfin
      (syn_cplc M (syn_c1c)) (syn_cplc (.cv n) (.cv n)) a dv_cache_0021 dv_cache_0022
  have p0068 :=
    @g_syl3anbrc
      (syn_wa (syn_w3a (.classMem M (syn_cnnc))
          (syn_wa (.classMem (syn_cpw1 (.cv y)) M) (.neg (.objMem z y)))
          (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.objMem y k) (.objMem y k))))
        (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wa (.classMem (syn_cpw (.cv y)) (.cv n))
            (.classMem (syn_cpw (.cv y)) (.cv n)))))
      (.classMem (syn_cplc M (syn_c1c)) (syn_cnnc))
      (.classMem (syn_cplc (.cv n) (.cv n)) (syn_cnnc))
      (syn_wex a (syn_wa (.classMem (syn_cpw1 (.cv a)) (syn_cplc M (syn_c1c)))
          (.classMem (syn_cpw (.cv a)) (syn_cplc (.cv n) (.cv n)))))
      (syn_wsfin (syn_cplc M (syn_c1c)) (syn_cplc (.cv n) (.cv n))) p0039 p0042 p0066
      p0067
  have p0069 :=
    @g_jca
      (syn_wa (syn_w3a (.classMem M (syn_cnnc))
          (syn_wa (.classMem (syn_cpw1 (.cv y)) M) (.neg (.objMem z y)))
          (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.objMem y k) (.objMem y k))))
        (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wa (.classMem (syn_cpw (.cv y)) (.cv n))
            (.classMem (syn_cpw (.cv y)) (.cv n)))))
      (syn_wsfin M (.cv n)) (syn_wsfin (syn_cplc M (syn_c1c)) (syn_cplc (.cv n) (.cv n)))
      p0037 p0068
  have p0070 :=
    @g_expr
      (syn_w3a (.classMem M (syn_cnnc))
        (syn_wa (.classMem (syn_cpw1 (.cv y)) M) (.neg (.objMem z y)))
        (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.objMem y k) (.objMem y k))))
      (.classMem (.cv n) (syn_cnnc))
      (syn_wa (.classMem (syn_cpw (.cv y)) (.cv n)) (.classMem (syn_cpw (.cv y)) (.cv n)))
      (syn_wa (syn_wsfin M (.cv n))
        (syn_wsfin (syn_cplc M (syn_c1c)) (syn_cplc (.cv n) (.cv n))))
      p0069
  have p0071 :=
    @g_reximdva
      (syn_w3a (.classMem M (syn_cnnc))
        (syn_wa (.classMem (syn_cpw1 (.cv y)) M) (.neg (.objMem z y)))
        (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.objMem y k) (.objMem y k))))
      (syn_wa (.classMem (syn_cpw (.cv y)) (.cv n)) (.classMem (syn_cpw (.cv y)) (.cv n)))
      (syn_wa (syn_wsfin M (.cv n))
        (syn_wsfin (syn_cplc M (syn_c1c)) (syn_cplc (.cv n) (.cv n))))
      n (syn_cnnc) dv_cache_0023 p0070
  have p0072 :=
    @g_mpd
      (syn_w3a (.classMem M (syn_cnnc))
        (syn_wa (.classMem (syn_cpw1 (.cv y)) M) (.neg (.objMem z y)))
        (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.objMem y k) (.objMem y k))))
      (syn_wrex n (syn_cnnc) (syn_wa (.classMem (syn_cpw (.cv y)) (.cv n))
          (.classMem (syn_cpw (.cv y)) (.cv n))))
      (syn_wrex n (syn_cnnc) (syn_wa (syn_wsfin M (.cv n))
          (syn_wsfin (syn_cplc M (syn_c1c)) (syn_cplc (.cv n) (.cv n)))))
      p0023 p0071
  have p0073 :=
    @g_n_3expa (.classMem M (syn_cnnc))
      (syn_wa (.classMem (syn_cpw1 (.cv y)) M) (.neg (.objMem z y)))
      (syn_wa (.classMem (.cv k) (syn_cnnc)) (syn_wa (.objMem y k) (.objMem y k)))
      (syn_wrex n (syn_cnnc) (syn_wa (syn_wsfin M (.cv n))
          (syn_wsfin (syn_cplc M (syn_c1c)) (syn_cplc (.cv n) (.cv n)))))
      p0072
  have p0074 :=
    @g_expr
      (syn_wa (.classMem M (syn_cnnc))
        (syn_wa (.classMem (syn_cpw1 (.cv y)) M) (.neg (.objMem z y))))
      (.classMem (.cv k) (syn_cnnc)) (syn_wa (.objMem y k) (.objMem y k))
      (syn_wrex n (syn_cnnc) (syn_wa (syn_wsfin M (.cv n))
          (syn_wsfin (syn_cplc M (syn_c1c)) (syn_cplc (.cv n) (.cv n)))))
      p0073
  have p0075 :=
    @g_rexlimdva
      (syn_wa (.classMem M (syn_cnnc))
        (syn_wa (.classMem (syn_cpw1 (.cv y)) M) (.neg (.objMem z y))))
      (syn_wa (.objMem y k) (.objMem y k))
      (syn_wrex n (syn_cnnc) (syn_wa (syn_wsfin M (.cv n))
          (syn_wsfin (syn_cplc M (syn_c1c)) (syn_cplc (.cv n) (.cv n)))))
      k (syn_cnnc) dv_cache_0024 dv_cache_0025 p0074
  have p0076 :=
    @g_mpd
      (syn_wa (.classMem M (syn_cnnc))
        (syn_wa (.classMem (syn_cpw1 (.cv y)) M) (.neg (.objMem z y))))
      (syn_wrex k (syn_cnnc) (syn_wa (.objMem y k) (.objMem y k)))
      (syn_wrex n (syn_cnnc) (syn_wa (syn_wsfin M (.cv n))
          (syn_wsfin (syn_cplc M (syn_c1c)) (syn_cplc (.cv n) (.cv n)))))
      p0019 p0075
  have p0077 :=
    @g_syl6bi
      (syn_wa (.classEq (.cv b) (syn_cpw1 (.cv y))) (.classEq (.cv x) (syn_csn (.cv z))))
      (syn_wa (.classMem M (syn_cnnc))
        (syn_wa (.classMem (.cv b) M) (.classMem (.cv x) (syn_ccompl (.cv b)))))
      (syn_wa (.classMem M (syn_cnnc))
        (syn_wa (.classMem (syn_cpw1 (.cv y)) M) (.neg (.objMem z y))))
      (syn_wrex n (syn_cnnc) (syn_wa (syn_wsfin M (.cv n))
          (syn_wsfin (syn_cplc M (syn_c1c)) (syn_cplc (.cv n) (.cv n)))))
      p0016 p0076
  have p0078 :=
    @g_n_3adant1 (.classEq (.cv b) (syn_cpw1 (.cv y)))
      (.classEq (.cv x) (syn_csn (.cv z)))
      (.imp (syn_wa (.classMem M (syn_cnnc))
          (syn_wa (.classMem (.cv b) M) (.classMem (.cv x) (syn_ccompl (.cv b)))))
        (syn_wrex n (syn_cnnc) (syn_wa (syn_wsfin M (.cv n))
            (syn_wsfin (syn_cplc M (syn_c1c)) (syn_cplc (.cv n) (.cv n))))))
      (.classEq A (syn_cun (.cv y) (syn_csn (.cv z)))) p0077
  have p0079 :=
    @g_com12
      (syn_w3a (.classEq A (syn_cun (.cv y) (syn_csn (.cv z))))
        (.classEq (.cv b) (syn_cpw1 (.cv y))) (.classEq (.cv x) (syn_csn (.cv z))))
      (syn_wa (.classMem M (syn_cnnc))
        (syn_wa (.classMem (.cv b) M) (.classMem (.cv x) (syn_ccompl (.cv b)))))
      (syn_wrex n (syn_cnnc) (syn_wa (syn_wsfin M (.cv n))
          (syn_wsfin (syn_cplc M (syn_c1c)) (syn_cplc (.cv n) (.cv n)))))
      p0078
  have p0080 :=
    @g_exlimdvv
      (syn_wa (.classMem M (syn_cnnc))
        (syn_wa (.classMem (.cv b) M) (.classMem (.cv x) (syn_ccompl (.cv b)))))
      (syn_w3a (.classEq A (syn_cun (.cv y) (syn_csn (.cv z))))
        (.classEq (.cv b) (syn_cpw1 (.cv y))) (.classEq (.cv x) (syn_csn (.cv z))))
      (syn_wrex n (syn_cnnc) (syn_wa (syn_wsfin M (.cv n))
          (syn_wsfin (syn_cplc M (syn_c1c)) (syn_cplc (.cv n) (.cv n)))))
      y z dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 p0079
  have p0081 :=
    @g_syl5bi (.classEq (syn_cpw1 A) (syn_cun (.cv b) (syn_csn (.cv x))))
      (syn_wex y (syn_wex z (syn_w3a (.classEq A (syn_cun (.cv y) (syn_csn (.cv z))))
            (.classEq (.cv b) (syn_cpw1 (.cv y))) (.classEq (.cv x) (syn_csn (.cv z))))))
      (syn_wa (.classMem M (syn_cnnc))
        (syn_wa (.classMem (.cv b) M) (.classMem (.cv x) (syn_ccompl (.cv b)))))
      (syn_wrex n (syn_cnnc) (syn_wa (syn_wsfin M (.cv n))
          (syn_wsfin (syn_cplc M (syn_c1c)) (syn_cplc (.cv n) (.cv n)))))
      p0003 p0080
  have p0082 :=
    @g_rexlimdvva (.classMem M (syn_cnnc))
      (.classEq (syn_cpw1 A) (syn_cun (.cv b) (syn_csn (.cv x))))
      (syn_wrex n (syn_cnnc) (syn_wa (syn_wsfin M (.cv n))
          (syn_wsfin (syn_cplc M (syn_c1c)) (syn_cplc (.cv n) (.cv n)))))
      b x M (syn_ccompl (.cv b)) dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033
      dv_cache_0034 dv_cache_0004 p0081
  have p0083 :=
    @g_imp (.classMem M (syn_cnnc))
      (syn_wrex b M (syn_wrex x (syn_ccompl (.cv b))
          (.classEq (syn_cpw1 A) (syn_cun (.cv b) (syn_csn (.cv x))))))
      (syn_wrex n (syn_cnnc) (syn_wa (syn_wsfin M (.cv n))
          (syn_wsfin (syn_cplc M (syn_c1c)) (syn_cplc (.cv n) (.cv n)))))
      p0082
  have p0084 :=
    @g_sylan2b (.classMem (syn_cpw1 A) (syn_cplc M (syn_c1c))) (.classMem M (syn_cnnc))
      (syn_wrex b M (syn_wrex x (syn_ccompl (.cv b))
          (.classEq (syn_cpw1 A) (syn_cun (.cv b) (syn_csn (.cv x))))))
      (syn_wrex n (syn_cnnc) (syn_wa (syn_wsfin M (.cv n))
          (syn_wsfin (syn_cplc M (syn_c1c)) (syn_cplc (.cv n) (.cv n)))))
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

@[expose]
noncomputable def g_sfintfinlem1 (m : Var) (n : Var) (dv_m_n : m ≠ n) :
    Nominal.NPrf
      (.classMem (.cab m (.all n (.imp (syn_wsfin (.cv m) (.cv n))
              (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv n)))))) (syn_cvv)) :=
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
      ((syn_ccnvk (syn_cdif (syn_csik (syn_cin (syn_cxpk (syn_cnnc) (syn_cnnc)) (syn_cimak
                  (syn_cin (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik
                              (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak
                                  (syn_csymdif (syn_cins3k (syn_cssetk))
                                    (syn_cins2k (syn_csik (syn_cssetk))))
                                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                          (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                    (syn_cins2k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
                                  (syn_csymdif (syn_cins3k (syn_cssetk))
                                    (syn_cins2k (syn_csik (syn_cssetk))))
                                  (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins2k (syn_cssetk)))
                        (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cimak (syn_cin (syn_cins2k
                  (syn_ccnvk (syn_cun (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0)))
                      (syn_cdif (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                              (syn_cins3k (syn_cimak
                                  (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k
                                      (syn_cimak (syn_csymdif (syn_cins2k
        (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak (syn_cin
        (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin (syn_cins3k
        (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif
        (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1
        (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins3k (syn_cidk)))
                                        (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_c1c)))))
                            (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                        (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv)))))) (syn_cins3k
                  (syn_cimak (syn_cin (syn_cins2k (syn_ccnvk (syn_cun
                            (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0))) (syn_cdif
                              (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                                    (syn_cins3k (syn_cimak
                                        (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk)))
        (syn_cins2k (syn_cimak (syn_csymdif (syn_cins2k (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv))
        (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin
        (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak
        (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1
        (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
        (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_c1c)))))
                                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                              (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv)))))) (syn_cins3k
                        (syn_cin (syn_cxpk (syn_cnnc) (syn_cnnc)) (syn_cimak (syn_cin
                              (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik
                                        (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv))
        (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk))))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk)))
                                  (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cins2k (syn_cimak
                                  (syn_cin (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
        (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk))))
        (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins2k (syn_cssetk)))
                                  (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                    (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_c1c)))))).fv :=
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
  have dv_cache_0002 : t ∉ ((syn_c1c)).fv :=
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
  have dv_cache_0003 : t ∉ ((syn_csn (.cv m))).fv :=
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
      ((Wff.classMem (syn_copk (.cv t) (syn_csn (.cv m))) (syn_ccnvk (syn_cdif (syn_csik
                (syn_cin (syn_cxpk (syn_cnnc) (syn_cnnc)) (syn_cimak (syn_cin (syn_cins3k
                        (syn_cimak (syn_cin (syn_cins3k (syn_csik
                                (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak
                                    (syn_csymdif (syn_cins3k (syn_cssetk))
                                      (syn_cins2k (syn_csik (syn_cssetk))))
                                    (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                            (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                      (syn_cins2k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_ccompl
                                  (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk))
                                      (syn_cins2k (syn_csik (syn_cssetk))))
                                    (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                            (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                    (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cimak (syn_cin
                  (syn_cins2k (syn_ccnvk
                      (syn_cun (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0)))
                        (syn_cdif (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                                (syn_cins3k (syn_cimak
                                    (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k
                                        (syn_cimak (syn_csymdif (syn_cins2k
        (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak (syn_cin
        (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin (syn_cins3k
        (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif
        (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1
        (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins3k (syn_cidk)))
        (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                          (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv)))))) (syn_cins3k
                    (syn_cimak (syn_cin (syn_cins2k (syn_ccnvk (syn_cun
                              (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0)))
                              (syn_cdif (syn_ccompl (syn_cimak
                                    (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
                                        (syn_cimak
        (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k (syn_cimak (syn_csymdif
        (syn_cins2k (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak (syn_cin (syn_cins2k
        (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif
        (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k
        (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1
        (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c)))))
        (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                                (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv))))))
                        (syn_cins3k (syn_cin (syn_cxpk (syn_cnnc) (syn_cnnc)) (syn_cimak
                              (syn_cin (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik
        (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak
        (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk)))
                                    (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cins2k (syn_cimak
                                    (syn_cin (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
        (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk))))
        (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins2k (syn_cssetk)))
                                    (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                      (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_c1c))))))).fv :=
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
  have dv_cache_0006 : t ∉ ((syn_csn (.cv n))).fv :=
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
      ((Wff.classMem (syn_copk (syn_csn (.cv n)) (syn_csn (.cv m))) (syn_ccnvk (syn_cdif
              (syn_csik (syn_cin (syn_cxpk (syn_cnnc) (syn_cnnc)) (syn_cimak (syn_cin
                      (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik
                                (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak
                                    (syn_csymdif (syn_cins3k (syn_cssetk))
                                      (syn_cins2k (syn_csik (syn_cssetk))))
                                    (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                            (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                      (syn_cins2k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_ccompl
                                  (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk))
                                      (syn_cins2k (syn_csik (syn_cssetk))))
                                    (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                            (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                    (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cimak (syn_cin
                  (syn_cins2k (syn_ccnvk
                      (syn_cun (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0)))
                        (syn_cdif (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                                (syn_cins3k (syn_cimak
                                    (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k
                                        (syn_cimak (syn_csymdif (syn_cins2k
        (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak (syn_cin
        (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin (syn_cins3k
        (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif
        (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1
        (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins3k (syn_cidk)))
        (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                          (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv)))))) (syn_cins3k
                    (syn_cimak (syn_cin (syn_cins2k (syn_ccnvk (syn_cun
                              (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0)))
                              (syn_cdif (syn_ccompl (syn_cimak
                                    (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
                                        (syn_cimak
        (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k (syn_cimak (syn_csymdif
        (syn_cins2k (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak (syn_cin (syn_cins2k
        (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif
        (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k
        (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1
        (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c)))))
        (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                                (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv))))))
                        (syn_cins3k (syn_cin (syn_cxpk (syn_cnnc) (syn_cnnc)) (syn_cimak
                              (syn_cin (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik
        (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak
        (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk)))
                                    (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cins2k (syn_cimak
                                    (syn_cin (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
        (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk))))
        (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins2k (syn_cssetk)))
                                    (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                      (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_c1c))))))).fv :=
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
      ((syn_cin (syn_cins2k (syn_ccnvk
              (syn_cun (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0))) (syn_cdif
                  (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
                          (syn_cimak (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k
                                (syn_cimak (syn_csymdif (syn_cins2k
                                      (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak
        (syn_cin (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin
        (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak
        (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                                    (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c)))))
                            (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                  (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv)))))) (syn_cins3k (syn_cimak
              (syn_cin (syn_cins2k (syn_ccnvk
                    (syn_cun (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0)))
                      (syn_cdif (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                              (syn_cins3k (syn_cimak
                                  (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k
                                      (syn_cimak (syn_csymdif (syn_cins2k
        (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak (syn_cin
        (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin (syn_cins3k
        (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif
        (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1
        (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins3k (syn_cidk)))
                                        (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_c1c)))))
                            (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                        (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv)))))) (syn_cins3k
                  (syn_cin (syn_cxpk (syn_cnnc) (syn_cnnc)) (syn_cimak (syn_cin (syn_cins3k
                          (syn_cimak (syn_cin (syn_cins3k (syn_csik
                                  (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak
                                      (syn_csymdif (syn_cins3k (syn_cssetk))
                                        (syn_cins2k (syn_csik (syn_cssetk))))
                                      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                              (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                        (syn_cins2k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_ccompl
                                    (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk))
                                        (syn_cins2k (syn_csik (syn_cssetk))))
                                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                              (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
              (syn_cpw1 (syn_c1c)))))).fv :=
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
  have dv_cache_0009 : t ∉ ((syn_cpw1 (syn_c1c))).fv :=
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
  have dv_cache_0010 : t ∉ ((syn_copk (syn_csn (.cv m)) (syn_csn (.cv n)))).fv :=
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
      ((Wff.classMem (syn_copk (.cv t) (syn_copk (syn_csn (.cv m)) (syn_csn (.cv n)))) (syn_cin
            (syn_cins2k (syn_ccnvk
                (syn_cun (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0))) (syn_cdif
                    (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
                            (syn_cimak (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk)))
                                (syn_cins2k (syn_cimak (syn_csymdif (syn_cins2k
                                        (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak
        (syn_cin (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin
        (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak
        (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                                      (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c)))))
                              (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                    (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv)))))) (syn_cins3k (syn_cimak
                (syn_cin (syn_cins2k (syn_ccnvk
                      (syn_cun (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0)))
                        (syn_cdif (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                                (syn_cins3k (syn_cimak
                                    (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k
                                        (syn_cimak (syn_csymdif (syn_cins2k
        (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak (syn_cin
        (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin (syn_cins3k
        (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif
        (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1
        (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins3k (syn_cidk)))
        (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                          (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv)))))) (syn_cins3k
                    (syn_cin (syn_cxpk (syn_cnnc) (syn_cnnc)) (syn_cimak (syn_cin (syn_cins3k
                            (syn_cimak (syn_cin (syn_cins3k (syn_csik
                                    (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv))
                                      (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk))
        (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                                (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                          (syn_cins2k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_ccompl
                                      (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk))
        (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                                (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                (syn_cpw1 (syn_c1c))))))).fv :=
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
  have dv_cache_0013 : t ∉ ((syn_csn (syn_csn (.cv y)))).fv :=
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
      ((Wff.classMem (syn_copk (syn_csn (syn_csn (.cv y)))
            (syn_copk (syn_csn (.cv m)) (syn_csn (.cv n)))) (syn_cin (syn_cins2k (syn_ccnvk
                (syn_cun (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0))) (syn_cdif
                    (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
                            (syn_cimak (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk)))
                                (syn_cins2k (syn_cimak (syn_csymdif (syn_cins2k
                                        (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak
        (syn_cin (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin
        (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak
        (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                                      (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c)))))
                              (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                    (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv)))))) (syn_cins3k (syn_cimak
                (syn_cin (syn_cins2k (syn_ccnvk
                      (syn_cun (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0)))
                        (syn_cdif (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                                (syn_cins3k (syn_cimak
                                    (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k
                                        (syn_cimak (syn_csymdif (syn_cins2k
        (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak (syn_cin
        (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin (syn_cins3k
        (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif
        (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1
        (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins3k (syn_cidk)))
        (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                          (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv)))))) (syn_cins3k
                    (syn_cin (syn_cxpk (syn_cnnc) (syn_cnnc)) (syn_cimak (syn_cin (syn_cins3k
                            (syn_cimak (syn_cin (syn_cins3k (syn_csik
                                    (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv))
                                      (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk))
        (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                                (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                          (syn_cins2k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_ccompl
                                      (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk))
        (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                                (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                (syn_cpw1 (syn_c1c))))))).fv :=
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
      ((syn_cin (syn_cins2k (syn_ccnvk
              (syn_cun (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0))) (syn_cdif
                  (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
                          (syn_cimak (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k
                                (syn_cimak (syn_csymdif (syn_cins2k
                                      (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak
        (syn_cin (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin
        (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak
        (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                                    (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c)))))
                            (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                  (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv)))))) (syn_cins3k
            (syn_cin (syn_cxpk (syn_cnnc) (syn_cnnc)) (syn_cimak (syn_cin (syn_cins3k (syn_cimak
                      (syn_cin (syn_cins3k (syn_csik
                            (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak
                                (syn_csymdif (syn_cins3k (syn_cssetk))
                                  (syn_cins2k (syn_csik (syn_cssetk))))
                                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                        (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cins2k
                    (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
                                (syn_csymdif (syn_cins3k (syn_cssetk))
                                  (syn_cins2k (syn_csik (syn_cssetk))))
                                (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins2k (syn_cssetk)))
                      (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))).fv :=
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
  have dv_cache_0016 : t ∉ ((syn_copk (.cv y) (syn_csn (.cv m)))).fv :=
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
      ((Wff.classMem (syn_copk (.cv t) (syn_copk (.cv y) (syn_csn (.cv m)))) (syn_cin
            (syn_cins2k (syn_ccnvk
                (syn_cun (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0))) (syn_cdif
                    (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
                            (syn_cimak (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk)))
                                (syn_cins2k (syn_cimak (syn_csymdif (syn_cins2k
                                        (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak
        (syn_cin (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin
        (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak
        (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                                      (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c)))))
                              (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                    (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv)))))) (syn_cins3k
              (syn_cin (syn_cxpk (syn_cnnc) (syn_cnnc)) (syn_cimak (syn_cin (syn_cins3k
                      (syn_cimak (syn_cin (syn_cins3k (syn_csik
                              (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak
                                  (syn_csymdif (syn_cins3k (syn_cssetk))
                                    (syn_cins2k (syn_csik (syn_cssetk))))
                                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                          (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                    (syn_cins2k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
                                  (syn_csymdif (syn_cins3k (syn_cssetk))
                                    (syn_cins2k (syn_csik (syn_cssetk))))
                                  (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins2k (syn_cssetk)))
                        (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))).fv :=
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
  have dv_cache_0019 : t ∉ ((syn_csn (syn_csn (.cv x)))).fv :=
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
      ((Wff.classMem (syn_copk (syn_csn (syn_csn (.cv x))) (syn_copk (.cv y) (syn_csn (.cv m))))
          (syn_cin (syn_cins2k (syn_ccnvk
                (syn_cun (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0))) (syn_cdif
                    (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
                            (syn_cimak (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk)))
                                (syn_cins2k (syn_cimak (syn_csymdif (syn_cins2k
                                        (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak
        (syn_cin (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin
        (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak
        (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                                      (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c)))))
                              (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                    (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv)))))) (syn_cins3k
              (syn_cin (syn_cxpk (syn_cnnc) (syn_cnnc)) (syn_cimak (syn_cin (syn_cins3k
                      (syn_cimak (syn_cin (syn_cins3k (syn_csik
                              (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak
                                  (syn_csymdif (syn_cins3k (syn_cssetk))
                                    (syn_cins2k (syn_csik (syn_cssetk))))
                                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                          (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                    (syn_cins2k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
                                  (syn_csymdif (syn_cins3k (syn_cssetk))
                                    (syn_cins2k (syn_csik (syn_cssetk))))
                                  (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins2k (syn_cssetk)))
                        (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))).fv :=
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
  have dv_cache_0021 : x ∉ ((syn_ctfin (.cv m))).fv :=
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
  have dv_cache_0022 : x ∉ ((syn_wsfin (syn_ctfin (.cv m)) (.cv y))).fv :=
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
  have dv_cache_0023 : y ∉ ((syn_ctfin (.cv n))).fv :=
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
  have dv_cache_0024 : y ∉ ((syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv n)))).fv :=
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
      ((syn_cuni1 (syn_ccompl (syn_cimak (syn_ccnvk (syn_cdif (syn_csik
                    (syn_cin (syn_cxpk (syn_cnnc) (syn_cnnc)) (syn_cimak (syn_cin (syn_cins3k
                            (syn_cimak (syn_cin (syn_cins3k (syn_csik
                                    (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv))
                                      (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk))
        (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                                (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                          (syn_cins2k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_ccompl
                                      (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk))
        (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                                (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cimak (syn_cin
                      (syn_cins2k (syn_ccnvk (syn_cun
                            (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0))) (syn_cdif
                              (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                                    (syn_cins3k (syn_cimak
                                        (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk)))
        (syn_cins2k (syn_cimak (syn_csymdif (syn_cins2k (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv))
        (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin
        (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak
        (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1
        (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
        (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_c1c)))))
                                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                              (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv)))))) (syn_cins3k
                        (syn_cimak (syn_cin (syn_cins2k (syn_ccnvk (syn_cun
                                  (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0)))
                                  (syn_cdif (syn_ccompl (syn_cimak
                                        (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
        (syn_cimak (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k (syn_cimak
        (syn_csymdif (syn_cins2k (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak (syn_cin
        (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin (syn_cins3k
        (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif
        (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1
        (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins3k (syn_cidk)))
        (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                                    (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv))))))
                            (syn_cins3k (syn_cin (syn_cxpk (syn_cnnc) (syn_cnnc)) (syn_cimak
                                  (syn_cin (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik
        (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak
        (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk)))
                                        (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cins2k (syn_cimak
                                        (syn_cin (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
        (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk))))
        (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins2k (syn_cssetk)))
                                        (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                          (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_c1c))))) (syn_c1c))))).fv :=
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
    (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk))))
      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))
  let syntaxClass0001 : Class :=
    (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) syntaxClass0000)
  let syntaxClass0002 : Class := (syn_csik syntaxClass0001)
  let syntaxClass0003 : Class := (syn_cins3k syntaxClass0002)
  let syntaxClass0004 : Class := (syn_cin syntaxClass0003 (syn_cins2k (syn_cssetk)))
  let syntaxClass0005 : Class :=
    (syn_cimak syntaxClass0004 (syn_cpw1 (syn_cpw1 (syn_c1c))))
  let syntaxClass0006 : Class := (syn_cins3k syntaxClass0005)
  let syntaxClass0007 : Class :=
    (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk))))
      (syn_cpw1 (syn_cpw1 (syn_c1c))))
  let syntaxClass0008 : Class := (syn_ccompl syntaxClass0007)
  let syntaxClass0009 : Class := (syn_csik syntaxClass0008)
  let syntaxClass0010 : Class := (syn_cins3k syntaxClass0009)
  let syntaxClass0011 : Class := (syn_cin syntaxClass0010 (syn_cins2k (syn_cssetk)))
  let syntaxClass0012 : Class :=
    (syn_cimak syntaxClass0011 (syn_cpw1 (syn_cpw1 (syn_c1c))))
  let syntaxClass0013 : Class := (syn_cins2k syntaxClass0012)
  let syntaxClass0014 : Class := (syn_cin syntaxClass0006 syntaxClass0013)
  let syntaxClass0015 : Class :=
    (syn_cimak syntaxClass0014 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))
  let syntaxClass0016 : Class :=
    (syn_cin (syn_cxpk (syn_cnnc) (syn_cnnc)) syntaxClass0015)
  let syntaxClass0017 : Class := (syn_csik syntaxClass0016)
  let syntaxClass0018 : Class :=
    (syn_cin (syn_cins2k (syn_csik (syn_cssetk))) syntaxClass0006)
  let syntaxClass0019 : Class :=
    (syn_cimak syntaxClass0018 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))
  let syntaxClass0020 : Class := (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) syntaxClass0019)
  let syntaxClass0021 : Class := (syn_cins2k syntaxClass0020)
  let syntaxClass0022 : Class := (syn_csymdif syntaxClass0021 (syn_cins3k (syn_cidk)))
  let syntaxClass0023 : Class := (syn_cimak syntaxClass0022 (syn_cpw1 (syn_c1c)))
  let syntaxClass0024 : Class := (syn_cins2k syntaxClass0023)
  let syntaxClass0025 : Class :=
    (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) syntaxClass0024)
  let syntaxClass0026 : Class := (syn_cimak syntaxClass0025 (syn_cpw1 (syn_c1c)))
  let syntaxClass0027 : Class := (syn_cins3k syntaxClass0026)
  let syntaxClass0028 : Class := (syn_csymdif (syn_cins2k (syn_cssetk)) syntaxClass0027)
  let syntaxClass0029 : Class :=
    (syn_cimak syntaxClass0028 (syn_cpw1 (syn_cpw1 (syn_c1c))))
  let syntaxClass0030 : Class := (syn_ccompl syntaxClass0029)
  let syntaxClass0031 : Class :=
    (syn_cdif syntaxClass0030 (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv)))
  let syntaxClass0032 : Class :=
    (syn_cun (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0))) syntaxClass0031)
  let syntaxClass0033 : Class := (syn_ccnvk syntaxClass0032)
  let syntaxClass0034 : Class := (syn_cins2k syntaxClass0033)
  let syntaxClass0035 : Class := (syn_cins3k syntaxClass0016)
  let syntaxClass0036 : Class := (syn_cin syntaxClass0034 syntaxClass0035)
  let syntaxClass0037 : Class := (syn_cimak syntaxClass0036 (syn_cpw1 (syn_c1c)))
  let syntaxClass0038 : Class := (syn_cins3k syntaxClass0037)
  let syntaxClass0039 : Class := (syn_cin syntaxClass0034 syntaxClass0038)
  let syntaxClass0040 : Class := (syn_cimak syntaxClass0039 (syn_cpw1 (syn_c1c)))
  let syntaxClass0041 : Class := (syn_cdif syntaxClass0017 syntaxClass0040)
  let syntaxClass0042 : Class := (syn_ccnvk syntaxClass0041)
  let syntaxClass0043 : Class := (syn_cimak syntaxClass0042 (syn_c1c))
  let syntaxClass0044 : Class := (syn_ccompl syntaxClass0043)
  let syntaxFormula0045 : Wff :=
    (.classMem (syn_copk (.cv t) (syn_csn (.cv m))) syntaxClass0042)
  let syntaxFormula0046 : Wff := (syn_wa (.classMem (.cv t) (syn_c1c)) syntaxFormula0045)
  let syntaxFormula0047 : Wff :=
    (syn_wa (.classEq (.cv t) (syn_csn (.cv n))) syntaxFormula0045)
  let syntaxFormula0048 : Wff := (syn_wex n syntaxFormula0047)
  let syntaxFormula0049 : Wff := (syn_wrex t (syn_c1c) syntaxFormula0045)
  let syntaxFormula0050 : Wff := (syn_wex t syntaxFormula0047)
  let syntaxFormula0051 : Wff := (syn_wex n syntaxFormula0050)
  let syntaxFormula0052 : Wff :=
    (.classMem (syn_copk (syn_csn (.cv n)) (syn_csn (.cv m))) syntaxClass0042)
  let syntaxFormula0053 : Wff :=
    (.classMem (syn_copk (syn_csn (.cv m)) (syn_csn (.cv n))) syntaxClass0017)
  let syntaxFormula0054 : Wff :=
    (.classMem (syn_copk (.cv t) (syn_copk (syn_csn (.cv m)) (syn_csn (.cv n))))
      syntaxClass0039)
  let syntaxFormula0055 : Wff := (syn_wrex t (syn_cpw1 (syn_c1c)) syntaxFormula0054)
  let syntaxFormula0056 : Wff :=
    (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_c1c))) syntaxFormula0054)
  let syntaxFormula0057 : Wff :=
    (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (.cv y)))) syntaxFormula0054)
  let syntaxFormula0058 : Wff := (syn_wex y syntaxFormula0057)
  let syntaxFormula0059 : Wff := (syn_wex t syntaxFormula0056)
  let syntaxFormula0060 : Wff := (syn_wex t syntaxFormula0057)
  let syntaxFormula0061 : Wff := (syn_wex y syntaxFormula0060)
  let syntaxFormula0062 : Wff :=
    (.classMem (syn_copk (syn_csn (.cv m)) (syn_csn (.cv n))) syntaxClass0040)
  let syntaxClass0063 : Class :=
    (syn_copk (syn_csn (syn_csn (.cv y))) (syn_copk (syn_csn (.cv m)) (syn_csn (.cv n))))
  let syntaxFormula0064 : Wff := (.classMem syntaxClass0063 syntaxClass0039)
  let syntaxFormula0065 : Wff := (.classMem syntaxClass0063 syntaxClass0034)
  let syntaxFormula0066 : Wff :=
    (.classMem (syn_copk (.cv t) (syn_copk (.cv y) (syn_csn (.cv m)))) syntaxClass0036)
  let syntaxFormula0067 : Wff :=
    (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_c1c))) syntaxFormula0066)
  let syntaxFormula0068 : Wff :=
    (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (.cv x)))) syntaxFormula0066)
  let syntaxFormula0069 : Wff := (syn_wex x syntaxFormula0068)
  let syntaxFormula0070 : Wff := (syn_wrex t (syn_cpw1 (syn_c1c)) syntaxFormula0066)
  let syntaxFormula0071 : Wff := (syn_wex t syntaxFormula0068)
  let syntaxFormula0072 : Wff := (syn_wex x syntaxFormula0071)
  let syntaxFormula0073 : Wff :=
    (.classMem (syn_copk (syn_csn (syn_csn (.cv x))) (syn_copk (.cv y) (syn_csn (.cv m))))
      syntaxClass0036)
  let syntaxFormula0074 : Wff :=
    (.classMem (syn_copk (syn_csn (syn_csn (.cv x))) (syn_copk (.cv y) (syn_csn (.cv m))))
      syntaxClass0034)
  let syntaxFormula0075 : Wff :=
    (.classMem (syn_copk (syn_csn (syn_csn (.cv x))) (syn_copk (.cv y) (syn_csn (.cv m))))
      syntaxClass0035)
  let syntaxFormula0076 : Wff :=
    (.classMem (syn_copk (.cv y) (syn_csn (.cv m))) syntaxClass0037)
  let syntaxFormula0077 : Wff := (.classMem syntaxClass0063 syntaxClass0038)
  let syntaxFormula0078 : Wff := (.neg syntaxFormula0062)
  let syntaxFormula0079 : Wff :=
    (.classMem (syn_copk (syn_csn (.cv m)) (syn_csn (.cv n))) syntaxClass0041)
  let syntaxFormula0080 : Wff :=
    (.imp (syn_wsfin (.cv m) (.cv n)) (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv n))))
  let syntaxFormula0081 : Wff := (.neg syntaxFormula0080)
  let syntaxFormula0082 : Wff := (.classMem (syn_csn (.cv m)) syntaxClass0043)
  let syntaxFormula0083 : Wff := (syn_wex n syntaxFormula0081)
  let syntaxFormula0084 : Wff := (.classMem (syn_csn (.cv m)) syntaxClass0044)
  let syntaxFormula0085 : Wff := (.all n syntaxFormula0080)
  let syntaxClass0086 : Class := (syn_cuni1 syntaxClass0044)
  have p0000 := @g_vex m
  have p0001 := @g_eluni1 (.cv m) syntaxClass0044 p0000
  have p0002 := @g_snex (.cv m)
  have p0003 :=
    @g_elimak t syntaxClass0042 (syn_c1c) (syn_csn (.cv m)) dv_cache_0001 dv_cache_0002
      dv_cache_0003 p0002
  have p0004 := @g_el1c n (.cv t) dv_cache_0004
  have p0005 :=
    @g_anbi1i (.classMem (.cv t) (syn_c1c))
      (syn_wex n (.classEq (.cv t) (syn_csn (.cv n)))) syntaxFormula0045 p0004
  have p0006 :=
    @g_n_19_41v (.classEq (.cv t) (syn_csn (.cv n))) syntaxFormula0045 n dv_cache_0005
  have p0007 :=
    @g_bitr4i syntaxFormula0046
      (syn_wa (syn_wex n (.classEq (.cv t) (syn_csn (.cv n)))) syntaxFormula0045)
      syntaxFormula0048 p0005 p0006
  have p0008 := @g_exbii syntaxFormula0046 syntaxFormula0048 t p0007
  have p0009 := (Nominal.biimpRefl syntaxFormula0049)
  have p0010 := @g_excom syntaxFormula0047 n t
  have p0011 :=
    @g_n_3bitr4i (syn_wex t syntaxFormula0046) (syn_wex t syntaxFormula0048)
      syntaxFormula0049 syntaxFormula0051 p0008 p0009 p0010
  have p0012 := @g_snex (.cv n)
  have p0013 := @g_opkeq1 (.cv t) (syn_csn (.cv n)) (syn_csn (.cv m))
  have p0014 :=
    @g_eleq1d (.classEq (.cv t) (syn_csn (.cv n))) (syn_copk (.cv t) (syn_csn (.cv m)))
      (syn_copk (syn_csn (.cv n)) (syn_csn (.cv m))) syntaxClass0042 p0013
  have p0015 :=
    @g_ceqsexv syntaxFormula0045 syntaxFormula0052 t (syn_csn (.cv n)) dv_cache_0006
      dv_cache_0007 p0012 p0014
  have p0016 :=
    @g_opkelcnvk (syn_csn (.cv n)) (syn_csn (.cv m)) syntaxClass0041 p0012 p0002
  have p0017 :=
    @g_eldif (syn_copk (syn_csn (.cv m)) (syn_csn (.cv n))) syntaxClass0017
      syntaxClass0040
  have p0018 := @g_vex n
  have p0019 := @g_opksnelsik (.cv m) (.cv n) syntaxClass0016 p0000 p0018
  have p0020 := @g_srelk (.cv m) (.cv n) p0000 p0018
  have p0021 :=
    @g_bitri syntaxFormula0053 (.classMem (syn_copk (.cv m) (.cv n)) syntaxClass0016)
      (syn_wsfin (.cv m) (.cv n)) p0019 p0020
  have p0022 := @g_opkex (syn_csn (.cv m)) (syn_csn (.cv n))
  have p0023 :=
    @g_elimak t syntaxClass0039 (syn_cpw1 (syn_c1c))
      (syn_copk (syn_csn (.cv m)) (syn_csn (.cv n))) dv_cache_0008 dv_cache_0009
      dv_cache_0010 p0022
  have p0024 := (Nominal.biimpRefl syntaxFormula0055)
  have p0025 := @g_elpw11c y (.cv t) dv_cache_0011
  have p0026 :=
    @g_anbi1i (.classMem (.cv t) (syn_cpw1 (syn_c1c)))
      (syn_wex y (.classEq (.cv t) (syn_csn (syn_csn (.cv y))))) syntaxFormula0054 p0025
  have p0027 :=
    @g_n_19_41v (.classEq (.cv t) (syn_csn (syn_csn (.cv y)))) syntaxFormula0054 y
      dv_cache_0012
  have p0028 :=
    @g_bitr4i syntaxFormula0056
      (syn_wa (syn_wex y (.classEq (.cv t) (syn_csn (syn_csn (.cv y))))) syntaxFormula0054)
      syntaxFormula0058 p0026 p0027
  have p0029 := @g_exbii syntaxFormula0056 syntaxFormula0058 t p0028
  have p0030 := @g_excom syntaxFormula0057 y t
  have p0031 :=
    @g_bitr4i syntaxFormula0059 (syn_wex t syntaxFormula0058) syntaxFormula0061 p0029
      p0030
  have p0032 :=
    @g_n_3bitri syntaxFormula0062 syntaxFormula0055 syntaxFormula0059 syntaxFormula0061
      p0023 p0024 p0031
  have p0033 := @g_snex (syn_csn (.cv y))
  have p0034 :=
    @g_opkeq1 (.cv t) (syn_csn (syn_csn (.cv y)))
      (syn_copk (syn_csn (.cv m)) (syn_csn (.cv n)))
  have p0035 :=
    @g_eleq1d (.classEq (.cv t) (syn_csn (syn_csn (.cv y))))
      (syn_copk (.cv t) (syn_copk (syn_csn (.cv m)) (syn_csn (.cv n)))) syntaxClass0063
      syntaxClass0039 p0034
  have p0036 :=
    @g_ceqsexv syntaxFormula0054 syntaxFormula0064 t (syn_csn (syn_csn (.cv y)))
      dv_cache_0013 dv_cache_0014 p0033 p0035
  have p0037 := @g_elin syntaxClass0063 syntaxClass0034 syntaxClass0038
  have p0038 := @g_vex y
  have p0039 :=
    @g_otkelins2k (.cv y) (syn_csn (.cv m)) (syn_csn (.cv n)) syntaxClass0033 p0038 p0002
      p0012
  have p0040 := @g_opkelcnvk (.cv y) (syn_csn (.cv n)) syntaxClass0032 p0038 p0012
  have p0041 := @g_eqtfinrelk (.cv n) (.cv y) p0018 p0038
  have p0042 :=
    @g_n_3bitri syntaxFormula0065
      (.classMem (syn_copk (.cv y) (syn_csn (.cv n))) syntaxClass0033)
      (.classMem (syn_copk (syn_csn (.cv n)) (.cv y)) syntaxClass0032)
      (.classEq (.cv y) (syn_ctfin (.cv n))) p0039 p0040 p0041
  have p0043 :=
    @g_otkelins3k (.cv y) (syn_csn (.cv m)) (syn_csn (.cv n)) syntaxClass0037 p0038 p0002
      p0012
  have p0044 := @g_opkex (.cv y) (syn_csn (.cv m))
  have p0045 :=
    @g_elimak t syntaxClass0036 (syn_cpw1 (syn_c1c)) (syn_copk (.cv y) (syn_csn (.cv m)))
      dv_cache_0015 dv_cache_0009 dv_cache_0016 p0044
  have p0046 := @g_elpw11c x (.cv t) dv_cache_0017
  have p0047 :=
    @g_anbi1i (.classMem (.cv t) (syn_cpw1 (syn_c1c)))
      (syn_wex x (.classEq (.cv t) (syn_csn (syn_csn (.cv x))))) syntaxFormula0066 p0046
  have p0048 :=
    @g_n_19_41v (.classEq (.cv t) (syn_csn (syn_csn (.cv x)))) syntaxFormula0066 x
      dv_cache_0018
  have p0049 :=
    @g_bitr4i syntaxFormula0067
      (syn_wa (syn_wex x (.classEq (.cv t) (syn_csn (syn_csn (.cv x))))) syntaxFormula0066)
      syntaxFormula0069 p0047 p0048
  have p0050 := @g_exbii syntaxFormula0067 syntaxFormula0069 t p0049
  have p0051 := (Nominal.biimpRefl syntaxFormula0070)
  have p0052 := @g_excom syntaxFormula0068 x t
  have p0053 :=
    @g_n_3bitr4i (syn_wex t syntaxFormula0067) (syn_wex t syntaxFormula0069)
      syntaxFormula0070 syntaxFormula0072 p0050 p0051 p0052
  have p0054 := @g_snex (syn_csn (.cv x))
  have p0055 :=
    @g_opkeq1 (.cv t) (syn_csn (syn_csn (.cv x))) (syn_copk (.cv y) (syn_csn (.cv m)))
  have p0056 :=
    @g_eleq1d (.classEq (.cv t) (syn_csn (syn_csn (.cv x))))
      (syn_copk (.cv t) (syn_copk (.cv y) (syn_csn (.cv m))))
      (syn_copk (syn_csn (syn_csn (.cv x))) (syn_copk (.cv y) (syn_csn (.cv m))))
      syntaxClass0036 p0055
  have p0057 :=
    @g_ceqsexv syntaxFormula0066 syntaxFormula0073 t (syn_csn (syn_csn (.cv x)))
      dv_cache_0019 dv_cache_0020 p0054 p0056
  have p0058 :=
    @g_elin (syn_copk (syn_csn (syn_csn (.cv x))) (syn_copk (.cv y) (syn_csn (.cv m))))
      syntaxClass0034 syntaxClass0035
  have p0059 := @g_vex x
  have p0060 :=
    @g_otkelins2k (.cv x) (.cv y) (syn_csn (.cv m)) syntaxClass0033 p0059 p0038 p0002
  have p0061 := @g_opkelcnvk (.cv x) (syn_csn (.cv m)) syntaxClass0032 p0059 p0002
  have p0062 := @g_eqtfinrelk (.cv m) (.cv x) p0000 p0059
  have p0063 :=
    @g_n_3bitri syntaxFormula0074
      (.classMem (syn_copk (.cv x) (syn_csn (.cv m))) syntaxClass0033)
      (.classMem (syn_copk (syn_csn (.cv m)) (.cv x)) syntaxClass0032)
      (.classEq (.cv x) (syn_ctfin (.cv m))) p0060 p0061 p0062
  have p0064 :=
    @g_otkelins3k (.cv x) (.cv y) (syn_csn (.cv m)) syntaxClass0016 p0059 p0038 p0002
  have p0065 := @g_srelk (.cv x) (.cv y) p0059 p0038
  have p0066 :=
    @g_bitri syntaxFormula0075 (.classMem (syn_copk (.cv x) (.cv y)) syntaxClass0016)
      (syn_wsfin (.cv x) (.cv y)) p0064 p0065
  have p0067 :=
    @g_anbi12i syntaxFormula0074 (.classEq (.cv x) (syn_ctfin (.cv m))) syntaxFormula0075
      (syn_wsfin (.cv x) (.cv y)) p0063 p0066
  have p0068 :=
    @g_n_3bitri syntaxFormula0071 syntaxFormula0073
      (syn_wa syntaxFormula0074 syntaxFormula0075)
      (syn_wa (.classEq (.cv x) (syn_ctfin (.cv m))) (syn_wsfin (.cv x) (.cv y))) p0057
      p0058 p0067
  have p0069 :=
    @g_exbii syntaxFormula0071
      (syn_wa (.classEq (.cv x) (syn_ctfin (.cv m))) (syn_wsfin (.cv x) (.cv y))) x p0068
  have p0070 :=
    @g_n_3bitri syntaxFormula0076 syntaxFormula0070 syntaxFormula0072
      (syn_wex x (syn_wa (.classEq (.cv x) (syn_ctfin (.cv m))) (syn_wsfin (.cv x) (.cv y))))
      p0045 p0053 p0069
  have p0071 := @g_tfinex (.cv m)
  have p0072 := @g_sfineq1 (.cv x) (syn_ctfin (.cv m)) (.cv y)
  have p0073 :=
    @g_ceqsexv (syn_wsfin (.cv x) (.cv y)) (syn_wsfin (syn_ctfin (.cv m)) (.cv y)) x
      (syn_ctfin (.cv m)) dv_cache_0021 dv_cache_0022 p0071 p0072
  have p0074 :=
    @g_n_3bitri syntaxFormula0077 syntaxFormula0076
      (syn_wex x (syn_wa (.classEq (.cv x) (syn_ctfin (.cv m))) (syn_wsfin (.cv x) (.cv y))))
      (syn_wsfin (syn_ctfin (.cv m)) (.cv y)) p0043 p0070 p0073
  have p0075 :=
    @g_anbi12i syntaxFormula0065 (.classEq (.cv y) (syn_ctfin (.cv n))) syntaxFormula0077
      (syn_wsfin (syn_ctfin (.cv m)) (.cv y)) p0042 p0074
  have p0076 :=
    @g_n_3bitri syntaxFormula0060 syntaxFormula0064
      (syn_wa syntaxFormula0065 syntaxFormula0077)
      (syn_wa (.classEq (.cv y) (syn_ctfin (.cv n))) (syn_wsfin (syn_ctfin (.cv m)) (.cv y)))
      p0036 p0037 p0075
  have p0077 :=
    @g_exbii syntaxFormula0060
      (syn_wa (.classEq (.cv y) (syn_ctfin (.cv n))) (syn_wsfin (syn_ctfin (.cv m)) (.cv y)))
      y p0076
  have p0078 := @g_tfinex (.cv n)
  have p0079 := @g_sfineq2 (.cv y) (syn_ctfin (.cv n)) (syn_ctfin (.cv m))
  have p0080 :=
    @g_ceqsexv (syn_wsfin (syn_ctfin (.cv m)) (.cv y))
      (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv n))) y (syn_ctfin (.cv n))
      dv_cache_0023 dv_cache_0024 p0078 p0079
  have p0081 :=
    @g_n_3bitri syntaxFormula0062 syntaxFormula0061
      (syn_wex y (syn_wa (.classEq (.cv y) (syn_ctfin (.cv n)))
          (syn_wsfin (syn_ctfin (.cv m)) (.cv y))))
      (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv n))) p0032 p0077 p0080
  have p0082 :=
    @g_notbii syntaxFormula0062 (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv n))) p0081
  have p0083 :=
    @g_anbi12i syntaxFormula0053 (syn_wsfin (.cv m) (.cv n)) syntaxFormula0078
      (.neg (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv n)))) p0021 p0082
  have p0084 :=
    @g_annim (syn_wsfin (.cv m) (.cv n))
      (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv n)))
  have p0085 :=
    @g_n_3bitri syntaxFormula0079 (syn_wa syntaxFormula0053 syntaxFormula0078)
      (syn_wa (syn_wsfin (.cv m) (.cv n))
        (.neg (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv n)))))
      syntaxFormula0081 p0017 p0083 p0084
  have p0086 :=
    @g_n_3bitri syntaxFormula0050 syntaxFormula0052 syntaxFormula0079 syntaxFormula0081
      p0015 p0016 p0085
  have p0087 := @g_exbii syntaxFormula0050 syntaxFormula0081 n p0086
  have p0088 :=
    @g_n_3bitri syntaxFormula0082 syntaxFormula0049 syntaxFormula0051 syntaxFormula0083
      p0003 p0011 p0087
  have p0089 := @g_notbii syntaxFormula0082 syntaxFormula0083 p0088
  have p0090 := @g_elcompl (syn_csn (.cv m)) syntaxClass0043 p0002
  have p0091 := @g_alex syntaxFormula0080 n
  have p0092 :=
    @g_n_3bitr4i (.neg syntaxFormula0082) (.neg syntaxFormula0083) syntaxFormula0084
      syntaxFormula0085 p0089 p0090 p0091
  have p0093 :=
    @g_bitri (.classMem (.cv m) syntaxClass0086) syntaxFormula0084 syntaxFormula0085 p0001
      p0092
  have p0094 := @g_eqabi syntaxFormula0085 m syntaxClass0086 dv_cache_0025 p0093
  have p0095 := @g_srelkex
  have p0096 := @g_sikex syntaxClass0016 p0095
  have p0097 := @g_tfinrelkex
  have p0098 := @g_cnvkex syntaxClass0032 p0097
  have p0099 := @g_ins2kex syntaxClass0033 p0098
  have p0101 := @g_ins3kex syntaxClass0016 p0095
  have p0102 := @g_inex syntaxClass0034 syntaxClass0035 p0099 p0101
  have p0103 := @g_n_1cex
  have p0104 := @g_pw1ex (syn_c1c) p0103
  have p0105 := @g_imakex syntaxClass0036 (syn_cpw1 (syn_c1c)) p0102 p0104
  have p0106 := @g_ins3kex syntaxClass0037 p0105
  have p0107 := @g_inex syntaxClass0034 syntaxClass0038 p0099 p0106
  have p0108 := @g_imakex syntaxClass0039 (syn_cpw1 (syn_c1c)) p0107 p0104
  have p0109 := @g_difex syntaxClass0017 syntaxClass0040 p0096 p0108
  have p0110 := @g_cnvkex syntaxClass0041 p0109
  have p0112 := @g_imakex syntaxClass0042 (syn_c1c) p0110 p0103
  have p0113 := @g_complex syntaxClass0043 p0112
  have p0114 := @g_uni1ex syntaxClass0044 p0113
  have p0115 :=
    @g_eqeltrri syntaxClass0086 (.cab m syntaxFormula0085) (syn_cvv) p0094 p0114
  exact p0115


end NFChoice.DirectNominalPrf.WPPReplay

end
