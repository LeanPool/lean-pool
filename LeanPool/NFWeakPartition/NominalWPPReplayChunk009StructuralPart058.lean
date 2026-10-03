/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module


public import LeanPool.NFWeakPartition.Certificates.NominalWPPReplayChunk009StructuralBlock012

/-! NF weak partition development: NominalWPPReplayChunk009StructuralPart058. -/


public section


namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_evenfinex : Nominal.NPrf (.classMem (syn_cevenfin) (syn_cvv)) :=
  by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let x : Var := freshVar proofSupport 0
  let n : Var := freshVar proofSupport 1
  let a : Var := freshVar proofSupport 2
  let t : Var := freshVar proofSupport 3
  let c : Var := freshVar proofSupport 4
  let b : Var := freshVar proofSupport 5
  have fresh_x_ne_n : x ≠ n :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_n_ne_x : n ≠ x := Ne.symm fresh_x_ne_n
  have fresh_x_ne_a : x ≠ a :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_a_ne_x : a ≠ x := Ne.symm fresh_x_ne_a
  have fresh_x_ne_t : x ≠ t :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_t_ne_x : t ≠ x := Ne.symm fresh_x_ne_t
  have fresh_x_ne_c : x ≠ c :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 0) (j := 4) (by decide)
  have fresh_x_ne_b : x ≠ b :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 0) (j := 5) (by decide)
  have fresh_n_ne_a : n ≠ a :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_a_ne_n : a ≠ n := Ne.symm fresh_n_ne_a
  have fresh_n_ne_t : n ≠ t :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_t_ne_n : t ≠ n := Ne.symm fresh_n_ne_t
  have fresh_n_ne_c : n ≠ c :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 1) (j := 4) (by decide)
  have fresh_c_ne_n : c ≠ n := Ne.symm fresh_n_ne_c
  have fresh_n_ne_b : n ≠ b :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 1) (j := 5) (by decide)
  have fresh_b_ne_n : b ≠ n := Ne.symm fresh_n_ne_b
  have fresh_a_ne_t : a ≠ t :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_t_ne_a : t ≠ a := Ne.symm fresh_a_ne_t
  have fresh_a_ne_c : a ≠ c :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 2) (j := 4) (by decide)
  have fresh_c_ne_a : c ≠ a := Ne.symm fresh_a_ne_c
  have fresh_a_ne_b : a ≠ b :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 2) (j := 5) (by decide)
  have fresh_b_ne_a : b ≠ a := Ne.symm fresh_a_ne_b
  have fresh_t_ne_c : t ≠ c :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 3) (j := 4) (by decide)
  have fresh_c_ne_t : c ≠ t := Ne.symm fresh_t_ne_c
  have fresh_t_ne_b : t ≠ b :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 3) (j := 5) (by decide)
  have fresh_b_ne_t : b ≠ t := Ne.symm fresh_t_ne_b
  have fresh_c_ne_b : c ≠ b :=
    by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 4) (j := 5) (by decide)
  have fresh_b_ne_c : b ≠ c := Ne.symm fresh_c_ne_b
  let syntaxClass0000 : Class :=
    (syn_cin (syn_cins2k (syn_cins2k (syn_cssetk)))
      (syn_cxpk (syn_cvv) (syn_cins2k (syn_cssetk))))
  let syntaxClass0001 : Class :=
    (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
      (syn_cpw1 (syn_cpw1 (syn_c1c))))
  let syntaxClass0002 : Class := (syn_ccompl syntaxClass0001)
  let syntaxClass0003 : Class := (syn_csik syntaxClass0002)
  let syntaxClass0004 : Class := (syn_csik syntaxClass0003)
  let syntaxClass0005 : Class := (syn_csik syntaxClass0004)
  let syntaxClass0006 : Class := (syn_cins3k syntaxClass0005)
  let syntaxClass0007 : Class :=
    (syn_cins3k (syn_csik (syn_csik (syn_csik (syn_csik (syn_csik (syn_cssetk)))))))
  let syntaxClass0008 : Class :=
    (syn_cun syntaxClass0007
      (syn_cins2k (syn_cins3k (syn_csik (syn_csik (syn_csik (syn_cssetk)))))))
  let syntaxClass0009 : Class :=
    (syn_csymdif (syn_cins2k (syn_cins2k (syn_cins3k (syn_csik (syn_cssetk))))) syntaxClass0008)
  let syntaxClass0010 : Class :=
    (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
  let syntaxClass0011 : Class := (syn_cimak syntaxClass0009 syntaxClass0010)
  let syntaxClass0012 : Class := (syn_ccompl syntaxClass0011)
  let syntaxClass0013 : Class := (syn_cin syntaxClass0006 syntaxClass0012)
  let syntaxClass0014 : Class := (syn_cin syntaxClass0000 syntaxClass0013)
  let syntaxClass0015 : Class :=
    (syn_cimak syntaxClass0014 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))
  let syntaxClass0016 : Class :=
    (syn_cimak syntaxClass0015 (syn_cpw1 (syn_cpw1 (syn_c1c))))
  let syntaxClass0017 : Class := (syn_cins3k syntaxClass0016)
  let syntaxClass0018 : Class := (syn_csymdif (syn_cins2k (syn_cssetk)) syntaxClass0017)
  let syntaxClass0019 : Class :=
    (syn_cimak syntaxClass0018 (syn_cpw1 (syn_cpw1 (syn_c1c))))
  let syntaxClass0020 : Class := (syn_ccompl syntaxClass0019)
  let syntaxClass0021 : Class := (syn_cimak syntaxClass0020 (syn_cnnc))
  let syntaxFormula0022 : Wff :=
    (.classMem (syn_copk (.cv t) (syn_copk (.cv n) (.cv x))) syntaxClass0018)
  let syntaxFormula0023 : Wff :=
    (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_cpw1 (syn_c1c)))) syntaxFormula0022)
  let syntaxFormula0024 : Wff :=
    (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv a))))) syntaxFormula0022)
  let syntaxFormula0025 : Wff := (syn_wex a syntaxFormula0024)
  let syntaxFormula0026 : Wff :=
    (syn_wrex t (syn_cpw1 (syn_cpw1 (syn_c1c))) syntaxFormula0022)
  let syntaxFormula0027 : Wff := (syn_wex t syntaxFormula0024)
  let syntaxFormula0028 : Wff := (syn_wex a syntaxFormula0027)
  let syntaxFormula0029 : Wff :=
    (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv a)))) (syn_copk (.cv n) (.cv x)))
      syntaxClass0018)
  let syntaxFormula0030 : Wff :=
    (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv a)))) (syn_copk (.cv n) (.cv x)))
      (syn_cins2k (syn_cssetk)))
  let syntaxFormula0031 : Wff :=
    (.classMem (syn_copk (.cv t) (syn_copk (syn_csn (.cv a)) (.cv n))) syntaxClass0015)
  let syntaxFormula0032 : Wff :=
    (syn_wrex t (syn_cpw1 (syn_cpw1 (syn_c1c))) syntaxFormula0031)
  let syntaxFormula0033 : Wff :=
    (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_cpw1 (syn_c1c)))) syntaxFormula0031)
  let syntaxFormula0034 : Wff :=
    (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv c))))) syntaxFormula0031)
  let syntaxFormula0035 : Wff := (syn_wex c syntaxFormula0034)
  let syntaxFormula0036 : Wff := (syn_wex t syntaxFormula0033)
  let syntaxFormula0037 : Wff := (syn_wex t syntaxFormula0034)
  let syntaxFormula0038 : Wff := (syn_wex c syntaxFormula0037)
  let syntaxFormula0039 : Wff :=
    (.classMem (syn_copk (syn_csn (.cv a)) (.cv n)) syntaxClass0016)
  let syntaxFormula0040 : Wff :=
    (syn_wa (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0))
      (.classEq (.cv a) (syn_cun (.cv b) (.cv c))))
  let syntaxClass0041 : Class :=
    (syn_copk (syn_csn (syn_csn (syn_csn (.cv c)))) (syn_copk (syn_csn (.cv a)) (.cv n)))
  let syntaxFormula0042 : Wff := (.classMem syntaxClass0041 syntaxClass0015)
  let syntaxClass0043 : Class := (syn_copk (.cv t) syntaxClass0041)
  let syntaxFormula0044 : Wff := (.classMem syntaxClass0043 syntaxClass0014)
  let syntaxFormula0045 : Wff :=
    (syn_wrex t (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))) syntaxFormula0044)
  let syntaxFormula0046 : Wff :=
    (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))
      syntaxFormula0044)
  let syntaxFormula0047 : Wff :=
    (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv b)))))))
      syntaxFormula0044)
  let syntaxFormula0048 : Wff := (syn_wex b syntaxFormula0047)
  let syntaxFormula0049 : Wff := (syn_wex t syntaxFormula0046)
  let syntaxFormula0050 : Wff := (syn_wex t syntaxFormula0047)
  let syntaxFormula0051 : Wff := (syn_wex b syntaxFormula0050)
  let syntaxClass0052 : Class :=
    (syn_copk (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv b)))))) syntaxClass0041)
  let syntaxFormula0053 : Wff := (.classMem syntaxClass0052 syntaxClass0014)
  let syntaxFormula0054 : Wff :=
    (.classMem syntaxClass0052 (syn_cins2k (syn_cins2k (syn_cssetk))))
  let syntaxFormula0055 : Wff :=
    (.classMem syntaxClass0052 (syn_cxpk (syn_cvv) (syn_cins2k (syn_cssetk))))
  let syntaxFormula0056 : Wff := (.classMem syntaxClass0052 syntaxClass0000)
  let syntaxFormula0057 : Wff :=
    (.classMem (syn_copk (syn_csn (syn_csn (.cv b))) (syn_csn (syn_csn (.cv c))))
      syntaxClass0004)
  let syntaxFormula0058 : Wff := (.classMem syntaxClass0052 syntaxClass0006)
  let syntaxFormula0059 : Wff := (.classMem (.cv t) syntaxClass0010)
  let syntaxClass0060 : Class :=
    (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))))
  let syntaxFormula0061 : Wff := (.classEq (.cv t) syntaxClass0060)
  let syntaxClass0062 : Class := (syn_copk (.cv t) syntaxClass0052)
  let syntaxFormula0063 : Wff := (.classMem syntaxClass0062 syntaxClass0009)
  let syntaxFormula0064 : Wff := (syn_wa syntaxFormula0059 syntaxFormula0063)
  let syntaxFormula0065 : Wff := (syn_wa syntaxFormula0061 syntaxFormula0063)
  let syntaxFormula0066 : Wff := (syn_wex x syntaxFormula0065)
  let syntaxFormula0067 : Wff := (syn_wrex t syntaxClass0010 syntaxFormula0063)
  let syntaxFormula0068 : Wff := (syn_wex t syntaxFormula0065)
  let syntaxFormula0069 : Wff := (syn_wex x syntaxFormula0068)
  let syntaxClass0070 : Class := (syn_copk syntaxClass0060 syntaxClass0052)
  let syntaxFormula0071 : Wff := (.classMem syntaxClass0070 syntaxClass0009)
  let syntaxFormula0072 : Wff :=
    (.classMem syntaxClass0070 (syn_cins2k (syn_cins2k (syn_cins3k (syn_csik (syn_cssetk))))))
  let syntaxFormula0073 : Wff :=
    (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))
        (syn_csn (syn_csn (syn_csn (syn_csn (.cv b))))))
      (syn_csik (syn_csik (syn_csik (syn_csik (syn_cssetk))))))
  let syntaxFormula0074 : Wff := (.classMem syntaxClass0070 syntaxClass0007)
  let syntaxFormula0075 : Wff :=
    (.classMem syntaxClass0070
      (syn_cins2k (syn_cins3k (syn_csik (syn_csik (syn_csik (syn_cssetk)))))))
  let syntaxFormula0076 : Wff := (.classMem syntaxClass0070 syntaxClass0008)
  let syntaxFormula0077 : Wff := (syn_wb syntaxFormula0072 syntaxFormula0076)
  let syntaxFormula0078 : Wff := (.classMem syntaxClass0052 syntaxClass0011)
  let syntaxFormula0079 : Wff := (.classMem syntaxClass0052 syntaxClass0012)
  let syntaxFormula0080 : Wff := (.classMem syntaxClass0052 syntaxClass0013)
  let syntaxFormula0081 : Wff :=
    (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv a)))) (syn_copk (.cv n) (.cv x)))
      syntaxClass0017)
  let syntaxFormula0082 : Wff := (syn_wb syntaxFormula0030 syntaxFormula0081)
  let syntaxFormula0083 : Wff := (.classMem (syn_copk (.cv n) (.cv x)) syntaxClass0019)
  let syntaxFormula0084 : Wff := (.classMem (syn_copk (.cv n) (.cv x)) syntaxClass0020)
  let syntaxFormula0085 : Wff := (.classMem (.cv x) syntaxClass0021)
  let syntaxClass0086 : Class := (syn_cdif syntaxClass0021 (syn_csn (syn_c0)))
  let syntaxFormula0087 : Wff :=
    (syn_wa (syn_wrex n (syn_cnnc) (.classEq (.cv x) (syn_cplc (.cv n) (.cv n))))
      (syn_wne (.cv x) (syn_c0)))
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_evenfin x n
      (show n ≠ x from (by exact fresh_n_ne_x))
  have p0001 := @g_eldifsn (.cv x) syntaxClass0021 (syn_c0)
  have p0002 := @g_vex x
  have freshnessCertificate0000 : n ∉ ((syn_cssetk)).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk];
      exact (show n ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))
  have freshnessCertificate0001 : n ∉ ((syn_cins2k (syn_cssetk))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0000)
  have freshnessCertificate0002 : n ∉ ((syn_cins2k (syn_cins2k (syn_cssetk)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0001)
  have freshnessCertificate0003 : n ∉ ((syn_cvv)).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv];
      exact (show n ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))
  have freshnessCertificate0004 :
    n ∉ (((syn_cvv)).fv) ∪ (((syn_cins2k (syn_cssetk))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0003 freshnessCertificate0001))
  have freshnessCertificate0005 :
    n ∉ ((syn_cxpk (syn_cvv) (syn_cins2k (syn_cssetk)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk];
      exact freshnessCertificate0004)
  have freshnessCertificate0006 :
    n ∉
      (((syn_cins2k (syn_cins2k (syn_cssetk)))).fv) ∪
        (((syn_cxpk (syn_cvv) (syn_cins2k (syn_cssetk)))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0002 freshnessCertificate0005))
  have freshnessCertificate0007 : n ∉ (syntaxClass0000).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin];
      exact freshnessCertificate0006)
  have freshnessCertificate0008 : n ∉ ((syn_cins3k (syn_cssetk))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0000)
  have freshnessCertificate0009 :
    n ∉ (((syn_cins3k (syn_cssetk))).fv) ∪ (((syn_cins2k (syn_cssetk))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0008 freshnessCertificate0001))
  have freshnessCertificate0010 :
    n ∉ ((syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin];
      exact freshnessCertificate0009)
  have freshnessCertificate0011 : n ∉ ((syn_c1c)).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c];
      exact (show n ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))
  have freshnessCertificate0012 : n ∉ ((syn_cpw1 (syn_c1c))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0011)
  have freshnessCertificate0013 : n ∉ ((syn_cpw1 (syn_cpw1 (syn_c1c)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0012)
  have freshnessCertificate0014 :
    n ∉
      (((syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))).fv) ∪
        (((syn_cpw1 (syn_cpw1 (syn_c1c)))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0010 freshnessCertificate0013))
  have freshnessCertificate0015 : n ∉ (syntaxClass0001).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak];
      exact freshnessCertificate0014)
  have freshnessCertificate0016 : n ∉ (syntaxClass0002).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl];
      exact freshnessCertificate0015)
  have freshnessCertificate0017 : n ∉ (syntaxClass0003).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0016)
  have freshnessCertificate0018 : n ∉ (syntaxClass0004).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0017)
  have freshnessCertificate0019 : n ∉ (syntaxClass0005).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0018)
  have freshnessCertificate0020 : n ∉ (syntaxClass0006).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0019)
  have freshnessCertificate0021 : n ∉ ((syn_csik (syn_cssetk))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0000)
  have freshnessCertificate0022 : n ∉ ((syn_cins3k (syn_csik (syn_cssetk)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0021)
  have freshnessCertificate0023 :
    n ∉ ((syn_cins2k (syn_cins3k (syn_csik (syn_cssetk))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0022)
  have freshnessCertificate0024 :
    n ∉ ((syn_cins2k (syn_cins2k (syn_cins3k (syn_csik (syn_cssetk)))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0023)
  have freshnessCertificate0025 : n ∉ ((syn_csik (syn_csik (syn_cssetk)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0021)
  have freshnessCertificate0026 :
    n ∉ ((syn_csik (syn_csik (syn_csik (syn_cssetk))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0025)
  have freshnessCertificate0027 :
    n ∉ ((syn_csik (syn_csik (syn_csik (syn_csik (syn_cssetk)))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0026)
  have freshnessCertificate0028 :
    n ∉ ((syn_csik (syn_csik (syn_csik (syn_csik (syn_csik (syn_cssetk))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0027)
  have freshnessCertificate0029 : n ∉ (syntaxClass0007).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0028)
  have freshnessCertificate0030 :
    n ∉ ((syn_cins3k (syn_csik (syn_csik (syn_csik (syn_cssetk)))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0026)
  have freshnessCertificate0031 :
    n ∉ ((syn_cins2k (syn_cins3k (syn_csik (syn_csik (syn_csik (syn_cssetk))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0030)
  have freshnessCertificate0032 :
    n ∉
      ((syntaxClass0007).fv) ∪
        (((syn_cins2k (syn_cins3k (syn_csik (syn_csik (syn_csik (syn_cssetk))))))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0029 freshnessCertificate0031))
  have freshnessCertificate0033 : n ∉ (syntaxClass0008).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun];
      exact freshnessCertificate0032)
  have freshnessCertificate0034 :
    n ∉
      (((syn_cins2k (syn_cins2k (syn_cins3k (syn_csik (syn_cssetk)))))).fv) ∪
        ((syntaxClass0008).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0024 freshnessCertificate0033))
  have freshnessCertificate0035 : n ∉ (syntaxClass0009).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif];
      exact freshnessCertificate0034)
  have freshnessCertificate0036 : n ∉ ((syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0013)
  have freshnessCertificate0037 :
    n ∉ ((syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0036)
  have freshnessCertificate0038 :
    n ∉ ((syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0037)
  have freshnessCertificate0039 :
    n ∉
      ((syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0038)
  have freshnessCertificate0040 : n ∉ (syntaxClass0010).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0039)
  have freshnessCertificate0041 : n ∉ ((syntaxClass0009).fv) ∪ ((syntaxClass0010).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0035 freshnessCertificate0040))
  have freshnessCertificate0042 : n ∉ (syntaxClass0011).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak];
      exact freshnessCertificate0041)
  have freshnessCertificate0043 : n ∉ (syntaxClass0012).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl];
      exact freshnessCertificate0042)
  have freshnessCertificate0044 : n ∉ ((syntaxClass0006).fv) ∪ ((syntaxClass0012).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0020 freshnessCertificate0043))
  have freshnessCertificate0045 : n ∉ (syntaxClass0013).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin];
      exact freshnessCertificate0044)
  have freshnessCertificate0046 : n ∉ ((syntaxClass0000).fv) ∪ ((syntaxClass0013).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0007 freshnessCertificate0045))
  have freshnessCertificate0047 : n ∉ (syntaxClass0014).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin];
      exact freshnessCertificate0046)
  have freshnessCertificate0048 :
    n ∉
      ((syntaxClass0014).fv) ∪
        (((syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0047 freshnessCertificate0037))
  have freshnessCertificate0049 : n ∉ (syntaxClass0015).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak];
      exact freshnessCertificate0048)
  have freshnessCertificate0050 :
    n ∉ ((syntaxClass0015).fv) ∪ (((syn_cpw1 (syn_cpw1 (syn_c1c)))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0049 freshnessCertificate0013))
  have freshnessCertificate0051 : n ∉ (syntaxClass0016).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak];
      exact freshnessCertificate0050)
  have freshnessCertificate0052 : n ∉ (syntaxClass0017).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0051)
  have freshnessCertificate0053 :
    n ∉ (((syn_cins2k (syn_cssetk))).fv) ∪ ((syntaxClass0017).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0001 freshnessCertificate0052))
  have freshnessCertificate0054 : n ∉ (syntaxClass0018).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif];
      exact freshnessCertificate0053)
  have freshnessCertificate0055 :
    n ∉ ((syntaxClass0018).fv) ∪ (((syn_cpw1 (syn_cpw1 (syn_c1c)))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0054 freshnessCertificate0013))
  have freshnessCertificate0056 : n ∉ (syntaxClass0019).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak];
      exact freshnessCertificate0055)
  have freshnessCertificate0057 : n ∉ (syntaxClass0020).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl];
      exact freshnessCertificate0056)
  have freshnessCertificate0058 : n ∉ ((syn_cnnc)).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc];
      exact (show n ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))
  have freshnessCertificate0059 : n ∉ ((Class.cv x)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show n ∉ ({ x } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show n ≠ x from (by exact fresh_n_ne_x)))))
  have p0003 :=
    @g_elimak n syntaxClass0020 (syn_cnnc) (.cv x) (by exact freshnessCertificate0057)
      (by exact freshnessCertificate0058) (by exact freshnessCertificate0059) p0002
  have p0004 := @g_opkex (.cv n) (.cv x)
  have freshnessCertificate0060 : t ∉ ((syn_cssetk)).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk];
      exact (show t ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))
  have freshnessCertificate0061 : t ∉ ((syn_cins2k (syn_cssetk))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0060)
  have freshnessCertificate0062 : t ∉ ((syn_cins2k (syn_cins2k (syn_cssetk)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0061)
  have freshnessCertificate0063 : t ∉ ((syn_cvv)).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv];
      exact (show t ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))
  have freshnessCertificate0064 :
    t ∉ (((syn_cvv)).fv) ∪ (((syn_cins2k (syn_cssetk))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0063 freshnessCertificate0061))
  have freshnessCertificate0065 :
    t ∉ ((syn_cxpk (syn_cvv) (syn_cins2k (syn_cssetk)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk];
      exact freshnessCertificate0064)
  have freshnessCertificate0066 :
    t ∉
      (((syn_cins2k (syn_cins2k (syn_cssetk)))).fv) ∪
        (((syn_cxpk (syn_cvv) (syn_cins2k (syn_cssetk)))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0062 freshnessCertificate0065))
  have freshnessCertificate0067 : t ∉ (syntaxClass0000).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin];
      exact freshnessCertificate0066)
  have freshnessCertificate0068 : t ∉ ((syn_cins3k (syn_cssetk))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0060)
  have freshnessCertificate0069 :
    t ∉ (((syn_cins3k (syn_cssetk))).fv) ∪ (((syn_cins2k (syn_cssetk))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0068 freshnessCertificate0061))
  have freshnessCertificate0070 :
    t ∉ ((syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin];
      exact freshnessCertificate0069)
  have freshnessCertificate0071 : t ∉ ((syn_c1c)).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c];
      exact (show t ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))
  have freshnessCertificate0072 : t ∉ ((syn_cpw1 (syn_c1c))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0071)
  have freshnessCertificate0073 : t ∉ ((syn_cpw1 (syn_cpw1 (syn_c1c)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0072)
  have freshnessCertificate0074 :
    t ∉
      (((syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))).fv) ∪
        (((syn_cpw1 (syn_cpw1 (syn_c1c)))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0070 freshnessCertificate0073))
  have freshnessCertificate0075 : t ∉ (syntaxClass0001).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak];
      exact freshnessCertificate0074)
  have freshnessCertificate0076 : t ∉ (syntaxClass0002).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl];
      exact freshnessCertificate0075)
  have freshnessCertificate0077 : t ∉ (syntaxClass0003).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0076)
  have freshnessCertificate0078 : t ∉ (syntaxClass0004).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0077)
  have freshnessCertificate0079 : t ∉ (syntaxClass0005).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0078)
  have freshnessCertificate0080 : t ∉ (syntaxClass0006).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0079)
  have freshnessCertificate0081 : t ∉ ((syn_csik (syn_cssetk))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0060)
  have freshnessCertificate0082 : t ∉ ((syn_cins3k (syn_csik (syn_cssetk)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0081)
  have freshnessCertificate0083 :
    t ∉ ((syn_cins2k (syn_cins3k (syn_csik (syn_cssetk))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0082)
  have freshnessCertificate0084 :
    t ∉ ((syn_cins2k (syn_cins2k (syn_cins3k (syn_csik (syn_cssetk)))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0083)
  have freshnessCertificate0085 : t ∉ ((syn_csik (syn_csik (syn_cssetk)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0081)
  have freshnessCertificate0086 :
    t ∉ ((syn_csik (syn_csik (syn_csik (syn_cssetk))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0085)
  have freshnessCertificate0087 :
    t ∉ ((syn_csik (syn_csik (syn_csik (syn_csik (syn_cssetk)))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0086)
  have freshnessCertificate0088 :
    t ∉ ((syn_csik (syn_csik (syn_csik (syn_csik (syn_csik (syn_cssetk))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0087)
  have freshnessCertificate0089 : t ∉ (syntaxClass0007).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0088)
  have freshnessCertificate0090 :
    t ∉ ((syn_cins3k (syn_csik (syn_csik (syn_csik (syn_cssetk)))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0086)
  have freshnessCertificate0091 :
    t ∉ ((syn_cins2k (syn_cins3k (syn_csik (syn_csik (syn_csik (syn_cssetk))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0090)
  have freshnessCertificate0092 :
    t ∉
      ((syntaxClass0007).fv) ∪
        (((syn_cins2k (syn_cins3k (syn_csik (syn_csik (syn_csik (syn_cssetk))))))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0089 freshnessCertificate0091))
  have freshnessCertificate0093 : t ∉ (syntaxClass0008).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun];
      exact freshnessCertificate0092)
  have freshnessCertificate0094 :
    t ∉
      (((syn_cins2k (syn_cins2k (syn_cins3k (syn_csik (syn_cssetk)))))).fv) ∪
        ((syntaxClass0008).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0084 freshnessCertificate0093))
  have freshnessCertificate0095 : t ∉ (syntaxClass0009).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif];
      exact freshnessCertificate0094)
  have freshnessCertificate0096 : t ∉ ((syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0073)
  have freshnessCertificate0097 :
    t ∉ ((syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0096)
  have freshnessCertificate0098 :
    t ∉ ((syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0097)
  have freshnessCertificate0099 :
    t ∉
      ((syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0098)
  have freshnessCertificate0100 : t ∉ (syntaxClass0010).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0099)
  have freshnessCertificate0101 : t ∉ ((syntaxClass0009).fv) ∪ ((syntaxClass0010).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0095 freshnessCertificate0100))
  have freshnessCertificate0102 : t ∉ (syntaxClass0011).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak];
      exact freshnessCertificate0101)
  have freshnessCertificate0103 : t ∉ (syntaxClass0012).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl];
      exact freshnessCertificate0102)
  have freshnessCertificate0104 : t ∉ ((syntaxClass0006).fv) ∪ ((syntaxClass0012).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0080 freshnessCertificate0103))
  have freshnessCertificate0105 : t ∉ (syntaxClass0013).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin];
      exact freshnessCertificate0104)
  have freshnessCertificate0106 : t ∉ ((syntaxClass0000).fv) ∪ ((syntaxClass0013).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0067 freshnessCertificate0105))
  have freshnessCertificate0107 : t ∉ (syntaxClass0014).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin];
      exact freshnessCertificate0106)
  have freshnessCertificate0108 :
    t ∉
      ((syntaxClass0014).fv) ∪
        (((syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0107 freshnessCertificate0097))
  have freshnessCertificate0109 : t ∉ (syntaxClass0015).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak];
      exact freshnessCertificate0108)
  have freshnessCertificate0110 :
    t ∉ ((syntaxClass0015).fv) ∪ (((syn_cpw1 (syn_cpw1 (syn_c1c)))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0109 freshnessCertificate0073))
  have freshnessCertificate0111 : t ∉ (syntaxClass0016).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak];
      exact freshnessCertificate0110)
  have freshnessCertificate0112 : t ∉ (syntaxClass0017).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0111)
  have freshnessCertificate0113 :
    t ∉ (((syn_cins2k (syn_cssetk))).fv) ∪ ((syntaxClass0017).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0061 freshnessCertificate0112))
  have freshnessCertificate0114 : t ∉ (syntaxClass0018).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif];
      exact freshnessCertificate0113)
  have freshnessCertificate0115 : t ∉ ((Class.cv n)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show t ∉ ({ n } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show t ≠ n from (by exact fresh_t_ne_n)))))
  have freshnessCertificate0116 : t ∉ ((Class.cv x)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show t ∉ ({ x } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show t ≠ x from (by exact fresh_t_ne_x)))))
  have freshnessCertificate0117 : t ∉ (((Class.cv n)).fv) ∪ (((Class.cv x)).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0115 freshnessCertificate0116))
  have freshnessCertificate0118 : t ∉ ((syn_copk (.cv n) (.cv x))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk];
      exact freshnessCertificate0117)
  have p0005 :=
    @g_elimak t syntaxClass0018 (syn_cpw1 (syn_cpw1 (syn_c1c))) (syn_copk (.cv n) (.cv x))
      (by exact freshnessCertificate0114) (by exact freshnessCertificate0073)
      (by exact freshnessCertificate0118) p0004
  have freshnessCertificate0119 : a ∉ ((Class.cv t)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show a ∉ ({ t } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show a ≠ t from (by exact fresh_a_ne_t)))))
  have p0006 := @g_elpw121c a (.cv t) (by exact freshnessCertificate0119)
  have p0007 :=
    @g_anbi1i (.classMem (.cv t) (syn_cpw1 (syn_cpw1 (syn_c1c))))
      (syn_wex a (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv a))))))
      syntaxFormula0022 p0006
  have freshnessCertificate0120 : a ∉ ((Class.cv n)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show a ∉ ({ n } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show a ≠ n from (by exact fresh_a_ne_n)))))
  have freshnessCertificate0121 : a ∉ ((Class.cv x)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show a ∉ ({ x } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show a ≠ x from (by exact fresh_a_ne_x)))))
  have freshnessCertificate0122 : a ∉ (((Class.cv n)).fv) ∪ (((Class.cv x)).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0120 freshnessCertificate0121))
  have freshnessCertificate0123 : a ∉ ((syn_copk (.cv n) (.cv x))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk];
      exact freshnessCertificate0122)
  have freshnessCertificate0124 :
    a ∉ (((Class.cv t)).fv) ∪ (((syn_copk (.cv n) (.cv x))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0119 freshnessCertificate0123))
  have freshnessCertificate0125 :
    a ∉ ((syn_copk (.cv t) (syn_copk (.cv n) (.cv x)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk];
      exact freshnessCertificate0124)
  have freshnessCertificate0126 : a ∉ ((syn_cssetk)).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk];
      exact (show a ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))
  have freshnessCertificate0127 : a ∉ ((syn_cins2k (syn_cssetk))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0126)
  have freshnessCertificate0128 : a ∉ ((syn_cins2k (syn_cins2k (syn_cssetk)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0127)
  have freshnessCertificate0129 : a ∉ ((syn_cvv)).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv];
      exact (show a ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))
  have freshnessCertificate0130 :
    a ∉ (((syn_cvv)).fv) ∪ (((syn_cins2k (syn_cssetk))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0129 freshnessCertificate0127))
  have freshnessCertificate0131 :
    a ∉ ((syn_cxpk (syn_cvv) (syn_cins2k (syn_cssetk)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk];
      exact freshnessCertificate0130)
  have freshnessCertificate0132 :
    a ∉
      (((syn_cins2k (syn_cins2k (syn_cssetk)))).fv) ∪
        (((syn_cxpk (syn_cvv) (syn_cins2k (syn_cssetk)))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0128 freshnessCertificate0131))
  have freshnessCertificate0133 : a ∉ (syntaxClass0000).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin];
      exact freshnessCertificate0132)
  have freshnessCertificate0134 : a ∉ ((syn_cins3k (syn_cssetk))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0126)
  have freshnessCertificate0135 :
    a ∉ (((syn_cins3k (syn_cssetk))).fv) ∪ (((syn_cins2k (syn_cssetk))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0134 freshnessCertificate0127))
  have freshnessCertificate0136 :
    a ∉ ((syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin];
      exact freshnessCertificate0135)
  have freshnessCertificate0137 : a ∉ ((syn_c1c)).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c];
      exact (show a ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))
  have freshnessCertificate0138 : a ∉ ((syn_cpw1 (syn_c1c))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0137)
  have freshnessCertificate0139 : a ∉ ((syn_cpw1 (syn_cpw1 (syn_c1c)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0138)
  have freshnessCertificate0140 :
    a ∉
      (((syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))).fv) ∪
        (((syn_cpw1 (syn_cpw1 (syn_c1c)))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0136 freshnessCertificate0139))
  have freshnessCertificate0141 : a ∉ (syntaxClass0001).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak];
      exact freshnessCertificate0140)
  have freshnessCertificate0142 : a ∉ (syntaxClass0002).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl];
      exact freshnessCertificate0141)
  have freshnessCertificate0143 : a ∉ (syntaxClass0003).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0142)
  have freshnessCertificate0144 : a ∉ (syntaxClass0004).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0143)
  have freshnessCertificate0145 : a ∉ (syntaxClass0005).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0144)
  have freshnessCertificate0146 : a ∉ (syntaxClass0006).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0145)
  have freshnessCertificate0147 : a ∉ ((syn_csik (syn_cssetk))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0126)
  have freshnessCertificate0148 : a ∉ ((syn_cins3k (syn_csik (syn_cssetk)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0147)
  have freshnessCertificate0149 :
    a ∉ ((syn_cins2k (syn_cins3k (syn_csik (syn_cssetk))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0148)
  have freshnessCertificate0150 :
    a ∉ ((syn_cins2k (syn_cins2k (syn_cins3k (syn_csik (syn_cssetk)))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0149)
  have freshnessCertificate0151 : a ∉ ((syn_csik (syn_csik (syn_cssetk)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0147)
  have freshnessCertificate0152 :
    a ∉ ((syn_csik (syn_csik (syn_csik (syn_cssetk))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0151)
  have freshnessCertificate0153 :
    a ∉ ((syn_csik (syn_csik (syn_csik (syn_csik (syn_cssetk)))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0152)
  have freshnessCertificate0154 :
    a ∉ ((syn_csik (syn_csik (syn_csik (syn_csik (syn_csik (syn_cssetk))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0153)
  have freshnessCertificate0155 : a ∉ (syntaxClass0007).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0154)
  have freshnessCertificate0156 :
    a ∉ ((syn_cins3k (syn_csik (syn_csik (syn_csik (syn_cssetk)))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0152)
  have freshnessCertificate0157 :
    a ∉ ((syn_cins2k (syn_cins3k (syn_csik (syn_csik (syn_csik (syn_cssetk))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0156)
  have freshnessCertificate0158 :
    a ∉
      ((syntaxClass0007).fv) ∪
        (((syn_cins2k (syn_cins3k (syn_csik (syn_csik (syn_csik (syn_cssetk))))))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0155 freshnessCertificate0157))
  have freshnessCertificate0159 : a ∉ (syntaxClass0008).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun];
      exact freshnessCertificate0158)
  have freshnessCertificate0160 :
    a ∉
      (((syn_cins2k (syn_cins2k (syn_cins3k (syn_csik (syn_cssetk)))))).fv) ∪
        ((syntaxClass0008).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0150 freshnessCertificate0159))
  have freshnessCertificate0161 : a ∉ (syntaxClass0009).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif];
      exact freshnessCertificate0160)
  have freshnessCertificate0162 : a ∉ ((syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0139)
  have freshnessCertificate0163 :
    a ∉ ((syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0162)
  have freshnessCertificate0164 :
    a ∉ ((syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0163)
  have freshnessCertificate0165 :
    a ∉
      ((syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0164)
  have freshnessCertificate0166 : a ∉ (syntaxClass0010).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0165)
  have freshnessCertificate0167 : a ∉ ((syntaxClass0009).fv) ∪ ((syntaxClass0010).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0161 freshnessCertificate0166))
  have freshnessCertificate0168 : a ∉ (syntaxClass0011).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak];
      exact freshnessCertificate0167)
  have freshnessCertificate0169 : a ∉ (syntaxClass0012).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl];
      exact freshnessCertificate0168)
  have freshnessCertificate0170 : a ∉ ((syntaxClass0006).fv) ∪ ((syntaxClass0012).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0146 freshnessCertificate0169))
  have freshnessCertificate0171 : a ∉ (syntaxClass0013).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin];
      exact freshnessCertificate0170)
  have freshnessCertificate0172 : a ∉ ((syntaxClass0000).fv) ∪ ((syntaxClass0013).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0133 freshnessCertificate0171))
  have freshnessCertificate0173 : a ∉ (syntaxClass0014).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin];
      exact freshnessCertificate0172)
  have freshnessCertificate0174 :
    a ∉
      ((syntaxClass0014).fv) ∪
        (((syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0173 freshnessCertificate0163))
  have freshnessCertificate0175 : a ∉ (syntaxClass0015).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak];
      exact freshnessCertificate0174)
  have freshnessCertificate0176 :
    a ∉ ((syntaxClass0015).fv) ∪ (((syn_cpw1 (syn_cpw1 (syn_c1c)))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0175 freshnessCertificate0139))
  have freshnessCertificate0177 : a ∉ (syntaxClass0016).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak];
      exact freshnessCertificate0176)
  have freshnessCertificate0178 : a ∉ (syntaxClass0017).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0177)
  have freshnessCertificate0179 :
    a ∉ (((syn_cins2k (syn_cssetk))).fv) ∪ ((syntaxClass0017).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0127 freshnessCertificate0178))
  have freshnessCertificate0180 : a ∉ (syntaxClass0018).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif];
      exact freshnessCertificate0179)
  have freshnessCertificate0181 :
    a ∉ (((syn_copk (.cv t) (syn_copk (.cv n) (.cv x)))).fv) ∪ ((syntaxClass0018).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0125 freshnessCertificate0180))
  have freshnessCertificate0182 :
    a ∉
      ((Wff.classMem (syn_copk (.cv t) (syn_copk (.cv n) (.cv x))) syntaxClass0018)).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact freshnessCertificate0181)
  have p0008 :=
    @g_n_19_41v (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv a))))) syntaxFormula0022
      a (by exact freshnessCertificate0182)
  have p0009 :=
    @g_bitr4i syntaxFormula0023
      (syn_wa (syn_wex a (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv a))))))
        syntaxFormula0022)
      syntaxFormula0025 p0007 p0008
  have p0010 := @g_exbii syntaxFormula0023 syntaxFormula0025 t p0009
  have p0011 := (Nominal.biimpRefl syntaxFormula0026)
  have p0012 := @g_excom syntaxFormula0024 a t
  have p0013 :=
    @g_n_3bitr4i (syn_wex t syntaxFormula0023) (syn_wex t syntaxFormula0025)
      syntaxFormula0026 syntaxFormula0028 p0010 p0011 p0012
  have p0014 := @g_snex (syn_csn (syn_csn (.cv a)))
  have p0015 :=
    @g_opkeq1 (.cv t) (syn_csn (syn_csn (syn_csn (.cv a)))) (syn_copk (.cv n) (.cv x))
  have p0016 :=
    @g_eleq1d (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv a)))))
      (syn_copk (.cv t) (syn_copk (.cv n) (.cv x)))
      (syn_copk (syn_csn (syn_csn (syn_csn (.cv a)))) (syn_copk (.cv n) (.cv x)))
      syntaxClass0018 p0015
  have freshnessCertificate0183 : t ∉ ((Class.cv a)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show t ∉ ({ a } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show t ≠ a from (by exact fresh_t_ne_a)))))
  have freshnessCertificate0184 : t ∉ ((syn_csn (.cv a))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0183)
  have freshnessCertificate0185 : t ∉ ((syn_csn (syn_csn (.cv a)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0184)
  have freshnessCertificate0186 : t ∉ ((syn_csn (syn_csn (syn_csn (.cv a))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0185)
  have freshnessCertificate0187 :
    t ∉
      (((syn_csn (syn_csn (syn_csn (.cv a))))).fv) ∪ (((syn_copk (.cv n) (.cv x))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0186 freshnessCertificate0118))
  have freshnessCertificate0188 :
    t ∉
      ((syn_copk (syn_csn (syn_csn (syn_csn (.cv a)))) (syn_copk (.cv n) (.cv x)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk];
      exact freshnessCertificate0187)
  have freshnessCertificate0189 :
    t ∉
      (((syn_copk (syn_csn (syn_csn (syn_csn (.cv a)))) (syn_copk (.cv n) (.cv x)))).fv) ∪
        ((syntaxClass0018).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0188 freshnessCertificate0114))
  have freshnessCertificate0190 :
    t ∉
      ((Wff.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv a)))) (syn_copk (.cv n) (.cv x)))
          syntaxClass0018)).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact freshnessCertificate0189)
  have p0017 :=
    @g_ceqsexv syntaxFormula0022 syntaxFormula0029 t (syn_csn (syn_csn (syn_csn (.cv a))))
      (by exact freshnessCertificate0186) (by exact freshnessCertificate0190) p0014 p0016
  have p0018 :=
    @g_elsymdif
      (syn_copk (syn_csn (syn_csn (syn_csn (.cv a)))) (syn_copk (.cv n) (.cv x)))
      (syn_cins2k (syn_cssetk)) syntaxClass0017
  have p0019 := @g_snex (.cv a)
  have p0020 := @g_vex n
  have p0021 :=
    @g_otkelins2k (syn_csn (.cv a)) (.cv n) (.cv x) (syn_cssetk) p0019 p0020 p0002
  have p0022 := @g_vex a
  have p0023 := @g_elssetk (.cv a) (.cv x) p0022 p0002
  have p0024_e01_recanon :
    Nominal.NPrf
      (syn_wb (.classMem (syn_copk (syn_csn (.cv a)) (.cv x)) (syn_cssetk)) (.objMem a x)) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [syn_wb, syn_copk, syn_cpr, syn_cun, syn_cnin, syn_wnan, syn_wa,
          syn_ccompl, syn_csn, syn_cssetk, syn_wex]
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
      p0023
  have p0024 :=
    @g_bitri syntaxFormula0030
      (.classMem (syn_copk (syn_csn (.cv a)) (.cv x)) (syn_cssetk)) (.objMem a x) p0021
      p0024_e01_recanon
  have p0025 := @g_opkex (syn_csn (.cv a)) (.cv n)
  have freshnessCertificate0191 : t ∉ (((syn_csn (.cv a))).fv) ∪ (((Class.cv n)).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0184 freshnessCertificate0115))
  have freshnessCertificate0192 : t ∉ ((syn_copk (syn_csn (.cv a)) (.cv n))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk];
      exact freshnessCertificate0191)
  have p0026 :=
    @g_elimak t syntaxClass0015 (syn_cpw1 (syn_cpw1 (syn_c1c)))
      (syn_copk (syn_csn (.cv a)) (.cv n)) (by exact freshnessCertificate0109)
      (by exact freshnessCertificate0073) (by exact freshnessCertificate0192) p0025
  have p0027 := (Nominal.biimpRefl syntaxFormula0032)
  have freshnessCertificate0193 : c ∉ ((Class.cv t)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show c ∉ ({ t } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show c ≠ t from (by exact fresh_c_ne_t)))))
  have p0028 := @g_elpw121c c (.cv t) (by exact freshnessCertificate0193)
  have p0029 :=
    @g_anbi1i (.classMem (.cv t) (syn_cpw1 (syn_cpw1 (syn_c1c))))
      (syn_wex c (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv c))))))
      syntaxFormula0031 p0028
  have freshnessCertificate0194 : c ∉ ((Class.cv a)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show c ∉ ({ a } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show c ≠ a from (by exact fresh_c_ne_a)))))
  have freshnessCertificate0195 : c ∉ ((syn_csn (.cv a))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0194)
  have freshnessCertificate0196 : c ∉ ((Class.cv n)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show c ∉ ({ n } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show c ≠ n from (by exact fresh_c_ne_n)))))
  have freshnessCertificate0197 : c ∉ (((syn_csn (.cv a))).fv) ∪ (((Class.cv n)).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0195 freshnessCertificate0196))
  have freshnessCertificate0198 : c ∉ ((syn_copk (syn_csn (.cv a)) (.cv n))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk];
      exact freshnessCertificate0197)
  have freshnessCertificate0199 :
    c ∉ (((Class.cv t)).fv) ∪ (((syn_copk (syn_csn (.cv a)) (.cv n))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0193 freshnessCertificate0198))
  have freshnessCertificate0200 :
    c ∉ ((syn_copk (.cv t) (syn_copk (syn_csn (.cv a)) (.cv n)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk];
      exact freshnessCertificate0199)
  have freshnessCertificate0201 : c ∉ ((syn_cssetk)).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk];
      exact (show c ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))
  have freshnessCertificate0202 : c ∉ ((syn_cins2k (syn_cssetk))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0201)
  have freshnessCertificate0203 : c ∉ ((syn_cins2k (syn_cins2k (syn_cssetk)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0202)
  have freshnessCertificate0204 : c ∉ ((syn_cvv)).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv];
      exact (show c ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))
  have freshnessCertificate0205 :
    c ∉ (((syn_cvv)).fv) ∪ (((syn_cins2k (syn_cssetk))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0204 freshnessCertificate0202))
  have freshnessCertificate0206 :
    c ∉ ((syn_cxpk (syn_cvv) (syn_cins2k (syn_cssetk)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk];
      exact freshnessCertificate0205)
  have freshnessCertificate0207 :
    c ∉
      (((syn_cins2k (syn_cins2k (syn_cssetk)))).fv) ∪
        (((syn_cxpk (syn_cvv) (syn_cins2k (syn_cssetk)))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0203 freshnessCertificate0206))
  have freshnessCertificate0208 : c ∉ (syntaxClass0000).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin];
      exact freshnessCertificate0207)
  have freshnessCertificate0209 : c ∉ ((syn_cins3k (syn_cssetk))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0201)
  have freshnessCertificate0210 :
    c ∉ (((syn_cins3k (syn_cssetk))).fv) ∪ (((syn_cins2k (syn_cssetk))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0209 freshnessCertificate0202))
  have freshnessCertificate0211 :
    c ∉ ((syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin];
      exact freshnessCertificate0210)
  have freshnessCertificate0212 : c ∉ ((syn_c1c)).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c];
      exact (show c ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))
  have freshnessCertificate0213 : c ∉ ((syn_cpw1 (syn_c1c))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0212)
  have freshnessCertificate0214 : c ∉ ((syn_cpw1 (syn_cpw1 (syn_c1c)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0213)
  have freshnessCertificate0215 :
    c ∉
      (((syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))).fv) ∪
        (((syn_cpw1 (syn_cpw1 (syn_c1c)))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0211 freshnessCertificate0214))
  have freshnessCertificate0216 : c ∉ (syntaxClass0001).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak];
      exact freshnessCertificate0215)
  have freshnessCertificate0217 : c ∉ (syntaxClass0002).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl];
      exact freshnessCertificate0216)
  have freshnessCertificate0218 : c ∉ (syntaxClass0003).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0217)
  have freshnessCertificate0219 : c ∉ (syntaxClass0004).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0218)
  have freshnessCertificate0220 : c ∉ (syntaxClass0005).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0219)
  have freshnessCertificate0221 : c ∉ (syntaxClass0006).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0220)
  have freshnessCertificate0222 : c ∉ ((syn_csik (syn_cssetk))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0201)
  have freshnessCertificate0223 : c ∉ ((syn_cins3k (syn_csik (syn_cssetk)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0222)
  have freshnessCertificate0224 :
    c ∉ ((syn_cins2k (syn_cins3k (syn_csik (syn_cssetk))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0223)
  have freshnessCertificate0225 :
    c ∉ ((syn_cins2k (syn_cins2k (syn_cins3k (syn_csik (syn_cssetk)))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0224)
  have freshnessCertificate0226 : c ∉ ((syn_csik (syn_csik (syn_cssetk)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0222)
  have freshnessCertificate0227 :
    c ∉ ((syn_csik (syn_csik (syn_csik (syn_cssetk))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0226)
  have freshnessCertificate0228 :
    c ∉ ((syn_csik (syn_csik (syn_csik (syn_csik (syn_cssetk)))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0227)
  have freshnessCertificate0229 :
    c ∉ ((syn_csik (syn_csik (syn_csik (syn_csik (syn_csik (syn_cssetk))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0228)
  have freshnessCertificate0230 : c ∉ (syntaxClass0007).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0229)
  have freshnessCertificate0231 :
    c ∉ ((syn_cins3k (syn_csik (syn_csik (syn_csik (syn_cssetk)))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0227)
  have freshnessCertificate0232 :
    c ∉ ((syn_cins2k (syn_cins3k (syn_csik (syn_csik (syn_csik (syn_cssetk))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0231)
  have freshnessCertificate0233 :
    c ∉
      ((syntaxClass0007).fv) ∪
        (((syn_cins2k (syn_cins3k (syn_csik (syn_csik (syn_csik (syn_cssetk))))))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0230 freshnessCertificate0232))
  have freshnessCertificate0234 : c ∉ (syntaxClass0008).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun];
      exact freshnessCertificate0233)
  have freshnessCertificate0235 :
    c ∉
      (((syn_cins2k (syn_cins2k (syn_cins3k (syn_csik (syn_cssetk)))))).fv) ∪
        ((syntaxClass0008).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0225 freshnessCertificate0234))
  have freshnessCertificate0236 : c ∉ (syntaxClass0009).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif];
      exact freshnessCertificate0235)
  have freshnessCertificate0237 : c ∉ ((syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0214)
  have freshnessCertificate0238 :
    c ∉ ((syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0237)
  have freshnessCertificate0239 :
    c ∉ ((syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0238)
  have freshnessCertificate0240 :
    c ∉
      ((syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0239)
  have freshnessCertificate0241 : c ∉ (syntaxClass0010).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0240)
  have freshnessCertificate0242 : c ∉ ((syntaxClass0009).fv) ∪ ((syntaxClass0010).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0236 freshnessCertificate0241))
  have freshnessCertificate0243 : c ∉ (syntaxClass0011).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak];
      exact freshnessCertificate0242)
  have freshnessCertificate0244 : c ∉ (syntaxClass0012).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl];
      exact freshnessCertificate0243)
  have freshnessCertificate0245 : c ∉ ((syntaxClass0006).fv) ∪ ((syntaxClass0012).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0221 freshnessCertificate0244))
  have freshnessCertificate0246 : c ∉ (syntaxClass0013).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin];
      exact freshnessCertificate0245)
  have freshnessCertificate0247 : c ∉ ((syntaxClass0000).fv) ∪ ((syntaxClass0013).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0208 freshnessCertificate0246))
  have freshnessCertificate0248 : c ∉ (syntaxClass0014).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin];
      exact freshnessCertificate0247)
  have freshnessCertificate0249 :
    c ∉
      ((syntaxClass0014).fv) ∪
        (((syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0248 freshnessCertificate0238))
  have freshnessCertificate0250 : c ∉ (syntaxClass0015).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak];
      exact freshnessCertificate0249)
  have freshnessCertificate0251 :
    c ∉
      (((syn_copk (.cv t) (syn_copk (syn_csn (.cv a)) (.cv n)))).fv) ∪
        ((syntaxClass0015).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0200 freshnessCertificate0250))
  have freshnessCertificate0252 :
    c ∉
      ((Wff.classMem (syn_copk (.cv t) (syn_copk (syn_csn (.cv a)) (.cv n)))
          syntaxClass0015)).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact freshnessCertificate0251)
  have p0030 :=
    @g_n_19_41v (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv c))))) syntaxFormula0031
      c (by exact freshnessCertificate0252)
  have p0031 :=
    @g_bitr4i syntaxFormula0033
      (syn_wa (syn_wex c (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv c))))))
        syntaxFormula0031)
      syntaxFormula0035 p0029 p0030
  have p0032 := @g_exbii syntaxFormula0033 syntaxFormula0035 t p0031
  have p0033 := @g_excom syntaxFormula0034 c t
  have p0034 :=
    @g_bitr4i syntaxFormula0036 (syn_wex t syntaxFormula0035) syntaxFormula0038 p0032
      p0033
  have p0035 :=
    @g_n_3bitri syntaxFormula0039 syntaxFormula0032 syntaxFormula0036 syntaxFormula0038
      p0026 p0027 p0034
  have p0036 :=
    @g_otkelins3k (syn_csn (.cv a)) (.cv n) (.cv x) syntaxClass0016 p0019 p0020 p0002
  have freshnessCertificate0253 : b ∉ ((Class.cv a)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show b ∉ ({ a } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show b ≠ a from (by exact fresh_b_ne_a)))))
  have freshnessCertificate0254 : b ∉ ((Class.cv n)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show b ∉ ({ n } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show b ≠ n from (by exact fresh_b_ne_n)))))
  have p0037 :=
    @g_eladdc (.cv a) (.cv n) (.cv n) b c (by exact freshnessCertificate0253)
      (by exact freshnessCertificate0194) (by exact freshnessCertificate0254)
      (by exact freshnessCertificate0196) (by exact freshnessCertificate0254)
      (by exact freshnessCertificate0196) (show b ≠ c from (by exact fresh_b_ne_c))
  have p0038 :=
    @g_r2ex syntaxFormula0040 b c (.cv n) (.cv n) (by exact freshnessCertificate0196)
      (show b ≠ c from (by exact fresh_b_ne_c))
  have p0039 :=
    @g_excom (syn_wa (syn_wa (.objMem b n) (.objMem c n)) syntaxFormula0040) b c
  have p0040 := @g_snex (syn_csn (syn_csn (.cv c)))
  have p0041 :=
    @g_opkeq1 (.cv t) (syn_csn (syn_csn (syn_csn (.cv c))))
      (syn_copk (syn_csn (.cv a)) (.cv n))
  have p0042 :=
    @g_eleq1d (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv c)))))
      (syn_copk (.cv t) (syn_copk (syn_csn (.cv a)) (.cv n))) syntaxClass0041
      syntaxClass0015 p0041
  have freshnessCertificate0255 : t ∉ ((Class.cv c)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show t ∉ ({ c } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show t ≠ c from (by exact fresh_t_ne_c)))))
  have freshnessCertificate0256 : t ∉ ((syn_csn (.cv c))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0255)
  have freshnessCertificate0257 : t ∉ ((syn_csn (syn_csn (.cv c)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0256)
  have freshnessCertificate0258 : t ∉ ((syn_csn (syn_csn (syn_csn (.cv c))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0257)
  have freshnessCertificate0259 :
    t ∉
      (((syn_csn (syn_csn (syn_csn (.cv c))))).fv) ∪
        (((syn_copk (syn_csn (.cv a)) (.cv n))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0258 freshnessCertificate0192))
  have freshnessCertificate0260 : t ∉ (syntaxClass0041).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk];
      exact freshnessCertificate0259)
  have freshnessCertificate0261 : t ∉ ((syntaxClass0041).fv) ∪ ((syntaxClass0015).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0260 freshnessCertificate0109))
  have freshnessCertificate0262 :
    t ∉ ((Wff.classMem syntaxClass0041 syntaxClass0015)).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact freshnessCertificate0261)
  have p0043 :=
    @g_ceqsexv syntaxFormula0031 syntaxFormula0042 t (syn_csn (syn_csn (syn_csn (.cv c))))
      (by exact freshnessCertificate0258) (by exact freshnessCertificate0262) p0040 p0042
  have p0044 :=
    @g_opkex (syn_csn (syn_csn (syn_csn (.cv c)))) (syn_copk (syn_csn (.cv a)) (.cv n))
  have p0045 :=
    @g_elimak t syntaxClass0014 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))
      syntaxClass0041 (by exact freshnessCertificate0107)
      (by exact freshnessCertificate0097) (by exact freshnessCertificate0260) p0044
  have p0046 := (Nominal.biimpRefl syntaxFormula0045)
  have freshnessCertificate0263 : b ∉ ((Class.cv t)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show b ∉ ({ t } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show b ≠ t from (by exact fresh_b_ne_t)))))
  have p0047 := @g_elpw141c b (.cv t) (by exact freshnessCertificate0263)
  have p0048 :=
    @g_anbi1i (.classMem (.cv t) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))
      (syn_wex b (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv b))))))))
      syntaxFormula0044 p0047
  have freshnessCertificate0264 : b ∉ ((Class.cv c)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show b ∉ ({ c } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show b ≠ c from (by exact fresh_b_ne_c)))))
  have freshnessCertificate0265 : b ∉ ((syn_csn (.cv c))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0264)
  have freshnessCertificate0266 : b ∉ ((syn_csn (syn_csn (.cv c)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0265)
  have freshnessCertificate0267 : b ∉ ((syn_csn (syn_csn (syn_csn (.cv c))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0266)
  have freshnessCertificate0268 : b ∉ ((syn_csn (.cv a))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0253)
  have freshnessCertificate0269 : b ∉ (((syn_csn (.cv a))).fv) ∪ (((Class.cv n)).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0268 freshnessCertificate0254))
  have freshnessCertificate0270 : b ∉ ((syn_copk (syn_csn (.cv a)) (.cv n))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk];
      exact freshnessCertificate0269)
  have freshnessCertificate0271 :
    b ∉
      (((syn_csn (syn_csn (syn_csn (.cv c))))).fv) ∪
        (((syn_copk (syn_csn (.cv a)) (.cv n))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0267 freshnessCertificate0270))
  have freshnessCertificate0272 : b ∉ (syntaxClass0041).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk];
      exact freshnessCertificate0271)
  have freshnessCertificate0273 : b ∉ (((Class.cv t)).fv) ∪ ((syntaxClass0041).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0263 freshnessCertificate0272))
  have freshnessCertificate0274 : b ∉ (syntaxClass0043).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk];
      exact freshnessCertificate0273)
  have freshnessCertificate0275 : b ∉ ((syn_cssetk)).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk];
      exact (show b ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))
  have freshnessCertificate0276 : b ∉ ((syn_cins2k (syn_cssetk))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0275)
  have freshnessCertificate0277 : b ∉ ((syn_cins2k (syn_cins2k (syn_cssetk)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0276)
  have freshnessCertificate0278 : b ∉ ((syn_cvv)).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv];
      exact (show b ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))
  have freshnessCertificate0279 :
    b ∉ (((syn_cvv)).fv) ∪ (((syn_cins2k (syn_cssetk))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0278 freshnessCertificate0276))
  have freshnessCertificate0280 :
    b ∉ ((syn_cxpk (syn_cvv) (syn_cins2k (syn_cssetk)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk];
      exact freshnessCertificate0279)
  have freshnessCertificate0281 :
    b ∉
      (((syn_cins2k (syn_cins2k (syn_cssetk)))).fv) ∪
        (((syn_cxpk (syn_cvv) (syn_cins2k (syn_cssetk)))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0277 freshnessCertificate0280))
  have freshnessCertificate0282 : b ∉ (syntaxClass0000).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin];
      exact freshnessCertificate0281)
  have freshnessCertificate0283 : b ∉ ((syn_cins3k (syn_cssetk))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0275)
  have freshnessCertificate0284 :
    b ∉ (((syn_cins3k (syn_cssetk))).fv) ∪ (((syn_cins2k (syn_cssetk))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0283 freshnessCertificate0276))
  have freshnessCertificate0285 :
    b ∉ ((syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin];
      exact freshnessCertificate0284)
  have freshnessCertificate0286 : b ∉ ((syn_c1c)).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c];
      exact (show b ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))
  have freshnessCertificate0287 : b ∉ ((syn_cpw1 (syn_c1c))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0286)
  have freshnessCertificate0288 : b ∉ ((syn_cpw1 (syn_cpw1 (syn_c1c)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0287)
  have freshnessCertificate0289 :
    b ∉
      (((syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))).fv) ∪
        (((syn_cpw1 (syn_cpw1 (syn_c1c)))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0285 freshnessCertificate0288))
  have freshnessCertificate0290 : b ∉ (syntaxClass0001).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak];
      exact freshnessCertificate0289)
  have freshnessCertificate0291 : b ∉ (syntaxClass0002).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl];
      exact freshnessCertificate0290)
  have freshnessCertificate0292 : b ∉ (syntaxClass0003).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0291)
  have freshnessCertificate0293 : b ∉ (syntaxClass0004).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0292)
  have freshnessCertificate0294 : b ∉ (syntaxClass0005).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0293)
  have freshnessCertificate0295 : b ∉ (syntaxClass0006).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0294)
  have freshnessCertificate0296 : b ∉ ((syn_csik (syn_cssetk))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0275)
  have freshnessCertificate0297 : b ∉ ((syn_cins3k (syn_csik (syn_cssetk)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0296)
  have freshnessCertificate0298 :
    b ∉ ((syn_cins2k (syn_cins3k (syn_csik (syn_cssetk))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0297)
  have freshnessCertificate0299 :
    b ∉ ((syn_cins2k (syn_cins2k (syn_cins3k (syn_csik (syn_cssetk)))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0298)
  have freshnessCertificate0300 : b ∉ ((syn_csik (syn_csik (syn_cssetk)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0296)
  have freshnessCertificate0301 :
    b ∉ ((syn_csik (syn_csik (syn_csik (syn_cssetk))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0300)
  have freshnessCertificate0302 :
    b ∉ ((syn_csik (syn_csik (syn_csik (syn_csik (syn_cssetk)))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0301)
  have freshnessCertificate0303 :
    b ∉ ((syn_csik (syn_csik (syn_csik (syn_csik (syn_csik (syn_cssetk))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0302)
  have freshnessCertificate0304 : b ∉ (syntaxClass0007).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0303)
  have freshnessCertificate0305 :
    b ∉ ((syn_cins3k (syn_csik (syn_csik (syn_csik (syn_cssetk)))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0301)
  have freshnessCertificate0306 :
    b ∉ ((syn_cins2k (syn_cins3k (syn_csik (syn_csik (syn_csik (syn_cssetk))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0305)
  have freshnessCertificate0307 :
    b ∉
      ((syntaxClass0007).fv) ∪
        (((syn_cins2k (syn_cins3k (syn_csik (syn_csik (syn_csik (syn_cssetk))))))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0304 freshnessCertificate0306))
  have freshnessCertificate0308 : b ∉ (syntaxClass0008).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun];
      exact freshnessCertificate0307)
  have freshnessCertificate0309 :
    b ∉
      (((syn_cins2k (syn_cins2k (syn_cins3k (syn_csik (syn_cssetk)))))).fv) ∪
        ((syntaxClass0008).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0299 freshnessCertificate0308))
  have freshnessCertificate0310 : b ∉ (syntaxClass0009).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif];
      exact freshnessCertificate0309)
  have freshnessCertificate0311 : b ∉ ((syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0288)
  have freshnessCertificate0312 :
    b ∉ ((syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0311)
  have freshnessCertificate0313 :
    b ∉ ((syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0312)
  have freshnessCertificate0314 :
    b ∉
      ((syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0313)
  have freshnessCertificate0315 : b ∉ (syntaxClass0010).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0314)
  have freshnessCertificate0316 : b ∉ ((syntaxClass0009).fv) ∪ ((syntaxClass0010).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0310 freshnessCertificate0315))
  have freshnessCertificate0317 : b ∉ (syntaxClass0011).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak];
      exact freshnessCertificate0316)
  have freshnessCertificate0318 : b ∉ (syntaxClass0012).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl];
      exact freshnessCertificate0317)
  have freshnessCertificate0319 : b ∉ ((syntaxClass0006).fv) ∪ ((syntaxClass0012).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0295 freshnessCertificate0318))
  have freshnessCertificate0320 : b ∉ (syntaxClass0013).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin];
      exact freshnessCertificate0319)
  have freshnessCertificate0321 : b ∉ ((syntaxClass0000).fv) ∪ ((syntaxClass0013).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0282 freshnessCertificate0320))
  have freshnessCertificate0322 : b ∉ (syntaxClass0014).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin];
      exact freshnessCertificate0321)
  have freshnessCertificate0323 : b ∉ ((syntaxClass0043).fv) ∪ ((syntaxClass0014).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0274 freshnessCertificate0322))
  have freshnessCertificate0324 :
    b ∉ ((Wff.classMem syntaxClass0043 syntaxClass0014)).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact freshnessCertificate0323)
  have p0049 :=
    @g_n_19_41v
      (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv b)))))))
      syntaxFormula0044 b (by exact freshnessCertificate0324)
  have p0050 :=
    @g_bitr4i syntaxFormula0046
      (syn_wa (syn_wex b
          (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv b))))))))
        syntaxFormula0044)
      syntaxFormula0048 p0048 p0049
  have p0051 := @g_exbii syntaxFormula0046 syntaxFormula0048 t p0050
  have p0052 := @g_excom syntaxFormula0047 b t
  have p0053 :=
    @g_bitr4i syntaxFormula0049 (syn_wex t syntaxFormula0048) syntaxFormula0051 p0051
      p0052
  have p0054 :=
    @g_n_3bitri syntaxFormula0042 syntaxFormula0045 syntaxFormula0049 syntaxFormula0051
      p0045 p0046 p0053
  have p0055 := @g_snex (syn_csn (syn_csn (syn_csn (syn_csn (.cv b)))))
  have p0056 :=
    @g_opkeq1 (.cv t) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv b))))))
      syntaxClass0041
  have p0057 :=
    @g_eleq1d (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv b)))))))
      syntaxClass0043 syntaxClass0052 syntaxClass0014 p0056
  have freshnessCertificate0325 : t ∉ ((Class.cv b)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show t ∉ ({ b } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show t ≠ b from (by exact fresh_t_ne_b)))))
  have freshnessCertificate0326 : t ∉ ((syn_csn (.cv b))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0325)
  have freshnessCertificate0327 : t ∉ ((syn_csn (syn_csn (.cv b)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0326)
  have freshnessCertificate0328 : t ∉ ((syn_csn (syn_csn (syn_csn (.cv b))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0327)
  have freshnessCertificate0329 :
    t ∉ ((syn_csn (syn_csn (syn_csn (syn_csn (.cv b)))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0328)
  have freshnessCertificate0330 :
    t ∉ ((syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv b))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0329)
  have freshnessCertificate0331 :
    t ∉
      (((syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv b))))))).fv) ∪
        ((syntaxClass0041).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0330 freshnessCertificate0260))
  have freshnessCertificate0332 : t ∉ (syntaxClass0052).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk];
      exact freshnessCertificate0331)
  have freshnessCertificate0333 : t ∉ ((syntaxClass0052).fv) ∪ ((syntaxClass0014).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0332 freshnessCertificate0107))
  have freshnessCertificate0334 :
    t ∉ ((Wff.classMem syntaxClass0052 syntaxClass0014)).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact freshnessCertificate0333)
  have p0058 :=
    @g_ceqsexv syntaxFormula0044 syntaxFormula0053 t
      (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv b))))))
      (by exact freshnessCertificate0330) (by exact freshnessCertificate0334) p0055 p0057
  have p0059 := @g_elin syntaxClass0052 syntaxClass0000 syntaxClass0013
  have p0060 :=
    @g_elin syntaxClass0052 (syn_cins2k (syn_cins2k (syn_cssetk)))
      (syn_cxpk (syn_cvv) (syn_cins2k (syn_cssetk)))
  have p0061 := @g_snex (syn_csn (syn_csn (.cv b)))
  have p0062 :=
    @g_otkelins2k (syn_csn (syn_csn (syn_csn (.cv b))))
      (syn_csn (syn_csn (syn_csn (.cv c)))) (syn_copk (syn_csn (.cv a)) (.cv n))
      (syn_cins2k (syn_cssetk)) p0061 p0040 p0025
  have p0063 := @g_snex (.cv b)
  have p0064 :=
    @g_otkelins2k (syn_csn (.cv b)) (syn_csn (.cv a)) (.cv n) (syn_cssetk) p0063 p0019
      p0020
  have p0065 := @g_vex b
  have p0066 := @g_elssetk (.cv b) (.cv n) p0065 p0020
  have p0067_e02_recanon :
    Nominal.NPrf
      (syn_wb (.classMem (syn_copk (syn_csn (.cv b)) (.cv n)) (syn_cssetk)) (.objMem b n)) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [syn_wb, syn_copk, syn_cpr, syn_cun, syn_cnin, syn_wnan, syn_wa,
          syn_ccompl, syn_csn, syn_cssetk, syn_wex]
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
      p0066
  have p0067 :=
    @g_n_3bitri syntaxFormula0054
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv b))))
          (syn_copk (syn_csn (.cv a)) (.cv n))) (syn_cins2k (syn_cssetk)))
      (.classMem (syn_copk (syn_csn (.cv b)) (.cv n)) (syn_cssetk)) (.objMem b n) p0062
      p0064 p0067_e02_recanon
  have p0068 :=
    @g_opkelxpk (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv b)))))) syntaxClass0041
      (syn_cvv) (syn_cins2k (syn_cssetk)) p0055 p0044
  have p0069 :=
    @g_mpbiran syntaxFormula0055
      (.classMem (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv b)))))) (syn_cvv))
      (.classMem syntaxClass0041 (syn_cins2k (syn_cssetk))) p0055 p0068
  have p0070 := @g_snex (.cv c)
  have p0071 :=
    @g_otkelins2k (syn_csn (.cv c)) (syn_csn (.cv a)) (.cv n) (syn_cssetk) p0070 p0019
      p0020
  have p0072 := @g_vex c
  have p0073 := @g_elssetk (.cv c) (.cv n) p0072 p0020
  have p0074_e02_recanon :
    Nominal.NPrf
      (syn_wb (.classMem (syn_copk (syn_csn (.cv c)) (.cv n)) (syn_cssetk)) (.objMem c n)) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [syn_wb, syn_copk, syn_cpr, syn_cun, syn_cnin, syn_wnan, syn_wa,
          syn_ccompl, syn_csn, syn_cssetk, syn_wex]
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
      p0073
  have p0074 :=
    @g_n_3bitri syntaxFormula0055 (.classMem syntaxClass0041 (syn_cins2k (syn_cssetk)))
      (.classMem (syn_copk (syn_csn (.cv c)) (.cv n)) (syn_cssetk)) (.objMem c n) p0069
      p0071 p0074_e02_recanon
  have p0075 :=
    @g_anbi12i syntaxFormula0054 (.objMem b n) syntaxFormula0055 (.objMem c n) p0067 p0074
  have p0076 :=
    @g_bitri syntaxFormula0056 (syn_wa syntaxFormula0054 syntaxFormula0055)
      (syn_wa (.objMem b n) (.objMem c n)) p0060 p0075
  have p0077 := @g_elin syntaxClass0052 syntaxClass0006 syntaxClass0012
  have p0078 :=
    @g_otkelins3k (syn_csn (syn_csn (syn_csn (.cv b))))
      (syn_csn (syn_csn (syn_csn (.cv c)))) (syn_copk (syn_csn (.cv a)) (.cv n))
      syntaxClass0005 p0061 p0040 p0025
  have p0079 := @g_snex (syn_csn (.cv b))
  have p0080 := @g_snex (syn_csn (.cv c))
  have p0081 :=
    @g_opksnelsik (syn_csn (syn_csn (.cv b))) (syn_csn (syn_csn (.cv c))) syntaxClass0004
      p0079 p0080
  have p0082 :=
    @g_opksnelsik (syn_csn (.cv b)) (syn_csn (.cv c)) syntaxClass0003 p0063 p0070
  have p0083 := @g_opksnelsik (.cv b) (.cv c) syntaxClass0002 p0065 p0072
  have p0084 := @g_ndisjrelk (.cv b) (.cv c) p0065 p0072
  have p0085 :=
    @g_notbii (.classMem (syn_copk (.cv b) (.cv c)) syntaxClass0001)
      (syn_wne (syn_cin (.cv b) (.cv c)) (syn_c0)) p0084
  have p0086 := @g_opkex (.cv b) (.cv c)
  have p0087 := @g_elcompl (syn_copk (.cv b) (.cv c)) syntaxClass0001 p0086
  have p0088 := (Nominal.biimpRefl (syn_wne (syn_cin (.cv b) (.cv c)) (syn_c0)))
  have p0089 :=
    @g_con2bii (syn_wne (syn_cin (.cv b) (.cv c)) (syn_c0))
      (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0)) p0088
  have p0090 :=
    @g_n_3bitr4i (.neg (.classMem (syn_copk (.cv b) (.cv c)) syntaxClass0001))
      (.neg (syn_wne (syn_cin (.cv b) (.cv c)) (syn_c0)))
      (.classMem (syn_copk (.cv b) (.cv c)) syntaxClass0002)
      (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0)) p0085 p0087 p0089
  have p0091 :=
    @g_n_3bitri syntaxFormula0057
      (.classMem (syn_copk (syn_csn (.cv b)) (syn_csn (.cv c))) syntaxClass0003)
      (.classMem (syn_copk (.cv b) (.cv c)) syntaxClass0002)
      (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0)) p0082 p0083 p0090
  have p0092 :=
    @g_n_3bitri syntaxFormula0058
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv b))))
          (syn_csn (syn_csn (syn_csn (.cv c))))) syntaxClass0005)
      syntaxFormula0057 (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0)) p0078 p0081 p0091
  have p0093 :=
    @g_opkex (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv b)))))) syntaxClass0041
  have p0094 :=
    @g_elimak t syntaxClass0009 syntaxClass0010 syntaxClass0052
      (by exact freshnessCertificate0095) (by exact freshnessCertificate0100)
      (by exact freshnessCertificate0332) p0093
  have freshnessCertificate0335 : x ∉ ((Class.cv t)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show x ∉ ({ t } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show x ≠ t from (by exact fresh_x_ne_t)))))
  have p0095 := @g_elpw171c x (.cv t) (by exact freshnessCertificate0335)
  have p0096 :=
    @g_anbi1i syntaxFormula0059 (syn_wex x syntaxFormula0061) syntaxFormula0063 p0095
  have freshnessCertificate0336 : x ∉ ((Class.cv b)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show x ∉ ({ b } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show x ≠ b from (by exact fresh_x_ne_b)))))
  have freshnessCertificate0337 : x ∉ ((syn_csn (.cv b))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0336)
  have freshnessCertificate0338 : x ∉ ((syn_csn (syn_csn (.cv b)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0337)
  have freshnessCertificate0339 : x ∉ ((syn_csn (syn_csn (syn_csn (.cv b))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0338)
  have freshnessCertificate0340 :
    x ∉ ((syn_csn (syn_csn (syn_csn (syn_csn (.cv b)))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0339)
  have freshnessCertificate0341 :
    x ∉ ((syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv b))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0340)
  have freshnessCertificate0342 : x ∉ ((Class.cv c)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show x ∉ ({ c } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show x ≠ c from (by exact fresh_x_ne_c)))))
  have freshnessCertificate0343 : x ∉ ((syn_csn (.cv c))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0342)
  have freshnessCertificate0344 : x ∉ ((syn_csn (syn_csn (.cv c)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0343)
  have freshnessCertificate0345 : x ∉ ((syn_csn (syn_csn (syn_csn (.cv c))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0344)
  have freshnessCertificate0346 : x ∉ ((Class.cv a)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show x ∉ ({ a } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show x ≠ a from (by exact fresh_x_ne_a)))))
  have freshnessCertificate0347 : x ∉ ((syn_csn (.cv a))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0346)
  have freshnessCertificate0348 : x ∉ ((Class.cv n)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show x ∉ ({ n } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show x ≠ n from (by exact fresh_x_ne_n)))))
  have freshnessCertificate0349 : x ∉ (((syn_csn (.cv a))).fv) ∪ (((Class.cv n)).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0347 freshnessCertificate0348))
  have freshnessCertificate0350 : x ∉ ((syn_copk (syn_csn (.cv a)) (.cv n))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk];
      exact freshnessCertificate0349)
  have freshnessCertificate0351 :
    x ∉
      (((syn_csn (syn_csn (syn_csn (.cv c))))).fv) ∪
        (((syn_copk (syn_csn (.cv a)) (.cv n))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0345 freshnessCertificate0350))
  have freshnessCertificate0352 : x ∉ (syntaxClass0041).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk];
      exact freshnessCertificate0351)
  have freshnessCertificate0353 :
    x ∉
      (((syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv b))))))).fv) ∪
        ((syntaxClass0041).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0341 freshnessCertificate0352))
  have freshnessCertificate0354 : x ∉ (syntaxClass0052).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk];
      exact freshnessCertificate0353)
  have freshnessCertificate0355 : x ∉ (((Class.cv t)).fv) ∪ ((syntaxClass0052).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0335 freshnessCertificate0354))
  have freshnessCertificate0356 : x ∉ (syntaxClass0062).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk];
      exact freshnessCertificate0355)
  have freshnessCertificate0357 : x ∉ ((syn_cssetk)).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk];
      exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))
  have freshnessCertificate0358 : x ∉ ((syn_csik (syn_cssetk))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0357)
  have freshnessCertificate0359 : x ∉ ((syn_cins3k (syn_csik (syn_cssetk)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0358)
  have freshnessCertificate0360 :
    x ∉ ((syn_cins2k (syn_cins3k (syn_csik (syn_cssetk))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0359)
  have freshnessCertificate0361 :
    x ∉ ((syn_cins2k (syn_cins2k (syn_cins3k (syn_csik (syn_cssetk)))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0360)
  have freshnessCertificate0362 : x ∉ ((syn_csik (syn_csik (syn_cssetk)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0358)
  have freshnessCertificate0363 :
    x ∉ ((syn_csik (syn_csik (syn_csik (syn_cssetk))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0362)
  have freshnessCertificate0364 :
    x ∉ ((syn_csik (syn_csik (syn_csik (syn_csik (syn_cssetk)))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0363)
  have freshnessCertificate0365 :
    x ∉ ((syn_csik (syn_csik (syn_csik (syn_csik (syn_csik (syn_cssetk))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0364)
  have freshnessCertificate0366 : x ∉ (syntaxClass0007).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0365)
  have freshnessCertificate0367 :
    x ∉ ((syn_cins3k (syn_csik (syn_csik (syn_csik (syn_cssetk)))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0363)
  have freshnessCertificate0368 :
    x ∉ ((syn_cins2k (syn_cins3k (syn_csik (syn_csik (syn_csik (syn_cssetk))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0367)
  have freshnessCertificate0369 :
    x ∉
      ((syntaxClass0007).fv) ∪
        (((syn_cins2k (syn_cins3k (syn_csik (syn_csik (syn_csik (syn_cssetk))))))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0366 freshnessCertificate0368))
  have freshnessCertificate0370 : x ∉ (syntaxClass0008).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun];
      exact freshnessCertificate0369)
  have freshnessCertificate0371 :
    x ∉
      (((syn_cins2k (syn_cins2k (syn_cins3k (syn_csik (syn_cssetk)))))).fv) ∪
        ((syntaxClass0008).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0361 freshnessCertificate0370))
  have freshnessCertificate0372 : x ∉ (syntaxClass0009).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif];
      exact freshnessCertificate0371)
  have freshnessCertificate0373 : x ∉ ((syntaxClass0062).fv) ∪ ((syntaxClass0009).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0356 freshnessCertificate0372))
  have freshnessCertificate0374 :
    x ∉ ((Wff.classMem syntaxClass0062 syntaxClass0009)).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact freshnessCertificate0373)
  have p0097 :=
    @g_n_19_41v syntaxFormula0061 syntaxFormula0063 x (by exact freshnessCertificate0374)
  have p0098 :=
    @g_bitr4i syntaxFormula0064 (syn_wa (syn_wex x syntaxFormula0061) syntaxFormula0063)
      syntaxFormula0066 p0096 p0097
  have p0099 := @g_exbii syntaxFormula0064 syntaxFormula0066 t p0098
  have p0100 := (Nominal.biimpRefl syntaxFormula0067)
  have p0101 := @g_excom syntaxFormula0065 x t
  have p0102 :=
    @g_n_3bitr4i (syn_wex t syntaxFormula0064) (syn_wex t syntaxFormula0066)
      syntaxFormula0067 syntaxFormula0069 p0099 p0100 p0101
  have p0103 :=
    @g_snex (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))))
  have p0104 := @g_opkeq1 (.cv t) syntaxClass0060 syntaxClass0052
  have p0105 :=
    @g_eleq1d syntaxFormula0061 syntaxClass0062 syntaxClass0070 syntaxClass0009 p0104
  have freshnessCertificate0375 : t ∉ ((syn_csn (.cv x))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0116)
  have freshnessCertificate0376 : t ∉ ((syn_csn (syn_csn (.cv x)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0375)
  have freshnessCertificate0377 : t ∉ ((syn_csn (syn_csn (syn_csn (.cv x))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0376)
  have freshnessCertificate0378 :
    t ∉ ((syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0377)
  have freshnessCertificate0379 :
    t ∉ ((syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0378)
  have freshnessCertificate0380 :
    t ∉ ((syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0379)
  have freshnessCertificate0381 :
    t ∉
      ((syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0380)
  have freshnessCertificate0382 : t ∉ (syntaxClass0060).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0381)
  have freshnessCertificate0383 : t ∉ ((syntaxClass0060).fv) ∪ ((syntaxClass0052).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0382 freshnessCertificate0332))
  have freshnessCertificate0384 : t ∉ (syntaxClass0070).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk];
      exact freshnessCertificate0383)
  have freshnessCertificate0385 : t ∉ ((syntaxClass0070).fv) ∪ ((syntaxClass0009).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0384 freshnessCertificate0095))
  have freshnessCertificate0386 :
    t ∉ ((Wff.classMem syntaxClass0070 syntaxClass0009)).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact freshnessCertificate0385)
  have p0106 :=
    @g_ceqsexv syntaxFormula0063 syntaxFormula0071 t syntaxClass0060
      (by exact freshnessCertificate0382) (by exact freshnessCertificate0386) p0103 p0105
  have p0107 :=
    @g_elsymdif syntaxClass0070
      (syn_cins2k (syn_cins2k (syn_cins3k (syn_csik (syn_cssetk))))) syntaxClass0008
  have p0108 := @g_snex (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))
  have p0109 :=
    @g_otkelins2k (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))
      (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv b)))))) syntaxClass0041
      (syn_cins2k (syn_cins3k (syn_csik (syn_cssetk)))) p0108 p0055 p0044
  have p0110 := @g_snex (syn_csn (syn_csn (syn_csn (.cv x))))
  have p0111 :=
    @g_otkelins2k (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))
      (syn_csn (syn_csn (syn_csn (.cv c)))) (syn_copk (syn_csn (.cv a)) (.cv n))
      (syn_cins3k (syn_csik (syn_cssetk))) p0110 p0040 p0025
  have p0112 := @g_snex (syn_csn (.cv x))
  have p0113 :=
    @g_otkelins3k (syn_csn (syn_csn (.cv x))) (syn_csn (.cv a)) (.cv n)
      (syn_csik (syn_cssetk)) p0112 p0019 p0020
  have p0114 := @g_snex (.cv x)
  have p0115 := @g_opksnelsik (syn_csn (.cv x)) (.cv a) (syn_cssetk) p0114 p0022
  have p0116 := @g_elssetk (.cv x) (.cv a) p0002 p0022
  have p0117_e02_recanon :
    Nominal.NPrf
      (syn_wb (.classMem (syn_copk (syn_csn (.cv x)) (.cv a)) (syn_cssetk)) (.objMem x a)) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [syn_wb, syn_copk, syn_cpr, syn_cun, syn_cnin, syn_wnan, syn_wa,
          syn_ccompl, syn_csn, syn_cssetk, syn_wex]
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
      p0116
  have p0117 :=
    @g_n_3bitri
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))
          (syn_copk (syn_csn (.cv a)) (.cv n))) (syn_cins3k (syn_csik (syn_cssetk))))
      (.classMem (syn_copk (syn_csn (syn_csn (.cv x))) (syn_csn (.cv a)))
        (syn_csik (syn_cssetk)))
      (.classMem (syn_copk (syn_csn (.cv x)) (.cv a)) (syn_cssetk)) (.objMem x a) p0113
      p0115 p0117_e02_recanon
  have p0118 :=
    @g_n_3bitri syntaxFormula0072
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))
          syntaxClass0041) (syn_cins2k (syn_cins3k (syn_csik (syn_cssetk)))))
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))
          (syn_copk (syn_csn (.cv a)) (.cv n))) (syn_cins3k (syn_csik (syn_cssetk))))
      (.objMem x a) p0109 p0111 p0117
  have p0119 :=
    @g_otkelins3k (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))
      (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv b)))))) syntaxClass0041
      (syn_csik (syn_csik (syn_csik (syn_csik (syn_csik (syn_cssetk)))))) p0108 p0055
      p0044
  have p0120 := @g_snex (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))
  have p0121 := @g_snex (syn_csn (syn_csn (syn_csn (.cv b))))
  have p0122 :=
    @g_opksnelsik (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))
      (syn_csn (syn_csn (syn_csn (syn_csn (.cv b)))))
      (syn_csik (syn_csik (syn_csik (syn_csik (syn_cssetk))))) p0120 p0121
  have p0123 :=
    @g_opksnelsik (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))
      (syn_csn (syn_csn (syn_csn (.cv b)))) (syn_csik (syn_csik (syn_csik (syn_cssetk))))
      p0110 p0061
  have p0124 := @g_snex (syn_csn (syn_csn (.cv x)))
  have p0125 :=
    @g_opksnelsik (syn_csn (syn_csn (syn_csn (.cv x)))) (syn_csn (syn_csn (.cv b)))
      (syn_csik (syn_csik (syn_cssetk))) p0124 p0079
  have p0126 :=
    @g_opksnelsik (syn_csn (syn_csn (.cv x))) (syn_csn (.cv b)) (syn_csik (syn_cssetk))
      p0112 p0063
  have p0127 := @g_opksnelsik (syn_csn (.cv x)) (.cv b) (syn_cssetk) p0114 p0065
  have p0128 := @g_elssetk (.cv x) (.cv b) p0002 p0065
  have p0129_e02_recanon :
    Nominal.NPrf
      (syn_wb (.classMem (syn_copk (syn_csn (.cv x)) (.cv b)) (syn_cssetk)) (.objMem x b)) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [syn_wb, syn_copk, syn_cpr, syn_cun, syn_cnin, syn_wnan, syn_wa,
          syn_ccompl, syn_csn, syn_cssetk, syn_wex]
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
      p0128
  have p0129 :=
    @g_n_3bitri
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv x)))) (syn_csn (syn_csn (.cv b))))
        (syn_csik (syn_csik (syn_cssetk))))
      (.classMem (syn_copk (syn_csn (syn_csn (.cv x))) (syn_csn (.cv b)))
        (syn_csik (syn_cssetk)))
      (.classMem (syn_copk (syn_csn (.cv x)) (.cv b)) (syn_cssetk)) (.objMem x b) p0126
      p0127 p0129_e02_recanon
  have p0130 :=
    @g_n_3bitri syntaxFormula0073
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))
          (syn_csn (syn_csn (syn_csn (.cv b))))) (syn_csik (syn_csik (syn_csik (syn_cssetk)))))
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv x)))) (syn_csn (syn_csn (.cv b))))
        (syn_csik (syn_csik (syn_cssetk))))
      (.objMem x b) p0123 p0125 p0129
  have p0131 :=
    @g_n_3bitri syntaxFormula0074
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))
          (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv b)))))))
        (syn_csik (syn_csik (syn_csik (syn_csik (syn_csik (syn_cssetk)))))))
      syntaxFormula0073 (.objMem x b) p0119 p0122 p0130
  have p0132 :=
    @g_otkelins2k (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))
      (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv b)))))) syntaxClass0041
      (syn_cins3k (syn_csik (syn_csik (syn_csik (syn_cssetk))))) p0108 p0055 p0044
  have p0133 :=
    @g_otkelins3k (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))
      (syn_csn (syn_csn (syn_csn (.cv c)))) (syn_copk (syn_csn (.cv a)) (.cv n))
      (syn_csik (syn_csik (syn_csik (syn_cssetk)))) p0110 p0040 p0025
  have p0134 :=
    @g_opksnelsik (syn_csn (syn_csn (syn_csn (.cv x)))) (syn_csn (syn_csn (.cv c)))
      (syn_csik (syn_csik (syn_cssetk))) p0124 p0080
  have p0135 :=
    @g_opksnelsik (syn_csn (syn_csn (.cv x))) (syn_csn (.cv c)) (syn_csik (syn_cssetk))
      p0112 p0070
  have p0136 := @g_opksnelsik (syn_csn (.cv x)) (.cv c) (syn_cssetk) p0114 p0072
  have p0137 := @g_elssetk (.cv x) (.cv c) p0002 p0072
  have p0138_e01_recanon :
    Nominal.NPrf
      (syn_wb (.classMem (syn_copk (syn_csn (.cv x)) (.cv c)) (syn_cssetk)) (.objMem x c)) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [syn_wb, syn_copk, syn_cpr, syn_cun, syn_cnin, syn_wnan, syn_wa,
          syn_ccompl, syn_csn, syn_cssetk, syn_wex]
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
      p0137
  have p0138 :=
    @g_bitri
      (.classMem (syn_copk (syn_csn (syn_csn (.cv x))) (syn_csn (.cv c)))
        (syn_csik (syn_cssetk)))
      (.classMem (syn_copk (syn_csn (.cv x)) (.cv c)) (syn_cssetk)) (.objMem x c) p0136
      p0138_e01_recanon
  have p0139 :=
    @g_n_3bitri
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))
          (syn_csn (syn_csn (syn_csn (.cv c))))) (syn_csik (syn_csik (syn_csik (syn_cssetk)))))
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv x)))) (syn_csn (syn_csn (.cv c))))
        (syn_csik (syn_csik (syn_cssetk))))
      (.classMem (syn_copk (syn_csn (syn_csn (.cv x))) (syn_csn (.cv c)))
        (syn_csik (syn_cssetk)))
      (.objMem x c) p0134 p0135 p0138
  have p0140 :=
    @g_n_3bitri syntaxFormula0075
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))
          syntaxClass0041) (syn_cins3k (syn_csik (syn_csik (syn_csik (syn_cssetk))))))
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))
          (syn_csn (syn_csn (syn_csn (.cv c))))) (syn_csik (syn_csik (syn_csik (syn_cssetk)))))
      (.objMem x c) p0132 p0133 p0139
  have p0141 :=
    @g_orbi12i syntaxFormula0074 (.objMem x b) syntaxFormula0075 (.objMem x c) p0131 p0140
  have p0142 :=
    @g_elun syntaxClass0070 syntaxClass0007
      (syn_cins2k (syn_cins3k (syn_csik (syn_csik (syn_csik (syn_cssetk))))))
  have p0143 := @g_elun (.cv x) (.cv b) (.cv c)
  have p0144_e02_recanon :
    Nominal.NPrf
      (syn_wb (.classMem (.cv x) (syn_cun (.cv b) (.cv c)))
        (syn_wo (.objMem x b) (.objMem x c))) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [syn_wb, syn_cun, syn_cnin, syn_wnan, syn_wa, syn_ccompl, syn_wo]
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
            · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
            · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0143
  have p0144 :=
    @g_n_3bitr4i (syn_wo syntaxFormula0074 syntaxFormula0075)
      (syn_wo (.objMem x b) (.objMem x c)) syntaxFormula0076
      (.classMem (.cv x) (syn_cun (.cv b) (.cv c))) p0141 p0142 p0144_e02_recanon
  have p0145 :=
    @g_bibi12i syntaxFormula0072 (.objMem x a) syntaxFormula0076
      (.classMem (.cv x) (syn_cun (.cv b) (.cv c))) p0118 p0144
  have p0146 :=
    @g_notbii syntaxFormula0077
      (syn_wb (.objMem x a) (.classMem (.cv x) (syn_cun (.cv b) (.cv c)))) p0145
  have p0147 :=
    @g_n_3bitri syntaxFormula0068 syntaxFormula0071 (.neg syntaxFormula0077)
      (.neg (syn_wb (.objMem x a) (.classMem (.cv x) (syn_cun (.cv b) (.cv c))))) p0106
      p0107 p0146
  have p0148 :=
    @g_exbii syntaxFormula0068
      (.neg (syn_wb (.objMem x a) (.classMem (.cv x) (syn_cun (.cv b) (.cv c))))) x p0147
  have p0149 :=
    @g_n_3bitri syntaxFormula0078 syntaxFormula0067 syntaxFormula0069
      (syn_wex x (.neg (syn_wb (.objMem x a) (.classMem (.cv x) (syn_cun (.cv b) (.cv c))))))
      p0094 p0102 p0148
  have p0150 :=
    @g_notbii syntaxFormula0078
      (syn_wex x (.neg (syn_wb (.objMem x a) (.classMem (.cv x) (syn_cun (.cv b) (.cv c))))))
      p0149
  have p0151 := @g_elcompl syntaxClass0052 syntaxClass0011 p0093
  have freshnessCertificate0387 : x ∉ (((Class.cv b)).fv) ∪ (((Class.cv c)).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0336 freshnessCertificate0342))
  have freshnessCertificate0388 : x ∉ ((syn_cun (.cv b) (.cv c))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun];
      exact freshnessCertificate0387)
  have p0152 :=
    @g_dfcleq x (.cv a) (syn_cun (.cv b) (.cv c)) (by exact freshnessCertificate0346)
      (by exact freshnessCertificate0388)
  have p0153 :=
    @g_alex (syn_wb (.objMem x a) (.classMem (.cv x) (syn_cun (.cv b) (.cv c)))) x
  have p0154_e00_recanon :
    Nominal.NPrf
      (syn_wb (.classEq (.cv a) (syn_cun (.cv b) (.cv c)))
        (.all x (syn_wb (.objMem x a) (.classMem (.cv x) (syn_cun (.cv b) (.cv c)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [syn_wb, syn_cun, syn_cnin, syn_wnan, syn_wa, syn_ccompl]
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
              · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
              · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0152
  have p0154 :=
    @g_bitri (.classEq (.cv a) (syn_cun (.cv b) (.cv c)))
      (.all x (syn_wb (.objMem x a) (.classMem (.cv x) (syn_cun (.cv b) (.cv c)))))
      (.neg (syn_wex x
          (.neg (syn_wb (.objMem x a) (.classMem (.cv x) (syn_cun (.cv b) (.cv c)))))))
      p0154_e00_recanon p0153
  have p0155 :=
    @g_n_3bitr4i (.neg syntaxFormula0078)
      (.neg (syn_wex x
          (.neg (syn_wb (.objMem x a) (.classMem (.cv x) (syn_cun (.cv b) (.cv c)))))))
      syntaxFormula0079 (.classEq (.cv a) (syn_cun (.cv b) (.cv c))) p0150 p0151 p0154
  have p0156 :=
    @g_anbi12i syntaxFormula0058 (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0))
      syntaxFormula0079 (.classEq (.cv a) (syn_cun (.cv b) (.cv c))) p0092 p0155
  have p0157 :=
    @g_bitri syntaxFormula0080 (syn_wa syntaxFormula0058 syntaxFormula0079)
      syntaxFormula0040 p0077 p0156
  have p0158 :=
    @g_anbi12i syntaxFormula0056 (syn_wa (.objMem b n) (.objMem c n)) syntaxFormula0080
      syntaxFormula0040 p0076 p0157
  have p0159 :=
    @g_n_3bitri syntaxFormula0050 syntaxFormula0053
      (syn_wa syntaxFormula0056 syntaxFormula0080)
      (syn_wa (syn_wa (.objMem b n) (.objMem c n)) syntaxFormula0040) p0058 p0059 p0158
  have p0160 :=
    @g_exbii syntaxFormula0050
      (syn_wa (syn_wa (.objMem b n) (.objMem c n)) syntaxFormula0040) b p0159
  have p0161 :=
    @g_n_3bitri syntaxFormula0037 syntaxFormula0042 syntaxFormula0051
      (syn_wex b (syn_wa (syn_wa (.objMem b n) (.objMem c n)) syntaxFormula0040)) p0043
      p0054 p0160
  have p0162 :=
    @g_exbii syntaxFormula0037
      (syn_wex b (syn_wa (syn_wa (.objMem b n) (.objMem c n)) syntaxFormula0040)) c p0161
  have p0163 :=
    @g_bitr4i
      (syn_wex b (syn_wex c (syn_wa (syn_wa (.objMem b n) (.objMem c n)) syntaxFormula0040)))
      (syn_wex c (syn_wex b (syn_wa (syn_wa (.objMem b n) (.objMem c n)) syntaxFormula0040)))
      syntaxFormula0038 p0039 p0162
  have p0164_e01_recanon :
    Nominal.NPrf
      (syn_wb (syn_wrex b (.cv n) (syn_wrex c (.cv n) syntaxFormula0040)) (syn_wex b
          (syn_wex c (syn_wa (syn_wa (.objMem b n) (.objMem c n)) syntaxFormula0040)))) :=
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
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
              · apply Nominal.RecanonTransportDev.TRecanonWff.neg
                exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
              · apply Nominal.RecanonTransportDev.TRecanonWff.neg
                exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0038
  have p0164 :=
    @g_n_3bitri (.classMem (.cv a) (syn_cplc (.cv n) (.cv n)))
      (syn_wrex b (.cv n) (syn_wrex c (.cv n) syntaxFormula0040))
      (syn_wex b (syn_wex c (syn_wa (syn_wa (.objMem b n) (.objMem c n)) syntaxFormula0040)))
      syntaxFormula0038 p0037 p0164_e01_recanon p0163
  have p0165 :=
    @g_n_3bitr4i syntaxFormula0039 syntaxFormula0038 syntaxFormula0081
      (.classMem (.cv a) (syn_cplc (.cv n) (.cv n))) p0035 p0036 p0164
  have p0166 :=
    @g_bibi12i syntaxFormula0030 (.objMem a x) syntaxFormula0081
      (.classMem (.cv a) (syn_cplc (.cv n) (.cv n))) p0024 p0165
  have p0167 :=
    @g_notbii syntaxFormula0082
      (syn_wb (.objMem a x) (.classMem (.cv a) (syn_cplc (.cv n) (.cv n)))) p0166
  have p0168 :=
    @g_n_3bitri syntaxFormula0027 syntaxFormula0029 (.neg syntaxFormula0082)
      (.neg (syn_wb (.objMem a x) (.classMem (.cv a) (syn_cplc (.cv n) (.cv n))))) p0017
      p0018 p0167
  have p0169 :=
    @g_exbii syntaxFormula0027
      (.neg (syn_wb (.objMem a x) (.classMem (.cv a) (syn_cplc (.cv n) (.cv n))))) a p0168
  have p0170 :=
    @g_n_3bitri syntaxFormula0083 syntaxFormula0026 syntaxFormula0028
      (syn_wex a (.neg (syn_wb (.objMem a x) (.classMem (.cv a) (syn_cplc (.cv n) (.cv n))))))
      p0005 p0013 p0169
  have p0171 :=
    @g_notbii syntaxFormula0083
      (syn_wex a (.neg (syn_wb (.objMem a x) (.classMem (.cv a) (syn_cplc (.cv n) (.cv n))))))
      p0170
  have p0172 := @g_elcompl (syn_copk (.cv n) (.cv x)) syntaxClass0019 p0004
  have freshnessCertificate0389 : a ∉ (((Class.cv n)).fv) ∪ (((Class.cv n)).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0120 freshnessCertificate0120))
  have freshnessCertificate0390 : a ∉ ((syn_cplc (.cv n) (.cv n))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc];
      exact freshnessCertificate0389)
  have p0173 :=
    @g_dfcleq a (.cv x) (syn_cplc (.cv n) (.cv n)) (by exact freshnessCertificate0121)
      (by exact freshnessCertificate0390)
  have p0174 :=
    @g_alex (syn_wb (.objMem a x) (.classMem (.cv a) (syn_cplc (.cv n) (.cv n)))) a
  have p0175_e00_recanon :
    Nominal.NPrf
      (syn_wb (.classEq (.cv x) (syn_cplc (.cv n) (.cv n)))
        (.all a (syn_wb (.objMem a x) (.classMem (.cv a) (syn_cplc (.cv n) (.cv n)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [syn_wb, syn_cplc, syn_wrex, syn_wex, syn_wa]
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
              · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
              · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0173
  have p0175 :=
    @g_bitri (.classEq (.cv x) (syn_cplc (.cv n) (.cv n)))
      (.all a (syn_wb (.objMem a x) (.classMem (.cv a) (syn_cplc (.cv n) (.cv n)))))
      (.neg (syn_wex a
          (.neg (syn_wb (.objMem a x) (.classMem (.cv a) (syn_cplc (.cv n) (.cv n)))))))
      p0175_e00_recanon p0174
  have p0176 :=
    @g_n_3bitr4i (.neg syntaxFormula0083)
      (.neg (syn_wex a
          (.neg (syn_wb (.objMem a x) (.classMem (.cv a) (syn_cplc (.cv n) (.cv n)))))))
      syntaxFormula0084 (.classEq (.cv x) (syn_cplc (.cv n) (.cv n))) p0171 p0172 p0175
  have p0177 :=
    @g_rexbii syntaxFormula0084 (.classEq (.cv x) (syn_cplc (.cv n) (.cv n))) n (syn_cnnc)
      p0176
  have p0178 :=
    @g_bitri syntaxFormula0085 (syn_wrex n (syn_cnnc) syntaxFormula0084)
      (syn_wrex n (syn_cnnc) (.classEq (.cv x) (syn_cplc (.cv n) (.cv n)))) p0003 p0177
  have p0179 :=
    @g_anbi1i syntaxFormula0085
      (syn_wrex n (syn_cnnc) (.classEq (.cv x) (syn_cplc (.cv n) (.cv n))))
      (syn_wne (.cv x) (syn_c0)) p0178
  have p0180 :=
    @g_bitri (.classMem (.cv x) syntaxClass0086)
      (syn_wa syntaxFormula0085 (syn_wne (.cv x) (syn_c0))) syntaxFormula0087 p0001 p0179
  have freshnessCertificate0391 : x ∉ ((syn_cins2k (syn_cssetk))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0357)
  have freshnessCertificate0392 : x ∉ ((syn_cins2k (syn_cins2k (syn_cssetk)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0391)
  have freshnessCertificate0393 : x ∉ ((syn_cvv)).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv];
      exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))
  have freshnessCertificate0394 :
    x ∉ (((syn_cvv)).fv) ∪ (((syn_cins2k (syn_cssetk))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0393 freshnessCertificate0391))
  have freshnessCertificate0395 :
    x ∉ ((syn_cxpk (syn_cvv) (syn_cins2k (syn_cssetk)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk];
      exact freshnessCertificate0394)
  have freshnessCertificate0396 :
    x ∉
      (((syn_cins2k (syn_cins2k (syn_cssetk)))).fv) ∪
        (((syn_cxpk (syn_cvv) (syn_cins2k (syn_cssetk)))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0392 freshnessCertificate0395))
  have freshnessCertificate0397 : x ∉ (syntaxClass0000).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin];
      exact freshnessCertificate0396)
  have freshnessCertificate0398 : x ∉ ((syn_cins3k (syn_cssetk))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0357)
  have freshnessCertificate0399 :
    x ∉ (((syn_cins3k (syn_cssetk))).fv) ∪ (((syn_cins2k (syn_cssetk))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0398 freshnessCertificate0391))
  have freshnessCertificate0400 :
    x ∉ ((syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin];
      exact freshnessCertificate0399)
  have freshnessCertificate0401 : x ∉ ((syn_c1c)).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c];
      exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))
  have freshnessCertificate0402 : x ∉ ((syn_cpw1 (syn_c1c))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0401)
  have freshnessCertificate0403 : x ∉ ((syn_cpw1 (syn_cpw1 (syn_c1c)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0402)
  have freshnessCertificate0404 :
    x ∉
      (((syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))).fv) ∪
        (((syn_cpw1 (syn_cpw1 (syn_c1c)))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0400 freshnessCertificate0403))
  have freshnessCertificate0405 : x ∉ (syntaxClass0001).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak];
      exact freshnessCertificate0404)
  have freshnessCertificate0406 : x ∉ (syntaxClass0002).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl];
      exact freshnessCertificate0405)
  have freshnessCertificate0407 : x ∉ (syntaxClass0003).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0406)
  have freshnessCertificate0408 : x ∉ (syntaxClass0004).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0407)
  have freshnessCertificate0409 : x ∉ (syntaxClass0005).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0408)
  have freshnessCertificate0410 : x ∉ (syntaxClass0006).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0409)
  have freshnessCertificate0411 : x ∉ ((syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0403)
  have freshnessCertificate0412 :
    x ∉ ((syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0411)
  have freshnessCertificate0413 :
    x ∉ ((syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0412)
  have freshnessCertificate0414 :
    x ∉
      ((syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0413)
  have freshnessCertificate0415 : x ∉ (syntaxClass0010).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0414)
  have freshnessCertificate0416 : x ∉ ((syntaxClass0009).fv) ∪ ((syntaxClass0010).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0372 freshnessCertificate0415))
  have freshnessCertificate0417 : x ∉ (syntaxClass0011).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak];
      exact freshnessCertificate0416)
  have freshnessCertificate0418 : x ∉ (syntaxClass0012).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl];
      exact freshnessCertificate0417)
  have freshnessCertificate0419 : x ∉ ((syntaxClass0006).fv) ∪ ((syntaxClass0012).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0410 freshnessCertificate0418))
  have freshnessCertificate0420 : x ∉ (syntaxClass0013).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin];
      exact freshnessCertificate0419)
  have freshnessCertificate0421 : x ∉ ((syntaxClass0000).fv) ∪ ((syntaxClass0013).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0397 freshnessCertificate0420))
  have freshnessCertificate0422 : x ∉ (syntaxClass0014).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin];
      exact freshnessCertificate0421)
  have freshnessCertificate0423 :
    x ∉
      ((syntaxClass0014).fv) ∪
        (((syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0422 freshnessCertificate0412))
  have freshnessCertificate0424 : x ∉ (syntaxClass0015).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak];
      exact freshnessCertificate0423)
  have freshnessCertificate0425 :
    x ∉ ((syntaxClass0015).fv) ∪ (((syn_cpw1 (syn_cpw1 (syn_c1c)))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0424 freshnessCertificate0403))
  have freshnessCertificate0426 : x ∉ (syntaxClass0016).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak];
      exact freshnessCertificate0425)
  have freshnessCertificate0427 : x ∉ (syntaxClass0017).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0426)
  have freshnessCertificate0428 :
    x ∉ (((syn_cins2k (syn_cssetk))).fv) ∪ ((syntaxClass0017).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0391 freshnessCertificate0427))
  have freshnessCertificate0429 : x ∉ (syntaxClass0018).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif];
      exact freshnessCertificate0428)
  have freshnessCertificate0430 :
    x ∉ ((syntaxClass0018).fv) ∪ (((syn_cpw1 (syn_cpw1 (syn_c1c)))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0429 freshnessCertificate0403))
  have freshnessCertificate0431 : x ∉ (syntaxClass0019).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak];
      exact freshnessCertificate0430)
  have freshnessCertificate0432 : x ∉ (syntaxClass0020).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl];
      exact freshnessCertificate0431)
  have freshnessCertificate0433 : x ∉ ((syn_cnnc)).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc];
      exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))
  have freshnessCertificate0434 : x ∉ ((syntaxClass0020).fv) ∪ (((syn_cnnc)).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0432 freshnessCertificate0433))
  have freshnessCertificate0435 : x ∉ (syntaxClass0021).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak];
      exact freshnessCertificate0434)
  have freshnessCertificate0436 : x ∉ ((syn_c0)).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0];
      exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))
  have freshnessCertificate0437 : x ∉ ((syn_csn (syn_c0))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0436)
  have freshnessCertificate0438 :
    x ∉ ((syntaxClass0021).fv) ∪ (((syn_csn (syn_c0))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0435 freshnessCertificate0437))
  have freshnessCertificate0439 : x ∉ (syntaxClass0086).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif];
      exact freshnessCertificate0438)
  have p0181 :=
    @g_eqabi syntaxFormula0087 x syntaxClass0086 (by exact freshnessCertificate0439) p0180
  have p0182 :=
    @g_eqtr4i (syn_cevenfin) (.cab x syntaxFormula0087) syntaxClass0086 p0000 p0181
  have p0183 := @g_ssetkex
  have p0184 := @g_ins2kex (syn_cssetk) p0183
  have p0185 := @g_ins2kex (syn_cins2k (syn_cssetk)) p0184
  have p0186 := @g_vvex
  have p0187 := @g_xpkex (syn_cvv) (syn_cins2k (syn_cssetk)) p0186 p0184
  have p0188 :=
    @g_inex (syn_cins2k (syn_cins2k (syn_cssetk)))
      (syn_cxpk (syn_cvv) (syn_cins2k (syn_cssetk))) p0185 p0187
  have p0190 := @g_ins3kex (syn_cssetk) p0183
  have p0191 := @g_inex (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)) p0190 p0184
  have p0192 := @g_n_1cex
  have p0193 := @g_pw1ex (syn_c1c) p0192
  have p0194 := @g_pw1ex (syn_cpw1 (syn_c1c)) p0193
  have p0195 :=
    @g_imakex (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
      (syn_cpw1 (syn_cpw1 (syn_c1c))) p0191 p0194
  have p0196 := @g_complex syntaxClass0001 p0195
  have p0197 := @g_sikex syntaxClass0002 p0196
  have p0198 := @g_sikex syntaxClass0003 p0197
  have p0199 := @g_sikex syntaxClass0004 p0198
  have p0200 := @g_ins3kex syntaxClass0005 p0199
  have p0202 := @g_sikex (syn_cssetk) p0183
  have p0203 := @g_ins3kex (syn_csik (syn_cssetk)) p0202
  have p0204 := @g_ins2kex (syn_cins3k (syn_csik (syn_cssetk))) p0203
  have p0205 := @g_ins2kex (syn_cins2k (syn_cins3k (syn_csik (syn_cssetk)))) p0204
  have p0206 := @g_sikex (syn_csik (syn_cssetk)) p0202
  have p0207 := @g_sikex (syn_csik (syn_csik (syn_cssetk))) p0206
  have p0208 := @g_sikex (syn_csik (syn_csik (syn_csik (syn_cssetk)))) p0207
  have p0209 := @g_sikex (syn_csik (syn_csik (syn_csik (syn_csik (syn_cssetk))))) p0208
  have p0210 :=
    @g_ins3kex (syn_csik (syn_csik (syn_csik (syn_csik (syn_csik (syn_cssetk)))))) p0209
  have p0211 := @g_ins3kex (syn_csik (syn_csik (syn_csik (syn_cssetk)))) p0207
  have p0212 :=
    @g_ins2kex (syn_cins3k (syn_csik (syn_csik (syn_csik (syn_cssetk))))) p0211
  have p0213 :=
    @g_unex syntaxClass0007
      (syn_cins2k (syn_cins3k (syn_csik (syn_csik (syn_csik (syn_cssetk)))))) p0210 p0212
  have p0214 :=
    @g_symdifex (syn_cins2k (syn_cins2k (syn_cins3k (syn_csik (syn_cssetk)))))
      syntaxClass0008 p0205 p0213
  have p0215 := @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_c1c))) p0194
  have p0216 := @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))) p0215
  have p0217 := @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))) p0216
  have p0218 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))) p0217
  have p0219 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
      p0218
  have p0220 := @g_imakex syntaxClass0009 syntaxClass0010 p0214 p0219
  have p0221 := @g_complex syntaxClass0011 p0220
  have p0222 := @g_inex syntaxClass0006 syntaxClass0012 p0200 p0221
  have p0223 := @g_inex syntaxClass0000 syntaxClass0013 p0188 p0222
  have p0224 :=
    @g_imakex syntaxClass0014 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))) p0223
      p0216
  have p0225 := @g_imakex syntaxClass0015 (syn_cpw1 (syn_cpw1 (syn_c1c))) p0224 p0194
  have p0226 := @g_ins3kex syntaxClass0016 p0225
  have p0227 := @g_symdifex (syn_cins2k (syn_cssetk)) syntaxClass0017 p0184 p0226
  have p0228 := @g_imakex syntaxClass0018 (syn_cpw1 (syn_cpw1 (syn_c1c))) p0227 p0194
  have p0229 := @g_complex syntaxClass0019 p0228
  have p0230 := @g_nncex
  have p0231 := @g_imakex syntaxClass0020 (syn_cnnc) p0229 p0230
  have p0232 := @g_snex (syn_c0)
  have p0233 := @g_difex syntaxClass0021 (syn_csn (syn_c0)) p0231 p0232
  have p0234 := @g_eqeltri (syn_cevenfin) syntaxClass0086 (syn_cvv) p0182 p0233
  exact p0234


end NFChoice.DirectNominalPrf.WPPReplay
