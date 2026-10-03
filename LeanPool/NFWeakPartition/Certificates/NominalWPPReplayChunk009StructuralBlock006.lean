/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NominalWPPReplayChunk009StructuralBlock005

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NominalWPPReplayChunk009StructuralPart032`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_nnsucelrlem1 (x : Var) (m : Var) (a : Var) (dv_a_m : a ≠ m)
    (dv_a_x : a ≠ x) (dv_m_x : m ≠ x) :
    Nominal.NPrf
      (.classMem (.cab m (.all a (.all x (.imp (syn_wa (.neg (.objMem x a))
                  (.classMem (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cplc (.cv m) (syn_c1c))))
                (.objMem a m))))) (syn_cvv)) :=
  by
  let proofSupport : Finset Var :=
    ({ x } : Finset Var) ∪ ({ m } : Finset Var) ∪ ({ a } : Finset Var)
  let t : Var := freshVar proofSupport 0
  let w : Var := freshVar proofSupport 1
  let e : Var := freshVar proofSupport 2
  have fresh_t : t ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_t_ne_x : t ≠ x := by
    intro h
    exact
      fresh_t
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_x_ne_t : x ≠ t := Ne.symm fresh_t_ne_x
  have fresh_t_ne_m : t ≠ m := by
    intro h
    exact
      fresh_t
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_t_ne_a : t ≠ a := by
    intro h
    exact fresh_t (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_a_ne_t : a ≠ t := Ne.symm fresh_t_ne_a
  have fresh_w : w ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_w_ne_x : w ≠ x := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_w_ne_m : w ≠ m := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_w_ne_a : w ≠ a := by
    intro h
    exact fresh_w (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_e : e ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_e_ne_x : e ≠ x := by
    intro h
    exact
      fresh_e
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_e_ne_m : e ≠ m := by
    intro h
    exact
      fresh_e
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_e_ne_a : e ≠ a := by
    intro h
    exact fresh_e (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_t_ne_w : t ≠ w :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_w_ne_t : w ≠ t := Ne.symm fresh_t_ne_w
  have fresh_t_ne_e : t ≠ e :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_e_ne_t : e ≠ t := Ne.symm fresh_t_ne_e
  have fresh_w_ne_e : w ≠ e :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_e_ne_w : e ≠ w := Ne.symm fresh_w_ne_e
  let syntaxClass0000 : Class :=
    (syn_cins3k (syn_csik (syn_csik (syn_csik (syn_csik (syn_csik (syn_cssetk)))))))
  let syntaxClass0001 : Class :=
    (syn_cun (syn_cins2k (syn_cins3k (syn_csik (syn_cssetk)))) (syn_cins3k (syn_cidk)))
  let syntaxClass0002 : Class := (syn_cins2k syntaxClass0001)
  let syntaxClass0003 : Class := (syn_csymdif syntaxClass0000 syntaxClass0002)
  let syntaxClass0004 : Class :=
    (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
  let syntaxClass0005 : Class := (syn_cimak syntaxClass0003 syntaxClass0004)
  let syntaxClass0006 : Class := (syn_ccompl syntaxClass0005)
  let syntaxClass0007 : Class :=
    (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
      (syn_cpw1 (syn_cpw1 (syn_c1c))))
  let syntaxClass0008 : Class := (syn_ccompl syntaxClass0007)
  let syntaxClass0009 : Class := (syn_cins3k syntaxClass0008)
  let syntaxClass0010 : Class :=
    (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
      (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))
  let syntaxClass0011 : Class :=
    (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) syntaxClass0010)
  let syntaxClass0012 : Class :=
    (syn_cimak syntaxClass0011 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))
  let syntaxClass0013 : Class := (syn_cdif syntaxClass0009 syntaxClass0012)
  let syntaxClass0014 : Class :=
    (syn_cimak syntaxClass0013 (syn_cpw1 (syn_cpw1 (syn_c1c))))
  let syntaxClass0015 : Class := (syn_cimagek syntaxClass0014)
  let syntaxClass0016 : Class := (syn_ccnvk syntaxClass0015)
  let syntaxClass0017 : Class := (syn_ccomk syntaxClass0016 (syn_cssetk))
  let syntaxClass0018 : Class := (syn_cins2k syntaxClass0017)
  let syntaxClass0019 : Class := (syn_cins2k syntaxClass0018)
  let syntaxClass0020 : Class := (syn_cin syntaxClass0006 syntaxClass0019)
  let syntaxClass0021 : Class :=
    (syn_cimak syntaxClass0020 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))
  let syntaxClass0022 : Class :=
    (syn_cdif syntaxClass0021 (syn_cins3k (syn_csik (syn_cssetk))))
  let syntaxClass0023 : Class :=
    (syn_cdif syntaxClass0022 (syn_cxpk (syn_cvv) (syn_cssetk)))
  let syntaxClass0024 : Class :=
    (syn_cimak syntaxClass0023 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))
  let syntaxFormula0025 : Wff := (.classMem (syn_copk (.cv t) (.cv m)) syntaxClass0024)
  let syntaxFormula0026 : Wff := (syn_wrex t (syn_c1c) syntaxFormula0025)
  let syntaxFormula0027 : Wff := (syn_wa (.classMem (.cv t) (syn_c1c)) syntaxFormula0025)
  let syntaxFormula0028 : Wff :=
    (syn_wa (.classEq (.cv t) (syn_csn (.cv a))) syntaxFormula0025)
  let syntaxFormula0029 : Wff := (syn_wex a syntaxFormula0028)
  let syntaxFormula0030 : Wff := (syn_wex t syntaxFormula0027)
  let syntaxFormula0031 : Wff := (syn_wex t syntaxFormula0028)
  let syntaxFormula0032 : Wff := (syn_wex a syntaxFormula0031)
  let syntaxClass0033 : Class := (syn_cimak syntaxClass0024 (syn_c1c))
  let syntaxFormula0034 : Wff := (.classMem (.cv m) syntaxClass0033)
  let syntaxFormula0035 : Wff :=
    (.classMem (syn_copk (syn_csn (.cv a)) (.cv m)) syntaxClass0024)
  let syntaxFormula0036 : Wff :=
    (.classMem (syn_copk (.cv t) (syn_copk (syn_csn (.cv a)) (.cv m))) syntaxClass0023)
  let syntaxFormula0037 : Wff :=
    (syn_wrex t (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))) syntaxFormula0036)
  let syntaxFormula0038 : Wff :=
    (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))) syntaxFormula0036)
  let syntaxFormula0039 : Wff :=
    (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))
      syntaxFormula0036)
  let syntaxFormula0040 : Wff := (syn_wex x syntaxFormula0039)
  let syntaxFormula0041 : Wff := (syn_wex t syntaxFormula0038)
  let syntaxFormula0042 : Wff := (syn_wex t syntaxFormula0039)
  let syntaxFormula0043 : Wff := (syn_wex x syntaxFormula0042)
  let syntaxClass0044 : Class :=
    (syn_copk (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))
      (syn_copk (syn_csn (.cv a)) (.cv m)))
  let syntaxFormula0045 : Wff := (.classMem syntaxClass0044 syntaxClass0023)
  let syntaxClass0046 : Class := (syn_copk (.cv t) syntaxClass0044)
  let syntaxFormula0047 : Wff := (.classMem syntaxClass0046 syntaxClass0020)
  let syntaxFormula0048 : Wff :=
    (syn_wrex t (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))) syntaxFormula0047)
  let syntaxFormula0049 : Wff :=
    (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))
      syntaxFormula0047)
  let syntaxFormula0050 : Wff :=
    (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv w)))))))
      syntaxFormula0047)
  let syntaxFormula0051 : Wff := (syn_wex w syntaxFormula0050)
  let syntaxFormula0052 : Wff := (syn_wex t syntaxFormula0049)
  let syntaxFormula0053 : Wff := (syn_wex t syntaxFormula0050)
  let syntaxFormula0054 : Wff := (syn_wex w syntaxFormula0053)
  let syntaxClass0055 : Class :=
    (syn_copk (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv w)))))) syntaxClass0044)
  let syntaxFormula0056 : Wff := (.classMem syntaxClass0055 syntaxClass0020)
  let syntaxClass0057 : Class := (syn_copk (.cv t) syntaxClass0055)
  let syntaxFormula0058 : Wff := (.classMem syntaxClass0057 syntaxClass0003)
  let syntaxFormula0059 : Wff := (syn_wrex t syntaxClass0004 syntaxFormula0058)
  let syntaxFormula0060 : Wff := (.classMem (.cv t) syntaxClass0004)
  let syntaxClass0061 : Class :=
    (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv e)))))))))
  let syntaxFormula0062 : Wff := (.classEq (.cv t) syntaxClass0061)
  let syntaxFormula0063 : Wff := (syn_wa syntaxFormula0060 syntaxFormula0058)
  let syntaxFormula0064 : Wff := (syn_wa syntaxFormula0062 syntaxFormula0058)
  let syntaxFormula0065 : Wff := (syn_wex e syntaxFormula0064)
  let syntaxFormula0066 : Wff := (syn_wex t syntaxFormula0063)
  let syntaxFormula0067 : Wff := (syn_wex t syntaxFormula0064)
  let syntaxFormula0068 : Wff := (syn_wex e syntaxFormula0067)
  let syntaxFormula0069 : Wff := (.classMem syntaxClass0055 syntaxClass0005)
  let syntaxClass0070 : Class := (syn_copk syntaxClass0061 syntaxClass0055)
  let syntaxFormula0071 : Wff := (.classMem syntaxClass0070 syntaxClass0003)
  let syntaxFormula0072 : Wff :=
    (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv e))))))
        (syn_csn (syn_csn (syn_csn (syn_csn (.cv w))))))
      (syn_csik (syn_csik (syn_csik (syn_csik (syn_cssetk))))))
  let syntaxFormula0073 : Wff :=
    (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv e)))))))
        (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv w)))))))
      (syn_csik (syn_csik (syn_csik (syn_csik (syn_csik (syn_cssetk)))))))
  let syntaxFormula0074 : Wff := (.classMem syntaxClass0070 syntaxClass0000)
  let syntaxClass0075 : Class :=
    (syn_copk (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv e)))))))
      syntaxClass0044)
  let syntaxFormula0076 : Wff :=
    (.classMem syntaxClass0075 (syn_cins2k (syn_cins3k (syn_csik (syn_cssetk)))))
  let syntaxFormula0077 : Wff :=
    (.classEq (syn_csn (syn_csn (syn_csn (syn_csn (.cv e)))))
      (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))
  let syntaxClass0078 : Class :=
    (syn_copk (syn_csn (syn_csn (syn_csn (syn_csn (.cv e)))))
      (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))
  let syntaxFormula0079 : Wff := (.classMem syntaxClass0078 (syn_cidk))
  let syntaxFormula0080 : Wff := (.classMem syntaxClass0075 (syn_cins3k (syn_cidk)))
  let syntaxFormula0081 : Wff := (.classMem syntaxClass0075 syntaxClass0001)
  let syntaxFormula0082 : Wff := (.classMem syntaxClass0070 syntaxClass0002)
  let syntaxFormula0083 : Wff := (syn_wb syntaxFormula0074 syntaxFormula0082)
  let syntaxFormula0084 : Wff :=
    (.neg (syn_wb (.objMem e w) (.classMem (.cv e) (syn_cun (.cv a) (syn_csn (.cv x))))))
  let syntaxFormula0085 : Wff := (syn_wex e syntaxFormula0084)
  let syntaxFormula0086 : Wff := (.classMem syntaxClass0055 syntaxClass0006)
  let syntaxFormula0087 : Wff := (.classMem (syn_copk (.cv t) (.cv m)) syntaxClass0016)
  let syntaxFormula0088 : Wff := (.classMem (syn_copk (.cv m) (.cv t)) syntaxClass0015)
  let syntaxClass0089 : Class := (syn_cimak syntaxClass0014 (.cv m))
  let syntaxFormula0090 : Wff := (.classEq (.cv t) syntaxClass0089)
  let syntaxFormula0091 : Wff :=
    (syn_wa (.classMem (syn_copk (syn_csn (.cv w)) (.cv t)) (syn_cssetk)) syntaxFormula0087)
  let syntaxFormula0092 : Wff :=
    (.classMem (syn_copk (syn_csn (.cv w)) (.cv m)) syntaxClass0017)
  let syntaxFormula0093 : Wff :=
    (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv w))))
        (syn_copk (syn_csn (.cv a)) (.cv m))) syntaxClass0018)
  let syntaxFormula0094 : Wff := (.classMem syntaxClass0055 syntaxClass0019)
  let syntaxFormula0095 : Wff :=
    (syn_wa (.classEq (.cv w) (syn_cun (.cv a) (syn_csn (.cv x))))
      (.classMem (.cv w) (syn_cplc (.cv m) (syn_c1c))))
  let syntaxFormula0096 : Wff := (syn_wex w syntaxFormula0095)
  let syntaxFormula0097 : Wff := (.classMem syntaxClass0044 syntaxClass0021)
  let syntaxFormula0098 : Wff :=
    (.classMem syntaxClass0044 (syn_cins3k (syn_csik (syn_cssetk))))
  let syntaxFormula0099 : Wff := (.classMem syntaxClass0044 syntaxClass0022)
  let syntaxFormula0100 : Wff :=
    (syn_wa (.neg (.objMem x a))
      (.classMem (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cplc (.cv m) (syn_c1c))))
  let syntaxFormula0101 : Wff :=
    (.classMem syntaxClass0044 (syn_cxpk (syn_cvv) (syn_cssetk)))
  let syntaxFormula0102 : Wff := (.imp syntaxFormula0100 (.objMem a m))
  let syntaxFormula0103 : Wff := (.neg syntaxFormula0102)
  let syntaxFormula0104 : Wff := (.all x syntaxFormula0102)
  let syntaxFormula0105 : Wff := (.neg syntaxFormula0104)
  let syntaxFormula0106 : Wff := (syn_wex a syntaxFormula0105)
  let syntaxClass0107 : Class := (syn_ccompl syntaxClass0033)
  let syntaxFormula0108 : Wff := (.all a syntaxFormula0104)
  have p0000 := @g_vex m
  have freshnessCertificate0000 : t ∉ ((syn_cssetk)).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk];
      exact (show t ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))
  have freshnessCertificate0001 : t ∉ ((syn_csik (syn_cssetk))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0000)
  have freshnessCertificate0002 : t ∉ ((syn_csik (syn_csik (syn_cssetk)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0001)
  have freshnessCertificate0003 :
    t ∉ ((syn_csik (syn_csik (syn_csik (syn_cssetk))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0002)
  have freshnessCertificate0004 :
    t ∉ ((syn_csik (syn_csik (syn_csik (syn_csik (syn_cssetk)))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0003)
  have freshnessCertificate0005 :
    t ∉ ((syn_csik (syn_csik (syn_csik (syn_csik (syn_csik (syn_cssetk))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0004)
  have freshnessCertificate0006 : t ∉ (syntaxClass0000).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0005)
  have freshnessCertificate0007 : t ∉ ((syn_cins3k (syn_csik (syn_cssetk)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0001)
  have freshnessCertificate0008 :
    t ∉ ((syn_cins2k (syn_cins3k (syn_csik (syn_cssetk))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0007)
  have freshnessCertificate0009 : t ∉ ((syn_cidk)).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cidk];
      exact (show t ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))
  have freshnessCertificate0010 : t ∉ ((syn_cins3k (syn_cidk))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0009)
  have freshnessCertificate0011 :
    t ∉
      (((syn_cins2k (syn_cins3k (syn_csik (syn_cssetk))))).fv) ∪
        (((syn_cins3k (syn_cidk))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0008 freshnessCertificate0010))
  have freshnessCertificate0012 : t ∉ (syntaxClass0001).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun];
      exact freshnessCertificate0011)
  have freshnessCertificate0013 : t ∉ (syntaxClass0002).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0012)
  have freshnessCertificate0014 : t ∉ ((syntaxClass0000).fv) ∪ ((syntaxClass0002).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0006 freshnessCertificate0013))
  have freshnessCertificate0015 : t ∉ (syntaxClass0003).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif];
      exact freshnessCertificate0014)
  have freshnessCertificate0016 : t ∉ ((syn_c1c)).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c];
      exact (show t ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))
  have freshnessCertificate0017 : t ∉ ((syn_cpw1 (syn_c1c))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0016)
  have freshnessCertificate0018 : t ∉ ((syn_cpw1 (syn_cpw1 (syn_c1c)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0017)
  have freshnessCertificate0019 : t ∉ ((syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0018)
  have freshnessCertificate0020 :
    t ∉ ((syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0019)
  have freshnessCertificate0021 :
    t ∉ ((syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0020)
  have freshnessCertificate0022 :
    t ∉
      ((syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0021)
  have freshnessCertificate0023 : t ∉ (syntaxClass0004).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0022)
  have freshnessCertificate0024 : t ∉ ((syntaxClass0003).fv) ∪ ((syntaxClass0004).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0015 freshnessCertificate0023))
  have freshnessCertificate0025 : t ∉ (syntaxClass0005).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak];
      exact freshnessCertificate0024)
  have freshnessCertificate0026 : t ∉ (syntaxClass0006).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl];
      exact freshnessCertificate0025)
  have freshnessCertificate0027 : t ∉ ((syn_cins3k (syn_cssetk))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0000)
  have freshnessCertificate0028 : t ∉ ((syn_cins2k (syn_cssetk))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0000)
  have freshnessCertificate0029 :
    t ∉ (((syn_cins3k (syn_cssetk))).fv) ∪ (((syn_cins2k (syn_cssetk))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0027 freshnessCertificate0028))
  have freshnessCertificate0030 :
    t ∉ ((syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin];
      exact freshnessCertificate0029)
  have freshnessCertificate0031 :
    t ∉
      (((syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))).fv) ∪
        (((syn_cpw1 (syn_cpw1 (syn_c1c)))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0030 freshnessCertificate0018))
  have freshnessCertificate0032 : t ∉ (syntaxClass0007).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak];
      exact freshnessCertificate0031)
  have freshnessCertificate0033 : t ∉ (syntaxClass0008).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl];
      exact freshnessCertificate0032)
  have freshnessCertificate0034 : t ∉ (syntaxClass0009).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0033)
  have freshnessCertificate0035 : t ∉ ((syn_cins2k (syn_cins2k (syn_cssetk)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0028)
  have freshnessCertificate0036 : t ∉ ((syn_cins2k (syn_cins3k (syn_cssetk)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0027)
  have freshnessCertificate0037 :
    t ∉ ((syn_cins3k (syn_csik (syn_csik (syn_cssetk))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0002)
  have freshnessCertificate0038 :
    t ∉
      (((syn_cins2k (syn_cins3k (syn_cssetk)))).fv) ∪
        (((syn_cins3k (syn_csik (syn_csik (syn_cssetk))))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0036 freshnessCertificate0037))
  have freshnessCertificate0039 : t ∉ (syntaxClass0010).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun];
      exact freshnessCertificate0038)
  have freshnessCertificate0040 :
    t ∉ (((syn_cins2k (syn_cins2k (syn_cssetk)))).fv) ∪ ((syntaxClass0010).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0035 freshnessCertificate0039))
  have freshnessCertificate0041 : t ∉ (syntaxClass0011).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif];
      exact freshnessCertificate0040)
  have freshnessCertificate0042 :
    t ∉
      ((syntaxClass0011).fv) ∪
        (((syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0041 freshnessCertificate0020))
  have freshnessCertificate0043 : t ∉ (syntaxClass0012).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak];
      exact freshnessCertificate0042)
  have freshnessCertificate0044 : t ∉ ((syntaxClass0009).fv) ∪ ((syntaxClass0012).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0034 freshnessCertificate0043))
  have freshnessCertificate0045 : t ∉ (syntaxClass0013).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif];
      exact freshnessCertificate0044)
  have freshnessCertificate0046 :
    t ∉ ((syntaxClass0013).fv) ∪ (((syn_cpw1 (syn_cpw1 (syn_c1c)))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0045 freshnessCertificate0018))
  have freshnessCertificate0047 : t ∉ (syntaxClass0014).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak];
      exact freshnessCertificate0046)
  have freshnessCertificate0048 : t ∉ (syntaxClass0015).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimagek];
      exact freshnessCertificate0047)
  have freshnessCertificate0049 : t ∉ (syntaxClass0016).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk];
      exact freshnessCertificate0048)
  have freshnessCertificate0050 : t ∉ ((syntaxClass0016).fv) ∪ (((syn_cssetk)).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0049 freshnessCertificate0000))
  have freshnessCertificate0051 : t ∉ (syntaxClass0017).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccomk];
      exact freshnessCertificate0050)
  have freshnessCertificate0052 : t ∉ (syntaxClass0018).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0051)
  have freshnessCertificate0053 : t ∉ (syntaxClass0019).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0052)
  have freshnessCertificate0054 : t ∉ ((syntaxClass0006).fv) ∪ ((syntaxClass0019).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0026 freshnessCertificate0053))
  have freshnessCertificate0055 : t ∉ (syntaxClass0020).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin];
      exact freshnessCertificate0054)
  have freshnessCertificate0056 :
    t ∉
      ((syntaxClass0020).fv) ∪
        (((syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0055 freshnessCertificate0020))
  have freshnessCertificate0057 : t ∉ (syntaxClass0021).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak];
      exact freshnessCertificate0056)
  have freshnessCertificate0058 :
    t ∉ ((syntaxClass0021).fv) ∪ (((syn_cins3k (syn_csik (syn_cssetk)))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0057 freshnessCertificate0007))
  have freshnessCertificate0059 : t ∉ (syntaxClass0022).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif];
      exact freshnessCertificate0058)
  have freshnessCertificate0060 : t ∉ ((syn_cvv)).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv];
      exact (show t ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))
  have freshnessCertificate0061 : t ∉ (((syn_cvv)).fv) ∪ (((syn_cssetk)).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0060 freshnessCertificate0000))
  have freshnessCertificate0062 : t ∉ ((syn_cxpk (syn_cvv) (syn_cssetk))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk];
      exact freshnessCertificate0061)
  have freshnessCertificate0063 :
    t ∉ ((syntaxClass0022).fv) ∪ (((syn_cxpk (syn_cvv) (syn_cssetk))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0059 freshnessCertificate0062))
  have freshnessCertificate0064 : t ∉ (syntaxClass0023).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif];
      exact freshnessCertificate0063)
  have freshnessCertificate0065 :
    t ∉ ((syntaxClass0023).fv) ∪ (((syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0064 freshnessCertificate0019))
  have freshnessCertificate0066 : t ∉ (syntaxClass0024).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak];
      exact freshnessCertificate0065)
  have freshnessCertificate0067 : t ∉ ((Class.cv m)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show t ∉ ({ m } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show t ≠ m from (by exact fresh_t_ne_m)))))
  have p0001 :=
    @g_elimak t syntaxClass0024 (syn_c1c) (.cv m) (by exact freshnessCertificate0066)
      (by exact freshnessCertificate0016) (by exact freshnessCertificate0067) p0000
  have p0002 := (Nominal.biimpRefl syntaxFormula0026)
  have freshnessCertificate0068 : a ∉ ((Class.cv t)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show a ∉ ({ t } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show a ≠ t from (by exact fresh_a_ne_t)))))
  have p0003 := @g_el1c a (.cv t) (by exact freshnessCertificate0068)
  have p0004 :=
    @g_anbi1i (.classMem (.cv t) (syn_c1c))
      (syn_wex a (.classEq (.cv t) (syn_csn (.cv a)))) syntaxFormula0025 p0003
  have freshnessCertificate0069 : a ∉ ((Class.cv m)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show a ∉ ({ m } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using (show a ≠ m from (by exact dv_a_m)))))
  have freshnessCertificate0070 : a ∉ (((Class.cv t)).fv) ∪ (((Class.cv m)).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0068 freshnessCertificate0069))
  have freshnessCertificate0071 : a ∉ ((syn_copk (.cv t) (.cv m))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk];
      exact freshnessCertificate0070)
  have freshnessCertificate0072 : a ∉ ((syn_cssetk)).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk];
      exact (show a ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))
  have freshnessCertificate0073 : a ∉ ((syn_csik (syn_cssetk))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0072)
  have freshnessCertificate0074 : a ∉ ((syn_csik (syn_csik (syn_cssetk)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0073)
  have freshnessCertificate0075 :
    a ∉ ((syn_csik (syn_csik (syn_csik (syn_cssetk))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0074)
  have freshnessCertificate0076 :
    a ∉ ((syn_csik (syn_csik (syn_csik (syn_csik (syn_cssetk)))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0075)
  have freshnessCertificate0077 :
    a ∉ ((syn_csik (syn_csik (syn_csik (syn_csik (syn_csik (syn_cssetk))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0076)
  have freshnessCertificate0078 : a ∉ (syntaxClass0000).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0077)
  have freshnessCertificate0079 : a ∉ ((syn_cins3k (syn_csik (syn_cssetk)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0073)
  have freshnessCertificate0080 :
    a ∉ ((syn_cins2k (syn_cins3k (syn_csik (syn_cssetk))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0079)
  have freshnessCertificate0081 : a ∉ ((syn_cidk)).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cidk];
      exact (show a ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))
  have freshnessCertificate0082 : a ∉ ((syn_cins3k (syn_cidk))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0081)
  have freshnessCertificate0083 :
    a ∉
      (((syn_cins2k (syn_cins3k (syn_csik (syn_cssetk))))).fv) ∪
        (((syn_cins3k (syn_cidk))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0080 freshnessCertificate0082))
  have freshnessCertificate0084 : a ∉ (syntaxClass0001).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun];
      exact freshnessCertificate0083)
  have freshnessCertificate0085 : a ∉ (syntaxClass0002).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0084)
  have freshnessCertificate0086 : a ∉ ((syntaxClass0000).fv) ∪ ((syntaxClass0002).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0078 freshnessCertificate0085))
  have freshnessCertificate0087 : a ∉ (syntaxClass0003).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif];
      exact freshnessCertificate0086)
  have freshnessCertificate0088 : a ∉ ((syn_c1c)).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c];
      exact (show a ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))
  have freshnessCertificate0089 : a ∉ ((syn_cpw1 (syn_c1c))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0088)
  have freshnessCertificate0090 : a ∉ ((syn_cpw1 (syn_cpw1 (syn_c1c)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0089)
  have freshnessCertificate0091 : a ∉ ((syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0090)
  have freshnessCertificate0092 :
    a ∉ ((syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0091)
  have freshnessCertificate0093 :
    a ∉ ((syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0092)
  have freshnessCertificate0094 :
    a ∉
      ((syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0093)
  have freshnessCertificate0095 : a ∉ (syntaxClass0004).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0094)
  have freshnessCertificate0096 : a ∉ ((syntaxClass0003).fv) ∪ ((syntaxClass0004).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0087 freshnessCertificate0095))
  have freshnessCertificate0097 : a ∉ (syntaxClass0005).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak];
      exact freshnessCertificate0096)
  have freshnessCertificate0098 : a ∉ (syntaxClass0006).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl];
      exact freshnessCertificate0097)
  have freshnessCertificate0099 : a ∉ ((syn_cins3k (syn_cssetk))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0072)
  have freshnessCertificate0100 : a ∉ ((syn_cins2k (syn_cssetk))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0072)
  have freshnessCertificate0101 :
    a ∉ (((syn_cins3k (syn_cssetk))).fv) ∪ (((syn_cins2k (syn_cssetk))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0099 freshnessCertificate0100))
  have freshnessCertificate0102 :
    a ∉ ((syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin];
      exact freshnessCertificate0101)
  have freshnessCertificate0103 :
    a ∉
      (((syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))).fv) ∪
        (((syn_cpw1 (syn_cpw1 (syn_c1c)))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0102 freshnessCertificate0090))
  have freshnessCertificate0104 : a ∉ (syntaxClass0007).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak];
      exact freshnessCertificate0103)
  have freshnessCertificate0105 : a ∉ (syntaxClass0008).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl];
      exact freshnessCertificate0104)
  have freshnessCertificate0106 : a ∉ (syntaxClass0009).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0105)
  have freshnessCertificate0107 : a ∉ ((syn_cins2k (syn_cins2k (syn_cssetk)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0100)
  have freshnessCertificate0108 : a ∉ ((syn_cins2k (syn_cins3k (syn_cssetk)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0099)
  have freshnessCertificate0109 :
    a ∉ ((syn_cins3k (syn_csik (syn_csik (syn_cssetk))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0074)
  have freshnessCertificate0110 :
    a ∉
      (((syn_cins2k (syn_cins3k (syn_cssetk)))).fv) ∪
        (((syn_cins3k (syn_csik (syn_csik (syn_cssetk))))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0108 freshnessCertificate0109))
  have freshnessCertificate0111 : a ∉ (syntaxClass0010).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun];
      exact freshnessCertificate0110)
  have freshnessCertificate0112 :
    a ∉ (((syn_cins2k (syn_cins2k (syn_cssetk)))).fv) ∪ ((syntaxClass0010).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0107 freshnessCertificate0111))
  have freshnessCertificate0113 : a ∉ (syntaxClass0011).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif];
      exact freshnessCertificate0112)
  have freshnessCertificate0114 :
    a ∉
      ((syntaxClass0011).fv) ∪
        (((syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0113 freshnessCertificate0092))
  have freshnessCertificate0115 : a ∉ (syntaxClass0012).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak];
      exact freshnessCertificate0114)
  have freshnessCertificate0116 : a ∉ ((syntaxClass0009).fv) ∪ ((syntaxClass0012).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0106 freshnessCertificate0115))
  have freshnessCertificate0117 : a ∉ (syntaxClass0013).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif];
      exact freshnessCertificate0116)
  have freshnessCertificate0118 :
    a ∉ ((syntaxClass0013).fv) ∪ (((syn_cpw1 (syn_cpw1 (syn_c1c)))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0117 freshnessCertificate0090))
  have freshnessCertificate0119 : a ∉ (syntaxClass0014).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak];
      exact freshnessCertificate0118)
  have freshnessCertificate0120 : a ∉ (syntaxClass0015).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimagek];
      exact freshnessCertificate0119)
  have freshnessCertificate0121 : a ∉ (syntaxClass0016).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk];
      exact freshnessCertificate0120)
  have freshnessCertificate0122 : a ∉ ((syntaxClass0016).fv) ∪ (((syn_cssetk)).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0121 freshnessCertificate0072))
  have freshnessCertificate0123 : a ∉ (syntaxClass0017).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccomk];
      exact freshnessCertificate0122)
  have freshnessCertificate0124 : a ∉ (syntaxClass0018).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0123)
  have freshnessCertificate0125 : a ∉ (syntaxClass0019).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0124)
  have freshnessCertificate0126 : a ∉ ((syntaxClass0006).fv) ∪ ((syntaxClass0019).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0098 freshnessCertificate0125))
  have freshnessCertificate0127 : a ∉ (syntaxClass0020).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin];
      exact freshnessCertificate0126)
  have freshnessCertificate0128 :
    a ∉
      ((syntaxClass0020).fv) ∪
        (((syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0127 freshnessCertificate0092))
  have freshnessCertificate0129 : a ∉ (syntaxClass0021).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak];
      exact freshnessCertificate0128)
  have freshnessCertificate0130 :
    a ∉ ((syntaxClass0021).fv) ∪ (((syn_cins3k (syn_csik (syn_cssetk)))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0129 freshnessCertificate0079))
  have freshnessCertificate0131 : a ∉ (syntaxClass0022).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif];
      exact freshnessCertificate0130)
  have freshnessCertificate0132 : a ∉ ((syn_cvv)).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv];
      exact (show a ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))
  have freshnessCertificate0133 : a ∉ (((syn_cvv)).fv) ∪ (((syn_cssetk)).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0132 freshnessCertificate0072))
  have freshnessCertificate0134 : a ∉ ((syn_cxpk (syn_cvv) (syn_cssetk))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk];
      exact freshnessCertificate0133)
  have freshnessCertificate0135 :
    a ∉ ((syntaxClass0022).fv) ∪ (((syn_cxpk (syn_cvv) (syn_cssetk))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0131 freshnessCertificate0134))
  have freshnessCertificate0136 : a ∉ (syntaxClass0023).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif];
      exact freshnessCertificate0135)
  have freshnessCertificate0137 :
    a ∉ ((syntaxClass0023).fv) ∪ (((syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0136 freshnessCertificate0091))
  have freshnessCertificate0138 : a ∉ (syntaxClass0024).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak];
      exact freshnessCertificate0137)
  have freshnessCertificate0139 :
    a ∉ (((syn_copk (.cv t) (.cv m))).fv) ∪ ((syntaxClass0024).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0071 freshnessCertificate0138))
  have freshnessCertificate0140 :
    a ∉ ((Wff.classMem (syn_copk (.cv t) (.cv m)) syntaxClass0024)).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact freshnessCertificate0139)
  have p0005 :=
    @g_n_19_41v (.classEq (.cv t) (syn_csn (.cv a))) syntaxFormula0025 a
      (by exact freshnessCertificate0140)
  have p0006 :=
    @g_bitr4i syntaxFormula0027
      (syn_wa (syn_wex a (.classEq (.cv t) (syn_csn (.cv a)))) syntaxFormula0025)
      syntaxFormula0029 p0004 p0005
  have p0007 := @g_exbii syntaxFormula0027 syntaxFormula0029 t p0006
  have p0008 := @g_excom syntaxFormula0028 a t
  have p0009 :=
    @g_bitr4i syntaxFormula0030 (syn_wex t syntaxFormula0029) syntaxFormula0032 p0007
      p0008
  have p0010 := @g_bitri syntaxFormula0026 syntaxFormula0030 syntaxFormula0032 p0002 p0009
  have p0011 := @g_bitri syntaxFormula0034 syntaxFormula0026 syntaxFormula0032 p0001 p0010
  have p0012 := @g_snex (.cv a)
  have p0013 := @g_opkeq1 (.cv t) (syn_csn (.cv a)) (.cv m)
  have p0014 :=
    @g_eleq1d (.classEq (.cv t) (syn_csn (.cv a))) (syn_copk (.cv t) (.cv m))
      (syn_copk (syn_csn (.cv a)) (.cv m)) syntaxClass0024 p0013
  have freshnessCertificate0141 : t ∉ ((Class.cv a)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show t ∉ ({ a } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show t ≠ a from (by exact fresh_t_ne_a)))))
  have freshnessCertificate0142 : t ∉ ((syn_csn (.cv a))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0141)
  have freshnessCertificate0143 : t ∉ (((syn_csn (.cv a))).fv) ∪ (((Class.cv m)).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0142 freshnessCertificate0067))
  have freshnessCertificate0144 : t ∉ ((syn_copk (syn_csn (.cv a)) (.cv m))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk];
      exact freshnessCertificate0143)
  have freshnessCertificate0145 :
    t ∉ (((syn_copk (syn_csn (.cv a)) (.cv m))).fv) ∪ ((syntaxClass0024).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0144 freshnessCertificate0066))
  have freshnessCertificate0146 :
    t ∉ ((Wff.classMem (syn_copk (syn_csn (.cv a)) (.cv m)) syntaxClass0024)).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact freshnessCertificate0145)
  have p0015 :=
    @g_ceqsexv syntaxFormula0025 syntaxFormula0035 t (syn_csn (.cv a))
      (by exact freshnessCertificate0142) (by exact freshnessCertificate0146) p0012 p0014
  have p0016 := @g_opkex (syn_csn (.cv a)) (.cv m)
  have p0017 :=
    @g_elimak t syntaxClass0023 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))
      (syn_copk (syn_csn (.cv a)) (.cv m)) (by exact freshnessCertificate0064)
      (by exact freshnessCertificate0019) (by exact freshnessCertificate0144) p0016
  have p0018 := (Nominal.biimpRefl syntaxFormula0037)
  have freshnessCertificate0147 : x ∉ ((Class.cv t)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show x ∉ ({ t } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show x ≠ t from (by exact fresh_x_ne_t)))))
  have p0019 := @g_elpw131c x (.cv t) (by exact freshnessCertificate0147)
  have p0020 :=
    @g_anbi1i (.classMem (.cv t) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))
      (syn_wex x (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))
      syntaxFormula0036 p0019
  have freshnessCertificate0148 : x ∉ ((Class.cv a)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show x ∉ ({ a } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show x ≠ a from (by exact Ne.symm dv_a_x)))))
  have freshnessCertificate0149 : x ∉ ((syn_csn (.cv a))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0148)
  have freshnessCertificate0150 : x ∉ ((Class.cv m)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show x ∉ ({ m } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show x ≠ m from (by exact Ne.symm dv_m_x)))))
  have freshnessCertificate0151 : x ∉ (((syn_csn (.cv a))).fv) ∪ (((Class.cv m)).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0149 freshnessCertificate0150))
  have freshnessCertificate0152 : x ∉ ((syn_copk (syn_csn (.cv a)) (.cv m))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk];
      exact freshnessCertificate0151)
  have freshnessCertificate0153 :
    x ∉ (((Class.cv t)).fv) ∪ (((syn_copk (syn_csn (.cv a)) (.cv m))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0147 freshnessCertificate0152))
  have freshnessCertificate0154 :
    x ∉ ((syn_copk (.cv t) (syn_copk (syn_csn (.cv a)) (.cv m)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk];
      exact freshnessCertificate0153)
  have freshnessCertificate0155 : x ∉ ((syn_cssetk)).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk];
      exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))
  have freshnessCertificate0156 : x ∉ ((syn_csik (syn_cssetk))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0155)
  have freshnessCertificate0157 : x ∉ ((syn_csik (syn_csik (syn_cssetk)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0156)
  have freshnessCertificate0158 :
    x ∉ ((syn_csik (syn_csik (syn_csik (syn_cssetk))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0157)
  have freshnessCertificate0159 :
    x ∉ ((syn_csik (syn_csik (syn_csik (syn_csik (syn_cssetk)))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0158)
  have freshnessCertificate0160 :
    x ∉ ((syn_csik (syn_csik (syn_csik (syn_csik (syn_csik (syn_cssetk))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0159)
  have freshnessCertificate0161 : x ∉ (syntaxClass0000).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0160)
  have freshnessCertificate0162 : x ∉ ((syn_cins3k (syn_csik (syn_cssetk)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0156)
  have freshnessCertificate0163 :
    x ∉ ((syn_cins2k (syn_cins3k (syn_csik (syn_cssetk))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0162)
  have freshnessCertificate0164 : x ∉ ((syn_cidk)).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cidk];
      exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))
  have freshnessCertificate0165 : x ∉ ((syn_cins3k (syn_cidk))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0164)
  have freshnessCertificate0166 :
    x ∉
      (((syn_cins2k (syn_cins3k (syn_csik (syn_cssetk))))).fv) ∪
        (((syn_cins3k (syn_cidk))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0163 freshnessCertificate0165))
  have freshnessCertificate0167 : x ∉ (syntaxClass0001).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun];
      exact freshnessCertificate0166)
  have freshnessCertificate0168 : x ∉ (syntaxClass0002).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0167)
  have freshnessCertificate0169 : x ∉ ((syntaxClass0000).fv) ∪ ((syntaxClass0002).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0161 freshnessCertificate0168))
  have freshnessCertificate0170 : x ∉ (syntaxClass0003).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif];
      exact freshnessCertificate0169)
  have freshnessCertificate0171 : x ∉ ((syn_c1c)).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c];
      exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))
  have freshnessCertificate0172 : x ∉ ((syn_cpw1 (syn_c1c))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0171)
  have freshnessCertificate0173 : x ∉ ((syn_cpw1 (syn_cpw1 (syn_c1c)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0172)
  have freshnessCertificate0174 : x ∉ ((syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0173)
  have freshnessCertificate0175 :
    x ∉ ((syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0174)
  have freshnessCertificate0176 :
    x ∉ ((syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0175)
  have freshnessCertificate0177 :
    x ∉
      ((syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0176)
  have freshnessCertificate0178 : x ∉ (syntaxClass0004).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0177)
  have freshnessCertificate0179 : x ∉ ((syntaxClass0003).fv) ∪ ((syntaxClass0004).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0170 freshnessCertificate0178))
  have freshnessCertificate0180 : x ∉ (syntaxClass0005).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak];
      exact freshnessCertificate0179)
  have freshnessCertificate0181 : x ∉ (syntaxClass0006).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl];
      exact freshnessCertificate0180)
  have freshnessCertificate0182 : x ∉ ((syn_cins3k (syn_cssetk))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0155)
  have freshnessCertificate0183 : x ∉ ((syn_cins2k (syn_cssetk))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0155)
  have freshnessCertificate0184 :
    x ∉ (((syn_cins3k (syn_cssetk))).fv) ∪ (((syn_cins2k (syn_cssetk))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0182 freshnessCertificate0183))
  have freshnessCertificate0185 :
    x ∉ ((syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin];
      exact freshnessCertificate0184)
  have freshnessCertificate0186 :
    x ∉
      (((syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))).fv) ∪
        (((syn_cpw1 (syn_cpw1 (syn_c1c)))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0185 freshnessCertificate0173))
  have freshnessCertificate0187 : x ∉ (syntaxClass0007).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak];
      exact freshnessCertificate0186)
  have freshnessCertificate0188 : x ∉ (syntaxClass0008).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl];
      exact freshnessCertificate0187)
  have freshnessCertificate0189 : x ∉ (syntaxClass0009).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0188)
  have freshnessCertificate0190 : x ∉ ((syn_cins2k (syn_cins2k (syn_cssetk)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0183)
  have freshnessCertificate0191 : x ∉ ((syn_cins2k (syn_cins3k (syn_cssetk)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0182)
  have freshnessCertificate0192 :
    x ∉ ((syn_cins3k (syn_csik (syn_csik (syn_cssetk))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0157)
  have freshnessCertificate0193 :
    x ∉
      (((syn_cins2k (syn_cins3k (syn_cssetk)))).fv) ∪
        (((syn_cins3k (syn_csik (syn_csik (syn_cssetk))))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0191 freshnessCertificate0192))
  have freshnessCertificate0194 : x ∉ (syntaxClass0010).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun];
      exact freshnessCertificate0193)
  have freshnessCertificate0195 :
    x ∉ (((syn_cins2k (syn_cins2k (syn_cssetk)))).fv) ∪ ((syntaxClass0010).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0190 freshnessCertificate0194))
  have freshnessCertificate0196 : x ∉ (syntaxClass0011).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif];
      exact freshnessCertificate0195)
  have freshnessCertificate0197 :
    x ∉
      ((syntaxClass0011).fv) ∪
        (((syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0196 freshnessCertificate0175))
  have freshnessCertificate0198 : x ∉ (syntaxClass0012).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak];
      exact freshnessCertificate0197)
  have freshnessCertificate0199 : x ∉ ((syntaxClass0009).fv) ∪ ((syntaxClass0012).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0189 freshnessCertificate0198))
  have freshnessCertificate0200 : x ∉ (syntaxClass0013).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif];
      exact freshnessCertificate0199)
  have freshnessCertificate0201 :
    x ∉ ((syntaxClass0013).fv) ∪ (((syn_cpw1 (syn_cpw1 (syn_c1c)))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0200 freshnessCertificate0173))
  have freshnessCertificate0202 : x ∉ (syntaxClass0014).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak];
      exact freshnessCertificate0201)
  have freshnessCertificate0203 : x ∉ (syntaxClass0015).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimagek];
      exact freshnessCertificate0202)
  have freshnessCertificate0204 : x ∉ (syntaxClass0016).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk];
      exact freshnessCertificate0203)
  have freshnessCertificate0205 : x ∉ ((syntaxClass0016).fv) ∪ (((syn_cssetk)).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0204 freshnessCertificate0155))
  have freshnessCertificate0206 : x ∉ (syntaxClass0017).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccomk];
      exact freshnessCertificate0205)
  have freshnessCertificate0207 : x ∉ (syntaxClass0018).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0206)
  have freshnessCertificate0208 : x ∉ (syntaxClass0019).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0207)
  have freshnessCertificate0209 : x ∉ ((syntaxClass0006).fv) ∪ ((syntaxClass0019).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0181 freshnessCertificate0208))
  have freshnessCertificate0210 : x ∉ (syntaxClass0020).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin];
      exact freshnessCertificate0209)
  have freshnessCertificate0211 :
    x ∉
      ((syntaxClass0020).fv) ∪
        (((syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0210 freshnessCertificate0175))
  have freshnessCertificate0212 : x ∉ (syntaxClass0021).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak];
      exact freshnessCertificate0211)
  have freshnessCertificate0213 :
    x ∉ ((syntaxClass0021).fv) ∪ (((syn_cins3k (syn_csik (syn_cssetk)))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0212 freshnessCertificate0162))
  have freshnessCertificate0214 : x ∉ (syntaxClass0022).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif];
      exact freshnessCertificate0213)
  have freshnessCertificate0215 : x ∉ ((syn_cvv)).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv];
      exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))
  have freshnessCertificate0216 : x ∉ (((syn_cvv)).fv) ∪ (((syn_cssetk)).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0215 freshnessCertificate0155))
  have freshnessCertificate0217 : x ∉ ((syn_cxpk (syn_cvv) (syn_cssetk))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk];
      exact freshnessCertificate0216)
  have freshnessCertificate0218 :
    x ∉ ((syntaxClass0022).fv) ∪ (((syn_cxpk (syn_cvv) (syn_cssetk))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0214 freshnessCertificate0217))
  have freshnessCertificate0219 : x ∉ (syntaxClass0023).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif];
      exact freshnessCertificate0218)
  have freshnessCertificate0220 :
    x ∉
      (((syn_copk (.cv t) (syn_copk (syn_csn (.cv a)) (.cv m)))).fv) ∪
        ((syntaxClass0023).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0154 freshnessCertificate0219))
  have freshnessCertificate0221 :
    x ∉
      ((Wff.classMem (syn_copk (.cv t) (syn_copk (syn_csn (.cv a)) (.cv m)))
          syntaxClass0023)).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact freshnessCertificate0220)
  have p0021 :=
    @g_n_19_41v (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))
      syntaxFormula0036 x (by exact freshnessCertificate0221)
  have p0022 :=
    @g_bitr4i syntaxFormula0038
      (syn_wa (syn_wex x (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))
        syntaxFormula0036)
      syntaxFormula0040 p0020 p0021
  have p0023 := @g_exbii syntaxFormula0038 syntaxFormula0040 t p0022
  have p0024 := @g_excom syntaxFormula0039 x t
  have p0025 :=
    @g_bitr4i syntaxFormula0041 (syn_wex t syntaxFormula0040) syntaxFormula0043 p0023
      p0024
  have p0026 := @g_bitri syntaxFormula0037 syntaxFormula0041 syntaxFormula0043 p0018 p0025
  have p0027 := @g_bitri syntaxFormula0035 syntaxFormula0037 syntaxFormula0043 p0017 p0026
  have p0028 := @g_snex (syn_csn (syn_csn (syn_csn (.cv x))))
  have p0029 :=
    @g_opkeq1 (.cv t) (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))
      (syn_copk (syn_csn (.cv a)) (.cv m))
  have p0030 :=
    @g_eleq1d (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))
      (syn_copk (.cv t) (syn_copk (syn_csn (.cv a)) (.cv m))) syntaxClass0044
      syntaxClass0023 p0029
  have freshnessCertificate0222 : t ∉ ((Class.cv x)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show t ∉ ({ x } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show t ≠ x from (by exact fresh_t_ne_x)))))
  have freshnessCertificate0223 : t ∉ ((syn_csn (.cv x))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0222)
  have freshnessCertificate0224 : t ∉ ((syn_csn (syn_csn (.cv x)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0223)
  have freshnessCertificate0225 : t ∉ ((syn_csn (syn_csn (syn_csn (.cv x))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0224)
  have freshnessCertificate0226 :
    t ∉ ((syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0225)
  have freshnessCertificate0227 :
    t ∉
      (((syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))).fv) ∪
        (((syn_copk (syn_csn (.cv a)) (.cv m))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0226 freshnessCertificate0144))
  have freshnessCertificate0228 : t ∉ (syntaxClass0044).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk];
      exact freshnessCertificate0227)
  have freshnessCertificate0229 : t ∉ ((syntaxClass0044).fv) ∪ ((syntaxClass0023).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0228 freshnessCertificate0064))
  have freshnessCertificate0230 :
    t ∉ ((Wff.classMem syntaxClass0044 syntaxClass0023)).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact freshnessCertificate0229)
  have p0031 :=
    @g_ceqsexv syntaxFormula0036 syntaxFormula0045 t
      (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))) (by exact freshnessCertificate0226)
      (by exact freshnessCertificate0230) p0028 p0030
  have p0032 := @g_eldif syntaxClass0044 syntaxClass0022 (syn_cxpk (syn_cvv) (syn_cssetk))
  have p0033 :=
    @g_eldif syntaxClass0044 syntaxClass0021 (syn_cins3k (syn_csik (syn_cssetk)))
  have p0034 :=
    @g_opkex (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))
      (syn_copk (syn_csn (.cv a)) (.cv m))
  have p0035 :=
    @g_elimak t syntaxClass0020 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))
      syntaxClass0044 (by exact freshnessCertificate0055)
      (by exact freshnessCertificate0020) (by exact freshnessCertificate0228) p0034
  have p0036 := (Nominal.biimpRefl syntaxFormula0048)
  have freshnessCertificate0231 : w ∉ ((Class.cv t)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show w ∉ ({ t } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show w ≠ t from (by exact fresh_w_ne_t)))))
  have p0037 := @g_elpw141c w (.cv t) (by exact freshnessCertificate0231)
  have p0038 :=
    @g_anbi1i (.classMem (.cv t) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))
      (syn_wex w (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv w))))))))
      syntaxFormula0047 p0037
  have freshnessCertificate0232 : w ∉ ((Class.cv x)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show w ∉ ({ x } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show w ≠ x from (by exact fresh_w_ne_x)))))
  have freshnessCertificate0233 : w ∉ ((syn_csn (.cv x))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0232)
  have freshnessCertificate0234 : w ∉ ((syn_csn (syn_csn (.cv x)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0233)
  have freshnessCertificate0235 : w ∉ ((syn_csn (syn_csn (syn_csn (.cv x))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0234)
  have freshnessCertificate0236 :
    w ∉ ((syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0235)
  have freshnessCertificate0237 : w ∉ ((Class.cv a)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show w ∉ ({ a } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show w ≠ a from (by exact fresh_w_ne_a)))))
  have freshnessCertificate0238 : w ∉ ((syn_csn (.cv a))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0237)
  have freshnessCertificate0239 : w ∉ ((Class.cv m)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show w ∉ ({ m } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show w ≠ m from (by exact fresh_w_ne_m)))))
  have freshnessCertificate0240 : w ∉ (((syn_csn (.cv a))).fv) ∪ (((Class.cv m)).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0238 freshnessCertificate0239))
  have freshnessCertificate0241 : w ∉ ((syn_copk (syn_csn (.cv a)) (.cv m))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk];
      exact freshnessCertificate0240)
  have freshnessCertificate0242 :
    w ∉
      (((syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))).fv) ∪
        (((syn_copk (syn_csn (.cv a)) (.cv m))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0236 freshnessCertificate0241))
  have freshnessCertificate0243 : w ∉ (syntaxClass0044).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk];
      exact freshnessCertificate0242)
  have freshnessCertificate0244 : w ∉ (((Class.cv t)).fv) ∪ ((syntaxClass0044).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0231 freshnessCertificate0243))
  have freshnessCertificate0245 : w ∉ (syntaxClass0046).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk];
      exact freshnessCertificate0244)
  have freshnessCertificate0246 : w ∉ ((syn_cssetk)).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk];
      exact (show w ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))
  have freshnessCertificate0247 : w ∉ ((syn_csik (syn_cssetk))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0246)
  have freshnessCertificate0248 : w ∉ ((syn_csik (syn_csik (syn_cssetk)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0247)
  have freshnessCertificate0249 :
    w ∉ ((syn_csik (syn_csik (syn_csik (syn_cssetk))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0248)
  have freshnessCertificate0250 :
    w ∉ ((syn_csik (syn_csik (syn_csik (syn_csik (syn_cssetk)))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0249)
  have freshnessCertificate0251 :
    w ∉ ((syn_csik (syn_csik (syn_csik (syn_csik (syn_csik (syn_cssetk))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0250)
  have freshnessCertificate0252 : w ∉ (syntaxClass0000).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0251)
  have freshnessCertificate0253 : w ∉ ((syn_cins3k (syn_csik (syn_cssetk)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0247)
  have freshnessCertificate0254 :
    w ∉ ((syn_cins2k (syn_cins3k (syn_csik (syn_cssetk))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0253)
  have freshnessCertificate0255 : w ∉ ((syn_cidk)).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cidk];
      exact (show w ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))
  have freshnessCertificate0256 : w ∉ ((syn_cins3k (syn_cidk))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0255)
  have freshnessCertificate0257 :
    w ∉
      (((syn_cins2k (syn_cins3k (syn_csik (syn_cssetk))))).fv) ∪
        (((syn_cins3k (syn_cidk))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0254 freshnessCertificate0256))
  have freshnessCertificate0258 : w ∉ (syntaxClass0001).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun];
      exact freshnessCertificate0257)
  have freshnessCertificate0259 : w ∉ (syntaxClass0002).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0258)
  have freshnessCertificate0260 : w ∉ ((syntaxClass0000).fv) ∪ ((syntaxClass0002).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0252 freshnessCertificate0259))
  have freshnessCertificate0261 : w ∉ (syntaxClass0003).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif];
      exact freshnessCertificate0260)
  have freshnessCertificate0262 : w ∉ ((syn_c1c)).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c];
      exact (show w ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))
  have freshnessCertificate0263 : w ∉ ((syn_cpw1 (syn_c1c))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0262)
  have freshnessCertificate0264 : w ∉ ((syn_cpw1 (syn_cpw1 (syn_c1c)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0263)
  have freshnessCertificate0265 : w ∉ ((syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0264)
  have freshnessCertificate0266 :
    w ∉ ((syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0265)
  have freshnessCertificate0267 :
    w ∉ ((syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0266)
  have freshnessCertificate0268 :
    w ∉
      ((syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0267)
  have freshnessCertificate0269 : w ∉ (syntaxClass0004).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0268)
  have freshnessCertificate0270 : w ∉ ((syntaxClass0003).fv) ∪ ((syntaxClass0004).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0261 freshnessCertificate0269))
  have freshnessCertificate0271 : w ∉ (syntaxClass0005).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak];
      exact freshnessCertificate0270)
  have freshnessCertificate0272 : w ∉ (syntaxClass0006).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl];
      exact freshnessCertificate0271)
  have freshnessCertificate0273 : w ∉ ((syn_cins3k (syn_cssetk))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0246)
  have freshnessCertificate0274 : w ∉ ((syn_cins2k (syn_cssetk))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0246)
  have freshnessCertificate0275 :
    w ∉ (((syn_cins3k (syn_cssetk))).fv) ∪ (((syn_cins2k (syn_cssetk))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0273 freshnessCertificate0274))
  have freshnessCertificate0276 :
    w ∉ ((syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin];
      exact freshnessCertificate0275)
  have freshnessCertificate0277 :
    w ∉
      (((syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))).fv) ∪
        (((syn_cpw1 (syn_cpw1 (syn_c1c)))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0276 freshnessCertificate0264))
  have freshnessCertificate0278 : w ∉ (syntaxClass0007).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak];
      exact freshnessCertificate0277)
  have freshnessCertificate0279 : w ∉ (syntaxClass0008).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl];
      exact freshnessCertificate0278)
  have freshnessCertificate0280 : w ∉ (syntaxClass0009).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0279)
  have freshnessCertificate0281 : w ∉ ((syn_cins2k (syn_cins2k (syn_cssetk)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0274)
  have freshnessCertificate0282 : w ∉ ((syn_cins2k (syn_cins3k (syn_cssetk)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0273)
  have freshnessCertificate0283 :
    w ∉ ((syn_cins3k (syn_csik (syn_csik (syn_cssetk))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0248)
  have freshnessCertificate0284 :
    w ∉
      (((syn_cins2k (syn_cins3k (syn_cssetk)))).fv) ∪
        (((syn_cins3k (syn_csik (syn_csik (syn_cssetk))))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0282 freshnessCertificate0283))
  have freshnessCertificate0285 : w ∉ (syntaxClass0010).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun];
      exact freshnessCertificate0284)
  have freshnessCertificate0286 :
    w ∉ (((syn_cins2k (syn_cins2k (syn_cssetk)))).fv) ∪ ((syntaxClass0010).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0281 freshnessCertificate0285))
  have freshnessCertificate0287 : w ∉ (syntaxClass0011).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif];
      exact freshnessCertificate0286)
  have freshnessCertificate0288 :
    w ∉
      ((syntaxClass0011).fv) ∪
        (((syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0287 freshnessCertificate0266))
  have freshnessCertificate0289 : w ∉ (syntaxClass0012).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak];
      exact freshnessCertificate0288)
  have freshnessCertificate0290 : w ∉ ((syntaxClass0009).fv) ∪ ((syntaxClass0012).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0280 freshnessCertificate0289))
  have freshnessCertificate0291 : w ∉ (syntaxClass0013).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif];
      exact freshnessCertificate0290)
  have freshnessCertificate0292 :
    w ∉ ((syntaxClass0013).fv) ∪ (((syn_cpw1 (syn_cpw1 (syn_c1c)))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0291 freshnessCertificate0264))
  have freshnessCertificate0293 : w ∉ (syntaxClass0014).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak];
      exact freshnessCertificate0292)
  have freshnessCertificate0294 : w ∉ (syntaxClass0015).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimagek];
      exact freshnessCertificate0293)
  have freshnessCertificate0295 : w ∉ (syntaxClass0016).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk];
      exact freshnessCertificate0294)
  have freshnessCertificate0296 : w ∉ ((syntaxClass0016).fv) ∪ (((syn_cssetk)).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0295 freshnessCertificate0246))
  have freshnessCertificate0297 : w ∉ (syntaxClass0017).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccomk];
      exact freshnessCertificate0296)
  have freshnessCertificate0298 : w ∉ (syntaxClass0018).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0297)
  have freshnessCertificate0299 : w ∉ (syntaxClass0019).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0298)
  have freshnessCertificate0300 : w ∉ ((syntaxClass0006).fv) ∪ ((syntaxClass0019).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0272 freshnessCertificate0299))
  have freshnessCertificate0301 : w ∉ (syntaxClass0020).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin];
      exact freshnessCertificate0300)
  have freshnessCertificate0302 : w ∉ ((syntaxClass0046).fv) ∪ ((syntaxClass0020).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0245 freshnessCertificate0301))
  have freshnessCertificate0303 :
    w ∉ ((Wff.classMem syntaxClass0046 syntaxClass0020)).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact freshnessCertificate0302)
  have p0039 :=
    @g_n_19_41v
      (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv w)))))))
      syntaxFormula0047 w (by exact freshnessCertificate0303)
  have p0040 :=
    @g_bitr4i syntaxFormula0049
      (syn_wa (syn_wex w
          (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv w))))))))
        syntaxFormula0047)
      syntaxFormula0051 p0038 p0039
  have p0041 := @g_exbii syntaxFormula0049 syntaxFormula0051 t p0040
  have p0042 := @g_excom syntaxFormula0050 w t
  have p0043 :=
    @g_bitr4i syntaxFormula0052 (syn_wex t syntaxFormula0051) syntaxFormula0054 p0041
      p0042
  have p0044 := @g_bitri syntaxFormula0048 syntaxFormula0052 syntaxFormula0054 p0036 p0043
  have p0045 := @g_snex (syn_csn (syn_csn (syn_csn (syn_csn (.cv w)))))
  have p0046 :=
    @g_opkeq1 (.cv t) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv w))))))
      syntaxClass0044
  have p0047 :=
    @g_eleq1d (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv w)))))))
      syntaxClass0046 syntaxClass0055 syntaxClass0020 p0046
  have freshnessCertificate0304 : t ∉ ((Class.cv w)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show t ∉ ({ w } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show t ≠ w from (by exact fresh_t_ne_w)))))
  have freshnessCertificate0305 : t ∉ ((syn_csn (.cv w))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0304)
  have freshnessCertificate0306 : t ∉ ((syn_csn (syn_csn (.cv w)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0305)
  have freshnessCertificate0307 : t ∉ ((syn_csn (syn_csn (syn_csn (.cv w))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0306)
  have freshnessCertificate0308 :
    t ∉ ((syn_csn (syn_csn (syn_csn (syn_csn (.cv w)))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0307)
  have freshnessCertificate0309 :
    t ∉ ((syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv w))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0308)
  have freshnessCertificate0310 :
    t ∉
      (((syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv w))))))).fv) ∪
        ((syntaxClass0044).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0309 freshnessCertificate0228))
  have freshnessCertificate0311 : t ∉ (syntaxClass0055).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk];
      exact freshnessCertificate0310)
  have freshnessCertificate0312 : t ∉ ((syntaxClass0055).fv) ∪ ((syntaxClass0020).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0311 freshnessCertificate0055))
  have freshnessCertificate0313 :
    t ∉ ((Wff.classMem syntaxClass0055 syntaxClass0020)).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact freshnessCertificate0312)
  have p0048 :=
    @g_ceqsexv syntaxFormula0047 syntaxFormula0056 t
      (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv w))))))
      (by exact freshnessCertificate0309) (by exact freshnessCertificate0313) p0045 p0047
  have p0049 := @g_elin syntaxClass0055 syntaxClass0006 syntaxClass0019
  have p0050 :=
    @g_opkex (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv w)))))) syntaxClass0044
  have p0051 :=
    @g_elimak t syntaxClass0003 syntaxClass0004 syntaxClass0055
      (by exact freshnessCertificate0015) (by exact freshnessCertificate0023)
      (by exact freshnessCertificate0311) p0050
  have p0052 := (Nominal.biimpRefl syntaxFormula0059)
  have freshnessCertificate0314 : e ∉ ((Class.cv t)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show e ∉ ({ t } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show e ≠ t from (by exact fresh_e_ne_t)))))
  have p0053 := @g_elpw171c e (.cv t) (by exact freshnessCertificate0314)
  have p0054 :=
    @g_anbi1i syntaxFormula0060 (syn_wex e syntaxFormula0062) syntaxFormula0058 p0053
  have freshnessCertificate0315 : e ∉ ((Class.cv w)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show e ∉ ({ w } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show e ≠ w from (by exact fresh_e_ne_w)))))
  have freshnessCertificate0316 : e ∉ ((syn_csn (.cv w))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0315)
  have freshnessCertificate0317 : e ∉ ((syn_csn (syn_csn (.cv w)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0316)
  have freshnessCertificate0318 : e ∉ ((syn_csn (syn_csn (syn_csn (.cv w))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0317)
  have freshnessCertificate0319 :
    e ∉ ((syn_csn (syn_csn (syn_csn (syn_csn (.cv w)))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0318)
  have freshnessCertificate0320 :
    e ∉ ((syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv w))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0319)
  have freshnessCertificate0321 : e ∉ ((Class.cv x)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show e ∉ ({ x } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show e ≠ x from (by exact fresh_e_ne_x)))))
  have freshnessCertificate0322 : e ∉ ((syn_csn (.cv x))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0321)
  have freshnessCertificate0323 : e ∉ ((syn_csn (syn_csn (.cv x)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0322)
  have freshnessCertificate0324 : e ∉ ((syn_csn (syn_csn (syn_csn (.cv x))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0323)
  have freshnessCertificate0325 :
    e ∉ ((syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0324)
  have freshnessCertificate0326 : e ∉ ((Class.cv a)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show e ∉ ({ a } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show e ≠ a from (by exact fresh_e_ne_a)))))
  have freshnessCertificate0327 : e ∉ ((syn_csn (.cv a))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0326)
  have freshnessCertificate0328 : e ∉ ((Class.cv m)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show e ∉ ({ m } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show e ≠ m from (by exact fresh_e_ne_m)))))
  have freshnessCertificate0329 : e ∉ (((syn_csn (.cv a))).fv) ∪ (((Class.cv m)).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0327 freshnessCertificate0328))
  have freshnessCertificate0330 : e ∉ ((syn_copk (syn_csn (.cv a)) (.cv m))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk];
      exact freshnessCertificate0329)
  have freshnessCertificate0331 :
    e ∉
      (((syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))).fv) ∪
        (((syn_copk (syn_csn (.cv a)) (.cv m))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0325 freshnessCertificate0330))
  have freshnessCertificate0332 : e ∉ (syntaxClass0044).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk];
      exact freshnessCertificate0331)
  have freshnessCertificate0333 :
    e ∉
      (((syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv w))))))).fv) ∪
        ((syntaxClass0044).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0320 freshnessCertificate0332))
  have freshnessCertificate0334 : e ∉ (syntaxClass0055).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk];
      exact freshnessCertificate0333)
  have freshnessCertificate0335 : e ∉ (((Class.cv t)).fv) ∪ ((syntaxClass0055).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0314 freshnessCertificate0334))
  have freshnessCertificate0336 : e ∉ (syntaxClass0057).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk];
      exact freshnessCertificate0335)
  have freshnessCertificate0337 : e ∉ ((syn_cssetk)).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk];
      exact (show e ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))
  have freshnessCertificate0338 : e ∉ ((syn_csik (syn_cssetk))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0337)
  have freshnessCertificate0339 : e ∉ ((syn_csik (syn_csik (syn_cssetk)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0338)
  have freshnessCertificate0340 :
    e ∉ ((syn_csik (syn_csik (syn_csik (syn_cssetk))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0339)
  have freshnessCertificate0341 :
    e ∉ ((syn_csik (syn_csik (syn_csik (syn_csik (syn_cssetk)))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0340)
  have freshnessCertificate0342 :
    e ∉ ((syn_csik (syn_csik (syn_csik (syn_csik (syn_csik (syn_cssetk))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0341)
  have freshnessCertificate0343 : e ∉ (syntaxClass0000).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0342)
  have freshnessCertificate0344 : e ∉ ((syn_cins3k (syn_csik (syn_cssetk)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0338)
  have freshnessCertificate0345 :
    e ∉ ((syn_cins2k (syn_cins3k (syn_csik (syn_cssetk))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0344)
  have freshnessCertificate0346 : e ∉ ((syn_cidk)).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cidk];
      exact (show e ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))
  have freshnessCertificate0347 : e ∉ ((syn_cins3k (syn_cidk))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0346)
  have freshnessCertificate0348 :
    e ∉
      (((syn_cins2k (syn_cins3k (syn_csik (syn_cssetk))))).fv) ∪
        (((syn_cins3k (syn_cidk))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0345 freshnessCertificate0347))
  have freshnessCertificate0349 : e ∉ (syntaxClass0001).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun];
      exact freshnessCertificate0348)
  have freshnessCertificate0350 : e ∉ (syntaxClass0002).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0349)
  have freshnessCertificate0351 : e ∉ ((syntaxClass0000).fv) ∪ ((syntaxClass0002).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0343 freshnessCertificate0350))
  have freshnessCertificate0352 : e ∉ (syntaxClass0003).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif];
      exact freshnessCertificate0351)
  have freshnessCertificate0353 : e ∉ ((syntaxClass0057).fv) ∪ ((syntaxClass0003).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0336 freshnessCertificate0352))
  have freshnessCertificate0354 :
    e ∉ ((Wff.classMem syntaxClass0057 syntaxClass0003)).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact freshnessCertificate0353)
  have p0055 :=
    @g_n_19_41v syntaxFormula0062 syntaxFormula0058 e (by exact freshnessCertificate0354)
  have p0056 :=
    @g_bitr4i syntaxFormula0063 (syn_wa (syn_wex e syntaxFormula0062) syntaxFormula0058)
      syntaxFormula0065 p0054 p0055
  have p0057 := @g_exbii syntaxFormula0063 syntaxFormula0065 t p0056
  have p0058 := @g_excom syntaxFormula0064 e t
  have p0059 :=
    @g_bitr4i syntaxFormula0066 (syn_wex t syntaxFormula0065) syntaxFormula0068 p0057
      p0058
  have p0060 := @g_bitri syntaxFormula0059 syntaxFormula0066 syntaxFormula0068 p0052 p0059
  have p0061 := @g_bitri syntaxFormula0069 syntaxFormula0059 syntaxFormula0068 p0051 p0060
  have p0062 :=
    @g_snex (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv e))))))))
  have p0063 := @g_opkeq1 (.cv t) syntaxClass0061 syntaxClass0055
  have p0064 :=
    @g_eleq1d syntaxFormula0062 syntaxClass0057 syntaxClass0070 syntaxClass0003 p0063
  have freshnessCertificate0355 : t ∉ ((Class.cv e)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show t ∉ ({ e } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show t ≠ e from (by exact fresh_t_ne_e)))))
  have freshnessCertificate0356 : t ∉ ((syn_csn (.cv e))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0355)
  have freshnessCertificate0357 : t ∉ ((syn_csn (syn_csn (.cv e)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0356)
  have freshnessCertificate0358 : t ∉ ((syn_csn (syn_csn (syn_csn (.cv e))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0357)
  have freshnessCertificate0359 :
    t ∉ ((syn_csn (syn_csn (syn_csn (syn_csn (.cv e)))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0358)
  have freshnessCertificate0360 :
    t ∉ ((syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv e))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0359)
  have freshnessCertificate0361 :
    t ∉ ((syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv e)))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0360)
  have freshnessCertificate0362 :
    t ∉
      ((syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv e))))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0361)
  have freshnessCertificate0363 : t ∉ (syntaxClass0061).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0362)
  have freshnessCertificate0364 : t ∉ ((syntaxClass0061).fv) ∪ ((syntaxClass0055).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0363 freshnessCertificate0311))
  have freshnessCertificate0365 : t ∉ (syntaxClass0070).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk];
      exact freshnessCertificate0364)
  have freshnessCertificate0366 : t ∉ ((syntaxClass0070).fv) ∪ ((syntaxClass0003).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0365 freshnessCertificate0015))
  have freshnessCertificate0367 :
    t ∉ ((Wff.classMem syntaxClass0070 syntaxClass0003)).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact freshnessCertificate0366)
  have p0065 :=
    @g_ceqsexv syntaxFormula0058 syntaxFormula0071 t syntaxClass0061
      (by exact freshnessCertificate0363) (by exact freshnessCertificate0367) p0062 p0064
  have p0066 := @g_elsymdif syntaxClass0070 syntaxClass0000 syntaxClass0002
  have p0067 := @g_snex (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv e))))))
  have p0068 :=
    @g_otkelins3k (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv e)))))))
      (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv w)))))) syntaxClass0044
      (syn_csik (syn_csik (syn_csik (syn_csik (syn_csik (syn_cssetk)))))) p0067 p0045
      p0034
  have p0069 := @g_snex (syn_csn (syn_csn (syn_csn (syn_csn (.cv e)))))
  have p0070 := @g_snex (syn_csn (syn_csn (syn_csn (.cv w))))
  have p0071 :=
    @g_opksnelsik (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv e))))))
      (syn_csn (syn_csn (syn_csn (syn_csn (.cv w)))))
      (syn_csik (syn_csik (syn_csik (syn_csik (syn_cssetk))))) p0069 p0070
  have p0072 := @g_snex (syn_csn (syn_csn (syn_csn (.cv e))))
  have p0073 := @g_snex (syn_csn (syn_csn (.cv w)))
  have p0074 :=
    @g_opksnelsik (syn_csn (syn_csn (syn_csn (syn_csn (.cv e)))))
      (syn_csn (syn_csn (syn_csn (.cv w)))) (syn_csik (syn_csik (syn_csik (syn_cssetk))))
      p0072 p0073
  have p0075 := @g_snex (syn_csn (syn_csn (.cv e)))
  have p0076 := @g_snex (syn_csn (.cv w))
  have p0077 :=
    @g_opksnelsik (syn_csn (syn_csn (syn_csn (.cv e)))) (syn_csn (syn_csn (.cv w)))
      (syn_csik (syn_csik (syn_cssetk))) p0075 p0076
  have p0078 := @g_snex (syn_csn (.cv e))
  have p0079 := @g_snex (.cv w)
  have p0080 :=
    @g_opksnelsik (syn_csn (syn_csn (.cv e))) (syn_csn (.cv w)) (syn_csik (syn_cssetk))
      p0078 p0079
  have p0081 := @g_snex (.cv e)
  have p0082 := @g_vex w
  have p0083 := @g_opksnelsik (syn_csn (.cv e)) (.cv w) (syn_cssetk) p0081 p0082
  have p0084 := @g_vex e
  have p0085 := @g_elssetk (.cv e) (.cv w) p0084 p0082
  have p0086_e01_recanon :
    Nominal.NPrf
      (syn_wb (.classMem (syn_copk (syn_csn (.cv e)) (.cv w)) (syn_cssetk)) (.objMem e w)) :=
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
      p0085
  have p0086 :=
    @g_bitri
      (.classMem (syn_copk (syn_csn (syn_csn (.cv e))) (syn_csn (.cv w)))
        (syn_csik (syn_cssetk)))
      (.classMem (syn_copk (syn_csn (.cv e)) (.cv w)) (syn_cssetk)) (.objMem e w) p0083
      p0086_e01_recanon
  have p0087 :=
    @g_bitri
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv e)))) (syn_csn (syn_csn (.cv w))))
        (syn_csik (syn_csik (syn_cssetk))))
      (.classMem (syn_copk (syn_csn (syn_csn (.cv e))) (syn_csn (.cv w)))
        (syn_csik (syn_cssetk)))
      (.objMem e w) p0080 p0086
  have p0088 :=
    @g_bitri
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (syn_csn (.cv e)))))
          (syn_csn (syn_csn (syn_csn (.cv w))))) (syn_csik (syn_csik (syn_csik (syn_cssetk)))))
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv e)))) (syn_csn (syn_csn (.cv w))))
        (syn_csik (syn_csik (syn_cssetk))))
      (.objMem e w) p0077 p0087
  have p0089 :=
    @g_bitri syntaxFormula0072
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (syn_csn (.cv e)))))
          (syn_csn (syn_csn (syn_csn (.cv w))))) (syn_csik (syn_csik (syn_csik (syn_cssetk)))))
      (.objMem e w) p0074 p0088
  have p0090 := @g_bitri syntaxFormula0073 syntaxFormula0072 (.objMem e w) p0071 p0089
  have p0091 := @g_bitri syntaxFormula0074 syntaxFormula0073 (.objMem e w) p0068 p0090
  have p0092 :=
    @g_otkelins2k (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv e)))))))
      (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv w)))))) syntaxClass0044
      syntaxClass0001 p0067 p0045 p0034
  have p0093 :=
    @g_otkelins2k (syn_csn (syn_csn (syn_csn (syn_csn (.cv e)))))
      (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))) (syn_copk (syn_csn (.cv a)) (.cv m))
      (syn_cins3k (syn_csik (syn_cssetk))) p0072 p0028 p0016
  have p0094 :=
    @g_otkelins3k (syn_csn (syn_csn (.cv e))) (syn_csn (.cv a)) (.cv m)
      (syn_csik (syn_cssetk)) p0078 p0012 p0000
  have p0095 := @g_vex a
  have p0096 := @g_opksnelsik (syn_csn (.cv e)) (.cv a) (syn_cssetk) p0081 p0095
  have p0097 := @g_elssetk (.cv e) (.cv a) p0084 p0095
  have p0098_e01_recanon :
    Nominal.NPrf
      (syn_wb (.classMem (syn_copk (syn_csn (.cv e)) (.cv a)) (syn_cssetk)) (.objMem e a)) :=
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
      p0097
  have p0098 :=
    @g_bitri
      (.classMem (syn_copk (syn_csn (syn_csn (.cv e))) (syn_csn (.cv a)))
        (syn_csik (syn_cssetk)))
      (.classMem (syn_copk (syn_csn (.cv e)) (.cv a)) (syn_cssetk)) (.objMem e a) p0096
      p0098_e01_recanon
  have p0099 :=
    @g_bitri
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (syn_csn (.cv e)))))
          (syn_copk (syn_csn (.cv a)) (.cv m))) (syn_cins3k (syn_csik (syn_cssetk))))
      (.classMem (syn_copk (syn_csn (syn_csn (.cv e))) (syn_csn (.cv a)))
        (syn_csik (syn_cssetk)))
      (.objMem e a) p0094 p0098
  have p0100 :=
    @g_bitri syntaxFormula0076
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (syn_csn (.cv e)))))
          (syn_copk (syn_csn (.cv a)) (.cv m))) (syn_cins3k (syn_csik (syn_cssetk))))
      (.objMem e a) p0093 p0099
  have p0101 :=
    @g_otkelins3k (syn_csn (syn_csn (syn_csn (syn_csn (.cv e)))))
      (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))) (syn_copk (syn_csn (.cv a)) (.cv m))
      (syn_cidk) p0072 p0028 p0016
  have p0102 :=
    @g_sneqb (syn_csn (syn_csn (syn_csn (.cv e)))) (syn_csn (syn_csn (syn_csn (.cv x))))
      p0075
  have p0103 := @g_sneqb (syn_csn (syn_csn (.cv e))) (syn_csn (syn_csn (.cv x))) p0078
  have p0104 := @g_sneqb (syn_csn (.cv e)) (syn_csn (.cv x)) p0081
  have p0105 := @g_sneqb (.cv e) (.cv x) p0084
  have p0106_e01_recanon :
    Nominal.NPrf (syn_wb (.classEq (syn_csn (.cv e)) (syn_csn (.cv x))) (.objEq e x)) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [syn_wb, syn_csn]
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0105
  have p0106 :=
    @g_bitri (.classEq (syn_csn (syn_csn (.cv e))) (syn_csn (syn_csn (.cv x))))
      (.classEq (syn_csn (.cv e)) (syn_csn (.cv x))) (.objEq e x) p0104 p0106_e01_recanon
  have p0107 :=
    @g_bitri
      (.classEq (syn_csn (syn_csn (syn_csn (.cv e)))) (syn_csn (syn_csn (syn_csn (.cv x)))))
      (.classEq (syn_csn (syn_csn (.cv e))) (syn_csn (syn_csn (.cv x)))) (.objEq e x)
      p0103 p0106
  have p0108 :=
    @g_bitri syntaxFormula0077
      (.classEq (syn_csn (syn_csn (syn_csn (.cv e)))) (syn_csn (syn_csn (syn_csn (.cv x)))))
      (.objEq e x) p0102 p0107
  have p0109 :=
    @g_opkelidkg (syn_csn (syn_csn (syn_csn (syn_csn (.cv e)))))
      (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))) (syn_cvv) (syn_cvv)
  have p0110 :=
    @g_mp2an (.classMem (syn_csn (syn_csn (syn_csn (syn_csn (.cv e))))) (syn_cvv))
      (.classMem (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))) (syn_cvv))
      (syn_wb syntaxFormula0079 syntaxFormula0077) p0072 p0028 p0109
  have p0111 := @g_elsnc (.cv e) (.cv x) p0084
  have p0112_e02_recanon :
    Nominal.NPrf (syn_wb (.classMem (.cv e) (syn_csn (.cv x))) (.objEq e x)) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [syn_wb, syn_csn]
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0111
  have p0112 :=
    @g_n_3bitr4i syntaxFormula0077 (.objEq e x) syntaxFormula0079
      (.classMem (.cv e) (syn_csn (.cv x))) p0108 p0110 p0112_e02_recanon
  have p0113 :=
    @g_bitri syntaxFormula0080 syntaxFormula0079 (.classMem (.cv e) (syn_csn (.cv x)))
      p0101 p0112
  have p0114 :=
    @g_orbi12i syntaxFormula0076 (.objMem e a) syntaxFormula0080
      (.classMem (.cv e) (syn_csn (.cv x))) p0100 p0113
  have p0115 :=
    @g_elun syntaxClass0075 (syn_cins2k (syn_cins3k (syn_csik (syn_cssetk))))
      (syn_cins3k (syn_cidk))
  have p0116 := @g_elun (.cv e) (.cv a) (syn_csn (.cv x))
  have p0117_e02_recanon :
    Nominal.NPrf
      (syn_wb (.classMem (.cv e) (syn_cun (.cv a) (syn_csn (.cv x))))
        (syn_wo (.objMem e a) (.classMem (.cv e) (syn_csn (.cv x))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [syn_wb, syn_cun, syn_cnin, syn_wnan, syn_wa, syn_ccompl, syn_csn,
          syn_wo]
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0116
  have p0117 :=
    @g_n_3bitr4i (syn_wo syntaxFormula0076 syntaxFormula0080)
      (syn_wo (.objMem e a) (.classMem (.cv e) (syn_csn (.cv x)))) syntaxFormula0081
      (.classMem (.cv e) (syn_cun (.cv a) (syn_csn (.cv x)))) p0114 p0115
      p0117_e02_recanon
  have p0118 :=
    @g_bitri syntaxFormula0082 syntaxFormula0081
      (.classMem (.cv e) (syn_cun (.cv a) (syn_csn (.cv x)))) p0092 p0117
  have p0119 :=
    @g_bibi12i syntaxFormula0074 (.objMem e w) syntaxFormula0082
      (.classMem (.cv e) (syn_cun (.cv a) (syn_csn (.cv x)))) p0091 p0118
  have p0120 :=
    @g_notbii syntaxFormula0083
      (syn_wb (.objMem e w) (.classMem (.cv e) (syn_cun (.cv a) (syn_csn (.cv x))))) p0119
  have p0121 :=
    @g_bitri syntaxFormula0071 (.neg syntaxFormula0083) syntaxFormula0084 p0066 p0120
  have p0122 := @g_bitri syntaxFormula0067 syntaxFormula0071 syntaxFormula0084 p0065 p0121
  have p0123 := @g_exbii syntaxFormula0067 syntaxFormula0084 e p0122
  have p0124 := @g_bitri syntaxFormula0069 syntaxFormula0068 syntaxFormula0085 p0061 p0123
  have p0125 := @g_notbii syntaxFormula0069 syntaxFormula0085 p0124
  have p0126 := @g_elcompl syntaxClass0055 syntaxClass0005 p0050
  have freshnessCertificate0368 : e ∉ (((Class.cv a)).fv) ∪ (((syn_csn (.cv x))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0326 freshnessCertificate0322))
  have freshnessCertificate0369 : e ∉ ((syn_cun (.cv a) (syn_csn (.cv x)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun];
      exact freshnessCertificate0368)
  have p0127 :=
    @g_dfcleq e (.cv w) (syn_cun (.cv a) (syn_csn (.cv x)))
      (by exact freshnessCertificate0315) (by exact freshnessCertificate0369)
  have p0128 :=
    @g_alex (syn_wb (.objMem e w) (.classMem (.cv e) (syn_cun (.cv a) (syn_csn (.cv x)))))
      e
  have p0129_e00_recanon :
    Nominal.NPrf
      (syn_wb (.classEq (.cv w) (syn_cun (.cv a) (syn_csn (.cv x)))) (.all e
          (syn_wb (.objMem e w) (.classMem (.cv e) (syn_cun (.cv a) (syn_csn (.cv x))))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [syn_wb, syn_cun, syn_cnin, syn_wnan, syn_wa, syn_ccompl, syn_csn]
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
      p0127
  have p0129 :=
    @g_bitri (.classEq (.cv w) (syn_cun (.cv a) (syn_csn (.cv x))))
      (.all e (syn_wb (.objMem e w) (.classMem (.cv e) (syn_cun (.cv a) (syn_csn (.cv x))))))
      (.neg syntaxFormula0085) p0129_e00_recanon p0128
  have p0130 :=
    @g_n_3bitr4i (.neg syntaxFormula0069) (.neg syntaxFormula0085) syntaxFormula0086
      (.classEq (.cv w) (syn_cun (.cv a) (syn_csn (.cv x)))) p0125 p0126 p0129
  have p0131 :=
    @g_otkelins2k (syn_csn (syn_csn (syn_csn (.cv w))))
      (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))) (syn_copk (syn_csn (.cv a)) (.cv m))
      syntaxClass0018 p0073 p0028 p0016
  have p0132 :=
    @g_otkelins2k (syn_csn (.cv w)) (syn_csn (.cv a)) (.cv m) syntaxClass0017 p0079 p0012
      p0000
  have p0133 :=
    @g_ancom (.classMem (syn_copk (syn_csn (.cv w)) (.cv t)) (syn_cssetk))
      syntaxFormula0087
  have p0134 := @g_vex t
  have p0135 := @g_opkelcnvk (.cv t) (.cv m) syntaxClass0015 p0134 p0000
  have p0136 := @g_opkelimagekg (.cv m) (.cv t) syntaxClass0014 (syn_cvv) (syn_cvv)
  have p0137 :=
    @g_mp2an (.classMem (.cv m) (syn_cvv)) (.classMem (.cv t) (syn_cvv))
      (syn_wb syntaxFormula0088 syntaxFormula0090) p0000 p0134 p0136
  have p0138 := @g_dfaddc2 (.cv m) (syn_c1c)
  have p0139 := @g_eqeq2i (syn_cplc (.cv m) (syn_c1c)) syntaxClass0089 (.cv t) p0138
  have p0140 :=
    @g_bicomi (.classEq (.cv t) (syn_cplc (.cv m) (syn_c1c))) syntaxFormula0090 p0139
  have p0141 :=
    @g_bitri syntaxFormula0088 syntaxFormula0090
      (.classEq (.cv t) (syn_cplc (.cv m) (syn_c1c))) p0137 p0140
  have p0142 :=
    @g_bitri syntaxFormula0087 syntaxFormula0088
      (.classEq (.cv t) (syn_cplc (.cv m) (syn_c1c))) p0135 p0141
  have p0143 := @g_elssetk (.cv w) (.cv t) p0082 p0134
  have p0144_e01_recanon :
    Nominal.NPrf
      (syn_wb (.classMem (syn_copk (syn_csn (.cv w)) (.cv t)) (syn_cssetk)) (.objMem w t)) :=
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
      p0143
  have p0144 :=
    @g_anbi12i syntaxFormula0087 (.classEq (.cv t) (syn_cplc (.cv m) (syn_c1c)))
      (.classMem (syn_copk (syn_csn (.cv w)) (.cv t)) (syn_cssetk)) (.objMem w t) p0142
      p0144_e01_recanon
  have p0145 :=
    @g_bitri syntaxFormula0091
      (syn_wa syntaxFormula0087 (.classMem (syn_copk (syn_csn (.cv w)) (.cv t)) (syn_cssetk)))
      (syn_wa (.classEq (.cv t) (syn_cplc (.cv m) (syn_c1c))) (.objMem w t)) p0133 p0144
  have p0146 :=
    @g_exbii syntaxFormula0091
      (syn_wa (.classEq (.cv t) (syn_cplc (.cv m) (syn_c1c))) (.objMem w t)) t p0145
  have p0147 :=
    @g_opkelcok t (syn_csn (.cv w)) (.cv m) syntaxClass0016 (syn_cssetk)
      (by exact freshnessCertificate0305) (by exact freshnessCertificate0067)
      (by exact freshnessCertificate0049) (by exact freshnessCertificate0000) p0079 p0000
  have p0148 := @g_n_1cex
  have p0149 := @g_addcex (.cv m) (syn_c1c) p0000 p0148
  have freshnessCertificate0370 : t ∉ (((Class.cv m)).fv) ∪ (((syn_c1c)).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0067 freshnessCertificate0016))
  have freshnessCertificate0371 : t ∉ ((syn_cplc (.cv m) (syn_c1c))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc];
      exact freshnessCertificate0370)
  have p0150 :=
    @g_clel3 t (.cv w) (syn_cplc (.cv m) (syn_c1c)) (by exact freshnessCertificate0304)
      (by exact freshnessCertificate0371) p0149
  have p0151_e02_recanon :
    Nominal.NPrf
      (syn_wb (.classMem (.cv w) (syn_cplc (.cv m) (syn_c1c))) (syn_wex t
          (syn_wa (.classEq (.cv t) (syn_cplc (.cv m) (syn_c1c))) (.objMem w t)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [syn_wb, syn_cplc, syn_wrex, syn_wex, syn_wa, syn_c1c]
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
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
      p0150
  have p0151 :=
    @g_n_3bitr4i (syn_wex t syntaxFormula0091)
      (syn_wex t (syn_wa (.classEq (.cv t) (syn_cplc (.cv m) (syn_c1c))) (.objMem w t)))
      syntaxFormula0092 (.classMem (.cv w) (syn_cplc (.cv m) (syn_c1c))) p0146 p0147
      p0151_e02_recanon
  have p0152 :=
    @g_bitri syntaxFormula0093 syntaxFormula0092
      (.classMem (.cv w) (syn_cplc (.cv m) (syn_c1c))) p0132 p0151
  have p0153 :=
    @g_bitri syntaxFormula0094 syntaxFormula0093
      (.classMem (.cv w) (syn_cplc (.cv m) (syn_c1c))) p0131 p0152
  have p0154 :=
    @g_anbi12i syntaxFormula0086 (.classEq (.cv w) (syn_cun (.cv a) (syn_csn (.cv x))))
      syntaxFormula0094 (.classMem (.cv w) (syn_cplc (.cv m) (syn_c1c))) p0130 p0153
  have p0155 :=
    @g_bitri syntaxFormula0056 (syn_wa syntaxFormula0086 syntaxFormula0094)
      syntaxFormula0095 p0049 p0154
  have p0156 := @g_bitri syntaxFormula0053 syntaxFormula0056 syntaxFormula0095 p0048 p0155
  have p0157 := @g_exbii syntaxFormula0053 syntaxFormula0095 w p0156
  have p0158 := @g_bitri syntaxFormula0048 syntaxFormula0054 syntaxFormula0096 p0044 p0157
  have p0159 := @g_bitri syntaxFormula0097 syntaxFormula0048 syntaxFormula0096 p0035 p0158
  have freshnessCertificate0372 : w ∉ (((Class.cv a)).fv) ∪ (((syn_csn (.cv x))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0237 freshnessCertificate0233))
  have freshnessCertificate0373 : w ∉ ((syn_cun (.cv a) (syn_csn (.cv x)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun];
      exact freshnessCertificate0372)
  have freshnessCertificate0374 : w ∉ (((Class.cv m)).fv) ∪ (((syn_c1c)).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0239 freshnessCertificate0262))
  have freshnessCertificate0375 : w ∉ ((syn_cplc (.cv m) (syn_c1c))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc];
      exact freshnessCertificate0374)
  have p0160 :=
    (NFChoice.DirectNominalPrf.Nominal.DefinitionLeafHandlersCanonical001.dfClelOfDV w
      (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cplc (.cv m) (syn_c1c))
      (by exact freshnessCertificate0373) (by exact freshnessCertificate0375))
  have p0161 :=
    @g_bitr4i syntaxFormula0097 syntaxFormula0096
      (.classMem (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cplc (.cv m) (syn_c1c))) p0159
      p0160
  have p0162 := @g_snex (syn_csn (.cv x))
  have p0163 :=
    @g_otkelins3k (syn_csn (syn_csn (.cv x))) (syn_csn (.cv a)) (.cv m)
      (syn_csik (syn_cssetk)) p0162 p0012 p0000
  have p0164 := @g_snex (.cv x)
  have p0165 := @g_opksnelsik (syn_csn (.cv x)) (.cv a) (syn_cssetk) p0164 p0095
  have p0166 := @g_vex x
  have p0167 := @g_elssetk (.cv x) (.cv a) p0166 p0095
  have p0168_e01_recanon :
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
      p0167
  have p0168 :=
    @g_bitri
      (.classMem (syn_copk (syn_csn (syn_csn (.cv x))) (syn_csn (.cv a)))
        (syn_csik (syn_cssetk)))
      (.classMem (syn_copk (syn_csn (.cv x)) (.cv a)) (syn_cssetk)) (.objMem x a) p0165
      p0168_e01_recanon
  have p0169 :=
    @g_bitri syntaxFormula0098
      (.classMem (syn_copk (syn_csn (syn_csn (.cv x))) (syn_csn (.cv a)))
        (syn_csik (syn_cssetk)))
      (.objMem x a) p0163 p0168
  have p0170 := @g_notbii syntaxFormula0098 (.objMem x a) p0169
  have p0171 :=
    @g_anbi12i syntaxFormula0097
      (.classMem (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cplc (.cv m) (syn_c1c)))
      (.neg syntaxFormula0098) (.neg (.objMem x a)) p0161 p0170
  have p0172 :=
    @g_bitri syntaxFormula0099 (syn_wa syntaxFormula0097 (.neg syntaxFormula0098))
      (syn_wa (.classMem (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cplc (.cv m) (syn_c1c)))
        (.neg (.objMem x a)))
      p0033 p0171
  have p0173 :=
    @g_ancom (.classMem (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cplc (.cv m) (syn_c1c)))
      (.neg (.objMem x a))
  have p0174 :=
    @g_bitri syntaxFormula0099
      (syn_wa (.classMem (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cplc (.cv m) (syn_c1c)))
        (.neg (.objMem x a)))
      syntaxFormula0100 p0172 p0173
  have p0175 :=
    @g_opkelxpk (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))
      (syn_copk (syn_csn (.cv a)) (.cv m)) (syn_cvv) (syn_cssetk) p0028 p0016
  have p0176 :=
    @g_mpbiran syntaxFormula0101
      (.classMem (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))) (syn_cvv))
      (.classMem (syn_copk (syn_csn (.cv a)) (.cv m)) (syn_cssetk)) p0028 p0175
  have p0177 := @g_elssetk (.cv a) (.cv m) p0095 p0000
  have p0178_e01_recanon :
    Nominal.NPrf
      (syn_wb (.classMem (syn_copk (syn_csn (.cv a)) (.cv m)) (syn_cssetk)) (.objMem a m)) :=
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
      p0177
  have p0178 :=
    @g_bitri syntaxFormula0101
      (.classMem (syn_copk (syn_csn (.cv a)) (.cv m)) (syn_cssetk)) (.objMem a m) p0176
      p0178_e01_recanon
  have p0179 := @g_notbii syntaxFormula0101 (.objMem a m) p0178
  have p0180 :=
    @g_anbi12i syntaxFormula0099 syntaxFormula0100 (.neg syntaxFormula0101)
      (.neg (.objMem a m)) p0174 p0179
  have p0181 :=
    @g_bitri syntaxFormula0045 (syn_wa syntaxFormula0099 (.neg syntaxFormula0101))
      (syn_wa syntaxFormula0100 (.neg (.objMem a m))) p0032 p0180
  have p0182 := @g_annim syntaxFormula0100 (.objMem a m)
  have p0183 :=
    @g_bitri syntaxFormula0045 (syn_wa syntaxFormula0100 (.neg (.objMem a m)))
      syntaxFormula0103 p0181 p0182
  have p0184 := @g_bitri syntaxFormula0042 syntaxFormula0045 syntaxFormula0103 p0031 p0183
  have p0185 := @g_exbii syntaxFormula0042 syntaxFormula0103 x p0184
  have p0186 :=
    @g_bitri syntaxFormula0035 syntaxFormula0043 (syn_wex x syntaxFormula0103) p0027 p0185
  have p0187 := @g_exnal syntaxFormula0102 x
  have p0188 :=
    @g_bitri syntaxFormula0035 (syn_wex x syntaxFormula0103) syntaxFormula0105 p0186 p0187
  have p0189 := @g_bitri syntaxFormula0031 syntaxFormula0035 syntaxFormula0105 p0015 p0188
  have p0190 := @g_exbii syntaxFormula0031 syntaxFormula0105 a p0189
  have p0191 := @g_bitri syntaxFormula0034 syntaxFormula0032 syntaxFormula0106 p0011 p0190
  have p0192 := @g_notbii syntaxFormula0034 syntaxFormula0106 p0191
  have p0193 := @g_elcompl (.cv m) syntaxClass0033 p0000
  have p0194 := @g_alex syntaxFormula0104 a
  have p0195 :=
    @g_n_3bitr4i (.neg syntaxFormula0034) (.neg syntaxFormula0106)
      (.classMem (.cv m) syntaxClass0107) syntaxFormula0108 p0192 p0193 p0194
  have freshnessCertificate0376 : m ∉ ((syn_cssetk)).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk];
      exact (show m ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))
  have freshnessCertificate0377 : m ∉ ((syn_csik (syn_cssetk))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0376)
  have freshnessCertificate0378 : m ∉ ((syn_csik (syn_csik (syn_cssetk)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0377)
  have freshnessCertificate0379 :
    m ∉ ((syn_csik (syn_csik (syn_csik (syn_cssetk))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0378)
  have freshnessCertificate0380 :
    m ∉ ((syn_csik (syn_csik (syn_csik (syn_csik (syn_cssetk)))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0379)
  have freshnessCertificate0381 :
    m ∉ ((syn_csik (syn_csik (syn_csik (syn_csik (syn_csik (syn_cssetk))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0380)
  have freshnessCertificate0382 : m ∉ (syntaxClass0000).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0381)
  have freshnessCertificate0383 : m ∉ ((syn_cins3k (syn_csik (syn_cssetk)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0377)
  have freshnessCertificate0384 :
    m ∉ ((syn_cins2k (syn_cins3k (syn_csik (syn_cssetk))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0383)
  have freshnessCertificate0385 : m ∉ ((syn_cidk)).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cidk];
      exact (show m ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))
  have freshnessCertificate0386 : m ∉ ((syn_cins3k (syn_cidk))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0385)
  have freshnessCertificate0387 :
    m ∉
      (((syn_cins2k (syn_cins3k (syn_csik (syn_cssetk))))).fv) ∪
        (((syn_cins3k (syn_cidk))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0384 freshnessCertificate0386))
  have freshnessCertificate0388 : m ∉ (syntaxClass0001).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun];
      exact freshnessCertificate0387)
  have freshnessCertificate0389 : m ∉ (syntaxClass0002).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0388)
  have freshnessCertificate0390 : m ∉ ((syntaxClass0000).fv) ∪ ((syntaxClass0002).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0382 freshnessCertificate0389))
  have freshnessCertificate0391 : m ∉ (syntaxClass0003).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif];
      exact freshnessCertificate0390)
  have freshnessCertificate0392 : m ∉ ((syn_c1c)).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c];
      exact (show m ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))
  have freshnessCertificate0393 : m ∉ ((syn_cpw1 (syn_c1c))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0392)
  have freshnessCertificate0394 : m ∉ ((syn_cpw1 (syn_cpw1 (syn_c1c)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0393)
  have freshnessCertificate0395 : m ∉ ((syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0394)
  have freshnessCertificate0396 :
    m ∉ ((syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0395)
  have freshnessCertificate0397 :
    m ∉ ((syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0396)
  have freshnessCertificate0398 :
    m ∉
      ((syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0397)
  have freshnessCertificate0399 : m ∉ (syntaxClass0004).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0398)
  have freshnessCertificate0400 : m ∉ ((syntaxClass0003).fv) ∪ ((syntaxClass0004).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0391 freshnessCertificate0399))
  have freshnessCertificate0401 : m ∉ (syntaxClass0005).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak];
      exact freshnessCertificate0400)
  have freshnessCertificate0402 : m ∉ (syntaxClass0006).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl];
      exact freshnessCertificate0401)
  have freshnessCertificate0403 : m ∉ ((syn_cins3k (syn_cssetk))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0376)
  have freshnessCertificate0404 : m ∉ ((syn_cins2k (syn_cssetk))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0376)
  have freshnessCertificate0405 :
    m ∉ (((syn_cins3k (syn_cssetk))).fv) ∪ (((syn_cins2k (syn_cssetk))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0403 freshnessCertificate0404))
  have freshnessCertificate0406 :
    m ∉ ((syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin];
      exact freshnessCertificate0405)
  have freshnessCertificate0407 :
    m ∉
      (((syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))).fv) ∪
        (((syn_cpw1 (syn_cpw1 (syn_c1c)))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0406 freshnessCertificate0394))
  have freshnessCertificate0408 : m ∉ (syntaxClass0007).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak];
      exact freshnessCertificate0407)
  have freshnessCertificate0409 : m ∉ (syntaxClass0008).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl];
      exact freshnessCertificate0408)
  have freshnessCertificate0410 : m ∉ (syntaxClass0009).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0409)
  have freshnessCertificate0411 : m ∉ ((syn_cins2k (syn_cins2k (syn_cssetk)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0404)
  have freshnessCertificate0412 : m ∉ ((syn_cins2k (syn_cins3k (syn_cssetk)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0403)
  have freshnessCertificate0413 :
    m ∉ ((syn_cins3k (syn_csik (syn_csik (syn_cssetk))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0378)
  have freshnessCertificate0414 :
    m ∉
      (((syn_cins2k (syn_cins3k (syn_cssetk)))).fv) ∪
        (((syn_cins3k (syn_csik (syn_csik (syn_cssetk))))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0412 freshnessCertificate0413))
  have freshnessCertificate0415 : m ∉ (syntaxClass0010).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun];
      exact freshnessCertificate0414)
  have freshnessCertificate0416 :
    m ∉ (((syn_cins2k (syn_cins2k (syn_cssetk)))).fv) ∪ ((syntaxClass0010).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0411 freshnessCertificate0415))
  have freshnessCertificate0417 : m ∉ (syntaxClass0011).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif];
      exact freshnessCertificate0416)
  have freshnessCertificate0418 :
    m ∉
      ((syntaxClass0011).fv) ∪
        (((syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0417 freshnessCertificate0396))
  have freshnessCertificate0419 : m ∉ (syntaxClass0012).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak];
      exact freshnessCertificate0418)
  have freshnessCertificate0420 : m ∉ ((syntaxClass0009).fv) ∪ ((syntaxClass0012).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0410 freshnessCertificate0419))
  have freshnessCertificate0421 : m ∉ (syntaxClass0013).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif];
      exact freshnessCertificate0420)
  have freshnessCertificate0422 :
    m ∉ ((syntaxClass0013).fv) ∪ (((syn_cpw1 (syn_cpw1 (syn_c1c)))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0421 freshnessCertificate0394))
  have freshnessCertificate0423 : m ∉ (syntaxClass0014).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak];
      exact freshnessCertificate0422)
  have freshnessCertificate0424 : m ∉ (syntaxClass0015).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimagek];
      exact freshnessCertificate0423)
  have freshnessCertificate0425 : m ∉ (syntaxClass0016).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk];
      exact freshnessCertificate0424)
  have freshnessCertificate0426 : m ∉ ((syntaxClass0016).fv) ∪ (((syn_cssetk)).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0425 freshnessCertificate0376))
  have freshnessCertificate0427 : m ∉ (syntaxClass0017).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccomk];
      exact freshnessCertificate0426)
  have freshnessCertificate0428 : m ∉ (syntaxClass0018).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0427)
  have freshnessCertificate0429 : m ∉ (syntaxClass0019).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0428)
  have freshnessCertificate0430 : m ∉ ((syntaxClass0006).fv) ∪ ((syntaxClass0019).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0402 freshnessCertificate0429))
  have freshnessCertificate0431 : m ∉ (syntaxClass0020).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin];
      exact freshnessCertificate0430)
  have freshnessCertificate0432 :
    m ∉
      ((syntaxClass0020).fv) ∪
        (((syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0431 freshnessCertificate0396))
  have freshnessCertificate0433 : m ∉ (syntaxClass0021).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak];
      exact freshnessCertificate0432)
  have freshnessCertificate0434 :
    m ∉ ((syntaxClass0021).fv) ∪ (((syn_cins3k (syn_csik (syn_cssetk)))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0433 freshnessCertificate0383))
  have freshnessCertificate0435 : m ∉ (syntaxClass0022).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif];
      exact freshnessCertificate0434)
  have freshnessCertificate0436 : m ∉ ((syn_cvv)).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv];
      exact (show m ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))
  have freshnessCertificate0437 : m ∉ (((syn_cvv)).fv) ∪ (((syn_cssetk)).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0436 freshnessCertificate0376))
  have freshnessCertificate0438 : m ∉ ((syn_cxpk (syn_cvv) (syn_cssetk))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk];
      exact freshnessCertificate0437)
  have freshnessCertificate0439 :
    m ∉ ((syntaxClass0022).fv) ∪ (((syn_cxpk (syn_cvv) (syn_cssetk))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0435 freshnessCertificate0438))
  have freshnessCertificate0440 : m ∉ (syntaxClass0023).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif];
      exact freshnessCertificate0439)
  have freshnessCertificate0441 :
    m ∉ ((syntaxClass0023).fv) ∪ (((syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0440 freshnessCertificate0395))
  have freshnessCertificate0442 : m ∉ (syntaxClass0024).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak];
      exact freshnessCertificate0441)
  have freshnessCertificate0443 : m ∉ ((syntaxClass0024).fv) ∪ (((syn_c1c)).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0442 freshnessCertificate0392))
  have freshnessCertificate0444 : m ∉ (syntaxClass0033).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak];
      exact freshnessCertificate0443)
  have freshnessCertificate0445 : m ∉ (syntaxClass0107).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl];
      exact freshnessCertificate0444)
  have p0196 :=
    @g_eqabi syntaxFormula0108 m syntaxClass0107 (by exact freshnessCertificate0445) p0195
  have p0197 := @g_ssetkex
  have p0198 := @g_sikex (syn_cssetk) p0197
  have p0199 := @g_sikex (syn_csik (syn_cssetk)) p0198
  have p0200 := @g_sikex (syn_csik (syn_csik (syn_cssetk))) p0199
  have p0201 := @g_sikex (syn_csik (syn_csik (syn_csik (syn_cssetk)))) p0200
  have p0202 := @g_sikex (syn_csik (syn_csik (syn_csik (syn_csik (syn_cssetk))))) p0201
  have p0203 :=
    @g_ins3kex (syn_csik (syn_csik (syn_csik (syn_csik (syn_csik (syn_cssetk)))))) p0202
  have p0204 := @g_ins3kex (syn_csik (syn_cssetk)) p0198
  have p0205 := @g_ins2kex (syn_cins3k (syn_csik (syn_cssetk))) p0204
  have p0206 := @g_idkex
  have p0207 := @g_ins3kex (syn_cidk) p0206
  have p0208 :=
    @g_unex (syn_cins2k (syn_cins3k (syn_csik (syn_cssetk)))) (syn_cins3k (syn_cidk))
      p0205 p0207
  have p0209 := @g_ins2kex syntaxClass0001 p0208
  have p0210 := @g_symdifex syntaxClass0000 syntaxClass0002 p0203 p0209
  have p0212 := @g_pw1ex (syn_c1c) p0148
  have p0213 := @g_pw1ex (syn_cpw1 (syn_c1c)) p0212
  have p0214 := @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_c1c))) p0213
  have p0215 := @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))) p0214
  have p0216 := @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))) p0215
  have p0217 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))) p0216
  have p0218 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
      p0217
  have p0219 := @g_imakex syntaxClass0003 syntaxClass0004 p0210 p0218
  have p0220 := @g_complex syntaxClass0005 p0219
  have p0221 := @g_addcexlem
  have p0222 := @g_imakex syntaxClass0013 (syn_cpw1 (syn_cpw1 (syn_c1c))) p0221 p0213
  have p0223 := @g_imagekex syntaxClass0014 p0222
  have p0224 := @g_cnvkex syntaxClass0015 p0223
  have p0226 := @g_cokex syntaxClass0016 (syn_cssetk) p0224 p0197
  have p0227 := @g_ins2kex syntaxClass0017 p0226
  have p0228 := @g_ins2kex syntaxClass0018 p0227
  have p0229 := @g_inex syntaxClass0006 syntaxClass0019 p0220 p0228
  have p0230 :=
    @g_imakex syntaxClass0020 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))) p0229
      p0215
  have p0231 := @g_difex syntaxClass0021 (syn_cins3k (syn_csik (syn_cssetk))) p0230 p0204
  have p0232 := @g_vvex
  have p0234 := @g_xpkex (syn_cvv) (syn_cssetk) p0232 p0197
  have p0235 := @g_difex syntaxClass0022 (syn_cxpk (syn_cvv) (syn_cssetk)) p0231 p0234
  have p0236 :=
    @g_imakex syntaxClass0023 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))) p0235 p0214
  have p0238 := @g_imakex syntaxClass0024 (syn_c1c) p0236 p0148
  have p0239 := @g_complex syntaxClass0033 p0238
  have p0240 :=
    @g_eqeltrri syntaxClass0107 (.cab m syntaxFormula0108) (syn_cvv) p0196 p0239
  exact p0240


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk009StructuralPart033`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_nnsucelrlem2 (A : Class) (B : Class) :
    Nominal.NPrf
      (.imp (.neg (.classMem B A))
        (.classEq (syn_cdif (syn_cun A (syn_csn B)) (syn_csn B)) A)) :=
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
  have p0000 := @g_eldifsn (.cv x) (syn_cun A (syn_csn B)) B
  have p0001 := @g_elun (.cv x) A (syn_csn B)
  have p0002 := @g_elsn x B (by exact (show x ∉ (B).fv from (by exact fresh_x_not_B)))
  have p0003 :=
    @g_orbi2i (.classMem (.cv x) (syn_csn B)) (.classEq (.cv x) B) (.classMem (.cv x) A)
      p0002
  have p0004 :=
    @g_bitri (.classMem (.cv x) (syn_cun A (syn_csn B)))
      (syn_wo (.classMem (.cv x) A) (.classMem (.cv x) (syn_csn B)))
      (syn_wo (.classMem (.cv x) A) (.classEq (.cv x) B)) p0001 p0003
  have p0005 := (Nominal.biimpRefl (syn_wne (.cv x) B))
  have p0006 :=
    @g_anbi12i (.classMem (.cv x) (syn_cun A (syn_csn B)))
      (syn_wo (.classMem (.cv x) A) (.classEq (.cv x) B)) (syn_wne (.cv x) B)
      (.neg (.classEq (.cv x) B)) p0004 p0005
  have p0007 := @g_pm5_61 (.classMem (.cv x) A) (.classEq (.cv x) B)
  have p0008 :=
    @g_n_3bitri (.classMem (.cv x) (syn_cdif (syn_cun A (syn_csn B)) (syn_csn B)))
      (syn_wa (.classMem (.cv x) (syn_cun A (syn_csn B))) (syn_wne (.cv x) B))
      (syn_wa (syn_wo (.classMem (.cv x) A) (.classEq (.cv x) B)) (.neg (.classEq (.cv x) B)))
      (syn_wa (.classMem (.cv x) A) (.neg (.classEq (.cv x) B))) p0000 p0006 p0007
  have p0009 := @g_ancom (.classMem (.cv x) A) (.neg (.classEq (.cv x) B))
  have p0010 :=
    @g_bitri (.classMem (.cv x) (syn_cdif (syn_cun A (syn_csn B)) (syn_csn B)))
      (syn_wa (.classMem (.cv x) A) (.neg (.classEq (.cv x) B)))
      (syn_wa (.neg (.classEq (.cv x) B)) (.classMem (.cv x) A)) p0008 p0009
  have p0011 := @g_eleq1 (.cv x) B A
  have p0012 :=
    @g_biimpcd (.classEq (.cv x) B) (.classMem (.cv x) A) (.classMem B A) p0011
  have p0013 := @g_con3d (.classMem (.cv x) A) (.classEq (.cv x) B) (.classMem B A) p0012
  have p0014 :=
    @g_com12 (.classMem (.cv x) A) (.neg (.classMem B A)) (.neg (.classEq (.cv x) B))
      p0013
  have p0015 :=
    @g_pm4_71rd (.neg (.classMem B A)) (.classMem (.cv x) A) (.neg (.classEq (.cv x) B))
      p0014
  have p0016 :=
    @g_bicomd (.neg (.classMem B A)) (.classMem (.cv x) A)
      (syn_wa (.neg (.classEq (.cv x) B)) (.classMem (.cv x) A)) p0015
  have p0017 :=
    @g_syl5bb (.classMem (.cv x) (syn_cdif (syn_cun A (syn_csn B)) (syn_csn B)))
      (syn_wa (.neg (.classEq (.cv x) B)) (.classMem (.cv x) A)) (.neg (.classMem B A))
      (.classMem (.cv x) A) p0010 p0016
  have freeVariableCertificate0 :
    x ∉ ((syn_cdif (syn_cun A (syn_csn B)) (syn_csn B))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
      fresh_x_not_A, fresh_x_not_B, or_false, not_false_eq_true]
  have freeVariableCertificate1 : x ∉ ((Wff.neg (.classMem B A))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_neg,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, Finset.mem_union, fresh_x_not_B,
      fresh_x_not_A, or_false, not_false_eq_true]
  have p0018 :=
    @g_eqrdv (.neg (.classMem B A)) x (syn_cdif (syn_cun A (syn_csn B)) (syn_csn B)) A
      freeVariableCertificate0 (by exact (show x ∉ (A).fv from (by exact fresh_x_not_A)))
      freeVariableCertificate1 p0017
  exact p0018

@[expose]
noncomputable def g_nnsucelrlem3 (A : Class) (B : Class) (X : Class) (Y : Class)
    (hyp_nnsucelrlem3_1 : Nominal.NPrf (.classMem X (syn_cvv))) :
    Nominal.NPrf
      (.imp (syn_w3a (syn_wne X Y) (.classEq (syn_cun A (syn_csn X)) (syn_cun B (syn_csn Y)))
          (.neg (.classMem Y B)))
        (.classEq B (syn_cun (syn_cdif A (syn_csn Y)) (syn_csn X)))) :=
  by
  have p0000 := @g_indir B (syn_csn Y) (syn_ccompl (syn_csn Y))
  have p0001 := (Nominal.classEqRefl (syn_cdif B (syn_csn Y)))
  have p0002 :=
    @g_eqcomi (syn_cdif B (syn_csn Y)) (syn_cin B (syn_ccompl (syn_csn Y))) p0001
  have p0003 := @g_incompl (syn_csn Y)
  have p0004 :=
    @g_uneq12i (syn_cin B (syn_ccompl (syn_csn Y))) (syn_cdif B (syn_csn Y))
      (syn_cin (syn_csn Y) (syn_ccompl (syn_csn Y))) (syn_c0) p0002 p0003
  have p0005 := @g_un0 (syn_cdif B (syn_csn Y))
  have p0006 :=
    @g_eqtri
      (syn_cun (syn_cin B (syn_ccompl (syn_csn Y)))
        (syn_cin (syn_csn Y) (syn_ccompl (syn_csn Y))))
      (syn_cun (syn_cdif B (syn_csn Y)) (syn_c0)) (syn_cdif B (syn_csn Y)) p0004 p0005
  have p0007 :=
    @g_eqtri (syn_cin (syn_cun B (syn_csn Y)) (syn_ccompl (syn_csn Y)))
      (syn_cun (syn_cin B (syn_ccompl (syn_csn Y)))
        (syn_cin (syn_csn Y) (syn_ccompl (syn_csn Y))))
      (syn_cdif B (syn_csn Y)) p0000 p0006
  have p0008 := @g_difsn Y B
  have p0009 :=
    @g_n_3ad2ant3 (.neg (.classMem Y B)) (syn_wne X Y)
      (.classEq (syn_cdif B (syn_csn Y)) B)
      (.classEq (syn_cun A (syn_csn X)) (syn_cun B (syn_csn Y))) p0008
  have p0010 :=
    @g_syl5req
      (syn_w3a (syn_wne X Y) (.classEq (syn_cun A (syn_csn X)) (syn_cun B (syn_csn Y)))
        (.neg (.classMem Y B)))
      (syn_cin (syn_cun B (syn_csn Y)) (syn_ccompl (syn_csn Y))) (syn_cdif B (syn_csn Y))
      B p0007 p0009
  have p0011 :=
    @g_simp2 (syn_wne X Y) (.classEq (syn_cun A (syn_csn X)) (syn_cun B (syn_csn Y)))
      (.neg (.classMem Y B))
  have p0012 := (Nominal.biimpRefl (syn_wne X Y))
  have p0013 := @g_biimpi (syn_wne X Y) (.neg (.classEq X Y)) p0012
  have p0014 :=
    @g_n_3ad2ant1 (syn_wne X Y) (.classEq (syn_cun A (syn_csn X)) (syn_cun B (syn_csn Y)))
      (.neg (.classEq X Y)) (.neg (.classMem Y B)) p0013
  have p0015 := @g_elcompl X (syn_csn Y) hyp_nnsucelrlem3_1
  have p0016 := @g_elsnc X Y hyp_nnsucelrlem3_1
  have p0017 :=
    @g_xchbinx (.classMem X (syn_ccompl (syn_csn Y))) (.classMem X (syn_csn Y))
      (.classEq X Y) p0015 p0016
  have p0018 := @g_snss X (syn_ccompl (syn_csn Y)) hyp_nnsucelrlem3_1
  have p0019 :=
    @g_bitr3i (.neg (.classEq X Y)) (.classMem X (syn_ccompl (syn_csn Y)))
      (syn_wss (syn_csn X) (syn_ccompl (syn_csn Y))) p0017 p0018
  have p0020 :=
    @g_sylib
      (syn_w3a (syn_wne X Y) (.classEq (syn_cun A (syn_csn X)) (syn_cun B (syn_csn Y)))
        (.neg (.classMem Y B)))
      (.neg (.classEq X Y)) (syn_wss (syn_csn X) (syn_ccompl (syn_csn Y))) p0014 p0019
  have p0021 := @g_ssequn2 (syn_csn X) (syn_ccompl (syn_csn Y))
  have p0022 :=
    @g_sylib
      (syn_w3a (syn_wne X Y) (.classEq (syn_cun A (syn_csn X)) (syn_cun B (syn_csn Y)))
        (.neg (.classMem Y B)))
      (syn_wss (syn_csn X) (syn_ccompl (syn_csn Y)))
      (.classEq (syn_cun (syn_ccompl (syn_csn Y)) (syn_csn X)) (syn_ccompl (syn_csn Y)))
      p0020 p0021
  have p0023 :=
    @g_ineq12d
      (syn_w3a (syn_wne X Y) (.classEq (syn_cun A (syn_csn X)) (syn_cun B (syn_csn Y)))
        (.neg (.classMem Y B)))
      (syn_cun A (syn_csn X)) (syn_cun B (syn_csn Y))
      (syn_cun (syn_ccompl (syn_csn Y)) (syn_csn X)) (syn_ccompl (syn_csn Y)) p0011 p0022
  have p0024 :=
    @g_eqtr4d
      (syn_w3a (syn_wne X Y) (.classEq (syn_cun A (syn_csn X)) (syn_cun B (syn_csn Y)))
        (.neg (.classMem Y B)))
      B (syn_cin (syn_cun B (syn_csn Y)) (syn_ccompl (syn_csn Y)))
      (syn_cin (syn_cun A (syn_csn X)) (syn_cun (syn_ccompl (syn_csn Y)) (syn_csn X)))
      p0010 p0023
  have p0025 := (Nominal.classEqRefl (syn_cdif A (syn_csn Y)))
  have p0026 :=
    @g_uneq1i (syn_cdif A (syn_csn Y)) (syn_cin A (syn_ccompl (syn_csn Y))) (syn_csn X)
      p0025
  have p0027 := @g_undir A (syn_ccompl (syn_csn Y)) (syn_csn X)
  have p0028 :=
    @g_eqtri (syn_cun (syn_cdif A (syn_csn Y)) (syn_csn X))
      (syn_cun (syn_cin A (syn_ccompl (syn_csn Y))) (syn_csn X))
      (syn_cin (syn_cun A (syn_csn X)) (syn_cun (syn_ccompl (syn_csn Y)) (syn_csn X)))
      p0026 p0027
  have p0029 :=
    @g_syl6eqr
      (syn_w3a (syn_wne X Y) (.classEq (syn_cun A (syn_csn X)) (syn_cun B (syn_csn Y)))
        (.neg (.classMem Y B)))
      B (syn_cin (syn_cun A (syn_csn X)) (syn_cun (syn_ccompl (syn_csn Y)) (syn_csn X)))
      (syn_cun (syn_cdif A (syn_csn Y)) (syn_csn X)) p0024 p0028
  exact p0029

@[expose]
noncomputable def g_nnsucelrlem4 (A : Class) (B : Class) :
    Nominal.NPrf
      (.imp (.classMem A B) (.classEq (syn_cun (syn_cdif B (syn_csn A)) (syn_csn A)) B)) :=
  by
  have p0000 := @g_undif1 B (syn_csn A)
  have p0001 := @g_snssi A B
  have p0002 := @g_ssequn2 (syn_csn A) B
  have p0003 :=
    @g_sylib (.classMem A B) (syn_wss (syn_csn A) B) (.classEq (syn_cun B (syn_csn A)) B)
      p0001 p0002
  have p0004 :=
    @g_syl5eq (.classMem A B) (syn_cun (syn_cdif B (syn_csn A)) (syn_csn A))
      (syn_cun B (syn_csn A)) B p0000 p0003
  exact p0004


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk009StructuralPart034`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_nnsucelr (A : Class) (M : Class) (X : Class)
    (hyp_nnsucelr_1 : Nominal.NPrf (.classMem A (syn_cvv)))
    (hyp_nnsucelr_2 : Nominal.NPrf (.classMem X (syn_cvv))) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem M (syn_cnnc)) (syn_wa (.neg (.classMem X A))
            (.classMem (syn_cun A (syn_csn X)) (syn_cplc M (syn_c1c))))) (.classMem A M)) :=
  by
  let proofSupport : Finset Var := A.fv ∪ M.fv ∪ X.fv
  let x : Var := freshVar proofSupport 0
  let a : Var := freshVar proofSupport 1
  let m : Var := freshVar proofSupport 2
  let y : Var := freshVar proofSupport 3
  let z : Var := freshVar proofSupport 4
  let c : Var := freshVar proofSupport 5
  let n : Var := freshVar proofSupport 6
  let b : Var := freshVar proofSupport 7
  let w : Var := freshVar proofSupport 8
  let d : Var := freshVar proofSupport 9
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_M : x ∉ M.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_X : x ∉ X.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_a : a ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_a_not_A : a ∉ A.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_a_not_M : a ∉ M.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_a_not_X : a ∉ X.fv := by
    intro h
    exact fresh_a (Finset.mem_union_right _ (h))
  have fresh_m : m ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_m_not_M : m ∉ M.fv := by
    intro h
    exact fresh_m (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_ne_a : x ≠ a :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_a_ne_x : a ≠ x := Ne.symm fresh_x_ne_a
  have fresh_x_ne_m : x ≠ m :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_m_ne_x : m ≠ x := Ne.symm fresh_x_ne_m
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_y_ne_x : y ≠ x := Ne.symm fresh_x_ne_y
  have fresh_x_ne_z : x ≠ z :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 0) (j := 4) (by decide)
  have fresh_z_ne_x : z ≠ x := Ne.symm fresh_x_ne_z
  have fresh_x_ne_c : x ≠ c :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 0) (j := 5) (by decide)
  have fresh_c_ne_x : c ≠ x := Ne.symm fresh_x_ne_c
  have fresh_x_ne_n : x ≠ n :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 0) (j := 6) (by decide)
  have fresh_n_ne_x : n ≠ x := Ne.symm fresh_x_ne_n
  have fresh_x_ne_b : x ≠ b :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 7
    exact freshVar_injective proofSupport (i := 0) (j := 7) (by decide)
  have fresh_b_ne_x : b ≠ x := Ne.symm fresh_x_ne_b
  have fresh_a_ne_m : a ≠ m :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_m_ne_a : m ≠ a := Ne.symm fresh_a_ne_m
  have fresh_a_ne_y : a ≠ y :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_y_ne_a : y ≠ a := Ne.symm fresh_a_ne_y
  have fresh_a_ne_z : a ≠ z :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 1) (j := 4) (by decide)
  have fresh_z_ne_a : z ≠ a := Ne.symm fresh_a_ne_z
  have fresh_a_ne_c : a ≠ c :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 1) (j := 5) (by decide)
  have fresh_c_ne_a : c ≠ a := Ne.symm fresh_a_ne_c
  have fresh_a_ne_n : a ≠ n :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 1) (j := 6) (by decide)
  have fresh_n_ne_a : n ≠ a := Ne.symm fresh_a_ne_n
  have fresh_a_ne_b : a ≠ b :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 7
    exact freshVar_injective proofSupport (i := 1) (j := 7) (by decide)
  have fresh_b_ne_a : b ≠ a := Ne.symm fresh_a_ne_b
  have fresh_a_ne_w : a ≠ w :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 8
    exact freshVar_injective proofSupport (i := 1) (j := 8) (by decide)
  have fresh_w_ne_a : w ≠ a := Ne.symm fresh_a_ne_w
  have fresh_a_ne_d : a ≠ d :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 9
    exact freshVar_injective proofSupport (i := 1) (j := 9) (by decide)
  have fresh_d_ne_a : d ≠ a := Ne.symm fresh_a_ne_d
  have fresh_m_ne_y : m ≠ y :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_m_ne_z : m ≠ z :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 2) (j := 4) (by decide)
  have fresh_m_ne_c : m ≠ c :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 2) (j := 5) (by decide)
  have fresh_m_ne_n : m ≠ n :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 2) (j := 6) (by decide)
  have fresh_n_ne_m : n ≠ m := Ne.symm fresh_m_ne_n
  have fresh_y_ne_z : y ≠ z :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 3) (j := 4) (by decide)
  have fresh_z_ne_y : z ≠ y := Ne.symm fresh_y_ne_z
  have fresh_y_ne_c : y ≠ c :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 3) (j := 5) (by decide)
  have fresh_c_ne_y : c ≠ y := Ne.symm fresh_y_ne_c
  have fresh_y_ne_n : y ≠ n :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 3) (j := 6) (by decide)
  have fresh_y_ne_b : y ≠ b :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 7
    exact freshVar_injective proofSupport (i := 3) (j := 7) (by decide)
  have fresh_b_ne_y : b ≠ y := Ne.symm fresh_y_ne_b
  have fresh_y_ne_w : y ≠ w :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 8
    exact freshVar_injective proofSupport (i := 3) (j := 8) (by decide)
  have fresh_w_ne_y : w ≠ y := Ne.symm fresh_y_ne_w
  have fresh_y_ne_d : y ≠ d :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 9
    exact freshVar_injective proofSupport (i := 3) (j := 9) (by decide)
  have fresh_d_ne_y : d ≠ y := Ne.symm fresh_y_ne_d
  have fresh_z_ne_c : z ≠ c :=
    by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 4) (j := 5) (by decide)
  have fresh_c_ne_z : c ≠ z := Ne.symm fresh_z_ne_c
  have fresh_z_ne_n : z ≠ n :=
    by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 4) (j := 6) (by decide)
  have fresh_z_ne_b : z ≠ b :=
    by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 7
    exact freshVar_injective proofSupport (i := 4) (j := 7) (by decide)
  have fresh_b_ne_z : b ≠ z := Ne.symm fresh_z_ne_b
  have fresh_c_ne_n : c ≠ n :=
    by
    change freshVar proofSupport 5 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 5) (j := 6) (by decide)
  have fresh_c_ne_b : c ≠ b :=
    by
    change freshVar proofSupport 5 ≠ freshVar proofSupport 7
    exact freshVar_injective proofSupport (i := 5) (j := 7) (by decide)
  have fresh_b_ne_c : b ≠ c := Ne.symm fresh_c_ne_b
  have fresh_n_ne_b : n ≠ b :=
    by
    change freshVar proofSupport 6 ≠ freshVar proofSupport 7
    exact freshVar_injective proofSupport (i := 6) (j := 7) (by decide)
  have fresh_b_ne_n : b ≠ n := Ne.symm fresh_n_ne_b
  have fresh_n_ne_d : n ≠ d :=
    by
    change freshVar proofSupport 6 ≠ freshVar proofSupport 9
    exact freshVar_injective proofSupport (i := 6) (j := 9) (by decide)
  have fresh_d_ne_n : d ≠ n := Ne.symm fresh_n_ne_d
  have fresh_w_ne_d : w ≠ d :=
    by
    change freshVar proofSupport 8 ≠ freshVar proofSupport 9
    exact freshVar_injective proofSupport (i := 8) (j := 9) (by decide)
  have fresh_d_ne_w : d ≠ w := Ne.symm fresh_w_ne_d
  have p0000 :=
    @g_nnsucelrlem1 x m a (show a ≠ m from (by exact fresh_a_ne_m))
      (show a ≠ x from (by exact fresh_a_ne_x)) (show m ≠ x from (by exact fresh_m_ne_x))
  have p0001 := @g_addceq1 (.cv m) (syn_c0c) (syn_c1c)
  have p0002 := @g_addcid2 (syn_c1c)
  have p0003 :=
    @g_syl6eq (.classEq (.cv m) (syn_c0c)) (syn_cplc (.cv m) (syn_c1c))
      (syn_cplc (syn_c0c) (syn_c1c)) (syn_c1c) p0001 p0002
  have p0004 :=
    @g_eleq2d (.classEq (.cv m) (syn_c0c)) (syn_cplc (.cv m) (syn_c1c)) (syn_c1c)
      (syn_cun (.cv a) (syn_csn (.cv x))) p0003
  have freeVariableCertificate0 : y ∉ ((syn_cun (.cv a) (syn_csn (.cv x)))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
      Finset.mem_singleton, fresh_y_ne_a, fresh_y_ne_x, or_false, not_false_eq_true]
  have p0005 := @g_el1c y (syn_cun (.cv a) (syn_csn (.cv x))) freeVariableCertificate0
  have p0006 :=
    @g_syl6bb (.classEq (.cv m) (syn_c0c))
      (.classMem (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cplc (.cv m) (syn_c1c)))
      (.classMem (syn_cun (.cv a) (syn_csn (.cv x))) (syn_c1c))
      (syn_wex y (.classEq (syn_cun (.cv a) (syn_csn (.cv x))) (syn_csn (.cv y)))) p0004
      p0005
  have p0007 :=
    @g_anbi2d (.classEq (.cv m) (syn_c0c))
      (.classMem (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cplc (.cv m) (syn_c1c)))
      (syn_wex y (.classEq (syn_cun (.cv a) (syn_csn (.cv x))) (syn_csn (.cv y))))
      (.neg (.objMem x a)) p0006
  have p0008 := @g_eleq2 (.cv m) (syn_c0c) (.cv a)
  have p0009 := (Nominal.classEqRefl (syn_c0c))
  have p0010 := @g_eleq2i (syn_c0c) (syn_csn (syn_c0)) (.cv a) p0009
  have p0011 := @g_vex a
  have p0012 := @g_elsnc (.cv a) (syn_c0) p0011
  have p0013 :=
    @g_bitri (.classMem (.cv a) (syn_c0c)) (.classMem (.cv a) (syn_csn (syn_c0)))
      (.classEq (.cv a) (syn_c0)) p0010 p0012
  have p0014_e00_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv m) (syn_c0c))
        (syn_wb (.objMem a m) (.classMem (.cv a) (syn_c0c)))) :=
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
      p0008
  have p0014 :=
    @g_syl6bb (.classEq (.cv m) (syn_c0c)) (.objMem a m) (.classMem (.cv a) (syn_c0c))
      (.classEq (.cv a) (syn_c0)) p0014_e00_recanon p0013
  have p0015 :=
    @g_imbi12d (.classEq (.cv m) (syn_c0c))
      (syn_wa (.neg (.objMem x a))
        (.classMem (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cplc (.cv m) (syn_c1c))))
      (syn_wa (.neg (.objMem x a))
        (syn_wex y (.classEq (syn_cun (.cv a) (syn_csn (.cv x))) (syn_csn (.cv y)))))
      (.objMem a m) (.classEq (.cv a) (syn_c0)) p0007 p0014
  have freeVariableCertificate1 : a ∉ ((Wff.classEq (.cv m) (syn_c0c))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_a_ne_m, or_false,
      not_false_eq_true]
  have freeVariableCertificate2 : x ∉ ((Wff.classEq (.cv m) (syn_c0c))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_x_ne_m, or_false,
      not_false_eq_true]
  have p0016 :=
    @g_n_2albidv (.classEq (.cv m) (syn_c0c))
      (.imp (syn_wa (.neg (.objMem x a))
          (.classMem (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cplc (.cv m) (syn_c1c))))
        (.objMem a m))
      (.imp (syn_wa (.neg (.objMem x a))
          (syn_wex y (.classEq (syn_cun (.cv a) (syn_csn (.cv x))) (syn_csn (.cv y)))))
        (.classEq (.cv a) (syn_c0)))
      a x freeVariableCertificate1 freeVariableCertificate2 p0015
  have p0017 := @g_addceq1 (.cv m) (.cv n) (syn_c1c)
  have p0018_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq m n)
        (.classEq (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv n) (syn_c1c)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_cplc syn_wrex syn_wex syn_wa syn_c1c
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0017
  have p0018 :=
    @g_eleq2d (.objEq m n) (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv n) (syn_c1c))
      (syn_cun (.cv a) (syn_csn (.cv x))) p0018_e00_recanon
  have p0019 :=
    @g_anbi2d (.objEq m n)
      (.classMem (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cplc (.cv m) (syn_c1c)))
      (.classMem (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cplc (.cv n) (syn_c1c)))
      (.neg (.objMem x a)) p0018
  have p0020 := @g_eleq2 (.cv m) (.cv n) (.cv a)
  have p0021_e01_recanon :
    Nominal.NPrf (.imp (.objEq m n) (syn_wb (.objMem a m) (.objMem a n))) :=
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
      p0020
  have p0021 :=
    @g_imbi12d (.objEq m n)
      (syn_wa (.neg (.objMem x a))
        (.classMem (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cplc (.cv m) (syn_c1c))))
      (syn_wa (.neg (.objMem x a))
        (.classMem (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cplc (.cv n) (syn_c1c))))
      (.objMem a m) (.objMem a n) p0019 p0021_e01_recanon
  have freeVariableCertificate3 : a ∉ ((Wff.objEq m n)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_insert,
      Finset.mem_singleton, fresh_a_ne_m, fresh_a_ne_n, or_false, not_false_eq_true]
  have freeVariableCertificate4 : x ∉ ((Wff.objEq m n)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_insert,
      Finset.mem_singleton, fresh_x_ne_m, fresh_x_ne_n, or_false, not_false_eq_true]
  have p0022 :=
    @g_n_2albidv (.objEq m n)
      (.imp (syn_wa (.neg (.objMem x a))
          (.classMem (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cplc (.cv m) (syn_c1c))))
        (.objMem a m))
      (.imp (syn_wa (.neg (.objMem x a))
          (.classMem (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cplc (.cv n) (syn_c1c))))
        (.objMem a n))
      a x freeVariableCertificate3 freeVariableCertificate4 p0021
  have p0023 := @g_eleq12 (.cv x) (.cv z) (.cv a) (.cv c)
  have p0024_e00_recanon :
    Nominal.NPrf
      (.imp (syn_wa (.objEq x z) (.objEq a c)) (syn_wb (.objMem x a) (.objMem z c))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wa syn_wb
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
            · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
            · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _)
      p0023
  have p0024 :=
    @g_ancoms (.objEq x z) (.objEq a c) (syn_wb (.objMem x a) (.objMem z c))
      p0024_e00_recanon
  have p0025 :=
    @g_notbid (syn_wa (.objEq a c) (.objEq x z)) (.objMem x a) (.objMem z c) p0024
  have p0026 := @g_sneq (.cv x) (.cv z)
  have p0027 := @g_uneq12 (.cv a) (.cv c) (syn_csn (.cv x)) (syn_csn (.cv z))
  have p0028_e00_recanon :
    Nominal.NPrf (.imp (.objEq x z) (.classEq (syn_csn (.cv x)) (syn_csn (.cv z)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_csn
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0026
  have p0028_e01_recanon :
    Nominal.NPrf
      (.imp (syn_wa (.objEq a c) (.classEq (syn_csn (.cv x)) (syn_csn (.cv z))))
        (.classEq (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cun (.cv c) (syn_csn (.cv z))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wa syn_csn syn_cun syn_cnin syn_wnan syn_ccompl
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0027
  have p0028 :=
    @g_sylan2 (.objEq x z) (.objEq a c) (.classEq (syn_csn (.cv x)) (syn_csn (.cv z)))
      (.classEq (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cun (.cv c) (syn_csn (.cv z))))
      p0028_e00_recanon p0028_e01_recanon
  have p0029 :=
    @g_eleq1d (syn_wa (.objEq a c) (.objEq x z)) (syn_cun (.cv a) (syn_csn (.cv x)))
      (syn_cun (.cv c) (syn_csn (.cv z))) (syn_cplc (.cv n) (syn_c1c)) p0028
  have p0030 :=
    @g_anbi12d (syn_wa (.objEq a c) (.objEq x z)) (.neg (.objMem x a))
      (.neg (.objMem z c))
      (.classMem (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cplc (.cv n) (syn_c1c)))
      (.classMem (syn_cun (.cv c) (syn_csn (.cv z))) (syn_cplc (.cv n) (syn_c1c))) p0025
      p0029
  have p0031 := @g_eleq1 (.cv a) (.cv c) (.cv n)
  have p0032_e00_recanon :
    Nominal.NPrf (.imp (.objEq a c) (syn_wb (.objMem a n) (.objMem c n))) :=
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
      p0031
  have p0032 :=
    @g_adantr (.objEq a c) (syn_wb (.objMem a n) (.objMem c n)) (.objEq x z)
      p0032_e00_recanon
  have p0033 :=
    @g_imbi12d (syn_wa (.objEq a c) (.objEq x z))
      (syn_wa (.neg (.objMem x a))
        (.classMem (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cplc (.cv n) (syn_c1c))))
      (syn_wa (.neg (.objMem z c))
        (.classMem (syn_cun (.cv c) (syn_csn (.cv z))) (syn_cplc (.cv n) (syn_c1c))))
      (.objMem a n) (.objMem c n) p0030 p0032
  have freeVariableCertificate5 :
    z ∉
      ((Wff.imp (syn_wa (.neg (.objMem x a))
            (.classMem (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cplc (.cv n) (syn_c1c))))
          (.objMem a n))).fv :=
    by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
      NFChoice.Compiler.CoreFVSimp.fv_wff_neg, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
      Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, fresh_z_ne_x,
      fresh_z_ne_a, fresh_z_ne_n, or_false, not_false_eq_true]
  have freeVariableCertificate6 :
    c ∉
      ((Wff.imp (syn_wa (.neg (.objMem x a))
            (.classMem (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cplc (.cv n) (syn_c1c))))
          (.objMem a n))).fv :=
    by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
      NFChoice.Compiler.CoreFVSimp.fv_wff_neg, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
      Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, fresh_c_ne_x,
      fresh_c_ne_a, fresh_c_ne_n, or_false, not_false_eq_true]
  have freeVariableCertificate7 :
    a ∉
      ((Wff.imp (syn_wa (.neg (.objMem z c))
            (.classMem (syn_cun (.cv c) (syn_csn (.cv z))) (syn_cplc (.cv n) (syn_c1c))))
          (.objMem c n))).fv :=
    by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
      NFChoice.Compiler.CoreFVSimp.fv_wff_neg, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
      Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, fresh_a_ne_z,
      fresh_a_ne_c, fresh_a_ne_n, or_false, not_false_eq_true]
  have freeVariableCertificate8 :
    x ∉
      ((Wff.imp (syn_wa (.neg (.objMem z c))
            (.classMem (syn_cun (.cv c) (syn_csn (.cv z))) (syn_cplc (.cv n) (syn_c1c))))
          (.objMem c n))).fv :=
    by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
      NFChoice.Compiler.CoreFVSimp.fv_wff_neg, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
      Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, fresh_x_ne_z,
      fresh_x_ne_c, fresh_x_ne_n, or_false, not_false_eq_true]
  have p0034 :=
    @g_cbval2v
      (.imp (syn_wa (.neg (.objMem x a))
          (.classMem (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cplc (.cv n) (syn_c1c))))
        (.objMem a n))
      (.imp (syn_wa (.neg (.objMem z c))
          (.classMem (syn_cun (.cv c) (syn_csn (.cv z))) (syn_cplc (.cv n) (syn_c1c))))
        (.objMem c n))
      a x c z freeVariableCertificate5 freeVariableCertificate6 freeVariableCertificate7
      freeVariableCertificate8 (show z ≠ a from (by exact fresh_z_ne_a))
      (show z ≠ c from (by exact fresh_z_ne_c)) (show a ≠ x from (by exact fresh_a_ne_x))
      (show x ≠ c from (by exact fresh_x_ne_c)) p0033
  have p0035 :=
    @g_syl6bb (.objEq m n)
      (.all a (.all x (.imp (syn_wa (.neg (.objMem x a))
              (.classMem (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cplc (.cv m) (syn_c1c))))
            (.objMem a m))))
      (.all a (.all x (.imp (syn_wa (.neg (.objMem x a))
              (.classMem (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cplc (.cv n) (syn_c1c))))
            (.objMem a n))))
      (.all c (.all z (.imp (syn_wa (.neg (.objMem z c))
              (.classMem (syn_cun (.cv c) (syn_csn (.cv z))) (syn_cplc (.cv n) (syn_c1c))))
            (.objMem c n))))
      p0022 p0034
  have p0036 := @g_addceq1 (.cv m) (syn_cplc (.cv n) (syn_c1c)) (syn_c1c)
  have p0037 :=
    @g_eleq2d (.classEq (.cv m) (syn_cplc (.cv n) (syn_c1c))) (syn_cplc (.cv m) (syn_c1c))
      (syn_cplc (syn_cplc (.cv n) (syn_c1c)) (syn_c1c))
      (syn_cun (.cv a) (syn_csn (.cv x))) p0036
  have p0038 :=
    @g_anbi2d (.classEq (.cv m) (syn_cplc (.cv n) (syn_c1c)))
      (.classMem (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cplc (.cv m) (syn_c1c)))
      (.classMem (syn_cun (.cv a) (syn_csn (.cv x)))
        (syn_cplc (syn_cplc (.cv n) (syn_c1c)) (syn_c1c)))
      (.neg (.objMem x a)) p0037
  have p0039 := @g_eleq2 (.cv m) (syn_cplc (.cv n) (syn_c1c)) (.cv a)
  have p0040_e01_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv m) (syn_cplc (.cv n) (syn_c1c)))
        (syn_wb (.objMem a m) (.classMem (.cv a) (syn_cplc (.cv n) (syn_c1c))))) :=
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
      p0039
  have p0040 :=
    @g_imbi12d (.classEq (.cv m) (syn_cplc (.cv n) (syn_c1c)))
      (syn_wa (.neg (.objMem x a))
        (.classMem (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cplc (.cv m) (syn_c1c))))
      (syn_wa (.neg (.objMem x a)) (.classMem (syn_cun (.cv a) (syn_csn (.cv x)))
          (syn_cplc (syn_cplc (.cv n) (syn_c1c)) (syn_c1c))))
      (.objMem a m) (.classMem (.cv a) (syn_cplc (.cv n) (syn_c1c))) p0038
      p0040_e01_recanon
  have freeVariableCertificate9 :
    a ∉ ((Wff.classEq (.cv m) (syn_cplc (.cv n) (syn_c1c)))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_a_ne_m, fresh_a_ne_n, or_false,
      not_false_eq_true]
  have freeVariableCertificate10 :
    x ∉ ((Wff.classEq (.cv m) (syn_cplc (.cv n) (syn_c1c)))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_x_ne_m, fresh_x_ne_n, or_false,
      not_false_eq_true]
  have p0041 :=
    @g_n_2albidv (.classEq (.cv m) (syn_cplc (.cv n) (syn_c1c)))
      (.imp (syn_wa (.neg (.objMem x a))
          (.classMem (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cplc (.cv m) (syn_c1c))))
        (.objMem a m))
      (.imp (syn_wa (.neg (.objMem x a)) (.classMem (syn_cun (.cv a) (syn_csn (.cv x)))
            (syn_cplc (syn_cplc (.cv n) (syn_c1c)) (syn_c1c))))
        (.classMem (.cv a) (syn_cplc (.cv n) (syn_c1c))))
      a x freeVariableCertificate9 freeVariableCertificate10 p0040
  have p0042 := @g_addceq1 (.cv m) M (syn_c1c)
  have p0043 :=
    @g_eleq2d (.classEq (.cv m) M) (syn_cplc (.cv m) (syn_c1c)) (syn_cplc M (syn_c1c))
      (syn_cun (.cv a) (syn_csn (.cv x))) p0042
  have p0044 :=
    @g_anbi2d (.classEq (.cv m) M)
      (.classMem (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cplc (.cv m) (syn_c1c)))
      (.classMem (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cplc M (syn_c1c)))
      (.neg (.objMem x a)) p0043
  have p0045 := @g_eleq2 (.cv m) M (.cv a)
  have p0046_e01_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv m) M) (syn_wb (.objMem a m) (.classMem (.cv a) M))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb
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
      p0045
  have p0046 :=
    @g_imbi12d (.classEq (.cv m) M)
      (syn_wa (.neg (.objMem x a))
        (.classMem (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cplc (.cv m) (syn_c1c))))
      (syn_wa (.neg (.objMem x a))
        (.classMem (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cplc M (syn_c1c))))
      (.objMem a m) (.classMem (.cv a) M) p0044 p0046_e01_recanon
  have freeVariableCertificate11 : a ∉ ((Wff.classEq (.cv m) M)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      fresh_a_ne_m, fresh_a_not_M, or_false, not_false_eq_true]
  have freeVariableCertificate12 : x ∉ ((Wff.classEq (.cv m) M)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      fresh_x_ne_m, fresh_x_not_M, or_false, not_false_eq_true]
  have p0047 :=
    @g_n_2albidv (.classEq (.cv m) M)
      (.imp (syn_wa (.neg (.objMem x a))
          (.classMem (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cplc (.cv m) (syn_c1c))))
        (.objMem a m))
      (.imp (syn_wa (.neg (.objMem x a))
          (.classMem (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cplc M (syn_c1c))))
        (.classMem (.cv a) M))
      a x freeVariableCertificate11 freeVariableCertificate12 p0046
  have p0048 := @g_vex x
  have p0049 := @g_unsneqsn (.cv a) (.cv x) (.cv y) p0048
  have p0050 :=
    @g_ord (.classEq (syn_cun (.cv a) (syn_csn (.cv x))) (syn_csn (.cv y)))
      (.classEq (.cv a) (syn_c0)) (.classEq (.cv a) (syn_csn (.cv x))) p0049
  have p0051 := @g_snid (.cv x) p0048
  have p0052 := @g_eleq2 (.cv a) (syn_csn (.cv x)) (.cv x)
  have p0053_e01_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv a) (syn_csn (.cv x)))
        (syn_wb (.objMem x a) (.classMem (.cv x) (syn_csn (.cv x))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_csn syn_wb
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
      p0052
  have p0053 :=
    @g_mpbiri (.classEq (.cv a) (syn_csn (.cv x))) (.objMem x a)
      (.classMem (.cv x) (syn_csn (.cv x))) p0051 p0053_e01_recanon
  have p0054 :=
    @g_syl6 (.classEq (syn_cun (.cv a) (syn_csn (.cv x))) (syn_csn (.cv y)))
      (.neg (.classEq (.cv a) (syn_c0))) (.classEq (.cv a) (syn_csn (.cv x)))
      (.objMem x a) p0050 p0053
  have p0055 :=
    @g_con1d (.classEq (syn_cun (.cv a) (syn_csn (.cv x))) (syn_csn (.cv y)))
      (.classEq (.cv a) (syn_c0)) (.objMem x a) p0054
  have freeVariableCertificate13 :
    y ∉ ((Wff.imp (.neg (.objMem x a)) (.classEq (.cv a) (syn_c0)))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
      NFChoice.Compiler.CoreFVSimp.fv_wff_neg, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union,
      Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, fresh_y_ne_x,
      fresh_y_ne_a, or_false, not_false_eq_true]
  have p0056 :=
    @g_exlimiv (.classEq (syn_cun (.cv a) (syn_csn (.cv x))) (syn_csn (.cv y)))
      (.imp (.neg (.objMem x a)) (.classEq (.cv a) (syn_c0))) y freeVariableCertificate13
      p0055
  have p0057 :=
    @g_impcom (syn_wex y (.classEq (syn_cun (.cv a) (syn_csn (.cv x))) (syn_csn (.cv y))))
      (.neg (.objMem x a)) (.classEq (.cv a) (syn_c0)) p0056
  have p0058 :=
    @g_gen2
      (.imp (syn_wa (.neg (.objMem x a))
          (syn_wex y (.classEq (syn_cun (.cv a) (syn_csn (.cv x))) (syn_csn (.cv y)))))
        (.classEq (.cv a) (syn_c0)))
      a x p0057
  have freeVariableCertificate14 : b ∉ ((syn_cun (.cv a) (syn_csn (.cv x)))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
      Finset.mem_singleton, fresh_b_ne_a, fresh_b_ne_x, or_false, not_false_eq_true]
  have freeVariableCertificate15 : b ∉ ((syn_cplc (.cv n) (syn_c1c))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_b_ne_n, or_false,
      not_false_eq_true]
  have p0059 :=
    @g_elsuc y (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cplc (.cv n) (syn_c1c)) b
      freeVariableCertificate14 freeVariableCertificate0 freeVariableCertificate15
      (show b ≠ y from (by exact fresh_b_ne_y))
  have p0060 := @g_vex y
  have p0061 := @g_elcompl (.cv y) (.cv b) p0060
  have p0062_e00_recanon :
    Nominal.NPrf (syn_wb (.classMem (.cv y) (syn_ccompl (.cv b))) (.neg (.objMem y b))) :=
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
      p0061
  have p0062 :=
    @g_anbi2i (.classMem (.cv y) (syn_ccompl (.cv b))) (.neg (.objMem y b))
      (.classMem (.cv b) (syn_cplc (.cv n) (syn_c1c))) p0062_e00_recanon
  have p0063 :=
    @g_simprrl (.objEq x y)
      (syn_wa (.classMem (.cv b) (syn_cplc (.cv n) (syn_c1c))) (.neg (.objMem y b)))
      (.classEq (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cun (.cv b) (syn_csn (.cv y))))
      (.neg (.objMem x a))
  have p0064 := @g_sneq (.cv x) (.cv y)
  have p0065_e00_recanon :
    Nominal.NPrf (.imp (.objEq x y) (.classEq (syn_csn (.cv x)) (syn_csn (.cv y)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_csn
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0064
  have p0065 :=
    @g_adantr (.objEq x y) (.classEq (syn_csn (.cv x)) (syn_csn (.cv y)))
      (syn_wa (syn_wa (.classMem (.cv b) (syn_cplc (.cv n) (syn_c1c))) (.neg (.objMem y b)))
        (syn_wa (.classEq (syn_cun (.cv a) (syn_csn (.cv x)))
            (syn_cun (.cv b) (syn_csn (.cv y)))) (.neg (.objMem x a))))
      p0065_e00_recanon
  have p0066 :=
    @g_difeq12d
      (syn_wa (.objEq x y) (syn_wa
          (syn_wa (.classMem (.cv b) (syn_cplc (.cv n) (syn_c1c))) (.neg (.objMem y b))) (syn_wa
            (.classEq (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cun (.cv b) (syn_csn (.cv y))))
            (.neg (.objMem x a)))))
      (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cun (.cv b) (syn_csn (.cv y)))
      (syn_csn (.cv x)) (syn_csn (.cv y)) p0063 p0065
  have p0067 :=
    @g_simprrr (.objEq x y)
      (syn_wa (.classMem (.cv b) (syn_cplc (.cv n) (syn_c1c))) (.neg (.objMem y b)))
      (.classEq (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cun (.cv b) (syn_csn (.cv y))))
      (.neg (.objMem x a))
  have p0068 := @g_nnsucelrlem2 (.cv a) (.cv x)
  have p0069_e01_recanon :
    Nominal.NPrf
      (.imp (.neg (.objMem x a))
        (.classEq (syn_cdif (syn_cun (.cv a) (syn_csn (.cv x))) (syn_csn (.cv x))) (.cv a))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_cdif syn_cin syn_ccompl syn_cnin syn_wnan syn_wa syn_cun syn_csn
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0068
  have p0069 :=
    @g_syl
      (syn_wa (.objEq x y) (syn_wa
          (syn_wa (.classMem (.cv b) (syn_cplc (.cv n) (syn_c1c))) (.neg (.objMem y b))) (syn_wa
            (.classEq (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cun (.cv b) (syn_csn (.cv y))))
            (.neg (.objMem x a)))))
      (.neg (.objMem x a))
      (.classEq (syn_cdif (syn_cun (.cv a) (syn_csn (.cv x))) (syn_csn (.cv x))) (.cv a))
      p0067 p0069_e01_recanon
  have p0070 :=
    @g_simprlr (.objEq x y) (.classMem (.cv b) (syn_cplc (.cv n) (syn_c1c)))
      (.neg (.objMem y b))
      (syn_wa (.classEq (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cun (.cv b) (syn_csn (.cv y))))
        (.neg (.objMem x a)))
  have p0071 := @g_nnsucelrlem2 (.cv b) (.cv y)
  have p0072_e01_recanon :
    Nominal.NPrf
      (.imp (.neg (.objMem y b))
        (.classEq (syn_cdif (syn_cun (.cv b) (syn_csn (.cv y))) (syn_csn (.cv y))) (.cv b))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_cdif syn_cin syn_ccompl syn_cnin syn_wnan syn_wa syn_cun syn_csn
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0071
  have p0072 :=
    @g_syl
      (syn_wa (.objEq x y) (syn_wa
          (syn_wa (.classMem (.cv b) (syn_cplc (.cv n) (syn_c1c))) (.neg (.objMem y b))) (syn_wa
            (.classEq (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cun (.cv b) (syn_csn (.cv y))))
            (.neg (.objMem x a)))))
      (.neg (.objMem y b))
      (.classEq (syn_cdif (syn_cun (.cv b) (syn_csn (.cv y))) (syn_csn (.cv y))) (.cv b))
      p0070 p0072_e01_recanon
  have p0073 :=
    @g_n_3eqtr3d
      (syn_wa (.objEq x y) (syn_wa
          (syn_wa (.classMem (.cv b) (syn_cplc (.cv n) (syn_c1c))) (.neg (.objMem y b))) (syn_wa
            (.classEq (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cun (.cv b) (syn_csn (.cv y))))
            (.neg (.objMem x a)))))
      (syn_cdif (syn_cun (.cv a) (syn_csn (.cv x))) (syn_csn (.cv x)))
      (syn_cdif (syn_cun (.cv b) (syn_csn (.cv y))) (syn_csn (.cv y))) (.cv a) (.cv b)
      p0066 p0069 p0072
  have p0074 :=
    @g_simprll (.objEq x y) (.classMem (.cv b) (syn_cplc (.cv n) (syn_c1c)))
      (.neg (.objMem y b))
      (syn_wa (.classEq (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cun (.cv b) (syn_csn (.cv y))))
        (.neg (.objMem x a)))
  have p0075 :=
    @g_eqeltrd
      (syn_wa (.objEq x y) (syn_wa
          (syn_wa (.classMem (.cv b) (syn_cplc (.cv n) (syn_c1c))) (.neg (.objMem y b))) (syn_wa
            (.classEq (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cun (.cv b) (syn_csn (.cv y))))
            (.neg (.objMem x a)))))
      (.cv a) (.cv b) (syn_cplc (.cv n) (syn_c1c)) p0073 p0074
  have p0076 :=
    @g_n_3adantr1 (.objEq x y)
      (syn_wa (.classMem (.cv b) (syn_cplc (.cv n) (syn_c1c))) (.neg (.objMem y b)))
      (syn_wa (.classEq (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cun (.cv b) (syn_csn (.cv y))))
        (.neg (.objMem x a)))
      (.classMem (.cv a) (syn_cplc (.cv n) (syn_c1c)))
      (.all c (.all z (.imp (syn_wa (.neg (.objMem z c))
              (.classMem (syn_cun (.cv c) (syn_csn (.cv z))) (syn_cplc (.cv n) (syn_c1c))))
            (.objMem c n))))
      p0075
  have p0077 :=
    @g_ex (.objEq x y)
      (syn_w3a (.all c (.all z (.imp (syn_wa (.neg (.objMem z c))
                (.classMem (syn_cun (.cv c) (syn_csn (.cv z))) (syn_cplc (.cv n) (syn_c1c))))
              (.objMem c n))))
        (syn_wa (.classMem (.cv b) (syn_cplc (.cv n) (syn_c1c))) (.neg (.objMem y b))) (syn_wa
          (.classEq (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cun (.cv b) (syn_csn (.cv y))))
          (.neg (.objMem x a))))
      (.classMem (.cv a) (syn_cplc (.cv n) (syn_c1c))) p0076
  have p0078 :=
    @g_simpl (syn_wne (.cv x) (.cv y))
      (syn_w3a (.all c (.all z (.imp (syn_wa (.neg (.objMem z c))
                (.classMem (syn_cun (.cv c) (syn_csn (.cv z))) (syn_cplc (.cv n) (syn_c1c))))
              (.objMem c n))))
        (syn_wa (.classMem (.cv b) (syn_cplc (.cv n) (syn_c1c))) (.neg (.objMem y b))) (syn_wa
          (.classEq (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cun (.cv b) (syn_csn (.cv y))))
          (.neg (.objMem x a))))
  have p0079 :=
    @g_simpr3l
      (.classEq (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cun (.cv b) (syn_csn (.cv y))))
      (.neg (.objMem x a))
      (.all c (.all z (.imp (syn_wa (.neg (.objMem z c))
              (.classMem (syn_cun (.cv c) (syn_csn (.cv z))) (syn_cplc (.cv n) (syn_c1c))))
            (.objMem c n))))
      (syn_wa (.classMem (.cv b) (syn_cplc (.cv n) (syn_c1c))) (.neg (.objMem y b)))
      (syn_wne (.cv x) (.cv y))
  have p0080 :=
    @g_simpr2r (.classMem (.cv b) (syn_cplc (.cv n) (syn_c1c))) (.neg (.objMem y b))
      (.all c (.all z (.imp (syn_wa (.neg (.objMem z c))
              (.classMem (syn_cun (.cv c) (syn_csn (.cv z))) (syn_cplc (.cv n) (syn_c1c))))
            (.objMem c n))))
      (syn_wa (.classEq (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cun (.cv b) (syn_csn (.cv y))))
        (.neg (.objMem x a)))
      (syn_wne (.cv x) (.cv y))
  have p0081 := @g_nnsucelrlem3 (.cv a) (.cv b) (.cv x) (.cv y) p0048
  have p0082_e03_recanon :
    Nominal.NPrf
      (.imp (syn_w3a (syn_wne (.cv x) (.cv y)) (.classEq (syn_cun (.cv a) (syn_csn (.cv x)))
            (syn_cun (.cv b) (syn_csn (.cv y)))) (.neg (.objMem y b))) (.classEq (.cv b)
          (syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv x))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_w3a syn_wa syn_wne syn_cun syn_cnin syn_wnan syn_ccompl syn_csn
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
      p0081
  have p0082 :=
    @g_syl3anc
      (syn_wa (syn_wne (.cv x) (.cv y)) (syn_w3a (.all c (.all z (.imp
                (syn_wa (.neg (.objMem z c)) (.classMem (syn_cun (.cv c) (syn_csn (.cv z)))
                    (syn_cplc (.cv n) (syn_c1c)))) (.objMem c n))))
          (syn_wa (.classMem (.cv b) (syn_cplc (.cv n) (syn_c1c))) (.neg (.objMem y b))) (syn_wa
            (.classEq (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cun (.cv b) (syn_csn (.cv y))))
            (.neg (.objMem x a)))))
      (syn_wne (.cv x) (.cv y))
      (.classEq (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cun (.cv b) (syn_csn (.cv y))))
      (.neg (.objMem y b))
      (.classEq (.cv b) (syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv x))))
      p0078 p0079 p0080 p0082_e03_recanon
  have p0083 :=
    @g_simp22r (.classMem (.cv b) (syn_cplc (.cv n) (syn_c1c))) (.neg (.objMem y b))
      (.all c (.all z (.imp (syn_wa (.neg (.objMem z c))
              (.classMem (syn_cun (.cv c) (syn_csn (.cv z))) (syn_cplc (.cv n) (syn_c1c))))
            (.objMem c n))))
      (syn_wa (.classEq (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cun (.cv b) (syn_csn (.cv y))))
        (.neg (.objMem x a)))
      (syn_wne (.cv x) (.cv y))
      (.classEq (.cv b) (syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv x))))
  have p0084 := @g_difsn (.cv y) (.cv a)
  have p0085_e00_recanon :
    Nominal.NPrf
      (.imp (.neg (.objMem y a)) (.classEq (syn_cdif (.cv a) (syn_csn (.cv y))) (.cv a))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_cdif syn_cin syn_ccompl syn_cnin syn_wnan syn_wa syn_csn
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0084
  have p0085 :=
    @g_uneq1d (.neg (.objMem y a)) (syn_cdif (.cv a) (syn_csn (.cv y))) (.cv a)
      (syn_csn (.cv x)) p0085_e00_recanon
  have p0086 :=
    @g_eqeq2d (.neg (.objMem y a))
      (syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv x)))
      (syn_cun (.cv a) (syn_csn (.cv x))) (.cv b) p0085
  have p0087 :=
    @g_biimpcd (.neg (.objMem y a))
      (.classEq (.cv b) (syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv x))))
      (.classEq (.cv b) (syn_cun (.cv a) (syn_csn (.cv x)))) p0086
  have p0088 :=
    @g_n_3ad2ant3
      (.classEq (.cv b) (syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv x))))
      (syn_wne (.cv x) (.cv y))
      (.imp (.neg (.objMem y a)) (.classEq (.cv b) (syn_cun (.cv a) (syn_csn (.cv x)))))
      (syn_w3a (.all c (.all z (.imp (syn_wa (.neg (.objMem z c))
                (.classMem (syn_cun (.cv c) (syn_csn (.cv z))) (syn_cplc (.cv n) (syn_c1c))))
              (.objMem c n))))
        (syn_wa (.classMem (.cv b) (syn_cplc (.cv n) (syn_c1c))) (.neg (.objMem y b))) (syn_wa
          (.classEq (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cun (.cv b) (syn_csn (.cv y))))
          (.neg (.objMem x a))))
      p0087
  have p0089 :=
    @g_simp23l
      (.classEq (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cun (.cv b) (syn_csn (.cv y))))
      (.neg (.objMem x a))
      (.all c (.all z (.imp (syn_wa (.neg (.objMem z c))
              (.classMem (syn_cun (.cv c) (syn_csn (.cv z))) (syn_cplc (.cv n) (syn_c1c))))
            (.objMem c n))))
      (syn_wa (.classMem (.cv b) (syn_cplc (.cv n) (syn_c1c))) (.neg (.objMem y b)))
      (syn_wne (.cv x) (.cv y))
      (.classEq (.cv b) (syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv x))))
  have p0090 :=
    @g_eqeq2d
      (syn_w3a (syn_wne (.cv x) (.cv y)) (syn_w3a (.all c (.all z (.imp
                (syn_wa (.neg (.objMem z c)) (.classMem (syn_cun (.cv c) (syn_csn (.cv z)))
                    (syn_cplc (.cv n) (syn_c1c)))) (.objMem c n))))
          (syn_wa (.classMem (.cv b) (syn_cplc (.cv n) (syn_c1c))) (.neg (.objMem y b))) (syn_wa
            (.classEq (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cun (.cv b) (syn_csn (.cv y))))
            (.neg (.objMem x a)))) (.classEq (.cv b)
          (syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv x)))))
      (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cun (.cv b) (syn_csn (.cv y))) (.cv b)
      p0089
  have p0091 := @g_snss (.cv y) (.cv b) p0060
  have p0092 := @g_ssequn2 (syn_csn (.cv y)) (.cv b)
  have p0093_e00_recanon :
    Nominal.NPrf (syn_wb (.objMem y b) (syn_wss (syn_csn (.cv y)) (.cv b))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wss syn_cin syn_ccompl syn_cnin syn_wnan syn_wa syn_csn
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _)
      p0091
  have p0093 :=
    @g_bitr2i (.objMem y b) (syn_wss (syn_csn (.cv y)) (.cv b))
      (.classEq (syn_cun (.cv b) (syn_csn (.cv y))) (.cv b)) p0093_e00_recanon p0092
  have p0094 :=
    @g_biimpi (.classEq (syn_cun (.cv b) (syn_csn (.cv y))) (.cv b)) (.objMem y b) p0093
  have p0095 := @g_eqcoms (.objMem y b) (syn_cun (.cv b) (syn_csn (.cv y))) (.cv b) p0094
  have p0096 :=
    @g_syl6bi
      (syn_w3a (syn_wne (.cv x) (.cv y)) (syn_w3a (.all c (.all z (.imp
                (syn_wa (.neg (.objMem z c)) (.classMem (syn_cun (.cv c) (syn_csn (.cv z)))
                    (syn_cplc (.cv n) (syn_c1c)))) (.objMem c n))))
          (syn_wa (.classMem (.cv b) (syn_cplc (.cv n) (syn_c1c))) (.neg (.objMem y b))) (syn_wa
            (.classEq (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cun (.cv b) (syn_csn (.cv y))))
            (.neg (.objMem x a)))) (.classEq (.cv b)
          (syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv x)))))
      (.classEq (.cv b) (syn_cun (.cv a) (syn_csn (.cv x))))
      (.classEq (.cv b) (syn_cun (.cv b) (syn_csn (.cv y)))) (.objMem y b) p0090 p0095
  have p0097 :=
    @g_syld
      (syn_w3a (syn_wne (.cv x) (.cv y)) (syn_w3a (.all c (.all z (.imp
                (syn_wa (.neg (.objMem z c)) (.classMem (syn_cun (.cv c) (syn_csn (.cv z)))
                    (syn_cplc (.cv n) (syn_c1c)))) (.objMem c n))))
          (syn_wa (.classMem (.cv b) (syn_cplc (.cv n) (syn_c1c))) (.neg (.objMem y b))) (syn_wa
            (.classEq (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cun (.cv b) (syn_csn (.cv y))))
            (.neg (.objMem x a)))) (.classEq (.cv b)
          (syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv x)))))
      (.neg (.objMem y a)) (.classEq (.cv b) (syn_cun (.cv a) (syn_csn (.cv x))))
      (.objMem y b) p0088 p0096
  have p0098 :=
    @g_mt3d
      (syn_w3a (syn_wne (.cv x) (.cv y)) (syn_w3a (.all c (.all z (.imp
                (syn_wa (.neg (.objMem z c)) (.classMem (syn_cun (.cv c) (syn_csn (.cv z)))
                    (syn_cplc (.cv n) (syn_c1c)))) (.objMem c n))))
          (syn_wa (.classMem (.cv b) (syn_cplc (.cv n) (syn_c1c))) (.neg (.objMem y b))) (syn_wa
            (.classEq (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cun (.cv b) (syn_csn (.cv y))))
            (.neg (.objMem x a)))) (.classEq (.cv b)
          (syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv x)))))
      (.objMem y a) (.objMem y b) p0083 p0097
  have p0099 := @g_nnsucelrlem4 (.cv y) (.cv a)
  have p0100_e01_recanon :
    Nominal.NPrf
      (.imp (.objMem y a)
        (.classEq (syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv y))) (.cv a))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_cdif syn_cin syn_csn
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0099
  have p0100 :=
    @g_syl
      (syn_w3a (syn_wne (.cv x) (.cv y)) (syn_w3a (.all c (.all z (.imp
                (syn_wa (.neg (.objMem z c)) (.classMem (syn_cun (.cv c) (syn_csn (.cv z)))
                    (syn_cplc (.cv n) (syn_c1c)))) (.objMem c n))))
          (syn_wa (.classMem (.cv b) (syn_cplc (.cv n) (syn_c1c))) (.neg (.objMem y b))) (syn_wa
            (.classEq (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cun (.cv b) (syn_csn (.cv y))))
            (.neg (.objMem x a)))) (.classEq (.cv b)
          (syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv x)))))
      (.objMem y a)
      (.classEq (syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv y))) (.cv a))
      p0098 p0100_e01_recanon
  have p0101 :=
    @g_simpl3r
      (.classEq (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cun (.cv b) (syn_csn (.cv y))))
      (.neg (.objMem x a))
      (.all c (.all z (.imp (syn_wa (.neg (.objMem z c))
              (.classMem (syn_cun (.cv c) (syn_csn (.cv z))) (syn_cplc (.cv n) (syn_c1c))))
            (.objMem c n))))
      (syn_wa (.classMem (.cv b) (syn_cplc (.cv n) (syn_c1c))) (.neg (.objMem y b)))
      (.classEq (.cv b) (syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv x))))
  have p0102 := @g_difss (.cv a) (syn_csn (.cv y))
  have p0103 := @g_sseli (syn_cdif (.cv a) (syn_csn (.cv y))) (.cv a) (.cv x) p0102
  have p0104_e01_recanon :
    Nominal.NPrf
      (.imp (.classMem (.cv x) (syn_cdif (.cv a) (syn_csn (.cv y)))) (.objMem x a)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_cdif syn_cin syn_ccompl syn_cnin syn_wnan syn_wa syn_csn
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _)
      p0103
  have p0104 :=
    @g_nsyl
      (syn_wa (syn_w3a (.all c (.all z (.imp (syn_wa (.neg (.objMem z c))
                  (.classMem (syn_cun (.cv c) (syn_csn (.cv z))) (syn_cplc (.cv n) (syn_c1c))))
                (.objMem c n))))
          (syn_wa (.classMem (.cv b) (syn_cplc (.cv n) (syn_c1c))) (.neg (.objMem y b))) (syn_wa
            (.classEq (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cun (.cv b) (syn_csn (.cv y))))
            (.neg (.objMem x a)))) (.classEq (.cv b)
          (syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv x)))))
      (.objMem x a) (.classMem (.cv x) (syn_cdif (.cv a) (syn_csn (.cv y)))) p0101
      p0104_e01_recanon
  have p0105 :=
    @g_simp2l
      (.all c (.all z (.imp (syn_wa (.neg (.objMem z c))
              (.classMem (syn_cun (.cv c) (syn_csn (.cv z))) (syn_cplc (.cv n) (syn_c1c))))
            (.objMem c n))))
      (.classMem (.cv b) (syn_cplc (.cv n) (syn_c1c))) (.neg (.objMem y b))
      (syn_wa (.classEq (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cun (.cv b) (syn_csn (.cv y))))
        (.neg (.objMem x a)))
  have p0106 :=
    @g_eleq1 (.cv b) (syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv x)))
      (syn_cplc (.cv n) (syn_c1c))
  have p0107 :=
    @g_biimpd
      (.classEq (.cv b) (syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv x))))
      (.classMem (.cv b) (syn_cplc (.cv n) (syn_c1c)))
      (.classMem (syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv x)))
        (syn_cplc (.cv n) (syn_c1c)))
      p0106
  have p0108 :=
    @g_mpan9
      (syn_w3a (.all c (.all z (.imp (syn_wa (.neg (.objMem z c))
                (.classMem (syn_cun (.cv c) (syn_csn (.cv z))) (syn_cplc (.cv n) (syn_c1c))))
              (.objMem c n))))
        (syn_wa (.classMem (.cv b) (syn_cplc (.cv n) (syn_c1c))) (.neg (.objMem y b))) (syn_wa
          (.classEq (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cun (.cv b) (syn_csn (.cv y))))
          (.neg (.objMem x a))))
      (.classMem (.cv b) (syn_cplc (.cv n) (syn_c1c)))
      (.classEq (.cv b) (syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv x))))
      (.classMem (syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv x)))
        (syn_cplc (.cv n) (syn_c1c)))
      p0105 p0107
  have p0109 :=
    @g_simpl1
      (.all c (.all z (.imp (syn_wa (.neg (.objMem z c))
              (.classMem (syn_cun (.cv c) (syn_csn (.cv z))) (syn_cplc (.cv n) (syn_c1c))))
            (.objMem c n))))
      (syn_wa (.classMem (.cv b) (syn_cplc (.cv n) (syn_c1c))) (.neg (.objMem y b)))
      (syn_wa (.classEq (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cun (.cv b) (syn_csn (.cv y))))
        (.neg (.objMem x a)))
      (.classEq (.cv b) (syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv x))))
  have p0110 := @g_snex (.cv y)
  have p0111 := @g_difex (.cv a) (syn_csn (.cv y)) p0011 p0110
  have p0112 := @g_eleq12 (.cv z) (.cv x) (.cv c) (syn_cdif (.cv a) (syn_csn (.cv y)))
  have p0113_e00_recanon :
    Nominal.NPrf
      (.imp (syn_wa (.objEq z x) (.classEq (.cv c) (syn_cdif (.cv a) (syn_csn (.cv y)))))
        (syn_wb (.objMem z c) (.classMem (.cv x) (syn_cdif (.cv a) (syn_csn (.cv y)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wa syn_cdif syn_cin syn_ccompl syn_cnin syn_wnan syn_csn syn_wb
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
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
      p0112
  have p0113 :=
    @g_ancoms (.objEq z x) (.classEq (.cv c) (syn_cdif (.cv a) (syn_csn (.cv y))))
      (syn_wb (.objMem z c) (.classMem (.cv x) (syn_cdif (.cv a) (syn_csn (.cv y)))))
      p0113_e00_recanon
  have p0114 :=
    @g_notbid
      (syn_wa (.classEq (.cv c) (syn_cdif (.cv a) (syn_csn (.cv y)))) (.objEq z x))
      (.objMem z c) (.classMem (.cv x) (syn_cdif (.cv a) (syn_csn (.cv y)))) p0113
  have p0115 := @g_sneq (.cv z) (.cv x)
  have p0116 :=
    @g_uneq12 (.cv c) (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv z))
      (syn_csn (.cv x))
  have p0117_e00_recanon :
    Nominal.NPrf (.imp (.objEq z x) (.classEq (syn_csn (.cv z)) (syn_csn (.cv x)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_csn
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0115
  have p0117 :=
    @g_sylan2 (.objEq z x) (.classEq (.cv c) (syn_cdif (.cv a) (syn_csn (.cv y))))
      (.classEq (syn_csn (.cv z)) (syn_csn (.cv x)))
      (.classEq (syn_cun (.cv c) (syn_csn (.cv z)))
        (syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv x))))
      p0117_e00_recanon p0116
  have p0118 :=
    @g_eleq1d
      (syn_wa (.classEq (.cv c) (syn_cdif (.cv a) (syn_csn (.cv y)))) (.objEq z x))
      (syn_cun (.cv c) (syn_csn (.cv z)))
      (syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv x)))
      (syn_cplc (.cv n) (syn_c1c)) p0117
  have p0119 :=
    @g_anbi12d
      (syn_wa (.classEq (.cv c) (syn_cdif (.cv a) (syn_csn (.cv y)))) (.objEq z x))
      (.neg (.objMem z c)) (.neg (.classMem (.cv x) (syn_cdif (.cv a) (syn_csn (.cv y)))))
      (.classMem (syn_cun (.cv c) (syn_csn (.cv z))) (syn_cplc (.cv n) (syn_c1c)))
      (.classMem (syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv x)))
        (syn_cplc (.cv n) (syn_c1c)))
      p0114 p0118
  have p0120 := @g_eleq1 (.cv c) (syn_cdif (.cv a) (syn_csn (.cv y))) (.cv n)
  have p0121_e00_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv c) (syn_cdif (.cv a) (syn_csn (.cv y)))) (syn_wb (.objMem c n)
          (.classMem (syn_cdif (.cv a) (syn_csn (.cv y))) (.cv n)))) :=
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
      p0120
  have p0121 :=
    @g_adantr (.classEq (.cv c) (syn_cdif (.cv a) (syn_csn (.cv y))))
      (syn_wb (.objMem c n) (.classMem (syn_cdif (.cv a) (syn_csn (.cv y))) (.cv n)))
      (.objEq z x) p0121_e00_recanon
  have p0122 :=
    @g_imbi12d
      (syn_wa (.classEq (.cv c) (syn_cdif (.cv a) (syn_csn (.cv y)))) (.objEq z x))
      (syn_wa (.neg (.objMem z c))
        (.classMem (syn_cun (.cv c) (syn_csn (.cv z))) (syn_cplc (.cv n) (syn_c1c))))
      (syn_wa (.neg (.classMem (.cv x) (syn_cdif (.cv a) (syn_csn (.cv y)))))
        (.classMem (syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv x)))
          (syn_cplc (.cv n) (syn_c1c))))
      (.objMem c n) (.classMem (syn_cdif (.cv a) (syn_csn (.cv y))) (.cv n)) p0119 p0121
  have p0123_e00_recanon :
    Nominal.NPrf
      (.imp (syn_wa (.classEq (.cv c) (syn_cdif (.cv a) (syn_csn (.cv y))))
          (.classEq (.cv z) (.cv x))) (syn_wb (.imp (syn_wa (.neg (.objMem z c))
              (.classMem (syn_cun (.cv c) (syn_csn (.cv z))) (syn_cplc (.cv n) (syn_c1c))))
            (.objMem c n)) (.imp
            (syn_wa (.neg (.classMem (.cv x) (syn_cdif (.cv a) (syn_csn (.cv y)))))
              (.classMem (syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv x)))
                (syn_cplc (.cv n) (syn_c1c))))
            (.classMem (syn_cdif (.cv a) (syn_csn (.cv y))) (.cv n))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wa syn_cdif syn_cin syn_ccompl syn_cnin syn_wnan syn_csn syn_wb
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0122
  have freeVariableCertificate16 : c ∉ ((syn_cdif (.cv a) (syn_csn (.cv y)))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
      Finset.mem_singleton, fresh_c_ne_a, fresh_c_ne_y, or_false, not_false_eq_true]
  have freeVariableCertificate17 : z ∉ ((syn_cdif (.cv a) (syn_csn (.cv y)))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
      Finset.mem_singleton, fresh_z_ne_a, fresh_z_ne_y, or_false, not_false_eq_true]
  have freeVariableCertificate18 : c ∉ ((Class.cv x)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_c_ne_x, not_false_eq_true]
  have freeVariableCertificate19 : z ∉ ((Class.cv x)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_z_ne_x, not_false_eq_true]
  have freeVariableCertificate20 :
    c ∉
      ((Wff.imp (syn_wa (.neg (.classMem (.cv x) (syn_cdif (.cv a) (syn_csn (.cv y)))))
            (.classMem (syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv x)))
              (syn_cplc (.cv n) (syn_c1c))))
          (.classMem (syn_cdif (.cv a) (syn_csn (.cv y))) (.cv n)))).fv :=
    by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
      NFChoice.Compiler.CoreFVSimp.fv_wff_neg,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_c_ne_x, fresh_c_ne_a, fresh_c_ne_y,
      fresh_c_ne_n, or_false, not_false_eq_true]
  have freeVariableCertificate21 :
    z ∉
      ((Wff.imp (syn_wa (.neg (.classMem (.cv x) (syn_cdif (.cv a) (syn_csn (.cv y)))))
            (.classMem (syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv x)))
              (syn_cplc (.cv n) (syn_c1c))))
          (.classMem (syn_cdif (.cv a) (syn_csn (.cv y))) (.cv n)))).fv :=
    by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
      NFChoice.Compiler.CoreFVSimp.fv_wff_neg,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_z_ne_x, fresh_z_ne_a, fresh_z_ne_y,
      fresh_z_ne_n, or_false, not_false_eq_true]
  have p0123 :=
    @g_spc2gv
      (.imp (syn_wa (.neg (.objMem z c))
          (.classMem (syn_cun (.cv c) (syn_csn (.cv z))) (syn_cplc (.cv n) (syn_c1c))))
        (.objMem c n))
      (.imp (syn_wa (.neg (.classMem (.cv x) (syn_cdif (.cv a) (syn_csn (.cv y)))))
          (.classMem (syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv x)))
            (syn_cplc (.cv n) (syn_c1c))))
        (.classMem (syn_cdif (.cv a) (syn_csn (.cv y))) (.cv n)))
      c z (syn_cdif (.cv a) (syn_csn (.cv y))) (.cv x) (syn_cvv) (syn_cvv)
      freeVariableCertificate16 freeVariableCertificate17 freeVariableCertificate18
      freeVariableCertificate19 freeVariableCertificate20 freeVariableCertificate21
      (show c ≠ z from (by exact fresh_c_ne_z)) p0123_e00_recanon
  have p0124 :=
    @g_mp2an (.classMem (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_cvv))
      (.classMem (.cv x) (syn_cvv))
      (.imp (.all c (.all z (.imp (syn_wa (.neg (.objMem z c))
                (.classMem (syn_cun (.cv c) (syn_csn (.cv z))) (syn_cplc (.cv n) (syn_c1c))))
              (.objMem c n)))) (.imp
          (syn_wa (.neg (.classMem (.cv x) (syn_cdif (.cv a) (syn_csn (.cv y)))))
            (.classMem (syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv x)))
              (syn_cplc (.cv n) (syn_c1c))))
          (.classMem (syn_cdif (.cv a) (syn_csn (.cv y))) (.cv n))))
      p0111 p0048 p0123
  have p0125 :=
    @g_syl
      (syn_wa (syn_w3a (.all c (.all z (.imp (syn_wa (.neg (.objMem z c))
                  (.classMem (syn_cun (.cv c) (syn_csn (.cv z))) (syn_cplc (.cv n) (syn_c1c))))
                (.objMem c n))))
          (syn_wa (.classMem (.cv b) (syn_cplc (.cv n) (syn_c1c))) (.neg (.objMem y b))) (syn_wa
            (.classEq (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cun (.cv b) (syn_csn (.cv y))))
            (.neg (.objMem x a)))) (.classEq (.cv b)
          (syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv x)))))
      (.all c (.all z (.imp (syn_wa (.neg (.objMem z c))
              (.classMem (syn_cun (.cv c) (syn_csn (.cv z))) (syn_cplc (.cv n) (syn_c1c))))
            (.objMem c n))))
      (.imp (syn_wa (.neg (.classMem (.cv x) (syn_cdif (.cv a) (syn_csn (.cv y)))))
          (.classMem (syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv x)))
            (syn_cplc (.cv n) (syn_c1c))))
        (.classMem (syn_cdif (.cv a) (syn_csn (.cv y))) (.cv n)))
      p0109 p0124
  have p0126 :=
    @g_mp2and
      (syn_wa (syn_w3a (.all c (.all z (.imp (syn_wa (.neg (.objMem z c))
                  (.classMem (syn_cun (.cv c) (syn_csn (.cv z))) (syn_cplc (.cv n) (syn_c1c))))
                (.objMem c n))))
          (syn_wa (.classMem (.cv b) (syn_cplc (.cv n) (syn_c1c))) (.neg (.objMem y b))) (syn_wa
            (.classEq (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cun (.cv b) (syn_csn (.cv y))))
            (.neg (.objMem x a)))) (.classEq (.cv b)
          (syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv x)))))
      (.neg (.classMem (.cv x) (syn_cdif (.cv a) (syn_csn (.cv y)))))
      (.classMem (syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv x)))
        (syn_cplc (.cv n) (syn_c1c)))
      (.classMem (syn_cdif (.cv a) (syn_csn (.cv y))) (.cv n)) p0104 p0108 p0125
  have p0127 :=
    @g_n_3adant1
      (syn_w3a (.all c (.all z (.imp (syn_wa (.neg (.objMem z c))
                (.classMem (syn_cun (.cv c) (syn_csn (.cv z))) (syn_cplc (.cv n) (syn_c1c))))
              (.objMem c n))))
        (syn_wa (.classMem (.cv b) (syn_cplc (.cv n) (syn_c1c))) (.neg (.objMem y b))) (syn_wa
          (.classEq (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cun (.cv b) (syn_csn (.cv y))))
          (.neg (.objMem x a))))
      (.classEq (.cv b) (syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv x))))
      (.classMem (syn_cdif (.cv a) (syn_csn (.cv y))) (.cv n)) (syn_wne (.cv x) (.cv y))
      p0126
  have p0128 := @g_snid (.cv y) p0060
  have p0129 := @g_eldif (.cv y) (.cv a) (syn_csn (.cv y))
  have p0130_e00_recanon :
    Nominal.NPrf
      (syn_wb (.classMem (.cv y) (syn_cdif (.cv a) (syn_csn (.cv y))))
        (syn_wa (.objMem y a) (.neg (.classMem (.cv y) (syn_csn (.cv y)))))) :=
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
      p0129
  have p0130 :=
    @g_simprbi (.classMem (.cv y) (syn_cdif (.cv a) (syn_csn (.cv y)))) (.objMem y a)
      (.neg (.classMem (.cv y) (syn_csn (.cv y)))) p0130_e00_recanon
  have p0131 :=
    @g_mt2 (.classMem (.cv y) (syn_cdif (.cv a) (syn_csn (.cv y))))
      (.classMem (.cv y) (syn_csn (.cv y))) p0128 p0130
  have p0132 := @g_elcompl (.cv y) (syn_cdif (.cv a) (syn_csn (.cv y))) p0060
  have p0133 :=
    @g_mpbir (.classMem (.cv y) (syn_ccompl (syn_cdif (.cv a) (syn_csn (.cv y)))))
      (.neg (.classMem (.cv y) (syn_cdif (.cv a) (syn_csn (.cv y))))) p0131 p0132
  have p0134 := @g_eqid (syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv y)))
  have p0135 := @g_sneq (.cv w) (.cv y)
  have p0136_e00_recanon :
    Nominal.NPrf (.imp (.objEq w y) (.classEq (syn_csn (.cv w)) (syn_csn (.cv y)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_csn
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0135
  have p0136 :=
    @g_uneq2d (.objEq w y) (syn_csn (.cv w)) (syn_csn (.cv y))
      (syn_cdif (.cv a) (syn_csn (.cv y))) p0136_e00_recanon
  have p0137 :=
    @g_eqeq2d (.objEq w y)
      (syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv w)))
      (syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv y)))
      (syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv y))) p0136
  have p0138_e00_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv w) (.cv y)) (syn_wb
          (.classEq (syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv y)))
            (syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv w))))
          (.classEq (syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv y)))
            (syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv y)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_cdif syn_cin syn_csn
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0137
  have freeVariableCertificate22 : w ∉ ((Class.cv y)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_w_ne_y, not_false_eq_true]
  have freeVariableCertificate23 :
    w ∉ ((syn_ccompl (syn_cdif (.cv a) (syn_csn (.cv y))))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
      Finset.mem_singleton, fresh_w_ne_a, fresh_w_ne_y, or_false, not_false_eq_true]
  have freeVariableCertificate24 :
    w ∉
      ((Wff.classEq (syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv y)))
          (syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv y))))).fv :=
    by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
      Finset.mem_singleton, fresh_w_ne_a, fresh_w_ne_y, or_false, not_false_eq_true]
  have p0138 :=
    @g_rspcev
      (.classEq (syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv y)))
        (syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv w))))
      (.classEq (syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv y)))
        (syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv y))))
      w (.cv y) (syn_ccompl (syn_cdif (.cv a) (syn_csn (.cv y))))
      freeVariableCertificate22 freeVariableCertificate23 freeVariableCertificate24
      p0138_e00_recanon
  have p0139 :=
    @g_mp2an (.classMem (.cv y) (syn_ccompl (syn_cdif (.cv a) (syn_csn (.cv y)))))
      (.classEq (syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv y)))
        (syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv y))))
      (syn_wrex w (syn_ccompl (syn_cdif (.cv a) (syn_csn (.cv y))))
        (.classEq (syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv y)))
          (syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv w)))))
      p0133 p0134 p0138
  have p0140 := @g_compleq (.cv d) (syn_cdif (.cv a) (syn_csn (.cv y)))
  have p0141 := @g_uneq1 (.cv d) (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv w))
  have p0142 :=
    @g_eqeq2d (.classEq (.cv d) (syn_cdif (.cv a) (syn_csn (.cv y))))
      (syn_cun (.cv d) (syn_csn (.cv w)))
      (syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv w)))
      (syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv y))) p0141
  have freeVariableCertificate25 : w ∉ ((syn_ccompl (.cv d))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_w_ne_d,
      not_false_eq_true]
  have freeVariableCertificate26 :
    w ∉ ((Wff.classEq (.cv d) (syn_cdif (.cv a) (syn_csn (.cv y))))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
      Finset.mem_singleton, fresh_w_ne_d, fresh_w_ne_a, fresh_w_ne_y, or_false,
      not_false_eq_true]
  have p0143 :=
    @g_rexeqbidv (.classEq (.cv d) (syn_cdif (.cv a) (syn_csn (.cv y))))
      (.classEq (syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv y)))
        (syn_cun (.cv d) (syn_csn (.cv w))))
      (.classEq (syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv y)))
        (syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv w))))
      w (syn_ccompl (.cv d)) (syn_ccompl (syn_cdif (.cv a) (syn_csn (.cv y))))
      freeVariableCertificate25 freeVariableCertificate23 freeVariableCertificate26 p0140
      p0142
  have freeVariableCertificate27 : d ∉ ((syn_cdif (.cv a) (syn_csn (.cv y)))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
      Finset.mem_singleton, fresh_d_ne_a, fresh_d_ne_y, or_false, not_false_eq_true]
  have freeVariableCertificate28 : d ∉ ((Class.cv n)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_d_ne_n, not_false_eq_true]
  have freeVariableCertificate29 :
    d ∉
      ((syn_wrex w (syn_ccompl (syn_cdif (.cv a) (syn_csn (.cv y))))
          (.classEq (syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv y)))
            (syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv w)))))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, Finset.mem_union,
      Finset.mem_erase, Finset.mem_singleton, fresh_d_ne_a, fresh_d_ne_y, fresh_d_ne_w,
      or_false, and_false, not_false_eq_true]
  have p0144 :=
    @g_rspcev
      (syn_wrex w (syn_ccompl (.cv d))
        (.classEq (syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv y)))
          (syn_cun (.cv d) (syn_csn (.cv w)))))
      (syn_wrex w (syn_ccompl (syn_cdif (.cv a) (syn_csn (.cv y))))
        (.classEq (syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv y)))
          (syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv w)))))
      d (syn_cdif (.cv a) (syn_csn (.cv y))) (.cv n) freeVariableCertificate27
      freeVariableCertificate28 freeVariableCertificate29 p0143
  have freeVariableCertificate30 :
    d ∉ ((syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv y)))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
      Finset.mem_singleton, fresh_d_ne_a, fresh_d_ne_y, or_false, not_false_eq_true]
  have freeVariableCertificate31 :
    w ∉ ((syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv y)))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
      Finset.mem_singleton, fresh_w_ne_a, fresh_w_ne_y, or_false, not_false_eq_true]
  have p0145 :=
    @g_elsuc w (syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv y))) (.cv n) d
      freeVariableCertificate30 freeVariableCertificate31 freeVariableCertificate28
      (show d ≠ w from (by exact fresh_d_ne_w))
  have p0146 :=
    @g_sylibr
      (syn_wa (.classMem (syn_cdif (.cv a) (syn_csn (.cv y))) (.cv n))
        (syn_wrex w (syn_ccompl (syn_cdif (.cv a) (syn_csn (.cv y))))
          (.classEq (syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv y)))
            (syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv w))))))
      (syn_wrex d (.cv n) (syn_wrex w (syn_ccompl (.cv d))
          (.classEq (syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv y)))
            (syn_cun (.cv d) (syn_csn (.cv w))))))
      (.classMem (syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv y)))
        (syn_cplc (.cv n) (syn_c1c)))
      p0144 p0145
  have p0147 :=
    @g_sylancl
      (syn_w3a (syn_wne (.cv x) (.cv y)) (syn_w3a (.all c (.all z (.imp
                (syn_wa (.neg (.objMem z c)) (.classMem (syn_cun (.cv c) (syn_csn (.cv z)))
                    (syn_cplc (.cv n) (syn_c1c)))) (.objMem c n))))
          (syn_wa (.classMem (.cv b) (syn_cplc (.cv n) (syn_c1c))) (.neg (.objMem y b))) (syn_wa
            (.classEq (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cun (.cv b) (syn_csn (.cv y))))
            (.neg (.objMem x a)))) (.classEq (.cv b)
          (syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv x)))))
      (.classMem (syn_cdif (.cv a) (syn_csn (.cv y))) (.cv n))
      (syn_wrex w (syn_ccompl (syn_cdif (.cv a) (syn_csn (.cv y))))
        (.classEq (syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv y)))
          (syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv w)))))
      (.classMem (syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv y)))
        (syn_cplc (.cv n) (syn_c1c)))
      p0127 p0139 p0146
  have p0148 :=
    @g_eqeltrrd
      (syn_w3a (syn_wne (.cv x) (.cv y)) (syn_w3a (.all c (.all z (.imp
                (syn_wa (.neg (.objMem z c)) (.classMem (syn_cun (.cv c) (syn_csn (.cv z)))
                    (syn_cplc (.cv n) (syn_c1c)))) (.objMem c n))))
          (syn_wa (.classMem (.cv b) (syn_cplc (.cv n) (syn_c1c))) (.neg (.objMem y b))) (syn_wa
            (.classEq (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cun (.cv b) (syn_csn (.cv y))))
            (.neg (.objMem x a)))) (.classEq (.cv b)
          (syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv x)))))
      (syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv y))) (.cv a)
      (syn_cplc (.cv n) (syn_c1c)) p0100 p0147
  have p0149 :=
    @g_mpd3an3 (syn_wne (.cv x) (.cv y))
      (syn_w3a (.all c (.all z (.imp (syn_wa (.neg (.objMem z c))
                (.classMem (syn_cun (.cv c) (syn_csn (.cv z))) (syn_cplc (.cv n) (syn_c1c))))
              (.objMem c n))))
        (syn_wa (.classMem (.cv b) (syn_cplc (.cv n) (syn_c1c))) (.neg (.objMem y b))) (syn_wa
          (.classEq (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cun (.cv b) (syn_csn (.cv y))))
          (.neg (.objMem x a))))
      (.classEq (.cv b) (syn_cun (syn_cdif (.cv a) (syn_csn (.cv y))) (syn_csn (.cv x))))
      (.classMem (.cv a) (syn_cplc (.cv n) (syn_c1c))) p0082 p0148
  have p0150 :=
    @g_ex (syn_wne (.cv x) (.cv y))
      (syn_w3a (.all c (.all z (.imp (syn_wa (.neg (.objMem z c))
                (.classMem (syn_cun (.cv c) (syn_csn (.cv z))) (syn_cplc (.cv n) (syn_c1c))))
              (.objMem c n))))
        (syn_wa (.classMem (.cv b) (syn_cplc (.cv n) (syn_c1c))) (.neg (.objMem y b))) (syn_wa
          (.classEq (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cun (.cv b) (syn_csn (.cv y))))
          (.neg (.objMem x a))))
      (.classMem (.cv a) (syn_cplc (.cv n) (syn_c1c))) p0149
  have p0151_e00_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv x) (.cv y)) (.imp (syn_w3a (.all c (.all z (.imp
                  (syn_wa (.neg (.objMem z c)) (.classMem (syn_cun (.cv c) (syn_csn (.cv z)))
                      (syn_cplc (.cv n) (syn_c1c)))) (.objMem c n))))
            (syn_wa (.classMem (.cv b) (syn_cplc (.cv n) (syn_c1c))) (.neg (.objMem y b)))
            (syn_wa (.classEq (syn_cun (.cv a) (syn_csn (.cv x)))
                (syn_cun (.cv b) (syn_csn (.cv y)))) (.neg (.objMem x a))))
          (.classMem (.cv a) (syn_cplc (.cv n) (syn_c1c))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_w3a syn_wa syn_cplc syn_wrex syn_wex syn_c1c
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0077
  have p0151 :=
    @g_pm2_61ine
      (.imp (syn_w3a (.all c (.all z (.imp (syn_wa (.neg (.objMem z c))
                  (.classMem (syn_cun (.cv c) (syn_csn (.cv z))) (syn_cplc (.cv n) (syn_c1c))))
                (.objMem c n))))
          (syn_wa (.classMem (.cv b) (syn_cplc (.cv n) (syn_c1c))) (.neg (.objMem y b))) (syn_wa
            (.classEq (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cun (.cv b) (syn_csn (.cv y))))
            (.neg (.objMem x a)))) (.classMem (.cv a) (syn_cplc (.cv n) (syn_c1c))))
      (.cv x) (.cv y) p0151_e00_recanon p0150
  have p0152 :=
    @g_n_3expa
      (.all c (.all z (.imp (syn_wa (.neg (.objMem z c))
              (.classMem (syn_cun (.cv c) (syn_csn (.cv z))) (syn_cplc (.cv n) (syn_c1c))))
            (.objMem c n))))
      (syn_wa (.classMem (.cv b) (syn_cplc (.cv n) (syn_c1c))) (.neg (.objMem y b)))
      (syn_wa (.classEq (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cun (.cv b) (syn_csn (.cv y))))
        (.neg (.objMem x a)))
      (.classMem (.cv a) (syn_cplc (.cv n) (syn_c1c))) p0151
  have p0153 :=
    @g_exp32
      (syn_wa (.all c (.all z (.imp (syn_wa (.neg (.objMem z c))
                (.classMem (syn_cun (.cv c) (syn_csn (.cv z))) (syn_cplc (.cv n) (syn_c1c))))
              (.objMem c n))))
        (syn_wa (.classMem (.cv b) (syn_cplc (.cv n) (syn_c1c))) (.neg (.objMem y b))))
      (.classEq (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cun (.cv b) (syn_csn (.cv y))))
      (.neg (.objMem x a)) (.classMem (.cv a) (syn_cplc (.cv n) (syn_c1c))) p0152
  have p0154 :=
    @g_sylan2b
      (syn_wa (.classMem (.cv b) (syn_cplc (.cv n) (syn_c1c)))
        (.classMem (.cv y) (syn_ccompl (.cv b))))
      (.all c (.all z (.imp (syn_wa (.neg (.objMem z c))
              (.classMem (syn_cun (.cv c) (syn_csn (.cv z))) (syn_cplc (.cv n) (syn_c1c))))
            (.objMem c n))))
      (syn_wa (.classMem (.cv b) (syn_cplc (.cv n) (syn_c1c))) (.neg (.objMem y b)))
      (.imp (.classEq (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cun (.cv b) (syn_csn (.cv y))))
        (.imp (.neg (.objMem x a)) (.classMem (.cv a) (syn_cplc (.cv n) (syn_c1c)))))
      p0062 p0153
  have freeVariableCertificate32 : y ∉ ((syn_cplc (.cv n) (syn_c1c))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_y_ne_n, or_false,
      not_false_eq_true]
  have freeVariableCertificate33 :
    b ∉
      ((Wff.imp (.neg (.objMem x a)) (.classMem (.cv a) (syn_cplc (.cv n) (syn_c1c))))).fv :=
    by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
      NFChoice.Compiler.CoreFVSimp.fv_wff_neg, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
      Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, fresh_b_ne_x,
      fresh_b_ne_a, fresh_b_ne_n, or_false, not_false_eq_true]
  have freeVariableCertificate34 :
    y ∉
      ((Wff.imp (.neg (.objMem x a)) (.classMem (.cv a) (syn_cplc (.cv n) (syn_c1c))))).fv :=
    by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
      NFChoice.Compiler.CoreFVSimp.fv_wff_neg, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
      Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, fresh_y_ne_x,
      fresh_y_ne_a, fresh_y_ne_n, or_false, not_false_eq_true]
  have freeVariableCertificate35 :
    b ∉
      ((Wff.all c (.all z (.imp (syn_wa (.neg (.objMem z c))
                (.classMem (syn_cun (.cv c) (syn_csn (.cv z))) (syn_cplc (.cv n) (syn_c1c))))
              (.objMem c n))))).fv :=
    by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_all,
      NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
      NFChoice.Compiler.CoreFVSimp.fv_wff_neg, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
      Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty,
      fresh_b_ne_z, fresh_b_ne_c, fresh_b_ne_n, or_false, and_false, not_false_eq_true]
  have freeVariableCertificate36 :
    y ∉
      ((Wff.all c (.all z (.imp (syn_wa (.neg (.objMem z c))
                (.classMem (syn_cun (.cv c) (syn_csn (.cv z))) (syn_cplc (.cv n) (syn_c1c))))
              (.objMem c n))))).fv :=
    by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_all,
      NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
      NFChoice.Compiler.CoreFVSimp.fv_wff_neg, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
      Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty,
      fresh_y_ne_z, fresh_y_ne_c, fresh_y_ne_n, or_false, and_false, not_false_eq_true]
  have p0155 :=
    @g_rexlimdvva
      (.all c (.all z (.imp (syn_wa (.neg (.objMem z c))
              (.classMem (syn_cun (.cv c) (syn_csn (.cv z))) (syn_cplc (.cv n) (syn_c1c))))
            (.objMem c n))))
      (.classEq (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cun (.cv b) (syn_csn (.cv y))))
      (.imp (.neg (.objMem x a)) (.classMem (.cv a) (syn_cplc (.cv n) (syn_c1c)))) b y
      (syn_cplc (.cv n) (syn_c1c)) (syn_ccompl (.cv b)) freeVariableCertificate32
      freeVariableCertificate33 freeVariableCertificate34 freeVariableCertificate35
      freeVariableCertificate36 (show b ≠ y from (by exact fresh_b_ne_y)) p0154
  have p0156 :=
    @g_syl5bi
      (.classMem (syn_cun (.cv a) (syn_csn (.cv x)))
        (syn_cplc (syn_cplc (.cv n) (syn_c1c)) (syn_c1c)))
      (syn_wrex b (syn_cplc (.cv n) (syn_c1c)) (syn_wrex y (syn_ccompl (.cv b))
          (.classEq (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cun (.cv b) (syn_csn (.cv y))))))
      (.all c (.all z (.imp (syn_wa (.neg (.objMem z c))
              (.classMem (syn_cun (.cv c) (syn_csn (.cv z))) (syn_cplc (.cv n) (syn_c1c))))
            (.objMem c n))))
      (.imp (.neg (.objMem x a)) (.classMem (.cv a) (syn_cplc (.cv n) (syn_c1c)))) p0059
      p0155
  have p0157 :=
    @g_com23
      (.all c (.all z (.imp (syn_wa (.neg (.objMem z c))
              (.classMem (syn_cun (.cv c) (syn_csn (.cv z))) (syn_cplc (.cv n) (syn_c1c))))
            (.objMem c n))))
      (.classMem (syn_cun (.cv a) (syn_csn (.cv x)))
        (syn_cplc (syn_cplc (.cv n) (syn_c1c)) (syn_c1c)))
      (.neg (.objMem x a)) (.classMem (.cv a) (syn_cplc (.cv n) (syn_c1c))) p0156
  have p0158 :=
    @g_imp3a
      (.all c (.all z (.imp (syn_wa (.neg (.objMem z c))
              (.classMem (syn_cun (.cv c) (syn_csn (.cv z))) (syn_cplc (.cv n) (syn_c1c))))
            (.objMem c n))))
      (.neg (.objMem x a))
      (.classMem (syn_cun (.cv a) (syn_csn (.cv x)))
        (syn_cplc (syn_cplc (.cv n) (syn_c1c)) (syn_c1c)))
      (.classMem (.cv a) (syn_cplc (.cv n) (syn_c1c))) p0157
  have freeVariableCertificate37 :
    a ∉
      ((Wff.all c (.all z (.imp (syn_wa (.neg (.objMem z c))
                (.classMem (syn_cun (.cv c) (syn_csn (.cv z))) (syn_cplc (.cv n) (syn_c1c))))
              (.objMem c n))))).fv :=
    by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_all,
      NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
      NFChoice.Compiler.CoreFVSimp.fv_wff_neg, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
      Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty,
      fresh_a_ne_z, fresh_a_ne_c, fresh_a_ne_n, or_false, and_false, not_false_eq_true]
  have freeVariableCertificate38 :
    x ∉
      ((Wff.all c (.all z (.imp (syn_wa (.neg (.objMem z c))
                (.classMem (syn_cun (.cv c) (syn_csn (.cv z))) (syn_cplc (.cv n) (syn_c1c))))
              (.objMem c n))))).fv :=
    by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_all,
      NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
      NFChoice.Compiler.CoreFVSimp.fv_wff_neg, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
      Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty,
      fresh_x_ne_z, fresh_x_ne_c, fresh_x_ne_n, or_false, and_false, not_false_eq_true]
  have p0159 :=
    @g_alrimivv
      (.all c (.all z (.imp (syn_wa (.neg (.objMem z c))
              (.classMem (syn_cun (.cv c) (syn_csn (.cv z))) (syn_cplc (.cv n) (syn_c1c))))
            (.objMem c n))))
      (.imp (syn_wa (.neg (.objMem x a)) (.classMem (syn_cun (.cv a) (syn_csn (.cv x)))
            (syn_cplc (syn_cplc (.cv n) (syn_c1c)) (syn_c1c))))
        (.classMem (.cv a) (syn_cplc (.cv n) (syn_c1c))))
      a x freeVariableCertificate37 freeVariableCertificate38 p0158
  have p0160 :=
    @g_a1i
      (.imp (.all c (.all z (.imp (syn_wa (.neg (.objMem z c))
                (.classMem (syn_cun (.cv c) (syn_csn (.cv z))) (syn_cplc (.cv n) (syn_c1c))))
              (.objMem c n)))) (.all a (.all x (.imp (syn_wa (.neg (.objMem x a))
                (.classMem (syn_cun (.cv a) (syn_csn (.cv x)))
                  (syn_cplc (syn_cplc (.cv n) (syn_c1c)) (syn_c1c))))
              (.classMem (.cv a) (syn_cplc (.cv n) (syn_c1c)))))))
      (.classMem (.cv n) (syn_cnnc)) p0159
  have freeVariableCertificate39 :
    m ∉
      ((Wff.all c (.all z (.imp (syn_wa (.neg (.objMem z c))
                (.classMem (syn_cun (.cv c) (syn_csn (.cv z))) (syn_cplc (.cv n) (syn_c1c))))
              (.objMem c n))))).fv :=
    by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_all,
      NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
      NFChoice.Compiler.CoreFVSimp.fv_wff_neg, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
      Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty,
      fresh_m_ne_z, fresh_m_ne_c, fresh_m_ne_n, or_false, and_false, not_false_eq_true]
  have freeVariableCertificate40 :
    n ∉
      ((Wff.all a (.all x (.imp (syn_wa (.neg (.objMem x a))
                (.classMem (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cplc (.cv m) (syn_c1c))))
              (.objMem a m))))).fv :=
    by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_all,
      NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
      NFChoice.Compiler.CoreFVSimp.fv_wff_neg, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
      Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty,
      fresh_n_ne_x, fresh_n_ne_a, fresh_n_ne_m, or_false, and_false, not_false_eq_true]
  have freeVariableCertificate41 :
    m ∉
      ((Wff.all a (.all x (.imp (syn_wa (.neg (.objMem x a)) (syn_wex y
                  (.classEq (syn_cun (.cv a) (syn_csn (.cv x))) (syn_csn (.cv y)))))
              (.classEq (.cv a) (syn_c0)))))).fv :=
    by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_all,
      NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
      NFChoice.Compiler.CoreFVSimp.fv_wff_neg, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union,
      Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty,
      fresh_m_ne_x, fresh_m_ne_a, fresh_m_ne_y, or_false, and_false, not_false_eq_true]
  have freeVariableCertificate42 :
    m ∉
      ((Wff.all a (.all x (.imp (syn_wa (.neg (.objMem x a))
                (.classMem (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cplc M (syn_c1c))))
              (.classMem (.cv a) M))))).fv :=
    by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_all,
      NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
      NFChoice.Compiler.CoreFVSimp.fv_wff_neg, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
      Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty,
      fresh_m_ne_x, fresh_m_ne_a, fresh_m_not_M, or_false, and_false, not_false_eq_true]
  have freeVariableCertificate43 :
    m ∉
      ((Wff.all a (.all x (.imp (syn_wa (.neg (.objMem x a))
                (.classMem (syn_cun (.cv a) (syn_csn (.cv x)))
                  (syn_cplc (syn_cplc (.cv n) (syn_c1c)) (syn_c1c))))
              (.classMem (.cv a) (syn_cplc (.cv n) (syn_c1c))))))).fv :=
    by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_all,
      NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
      NFChoice.Compiler.CoreFVSimp.fv_wff_neg, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
      Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty,
      fresh_m_ne_x, fresh_m_ne_a, fresh_m_ne_n, or_false, and_false, not_false_eq_true]
  have p0161 :=
    @g_finds
      (.all a (.all x (.imp (syn_wa (.neg (.objMem x a))
              (.classMem (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cplc (.cv m) (syn_c1c))))
            (.objMem a m))))
      (.all a (.all x (.imp (syn_wa (.neg (.objMem x a)) (syn_wex y
                (.classEq (syn_cun (.cv a) (syn_csn (.cv x))) (syn_csn (.cv y)))))
            (.classEq (.cv a) (syn_c0)))))
      (.all c (.all z (.imp (syn_wa (.neg (.objMem z c))
              (.classMem (syn_cun (.cv c) (syn_csn (.cv z))) (syn_cplc (.cv n) (syn_c1c))))
            (.objMem c n))))
      (.all a (.all x (.imp (syn_wa (.neg (.objMem x a))
              (.classMem (syn_cun (.cv a) (syn_csn (.cv x)))
                (syn_cplc (syn_cplc (.cv n) (syn_c1c)) (syn_c1c))))
            (.classMem (.cv a) (syn_cplc (.cv n) (syn_c1c))))))
      (.all a (.all x (.imp (syn_wa (.neg (.objMem x a))
              (.classMem (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cplc M (syn_c1c))))
            (.classMem (.cv a) M))))
      m n M (by exact (show m ∉ (M).fv from (by exact fresh_m_not_M)))
      freeVariableCertificate39 freeVariableCertificate40 freeVariableCertificate41
      freeVariableCertificate42 freeVariableCertificate43
      (show m ≠ n from (by exact fresh_m_ne_n)) p0000 p0016 p0035 p0041 p0047 p0058 p0160
  have p0162 := @g_eleq1 (.cv x) X (.cv a)
  have p0163_e00_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv x) X) (syn_wb (.objMem x a) (.classMem X (.cv a)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb
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
      p0162
  have p0163 :=
    @g_notbid (.classEq (.cv x) X) (.objMem x a) (.classMem X (.cv a)) p0163_e00_recanon
  have p0164 := @g_sneq (.cv x) X
  have p0165 := @g_uneq2d (.classEq (.cv x) X) (syn_csn (.cv x)) (syn_csn X) (.cv a) p0164
  have p0166 :=
    @g_eleq1d (.classEq (.cv x) X) (syn_cun (.cv a) (syn_csn (.cv x)))
      (syn_cun (.cv a) (syn_csn X)) (syn_cplc M (syn_c1c)) p0165
  have p0167 :=
    @g_anbi12d (.classEq (.cv x) X) (.neg (.objMem x a)) (.neg (.classMem X (.cv a)))
      (.classMem (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cplc M (syn_c1c)))
      (.classMem (syn_cun (.cv a) (syn_csn X)) (syn_cplc M (syn_c1c))) p0163 p0166
  have p0168 :=
    @g_imbi1d (.classEq (.cv x) X)
      (syn_wa (.neg (.objMem x a))
        (.classMem (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cplc M (syn_c1c))))
      (syn_wa (.neg (.classMem X (.cv a)))
        (.classMem (syn_cun (.cv a) (syn_csn X)) (syn_cplc M (syn_c1c))))
      (.classMem (.cv a) M) p0167
  have freeVariableCertificate44 :
    x ∉
      ((Wff.imp (syn_wa (.neg (.classMem X (.cv a)))
            (.classMem (syn_cun (.cv a) (syn_csn X)) (syn_cplc M (syn_c1c))))
          (.classMem (.cv a) M))).fv :=
    by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
      NFChoice.Compiler.CoreFVSimp.fv_wff_neg,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_x_not_X, fresh_x_ne_a,
      fresh_x_not_M, or_false, not_false_eq_true]
  have p0169 :=
    @g_spcv
      (.imp (syn_wa (.neg (.objMem x a))
          (.classMem (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cplc M (syn_c1c))))
        (.classMem (.cv a) M))
      (.imp (syn_wa (.neg (.classMem X (.cv a)))
          (.classMem (syn_cun (.cv a) (syn_csn X)) (syn_cplc M (syn_c1c))))
        (.classMem (.cv a) M))
      x X (by exact (show x ∉ (X).fv from (by exact fresh_x_not_X)))
      freeVariableCertificate44 hyp_nnsucelr_2 p0168
  have p0170 :=
    @g_alimi
      (.all x (.imp (syn_wa (.neg (.objMem x a))
            (.classMem (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cplc M (syn_c1c))))
          (.classMem (.cv a) M)))
      (.imp (syn_wa (.neg (.classMem X (.cv a)))
          (.classMem (syn_cun (.cv a) (syn_csn X)) (syn_cplc M (syn_c1c))))
        (.classMem (.cv a) M))
      a p0169
  have p0171 := @g_eleq2 (.cv a) A X
  have p0172 := @g_notbid (.classEq (.cv a) A) (.classMem X (.cv a)) (.classMem X A) p0171
  have p0173 := @g_uneq1 (.cv a) A (syn_csn X)
  have p0174 :=
    @g_eleq1d (.classEq (.cv a) A) (syn_cun (.cv a) (syn_csn X)) (syn_cun A (syn_csn X))
      (syn_cplc M (syn_c1c)) p0173
  have p0175 :=
    @g_anbi12d (.classEq (.cv a) A) (.neg (.classMem X (.cv a))) (.neg (.classMem X A))
      (.classMem (syn_cun (.cv a) (syn_csn X)) (syn_cplc M (syn_c1c)))
      (.classMem (syn_cun A (syn_csn X)) (syn_cplc M (syn_c1c))) p0172 p0174
  have p0176 := @g_eleq1 (.cv a) A M
  have p0177 :=
    @g_imbi12d (.classEq (.cv a) A)
      (syn_wa (.neg (.classMem X (.cv a)))
        (.classMem (syn_cun (.cv a) (syn_csn X)) (syn_cplc M (syn_c1c))))
      (syn_wa (.neg (.classMem X A)) (.classMem (syn_cun A (syn_csn X)) (syn_cplc M (syn_c1c))))
      (.classMem (.cv a) M) (.classMem A M) p0175 p0176
  have freeVariableCertificate45 :
    a ∉
      ((Wff.imp (syn_wa (.neg (.classMem X A))
            (.classMem (syn_cun A (syn_csn X)) (syn_cplc M (syn_c1c)))) (.classMem A M))).fv :=
    by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
      NFChoice.Compiler.CoreFVSimp.fv_wff_neg,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
      Finset.notMem_empty, fresh_a_not_X, fresh_a_not_A, fresh_a_not_M, or_false,
      not_false_eq_true]
  have p0178 :=
    @g_spcv
      (.imp (syn_wa (.neg (.classMem X (.cv a)))
          (.classMem (syn_cun (.cv a) (syn_csn X)) (syn_cplc M (syn_c1c))))
        (.classMem (.cv a) M))
      (.imp (syn_wa (.neg (.classMem X A))
          (.classMem (syn_cun A (syn_csn X)) (syn_cplc M (syn_c1c)))) (.classMem A M))
      a A (by exact (show a ∉ (A).fv from (by exact fresh_a_not_A)))
      freeVariableCertificate45 hyp_nnsucelr_1 p0177
  have p0179 :=
    @g_n_3syl (.classMem M (syn_cnnc))
      (.all a (.all x (.imp (syn_wa (.neg (.objMem x a))
              (.classMem (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cplc M (syn_c1c))))
            (.classMem (.cv a) M))))
      (.all a (.imp (syn_wa (.neg (.classMem X (.cv a)))
            (.classMem (syn_cun (.cv a) (syn_csn X)) (syn_cplc M (syn_c1c))))
          (.classMem (.cv a) M)))
      (.imp (syn_wa (.neg (.classMem X A))
          (.classMem (syn_cun A (syn_csn X)) (syn_cplc M (syn_c1c)))) (.classMem A M))
      p0161 p0170 p0178
  have p0180 :=
    @g_imp (.classMem M (syn_cnnc))
      (syn_wa (.neg (.classMem X A)) (.classMem (syn_cun A (syn_csn X)) (syn_cplc M (syn_c1c))))
      (.classMem A M) p0179
  exact p0180


end NFChoice.DirectNominalPrf.WPPReplay

end
