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

/-- Checked nominal proof certificate identified upstream as `g_nnsucelrlem1`. -/
@[expose]
noncomputable def gNnsucelrlem1 (x : Var) (m : Var) (a : Var) (dv_a_m : a ≠ m)
    (dv_a_x : a ≠ x) (dv_m_x : m ≠ x) :
    Nominal.NPrf
      (.classMem (.cab m (.all a (.all x (.imp (synWa (.neg (.objMem x a))
                  (.classMem (synCun (.cv a) (synCsn (.cv x))) (synCplc (.cv m) (synC1c))))
                (.objMem a m))))) (synCvv)) :=
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
    (synCins3k (synCsik (synCsik (synCsik (synCsik (synCsik (synCssetk)))))))
  let syntaxClass0001 : Class :=
    (synCun (synCins2k (synCins3k (synCsik (synCssetk)))) (synCins3k (synCidk)))
  let syntaxClass0002 : Class := (synCins2k syntaxClass0001)
  let syntaxClass0003 : Class := (synCsymdif syntaxClass0000 syntaxClass0002)
  let syntaxClass0004 : Class :=
    (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
  let syntaxClass0005 : Class := (synCimak syntaxClass0003 syntaxClass0004)
  let syntaxClass0006 : Class := (synCcompl syntaxClass0005)
  let syntaxClass0007 : Class :=
    (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
      (synCpw1 (synCpw1 (synC1c))))
  let syntaxClass0008 : Class := (synCcompl syntaxClass0007)
  let syntaxClass0009 : Class := (synCins3k syntaxClass0008)
  let syntaxClass0010 : Class :=
    (synCun (synCins2k (synCins3k (synCssetk)))
      (synCins3k (synCsik (synCsik (synCssetk)))))
  let syntaxClass0011 : Class :=
    (synCsymdif (synCins2k (synCins2k (synCssetk))) syntaxClass0010)
  let syntaxClass0012 : Class :=
    (synCimak syntaxClass0011 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))
  let syntaxClass0013 : Class := (synCdif syntaxClass0009 syntaxClass0012)
  let syntaxClass0014 : Class :=
    (synCimak syntaxClass0013 (synCpw1 (synCpw1 (synC1c))))
  let syntaxClass0015 : Class := (synCimagek syntaxClass0014)
  let syntaxClass0016 : Class := (synCcnvk syntaxClass0015)
  let syntaxClass0017 : Class := (synCcomk syntaxClass0016 (synCssetk))
  let syntaxClass0018 : Class := (synCins2k syntaxClass0017)
  let syntaxClass0019 : Class := (synCins2k syntaxClass0018)
  let syntaxClass0020 : Class := (synCin syntaxClass0006 syntaxClass0019)
  let syntaxClass0021 : Class :=
    (synCimak syntaxClass0020 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))
  let syntaxClass0022 : Class :=
    (synCdif syntaxClass0021 (synCins3k (synCsik (synCssetk))))
  let syntaxClass0023 : Class :=
    (synCdif syntaxClass0022 (synCxpk (synCvv) (synCssetk)))
  let syntaxClass0024 : Class :=
    (synCimak syntaxClass0023 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))
  let syntaxFormula0025 : Wff := (.classMem (synCopk (.cv t) (.cv m)) syntaxClass0024)
  let syntaxFormula0026 : Wff := (synWrex t (synC1c) syntaxFormula0025)
  let syntaxFormula0027 : Wff := (synWa (.classMem (.cv t) (synC1c)) syntaxFormula0025)
  let syntaxFormula0028 : Wff :=
    (synWa (.classEq (.cv t) (synCsn (.cv a))) syntaxFormula0025)
  let syntaxFormula0029 : Wff := (synWex a syntaxFormula0028)
  let syntaxFormula0030 : Wff := (synWex t syntaxFormula0027)
  let syntaxFormula0031 : Wff := (synWex t syntaxFormula0028)
  let syntaxFormula0032 : Wff := (synWex a syntaxFormula0031)
  let syntaxClass0033 : Class := (synCimak syntaxClass0024 (synC1c))
  let syntaxFormula0034 : Wff := (.classMem (.cv m) syntaxClass0033)
  let syntaxFormula0035 : Wff :=
    (.classMem (synCopk (synCsn (.cv a)) (.cv m)) syntaxClass0024)
  let syntaxFormula0036 : Wff :=
    (.classMem (synCopk (.cv t) (synCopk (synCsn (.cv a)) (.cv m))) syntaxClass0023)
  let syntaxFormula0037 : Wff :=
    (synWrex t (synCpw1 (synCpw1 (synCpw1 (synC1c)))) syntaxFormula0036)
  let syntaxFormula0038 : Wff :=
    (synWa (.classMem (.cv t) (synCpw1 (synCpw1 (synCpw1 (synC1c))))) syntaxFormula0036)
  let syntaxFormula0039 : Wff :=
    (synWa (.classEq (.cv t) (synCsn (synCsn (synCsn (synCsn (.cv x))))))
      syntaxFormula0036)
  let syntaxFormula0040 : Wff := (synWex x syntaxFormula0039)
  let syntaxFormula0041 : Wff := (synWex t syntaxFormula0038)
  let syntaxFormula0042 : Wff := (synWex t syntaxFormula0039)
  let syntaxFormula0043 : Wff := (synWex x syntaxFormula0042)
  let syntaxClass0044 : Class :=
    (synCopk (synCsn (synCsn (synCsn (synCsn (.cv x)))))
      (synCopk (synCsn (.cv a)) (.cv m)))
  let syntaxFormula0045 : Wff := (.classMem syntaxClass0044 syntaxClass0023)
  let syntaxClass0046 : Class := (synCopk (.cv t) syntaxClass0044)
  let syntaxFormula0047 : Wff := (.classMem syntaxClass0046 syntaxClass0020)
  let syntaxFormula0048 : Wff :=
    (synWrex t (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))) syntaxFormula0047)
  let syntaxFormula0049 : Wff :=
    (synWa (.classMem (.cv t) (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))
      syntaxFormula0047)
  let syntaxFormula0050 : Wff :=
    (synWa (.classEq (.cv t) (synCsn (synCsn (synCsn (synCsn (synCsn (.cv w)))))))
      syntaxFormula0047)
  let syntaxFormula0051 : Wff := (synWex w syntaxFormula0050)
  let syntaxFormula0052 : Wff := (synWex t syntaxFormula0049)
  let syntaxFormula0053 : Wff := (synWex t syntaxFormula0050)
  let syntaxFormula0054 : Wff := (synWex w syntaxFormula0053)
  let syntaxClass0055 : Class :=
    (synCopk (synCsn (synCsn (synCsn (synCsn (synCsn (.cv w)))))) syntaxClass0044)
  let syntaxFormula0056 : Wff := (.classMem syntaxClass0055 syntaxClass0020)
  let syntaxClass0057 : Class := (synCopk (.cv t) syntaxClass0055)
  let syntaxFormula0058 : Wff := (.classMem syntaxClass0057 syntaxClass0003)
  let syntaxFormula0059 : Wff := (synWrex t syntaxClass0004 syntaxFormula0058)
  let syntaxFormula0060 : Wff := (.classMem (.cv t) syntaxClass0004)
  let syntaxClass0061 : Class :=
    (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (.cv e)))))))))
  let syntaxFormula0062 : Wff := (.classEq (.cv t) syntaxClass0061)
  let syntaxFormula0063 : Wff := (synWa syntaxFormula0060 syntaxFormula0058)
  let syntaxFormula0064 : Wff := (synWa syntaxFormula0062 syntaxFormula0058)
  let syntaxFormula0065 : Wff := (synWex e syntaxFormula0064)
  let syntaxFormula0066 : Wff := (synWex t syntaxFormula0063)
  let syntaxFormula0067 : Wff := (synWex t syntaxFormula0064)
  let syntaxFormula0068 : Wff := (synWex e syntaxFormula0067)
  let syntaxFormula0069 : Wff := (.classMem syntaxClass0055 syntaxClass0005)
  let syntaxClass0070 : Class := (synCopk syntaxClass0061 syntaxClass0055)
  let syntaxFormula0071 : Wff := (.classMem syntaxClass0070 syntaxClass0003)
  let syntaxFormula0072 : Wff :=
    (.classMem (synCopk (synCsn (synCsn (synCsn (synCsn (synCsn (.cv e))))))
        (synCsn (synCsn (synCsn (synCsn (.cv w))))))
      (synCsik (synCsik (synCsik (synCsik (synCssetk))))))
  let syntaxFormula0073 : Wff :=
    (.classMem (synCopk (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (.cv e)))))))
        (synCsn (synCsn (synCsn (synCsn (synCsn (.cv w)))))))
      (synCsik (synCsik (synCsik (synCsik (synCsik (synCssetk)))))))
  let syntaxFormula0074 : Wff := (.classMem syntaxClass0070 syntaxClass0000)
  let syntaxClass0075 : Class :=
    (synCopk (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (.cv e)))))))
      syntaxClass0044)
  let syntaxFormula0076 : Wff :=
    (.classMem syntaxClass0075 (synCins2k (synCins3k (synCsik (synCssetk)))))
  let syntaxFormula0077 : Wff :=
    (.classEq (synCsn (synCsn (synCsn (synCsn (.cv e)))))
      (synCsn (synCsn (synCsn (synCsn (.cv x))))))
  let syntaxClass0078 : Class :=
    (synCopk (synCsn (synCsn (synCsn (synCsn (.cv e)))))
      (synCsn (synCsn (synCsn (synCsn (.cv x))))))
  let syntaxFormula0079 : Wff := (.classMem syntaxClass0078 (synCidk))
  let syntaxFormula0080 : Wff := (.classMem syntaxClass0075 (synCins3k (synCidk)))
  let syntaxFormula0081 : Wff := (.classMem syntaxClass0075 syntaxClass0001)
  let syntaxFormula0082 : Wff := (.classMem syntaxClass0070 syntaxClass0002)
  let syntaxFormula0083 : Wff := (synWb syntaxFormula0074 syntaxFormula0082)
  let syntaxFormula0084 : Wff :=
    (.neg (synWb (.objMem e w) (.classMem (.cv e) (synCun (.cv a) (synCsn (.cv x))))))
  let syntaxFormula0085 : Wff := (synWex e syntaxFormula0084)
  let syntaxFormula0086 : Wff := (.classMem syntaxClass0055 syntaxClass0006)
  let syntaxFormula0087 : Wff := (.classMem (synCopk (.cv t) (.cv m)) syntaxClass0016)
  let syntaxFormula0088 : Wff := (.classMem (synCopk (.cv m) (.cv t)) syntaxClass0015)
  let syntaxClass0089 : Class := (synCimak syntaxClass0014 (.cv m))
  let syntaxFormula0090 : Wff := (.classEq (.cv t) syntaxClass0089)
  let syntaxFormula0091 : Wff :=
    (synWa (.classMem (synCopk (synCsn (.cv w)) (.cv t)) (synCssetk)) syntaxFormula0087)
  let syntaxFormula0092 : Wff :=
    (.classMem (synCopk (synCsn (.cv w)) (.cv m)) syntaxClass0017)
  let syntaxFormula0093 : Wff :=
    (.classMem (synCopk (synCsn (synCsn (synCsn (.cv w))))
        (synCopk (synCsn (.cv a)) (.cv m))) syntaxClass0018)
  let syntaxFormula0094 : Wff := (.classMem syntaxClass0055 syntaxClass0019)
  let syntaxFormula0095 : Wff :=
    (synWa (.classEq (.cv w) (synCun (.cv a) (synCsn (.cv x))))
      (.classMem (.cv w) (synCplc (.cv m) (synC1c))))
  let syntaxFormula0096 : Wff := (synWex w syntaxFormula0095)
  let syntaxFormula0097 : Wff := (.classMem syntaxClass0044 syntaxClass0021)
  let syntaxFormula0098 : Wff :=
    (.classMem syntaxClass0044 (synCins3k (synCsik (synCssetk))))
  let syntaxFormula0099 : Wff := (.classMem syntaxClass0044 syntaxClass0022)
  let syntaxFormula0100 : Wff :=
    (synWa (.neg (.objMem x a))
      (.classMem (synCun (.cv a) (synCsn (.cv x))) (synCplc (.cv m) (synC1c))))
  let syntaxFormula0101 : Wff :=
    (.classMem syntaxClass0044 (synCxpk (synCvv) (synCssetk)))
  let syntaxFormula0102 : Wff := (.imp syntaxFormula0100 (.objMem a m))
  let syntaxFormula0103 : Wff := (.neg syntaxFormula0102)
  let syntaxFormula0104 : Wff := (.all x syntaxFormula0102)
  let syntaxFormula0105 : Wff := (.neg syntaxFormula0104)
  let syntaxFormula0106 : Wff := (synWex a syntaxFormula0105)
  let syntaxClass0107 : Class := (synCcompl syntaxClass0033)
  let syntaxFormula0108 : Wff := (.all a syntaxFormula0104)
  have p0000 := @gVex m
  have freshnessCertificate0000 : t ∉ ((synCssetk)).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk];
      exact (show t ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))
  have freshnessCertificate0001 : t ∉ ((synCsik (synCssetk))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0000)
  have freshnessCertificate0002 : t ∉ ((synCsik (synCsik (synCssetk)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0001)
  have freshnessCertificate0003 :
    t ∉ ((synCsik (synCsik (synCsik (synCssetk))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0002)
  have freshnessCertificate0004 :
    t ∉ ((synCsik (synCsik (synCsik (synCsik (synCssetk)))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0003)
  have freshnessCertificate0005 :
    t ∉ ((synCsik (synCsik (synCsik (synCsik (synCsik (synCssetk))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0004)
  have freshnessCertificate0006 : t ∉ (syntaxClass0000).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0005)
  have freshnessCertificate0007 : t ∉ ((synCins3k (synCsik (synCssetk)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0001)
  have freshnessCertificate0008 :
    t ∉ ((synCins2k (synCins3k (synCsik (synCssetk))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0007)
  have freshnessCertificate0009 : t ∉ ((synCidk)).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cidk];
      exact (show t ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))
  have freshnessCertificate0010 : t ∉ ((synCins3k (synCidk))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0009)
  have freshnessCertificate0011 :
    t ∉
      (((synCins2k (synCins3k (synCsik (synCssetk))))).fv) ∪
        (((synCins3k (synCidk))).fv) :=
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
  have freshnessCertificate0016 : t ∉ ((synC1c)).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c];
      exact (show t ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))
  have freshnessCertificate0017 : t ∉ ((synCpw1 (synC1c))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0016)
  have freshnessCertificate0018 : t ∉ ((synCpw1 (synCpw1 (synC1c)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0017)
  have freshnessCertificate0019 : t ∉ ((synCpw1 (synCpw1 (synCpw1 (synC1c))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0018)
  have freshnessCertificate0020 :
    t ∉ ((synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0019)
  have freshnessCertificate0021 :
    t ∉ ((synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0020)
  have freshnessCertificate0022 :
    t ∉
      ((synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))).fv :=
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
  have freshnessCertificate0027 : t ∉ ((synCins3k (synCssetk))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0000)
  have freshnessCertificate0028 : t ∉ ((synCins2k (synCssetk))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0000)
  have freshnessCertificate0029 :
    t ∉ (((synCins3k (synCssetk))).fv) ∪ (((synCins2k (synCssetk))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0027 freshnessCertificate0028))
  have freshnessCertificate0030 :
    t ∉ ((synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin];
      exact freshnessCertificate0029)
  have freshnessCertificate0031 :
    t ∉
      (((synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))).fv) ∪
        (((synCpw1 (synCpw1 (synC1c)))).fv) :=
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
  have freshnessCertificate0035 : t ∉ ((synCins2k (synCins2k (synCssetk)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0028)
  have freshnessCertificate0036 : t ∉ ((synCins2k (synCins3k (synCssetk)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0027)
  have freshnessCertificate0037 :
    t ∉ ((synCins3k (synCsik (synCsik (synCssetk))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0002)
  have freshnessCertificate0038 :
    t ∉
      (((synCins2k (synCins3k (synCssetk)))).fv) ∪
        (((synCins3k (synCsik (synCsik (synCssetk))))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0036 freshnessCertificate0037))
  have freshnessCertificate0039 : t ∉ (syntaxClass0010).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun];
      exact freshnessCertificate0038)
  have freshnessCertificate0040 :
    t ∉ (((synCins2k (synCins2k (synCssetk)))).fv) ∪ ((syntaxClass0010).fv) :=
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
        (((synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))).fv) :=
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
    t ∉ ((syntaxClass0013).fv) ∪ (((synCpw1 (synCpw1 (synC1c)))).fv) :=
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
  have freshnessCertificate0050 : t ∉ ((syntaxClass0016).fv) ∪ (((synCssetk)).fv) :=
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
        (((synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0055 freshnessCertificate0020))
  have freshnessCertificate0057 : t ∉ (syntaxClass0021).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak];
      exact freshnessCertificate0056)
  have freshnessCertificate0058 :
    t ∉ ((syntaxClass0021).fv) ∪ (((synCins3k (synCsik (synCssetk)))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0057 freshnessCertificate0007))
  have freshnessCertificate0059 : t ∉ (syntaxClass0022).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif];
      exact freshnessCertificate0058)
  have freshnessCertificate0060 : t ∉ ((synCvv)).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv];
      exact (show t ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))
  have freshnessCertificate0061 : t ∉ (((synCvv)).fv) ∪ (((synCssetk)).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0060 freshnessCertificate0000))
  have freshnessCertificate0062 : t ∉ ((synCxpk (synCvv) (synCssetk))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk];
      exact freshnessCertificate0061)
  have freshnessCertificate0063 :
    t ∉ ((syntaxClass0022).fv) ∪ (((synCxpk (synCvv) (synCssetk))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0059 freshnessCertificate0062))
  have freshnessCertificate0064 : t ∉ (syntaxClass0023).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif];
      exact freshnessCertificate0063)
  have freshnessCertificate0065 :
    t ∉ ((syntaxClass0023).fv) ∪ (((synCpw1 (synCpw1 (synCpw1 (synC1c))))).fv) :=
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
    @gElimak t syntaxClass0024 (synC1c) (.cv m) (by exact freshnessCertificate0066)
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
  have p0003 := @gEl1c a (.cv t) (by exact freshnessCertificate0068)
  have p0004 :=
    @gAnbi1i (.classMem (.cv t) (synC1c))
      (synWex a (.classEq (.cv t) (synCsn (.cv a)))) syntaxFormula0025 p0003
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
  have freshnessCertificate0071 : a ∉ ((synCopk (.cv t) (.cv m))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk];
      exact freshnessCertificate0070)
  have freshnessCertificate0072 : a ∉ ((synCssetk)).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk];
      exact (show a ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))
  have freshnessCertificate0073 : a ∉ ((synCsik (synCssetk))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0072)
  have freshnessCertificate0074 : a ∉ ((synCsik (synCsik (synCssetk)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0073)
  have freshnessCertificate0075 :
    a ∉ ((synCsik (synCsik (synCsik (synCssetk))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0074)
  have freshnessCertificate0076 :
    a ∉ ((synCsik (synCsik (synCsik (synCsik (synCssetk)))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0075)
  have freshnessCertificate0077 :
    a ∉ ((synCsik (synCsik (synCsik (synCsik (synCsik (synCssetk))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0076)
  have freshnessCertificate0078 : a ∉ (syntaxClass0000).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0077)
  have freshnessCertificate0079 : a ∉ ((synCins3k (synCsik (synCssetk)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0073)
  have freshnessCertificate0080 :
    a ∉ ((synCins2k (synCins3k (synCsik (synCssetk))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0079)
  have freshnessCertificate0081 : a ∉ ((synCidk)).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cidk];
      exact (show a ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))
  have freshnessCertificate0082 : a ∉ ((synCins3k (synCidk))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0081)
  have freshnessCertificate0083 :
    a ∉
      (((synCins2k (synCins3k (synCsik (synCssetk))))).fv) ∪
        (((synCins3k (synCidk))).fv) :=
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
  have freshnessCertificate0088 : a ∉ ((synC1c)).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c];
      exact (show a ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))
  have freshnessCertificate0089 : a ∉ ((synCpw1 (synC1c))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0088)
  have freshnessCertificate0090 : a ∉ ((synCpw1 (synCpw1 (synC1c)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0089)
  have freshnessCertificate0091 : a ∉ ((synCpw1 (synCpw1 (synCpw1 (synC1c))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0090)
  have freshnessCertificate0092 :
    a ∉ ((synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0091)
  have freshnessCertificate0093 :
    a ∉ ((synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0092)
  have freshnessCertificate0094 :
    a ∉
      ((synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))).fv :=
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
  have freshnessCertificate0099 : a ∉ ((synCins3k (synCssetk))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0072)
  have freshnessCertificate0100 : a ∉ ((synCins2k (synCssetk))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0072)
  have freshnessCertificate0101 :
    a ∉ (((synCins3k (synCssetk))).fv) ∪ (((synCins2k (synCssetk))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0099 freshnessCertificate0100))
  have freshnessCertificate0102 :
    a ∉ ((synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin];
      exact freshnessCertificate0101)
  have freshnessCertificate0103 :
    a ∉
      (((synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))).fv) ∪
        (((synCpw1 (synCpw1 (synC1c)))).fv) :=
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
  have freshnessCertificate0107 : a ∉ ((synCins2k (synCins2k (synCssetk)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0100)
  have freshnessCertificate0108 : a ∉ ((synCins2k (synCins3k (synCssetk)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0099)
  have freshnessCertificate0109 :
    a ∉ ((synCins3k (synCsik (synCsik (synCssetk))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0074)
  have freshnessCertificate0110 :
    a ∉
      (((synCins2k (synCins3k (synCssetk)))).fv) ∪
        (((synCins3k (synCsik (synCsik (synCssetk))))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0108 freshnessCertificate0109))
  have freshnessCertificate0111 : a ∉ (syntaxClass0010).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun];
      exact freshnessCertificate0110)
  have freshnessCertificate0112 :
    a ∉ (((synCins2k (synCins2k (synCssetk)))).fv) ∪ ((syntaxClass0010).fv) :=
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
        (((synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))).fv) :=
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
    a ∉ ((syntaxClass0013).fv) ∪ (((synCpw1 (synCpw1 (synC1c)))).fv) :=
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
  have freshnessCertificate0122 : a ∉ ((syntaxClass0016).fv) ∪ (((synCssetk)).fv) :=
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
        (((synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0127 freshnessCertificate0092))
  have freshnessCertificate0129 : a ∉ (syntaxClass0021).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak];
      exact freshnessCertificate0128)
  have freshnessCertificate0130 :
    a ∉ ((syntaxClass0021).fv) ∪ (((synCins3k (synCsik (synCssetk)))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0129 freshnessCertificate0079))
  have freshnessCertificate0131 : a ∉ (syntaxClass0022).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif];
      exact freshnessCertificate0130)
  have freshnessCertificate0132 : a ∉ ((synCvv)).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv];
      exact (show a ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))
  have freshnessCertificate0133 : a ∉ (((synCvv)).fv) ∪ (((synCssetk)).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0132 freshnessCertificate0072))
  have freshnessCertificate0134 : a ∉ ((synCxpk (synCvv) (synCssetk))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk];
      exact freshnessCertificate0133)
  have freshnessCertificate0135 :
    a ∉ ((syntaxClass0022).fv) ∪ (((synCxpk (synCvv) (synCssetk))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0131 freshnessCertificate0134))
  have freshnessCertificate0136 : a ∉ (syntaxClass0023).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif];
      exact freshnessCertificate0135)
  have freshnessCertificate0137 :
    a ∉ ((syntaxClass0023).fv) ∪ (((synCpw1 (synCpw1 (synCpw1 (synC1c))))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0136 freshnessCertificate0091))
  have freshnessCertificate0138 : a ∉ (syntaxClass0024).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak];
      exact freshnessCertificate0137)
  have freshnessCertificate0139 :
    a ∉ (((synCopk (.cv t) (.cv m))).fv) ∪ ((syntaxClass0024).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0071 freshnessCertificate0138))
  have freshnessCertificate0140 :
    a ∉ ((Wff.classMem (synCopk (.cv t) (.cv m)) syntaxClass0024)).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact freshnessCertificate0139)
  have p0005 :=
    @gN1941v (.classEq (.cv t) (synCsn (.cv a))) syntaxFormula0025 a
      (by exact freshnessCertificate0140)
  have p0006 :=
    @gBitr4i syntaxFormula0027
      (synWa (synWex a (.classEq (.cv t) (synCsn (.cv a)))) syntaxFormula0025)
      syntaxFormula0029 p0004 p0005
  have p0007 := @gExbii syntaxFormula0027 syntaxFormula0029 t p0006
  have p0008 := @gExcom syntaxFormula0028 a t
  have p0009 :=
    @gBitr4i syntaxFormula0030 (synWex t syntaxFormula0029) syntaxFormula0032 p0007
      p0008
  have p0010 := @gBitri syntaxFormula0026 syntaxFormula0030 syntaxFormula0032 p0002 p0009
  have p0011 := @gBitri syntaxFormula0034 syntaxFormula0026 syntaxFormula0032 p0001 p0010
  have p0012 := @gSnex (.cv a)
  have p0013 := @gOpkeq1 (.cv t) (synCsn (.cv a)) (.cv m)
  have p0014 :=
    @gEleq1d (.classEq (.cv t) (synCsn (.cv a))) (synCopk (.cv t) (.cv m))
      (synCopk (synCsn (.cv a)) (.cv m)) syntaxClass0024 p0013
  have freshnessCertificate0141 : t ∉ ((Class.cv a)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show t ∉ ({ a } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show t ≠ a from (by exact fresh_t_ne_a)))))
  have freshnessCertificate0142 : t ∉ ((synCsn (.cv a))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0141)
  have freshnessCertificate0143 : t ∉ (((synCsn (.cv a))).fv) ∪ (((Class.cv m)).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0142 freshnessCertificate0067))
  have freshnessCertificate0144 : t ∉ ((synCopk (synCsn (.cv a)) (.cv m))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk];
      exact freshnessCertificate0143)
  have freshnessCertificate0145 :
    t ∉ (((synCopk (synCsn (.cv a)) (.cv m))).fv) ∪ ((syntaxClass0024).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0144 freshnessCertificate0066))
  have freshnessCertificate0146 :
    t ∉ ((Wff.classMem (synCopk (synCsn (.cv a)) (.cv m)) syntaxClass0024)).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact freshnessCertificate0145)
  have p0015 :=
    @gCeqsexv syntaxFormula0025 syntaxFormula0035 t (synCsn (.cv a))
      (by exact freshnessCertificate0142) (by exact freshnessCertificate0146) p0012 p0014
  have p0016 := @gOpkex (synCsn (.cv a)) (.cv m)
  have p0017 :=
    @gElimak t syntaxClass0023 (synCpw1 (synCpw1 (synCpw1 (synC1c))))
      (synCopk (synCsn (.cv a)) (.cv m)) (by exact freshnessCertificate0064)
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
  have p0019 := @gElpw131c x (.cv t) (by exact freshnessCertificate0147)
  have p0020 :=
    @gAnbi1i (.classMem (.cv t) (synCpw1 (synCpw1 (synCpw1 (synC1c)))))
      (synWex x (.classEq (.cv t) (synCsn (synCsn (synCsn (synCsn (.cv x)))))))
      syntaxFormula0036 p0019
  have freshnessCertificate0148 : x ∉ ((Class.cv a)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show x ∉ ({ a } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show x ≠ a from (by exact Ne.symm dv_a_x)))))
  have freshnessCertificate0149 : x ∉ ((synCsn (.cv a))).fv :=
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
  have freshnessCertificate0151 : x ∉ (((synCsn (.cv a))).fv) ∪ (((Class.cv m)).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0149 freshnessCertificate0150))
  have freshnessCertificate0152 : x ∉ ((synCopk (synCsn (.cv a)) (.cv m))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk];
      exact freshnessCertificate0151)
  have freshnessCertificate0153 :
    x ∉ (((Class.cv t)).fv) ∪ (((synCopk (synCsn (.cv a)) (.cv m))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0147 freshnessCertificate0152))
  have freshnessCertificate0154 :
    x ∉ ((synCopk (.cv t) (synCopk (synCsn (.cv a)) (.cv m)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk];
      exact freshnessCertificate0153)
  have freshnessCertificate0155 : x ∉ ((synCssetk)).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk];
      exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))
  have freshnessCertificate0156 : x ∉ ((synCsik (synCssetk))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0155)
  have freshnessCertificate0157 : x ∉ ((synCsik (synCsik (synCssetk)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0156)
  have freshnessCertificate0158 :
    x ∉ ((synCsik (synCsik (synCsik (synCssetk))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0157)
  have freshnessCertificate0159 :
    x ∉ ((synCsik (synCsik (synCsik (synCsik (synCssetk)))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0158)
  have freshnessCertificate0160 :
    x ∉ ((synCsik (synCsik (synCsik (synCsik (synCsik (synCssetk))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0159)
  have freshnessCertificate0161 : x ∉ (syntaxClass0000).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0160)
  have freshnessCertificate0162 : x ∉ ((synCins3k (synCsik (synCssetk)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0156)
  have freshnessCertificate0163 :
    x ∉ ((synCins2k (synCins3k (synCsik (synCssetk))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0162)
  have freshnessCertificate0164 : x ∉ ((synCidk)).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cidk];
      exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))
  have freshnessCertificate0165 : x ∉ ((synCins3k (synCidk))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0164)
  have freshnessCertificate0166 :
    x ∉
      (((synCins2k (synCins3k (synCsik (synCssetk))))).fv) ∪
        (((synCins3k (synCidk))).fv) :=
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
  have freshnessCertificate0171 : x ∉ ((synC1c)).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c];
      exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))
  have freshnessCertificate0172 : x ∉ ((synCpw1 (synC1c))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0171)
  have freshnessCertificate0173 : x ∉ ((synCpw1 (synCpw1 (synC1c)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0172)
  have freshnessCertificate0174 : x ∉ ((synCpw1 (synCpw1 (synCpw1 (synC1c))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0173)
  have freshnessCertificate0175 :
    x ∉ ((synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0174)
  have freshnessCertificate0176 :
    x ∉ ((synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0175)
  have freshnessCertificate0177 :
    x ∉
      ((synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))).fv :=
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
  have freshnessCertificate0182 : x ∉ ((synCins3k (synCssetk))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0155)
  have freshnessCertificate0183 : x ∉ ((synCins2k (synCssetk))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0155)
  have freshnessCertificate0184 :
    x ∉ (((synCins3k (synCssetk))).fv) ∪ (((synCins2k (synCssetk))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0182 freshnessCertificate0183))
  have freshnessCertificate0185 :
    x ∉ ((synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin];
      exact freshnessCertificate0184)
  have freshnessCertificate0186 :
    x ∉
      (((synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))).fv) ∪
        (((synCpw1 (synCpw1 (synC1c)))).fv) :=
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
  have freshnessCertificate0190 : x ∉ ((synCins2k (synCins2k (synCssetk)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0183)
  have freshnessCertificate0191 : x ∉ ((synCins2k (synCins3k (synCssetk)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0182)
  have freshnessCertificate0192 :
    x ∉ ((synCins3k (synCsik (synCsik (synCssetk))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0157)
  have freshnessCertificate0193 :
    x ∉
      (((synCins2k (synCins3k (synCssetk)))).fv) ∪
        (((synCins3k (synCsik (synCsik (synCssetk))))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0191 freshnessCertificate0192))
  have freshnessCertificate0194 : x ∉ (syntaxClass0010).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun];
      exact freshnessCertificate0193)
  have freshnessCertificate0195 :
    x ∉ (((synCins2k (synCins2k (synCssetk)))).fv) ∪ ((syntaxClass0010).fv) :=
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
        (((synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))).fv) :=
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
    x ∉ ((syntaxClass0013).fv) ∪ (((synCpw1 (synCpw1 (synC1c)))).fv) :=
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
  have freshnessCertificate0205 : x ∉ ((syntaxClass0016).fv) ∪ (((synCssetk)).fv) :=
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
        (((synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0210 freshnessCertificate0175))
  have freshnessCertificate0212 : x ∉ (syntaxClass0021).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak];
      exact freshnessCertificate0211)
  have freshnessCertificate0213 :
    x ∉ ((syntaxClass0021).fv) ∪ (((synCins3k (synCsik (synCssetk)))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0212 freshnessCertificate0162))
  have freshnessCertificate0214 : x ∉ (syntaxClass0022).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif];
      exact freshnessCertificate0213)
  have freshnessCertificate0215 : x ∉ ((synCvv)).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv];
      exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))
  have freshnessCertificate0216 : x ∉ (((synCvv)).fv) ∪ (((synCssetk)).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0215 freshnessCertificate0155))
  have freshnessCertificate0217 : x ∉ ((synCxpk (synCvv) (synCssetk))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk];
      exact freshnessCertificate0216)
  have freshnessCertificate0218 :
    x ∉ ((syntaxClass0022).fv) ∪ (((synCxpk (synCvv) (synCssetk))).fv) :=
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
      (((synCopk (.cv t) (synCopk (synCsn (.cv a)) (.cv m)))).fv) ∪
        ((syntaxClass0023).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0154 freshnessCertificate0219))
  have freshnessCertificate0221 :
    x ∉
      ((Wff.classMem (synCopk (.cv t) (synCopk (synCsn (.cv a)) (.cv m)))
          syntaxClass0023)).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact freshnessCertificate0220)
  have p0021 :=
    @gN1941v (.classEq (.cv t) (synCsn (synCsn (synCsn (synCsn (.cv x))))))
      syntaxFormula0036 x (by exact freshnessCertificate0221)
  have p0022 :=
    @gBitr4i syntaxFormula0038
      (synWa (synWex x (.classEq (.cv t) (synCsn (synCsn (synCsn (synCsn (.cv x)))))))
        syntaxFormula0036)
      syntaxFormula0040 p0020 p0021
  have p0023 := @gExbii syntaxFormula0038 syntaxFormula0040 t p0022
  have p0024 := @gExcom syntaxFormula0039 x t
  have p0025 :=
    @gBitr4i syntaxFormula0041 (synWex t syntaxFormula0040) syntaxFormula0043 p0023
      p0024
  have p0026 := @gBitri syntaxFormula0037 syntaxFormula0041 syntaxFormula0043 p0018 p0025
  have p0027 := @gBitri syntaxFormula0035 syntaxFormula0037 syntaxFormula0043 p0017 p0026
  have p0028 := @gSnex (synCsn (synCsn (synCsn (.cv x))))
  have p0029 :=
    @gOpkeq1 (.cv t) (synCsn (synCsn (synCsn (synCsn (.cv x)))))
      (synCopk (synCsn (.cv a)) (.cv m))
  have p0030 :=
    @gEleq1d (.classEq (.cv t) (synCsn (synCsn (synCsn (synCsn (.cv x))))))
      (synCopk (.cv t) (synCopk (synCsn (.cv a)) (.cv m))) syntaxClass0044
      syntaxClass0023 p0029
  have freshnessCertificate0222 : t ∉ ((Class.cv x)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show t ∉ ({ x } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show t ≠ x from (by exact fresh_t_ne_x)))))
  have freshnessCertificate0223 : t ∉ ((synCsn (.cv x))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0222)
  have freshnessCertificate0224 : t ∉ ((synCsn (synCsn (.cv x)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0223)
  have freshnessCertificate0225 : t ∉ ((synCsn (synCsn (synCsn (.cv x))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0224)
  have freshnessCertificate0226 :
    t ∉ ((synCsn (synCsn (synCsn (synCsn (.cv x)))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0225)
  have freshnessCertificate0227 :
    t ∉
      (((synCsn (synCsn (synCsn (synCsn (.cv x)))))).fv) ∪
        (((synCopk (synCsn (.cv a)) (.cv m))).fv) :=
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
    @gCeqsexv syntaxFormula0036 syntaxFormula0045 t
      (synCsn (synCsn (synCsn (synCsn (.cv x))))) (by exact freshnessCertificate0226)
      (by exact freshnessCertificate0230) p0028 p0030
  have p0032 := @gEldif syntaxClass0044 syntaxClass0022 (synCxpk (synCvv) (synCssetk))
  have p0033 :=
    @gEldif syntaxClass0044 syntaxClass0021 (synCins3k (synCsik (synCssetk)))
  have p0034 :=
    @gOpkex (synCsn (synCsn (synCsn (synCsn (.cv x)))))
      (synCopk (synCsn (.cv a)) (.cv m))
  have p0035 :=
    @gElimak t syntaxClass0020 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))
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
  have p0037 := @gElpw141c w (.cv t) (by exact freshnessCertificate0231)
  have p0038 :=
    @gAnbi1i (.classMem (.cv t) (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))
      (synWex w (.classEq (.cv t) (synCsn (synCsn (synCsn (synCsn (synCsn (.cv w))))))))
      syntaxFormula0047 p0037
  have freshnessCertificate0232 : w ∉ ((Class.cv x)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show w ∉ ({ x } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show w ≠ x from (by exact fresh_w_ne_x)))))
  have freshnessCertificate0233 : w ∉ ((synCsn (.cv x))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0232)
  have freshnessCertificate0234 : w ∉ ((synCsn (synCsn (.cv x)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0233)
  have freshnessCertificate0235 : w ∉ ((synCsn (synCsn (synCsn (.cv x))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0234)
  have freshnessCertificate0236 :
    w ∉ ((synCsn (synCsn (synCsn (synCsn (.cv x)))))).fv :=
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
  have freshnessCertificate0238 : w ∉ ((synCsn (.cv a))).fv :=
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
  have freshnessCertificate0240 : w ∉ (((synCsn (.cv a))).fv) ∪ (((Class.cv m)).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0238 freshnessCertificate0239))
  have freshnessCertificate0241 : w ∉ ((synCopk (synCsn (.cv a)) (.cv m))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk];
      exact freshnessCertificate0240)
  have freshnessCertificate0242 :
    w ∉
      (((synCsn (synCsn (synCsn (synCsn (.cv x)))))).fv) ∪
        (((synCopk (synCsn (.cv a)) (.cv m))).fv) :=
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
  have freshnessCertificate0246 : w ∉ ((synCssetk)).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk];
      exact (show w ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))
  have freshnessCertificate0247 : w ∉ ((synCsik (synCssetk))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0246)
  have freshnessCertificate0248 : w ∉ ((synCsik (synCsik (synCssetk)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0247)
  have freshnessCertificate0249 :
    w ∉ ((synCsik (synCsik (synCsik (synCssetk))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0248)
  have freshnessCertificate0250 :
    w ∉ ((synCsik (synCsik (synCsik (synCsik (synCssetk)))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0249)
  have freshnessCertificate0251 :
    w ∉ ((synCsik (synCsik (synCsik (synCsik (synCsik (synCssetk))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0250)
  have freshnessCertificate0252 : w ∉ (syntaxClass0000).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0251)
  have freshnessCertificate0253 : w ∉ ((synCins3k (synCsik (synCssetk)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0247)
  have freshnessCertificate0254 :
    w ∉ ((synCins2k (synCins3k (synCsik (synCssetk))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0253)
  have freshnessCertificate0255 : w ∉ ((synCidk)).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cidk];
      exact (show w ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))
  have freshnessCertificate0256 : w ∉ ((synCins3k (synCidk))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0255)
  have freshnessCertificate0257 :
    w ∉
      (((synCins2k (synCins3k (synCsik (synCssetk))))).fv) ∪
        (((synCins3k (synCidk))).fv) :=
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
  have freshnessCertificate0262 : w ∉ ((synC1c)).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c];
      exact (show w ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))
  have freshnessCertificate0263 : w ∉ ((synCpw1 (synC1c))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0262)
  have freshnessCertificate0264 : w ∉ ((synCpw1 (synCpw1 (synC1c)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0263)
  have freshnessCertificate0265 : w ∉ ((synCpw1 (synCpw1 (synCpw1 (synC1c))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0264)
  have freshnessCertificate0266 :
    w ∉ ((synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0265)
  have freshnessCertificate0267 :
    w ∉ ((synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0266)
  have freshnessCertificate0268 :
    w ∉
      ((synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))).fv :=
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
  have freshnessCertificate0273 : w ∉ ((synCins3k (synCssetk))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0246)
  have freshnessCertificate0274 : w ∉ ((synCins2k (synCssetk))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0246)
  have freshnessCertificate0275 :
    w ∉ (((synCins3k (synCssetk))).fv) ∪ (((synCins2k (synCssetk))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0273 freshnessCertificate0274))
  have freshnessCertificate0276 :
    w ∉ ((synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin];
      exact freshnessCertificate0275)
  have freshnessCertificate0277 :
    w ∉
      (((synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))).fv) ∪
        (((synCpw1 (synCpw1 (synC1c)))).fv) :=
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
  have freshnessCertificate0281 : w ∉ ((synCins2k (synCins2k (synCssetk)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0274)
  have freshnessCertificate0282 : w ∉ ((synCins2k (synCins3k (synCssetk)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0273)
  have freshnessCertificate0283 :
    w ∉ ((synCins3k (synCsik (synCsik (synCssetk))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0248)
  have freshnessCertificate0284 :
    w ∉
      (((synCins2k (synCins3k (synCssetk)))).fv) ∪
        (((synCins3k (synCsik (synCsik (synCssetk))))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0282 freshnessCertificate0283))
  have freshnessCertificate0285 : w ∉ (syntaxClass0010).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun];
      exact freshnessCertificate0284)
  have freshnessCertificate0286 :
    w ∉ (((synCins2k (synCins2k (synCssetk)))).fv) ∪ ((syntaxClass0010).fv) :=
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
        (((synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))).fv) :=
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
    w ∉ ((syntaxClass0013).fv) ∪ (((synCpw1 (synCpw1 (synC1c)))).fv) :=
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
  have freshnessCertificate0296 : w ∉ ((syntaxClass0016).fv) ∪ (((synCssetk)).fv) :=
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
    @gN1941v
      (.classEq (.cv t) (synCsn (synCsn (synCsn (synCsn (synCsn (.cv w)))))))
      syntaxFormula0047 w (by exact freshnessCertificate0303)
  have p0040 :=
    @gBitr4i syntaxFormula0049
      (synWa (synWex w
          (.classEq (.cv t) (synCsn (synCsn (synCsn (synCsn (synCsn (.cv w))))))))
        syntaxFormula0047)
      syntaxFormula0051 p0038 p0039
  have p0041 := @gExbii syntaxFormula0049 syntaxFormula0051 t p0040
  have p0042 := @gExcom syntaxFormula0050 w t
  have p0043 :=
    @gBitr4i syntaxFormula0052 (synWex t syntaxFormula0051) syntaxFormula0054 p0041
      p0042
  have p0044 := @gBitri syntaxFormula0048 syntaxFormula0052 syntaxFormula0054 p0036 p0043
  have p0045 := @gSnex (synCsn (synCsn (synCsn (synCsn (.cv w)))))
  have p0046 :=
    @gOpkeq1 (.cv t) (synCsn (synCsn (synCsn (synCsn (synCsn (.cv w))))))
      syntaxClass0044
  have p0047 :=
    @gEleq1d (.classEq (.cv t) (synCsn (synCsn (synCsn (synCsn (synCsn (.cv w)))))))
      syntaxClass0046 syntaxClass0055 syntaxClass0020 p0046
  have freshnessCertificate0304 : t ∉ ((Class.cv w)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show t ∉ ({ w } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show t ≠ w from (by exact fresh_t_ne_w)))))
  have freshnessCertificate0305 : t ∉ ((synCsn (.cv w))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0304)
  have freshnessCertificate0306 : t ∉ ((synCsn (synCsn (.cv w)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0305)
  have freshnessCertificate0307 : t ∉ ((synCsn (synCsn (synCsn (.cv w))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0306)
  have freshnessCertificate0308 :
    t ∉ ((synCsn (synCsn (synCsn (synCsn (.cv w)))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0307)
  have freshnessCertificate0309 :
    t ∉ ((synCsn (synCsn (synCsn (synCsn (synCsn (.cv w))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0308)
  have freshnessCertificate0310 :
    t ∉
      (((synCsn (synCsn (synCsn (synCsn (synCsn (.cv w))))))).fv) ∪
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
    @gCeqsexv syntaxFormula0047 syntaxFormula0056 t
      (synCsn (synCsn (synCsn (synCsn (synCsn (.cv w))))))
      (by exact freshnessCertificate0309) (by exact freshnessCertificate0313) p0045 p0047
  have p0049 := @gElin syntaxClass0055 syntaxClass0006 syntaxClass0019
  have p0050 :=
    @gOpkex (synCsn (synCsn (synCsn (synCsn (synCsn (.cv w)))))) syntaxClass0044
  have p0051 :=
    @gElimak t syntaxClass0003 syntaxClass0004 syntaxClass0055
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
  have p0053 := @gElpw171c e (.cv t) (by exact freshnessCertificate0314)
  have p0054 :=
    @gAnbi1i syntaxFormula0060 (synWex e syntaxFormula0062) syntaxFormula0058 p0053
  have freshnessCertificate0315 : e ∉ ((Class.cv w)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show e ∉ ({ w } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show e ≠ w from (by exact fresh_e_ne_w)))))
  have freshnessCertificate0316 : e ∉ ((synCsn (.cv w))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0315)
  have freshnessCertificate0317 : e ∉ ((synCsn (synCsn (.cv w)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0316)
  have freshnessCertificate0318 : e ∉ ((synCsn (synCsn (synCsn (.cv w))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0317)
  have freshnessCertificate0319 :
    e ∉ ((synCsn (synCsn (synCsn (synCsn (.cv w)))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0318)
  have freshnessCertificate0320 :
    e ∉ ((synCsn (synCsn (synCsn (synCsn (synCsn (.cv w))))))).fv :=
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
  have freshnessCertificate0322 : e ∉ ((synCsn (.cv x))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0321)
  have freshnessCertificate0323 : e ∉ ((synCsn (synCsn (.cv x)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0322)
  have freshnessCertificate0324 : e ∉ ((synCsn (synCsn (synCsn (.cv x))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0323)
  have freshnessCertificate0325 :
    e ∉ ((synCsn (synCsn (synCsn (synCsn (.cv x)))))).fv :=
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
  have freshnessCertificate0327 : e ∉ ((synCsn (.cv a))).fv :=
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
  have freshnessCertificate0329 : e ∉ (((synCsn (.cv a))).fv) ∪ (((Class.cv m)).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0327 freshnessCertificate0328))
  have freshnessCertificate0330 : e ∉ ((synCopk (synCsn (.cv a)) (.cv m))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk];
      exact freshnessCertificate0329)
  have freshnessCertificate0331 :
    e ∉
      (((synCsn (synCsn (synCsn (synCsn (.cv x)))))).fv) ∪
        (((synCopk (synCsn (.cv a)) (.cv m))).fv) :=
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
      (((synCsn (synCsn (synCsn (synCsn (synCsn (.cv w))))))).fv) ∪
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
  have freshnessCertificate0337 : e ∉ ((synCssetk)).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk];
      exact (show e ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))
  have freshnessCertificate0338 : e ∉ ((synCsik (synCssetk))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0337)
  have freshnessCertificate0339 : e ∉ ((synCsik (synCsik (synCssetk)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0338)
  have freshnessCertificate0340 :
    e ∉ ((synCsik (synCsik (synCsik (synCssetk))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0339)
  have freshnessCertificate0341 :
    e ∉ ((synCsik (synCsik (synCsik (synCsik (synCssetk)))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0340)
  have freshnessCertificate0342 :
    e ∉ ((synCsik (synCsik (synCsik (synCsik (synCsik (synCssetk))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0341)
  have freshnessCertificate0343 : e ∉ (syntaxClass0000).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0342)
  have freshnessCertificate0344 : e ∉ ((synCins3k (synCsik (synCssetk)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0338)
  have freshnessCertificate0345 :
    e ∉ ((synCins2k (synCins3k (synCsik (synCssetk))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0344)
  have freshnessCertificate0346 : e ∉ ((synCidk)).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cidk];
      exact (show e ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))
  have freshnessCertificate0347 : e ∉ ((synCins3k (synCidk))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0346)
  have freshnessCertificate0348 :
    e ∉
      (((synCins2k (synCins3k (synCsik (synCssetk))))).fv) ∪
        (((synCins3k (synCidk))).fv) :=
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
    @gN1941v syntaxFormula0062 syntaxFormula0058 e (by exact freshnessCertificate0354)
  have p0056 :=
    @gBitr4i syntaxFormula0063 (synWa (synWex e syntaxFormula0062) syntaxFormula0058)
      syntaxFormula0065 p0054 p0055
  have p0057 := @gExbii syntaxFormula0063 syntaxFormula0065 t p0056
  have p0058 := @gExcom syntaxFormula0064 e t
  have p0059 :=
    @gBitr4i syntaxFormula0066 (synWex t syntaxFormula0065) syntaxFormula0068 p0057
      p0058
  have p0060 := @gBitri syntaxFormula0059 syntaxFormula0066 syntaxFormula0068 p0052 p0059
  have p0061 := @gBitri syntaxFormula0069 syntaxFormula0059 syntaxFormula0068 p0051 p0060
  have p0062 :=
    @gSnex (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (.cv e))))))))
  have p0063 := @gOpkeq1 (.cv t) syntaxClass0061 syntaxClass0055
  have p0064 :=
    @gEleq1d syntaxFormula0062 syntaxClass0057 syntaxClass0070 syntaxClass0003 p0063
  have freshnessCertificate0355 : t ∉ ((Class.cv e)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show t ∉ ({ e } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show t ≠ e from (by exact fresh_t_ne_e)))))
  have freshnessCertificate0356 : t ∉ ((synCsn (.cv e))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0355)
  have freshnessCertificate0357 : t ∉ ((synCsn (synCsn (.cv e)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0356)
  have freshnessCertificate0358 : t ∉ ((synCsn (synCsn (synCsn (.cv e))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0357)
  have freshnessCertificate0359 :
    t ∉ ((synCsn (synCsn (synCsn (synCsn (.cv e)))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0358)
  have freshnessCertificate0360 :
    t ∉ ((synCsn (synCsn (synCsn (synCsn (synCsn (.cv e))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0359)
  have freshnessCertificate0361 :
    t ∉ ((synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (.cv e)))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0360)
  have freshnessCertificate0362 :
    t ∉
      ((synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (.cv e))))))))).fv :=
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
    @gCeqsexv syntaxFormula0058 syntaxFormula0071 t syntaxClass0061
      (by exact freshnessCertificate0363) (by exact freshnessCertificate0367) p0062 p0064
  have p0066 := @gElsymdif syntaxClass0070 syntaxClass0000 syntaxClass0002
  have p0067 := @gSnex (synCsn (synCsn (synCsn (synCsn (synCsn (.cv e))))))
  have p0068 :=
    @gOtkelins3k (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (.cv e)))))))
      (synCsn (synCsn (synCsn (synCsn (synCsn (.cv w)))))) syntaxClass0044
      (synCsik (synCsik (synCsik (synCsik (synCsik (synCssetk)))))) p0067 p0045
      p0034
  have p0069 := @gSnex (synCsn (synCsn (synCsn (synCsn (.cv e)))))
  have p0070 := @gSnex (synCsn (synCsn (synCsn (.cv w))))
  have p0071 :=
    @gOpksnelsik (synCsn (synCsn (synCsn (synCsn (synCsn (.cv e))))))
      (synCsn (synCsn (synCsn (synCsn (.cv w)))))
      (synCsik (synCsik (synCsik (synCsik (synCssetk))))) p0069 p0070
  have p0072 := @gSnex (synCsn (synCsn (synCsn (.cv e))))
  have p0073 := @gSnex (synCsn (synCsn (.cv w)))
  have p0074 :=
    @gOpksnelsik (synCsn (synCsn (synCsn (synCsn (.cv e)))))
      (synCsn (synCsn (synCsn (.cv w)))) (synCsik (synCsik (synCsik (synCssetk))))
      p0072 p0073
  have p0075 := @gSnex (synCsn (synCsn (.cv e)))
  have p0076 := @gSnex (synCsn (.cv w))
  have p0077 :=
    @gOpksnelsik (synCsn (synCsn (synCsn (.cv e)))) (synCsn (synCsn (.cv w)))
      (synCsik (synCsik (synCssetk))) p0075 p0076
  have p0078 := @gSnex (synCsn (.cv e))
  have p0079 := @gSnex (.cv w)
  have p0080 :=
    @gOpksnelsik (synCsn (synCsn (.cv e))) (synCsn (.cv w)) (synCsik (synCssetk))
      p0078 p0079
  have p0081 := @gSnex (.cv e)
  have p0082 := @gVex w
  have p0083 := @gOpksnelsik (synCsn (.cv e)) (.cv w) (synCssetk) p0081 p0082
  have p0084 := @gVex e
  have p0085 := @gElssetk (.cv e) (.cv w) p0084 p0082
  have p0086_e01_recanon :
    Nominal.NPrf
      (synWb (.classMem (synCopk (synCsn (.cv e)) (.cv w)) (synCssetk)) (.objMem e w)) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [synWb, synCopk, synCpr, synCun, synCnin, synWnan, synWa,
          synCcompl, synCsn, synCssetk, synWex]
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
    @gBitri
      (.classMem (synCopk (synCsn (synCsn (.cv e))) (synCsn (.cv w)))
        (synCsik (synCssetk)))
      (.classMem (synCopk (synCsn (.cv e)) (.cv w)) (synCssetk)) (.objMem e w) p0083
      p0086_e01_recanon
  have p0087 :=
    @gBitri
      (.classMem (synCopk (synCsn (synCsn (synCsn (.cv e)))) (synCsn (synCsn (.cv w))))
        (synCsik (synCsik (synCssetk))))
      (.classMem (synCopk (synCsn (synCsn (.cv e))) (synCsn (.cv w)))
        (synCsik (synCssetk)))
      (.objMem e w) p0080 p0086
  have p0088 :=
    @gBitri
      (.classMem (synCopk (synCsn (synCsn (synCsn (synCsn (.cv e)))))
          (synCsn (synCsn (synCsn (.cv w))))) (synCsik (synCsik (synCsik (synCssetk)))))
      (.classMem (synCopk (synCsn (synCsn (synCsn (.cv e)))) (synCsn (synCsn (.cv w))))
        (synCsik (synCsik (synCssetk))))
      (.objMem e w) p0077 p0087
  have p0089 :=
    @gBitri syntaxFormula0072
      (.classMem (synCopk (synCsn (synCsn (synCsn (synCsn (.cv e)))))
          (synCsn (synCsn (synCsn (.cv w))))) (synCsik (synCsik (synCsik (synCssetk)))))
      (.objMem e w) p0074 p0088
  have p0090 := @gBitri syntaxFormula0073 syntaxFormula0072 (.objMem e w) p0071 p0089
  have p0091 := @gBitri syntaxFormula0074 syntaxFormula0073 (.objMem e w) p0068 p0090
  have p0092 :=
    @gOtkelins2k (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (.cv e)))))))
      (synCsn (synCsn (synCsn (synCsn (synCsn (.cv w)))))) syntaxClass0044
      syntaxClass0001 p0067 p0045 p0034
  have p0093 :=
    @gOtkelins2k (synCsn (synCsn (synCsn (synCsn (.cv e)))))
      (synCsn (synCsn (synCsn (synCsn (.cv x))))) (synCopk (synCsn (.cv a)) (.cv m))
      (synCins3k (synCsik (synCssetk))) p0072 p0028 p0016
  have p0094 :=
    @gOtkelins3k (synCsn (synCsn (.cv e))) (synCsn (.cv a)) (.cv m)
      (synCsik (synCssetk)) p0078 p0012 p0000
  have p0095 := @gVex a
  have p0096 := @gOpksnelsik (synCsn (.cv e)) (.cv a) (synCssetk) p0081 p0095
  have p0097 := @gElssetk (.cv e) (.cv a) p0084 p0095
  have p0098_e01_recanon :
    Nominal.NPrf
      (synWb (.classMem (synCopk (synCsn (.cv e)) (.cv a)) (synCssetk)) (.objMem e a)) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [synWb, synCopk, synCpr, synCun, synCnin, synWnan, synWa,
          synCcompl, synCsn, synCssetk, synWex]
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
    @gBitri
      (.classMem (synCopk (synCsn (synCsn (.cv e))) (synCsn (.cv a)))
        (synCsik (synCssetk)))
      (.classMem (synCopk (synCsn (.cv e)) (.cv a)) (synCssetk)) (.objMem e a) p0096
      p0098_e01_recanon
  have p0099 :=
    @gBitri
      (.classMem (synCopk (synCsn (synCsn (synCsn (synCsn (.cv e)))))
          (synCopk (synCsn (.cv a)) (.cv m))) (synCins3k (synCsik (synCssetk))))
      (.classMem (synCopk (synCsn (synCsn (.cv e))) (synCsn (.cv a)))
        (synCsik (synCssetk)))
      (.objMem e a) p0094 p0098
  have p0100 :=
    @gBitri syntaxFormula0076
      (.classMem (synCopk (synCsn (synCsn (synCsn (synCsn (.cv e)))))
          (synCopk (synCsn (.cv a)) (.cv m))) (synCins3k (synCsik (synCssetk))))
      (.objMem e a) p0093 p0099
  have p0101 :=
    @gOtkelins3k (synCsn (synCsn (synCsn (synCsn (.cv e)))))
      (synCsn (synCsn (synCsn (synCsn (.cv x))))) (synCopk (synCsn (.cv a)) (.cv m))
      (synCidk) p0072 p0028 p0016
  have p0102 :=
    @gSneqb (synCsn (synCsn (synCsn (.cv e)))) (synCsn (synCsn (synCsn (.cv x))))
      p0075
  have p0103 := @gSneqb (synCsn (synCsn (.cv e))) (synCsn (synCsn (.cv x))) p0078
  have p0104 := @gSneqb (synCsn (.cv e)) (synCsn (.cv x)) p0081
  have p0105 := @gSneqb (.cv e) (.cv x) p0084
  have p0106_e01_recanon :
    Nominal.NPrf (synWb (.classEq (synCsn (.cv e)) (synCsn (.cv x))) (.objEq e x)) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [synWb, synCsn]
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
    @gBitri (.classEq (synCsn (synCsn (.cv e))) (synCsn (synCsn (.cv x))))
      (.classEq (synCsn (.cv e)) (synCsn (.cv x))) (.objEq e x) p0104 p0106_e01_recanon
  have p0107 :=
    @gBitri
      (.classEq (synCsn (synCsn (synCsn (.cv e)))) (synCsn (synCsn (synCsn (.cv x)))))
      (.classEq (synCsn (synCsn (.cv e))) (synCsn (synCsn (.cv x)))) (.objEq e x)
      p0103 p0106
  have p0108 :=
    @gBitri syntaxFormula0077
      (.classEq (synCsn (synCsn (synCsn (.cv e)))) (synCsn (synCsn (synCsn (.cv x)))))
      (.objEq e x) p0102 p0107
  have p0109 :=
    @gOpkelidkg (synCsn (synCsn (synCsn (synCsn (.cv e)))))
      (synCsn (synCsn (synCsn (synCsn (.cv x))))) (synCvv) (synCvv)
  have p0110 :=
    @gMp2an (.classMem (synCsn (synCsn (synCsn (synCsn (.cv e))))) (synCvv))
      (.classMem (synCsn (synCsn (synCsn (synCsn (.cv x))))) (synCvv))
      (synWb syntaxFormula0079 syntaxFormula0077) p0072 p0028 p0109
  have p0111 := @gElsnc (.cv e) (.cv x) p0084
  have p0112_e02_recanon :
    Nominal.NPrf (synWb (.classMem (.cv e) (synCsn (.cv x))) (.objEq e x)) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [synWb, synCsn]
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
    @gN3bitr4i syntaxFormula0077 (.objEq e x) syntaxFormula0079
      (.classMem (.cv e) (synCsn (.cv x))) p0108 p0110 p0112_e02_recanon
  have p0113 :=
    @gBitri syntaxFormula0080 syntaxFormula0079 (.classMem (.cv e) (synCsn (.cv x)))
      p0101 p0112
  have p0114 :=
    @gOrbi12i syntaxFormula0076 (.objMem e a) syntaxFormula0080
      (.classMem (.cv e) (synCsn (.cv x))) p0100 p0113
  have p0115 :=
    @gElun syntaxClass0075 (synCins2k (synCins3k (synCsik (synCssetk))))
      (synCins3k (synCidk))
  have p0116 := @gElun (.cv e) (.cv a) (synCsn (.cv x))
  have p0117_e02_recanon :
    Nominal.NPrf
      (synWb (.classMem (.cv e) (synCun (.cv a) (synCsn (.cv x))))
        (synWo (.objMem e a) (.classMem (.cv e) (synCsn (.cv x))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [synWb, synCun, synCnin, synWnan, synWa, synCcompl, synCsn,
          synWo]
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
    @gN3bitr4i (synWo syntaxFormula0076 syntaxFormula0080)
      (synWo (.objMem e a) (.classMem (.cv e) (synCsn (.cv x)))) syntaxFormula0081
      (.classMem (.cv e) (synCun (.cv a) (synCsn (.cv x)))) p0114 p0115
      p0117_e02_recanon
  have p0118 :=
    @gBitri syntaxFormula0082 syntaxFormula0081
      (.classMem (.cv e) (synCun (.cv a) (synCsn (.cv x)))) p0092 p0117
  have p0119 :=
    @gBibi12i syntaxFormula0074 (.objMem e w) syntaxFormula0082
      (.classMem (.cv e) (synCun (.cv a) (synCsn (.cv x)))) p0091 p0118
  have p0120 :=
    @gNotbii syntaxFormula0083
      (synWb (.objMem e w) (.classMem (.cv e) (synCun (.cv a) (synCsn (.cv x))))) p0119
  have p0121 :=
    @gBitri syntaxFormula0071 (.neg syntaxFormula0083) syntaxFormula0084 p0066 p0120
  have p0122 := @gBitri syntaxFormula0067 syntaxFormula0071 syntaxFormula0084 p0065 p0121
  have p0123 := @gExbii syntaxFormula0067 syntaxFormula0084 e p0122
  have p0124 := @gBitri syntaxFormula0069 syntaxFormula0068 syntaxFormula0085 p0061 p0123
  have p0125 := @gNotbii syntaxFormula0069 syntaxFormula0085 p0124
  have p0126 := @gElcompl syntaxClass0055 syntaxClass0005 p0050
  have freshnessCertificate0368 : e ∉ (((Class.cv a)).fv) ∪ (((synCsn (.cv x))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0326 freshnessCertificate0322))
  have freshnessCertificate0369 : e ∉ ((synCun (.cv a) (synCsn (.cv x)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun];
      exact freshnessCertificate0368)
  have p0127 :=
    @gDfcleq e (.cv w) (synCun (.cv a) (synCsn (.cv x)))
      (by exact freshnessCertificate0315) (by exact freshnessCertificate0369)
  have p0128 :=
    @gAlex (synWb (.objMem e w) (.classMem (.cv e) (synCun (.cv a) (synCsn (.cv x)))))
      e
  have p0129_e00_recanon :
    Nominal.NPrf
      (synWb (.classEq (.cv w) (synCun (.cv a) (synCsn (.cv x)))) (.all e
          (synWb (.objMem e w) (.classMem (.cv e) (synCun (.cv a) (synCsn (.cv x))))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [synWb, synCun, synCnin, synWnan, synWa, synCcompl, synCsn]
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
    @gBitri (.classEq (.cv w) (synCun (.cv a) (synCsn (.cv x))))
      (.all e (synWb (.objMem e w) (.classMem (.cv e) (synCun (.cv a) (synCsn (.cv x))))))
      (.neg syntaxFormula0085) p0129_e00_recanon p0128
  have p0130 :=
    @gN3bitr4i (.neg syntaxFormula0069) (.neg syntaxFormula0085) syntaxFormula0086
      (.classEq (.cv w) (synCun (.cv a) (synCsn (.cv x)))) p0125 p0126 p0129
  have p0131 :=
    @gOtkelins2k (synCsn (synCsn (synCsn (.cv w))))
      (synCsn (synCsn (synCsn (synCsn (.cv x))))) (synCopk (synCsn (.cv a)) (.cv m))
      syntaxClass0018 p0073 p0028 p0016
  have p0132 :=
    @gOtkelins2k (synCsn (.cv w)) (synCsn (.cv a)) (.cv m) syntaxClass0017 p0079 p0012
      p0000
  have p0133 :=
    @gAncom (.classMem (synCopk (synCsn (.cv w)) (.cv t)) (synCssetk))
      syntaxFormula0087
  have p0134 := @gVex t
  have p0135 := @gOpkelcnvk (.cv t) (.cv m) syntaxClass0015 p0134 p0000
  have p0136 := @gOpkelimagekg (.cv m) (.cv t) syntaxClass0014 (synCvv) (synCvv)
  have p0137 :=
    @gMp2an (.classMem (.cv m) (synCvv)) (.classMem (.cv t) (synCvv))
      (synWb syntaxFormula0088 syntaxFormula0090) p0000 p0134 p0136
  have p0138 := @gDfaddc2 (.cv m) (synC1c)
  have p0139 := @gEqeq2i (synCplc (.cv m) (synC1c)) syntaxClass0089 (.cv t) p0138
  have p0140 :=
    @gBicomi (.classEq (.cv t) (synCplc (.cv m) (synC1c))) syntaxFormula0090 p0139
  have p0141 :=
    @gBitri syntaxFormula0088 syntaxFormula0090
      (.classEq (.cv t) (synCplc (.cv m) (synC1c))) p0137 p0140
  have p0142 :=
    @gBitri syntaxFormula0087 syntaxFormula0088
      (.classEq (.cv t) (synCplc (.cv m) (synC1c))) p0135 p0141
  have p0143 := @gElssetk (.cv w) (.cv t) p0082 p0134
  have p0144_e01_recanon :
    Nominal.NPrf
      (synWb (.classMem (synCopk (synCsn (.cv w)) (.cv t)) (synCssetk)) (.objMem w t)) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [synWb, synCopk, synCpr, synCun, synCnin, synWnan, synWa,
          synCcompl, synCsn, synCssetk, synWex]
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
    @gAnbi12i syntaxFormula0087 (.classEq (.cv t) (synCplc (.cv m) (synC1c)))
      (.classMem (synCopk (synCsn (.cv w)) (.cv t)) (synCssetk)) (.objMem w t) p0142
      p0144_e01_recanon
  have p0145 :=
    @gBitri syntaxFormula0091
      (synWa syntaxFormula0087 (.classMem (synCopk (synCsn (.cv w)) (.cv t)) (synCssetk)))
      (synWa (.classEq (.cv t) (synCplc (.cv m) (synC1c))) (.objMem w t)) p0133 p0144
  have p0146 :=
    @gExbii syntaxFormula0091
      (synWa (.classEq (.cv t) (synCplc (.cv m) (synC1c))) (.objMem w t)) t p0145
  have p0147 :=
    @gOpkelcok t (synCsn (.cv w)) (.cv m) syntaxClass0016 (synCssetk)
      (by exact freshnessCertificate0305) (by exact freshnessCertificate0067)
      (by exact freshnessCertificate0049) (by exact freshnessCertificate0000) p0079 p0000
  have p0148 := @gN1cex
  have p0149 := @gAddcex (.cv m) (synC1c) p0000 p0148
  have freshnessCertificate0370 : t ∉ (((Class.cv m)).fv) ∪ (((synC1c)).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0067 freshnessCertificate0016))
  have freshnessCertificate0371 : t ∉ ((synCplc (.cv m) (synC1c))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc];
      exact freshnessCertificate0370)
  have p0150 :=
    @gClel3 t (.cv w) (synCplc (.cv m) (synC1c)) (by exact freshnessCertificate0304)
      (by exact freshnessCertificate0371) p0149
  have p0151_e02_recanon :
    Nominal.NPrf
      (synWb (.classMem (.cv w) (synCplc (.cv m) (synC1c))) (synWex t
          (synWa (.classEq (.cv t) (synCplc (.cv m) (synC1c))) (.objMem w t)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [synWb, synCplc, synWrex, synWex, synWa, synC1c]
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
    @gN3bitr4i (synWex t syntaxFormula0091)
      (synWex t (synWa (.classEq (.cv t) (synCplc (.cv m) (synC1c))) (.objMem w t)))
      syntaxFormula0092 (.classMem (.cv w) (synCplc (.cv m) (synC1c))) p0146 p0147
      p0151_e02_recanon
  have p0152 :=
    @gBitri syntaxFormula0093 syntaxFormula0092
      (.classMem (.cv w) (synCplc (.cv m) (synC1c))) p0132 p0151
  have p0153 :=
    @gBitri syntaxFormula0094 syntaxFormula0093
      (.classMem (.cv w) (synCplc (.cv m) (synC1c))) p0131 p0152
  have p0154 :=
    @gAnbi12i syntaxFormula0086 (.classEq (.cv w) (synCun (.cv a) (synCsn (.cv x))))
      syntaxFormula0094 (.classMem (.cv w) (synCplc (.cv m) (synC1c))) p0130 p0153
  have p0155 :=
    @gBitri syntaxFormula0056 (synWa syntaxFormula0086 syntaxFormula0094)
      syntaxFormula0095 p0049 p0154
  have p0156 := @gBitri syntaxFormula0053 syntaxFormula0056 syntaxFormula0095 p0048 p0155
  have p0157 := @gExbii syntaxFormula0053 syntaxFormula0095 w p0156
  have p0158 := @gBitri syntaxFormula0048 syntaxFormula0054 syntaxFormula0096 p0044 p0157
  have p0159 := @gBitri syntaxFormula0097 syntaxFormula0048 syntaxFormula0096 p0035 p0158
  have freshnessCertificate0372 : w ∉ (((Class.cv a)).fv) ∪ (((synCsn (.cv x))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0237 freshnessCertificate0233))
  have freshnessCertificate0373 : w ∉ ((synCun (.cv a) (synCsn (.cv x)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun];
      exact freshnessCertificate0372)
  have freshnessCertificate0374 : w ∉ (((Class.cv m)).fv) ∪ (((synC1c)).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0239 freshnessCertificate0262))
  have freshnessCertificate0375 : w ∉ ((synCplc (.cv m) (synC1c))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc];
      exact freshnessCertificate0374)
  have p0160 :=
    (NFChoice.DirectNominalPrf.Nominal.DefinitionLeafHandlersCanonical001.dfClelOfDV w
      (synCun (.cv a) (synCsn (.cv x))) (synCplc (.cv m) (synC1c))
      (by exact freshnessCertificate0373) (by exact freshnessCertificate0375))
  have p0161 :=
    @gBitr4i syntaxFormula0097 syntaxFormula0096
      (.classMem (synCun (.cv a) (synCsn (.cv x))) (synCplc (.cv m) (synC1c))) p0159
      p0160
  have p0162 := @gSnex (synCsn (.cv x))
  have p0163 :=
    @gOtkelins3k (synCsn (synCsn (.cv x))) (synCsn (.cv a)) (.cv m)
      (synCsik (synCssetk)) p0162 p0012 p0000
  have p0164 := @gSnex (.cv x)
  have p0165 := @gOpksnelsik (synCsn (.cv x)) (.cv a) (synCssetk) p0164 p0095
  have p0166 := @gVex x
  have p0167 := @gElssetk (.cv x) (.cv a) p0166 p0095
  have p0168_e01_recanon :
    Nominal.NPrf
      (synWb (.classMem (synCopk (synCsn (.cv x)) (.cv a)) (synCssetk)) (.objMem x a)) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [synWb, synCopk, synCpr, synCun, synCnin, synWnan, synWa,
          synCcompl, synCsn, synCssetk, synWex]
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
    @gBitri
      (.classMem (synCopk (synCsn (synCsn (.cv x))) (synCsn (.cv a)))
        (synCsik (synCssetk)))
      (.classMem (synCopk (synCsn (.cv x)) (.cv a)) (synCssetk)) (.objMem x a) p0165
      p0168_e01_recanon
  have p0169 :=
    @gBitri syntaxFormula0098
      (.classMem (synCopk (synCsn (synCsn (.cv x))) (synCsn (.cv a)))
        (synCsik (synCssetk)))
      (.objMem x a) p0163 p0168
  have p0170 := @gNotbii syntaxFormula0098 (.objMem x a) p0169
  have p0171 :=
    @gAnbi12i syntaxFormula0097
      (.classMem (synCun (.cv a) (synCsn (.cv x))) (synCplc (.cv m) (synC1c)))
      (.neg syntaxFormula0098) (.neg (.objMem x a)) p0161 p0170
  have p0172 :=
    @gBitri syntaxFormula0099 (synWa syntaxFormula0097 (.neg syntaxFormula0098))
      (synWa (.classMem (synCun (.cv a) (synCsn (.cv x))) (synCplc (.cv m) (synC1c)))
        (.neg (.objMem x a)))
      p0033 p0171
  have p0173 :=
    @gAncom (.classMem (synCun (.cv a) (synCsn (.cv x))) (synCplc (.cv m) (synC1c)))
      (.neg (.objMem x a))
  have p0174 :=
    @gBitri syntaxFormula0099
      (synWa (.classMem (synCun (.cv a) (synCsn (.cv x))) (synCplc (.cv m) (synC1c)))
        (.neg (.objMem x a)))
      syntaxFormula0100 p0172 p0173
  have p0175 :=
    @gOpkelxpk (synCsn (synCsn (synCsn (synCsn (.cv x)))))
      (synCopk (synCsn (.cv a)) (.cv m)) (synCvv) (synCssetk) p0028 p0016
  have p0176 :=
    @gMpbiran syntaxFormula0101
      (.classMem (synCsn (synCsn (synCsn (synCsn (.cv x))))) (synCvv))
      (.classMem (synCopk (synCsn (.cv a)) (.cv m)) (synCssetk)) p0028 p0175
  have p0177 := @gElssetk (.cv a) (.cv m) p0095 p0000
  have p0178_e01_recanon :
    Nominal.NPrf
      (synWb (.classMem (synCopk (synCsn (.cv a)) (.cv m)) (synCssetk)) (.objMem a m)) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [synWb, synCopk, synCpr, synCun, synCnin, synWnan, synWa,
          synCcompl, synCsn, synCssetk, synWex]
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
    @gBitri syntaxFormula0101
      (.classMem (synCopk (synCsn (.cv a)) (.cv m)) (synCssetk)) (.objMem a m) p0176
      p0178_e01_recanon
  have p0179 := @gNotbii syntaxFormula0101 (.objMem a m) p0178
  have p0180 :=
    @gAnbi12i syntaxFormula0099 syntaxFormula0100 (.neg syntaxFormula0101)
      (.neg (.objMem a m)) p0174 p0179
  have p0181 :=
    @gBitri syntaxFormula0045 (synWa syntaxFormula0099 (.neg syntaxFormula0101))
      (synWa syntaxFormula0100 (.neg (.objMem a m))) p0032 p0180
  have p0182 := @gAnnim syntaxFormula0100 (.objMem a m)
  have p0183 :=
    @gBitri syntaxFormula0045 (synWa syntaxFormula0100 (.neg (.objMem a m)))
      syntaxFormula0103 p0181 p0182
  have p0184 := @gBitri syntaxFormula0042 syntaxFormula0045 syntaxFormula0103 p0031 p0183
  have p0185 := @gExbii syntaxFormula0042 syntaxFormula0103 x p0184
  have p0186 :=
    @gBitri syntaxFormula0035 syntaxFormula0043 (synWex x syntaxFormula0103) p0027 p0185
  have p0187 := @gExnal syntaxFormula0102 x
  have p0188 :=
    @gBitri syntaxFormula0035 (synWex x syntaxFormula0103) syntaxFormula0105 p0186 p0187
  have p0189 := @gBitri syntaxFormula0031 syntaxFormula0035 syntaxFormula0105 p0015 p0188
  have p0190 := @gExbii syntaxFormula0031 syntaxFormula0105 a p0189
  have p0191 := @gBitri syntaxFormula0034 syntaxFormula0032 syntaxFormula0106 p0011 p0190
  have p0192 := @gNotbii syntaxFormula0034 syntaxFormula0106 p0191
  have p0193 := @gElcompl (.cv m) syntaxClass0033 p0000
  have p0194 := @gAlex syntaxFormula0104 a
  have p0195 :=
    @gN3bitr4i (.neg syntaxFormula0034) (.neg syntaxFormula0106)
      (.classMem (.cv m) syntaxClass0107) syntaxFormula0108 p0192 p0193 p0194
  have freshnessCertificate0376 : m ∉ ((synCssetk)).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk];
      exact (show m ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))
  have freshnessCertificate0377 : m ∉ ((synCsik (synCssetk))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0376)
  have freshnessCertificate0378 : m ∉ ((synCsik (synCsik (synCssetk)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0377)
  have freshnessCertificate0379 :
    m ∉ ((synCsik (synCsik (synCsik (synCssetk))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0378)
  have freshnessCertificate0380 :
    m ∉ ((synCsik (synCsik (synCsik (synCsik (synCssetk)))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0379)
  have freshnessCertificate0381 :
    m ∉ ((synCsik (synCsik (synCsik (synCsik (synCsik (synCssetk))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0380)
  have freshnessCertificate0382 : m ∉ (syntaxClass0000).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0381)
  have freshnessCertificate0383 : m ∉ ((synCins3k (synCsik (synCssetk)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0377)
  have freshnessCertificate0384 :
    m ∉ ((synCins2k (synCins3k (synCsik (synCssetk))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0383)
  have freshnessCertificate0385 : m ∉ ((synCidk)).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cidk];
      exact (show m ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))
  have freshnessCertificate0386 : m ∉ ((synCins3k (synCidk))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0385)
  have freshnessCertificate0387 :
    m ∉
      (((synCins2k (synCins3k (synCsik (synCssetk))))).fv) ∪
        (((synCins3k (synCidk))).fv) :=
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
  have freshnessCertificate0392 : m ∉ ((synC1c)).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c];
      exact (show m ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))
  have freshnessCertificate0393 : m ∉ ((synCpw1 (synC1c))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0392)
  have freshnessCertificate0394 : m ∉ ((synCpw1 (synCpw1 (synC1c)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0393)
  have freshnessCertificate0395 : m ∉ ((synCpw1 (synCpw1 (synCpw1 (synC1c))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0394)
  have freshnessCertificate0396 :
    m ∉ ((synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0395)
  have freshnessCertificate0397 :
    m ∉ ((synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0396)
  have freshnessCertificate0398 :
    m ∉
      ((synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))).fv :=
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
  have freshnessCertificate0403 : m ∉ ((synCins3k (synCssetk))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0376)
  have freshnessCertificate0404 : m ∉ ((synCins2k (synCssetk))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0376)
  have freshnessCertificate0405 :
    m ∉ (((synCins3k (synCssetk))).fv) ∪ (((synCins2k (synCssetk))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0403 freshnessCertificate0404))
  have freshnessCertificate0406 :
    m ∉ ((synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin];
      exact freshnessCertificate0405)
  have freshnessCertificate0407 :
    m ∉
      (((synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))).fv) ∪
        (((synCpw1 (synCpw1 (synC1c)))).fv) :=
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
  have freshnessCertificate0411 : m ∉ ((synCins2k (synCins2k (synCssetk)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0404)
  have freshnessCertificate0412 : m ∉ ((synCins2k (synCins3k (synCssetk)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0403)
  have freshnessCertificate0413 :
    m ∉ ((synCins3k (synCsik (synCsik (synCssetk))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0378)
  have freshnessCertificate0414 :
    m ∉
      (((synCins2k (synCins3k (synCssetk)))).fv) ∪
        (((synCins3k (synCsik (synCsik (synCssetk))))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0412 freshnessCertificate0413))
  have freshnessCertificate0415 : m ∉ (syntaxClass0010).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun];
      exact freshnessCertificate0414)
  have freshnessCertificate0416 :
    m ∉ (((synCins2k (synCins2k (synCssetk)))).fv) ∪ ((syntaxClass0010).fv) :=
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
        (((synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))).fv) :=
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
    m ∉ ((syntaxClass0013).fv) ∪ (((synCpw1 (synCpw1 (synC1c)))).fv) :=
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
  have freshnessCertificate0426 : m ∉ ((syntaxClass0016).fv) ∪ (((synCssetk)).fv) :=
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
        (((synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0431 freshnessCertificate0396))
  have freshnessCertificate0433 : m ∉ (syntaxClass0021).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak];
      exact freshnessCertificate0432)
  have freshnessCertificate0434 :
    m ∉ ((syntaxClass0021).fv) ∪ (((synCins3k (synCsik (synCssetk)))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0433 freshnessCertificate0383))
  have freshnessCertificate0435 : m ∉ (syntaxClass0022).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif];
      exact freshnessCertificate0434)
  have freshnessCertificate0436 : m ∉ ((synCvv)).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv];
      exact (show m ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))
  have freshnessCertificate0437 : m ∉ (((synCvv)).fv) ∪ (((synCssetk)).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0436 freshnessCertificate0376))
  have freshnessCertificate0438 : m ∉ ((synCxpk (synCvv) (synCssetk))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk];
      exact freshnessCertificate0437)
  have freshnessCertificate0439 :
    m ∉ ((syntaxClass0022).fv) ∪ (((synCxpk (synCvv) (synCssetk))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0435 freshnessCertificate0438))
  have freshnessCertificate0440 : m ∉ (syntaxClass0023).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif];
      exact freshnessCertificate0439)
  have freshnessCertificate0441 :
    m ∉ ((syntaxClass0023).fv) ∪ (((synCpw1 (synCpw1 (synCpw1 (synC1c))))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0440 freshnessCertificate0395))
  have freshnessCertificate0442 : m ∉ (syntaxClass0024).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak];
      exact freshnessCertificate0441)
  have freshnessCertificate0443 : m ∉ ((syntaxClass0024).fv) ∪ (((synC1c)).fv) :=
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
    @gEqabi syntaxFormula0108 m syntaxClass0107 (by exact freshnessCertificate0445) p0195
  have p0197 := @gSsetkex
  have p0198 := @gSikex (synCssetk) p0197
  have p0199 := @gSikex (synCsik (synCssetk)) p0198
  have p0200 := @gSikex (synCsik (synCsik (synCssetk))) p0199
  have p0201 := @gSikex (synCsik (synCsik (synCsik (synCssetk)))) p0200
  have p0202 := @gSikex (synCsik (synCsik (synCsik (synCsik (synCssetk))))) p0201
  have p0203 :=
    @gIns3kex (synCsik (synCsik (synCsik (synCsik (synCsik (synCssetk)))))) p0202
  have p0204 := @gIns3kex (synCsik (synCssetk)) p0198
  have p0205 := @gIns2kex (synCins3k (synCsik (synCssetk))) p0204
  have p0206 := @gIdkex
  have p0207 := @gIns3kex (synCidk) p0206
  have p0208 :=
    @gUnex (synCins2k (synCins3k (synCsik (synCssetk)))) (synCins3k (synCidk))
      p0205 p0207
  have p0209 := @gIns2kex syntaxClass0001 p0208
  have p0210 := @gSymdifex syntaxClass0000 syntaxClass0002 p0203 p0209
  have p0212 := @gPw1ex (synC1c) p0148
  have p0213 := @gPw1ex (synCpw1 (synC1c)) p0212
  have p0214 := @gPw1ex (synCpw1 (synCpw1 (synC1c))) p0213
  have p0215 := @gPw1ex (synCpw1 (synCpw1 (synCpw1 (synC1c)))) p0214
  have p0216 := @gPw1ex (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))) p0215
  have p0217 :=
    @gPw1ex (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))) p0216
  have p0218 :=
    @gPw1ex (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
      p0217
  have p0219 := @gImakex syntaxClass0003 syntaxClass0004 p0210 p0218
  have p0220 := @gComplex syntaxClass0005 p0219
  have p0221 := @gAddcexlem
  have p0222 := @gImakex syntaxClass0013 (synCpw1 (synCpw1 (synC1c))) p0221 p0213
  have p0223 := @gImagekex syntaxClass0014 p0222
  have p0224 := @gCnvkex syntaxClass0015 p0223
  have p0226 := @gCokex syntaxClass0016 (synCssetk) p0224 p0197
  have p0227 := @gIns2kex syntaxClass0017 p0226
  have p0228 := @gIns2kex syntaxClass0018 p0227
  have p0229 := @gInex syntaxClass0006 syntaxClass0019 p0220 p0228
  have p0230 :=
    @gImakex syntaxClass0020 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))) p0229
      p0215
  have p0231 := @gDifex syntaxClass0021 (synCins3k (synCsik (synCssetk))) p0230 p0204
  have p0232 := @gVvex
  have p0234 := @gXpkex (synCvv) (synCssetk) p0232 p0197
  have p0235 := @gDifex syntaxClass0022 (synCxpk (synCvv) (synCssetk)) p0231 p0234
  have p0236 :=
    @gImakex syntaxClass0023 (synCpw1 (synCpw1 (synCpw1 (synC1c)))) p0235 p0214
  have p0238 := @gImakex syntaxClass0024 (synC1c) p0236 p0148
  have p0239 := @gComplex syntaxClass0033 p0238
  have p0240 :=
    @gEqeltrri syntaxClass0107 (.cab m syntaxFormula0108) (synCvv) p0196 p0239
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

/-- Checked nominal proof certificate identified upstream as `g_nnsucelrlem2`. -/
@[expose]
noncomputable def gNnsucelrlem2 (A : Class) (B : Class) :
    Nominal.NPrf
      (.imp (.neg (.classMem B A))
        (.classEq (synCdif (synCun A (synCsn B)) (synCsn B)) A)) :=
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
  have p0000 := @gEldifsn (.cv x) (synCun A (synCsn B)) B
  have p0001 := @gElun (.cv x) A (synCsn B)
  have p0002 := @gElsn x B (by exact (show x ∉ (B).fv from (by exact fresh_x_not_B)))
  have p0003 :=
    @gOrbi2i (.classMem (.cv x) (synCsn B)) (.classEq (.cv x) B) (.classMem (.cv x) A)
      p0002
  have p0004 :=
    @gBitri (.classMem (.cv x) (synCun A (synCsn B)))
      (synWo (.classMem (.cv x) A) (.classMem (.cv x) (synCsn B)))
      (synWo (.classMem (.cv x) A) (.classEq (.cv x) B)) p0001 p0003
  have p0005 := (Nominal.biimpRefl (synWne (.cv x) B))
  have p0006 :=
    @gAnbi12i (.classMem (.cv x) (synCun A (synCsn B)))
      (synWo (.classMem (.cv x) A) (.classEq (.cv x) B)) (synWne (.cv x) B)
      (.neg (.classEq (.cv x) B)) p0004 p0005
  have p0007 := @gPm561 (.classMem (.cv x) A) (.classEq (.cv x) B)
  have p0008 :=
    @gN3bitri (.classMem (.cv x) (synCdif (synCun A (synCsn B)) (synCsn B)))
      (synWa (.classMem (.cv x) (synCun A (synCsn B))) (synWne (.cv x) B))
      (synWa (synWo (.classMem (.cv x) A) (.classEq (.cv x) B)) (.neg (.classEq (.cv x) B)))
      (synWa (.classMem (.cv x) A) (.neg (.classEq (.cv x) B))) p0000 p0006 p0007
  have p0009 := @gAncom (.classMem (.cv x) A) (.neg (.classEq (.cv x) B))
  have p0010 :=
    @gBitri (.classMem (.cv x) (synCdif (synCun A (synCsn B)) (synCsn B)))
      (synWa (.classMem (.cv x) A) (.neg (.classEq (.cv x) B)))
      (synWa (.neg (.classEq (.cv x) B)) (.classMem (.cv x) A)) p0008 p0009
  have p0011 := @gEleq1 (.cv x) B A
  have p0012 :=
    @gBiimpcd (.classEq (.cv x) B) (.classMem (.cv x) A) (.classMem B A) p0011
  have p0013 := @gCon3d (.classMem (.cv x) A) (.classEq (.cv x) B) (.classMem B A) p0012
  have p0014 :=
    @gCom12 (.classMem (.cv x) A) (.neg (.classMem B A)) (.neg (.classEq (.cv x) B))
      p0013
  have p0015 :=
    @gPm471rd (.neg (.classMem B A)) (.classMem (.cv x) A) (.neg (.classEq (.cv x) B))
      p0014
  have p0016 :=
    @gBicomd (.neg (.classMem B A)) (.classMem (.cv x) A)
      (synWa (.neg (.classEq (.cv x) B)) (.classMem (.cv x) A)) p0015
  have p0017 :=
    @gSyl5bb (.classMem (.cv x) (synCdif (synCun A (synCsn B)) (synCsn B)))
      (synWa (.neg (.classEq (.cv x) B)) (.classMem (.cv x) A)) (.neg (.classMem B A))
      (.classMem (.cv x) A) p0010 p0016
  have freeVariableCertificate0 :
    x ∉ ((synCdif (synCun A (synCsn B)) (synCsn B))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
      fresh_x_not_A, fresh_x_not_B, or_false, not_false_eq_true]
  have freeVariableCertificate1 : x ∉ ((Wff.neg (.classMem B A))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_neg,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, Finset.mem_union, fresh_x_not_B,
      fresh_x_not_A, or_false, not_false_eq_true]
  have p0018 :=
    @gEqrdv (.neg (.classMem B A)) x (synCdif (synCun A (synCsn B)) (synCsn B)) A
      freeVariableCertificate0 (by exact (show x ∉ (A).fv from (by exact fresh_x_not_A)))
      freeVariableCertificate1 p0017
  exact p0018

/-- Checked nominal proof certificate identified upstream as `g_nnsucelrlem3`. -/
@[expose]
noncomputable def gNnsucelrlem3 (A : Class) (B : Class) (X : Class) (Y : Class)
    (hyp_nnsucelrlem3_1 : Nominal.NPrf (.classMem X (synCvv))) :
    Nominal.NPrf
      (.imp (synW3a (synWne X Y) (.classEq (synCun A (synCsn X)) (synCun B (synCsn Y)))
          (.neg (.classMem Y B)))
        (.classEq B (synCun (synCdif A (synCsn Y)) (synCsn X)))) :=
  by
  have p0000 := @gIndir B (synCsn Y) (synCcompl (synCsn Y))
  have p0001 := (Nominal.classEqRefl (synCdif B (synCsn Y)))
  have p0002 :=
    @gEqcomi (synCdif B (synCsn Y)) (synCin B (synCcompl (synCsn Y))) p0001
  have p0003 := @gIncompl (synCsn Y)
  have p0004 :=
    @gUneq12i (synCin B (synCcompl (synCsn Y))) (synCdif B (synCsn Y))
      (synCin (synCsn Y) (synCcompl (synCsn Y))) (synC0) p0002 p0003
  have p0005 := @gUn0 (synCdif B (synCsn Y))
  have p0006 :=
    @gEqtri
      (synCun (synCin B (synCcompl (synCsn Y)))
        (synCin (synCsn Y) (synCcompl (synCsn Y))))
      (synCun (synCdif B (synCsn Y)) (synC0)) (synCdif B (synCsn Y)) p0004 p0005
  have p0007 :=
    @gEqtri (synCin (synCun B (synCsn Y)) (synCcompl (synCsn Y)))
      (synCun (synCin B (synCcompl (synCsn Y)))
        (synCin (synCsn Y) (synCcompl (synCsn Y))))
      (synCdif B (synCsn Y)) p0000 p0006
  have p0008 := @gDifsn Y B
  have p0009 :=
    @gN3ad2ant3 (.neg (.classMem Y B)) (synWne X Y)
      (.classEq (synCdif B (synCsn Y)) B)
      (.classEq (synCun A (synCsn X)) (synCun B (synCsn Y))) p0008
  have p0010 :=
    @gSyl5req
      (synW3a (synWne X Y) (.classEq (synCun A (synCsn X)) (synCun B (synCsn Y)))
        (.neg (.classMem Y B)))
      (synCin (synCun B (synCsn Y)) (synCcompl (synCsn Y))) (synCdif B (synCsn Y))
      B p0007 p0009
  have p0011 :=
    @gSimp2 (synWne X Y) (.classEq (synCun A (synCsn X)) (synCun B (synCsn Y)))
      (.neg (.classMem Y B))
  have p0012 := (Nominal.biimpRefl (synWne X Y))
  have p0013 := @gBiimpi (synWne X Y) (.neg (.classEq X Y)) p0012
  have p0014 :=
    @gN3ad2ant1 (synWne X Y) (.classEq (synCun A (synCsn X)) (synCun B (synCsn Y)))
      (.neg (.classEq X Y)) (.neg (.classMem Y B)) p0013
  have p0015 := @gElcompl X (synCsn Y) hyp_nnsucelrlem3_1
  have p0016 := @gElsnc X Y hyp_nnsucelrlem3_1
  have p0017 :=
    @gXchbinx (.classMem X (synCcompl (synCsn Y))) (.classMem X (synCsn Y))
      (.classEq X Y) p0015 p0016
  have p0018 := @gSnss X (synCcompl (synCsn Y)) hyp_nnsucelrlem3_1
  have p0019 :=
    @gBitr3i (.neg (.classEq X Y)) (.classMem X (synCcompl (synCsn Y)))
      (synWss (synCsn X) (synCcompl (synCsn Y))) p0017 p0018
  have p0020 :=
    @gSylib
      (synW3a (synWne X Y) (.classEq (synCun A (synCsn X)) (synCun B (synCsn Y)))
        (.neg (.classMem Y B)))
      (.neg (.classEq X Y)) (synWss (synCsn X) (synCcompl (synCsn Y))) p0014 p0019
  have p0021 := @gSsequn2 (synCsn X) (synCcompl (synCsn Y))
  have p0022 :=
    @gSylib
      (synW3a (synWne X Y) (.classEq (synCun A (synCsn X)) (synCun B (synCsn Y)))
        (.neg (.classMem Y B)))
      (synWss (synCsn X) (synCcompl (synCsn Y)))
      (.classEq (synCun (synCcompl (synCsn Y)) (synCsn X)) (synCcompl (synCsn Y)))
      p0020 p0021
  have p0023 :=
    @gIneq12d
      (synW3a (synWne X Y) (.classEq (synCun A (synCsn X)) (synCun B (synCsn Y)))
        (.neg (.classMem Y B)))
      (synCun A (synCsn X)) (synCun B (synCsn Y))
      (synCun (synCcompl (synCsn Y)) (synCsn X)) (synCcompl (synCsn Y)) p0011 p0022
  have p0024 :=
    @gEqtr4d
      (synW3a (synWne X Y) (.classEq (synCun A (synCsn X)) (synCun B (synCsn Y)))
        (.neg (.classMem Y B)))
      B (synCin (synCun B (synCsn Y)) (synCcompl (synCsn Y)))
      (synCin (synCun A (synCsn X)) (synCun (synCcompl (synCsn Y)) (synCsn X)))
      p0010 p0023
  have p0025 := (Nominal.classEqRefl (synCdif A (synCsn Y)))
  have p0026 :=
    @gUneq1i (synCdif A (synCsn Y)) (synCin A (synCcompl (synCsn Y))) (synCsn X)
      p0025
  have p0027 := @gUndir A (synCcompl (synCsn Y)) (synCsn X)
  have p0028 :=
    @gEqtri (synCun (synCdif A (synCsn Y)) (synCsn X))
      (synCun (synCin A (synCcompl (synCsn Y))) (synCsn X))
      (synCin (synCun A (synCsn X)) (synCun (synCcompl (synCsn Y)) (synCsn X)))
      p0026 p0027
  have p0029 :=
    @gSyl6eqr
      (synW3a (synWne X Y) (.classEq (synCun A (synCsn X)) (synCun B (synCsn Y)))
        (.neg (.classMem Y B)))
      B (synCin (synCun A (synCsn X)) (synCun (synCcompl (synCsn Y)) (synCsn X)))
      (synCun (synCdif A (synCsn Y)) (synCsn X)) p0024 p0028
  exact p0029

/-- Checked nominal proof certificate identified upstream as `g_nnsucelrlem4`. -/
@[expose]
noncomputable def gNnsucelrlem4 (A : Class) (B : Class) :
    Nominal.NPrf
      (.imp (.classMem A B) (.classEq (synCun (synCdif B (synCsn A)) (synCsn A)) B)) :=
  by
  have p0000 := @gUndif1 B (synCsn A)
  have p0001 := @gSnssi A B
  have p0002 := @gSsequn2 (synCsn A) B
  have p0003 :=
    @gSylib (.classMem A B) (synWss (synCsn A) B) (.classEq (synCun B (synCsn A)) B)
      p0001 p0002
  have p0004 :=
    @gSyl5eq (.classMem A B) (synCun (synCdif B (synCsn A)) (synCsn A))
      (synCun B (synCsn A)) B p0000 p0003
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

/-- Checked nominal proof certificate identified upstream as `g_nnsucelr`. -/
@[expose]
noncomputable def gNnsucelr (A : Class) (M : Class) (X : Class)
    (hyp_nnsucelr_1 : Nominal.NPrf (.classMem A (synCvv)))
    (hyp_nnsucelr_2 : Nominal.NPrf (.classMem X (synCvv))) :
    Nominal.NPrf
      (.imp (synWa (.classMem M (synCnnc)) (synWa (.neg (.classMem X A))
            (.classMem (synCun A (synCsn X)) (synCplc M (synC1c))))) (.classMem A M)) :=
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
    @gNnsucelrlem1 x m a (show a ≠ m from (by exact fresh_a_ne_m))
      (show a ≠ x from (by exact fresh_a_ne_x)) (show m ≠ x from (by exact fresh_m_ne_x))
  have p0001 := @gAddceq1 (.cv m) (synC0c) (synC1c)
  have p0002 := @gAddcid2 (synC1c)
  have p0003 :=
    @gSyl6eq (.classEq (.cv m) (synC0c)) (synCplc (.cv m) (synC1c))
      (synCplc (synC0c) (synC1c)) (synC1c) p0001 p0002
  have p0004 :=
    @gEleq2d (.classEq (.cv m) (synC0c)) (synCplc (.cv m) (synC1c)) (synC1c)
      (synCun (.cv a) (synCsn (.cv x))) p0003
  have freeVariableCertificate0 : y ∉ ((synCun (.cv a) (synCsn (.cv x)))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
      Finset.mem_singleton, fresh_y_ne_a, fresh_y_ne_x, or_false, not_false_eq_true]
  have p0005 := @gEl1c y (synCun (.cv a) (synCsn (.cv x))) freeVariableCertificate0
  have p0006 :=
    @gSyl6bb (.classEq (.cv m) (synC0c))
      (.classMem (synCun (.cv a) (synCsn (.cv x))) (synCplc (.cv m) (synC1c)))
      (.classMem (synCun (.cv a) (synCsn (.cv x))) (synC1c))
      (synWex y (.classEq (synCun (.cv a) (synCsn (.cv x))) (synCsn (.cv y)))) p0004
      p0005
  have p0007 :=
    @gAnbi2d (.classEq (.cv m) (synC0c))
      (.classMem (synCun (.cv a) (synCsn (.cv x))) (synCplc (.cv m) (synC1c)))
      (synWex y (.classEq (synCun (.cv a) (synCsn (.cv x))) (synCsn (.cv y))))
      (.neg (.objMem x a)) p0006
  have p0008 := @gEleq2 (.cv m) (synC0c) (.cv a)
  have p0009 := (Nominal.classEqRefl (synC0c))
  have p0010 := @gEleq2i (synC0c) (synCsn (synC0)) (.cv a) p0009
  have p0011 := @gVex a
  have p0012 := @gElsnc (.cv a) (synC0) p0011
  have p0013 :=
    @gBitri (.classMem (.cv a) (synC0c)) (.classMem (.cv a) (synCsn (synC0)))
      (.classEq (.cv a) (synC0)) p0010 p0012
  have p0014_e00_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv m) (synC0c))
        (synWb (.objMem a m) (.classMem (.cv a) (synC0c)))) :=
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
      p0008
  have p0014 :=
    @gSyl6bb (.classEq (.cv m) (synC0c)) (.objMem a m) (.classMem (.cv a) (synC0c))
      (.classEq (.cv a) (synC0)) p0014_e00_recanon p0013
  have p0015 :=
    @gImbi12d (.classEq (.cv m) (synC0c))
      (synWa (.neg (.objMem x a))
        (.classMem (synCun (.cv a) (synCsn (.cv x))) (synCplc (.cv m) (synC1c))))
      (synWa (.neg (.objMem x a))
        (synWex y (.classEq (synCun (.cv a) (synCsn (.cv x))) (synCsn (.cv y)))))
      (.objMem a m) (.classEq (.cv a) (synC0)) p0007 p0014
  have freeVariableCertificate1 : a ∉ ((Wff.classEq (.cv m) (synC0c))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_a_ne_m, or_false,
      not_false_eq_true]
  have freeVariableCertificate2 : x ∉ ((Wff.classEq (.cv m) (synC0c))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_x_ne_m, or_false,
      not_false_eq_true]
  have p0016 :=
    @gN2albidv (.classEq (.cv m) (synC0c))
      (.imp (synWa (.neg (.objMem x a))
          (.classMem (synCun (.cv a) (synCsn (.cv x))) (synCplc (.cv m) (synC1c))))
        (.objMem a m))
      (.imp (synWa (.neg (.objMem x a))
          (synWex y (.classEq (synCun (.cv a) (synCsn (.cv x))) (synCsn (.cv y)))))
        (.classEq (.cv a) (synC0)))
      a x freeVariableCertificate1 freeVariableCertificate2 p0015
  have p0017 := @gAddceq1 (.cv m) (.cv n) (synC1c)
  have p0018_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq m n)
        (.classEq (synCplc (.cv m) (synC1c)) (synCplc (.cv n) (synC1c)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synCplc synWrex synWex synWa synC1c
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0017
  have p0018 :=
    @gEleq2d (.objEq m n) (synCplc (.cv m) (synC1c)) (synCplc (.cv n) (synC1c))
      (synCun (.cv a) (synCsn (.cv x))) p0018_e00_recanon
  have p0019 :=
    @gAnbi2d (.objEq m n)
      (.classMem (synCun (.cv a) (synCsn (.cv x))) (synCplc (.cv m) (synC1c)))
      (.classMem (synCun (.cv a) (synCsn (.cv x))) (synCplc (.cv n) (synC1c)))
      (.neg (.objMem x a)) p0018
  have p0020 := @gEleq2 (.cv m) (.cv n) (.cv a)
  have p0021_e01_recanon :
    Nominal.NPrf (.imp (.objEq m n) (synWb (.objMem a m) (.objMem a n))) :=
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
      p0020
  have p0021 :=
    @gImbi12d (.objEq m n)
      (synWa (.neg (.objMem x a))
        (.classMem (synCun (.cv a) (synCsn (.cv x))) (synCplc (.cv m) (synC1c))))
      (synWa (.neg (.objMem x a))
        (.classMem (synCun (.cv a) (synCsn (.cv x))) (synCplc (.cv n) (synC1c))))
      (.objMem a m) (.objMem a n) p0019 p0021_e01_recanon
  have freeVariableCertificate3 : a ∉ ((Wff.objEq m n)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_insert,
      Finset.mem_singleton, fresh_a_ne_m, fresh_a_ne_n, or_false, not_false_eq_true]
  have freeVariableCertificate4 : x ∉ ((Wff.objEq m n)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_insert,
      Finset.mem_singleton, fresh_x_ne_m, fresh_x_ne_n, or_false, not_false_eq_true]
  have p0022 :=
    @gN2albidv (.objEq m n)
      (.imp (synWa (.neg (.objMem x a))
          (.classMem (synCun (.cv a) (synCsn (.cv x))) (synCplc (.cv m) (synC1c))))
        (.objMem a m))
      (.imp (synWa (.neg (.objMem x a))
          (.classMem (synCun (.cv a) (synCsn (.cv x))) (synCplc (.cv n) (synC1c))))
        (.objMem a n))
      a x freeVariableCertificate3 freeVariableCertificate4 p0021
  have p0023 := @gEleq12 (.cv x) (.cv z) (.cv a) (.cv c)
  have p0024_e00_recanon :
    Nominal.NPrf
      (.imp (synWa (.objEq x z) (.objEq a c)) (synWb (.objMem x a) (.objMem z c))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWa synWb
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
    @gAncoms (.objEq x z) (.objEq a c) (synWb (.objMem x a) (.objMem z c))
      p0024_e00_recanon
  have p0025 :=
    @gNotbid (synWa (.objEq a c) (.objEq x z)) (.objMem x a) (.objMem z c) p0024
  have p0026 := @gSneq (.cv x) (.cv z)
  have p0027 := @gUneq12 (.cv a) (.cv c) (synCsn (.cv x)) (synCsn (.cv z))
  have p0028_e00_recanon :
    Nominal.NPrf (.imp (.objEq x z) (.classEq (synCsn (.cv x)) (synCsn (.cv z)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synCsn
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0026
  have p0028_e01_recanon :
    Nominal.NPrf
      (.imp (synWa (.objEq a c) (.classEq (synCsn (.cv x)) (synCsn (.cv z))))
        (.classEq (synCun (.cv a) (synCsn (.cv x))) (synCun (.cv c) (synCsn (.cv z))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWa synCsn synCun synCnin synWnan synCcompl
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
    @gSylan2 (.objEq x z) (.objEq a c) (.classEq (synCsn (.cv x)) (synCsn (.cv z)))
      (.classEq (synCun (.cv a) (synCsn (.cv x))) (synCun (.cv c) (synCsn (.cv z))))
      p0028_e00_recanon p0028_e01_recanon
  have p0029 :=
    @gEleq1d (synWa (.objEq a c) (.objEq x z)) (synCun (.cv a) (synCsn (.cv x)))
      (synCun (.cv c) (synCsn (.cv z))) (synCplc (.cv n) (synC1c)) p0028
  have p0030 :=
    @gAnbi12d (synWa (.objEq a c) (.objEq x z)) (.neg (.objMem x a))
      (.neg (.objMem z c))
      (.classMem (synCun (.cv a) (synCsn (.cv x))) (synCplc (.cv n) (synC1c)))
      (.classMem (synCun (.cv c) (synCsn (.cv z))) (synCplc (.cv n) (synC1c))) p0025
      p0029
  have p0031 := @gEleq1 (.cv a) (.cv c) (.cv n)
  have p0032_e00_recanon :
    Nominal.NPrf (.imp (.objEq a c) (synWb (.objMem a n) (.objMem c n))) :=
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
      p0031
  have p0032 :=
    @gAdantr (.objEq a c) (synWb (.objMem a n) (.objMem c n)) (.objEq x z)
      p0032_e00_recanon
  have p0033 :=
    @gImbi12d (synWa (.objEq a c) (.objEq x z))
      (synWa (.neg (.objMem x a))
        (.classMem (synCun (.cv a) (synCsn (.cv x))) (synCplc (.cv n) (synC1c))))
      (synWa (.neg (.objMem z c))
        (.classMem (synCun (.cv c) (synCsn (.cv z))) (synCplc (.cv n) (synC1c))))
      (.objMem a n) (.objMem c n) p0030 p0032
  have freeVariableCertificate5 :
    z ∉
      ((Wff.imp (synWa (.neg (.objMem x a))
            (.classMem (synCun (.cv a) (synCsn (.cv x))) (synCplc (.cv n) (synC1c))))
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
      ((Wff.imp (synWa (.neg (.objMem x a))
            (.classMem (synCun (.cv a) (synCsn (.cv x))) (synCplc (.cv n) (synC1c))))
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
      ((Wff.imp (synWa (.neg (.objMem z c))
            (.classMem (synCun (.cv c) (synCsn (.cv z))) (synCplc (.cv n) (synC1c))))
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
      ((Wff.imp (synWa (.neg (.objMem z c))
            (.classMem (synCun (.cv c) (synCsn (.cv z))) (synCplc (.cv n) (synC1c))))
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
    @gCbval2v
      (.imp (synWa (.neg (.objMem x a))
          (.classMem (synCun (.cv a) (synCsn (.cv x))) (synCplc (.cv n) (synC1c))))
        (.objMem a n))
      (.imp (synWa (.neg (.objMem z c))
          (.classMem (synCun (.cv c) (synCsn (.cv z))) (synCplc (.cv n) (synC1c))))
        (.objMem c n))
      a x c z freeVariableCertificate5 freeVariableCertificate6 freeVariableCertificate7
      freeVariableCertificate8 (show z ≠ a from (by exact fresh_z_ne_a))
      (show z ≠ c from (by exact fresh_z_ne_c)) (show a ≠ x from (by exact fresh_a_ne_x))
      (show x ≠ c from (by exact fresh_x_ne_c)) p0033
  have p0035 :=
    @gSyl6bb (.objEq m n)
      (.all a (.all x (.imp (synWa (.neg (.objMem x a))
              (.classMem (synCun (.cv a) (synCsn (.cv x))) (synCplc (.cv m) (synC1c))))
            (.objMem a m))))
      (.all a (.all x (.imp (synWa (.neg (.objMem x a))
              (.classMem (synCun (.cv a) (synCsn (.cv x))) (synCplc (.cv n) (synC1c))))
            (.objMem a n))))
      (.all c (.all z (.imp (synWa (.neg (.objMem z c))
              (.classMem (synCun (.cv c) (synCsn (.cv z))) (synCplc (.cv n) (synC1c))))
            (.objMem c n))))
      p0022 p0034
  have p0036 := @gAddceq1 (.cv m) (synCplc (.cv n) (synC1c)) (synC1c)
  have p0037 :=
    @gEleq2d (.classEq (.cv m) (synCplc (.cv n) (synC1c))) (synCplc (.cv m) (synC1c))
      (synCplc (synCplc (.cv n) (synC1c)) (synC1c))
      (synCun (.cv a) (synCsn (.cv x))) p0036
  have p0038 :=
    @gAnbi2d (.classEq (.cv m) (synCplc (.cv n) (synC1c)))
      (.classMem (synCun (.cv a) (synCsn (.cv x))) (synCplc (.cv m) (synC1c)))
      (.classMem (synCun (.cv a) (synCsn (.cv x)))
        (synCplc (synCplc (.cv n) (synC1c)) (synC1c)))
      (.neg (.objMem x a)) p0037
  have p0039 := @gEleq2 (.cv m) (synCplc (.cv n) (synC1c)) (.cv a)
  have p0040_e01_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv m) (synCplc (.cv n) (synC1c)))
        (synWb (.objMem a m) (.classMem (.cv a) (synCplc (.cv n) (synC1c))))) :=
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
      p0039
  have p0040 :=
    @gImbi12d (.classEq (.cv m) (synCplc (.cv n) (synC1c)))
      (synWa (.neg (.objMem x a))
        (.classMem (synCun (.cv a) (synCsn (.cv x))) (synCplc (.cv m) (synC1c))))
      (synWa (.neg (.objMem x a)) (.classMem (synCun (.cv a) (synCsn (.cv x)))
          (synCplc (synCplc (.cv n) (synC1c)) (synC1c))))
      (.objMem a m) (.classMem (.cv a) (synCplc (.cv n) (synC1c))) p0038
      p0040_e01_recanon
  have freeVariableCertificate9 :
    a ∉ ((Wff.classEq (.cv m) (synCplc (.cv n) (synC1c)))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_a_ne_m, fresh_a_ne_n, or_false,
      not_false_eq_true]
  have freeVariableCertificate10 :
    x ∉ ((Wff.classEq (.cv m) (synCplc (.cv n) (synC1c)))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_x_ne_m, fresh_x_ne_n, or_false,
      not_false_eq_true]
  have p0041 :=
    @gN2albidv (.classEq (.cv m) (synCplc (.cv n) (synC1c)))
      (.imp (synWa (.neg (.objMem x a))
          (.classMem (synCun (.cv a) (synCsn (.cv x))) (synCplc (.cv m) (synC1c))))
        (.objMem a m))
      (.imp (synWa (.neg (.objMem x a)) (.classMem (synCun (.cv a) (synCsn (.cv x)))
            (synCplc (synCplc (.cv n) (synC1c)) (synC1c))))
        (.classMem (.cv a) (synCplc (.cv n) (synC1c))))
      a x freeVariableCertificate9 freeVariableCertificate10 p0040
  have p0042 := @gAddceq1 (.cv m) M (synC1c)
  have p0043 :=
    @gEleq2d (.classEq (.cv m) M) (synCplc (.cv m) (synC1c)) (synCplc M (synC1c))
      (synCun (.cv a) (synCsn (.cv x))) p0042
  have p0044 :=
    @gAnbi2d (.classEq (.cv m) M)
      (.classMem (synCun (.cv a) (synCsn (.cv x))) (synCplc (.cv m) (synC1c)))
      (.classMem (synCun (.cv a) (synCsn (.cv x))) (synCplc M (synC1c)))
      (.neg (.objMem x a)) p0043
  have p0045 := @gEleq2 (.cv m) M (.cv a)
  have p0046_e01_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv m) M) (synWb (.objMem a m) (.classMem (.cv a) M))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb
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
    @gImbi12d (.classEq (.cv m) M)
      (synWa (.neg (.objMem x a))
        (.classMem (synCun (.cv a) (synCsn (.cv x))) (synCplc (.cv m) (synC1c))))
      (synWa (.neg (.objMem x a))
        (.classMem (synCun (.cv a) (synCsn (.cv x))) (synCplc M (synC1c))))
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
    @gN2albidv (.classEq (.cv m) M)
      (.imp (synWa (.neg (.objMem x a))
          (.classMem (synCun (.cv a) (synCsn (.cv x))) (synCplc (.cv m) (synC1c))))
        (.objMem a m))
      (.imp (synWa (.neg (.objMem x a))
          (.classMem (synCun (.cv a) (synCsn (.cv x))) (synCplc M (synC1c))))
        (.classMem (.cv a) M))
      a x freeVariableCertificate11 freeVariableCertificate12 p0046
  have p0048 := @gVex x
  have p0049 := @gUnsneqsn (.cv a) (.cv x) (.cv y) p0048
  have p0050 :=
    @gOrd (.classEq (synCun (.cv a) (synCsn (.cv x))) (synCsn (.cv y)))
      (.classEq (.cv a) (synC0)) (.classEq (.cv a) (synCsn (.cv x))) p0049
  have p0051 := @gSnid (.cv x) p0048
  have p0052 := @gEleq2 (.cv a) (synCsn (.cv x)) (.cv x)
  have p0053_e01_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv a) (synCsn (.cv x)))
        (synWb (.objMem x a) (.classMem (.cv x) (synCsn (.cv x))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synCsn synWb
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
    @gMpbiri (.classEq (.cv a) (synCsn (.cv x))) (.objMem x a)
      (.classMem (.cv x) (synCsn (.cv x))) p0051 p0053_e01_recanon
  have p0054 :=
    @gSyl6 (.classEq (synCun (.cv a) (synCsn (.cv x))) (synCsn (.cv y)))
      (.neg (.classEq (.cv a) (synC0))) (.classEq (.cv a) (synCsn (.cv x)))
      (.objMem x a) p0050 p0053
  have p0055 :=
    @gCon1d (.classEq (synCun (.cv a) (synCsn (.cv x))) (synCsn (.cv y)))
      (.classEq (.cv a) (synC0)) (.objMem x a) p0054
  have freeVariableCertificate13 :
    y ∉ ((Wff.imp (.neg (.objMem x a)) (.classEq (.cv a) (synC0)))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
      NFChoice.Compiler.CoreFVSimp.fv_wff_neg, NFChoice.Compiler.CoreFVSimp.fv_wff_objMem,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union,
      Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, fresh_y_ne_x,
      fresh_y_ne_a, or_false, not_false_eq_true]
  have p0056 :=
    @gExlimiv (.classEq (synCun (.cv a) (synCsn (.cv x))) (synCsn (.cv y)))
      (.imp (.neg (.objMem x a)) (.classEq (.cv a) (synC0))) y freeVariableCertificate13
      p0055
  have p0057 :=
    @gImpcom (synWex y (.classEq (synCun (.cv a) (synCsn (.cv x))) (synCsn (.cv y))))
      (.neg (.objMem x a)) (.classEq (.cv a) (synC0)) p0056
  have p0058 :=
    @gGen2
      (.imp (synWa (.neg (.objMem x a))
          (synWex y (.classEq (synCun (.cv a) (synCsn (.cv x))) (synCsn (.cv y)))))
        (.classEq (.cv a) (synC0)))
      a x p0057
  have freeVariableCertificate14 : b ∉ ((synCun (.cv a) (synCsn (.cv x)))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
      Finset.mem_singleton, fresh_b_ne_a, fresh_b_ne_x, or_false, not_false_eq_true]
  have freeVariableCertificate15 : b ∉ ((synCplc (.cv n) (synC1c))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_b_ne_n, or_false,
      not_false_eq_true]
  have p0059 :=
    @gElsuc y (synCun (.cv a) (synCsn (.cv x))) (synCplc (.cv n) (synC1c)) b
      freeVariableCertificate14 freeVariableCertificate0 freeVariableCertificate15
      (show b ≠ y from (by exact fresh_b_ne_y))
  have p0060 := @gVex y
  have p0061 := @gElcompl (.cv y) (.cv b) p0060
  have p0062_e00_recanon :
    Nominal.NPrf (synWb (.classMem (.cv y) (synCcompl (.cv b))) (.neg (.objMem y b))) :=
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
      p0061
  have p0062 :=
    @gAnbi2i (.classMem (.cv y) (synCcompl (.cv b))) (.neg (.objMem y b))
      (.classMem (.cv b) (synCplc (.cv n) (synC1c))) p0062_e00_recanon
  have p0063 :=
    @gSimprrl (.objEq x y)
      (synWa (.classMem (.cv b) (synCplc (.cv n) (synC1c))) (.neg (.objMem y b)))
      (.classEq (synCun (.cv a) (synCsn (.cv x))) (synCun (.cv b) (synCsn (.cv y))))
      (.neg (.objMem x a))
  have p0064 := @gSneq (.cv x) (.cv y)
  have p0065_e00_recanon :
    Nominal.NPrf (.imp (.objEq x y) (.classEq (synCsn (.cv x)) (synCsn (.cv y)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synCsn
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0064
  have p0065 :=
    @gAdantr (.objEq x y) (.classEq (synCsn (.cv x)) (synCsn (.cv y)))
      (synWa (synWa (.classMem (.cv b) (synCplc (.cv n) (synC1c))) (.neg (.objMem y b)))
        (synWa (.classEq (synCun (.cv a) (synCsn (.cv x)))
            (synCun (.cv b) (synCsn (.cv y)))) (.neg (.objMem x a))))
      p0065_e00_recanon
  have p0066 :=
    @gDifeq12d
      (synWa (.objEq x y) (synWa
          (synWa (.classMem (.cv b) (synCplc (.cv n) (synC1c))) (.neg (.objMem y b))) (synWa
            (.classEq (synCun (.cv a) (synCsn (.cv x))) (synCun (.cv b) (synCsn (.cv y))))
            (.neg (.objMem x a)))))
      (synCun (.cv a) (synCsn (.cv x))) (synCun (.cv b) (synCsn (.cv y)))
      (synCsn (.cv x)) (synCsn (.cv y)) p0063 p0065
  have p0067 :=
    @gSimprrr (.objEq x y)
      (synWa (.classMem (.cv b) (synCplc (.cv n) (synC1c))) (.neg (.objMem y b)))
      (.classEq (synCun (.cv a) (synCsn (.cv x))) (synCun (.cv b) (synCsn (.cv y))))
      (.neg (.objMem x a))
  have p0068 := @gNnsucelrlem2 (.cv a) (.cv x)
  have p0069_e01_recanon :
    Nominal.NPrf
      (.imp (.neg (.objMem x a))
        (.classEq (synCdif (synCun (.cv a) (synCsn (.cv x))) (synCsn (.cv x))) (.cv a))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synCdif synCin synCcompl synCnin synWnan synWa synCun synCsn
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0068
  have p0069 :=
    @gSyl
      (synWa (.objEq x y) (synWa
          (synWa (.classMem (.cv b) (synCplc (.cv n) (synC1c))) (.neg (.objMem y b))) (synWa
            (.classEq (synCun (.cv a) (synCsn (.cv x))) (synCun (.cv b) (synCsn (.cv y))))
            (.neg (.objMem x a)))))
      (.neg (.objMem x a))
      (.classEq (synCdif (synCun (.cv a) (synCsn (.cv x))) (synCsn (.cv x))) (.cv a))
      p0067 p0069_e01_recanon
  have p0070 :=
    @gSimprlr (.objEq x y) (.classMem (.cv b) (synCplc (.cv n) (synC1c)))
      (.neg (.objMem y b))
      (synWa (.classEq (synCun (.cv a) (synCsn (.cv x))) (synCun (.cv b) (synCsn (.cv y))))
        (.neg (.objMem x a)))
  have p0071 := @gNnsucelrlem2 (.cv b) (.cv y)
  have p0072_e01_recanon :
    Nominal.NPrf
      (.imp (.neg (.objMem y b))
        (.classEq (synCdif (synCun (.cv b) (synCsn (.cv y))) (synCsn (.cv y))) (.cv b))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synCdif synCin synCcompl synCnin synWnan synWa synCun synCsn
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0071
  have p0072 :=
    @gSyl
      (synWa (.objEq x y) (synWa
          (synWa (.classMem (.cv b) (synCplc (.cv n) (synC1c))) (.neg (.objMem y b))) (synWa
            (.classEq (synCun (.cv a) (synCsn (.cv x))) (synCun (.cv b) (synCsn (.cv y))))
            (.neg (.objMem x a)))))
      (.neg (.objMem y b))
      (.classEq (synCdif (synCun (.cv b) (synCsn (.cv y))) (synCsn (.cv y))) (.cv b))
      p0070 p0072_e01_recanon
  have p0073 :=
    @gN3eqtr3d
      (synWa (.objEq x y) (synWa
          (synWa (.classMem (.cv b) (synCplc (.cv n) (synC1c))) (.neg (.objMem y b))) (synWa
            (.classEq (synCun (.cv a) (synCsn (.cv x))) (synCun (.cv b) (synCsn (.cv y))))
            (.neg (.objMem x a)))))
      (synCdif (synCun (.cv a) (synCsn (.cv x))) (synCsn (.cv x)))
      (synCdif (synCun (.cv b) (synCsn (.cv y))) (synCsn (.cv y))) (.cv a) (.cv b)
      p0066 p0069 p0072
  have p0074 :=
    @gSimprll (.objEq x y) (.classMem (.cv b) (synCplc (.cv n) (synC1c)))
      (.neg (.objMem y b))
      (synWa (.classEq (synCun (.cv a) (synCsn (.cv x))) (synCun (.cv b) (synCsn (.cv y))))
        (.neg (.objMem x a)))
  have p0075 :=
    @gEqeltrd
      (synWa (.objEq x y) (synWa
          (synWa (.classMem (.cv b) (synCplc (.cv n) (synC1c))) (.neg (.objMem y b))) (synWa
            (.classEq (synCun (.cv a) (synCsn (.cv x))) (synCun (.cv b) (synCsn (.cv y))))
            (.neg (.objMem x a)))))
      (.cv a) (.cv b) (synCplc (.cv n) (synC1c)) p0073 p0074
  have p0076 :=
    @gN3adantr1 (.objEq x y)
      (synWa (.classMem (.cv b) (synCplc (.cv n) (synC1c))) (.neg (.objMem y b)))
      (synWa (.classEq (synCun (.cv a) (synCsn (.cv x))) (synCun (.cv b) (synCsn (.cv y))))
        (.neg (.objMem x a)))
      (.classMem (.cv a) (synCplc (.cv n) (synC1c)))
      (.all c (.all z (.imp (synWa (.neg (.objMem z c))
              (.classMem (synCun (.cv c) (synCsn (.cv z))) (synCplc (.cv n) (synC1c))))
            (.objMem c n))))
      p0075
  have p0077 :=
    @gEx (.objEq x y)
      (synW3a (.all c (.all z (.imp (synWa (.neg (.objMem z c))
                (.classMem (synCun (.cv c) (synCsn (.cv z))) (synCplc (.cv n) (synC1c))))
              (.objMem c n))))
        (synWa (.classMem (.cv b) (synCplc (.cv n) (synC1c))) (.neg (.objMem y b))) (synWa
          (.classEq (synCun (.cv a) (synCsn (.cv x))) (synCun (.cv b) (synCsn (.cv y))))
          (.neg (.objMem x a))))
      (.classMem (.cv a) (synCplc (.cv n) (synC1c))) p0076
  have p0078 :=
    @gSimpl (synWne (.cv x) (.cv y))
      (synW3a (.all c (.all z (.imp (synWa (.neg (.objMem z c))
                (.classMem (synCun (.cv c) (synCsn (.cv z))) (synCplc (.cv n) (synC1c))))
              (.objMem c n))))
        (synWa (.classMem (.cv b) (synCplc (.cv n) (synC1c))) (.neg (.objMem y b))) (synWa
          (.classEq (synCun (.cv a) (synCsn (.cv x))) (synCun (.cv b) (synCsn (.cv y))))
          (.neg (.objMem x a))))
  have p0079 :=
    @gSimpr3l
      (.classEq (synCun (.cv a) (synCsn (.cv x))) (synCun (.cv b) (synCsn (.cv y))))
      (.neg (.objMem x a))
      (.all c (.all z (.imp (synWa (.neg (.objMem z c))
              (.classMem (synCun (.cv c) (synCsn (.cv z))) (synCplc (.cv n) (synC1c))))
            (.objMem c n))))
      (synWa (.classMem (.cv b) (synCplc (.cv n) (synC1c))) (.neg (.objMem y b)))
      (synWne (.cv x) (.cv y))
  have p0080 :=
    @gSimpr2r (.classMem (.cv b) (synCplc (.cv n) (synC1c))) (.neg (.objMem y b))
      (.all c (.all z (.imp (synWa (.neg (.objMem z c))
              (.classMem (synCun (.cv c) (synCsn (.cv z))) (synCplc (.cv n) (synC1c))))
            (.objMem c n))))
      (synWa (.classEq (synCun (.cv a) (synCsn (.cv x))) (synCun (.cv b) (synCsn (.cv y))))
        (.neg (.objMem x a)))
      (synWne (.cv x) (.cv y))
  have p0081 := @gNnsucelrlem3 (.cv a) (.cv b) (.cv x) (.cv y) p0048
  have p0082_e03_recanon :
    Nominal.NPrf
      (.imp (synW3a (synWne (.cv x) (.cv y)) (.classEq (synCun (.cv a) (synCsn (.cv x)))
            (synCun (.cv b) (synCsn (.cv y)))) (.neg (.objMem y b))) (.classEq (.cv b)
          (synCun (synCdif (.cv a) (synCsn (.cv y))) (synCsn (.cv x))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synW3a synWa synWne synCun synCnin synWnan synCcompl synCsn
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
    @gSyl3anc
      (synWa (synWne (.cv x) (.cv y)) (synW3a (.all c (.all z (.imp
                (synWa (.neg (.objMem z c)) (.classMem (synCun (.cv c) (synCsn (.cv z)))
                    (synCplc (.cv n) (synC1c)))) (.objMem c n))))
          (synWa (.classMem (.cv b) (synCplc (.cv n) (synC1c))) (.neg (.objMem y b))) (synWa
            (.classEq (synCun (.cv a) (synCsn (.cv x))) (synCun (.cv b) (synCsn (.cv y))))
            (.neg (.objMem x a)))))
      (synWne (.cv x) (.cv y))
      (.classEq (synCun (.cv a) (synCsn (.cv x))) (synCun (.cv b) (synCsn (.cv y))))
      (.neg (.objMem y b))
      (.classEq (.cv b) (synCun (synCdif (.cv a) (synCsn (.cv y))) (synCsn (.cv x))))
      p0078 p0079 p0080 p0082_e03_recanon
  have p0083 :=
    @gSimp22r (.classMem (.cv b) (synCplc (.cv n) (synC1c))) (.neg (.objMem y b))
      (.all c (.all z (.imp (synWa (.neg (.objMem z c))
              (.classMem (synCun (.cv c) (synCsn (.cv z))) (synCplc (.cv n) (synC1c))))
            (.objMem c n))))
      (synWa (.classEq (synCun (.cv a) (synCsn (.cv x))) (synCun (.cv b) (synCsn (.cv y))))
        (.neg (.objMem x a)))
      (synWne (.cv x) (.cv y))
      (.classEq (.cv b) (synCun (synCdif (.cv a) (synCsn (.cv y))) (synCsn (.cv x))))
  have p0084 := @gDifsn (.cv y) (.cv a)
  have p0085_e00_recanon :
    Nominal.NPrf
      (.imp (.neg (.objMem y a)) (.classEq (synCdif (.cv a) (synCsn (.cv y))) (.cv a))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synCdif synCin synCcompl synCnin synWnan synWa synCsn
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0084
  have p0085 :=
    @gUneq1d (.neg (.objMem y a)) (synCdif (.cv a) (synCsn (.cv y))) (.cv a)
      (synCsn (.cv x)) p0085_e00_recanon
  have p0086 :=
    @gEqeq2d (.neg (.objMem y a))
      (synCun (synCdif (.cv a) (synCsn (.cv y))) (synCsn (.cv x)))
      (synCun (.cv a) (synCsn (.cv x))) (.cv b) p0085
  have p0087 :=
    @gBiimpcd (.neg (.objMem y a))
      (.classEq (.cv b) (synCun (synCdif (.cv a) (synCsn (.cv y))) (synCsn (.cv x))))
      (.classEq (.cv b) (synCun (.cv a) (synCsn (.cv x)))) p0086
  have p0088 :=
    @gN3ad2ant3
      (.classEq (.cv b) (synCun (synCdif (.cv a) (synCsn (.cv y))) (synCsn (.cv x))))
      (synWne (.cv x) (.cv y))
      (.imp (.neg (.objMem y a)) (.classEq (.cv b) (synCun (.cv a) (synCsn (.cv x)))))
      (synW3a (.all c (.all z (.imp (synWa (.neg (.objMem z c))
                (.classMem (synCun (.cv c) (synCsn (.cv z))) (synCplc (.cv n) (synC1c))))
              (.objMem c n))))
        (synWa (.classMem (.cv b) (synCplc (.cv n) (synC1c))) (.neg (.objMem y b))) (synWa
          (.classEq (synCun (.cv a) (synCsn (.cv x))) (synCun (.cv b) (synCsn (.cv y))))
          (.neg (.objMem x a))))
      p0087
  have p0089 :=
    @gSimp23l
      (.classEq (synCun (.cv a) (synCsn (.cv x))) (synCun (.cv b) (synCsn (.cv y))))
      (.neg (.objMem x a))
      (.all c (.all z (.imp (synWa (.neg (.objMem z c))
              (.classMem (synCun (.cv c) (synCsn (.cv z))) (synCplc (.cv n) (synC1c))))
            (.objMem c n))))
      (synWa (.classMem (.cv b) (synCplc (.cv n) (synC1c))) (.neg (.objMem y b)))
      (synWne (.cv x) (.cv y))
      (.classEq (.cv b) (synCun (synCdif (.cv a) (synCsn (.cv y))) (synCsn (.cv x))))
  have p0090 :=
    @gEqeq2d
      (synW3a (synWne (.cv x) (.cv y)) (synW3a (.all c (.all z (.imp
                (synWa (.neg (.objMem z c)) (.classMem (synCun (.cv c) (synCsn (.cv z)))
                    (synCplc (.cv n) (synC1c)))) (.objMem c n))))
          (synWa (.classMem (.cv b) (synCplc (.cv n) (synC1c))) (.neg (.objMem y b))) (synWa
            (.classEq (synCun (.cv a) (synCsn (.cv x))) (synCun (.cv b) (synCsn (.cv y))))
            (.neg (.objMem x a)))) (.classEq (.cv b)
          (synCun (synCdif (.cv a) (synCsn (.cv y))) (synCsn (.cv x)))))
      (synCun (.cv a) (synCsn (.cv x))) (synCun (.cv b) (synCsn (.cv y))) (.cv b)
      p0089
  have p0091 := @gSnss (.cv y) (.cv b) p0060
  have p0092 := @gSsequn2 (synCsn (.cv y)) (.cv b)
  have p0093_e00_recanon :
    Nominal.NPrf (synWb (.objMem y b) (synWss (synCsn (.cv y)) (.cv b))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWss synCin synCcompl synCnin synWnan synWa synCsn
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
    @gBitr2i (.objMem y b) (synWss (synCsn (.cv y)) (.cv b))
      (.classEq (synCun (.cv b) (synCsn (.cv y))) (.cv b)) p0093_e00_recanon p0092
  have p0094 :=
    @gBiimpi (.classEq (synCun (.cv b) (synCsn (.cv y))) (.cv b)) (.objMem y b) p0093
  have p0095 := @gEqcoms (.objMem y b) (synCun (.cv b) (synCsn (.cv y))) (.cv b) p0094
  have p0096 :=
    @gSyl6bi
      (synW3a (synWne (.cv x) (.cv y)) (synW3a (.all c (.all z (.imp
                (synWa (.neg (.objMem z c)) (.classMem (synCun (.cv c) (synCsn (.cv z)))
                    (synCplc (.cv n) (synC1c)))) (.objMem c n))))
          (synWa (.classMem (.cv b) (synCplc (.cv n) (synC1c))) (.neg (.objMem y b))) (synWa
            (.classEq (synCun (.cv a) (synCsn (.cv x))) (synCun (.cv b) (synCsn (.cv y))))
            (.neg (.objMem x a)))) (.classEq (.cv b)
          (synCun (synCdif (.cv a) (synCsn (.cv y))) (synCsn (.cv x)))))
      (.classEq (.cv b) (synCun (.cv a) (synCsn (.cv x))))
      (.classEq (.cv b) (synCun (.cv b) (synCsn (.cv y)))) (.objMem y b) p0090 p0095
  have p0097 :=
    @gSyld
      (synW3a (synWne (.cv x) (.cv y)) (synW3a (.all c (.all z (.imp
                (synWa (.neg (.objMem z c)) (.classMem (synCun (.cv c) (synCsn (.cv z)))
                    (synCplc (.cv n) (synC1c)))) (.objMem c n))))
          (synWa (.classMem (.cv b) (synCplc (.cv n) (synC1c))) (.neg (.objMem y b))) (synWa
            (.classEq (synCun (.cv a) (synCsn (.cv x))) (synCun (.cv b) (synCsn (.cv y))))
            (.neg (.objMem x a)))) (.classEq (.cv b)
          (synCun (synCdif (.cv a) (synCsn (.cv y))) (synCsn (.cv x)))))
      (.neg (.objMem y a)) (.classEq (.cv b) (synCun (.cv a) (synCsn (.cv x))))
      (.objMem y b) p0088 p0096
  have p0098 :=
    @gMt3d
      (synW3a (synWne (.cv x) (.cv y)) (synW3a (.all c (.all z (.imp
                (synWa (.neg (.objMem z c)) (.classMem (synCun (.cv c) (synCsn (.cv z)))
                    (synCplc (.cv n) (synC1c)))) (.objMem c n))))
          (synWa (.classMem (.cv b) (synCplc (.cv n) (synC1c))) (.neg (.objMem y b))) (synWa
            (.classEq (synCun (.cv a) (synCsn (.cv x))) (synCun (.cv b) (synCsn (.cv y))))
            (.neg (.objMem x a)))) (.classEq (.cv b)
          (synCun (synCdif (.cv a) (synCsn (.cv y))) (synCsn (.cv x)))))
      (.objMem y a) (.objMem y b) p0083 p0097
  have p0099 := @gNnsucelrlem4 (.cv y) (.cv a)
  have p0100_e01_recanon :
    Nominal.NPrf
      (.imp (.objMem y a)
        (.classEq (synCun (synCdif (.cv a) (synCsn (.cv y))) (synCsn (.cv y))) (.cv a))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synCun synCnin synWnan synWa synCcompl synCdif synCin synCsn
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0099
  have p0100 :=
    @gSyl
      (synW3a (synWne (.cv x) (.cv y)) (synW3a (.all c (.all z (.imp
                (synWa (.neg (.objMem z c)) (.classMem (synCun (.cv c) (synCsn (.cv z)))
                    (synCplc (.cv n) (synC1c)))) (.objMem c n))))
          (synWa (.classMem (.cv b) (synCplc (.cv n) (synC1c))) (.neg (.objMem y b))) (synWa
            (.classEq (synCun (.cv a) (synCsn (.cv x))) (synCun (.cv b) (synCsn (.cv y))))
            (.neg (.objMem x a)))) (.classEq (.cv b)
          (synCun (synCdif (.cv a) (synCsn (.cv y))) (synCsn (.cv x)))))
      (.objMem y a)
      (.classEq (synCun (synCdif (.cv a) (synCsn (.cv y))) (synCsn (.cv y))) (.cv a))
      p0098 p0100_e01_recanon
  have p0101 :=
    @gSimpl3r
      (.classEq (synCun (.cv a) (synCsn (.cv x))) (synCun (.cv b) (synCsn (.cv y))))
      (.neg (.objMem x a))
      (.all c (.all z (.imp (synWa (.neg (.objMem z c))
              (.classMem (synCun (.cv c) (synCsn (.cv z))) (synCplc (.cv n) (synC1c))))
            (.objMem c n))))
      (synWa (.classMem (.cv b) (synCplc (.cv n) (synC1c))) (.neg (.objMem y b)))
      (.classEq (.cv b) (synCun (synCdif (.cv a) (synCsn (.cv y))) (synCsn (.cv x))))
  have p0102 := @gDifss (.cv a) (synCsn (.cv y))
  have p0103 := @gSseli (synCdif (.cv a) (synCsn (.cv y))) (.cv a) (.cv x) p0102
  have p0104_e01_recanon :
    Nominal.NPrf
      (.imp (.classMem (.cv x) (synCdif (.cv a) (synCsn (.cv y)))) (.objMem x a)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synCdif synCin synCcompl synCnin synWnan synWa synCsn
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _)
      p0103
  have p0104 :=
    @gNsyl
      (synWa (synW3a (.all c (.all z (.imp (synWa (.neg (.objMem z c))
                  (.classMem (synCun (.cv c) (synCsn (.cv z))) (synCplc (.cv n) (synC1c))))
                (.objMem c n))))
          (synWa (.classMem (.cv b) (synCplc (.cv n) (synC1c))) (.neg (.objMem y b))) (synWa
            (.classEq (synCun (.cv a) (synCsn (.cv x))) (synCun (.cv b) (synCsn (.cv y))))
            (.neg (.objMem x a)))) (.classEq (.cv b)
          (synCun (synCdif (.cv a) (synCsn (.cv y))) (synCsn (.cv x)))))
      (.objMem x a) (.classMem (.cv x) (synCdif (.cv a) (synCsn (.cv y)))) p0101
      p0104_e01_recanon
  have p0105 :=
    @gSimp2l
      (.all c (.all z (.imp (synWa (.neg (.objMem z c))
              (.classMem (synCun (.cv c) (synCsn (.cv z))) (synCplc (.cv n) (synC1c))))
            (.objMem c n))))
      (.classMem (.cv b) (synCplc (.cv n) (synC1c))) (.neg (.objMem y b))
      (synWa (.classEq (synCun (.cv a) (synCsn (.cv x))) (synCun (.cv b) (synCsn (.cv y))))
        (.neg (.objMem x a)))
  have p0106 :=
    @gEleq1 (.cv b) (synCun (synCdif (.cv a) (synCsn (.cv y))) (synCsn (.cv x)))
      (synCplc (.cv n) (synC1c))
  have p0107 :=
    @gBiimpd
      (.classEq (.cv b) (synCun (synCdif (.cv a) (synCsn (.cv y))) (synCsn (.cv x))))
      (.classMem (.cv b) (synCplc (.cv n) (synC1c)))
      (.classMem (synCun (synCdif (.cv a) (synCsn (.cv y))) (synCsn (.cv x)))
        (synCplc (.cv n) (synC1c)))
      p0106
  have p0108 :=
    @gMpan9
      (synW3a (.all c (.all z (.imp (synWa (.neg (.objMem z c))
                (.classMem (synCun (.cv c) (synCsn (.cv z))) (synCplc (.cv n) (synC1c))))
              (.objMem c n))))
        (synWa (.classMem (.cv b) (synCplc (.cv n) (synC1c))) (.neg (.objMem y b))) (synWa
          (.classEq (synCun (.cv a) (synCsn (.cv x))) (synCun (.cv b) (synCsn (.cv y))))
          (.neg (.objMem x a))))
      (.classMem (.cv b) (synCplc (.cv n) (synC1c)))
      (.classEq (.cv b) (synCun (synCdif (.cv a) (synCsn (.cv y))) (synCsn (.cv x))))
      (.classMem (synCun (synCdif (.cv a) (synCsn (.cv y))) (synCsn (.cv x)))
        (synCplc (.cv n) (synC1c)))
      p0105 p0107
  have p0109 :=
    @gSimpl1
      (.all c (.all z (.imp (synWa (.neg (.objMem z c))
              (.classMem (synCun (.cv c) (synCsn (.cv z))) (synCplc (.cv n) (synC1c))))
            (.objMem c n))))
      (synWa (.classMem (.cv b) (synCplc (.cv n) (synC1c))) (.neg (.objMem y b)))
      (synWa (.classEq (synCun (.cv a) (synCsn (.cv x))) (synCun (.cv b) (synCsn (.cv y))))
        (.neg (.objMem x a)))
      (.classEq (.cv b) (synCun (synCdif (.cv a) (synCsn (.cv y))) (synCsn (.cv x))))
  have p0110 := @gSnex (.cv y)
  have p0111 := @gDifex (.cv a) (synCsn (.cv y)) p0011 p0110
  have p0112 := @gEleq12 (.cv z) (.cv x) (.cv c) (synCdif (.cv a) (synCsn (.cv y)))
  have p0113_e00_recanon :
    Nominal.NPrf
      (.imp (synWa (.objEq z x) (.classEq (.cv c) (synCdif (.cv a) (synCsn (.cv y)))))
        (synWb (.objMem z c) (.classMem (.cv x) (synCdif (.cv a) (synCsn (.cv y)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWa synCdif synCin synCcompl synCnin synWnan synCsn synWb
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
    @gAncoms (.objEq z x) (.classEq (.cv c) (synCdif (.cv a) (synCsn (.cv y))))
      (synWb (.objMem z c) (.classMem (.cv x) (synCdif (.cv a) (synCsn (.cv y)))))
      p0113_e00_recanon
  have p0114 :=
    @gNotbid
      (synWa (.classEq (.cv c) (synCdif (.cv a) (synCsn (.cv y)))) (.objEq z x))
      (.objMem z c) (.classMem (.cv x) (synCdif (.cv a) (synCsn (.cv y)))) p0113
  have p0115 := @gSneq (.cv z) (.cv x)
  have p0116 :=
    @gUneq12 (.cv c) (synCdif (.cv a) (synCsn (.cv y))) (synCsn (.cv z))
      (synCsn (.cv x))
  have p0117_e00_recanon :
    Nominal.NPrf (.imp (.objEq z x) (.classEq (synCsn (.cv z)) (synCsn (.cv x)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synCsn
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0115
  have p0117 :=
    @gSylan2 (.objEq z x) (.classEq (.cv c) (synCdif (.cv a) (synCsn (.cv y))))
      (.classEq (synCsn (.cv z)) (synCsn (.cv x)))
      (.classEq (synCun (.cv c) (synCsn (.cv z)))
        (synCun (synCdif (.cv a) (synCsn (.cv y))) (synCsn (.cv x))))
      p0117_e00_recanon p0116
  have p0118 :=
    @gEleq1d
      (synWa (.classEq (.cv c) (synCdif (.cv a) (synCsn (.cv y)))) (.objEq z x))
      (synCun (.cv c) (synCsn (.cv z)))
      (synCun (synCdif (.cv a) (synCsn (.cv y))) (synCsn (.cv x)))
      (synCplc (.cv n) (synC1c)) p0117
  have p0119 :=
    @gAnbi12d
      (synWa (.classEq (.cv c) (synCdif (.cv a) (synCsn (.cv y)))) (.objEq z x))
      (.neg (.objMem z c)) (.neg (.classMem (.cv x) (synCdif (.cv a) (synCsn (.cv y)))))
      (.classMem (synCun (.cv c) (synCsn (.cv z))) (synCplc (.cv n) (synC1c)))
      (.classMem (synCun (synCdif (.cv a) (synCsn (.cv y))) (synCsn (.cv x)))
        (synCplc (.cv n) (synC1c)))
      p0114 p0118
  have p0120 := @gEleq1 (.cv c) (synCdif (.cv a) (synCsn (.cv y))) (.cv n)
  have p0121_e00_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv c) (synCdif (.cv a) (synCsn (.cv y)))) (synWb (.objMem c n)
          (.classMem (synCdif (.cv a) (synCsn (.cv y))) (.cv n)))) :=
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
      p0120
  have p0121 :=
    @gAdantr (.classEq (.cv c) (synCdif (.cv a) (synCsn (.cv y))))
      (synWb (.objMem c n) (.classMem (synCdif (.cv a) (synCsn (.cv y))) (.cv n)))
      (.objEq z x) p0121_e00_recanon
  have p0122 :=
    @gImbi12d
      (synWa (.classEq (.cv c) (synCdif (.cv a) (synCsn (.cv y)))) (.objEq z x))
      (synWa (.neg (.objMem z c))
        (.classMem (synCun (.cv c) (synCsn (.cv z))) (synCplc (.cv n) (synC1c))))
      (synWa (.neg (.classMem (.cv x) (synCdif (.cv a) (synCsn (.cv y)))))
        (.classMem (synCun (synCdif (.cv a) (synCsn (.cv y))) (synCsn (.cv x)))
          (synCplc (.cv n) (synC1c))))
      (.objMem c n) (.classMem (synCdif (.cv a) (synCsn (.cv y))) (.cv n)) p0119 p0121
  have p0123_e00_recanon :
    Nominal.NPrf
      (.imp (synWa (.classEq (.cv c) (synCdif (.cv a) (synCsn (.cv y))))
          (.classEq (.cv z) (.cv x))) (synWb (.imp (synWa (.neg (.objMem z c))
              (.classMem (synCun (.cv c) (synCsn (.cv z))) (synCplc (.cv n) (synC1c))))
            (.objMem c n)) (.imp
            (synWa (.neg (.classMem (.cv x) (synCdif (.cv a) (synCsn (.cv y)))))
              (.classMem (synCun (synCdif (.cv a) (synCsn (.cv y))) (synCsn (.cv x)))
                (synCplc (.cv n) (synC1c))))
            (.classMem (synCdif (.cv a) (synCsn (.cv y))) (.cv n))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWa synCdif synCin synCcompl synCnin synWnan synCsn synWb
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
  have freeVariableCertificate16 : c ∉ ((synCdif (.cv a) (synCsn (.cv y)))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
      Finset.mem_singleton, fresh_c_ne_a, fresh_c_ne_y, or_false, not_false_eq_true]
  have freeVariableCertificate17 : z ∉ ((synCdif (.cv a) (synCsn (.cv y)))).fv := by
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
      ((Wff.imp (synWa (.neg (.classMem (.cv x) (synCdif (.cv a) (synCsn (.cv y)))))
            (.classMem (synCun (synCdif (.cv a) (synCsn (.cv y))) (synCsn (.cv x)))
              (synCplc (.cv n) (synC1c))))
          (.classMem (synCdif (.cv a) (synCsn (.cv y))) (.cv n)))).fv :=
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
      ((Wff.imp (synWa (.neg (.classMem (.cv x) (synCdif (.cv a) (synCsn (.cv y)))))
            (.classMem (synCun (synCdif (.cv a) (synCsn (.cv y))) (synCsn (.cv x)))
              (synCplc (.cv n) (synC1c))))
          (.classMem (synCdif (.cv a) (synCsn (.cv y))) (.cv n)))).fv :=
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
    @gSpc2gv
      (.imp (synWa (.neg (.objMem z c))
          (.classMem (synCun (.cv c) (synCsn (.cv z))) (synCplc (.cv n) (synC1c))))
        (.objMem c n))
      (.imp (synWa (.neg (.classMem (.cv x) (synCdif (.cv a) (synCsn (.cv y)))))
          (.classMem (synCun (synCdif (.cv a) (synCsn (.cv y))) (synCsn (.cv x)))
            (synCplc (.cv n) (synC1c))))
        (.classMem (synCdif (.cv a) (synCsn (.cv y))) (.cv n)))
      c z (synCdif (.cv a) (synCsn (.cv y))) (.cv x) (synCvv) (synCvv)
      freeVariableCertificate16 freeVariableCertificate17 freeVariableCertificate18
      freeVariableCertificate19 freeVariableCertificate20 freeVariableCertificate21
      (show c ≠ z from (by exact fresh_c_ne_z)) p0123_e00_recanon
  have p0124 :=
    @gMp2an (.classMem (synCdif (.cv a) (synCsn (.cv y))) (synCvv))
      (.classMem (.cv x) (synCvv))
      (.imp (.all c (.all z (.imp (synWa (.neg (.objMem z c))
                (.classMem (synCun (.cv c) (synCsn (.cv z))) (synCplc (.cv n) (synC1c))))
              (.objMem c n)))) (.imp
          (synWa (.neg (.classMem (.cv x) (synCdif (.cv a) (synCsn (.cv y)))))
            (.classMem (synCun (synCdif (.cv a) (synCsn (.cv y))) (synCsn (.cv x)))
              (synCplc (.cv n) (synC1c))))
          (.classMem (synCdif (.cv a) (synCsn (.cv y))) (.cv n))))
      p0111 p0048 p0123
  have p0125 :=
    @gSyl
      (synWa (synW3a (.all c (.all z (.imp (synWa (.neg (.objMem z c))
                  (.classMem (synCun (.cv c) (synCsn (.cv z))) (synCplc (.cv n) (synC1c))))
                (.objMem c n))))
          (synWa (.classMem (.cv b) (synCplc (.cv n) (synC1c))) (.neg (.objMem y b))) (synWa
            (.classEq (synCun (.cv a) (synCsn (.cv x))) (synCun (.cv b) (synCsn (.cv y))))
            (.neg (.objMem x a)))) (.classEq (.cv b)
          (synCun (synCdif (.cv a) (synCsn (.cv y))) (synCsn (.cv x)))))
      (.all c (.all z (.imp (synWa (.neg (.objMem z c))
              (.classMem (synCun (.cv c) (synCsn (.cv z))) (synCplc (.cv n) (synC1c))))
            (.objMem c n))))
      (.imp (synWa (.neg (.classMem (.cv x) (synCdif (.cv a) (synCsn (.cv y)))))
          (.classMem (synCun (synCdif (.cv a) (synCsn (.cv y))) (synCsn (.cv x)))
            (synCplc (.cv n) (synC1c))))
        (.classMem (synCdif (.cv a) (synCsn (.cv y))) (.cv n)))
      p0109 p0124
  have p0126 :=
    @gMp2and
      (synWa (synW3a (.all c (.all z (.imp (synWa (.neg (.objMem z c))
                  (.classMem (synCun (.cv c) (synCsn (.cv z))) (synCplc (.cv n) (synC1c))))
                (.objMem c n))))
          (synWa (.classMem (.cv b) (synCplc (.cv n) (synC1c))) (.neg (.objMem y b))) (synWa
            (.classEq (synCun (.cv a) (synCsn (.cv x))) (synCun (.cv b) (synCsn (.cv y))))
            (.neg (.objMem x a)))) (.classEq (.cv b)
          (synCun (synCdif (.cv a) (synCsn (.cv y))) (synCsn (.cv x)))))
      (.neg (.classMem (.cv x) (synCdif (.cv a) (synCsn (.cv y)))))
      (.classMem (synCun (synCdif (.cv a) (synCsn (.cv y))) (synCsn (.cv x)))
        (synCplc (.cv n) (synC1c)))
      (.classMem (synCdif (.cv a) (synCsn (.cv y))) (.cv n)) p0104 p0108 p0125
  have p0127 :=
    @gN3adant1
      (synW3a (.all c (.all z (.imp (synWa (.neg (.objMem z c))
                (.classMem (synCun (.cv c) (synCsn (.cv z))) (synCplc (.cv n) (synC1c))))
              (.objMem c n))))
        (synWa (.classMem (.cv b) (synCplc (.cv n) (synC1c))) (.neg (.objMem y b))) (synWa
          (.classEq (synCun (.cv a) (synCsn (.cv x))) (synCun (.cv b) (synCsn (.cv y))))
          (.neg (.objMem x a))))
      (.classEq (.cv b) (synCun (synCdif (.cv a) (synCsn (.cv y))) (synCsn (.cv x))))
      (.classMem (synCdif (.cv a) (synCsn (.cv y))) (.cv n)) (synWne (.cv x) (.cv y))
      p0126
  have p0128 := @gSnid (.cv y) p0060
  have p0129 := @gEldif (.cv y) (.cv a) (synCsn (.cv y))
  have p0130_e00_recanon :
    Nominal.NPrf
      (synWb (.classMem (.cv y) (synCdif (.cv a) (synCsn (.cv y))))
        (synWa (.objMem y a) (.neg (.classMem (.cv y) (synCsn (.cv y)))))) :=
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
      p0129
  have p0130 :=
    @gSimprbi (.classMem (.cv y) (synCdif (.cv a) (synCsn (.cv y)))) (.objMem y a)
      (.neg (.classMem (.cv y) (synCsn (.cv y)))) p0130_e00_recanon
  have p0131 :=
    @gMt2 (.classMem (.cv y) (synCdif (.cv a) (synCsn (.cv y))))
      (.classMem (.cv y) (synCsn (.cv y))) p0128 p0130
  have p0132 := @gElcompl (.cv y) (synCdif (.cv a) (synCsn (.cv y))) p0060
  have p0133 :=
    @gMpbir (.classMem (.cv y) (synCcompl (synCdif (.cv a) (synCsn (.cv y)))))
      (.neg (.classMem (.cv y) (synCdif (.cv a) (synCsn (.cv y))))) p0131 p0132
  have p0134 := @gEqid (synCun (synCdif (.cv a) (synCsn (.cv y))) (synCsn (.cv y)))
  have p0135 := @gSneq (.cv w) (.cv y)
  have p0136_e00_recanon :
    Nominal.NPrf (.imp (.objEq w y) (.classEq (synCsn (.cv w)) (synCsn (.cv y)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synCsn
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0135
  have p0136 :=
    @gUneq2d (.objEq w y) (synCsn (.cv w)) (synCsn (.cv y))
      (synCdif (.cv a) (synCsn (.cv y))) p0136_e00_recanon
  have p0137 :=
    @gEqeq2d (.objEq w y)
      (synCun (synCdif (.cv a) (synCsn (.cv y))) (synCsn (.cv w)))
      (synCun (synCdif (.cv a) (synCsn (.cv y))) (synCsn (.cv y)))
      (synCun (synCdif (.cv a) (synCsn (.cv y))) (synCsn (.cv y))) p0136
  have p0138_e00_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv w) (.cv y)) (synWb
          (.classEq (synCun (synCdif (.cv a) (synCsn (.cv y))) (synCsn (.cv y)))
            (synCun (synCdif (.cv a) (synCsn (.cv y))) (synCsn (.cv w))))
          (.classEq (synCun (synCdif (.cv a) (synCsn (.cv y))) (synCsn (.cv y)))
            (synCun (synCdif (.cv a) (synCsn (.cv y))) (synCsn (.cv y)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCun synCnin synWnan synWa synCcompl synCdif synCin synCsn
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
    w ∉ ((synCcompl (synCdif (.cv a) (synCsn (.cv y))))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
      Finset.mem_singleton, fresh_w_ne_a, fresh_w_ne_y, or_false, not_false_eq_true]
  have freeVariableCertificate24 :
    w ∉
      ((Wff.classEq (synCun (synCdif (.cv a) (synCsn (.cv y))) (synCsn (.cv y)))
          (synCun (synCdif (.cv a) (synCsn (.cv y))) (synCsn (.cv y))))).fv :=
    by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
      Finset.mem_singleton, fresh_w_ne_a, fresh_w_ne_y, or_false, not_false_eq_true]
  have p0138 :=
    @gRspcev
      (.classEq (synCun (synCdif (.cv a) (synCsn (.cv y))) (synCsn (.cv y)))
        (synCun (synCdif (.cv a) (synCsn (.cv y))) (synCsn (.cv w))))
      (.classEq (synCun (synCdif (.cv a) (synCsn (.cv y))) (synCsn (.cv y)))
        (synCun (synCdif (.cv a) (synCsn (.cv y))) (synCsn (.cv y))))
      w (.cv y) (synCcompl (synCdif (.cv a) (synCsn (.cv y))))
      freeVariableCertificate22 freeVariableCertificate23 freeVariableCertificate24
      p0138_e00_recanon
  have p0139 :=
    @gMp2an (.classMem (.cv y) (synCcompl (synCdif (.cv a) (synCsn (.cv y)))))
      (.classEq (synCun (synCdif (.cv a) (synCsn (.cv y))) (synCsn (.cv y)))
        (synCun (synCdif (.cv a) (synCsn (.cv y))) (synCsn (.cv y))))
      (synWrex w (synCcompl (synCdif (.cv a) (synCsn (.cv y))))
        (.classEq (synCun (synCdif (.cv a) (synCsn (.cv y))) (synCsn (.cv y)))
          (synCun (synCdif (.cv a) (synCsn (.cv y))) (synCsn (.cv w)))))
      p0133 p0134 p0138
  have p0140 := @gCompleq (.cv d) (synCdif (.cv a) (synCsn (.cv y)))
  have p0141 := @gUneq1 (.cv d) (synCdif (.cv a) (synCsn (.cv y))) (synCsn (.cv w))
  have p0142 :=
    @gEqeq2d (.classEq (.cv d) (synCdif (.cv a) (synCsn (.cv y))))
      (synCun (.cv d) (synCsn (.cv w)))
      (synCun (synCdif (.cv a) (synCsn (.cv y))) (synCsn (.cv w)))
      (synCun (synCdif (.cv a) (synCsn (.cv y))) (synCsn (.cv y))) p0141
  have freeVariableCertificate25 : w ∉ ((synCcompl (.cv d))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_w_ne_d,
      not_false_eq_true]
  have freeVariableCertificate26 :
    w ∉ ((Wff.classEq (.cv d) (synCdif (.cv a) (synCsn (.cv y))))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
      Finset.mem_singleton, fresh_w_ne_d, fresh_w_ne_a, fresh_w_ne_y, or_false,
      not_false_eq_true]
  have p0143 :=
    @gRexeqbidv (.classEq (.cv d) (synCdif (.cv a) (synCsn (.cv y))))
      (.classEq (synCun (synCdif (.cv a) (synCsn (.cv y))) (synCsn (.cv y)))
        (synCun (.cv d) (synCsn (.cv w))))
      (.classEq (synCun (synCdif (.cv a) (synCsn (.cv y))) (synCsn (.cv y)))
        (synCun (synCdif (.cv a) (synCsn (.cv y))) (synCsn (.cv w))))
      w (synCcompl (.cv d)) (synCcompl (synCdif (.cv a) (synCsn (.cv y))))
      freeVariableCertificate25 freeVariableCertificate23 freeVariableCertificate26 p0140
      p0142
  have freeVariableCertificate27 : d ∉ ((synCdif (.cv a) (synCsn (.cv y)))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
      Finset.mem_singleton, fresh_d_ne_a, fresh_d_ne_y, or_false, not_false_eq_true]
  have freeVariableCertificate28 : d ∉ ((Class.cv n)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_d_ne_n, not_false_eq_true]
  have freeVariableCertificate29 :
    d ∉
      ((synWrex w (synCcompl (synCdif (.cv a) (synCsn (.cv y))))
          (.classEq (synCun (synCdif (.cv a) (synCsn (.cv y))) (synCsn (.cv y)))
            (synCun (synCdif (.cv a) (synCsn (.cv y))) (synCsn (.cv w)))))).fv :=
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
    @gRspcev
      (synWrex w (synCcompl (.cv d))
        (.classEq (synCun (synCdif (.cv a) (synCsn (.cv y))) (synCsn (.cv y)))
          (synCun (.cv d) (synCsn (.cv w)))))
      (synWrex w (synCcompl (synCdif (.cv a) (synCsn (.cv y))))
        (.classEq (synCun (synCdif (.cv a) (synCsn (.cv y))) (synCsn (.cv y)))
          (synCun (synCdif (.cv a) (synCsn (.cv y))) (synCsn (.cv w)))))
      d (synCdif (.cv a) (synCsn (.cv y))) (.cv n) freeVariableCertificate27
      freeVariableCertificate28 freeVariableCertificate29 p0143
  have freeVariableCertificate30 :
    d ∉ ((synCun (synCdif (.cv a) (synCsn (.cv y))) (synCsn (.cv y)))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
      Finset.mem_singleton, fresh_d_ne_a, fresh_d_ne_y, or_false, not_false_eq_true]
  have freeVariableCertificate31 :
    w ∉ ((synCun (synCdif (.cv a) (synCsn (.cv y))) (synCsn (.cv y)))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
      Finset.mem_singleton, fresh_w_ne_a, fresh_w_ne_y, or_false, not_false_eq_true]
  have p0145 :=
    @gElsuc w (synCun (synCdif (.cv a) (synCsn (.cv y))) (synCsn (.cv y))) (.cv n) d
      freeVariableCertificate30 freeVariableCertificate31 freeVariableCertificate28
      (show d ≠ w from (by exact fresh_d_ne_w))
  have p0146 :=
    @gSylibr
      (synWa (.classMem (synCdif (.cv a) (synCsn (.cv y))) (.cv n))
        (synWrex w (synCcompl (synCdif (.cv a) (synCsn (.cv y))))
          (.classEq (synCun (synCdif (.cv a) (synCsn (.cv y))) (synCsn (.cv y)))
            (synCun (synCdif (.cv a) (synCsn (.cv y))) (synCsn (.cv w))))))
      (synWrex d (.cv n) (synWrex w (synCcompl (.cv d))
          (.classEq (synCun (synCdif (.cv a) (synCsn (.cv y))) (synCsn (.cv y)))
            (synCun (.cv d) (synCsn (.cv w))))))
      (.classMem (synCun (synCdif (.cv a) (synCsn (.cv y))) (synCsn (.cv y)))
        (synCplc (.cv n) (synC1c)))
      p0144 p0145
  have p0147 :=
    @gSylancl
      (synW3a (synWne (.cv x) (.cv y)) (synW3a (.all c (.all z (.imp
                (synWa (.neg (.objMem z c)) (.classMem (synCun (.cv c) (synCsn (.cv z)))
                    (synCplc (.cv n) (synC1c)))) (.objMem c n))))
          (synWa (.classMem (.cv b) (synCplc (.cv n) (synC1c))) (.neg (.objMem y b))) (synWa
            (.classEq (synCun (.cv a) (synCsn (.cv x))) (synCun (.cv b) (synCsn (.cv y))))
            (.neg (.objMem x a)))) (.classEq (.cv b)
          (synCun (synCdif (.cv a) (synCsn (.cv y))) (synCsn (.cv x)))))
      (.classMem (synCdif (.cv a) (synCsn (.cv y))) (.cv n))
      (synWrex w (synCcompl (synCdif (.cv a) (synCsn (.cv y))))
        (.classEq (synCun (synCdif (.cv a) (synCsn (.cv y))) (synCsn (.cv y)))
          (synCun (synCdif (.cv a) (synCsn (.cv y))) (synCsn (.cv w)))))
      (.classMem (synCun (synCdif (.cv a) (synCsn (.cv y))) (synCsn (.cv y)))
        (synCplc (.cv n) (synC1c)))
      p0127 p0139 p0146
  have p0148 :=
    @gEqeltrrd
      (synW3a (synWne (.cv x) (.cv y)) (synW3a (.all c (.all z (.imp
                (synWa (.neg (.objMem z c)) (.classMem (synCun (.cv c) (synCsn (.cv z)))
                    (synCplc (.cv n) (synC1c)))) (.objMem c n))))
          (synWa (.classMem (.cv b) (synCplc (.cv n) (synC1c))) (.neg (.objMem y b))) (synWa
            (.classEq (synCun (.cv a) (synCsn (.cv x))) (synCun (.cv b) (synCsn (.cv y))))
            (.neg (.objMem x a)))) (.classEq (.cv b)
          (synCun (synCdif (.cv a) (synCsn (.cv y))) (synCsn (.cv x)))))
      (synCun (synCdif (.cv a) (synCsn (.cv y))) (synCsn (.cv y))) (.cv a)
      (synCplc (.cv n) (synC1c)) p0100 p0147
  have p0149 :=
    @gMpd3an3 (synWne (.cv x) (.cv y))
      (synW3a (.all c (.all z (.imp (synWa (.neg (.objMem z c))
                (.classMem (synCun (.cv c) (synCsn (.cv z))) (synCplc (.cv n) (synC1c))))
              (.objMem c n))))
        (synWa (.classMem (.cv b) (synCplc (.cv n) (synC1c))) (.neg (.objMem y b))) (synWa
          (.classEq (synCun (.cv a) (synCsn (.cv x))) (synCun (.cv b) (synCsn (.cv y))))
          (.neg (.objMem x a))))
      (.classEq (.cv b) (synCun (synCdif (.cv a) (synCsn (.cv y))) (synCsn (.cv x))))
      (.classMem (.cv a) (synCplc (.cv n) (synC1c))) p0082 p0148
  have p0150 :=
    @gEx (synWne (.cv x) (.cv y))
      (synW3a (.all c (.all z (.imp (synWa (.neg (.objMem z c))
                (.classMem (synCun (.cv c) (synCsn (.cv z))) (synCplc (.cv n) (synC1c))))
              (.objMem c n))))
        (synWa (.classMem (.cv b) (synCplc (.cv n) (synC1c))) (.neg (.objMem y b))) (synWa
          (.classEq (synCun (.cv a) (synCsn (.cv x))) (synCun (.cv b) (synCsn (.cv y))))
          (.neg (.objMem x a))))
      (.classMem (.cv a) (synCplc (.cv n) (synC1c))) p0149
  have p0151_e00_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv x) (.cv y)) (.imp (synW3a (.all c (.all z (.imp
                  (synWa (.neg (.objMem z c)) (.classMem (synCun (.cv c) (synCsn (.cv z)))
                      (synCplc (.cv n) (synC1c)))) (.objMem c n))))
            (synWa (.classMem (.cv b) (synCplc (.cv n) (synC1c))) (.neg (.objMem y b)))
            (synWa (.classEq (synCun (.cv a) (synCsn (.cv x)))
                (synCun (.cv b) (synCsn (.cv y)))) (.neg (.objMem x a))))
          (.classMem (.cv a) (synCplc (.cv n) (synC1c))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synW3a synWa synCplc synWrex synWex synC1c
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0077
  have p0151 :=
    @gPm261ine
      (.imp (synW3a (.all c (.all z (.imp (synWa (.neg (.objMem z c))
                  (.classMem (synCun (.cv c) (synCsn (.cv z))) (synCplc (.cv n) (synC1c))))
                (.objMem c n))))
          (synWa (.classMem (.cv b) (synCplc (.cv n) (synC1c))) (.neg (.objMem y b))) (synWa
            (.classEq (synCun (.cv a) (synCsn (.cv x))) (synCun (.cv b) (synCsn (.cv y))))
            (.neg (.objMem x a)))) (.classMem (.cv a) (synCplc (.cv n) (synC1c))))
      (.cv x) (.cv y) p0151_e00_recanon p0150
  have p0152 :=
    @gN3expa
      (.all c (.all z (.imp (synWa (.neg (.objMem z c))
              (.classMem (synCun (.cv c) (synCsn (.cv z))) (synCplc (.cv n) (synC1c))))
            (.objMem c n))))
      (synWa (.classMem (.cv b) (synCplc (.cv n) (synC1c))) (.neg (.objMem y b)))
      (synWa (.classEq (synCun (.cv a) (synCsn (.cv x))) (synCun (.cv b) (synCsn (.cv y))))
        (.neg (.objMem x a)))
      (.classMem (.cv a) (synCplc (.cv n) (synC1c))) p0151
  have p0153 :=
    @gExp32
      (synWa (.all c (.all z (.imp (synWa (.neg (.objMem z c))
                (.classMem (synCun (.cv c) (synCsn (.cv z))) (synCplc (.cv n) (synC1c))))
              (.objMem c n))))
        (synWa (.classMem (.cv b) (synCplc (.cv n) (synC1c))) (.neg (.objMem y b))))
      (.classEq (synCun (.cv a) (synCsn (.cv x))) (synCun (.cv b) (synCsn (.cv y))))
      (.neg (.objMem x a)) (.classMem (.cv a) (synCplc (.cv n) (synC1c))) p0152
  have p0154 :=
    @gSylan2b
      (synWa (.classMem (.cv b) (synCplc (.cv n) (synC1c)))
        (.classMem (.cv y) (synCcompl (.cv b))))
      (.all c (.all z (.imp (synWa (.neg (.objMem z c))
              (.classMem (synCun (.cv c) (synCsn (.cv z))) (synCplc (.cv n) (synC1c))))
            (.objMem c n))))
      (synWa (.classMem (.cv b) (synCplc (.cv n) (synC1c))) (.neg (.objMem y b)))
      (.imp (.classEq (synCun (.cv a) (synCsn (.cv x))) (synCun (.cv b) (synCsn (.cv y))))
        (.imp (.neg (.objMem x a)) (.classMem (.cv a) (synCplc (.cv n) (synC1c)))))
      p0062 p0153
  have freeVariableCertificate32 : y ∉ ((synCplc (.cv n) (synC1c))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_y_ne_n, or_false,
      not_false_eq_true]
  have freeVariableCertificate33 :
    b ∉
      ((Wff.imp (.neg (.objMem x a)) (.classMem (.cv a) (synCplc (.cv n) (synC1c))))).fv :=
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
      ((Wff.imp (.neg (.objMem x a)) (.classMem (.cv a) (synCplc (.cv n) (synC1c))))).fv :=
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
      ((Wff.all c (.all z (.imp (synWa (.neg (.objMem z c))
                (.classMem (synCun (.cv c) (synCsn (.cv z))) (synCplc (.cv n) (synC1c))))
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
      ((Wff.all c (.all z (.imp (synWa (.neg (.objMem z c))
                (.classMem (synCun (.cv c) (synCsn (.cv z))) (synCplc (.cv n) (synC1c))))
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
    @gRexlimdvva
      (.all c (.all z (.imp (synWa (.neg (.objMem z c))
              (.classMem (synCun (.cv c) (synCsn (.cv z))) (synCplc (.cv n) (synC1c))))
            (.objMem c n))))
      (.classEq (synCun (.cv a) (synCsn (.cv x))) (synCun (.cv b) (synCsn (.cv y))))
      (.imp (.neg (.objMem x a)) (.classMem (.cv a) (synCplc (.cv n) (synC1c)))) b y
      (synCplc (.cv n) (synC1c)) (synCcompl (.cv b)) freeVariableCertificate32
      freeVariableCertificate33 freeVariableCertificate34 freeVariableCertificate35
      freeVariableCertificate36 (show b ≠ y from (by exact fresh_b_ne_y)) p0154
  have p0156 :=
    @gSyl5bi
      (.classMem (synCun (.cv a) (synCsn (.cv x)))
        (synCplc (synCplc (.cv n) (synC1c)) (synC1c)))
      (synWrex b (synCplc (.cv n) (synC1c)) (synWrex y (synCcompl (.cv b))
          (.classEq (synCun (.cv a) (synCsn (.cv x))) (synCun (.cv b) (synCsn (.cv y))))))
      (.all c (.all z (.imp (synWa (.neg (.objMem z c))
              (.classMem (synCun (.cv c) (synCsn (.cv z))) (synCplc (.cv n) (synC1c))))
            (.objMem c n))))
      (.imp (.neg (.objMem x a)) (.classMem (.cv a) (synCplc (.cv n) (synC1c)))) p0059
      p0155
  have p0157 :=
    @gCom23
      (.all c (.all z (.imp (synWa (.neg (.objMem z c))
              (.classMem (synCun (.cv c) (synCsn (.cv z))) (synCplc (.cv n) (synC1c))))
            (.objMem c n))))
      (.classMem (synCun (.cv a) (synCsn (.cv x)))
        (synCplc (synCplc (.cv n) (synC1c)) (synC1c)))
      (.neg (.objMem x a)) (.classMem (.cv a) (synCplc (.cv n) (synC1c))) p0156
  have p0158 :=
    @gImp3a
      (.all c (.all z (.imp (synWa (.neg (.objMem z c))
              (.classMem (synCun (.cv c) (synCsn (.cv z))) (synCplc (.cv n) (synC1c))))
            (.objMem c n))))
      (.neg (.objMem x a))
      (.classMem (synCun (.cv a) (synCsn (.cv x)))
        (synCplc (synCplc (.cv n) (synC1c)) (synC1c)))
      (.classMem (.cv a) (synCplc (.cv n) (synC1c))) p0157
  have freeVariableCertificate37 :
    a ∉
      ((Wff.all c (.all z (.imp (synWa (.neg (.objMem z c))
                (.classMem (synCun (.cv c) (synCsn (.cv z))) (synCplc (.cv n) (synC1c))))
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
      ((Wff.all c (.all z (.imp (synWa (.neg (.objMem z c))
                (.classMem (synCun (.cv c) (synCsn (.cv z))) (synCplc (.cv n) (synC1c))))
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
    @gAlrimivv
      (.all c (.all z (.imp (synWa (.neg (.objMem z c))
              (.classMem (synCun (.cv c) (synCsn (.cv z))) (synCplc (.cv n) (synC1c))))
            (.objMem c n))))
      (.imp (synWa (.neg (.objMem x a)) (.classMem (synCun (.cv a) (synCsn (.cv x)))
            (synCplc (synCplc (.cv n) (synC1c)) (synC1c))))
        (.classMem (.cv a) (synCplc (.cv n) (synC1c))))
      a x freeVariableCertificate37 freeVariableCertificate38 p0158
  have p0160 :=
    @gA1i
      (.imp (.all c (.all z (.imp (synWa (.neg (.objMem z c))
                (.classMem (synCun (.cv c) (synCsn (.cv z))) (synCplc (.cv n) (synC1c))))
              (.objMem c n)))) (.all a (.all x (.imp (synWa (.neg (.objMem x a))
                (.classMem (synCun (.cv a) (synCsn (.cv x)))
                  (synCplc (synCplc (.cv n) (synC1c)) (synC1c))))
              (.classMem (.cv a) (synCplc (.cv n) (synC1c)))))))
      (.classMem (.cv n) (synCnnc)) p0159
  have freeVariableCertificate39 :
    m ∉
      ((Wff.all c (.all z (.imp (synWa (.neg (.objMem z c))
                (.classMem (synCun (.cv c) (synCsn (.cv z))) (synCplc (.cv n) (synC1c))))
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
      ((Wff.all a (.all x (.imp (synWa (.neg (.objMem x a))
                (.classMem (synCun (.cv a) (synCsn (.cv x))) (synCplc (.cv m) (synC1c))))
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
      ((Wff.all a (.all x (.imp (synWa (.neg (.objMem x a)) (synWex y
                  (.classEq (synCun (.cv a) (synCsn (.cv x))) (synCsn (.cv y)))))
              (.classEq (.cv a) (synC0)))))).fv :=
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
      ((Wff.all a (.all x (.imp (synWa (.neg (.objMem x a))
                (.classMem (synCun (.cv a) (synCsn (.cv x))) (synCplc M (synC1c))))
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
      ((Wff.all a (.all x (.imp (synWa (.neg (.objMem x a))
                (.classMem (synCun (.cv a) (synCsn (.cv x)))
                  (synCplc (synCplc (.cv n) (synC1c)) (synC1c))))
              (.classMem (.cv a) (synCplc (.cv n) (synC1c))))))).fv :=
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
    @gFinds
      (.all a (.all x (.imp (synWa (.neg (.objMem x a))
              (.classMem (synCun (.cv a) (synCsn (.cv x))) (synCplc (.cv m) (synC1c))))
            (.objMem a m))))
      (.all a (.all x (.imp (synWa (.neg (.objMem x a)) (synWex y
                (.classEq (synCun (.cv a) (synCsn (.cv x))) (synCsn (.cv y)))))
            (.classEq (.cv a) (synC0)))))
      (.all c (.all z (.imp (synWa (.neg (.objMem z c))
              (.classMem (synCun (.cv c) (synCsn (.cv z))) (synCplc (.cv n) (synC1c))))
            (.objMem c n))))
      (.all a (.all x (.imp (synWa (.neg (.objMem x a))
              (.classMem (synCun (.cv a) (synCsn (.cv x)))
                (synCplc (synCplc (.cv n) (synC1c)) (synC1c))))
            (.classMem (.cv a) (synCplc (.cv n) (synC1c))))))
      (.all a (.all x (.imp (synWa (.neg (.objMem x a))
              (.classMem (synCun (.cv a) (synCsn (.cv x))) (synCplc M (synC1c))))
            (.classMem (.cv a) M))))
      m n M (by exact (show m ∉ (M).fv from (by exact fresh_m_not_M)))
      freeVariableCertificate39 freeVariableCertificate40 freeVariableCertificate41
      freeVariableCertificate42 freeVariableCertificate43
      (show m ≠ n from (by exact fresh_m_ne_n)) p0000 p0016 p0035 p0041 p0047 p0058 p0160
  have p0162 := @gEleq1 (.cv x) X (.cv a)
  have p0163_e00_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv x) X) (synWb (.objMem x a) (.classMem X (.cv a)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb
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
    @gNotbid (.classEq (.cv x) X) (.objMem x a) (.classMem X (.cv a)) p0163_e00_recanon
  have p0164 := @gSneq (.cv x) X
  have p0165 := @gUneq2d (.classEq (.cv x) X) (synCsn (.cv x)) (synCsn X) (.cv a) p0164
  have p0166 :=
    @gEleq1d (.classEq (.cv x) X) (synCun (.cv a) (synCsn (.cv x)))
      (synCun (.cv a) (synCsn X)) (synCplc M (synC1c)) p0165
  have p0167 :=
    @gAnbi12d (.classEq (.cv x) X) (.neg (.objMem x a)) (.neg (.classMem X (.cv a)))
      (.classMem (synCun (.cv a) (synCsn (.cv x))) (synCplc M (synC1c)))
      (.classMem (synCun (.cv a) (synCsn X)) (synCplc M (synC1c))) p0163 p0166
  have p0168 :=
    @gImbi1d (.classEq (.cv x) X)
      (synWa (.neg (.objMem x a))
        (.classMem (synCun (.cv a) (synCsn (.cv x))) (synCplc M (synC1c))))
      (synWa (.neg (.classMem X (.cv a)))
        (.classMem (synCun (.cv a) (synCsn X)) (synCplc M (synC1c))))
      (.classMem (.cv a) M) p0167
  have freeVariableCertificate44 :
    x ∉
      ((Wff.imp (synWa (.neg (.classMem X (.cv a)))
            (.classMem (synCun (.cv a) (synCsn X)) (synCplc M (synC1c))))
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
    @gSpcv
      (.imp (synWa (.neg (.objMem x a))
          (.classMem (synCun (.cv a) (synCsn (.cv x))) (synCplc M (synC1c))))
        (.classMem (.cv a) M))
      (.imp (synWa (.neg (.classMem X (.cv a)))
          (.classMem (synCun (.cv a) (synCsn X)) (synCplc M (synC1c))))
        (.classMem (.cv a) M))
      x X (by exact (show x ∉ (X).fv from (by exact fresh_x_not_X)))
      freeVariableCertificate44 hyp_nnsucelr_2 p0168
  have p0170 :=
    @gAlimi
      (.all x (.imp (synWa (.neg (.objMem x a))
            (.classMem (synCun (.cv a) (synCsn (.cv x))) (synCplc M (synC1c))))
          (.classMem (.cv a) M)))
      (.imp (synWa (.neg (.classMem X (.cv a)))
          (.classMem (synCun (.cv a) (synCsn X)) (synCplc M (synC1c))))
        (.classMem (.cv a) M))
      a p0169
  have p0171 := @gEleq2 (.cv a) A X
  have p0172 := @gNotbid (.classEq (.cv a) A) (.classMem X (.cv a)) (.classMem X A) p0171
  have p0173 := @gUneq1 (.cv a) A (synCsn X)
  have p0174 :=
    @gEleq1d (.classEq (.cv a) A) (synCun (.cv a) (synCsn X)) (synCun A (synCsn X))
      (synCplc M (synC1c)) p0173
  have p0175 :=
    @gAnbi12d (.classEq (.cv a) A) (.neg (.classMem X (.cv a))) (.neg (.classMem X A))
      (.classMem (synCun (.cv a) (synCsn X)) (synCplc M (synC1c)))
      (.classMem (synCun A (synCsn X)) (synCplc M (synC1c))) p0172 p0174
  have p0176 := @gEleq1 (.cv a) A M
  have p0177 :=
    @gImbi12d (.classEq (.cv a) A)
      (synWa (.neg (.classMem X (.cv a)))
        (.classMem (synCun (.cv a) (synCsn X)) (synCplc M (synC1c))))
      (synWa (.neg (.classMem X A)) (.classMem (synCun A (synCsn X)) (synCplc M (synC1c))))
      (.classMem (.cv a) M) (.classMem A M) p0175 p0176
  have freeVariableCertificate45 :
    a ∉
      ((Wff.imp (synWa (.neg (.classMem X A))
            (.classMem (synCun A (synCsn X)) (synCplc M (synC1c)))) (.classMem A M))).fv :=
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
    @gSpcv
      (.imp (synWa (.neg (.classMem X (.cv a)))
          (.classMem (synCun (.cv a) (synCsn X)) (synCplc M (synC1c))))
        (.classMem (.cv a) M))
      (.imp (synWa (.neg (.classMem X A))
          (.classMem (synCun A (synCsn X)) (synCplc M (synC1c)))) (.classMem A M))
      a A (by exact (show a ∉ (A).fv from (by exact fresh_a_not_A)))
      freeVariableCertificate45 hyp_nnsucelr_1 p0177
  have p0179 :=
    @gN3syl (.classMem M (synCnnc))
      (.all a (.all x (.imp (synWa (.neg (.objMem x a))
              (.classMem (synCun (.cv a) (synCsn (.cv x))) (synCplc M (synC1c))))
            (.classMem (.cv a) M))))
      (.all a (.imp (synWa (.neg (.classMem X (.cv a)))
            (.classMem (synCun (.cv a) (synCsn X)) (synCplc M (synC1c))))
          (.classMem (.cv a) M)))
      (.imp (synWa (.neg (.classMem X A))
          (.classMem (synCun A (synCsn X)) (synCplc M (synC1c)))) (.classMem A M))
      p0161 p0170 p0178
  have p0180 :=
    @gImp (.classMem M (synCnnc))
      (synWa (.neg (.classMem X A)) (.classMem (synCun A (synCsn X)) (synCplc M (synC1c))))
      (.classMem A M) p0179
  exact p0180


end NFChoice.DirectNominalPrf.WPPReplay

end
