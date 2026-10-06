/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NominalWPPReplayChunk009StructuralBlock009

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NominalWPPReplayChunk009StructuralPart048`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_ncfinraiselem2`. -/
@[expose]
noncomputable def gNcfinraiselem2 (m : Var) (n : Var) (a : Var) (b : Var)
    (dv_a_b : a ≠ b) (dv_a_m : a ≠ m) (dv_a_n : a ≠ n) (dv_b_m : b ≠ m) (dv_b_n : b ≠ n) :
    Nominal.NPrf
      (.classMem (.cab m (synWral a (.cv m) (synWral b (.cv m) (synWrex n (synCnnc)
                (synWa (.classMem (synCpw1 (.cv a)) (.cv n))
                  (.classMem (synCpw1 (.cv b)) (.cv n))))))) (synCvv)) :=
  by
  let proofSupport : Finset Var :=
    ({ m } : Finset Var) ∪ ({ n } : Finset Var) ∪ ({ a } : Finset Var) ∪
      ({ b } : Finset Var)
  let t : Var := freshVar proofSupport 0
  let x : Var := freshVar proofSupport 1
  have fresh_t : t ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_t_ne_m : t ≠ m := by
    intro h
    exact
      fresh_t
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_t_ne_n : t ≠ n := by
    intro h
    exact
      fresh_t
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_n_ne_t : n ≠ t := Ne.symm fresh_t_ne_n
  have fresh_t_ne_a : t ≠ a := by
    intro h
    exact
      fresh_t
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_a_ne_t : a ≠ t := Ne.symm fresh_t_ne_a
  have fresh_t_ne_b : t ≠ b := by
    intro h
    exact fresh_t (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_b_ne_t : b ≠ t := Ne.symm fresh_t_ne_b
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_x_ne_n : x ≠ n := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_x_ne_a : x ≠ a := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_x_ne_b : x ≠ b := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_t_ne_x : t ≠ x :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_x_ne_t : x ≠ t := Ne.symm fresh_t_ne_x
  let syntaxClass0000 : Class :=
    (synCimak (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk))))
      (synCpw1 (synCpw1 (synCpw1 (synC1c)))))
  let syntaxClass0001 : Class :=
    (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) syntaxClass0000)
  let syntaxClass0002 : Class := (synCsik syntaxClass0001)
  let syntaxClass0003 : Class := (synCins2k syntaxClass0002)
  let syntaxClass0004 : Class := (synCin syntaxClass0003 (synCins3k (synCssetk)))
  let syntaxClass0005 : Class :=
    (synCimak syntaxClass0004 (synCpw1 (synCpw1 (synC1c))))
  let syntaxClass0006 : Class := (synCins2k syntaxClass0005)
  let syntaxClass0007 : Class := (synCins3k syntaxClass0005)
  let syntaxClass0008 : Class := (synCin syntaxClass0006 syntaxClass0007)
  let syntaxClass0009 : Class :=
    (synCin (synCxpk (synCpw1 (synCpw1 (synCnnc))) (synCvv)) syntaxClass0008)
  let syntaxClass0010 : Class := (synCimak syntaxClass0009 (synCpw1 (synC1c)))
  let syntaxClass0011 : Class := (synCins3k syntaxClass0010)
  let syntaxClass0012 : Class :=
    (synCdif (synCins2k (synCsik (synCssetk))) syntaxClass0011)
  let syntaxClass0013 : Class :=
    (synCimak syntaxClass0012 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))
  let syntaxClass0014 : Class := (synCin (synCsik (synCssetk)) syntaxClass0013)
  let syntaxClass0015 : Class := (synCimak syntaxClass0014 (synCpw1 (synC1c)))
  let syntaxFormula0016 : Wff :=
    (.classMem (synCopk (.cv t) (synCsn (.cv m))) syntaxClass0014)
  let syntaxFormula0017 : Wff :=
    (synWa (.classMem (.cv t) (synCpw1 (synC1c))) syntaxFormula0016)
  let syntaxFormula0018 : Wff :=
    (synWa (.classEq (.cv t) (synCsn (synCsn (.cv a)))) syntaxFormula0016)
  let syntaxFormula0019 : Wff := (synWex a syntaxFormula0018)
  let syntaxFormula0020 : Wff := (synWrex t (synCpw1 (synC1c)) syntaxFormula0016)
  let syntaxFormula0021 : Wff := (synWex t syntaxFormula0018)
  let syntaxFormula0022 : Wff := (synWex a syntaxFormula0021)
  let syntaxFormula0023 : Wff :=
    (.classMem (synCopk (synCsn (synCsn (.cv a))) (synCsn (.cv m))) syntaxClass0014)
  let syntaxFormula0024 : Wff :=
    (.classMem (synCopk (.cv t) (synCopk (synCsn (synCsn (.cv a))) (synCsn (.cv m))))
      syntaxClass0012)
  let syntaxFormula0025 : Wff :=
    (synWrex t (synCpw1 (synCpw1 (synCpw1 (synC1c)))) syntaxFormula0024)
  let syntaxFormula0026 : Wff :=
    (synWa (.classMem (.cv t) (synCpw1 (synCpw1 (synCpw1 (synC1c))))) syntaxFormula0024)
  let syntaxFormula0027 : Wff :=
    (synWa (.classEq (.cv t) (synCsn (synCsn (synCsn (synCsn (.cv b))))))
      syntaxFormula0024)
  let syntaxFormula0028 : Wff := (synWex b syntaxFormula0027)
  let syntaxFormula0029 : Wff := (synWex t syntaxFormula0026)
  let syntaxFormula0030 : Wff := (synWex t syntaxFormula0027)
  let syntaxFormula0031 : Wff := (synWex b syntaxFormula0030)
  let syntaxFormula0032 : Wff :=
    (.classMem (synCopk (synCsn (synCsn (.cv a))) (synCsn (.cv m))) syntaxClass0013)
  let syntaxClass0033 : Class :=
    (synCopk (synCsn (synCsn (synCsn (synCsn (.cv b)))))
      (synCopk (synCsn (synCsn (.cv a))) (synCsn (.cv m))))
  let syntaxFormula0034 : Wff := (.classMem syntaxClass0033 syntaxClass0012)
  let syntaxFormula0035 : Wff :=
    (.classMem syntaxClass0033 (synCins2k (synCsik (synCssetk))))
  let syntaxClass0036 : Class :=
    (synCopk (.cv t) (synCopk (synCsn (synCsn (.cv b))) (synCsn (synCsn (.cv a)))))
  let syntaxFormula0037 : Wff := (.classMem syntaxClass0036 syntaxClass0009)
  let syntaxFormula0038 : Wff := (synWrex t (synCpw1 (synC1c)) syntaxFormula0037)
  let syntaxFormula0039 : Wff :=
    (synWa (.classMem (.cv t) (synCpw1 (synC1c))) syntaxFormula0037)
  let syntaxFormula0040 : Wff :=
    (synWa (.classEq (.cv t) (synCsn (synCsn (.cv n)))) syntaxFormula0037)
  let syntaxFormula0041 : Wff := (synWex n syntaxFormula0040)
  let syntaxFormula0042 : Wff := (synWex t syntaxFormula0041)
  let syntaxFormula0043 : Wff :=
    (.classMem (synCopk (synCsn (synCsn (.cv b))) (synCsn (synCsn (.cv a))))
      syntaxClass0010)
  let syntaxFormula0044 : Wff := (synWex t syntaxFormula0040)
  let syntaxFormula0045 : Wff := (synWex n syntaxFormula0044)
  let syntaxClass0046 : Class :=
    (synCopk (synCsn (synCsn (.cv n)))
      (synCopk (synCsn (synCsn (.cv b))) (synCsn (synCsn (.cv a)))))
  let syntaxFormula0047 : Wff := (.classMem syntaxClass0046 syntaxClass0009)
  let syntaxFormula0048 : Wff :=
    (.classMem syntaxClass0046 (synCxpk (synCpw1 (synCpw1 (synCnnc))) (synCvv)))
  let syntaxFormula0049 : Wff :=
    (.classMem (synCopk (.cv t) (synCopk (.cv n) (synCsn (synCsn (.cv a)))))
      syntaxClass0004)
  let syntaxFormula0050 : Wff :=
    (synWrex t (synCpw1 (synCpw1 (synC1c))) syntaxFormula0049)
  let syntaxFormula0051 : Wff :=
    (synWa (.classMem (.cv t) (synCpw1 (synCpw1 (synC1c)))) syntaxFormula0049)
  let syntaxFormula0052 : Wff :=
    (synWa (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv x))))) syntaxFormula0049)
  let syntaxFormula0053 : Wff := (synWex x syntaxFormula0052)
  let syntaxFormula0054 : Wff := (synWex t syntaxFormula0051)
  let syntaxFormula0055 : Wff := (synWex t syntaxFormula0052)
  let syntaxFormula0056 : Wff := (synWex x syntaxFormula0055)
  let syntaxFormula0057 : Wff :=
    (.classMem (synCopk (.cv n) (synCsn (synCsn (.cv a)))) syntaxClass0005)
  let syntaxClass0058 : Class :=
    (synCopk (synCsn (synCsn (synCsn (.cv x))))
      (synCopk (.cv n) (synCsn (synCsn (.cv a)))))
  let syntaxFormula0059 : Wff := (.classMem syntaxClass0058 syntaxClass0004)
  let syntaxFormula0060 : Wff := (.classMem syntaxClass0058 syntaxClass0003)
  let syntaxFormula0061 : Wff := (.classMem syntaxClass0058 (synCins3k (synCssetk)))
  let syntaxFormula0062 : Wff := (.classMem syntaxClass0046 syntaxClass0006)
  let syntaxFormula0063 : Wff :=
    (.classMem (synCopk (.cv t) (synCopk (.cv n) (synCsn (synCsn (.cv b)))))
      syntaxClass0004)
  let syntaxFormula0064 : Wff :=
    (synWa (.classMem (.cv t) (synCpw1 (synCpw1 (synC1c)))) syntaxFormula0063)
  let syntaxFormula0065 : Wff :=
    (synWa (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv x))))) syntaxFormula0063)
  let syntaxFormula0066 : Wff := (synWex x syntaxFormula0065)
  let syntaxFormula0067 : Wff :=
    (synWrex t (synCpw1 (synCpw1 (synC1c))) syntaxFormula0063)
  let syntaxFormula0068 : Wff := (synWex t syntaxFormula0065)
  let syntaxFormula0069 : Wff := (synWex x syntaxFormula0068)
  let syntaxClass0070 : Class :=
    (synCopk (synCsn (synCsn (synCsn (.cv x))))
      (synCopk (.cv n) (synCsn (synCsn (.cv b)))))
  let syntaxFormula0071 : Wff := (.classMem syntaxClass0070 syntaxClass0004)
  let syntaxFormula0072 : Wff := (.classMem syntaxClass0070 syntaxClass0003)
  let syntaxFormula0073 : Wff := (.classMem syntaxClass0070 (synCins3k (synCssetk)))
  let syntaxFormula0074 : Wff :=
    (.classMem (synCopk (.cv n) (synCsn (synCsn (.cv b)))) syntaxClass0005)
  let syntaxFormula0075 : Wff := (.classMem syntaxClass0046 syntaxClass0007)
  let syntaxFormula0076 : Wff := (.classMem syntaxClass0046 syntaxClass0008)
  let syntaxFormula0077 : Wff :=
    (synWa (.classMem (synCpw1 (.cv a)) (.cv n)) (.classMem (synCpw1 (.cv b)) (.cv n)))
  let syntaxFormula0078 : Wff := (synWa (.classMem (.cv n) (synCnnc)) syntaxFormula0077)
  let syntaxFormula0079 : Wff := (synWrex n (synCnnc) syntaxFormula0077)
  let syntaxFormula0080 : Wff := (.classMem syntaxClass0033 syntaxClass0011)
  let syntaxFormula0081 : Wff := (.neg syntaxFormula0080)
  let syntaxFormula0082 : Wff := (.neg syntaxFormula0079)
  let syntaxFormula0083 : Wff := (synWrex b (.cv m) syntaxFormula0082)
  let syntaxFormula0084 : Wff := (synWral b (.cv m) syntaxFormula0079)
  let syntaxFormula0085 : Wff := (.neg syntaxFormula0084)
  let syntaxFormula0086 : Wff := (synWrex a (.cv m) syntaxFormula0085)
  let syntaxFormula0087 : Wff := (.classMem (synCsn (.cv m)) syntaxClass0015)
  let syntaxClass0088 : Class := (synCcompl syntaxClass0015)
  let syntaxFormula0089 : Wff := (.classMem (synCsn (.cv m)) syntaxClass0088)
  let syntaxClass0090 : Class := (synCuni1 syntaxClass0088)
  let syntaxFormula0091 : Wff := (synWral a (.cv m) syntaxFormula0084)
  have p0000 := @gSnex (.cv m)
  have p0001 := @gElcompl (synCsn (.cv m)) syntaxClass0015 p0000
  have freshnessCertificate0000 : t ∉ ((synCssetk)).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk];
      exact (show t ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))
  have freshnessCertificate0001 : t ∉ ((synCsik (synCssetk))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0000)
  have freshnessCertificate0002 : t ∉ ((synCins2k (synCsik (synCssetk)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0001)
  have freshnessCertificate0003 : t ∉ ((synCnnc)).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc];
      exact (show t ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))
  have freshnessCertificate0004 : t ∉ ((synCpw1 (synCnnc))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0003)
  have freshnessCertificate0005 : t ∉ ((synCpw1 (synCpw1 (synCnnc)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0004)
  have freshnessCertificate0006 : t ∉ ((synCvv)).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv];
      exact (show t ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))
  have freshnessCertificate0007 :
    t ∉ (((synCpw1 (synCpw1 (synCnnc)))).fv) ∪ (((synCvv)).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0005 freshnessCertificate0006))
  have freshnessCertificate0008 :
    t ∉ ((synCxpk (synCpw1 (synCpw1 (synCnnc))) (synCvv))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk];
      exact freshnessCertificate0007)
  have freshnessCertificate0009 : t ∉ ((synC1c)).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c];
      exact (show t ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))
  have freshnessCertificate0010 : t ∉ ((synCpw (synC1c))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw];
      exact freshnessCertificate0009)
  have freshnessCertificate0011 : t ∉ (((synCpw (synC1c))).fv) ∪ (((synCvv)).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0010 freshnessCertificate0006))
  have freshnessCertificate0012 : t ∉ ((synCxpk (synCpw (synC1c)) (synCvv))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk];
      exact freshnessCertificate0011)
  have freshnessCertificate0013 : t ∉ ((synCins3k (synCssetk))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0000)
  have freshnessCertificate0014 :
    t ∉ (((synCins3k (synCssetk))).fv) ∪ (((synCins2k (synCsik (synCssetk)))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0013 freshnessCertificate0002))
  have freshnessCertificate0015 :
    t ∉
      ((synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif];
      exact freshnessCertificate0014)
  have freshnessCertificate0016 : t ∉ ((synCpw1 (synC1c))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0009)
  have freshnessCertificate0017 : t ∉ ((synCpw1 (synCpw1 (synC1c)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0016)
  have freshnessCertificate0018 : t ∉ ((synCpw1 (synCpw1 (synCpw1 (synC1c))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0017)
  have freshnessCertificate0019 :
    t ∉
      (((synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk))))).fv) ∪
        (((synCpw1 (synCpw1 (synCpw1 (synC1c))))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0015 freshnessCertificate0018))
  have freshnessCertificate0020 : t ∉ (syntaxClass0000).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak];
      exact freshnessCertificate0019)
  have freshnessCertificate0021 :
    t ∉ (((synCxpk (synCpw (synC1c)) (synCvv))).fv) ∪ ((syntaxClass0000).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0012 freshnessCertificate0020))
  have freshnessCertificate0022 : t ∉ (syntaxClass0001).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif];
      exact freshnessCertificate0021)
  have freshnessCertificate0023 : t ∉ (syntaxClass0002).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0022)
  have freshnessCertificate0024 : t ∉ (syntaxClass0003).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0023)
  have freshnessCertificate0025 :
    t ∉ ((syntaxClass0003).fv) ∪ (((synCins3k (synCssetk))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0024 freshnessCertificate0013))
  have freshnessCertificate0026 : t ∉ (syntaxClass0004).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin];
      exact freshnessCertificate0025)
  have freshnessCertificate0027 :
    t ∉ ((syntaxClass0004).fv) ∪ (((synCpw1 (synCpw1 (synC1c)))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0026 freshnessCertificate0017))
  have freshnessCertificate0028 : t ∉ (syntaxClass0005).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak];
      exact freshnessCertificate0027)
  have freshnessCertificate0029 : t ∉ (syntaxClass0006).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0028)
  have freshnessCertificate0030 : t ∉ (syntaxClass0007).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0028)
  have freshnessCertificate0031 : t ∉ ((syntaxClass0006).fv) ∪ ((syntaxClass0007).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0029 freshnessCertificate0030))
  have freshnessCertificate0032 : t ∉ (syntaxClass0008).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin];
      exact freshnessCertificate0031)
  have freshnessCertificate0033 :
    t ∉
      (((synCxpk (synCpw1 (synCpw1 (synCnnc))) (synCvv))).fv) ∪
        ((syntaxClass0008).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0008 freshnessCertificate0032))
  have freshnessCertificate0034 : t ∉ (syntaxClass0009).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin];
      exact freshnessCertificate0033)
  have freshnessCertificate0035 :
    t ∉ ((syntaxClass0009).fv) ∪ (((synCpw1 (synC1c))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0034 freshnessCertificate0016))
  have freshnessCertificate0036 : t ∉ (syntaxClass0010).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak];
      exact freshnessCertificate0035)
  have freshnessCertificate0037 : t ∉ (syntaxClass0011).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0036)
  have freshnessCertificate0038 :
    t ∉ (((synCins2k (synCsik (synCssetk)))).fv) ∪ ((syntaxClass0011).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0002 freshnessCertificate0037))
  have freshnessCertificate0039 : t ∉ (syntaxClass0012).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif];
      exact freshnessCertificate0038)
  have freshnessCertificate0040 :
    t ∉ ((syntaxClass0012).fv) ∪ (((synCpw1 (synCpw1 (synCpw1 (synC1c))))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0039 freshnessCertificate0018))
  have freshnessCertificate0041 : t ∉ (syntaxClass0013).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak];
      exact freshnessCertificate0040)
  have freshnessCertificate0042 :
    t ∉ (((synCsik (synCssetk))).fv) ∪ ((syntaxClass0013).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0001 freshnessCertificate0041))
  have freshnessCertificate0043 : t ∉ (syntaxClass0014).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin];
      exact freshnessCertificate0042)
  have freshnessCertificate0044 : t ∉ ((Class.cv m)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show t ∉ ({ m } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show t ≠ m from (by exact fresh_t_ne_m)))))
  have freshnessCertificate0045 : t ∉ ((synCsn (.cv m))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0044)
  have p0002 :=
    @gElimak t syntaxClass0014 (synCpw1 (synC1c)) (synCsn (.cv m))
      (by exact freshnessCertificate0043) (by exact freshnessCertificate0016)
      (by exact freshnessCertificate0045) p0000
  have freshnessCertificate0046 : a ∉ ((Class.cv t)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show a ∉ ({ t } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show a ≠ t from (by exact fresh_a_ne_t)))))
  have p0003 := @gElpw11c a (.cv t) (by exact freshnessCertificate0046)
  have p0004 :=
    @gAnbi1i (.classMem (.cv t) (synCpw1 (synC1c)))
      (synWex a (.classEq (.cv t) (synCsn (synCsn (.cv a))))) syntaxFormula0016 p0003
  have freshnessCertificate0047 : a ∉ ((Class.cv m)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show a ∉ ({ m } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using (show a ≠ m from (by exact dv_a_m)))))
  have freshnessCertificate0048 : a ∉ ((synCsn (.cv m))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0047)
  have freshnessCertificate0049 : a ∉ (((Class.cv t)).fv) ∪ (((synCsn (.cv m))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0046 freshnessCertificate0048))
  have freshnessCertificate0050 : a ∉ ((synCopk (.cv t) (synCsn (.cv m)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk];
      exact freshnessCertificate0049)
  have freshnessCertificate0051 : a ∉ ((synCssetk)).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk];
      exact (show a ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))
  have freshnessCertificate0052 : a ∉ ((synCsik (synCssetk))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0051)
  have freshnessCertificate0053 : a ∉ ((synCins2k (synCsik (synCssetk)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0052)
  have freshnessCertificate0054 : a ∉ ((synCnnc)).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc];
      exact (show a ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))
  have freshnessCertificate0055 : a ∉ ((synCpw1 (synCnnc))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0054)
  have freshnessCertificate0056 : a ∉ ((synCpw1 (synCpw1 (synCnnc)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0055)
  have freshnessCertificate0057 : a ∉ ((synCvv)).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv];
      exact (show a ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))
  have freshnessCertificate0058 :
    a ∉ (((synCpw1 (synCpw1 (synCnnc)))).fv) ∪ (((synCvv)).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0056 freshnessCertificate0057))
  have freshnessCertificate0059 :
    a ∉ ((synCxpk (synCpw1 (synCpw1 (synCnnc))) (synCvv))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk];
      exact freshnessCertificate0058)
  have freshnessCertificate0060 : a ∉ ((synC1c)).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c];
      exact (show a ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))
  have freshnessCertificate0061 : a ∉ ((synCpw (synC1c))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw];
      exact freshnessCertificate0060)
  have freshnessCertificate0062 : a ∉ (((synCpw (synC1c))).fv) ∪ (((synCvv)).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0061 freshnessCertificate0057))
  have freshnessCertificate0063 : a ∉ ((synCxpk (synCpw (synC1c)) (synCvv))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk];
      exact freshnessCertificate0062)
  have freshnessCertificate0064 : a ∉ ((synCins3k (synCssetk))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0051)
  have freshnessCertificate0065 :
    a ∉ (((synCins3k (synCssetk))).fv) ∪ (((synCins2k (synCsik (synCssetk)))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0064 freshnessCertificate0053))
  have freshnessCertificate0066 :
    a ∉
      ((synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif];
      exact freshnessCertificate0065)
  have freshnessCertificate0067 : a ∉ ((synCpw1 (synC1c))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0060)
  have freshnessCertificate0068 : a ∉ ((synCpw1 (synCpw1 (synC1c)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0067)
  have freshnessCertificate0069 : a ∉ ((synCpw1 (synCpw1 (synCpw1 (synC1c))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0068)
  have freshnessCertificate0070 :
    a ∉
      (((synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk))))).fv) ∪
        (((synCpw1 (synCpw1 (synCpw1 (synC1c))))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0066 freshnessCertificate0069))
  have freshnessCertificate0071 : a ∉ (syntaxClass0000).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak];
      exact freshnessCertificate0070)
  have freshnessCertificate0072 :
    a ∉ (((synCxpk (synCpw (synC1c)) (synCvv))).fv) ∪ ((syntaxClass0000).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0063 freshnessCertificate0071))
  have freshnessCertificate0073 : a ∉ (syntaxClass0001).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif];
      exact freshnessCertificate0072)
  have freshnessCertificate0074 : a ∉ (syntaxClass0002).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0073)
  have freshnessCertificate0075 : a ∉ (syntaxClass0003).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0074)
  have freshnessCertificate0076 :
    a ∉ ((syntaxClass0003).fv) ∪ (((synCins3k (synCssetk))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0075 freshnessCertificate0064))
  have freshnessCertificate0077 : a ∉ (syntaxClass0004).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin];
      exact freshnessCertificate0076)
  have freshnessCertificate0078 :
    a ∉ ((syntaxClass0004).fv) ∪ (((synCpw1 (synCpw1 (synC1c)))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0077 freshnessCertificate0068))
  have freshnessCertificate0079 : a ∉ (syntaxClass0005).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak];
      exact freshnessCertificate0078)
  have freshnessCertificate0080 : a ∉ (syntaxClass0006).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0079)
  have freshnessCertificate0081 : a ∉ (syntaxClass0007).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0079)
  have freshnessCertificate0082 : a ∉ ((syntaxClass0006).fv) ∪ ((syntaxClass0007).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0080 freshnessCertificate0081))
  have freshnessCertificate0083 : a ∉ (syntaxClass0008).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin];
      exact freshnessCertificate0082)
  have freshnessCertificate0084 :
    a ∉
      (((synCxpk (synCpw1 (synCpw1 (synCnnc))) (synCvv))).fv) ∪
        ((syntaxClass0008).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0059 freshnessCertificate0083))
  have freshnessCertificate0085 : a ∉ (syntaxClass0009).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin];
      exact freshnessCertificate0084)
  have freshnessCertificate0086 :
    a ∉ ((syntaxClass0009).fv) ∪ (((synCpw1 (synC1c))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0085 freshnessCertificate0067))
  have freshnessCertificate0087 : a ∉ (syntaxClass0010).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak];
      exact freshnessCertificate0086)
  have freshnessCertificate0088 : a ∉ (syntaxClass0011).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0087)
  have freshnessCertificate0089 :
    a ∉ (((synCins2k (synCsik (synCssetk)))).fv) ∪ ((syntaxClass0011).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0053 freshnessCertificate0088))
  have freshnessCertificate0090 : a ∉ (syntaxClass0012).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif];
      exact freshnessCertificate0089)
  have freshnessCertificate0091 :
    a ∉ ((syntaxClass0012).fv) ∪ (((synCpw1 (synCpw1 (synCpw1 (synC1c))))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0090 freshnessCertificate0069))
  have freshnessCertificate0092 : a ∉ (syntaxClass0013).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak];
      exact freshnessCertificate0091)
  have freshnessCertificate0093 :
    a ∉ (((synCsik (synCssetk))).fv) ∪ ((syntaxClass0013).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0052 freshnessCertificate0092))
  have freshnessCertificate0094 : a ∉ (syntaxClass0014).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin];
      exact freshnessCertificate0093)
  have freshnessCertificate0095 :
    a ∉ (((synCopk (.cv t) (synCsn (.cv m)))).fv) ∪ ((syntaxClass0014).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0050 freshnessCertificate0094))
  have freshnessCertificate0096 :
    a ∉ ((Wff.classMem (synCopk (.cv t) (synCsn (.cv m))) syntaxClass0014)).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact freshnessCertificate0095)
  have p0005 :=
    @gN1941v (.classEq (.cv t) (synCsn (synCsn (.cv a)))) syntaxFormula0016 a
      (by exact freshnessCertificate0096)
  have p0006 :=
    @gBitr4i syntaxFormula0017
      (synWa (synWex a (.classEq (.cv t) (synCsn (synCsn (.cv a))))) syntaxFormula0016)
      syntaxFormula0019 p0004 p0005
  have p0007 := @gExbii syntaxFormula0017 syntaxFormula0019 t p0006
  have p0008 := (Nominal.biimpRefl syntaxFormula0020)
  have p0009 := @gExcom syntaxFormula0018 a t
  have p0010 :=
    @gN3bitr4i (synWex t syntaxFormula0017) (synWex t syntaxFormula0019)
      syntaxFormula0020 syntaxFormula0022 p0007 p0008 p0009
  have p0011 := @gSnex (synCsn (.cv a))
  have p0012 := @gOpkeq1 (.cv t) (synCsn (synCsn (.cv a))) (synCsn (.cv m))
  have p0013 :=
    @gEleq1d (.classEq (.cv t) (synCsn (synCsn (.cv a))))
      (synCopk (.cv t) (synCsn (.cv m)))
      (synCopk (synCsn (synCsn (.cv a))) (synCsn (.cv m))) syntaxClass0014 p0012
  have freshnessCertificate0097 : t ∉ ((Class.cv a)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show t ∉ ({ a } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show t ≠ a from (by exact fresh_t_ne_a)))))
  have freshnessCertificate0098 : t ∉ ((synCsn (.cv a))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0097)
  have freshnessCertificate0099 : t ∉ ((synCsn (synCsn (.cv a)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0098)
  have freshnessCertificate0100 :
    t ∉ (((synCsn (synCsn (.cv a)))).fv) ∪ (((synCsn (.cv m))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0099 freshnessCertificate0045))
  have freshnessCertificate0101 :
    t ∉ ((synCopk (synCsn (synCsn (.cv a))) (synCsn (.cv m)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk];
      exact freshnessCertificate0100)
  have freshnessCertificate0102 :
    t ∉
      (((synCopk (synCsn (synCsn (.cv a))) (synCsn (.cv m)))).fv) ∪
        ((syntaxClass0014).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0101 freshnessCertificate0043))
  have freshnessCertificate0103 :
    t ∉
      ((Wff.classMem (synCopk (synCsn (synCsn (.cv a))) (synCsn (.cv m)))
          syntaxClass0014)).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact freshnessCertificate0102)
  have p0014 :=
    @gCeqsexv syntaxFormula0016 syntaxFormula0023 t (synCsn (synCsn (.cv a)))
      (by exact freshnessCertificate0099) (by exact freshnessCertificate0103) p0011 p0013
  have p0015 :=
    @gElin (synCopk (synCsn (synCsn (.cv a))) (synCsn (.cv m)))
      (synCsik (synCssetk)) syntaxClass0013
  have p0016 := @gSnex (.cv a)
  have p0017 := @gVex m
  have p0018 := @gOpksnelsik (synCsn (.cv a)) (.cv m) (synCssetk) p0016 p0017
  have p0019 := @gVex a
  have p0020 := @gElssetk (.cv a) (.cv m) p0019 p0017
  have p0021_e01_recanon :
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
      p0020
  have p0021 :=
    @gBitri
      (.classMem (synCopk (synCsn (synCsn (.cv a))) (synCsn (.cv m)))
        (synCsik (synCssetk)))
      (.classMem (synCopk (synCsn (.cv a)) (.cv m)) (synCssetk)) (.objMem a m) p0018
      p0021_e01_recanon
  have p0022 := @gOpkex (synCsn (synCsn (.cv a))) (synCsn (.cv m))
  have p0023 :=
    @gElimak t syntaxClass0012 (synCpw1 (synCpw1 (synCpw1 (synC1c))))
      (synCopk (synCsn (synCsn (.cv a))) (synCsn (.cv m)))
      (by exact freshnessCertificate0039) (by exact freshnessCertificate0018)
      (by exact freshnessCertificate0101) p0022
  have p0024 := (Nominal.biimpRefl syntaxFormula0025)
  have freshnessCertificate0104 : b ∉ ((Class.cv t)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show b ∉ ({ t } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show b ≠ t from (by exact fresh_b_ne_t)))))
  have p0025 := @gElpw131c b (.cv t) (by exact freshnessCertificate0104)
  have p0026 :=
    @gAnbi1i (.classMem (.cv t) (synCpw1 (synCpw1 (synCpw1 (synC1c)))))
      (synWex b (.classEq (.cv t) (synCsn (synCsn (synCsn (synCsn (.cv b)))))))
      syntaxFormula0024 p0025
  have freshnessCertificate0105 : b ∉ ((Class.cv a)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show b ∉ ({ a } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show b ≠ a from (by exact Ne.symm dv_a_b)))))
  have freshnessCertificate0106 : b ∉ ((synCsn (.cv a))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0105)
  have freshnessCertificate0107 : b ∉ ((synCsn (synCsn (.cv a)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0106)
  have freshnessCertificate0108 : b ∉ ((Class.cv m)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show b ∉ ({ m } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using (show b ≠ m from (by exact dv_b_m)))))
  have freshnessCertificate0109 : b ∉ ((synCsn (.cv m))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0108)
  have freshnessCertificate0110 :
    b ∉ (((synCsn (synCsn (.cv a)))).fv) ∪ (((synCsn (.cv m))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0107 freshnessCertificate0109))
  have freshnessCertificate0111 :
    b ∉ ((synCopk (synCsn (synCsn (.cv a))) (synCsn (.cv m)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk];
      exact freshnessCertificate0110)
  have freshnessCertificate0112 :
    b ∉
      (((Class.cv t)).fv) ∪
        (((synCopk (synCsn (synCsn (.cv a))) (synCsn (.cv m)))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0104 freshnessCertificate0111))
  have freshnessCertificate0113 :
    b ∉
      ((synCopk (.cv t) (synCopk (synCsn (synCsn (.cv a))) (synCsn (.cv m))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk];
      exact freshnessCertificate0112)
  have freshnessCertificate0114 : b ∉ ((synCssetk)).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk];
      exact (show b ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))
  have freshnessCertificate0115 : b ∉ ((synCsik (synCssetk))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0114)
  have freshnessCertificate0116 : b ∉ ((synCins2k (synCsik (synCssetk)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0115)
  have freshnessCertificate0117 : b ∉ ((synCnnc)).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc];
      exact (show b ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))
  have freshnessCertificate0118 : b ∉ ((synCpw1 (synCnnc))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0117)
  have freshnessCertificate0119 : b ∉ ((synCpw1 (synCpw1 (synCnnc)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0118)
  have freshnessCertificate0120 : b ∉ ((synCvv)).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv];
      exact (show b ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))
  have freshnessCertificate0121 :
    b ∉ (((synCpw1 (synCpw1 (synCnnc)))).fv) ∪ (((synCvv)).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0119 freshnessCertificate0120))
  have freshnessCertificate0122 :
    b ∉ ((synCxpk (synCpw1 (synCpw1 (synCnnc))) (synCvv))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk];
      exact freshnessCertificate0121)
  have freshnessCertificate0123 : b ∉ ((synC1c)).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c];
      exact (show b ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))
  have freshnessCertificate0124 : b ∉ ((synCpw (synC1c))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw];
      exact freshnessCertificate0123)
  have freshnessCertificate0125 : b ∉ (((synCpw (synC1c))).fv) ∪ (((synCvv)).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0124 freshnessCertificate0120))
  have freshnessCertificate0126 : b ∉ ((synCxpk (synCpw (synC1c)) (synCvv))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk];
      exact freshnessCertificate0125)
  have freshnessCertificate0127 : b ∉ ((synCins3k (synCssetk))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0114)
  have freshnessCertificate0128 :
    b ∉ (((synCins3k (synCssetk))).fv) ∪ (((synCins2k (synCsik (synCssetk)))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0127 freshnessCertificate0116))
  have freshnessCertificate0129 :
    b ∉
      ((synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif];
      exact freshnessCertificate0128)
  have freshnessCertificate0130 : b ∉ ((synCpw1 (synC1c))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0123)
  have freshnessCertificate0131 : b ∉ ((synCpw1 (synCpw1 (synC1c)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0130)
  have freshnessCertificate0132 : b ∉ ((synCpw1 (synCpw1 (synCpw1 (synC1c))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0131)
  have freshnessCertificate0133 :
    b ∉
      (((synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk))))).fv) ∪
        (((synCpw1 (synCpw1 (synCpw1 (synC1c))))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0129 freshnessCertificate0132))
  have freshnessCertificate0134 : b ∉ (syntaxClass0000).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak];
      exact freshnessCertificate0133)
  have freshnessCertificate0135 :
    b ∉ (((synCxpk (synCpw (synC1c)) (synCvv))).fv) ∪ ((syntaxClass0000).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0126 freshnessCertificate0134))
  have freshnessCertificate0136 : b ∉ (syntaxClass0001).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif];
      exact freshnessCertificate0135)
  have freshnessCertificate0137 : b ∉ (syntaxClass0002).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0136)
  have freshnessCertificate0138 : b ∉ (syntaxClass0003).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0137)
  have freshnessCertificate0139 :
    b ∉ ((syntaxClass0003).fv) ∪ (((synCins3k (synCssetk))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0138 freshnessCertificate0127))
  have freshnessCertificate0140 : b ∉ (syntaxClass0004).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin];
      exact freshnessCertificate0139)
  have freshnessCertificate0141 :
    b ∉ ((syntaxClass0004).fv) ∪ (((synCpw1 (synCpw1 (synC1c)))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0140 freshnessCertificate0131))
  have freshnessCertificate0142 : b ∉ (syntaxClass0005).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak];
      exact freshnessCertificate0141)
  have freshnessCertificate0143 : b ∉ (syntaxClass0006).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0142)
  have freshnessCertificate0144 : b ∉ (syntaxClass0007).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0142)
  have freshnessCertificate0145 : b ∉ ((syntaxClass0006).fv) ∪ ((syntaxClass0007).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0143 freshnessCertificate0144))
  have freshnessCertificate0146 : b ∉ (syntaxClass0008).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin];
      exact freshnessCertificate0145)
  have freshnessCertificate0147 :
    b ∉
      (((synCxpk (synCpw1 (synCpw1 (synCnnc))) (synCvv))).fv) ∪
        ((syntaxClass0008).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0122 freshnessCertificate0146))
  have freshnessCertificate0148 : b ∉ (syntaxClass0009).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin];
      exact freshnessCertificate0147)
  have freshnessCertificate0149 :
    b ∉ ((syntaxClass0009).fv) ∪ (((synCpw1 (synC1c))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0148 freshnessCertificate0130))
  have freshnessCertificate0150 : b ∉ (syntaxClass0010).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak];
      exact freshnessCertificate0149)
  have freshnessCertificate0151 : b ∉ (syntaxClass0011).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0150)
  have freshnessCertificate0152 :
    b ∉ (((synCins2k (synCsik (synCssetk)))).fv) ∪ ((syntaxClass0011).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0116 freshnessCertificate0151))
  have freshnessCertificate0153 : b ∉ (syntaxClass0012).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif];
      exact freshnessCertificate0152)
  have freshnessCertificate0154 :
    b ∉
      (((synCopk (.cv t) (synCopk (synCsn (synCsn (.cv a))) (synCsn (.cv m))))).fv) ∪
        ((syntaxClass0012).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0113 freshnessCertificate0153))
  have freshnessCertificate0155 :
    b ∉
      ((Wff.classMem (synCopk (.cv t) (synCopk (synCsn (synCsn (.cv a))) (synCsn (.cv m))))
          syntaxClass0012)).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact freshnessCertificate0154)
  have p0027 :=
    @gN1941v (.classEq (.cv t) (synCsn (synCsn (synCsn (synCsn (.cv b))))))
      syntaxFormula0024 b (by exact freshnessCertificate0155)
  have p0028 :=
    @gBitr4i syntaxFormula0026
      (synWa (synWex b (.classEq (.cv t) (synCsn (synCsn (synCsn (synCsn (.cv b)))))))
        syntaxFormula0024)
      syntaxFormula0028 p0026 p0027
  have p0029 := @gExbii syntaxFormula0026 syntaxFormula0028 t p0028
  have p0030 := @gExcom syntaxFormula0027 b t
  have p0031 :=
    @gBitr4i syntaxFormula0029 (synWex t syntaxFormula0028) syntaxFormula0031 p0029
      p0030
  have p0032 :=
    @gN3bitri syntaxFormula0032 syntaxFormula0025 syntaxFormula0029 syntaxFormula0031
      p0023 p0024 p0031
  have p0033 := @gSnex (synCsn (synCsn (synCsn (.cv b))))
  have p0034 :=
    @gOpkeq1 (.cv t) (synCsn (synCsn (synCsn (synCsn (.cv b)))))
      (synCopk (synCsn (synCsn (.cv a))) (synCsn (.cv m)))
  have p0035 :=
    @gEleq1d (.classEq (.cv t) (synCsn (synCsn (synCsn (synCsn (.cv b))))))
      (synCopk (.cv t) (synCopk (synCsn (synCsn (.cv a))) (synCsn (.cv m))))
      syntaxClass0033 syntaxClass0012 p0034
  have freshnessCertificate0156 : t ∉ ((Class.cv b)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show t ∉ ({ b } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show t ≠ b from (by exact fresh_t_ne_b)))))
  have freshnessCertificate0157 : t ∉ ((synCsn (.cv b))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0156)
  have freshnessCertificate0158 : t ∉ ((synCsn (synCsn (.cv b)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0157)
  have freshnessCertificate0159 : t ∉ ((synCsn (synCsn (synCsn (.cv b))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0158)
  have freshnessCertificate0160 :
    t ∉ ((synCsn (synCsn (synCsn (synCsn (.cv b)))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0159)
  have freshnessCertificate0161 :
    t ∉
      (((synCsn (synCsn (synCsn (synCsn (.cv b)))))).fv) ∪
        (((synCopk (synCsn (synCsn (.cv a))) (synCsn (.cv m)))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0160 freshnessCertificate0101))
  have freshnessCertificate0162 : t ∉ (syntaxClass0033).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk];
      exact freshnessCertificate0161)
  have freshnessCertificate0163 : t ∉ ((syntaxClass0033).fv) ∪ ((syntaxClass0012).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0162 freshnessCertificate0039))
  have freshnessCertificate0164 :
    t ∉ ((Wff.classMem syntaxClass0033 syntaxClass0012)).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact freshnessCertificate0163)
  have p0036 :=
    @gCeqsexv syntaxFormula0024 syntaxFormula0034 t
      (synCsn (synCsn (synCsn (synCsn (.cv b))))) (by exact freshnessCertificate0160)
      (by exact freshnessCertificate0164) p0033 p0035
  have p0037 :=
    @gEldif syntaxClass0033 (synCins2k (synCsik (synCssetk))) syntaxClass0011
  have p0038 := @gSnex (synCsn (.cv b))
  have p0039 :=
    @gOtkelins2k (synCsn (synCsn (.cv b))) (synCsn (synCsn (.cv a)))
      (synCsn (.cv m)) (synCsik (synCssetk)) p0038 p0011 p0000
  have p0040 := @gSnex (.cv b)
  have p0041 := @gOpksnelsik (synCsn (.cv b)) (.cv m) (synCssetk) p0040 p0017
  have p0042 := @gVex b
  have p0043 := @gElssetk (.cv b) (.cv m) p0042 p0017
  have p0044_e02_recanon :
    Nominal.NPrf
      (synWb (.classMem (synCopk (synCsn (.cv b)) (.cv m)) (synCssetk)) (.objMem b m)) :=
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
      p0043
  have p0044 :=
    @gN3bitri syntaxFormula0035
      (.classMem (synCopk (synCsn (synCsn (.cv b))) (synCsn (.cv m)))
        (synCsik (synCssetk)))
      (.classMem (synCopk (synCsn (.cv b)) (.cv m)) (synCssetk)) (.objMem b m) p0039
      p0041 p0044_e02_recanon
  have p0045 :=
    @gOtkelins3k (synCsn (synCsn (.cv b))) (synCsn (synCsn (.cv a)))
      (synCsn (.cv m)) syntaxClass0010 p0038 p0011 p0000
  have p0046 := (Nominal.biimpRefl syntaxFormula0038)
  have freshnessCertificate0165 : n ∉ ((Class.cv t)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show n ∉ ({ t } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show n ≠ t from (by exact fresh_n_ne_t)))))
  have p0047 := @gElpw11c n (.cv t) (by exact freshnessCertificate0165)
  have p0048 :=
    @gAnbi1i (.classMem (.cv t) (synCpw1 (synC1c)))
      (synWex n (.classEq (.cv t) (synCsn (synCsn (.cv n))))) syntaxFormula0037 p0047
  have freshnessCertificate0166 : n ∉ ((Class.cv b)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show n ∉ ({ b } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show n ≠ b from (by exact Ne.symm dv_b_n)))))
  have freshnessCertificate0167 : n ∉ ((synCsn (.cv b))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0166)
  have freshnessCertificate0168 : n ∉ ((synCsn (synCsn (.cv b)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0167)
  have freshnessCertificate0169 : n ∉ ((Class.cv a)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show n ∉ ({ a } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show n ≠ a from (by exact Ne.symm dv_a_n)))))
  have freshnessCertificate0170 : n ∉ ((synCsn (.cv a))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0169)
  have freshnessCertificate0171 : n ∉ ((synCsn (synCsn (.cv a)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0170)
  have freshnessCertificate0172 :
    n ∉ (((synCsn (synCsn (.cv b)))).fv) ∪ (((synCsn (synCsn (.cv a)))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0168 freshnessCertificate0171))
  have freshnessCertificate0173 :
    n ∉ ((synCopk (synCsn (synCsn (.cv b))) (synCsn (synCsn (.cv a))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk];
      exact freshnessCertificate0172)
  have freshnessCertificate0174 :
    n ∉
      (((Class.cv t)).fv) ∪
        (((synCopk (synCsn (synCsn (.cv b))) (synCsn (synCsn (.cv a))))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0165 freshnessCertificate0173))
  have freshnessCertificate0175 : n ∉ (syntaxClass0036).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk];
      exact freshnessCertificate0174)
  have freshnessCertificate0176 : n ∉ ((synCnnc)).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc];
      exact (show n ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))
  have freshnessCertificate0177 : n ∉ ((synCpw1 (synCnnc))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0176)
  have freshnessCertificate0178 : n ∉ ((synCpw1 (synCpw1 (synCnnc)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0177)
  have freshnessCertificate0179 : n ∉ ((synCvv)).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv];
      exact (show n ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))
  have freshnessCertificate0180 :
    n ∉ (((synCpw1 (synCpw1 (synCnnc)))).fv) ∪ (((synCvv)).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0178 freshnessCertificate0179))
  have freshnessCertificate0181 :
    n ∉ ((synCxpk (synCpw1 (synCpw1 (synCnnc))) (synCvv))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk];
      exact freshnessCertificate0180)
  have freshnessCertificate0182 : n ∉ ((synC1c)).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c];
      exact (show n ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))
  have freshnessCertificate0183 : n ∉ ((synCpw (synC1c))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw];
      exact freshnessCertificate0182)
  have freshnessCertificate0184 : n ∉ (((synCpw (synC1c))).fv) ∪ (((synCvv)).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0183 freshnessCertificate0179))
  have freshnessCertificate0185 : n ∉ ((synCxpk (synCpw (synC1c)) (synCvv))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk];
      exact freshnessCertificate0184)
  have freshnessCertificate0186 : n ∉ ((synCssetk)).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk];
      exact (show n ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))
  have freshnessCertificate0187 : n ∉ ((synCins3k (synCssetk))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0186)
  have freshnessCertificate0188 : n ∉ ((synCsik (synCssetk))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0186)
  have freshnessCertificate0189 : n ∉ ((synCins2k (synCsik (synCssetk)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0188)
  have freshnessCertificate0190 :
    n ∉ (((synCins3k (synCssetk))).fv) ∪ (((synCins2k (synCsik (synCssetk)))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0187 freshnessCertificate0189))
  have freshnessCertificate0191 :
    n ∉
      ((synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif];
      exact freshnessCertificate0190)
  have freshnessCertificate0192 : n ∉ ((synCpw1 (synC1c))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0182)
  have freshnessCertificate0193 : n ∉ ((synCpw1 (synCpw1 (synC1c)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0192)
  have freshnessCertificate0194 : n ∉ ((synCpw1 (synCpw1 (synCpw1 (synC1c))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0193)
  have freshnessCertificate0195 :
    n ∉
      (((synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk))))).fv) ∪
        (((synCpw1 (synCpw1 (synCpw1 (synC1c))))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0191 freshnessCertificate0194))
  have freshnessCertificate0196 : n ∉ (syntaxClass0000).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak];
      exact freshnessCertificate0195)
  have freshnessCertificate0197 :
    n ∉ (((synCxpk (synCpw (synC1c)) (synCvv))).fv) ∪ ((syntaxClass0000).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0185 freshnessCertificate0196))
  have freshnessCertificate0198 : n ∉ (syntaxClass0001).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif];
      exact freshnessCertificate0197)
  have freshnessCertificate0199 : n ∉ (syntaxClass0002).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0198)
  have freshnessCertificate0200 : n ∉ (syntaxClass0003).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0199)
  have freshnessCertificate0201 :
    n ∉ ((syntaxClass0003).fv) ∪ (((synCins3k (synCssetk))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0200 freshnessCertificate0187))
  have freshnessCertificate0202 : n ∉ (syntaxClass0004).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin];
      exact freshnessCertificate0201)
  have freshnessCertificate0203 :
    n ∉ ((syntaxClass0004).fv) ∪ (((synCpw1 (synCpw1 (synC1c)))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0202 freshnessCertificate0193))
  have freshnessCertificate0204 : n ∉ (syntaxClass0005).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak];
      exact freshnessCertificate0203)
  have freshnessCertificate0205 : n ∉ (syntaxClass0006).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0204)
  have freshnessCertificate0206 : n ∉ (syntaxClass0007).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0204)
  have freshnessCertificate0207 : n ∉ ((syntaxClass0006).fv) ∪ ((syntaxClass0007).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0205 freshnessCertificate0206))
  have freshnessCertificate0208 : n ∉ (syntaxClass0008).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin];
      exact freshnessCertificate0207)
  have freshnessCertificate0209 :
    n ∉
      (((synCxpk (synCpw1 (synCpw1 (synCnnc))) (synCvv))).fv) ∪
        ((syntaxClass0008).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0181 freshnessCertificate0208))
  have freshnessCertificate0210 : n ∉ (syntaxClass0009).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin];
      exact freshnessCertificate0209)
  have freshnessCertificate0211 : n ∉ ((syntaxClass0036).fv) ∪ ((syntaxClass0009).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0175 freshnessCertificate0210))
  have freshnessCertificate0212 :
    n ∉ ((Wff.classMem syntaxClass0036 syntaxClass0009)).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact freshnessCertificate0211)
  have p0049 :=
    @gN1941v (.classEq (.cv t) (synCsn (synCsn (.cv n)))) syntaxFormula0037 n
      (by exact freshnessCertificate0212)
  have p0050 :=
    @gBitr4i syntaxFormula0039
      (synWa (synWex n (.classEq (.cv t) (synCsn (synCsn (.cv n))))) syntaxFormula0037)
      syntaxFormula0041 p0048 p0049
  have p0051 := @gExbii syntaxFormula0039 syntaxFormula0041 t p0050
  have p0052 :=
    @gBitri syntaxFormula0038 (synWex t syntaxFormula0039) syntaxFormula0042 p0046 p0051
  have p0053 := @gOpkex (synCsn (synCsn (.cv b))) (synCsn (synCsn (.cv a)))
  have freshnessCertificate0213 :
    t ∉ (((synCsn (synCsn (.cv b)))).fv) ∪ (((synCsn (synCsn (.cv a)))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0158 freshnessCertificate0099))
  have freshnessCertificate0214 :
    t ∉ ((synCopk (synCsn (synCsn (.cv b))) (synCsn (synCsn (.cv a))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk];
      exact freshnessCertificate0213)
  have p0054 :=
    @gElimak t syntaxClass0009 (synCpw1 (synC1c))
      (synCopk (synCsn (synCsn (.cv b))) (synCsn (synCsn (.cv a))))
      (by exact freshnessCertificate0034) (by exact freshnessCertificate0016)
      (by exact freshnessCertificate0214) p0053
  have p0055 := @gExcom syntaxFormula0040 n t
  have p0056 :=
    @gN3bitr4i syntaxFormula0038 syntaxFormula0042 syntaxFormula0043 syntaxFormula0045
      p0052 p0054 p0055
  have p0057 := @gSnex (synCsn (.cv n))
  have p0058 :=
    @gOpkeq1 (.cv t) (synCsn (synCsn (.cv n)))
      (synCopk (synCsn (synCsn (.cv b))) (synCsn (synCsn (.cv a))))
  have p0059 :=
    @gEleq1d (.classEq (.cv t) (synCsn (synCsn (.cv n)))) syntaxClass0036
      syntaxClass0046 syntaxClass0009 p0058
  have freshnessCertificate0215 : t ∉ ((Class.cv n)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show t ∉ ({ n } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show t ≠ n from (by exact fresh_t_ne_n)))))
  have freshnessCertificate0216 : t ∉ ((synCsn (.cv n))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0215)
  have freshnessCertificate0217 : t ∉ ((synCsn (synCsn (.cv n)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0216)
  have freshnessCertificate0218 :
    t ∉
      (((synCsn (synCsn (.cv n)))).fv) ∪
        (((synCopk (synCsn (synCsn (.cv b))) (synCsn (synCsn (.cv a))))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0217 freshnessCertificate0214))
  have freshnessCertificate0219 : t ∉ (syntaxClass0046).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk];
      exact freshnessCertificate0218)
  have freshnessCertificate0220 : t ∉ ((syntaxClass0046).fv) ∪ ((syntaxClass0009).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0219 freshnessCertificate0034))
  have freshnessCertificate0221 :
    t ∉ ((Wff.classMem syntaxClass0046 syntaxClass0009)).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact freshnessCertificate0220)
  have p0060 :=
    @gCeqsexv syntaxFormula0037 syntaxFormula0047 t (synCsn (synCsn (.cv n)))
      (by exact freshnessCertificate0217) (by exact freshnessCertificate0221) p0057 p0059
  have p0061 :=
    @gElin syntaxClass0046 (synCxpk (synCpw1 (synCpw1 (synCnnc))) (synCvv))
      syntaxClass0008
  have p0062 :=
    @gOpkelxpk (synCsn (synCsn (.cv n)))
      (synCopk (synCsn (synCsn (.cv b))) (synCsn (synCsn (.cv a))))
      (synCpw1 (synCpw1 (synCnnc))) (synCvv) p0057 p0053
  have p0063 :=
    @gMpbiran2 syntaxFormula0048
      (.classMem (synCsn (synCsn (.cv n))) (synCpw1 (synCpw1 (synCnnc))))
      (.classMem (synCopk (synCsn (synCsn (.cv b))) (synCsn (synCsn (.cv a)))) (synCvv))
      p0053 p0062
  have p0064 := @gSnelpw1 (synCsn (.cv n)) (synCpw1 (synCnnc))
  have p0065 := @gSnelpw1 (.cv n) (synCnnc)
  have p0066 :=
    @gN3bitri syntaxFormula0048
      (.classMem (synCsn (synCsn (.cv n))) (synCpw1 (synCpw1 (synCnnc))))
      (.classMem (synCsn (.cv n)) (synCpw1 (synCnnc))) (.classMem (.cv n) (synCnnc))
      p0063 p0064 p0065
  have p0067 := @gElin syntaxClass0046 syntaxClass0006 syntaxClass0007
  have p0068 := @gVex n
  have p0069 :=
    @gOtkelins2k (.cv n) (synCsn (synCsn (.cv b))) (synCsn (synCsn (.cv a)))
      syntaxClass0005 p0068 p0038 p0011
  have p0070 := @gOpkex (.cv n) (synCsn (synCsn (.cv a)))
  have freshnessCertificate0222 :
    t ∉ (((Class.cv n)).fv) ∪ (((synCsn (synCsn (.cv a)))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0215 freshnessCertificate0099))
  have freshnessCertificate0223 :
    t ∉ ((synCopk (.cv n) (synCsn (synCsn (.cv a))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk];
      exact freshnessCertificate0222)
  have p0071 :=
    @gElimak t syntaxClass0004 (synCpw1 (synCpw1 (synC1c)))
      (synCopk (.cv n) (synCsn (synCsn (.cv a)))) (by exact freshnessCertificate0026)
      (by exact freshnessCertificate0017) (by exact freshnessCertificate0223) p0070
  have p0072 := (Nominal.biimpRefl syntaxFormula0050)
  have freshnessCertificate0224 : x ∉ ((Class.cv t)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show x ∉ ({ t } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show x ≠ t from (by exact fresh_x_ne_t)))))
  have p0073 := @gElpw121c x (.cv t) (by exact freshnessCertificate0224)
  have p0074 :=
    @gAnbi1i (.classMem (.cv t) (synCpw1 (synCpw1 (synC1c))))
      (synWex x (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv x))))))
      syntaxFormula0049 p0073
  have freshnessCertificate0225 : x ∉ ((Class.cv n)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show x ∉ ({ n } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show x ≠ n from (by exact fresh_x_ne_n)))))
  have freshnessCertificate0226 : x ∉ ((Class.cv a)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show x ∉ ({ a } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show x ≠ a from (by exact fresh_x_ne_a)))))
  have freshnessCertificate0227 : x ∉ ((synCsn (.cv a))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0226)
  have freshnessCertificate0228 : x ∉ ((synCsn (synCsn (.cv a)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0227)
  have freshnessCertificate0229 :
    x ∉ (((Class.cv n)).fv) ∪ (((synCsn (synCsn (.cv a)))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0225 freshnessCertificate0228))
  have freshnessCertificate0230 :
    x ∉ ((synCopk (.cv n) (synCsn (synCsn (.cv a))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk];
      exact freshnessCertificate0229)
  have freshnessCertificate0231 :
    x ∉ (((Class.cv t)).fv) ∪ (((synCopk (.cv n) (synCsn (synCsn (.cv a))))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0224 freshnessCertificate0230))
  have freshnessCertificate0232 :
    x ∉ ((synCopk (.cv t) (synCopk (.cv n) (synCsn (synCsn (.cv a)))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk];
      exact freshnessCertificate0231)
  have freshnessCertificate0233 : x ∉ ((synC1c)).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c];
      exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))
  have freshnessCertificate0234 : x ∉ ((synCpw (synC1c))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw];
      exact freshnessCertificate0233)
  have freshnessCertificate0235 : x ∉ ((synCvv)).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv];
      exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))
  have freshnessCertificate0236 : x ∉ (((synCpw (synC1c))).fv) ∪ (((synCvv)).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0234 freshnessCertificate0235))
  have freshnessCertificate0237 : x ∉ ((synCxpk (synCpw (synC1c)) (synCvv))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk];
      exact freshnessCertificate0236)
  have freshnessCertificate0238 : x ∉ ((synCssetk)).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk];
      exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))
  have freshnessCertificate0239 : x ∉ ((synCins3k (synCssetk))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0238)
  have freshnessCertificate0240 : x ∉ ((synCsik (synCssetk))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0238)
  have freshnessCertificate0241 : x ∉ ((synCins2k (synCsik (synCssetk)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0240)
  have freshnessCertificate0242 :
    x ∉ (((synCins3k (synCssetk))).fv) ∪ (((synCins2k (synCsik (synCssetk)))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0239 freshnessCertificate0241))
  have freshnessCertificate0243 :
    x ∉
      ((synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif];
      exact freshnessCertificate0242)
  have freshnessCertificate0244 : x ∉ ((synCpw1 (synC1c))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0233)
  have freshnessCertificate0245 : x ∉ ((synCpw1 (synCpw1 (synC1c)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0244)
  have freshnessCertificate0246 : x ∉ ((synCpw1 (synCpw1 (synCpw1 (synC1c))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0245)
  have freshnessCertificate0247 :
    x ∉
      (((synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk))))).fv) ∪
        (((synCpw1 (synCpw1 (synCpw1 (synC1c))))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0243 freshnessCertificate0246))
  have freshnessCertificate0248 : x ∉ (syntaxClass0000).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak];
      exact freshnessCertificate0247)
  have freshnessCertificate0249 :
    x ∉ (((synCxpk (synCpw (synC1c)) (synCvv))).fv) ∪ ((syntaxClass0000).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0237 freshnessCertificate0248))
  have freshnessCertificate0250 : x ∉ (syntaxClass0001).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif];
      exact freshnessCertificate0249)
  have freshnessCertificate0251 : x ∉ (syntaxClass0002).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0250)
  have freshnessCertificate0252 : x ∉ (syntaxClass0003).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0251)
  have freshnessCertificate0253 :
    x ∉ ((syntaxClass0003).fv) ∪ (((synCins3k (synCssetk))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0252 freshnessCertificate0239))
  have freshnessCertificate0254 : x ∉ (syntaxClass0004).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin];
      exact freshnessCertificate0253)
  have freshnessCertificate0255 :
    x ∉
      (((synCopk (.cv t) (synCopk (.cv n) (synCsn (synCsn (.cv a)))))).fv) ∪
        ((syntaxClass0004).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0232 freshnessCertificate0254))
  have freshnessCertificate0256 :
    x ∉
      ((Wff.classMem (synCopk (.cv t) (synCopk (.cv n) (synCsn (synCsn (.cv a)))))
          syntaxClass0004)).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact freshnessCertificate0255)
  have p0075 :=
    @gN1941v (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv x))))) syntaxFormula0049
      x (by exact freshnessCertificate0256)
  have p0076 :=
    @gBitr4i syntaxFormula0051
      (synWa (synWex x (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv x))))))
        syntaxFormula0049)
      syntaxFormula0053 p0074 p0075
  have p0077 := @gExbii syntaxFormula0051 syntaxFormula0053 t p0076
  have p0078 := @gExcom syntaxFormula0052 x t
  have p0079 :=
    @gBitr4i syntaxFormula0054 (synWex t syntaxFormula0053) syntaxFormula0056 p0077
      p0078
  have p0080 :=
    @gN3bitri syntaxFormula0057 syntaxFormula0050 syntaxFormula0054 syntaxFormula0056
      p0071 p0072 p0079
  have p0081 := @gSnex (synCsn (synCsn (.cv x)))
  have p0082 :=
    @gOpkeq1 (.cv t) (synCsn (synCsn (synCsn (.cv x))))
      (synCopk (.cv n) (synCsn (synCsn (.cv a))))
  have p0083 :=
    @gEleq1d (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv x)))))
      (synCopk (.cv t) (synCopk (.cv n) (synCsn (synCsn (.cv a))))) syntaxClass0058
      syntaxClass0004 p0082
  have freshnessCertificate0257 : t ∉ ((Class.cv x)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show t ∉ ({ x } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show t ≠ x from (by exact fresh_t_ne_x)))))
  have freshnessCertificate0258 : t ∉ ((synCsn (.cv x))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0257)
  have freshnessCertificate0259 : t ∉ ((synCsn (synCsn (.cv x)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0258)
  have freshnessCertificate0260 : t ∉ ((synCsn (synCsn (synCsn (.cv x))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0259)
  have freshnessCertificate0261 :
    t ∉
      (((synCsn (synCsn (synCsn (.cv x))))).fv) ∪
        (((synCopk (.cv n) (synCsn (synCsn (.cv a))))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0260 freshnessCertificate0223))
  have freshnessCertificate0262 : t ∉ (syntaxClass0058).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk];
      exact freshnessCertificate0261)
  have freshnessCertificate0263 : t ∉ ((syntaxClass0058).fv) ∪ ((syntaxClass0004).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0262 freshnessCertificate0026))
  have freshnessCertificate0264 :
    t ∉ ((Wff.classMem syntaxClass0058 syntaxClass0004)).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact freshnessCertificate0263)
  have p0084 :=
    @gCeqsexv syntaxFormula0049 syntaxFormula0059 t (synCsn (synCsn (synCsn (.cv x))))
      (by exact freshnessCertificate0260) (by exact freshnessCertificate0264) p0081 p0083
  have p0085 := @gElin syntaxClass0058 syntaxClass0003 (synCins3k (synCssetk))
  have p0086 := @gSnex (.cv x)
  have p0087 :=
    @gOtkelins2k (synCsn (.cv x)) (.cv n) (synCsn (synCsn (.cv a))) syntaxClass0002
      p0086 p0068 p0011
  have p0088 := @gVex x
  have p0089 := @gOpksnelsik (.cv x) (synCsn (.cv a)) syntaxClass0001 p0088 p0016
  have p0090 := @gEqpw1relk (.cv x) (.cv a) p0088 p0019
  have p0091 :=
    @gN3bitri syntaxFormula0060
      (.classMem (synCopk (synCsn (.cv x)) (synCsn (synCsn (.cv a)))) syntaxClass0002)
      (.classMem (synCopk (.cv x) (synCsn (.cv a))) syntaxClass0001)
      (.classEq (.cv x) (synCpw1 (.cv a))) p0087 p0089 p0090
  have p0092 :=
    @gOtkelins3k (synCsn (.cv x)) (.cv n) (synCsn (synCsn (.cv a))) (synCssetk) p0086
      p0068 p0011
  have p0093 := @gElssetk (.cv x) (.cv n) p0088 p0068
  have p0094_e01_recanon :
    Nominal.NPrf
      (synWb (.classMem (synCopk (synCsn (.cv x)) (.cv n)) (synCssetk)) (.objMem x n)) :=
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
      p0093
  have p0094 :=
    @gBitri syntaxFormula0061
      (.classMem (synCopk (synCsn (.cv x)) (.cv n)) (synCssetk)) (.objMem x n) p0092
      p0094_e01_recanon
  have p0095 :=
    @gAnbi12i syntaxFormula0060 (.classEq (.cv x) (synCpw1 (.cv a))) syntaxFormula0061
      (.objMem x n) p0091 p0094
  have p0096 :=
    @gN3bitri syntaxFormula0055 syntaxFormula0059
      (synWa syntaxFormula0060 syntaxFormula0061)
      (synWa (.classEq (.cv x) (synCpw1 (.cv a))) (.objMem x n)) p0084 p0085 p0095
  have p0097 :=
    @gExbii syntaxFormula0055
      (synWa (.classEq (.cv x) (synCpw1 (.cv a))) (.objMem x n)) x p0096
  have freshnessCertificate0265 : x ∉ ((synCpw1 (.cv a))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0226)
  have p0098 :=
    (NFChoice.DirectNominalPrf.Nominal.DefinitionLeafHandlersCanonical001.dfClelOfDV x
      (synCpw1 (.cv a)) (.cv n) (by exact freshnessCertificate0265)
      (by exact freshnessCertificate0225))
  have p0099_e01_recanon :
    Nominal.NPrf
      (synWb (.classMem (synCpw1 (.cv a)) (.cv n))
        (synWex x (synWa (.classEq (.cv x) (synCpw1 (.cv a))) (.objMem x n)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [synWb, synCpw1, synCin, synCcompl, synCnin, synWnan, synWa,
          synCpw, synWss, synC1c, synWex, synCsn]
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
      p0098
  have p0099 :=
    @gBitr4i syntaxFormula0056
      (synWex x (synWa (.classEq (.cv x) (synCpw1 (.cv a))) (.objMem x n)))
      (.classMem (synCpw1 (.cv a)) (.cv n)) p0097 p0099_e01_recanon
  have p0100 :=
    @gN3bitri syntaxFormula0062 syntaxFormula0057 syntaxFormula0056
      (.classMem (synCpw1 (.cv a)) (.cv n)) p0069 p0080 p0099
  have p0101 := @gOpkex (.cv n) (synCsn (synCsn (.cv b)))
  have freshnessCertificate0266 :
    t ∉ (((Class.cv n)).fv) ∪ (((synCsn (synCsn (.cv b)))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0215 freshnessCertificate0158))
  have freshnessCertificate0267 :
    t ∉ ((synCopk (.cv n) (synCsn (synCsn (.cv b))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk];
      exact freshnessCertificate0266)
  have p0102 :=
    @gElimak t syntaxClass0004 (synCpw1 (synCpw1 (synC1c)))
      (synCopk (.cv n) (synCsn (synCsn (.cv b)))) (by exact freshnessCertificate0026)
      (by exact freshnessCertificate0017) (by exact freshnessCertificate0267) p0101
  have p0103 :=
    @gAnbi1i (.classMem (.cv t) (synCpw1 (synCpw1 (synC1c))))
      (synWex x (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv x))))))
      syntaxFormula0063 p0073
  have freshnessCertificate0268 : x ∉ ((Class.cv b)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show x ∉ ({ b } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show x ≠ b from (by exact fresh_x_ne_b)))))
  have freshnessCertificate0269 : x ∉ ((synCsn (.cv b))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0268)
  have freshnessCertificate0270 : x ∉ ((synCsn (synCsn (.cv b)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0269)
  have freshnessCertificate0271 :
    x ∉ (((Class.cv n)).fv) ∪ (((synCsn (synCsn (.cv b)))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0225 freshnessCertificate0270))
  have freshnessCertificate0272 :
    x ∉ ((synCopk (.cv n) (synCsn (synCsn (.cv b))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk];
      exact freshnessCertificate0271)
  have freshnessCertificate0273 :
    x ∉ (((Class.cv t)).fv) ∪ (((synCopk (.cv n) (synCsn (synCsn (.cv b))))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0224 freshnessCertificate0272))
  have freshnessCertificate0274 :
    x ∉ ((synCopk (.cv t) (synCopk (.cv n) (synCsn (synCsn (.cv b)))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk];
      exact freshnessCertificate0273)
  have freshnessCertificate0275 :
    x ∉
      (((synCopk (.cv t) (synCopk (.cv n) (synCsn (synCsn (.cv b)))))).fv) ∪
        ((syntaxClass0004).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0274 freshnessCertificate0254))
  have freshnessCertificate0276 :
    x ∉
      ((Wff.classMem (synCopk (.cv t) (synCopk (.cv n) (synCsn (synCsn (.cv b)))))
          syntaxClass0004)).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact freshnessCertificate0275)
  have p0104 :=
    @gN1941v (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv x))))) syntaxFormula0063
      x (by exact freshnessCertificate0276)
  have p0105 :=
    @gBitr4i syntaxFormula0064
      (synWa (synWex x (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv x))))))
        syntaxFormula0063)
      syntaxFormula0066 p0103 p0104
  have p0106 := @gExbii syntaxFormula0064 syntaxFormula0066 t p0105
  have p0107 := (Nominal.biimpRefl syntaxFormula0067)
  have p0108 := @gExcom syntaxFormula0065 x t
  have p0109 :=
    @gN3bitr4i (synWex t syntaxFormula0064) (synWex t syntaxFormula0066)
      syntaxFormula0067 syntaxFormula0069 p0106 p0107 p0108
  have p0110 :=
    @gOpkeq1 (.cv t) (synCsn (synCsn (synCsn (.cv x))))
      (synCopk (.cv n) (synCsn (synCsn (.cv b))))
  have p0111 :=
    @gEleq1d (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv x)))))
      (synCopk (.cv t) (synCopk (.cv n) (synCsn (synCsn (.cv b))))) syntaxClass0070
      syntaxClass0004 p0110
  have freshnessCertificate0277 :
    t ∉
      (((synCsn (synCsn (synCsn (.cv x))))).fv) ∪
        (((synCopk (.cv n) (synCsn (synCsn (.cv b))))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0260 freshnessCertificate0267))
  have freshnessCertificate0278 : t ∉ (syntaxClass0070).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk];
      exact freshnessCertificate0277)
  have freshnessCertificate0279 : t ∉ ((syntaxClass0070).fv) ∪ ((syntaxClass0004).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0278 freshnessCertificate0026))
  have freshnessCertificate0280 :
    t ∉ ((Wff.classMem syntaxClass0070 syntaxClass0004)).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact freshnessCertificate0279)
  have p0112 :=
    @gCeqsexv syntaxFormula0063 syntaxFormula0071 t (synCsn (synCsn (synCsn (.cv x))))
      (by exact freshnessCertificate0260) (by exact freshnessCertificate0280) p0081 p0111
  have p0113 := @gElin syntaxClass0070 syntaxClass0003 (synCins3k (synCssetk))
  have p0114 :=
    @gOtkelins2k (synCsn (.cv x)) (.cv n) (synCsn (synCsn (.cv b))) syntaxClass0002
      p0086 p0068 p0038
  have p0115 := @gOpksnelsik (.cv x) (synCsn (.cv b)) syntaxClass0001 p0088 p0040
  have p0116 := @gEqpw1relk (.cv x) (.cv b) p0088 p0042
  have p0117 :=
    @gN3bitri syntaxFormula0072
      (.classMem (synCopk (synCsn (.cv x)) (synCsn (synCsn (.cv b)))) syntaxClass0002)
      (.classMem (synCopk (.cv x) (synCsn (.cv b))) syntaxClass0001)
      (.classEq (.cv x) (synCpw1 (.cv b))) p0114 p0115 p0116
  have p0118 :=
    @gOtkelins3k (synCsn (.cv x)) (.cv n) (synCsn (synCsn (.cv b))) (synCssetk) p0086
      p0068 p0038
  have p0119_e01_recanon :
    Nominal.NPrf
      (synWb (.classMem (synCopk (synCsn (.cv x)) (.cv n)) (synCssetk)) (.objMem x n)) :=
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
      p0093
  have p0119 :=
    @gBitri syntaxFormula0073
      (.classMem (synCopk (synCsn (.cv x)) (.cv n)) (synCssetk)) (.objMem x n) p0118
      p0119_e01_recanon
  have p0120 :=
    @gAnbi12i syntaxFormula0072 (.classEq (.cv x) (synCpw1 (.cv b))) syntaxFormula0073
      (.objMem x n) p0117 p0119
  have p0121 :=
    @gN3bitri syntaxFormula0068 syntaxFormula0071
      (synWa syntaxFormula0072 syntaxFormula0073)
      (synWa (.classEq (.cv x) (synCpw1 (.cv b))) (.objMem x n)) p0112 p0113 p0120
  have p0122 :=
    @gExbii syntaxFormula0068
      (synWa (.classEq (.cv x) (synCpw1 (.cv b))) (.objMem x n)) x p0121
  have p0123 :=
    @gN3bitri syntaxFormula0074 syntaxFormula0067 syntaxFormula0069
      (synWex x (synWa (.classEq (.cv x) (synCpw1 (.cv b))) (.objMem x n))) p0102 p0109
      p0122
  have p0124 :=
    @gOtkelins3k (.cv n) (synCsn (synCsn (.cv b))) (synCsn (synCsn (.cv a)))
      syntaxClass0005 p0068 p0038 p0011
  have freshnessCertificate0281 : x ∉ ((synCpw1 (.cv b))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0268)
  have p0125 :=
    (NFChoice.DirectNominalPrf.Nominal.DefinitionLeafHandlersCanonical001.dfClelOfDV x
      (synCpw1 (.cv b)) (.cv n) (by exact freshnessCertificate0281)
      (by exact freshnessCertificate0225))
  have p0126_e02_recanon :
    Nominal.NPrf
      (synWb (.classMem (synCpw1 (.cv b)) (.cv n))
        (synWex x (synWa (.classEq (.cv x) (synCpw1 (.cv b))) (.objMem x n)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [synWb, synCpw1, synCin, synCcompl, synCnin, synWnan, synWa,
          synCpw, synWss, synC1c, synWex, synCsn]
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
      p0125
  have p0126 :=
    @gN3bitr4i syntaxFormula0074
      (synWex x (synWa (.classEq (.cv x) (synCpw1 (.cv b))) (.objMem x n)))
      syntaxFormula0075 (.classMem (synCpw1 (.cv b)) (.cv n)) p0123 p0124
      p0126_e02_recanon
  have p0127 :=
    @gAnbi12i syntaxFormula0062 (.classMem (synCpw1 (.cv a)) (.cv n)) syntaxFormula0075
      (.classMem (synCpw1 (.cv b)) (.cv n)) p0100 p0126
  have p0128 :=
    @gBitri syntaxFormula0076 (synWa syntaxFormula0062 syntaxFormula0075)
      syntaxFormula0077 p0067 p0127
  have p0129 :=
    @gAnbi12i syntaxFormula0048 (.classMem (.cv n) (synCnnc)) syntaxFormula0076
      syntaxFormula0077 p0066 p0128
  have p0130 :=
    @gN3bitri syntaxFormula0044 syntaxFormula0047
      (synWa syntaxFormula0048 syntaxFormula0076) syntaxFormula0078 p0060 p0061 p0129
  have p0131 := @gExbii syntaxFormula0044 syntaxFormula0078 n p0130
  have p0132 := (Nominal.biimpRefl syntaxFormula0079)
  have p0133 :=
    @gBitr4i syntaxFormula0045 (synWex n syntaxFormula0078) syntaxFormula0079 p0131
      p0132
  have p0134 :=
    @gN3bitri syntaxFormula0080 syntaxFormula0043 syntaxFormula0045 syntaxFormula0079
      p0045 p0056 p0133
  have p0135 := @gNotbii syntaxFormula0080 syntaxFormula0079 p0134
  have p0136 :=
    @gAnbi12i syntaxFormula0035 (.objMem b m) syntaxFormula0081 syntaxFormula0082 p0044
      p0135
  have p0137 :=
    @gN3bitri syntaxFormula0030 syntaxFormula0034
      (synWa syntaxFormula0035 syntaxFormula0081)
      (synWa (.objMem b m) syntaxFormula0082) p0036 p0037 p0136
  have p0138 :=
    @gExbii syntaxFormula0030 (synWa (.objMem b m) syntaxFormula0082) b p0137
  have p0139 := (Nominal.biimpRefl syntaxFormula0083)
  have p0140_e01_recanon :
    Nominal.NPrf
      (synWb syntaxFormula0083 (synWex b (synWa (.objMem b m) syntaxFormula0082))) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [synWb, synWex, synWa]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0139
  have p0140 :=
    @gBitr4i syntaxFormula0031 (synWex b (synWa (.objMem b m) syntaxFormula0082))
      syntaxFormula0083 p0138 p0140_e01_recanon
  have p0141 := @gRexnal syntaxFormula0079 b (.cv m)
  have p0142 :=
    @gN3bitri syntaxFormula0032 syntaxFormula0031 syntaxFormula0083 syntaxFormula0085
      p0032 p0140 p0141
  have p0143 :=
    @gAnbi12i
      (.classMem (synCopk (synCsn (synCsn (.cv a))) (synCsn (.cv m)))
        (synCsik (synCssetk)))
      (.objMem a m) syntaxFormula0032 syntaxFormula0085 p0021 p0142
  have p0144 :=
    @gN3bitri syntaxFormula0021 syntaxFormula0023
      (synWa (.classMem (synCopk (synCsn (synCsn (.cv a))) (synCsn (.cv m)))
          (synCsik (synCssetk))) syntaxFormula0032)
      (synWa (.objMem a m) syntaxFormula0085) p0014 p0015 p0143
  have p0145 :=
    @gExbii syntaxFormula0021 (synWa (.objMem a m) syntaxFormula0085) a p0144
  have p0146 := (Nominal.biimpRefl syntaxFormula0086)
  have p0147_e01_recanon :
    Nominal.NPrf
      (synWb syntaxFormula0086 (synWex a (synWa (.objMem a m) syntaxFormula0085))) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [synWb, synWex, synWa]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0146
  have p0147 :=
    @gBitr4i syntaxFormula0022 (synWex a (synWa (.objMem a m) syntaxFormula0085))
      syntaxFormula0086 p0145 p0147_e01_recanon
  have p0148 :=
    @gN3bitri syntaxFormula0087 syntaxFormula0020 syntaxFormula0022 syntaxFormula0086
      p0002 p0010 p0147
  have p0149 :=
    @gXchbinx syntaxFormula0089 syntaxFormula0087 syntaxFormula0086 p0001 p0148
  have p0150 := @gEluni1 (.cv m) syntaxClass0088 p0017
  have p0151 := @gDfral2 syntaxFormula0084 a (.cv m)
  have p0152 :=
    @gN3bitr4i syntaxFormula0089 (.neg syntaxFormula0086)
      (.classMem (.cv m) syntaxClass0090) syntaxFormula0091 p0149 p0150 p0151
  have freshnessCertificate0282 : m ∉ ((synCssetk)).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk];
      exact (show m ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))
  have freshnessCertificate0283 : m ∉ ((synCsik (synCssetk))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0282)
  have freshnessCertificate0284 : m ∉ ((synCins2k (synCsik (synCssetk)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0283)
  have freshnessCertificate0285 : m ∉ ((synCnnc)).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc];
      exact (show m ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))
  have freshnessCertificate0286 : m ∉ ((synCpw1 (synCnnc))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0285)
  have freshnessCertificate0287 : m ∉ ((synCpw1 (synCpw1 (synCnnc)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0286)
  have freshnessCertificate0288 : m ∉ ((synCvv)).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv];
      exact (show m ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))
  have freshnessCertificate0289 :
    m ∉ (((synCpw1 (synCpw1 (synCnnc)))).fv) ∪ (((synCvv)).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0287 freshnessCertificate0288))
  have freshnessCertificate0290 :
    m ∉ ((synCxpk (synCpw1 (synCpw1 (synCnnc))) (synCvv))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk];
      exact freshnessCertificate0289)
  have freshnessCertificate0291 : m ∉ ((synC1c)).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c];
      exact (show m ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))
  have freshnessCertificate0292 : m ∉ ((synCpw (synC1c))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw];
      exact freshnessCertificate0291)
  have freshnessCertificate0293 : m ∉ (((synCpw (synC1c))).fv) ∪ (((synCvv)).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0292 freshnessCertificate0288))
  have freshnessCertificate0294 : m ∉ ((synCxpk (synCpw (synC1c)) (synCvv))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk];
      exact freshnessCertificate0293)
  have freshnessCertificate0295 : m ∉ ((synCins3k (synCssetk))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0282)
  have freshnessCertificate0296 :
    m ∉ (((synCins3k (synCssetk))).fv) ∪ (((synCins2k (synCsik (synCssetk)))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0295 freshnessCertificate0284))
  have freshnessCertificate0297 :
    m ∉
      ((synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif];
      exact freshnessCertificate0296)
  have freshnessCertificate0298 : m ∉ ((synCpw1 (synC1c))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0291)
  have freshnessCertificate0299 : m ∉ ((synCpw1 (synCpw1 (synC1c)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0298)
  have freshnessCertificate0300 : m ∉ ((synCpw1 (synCpw1 (synCpw1 (synC1c))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0299)
  have freshnessCertificate0301 :
    m ∉
      (((synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk))))).fv) ∪
        (((synCpw1 (synCpw1 (synCpw1 (synC1c))))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0297 freshnessCertificate0300))
  have freshnessCertificate0302 : m ∉ (syntaxClass0000).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak];
      exact freshnessCertificate0301)
  have freshnessCertificate0303 :
    m ∉ (((synCxpk (synCpw (synC1c)) (synCvv))).fv) ∪ ((syntaxClass0000).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0294 freshnessCertificate0302))
  have freshnessCertificate0304 : m ∉ (syntaxClass0001).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif];
      exact freshnessCertificate0303)
  have freshnessCertificate0305 : m ∉ (syntaxClass0002).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0304)
  have freshnessCertificate0306 : m ∉ (syntaxClass0003).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0305)
  have freshnessCertificate0307 :
    m ∉ ((syntaxClass0003).fv) ∪ (((synCins3k (synCssetk))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0306 freshnessCertificate0295))
  have freshnessCertificate0308 : m ∉ (syntaxClass0004).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin];
      exact freshnessCertificate0307)
  have freshnessCertificate0309 :
    m ∉ ((syntaxClass0004).fv) ∪ (((synCpw1 (synCpw1 (synC1c)))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0308 freshnessCertificate0299))
  have freshnessCertificate0310 : m ∉ (syntaxClass0005).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak];
      exact freshnessCertificate0309)
  have freshnessCertificate0311 : m ∉ (syntaxClass0006).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0310)
  have freshnessCertificate0312 : m ∉ (syntaxClass0007).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0310)
  have freshnessCertificate0313 : m ∉ ((syntaxClass0006).fv) ∪ ((syntaxClass0007).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0311 freshnessCertificate0312))
  have freshnessCertificate0314 : m ∉ (syntaxClass0008).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin];
      exact freshnessCertificate0313)
  have freshnessCertificate0315 :
    m ∉
      (((synCxpk (synCpw1 (synCpw1 (synCnnc))) (synCvv))).fv) ∪
        ((syntaxClass0008).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0290 freshnessCertificate0314))
  have freshnessCertificate0316 : m ∉ (syntaxClass0009).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin];
      exact freshnessCertificate0315)
  have freshnessCertificate0317 :
    m ∉ ((syntaxClass0009).fv) ∪ (((synCpw1 (synC1c))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0316 freshnessCertificate0298))
  have freshnessCertificate0318 : m ∉ (syntaxClass0010).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak];
      exact freshnessCertificate0317)
  have freshnessCertificate0319 : m ∉ (syntaxClass0011).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0318)
  have freshnessCertificate0320 :
    m ∉ (((synCins2k (synCsik (synCssetk)))).fv) ∪ ((syntaxClass0011).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0284 freshnessCertificate0319))
  have freshnessCertificate0321 : m ∉ (syntaxClass0012).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif];
      exact freshnessCertificate0320)
  have freshnessCertificate0322 :
    m ∉ ((syntaxClass0012).fv) ∪ (((synCpw1 (synCpw1 (synCpw1 (synC1c))))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0321 freshnessCertificate0300))
  have freshnessCertificate0323 : m ∉ (syntaxClass0013).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak];
      exact freshnessCertificate0322)
  have freshnessCertificate0324 :
    m ∉ (((synCsik (synCssetk))).fv) ∪ ((syntaxClass0013).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0283 freshnessCertificate0323))
  have freshnessCertificate0325 : m ∉ (syntaxClass0014).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin];
      exact freshnessCertificate0324)
  have freshnessCertificate0326 :
    m ∉ ((syntaxClass0014).fv) ∪ (((synCpw1 (synC1c))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0325 freshnessCertificate0298))
  have freshnessCertificate0327 : m ∉ (syntaxClass0015).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak];
      exact freshnessCertificate0326)
  have freshnessCertificate0328 : m ∉ (syntaxClass0088).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl];
      exact freshnessCertificate0327)
  have freshnessCertificate0329 : m ∉ (syntaxClass0090).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni1];
      exact freshnessCertificate0328)
  have p0153 :=
    @gEqabi syntaxFormula0091 m syntaxClass0090 (by exact freshnessCertificate0329) p0152
  have p0154 := @gSsetkex
  have p0155 := @gSikex (synCssetk) p0154
  have p0156 := @gIns2kex (synCsik (synCssetk)) p0155
  have p0157 := @gNncex
  have p0158 := @gPw1ex (synCnnc) p0157
  have p0159 := @gPw1ex (synCpw1 (synCnnc)) p0158
  have p0160 := @gVvex
  have p0161 := @gXpkex (synCpw1 (synCpw1 (synCnnc))) (synCvv) p0159 p0160
  have p0162 := @gN1cex
  have p0163 := @gPwex (synC1c) p0162
  have p0165 := @gXpkex (synCpw (synC1c)) (synCvv) p0163 p0160
  have p0167 := @gIns3kex (synCssetk) p0154
  have p0168 :=
    @gSymdifex (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk))) p0167 p0156
  have p0170 := @gPw1ex (synC1c) p0162
  have p0171 := @gPw1ex (synCpw1 (synC1c)) p0170
  have p0172 := @gPw1ex (synCpw1 (synCpw1 (synC1c))) p0171
  have p0173 :=
    @gImakex (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk))))
      (synCpw1 (synCpw1 (synCpw1 (synC1c)))) p0168 p0172
  have p0174 :=
    @gDifex (synCxpk (synCpw (synC1c)) (synCvv)) syntaxClass0000 p0165 p0173
  have p0175 := @gSikex syntaxClass0001 p0174
  have p0176 := @gIns2kex syntaxClass0002 p0175
  have p0177 := @gInex syntaxClass0003 (synCins3k (synCssetk)) p0176 p0167
  have p0178 := @gImakex syntaxClass0004 (synCpw1 (synCpw1 (synC1c))) p0177 p0171
  have p0179 := @gIns2kex syntaxClass0005 p0178
  have p0180 := @gIns3kex syntaxClass0005 p0178
  have p0181 := @gInex syntaxClass0006 syntaxClass0007 p0179 p0180
  have p0182 :=
    @gInex (synCxpk (synCpw1 (synCpw1 (synCnnc))) (synCvv)) syntaxClass0008 p0161
      p0181
  have p0183 := @gImakex syntaxClass0009 (synCpw1 (synC1c)) p0182 p0170
  have p0184 := @gIns3kex syntaxClass0010 p0183
  have p0185 := @gDifex (synCins2k (synCsik (synCssetk))) syntaxClass0011 p0156 p0184
  have p0186 :=
    @gImakex syntaxClass0012 (synCpw1 (synCpw1 (synCpw1 (synC1c)))) p0185 p0172
  have p0187 := @gInex (synCsik (synCssetk)) syntaxClass0013 p0155 p0186
  have p0188 := @gImakex syntaxClass0014 (synCpw1 (synC1c)) p0187 p0170
  have p0189 := @gComplex syntaxClass0015 p0188
  have p0190 := @gUni1ex syntaxClass0088 p0189
  have p0191 :=
    @gEqeltrri syntaxClass0090 (.cab m syntaxFormula0091) (synCvv) p0153 p0190
  exact p0191


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk009StructuralPart049`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_ncfinraise`. -/
@[expose]
noncomputable def gNcfinraise (A : Class) (B : Class) (n : Var) (M : Class)
    (dv_A_n : n ∉ A.fv) (dv_B_n : n ∉ B.fv) :
    Nominal.NPrf
      (.imp (synW3a (.classMem M (synCnnc)) (.classMem A M) (.classMem B M))
        (synWrex n (synCnnc)
          (synWa (.classMem (synCpw1 A) (.cv n)) (.classMem (synCpw1 B) (.cv n))))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ ({ n } : Finset Var) ∪ M.fv
  let a : Var := freshVar proofSupport 0
  let b : Var := freshVar proofSupport 1
  let m : Var := freshVar proofSupport 2
  let k : Var := freshVar proofSupport 3
  let c : Var := freshVar proofSupport 4
  let x : Var := freshVar proofSupport 5
  let d : Var := freshVar proofSupport 6
  let y : Var := freshVar proofSupport 7
  have fresh_a : a ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_a_not_A : a ∉ A.fv := by
    intro h
    exact
      fresh_a
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_a_ne_n : a ≠ n := by
    intro h
    exact
      fresh_a
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_n_ne_a : n ≠ a := Ne.symm fresh_a_ne_n
  have fresh_a_not_M : a ∉ M.fv := by
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
  have fresh_b_ne_n : b ≠ n := by
    intro h
    exact
      fresh_b
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_n_ne_b : n ≠ b := Ne.symm fresh_b_ne_n
  have fresh_b_not_M : b ∉ M.fv := by
    intro h
    exact fresh_b (Finset.mem_union_right _ (h))
  have fresh_m : m ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_m_ne_n : m ≠ n := by
    intro h
    exact
      fresh_m
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_n_ne_m : n ≠ m := Ne.symm fresh_m_ne_n
  have fresh_m_not_M : m ∉ M.fv := by
    intro h
    exact fresh_m (Finset.mem_union_right _ (h))
  have fresh_k : k ∉ proofSupport :=
    by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_k_ne_n : k ≠ n := by
    intro h
    exact
      fresh_k
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_n_ne_k : n ≠ k := Ne.symm fresh_k_ne_n
  have fresh_c : c ∉ proofSupport :=
    by
    change freshVar proofSupport 4 ∉ proofSupport
    exact freshVar_not_mem proofSupport 4
  have fresh_c_ne_n : c ≠ n := by
    intro h
    exact
      fresh_c
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_n_ne_c : n ≠ c := Ne.symm fresh_c_ne_n
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 5 ∉ proofSupport
    exact freshVar_not_mem proofSupport 5
  have fresh_x_ne_n : x ≠ n := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_n_ne_x : n ≠ x := Ne.symm fresh_x_ne_n
  have fresh_d : d ∉ proofSupport :=
    by
    change freshVar proofSupport 6 ∉ proofSupport
    exact freshVar_not_mem proofSupport 6
  have fresh_d_ne_n : d ≠ n := by
    intro h
    exact
      fresh_d
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_n_ne_d : n ≠ d := Ne.symm fresh_d_ne_n
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 7 ∉ proofSupport
    exact freshVar_not_mem proofSupport 7
  have fresh_y_ne_n : y ≠ n := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_n_ne_y : n ≠ y := Ne.symm fresh_y_ne_n
  have fresh_a_ne_b : a ≠ b :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_b_ne_a : b ≠ a := Ne.symm fresh_a_ne_b
  have fresh_a_ne_m : a ≠ m :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_m_ne_a : m ≠ a := Ne.symm fresh_a_ne_m
  have fresh_a_ne_k : a ≠ k :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_k_ne_a : k ≠ a := Ne.symm fresh_a_ne_k
  have fresh_a_ne_c : a ≠ c :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 0) (j := 4) (by decide)
  have fresh_c_ne_a : c ≠ a := Ne.symm fresh_a_ne_c
  have fresh_a_ne_x : a ≠ x :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 0) (j := 5) (by decide)
  have fresh_x_ne_a : x ≠ a := Ne.symm fresh_a_ne_x
  have fresh_a_ne_d : a ≠ d :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 0) (j := 6) (by decide)
  have fresh_d_ne_a : d ≠ a := Ne.symm fresh_a_ne_d
  have fresh_a_ne_y : a ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 7
    exact freshVar_injective proofSupport (i := 0) (j := 7) (by decide)
  have fresh_y_ne_a : y ≠ a := Ne.symm fresh_a_ne_y
  have fresh_b_ne_m : b ≠ m :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_m_ne_b : m ≠ b := Ne.symm fresh_b_ne_m
  have fresh_b_ne_k : b ≠ k :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_k_ne_b : k ≠ b := Ne.symm fresh_b_ne_k
  have fresh_b_ne_c : b ≠ c :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 1) (j := 4) (by decide)
  have fresh_c_ne_b : c ≠ b := Ne.symm fresh_b_ne_c
  have fresh_b_ne_x : b ≠ x :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 1) (j := 5) (by decide)
  have fresh_x_ne_b : x ≠ b := Ne.symm fresh_b_ne_x
  have fresh_b_ne_d : b ≠ d :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 1) (j := 6) (by decide)
  have fresh_d_ne_b : d ≠ b := Ne.symm fresh_b_ne_d
  have fresh_b_ne_y : b ≠ y :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 7
    exact freshVar_injective proofSupport (i := 1) (j := 7) (by decide)
  have fresh_y_ne_b : y ≠ b := Ne.symm fresh_b_ne_y
  have fresh_m_ne_k : m ≠ k :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_k_ne_m : k ≠ m := Ne.symm fresh_m_ne_k
  have fresh_m_ne_c : m ≠ c :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 2) (j := 4) (by decide)
  have fresh_m_ne_x : m ≠ x :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 2) (j := 5) (by decide)
  have fresh_m_ne_d : m ≠ d :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 2) (j := 6) (by decide)
  have fresh_m_ne_y : m ≠ y :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 7
    exact freshVar_injective proofSupport (i := 2) (j := 7) (by decide)
  have fresh_k_ne_c : k ≠ c :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 3) (j := 4) (by decide)
  have fresh_c_ne_k : c ≠ k := Ne.symm fresh_k_ne_c
  have fresh_k_ne_x : k ≠ x :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 3) (j := 5) (by decide)
  have fresh_x_ne_k : x ≠ k := Ne.symm fresh_k_ne_x
  have fresh_k_ne_d : k ≠ d :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 3) (j := 6) (by decide)
  have fresh_d_ne_k : d ≠ k := Ne.symm fresh_k_ne_d
  have fresh_k_ne_y : k ≠ y :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 7
    exact freshVar_injective proofSupport (i := 3) (j := 7) (by decide)
  have fresh_y_ne_k : y ≠ k := Ne.symm fresh_k_ne_y
  have fresh_c_ne_x : c ≠ x :=
    by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 4) (j := 5) (by decide)
  have fresh_x_ne_c : x ≠ c := Ne.symm fresh_c_ne_x
  have fresh_c_ne_d : c ≠ d :=
    by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 4) (j := 6) (by decide)
  have fresh_d_ne_c : d ≠ c := Ne.symm fresh_c_ne_d
  have fresh_c_ne_y : c ≠ y :=
    by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 7
    exact freshVar_injective proofSupport (i := 4) (j := 7) (by decide)
  have fresh_y_ne_c : y ≠ c := Ne.symm fresh_c_ne_y
  have fresh_x_ne_d : x ≠ d :=
    by
    change freshVar proofSupport 5 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 5) (j := 6) (by decide)
  have fresh_d_ne_x : d ≠ x := Ne.symm fresh_x_ne_d
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 5 ≠ freshVar proofSupport 7
    exact freshVar_injective proofSupport (i := 5) (j := 7) (by decide)
  have fresh_y_ne_x : y ≠ x := Ne.symm fresh_x_ne_y
  have fresh_d_ne_y : d ≠ y :=
    by
    change freshVar proofSupport 6 ≠ freshVar proofSupport 7
    exact freshVar_injective proofSupport (i := 6) (j := 7) (by decide)
  have fresh_y_ne_d : y ≠ d := Ne.symm fresh_d_ne_y
  have p0000 :=
    @gNcfinraiselem2 m n a b (show a ≠ b from (by exact fresh_a_ne_b))
      (show a ≠ m from (by exact fresh_a_ne_m)) (show a ≠ n from (by exact fresh_a_ne_n))
      (show b ≠ m from (by exact fresh_b_ne_m)) (show b ≠ n from (by exact fresh_b_ne_n))
  have freeVariableCertificate0 : b ∉ ((Class.cv m)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_b_ne_m, not_false_eq_true]
  have p0001 :=
    @gRaleq
      (synWrex n (synCnnc) (synWa (.classMem (synCpw1 (.cv a)) (.cv n))
          (.classMem (synCpw1 (.cv b)) (.cv n))))
      b (.cv m) (synC0c) freeVariableCertificate0
      (by
        exact
          (show b ∉ ((synC0c)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c];
              exact (show b ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
  have freeVariableCertificate1 : a ∉ ((Class.cv m)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_a_ne_m, not_false_eq_true]
  have p0002 :=
    @gRaleqbi1dv
      (synWral b (.cv m) (synWrex n (synCnnc) (synWa (.classMem (synCpw1 (.cv a)) (.cv n))
            (.classMem (synCpw1 (.cv b)) (.cv n)))))
      (synWral b (synC0c) (synWrex n (synCnnc)
          (synWa (.classMem (synCpw1 (.cv a)) (.cv n))
            (.classMem (synCpw1 (.cv b)) (.cv n)))))
      a (.cv m) (synC0c) freeVariableCertificate1
      (by
        exact
          (show a ∉ ((synC0c)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c];
              exact (show a ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
      p0001
  have freeVariableCertificate2 : b ∉ ((Class.cv k)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_b_ne_k, not_false_eq_true]
  have p0003 :=
    @gRaleq
      (synWrex n (synCnnc) (synWa (.classMem (synCpw1 (.cv a)) (.cv n))
          (.classMem (synCpw1 (.cv b)) (.cv n))))
      b (.cv m) (.cv k) freeVariableCertificate0 freeVariableCertificate2
  have freeVariableCertificate3 : a ∉ ((Class.cv k)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_a_ne_k, not_false_eq_true]
  have p0004 :=
    @gRaleqbi1dv
      (synWral b (.cv m) (synWrex n (synCnnc) (synWa (.classMem (synCpw1 (.cv a)) (.cv n))
            (.classMem (synCpw1 (.cv b)) (.cv n)))))
      (synWral b (.cv k) (synWrex n (synCnnc) (synWa (.classMem (synCpw1 (.cv a)) (.cv n))
            (.classMem (synCpw1 (.cv b)) (.cv n)))))
      a (.cv m) (.cv k) freeVariableCertificate1 freeVariableCertificate3 p0003
  have freeVariableCertificate4 : b ∉ ((synCplc (.cv k) (synC1c))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_b_ne_k, or_false,
      not_false_eq_true]
  have p0005 :=
    @gRaleq
      (synWrex n (synCnnc) (synWa (.classMem (synCpw1 (.cv a)) (.cv n))
          (.classMem (synCpw1 (.cv b)) (.cv n))))
      b (.cv m) (synCplc (.cv k) (synC1c)) freeVariableCertificate0
      freeVariableCertificate4
  have freeVariableCertificate5 : a ∉ ((synCplc (.cv k) (synC1c))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_a_ne_k, or_false,
      not_false_eq_true]
  have p0006 :=
    @gRaleqbi1dv
      (synWral b (.cv m) (synWrex n (synCnnc) (synWa (.classMem (synCpw1 (.cv a)) (.cv n))
            (.classMem (synCpw1 (.cv b)) (.cv n)))))
      (synWral b (synCplc (.cv k) (synC1c)) (synWrex n (synCnnc)
          (synWa (.classMem (synCpw1 (.cv a)) (.cv n))
            (.classMem (synCpw1 (.cv b)) (.cv n)))))
      a (.cv m) (synCplc (.cv k) (synC1c)) freeVariableCertificate1
      freeVariableCertificate5 p0005
  have p0007 :=
    @gRaleq
      (synWrex n (synCnnc) (synWa (.classMem (synCpw1 (.cv a)) (.cv n))
          (.classMem (synCpw1 (.cv b)) (.cv n))))
      b (.cv m) M freeVariableCertificate0
      (by exact (show b ∉ (M).fv from (by exact fresh_b_not_M)))
  have p0008 :=
    @gRaleqbi1dv
      (synWral b (.cv m) (synWrex n (synCnnc) (synWa (.classMem (synCpw1 (.cv a)) (.cv n))
            (.classMem (synCpw1 (.cv b)) (.cv n)))))
      (synWral b M (synWrex n (synCnnc) (synWa (.classMem (synCpw1 (.cv a)) (.cv n))
            (.classMem (synCpw1 (.cv b)) (.cv n)))))
      a (.cv m) M freeVariableCertificate1
      (by exact (show a ∉ (M).fv from (by exact fresh_a_not_M))) p0007
  have p0009 := @gEl0c (.cv a)
  have p0010 := @gEl0c (.cv b)
  have p0011 := @gPeano1
  have p0012 := @gNulel0c
  have p0014 :=
    @gPm32i (.classMem (synC0) (synC0c)) (.classMem (synC0) (synC0c)) p0012 p0012
  have p0015 := @gEleq2 (.cv n) (synC0c) (synC0)
  have p0016 :=
    @gAnbi12d (.classEq (.cv n) (synC0c)) (.classMem (synC0) (.cv n))
      (.classMem (synC0) (synC0c)) (.classMem (synC0) (.cv n))
      (.classMem (synC0) (synC0c)) p0015 p0015
  have freeVariableCertificate6 :
    n ∉ ((synWa (.classMem (synC0) (synC0c)) (.classMem (synC0) (synC0c)))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union,
      Finset.notMem_empty, or_false, not_false_eq_true]
  have p0017 :=
    @gRspcev (synWa (.classMem (synC0) (.cv n)) (.classMem (synC0) (.cv n)))
      (synWa (.classMem (synC0) (synC0c)) (.classMem (synC0) (synC0c))) n (synC0c)
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
      freeVariableCertificate6 p0016
  have p0018 :=
    @gMp2an (.classMem (synC0c) (synCnnc))
      (synWa (.classMem (synC0) (synC0c)) (.classMem (synC0) (synC0c)))
      (synWrex n (synCnnc) (synWa (.classMem (synC0) (.cv n)) (.classMem (synC0) (.cv n))))
      p0011 p0014 p0017
  have p0019 := @gPw1eq (.cv a) (synC0)
  have p0020 := @gPw10
  have p0021 :=
    @gSyl6eq (.classEq (.cv a) (synC0)) (synCpw1 (.cv a)) (synCpw1 (synC0)) (synC0)
      p0019 p0020
  have p0022 :=
    @gEleq1d (.classEq (.cv a) (synC0)) (synCpw1 (.cv a)) (synC0) (.cv n) p0021
  have p0023 := @gPw1eq (.cv b) (synC0)
  have p0025 :=
    @gSyl6eq (.classEq (.cv b) (synC0)) (synCpw1 (.cv b)) (synCpw1 (synC0)) (synC0)
      p0023 p0020
  have p0026 :=
    @gEleq1d (.classEq (.cv b) (synC0)) (synCpw1 (.cv b)) (synC0) (.cv n) p0025
  have p0027 :=
    @gBi2anan9 (.classEq (.cv a) (synC0)) (.classMem (synCpw1 (.cv a)) (.cv n))
      (.classMem (synC0) (.cv n)) (.classEq (.cv b) (synC0))
      (.classMem (synCpw1 (.cv b)) (.cv n)) (.classMem (synC0) (.cv n)) p0022 p0026
  have freeVariableCertificate7 :
    n ∉ ((synWa (.classEq (.cv a) (synC0)) (.classEq (.cv b) (synC0)))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_n_ne_a, fresh_n_ne_b, or_false,
      not_false_eq_true]
  have p0028 :=
    @gRexbidv (synWa (.classEq (.cv a) (synC0)) (.classEq (.cv b) (synC0)))
      (synWa (.classMem (synCpw1 (.cv a)) (.cv n)) (.classMem (synCpw1 (.cv b)) (.cv n)))
      (synWa (.classMem (synC0) (.cv n)) (.classMem (synC0) (.cv n))) n (synCnnc)
      freeVariableCertificate7 p0027
  have p0029 :=
    @gMpbiri (synWa (.classEq (.cv a) (synC0)) (.classEq (.cv b) (synC0)))
      (synWrex n (synCnnc) (synWa (.classMem (synCpw1 (.cv a)) (.cv n))
          (.classMem (synCpw1 (.cv b)) (.cv n))))
      (synWrex n (synCnnc) (synWa (.classMem (synC0) (.cv n)) (.classMem (synC0) (.cv n))))
      p0018 p0028
  have p0030 :=
    @gSyl2anb (.classMem (.cv a) (synC0c)) (.classEq (.cv a) (synC0))
      (.classEq (.cv b) (synC0))
      (synWrex n (synCnnc) (synWa (.classMem (synCpw1 (.cv a)) (.cv n))
          (.classMem (synCpw1 (.cv b)) (.cv n))))
      (.classMem (.cv b) (synC0c)) p0009 p0010 p0029
  have p0031 :=
    @gRgen2a
      (synWrex n (synCnnc) (synWa (.classMem (synCpw1 (.cv a)) (.cv n))
          (.classMem (synCpw1 (.cv b)) (.cv n))))
      a b (synC0c)
      (by
        exact
          (show b ∉ ((synC0c)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c];
              exact (show b ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
      p0030
  have freeVariableCertificate8 : a ∉ ((Wff.classMem (.cv k) (synCnnc))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_a_ne_k, or_false,
      not_false_eq_true]
  have p0032 := @gNfv (.classMem (.cv k) (synCnnc)) a freeVariableCertificate8
  have p0033 :=
    @gNfra1
      (synWral b (.cv k) (synWrex n (synCnnc) (synWa (.classMem (synCpw1 (.cv a)) (.cv n))
            (.classMem (synCpw1 (.cv b)) (.cv n)))))
      a (.cv k)
  have p0034 :=
    @gNfan (.classMem (.cv k) (synCnnc))
      (synWral a (.cv k) (synWral b (.cv k) (synWrex n (synCnnc)
            (synWa (.classMem (synCpw1 (.cv a)) (.cv n))
              (.classMem (synCpw1 (.cv b)) (.cv n))))))
      a p0032 p0033
  have freeVariableCertificate9 : b ∉ ((Wff.classMem (.cv k) (synCnnc))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_b_ne_k, or_false,
      not_false_eq_true]
  have p0035 := @gNfv (.classMem (.cv k) (synCnnc)) b freeVariableCertificate9
  have p0036 :=
    @gNfra2
      (synWrex n (synCnnc) (synWa (.classMem (synCpw1 (.cv a)) (.cv n))
          (.classMem (synCpw1 (.cv b)) (.cv n))))
      a b (.cv k) (.cv k) freeVariableCertificate2
  have p0037 :=
    @gNfan (.classMem (.cv k) (synCnnc))
      (synWral a (.cv k) (synWral b (.cv k) (synWrex n (synCnnc)
            (synWa (.classMem (synCpw1 (.cv a)) (.cv n))
              (.classMem (synCpw1 (.cv b)) (.cv n))))))
      b p0035 p0036
  have freeVariableCertificate10 :
    b ∉ ((Wff.classMem (.cv a) (synCplc (.cv k) (synC1c)))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_b_ne_a, fresh_b_ne_k, or_false,
      not_false_eq_true]
  have p0038 :=
    @gNfv (.classMem (.cv a) (synCplc (.cv k) (synC1c))) b freeVariableCertificate10
  have freeVariableCertificate11 : d ∉ ((Class.cv k)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_d_ne_k, not_false_eq_true]
  have freeVariableCertificate12 : c ∉ ((Class.cv k)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_c_ne_k, not_false_eq_true]
  have freeVariableCertificate13 :
    d ∉
      ((synWrex x (synCcompl (.cv c))
          (.classEq (.cv a) (synCun (.cv c) (synCsn (.cv x)))))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
      Finset.mem_erase, Finset.mem_singleton, fresh_d_ne_c, fresh_d_ne_a, fresh_d_ne_x,
      or_false, and_false, not_false_eq_true]
  have freeVariableCertificate14 :
    c ∉
      ((synWrex y (synCcompl (.cv d))
          (.classEq (.cv b) (synCun (.cv d) (synCsn (.cv y)))))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
      Finset.mem_erase, Finset.mem_singleton, fresh_c_ne_d, fresh_c_ne_b, fresh_c_ne_y,
      or_false, and_false, not_false_eq_true]
  have p0039 :=
    @gReeanv
      (synWrex x (synCcompl (.cv c)) (.classEq (.cv a) (synCun (.cv c) (synCsn (.cv x)))))
      (synWrex y (synCcompl (.cv d)) (.classEq (.cv b) (synCun (.cv d) (synCsn (.cv y)))))
      c d (.cv k) (.cv k) freeVariableCertificate11 freeVariableCertificate12
      freeVariableCertificate13 freeVariableCertificate14
      (show c ≠ d from (by exact fresh_c_ne_d))
  have freeVariableCertificate15 : y ∉ ((synCcompl (.cv c))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_y_ne_c,
      not_false_eq_true]
  have freeVariableCertificate16 : x ∉ ((synCcompl (.cv d))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_x_ne_d,
      not_false_eq_true]
  have freeVariableCertificate17 :
    y ∉ ((Wff.classEq (.cv a) (synCun (.cv c) (synCsn (.cv x))))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
      Finset.mem_singleton, fresh_y_ne_a, fresh_y_ne_c, fresh_y_ne_x, or_false,
      not_false_eq_true]
  have freeVariableCertificate18 :
    x ∉ ((Wff.classEq (.cv b) (synCun (.cv d) (synCsn (.cv y))))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
      Finset.mem_singleton, fresh_x_ne_b, fresh_x_ne_d, fresh_x_ne_y, or_false,
      not_false_eq_true]
  have p0040 :=
    @gReeanv (.classEq (.cv a) (synCun (.cv c) (synCsn (.cv x))))
      (.classEq (.cv b) (synCun (.cv d) (synCsn (.cv y)))) x y (synCcompl (.cv c))
      (synCcompl (.cv d)) freeVariableCertificate15 freeVariableCertificate16
      freeVariableCertificate17 freeVariableCertificate18
      (show x ≠ y from (by exact fresh_x_ne_y))
  have p0041 :=
    @gN2rexbii
      (synWrex x (synCcompl (.cv c)) (synWrex y (synCcompl (.cv d))
          (synWa (.classEq (.cv a) (synCun (.cv c) (synCsn (.cv x))))
            (.classEq (.cv b) (synCun (.cv d) (synCsn (.cv y)))))))
      (synWa (synWrex x (synCcompl (.cv c))
          (.classEq (.cv a) (synCun (.cv c) (synCsn (.cv x)))))
        (synWrex y (synCcompl (.cv d))
          (.classEq (.cv b) (synCun (.cv d) (synCsn (.cv y))))))
      c d (.cv k) (.cv k) p0040
  have freeVariableCertificate19 : c ∉ ((Class.cv a)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_c_ne_a, not_false_eq_true]
  have freeVariableCertificate20 : x ∉ ((Class.cv a)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_x_ne_a, not_false_eq_true]
  have p0042 :=
    @gElsuc x (.cv a) (.cv k) c freeVariableCertificate19 freeVariableCertificate20
      freeVariableCertificate12 (show c ≠ x from (by exact fresh_c_ne_x))
  have freeVariableCertificate21 : d ∉ ((Class.cv b)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_d_ne_b, not_false_eq_true]
  have freeVariableCertificate22 : y ∉ ((Class.cv b)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_y_ne_b, not_false_eq_true]
  have p0043 :=
    @gElsuc y (.cv b) (.cv k) d freeVariableCertificate21 freeVariableCertificate22
      freeVariableCertificate11 (show d ≠ y from (by exact fresh_d_ne_y))
  have p0044 :=
    @gAnbi12i (.classMem (.cv a) (synCplc (.cv k) (synC1c)))
      (synWrex c (.cv k) (synWrex x (synCcompl (.cv c))
          (.classEq (.cv a) (synCun (.cv c) (synCsn (.cv x))))))
      (.classMem (.cv b) (synCplc (.cv k) (synC1c)))
      (synWrex d (.cv k) (synWrex y (synCcompl (.cv d))
          (.classEq (.cv b) (synCun (.cv d) (synCsn (.cv y))))))
      p0042 p0043
  have p0045 :=
    @gN3bitr4ri
      (synWrex c (.cv k) (synWrex d (.cv k) (synWa (synWrex x (synCcompl (.cv c))
              (.classEq (.cv a) (synCun (.cv c) (synCsn (.cv x)))))
            (synWrex y (synCcompl (.cv d))
              (.classEq (.cv b) (synCun (.cv d) (synCsn (.cv y))))))))
      (synWa (synWrex c (.cv k) (synWrex x (synCcompl (.cv c))
            (.classEq (.cv a) (synCun (.cv c) (synCsn (.cv x)))))) (synWrex d (.cv k)
          (synWrex y (synCcompl (.cv d))
            (.classEq (.cv b) (synCun (.cv d) (synCsn (.cv y)))))))
      (synWrex c (.cv k) (synWrex d (.cv k) (synWrex x (synCcompl (.cv c))
            (synWrex y (synCcompl (.cv d))
              (synWa (.classEq (.cv a) (synCun (.cv c) (synCsn (.cv x))))
                (.classEq (.cv b) (synCun (.cv d) (synCsn (.cv y)))))))))
      (synWa (.classMem (.cv a) (synCplc (.cv k) (synC1c)))
        (.classMem (.cv b) (synCplc (.cv k) (synC1c))))
      p0039 p0041 p0044
  have p0046 := @gPw1eq (.cv a) (.cv c)
  have p0047_e00_recanon :
    Nominal.NPrf (.imp (.objEq a c) (.classEq (synCpw1 (.cv a)) (synCpw1 (.cv c)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synCpw1 synCin synCcompl synCnin synWnan synWa synCpw synWss
          synC1c synWex synCsn
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0046
  have p0047 :=
    @gEleq1d (.objEq a c) (synCpw1 (.cv a)) (synCpw1 (.cv c)) (.cv n) p0047_e00_recanon
  have p0048 :=
    @gAnbi1d (.objEq a c) (.classMem (synCpw1 (.cv a)) (.cv n))
      (.classMem (synCpw1 (.cv c)) (.cv n)) (.classMem (synCpw1 (.cv b)) (.cv n)) p0047
  have freeVariableCertificate23 : n ∉ ((Wff.objEq a c)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_insert,
      Finset.mem_singleton, fresh_n_ne_a, fresh_n_ne_c, or_false, not_false_eq_true]
  have p0049 :=
    @gRexbidv (.objEq a c)
      (synWa (.classMem (synCpw1 (.cv a)) (.cv n)) (.classMem (synCpw1 (.cv b)) (.cv n)))
      (synWa (.classMem (synCpw1 (.cv c)) (.cv n)) (.classMem (synCpw1 (.cv b)) (.cv n)))
      n (synCnnc) freeVariableCertificate23 p0048
  have p0050 := @gPw1eq (.cv b) (.cv d)
  have p0051_e00_recanon :
    Nominal.NPrf (.imp (.objEq b d) (.classEq (synCpw1 (.cv b)) (synCpw1 (.cv d)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synCpw1 synCin synCcompl synCnin synWnan synWa synCpw synWss
          synC1c synWex synCsn
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0050
  have p0051 :=
    @gEleq1d (.objEq b d) (synCpw1 (.cv b)) (synCpw1 (.cv d)) (.cv n) p0051_e00_recanon
  have p0052 :=
    @gAnbi2d (.objEq b d) (.classMem (synCpw1 (.cv b)) (.cv n))
      (.classMem (synCpw1 (.cv d)) (.cv n)) (.classMem (synCpw1 (.cv c)) (.cv n)) p0051
  have freeVariableCertificate24 : n ∉ ((Wff.objEq b d)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_insert,
      Finset.mem_singleton, fresh_n_ne_b, fresh_n_ne_d, or_false, not_false_eq_true]
  have p0053 :=
    @gRexbidv (.objEq b d)
      (synWa (.classMem (synCpw1 (.cv c)) (.cv n)) (.classMem (synCpw1 (.cv b)) (.cv n)))
      (synWa (.classMem (synCpw1 (.cv c)) (.cv n)) (.classMem (synCpw1 (.cv d)) (.cv n)))
      n (synCnnc) freeVariableCertificate24 p0052
  have p0054_e00_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv a) (.cv c)) (synWb (synWrex n (synCnnc)
            (synWa (.classMem (synCpw1 (.cv a)) (.cv n))
              (.classMem (synCpw1 (.cv b)) (.cv n)))) (synWrex n (synCnnc)
            (synWa (.classMem (synCpw1 (.cv c)) (.cv n))
              (.classMem (synCpw1 (.cv b)) (.cv n)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [synWb, synWrex, synWex, synWa, synCnnc, synCint]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0049
  have p0054_e01_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv b) (.cv d)) (synWb (synWrex n (synCnnc)
            (synWa (.classMem (synCpw1 (.cv c)) (.cv n))
              (.classMem (synCpw1 (.cv b)) (.cv n)))) (synWrex n (synCnnc)
            (synWa (.classMem (synCpw1 (.cv c)) (.cv n))
              (.classMem (synCpw1 (.cv d)) (.cv n)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [synWb, synWrex, synWex, synWa, synCnnc, synCint]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0053
  have freeVariableCertificate25 : a ∉ ((Class.cv c)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_a_ne_c, not_false_eq_true]
  have freeVariableCertificate26 : b ∉ ((Class.cv c)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_b_ne_c, not_false_eq_true]
  have freeVariableCertificate27 : b ∉ ((Class.cv d)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_b_ne_d, not_false_eq_true]
  have freeVariableCertificate28 :
    a ∉
      ((synWrex n (synCnnc) (synWa (.classMem (synCpw1 (.cv c)) (.cv n))
            (.classMem (synCpw1 (.cv b)) (.cv n))))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
      Finset.mem_singleton, Finset.notMem_empty, fresh_a_ne_c, fresh_a_ne_n, fresh_a_ne_b,
      or_false, and_false, not_false_eq_true]
  have freeVariableCertificate29 :
    b ∉
      ((synWrex n (synCnnc) (synWa (.classMem (synCpw1 (.cv c)) (.cv n))
            (.classMem (synCpw1 (.cv d)) (.cv n))))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
      Finset.mem_singleton, Finset.notMem_empty, fresh_b_ne_c, fresh_b_ne_n, fresh_b_ne_d,
      or_false, and_false, not_false_eq_true]
  have p0054 :=
    @gRspc2v
      (synWrex n (synCnnc) (synWa (.classMem (synCpw1 (.cv a)) (.cv n))
          (.classMem (synCpw1 (.cv b)) (.cv n))))
      (synWrex n (synCnnc) (synWa (.classMem (synCpw1 (.cv c)) (.cv n))
          (.classMem (synCpw1 (.cv d)) (.cv n))))
      (synWrex n (synCnnc) (synWa (.classMem (synCpw1 (.cv c)) (.cv n))
          (.classMem (synCpw1 (.cv b)) (.cv n))))
      a b (.cv c) (.cv d) (.cv k) (.cv k) freeVariableCertificate25
      freeVariableCertificate26 freeVariableCertificate27 freeVariableCertificate3
      freeVariableCertificate3 freeVariableCertificate2 freeVariableCertificate28
      freeVariableCertificate29 (show a ≠ b from (by exact fresh_a_ne_b))
      p0054_e00_recanon p0054_e01_recanon
  have p0055_e00_recanon :
    Nominal.NPrf
      (.imp (synWa (.objMem c k) (.objMem d k)) (.imp (synWral a (.cv k) (synWral b (.cv k)
              (synWrex n (synCnnc) (synWa (.classMem (synCpw1 (.cv a)) (.cv n))
                  (.classMem (synCpw1 (.cv b)) (.cv n)))))) (synWrex n (synCnnc)
            (synWa (.classMem (synCpw1 (.cv c)) (.cv n))
              (.classMem (synCpw1 (.cv d)) (.cv n)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWa synWral synWrex synWex synCnnc synCint
        simp (config := { failIfUnchanged := false }) only []
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0054
  have p0055 :=
    @gCom12 (synWa (.objMem c k) (.objMem d k))
      (synWral a (.cv k) (synWral b (.cv k) (synWrex n (synCnnc)
            (synWa (.classMem (synCpw1 (.cv a)) (.cv n))
              (.classMem (synCpw1 (.cv b)) (.cv n))))))
      (synWrex n (synCnnc) (synWa (.classMem (synCpw1 (.cv c)) (.cv n))
          (.classMem (synCpw1 (.cv d)) (.cv n))))
      p0055_e00_recanon
  have p0056 := @gVex x
  have p0057 := @gElcompl (.cv x) (.cv c) p0056
  have p0058 := @gVex y
  have p0059 := @gElcompl (.cv y) (.cv d) p0058
  have p0060_e00_recanon :
    Nominal.NPrf (synWb (.classMem (.cv x) (synCcompl (.cv c))) (.neg (.objMem x c))) :=
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
      p0057
  have p0060_e01_recanon :
    Nominal.NPrf (synWb (.classMem (.cv y) (synCcompl (.cv d))) (.neg (.objMem y d))) :=
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
      p0059
  have p0060 :=
    @gAnbi12i (.classMem (.cv x) (synCcompl (.cv c))) (.neg (.objMem x c))
      (.classMem (.cv y) (synCcompl (.cv d))) (.neg (.objMem y d)) p0060_e00_recanon
      p0060_e01_recanon
  have p0061 :=
    @gAnbi2i
      (synWa (.classMem (.cv x) (synCcompl (.cv c))) (.classMem (.cv y) (synCcompl (.cv d))))
      (synWa (.neg (.objMem x c)) (.neg (.objMem y d)))
      (synWa (.objMem c k) (.objMem d k)) p0060
  have p0062 := @gPeano2 (.cv n)
  have p0063 :=
    @gAd3antrrr (.classMem (.cv n) (synCnnc))
      (.classMem (synCplc (.cv n) (synC1c)) (synCnnc))
      (synWa (.classMem (synCpw1 (.cv c)) (.cv n)) (.classMem (synCpw1 (.cv d)) (.cv n)))
      (.classMem (.cv k) (synCnnc))
      (synWa (synWa (.objMem c k) (.objMem d k))
        (synWa (.neg (.objMem x c)) (.neg (.objMem y d))))
      p0062
  have p0064 :=
    @gSimplrl (.classMem (.cv n) (synCnnc)) (.classMem (synCpw1 (.cv c)) (.cv n))
      (.classMem (synCpw1 (.cv d)) (.cv n)) (.classMem (.cv k) (synCnnc))
  have p0065 :=
    @gAdantr
      (synWa (synWa (.classMem (.cv n) (synCnnc))
          (synWa (.classMem (synCpw1 (.cv c)) (.cv n))
            (.classMem (synCpw1 (.cv d)) (.cv n)))) (.classMem (.cv k) (synCnnc)))
      (.classMem (synCpw1 (.cv c)) (.cv n))
      (synWa (synWa (.objMem c k) (.objMem d k))
        (synWa (.neg (.objMem x c)) (.neg (.objMem y d))))
      p0064
  have p0066 :=
    @gSimprrl
      (synWa (synWa (.classMem (.cv n) (synCnnc))
          (synWa (.classMem (synCpw1 (.cv c)) (.cv n))
            (.classMem (synCpw1 (.cv d)) (.cv n)))) (.classMem (.cv k) (synCnnc)))
      (synWa (.objMem c k) (.objMem d k)) (.neg (.objMem x c)) (.neg (.objMem y d))
  have p0067 := @gSnelpw1 (.cv x) (.cv c)
  have p0068_e01_recanon :
    Nominal.NPrf
      (synWb (.classMem (synCsn (.cv x)) (synCpw1 (.cv c))) (.objMem x c)) :=
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
      p0067
  have p0068 :=
    @gSylnibr
      (synWa (synWa (synWa (.classMem (.cv n) (synCnnc))
            (synWa (.classMem (synCpw1 (.cv c)) (.cv n))
              (.classMem (synCpw1 (.cv d)) (.cv n)))) (.classMem (.cv k) (synCnnc)))
        (synWa (synWa (.objMem c k) (.objMem d k))
          (synWa (.neg (.objMem x c)) (.neg (.objMem y d)))))
      (.objMem x c) (.classMem (synCsn (.cv x)) (synCpw1 (.cv c))) p0066
      p0068_e01_recanon
  have p0069 := @gSnex (.cv x)
  have p0070 := @gElsuci (synCpw1 (.cv c)) (.cv n) (synCsn (.cv x)) p0069
  have p0071 :=
    @gSyl2anc
      (synWa (synWa (synWa (.classMem (.cv n) (synCnnc))
            (synWa (.classMem (synCpw1 (.cv c)) (.cv n))
              (.classMem (synCpw1 (.cv d)) (.cv n)))) (.classMem (.cv k) (synCnnc)))
        (synWa (synWa (.objMem c k) (.objMem d k))
          (synWa (.neg (.objMem x c)) (.neg (.objMem y d)))))
      (.classMem (synCpw1 (.cv c)) (.cv n))
      (.neg (.classMem (synCsn (.cv x)) (synCpw1 (.cv c))))
      (.classMem (synCun (synCpw1 (.cv c)) (synCsn (synCsn (.cv x))))
        (synCplc (.cv n) (synC1c)))
      p0065 p0068 p0070
  have p0072 :=
    @gSimplrr (.classMem (.cv n) (synCnnc)) (.classMem (synCpw1 (.cv c)) (.cv n))
      (.classMem (synCpw1 (.cv d)) (.cv n)) (.classMem (.cv k) (synCnnc))
  have p0073 :=
    @gAdantr
      (synWa (synWa (.classMem (.cv n) (synCnnc))
          (synWa (.classMem (synCpw1 (.cv c)) (.cv n))
            (.classMem (synCpw1 (.cv d)) (.cv n)))) (.classMem (.cv k) (synCnnc)))
      (.classMem (synCpw1 (.cv d)) (.cv n))
      (synWa (synWa (.objMem c k) (.objMem d k))
        (synWa (.neg (.objMem x c)) (.neg (.objMem y d))))
      p0072
  have p0074 :=
    @gSimprrr
      (synWa (synWa (.classMem (.cv n) (synCnnc))
          (synWa (.classMem (synCpw1 (.cv c)) (.cv n))
            (.classMem (synCpw1 (.cv d)) (.cv n)))) (.classMem (.cv k) (synCnnc)))
      (synWa (.objMem c k) (.objMem d k)) (.neg (.objMem x c)) (.neg (.objMem y d))
  have p0075 := @gSnelpw1 (.cv y) (.cv d)
  have p0076_e01_recanon :
    Nominal.NPrf
      (synWb (.classMem (synCsn (.cv y)) (synCpw1 (.cv d))) (.objMem y d)) :=
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
      p0075
  have p0076 :=
    @gSylnibr
      (synWa (synWa (synWa (.classMem (.cv n) (synCnnc))
            (synWa (.classMem (synCpw1 (.cv c)) (.cv n))
              (.classMem (synCpw1 (.cv d)) (.cv n)))) (.classMem (.cv k) (synCnnc)))
        (synWa (synWa (.objMem c k) (.objMem d k))
          (synWa (.neg (.objMem x c)) (.neg (.objMem y d)))))
      (.objMem y d) (.classMem (synCsn (.cv y)) (synCpw1 (.cv d))) p0074
      p0076_e01_recanon
  have p0077 := @gSnex (.cv y)
  have p0078 := @gElsuci (synCpw1 (.cv d)) (.cv n) (synCsn (.cv y)) p0077
  have p0079 :=
    @gSyl2anc
      (synWa (synWa (synWa (.classMem (.cv n) (synCnnc))
            (synWa (.classMem (synCpw1 (.cv c)) (.cv n))
              (.classMem (synCpw1 (.cv d)) (.cv n)))) (.classMem (.cv k) (synCnnc)))
        (synWa (synWa (.objMem c k) (.objMem d k))
          (synWa (.neg (.objMem x c)) (.neg (.objMem y d)))))
      (.classMem (synCpw1 (.cv d)) (.cv n))
      (.neg (.classMem (synCsn (.cv y)) (synCpw1 (.cv d))))
      (.classMem (synCun (synCpw1 (.cv d)) (synCsn (synCsn (.cv y))))
        (synCplc (.cv n) (synC1c)))
      p0073 p0076 p0078
  have p0080 :=
    @gEleq2 (.cv m) (synCplc (.cv n) (synC1c))
      (synCun (synCpw1 (.cv c)) (synCsn (synCsn (.cv x))))
  have p0081 :=
    @gEleq2 (.cv m) (synCplc (.cv n) (synC1c))
      (synCun (synCpw1 (.cv d)) (synCsn (synCsn (.cv y))))
  have p0082 :=
    @gAnbi12d (.classEq (.cv m) (synCplc (.cv n) (synC1c)))
      (.classMem (synCun (synCpw1 (.cv c)) (synCsn (synCsn (.cv x)))) (.cv m))
      (.classMem (synCun (synCpw1 (.cv c)) (synCsn (synCsn (.cv x))))
        (synCplc (.cv n) (synC1c)))
      (.classMem (synCun (synCpw1 (.cv d)) (synCsn (synCsn (.cv y)))) (.cv m))
      (.classMem (synCun (synCpw1 (.cv d)) (synCsn (synCsn (.cv y))))
        (synCplc (.cv n) (synC1c)))
      p0080 p0081
  have freeVariableCertificate30 : m ∉ ((synCplc (.cv n) (synC1c))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_m_ne_n, or_false,
      not_false_eq_true]
  have freeVariableCertificate31 :
    m ∉
      ((synWa (.classMem (synCun (synCpw1 (.cv c)) (synCsn (synCsn (.cv x))))
            (synCplc (.cv n) (synC1c)))
          (.classMem (synCun (synCpw1 (.cv d)) (synCsn (synCsn (.cv y))))
            (synCplc (.cv n) (synC1c))))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_m_ne_c, fresh_m_ne_x, fresh_m_ne_n,
      fresh_m_ne_d, fresh_m_ne_y, or_false, not_false_eq_true]
  have p0083 :=
    @gRspcev
      (synWa (.classMem (synCun (synCpw1 (.cv c)) (synCsn (synCsn (.cv x)))) (.cv m))
        (.classMem (synCun (synCpw1 (.cv d)) (synCsn (synCsn (.cv y)))) (.cv m)))
      (synWa (.classMem (synCun (synCpw1 (.cv c)) (synCsn (synCsn (.cv x))))
          (synCplc (.cv n) (synC1c)))
        (.classMem (synCun (synCpw1 (.cv d)) (synCsn (synCsn (.cv y))))
          (synCplc (.cv n) (synC1c))))
      m (synCplc (.cv n) (synC1c)) (synCnnc) freeVariableCertificate30
      (by
        exact
          (show m ∉ ((synCnnc)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc];
              exact (show m ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
      freeVariableCertificate31 p0082
  have p0084 :=
    @gSyl12anc
      (synWa (synWa (synWa (.classMem (.cv n) (synCnnc))
            (synWa (.classMem (synCpw1 (.cv c)) (.cv n))
              (.classMem (synCpw1 (.cv d)) (.cv n)))) (.classMem (.cv k) (synCnnc)))
        (synWa (synWa (.objMem c k) (.objMem d k))
          (synWa (.neg (.objMem x c)) (.neg (.objMem y d)))))
      (.classMem (synCplc (.cv n) (synC1c)) (synCnnc))
      (.classMem (synCun (synCpw1 (.cv c)) (synCsn (synCsn (.cv x))))
        (synCplc (.cv n) (synC1c)))
      (.classMem (synCun (synCpw1 (.cv d)) (synCsn (synCsn (.cv y))))
        (synCplc (.cv n) (synC1c)))
      (synWrex m (synCnnc) (synWa
          (.classMem (synCun (synCpw1 (.cv c)) (synCsn (synCsn (.cv x)))) (.cv m))
          (.classMem (synCun (synCpw1 (.cv d)) (synCsn (synCsn (.cv y)))) (.cv m))))
      p0063 p0071 p0079 p0083
  have p0085 :=
    @gEx
      (synWa (synWa (.classMem (.cv n) (synCnnc))
          (synWa (.classMem (synCpw1 (.cv c)) (.cv n))
            (.classMem (synCpw1 (.cv d)) (.cv n)))) (.classMem (.cv k) (synCnnc)))
      (synWa (synWa (.objMem c k) (.objMem d k))
        (synWa (.neg (.objMem x c)) (.neg (.objMem y d))))
      (synWrex m (synCnnc) (synWa
          (.classMem (synCun (synCpw1 (.cv c)) (synCsn (synCsn (.cv x)))) (.cv m))
          (.classMem (synCun (synCpw1 (.cv d)) (synCsn (synCsn (.cv y)))) (.cv m))))
      p0084
  have p0086 :=
    @gEx
      (synWa (.classMem (.cv n) (synCnnc)) (synWa (.classMem (synCpw1 (.cv c)) (.cv n))
          (.classMem (synCpw1 (.cv d)) (.cv n))))
      (.classMem (.cv k) (synCnnc))
      (.imp (synWa (synWa (.objMem c k) (.objMem d k))
          (synWa (.neg (.objMem x c)) (.neg (.objMem y d)))) (synWrex m (synCnnc) (synWa
            (.classMem (synCun (synCpw1 (.cv c)) (synCsn (synCsn (.cv x)))) (.cv m))
            (.classMem (synCun (synCpw1 (.cv d)) (synCsn (synCsn (.cv y)))) (.cv m)))))
      p0085
  have freeVariableCertificate32 :
    n ∉
      ((Wff.imp (.classMem (.cv k) (synCnnc)) (.imp
            (synWa (synWa (.objMem c k) (.objMem d k))
              (synWa (.neg (.objMem x c)) (.neg (.objMem y d)))) (synWrex m (synCnnc) (synWa
                (.classMem (synCun (synCpw1 (.cv c)) (synCsn (synCsn (.cv x)))) (.cv m))
                (.classMem (synCun (synCpw1 (.cv d)) (synCsn (synCsn (.cv y))))
                  (.cv m))))))).fv :=
    by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
      NFChoice.Compiler.CoreFVSimp.fv_wff_objMem, NFChoice.Compiler.CoreFVSimp.fv_wff_neg,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
      Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty,
      fresh_n_ne_k, fresh_n_ne_c, fresh_n_ne_d, fresh_n_ne_x, fresh_n_ne_y, fresh_n_ne_m,
      or_false, and_false, not_false_eq_true]
  have p0087 :=
    @gRexlimiva
      (synWa (.classMem (synCpw1 (.cv c)) (.cv n)) (.classMem (synCpw1 (.cv d)) (.cv n)))
      (.imp (.classMem (.cv k) (synCnnc)) (.imp (synWa (synWa (.objMem c k) (.objMem d k))
            (synWa (.neg (.objMem x c)) (.neg (.objMem y d)))) (synWrex m (synCnnc) (synWa
              (.classMem (synCun (synCpw1 (.cv c)) (synCsn (synCsn (.cv x)))) (.cv m))
              (.classMem (synCun (synCpw1 (.cv d)) (synCsn (synCsn (.cv y)))) (.cv m))))))
      n (synCnnc) freeVariableCertificate32 p0086
  have p0088 :=
    @gEleq2 (.cv m) (.cv n) (synCun (synCpw1 (.cv c)) (synCsn (synCsn (.cv x))))
  have p0089 :=
    @gEleq2 (.cv m) (.cv n) (synCun (synCpw1 (.cv d)) (synCsn (synCsn (.cv y))))
  have p0090_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq m n) (synWb
          (.classMem (synCun (synCpw1 (.cv c)) (synCsn (synCsn (.cv x)))) (.cv m))
          (.classMem (synCun (synCpw1 (.cv c)) (synCsn (synCsn (.cv x)))) (.cv n)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCun synCnin synWnan synWa synCcompl synCpw1 synCin synCpw
          synWss synC1c synWex synCsn
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0088
  have p0090_e01_recanon :
    Nominal.NPrf
      (.imp (.objEq m n) (synWb
          (.classMem (synCun (synCpw1 (.cv d)) (synCsn (synCsn (.cv y)))) (.cv m))
          (.classMem (synCun (synCpw1 (.cv d)) (synCsn (synCsn (.cv y)))) (.cv n)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCun synCnin synWnan synWa synCcompl synCpw1 synCin synCpw
          synWss synC1c synWex synCsn
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0089
  have p0090 :=
    @gAnbi12d (.objEq m n)
      (.classMem (synCun (synCpw1 (.cv c)) (synCsn (synCsn (.cv x)))) (.cv m))
      (.classMem (synCun (synCpw1 (.cv c)) (synCsn (synCsn (.cv x)))) (.cv n))
      (.classMem (synCun (synCpw1 (.cv d)) (synCsn (synCsn (.cv y)))) (.cv m))
      (.classMem (synCun (synCpw1 (.cv d)) (synCsn (synCsn (.cv y)))) (.cv n))
      p0090_e00_recanon p0090_e01_recanon
  have freeVariableCertificate33 :
    n ∉
      ((synWa (.classMem (synCun (synCpw1 (.cv c)) (synCsn (synCsn (.cv x)))) (.cv m))
          (.classMem (synCun (synCpw1 (.cv d)) (synCsn (synCsn (.cv y)))) (.cv m)))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
      Finset.mem_singleton, fresh_n_ne_c, fresh_n_ne_x, fresh_n_ne_m, fresh_n_ne_d,
      fresh_n_ne_y, or_false, not_false_eq_true]
  have freeVariableCertificate34 :
    m ∉
      ((synWa (.classMem (synCun (synCpw1 (.cv c)) (synCsn (synCsn (.cv x)))) (.cv n))
          (.classMem (synCun (synCpw1 (.cv d)) (synCsn (synCsn (.cv y)))) (.cv n)))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
      Finset.mem_singleton, fresh_m_ne_c, fresh_m_ne_x, fresh_m_ne_n, fresh_m_ne_d,
      fresh_m_ne_y, or_false, not_false_eq_true]
  have p0091 :=
    @gCbvrexv
      (synWa (.classMem (synCun (synCpw1 (.cv c)) (synCsn (synCsn (.cv x)))) (.cv m))
        (.classMem (synCun (synCpw1 (.cv d)) (synCsn (synCsn (.cv y)))) (.cv m)))
      (synWa (.classMem (synCun (synCpw1 (.cv c)) (synCsn (synCsn (.cv x)))) (.cv n))
        (.classMem (synCun (synCpw1 (.cv d)) (synCsn (synCsn (.cv y)))) (.cv n)))
      m n (synCnnc)
      (by
        exact
          (show m ∉ ((synCnnc)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc];
              exact (show m ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
      (by
        exact
          (show n ∉ ((synCnnc)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc];
              exact (show n ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
      freeVariableCertificate33 freeVariableCertificate34 p0090
  have p0092 :=
    @gSyl8ib
      (synWrex n (synCnnc) (synWa (.classMem (synCpw1 (.cv c)) (.cv n))
          (.classMem (synCpw1 (.cv d)) (.cv n))))
      (.classMem (.cv k) (synCnnc))
      (synWa (synWa (.objMem c k) (.objMem d k))
        (synWa (.neg (.objMem x c)) (.neg (.objMem y d))))
      (synWrex m (synCnnc) (synWa
          (.classMem (synCun (synCpw1 (.cv c)) (synCsn (synCsn (.cv x)))) (.cv m))
          (.classMem (synCun (synCpw1 (.cv d)) (synCsn (synCsn (.cv y)))) (.cv m))))
      (synWrex n (synCnnc) (synWa
          (.classMem (synCun (synCpw1 (.cv c)) (synCsn (synCsn (.cv x)))) (.cv n))
          (.classMem (synCun (synCpw1 (.cv d)) (synCsn (synCsn (.cv y)))) (.cv n))))
      p0087 p0091
  have p0093 :=
    @gCom12
      (synWrex n (synCnnc) (synWa (.classMem (synCpw1 (.cv c)) (.cv n))
          (.classMem (synCpw1 (.cv d)) (.cv n))))
      (.classMem (.cv k) (synCnnc))
      (.imp (synWa (synWa (.objMem c k) (.objMem d k))
          (synWa (.neg (.objMem x c)) (.neg (.objMem y d)))) (synWrex n (synCnnc) (synWa
            (.classMem (synCun (synCpw1 (.cv c)) (synCsn (synCsn (.cv x)))) (.cv n))
            (.classMem (synCun (synCpw1 (.cv d)) (synCsn (synCsn (.cv y)))) (.cv n)))))
      p0092
  have p0094 :=
    @gImp31 (.classMem (.cv k) (synCnnc))
      (synWrex n (synCnnc) (synWa (.classMem (synCpw1 (.cv c)) (.cv n))
          (.classMem (synCpw1 (.cv d)) (.cv n))))
      (synWa (synWa (.objMem c k) (.objMem d k))
        (synWa (.neg (.objMem x c)) (.neg (.objMem y d))))
      (synWrex n (synCnnc) (synWa
          (.classMem (synCun (synCpw1 (.cv c)) (synCsn (synCsn (.cv x)))) (.cv n))
          (.classMem (synCun (synCpw1 (.cv d)) (synCsn (synCsn (.cv y)))) (.cv n))))
      p0093
  have p0095 := @gPw1eq (.cv a) (synCun (.cv c) (synCsn (.cv x)))
  have p0096 := @gPw1un (.cv c) (synCsn (.cv x))
  have p0097 := @gPw1sn (.cv x) p0056
  have p0098 :=
    @gUneq2i (synCpw1 (synCsn (.cv x))) (synCsn (synCsn (.cv x))) (synCpw1 (.cv c))
      p0097
  have p0099 :=
    @gEqtri (synCpw1 (synCun (.cv c) (synCsn (.cv x))))
      (synCun (synCpw1 (.cv c)) (synCpw1 (synCsn (.cv x))))
      (synCun (synCpw1 (.cv c)) (synCsn (synCsn (.cv x)))) p0096 p0098
  have p0100 :=
    @gSyl6eq (.classEq (.cv a) (synCun (.cv c) (synCsn (.cv x)))) (synCpw1 (.cv a))
      (synCpw1 (synCun (.cv c) (synCsn (.cv x))))
      (synCun (synCpw1 (.cv c)) (synCsn (synCsn (.cv x)))) p0095 p0099
  have p0101 :=
    @gEleq1d (.classEq (.cv a) (synCun (.cv c) (synCsn (.cv x)))) (synCpw1 (.cv a))
      (synCun (synCpw1 (.cv c)) (synCsn (synCsn (.cv x)))) (.cv n) p0100
  have p0102 := @gPw1eq (.cv b) (synCun (.cv d) (synCsn (.cv y)))
  have p0103 := @gPw1un (.cv d) (synCsn (.cv y))
  have p0104 := @gPw1sn (.cv y) p0058
  have p0105 :=
    @gUneq2i (synCpw1 (synCsn (.cv y))) (synCsn (synCsn (.cv y))) (synCpw1 (.cv d))
      p0104
  have p0106 :=
    @gEqtri (synCpw1 (synCun (.cv d) (synCsn (.cv y))))
      (synCun (synCpw1 (.cv d)) (synCpw1 (synCsn (.cv y))))
      (synCun (synCpw1 (.cv d)) (synCsn (synCsn (.cv y)))) p0103 p0105
  have p0107 :=
    @gSyl6eq (.classEq (.cv b) (synCun (.cv d) (synCsn (.cv y)))) (synCpw1 (.cv b))
      (synCpw1 (synCun (.cv d) (synCsn (.cv y))))
      (synCun (synCpw1 (.cv d)) (synCsn (synCsn (.cv y)))) p0102 p0106
  have p0108 :=
    @gEleq1d (.classEq (.cv b) (synCun (.cv d) (synCsn (.cv y)))) (synCpw1 (.cv b))
      (synCun (synCpw1 (.cv d)) (synCsn (synCsn (.cv y)))) (.cv n) p0107
  have p0109 :=
    @gBi2anan9 (.classEq (.cv a) (synCun (.cv c) (synCsn (.cv x))))
      (.classMem (synCpw1 (.cv a)) (.cv n))
      (.classMem (synCun (synCpw1 (.cv c)) (synCsn (synCsn (.cv x)))) (.cv n))
      (.classEq (.cv b) (synCun (.cv d) (synCsn (.cv y))))
      (.classMem (synCpw1 (.cv b)) (.cv n))
      (.classMem (synCun (synCpw1 (.cv d)) (synCsn (synCsn (.cv y)))) (.cv n)) p0101
      p0108
  have freeVariableCertificate35 :
    n ∉
      ((synWa (.classEq (.cv a) (synCun (.cv c) (synCsn (.cv x))))
          (.classEq (.cv b) (synCun (.cv d) (synCsn (.cv y)))))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
      Finset.mem_singleton, fresh_n_ne_a, fresh_n_ne_c, fresh_n_ne_x, fresh_n_ne_b,
      fresh_n_ne_d, fresh_n_ne_y, or_false, not_false_eq_true]
  have p0110 :=
    @gRexbidv
      (synWa (.classEq (.cv a) (synCun (.cv c) (synCsn (.cv x))))
        (.classEq (.cv b) (synCun (.cv d) (synCsn (.cv y)))))
      (synWa (.classMem (synCpw1 (.cv a)) (.cv n)) (.classMem (synCpw1 (.cv b)) (.cv n)))
      (synWa (.classMem (synCun (synCpw1 (.cv c)) (synCsn (synCsn (.cv x)))) (.cv n))
        (.classMem (synCun (synCpw1 (.cv d)) (synCsn (synCsn (.cv y)))) (.cv n)))
      n (synCnnc) freeVariableCertificate35 p0109
  have p0111 :=
    @gSyl5ibrcom
      (synWa (synWa (.classMem (.cv k) (synCnnc)) (synWrex n (synCnnc)
            (synWa (.classMem (synCpw1 (.cv c)) (.cv n))
              (.classMem (synCpw1 (.cv d)) (.cv n)))))
        (synWa (synWa (.objMem c k) (.objMem d k))
          (synWa (.neg (.objMem x c)) (.neg (.objMem y d)))))
      (synWrex n (synCnnc) (synWa (.classMem (synCpw1 (.cv a)) (.cv n))
          (.classMem (synCpw1 (.cv b)) (.cv n))))
      (synWa (.classEq (.cv a) (synCun (.cv c) (synCsn (.cv x))))
        (.classEq (.cv b) (synCun (.cv d) (synCsn (.cv y)))))
      (synWrex n (synCnnc) (synWa
          (.classMem (synCun (synCpw1 (.cv c)) (synCsn (synCsn (.cv x)))) (.cv n))
          (.classMem (synCun (synCpw1 (.cv d)) (synCsn (synCsn (.cv y)))) (.cv n))))
      p0094 p0110
  have p0112 :=
    @gSylan2b
      (synWa (synWa (.objMem c k) (.objMem d k))
        (synWa (.classMem (.cv x) (synCcompl (.cv c)))
          (.classMem (.cv y) (synCcompl (.cv d)))))
      (synWa (.classMem (.cv k) (synCnnc)) (synWrex n (synCnnc)
          (synWa (.classMem (synCpw1 (.cv c)) (.cv n))
            (.classMem (synCpw1 (.cv d)) (.cv n)))))
      (synWa (synWa (.objMem c k) (.objMem d k))
        (synWa (.neg (.objMem x c)) (.neg (.objMem y d))))
      (.imp (synWa (.classEq (.cv a) (synCun (.cv c) (synCsn (.cv x))))
          (.classEq (.cv b) (synCun (.cv d) (synCsn (.cv y))))) (synWrex n (synCnnc)
          (synWa (.classMem (synCpw1 (.cv a)) (.cv n))
            (.classMem (synCpw1 (.cv b)) (.cv n)))))
      p0061 p0111
  have p0113 :=
    @gExpr
      (synWa (.classMem (.cv k) (synCnnc)) (synWrex n (synCnnc)
          (synWa (.classMem (synCpw1 (.cv c)) (.cv n))
            (.classMem (synCpw1 (.cv d)) (.cv n)))))
      (synWa (.objMem c k) (.objMem d k))
      (synWa (.classMem (.cv x) (synCcompl (.cv c))) (.classMem (.cv y) (synCcompl (.cv d))))
      (.imp (synWa (.classEq (.cv a) (synCun (.cv c) (synCsn (.cv x))))
          (.classEq (.cv b) (synCun (.cv d) (synCsn (.cv y))))) (synWrex n (synCnnc)
          (synWa (.classMem (synCpw1 (.cv a)) (.cv n))
            (.classMem (synCpw1 (.cv b)) (.cv n)))))
      p0112
  have p0114 :=
    @gAnasss (.classMem (.cv k) (synCnnc))
      (synWrex n (synCnnc) (synWa (.classMem (synCpw1 (.cv c)) (.cv n))
          (.classMem (synCpw1 (.cv d)) (.cv n))))
      (synWa (.objMem c k) (.objMem d k))
      (.imp (synWa (.classMem (.cv x) (synCcompl (.cv c)))
          (.classMem (.cv y) (synCcompl (.cv d)))) (.imp
          (synWa (.classEq (.cv a) (synCun (.cv c) (synCsn (.cv x))))
            (.classEq (.cv b) (synCun (.cv d) (synCsn (.cv y))))) (synWrex n (synCnnc)
            (synWa (.classMem (synCpw1 (.cv a)) (.cv n))
              (.classMem (synCpw1 (.cv b)) (.cv n))))))
      p0113
  have freeVariableCertificate36 :
    x ∉
      ((synWrex n (synCnnc) (synWa (.classMem (synCpw1 (.cv a)) (.cv n))
            (.classMem (synCpw1 (.cv b)) (.cv n))))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
      Finset.mem_singleton, Finset.notMem_empty, fresh_x_ne_a, fresh_x_ne_n, fresh_x_ne_b,
      or_false, and_false, not_false_eq_true]
  have freeVariableCertificate37 :
    y ∉
      ((synWrex n (synCnnc) (synWa (.classMem (synCpw1 (.cv a)) (.cv n))
            (.classMem (synCpw1 (.cv b)) (.cv n))))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
      Finset.mem_singleton, Finset.notMem_empty, fresh_y_ne_a, fresh_y_ne_n, fresh_y_ne_b,
      or_false, and_false, not_false_eq_true]
  have freeVariableCertificate38 :
    x ∉
      ((synWa (.classMem (.cv k) (synCnnc)) (synWa (synWrex n (synCnnc)
              (synWa (.classMem (synCpw1 (.cv c)) (.cv n))
                (.classMem (synCpw1 (.cv d)) (.cv n))))
            (synWa (.objMem c k) (.objMem d k))))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
      NFChoice.Compiler.CoreFVSimp.fv_wff_objMem, Finset.mem_union, Finset.mem_erase,
      Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, fresh_x_ne_k,
      fresh_x_ne_c, fresh_x_ne_n, fresh_x_ne_d, or_false, and_false, not_false_eq_true]
  have freeVariableCertificate39 :
    y ∉
      ((synWa (.classMem (.cv k) (synCnnc)) (synWa (synWrex n (synCnnc)
              (synWa (.classMem (synCpw1 (.cv c)) (.cv n))
                (.classMem (synCpw1 (.cv d)) (.cv n))))
            (synWa (.objMem c k) (.objMem d k))))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
      NFChoice.Compiler.CoreFVSimp.fv_wff_objMem, Finset.mem_union, Finset.mem_erase,
      Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, fresh_y_ne_k,
      fresh_y_ne_c, fresh_y_ne_n, fresh_y_ne_d, or_false, and_false, not_false_eq_true]
  have p0115 :=
    @gRexlimdvv
      (synWa (.classMem (.cv k) (synCnnc)) (synWa (synWrex n (synCnnc)
            (synWa (.classMem (synCpw1 (.cv c)) (.cv n))
              (.classMem (synCpw1 (.cv d)) (.cv n)))) (synWa (.objMem c k) (.objMem d k))))
      (synWa (.classEq (.cv a) (synCun (.cv c) (synCsn (.cv x))))
        (.classEq (.cv b) (synCun (.cv d) (synCsn (.cv y)))))
      (synWrex n (synCnnc) (synWa (.classMem (synCpw1 (.cv a)) (.cv n))
          (.classMem (synCpw1 (.cv b)) (.cv n))))
      x y (synCcompl (.cv c)) (synCcompl (.cv d)) freeVariableCertificate15
      freeVariableCertificate36 freeVariableCertificate37 freeVariableCertificate38
      freeVariableCertificate39 (show x ≠ y from (by exact fresh_x_ne_y)) p0114
  have p0116 :=
    @gExp32 (.classMem (.cv k) (synCnnc))
      (synWrex n (synCnnc) (synWa (.classMem (synCpw1 (.cv c)) (.cv n))
          (.classMem (synCpw1 (.cv d)) (.cv n))))
      (synWa (.objMem c k) (.objMem d k))
      (.imp (synWrex x (synCcompl (.cv c)) (synWrex y (synCcompl (.cv d))
            (synWa (.classEq (.cv a) (synCun (.cv c) (synCsn (.cv x))))
              (.classEq (.cv b) (synCun (.cv d) (synCsn (.cv y))))))) (synWrex n (synCnnc)
          (synWa (.classMem (synCpw1 (.cv a)) (.cv n))
            (.classMem (synCpw1 (.cv b)) (.cv n)))))
      p0115
  have p0117 :=
    @gSylan9r
      (synWral a (.cv k) (synWral b (.cv k) (synWrex n (synCnnc)
            (synWa (.classMem (synCpw1 (.cv a)) (.cv n))
              (.classMem (synCpw1 (.cv b)) (.cv n))))))
      (synWa (.objMem c k) (.objMem d k))
      (synWrex n (synCnnc) (synWa (.classMem (synCpw1 (.cv c)) (.cv n))
          (.classMem (synCpw1 (.cv d)) (.cv n))))
      (.classMem (.cv k) (synCnnc))
      (.imp (synWa (.objMem c k) (.objMem d k)) (.imp (synWrex x (synCcompl (.cv c))
            (synWrex y (synCcompl (.cv d))
              (synWa (.classEq (.cv a) (synCun (.cv c) (synCsn (.cv x))))
                (.classEq (.cv b) (synCun (.cv d) (synCsn (.cv y))))))) (synWrex n (synCnnc)
            (synWa (.classMem (synCpw1 (.cv a)) (.cv n))
              (.classMem (synCpw1 (.cv b)) (.cv n))))))
      p0055 p0116
  have p0118 :=
    @gPm243d
      (synWa (.classMem (.cv k) (synCnnc)) (synWral a (.cv k) (synWral b (.cv k)
            (synWrex n (synCnnc) (synWa (.classMem (synCpw1 (.cv a)) (.cv n))
                (.classMem (synCpw1 (.cv b)) (.cv n)))))))
      (synWa (.objMem c k) (.objMem d k))
      (.imp (synWrex x (synCcompl (.cv c)) (synWrex y (synCcompl (.cv d))
            (synWa (.classEq (.cv a) (synCun (.cv c) (synCsn (.cv x))))
              (.classEq (.cv b) (synCun (.cv d) (synCsn (.cv y))))))) (synWrex n (synCnnc)
          (synWa (.classMem (synCpw1 (.cv a)) (.cv n))
            (.classMem (synCpw1 (.cv b)) (.cv n)))))
      p0117
  have p0119_e00_recanon :
    Nominal.NPrf
      (.imp (synWa (.classMem (.cv k) (synCnnc)) (synWral a (.cv k) (synWral b (.cv k)
              (synWrex n (synCnnc) (synWa (.classMem (synCpw1 (.cv a)) (.cv n))
                  (.classMem (synCpw1 (.cv b)) (.cv n)))))))
        (.imp (synWa (.classMem (.cv c) (.cv k)) (.classMem (.cv d) (.cv k))) (.imp
            (synWrex x (synCcompl (.cv c)) (synWrex y (synCcompl (.cv d))
                (synWa (.classEq (.cv a) (synCun (.cv c) (synCsn (.cv x))))
                  (.classEq (.cv b) (synCun (.cv d) (synCsn (.cv y)))))))
            (synWrex n (synCnnc) (synWa (.classMem (synCpw1 (.cv a)) (.cv n))
                (.classMem (synCpw1 (.cv b)) (.cv n))))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWa synCnnc synCint synWral synWrex synWex synCcompl synCnin
          synWnan
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.objMem_classMem _ _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              exact Nominal.RecanonTransportDev.TRecanonWff.objMem_classMem _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0118
  have freeVariableCertificate40 :
    c ∉
      ((synWrex n (synCnnc) (synWa (.classMem (synCpw1 (.cv a)) (.cv n))
            (.classMem (synCpw1 (.cv b)) (.cv n))))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
      Finset.mem_singleton, Finset.notMem_empty, fresh_c_ne_a, fresh_c_ne_n, fresh_c_ne_b,
      or_false, and_false, not_false_eq_true]
  have freeVariableCertificate41 :
    d ∉
      ((synWrex n (synCnnc) (synWa (.classMem (synCpw1 (.cv a)) (.cv n))
            (.classMem (synCpw1 (.cv b)) (.cv n))))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
      Finset.mem_singleton, Finset.notMem_empty, fresh_d_ne_a, fresh_d_ne_n, fresh_d_ne_b,
      or_false, and_false, not_false_eq_true]
  have freeVariableCertificate42 :
    c ∉
      ((synWa (.classMem (.cv k) (synCnnc)) (synWral a (.cv k) (synWral b (.cv k)
              (synWrex n (synCnnc) (synWa (.classMem (synCpw1 (.cv a)) (.cv n))
                  (.classMem (synCpw1 (.cv b)) (.cv n)))))))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union,
      Finset.mem_erase, Finset.mem_singleton, Finset.notMem_empty, fresh_c_ne_k,
      fresh_c_ne_a, fresh_c_ne_n, fresh_c_ne_b, or_false, and_false, not_false_eq_true]
  have freeVariableCertificate43 :
    d ∉
      ((synWa (.classMem (.cv k) (synCnnc)) (synWral a (.cv k) (synWral b (.cv k)
              (synWrex n (synCnnc) (synWa (.classMem (synCpw1 (.cv a)) (.cv n))
                  (.classMem (synCpw1 (.cv b)) (.cv n)))))))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union,
      Finset.mem_erase, Finset.mem_singleton, Finset.notMem_empty, fresh_d_ne_k,
      fresh_d_ne_a, fresh_d_ne_n, fresh_d_ne_b, or_false, and_false, not_false_eq_true]
  have p0119 :=
    @gRexlimdvv
      (synWa (.classMem (.cv k) (synCnnc)) (synWral a (.cv k) (synWral b (.cv k)
            (synWrex n (synCnnc) (synWa (.classMem (synCpw1 (.cv a)) (.cv n))
                (.classMem (synCpw1 (.cv b)) (.cv n)))))))
      (synWrex x (synCcompl (.cv c)) (synWrex y (synCcompl (.cv d))
          (synWa (.classEq (.cv a) (synCun (.cv c) (synCsn (.cv x))))
            (.classEq (.cv b) (synCun (.cv d) (synCsn (.cv y)))))))
      (synWrex n (synCnnc) (synWa (.classMem (synCpw1 (.cv a)) (.cv n))
          (.classMem (synCpw1 (.cv b)) (.cv n))))
      c d (.cv k) (.cv k) freeVariableCertificate11 freeVariableCertificate40
      freeVariableCertificate41 freeVariableCertificate42 freeVariableCertificate43
      (show c ≠ d from (by exact fresh_c_ne_d)) p0119_e00_recanon
  have p0120 :=
    @gSyl5bi
      (synWa (.classMem (.cv a) (synCplc (.cv k) (synC1c)))
        (.classMem (.cv b) (synCplc (.cv k) (synC1c))))
      (synWrex c (.cv k) (synWrex d (.cv k) (synWrex x (synCcompl (.cv c))
            (synWrex y (synCcompl (.cv d))
              (synWa (.classEq (.cv a) (synCun (.cv c) (synCsn (.cv x))))
                (.classEq (.cv b) (synCun (.cv d) (synCsn (.cv y)))))))))
      (synWa (.classMem (.cv k) (synCnnc)) (synWral a (.cv k) (synWral b (.cv k)
            (synWrex n (synCnnc) (synWa (.classMem (synCpw1 (.cv a)) (.cv n))
                (.classMem (synCpw1 (.cv b)) (.cv n)))))))
      (synWrex n (synCnnc) (synWa (.classMem (synCpw1 (.cv a)) (.cv n))
          (.classMem (synCpw1 (.cv b)) (.cv n))))
      p0045 p0119
  have p0121 :=
    @gExp3a
      (synWa (.classMem (.cv k) (synCnnc)) (synWral a (.cv k) (synWral b (.cv k)
            (synWrex n (synCnnc) (synWa (.classMem (synCpw1 (.cv a)) (.cv n))
                (.classMem (synCpw1 (.cv b)) (.cv n)))))))
      (.classMem (.cv a) (synCplc (.cv k) (synC1c)))
      (.classMem (.cv b) (synCplc (.cv k) (synC1c)))
      (synWrex n (synCnnc) (synWa (.classMem (synCpw1 (.cv a)) (.cv n))
          (.classMem (synCpw1 (.cv b)) (.cv n))))
      p0120
  have p0122 :=
    @gRalrimd
      (synWa (.classMem (.cv k) (synCnnc)) (synWral a (.cv k) (synWral b (.cv k)
            (synWrex n (synCnnc) (synWa (.classMem (synCpw1 (.cv a)) (.cv n))
                (.classMem (synCpw1 (.cv b)) (.cv n)))))))
      (.classMem (.cv a) (synCplc (.cv k) (synC1c)))
      (synWrex n (synCnnc) (synWa (.classMem (synCpw1 (.cv a)) (.cv n))
          (.classMem (synCpw1 (.cv b)) (.cv n))))
      b (synCplc (.cv k) (synC1c)) p0037 p0038 p0121
  have p0123 :=
    @gRalrimi
      (synWa (.classMem (.cv k) (synCnnc)) (synWral a (.cv k) (synWral b (.cv k)
            (synWrex n (synCnnc) (synWa (.classMem (synCpw1 (.cv a)) (.cv n))
                (.classMem (synCpw1 (.cv b)) (.cv n)))))))
      (synWral b (synCplc (.cv k) (synC1c)) (synWrex n (synCnnc)
          (synWa (.classMem (synCpw1 (.cv a)) (.cv n))
            (.classMem (synCpw1 (.cv b)) (.cv n)))))
      a (synCplc (.cv k) (synC1c)) p0034 p0122
  have p0124 :=
    @gEx (.classMem (.cv k) (synCnnc))
      (synWral a (.cv k) (synWral b (.cv k) (synWrex n (synCnnc)
            (synWa (.classMem (synCpw1 (.cv a)) (.cv n))
              (.classMem (synCpw1 (.cv b)) (.cv n))))))
      (synWral a (synCplc (.cv k) (synC1c)) (synWral b (synCplc (.cv k) (synC1c))
          (synWrex n (synCnnc) (synWa (.classMem (synCpw1 (.cv a)) (.cv n))
              (.classMem (synCpw1 (.cv b)) (.cv n))))))
      p0123
  have p0125_e02_recanon :
    Nominal.NPrf
      (.imp (.objEq m k) (synWb (synWral a (.cv m) (synWral b (.cv m) (synWrex n (synCnnc)
                (synWa (.classMem (synCpw1 (.cv a)) (.cv n))
                  (.classMem (synCpw1 (.cv b)) (.cv n)))))) (synWral a (.cv k)
            (synWral b (.cv k) (synWrex n (synCnnc)
                (synWa (.classMem (synCpw1 (.cv a)) (.cv n))
                  (.classMem (synCpw1 (.cv b)) (.cv n)))))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWral
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0004
  have freeVariableCertificate44 :
    m ∉
      ((synWral a (.cv k) (synWral b (.cv k) (synWrex n (synCnnc)
              (synWa (.classMem (synCpw1 (.cv a)) (.cv n))
                (.classMem (synCpw1 (.cv b)) (.cv n))))))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union,
      Finset.mem_erase, Finset.mem_singleton, Finset.notMem_empty, fresh_m_ne_k,
      fresh_m_ne_a, fresh_m_ne_n, fresh_m_ne_b, or_false, and_false, not_false_eq_true]
  have freeVariableCertificate45 :
    k ∉
      ((synWral a (.cv m) (synWral b (.cv m) (synWrex n (synCnnc)
              (synWa (.classMem (synCpw1 (.cv a)) (.cv n))
                (.classMem (synCpw1 (.cv b)) (.cv n))))))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union,
      Finset.mem_erase, Finset.mem_singleton, Finset.notMem_empty, fresh_k_ne_m,
      fresh_k_ne_a, fresh_k_ne_n, fresh_k_ne_b, or_false, and_false, not_false_eq_true]
  have freeVariableCertificate46 :
    m ∉
      ((synWral a (synC0c) (synWral b (synC0c) (synWrex n (synCnnc)
              (synWa (.classMem (synCpw1 (.cv a)) (.cv n))
                (.classMem (synCpw1 (.cv b)) (.cv n))))))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
      Finset.mem_singleton, Finset.notMem_empty, fresh_m_ne_a, fresh_m_ne_n, fresh_m_ne_b,
      or_false, and_false, not_false_eq_true]
  have freeVariableCertificate47 :
    m ∉
      ((synWral a M (synWral b M (synWrex n (synCnnc)
              (synWa (.classMem (synCpw1 (.cv a)) (.cv n))
                (.classMem (synCpw1 (.cv b)) (.cv n))))))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
      Finset.mem_singleton, Finset.notMem_empty, fresh_m_not_M, fresh_m_ne_a,
      fresh_m_ne_n, fresh_m_ne_b, or_false, and_false, not_false_eq_true]
  have freeVariableCertificate48 :
    m ∉
      ((synWral a (synCplc (.cv k) (synC1c)) (synWral b (synCplc (.cv k) (synC1c))
            (synWrex n (synCnnc) (synWa (.classMem (synCpw1 (.cv a)) (.cv n))
                (.classMem (synCpw1 (.cv b)) (.cv n))))))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union,
      Finset.mem_erase, Finset.mem_singleton, Finset.notMem_empty, fresh_m_ne_k,
      fresh_m_ne_a, fresh_m_ne_n, fresh_m_ne_b, or_false, and_false, not_false_eq_true]
  have p0125 :=
    @gFinds
      (synWral a (.cv m) (synWral b (.cv m) (synWrex n (synCnnc)
            (synWa (.classMem (synCpw1 (.cv a)) (.cv n))
              (.classMem (synCpw1 (.cv b)) (.cv n))))))
      (synWral a (synC0c) (synWral b (synC0c) (synWrex n (synCnnc)
            (synWa (.classMem (synCpw1 (.cv a)) (.cv n))
              (.classMem (synCpw1 (.cv b)) (.cv n))))))
      (synWral a (.cv k) (synWral b (.cv k) (synWrex n (synCnnc)
            (synWa (.classMem (synCpw1 (.cv a)) (.cv n))
              (.classMem (synCpw1 (.cv b)) (.cv n))))))
      (synWral a (synCplc (.cv k) (synC1c)) (synWral b (synCplc (.cv k) (synC1c))
          (synWrex n (synCnnc) (synWa (.classMem (synCpw1 (.cv a)) (.cv n))
              (.classMem (synCpw1 (.cv b)) (.cv n))))))
      (synWral a M (synWral b M (synWrex n (synCnnc)
            (synWa (.classMem (synCpw1 (.cv a)) (.cv n))
              (.classMem (synCpw1 (.cv b)) (.cv n))))))
      m k M (by exact (show m ∉ (M).fv from (by exact fresh_m_not_M)))
      freeVariableCertificate44 freeVariableCertificate45 freeVariableCertificate46
      freeVariableCertificate47 freeVariableCertificate48
      (show m ≠ k from (by exact fresh_m_ne_k)) p0000 p0002 p0125_e02_recanon p0006 p0008
      p0031 p0124
  have p0126 := @gPw1eq (.cv a) A
  have p0127 :=
    @gEleq1d (.classEq (.cv a) A) (synCpw1 (.cv a)) (synCpw1 A) (.cv n) p0126
  have p0128 :=
    @gAnbi1d (.classEq (.cv a) A) (.classMem (synCpw1 (.cv a)) (.cv n))
      (.classMem (synCpw1 A) (.cv n)) (.classMem (synCpw1 (.cv b)) (.cv n)) p0127
  have freeVariableCertificate49 : n ∉ ((Wff.classEq (.cv a) A)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      fresh_n_ne_a, dv_A_n, or_false, not_false_eq_true]
  have p0129 :=
    @gRexbidv (.classEq (.cv a) A)
      (synWa (.classMem (synCpw1 (.cv a)) (.cv n)) (.classMem (synCpw1 (.cv b)) (.cv n)))
      (synWa (.classMem (synCpw1 A) (.cv n)) (.classMem (synCpw1 (.cv b)) (.cv n))) n
      (synCnnc) freeVariableCertificate49 p0128
  have p0130 := @gPw1eq (.cv b) B
  have p0131 :=
    @gEleq1d (.classEq (.cv b) B) (synCpw1 (.cv b)) (synCpw1 B) (.cv n) p0130
  have p0132 :=
    @gAnbi2d (.classEq (.cv b) B) (.classMem (synCpw1 (.cv b)) (.cv n))
      (.classMem (synCpw1 B) (.cv n)) (.classMem (synCpw1 A) (.cv n)) p0131
  have freeVariableCertificate50 : n ∉ ((Wff.classEq (.cv b) B)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      fresh_n_ne_b, dv_B_n, or_false, not_false_eq_true]
  have p0133 :=
    @gRexbidv (.classEq (.cv b) B)
      (synWa (.classMem (synCpw1 A) (.cv n)) (.classMem (synCpw1 (.cv b)) (.cv n)))
      (synWa (.classMem (synCpw1 A) (.cv n)) (.classMem (synCpw1 B) (.cv n))) n
      (synCnnc) freeVariableCertificate50 p0132
  have freeVariableCertificate51 :
    a ∉
      ((synWrex n (synCnnc) (synWa (.classMem (synCpw1 A) (.cv n))
            (.classMem (synCpw1 (.cv b)) (.cv n))))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
      Finset.mem_singleton, Finset.notMem_empty, fresh_a_not_A, fresh_a_ne_n,
      fresh_a_ne_b, or_false, and_false, not_false_eq_true]
  have freeVariableCertificate52 :
    b ∉
      ((synWrex n (synCnnc) (synWa (.classMem (synCpw1 A) (.cv n))
            (.classMem (synCpw1 B) (.cv n))))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
      Finset.mem_singleton, Finset.notMem_empty, fresh_b_not_A, fresh_b_ne_n,
      fresh_b_not_B, or_false, and_false, not_false_eq_true]
  have p0134 :=
    @gRspc2v
      (synWrex n (synCnnc) (synWa (.classMem (synCpw1 (.cv a)) (.cv n))
          (.classMem (synCpw1 (.cv b)) (.cv n))))
      (synWrex n (synCnnc)
        (synWa (.classMem (synCpw1 A) (.cv n)) (.classMem (synCpw1 B) (.cv n))))
      (synWrex n (synCnnc)
        (synWa (.classMem (synCpw1 A) (.cv n)) (.classMem (synCpw1 (.cv b)) (.cv n))))
      a b A B M M (by exact (show a ∉ (A).fv from (by exact fresh_a_not_A)))
      (by exact (show b ∉ (A).fv from (by exact fresh_b_not_A)))
      (by exact (show b ∉ (B).fv from (by exact fresh_b_not_B)))
      (by exact (show a ∉ (M).fv from (by exact fresh_a_not_M)))
      (by exact (show a ∉ (M).fv from (by exact fresh_a_not_M)))
      (by exact (show b ∉ (M).fv from (by exact fresh_b_not_M))) freeVariableCertificate51
      freeVariableCertificate52 (show a ≠ b from (by exact fresh_a_ne_b)) p0129 p0133
  have p0135 :=
    @gSyl5com (.classMem M (synCnnc))
      (synWral a M (synWral b M (synWrex n (synCnnc)
            (synWa (.classMem (synCpw1 (.cv a)) (.cv n))
              (.classMem (synCpw1 (.cv b)) (.cv n))))))
      (synWa (.classMem A M) (.classMem B M))
      (synWrex n (synCnnc)
        (synWa (.classMem (synCpw1 A) (.cv n)) (.classMem (synCpw1 B) (.cv n))))
      p0125 p0134
  have p0136 :=
    @gN3impib (.classMem M (synCnnc)) (.classMem A M) (.classMem B M)
      (synWrex n (synCnnc)
        (synWa (.classMem (synCpw1 A) (.cv n)) (.classMem (synCpw1 B) (.cv n))))
      p0135
  exact p0136


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk009StructuralPart050`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_ncfinlowerlem1`. -/
@[expose]
noncomputable def gNcfinlowerlem1 (m : Var) (n : Var) (a : Var) (b : Var)
    (dv_a_b : a ≠ b) (dv_a_m : a ≠ m) (dv_a_n : a ≠ n) (dv_b_m : b ≠ m) (dv_b_n : b ≠ n)
    (_dv_m_n : m ≠ n) :
    Nominal.NPrf
      (.classMem (.cab m (.all a (.all b (.imp (synWa (.classMem (synCpw1 (.cv a)) (.cv m))
                  (.classMem (synCpw1 (.cv b)) (.cv m)))
                (synWrex n (synCnnc) (synWa (.objMem a n) (.objMem b n))))))) (synCvv)) :=
  by
  let proofSupport : Finset Var :=
    ({ m } : Finset Var) ∪ ({ n } : Finset Var) ∪ ({ a } : Finset Var) ∪
      ({ b } : Finset Var)
  let t : Var := freshVar proofSupport 0
  let x : Var := freshVar proofSupport 1
  have fresh_t : t ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_t_ne_m : t ≠ m := by
    intro h
    exact
      fresh_t
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_t_ne_n : t ≠ n := by
    intro h
    exact
      fresh_t
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_n_ne_t : n ≠ t := Ne.symm fresh_t_ne_n
  have fresh_t_ne_a : t ≠ a := by
    intro h
    exact
      fresh_t
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_a_ne_t : a ≠ t := Ne.symm fresh_t_ne_a
  have fresh_t_ne_b : t ≠ b := by
    intro h
    exact fresh_t (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_b_ne_t : b ≠ t := Ne.symm fresh_t_ne_b
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_x_ne_m : x ≠ m := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_x_ne_a : x ≠ a := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_x_ne_b : x ≠ b := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_t_ne_x : t ≠ x :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_x_ne_t : x ≠ t := Ne.symm fresh_t_ne_x
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
  let syntaxClass0006 : Class := (synCxpk (synCvv) syntaxClass0005)
  let syntaxClass0007 : Class := (synCins2k syntaxClass0005)
  let syntaxClass0008 : Class := (synCin syntaxClass0006 syntaxClass0007)
  let syntaxClass0009 : Class :=
    (synCin (synCins2k (synCcnvk (synCssetk))) (synCins3k (synCcnvk (synCssetk))))
  let syntaxClass0010 : Class :=
    (synCimak syntaxClass0009 (synCpw1 (synCpw1 (synCnnc))))
  let syntaxClass0011 : Class := (synCsik syntaxClass0010)
  let syntaxClass0012 : Class := (synCins3k syntaxClass0011)
  let syntaxClass0013 : Class := (synCdif syntaxClass0008 syntaxClass0012)
  let syntaxClass0014 : Class :=
    (synCimak syntaxClass0013 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))
  let syntaxFormula0015 : Wff := (.classMem (synCopk (.cv t) (.cv m)) syntaxClass0014)
  let syntaxFormula0016 : Wff :=
    (synWa (.classMem (.cv t) (synCpw1 (synC1c))) syntaxFormula0015)
  let syntaxFormula0017 : Wff :=
    (synWa (.classEq (.cv t) (synCsn (synCsn (.cv a)))) syntaxFormula0015)
  let syntaxFormula0018 : Wff := (synWex a syntaxFormula0017)
  let syntaxFormula0019 : Wff := (synWrex t (synCpw1 (synC1c)) syntaxFormula0015)
  let syntaxFormula0020 : Wff := (synWex t syntaxFormula0017)
  let syntaxFormula0021 : Wff := (synWex a syntaxFormula0020)
  let syntaxFormula0022 : Wff :=
    (.classMem (synCopk (synCsn (synCsn (.cv a))) (.cv m)) syntaxClass0014)
  let syntaxFormula0023 : Wff :=
    (.classMem (synCopk (.cv t) (synCopk (synCsn (synCsn (.cv a))) (.cv m)))
      syntaxClass0013)
  let syntaxFormula0024 : Wff :=
    (synWa (.classMem (.cv t) (synCpw1 (synCpw1 (synCpw1 (synC1c))))) syntaxFormula0023)
  let syntaxFormula0025 : Wff :=
    (synWa (.classEq (.cv t) (synCsn (synCsn (synCsn (synCsn (.cv b))))))
      syntaxFormula0023)
  let syntaxFormula0026 : Wff := (synWex b syntaxFormula0025)
  let syntaxFormula0027 : Wff :=
    (synWrex t (synCpw1 (synCpw1 (synCpw1 (synC1c)))) syntaxFormula0023)
  let syntaxFormula0028 : Wff := (synWex t syntaxFormula0025)
  let syntaxFormula0029 : Wff := (synWex b syntaxFormula0028)
  let syntaxClass0030 : Class :=
    (synCopk (synCsn (synCsn (synCsn (synCsn (.cv b)))))
      (synCopk (synCsn (synCsn (.cv a))) (.cv m)))
  let syntaxFormula0031 : Wff := (.classMem syntaxClass0030 syntaxClass0013)
  let syntaxFormula0032 : Wff :=
    (.classMem (synCopk (.cv t) (synCopk (synCsn (synCsn (.cv a))) (.cv m)))
      syntaxClass0004)
  let syntaxFormula0033 : Wff :=
    (synWa (.classMem (.cv t) (synCpw1 (synCpw1 (synC1c)))) syntaxFormula0032)
  let syntaxFormula0034 : Wff :=
    (synWa (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv x))))) syntaxFormula0032)
  let syntaxFormula0035 : Wff := (synWex x syntaxFormula0034)
  let syntaxFormula0036 : Wff :=
    (synWrex t (synCpw1 (synCpw1 (synC1c))) syntaxFormula0032)
  let syntaxFormula0037 : Wff := (synWex t syntaxFormula0034)
  let syntaxFormula0038 : Wff := (synWex x syntaxFormula0037)
  let syntaxClass0039 : Class :=
    (synCopk (synCsn (synCsn (synCsn (.cv x))))
      (synCopk (synCsn (synCsn (.cv a))) (.cv m)))
  let syntaxFormula0040 : Wff := (.classMem syntaxClass0039 syntaxClass0004)
  let syntaxFormula0041 : Wff := (.classMem syntaxClass0039 syntaxClass0003)
  let syntaxFormula0042 : Wff := (.classMem syntaxClass0039 (synCins2k (synCssetk)))
  let syntaxFormula0043 : Wff :=
    (.classMem (synCopk (synCsn (synCsn (.cv a))) (.cv m)) syntaxClass0005)
  let syntaxFormula0044 : Wff := (.classMem syntaxClass0030 syntaxClass0006)
  let syntaxFormula0045 : Wff :=
    (.classMem (synCopk (.cv t) (synCopk (synCsn (synCsn (.cv b))) (.cv m)))
      syntaxClass0004)
  let syntaxFormula0046 : Wff :=
    (synWa (.classMem (.cv t) (synCpw1 (synCpw1 (synC1c)))) syntaxFormula0045)
  let syntaxFormula0047 : Wff :=
    (synWa (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv x))))) syntaxFormula0045)
  let syntaxFormula0048 : Wff := (synWex x syntaxFormula0047)
  let syntaxFormula0049 : Wff :=
    (synWrex t (synCpw1 (synCpw1 (synC1c))) syntaxFormula0045)
  let syntaxFormula0050 : Wff := (synWex t syntaxFormula0047)
  let syntaxFormula0051 : Wff := (synWex x syntaxFormula0050)
  let syntaxClass0052 : Class :=
    (synCopk (synCsn (synCsn (synCsn (.cv x))))
      (synCopk (synCsn (synCsn (.cv b))) (.cv m)))
  let syntaxFormula0053 : Wff := (.classMem syntaxClass0052 syntaxClass0004)
  let syntaxFormula0054 : Wff := (.classMem syntaxClass0052 syntaxClass0003)
  let syntaxFormula0055 : Wff := (.classMem syntaxClass0052 (synCins2k (synCssetk)))
  let syntaxFormula0056 : Wff :=
    (.classMem (synCopk (synCsn (synCsn (.cv b))) (.cv m)) syntaxClass0005)
  let syntaxFormula0057 : Wff := (.classMem syntaxClass0030 syntaxClass0007)
  let syntaxFormula0058 : Wff := (.classMem syntaxClass0030 syntaxClass0008)
  let syntaxFormula0059 : Wff :=
    (synWa (.classMem (synCpw1 (.cv a)) (.cv m)) (.classMem (synCpw1 (.cv b)) (.cv m)))
  let syntaxFormula0060 : Wff :=
    (.classMem (synCopk (.cv t) (synCopk (synCsn (.cv b)) (synCsn (.cv a))))
      syntaxClass0009)
  let syntaxFormula0061 : Wff :=
    (synWa (.classMem (.cv t) (synCpw1 (synCpw1 (synCnnc)))) syntaxFormula0060)
  let syntaxFormula0062 : Wff :=
    (synWa (.classEq (.cv t) (synCsn (synCsn (.cv n)))) syntaxFormula0060)
  let syntaxFormula0063 : Wff := (synWrex n (synCnnc) syntaxFormula0062)
  let syntaxFormula0064 : Wff :=
    (synWrex t (synCpw1 (synCpw1 (synCnnc))) syntaxFormula0060)
  let syntaxFormula0065 : Wff := (synWex t syntaxFormula0062)
  let syntaxFormula0066 : Wff := (synWrex n (synCnnc) syntaxFormula0065)
  let syntaxClass0067 : Class :=
    (synCopk (synCsn (synCsn (.cv n))) (synCopk (synCsn (.cv b)) (synCsn (.cv a))))
  let syntaxFormula0068 : Wff := (.classMem syntaxClass0067 syntaxClass0009)
  let syntaxFormula0069 : Wff :=
    (.classMem syntaxClass0067 (synCins2k (synCcnvk (synCssetk))))
  let syntaxFormula0070 : Wff :=
    (.classMem syntaxClass0067 (synCins3k (synCcnvk (synCssetk))))
  let syntaxFormula0071 : Wff :=
    (.classMem (synCopk (synCsn (.cv b)) (synCsn (.cv a))) syntaxClass0010)
  let syntaxFormula0072 : Wff := (.classMem syntaxClass0030 syntaxClass0012)
  let syntaxFormula0073 : Wff := (.neg syntaxFormula0072)
  let syntaxFormula0074 : Wff :=
    (synWa syntaxFormula0059
      (.neg (synWrex n (synCnnc) (synWa (.objMem a n) (.objMem b n)))))
  let syntaxFormula0075 : Wff := (synWex b syntaxFormula0074)
  let syntaxFormula0076 : Wff :=
    (.imp syntaxFormula0059 (synWrex n (synCnnc) (synWa (.objMem a n) (.objMem b n))))
  let syntaxFormula0077 : Wff := (.all b syntaxFormula0076)
  let syntaxFormula0078 : Wff := (.neg syntaxFormula0077)
  let syntaxClass0079 : Class := (synCimak syntaxClass0014 (synCpw1 (synC1c)))
  let syntaxFormula0080 : Wff := (.classMem (.cv m) syntaxClass0079)
  let syntaxFormula0081 : Wff := (synWex a syntaxFormula0078)
  let syntaxClass0082 : Class := (synCcompl syntaxClass0079)
  let syntaxFormula0083 : Wff := (.all a syntaxFormula0077)
  have p0000 := @gVex m
  have freeVariableCertificate0 : t ∉ (syntaxClass0014).fv := by
    simp only [syntaxClass0000, syntaxClass0001, syntaxClass0002, syntaxClass0003,
      syntaxClass0004, syntaxClass0005, syntaxClass0006, syntaxClass0007, syntaxClass0008,
      syntaxClass0009, syntaxClass0010, syntaxClass0011, syntaxClass0012, syntaxClass0013,
      syntaxClass0014, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union,
      Finset.notMem_empty, or_false, not_false_eq_true]
  have freeVariableCertificate1 : t ∉ ((synCpw1 (synC1c))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.notMem_empty,
      not_false_eq_true]
  have freeVariableCertificate2 : t ∉ ((Class.cv m)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_t_ne_m, not_false_eq_true]
  have p0001 :=
    @gElimak t syntaxClass0014 (synCpw1 (synC1c)) (.cv m) freeVariableCertificate0
      freeVariableCertificate1 freeVariableCertificate2 p0000
  have freeVariableCertificate3 : a ∉ ((Class.cv t)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_a_ne_t, not_false_eq_true]
  have p0002 := @gElpw11c a (.cv t) freeVariableCertificate3
  have p0003 :=
    @gAnbi1i (.classMem (.cv t) (synCpw1 (synC1c)))
      (synWex a (.classEq (.cv t) (synCsn (synCsn (.cv a))))) syntaxFormula0015 p0002
  have freeVariableCertificate4 :
    a ∉ ((Wff.classMem (synCopk (.cv t) (.cv m)) syntaxClass0014)).fv := by
    simp only [syntaxClass0000, syntaxClass0001, syntaxClass0002, syntaxClass0003,
      syntaxClass0004, syntaxClass0005, syntaxClass0006, syntaxClass0007, syntaxClass0008,
      syntaxClass0009, syntaxClass0010, syntaxClass0011, syntaxClass0012, syntaxClass0013,
      syntaxClass0014, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_a_ne_t, dv_a_m, or_false,
      not_false_eq_true]
  have p0004 :=
    @gN1941v (.classEq (.cv t) (synCsn (synCsn (.cv a)))) syntaxFormula0015 a
      freeVariableCertificate4
  have p0005 :=
    @gBitr4i syntaxFormula0016
      (synWa (synWex a (.classEq (.cv t) (synCsn (synCsn (.cv a))))) syntaxFormula0015)
      syntaxFormula0018 p0003 p0004
  have p0006 := @gExbii syntaxFormula0016 syntaxFormula0018 t p0005
  have p0007 := (Nominal.biimpRefl syntaxFormula0019)
  have p0008 := @gExcom syntaxFormula0017 a t
  have p0009 :=
    @gN3bitr4i (synWex t syntaxFormula0016) (synWex t syntaxFormula0018)
      syntaxFormula0019 syntaxFormula0021 p0006 p0007 p0008
  have p0010 := @gSnex (synCsn (.cv a))
  have p0011 := @gOpkeq1 (.cv t) (synCsn (synCsn (.cv a))) (.cv m)
  have p0012 :=
    @gEleq1d (.classEq (.cv t) (synCsn (synCsn (.cv a)))) (synCopk (.cv t) (.cv m))
      (synCopk (synCsn (synCsn (.cv a))) (.cv m)) syntaxClass0014 p0011
  have freeVariableCertificate5 : t ∉ ((synCsn (synCsn (.cv a)))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_t_ne_a,
      not_false_eq_true]
  have freeVariableCertificate6 :
    t ∉
      ((Wff.classMem (synCopk (synCsn (synCsn (.cv a))) (.cv m)) syntaxClass0014)).fv :=
    by
    simp only [syntaxClass0000, syntaxClass0001, syntaxClass0002, syntaxClass0003,
      syntaxClass0004, syntaxClass0005, syntaxClass0006, syntaxClass0007, syntaxClass0008,
      syntaxClass0009, syntaxClass0010, syntaxClass0011, syntaxClass0012, syntaxClass0013,
      syntaxClass0014, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_t_ne_a, fresh_t_ne_m, or_false,
      not_false_eq_true]
  have p0013 :=
    @gCeqsexv syntaxFormula0015 syntaxFormula0022 t (synCsn (synCsn (.cv a)))
      freeVariableCertificate5 freeVariableCertificate6 p0010 p0012
  have p0014 := @gOpkex (synCsn (synCsn (.cv a))) (.cv m)
  have freeVariableCertificate7 : t ∉ (syntaxClass0013).fv := by
    simp only [syntaxClass0000, syntaxClass0001, syntaxClass0002, syntaxClass0003,
      syntaxClass0004, syntaxClass0005, syntaxClass0006, syntaxClass0007, syntaxClass0008,
      syntaxClass0009, syntaxClass0010, syntaxClass0011, syntaxClass0012, syntaxClass0013,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union,
      Finset.notMem_empty, or_false, not_false_eq_true]
  have freeVariableCertificate8 : t ∉ ((synCpw1 (synCpw1 (synCpw1 (synC1c))))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.notMem_empty,
      not_false_eq_true]
  have freeVariableCertificate9 :
    t ∉ ((synCopk (synCsn (synCsn (.cv a))) (.cv m))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      fresh_t_ne_a, fresh_t_ne_m, or_false, not_false_eq_true]
  have p0015 :=
    @gElimak t syntaxClass0013 (synCpw1 (synCpw1 (synCpw1 (synC1c))))
      (synCopk (synCsn (synCsn (.cv a))) (.cv m)) freeVariableCertificate7
      freeVariableCertificate8 freeVariableCertificate9 p0014
  have freeVariableCertificate10 : b ∉ ((Class.cv t)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_b_ne_t, not_false_eq_true]
  have p0016 := @gElpw131c b (.cv t) freeVariableCertificate10
  have p0017 :=
    @gAnbi1i (.classMem (.cv t) (synCpw1 (synCpw1 (synCpw1 (synC1c)))))
      (synWex b (.classEq (.cv t) (synCsn (synCsn (synCsn (synCsn (.cv b)))))))
      syntaxFormula0023 p0016
  have freeVariableCertificate11 :
    b ∉
      ((Wff.classMem (synCopk (.cv t) (synCopk (synCsn (synCsn (.cv a))) (.cv m)))
          syntaxClass0013)).fv :=
    by
    simp only [syntaxClass0000, syntaxClass0001, syntaxClass0002, syntaxClass0003,
      syntaxClass0004, syntaxClass0005, syntaxClass0006, syntaxClass0007, syntaxClass0008,
      syntaxClass0009, syntaxClass0010, syntaxClass0011, syntaxClass0012, syntaxClass0013,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_b_ne_t, dv_b_m, (Ne.symm dv_a_b),
      or_false, not_false_eq_true]
  have p0018 :=
    @gN1941v (.classEq (.cv t) (synCsn (synCsn (synCsn (synCsn (.cv b))))))
      syntaxFormula0023 b freeVariableCertificate11
  have p0019 :=
    @gBitr4i syntaxFormula0024
      (synWa (synWex b (.classEq (.cv t) (synCsn (synCsn (synCsn (synCsn (.cv b)))))))
        syntaxFormula0023)
      syntaxFormula0026 p0017 p0018
  have p0020 := @gExbii syntaxFormula0024 syntaxFormula0026 t p0019
  have p0021 := (Nominal.biimpRefl syntaxFormula0027)
  have p0022 := @gExcom syntaxFormula0025 b t
  have p0023 :=
    @gN3bitr4i (synWex t syntaxFormula0024) (synWex t syntaxFormula0026)
      syntaxFormula0027 syntaxFormula0029 p0020 p0021 p0022
  have p0024 := @gSnex (synCsn (synCsn (synCsn (.cv b))))
  have p0025 :=
    @gOpkeq1 (.cv t) (synCsn (synCsn (synCsn (synCsn (.cv b)))))
      (synCopk (synCsn (synCsn (.cv a))) (.cv m))
  have p0026 :=
    @gEleq1d (.classEq (.cv t) (synCsn (synCsn (synCsn (synCsn (.cv b))))))
      (synCopk (.cv t) (synCopk (synCsn (synCsn (.cv a))) (.cv m))) syntaxClass0030
      syntaxClass0013 p0025
  have freeVariableCertificate12 :
    t ∉ ((synCsn (synCsn (synCsn (synCsn (.cv b)))))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_t_ne_b,
      not_false_eq_true]
  have freeVariableCertificate13 :
    t ∉ ((Wff.classMem syntaxClass0030 syntaxClass0013)).fv := by
    simp only [syntaxClass0000, syntaxClass0001, syntaxClass0002, syntaxClass0003,
      syntaxClass0004, syntaxClass0005, syntaxClass0006, syntaxClass0007, syntaxClass0008,
      syntaxClass0009, syntaxClass0010, syntaxClass0011, syntaxClass0012, syntaxClass0013,
      syntaxClass0030, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_t_ne_b, fresh_t_ne_a, fresh_t_ne_m,
      or_false, not_false_eq_true]
  have p0027 :=
    @gCeqsexv syntaxFormula0023 syntaxFormula0031 t
      (synCsn (synCsn (synCsn (synCsn (.cv b))))) freeVariableCertificate12
      freeVariableCertificate13 p0024 p0026
  have p0028 := @gEldif syntaxClass0030 syntaxClass0008 syntaxClass0012
  have p0029 := @gElin syntaxClass0030 syntaxClass0006 syntaxClass0007
  have freeVariableCertificate14 : t ∉ (syntaxClass0004).fv := by
    simp only [syntaxClass0000, syntaxClass0001, syntaxClass0002, syntaxClass0003,
      syntaxClass0004, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union,
      Finset.notMem_empty, or_false, not_false_eq_true]
  have freeVariableCertificate15 : t ∉ ((synCpw1 (synCpw1 (synC1c)))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.notMem_empty,
      not_false_eq_true]
  have p0030 :=
    @gElimak t syntaxClass0004 (synCpw1 (synCpw1 (synC1c)))
      (synCopk (synCsn (synCsn (.cv a))) (.cv m)) freeVariableCertificate14
      freeVariableCertificate15 freeVariableCertificate9 p0014
  have freeVariableCertificate16 : x ∉ ((Class.cv t)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_x_ne_t, not_false_eq_true]
  have p0031 := @gElpw121c x (.cv t) freeVariableCertificate16
  have p0032 :=
    @gAnbi1i (.classMem (.cv t) (synCpw1 (synCpw1 (synC1c))))
      (synWex x (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv x))))))
      syntaxFormula0032 p0031
  have freeVariableCertificate17 :
    x ∉
      ((Wff.classMem (synCopk (.cv t) (synCopk (synCsn (synCsn (.cv a))) (.cv m)))
          syntaxClass0004)).fv :=
    by
    simp only [syntaxClass0000, syntaxClass0001, syntaxClass0002, syntaxClass0003,
      syntaxClass0004, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_x_ne_t, fresh_x_ne_a, fresh_x_ne_m,
      or_false, not_false_eq_true]
  have p0033 :=
    @gN1941v (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv x))))) syntaxFormula0032
      x freeVariableCertificate17
  have p0034 :=
    @gBitr4i syntaxFormula0033
      (synWa (synWex x (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv x))))))
        syntaxFormula0032)
      syntaxFormula0035 p0032 p0033
  have p0035 := @gExbii syntaxFormula0033 syntaxFormula0035 t p0034
  have p0036 := (Nominal.biimpRefl syntaxFormula0036)
  have p0037 := @gExcom syntaxFormula0034 x t
  have p0038 :=
    @gN3bitr4i (synWex t syntaxFormula0033) (synWex t syntaxFormula0035)
      syntaxFormula0036 syntaxFormula0038 p0035 p0036 p0037
  have p0039 := @gSnex (synCsn (synCsn (.cv x)))
  have p0040 :=
    @gOpkeq1 (.cv t) (synCsn (synCsn (synCsn (.cv x))))
      (synCopk (synCsn (synCsn (.cv a))) (.cv m))
  have p0041 :=
    @gEleq1d (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv x)))))
      (synCopk (.cv t) (synCopk (synCsn (synCsn (.cv a))) (.cv m))) syntaxClass0039
      syntaxClass0004 p0040
  have freeVariableCertificate18 : t ∉ ((synCsn (synCsn (synCsn (.cv x))))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_t_ne_x,
      not_false_eq_true]
  have freeVariableCertificate19 :
    t ∉ ((Wff.classMem syntaxClass0039 syntaxClass0004)).fv := by
    simp only [syntaxClass0000, syntaxClass0001, syntaxClass0002, syntaxClass0003,
      syntaxClass0004, syntaxClass0039, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_t_ne_x, fresh_t_ne_a, fresh_t_ne_m,
      or_false, not_false_eq_true]
  have p0042 :=
    @gCeqsexv syntaxFormula0032 syntaxFormula0040 t (synCsn (synCsn (synCsn (.cv x))))
      freeVariableCertificate18 freeVariableCertificate19 p0039 p0041
  have p0043 := @gElin syntaxClass0039 syntaxClass0003 (synCins2k (synCssetk))
  have p0044 := @gSnex (.cv x)
  have p0045 :=
    @gOtkelins3k (synCsn (.cv x)) (synCsn (synCsn (.cv a))) (.cv m) syntaxClass0002
      p0044 p0010 p0000
  have p0046 := @gVex x
  have p0047 := @gSnex (.cv a)
  have p0048 := @gOpksnelsik (.cv x) (synCsn (.cv a)) syntaxClass0001 p0046 p0047
  have p0049 := @gVex a
  have p0050 := @gEqpw1relk (.cv x) (.cv a) p0046 p0049
  have p0051 :=
    @gN3bitri syntaxFormula0041
      (.classMem (synCopk (synCsn (.cv x)) (synCsn (synCsn (.cv a)))) syntaxClass0002)
      (.classMem (synCopk (.cv x) (synCsn (.cv a))) syntaxClass0001)
      (.classEq (.cv x) (synCpw1 (.cv a))) p0045 p0048 p0050
  have p0052 :=
    @gOtkelins2k (synCsn (.cv x)) (synCsn (synCsn (.cv a))) (.cv m) (synCssetk) p0044
      p0010 p0000
  have p0053 := @gElssetk (.cv x) (.cv m) p0046 p0000
  have p0054_e01_recanon :
    Nominal.NPrf
      (synWb (.classMem (synCopk (synCsn (.cv x)) (.cv m)) (synCssetk)) (.objMem x m)) :=
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
      p0053
  have p0054 :=
    @gBitri syntaxFormula0042
      (.classMem (synCopk (synCsn (.cv x)) (.cv m)) (synCssetk)) (.objMem x m) p0052
      p0054_e01_recanon
  have p0055 :=
    @gAnbi12i syntaxFormula0041 (.classEq (.cv x) (synCpw1 (.cv a))) syntaxFormula0042
      (.objMem x m) p0051 p0054
  have p0056 :=
    @gN3bitri syntaxFormula0037 syntaxFormula0040
      (synWa syntaxFormula0041 syntaxFormula0042)
      (synWa (.classEq (.cv x) (synCpw1 (.cv a))) (.objMem x m)) p0042 p0043 p0055
  have p0057 :=
    @gExbii syntaxFormula0037
      (synWa (.classEq (.cv x) (synCpw1 (.cv a))) (.objMem x m)) x p0056
  have p0058 :=
    @gN3bitri syntaxFormula0043 syntaxFormula0036 syntaxFormula0038
      (synWex x (synWa (.classEq (.cv x) (synCpw1 (.cv a))) (.objMem x m))) p0030 p0038
      p0057
  have p0059 :=
    @gOpkelxpk (synCsn (synCsn (synCsn (synCsn (.cv b)))))
      (synCopk (synCsn (synCsn (.cv a))) (.cv m)) (synCvv) syntaxClass0005 p0024 p0014
  have p0060 :=
    @gMpbiran syntaxFormula0044
      (.classMem (synCsn (synCsn (synCsn (synCsn (.cv b))))) (synCvv))
      syntaxFormula0043 p0024 p0059
  have freeVariableCertificate20 : x ∉ ((synCpw1 (.cv a))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_x_ne_a,
      not_false_eq_true]
  have freeVariableCertificate21 : x ∉ ((Class.cv m)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_x_ne_m, not_false_eq_true]
  have p0061 :=
    (NFChoice.DirectNominalPrf.Nominal.DefinitionLeafHandlersCanonical001.dfClelOfDV x
      (synCpw1 (.cv a)) (.cv m) freeVariableCertificate20 freeVariableCertificate21)
  have p0062_e02_recanon :
    Nominal.NPrf
      (synWb (.classMem (synCpw1 (.cv a)) (.cv m))
        (synWex x (synWa (.classEq (.cv x) (synCpw1 (.cv a))) (.objMem x m)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [synWb, synCpw1, synCin, synCcompl, synCnin, synWnan, synWa,
          synCpw, synWss, synC1c, synWex, synCsn]
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
      p0061
  have p0062 :=
    @gN3bitr4i syntaxFormula0043
      (synWex x (synWa (.classEq (.cv x) (synCpw1 (.cv a))) (.objMem x m)))
      syntaxFormula0044 (.classMem (synCpw1 (.cv a)) (.cv m)) p0058 p0060
      p0062_e02_recanon
  have p0063 := @gOpkex (synCsn (synCsn (.cv b))) (.cv m)
  have freeVariableCertificate22 :
    t ∉ ((synCopk (synCsn (synCsn (.cv b))) (.cv m))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      fresh_t_ne_b, fresh_t_ne_m, or_false, not_false_eq_true]
  have p0064 :=
    @gElimak t syntaxClass0004 (synCpw1 (synCpw1 (synC1c)))
      (synCopk (synCsn (synCsn (.cv b))) (.cv m)) freeVariableCertificate14
      freeVariableCertificate15 freeVariableCertificate22 p0063
  have p0065 :=
    @gAnbi1i (.classMem (.cv t) (synCpw1 (synCpw1 (synC1c))))
      (synWex x (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv x))))))
      syntaxFormula0045 p0031
  have freeVariableCertificate23 :
    x ∉
      ((Wff.classMem (synCopk (.cv t) (synCopk (synCsn (synCsn (.cv b))) (.cv m)))
          syntaxClass0004)).fv :=
    by
    simp only [syntaxClass0000, syntaxClass0001, syntaxClass0002, syntaxClass0003,
      syntaxClass0004, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_x_ne_t, fresh_x_ne_b, fresh_x_ne_m,
      or_false, not_false_eq_true]
  have p0066 :=
    @gN1941v (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv x))))) syntaxFormula0045
      x freeVariableCertificate23
  have p0067 :=
    @gBitr4i syntaxFormula0046
      (synWa (synWex x (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv x))))))
        syntaxFormula0045)
      syntaxFormula0048 p0065 p0066
  have p0068 := @gExbii syntaxFormula0046 syntaxFormula0048 t p0067
  have p0069 := (Nominal.biimpRefl syntaxFormula0049)
  have p0070 := @gExcom syntaxFormula0047 x t
  have p0071 :=
    @gN3bitr4i (synWex t syntaxFormula0046) (synWex t syntaxFormula0048)
      syntaxFormula0049 syntaxFormula0051 p0068 p0069 p0070
  have p0072 :=
    @gOpkeq1 (.cv t) (synCsn (synCsn (synCsn (.cv x))))
      (synCopk (synCsn (synCsn (.cv b))) (.cv m))
  have p0073 :=
    @gEleq1d (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv x)))))
      (synCopk (.cv t) (synCopk (synCsn (synCsn (.cv b))) (.cv m))) syntaxClass0052
      syntaxClass0004 p0072
  have freeVariableCertificate24 :
    t ∉ ((Wff.classMem syntaxClass0052 syntaxClass0004)).fv := by
    simp only [syntaxClass0000, syntaxClass0001, syntaxClass0002, syntaxClass0003,
      syntaxClass0004, syntaxClass0052, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_t_ne_x, fresh_t_ne_b, fresh_t_ne_m,
      or_false, not_false_eq_true]
  have p0074 :=
    @gCeqsexv syntaxFormula0045 syntaxFormula0053 t (synCsn (synCsn (synCsn (.cv x))))
      freeVariableCertificate18 freeVariableCertificate24 p0039 p0073
  have p0075 := @gElin syntaxClass0052 syntaxClass0003 (synCins2k (synCssetk))
  have p0076 := @gSnex (synCsn (.cv b))
  have p0077 :=
    @gOtkelins3k (synCsn (.cv x)) (synCsn (synCsn (.cv b))) (.cv m) syntaxClass0002
      p0044 p0076 p0000
  have p0078 := @gSnex (.cv b)
  have p0079 := @gOpksnelsik (.cv x) (synCsn (.cv b)) syntaxClass0001 p0046 p0078
  have p0080 := @gVex b
  have p0081 := @gEqpw1relk (.cv x) (.cv b) p0046 p0080
  have p0082 :=
    @gN3bitri syntaxFormula0054
      (.classMem (synCopk (synCsn (.cv x)) (synCsn (synCsn (.cv b)))) syntaxClass0002)
      (.classMem (synCopk (.cv x) (synCsn (.cv b))) syntaxClass0001)
      (.classEq (.cv x) (synCpw1 (.cv b))) p0077 p0079 p0081
  have p0083 :=
    @gOtkelins2k (synCsn (.cv x)) (synCsn (synCsn (.cv b))) (.cv m) (synCssetk) p0044
      p0076 p0000
  have p0084_e01_recanon :
    Nominal.NPrf
      (synWb (.classMem (synCopk (synCsn (.cv x)) (.cv m)) (synCssetk)) (.objMem x m)) :=
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
      p0053
  have p0084 :=
    @gBitri syntaxFormula0055
      (.classMem (synCopk (synCsn (.cv x)) (.cv m)) (synCssetk)) (.objMem x m) p0083
      p0084_e01_recanon
  have p0085 :=
    @gAnbi12i syntaxFormula0054 (.classEq (.cv x) (synCpw1 (.cv b))) syntaxFormula0055
      (.objMem x m) p0082 p0084
  have p0086 :=
    @gN3bitri syntaxFormula0050 syntaxFormula0053
      (synWa syntaxFormula0054 syntaxFormula0055)
      (synWa (.classEq (.cv x) (synCpw1 (.cv b))) (.objMem x m)) p0074 p0075 p0085
  have p0087 :=
    @gExbii syntaxFormula0050
      (synWa (.classEq (.cv x) (synCpw1 (.cv b))) (.objMem x m)) x p0086
  have p0088 :=
    @gN3bitri syntaxFormula0056 syntaxFormula0049 syntaxFormula0051
      (synWex x (synWa (.classEq (.cv x) (synCpw1 (.cv b))) (.objMem x m))) p0064 p0071
      p0087
  have p0089 :=
    @gOtkelins2k (synCsn (synCsn (.cv b))) (synCsn (synCsn (.cv a))) (.cv m)
      syntaxClass0005 p0076 p0010 p0000
  have freeVariableCertificate25 : x ∉ ((synCpw1 (.cv b))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_x_ne_b,
      not_false_eq_true]
  have p0090 :=
    (NFChoice.DirectNominalPrf.Nominal.DefinitionLeafHandlersCanonical001.dfClelOfDV x
      (synCpw1 (.cv b)) (.cv m) freeVariableCertificate25 freeVariableCertificate21)
  have p0091_e02_recanon :
    Nominal.NPrf
      (synWb (.classMem (synCpw1 (.cv b)) (.cv m))
        (synWex x (synWa (.classEq (.cv x) (synCpw1 (.cv b))) (.objMem x m)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [synWb, synCpw1, synCin, synCcompl, synCnin, synWnan, synWa,
          synCpw, synWss, synC1c, synWex, synCsn]
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
      p0090
  have p0091 :=
    @gN3bitr4i syntaxFormula0056
      (synWex x (synWa (.classEq (.cv x) (synCpw1 (.cv b))) (.objMem x m)))
      syntaxFormula0057 (.classMem (synCpw1 (.cv b)) (.cv m)) p0088 p0089
      p0091_e02_recanon
  have p0092 :=
    @gAnbi12i syntaxFormula0044 (.classMem (synCpw1 (.cv a)) (.cv m)) syntaxFormula0057
      (.classMem (synCpw1 (.cv b)) (.cv m)) p0062 p0091
  have p0093 :=
    @gBitri syntaxFormula0058 (synWa syntaxFormula0044 syntaxFormula0057)
      syntaxFormula0059 p0029 p0092
  have p0094 :=
    @gOtkelins3k (synCsn (synCsn (.cv b))) (synCsn (synCsn (.cv a))) (.cv m)
      syntaxClass0011 p0076 p0010 p0000
  have p0095 :=
    @gOpksnelsik (synCsn (.cv b)) (synCsn (.cv a)) syntaxClass0010 p0078 p0047
  have p0096 := @gOpkex (synCsn (.cv b)) (synCsn (.cv a))
  have freeVariableCertificate26 : t ∉ (syntaxClass0009).fv := by
    simp only [syntaxClass0009, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k, Finset.mem_union,
      Finset.notMem_empty, or_false, not_false_eq_true]
  have freeVariableCertificate27 : t ∉ ((synCpw1 (synCpw1 (synCnnc)))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.notMem_empty,
      not_false_eq_true]
  have freeVariableCertificate28 :
    t ∉ ((synCopk (synCsn (.cv b)) (synCsn (.cv a)))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      fresh_t_ne_b, fresh_t_ne_a, or_false, not_false_eq_true]
  have p0097 :=
    @gElimak t syntaxClass0009 (synCpw1 (synCpw1 (synCnnc)))
      (synCopk (synCsn (.cv b)) (synCsn (.cv a))) freeVariableCertificate26
      freeVariableCertificate27 freeVariableCertificate28 p0096
  have freeVariableCertificate29 : n ∉ ((Class.cv t)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_n_ne_t, not_false_eq_true]
  have p0098 :=
    @gElpw12 n (.cv t) (synCnnc) freeVariableCertificate29
      (by
        exact
          (show n ∉ ((synCnnc)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc];
              exact (show n ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
  have p0099 :=
    @gAnbi1i (.classMem (.cv t) (synCpw1 (synCpw1 (synCnnc))))
      (synWrex n (synCnnc) (.classEq (.cv t) (synCsn (synCsn (.cv n)))))
      syntaxFormula0060 p0098
  have freeVariableCertificate30 :
    n ∉
      ((Wff.classMem (synCopk (.cv t) (synCopk (synCsn (.cv b)) (synCsn (.cv a))))
          syntaxClass0009)).fv :=
    by
    simp only [syntaxClass0009, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_n_ne_t, (Ne.symm dv_b_n),
      (Ne.symm dv_a_n), or_false, not_false_eq_true]
  have p0100 :=
    @gR1941v (.classEq (.cv t) (synCsn (synCsn (.cv n)))) syntaxFormula0060 n
      (synCnnc) freeVariableCertificate30
  have p0101 :=
    @gBitr4i syntaxFormula0061
      (synWa (synWrex n (synCnnc) (.classEq (.cv t) (synCsn (synCsn (.cv n)))))
        syntaxFormula0060)
      syntaxFormula0063 p0099 p0100
  have p0102 := @gExbii syntaxFormula0061 syntaxFormula0063 t p0101
  have p0103 := (Nominal.biimpRefl syntaxFormula0064)
  have p0104 :=
    @gRexcom4 syntaxFormula0062 n t (synCnnc)
      (by
        exact
          (show t ∉ ((synCnnc)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc];
              exact (show t ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
      (show n ≠ t from (by exact fresh_n_ne_t))
  have p0105 :=
    @gN3bitr4i (synWex t syntaxFormula0061) (synWex t syntaxFormula0063)
      syntaxFormula0064 syntaxFormula0066 p0102 p0103 p0104
  have p0106 := @gSnex (synCsn (.cv n))
  have p0107 :=
    @gOpkeq1 (.cv t) (synCsn (synCsn (.cv n)))
      (synCopk (synCsn (.cv b)) (synCsn (.cv a)))
  have p0108 :=
    @gEleq1d (.classEq (.cv t) (synCsn (synCsn (.cv n))))
      (synCopk (.cv t) (synCopk (synCsn (.cv b)) (synCsn (.cv a)))) syntaxClass0067
      syntaxClass0009 p0107
  have freeVariableCertificate31 : t ∉ ((synCsn (synCsn (.cv n)))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_t_ne_n,
      not_false_eq_true]
  have freeVariableCertificate32 :
    t ∉ ((Wff.classMem syntaxClass0067 syntaxClass0009)).fv := by
    simp only [syntaxClass0009, syntaxClass0067,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_t_ne_n, fresh_t_ne_b, fresh_t_ne_a,
      or_false, not_false_eq_true]
  have p0109 :=
    @gCeqsexv syntaxFormula0060 syntaxFormula0068 t (synCsn (synCsn (.cv n)))
      freeVariableCertificate31 freeVariableCertificate32 p0106 p0108
  have p0110 :=
    @gElin syntaxClass0067 (synCins2k (synCcnvk (synCssetk)))
      (synCins3k (synCcnvk (synCssetk)))
  have p0111 := @gVex n
  have p0112 :=
    @gOtkelins2k (.cv n) (synCsn (.cv b)) (synCsn (.cv a)) (synCcnvk (synCssetk))
      p0111 p0078 p0047
  have p0113 := @gOpkelcnvk (.cv n) (synCsn (.cv a)) (synCssetk) p0111 p0047
  have p0114 := @gElssetk (.cv a) (.cv n) p0049 p0111
  have p0115_e02_recanon :
    Nominal.NPrf
      (synWb (.classMem (synCopk (synCsn (.cv a)) (.cv n)) (synCssetk)) (.objMem a n)) :=
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
      p0114
  have p0115 :=
    @gN3bitri syntaxFormula0069
      (.classMem (synCopk (.cv n) (synCsn (.cv a))) (synCcnvk (synCssetk)))
      (.classMem (synCopk (synCsn (.cv a)) (.cv n)) (synCssetk)) (.objMem a n) p0112
      p0113 p0115_e02_recanon
  have p0116 :=
    @gOtkelins3k (.cv n) (synCsn (.cv b)) (synCsn (.cv a)) (synCcnvk (synCssetk))
      p0111 p0078 p0047
  have p0117 := @gOpkelcnvk (.cv n) (synCsn (.cv b)) (synCssetk) p0111 p0078
  have p0118 := @gElssetk (.cv b) (.cv n) p0080 p0111
  have p0119_e02_recanon :
    Nominal.NPrf
      (synWb (.classMem (synCopk (synCsn (.cv b)) (.cv n)) (synCssetk)) (.objMem b n)) :=
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
      p0118
  have p0119 :=
    @gN3bitri syntaxFormula0070
      (.classMem (synCopk (.cv n) (synCsn (.cv b))) (synCcnvk (synCssetk)))
      (.classMem (synCopk (synCsn (.cv b)) (.cv n)) (synCssetk)) (.objMem b n) p0116
      p0117 p0119_e02_recanon
  have p0120 :=
    @gAnbi12i syntaxFormula0069 (.objMem a n) syntaxFormula0070 (.objMem b n) p0115 p0119
  have p0121 :=
    @gN3bitri syntaxFormula0065 syntaxFormula0068
      (synWa syntaxFormula0069 syntaxFormula0070) (synWa (.objMem a n) (.objMem b n))
      p0109 p0110 p0120
  have p0122 :=
    @gRexbii syntaxFormula0065 (synWa (.objMem a n) (.objMem b n)) n (synCnnc) p0121
  have p0123 :=
    @gN3bitri syntaxFormula0071 syntaxFormula0064 syntaxFormula0066
      (synWrex n (synCnnc) (synWa (.objMem a n) (.objMem b n))) p0097 p0105 p0122
  have p0124 :=
    @gN3bitri syntaxFormula0072
      (.classMem (synCopk (synCsn (synCsn (.cv b))) (synCsn (synCsn (.cv a))))
        syntaxClass0011)
      syntaxFormula0071 (synWrex n (synCnnc) (synWa (.objMem a n) (.objMem b n))) p0094
      p0095 p0123
  have p0125 :=
    @gNotbii syntaxFormula0072
      (synWrex n (synCnnc) (synWa (.objMem a n) (.objMem b n))) p0124
  have p0126 :=
    @gAnbi12i syntaxFormula0058 syntaxFormula0059 syntaxFormula0073
      (.neg (synWrex n (synCnnc) (synWa (.objMem a n) (.objMem b n)))) p0093 p0125
  have p0127 :=
    @gN3bitri syntaxFormula0028 syntaxFormula0031
      (synWa syntaxFormula0058 syntaxFormula0073) syntaxFormula0074 p0027 p0028 p0126
  have p0128 := @gExbii syntaxFormula0028 syntaxFormula0074 b p0127
  have p0129 :=
    @gN3bitri syntaxFormula0022 syntaxFormula0027 syntaxFormula0029 syntaxFormula0075
      p0015 p0023 p0128
  have p0130 :=
    @gExanali syntaxFormula0059
      (synWrex n (synCnnc) (synWa (.objMem a n) (.objMem b n))) b
  have p0131 :=
    @gN3bitri syntaxFormula0020 syntaxFormula0022 syntaxFormula0075 syntaxFormula0078
      p0013 p0129 p0130
  have p0132 := @gExbii syntaxFormula0020 syntaxFormula0078 a p0131
  have p0133 :=
    @gN3bitri syntaxFormula0080 syntaxFormula0019 syntaxFormula0021 syntaxFormula0081
      p0001 p0009 p0132
  have p0134 := @gNotbii syntaxFormula0080 syntaxFormula0081 p0133
  have p0135 := @gElcompl (.cv m) syntaxClass0079 p0000
  have p0136 := @gAlex syntaxFormula0077 a
  have p0137 :=
    @gN3bitr4i (.neg syntaxFormula0080) (.neg syntaxFormula0081)
      (.classMem (.cv m) syntaxClass0082) syntaxFormula0083 p0134 p0135 p0136
  have freeVariableCertificate33 : m ∉ (syntaxClass0082).fv := by
    simp only [syntaxClass0000, syntaxClass0001, syntaxClass0002, syntaxClass0003,
      syntaxClass0004, syntaxClass0005, syntaxClass0006, syntaxClass0007, syntaxClass0008,
      syntaxClass0009, syntaxClass0010, syntaxClass0011, syntaxClass0012, syntaxClass0013,
      syntaxClass0014, syntaxClass0079, syntaxClass0082,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union,
      Finset.notMem_empty, or_false, not_false_eq_true]
  have p0138 :=
    @gEqabi syntaxFormula0083 m syntaxClass0082 freeVariableCertificate33 p0137
  have p0139 := @gVvex
  have p0140 := @gN1cex
  have p0141 := @gPwex (synC1c) p0140
  have p0143 := @gXpkex (synCpw (synC1c)) (synCvv) p0141 p0139
  have p0144 := @gSsetkex
  have p0145 := @gIns3kex (synCssetk) p0144
  have p0147 := @gSikex (synCssetk) p0144
  have p0148 := @gIns2kex (synCsik (synCssetk)) p0147
  have p0149 :=
    @gSymdifex (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk))) p0145 p0148
  have p0151 := @gPw1ex (synC1c) p0140
  have p0152 := @gPw1ex (synCpw1 (synC1c)) p0151
  have p0153 := @gPw1ex (synCpw1 (synCpw1 (synC1c))) p0152
  have p0154 :=
    @gImakex (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk))))
      (synCpw1 (synCpw1 (synCpw1 (synC1c)))) p0149 p0153
  have p0155 :=
    @gDifex (synCxpk (synCpw (synC1c)) (synCvv)) syntaxClass0000 p0143 p0154
  have p0156 := @gSikex syntaxClass0001 p0155
  have p0157 := @gIns3kex syntaxClass0002 p0156
  have p0159 := @gIns2kex (synCssetk) p0144
  have p0160 := @gInex syntaxClass0003 (synCins2k (synCssetk)) p0157 p0159
  have p0161 := @gImakex syntaxClass0004 (synCpw1 (synCpw1 (synC1c))) p0160 p0152
  have p0162 := @gXpkex (synCvv) syntaxClass0005 p0139 p0161
  have p0163 := @gIns2kex syntaxClass0005 p0161
  have p0164 := @gInex syntaxClass0006 syntaxClass0007 p0162 p0163
  have p0166 := @gCnvkex (synCssetk) p0144
  have p0167 := @gIns2kex (synCcnvk (synCssetk)) p0166
  have p0168 := @gIns3kex (synCcnvk (synCssetk)) p0166
  have p0169 :=
    @gInex (synCins2k (synCcnvk (synCssetk))) (synCins3k (synCcnvk (synCssetk)))
      p0167 p0168
  have p0170 := @gNncex
  have p0171 := @gPw1ex (synCnnc) p0170
  have p0172 := @gPw1ex (synCpw1 (synCnnc)) p0171
  have p0173 := @gImakex syntaxClass0009 (synCpw1 (synCpw1 (synCnnc))) p0169 p0172
  have p0174 := @gSikex syntaxClass0010 p0173
  have p0175 := @gIns3kex syntaxClass0011 p0174
  have p0176 := @gDifex syntaxClass0008 syntaxClass0012 p0164 p0175
  have p0177 :=
    @gImakex syntaxClass0013 (synCpw1 (synCpw1 (synCpw1 (synC1c)))) p0176 p0153
  have p0178 := @gImakex syntaxClass0014 (synCpw1 (synC1c)) p0177 p0151
  have p0179 := @gComplex syntaxClass0079 p0178
  have p0180 :=
    @gEqeltrri syntaxClass0082 (.cab m syntaxFormula0083) (synCvv) p0138 p0179
  exact p0180


end NFChoice.DirectNominalPrf.WPPReplay

end
