/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NominalWPPReplayChunk009StructuralPart058

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NominalWPPReplayChunk009StructuralPart059`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_oddfinex`. -/
@[expose]
noncomputable def gOddfinex : Nominal.NPrf (.classMem (synCoddfin) (synCvv)) :=
  by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let x : Var := freshVar proofSupport 0
  let n : Var := freshVar proofSupport 1
  let a : Var := freshVar proofSupport 2
  let t : Var := freshVar proofSupport 3
  let b : Var := freshVar proofSupport 4
  let c : Var := freshVar proofSupport 5
  let y : Var := freshVar proofSupport 6
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
  have fresh_x_ne_b : x ≠ b :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 0) (j := 4) (by decide)
  have fresh_b_ne_x : b ≠ x := Ne.symm fresh_x_ne_b
  have fresh_x_ne_c : x ≠ c :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 0) (j := 5) (by decide)
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 0) (j := 6) (by decide)
  have fresh_y_ne_x : y ≠ x := Ne.symm fresh_x_ne_y
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
  have fresh_n_ne_b : n ≠ b :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 1) (j := 4) (by decide)
  have fresh_b_ne_n : b ≠ n := Ne.symm fresh_n_ne_b
  have fresh_n_ne_c : n ≠ c :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 1) (j := 5) (by decide)
  have fresh_c_ne_n : c ≠ n := Ne.symm fresh_n_ne_c
  have fresh_n_ne_y : n ≠ y :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 1) (j := 6) (by decide)
  have fresh_y_ne_n : y ≠ n := Ne.symm fresh_n_ne_y
  have fresh_a_ne_t : a ≠ t :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_t_ne_a : t ≠ a := Ne.symm fresh_a_ne_t
  have fresh_a_ne_b : a ≠ b :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 2) (j := 4) (by decide)
  have fresh_b_ne_a : b ≠ a := Ne.symm fresh_a_ne_b
  have fresh_a_ne_c : a ≠ c :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 2) (j := 5) (by decide)
  have fresh_a_ne_y : a ≠ y :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 2) (j := 6) (by decide)
  have fresh_y_ne_a : y ≠ a := Ne.symm fresh_a_ne_y
  have fresh_t_ne_b : t ≠ b :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 3) (j := 4) (by decide)
  have fresh_b_ne_t : b ≠ t := Ne.symm fresh_t_ne_b
  have fresh_t_ne_c : t ≠ c :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 3) (j := 5) (by decide)
  have fresh_c_ne_t : c ≠ t := Ne.symm fresh_t_ne_c
  have fresh_t_ne_y : t ≠ y :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 3) (j := 6) (by decide)
  have fresh_y_ne_t : y ≠ t := Ne.symm fresh_t_ne_y
  have fresh_b_ne_c : b ≠ c :=
    by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 4) (j := 5) (by decide)
  have fresh_c_ne_b : c ≠ b := Ne.symm fresh_b_ne_c
  have fresh_b_ne_y : b ≠ y :=
    by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 4) (j := 6) (by decide)
  have fresh_y_ne_b : y ≠ b := Ne.symm fresh_b_ne_y
  let syntaxClass0000 : Class :=
    (synCin (synCins2k (synCins2k (synCssetk)))
      (synCxpk (synCvv) (synCins2k (synCssetk))))
  let syntaxClass0001 : Class :=
    (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
      (synCpw1 (synCpw1 (synC1c))))
  let syntaxClass0002 : Class := (synCcompl syntaxClass0001)
  let syntaxClass0003 : Class := (synCsik syntaxClass0002)
  let syntaxClass0004 : Class := (synCsik syntaxClass0003)
  let syntaxClass0005 : Class := (synCsik syntaxClass0004)
  let syntaxClass0006 : Class := (synCins3k syntaxClass0005)
  let syntaxClass0007 : Class :=
    (synCins3k (synCsik (synCsik (synCsik (synCsik (synCsik (synCssetk)))))))
  let syntaxClass0008 : Class :=
    (synCun syntaxClass0007
      (synCins2k (synCins3k (synCsik (synCsik (synCsik (synCssetk)))))))
  let syntaxClass0009 : Class :=
    (synCsymdif (synCins2k (synCins2k (synCins3k (synCsik (synCssetk))))) syntaxClass0008)
  let syntaxClass0010 : Class :=
    (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
  let syntaxClass0011 : Class := (synCimak syntaxClass0009 syntaxClass0010)
  let syntaxClass0012 : Class := (synCcompl syntaxClass0011)
  let syntaxClass0013 : Class := (synCin syntaxClass0006 syntaxClass0012)
  let syntaxClass0014 : Class := (synCin syntaxClass0000 syntaxClass0013)
  let syntaxClass0015 : Class :=
    (synCimak syntaxClass0014 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))
  let syntaxClass0016 : Class :=
    (synCimak syntaxClass0015 (synCpw1 (synCpw1 (synC1c))))
  let syntaxClass0017 : Class := (synCins2k syntaxClass0016)
  let syntaxClass0018 : Class := (synCins2k syntaxClass0017)
  let syntaxClass0019 : Class :=
    (synCins3k (synCcnvk (synCsik (synCsik (synCsik (synCcompl (synCssetk)))))))
  let syntaxClass0020 : Class := (synCin syntaxClass0018 syntaxClass0019)
  let syntaxClass0021 : Class :=
    (synCun syntaxClass0007 (synCins2k (synCins3k (synCidk))))
  let syntaxClass0022 : Class :=
    (synCsymdif (synCins2k (synCins2k (synCins3k (synCsik (synCssetk))))) syntaxClass0021)
  let syntaxClass0023 : Class := (synCimak syntaxClass0022 syntaxClass0010)
  let syntaxClass0024 : Class := (synCcompl syntaxClass0023)
  let syntaxClass0025 : Class := (synCin syntaxClass0020 syntaxClass0024)
  let syntaxClass0026 : Class :=
    (synCimak syntaxClass0025 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))
  let syntaxClass0027 : Class :=
    (synCimak syntaxClass0026 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))
  let syntaxClass0028 : Class := (synCins3k syntaxClass0027)
  let syntaxClass0029 : Class := (synCsymdif (synCins2k (synCssetk)) syntaxClass0028)
  let syntaxClass0030 : Class :=
    (synCimak syntaxClass0029 (synCpw1 (synCpw1 (synC1c))))
  let syntaxClass0031 : Class := (synCcompl syntaxClass0030)
  let syntaxClass0032 : Class := (synCimak syntaxClass0031 (synCnnc))
  let syntaxFormula0033 : Wff :=
    (.classMem (synCopk (.cv t) (synCopk (.cv n) (.cv x))) syntaxClass0029)
  let syntaxFormula0034 : Wff :=
    (synWa (.classMem (.cv t) (synCpw1 (synCpw1 (synC1c)))) syntaxFormula0033)
  let syntaxFormula0035 : Wff :=
    (synWa (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv a))))) syntaxFormula0033)
  let syntaxFormula0036 : Wff := (synWex a syntaxFormula0035)
  let syntaxFormula0037 : Wff :=
    (synWrex t (synCpw1 (synCpw1 (synC1c))) syntaxFormula0033)
  let syntaxFormula0038 : Wff := (synWex t syntaxFormula0035)
  let syntaxFormula0039 : Wff := (synWex a syntaxFormula0038)
  let syntaxFormula0040 : Wff :=
    (.classMem (synCopk (synCsn (synCsn (synCsn (.cv a)))) (synCopk (.cv n) (.cv x)))
      syntaxClass0029)
  let syntaxFormula0041 : Wff :=
    (.classMem (synCopk (synCsn (synCsn (synCsn (.cv a)))) (synCopk (.cv n) (.cv x)))
      (synCins2k (synCssetk)))
  let syntaxFormula0042 : Wff :=
    (.classMem (synCopk (.cv t) (synCopk (synCsn (.cv a)) (.cv n))) syntaxClass0026)
  let syntaxFormula0043 : Wff :=
    (synWrex t (synCpw1 (synCpw1 (synCpw1 (synC1c)))) syntaxFormula0042)
  let syntaxFormula0044 : Wff :=
    (synWa (.classMem (.cv t) (synCpw1 (synCpw1 (synCpw1 (synC1c))))) syntaxFormula0042)
  let syntaxFormula0045 : Wff :=
    (synWa (.classEq (.cv t) (synCsn (synCsn (synCsn (synCsn (.cv x))))))
      syntaxFormula0042)
  let syntaxFormula0046 : Wff := (synWex x syntaxFormula0045)
  let syntaxFormula0047 : Wff := (synWex t syntaxFormula0045)
  let syntaxFormula0048 : Wff := (synWex x syntaxFormula0047)
  let syntaxClass0049 : Class :=
    (synCopk (synCsn (synCsn (synCsn (synCsn (.cv x)))))
      (synCopk (synCsn (.cv a)) (.cv n)))
  let syntaxFormula0050 : Wff := (.classMem syntaxClass0049 syntaxClass0026)
  let syntaxClass0051 : Class := (synCopk (.cv t) syntaxClass0049)
  let syntaxFormula0052 : Wff := (.classMem syntaxClass0051 syntaxClass0025)
  let syntaxFormula0053 : Wff :=
    (synWrex t (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))) syntaxFormula0052)
  let syntaxFormula0054 : Wff :=
    (synWa (.classMem (.cv t) (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))
      syntaxFormula0052)
  let syntaxFormula0055 : Wff :=
    (synWa (.classEq (.cv t) (synCsn (synCsn (synCsn (synCsn (synCsn (.cv b)))))))
      syntaxFormula0052)
  let syntaxFormula0056 : Wff := (synWex b syntaxFormula0055)
  let syntaxFormula0057 : Wff := (synWex t syntaxFormula0054)
  let syntaxFormula0058 : Wff := (synWex t syntaxFormula0055)
  let syntaxFormula0059 : Wff := (synWex b syntaxFormula0058)
  let syntaxClass0060 : Class :=
    (synCopk (synCsn (synCsn (synCsn (synCsn (synCsn (.cv b)))))) syntaxClass0049)
  let syntaxFormula0061 : Wff := (.classMem syntaxClass0060 syntaxClass0025)
  let syntaxFormula0062 : Wff :=
    (.classMem (synCopk (.cv t) (synCopk (synCsn (.cv b)) (.cv n))) syntaxClass0015)
  let syntaxFormula0063 : Wff :=
    (synWa (.classMem (.cv t) (synCpw1 (synCpw1 (synC1c)))) syntaxFormula0062)
  let syntaxFormula0064 : Wff :=
    (synWa (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv c))))) syntaxFormula0062)
  let syntaxFormula0065 : Wff := (synWex c syntaxFormula0064)
  let syntaxFormula0066 : Wff :=
    (synWrex t (synCpw1 (synCpw1 (synC1c))) syntaxFormula0062)
  let syntaxFormula0067 : Wff := (synWex t syntaxFormula0064)
  let syntaxFormula0068 : Wff := (synWex c syntaxFormula0067)
  let syntaxClass0069 : Class :=
    (synCopk (synCsn (synCsn (synCsn (.cv c)))) (synCopk (synCsn (.cv b)) (.cv n)))
  let syntaxFormula0070 : Wff := (.classMem syntaxClass0069 syntaxClass0015)
  let syntaxClass0071 : Class := (synCopk (.cv t) syntaxClass0069)
  let syntaxFormula0072 : Wff := (.classMem syntaxClass0071 syntaxClass0014)
  let syntaxFormula0073 : Wff :=
    (synWrex t (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))) syntaxFormula0072)
  let syntaxFormula0074 : Wff :=
    (synWa (.classMem (.cv t) (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))
      syntaxFormula0072)
  let syntaxFormula0075 : Wff :=
    (synWa (.classEq (.cv t) (synCsn (synCsn (synCsn (synCsn (synCsn (.cv a)))))))
      syntaxFormula0072)
  let syntaxFormula0076 : Wff := (synWex a syntaxFormula0075)
  let syntaxFormula0077 : Wff := (synWex t syntaxFormula0074)
  let syntaxFormula0078 : Wff := (synWex t syntaxFormula0075)
  let syntaxFormula0079 : Wff := (synWex a syntaxFormula0078)
  let syntaxClass0080 : Class :=
    (synCopk (synCsn (synCsn (synCsn (synCsn (synCsn (.cv a)))))) syntaxClass0069)
  let syntaxFormula0081 : Wff := (.classMem syntaxClass0080 syntaxClass0014)
  let syntaxFormula0082 : Wff :=
    (.classMem syntaxClass0080 (synCins2k (synCins2k (synCssetk))))
  let syntaxFormula0083 : Wff :=
    (.classMem syntaxClass0080 (synCxpk (synCvv) (synCins2k (synCssetk))))
  let syntaxFormula0084 : Wff := (.classMem syntaxClass0080 syntaxClass0000)
  let syntaxFormula0085 : Wff :=
    (.classMem (synCopk (synCsn (synCsn (.cv a))) (synCsn (synCsn (.cv c))))
      syntaxClass0004)
  let syntaxFormula0086 : Wff := (.classMem syntaxClass0080 syntaxClass0006)
  let syntaxFormula0087 : Wff := (.classMem (.cv t) syntaxClass0010)
  let syntaxClass0088 : Class :=
    (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x)))))))))
  let syntaxFormula0089 : Wff := (.classEq (.cv t) syntaxClass0088)
  let syntaxClass0090 : Class := (synCopk (.cv t) syntaxClass0080)
  let syntaxFormula0091 : Wff := (.classMem syntaxClass0090 syntaxClass0009)
  let syntaxFormula0092 : Wff := (synWa syntaxFormula0087 syntaxFormula0091)
  let syntaxFormula0093 : Wff := (synWa syntaxFormula0089 syntaxFormula0091)
  let syntaxFormula0094 : Wff := (synWex x syntaxFormula0093)
  let syntaxFormula0095 : Wff := (synWrex t syntaxClass0010 syntaxFormula0091)
  let syntaxFormula0096 : Wff := (synWex t syntaxFormula0093)
  let syntaxFormula0097 : Wff := (synWex x syntaxFormula0096)
  let syntaxClass0098 : Class := (synCopk syntaxClass0088 syntaxClass0080)
  let syntaxFormula0099 : Wff := (.classMem syntaxClass0098 syntaxClass0009)
  let syntaxFormula0100 : Wff :=
    (.classMem syntaxClass0098 (synCins2k (synCins2k (synCins3k (synCsik (synCssetk))))))
  let syntaxFormula0101 : Wff :=
    (.classMem (synCopk (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x))))))
        (synCsn (synCsn (synCsn (synCsn (.cv a))))))
      (synCsik (synCsik (synCsik (synCsik (synCssetk))))))
  let syntaxFormula0102 : Wff := (.classMem syntaxClass0098 syntaxClass0007)
  let syntaxFormula0103 : Wff :=
    (.classMem syntaxClass0098
      (synCins2k (synCins3k (synCsik (synCsik (synCsik (synCssetk)))))))
  let syntaxFormula0104 : Wff := (.classMem syntaxClass0098 syntaxClass0008)
  let syntaxFormula0105 : Wff := (synWb syntaxFormula0100 syntaxFormula0104)
  let syntaxFormula0106 : Wff := (.classMem syntaxClass0080 syntaxClass0011)
  let syntaxFormula0107 : Wff := (.classMem syntaxClass0080 syntaxClass0012)
  let syntaxFormula0108 : Wff := (.classMem syntaxClass0080 syntaxClass0013)
  let syntaxFormula0109 : Wff :=
    (synWa (.classEq (synCin (.cv a) (.cv c)) (synC0))
      (.classEq (.cv b) (synCun (.cv a) (.cv c))))
  let syntaxFormula0110 : Wff :=
    (.classMem (synCopk (synCsn (.cv b)) (.cv n)) syntaxClass0016)
  let syntaxFormula0111 : Wff := (.classMem syntaxClass0060 syntaxClass0018)
  let syntaxFormula0112 : Wff :=
    (.classMem (synCopk (synCsn (synCsn (synCsn (synCsn (.cv x)))))
        (synCsn (synCsn (synCsn (.cv b)))))
      (synCsik (synCsik (synCsik (synCcompl (synCssetk))))))
  let syntaxFormula0113 : Wff := (.classMem syntaxClass0060 syntaxClass0019)
  let syntaxFormula0114 : Wff := (.classMem syntaxClass0060 syntaxClass0020)
  let syntaxFormula0115 : Wff :=
    (synWa (.classMem (.cv b) (synCplc (.cv n) (.cv n)))
      (.classMem (.cv x) (synCcompl (.cv b))))
  let syntaxClass0116 : Class :=
    (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (.cv y)))))))))
  let syntaxFormula0117 : Wff := (.classEq (.cv t) syntaxClass0116)
  let syntaxClass0118 : Class := (synCopk (.cv t) syntaxClass0060)
  let syntaxFormula0119 : Wff := (.classMem syntaxClass0118 syntaxClass0022)
  let syntaxFormula0120 : Wff := (synWa syntaxFormula0087 syntaxFormula0119)
  let syntaxFormula0121 : Wff := (synWa syntaxFormula0117 syntaxFormula0119)
  let syntaxFormula0122 : Wff := (synWex y syntaxFormula0121)
  let syntaxFormula0123 : Wff := (synWrex t syntaxClass0010 syntaxFormula0119)
  let syntaxFormula0124 : Wff := (synWex t syntaxFormula0121)
  let syntaxFormula0125 : Wff := (synWex y syntaxFormula0124)
  let syntaxClass0126 : Class := (synCopk syntaxClass0116 syntaxClass0060)
  let syntaxFormula0127 : Wff := (.classMem syntaxClass0126 syntaxClass0022)
  let syntaxFormula0128 : Wff :=
    (.classMem syntaxClass0126 (synCins2k (synCins2k (synCins3k (synCsik (synCssetk))))))
  let syntaxClass0129 : Class :=
    (synCopk (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (.cv y)))))))
      syntaxClass0049)
  let syntaxFormula0130 : Wff :=
    (.classMem (synCopk (synCsn (synCsn (synCsn (synCsn (synCsn (.cv y))))))
        (synCsn (synCsn (synCsn (synCsn (.cv b))))))
      (synCsik (synCsik (synCsik (synCsik (synCssetk))))))
  let syntaxFormula0131 : Wff := (.classMem syntaxClass0126 syntaxClass0007)
  let syntaxFormula0132 : Wff :=
    (.classEq (synCsn (synCsn (synCsn (synCsn (.cv y)))))
      (synCsn (synCsn (synCsn (synCsn (.cv x))))))
  let syntaxClass0133 : Class :=
    (synCopk (synCsn (synCsn (synCsn (synCsn (.cv y)))))
      (synCsn (synCsn (synCsn (synCsn (.cv x))))))
  let syntaxFormula0134 : Wff := (.classMem syntaxClass0133 (synCidk))
  let syntaxFormula0135 : Wff :=
    (.classMem syntaxClass0126 (synCins2k (synCins3k (synCidk))))
  let syntaxFormula0136 : Wff := (.classMem syntaxClass0126 syntaxClass0021)
  let syntaxFormula0137 : Wff := (synWb syntaxFormula0128 syntaxFormula0136)
  let syntaxFormula0138 : Wff := (.classMem syntaxClass0060 syntaxClass0023)
  let syntaxFormula0139 : Wff := (.classMem syntaxClass0060 syntaxClass0024)
  let syntaxFormula0140 : Wff :=
    (synWa syntaxFormula0115 (.classEq (.cv a) (synCun (.cv b) (synCsn (.cv x)))))
  let syntaxFormula0141 : Wff := (synWex b syntaxFormula0140)
  let syntaxFormula0142 : Wff :=
    (.classMem (synCopk (synCsn (.cv a)) (.cv n)) syntaxClass0027)
  let syntaxFormula0143 : Wff := (synWex x syntaxFormula0141)
  let syntaxFormula0144 : Wff :=
    (.classMem (synCopk (synCsn (synCsn (synCsn (.cv a)))) (synCopk (.cv n) (.cv x)))
      syntaxClass0028)
  let syntaxFormula0145 : Wff := (synWb syntaxFormula0041 syntaxFormula0144)
  let syntaxFormula0146 : Wff := (.classMem (synCopk (.cv n) (.cv x)) syntaxClass0030)
  let syntaxFormula0147 : Wff := (.classMem (synCopk (.cv n) (.cv x)) syntaxClass0031)
  let syntaxFormula0148 : Wff := (.classMem (.cv x) syntaxClass0032)
  let syntaxFormula0149 : Wff :=
    (synWrex n (synCnnc) (.classEq (.cv x) (synCplc (synCplc (.cv n) (.cv n)) (synC1c))))
  let syntaxClass0150 : Class := (synCdif syntaxClass0032 (synCsn (synC0)))
  let syntaxFormula0151 : Wff := (synWa syntaxFormula0149 (synWne (.cv x) (synC0)))
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfOddfin x n
      (show n ≠ x from (by exact fresh_n_ne_x))
  have p0001 := @gEldifsn (.cv x) syntaxClass0032 (synC0)
  have p0002 := @gVex x
  have freshnessCertificate0000 : n ∉ ((synCssetk)).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk];
      exact (show n ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))
  have freshnessCertificate0001 : n ∉ ((synCins2k (synCssetk))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0000)
  have freshnessCertificate0002 : n ∉ ((synCins2k (synCins2k (synCssetk)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0001)
  have freshnessCertificate0003 : n ∉ ((synCvv)).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv];
      exact (show n ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))
  have freshnessCertificate0004 :
    n ∉ (((synCvv)).fv) ∪ (((synCins2k (synCssetk))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0003 freshnessCertificate0001))
  have freshnessCertificate0005 :
    n ∉ ((synCxpk (synCvv) (synCins2k (synCssetk)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk];
      exact freshnessCertificate0004)
  have freshnessCertificate0006 :
    n ∉
      (((synCins2k (synCins2k (synCssetk)))).fv) ∪
        (((synCxpk (synCvv) (synCins2k (synCssetk)))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0002 freshnessCertificate0005))
  have freshnessCertificate0007 : n ∉ (syntaxClass0000).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin];
      exact freshnessCertificate0006)
  have freshnessCertificate0008 : n ∉ ((synCins3k (synCssetk))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0000)
  have freshnessCertificate0009 :
    n ∉ (((synCins3k (synCssetk))).fv) ∪ (((synCins2k (synCssetk))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0008 freshnessCertificate0001))
  have freshnessCertificate0010 :
    n ∉ ((synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin];
      exact freshnessCertificate0009)
  have freshnessCertificate0011 : n ∉ ((synC1c)).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c];
      exact (show n ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))
  have freshnessCertificate0012 : n ∉ ((synCpw1 (synC1c))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0011)
  have freshnessCertificate0013 : n ∉ ((synCpw1 (synCpw1 (synC1c)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0012)
  have freshnessCertificate0014 :
    n ∉
      (((synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))).fv) ∪
        (((synCpw1 (synCpw1 (synC1c)))).fv) :=
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
  have freshnessCertificate0021 : n ∉ ((synCsik (synCssetk))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0000)
  have freshnessCertificate0022 : n ∉ ((synCins3k (synCsik (synCssetk)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0021)
  have freshnessCertificate0023 :
    n ∉ ((synCins2k (synCins3k (synCsik (synCssetk))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0022)
  have freshnessCertificate0024 :
    n ∉ ((synCins2k (synCins2k (synCins3k (synCsik (synCssetk)))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0023)
  have freshnessCertificate0025 : n ∉ ((synCsik (synCsik (synCssetk)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0021)
  have freshnessCertificate0026 :
    n ∉ ((synCsik (synCsik (synCsik (synCssetk))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0025)
  have freshnessCertificate0027 :
    n ∉ ((synCsik (synCsik (synCsik (synCsik (synCssetk)))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0026)
  have freshnessCertificate0028 :
    n ∉ ((synCsik (synCsik (synCsik (synCsik (synCsik (synCssetk))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0027)
  have freshnessCertificate0029 : n ∉ (syntaxClass0007).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0028)
  have freshnessCertificate0030 :
    n ∉ ((synCins3k (synCsik (synCsik (synCsik (synCssetk)))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0026)
  have freshnessCertificate0031 :
    n ∉ ((synCins2k (synCins3k (synCsik (synCsik (synCsik (synCssetk))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0030)
  have freshnessCertificate0032 :
    n ∉
      ((syntaxClass0007).fv) ∪
        (((synCins2k (synCins3k (synCsik (synCsik (synCsik (synCssetk))))))).fv) :=
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
      (((synCins2k (synCins2k (synCins3k (synCsik (synCssetk)))))).fv) ∪
        ((syntaxClass0008).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0024 freshnessCertificate0033))
  have freshnessCertificate0035 : n ∉ (syntaxClass0009).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif];
      exact freshnessCertificate0034)
  have freshnessCertificate0036 : n ∉ ((synCpw1 (synCpw1 (synCpw1 (synC1c))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0013)
  have freshnessCertificate0037 :
    n ∉ ((synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0036)
  have freshnessCertificate0038 :
    n ∉ ((synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0037)
  have freshnessCertificate0039 :
    n ∉
      ((synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))).fv :=
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
        (((synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0047 freshnessCertificate0037))
  have freshnessCertificate0049 : n ∉ (syntaxClass0015).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak];
      exact freshnessCertificate0048)
  have freshnessCertificate0050 :
    n ∉ ((syntaxClass0015).fv) ∪ (((synCpw1 (synCpw1 (synC1c)))).fv) :=
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
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0051)
  have freshnessCertificate0053 : n ∉ (syntaxClass0018).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0052)
  have freshnessCertificate0054 : n ∉ ((synCcompl (synCssetk))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl];
      exact freshnessCertificate0000)
  have freshnessCertificate0055 : n ∉ ((synCsik (synCcompl (synCssetk)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0054)
  have freshnessCertificate0056 :
    n ∉ ((synCsik (synCsik (synCcompl (synCssetk))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0055)
  have freshnessCertificate0057 :
    n ∉ ((synCsik (synCsik (synCsik (synCcompl (synCssetk)))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0056)
  have freshnessCertificate0058 :
    n ∉ ((synCcnvk (synCsik (synCsik (synCsik (synCcompl (synCssetk))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk];
      exact freshnessCertificate0057)
  have freshnessCertificate0059 : n ∉ (syntaxClass0019).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0058)
  have freshnessCertificate0060 : n ∉ ((syntaxClass0018).fv) ∪ ((syntaxClass0019).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0053 freshnessCertificate0059))
  have freshnessCertificate0061 : n ∉ (syntaxClass0020).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin];
      exact freshnessCertificate0060)
  have freshnessCertificate0062 : n ∉ ((synCidk)).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cidk];
      exact (show n ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))
  have freshnessCertificate0063 : n ∉ ((synCins3k (synCidk))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0062)
  have freshnessCertificate0064 : n ∉ ((synCins2k (synCins3k (synCidk)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0063)
  have freshnessCertificate0065 :
    n ∉ ((syntaxClass0007).fv) ∪ (((synCins2k (synCins3k (synCidk)))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0029 freshnessCertificate0064))
  have freshnessCertificate0066 : n ∉ (syntaxClass0021).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun];
      exact freshnessCertificate0065)
  have freshnessCertificate0067 :
    n ∉
      (((synCins2k (synCins2k (synCins3k (synCsik (synCssetk)))))).fv) ∪
        ((syntaxClass0021).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0024 freshnessCertificate0066))
  have freshnessCertificate0068 : n ∉ (syntaxClass0022).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif];
      exact freshnessCertificate0067)
  have freshnessCertificate0069 : n ∉ ((syntaxClass0022).fv) ∪ ((syntaxClass0010).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0068 freshnessCertificate0040))
  have freshnessCertificate0070 : n ∉ (syntaxClass0023).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak];
      exact freshnessCertificate0069)
  have freshnessCertificate0071 : n ∉ (syntaxClass0024).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl];
      exact freshnessCertificate0070)
  have freshnessCertificate0072 : n ∉ ((syntaxClass0020).fv) ∪ ((syntaxClass0024).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0061 freshnessCertificate0071))
  have freshnessCertificate0073 : n ∉ (syntaxClass0025).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin];
      exact freshnessCertificate0072)
  have freshnessCertificate0074 :
    n ∉
      ((syntaxClass0025).fv) ∪
        (((synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0073 freshnessCertificate0037))
  have freshnessCertificate0075 : n ∉ (syntaxClass0026).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak];
      exact freshnessCertificate0074)
  have freshnessCertificate0076 :
    n ∉ ((syntaxClass0026).fv) ∪ (((synCpw1 (synCpw1 (synCpw1 (synC1c))))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0075 freshnessCertificate0036))
  have freshnessCertificate0077 : n ∉ (syntaxClass0027).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak];
      exact freshnessCertificate0076)
  have freshnessCertificate0078 : n ∉ (syntaxClass0028).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0077)
  have freshnessCertificate0079 :
    n ∉ (((synCins2k (synCssetk))).fv) ∪ ((syntaxClass0028).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0001 freshnessCertificate0078))
  have freshnessCertificate0080 : n ∉ (syntaxClass0029).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif];
      exact freshnessCertificate0079)
  have freshnessCertificate0081 :
    n ∉ ((syntaxClass0029).fv) ∪ (((synCpw1 (synCpw1 (synC1c)))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0080 freshnessCertificate0013))
  have freshnessCertificate0082 : n ∉ (syntaxClass0030).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak];
      exact freshnessCertificate0081)
  have freshnessCertificate0083 : n ∉ (syntaxClass0031).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl];
      exact freshnessCertificate0082)
  have freshnessCertificate0084 : n ∉ ((synCnnc)).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc];
      exact (show n ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))
  have freshnessCertificate0085 : n ∉ ((Class.cv x)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show n ∉ ({ x } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show n ≠ x from (by exact fresh_n_ne_x)))))
  have p0003 :=
    @gElimak n syntaxClass0031 (synCnnc) (.cv x) (by exact freshnessCertificate0083)
      (by exact freshnessCertificate0084) (by exact freshnessCertificate0085) p0002
  have p0004 := @gOpkex (.cv n) (.cv x)
  have freshnessCertificate0086 : t ∉ ((synCssetk)).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk];
      exact (show t ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))
  have freshnessCertificate0087 : t ∉ ((synCins2k (synCssetk))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0086)
  have freshnessCertificate0088 : t ∉ ((synCins2k (synCins2k (synCssetk)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0087)
  have freshnessCertificate0089 : t ∉ ((synCvv)).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv];
      exact (show t ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))
  have freshnessCertificate0090 :
    t ∉ (((synCvv)).fv) ∪ (((synCins2k (synCssetk))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0089 freshnessCertificate0087))
  have freshnessCertificate0091 :
    t ∉ ((synCxpk (synCvv) (synCins2k (synCssetk)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk];
      exact freshnessCertificate0090)
  have freshnessCertificate0092 :
    t ∉
      (((synCins2k (synCins2k (synCssetk)))).fv) ∪
        (((synCxpk (synCvv) (synCins2k (synCssetk)))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0088 freshnessCertificate0091))
  have freshnessCertificate0093 : t ∉ (syntaxClass0000).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin];
      exact freshnessCertificate0092)
  have freshnessCertificate0094 : t ∉ ((synCins3k (synCssetk))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0086)
  have freshnessCertificate0095 :
    t ∉ (((synCins3k (synCssetk))).fv) ∪ (((synCins2k (synCssetk))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0094 freshnessCertificate0087))
  have freshnessCertificate0096 :
    t ∉ ((synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin];
      exact freshnessCertificate0095)
  have freshnessCertificate0097 : t ∉ ((synC1c)).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c];
      exact (show t ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))
  have freshnessCertificate0098 : t ∉ ((synCpw1 (synC1c))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0097)
  have freshnessCertificate0099 : t ∉ ((synCpw1 (synCpw1 (synC1c)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0098)
  have freshnessCertificate0100 :
    t ∉
      (((synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))).fv) ∪
        (((synCpw1 (synCpw1 (synC1c)))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0096 freshnessCertificate0099))
  have freshnessCertificate0101 : t ∉ (syntaxClass0001).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak];
      exact freshnessCertificate0100)
  have freshnessCertificate0102 : t ∉ (syntaxClass0002).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl];
      exact freshnessCertificate0101)
  have freshnessCertificate0103 : t ∉ (syntaxClass0003).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0102)
  have freshnessCertificate0104 : t ∉ (syntaxClass0004).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0103)
  have freshnessCertificate0105 : t ∉ (syntaxClass0005).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0104)
  have freshnessCertificate0106 : t ∉ (syntaxClass0006).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0105)
  have freshnessCertificate0107 : t ∉ ((synCsik (synCssetk))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0086)
  have freshnessCertificate0108 : t ∉ ((synCins3k (synCsik (synCssetk)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0107)
  have freshnessCertificate0109 :
    t ∉ ((synCins2k (synCins3k (synCsik (synCssetk))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0108)
  have freshnessCertificate0110 :
    t ∉ ((synCins2k (synCins2k (synCins3k (synCsik (synCssetk)))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0109)
  have freshnessCertificate0111 : t ∉ ((synCsik (synCsik (synCssetk)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0107)
  have freshnessCertificate0112 :
    t ∉ ((synCsik (synCsik (synCsik (synCssetk))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0111)
  have freshnessCertificate0113 :
    t ∉ ((synCsik (synCsik (synCsik (synCsik (synCssetk)))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0112)
  have freshnessCertificate0114 :
    t ∉ ((synCsik (synCsik (synCsik (synCsik (synCsik (synCssetk))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0113)
  have freshnessCertificate0115 : t ∉ (syntaxClass0007).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0114)
  have freshnessCertificate0116 :
    t ∉ ((synCins3k (synCsik (synCsik (synCsik (synCssetk)))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0112)
  have freshnessCertificate0117 :
    t ∉ ((synCins2k (synCins3k (synCsik (synCsik (synCsik (synCssetk))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0116)
  have freshnessCertificate0118 :
    t ∉
      ((syntaxClass0007).fv) ∪
        (((synCins2k (synCins3k (synCsik (synCsik (synCsik (synCssetk))))))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0115 freshnessCertificate0117))
  have freshnessCertificate0119 : t ∉ (syntaxClass0008).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun];
      exact freshnessCertificate0118)
  have freshnessCertificate0120 :
    t ∉
      (((synCins2k (synCins2k (synCins3k (synCsik (synCssetk)))))).fv) ∪
        ((syntaxClass0008).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0110 freshnessCertificate0119))
  have freshnessCertificate0121 : t ∉ (syntaxClass0009).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif];
      exact freshnessCertificate0120)
  have freshnessCertificate0122 : t ∉ ((synCpw1 (synCpw1 (synCpw1 (synC1c))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0099)
  have freshnessCertificate0123 :
    t ∉ ((synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0122)
  have freshnessCertificate0124 :
    t ∉ ((synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0123)
  have freshnessCertificate0125 :
    t ∉
      ((synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0124)
  have freshnessCertificate0126 : t ∉ (syntaxClass0010).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0125)
  have freshnessCertificate0127 : t ∉ ((syntaxClass0009).fv) ∪ ((syntaxClass0010).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0121 freshnessCertificate0126))
  have freshnessCertificate0128 : t ∉ (syntaxClass0011).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak];
      exact freshnessCertificate0127)
  have freshnessCertificate0129 : t ∉ (syntaxClass0012).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl];
      exact freshnessCertificate0128)
  have freshnessCertificate0130 : t ∉ ((syntaxClass0006).fv) ∪ ((syntaxClass0012).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0106 freshnessCertificate0129))
  have freshnessCertificate0131 : t ∉ (syntaxClass0013).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin];
      exact freshnessCertificate0130)
  have freshnessCertificate0132 : t ∉ ((syntaxClass0000).fv) ∪ ((syntaxClass0013).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0093 freshnessCertificate0131))
  have freshnessCertificate0133 : t ∉ (syntaxClass0014).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin];
      exact freshnessCertificate0132)
  have freshnessCertificate0134 :
    t ∉
      ((syntaxClass0014).fv) ∪
        (((synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0133 freshnessCertificate0123))
  have freshnessCertificate0135 : t ∉ (syntaxClass0015).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak];
      exact freshnessCertificate0134)
  have freshnessCertificate0136 :
    t ∉ ((syntaxClass0015).fv) ∪ (((synCpw1 (synCpw1 (synC1c)))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0135 freshnessCertificate0099))
  have freshnessCertificate0137 : t ∉ (syntaxClass0016).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak];
      exact freshnessCertificate0136)
  have freshnessCertificate0138 : t ∉ (syntaxClass0017).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0137)
  have freshnessCertificate0139 : t ∉ (syntaxClass0018).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0138)
  have freshnessCertificate0140 : t ∉ ((synCcompl (synCssetk))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl];
      exact freshnessCertificate0086)
  have freshnessCertificate0141 : t ∉ ((synCsik (synCcompl (synCssetk)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0140)
  have freshnessCertificate0142 :
    t ∉ ((synCsik (synCsik (synCcompl (synCssetk))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0141)
  have freshnessCertificate0143 :
    t ∉ ((synCsik (synCsik (synCsik (synCcompl (synCssetk)))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0142)
  have freshnessCertificate0144 :
    t ∉ ((synCcnvk (synCsik (synCsik (synCsik (synCcompl (synCssetk))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk];
      exact freshnessCertificate0143)
  have freshnessCertificate0145 : t ∉ (syntaxClass0019).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0144)
  have freshnessCertificate0146 : t ∉ ((syntaxClass0018).fv) ∪ ((syntaxClass0019).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0139 freshnessCertificate0145))
  have freshnessCertificate0147 : t ∉ (syntaxClass0020).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin];
      exact freshnessCertificate0146)
  have freshnessCertificate0148 : t ∉ ((synCidk)).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cidk];
      exact (show t ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))
  have freshnessCertificate0149 : t ∉ ((synCins3k (synCidk))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0148)
  have freshnessCertificate0150 : t ∉ ((synCins2k (synCins3k (synCidk)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0149)
  have freshnessCertificate0151 :
    t ∉ ((syntaxClass0007).fv) ∪ (((synCins2k (synCins3k (synCidk)))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0115 freshnessCertificate0150))
  have freshnessCertificate0152 : t ∉ (syntaxClass0021).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun];
      exact freshnessCertificate0151)
  have freshnessCertificate0153 :
    t ∉
      (((synCins2k (synCins2k (synCins3k (synCsik (synCssetk)))))).fv) ∪
        ((syntaxClass0021).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0110 freshnessCertificate0152))
  have freshnessCertificate0154 : t ∉ (syntaxClass0022).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif];
      exact freshnessCertificate0153)
  have freshnessCertificate0155 : t ∉ ((syntaxClass0022).fv) ∪ ((syntaxClass0010).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0154 freshnessCertificate0126))
  have freshnessCertificate0156 : t ∉ (syntaxClass0023).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak];
      exact freshnessCertificate0155)
  have freshnessCertificate0157 : t ∉ (syntaxClass0024).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl];
      exact freshnessCertificate0156)
  have freshnessCertificate0158 : t ∉ ((syntaxClass0020).fv) ∪ ((syntaxClass0024).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0147 freshnessCertificate0157))
  have freshnessCertificate0159 : t ∉ (syntaxClass0025).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin];
      exact freshnessCertificate0158)
  have freshnessCertificate0160 :
    t ∉
      ((syntaxClass0025).fv) ∪
        (((synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0159 freshnessCertificate0123))
  have freshnessCertificate0161 : t ∉ (syntaxClass0026).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak];
      exact freshnessCertificate0160)
  have freshnessCertificate0162 :
    t ∉ ((syntaxClass0026).fv) ∪ (((synCpw1 (synCpw1 (synCpw1 (synC1c))))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0161 freshnessCertificate0122))
  have freshnessCertificate0163 : t ∉ (syntaxClass0027).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak];
      exact freshnessCertificate0162)
  have freshnessCertificate0164 : t ∉ (syntaxClass0028).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0163)
  have freshnessCertificate0165 :
    t ∉ (((synCins2k (synCssetk))).fv) ∪ ((syntaxClass0028).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0087 freshnessCertificate0164))
  have freshnessCertificate0166 : t ∉ (syntaxClass0029).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif];
      exact freshnessCertificate0165)
  have freshnessCertificate0167 : t ∉ ((Class.cv n)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show t ∉ ({ n } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show t ≠ n from (by exact fresh_t_ne_n)))))
  have freshnessCertificate0168 : t ∉ ((Class.cv x)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show t ∉ ({ x } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show t ≠ x from (by exact fresh_t_ne_x)))))
  have freshnessCertificate0169 : t ∉ (((Class.cv n)).fv) ∪ (((Class.cv x)).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0167 freshnessCertificate0168))
  have freshnessCertificate0170 : t ∉ ((synCopk (.cv n) (.cv x))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk];
      exact freshnessCertificate0169)
  have p0005 :=
    @gElimak t syntaxClass0029 (synCpw1 (synCpw1 (synC1c))) (synCopk (.cv n) (.cv x))
      (by exact freshnessCertificate0166) (by exact freshnessCertificate0099)
      (by exact freshnessCertificate0170) p0004
  have freshnessCertificate0171 : a ∉ ((Class.cv t)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show a ∉ ({ t } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show a ≠ t from (by exact fresh_a_ne_t)))))
  have p0006 := @gElpw121c a (.cv t) (by exact freshnessCertificate0171)
  have p0007 :=
    @gAnbi1i (.classMem (.cv t) (synCpw1 (synCpw1 (synC1c))))
      (synWex a (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv a))))))
      syntaxFormula0033 p0006
  have freshnessCertificate0172 : a ∉ ((Class.cv n)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show a ∉ ({ n } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show a ≠ n from (by exact fresh_a_ne_n)))))
  have freshnessCertificate0173 : a ∉ ((Class.cv x)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show a ∉ ({ x } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show a ≠ x from (by exact fresh_a_ne_x)))))
  have freshnessCertificate0174 : a ∉ (((Class.cv n)).fv) ∪ (((Class.cv x)).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0172 freshnessCertificate0173))
  have freshnessCertificate0175 : a ∉ ((synCopk (.cv n) (.cv x))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk];
      exact freshnessCertificate0174)
  have freshnessCertificate0176 :
    a ∉ (((Class.cv t)).fv) ∪ (((synCopk (.cv n) (.cv x))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0171 freshnessCertificate0175))
  have freshnessCertificate0177 :
    a ∉ ((synCopk (.cv t) (synCopk (.cv n) (.cv x)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk];
      exact freshnessCertificate0176)
  have freshnessCertificate0178 : a ∉ ((synCssetk)).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk];
      exact (show a ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))
  have freshnessCertificate0179 : a ∉ ((synCins2k (synCssetk))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0178)
  have freshnessCertificate0180 : a ∉ ((synCins2k (synCins2k (synCssetk)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0179)
  have freshnessCertificate0181 : a ∉ ((synCvv)).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv];
      exact (show a ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))
  have freshnessCertificate0182 :
    a ∉ (((synCvv)).fv) ∪ (((synCins2k (synCssetk))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0181 freshnessCertificate0179))
  have freshnessCertificate0183 :
    a ∉ ((synCxpk (synCvv) (synCins2k (synCssetk)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk];
      exact freshnessCertificate0182)
  have freshnessCertificate0184 :
    a ∉
      (((synCins2k (synCins2k (synCssetk)))).fv) ∪
        (((synCxpk (synCvv) (synCins2k (synCssetk)))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0180 freshnessCertificate0183))
  have freshnessCertificate0185 : a ∉ (syntaxClass0000).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin];
      exact freshnessCertificate0184)
  have freshnessCertificate0186 : a ∉ ((synCins3k (synCssetk))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0178)
  have freshnessCertificate0187 :
    a ∉ (((synCins3k (synCssetk))).fv) ∪ (((synCins2k (synCssetk))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0186 freshnessCertificate0179))
  have freshnessCertificate0188 :
    a ∉ ((synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin];
      exact freshnessCertificate0187)
  have freshnessCertificate0189 : a ∉ ((synC1c)).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c];
      exact (show a ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))
  have freshnessCertificate0190 : a ∉ ((synCpw1 (synC1c))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0189)
  have freshnessCertificate0191 : a ∉ ((synCpw1 (synCpw1 (synC1c)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0190)
  have freshnessCertificate0192 :
    a ∉
      (((synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))).fv) ∪
        (((synCpw1 (synCpw1 (synC1c)))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0188 freshnessCertificate0191))
  have freshnessCertificate0193 : a ∉ (syntaxClass0001).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak];
      exact freshnessCertificate0192)
  have freshnessCertificate0194 : a ∉ (syntaxClass0002).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl];
      exact freshnessCertificate0193)
  have freshnessCertificate0195 : a ∉ (syntaxClass0003).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0194)
  have freshnessCertificate0196 : a ∉ (syntaxClass0004).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0195)
  have freshnessCertificate0197 : a ∉ (syntaxClass0005).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0196)
  have freshnessCertificate0198 : a ∉ (syntaxClass0006).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0197)
  have freshnessCertificate0199 : a ∉ ((synCsik (synCssetk))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0178)
  have freshnessCertificate0200 : a ∉ ((synCins3k (synCsik (synCssetk)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0199)
  have freshnessCertificate0201 :
    a ∉ ((synCins2k (synCins3k (synCsik (synCssetk))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0200)
  have freshnessCertificate0202 :
    a ∉ ((synCins2k (synCins2k (synCins3k (synCsik (synCssetk)))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0201)
  have freshnessCertificate0203 : a ∉ ((synCsik (synCsik (synCssetk)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0199)
  have freshnessCertificate0204 :
    a ∉ ((synCsik (synCsik (synCsik (synCssetk))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0203)
  have freshnessCertificate0205 :
    a ∉ ((synCsik (synCsik (synCsik (synCsik (synCssetk)))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0204)
  have freshnessCertificate0206 :
    a ∉ ((synCsik (synCsik (synCsik (synCsik (synCsik (synCssetk))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0205)
  have freshnessCertificate0207 : a ∉ (syntaxClass0007).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0206)
  have freshnessCertificate0208 :
    a ∉ ((synCins3k (synCsik (synCsik (synCsik (synCssetk)))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0204)
  have freshnessCertificate0209 :
    a ∉ ((synCins2k (synCins3k (synCsik (synCsik (synCsik (synCssetk))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0208)
  have freshnessCertificate0210 :
    a ∉
      ((syntaxClass0007).fv) ∪
        (((synCins2k (synCins3k (synCsik (synCsik (synCsik (synCssetk))))))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0207 freshnessCertificate0209))
  have freshnessCertificate0211 : a ∉ (syntaxClass0008).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun];
      exact freshnessCertificate0210)
  have freshnessCertificate0212 :
    a ∉
      (((synCins2k (synCins2k (synCins3k (synCsik (synCssetk)))))).fv) ∪
        ((syntaxClass0008).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0202 freshnessCertificate0211))
  have freshnessCertificate0213 : a ∉ (syntaxClass0009).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif];
      exact freshnessCertificate0212)
  have freshnessCertificate0214 : a ∉ ((synCpw1 (synCpw1 (synCpw1 (synC1c))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0191)
  have freshnessCertificate0215 :
    a ∉ ((synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0214)
  have freshnessCertificate0216 :
    a ∉ ((synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0215)
  have freshnessCertificate0217 :
    a ∉
      ((synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0216)
  have freshnessCertificate0218 : a ∉ (syntaxClass0010).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0217)
  have freshnessCertificate0219 : a ∉ ((syntaxClass0009).fv) ∪ ((syntaxClass0010).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0213 freshnessCertificate0218))
  have freshnessCertificate0220 : a ∉ (syntaxClass0011).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak];
      exact freshnessCertificate0219)
  have freshnessCertificate0221 : a ∉ (syntaxClass0012).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl];
      exact freshnessCertificate0220)
  have freshnessCertificate0222 : a ∉ ((syntaxClass0006).fv) ∪ ((syntaxClass0012).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0198 freshnessCertificate0221))
  have freshnessCertificate0223 : a ∉ (syntaxClass0013).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin];
      exact freshnessCertificate0222)
  have freshnessCertificate0224 : a ∉ ((syntaxClass0000).fv) ∪ ((syntaxClass0013).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0185 freshnessCertificate0223))
  have freshnessCertificate0225 : a ∉ (syntaxClass0014).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin];
      exact freshnessCertificate0224)
  have freshnessCertificate0226 :
    a ∉
      ((syntaxClass0014).fv) ∪
        (((synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0225 freshnessCertificate0215))
  have freshnessCertificate0227 : a ∉ (syntaxClass0015).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak];
      exact freshnessCertificate0226)
  have freshnessCertificate0228 :
    a ∉ ((syntaxClass0015).fv) ∪ (((synCpw1 (synCpw1 (synC1c)))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0227 freshnessCertificate0191))
  have freshnessCertificate0229 : a ∉ (syntaxClass0016).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak];
      exact freshnessCertificate0228)
  have freshnessCertificate0230 : a ∉ (syntaxClass0017).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0229)
  have freshnessCertificate0231 : a ∉ (syntaxClass0018).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0230)
  have freshnessCertificate0232 : a ∉ ((synCcompl (synCssetk))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl];
      exact freshnessCertificate0178)
  have freshnessCertificate0233 : a ∉ ((synCsik (synCcompl (synCssetk)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0232)
  have freshnessCertificate0234 :
    a ∉ ((synCsik (synCsik (synCcompl (synCssetk))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0233)
  have freshnessCertificate0235 :
    a ∉ ((synCsik (synCsik (synCsik (synCcompl (synCssetk)))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0234)
  have freshnessCertificate0236 :
    a ∉ ((synCcnvk (synCsik (synCsik (synCsik (synCcompl (synCssetk))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk];
      exact freshnessCertificate0235)
  have freshnessCertificate0237 : a ∉ (syntaxClass0019).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0236)
  have freshnessCertificate0238 : a ∉ ((syntaxClass0018).fv) ∪ ((syntaxClass0019).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0231 freshnessCertificate0237))
  have freshnessCertificate0239 : a ∉ (syntaxClass0020).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin];
      exact freshnessCertificate0238)
  have freshnessCertificate0240 : a ∉ ((synCidk)).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cidk];
      exact (show a ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))
  have freshnessCertificate0241 : a ∉ ((synCins3k (synCidk))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0240)
  have freshnessCertificate0242 : a ∉ ((synCins2k (synCins3k (synCidk)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0241)
  have freshnessCertificate0243 :
    a ∉ ((syntaxClass0007).fv) ∪ (((synCins2k (synCins3k (synCidk)))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0207 freshnessCertificate0242))
  have freshnessCertificate0244 : a ∉ (syntaxClass0021).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun];
      exact freshnessCertificate0243)
  have freshnessCertificate0245 :
    a ∉
      (((synCins2k (synCins2k (synCins3k (synCsik (synCssetk)))))).fv) ∪
        ((syntaxClass0021).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0202 freshnessCertificate0244))
  have freshnessCertificate0246 : a ∉ (syntaxClass0022).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif];
      exact freshnessCertificate0245)
  have freshnessCertificate0247 : a ∉ ((syntaxClass0022).fv) ∪ ((syntaxClass0010).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0246 freshnessCertificate0218))
  have freshnessCertificate0248 : a ∉ (syntaxClass0023).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak];
      exact freshnessCertificate0247)
  have freshnessCertificate0249 : a ∉ (syntaxClass0024).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl];
      exact freshnessCertificate0248)
  have freshnessCertificate0250 : a ∉ ((syntaxClass0020).fv) ∪ ((syntaxClass0024).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0239 freshnessCertificate0249))
  have freshnessCertificate0251 : a ∉ (syntaxClass0025).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin];
      exact freshnessCertificate0250)
  have freshnessCertificate0252 :
    a ∉
      ((syntaxClass0025).fv) ∪
        (((synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0251 freshnessCertificate0215))
  have freshnessCertificate0253 : a ∉ (syntaxClass0026).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak];
      exact freshnessCertificate0252)
  have freshnessCertificate0254 :
    a ∉ ((syntaxClass0026).fv) ∪ (((synCpw1 (synCpw1 (synCpw1 (synC1c))))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0253 freshnessCertificate0214))
  have freshnessCertificate0255 : a ∉ (syntaxClass0027).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak];
      exact freshnessCertificate0254)
  have freshnessCertificate0256 : a ∉ (syntaxClass0028).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0255)
  have freshnessCertificate0257 :
    a ∉ (((synCins2k (synCssetk))).fv) ∪ ((syntaxClass0028).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0179 freshnessCertificate0256))
  have freshnessCertificate0258 : a ∉ (syntaxClass0029).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif];
      exact freshnessCertificate0257)
  have freshnessCertificate0259 :
    a ∉ (((synCopk (.cv t) (synCopk (.cv n) (.cv x)))).fv) ∪ ((syntaxClass0029).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0177 freshnessCertificate0258))
  have freshnessCertificate0260 :
    a ∉
      ((Wff.classMem (synCopk (.cv t) (synCopk (.cv n) (.cv x))) syntaxClass0029)).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact freshnessCertificate0259)
  have p0008 :=
    @gN1941v (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv a))))) syntaxFormula0033
      a (by exact freshnessCertificate0260)
  have p0009 :=
    @gBitr4i syntaxFormula0034
      (synWa (synWex a (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv a))))))
        syntaxFormula0033)
      syntaxFormula0036 p0007 p0008
  have p0010 := @gExbii syntaxFormula0034 syntaxFormula0036 t p0009
  have p0011 := (Nominal.biimpRefl syntaxFormula0037)
  have p0012 := @gExcom syntaxFormula0035 a t
  have p0013 :=
    @gN3bitr4i (synWex t syntaxFormula0034) (synWex t syntaxFormula0036)
      syntaxFormula0037 syntaxFormula0039 p0010 p0011 p0012
  have p0014 := @gSnex (synCsn (synCsn (.cv a)))
  have p0015 :=
    @gOpkeq1 (.cv t) (synCsn (synCsn (synCsn (.cv a)))) (synCopk (.cv n) (.cv x))
  have p0016 :=
    @gEleq1d (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv a)))))
      (synCopk (.cv t) (synCopk (.cv n) (.cv x)))
      (synCopk (synCsn (synCsn (synCsn (.cv a)))) (synCopk (.cv n) (.cv x)))
      syntaxClass0029 p0015
  have freshnessCertificate0261 : t ∉ ((Class.cv a)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show t ∉ ({ a } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show t ≠ a from (by exact fresh_t_ne_a)))))
  have freshnessCertificate0262 : t ∉ ((synCsn (.cv a))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0261)
  have freshnessCertificate0263 : t ∉ ((synCsn (synCsn (.cv a)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0262)
  have freshnessCertificate0264 : t ∉ ((synCsn (synCsn (synCsn (.cv a))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0263)
  have freshnessCertificate0265 :
    t ∉
      (((synCsn (synCsn (synCsn (.cv a))))).fv) ∪ (((synCopk (.cv n) (.cv x))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0264 freshnessCertificate0170))
  have freshnessCertificate0266 :
    t ∉
      ((synCopk (synCsn (synCsn (synCsn (.cv a)))) (synCopk (.cv n) (.cv x)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk];
      exact freshnessCertificate0265)
  have freshnessCertificate0267 :
    t ∉
      (((synCopk (synCsn (synCsn (synCsn (.cv a)))) (synCopk (.cv n) (.cv x)))).fv) ∪
        ((syntaxClass0029).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0266 freshnessCertificate0166))
  have freshnessCertificate0268 :
    t ∉
      ((Wff.classMem (synCopk (synCsn (synCsn (synCsn (.cv a)))) (synCopk (.cv n) (.cv x)))
          syntaxClass0029)).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact freshnessCertificate0267)
  have p0017 :=
    @gCeqsexv syntaxFormula0033 syntaxFormula0040 t (synCsn (synCsn (synCsn (.cv a))))
      (by exact freshnessCertificate0264) (by exact freshnessCertificate0268) p0014 p0016
  have p0018 :=
    @gElsymdif
      (synCopk (synCsn (synCsn (synCsn (.cv a)))) (synCopk (.cv n) (.cv x)))
      (synCins2k (synCssetk)) syntaxClass0028
  have p0019 := @gSnex (.cv a)
  have p0020 := @gVex n
  have p0021 :=
    @gOtkelins2k (synCsn (.cv a)) (.cv n) (.cv x) (synCssetk) p0019 p0020 p0002
  have p0022 := @gVex a
  have p0023 := @gElssetk (.cv a) (.cv x) p0022 p0002
  have p0024_e01_recanon :
    Nominal.NPrf
      (synWb (.classMem (synCopk (synCsn (.cv a)) (.cv x)) (synCssetk)) (.objMem a x)) :=
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
      p0023
  have p0024 :=
    @gBitri syntaxFormula0041
      (.classMem (synCopk (synCsn (.cv a)) (.cv x)) (synCssetk)) (.objMem a x) p0021
      p0024_e01_recanon
  have p0025 := @gOpkex (synCsn (.cv a)) (.cv n)
  have freshnessCertificate0269 : t ∉ (((synCsn (.cv a))).fv) ∪ (((Class.cv n)).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0262 freshnessCertificate0167))
  have freshnessCertificate0270 : t ∉ ((synCopk (synCsn (.cv a)) (.cv n))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk];
      exact freshnessCertificate0269)
  have p0026 :=
    @gElimak t syntaxClass0026 (synCpw1 (synCpw1 (synCpw1 (synC1c))))
      (synCopk (synCsn (.cv a)) (.cv n)) (by exact freshnessCertificate0161)
      (by exact freshnessCertificate0122) (by exact freshnessCertificate0270) p0025
  have p0027 := (Nominal.biimpRefl syntaxFormula0043)
  have freshnessCertificate0271 : x ∉ ((Class.cv t)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show x ∉ ({ t } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show x ≠ t from (by exact fresh_x_ne_t)))))
  have p0028 := @gElpw131c x (.cv t) (by exact freshnessCertificate0271)
  have p0029 :=
    @gAnbi1i (.classMem (.cv t) (synCpw1 (synCpw1 (synCpw1 (synC1c)))))
      (synWex x (.classEq (.cv t) (synCsn (synCsn (synCsn (synCsn (.cv x)))))))
      syntaxFormula0042 p0028
  have freshnessCertificate0272 : x ∉ ((Class.cv a)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show x ∉ ({ a } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show x ≠ a from (by exact fresh_x_ne_a)))))
  have freshnessCertificate0273 : x ∉ ((synCsn (.cv a))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0272)
  have freshnessCertificate0274 : x ∉ ((Class.cv n)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show x ∉ ({ n } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show x ≠ n from (by exact fresh_x_ne_n)))))
  have freshnessCertificate0275 : x ∉ (((synCsn (.cv a))).fv) ∪ (((Class.cv n)).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0273 freshnessCertificate0274))
  have freshnessCertificate0276 : x ∉ ((synCopk (synCsn (.cv a)) (.cv n))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk];
      exact freshnessCertificate0275)
  have freshnessCertificate0277 :
    x ∉ (((Class.cv t)).fv) ∪ (((synCopk (synCsn (.cv a)) (.cv n))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0271 freshnessCertificate0276))
  have freshnessCertificate0278 :
    x ∉ ((synCopk (.cv t) (synCopk (synCsn (.cv a)) (.cv n)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk];
      exact freshnessCertificate0277)
  have freshnessCertificate0279 : x ∉ ((synCssetk)).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk];
      exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))
  have freshnessCertificate0280 : x ∉ ((synCins2k (synCssetk))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0279)
  have freshnessCertificate0281 : x ∉ ((synCins2k (synCins2k (synCssetk)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0280)
  have freshnessCertificate0282 : x ∉ ((synCvv)).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv];
      exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))
  have freshnessCertificate0283 :
    x ∉ (((synCvv)).fv) ∪ (((synCins2k (synCssetk))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0282 freshnessCertificate0280))
  have freshnessCertificate0284 :
    x ∉ ((synCxpk (synCvv) (synCins2k (synCssetk)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk];
      exact freshnessCertificate0283)
  have freshnessCertificate0285 :
    x ∉
      (((synCins2k (synCins2k (synCssetk)))).fv) ∪
        (((synCxpk (synCvv) (synCins2k (synCssetk)))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0281 freshnessCertificate0284))
  have freshnessCertificate0286 : x ∉ (syntaxClass0000).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin];
      exact freshnessCertificate0285)
  have freshnessCertificate0287 : x ∉ ((synCins3k (synCssetk))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0279)
  have freshnessCertificate0288 :
    x ∉ (((synCins3k (synCssetk))).fv) ∪ (((synCins2k (synCssetk))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0287 freshnessCertificate0280))
  have freshnessCertificate0289 :
    x ∉ ((synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin];
      exact freshnessCertificate0288)
  have freshnessCertificate0290 : x ∉ ((synC1c)).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c];
      exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))
  have freshnessCertificate0291 : x ∉ ((synCpw1 (synC1c))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0290)
  have freshnessCertificate0292 : x ∉ ((synCpw1 (synCpw1 (synC1c)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0291)
  have freshnessCertificate0293 :
    x ∉
      (((synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))).fv) ∪
        (((synCpw1 (synCpw1 (synC1c)))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0289 freshnessCertificate0292))
  have freshnessCertificate0294 : x ∉ (syntaxClass0001).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak];
      exact freshnessCertificate0293)
  have freshnessCertificate0295 : x ∉ (syntaxClass0002).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl];
      exact freshnessCertificate0294)
  have freshnessCertificate0296 : x ∉ (syntaxClass0003).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0295)
  have freshnessCertificate0297 : x ∉ (syntaxClass0004).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0296)
  have freshnessCertificate0298 : x ∉ (syntaxClass0005).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0297)
  have freshnessCertificate0299 : x ∉ (syntaxClass0006).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0298)
  have freshnessCertificate0300 : x ∉ ((synCsik (synCssetk))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0279)
  have freshnessCertificate0301 : x ∉ ((synCins3k (synCsik (synCssetk)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0300)
  have freshnessCertificate0302 :
    x ∉ ((synCins2k (synCins3k (synCsik (synCssetk))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0301)
  have freshnessCertificate0303 :
    x ∉ ((synCins2k (synCins2k (synCins3k (synCsik (synCssetk)))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0302)
  have freshnessCertificate0304 : x ∉ ((synCsik (synCsik (synCssetk)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0300)
  have freshnessCertificate0305 :
    x ∉ ((synCsik (synCsik (synCsik (synCssetk))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0304)
  have freshnessCertificate0306 :
    x ∉ ((synCsik (synCsik (synCsik (synCsik (synCssetk)))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0305)
  have freshnessCertificate0307 :
    x ∉ ((synCsik (synCsik (synCsik (synCsik (synCsik (synCssetk))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0306)
  have freshnessCertificate0308 : x ∉ (syntaxClass0007).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0307)
  have freshnessCertificate0309 :
    x ∉ ((synCins3k (synCsik (synCsik (synCsik (synCssetk)))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0305)
  have freshnessCertificate0310 :
    x ∉ ((synCins2k (synCins3k (synCsik (synCsik (synCsik (synCssetk))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0309)
  have freshnessCertificate0311 :
    x ∉
      ((syntaxClass0007).fv) ∪
        (((synCins2k (synCins3k (synCsik (synCsik (synCsik (synCssetk))))))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0308 freshnessCertificate0310))
  have freshnessCertificate0312 : x ∉ (syntaxClass0008).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun];
      exact freshnessCertificate0311)
  have freshnessCertificate0313 :
    x ∉
      (((synCins2k (synCins2k (synCins3k (synCsik (synCssetk)))))).fv) ∪
        ((syntaxClass0008).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0303 freshnessCertificate0312))
  have freshnessCertificate0314 : x ∉ (syntaxClass0009).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif];
      exact freshnessCertificate0313)
  have freshnessCertificate0315 : x ∉ ((synCpw1 (synCpw1 (synCpw1 (synC1c))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0292)
  have freshnessCertificate0316 :
    x ∉ ((synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0315)
  have freshnessCertificate0317 :
    x ∉ ((synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0316)
  have freshnessCertificate0318 :
    x ∉
      ((synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0317)
  have freshnessCertificate0319 : x ∉ (syntaxClass0010).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0318)
  have freshnessCertificate0320 : x ∉ ((syntaxClass0009).fv) ∪ ((syntaxClass0010).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0314 freshnessCertificate0319))
  have freshnessCertificate0321 : x ∉ (syntaxClass0011).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak];
      exact freshnessCertificate0320)
  have freshnessCertificate0322 : x ∉ (syntaxClass0012).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl];
      exact freshnessCertificate0321)
  have freshnessCertificate0323 : x ∉ ((syntaxClass0006).fv) ∪ ((syntaxClass0012).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0299 freshnessCertificate0322))
  have freshnessCertificate0324 : x ∉ (syntaxClass0013).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin];
      exact freshnessCertificate0323)
  have freshnessCertificate0325 : x ∉ ((syntaxClass0000).fv) ∪ ((syntaxClass0013).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0286 freshnessCertificate0324))
  have freshnessCertificate0326 : x ∉ (syntaxClass0014).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin];
      exact freshnessCertificate0325)
  have freshnessCertificate0327 :
    x ∉
      ((syntaxClass0014).fv) ∪
        (((synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0326 freshnessCertificate0316))
  have freshnessCertificate0328 : x ∉ (syntaxClass0015).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak];
      exact freshnessCertificate0327)
  have freshnessCertificate0329 :
    x ∉ ((syntaxClass0015).fv) ∪ (((synCpw1 (synCpw1 (synC1c)))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0328 freshnessCertificate0292))
  have freshnessCertificate0330 : x ∉ (syntaxClass0016).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak];
      exact freshnessCertificate0329)
  have freshnessCertificate0331 : x ∉ (syntaxClass0017).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0330)
  have freshnessCertificate0332 : x ∉ (syntaxClass0018).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0331)
  have freshnessCertificate0333 : x ∉ ((synCcompl (synCssetk))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl];
      exact freshnessCertificate0279)
  have freshnessCertificate0334 : x ∉ ((synCsik (synCcompl (synCssetk)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0333)
  have freshnessCertificate0335 :
    x ∉ ((synCsik (synCsik (synCcompl (synCssetk))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0334)
  have freshnessCertificate0336 :
    x ∉ ((synCsik (synCsik (synCsik (synCcompl (synCssetk)))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0335)
  have freshnessCertificate0337 :
    x ∉ ((synCcnvk (synCsik (synCsik (synCsik (synCcompl (synCssetk))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk];
      exact freshnessCertificate0336)
  have freshnessCertificate0338 : x ∉ (syntaxClass0019).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0337)
  have freshnessCertificate0339 : x ∉ ((syntaxClass0018).fv) ∪ ((syntaxClass0019).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0332 freshnessCertificate0338))
  have freshnessCertificate0340 : x ∉ (syntaxClass0020).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin];
      exact freshnessCertificate0339)
  have freshnessCertificate0341 : x ∉ ((synCidk)).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cidk];
      exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))
  have freshnessCertificate0342 : x ∉ ((synCins3k (synCidk))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0341)
  have freshnessCertificate0343 : x ∉ ((synCins2k (synCins3k (synCidk)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0342)
  have freshnessCertificate0344 :
    x ∉ ((syntaxClass0007).fv) ∪ (((synCins2k (synCins3k (synCidk)))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0308 freshnessCertificate0343))
  have freshnessCertificate0345 : x ∉ (syntaxClass0021).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun];
      exact freshnessCertificate0344)
  have freshnessCertificate0346 :
    x ∉
      (((synCins2k (synCins2k (synCins3k (synCsik (synCssetk)))))).fv) ∪
        ((syntaxClass0021).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0303 freshnessCertificate0345))
  have freshnessCertificate0347 : x ∉ (syntaxClass0022).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif];
      exact freshnessCertificate0346)
  have freshnessCertificate0348 : x ∉ ((syntaxClass0022).fv) ∪ ((syntaxClass0010).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0347 freshnessCertificate0319))
  have freshnessCertificate0349 : x ∉ (syntaxClass0023).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak];
      exact freshnessCertificate0348)
  have freshnessCertificate0350 : x ∉ (syntaxClass0024).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl];
      exact freshnessCertificate0349)
  have freshnessCertificate0351 : x ∉ ((syntaxClass0020).fv) ∪ ((syntaxClass0024).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0340 freshnessCertificate0350))
  have freshnessCertificate0352 : x ∉ (syntaxClass0025).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin];
      exact freshnessCertificate0351)
  have freshnessCertificate0353 :
    x ∉
      ((syntaxClass0025).fv) ∪
        (((synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0352 freshnessCertificate0316))
  have freshnessCertificate0354 : x ∉ (syntaxClass0026).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak];
      exact freshnessCertificate0353)
  have freshnessCertificate0355 :
    x ∉
      (((synCopk (.cv t) (synCopk (synCsn (.cv a)) (.cv n)))).fv) ∪
        ((syntaxClass0026).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0278 freshnessCertificate0354))
  have freshnessCertificate0356 :
    x ∉
      ((Wff.classMem (synCopk (.cv t) (synCopk (synCsn (.cv a)) (.cv n)))
          syntaxClass0026)).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact freshnessCertificate0355)
  have p0030 :=
    @gN1941v (.classEq (.cv t) (synCsn (synCsn (synCsn (synCsn (.cv x))))))
      syntaxFormula0042 x (by exact freshnessCertificate0356)
  have p0031 :=
    @gBitr4i syntaxFormula0044
      (synWa (synWex x (.classEq (.cv t) (synCsn (synCsn (synCsn (synCsn (.cv x)))))))
        syntaxFormula0042)
      syntaxFormula0046 p0029 p0030
  have p0032 := @gExbii syntaxFormula0044 syntaxFormula0046 t p0031
  have p0033 := @gExcom syntaxFormula0045 t x
  have p0034 :=
    @gN3bitri syntaxFormula0043 (synWex t syntaxFormula0044)
      (synWex t syntaxFormula0046) syntaxFormula0048 p0027 p0032 p0033
  have p0035 := @gSnex (synCsn (synCsn (synCsn (.cv x))))
  have p0036 :=
    @gOpkeq1 (.cv t) (synCsn (synCsn (synCsn (synCsn (.cv x)))))
      (synCopk (synCsn (.cv a)) (.cv n))
  have p0037 :=
    @gEleq1d (.classEq (.cv t) (synCsn (synCsn (synCsn (synCsn (.cv x))))))
      (synCopk (.cv t) (synCopk (synCsn (.cv a)) (.cv n))) syntaxClass0049
      syntaxClass0026 p0036
  have freshnessCertificate0357 : t ∉ ((synCsn (.cv x))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0168)
  have freshnessCertificate0358 : t ∉ ((synCsn (synCsn (.cv x)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0357)
  have freshnessCertificate0359 : t ∉ ((synCsn (synCsn (synCsn (.cv x))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0358)
  have freshnessCertificate0360 :
    t ∉ ((synCsn (synCsn (synCsn (synCsn (.cv x)))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0359)
  have freshnessCertificate0361 :
    t ∉
      (((synCsn (synCsn (synCsn (synCsn (.cv x)))))).fv) ∪
        (((synCopk (synCsn (.cv a)) (.cv n))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0360 freshnessCertificate0270))
  have freshnessCertificate0362 : t ∉ (syntaxClass0049).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk];
      exact freshnessCertificate0361)
  have freshnessCertificate0363 : t ∉ ((syntaxClass0049).fv) ∪ ((syntaxClass0026).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0362 freshnessCertificate0161))
  have freshnessCertificate0364 :
    t ∉ ((Wff.classMem syntaxClass0049 syntaxClass0026)).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact freshnessCertificate0363)
  have p0038 :=
    @gCeqsexv syntaxFormula0042 syntaxFormula0050 t
      (synCsn (synCsn (synCsn (synCsn (.cv x))))) (by exact freshnessCertificate0360)
      (by exact freshnessCertificate0364) p0035 p0037
  have p0039 :=
    @gOpkex (synCsn (synCsn (synCsn (synCsn (.cv x)))))
      (synCopk (synCsn (.cv a)) (.cv n))
  have p0040 :=
    @gElimak t syntaxClass0025 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))
      syntaxClass0049 (by exact freshnessCertificate0159)
      (by exact freshnessCertificate0123) (by exact freshnessCertificate0362) p0039
  have p0041 := (Nominal.biimpRefl syntaxFormula0053)
  have freshnessCertificate0365 : b ∉ ((Class.cv t)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show b ∉ ({ t } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show b ≠ t from (by exact fresh_b_ne_t)))))
  have p0042 := @gElpw141c b (.cv t) (by exact freshnessCertificate0365)
  have p0043 :=
    @gAnbi1i (.classMem (.cv t) (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))
      (synWex b (.classEq (.cv t) (synCsn (synCsn (synCsn (synCsn (synCsn (.cv b))))))))
      syntaxFormula0052 p0042
  have freshnessCertificate0366 : b ∉ ((Class.cv x)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show b ∉ ({ x } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show b ≠ x from (by exact fresh_b_ne_x)))))
  have freshnessCertificate0367 : b ∉ ((synCsn (.cv x))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0366)
  have freshnessCertificate0368 : b ∉ ((synCsn (synCsn (.cv x)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0367)
  have freshnessCertificate0369 : b ∉ ((synCsn (synCsn (synCsn (.cv x))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0368)
  have freshnessCertificate0370 :
    b ∉ ((synCsn (synCsn (synCsn (synCsn (.cv x)))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0369)
  have freshnessCertificate0371 : b ∉ ((Class.cv a)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show b ∉ ({ a } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show b ≠ a from (by exact fresh_b_ne_a)))))
  have freshnessCertificate0372 : b ∉ ((synCsn (.cv a))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0371)
  have freshnessCertificate0373 : b ∉ ((Class.cv n)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show b ∉ ({ n } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show b ≠ n from (by exact fresh_b_ne_n)))))
  have freshnessCertificate0374 : b ∉ (((synCsn (.cv a))).fv) ∪ (((Class.cv n)).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0372 freshnessCertificate0373))
  have freshnessCertificate0375 : b ∉ ((synCopk (synCsn (.cv a)) (.cv n))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk];
      exact freshnessCertificate0374)
  have freshnessCertificate0376 :
    b ∉
      (((synCsn (synCsn (synCsn (synCsn (.cv x)))))).fv) ∪
        (((synCopk (synCsn (.cv a)) (.cv n))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0370 freshnessCertificate0375))
  have freshnessCertificate0377 : b ∉ (syntaxClass0049).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk];
      exact freshnessCertificate0376)
  have freshnessCertificate0378 : b ∉ (((Class.cv t)).fv) ∪ ((syntaxClass0049).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0365 freshnessCertificate0377))
  have freshnessCertificate0379 : b ∉ (syntaxClass0051).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk];
      exact freshnessCertificate0378)
  have freshnessCertificate0380 : b ∉ ((synCssetk)).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk];
      exact (show b ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))
  have freshnessCertificate0381 : b ∉ ((synCins2k (synCssetk))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0380)
  have freshnessCertificate0382 : b ∉ ((synCins2k (synCins2k (synCssetk)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0381)
  have freshnessCertificate0383 : b ∉ ((synCvv)).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv];
      exact (show b ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))
  have freshnessCertificate0384 :
    b ∉ (((synCvv)).fv) ∪ (((synCins2k (synCssetk))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0383 freshnessCertificate0381))
  have freshnessCertificate0385 :
    b ∉ ((synCxpk (synCvv) (synCins2k (synCssetk)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk];
      exact freshnessCertificate0384)
  have freshnessCertificate0386 :
    b ∉
      (((synCins2k (synCins2k (synCssetk)))).fv) ∪
        (((synCxpk (synCvv) (synCins2k (synCssetk)))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0382 freshnessCertificate0385))
  have freshnessCertificate0387 : b ∉ (syntaxClass0000).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin];
      exact freshnessCertificate0386)
  have freshnessCertificate0388 : b ∉ ((synCins3k (synCssetk))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0380)
  have freshnessCertificate0389 :
    b ∉ (((synCins3k (synCssetk))).fv) ∪ (((synCins2k (synCssetk))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0388 freshnessCertificate0381))
  have freshnessCertificate0390 :
    b ∉ ((synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin];
      exact freshnessCertificate0389)
  have freshnessCertificate0391 : b ∉ ((synC1c)).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c];
      exact (show b ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))
  have freshnessCertificate0392 : b ∉ ((synCpw1 (synC1c))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0391)
  have freshnessCertificate0393 : b ∉ ((synCpw1 (synCpw1 (synC1c)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0392)
  have freshnessCertificate0394 :
    b ∉
      (((synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))).fv) ∪
        (((synCpw1 (synCpw1 (synC1c)))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0390 freshnessCertificate0393))
  have freshnessCertificate0395 : b ∉ (syntaxClass0001).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak];
      exact freshnessCertificate0394)
  have freshnessCertificate0396 : b ∉ (syntaxClass0002).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl];
      exact freshnessCertificate0395)
  have freshnessCertificate0397 : b ∉ (syntaxClass0003).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0396)
  have freshnessCertificate0398 : b ∉ (syntaxClass0004).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0397)
  have freshnessCertificate0399 : b ∉ (syntaxClass0005).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0398)
  have freshnessCertificate0400 : b ∉ (syntaxClass0006).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0399)
  have freshnessCertificate0401 : b ∉ ((synCsik (synCssetk))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0380)
  have freshnessCertificate0402 : b ∉ ((synCins3k (synCsik (synCssetk)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0401)
  have freshnessCertificate0403 :
    b ∉ ((synCins2k (synCins3k (synCsik (synCssetk))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0402)
  have freshnessCertificate0404 :
    b ∉ ((synCins2k (synCins2k (synCins3k (synCsik (synCssetk)))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0403)
  have freshnessCertificate0405 : b ∉ ((synCsik (synCsik (synCssetk)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0401)
  have freshnessCertificate0406 :
    b ∉ ((synCsik (synCsik (synCsik (synCssetk))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0405)
  have freshnessCertificate0407 :
    b ∉ ((synCsik (synCsik (synCsik (synCsik (synCssetk)))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0406)
  have freshnessCertificate0408 :
    b ∉ ((synCsik (synCsik (synCsik (synCsik (synCsik (synCssetk))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0407)
  have freshnessCertificate0409 : b ∉ (syntaxClass0007).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0408)
  have freshnessCertificate0410 :
    b ∉ ((synCins3k (synCsik (synCsik (synCsik (synCssetk)))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0406)
  have freshnessCertificate0411 :
    b ∉ ((synCins2k (synCins3k (synCsik (synCsik (synCsik (synCssetk))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0410)
  have freshnessCertificate0412 :
    b ∉
      ((syntaxClass0007).fv) ∪
        (((synCins2k (synCins3k (synCsik (synCsik (synCsik (synCssetk))))))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0409 freshnessCertificate0411))
  have freshnessCertificate0413 : b ∉ (syntaxClass0008).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun];
      exact freshnessCertificate0412)
  have freshnessCertificate0414 :
    b ∉
      (((synCins2k (synCins2k (synCins3k (synCsik (synCssetk)))))).fv) ∪
        ((syntaxClass0008).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0404 freshnessCertificate0413))
  have freshnessCertificate0415 : b ∉ (syntaxClass0009).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif];
      exact freshnessCertificate0414)
  have freshnessCertificate0416 : b ∉ ((synCpw1 (synCpw1 (synCpw1 (synC1c))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0393)
  have freshnessCertificate0417 :
    b ∉ ((synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0416)
  have freshnessCertificate0418 :
    b ∉ ((synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0417)
  have freshnessCertificate0419 :
    b ∉
      ((synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0418)
  have freshnessCertificate0420 : b ∉ (syntaxClass0010).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0419)
  have freshnessCertificate0421 : b ∉ ((syntaxClass0009).fv) ∪ ((syntaxClass0010).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0415 freshnessCertificate0420))
  have freshnessCertificate0422 : b ∉ (syntaxClass0011).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak];
      exact freshnessCertificate0421)
  have freshnessCertificate0423 : b ∉ (syntaxClass0012).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl];
      exact freshnessCertificate0422)
  have freshnessCertificate0424 : b ∉ ((syntaxClass0006).fv) ∪ ((syntaxClass0012).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0400 freshnessCertificate0423))
  have freshnessCertificate0425 : b ∉ (syntaxClass0013).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin];
      exact freshnessCertificate0424)
  have freshnessCertificate0426 : b ∉ ((syntaxClass0000).fv) ∪ ((syntaxClass0013).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0387 freshnessCertificate0425))
  have freshnessCertificate0427 : b ∉ (syntaxClass0014).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin];
      exact freshnessCertificate0426)
  have freshnessCertificate0428 :
    b ∉
      ((syntaxClass0014).fv) ∪
        (((synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0427 freshnessCertificate0417))
  have freshnessCertificate0429 : b ∉ (syntaxClass0015).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak];
      exact freshnessCertificate0428)
  have freshnessCertificate0430 :
    b ∉ ((syntaxClass0015).fv) ∪ (((synCpw1 (synCpw1 (synC1c)))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0429 freshnessCertificate0393))
  have freshnessCertificate0431 : b ∉ (syntaxClass0016).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak];
      exact freshnessCertificate0430)
  have freshnessCertificate0432 : b ∉ (syntaxClass0017).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0431)
  have freshnessCertificate0433 : b ∉ (syntaxClass0018).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0432)
  have freshnessCertificate0434 : b ∉ ((synCcompl (synCssetk))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl];
      exact freshnessCertificate0380)
  have freshnessCertificate0435 : b ∉ ((synCsik (synCcompl (synCssetk)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0434)
  have freshnessCertificate0436 :
    b ∉ ((synCsik (synCsik (synCcompl (synCssetk))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0435)
  have freshnessCertificate0437 :
    b ∉ ((synCsik (synCsik (synCsik (synCcompl (synCssetk)))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0436)
  have freshnessCertificate0438 :
    b ∉ ((synCcnvk (synCsik (synCsik (synCsik (synCcompl (synCssetk))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk];
      exact freshnessCertificate0437)
  have freshnessCertificate0439 : b ∉ (syntaxClass0019).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0438)
  have freshnessCertificate0440 : b ∉ ((syntaxClass0018).fv) ∪ ((syntaxClass0019).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0433 freshnessCertificate0439))
  have freshnessCertificate0441 : b ∉ (syntaxClass0020).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin];
      exact freshnessCertificate0440)
  have freshnessCertificate0442 : b ∉ ((synCidk)).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cidk];
      exact (show b ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))
  have freshnessCertificate0443 : b ∉ ((synCins3k (synCidk))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0442)
  have freshnessCertificate0444 : b ∉ ((synCins2k (synCins3k (synCidk)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0443)
  have freshnessCertificate0445 :
    b ∉ ((syntaxClass0007).fv) ∪ (((synCins2k (synCins3k (synCidk)))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0409 freshnessCertificate0444))
  have freshnessCertificate0446 : b ∉ (syntaxClass0021).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun];
      exact freshnessCertificate0445)
  have freshnessCertificate0447 :
    b ∉
      (((synCins2k (synCins2k (synCins3k (synCsik (synCssetk)))))).fv) ∪
        ((syntaxClass0021).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0404 freshnessCertificate0446))
  have freshnessCertificate0448 : b ∉ (syntaxClass0022).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif];
      exact freshnessCertificate0447)
  have freshnessCertificate0449 : b ∉ ((syntaxClass0022).fv) ∪ ((syntaxClass0010).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0448 freshnessCertificate0420))
  have freshnessCertificate0450 : b ∉ (syntaxClass0023).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak];
      exact freshnessCertificate0449)
  have freshnessCertificate0451 : b ∉ (syntaxClass0024).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl];
      exact freshnessCertificate0450)
  have freshnessCertificate0452 : b ∉ ((syntaxClass0020).fv) ∪ ((syntaxClass0024).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0441 freshnessCertificate0451))
  have freshnessCertificate0453 : b ∉ (syntaxClass0025).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin];
      exact freshnessCertificate0452)
  have freshnessCertificate0454 : b ∉ ((syntaxClass0051).fv) ∪ ((syntaxClass0025).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0379 freshnessCertificate0453))
  have freshnessCertificate0455 :
    b ∉ ((Wff.classMem syntaxClass0051 syntaxClass0025)).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact freshnessCertificate0454)
  have p0044 :=
    @gN1941v
      (.classEq (.cv t) (synCsn (synCsn (synCsn (synCsn (synCsn (.cv b)))))))
      syntaxFormula0052 b (by exact freshnessCertificate0455)
  have p0045 :=
    @gBitr4i syntaxFormula0054
      (synWa (synWex b
          (.classEq (.cv t) (synCsn (synCsn (synCsn (synCsn (synCsn (.cv b))))))))
        syntaxFormula0052)
      syntaxFormula0056 p0043 p0044
  have p0046 := @gExbii syntaxFormula0054 syntaxFormula0056 t p0045
  have p0047 := @gExcom syntaxFormula0055 b t
  have p0048 :=
    @gBitr4i syntaxFormula0057 (synWex t syntaxFormula0056) syntaxFormula0059 p0046
      p0047
  have p0049 :=
    @gN3bitri syntaxFormula0050 syntaxFormula0053 syntaxFormula0057 syntaxFormula0059
      p0040 p0041 p0048
  have p0050 := @gSnex (synCsn (synCsn (synCsn (synCsn (.cv b)))))
  have p0051 :=
    @gOpkeq1 (.cv t) (synCsn (synCsn (synCsn (synCsn (synCsn (.cv b))))))
      syntaxClass0049
  have p0052 :=
    @gEleq1d (.classEq (.cv t) (synCsn (synCsn (synCsn (synCsn (synCsn (.cv b)))))))
      syntaxClass0051 syntaxClass0060 syntaxClass0025 p0051
  have freshnessCertificate0456 : t ∉ ((Class.cv b)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show t ∉ ({ b } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show t ≠ b from (by exact fresh_t_ne_b)))))
  have freshnessCertificate0457 : t ∉ ((synCsn (.cv b))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0456)
  have freshnessCertificate0458 : t ∉ ((synCsn (synCsn (.cv b)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0457)
  have freshnessCertificate0459 : t ∉ ((synCsn (synCsn (synCsn (.cv b))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0458)
  have freshnessCertificate0460 :
    t ∉ ((synCsn (synCsn (synCsn (synCsn (.cv b)))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0459)
  have freshnessCertificate0461 :
    t ∉ ((synCsn (synCsn (synCsn (synCsn (synCsn (.cv b))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0460)
  have freshnessCertificate0462 :
    t ∉
      (((synCsn (synCsn (synCsn (synCsn (synCsn (.cv b))))))).fv) ∪
        ((syntaxClass0049).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0461 freshnessCertificate0362))
  have freshnessCertificate0463 : t ∉ (syntaxClass0060).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk];
      exact freshnessCertificate0462)
  have freshnessCertificate0464 : t ∉ ((syntaxClass0060).fv) ∪ ((syntaxClass0025).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0463 freshnessCertificate0159))
  have freshnessCertificate0465 :
    t ∉ ((Wff.classMem syntaxClass0060 syntaxClass0025)).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact freshnessCertificate0464)
  have p0053 :=
    @gCeqsexv syntaxFormula0052 syntaxFormula0061 t
      (synCsn (synCsn (synCsn (synCsn (synCsn (.cv b))))))
      (by exact freshnessCertificate0461) (by exact freshnessCertificate0465) p0050 p0052
  have p0054 := @gElin syntaxClass0060 syntaxClass0020 syntaxClass0024
  have p0055 := @gElin syntaxClass0060 syntaxClass0018 syntaxClass0019
  have p0056 := @gSnex (synCsn (synCsn (.cv b)))
  have p0057 :=
    @gOtkelins2k (synCsn (synCsn (synCsn (.cv b))))
      (synCsn (synCsn (synCsn (synCsn (.cv x))))) (synCopk (synCsn (.cv a)) (.cv n))
      syntaxClass0017 p0056 p0035 p0025
  have p0058 := @gSnex (.cv b)
  have p0059 :=
    @gOtkelins2k (synCsn (.cv b)) (synCsn (.cv a)) (.cv n) syntaxClass0016 p0058 p0019
      p0020
  have p0060 := @gOpkex (synCsn (.cv b)) (.cv n)
  have freshnessCertificate0466 : t ∉ (((synCsn (.cv b))).fv) ∪ (((Class.cv n)).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0457 freshnessCertificate0167))
  have freshnessCertificate0467 : t ∉ ((synCopk (synCsn (.cv b)) (.cv n))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk];
      exact freshnessCertificate0466)
  have p0061 :=
    @gElimak t syntaxClass0015 (synCpw1 (synCpw1 (synC1c)))
      (synCopk (synCsn (.cv b)) (.cv n)) (by exact freshnessCertificate0135)
      (by exact freshnessCertificate0099) (by exact freshnessCertificate0467) p0060
  have freshnessCertificate0468 : c ∉ ((Class.cv t)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show c ∉ ({ t } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show c ≠ t from (by exact fresh_c_ne_t)))))
  have p0062 := @gElpw121c c (.cv t) (by exact freshnessCertificate0468)
  have p0063 :=
    @gAnbi1i (.classMem (.cv t) (synCpw1 (synCpw1 (synC1c))))
      (synWex c (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv c))))))
      syntaxFormula0062 p0062
  have freshnessCertificate0469 : c ∉ ((Class.cv b)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show c ∉ ({ b } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show c ≠ b from (by exact fresh_c_ne_b)))))
  have freshnessCertificate0470 : c ∉ ((synCsn (.cv b))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0469)
  have freshnessCertificate0471 : c ∉ ((Class.cv n)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show c ∉ ({ n } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show c ≠ n from (by exact fresh_c_ne_n)))))
  have freshnessCertificate0472 : c ∉ (((synCsn (.cv b))).fv) ∪ (((Class.cv n)).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0470 freshnessCertificate0471))
  have freshnessCertificate0473 : c ∉ ((synCopk (synCsn (.cv b)) (.cv n))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk];
      exact freshnessCertificate0472)
  have freshnessCertificate0474 :
    c ∉ (((Class.cv t)).fv) ∪ (((synCopk (synCsn (.cv b)) (.cv n))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0468 freshnessCertificate0473))
  have freshnessCertificate0475 :
    c ∉ ((synCopk (.cv t) (synCopk (synCsn (.cv b)) (.cv n)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk];
      exact freshnessCertificate0474)
  have freshnessCertificate0476 : c ∉ ((synCssetk)).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk];
      exact (show c ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))
  have freshnessCertificate0477 : c ∉ ((synCins2k (synCssetk))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0476)
  have freshnessCertificate0478 : c ∉ ((synCins2k (synCins2k (synCssetk)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0477)
  have freshnessCertificate0479 : c ∉ ((synCvv)).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv];
      exact (show c ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))
  have freshnessCertificate0480 :
    c ∉ (((synCvv)).fv) ∪ (((synCins2k (synCssetk))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0479 freshnessCertificate0477))
  have freshnessCertificate0481 :
    c ∉ ((synCxpk (synCvv) (synCins2k (synCssetk)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk];
      exact freshnessCertificate0480)
  have freshnessCertificate0482 :
    c ∉
      (((synCins2k (synCins2k (synCssetk)))).fv) ∪
        (((synCxpk (synCvv) (synCins2k (synCssetk)))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0478 freshnessCertificate0481))
  have freshnessCertificate0483 : c ∉ (syntaxClass0000).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin];
      exact freshnessCertificate0482)
  have freshnessCertificate0484 : c ∉ ((synCins3k (synCssetk))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0476)
  have freshnessCertificate0485 :
    c ∉ (((synCins3k (synCssetk))).fv) ∪ (((synCins2k (synCssetk))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0484 freshnessCertificate0477))
  have freshnessCertificate0486 :
    c ∉ ((synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin];
      exact freshnessCertificate0485)
  have freshnessCertificate0487 : c ∉ ((synC1c)).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c];
      exact (show c ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))
  have freshnessCertificate0488 : c ∉ ((synCpw1 (synC1c))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0487)
  have freshnessCertificate0489 : c ∉ ((synCpw1 (synCpw1 (synC1c)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0488)
  have freshnessCertificate0490 :
    c ∉
      (((synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))).fv) ∪
        (((synCpw1 (synCpw1 (synC1c)))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0486 freshnessCertificate0489))
  have freshnessCertificate0491 : c ∉ (syntaxClass0001).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak];
      exact freshnessCertificate0490)
  have freshnessCertificate0492 : c ∉ (syntaxClass0002).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl];
      exact freshnessCertificate0491)
  have freshnessCertificate0493 : c ∉ (syntaxClass0003).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0492)
  have freshnessCertificate0494 : c ∉ (syntaxClass0004).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0493)
  have freshnessCertificate0495 : c ∉ (syntaxClass0005).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0494)
  have freshnessCertificate0496 : c ∉ (syntaxClass0006).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0495)
  have freshnessCertificate0497 : c ∉ ((synCsik (synCssetk))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0476)
  have freshnessCertificate0498 : c ∉ ((synCins3k (synCsik (synCssetk)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0497)
  have freshnessCertificate0499 :
    c ∉ ((synCins2k (synCins3k (synCsik (synCssetk))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0498)
  have freshnessCertificate0500 :
    c ∉ ((synCins2k (synCins2k (synCins3k (synCsik (synCssetk)))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0499)
  have freshnessCertificate0501 : c ∉ ((synCsik (synCsik (synCssetk)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0497)
  have freshnessCertificate0502 :
    c ∉ ((synCsik (synCsik (synCsik (synCssetk))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0501)
  have freshnessCertificate0503 :
    c ∉ ((synCsik (synCsik (synCsik (synCsik (synCssetk)))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0502)
  have freshnessCertificate0504 :
    c ∉ ((synCsik (synCsik (synCsik (synCsik (synCsik (synCssetk))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0503)
  have freshnessCertificate0505 : c ∉ (syntaxClass0007).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0504)
  have freshnessCertificate0506 :
    c ∉ ((synCins3k (synCsik (synCsik (synCsik (synCssetk)))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0502)
  have freshnessCertificate0507 :
    c ∉ ((synCins2k (synCins3k (synCsik (synCsik (synCsik (synCssetk))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0506)
  have freshnessCertificate0508 :
    c ∉
      ((syntaxClass0007).fv) ∪
        (((synCins2k (synCins3k (synCsik (synCsik (synCsik (synCssetk))))))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0505 freshnessCertificate0507))
  have freshnessCertificate0509 : c ∉ (syntaxClass0008).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun];
      exact freshnessCertificate0508)
  have freshnessCertificate0510 :
    c ∉
      (((synCins2k (synCins2k (synCins3k (synCsik (synCssetk)))))).fv) ∪
        ((syntaxClass0008).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0500 freshnessCertificate0509))
  have freshnessCertificate0511 : c ∉ (syntaxClass0009).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif];
      exact freshnessCertificate0510)
  have freshnessCertificate0512 : c ∉ ((synCpw1 (synCpw1 (synCpw1 (synC1c))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0489)
  have freshnessCertificate0513 :
    c ∉ ((synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0512)
  have freshnessCertificate0514 :
    c ∉ ((synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0513)
  have freshnessCertificate0515 :
    c ∉
      ((synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0514)
  have freshnessCertificate0516 : c ∉ (syntaxClass0010).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0515)
  have freshnessCertificate0517 : c ∉ ((syntaxClass0009).fv) ∪ ((syntaxClass0010).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0511 freshnessCertificate0516))
  have freshnessCertificate0518 : c ∉ (syntaxClass0011).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak];
      exact freshnessCertificate0517)
  have freshnessCertificate0519 : c ∉ (syntaxClass0012).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl];
      exact freshnessCertificate0518)
  have freshnessCertificate0520 : c ∉ ((syntaxClass0006).fv) ∪ ((syntaxClass0012).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0496 freshnessCertificate0519))
  have freshnessCertificate0521 : c ∉ (syntaxClass0013).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin];
      exact freshnessCertificate0520)
  have freshnessCertificate0522 : c ∉ ((syntaxClass0000).fv) ∪ ((syntaxClass0013).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0483 freshnessCertificate0521))
  have freshnessCertificate0523 : c ∉ (syntaxClass0014).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin];
      exact freshnessCertificate0522)
  have freshnessCertificate0524 :
    c ∉
      ((syntaxClass0014).fv) ∪
        (((synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0523 freshnessCertificate0513))
  have freshnessCertificate0525 : c ∉ (syntaxClass0015).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak];
      exact freshnessCertificate0524)
  have freshnessCertificate0526 :
    c ∉
      (((synCopk (.cv t) (synCopk (synCsn (.cv b)) (.cv n)))).fv) ∪
        ((syntaxClass0015).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0475 freshnessCertificate0525))
  have freshnessCertificate0527 :
    c ∉
      ((Wff.classMem (synCopk (.cv t) (synCopk (synCsn (.cv b)) (.cv n)))
          syntaxClass0015)).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact freshnessCertificate0526)
  have p0064 :=
    @gN1941v (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv c))))) syntaxFormula0062
      c (by exact freshnessCertificate0527)
  have p0065 :=
    @gBitr4i syntaxFormula0063
      (synWa (synWex c (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv c))))))
        syntaxFormula0062)
      syntaxFormula0065 p0063 p0064
  have p0066 := @gExbii syntaxFormula0063 syntaxFormula0065 t p0065
  have p0067 := (Nominal.biimpRefl syntaxFormula0066)
  have p0068 := @gExcom syntaxFormula0064 c t
  have p0069 :=
    @gN3bitr4i (synWex t syntaxFormula0063) (synWex t syntaxFormula0065)
      syntaxFormula0066 syntaxFormula0068 p0066 p0067 p0068
  have p0070 := @gSnex (synCsn (synCsn (.cv c)))
  have p0071 :=
    @gOpkeq1 (.cv t) (synCsn (synCsn (synCsn (.cv c))))
      (synCopk (synCsn (.cv b)) (.cv n))
  have p0072 :=
    @gEleq1d (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv c)))))
      (synCopk (.cv t) (synCopk (synCsn (.cv b)) (.cv n))) syntaxClass0069
      syntaxClass0015 p0071
  have freshnessCertificate0528 : t ∉ ((Class.cv c)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show t ∉ ({ c } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show t ≠ c from (by exact fresh_t_ne_c)))))
  have freshnessCertificate0529 : t ∉ ((synCsn (.cv c))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0528)
  have freshnessCertificate0530 : t ∉ ((synCsn (synCsn (.cv c)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0529)
  have freshnessCertificate0531 : t ∉ ((synCsn (synCsn (synCsn (.cv c))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0530)
  have freshnessCertificate0532 :
    t ∉
      (((synCsn (synCsn (synCsn (.cv c))))).fv) ∪
        (((synCopk (synCsn (.cv b)) (.cv n))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0531 freshnessCertificate0467))
  have freshnessCertificate0533 : t ∉ (syntaxClass0069).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk];
      exact freshnessCertificate0532)
  have freshnessCertificate0534 : t ∉ ((syntaxClass0069).fv) ∪ ((syntaxClass0015).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0533 freshnessCertificate0135))
  have freshnessCertificate0535 :
    t ∉ ((Wff.classMem syntaxClass0069 syntaxClass0015)).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact freshnessCertificate0534)
  have p0073 :=
    @gCeqsexv syntaxFormula0062 syntaxFormula0070 t (synCsn (synCsn (synCsn (.cv c))))
      (by exact freshnessCertificate0531) (by exact freshnessCertificate0535) p0070 p0072
  have p0074 :=
    @gOpkex (synCsn (synCsn (synCsn (.cv c)))) (synCopk (synCsn (.cv b)) (.cv n))
  have p0075 :=
    @gElimak t syntaxClass0014 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))
      syntaxClass0069 (by exact freshnessCertificate0133)
      (by exact freshnessCertificate0123) (by exact freshnessCertificate0533) p0074
  have p0076 := (Nominal.biimpRefl syntaxFormula0073)
  have p0077 := @gElpw141c a (.cv t) (by exact freshnessCertificate0171)
  have p0078 :=
    @gAnbi1i (.classMem (.cv t) (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))
      (synWex a (.classEq (.cv t) (synCsn (synCsn (synCsn (synCsn (synCsn (.cv a))))))))
      syntaxFormula0072 p0077
  have freshnessCertificate0536 : a ∉ ((Class.cv c)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show a ∉ ({ c } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show a ≠ c from (by exact fresh_a_ne_c)))))
  have freshnessCertificate0537 : a ∉ ((synCsn (.cv c))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0536)
  have freshnessCertificate0538 : a ∉ ((synCsn (synCsn (.cv c)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0537)
  have freshnessCertificate0539 : a ∉ ((synCsn (synCsn (synCsn (.cv c))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0538)
  have freshnessCertificate0540 : a ∉ ((Class.cv b)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show a ∉ ({ b } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show a ≠ b from (by exact fresh_a_ne_b)))))
  have freshnessCertificate0541 : a ∉ ((synCsn (.cv b))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0540)
  have freshnessCertificate0542 : a ∉ (((synCsn (.cv b))).fv) ∪ (((Class.cv n)).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0541 freshnessCertificate0172))
  have freshnessCertificate0543 : a ∉ ((synCopk (synCsn (.cv b)) (.cv n))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk];
      exact freshnessCertificate0542)
  have freshnessCertificate0544 :
    a ∉
      (((synCsn (synCsn (synCsn (.cv c))))).fv) ∪
        (((synCopk (synCsn (.cv b)) (.cv n))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0539 freshnessCertificate0543))
  have freshnessCertificate0545 : a ∉ (syntaxClass0069).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk];
      exact freshnessCertificate0544)
  have freshnessCertificate0546 : a ∉ (((Class.cv t)).fv) ∪ ((syntaxClass0069).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0171 freshnessCertificate0545))
  have freshnessCertificate0547 : a ∉ (syntaxClass0071).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk];
      exact freshnessCertificate0546)
  have freshnessCertificate0548 : a ∉ ((syntaxClass0071).fv) ∪ ((syntaxClass0014).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0547 freshnessCertificate0225))
  have freshnessCertificate0549 :
    a ∉ ((Wff.classMem syntaxClass0071 syntaxClass0014)).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact freshnessCertificate0548)
  have p0079 :=
    @gN1941v
      (.classEq (.cv t) (synCsn (synCsn (synCsn (synCsn (synCsn (.cv a)))))))
      syntaxFormula0072 a (by exact freshnessCertificate0549)
  have p0080 :=
    @gBitr4i syntaxFormula0074
      (synWa (synWex a
          (.classEq (.cv t) (synCsn (synCsn (synCsn (synCsn (synCsn (.cv a))))))))
        syntaxFormula0072)
      syntaxFormula0076 p0078 p0079
  have p0081 := @gExbii syntaxFormula0074 syntaxFormula0076 t p0080
  have p0082 := @gExcom syntaxFormula0075 a t
  have p0083 :=
    @gBitr4i syntaxFormula0077 (synWex t syntaxFormula0076) syntaxFormula0079 p0081
      p0082
  have p0084 :=
    @gN3bitri syntaxFormula0070 syntaxFormula0073 syntaxFormula0077 syntaxFormula0079
      p0075 p0076 p0083
  have p0085 := @gSnex (synCsn (synCsn (synCsn (synCsn (.cv a)))))
  have p0086 :=
    @gOpkeq1 (.cv t) (synCsn (synCsn (synCsn (synCsn (synCsn (.cv a))))))
      syntaxClass0069
  have p0087 :=
    @gEleq1d (.classEq (.cv t) (synCsn (synCsn (synCsn (synCsn (synCsn (.cv a)))))))
      syntaxClass0071 syntaxClass0080 syntaxClass0014 p0086
  have freshnessCertificate0550 :
    t ∉ ((synCsn (synCsn (synCsn (synCsn (.cv a)))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0264)
  have freshnessCertificate0551 :
    t ∉ ((synCsn (synCsn (synCsn (synCsn (synCsn (.cv a))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0550)
  have freshnessCertificate0552 :
    t ∉
      (((synCsn (synCsn (synCsn (synCsn (synCsn (.cv a))))))).fv) ∪
        ((syntaxClass0069).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0551 freshnessCertificate0533))
  have freshnessCertificate0553 : t ∉ (syntaxClass0080).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk];
      exact freshnessCertificate0552)
  have freshnessCertificate0554 : t ∉ ((syntaxClass0080).fv) ∪ ((syntaxClass0014).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0553 freshnessCertificate0133))
  have freshnessCertificate0555 :
    t ∉ ((Wff.classMem syntaxClass0080 syntaxClass0014)).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact freshnessCertificate0554)
  have p0088 :=
    @gCeqsexv syntaxFormula0072 syntaxFormula0081 t
      (synCsn (synCsn (synCsn (synCsn (synCsn (.cv a))))))
      (by exact freshnessCertificate0551) (by exact freshnessCertificate0555) p0085 p0087
  have p0089 := @gElin syntaxClass0080 syntaxClass0000 syntaxClass0013
  have p0090 :=
    @gElin syntaxClass0080 (synCins2k (synCins2k (synCssetk)))
      (synCxpk (synCvv) (synCins2k (synCssetk)))
  have p0091 :=
    @gOtkelins2k (synCsn (synCsn (synCsn (.cv a))))
      (synCsn (synCsn (synCsn (.cv c)))) (synCopk (synCsn (.cv b)) (.cv n))
      (synCins2k (synCssetk)) p0014 p0070 p0060
  have p0092 :=
    @gOtkelins2k (synCsn (.cv a)) (synCsn (.cv b)) (.cv n) (synCssetk) p0019 p0058
      p0020
  have p0093 := @gElssetk (.cv a) (.cv n) p0022 p0020
  have p0094_e02_recanon :
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
      p0093
  have p0094 :=
    @gN3bitri syntaxFormula0082
      (.classMem (synCopk (synCsn (synCsn (synCsn (.cv a))))
          (synCopk (synCsn (.cv b)) (.cv n))) (synCins2k (synCssetk)))
      (.classMem (synCopk (synCsn (.cv a)) (.cv n)) (synCssetk)) (.objMem a n) p0091
      p0092 p0094_e02_recanon
  have p0095 :=
    @gOpkelxpk (synCsn (synCsn (synCsn (synCsn (synCsn (.cv a)))))) syntaxClass0069
      (synCvv) (synCins2k (synCssetk)) p0085 p0074
  have p0096 :=
    @gMpbiran syntaxFormula0083
      (.classMem (synCsn (synCsn (synCsn (synCsn (synCsn (.cv a)))))) (synCvv))
      (.classMem syntaxClass0069 (synCins2k (synCssetk))) p0085 p0095
  have p0097 := @gSnex (.cv c)
  have p0098 :=
    @gOtkelins2k (synCsn (.cv c)) (synCsn (.cv b)) (.cv n) (synCssetk) p0097 p0058
      p0020
  have p0099 := @gVex c
  have p0100 := @gElssetk (.cv c) (.cv n) p0099 p0020
  have p0101_e02_recanon :
    Nominal.NPrf
      (synWb (.classMem (synCopk (synCsn (.cv c)) (.cv n)) (synCssetk)) (.objMem c n)) :=
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
      p0100
  have p0101 :=
    @gN3bitri syntaxFormula0083 (.classMem syntaxClass0069 (synCins2k (synCssetk)))
      (.classMem (synCopk (synCsn (.cv c)) (.cv n)) (synCssetk)) (.objMem c n) p0096
      p0098 p0101_e02_recanon
  have p0102 :=
    @gAnbi12i syntaxFormula0082 (.objMem a n) syntaxFormula0083 (.objMem c n) p0094 p0101
  have p0103 :=
    @gBitri syntaxFormula0084 (synWa syntaxFormula0082 syntaxFormula0083)
      (synWa (.objMem a n) (.objMem c n)) p0090 p0102
  have p0104 := @gElin syntaxClass0080 syntaxClass0006 syntaxClass0012
  have p0105 :=
    @gOtkelins3k (synCsn (synCsn (synCsn (.cv a))))
      (synCsn (synCsn (synCsn (.cv c)))) (synCopk (synCsn (.cv b)) (.cv n))
      syntaxClass0005 p0014 p0070 p0060
  have p0106 := @gSnex (synCsn (.cv a))
  have p0107 := @gSnex (synCsn (.cv c))
  have p0108 :=
    @gOpksnelsik (synCsn (synCsn (.cv a))) (synCsn (synCsn (.cv c))) syntaxClass0004
      p0106 p0107
  have p0109 :=
    @gOpksnelsik (synCsn (.cv a)) (synCsn (.cv c)) syntaxClass0003 p0019 p0097
  have p0110 := @gOpksnelsik (.cv a) (.cv c) syntaxClass0002 p0022 p0099
  have p0111 := @gNdisjrelk (.cv a) (.cv c) p0022 p0099
  have p0112 :=
    @gNotbii (.classMem (synCopk (.cv a) (.cv c)) syntaxClass0001)
      (synWne (synCin (.cv a) (.cv c)) (synC0)) p0111
  have p0113 := @gOpkex (.cv a) (.cv c)
  have p0114 := @gElcompl (synCopk (.cv a) (.cv c)) syntaxClass0001 p0113
  have p0115 := (Nominal.biimpRefl (synWne (synCin (.cv a) (.cv c)) (synC0)))
  have p0116 :=
    @gCon2bii (synWne (synCin (.cv a) (.cv c)) (synC0))
      (.classEq (synCin (.cv a) (.cv c)) (synC0)) p0115
  have p0117 :=
    @gN3bitr4i (.neg (.classMem (synCopk (.cv a) (.cv c)) syntaxClass0001))
      (.neg (synWne (synCin (.cv a) (.cv c)) (synC0)))
      (.classMem (synCopk (.cv a) (.cv c)) syntaxClass0002)
      (.classEq (synCin (.cv a) (.cv c)) (synC0)) p0112 p0114 p0116
  have p0118 :=
    @gN3bitri syntaxFormula0085
      (.classMem (synCopk (synCsn (.cv a)) (synCsn (.cv c))) syntaxClass0003)
      (.classMem (synCopk (.cv a) (.cv c)) syntaxClass0002)
      (.classEq (synCin (.cv a) (.cv c)) (synC0)) p0109 p0110 p0117
  have p0119 :=
    @gN3bitri syntaxFormula0086
      (.classMem (synCopk (synCsn (synCsn (synCsn (.cv a))))
          (synCsn (synCsn (synCsn (.cv c))))) syntaxClass0005)
      syntaxFormula0085 (.classEq (synCin (.cv a) (.cv c)) (synC0)) p0105 p0108 p0118
  have p0120 :=
    @gOpkex (synCsn (synCsn (synCsn (synCsn (synCsn (.cv a)))))) syntaxClass0069
  have p0121 :=
    @gElimak t syntaxClass0009 syntaxClass0010 syntaxClass0080
      (by exact freshnessCertificate0121) (by exact freshnessCertificate0126)
      (by exact freshnessCertificate0553) p0120
  have p0122 := @gElpw171c x (.cv t) (by exact freshnessCertificate0271)
  have p0123 :=
    @gAnbi1i syntaxFormula0087 (synWex x syntaxFormula0089) syntaxFormula0091 p0122
  have freshnessCertificate0556 : x ∉ ((synCsn (synCsn (.cv a)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0273)
  have freshnessCertificate0557 : x ∉ ((synCsn (synCsn (synCsn (.cv a))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0556)
  have freshnessCertificate0558 :
    x ∉ ((synCsn (synCsn (synCsn (synCsn (.cv a)))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0557)
  have freshnessCertificate0559 :
    x ∉ ((synCsn (synCsn (synCsn (synCsn (synCsn (.cv a))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0558)
  have freshnessCertificate0560 : x ∉ ((Class.cv c)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show x ∉ ({ c } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show x ≠ c from (by exact fresh_x_ne_c)))))
  have freshnessCertificate0561 : x ∉ ((synCsn (.cv c))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0560)
  have freshnessCertificate0562 : x ∉ ((synCsn (synCsn (.cv c)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0561)
  have freshnessCertificate0563 : x ∉ ((synCsn (synCsn (synCsn (.cv c))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0562)
  have freshnessCertificate0564 : x ∉ ((Class.cv b)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show x ∉ ({ b } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show x ≠ b from (by exact fresh_x_ne_b)))))
  have freshnessCertificate0565 : x ∉ ((synCsn (.cv b))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0564)
  have freshnessCertificate0566 : x ∉ (((synCsn (.cv b))).fv) ∪ (((Class.cv n)).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0565 freshnessCertificate0274))
  have freshnessCertificate0567 : x ∉ ((synCopk (synCsn (.cv b)) (.cv n))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk];
      exact freshnessCertificate0566)
  have freshnessCertificate0568 :
    x ∉
      (((synCsn (synCsn (synCsn (.cv c))))).fv) ∪
        (((synCopk (synCsn (.cv b)) (.cv n))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0563 freshnessCertificate0567))
  have freshnessCertificate0569 : x ∉ (syntaxClass0069).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk];
      exact freshnessCertificate0568)
  have freshnessCertificate0570 :
    x ∉
      (((synCsn (synCsn (synCsn (synCsn (synCsn (.cv a))))))).fv) ∪
        ((syntaxClass0069).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0559 freshnessCertificate0569))
  have freshnessCertificate0571 : x ∉ (syntaxClass0080).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk];
      exact freshnessCertificate0570)
  have freshnessCertificate0572 : x ∉ (((Class.cv t)).fv) ∪ ((syntaxClass0080).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0271 freshnessCertificate0571))
  have freshnessCertificate0573 : x ∉ (syntaxClass0090).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk];
      exact freshnessCertificate0572)
  have freshnessCertificate0574 : x ∉ ((syntaxClass0090).fv) ∪ ((syntaxClass0009).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0573 freshnessCertificate0314))
  have freshnessCertificate0575 :
    x ∉ ((Wff.classMem syntaxClass0090 syntaxClass0009)).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact freshnessCertificate0574)
  have p0124 :=
    @gN1941v syntaxFormula0089 syntaxFormula0091 x (by exact freshnessCertificate0575)
  have p0125 :=
    @gBitr4i syntaxFormula0092 (synWa (synWex x syntaxFormula0089) syntaxFormula0091)
      syntaxFormula0094 p0123 p0124
  have p0126 := @gExbii syntaxFormula0092 syntaxFormula0094 t p0125
  have p0127 := (Nominal.biimpRefl syntaxFormula0095)
  have p0128 := @gExcom syntaxFormula0093 x t
  have p0129 :=
    @gN3bitr4i (synWex t syntaxFormula0092) (synWex t syntaxFormula0094)
      syntaxFormula0095 syntaxFormula0097 p0126 p0127 p0128
  have p0130 :=
    @gSnex (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x))))))))
  have p0131 := @gOpkeq1 (.cv t) syntaxClass0088 syntaxClass0080
  have p0132 :=
    @gEleq1d syntaxFormula0089 syntaxClass0090 syntaxClass0098 syntaxClass0009 p0131
  have freshnessCertificate0576 :
    t ∉ ((synCsn (synCsn (synCsn (synCsn (synCsn (.cv x))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0360)
  have freshnessCertificate0577 :
    t ∉ ((synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x)))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0576)
  have freshnessCertificate0578 :
    t ∉
      ((synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x))))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0577)
  have freshnessCertificate0579 : t ∉ (syntaxClass0088).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0578)
  have freshnessCertificate0580 : t ∉ ((syntaxClass0088).fv) ∪ ((syntaxClass0080).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0579 freshnessCertificate0553))
  have freshnessCertificate0581 : t ∉ (syntaxClass0098).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk];
      exact freshnessCertificate0580)
  have freshnessCertificate0582 : t ∉ ((syntaxClass0098).fv) ∪ ((syntaxClass0009).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0581 freshnessCertificate0121))
  have freshnessCertificate0583 :
    t ∉ ((Wff.classMem syntaxClass0098 syntaxClass0009)).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact freshnessCertificate0582)
  have p0133 :=
    @gCeqsexv syntaxFormula0091 syntaxFormula0099 t syntaxClass0088
      (by exact freshnessCertificate0579) (by exact freshnessCertificate0583) p0130 p0132
  have p0134 :=
    @gElsymdif syntaxClass0098
      (synCins2k (synCins2k (synCins3k (synCsik (synCssetk))))) syntaxClass0008
  have p0135 := @gSnex (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x))))))
  have p0136 :=
    @gOtkelins2k (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x)))))))
      (synCsn (synCsn (synCsn (synCsn (synCsn (.cv a)))))) syntaxClass0069
      (synCins2k (synCins3k (synCsik (synCssetk)))) p0135 p0085 p0074
  have p0137 :=
    @gOtkelins2k (synCsn (synCsn (synCsn (synCsn (.cv x)))))
      (synCsn (synCsn (synCsn (.cv c)))) (synCopk (synCsn (.cv b)) (.cv n))
      (synCins3k (synCsik (synCssetk))) p0035 p0070 p0060
  have p0138 := @gSnex (synCsn (.cv x))
  have p0139 :=
    @gOtkelins3k (synCsn (synCsn (.cv x))) (synCsn (.cv b)) (.cv n)
      (synCsik (synCssetk)) p0138 p0058 p0020
  have p0140 := @gSnex (.cv x)
  have p0141 := @gVex b
  have p0142 := @gOpksnelsik (synCsn (.cv x)) (.cv b) (synCssetk) p0140 p0141
  have p0143 := @gElssetk (.cv x) (.cv b) p0002 p0141
  have p0144_e02_recanon :
    Nominal.NPrf
      (synWb (.classMem (synCopk (synCsn (.cv x)) (.cv b)) (synCssetk)) (.objMem x b)) :=
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
    @gN3bitri
      (.classMem (synCopk (synCsn (synCsn (synCsn (synCsn (.cv x)))))
          (synCopk (synCsn (.cv b)) (.cv n))) (synCins3k (synCsik (synCssetk))))
      (.classMem (synCopk (synCsn (synCsn (.cv x))) (synCsn (.cv b)))
        (synCsik (synCssetk)))
      (.classMem (synCopk (synCsn (.cv x)) (.cv b)) (synCssetk)) (.objMem x b) p0139
      p0142 p0144_e02_recanon
  have p0145 :=
    @gN3bitri syntaxFormula0100
      (.classMem (synCopk (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x)))))))
          syntaxClass0069) (synCins2k (synCins3k (synCsik (synCssetk)))))
      (.classMem (synCopk (synCsn (synCsn (synCsn (synCsn (.cv x)))))
          (synCopk (synCsn (.cv b)) (.cv n))) (synCins3k (synCsik (synCssetk))))
      (.objMem x b) p0136 p0137 p0144
  have p0146 :=
    @gOtkelins3k (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x)))))))
      (synCsn (synCsn (synCsn (synCsn (synCsn (.cv a)))))) syntaxClass0069
      (synCsik (synCsik (synCsik (synCsik (synCsik (synCssetk)))))) p0135 p0085
      p0074
  have p0147 := @gSnex (synCsn (synCsn (synCsn (synCsn (.cv x)))))
  have p0148 := @gSnex (synCsn (synCsn (synCsn (.cv a))))
  have p0149 :=
    @gOpksnelsik (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x))))))
      (synCsn (synCsn (synCsn (synCsn (.cv a)))))
      (synCsik (synCsik (synCsik (synCsik (synCssetk))))) p0147 p0148
  have p0150 :=
    @gOpksnelsik (synCsn (synCsn (synCsn (synCsn (.cv x)))))
      (synCsn (synCsn (synCsn (.cv a)))) (synCsik (synCsik (synCsik (synCssetk))))
      p0035 p0014
  have p0151 := @gSnex (synCsn (synCsn (.cv x)))
  have p0152 :=
    @gOpksnelsik (synCsn (synCsn (synCsn (.cv x)))) (synCsn (synCsn (.cv a)))
      (synCsik (synCsik (synCssetk))) p0151 p0106
  have p0153 :=
    @gOpksnelsik (synCsn (synCsn (.cv x))) (synCsn (.cv a)) (synCsik (synCssetk))
      p0138 p0019
  have p0154 := @gOpksnelsik (synCsn (.cv x)) (.cv a) (synCssetk) p0140 p0022
  have p0155 := @gElssetk (.cv x) (.cv a) p0002 p0022
  have p0156_e02_recanon :
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
      p0155
  have p0156 :=
    @gN3bitri
      (.classMem (synCopk (synCsn (synCsn (synCsn (.cv x)))) (synCsn (synCsn (.cv a))))
        (synCsik (synCsik (synCssetk))))
      (.classMem (synCopk (synCsn (synCsn (.cv x))) (synCsn (.cv a)))
        (synCsik (synCssetk)))
      (.classMem (synCopk (synCsn (.cv x)) (.cv a)) (synCssetk)) (.objMem x a) p0153
      p0154 p0156_e02_recanon
  have p0157 :=
    @gN3bitri syntaxFormula0101
      (.classMem (synCopk (synCsn (synCsn (synCsn (synCsn (.cv x)))))
          (synCsn (synCsn (synCsn (.cv a))))) (synCsik (synCsik (synCsik (synCssetk)))))
      (.classMem (synCopk (synCsn (synCsn (synCsn (.cv x)))) (synCsn (synCsn (.cv a))))
        (synCsik (synCsik (synCssetk))))
      (.objMem x a) p0150 p0152 p0156
  have p0158 :=
    @gN3bitri syntaxFormula0102
      (.classMem (synCopk (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x)))))))
          (synCsn (synCsn (synCsn (synCsn (synCsn (.cv a)))))))
        (synCsik (synCsik (synCsik (synCsik (synCsik (synCssetk)))))))
      syntaxFormula0101 (.objMem x a) p0146 p0149 p0157
  have p0159 :=
    @gOtkelins2k (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x)))))))
      (synCsn (synCsn (synCsn (synCsn (synCsn (.cv a)))))) syntaxClass0069
      (synCins3k (synCsik (synCsik (synCsik (synCssetk))))) p0135 p0085 p0074
  have p0160 :=
    @gOtkelins3k (synCsn (synCsn (synCsn (synCsn (.cv x)))))
      (synCsn (synCsn (synCsn (.cv c)))) (synCopk (synCsn (.cv b)) (.cv n))
      (synCsik (synCsik (synCsik (synCssetk)))) p0035 p0070 p0060
  have p0161 :=
    @gOpksnelsik (synCsn (synCsn (synCsn (.cv x)))) (synCsn (synCsn (.cv c)))
      (synCsik (synCsik (synCssetk))) p0151 p0107
  have p0162 :=
    @gOpksnelsik (synCsn (synCsn (.cv x))) (synCsn (.cv c)) (synCsik (synCssetk))
      p0138 p0097
  have p0163 := @gOpksnelsik (synCsn (.cv x)) (.cv c) (synCssetk) p0140 p0099
  have p0164 := @gElssetk (.cv x) (.cv c) p0002 p0099
  have p0165_e01_recanon :
    Nominal.NPrf
      (synWb (.classMem (synCopk (synCsn (.cv x)) (.cv c)) (synCssetk)) (.objMem x c)) :=
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
      p0164
  have p0165 :=
    @gBitri
      (.classMem (synCopk (synCsn (synCsn (.cv x))) (synCsn (.cv c)))
        (synCsik (synCssetk)))
      (.classMem (synCopk (synCsn (.cv x)) (.cv c)) (synCssetk)) (.objMem x c) p0163
      p0165_e01_recanon
  have p0166 :=
    @gN3bitri
      (.classMem (synCopk (synCsn (synCsn (synCsn (synCsn (.cv x)))))
          (synCsn (synCsn (synCsn (.cv c))))) (synCsik (synCsik (synCsik (synCssetk)))))
      (.classMem (synCopk (synCsn (synCsn (synCsn (.cv x)))) (synCsn (synCsn (.cv c))))
        (synCsik (synCsik (synCssetk))))
      (.classMem (synCopk (synCsn (synCsn (.cv x))) (synCsn (.cv c)))
        (synCsik (synCssetk)))
      (.objMem x c) p0161 p0162 p0165
  have p0167 :=
    @gN3bitri syntaxFormula0103
      (.classMem (synCopk (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x)))))))
          syntaxClass0069) (synCins3k (synCsik (synCsik (synCsik (synCssetk))))))
      (.classMem (synCopk (synCsn (synCsn (synCsn (synCsn (.cv x)))))
          (synCsn (synCsn (synCsn (.cv c))))) (synCsik (synCsik (synCsik (synCssetk)))))
      (.objMem x c) p0159 p0160 p0166
  have p0168 :=
    @gOrbi12i syntaxFormula0102 (.objMem x a) syntaxFormula0103 (.objMem x c) p0158 p0167
  have p0169 :=
    @gElun syntaxClass0098 syntaxClass0007
      (synCins2k (synCins3k (synCsik (synCsik (synCsik (synCssetk))))))
  have p0170 := @gElun (.cv x) (.cv a) (.cv c)
  have p0171_e02_recanon :
    Nominal.NPrf
      (synWb (.classMem (.cv x) (synCun (.cv a) (.cv c)))
        (synWo (.objMem x a) (.objMem x c))) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [synWb, synCun, synCnin, synWnan, synWa, synCcompl, synWo]
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
      p0170
  have p0171 :=
    @gN3bitr4i (synWo syntaxFormula0102 syntaxFormula0103)
      (synWo (.objMem x a) (.objMem x c)) syntaxFormula0104
      (.classMem (.cv x) (synCun (.cv a) (.cv c))) p0168 p0169 p0171_e02_recanon
  have p0172 :=
    @gBibi12i syntaxFormula0100 (.objMem x b) syntaxFormula0104
      (.classMem (.cv x) (synCun (.cv a) (.cv c))) p0145 p0171
  have p0173 :=
    @gNotbii syntaxFormula0105
      (synWb (.objMem x b) (.classMem (.cv x) (synCun (.cv a) (.cv c)))) p0172
  have p0174 :=
    @gN3bitri syntaxFormula0096 syntaxFormula0099 (.neg syntaxFormula0105)
      (.neg (synWb (.objMem x b) (.classMem (.cv x) (synCun (.cv a) (.cv c))))) p0133
      p0134 p0173
  have p0175 :=
    @gExbii syntaxFormula0096
      (.neg (synWb (.objMem x b) (.classMem (.cv x) (synCun (.cv a) (.cv c))))) x p0174
  have p0176 :=
    @gN3bitri syntaxFormula0106 syntaxFormula0095 syntaxFormula0097
      (synWex x (.neg (synWb (.objMem x b) (.classMem (.cv x) (synCun (.cv a) (.cv c))))))
      p0121 p0129 p0175
  have p0177 :=
    @gNotbii syntaxFormula0106
      (synWex x (.neg (synWb (.objMem x b) (.classMem (.cv x) (synCun (.cv a) (.cv c))))))
      p0176
  have p0178 := @gElcompl syntaxClass0080 syntaxClass0011 p0120
  have freshnessCertificate0584 : x ∉ (((Class.cv a)).fv) ∪ (((Class.cv c)).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0272 freshnessCertificate0560))
  have freshnessCertificate0585 : x ∉ ((synCun (.cv a) (.cv c))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun];
      exact freshnessCertificate0584)
  have p0179 :=
    @gDfcleq x (.cv b) (synCun (.cv a) (.cv c)) (by exact freshnessCertificate0564)
      (by exact freshnessCertificate0585)
  have p0180 :=
    @gAlex (synWb (.objMem x b) (.classMem (.cv x) (synCun (.cv a) (.cv c)))) x
  have p0181_e00_recanon :
    Nominal.NPrf
      (synWb (.classEq (.cv b) (synCun (.cv a) (.cv c)))
        (.all x (synWb (.objMem x b) (.classMem (.cv x) (synCun (.cv a) (.cv c)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [synWb, synCun, synCnin, synWnan, synWa, synCcompl]
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
      p0179
  have p0181 :=
    @gBitri (.classEq (.cv b) (synCun (.cv a) (.cv c)))
      (.all x (synWb (.objMem x b) (.classMem (.cv x) (synCun (.cv a) (.cv c)))))
      (.neg (synWex x
          (.neg (synWb (.objMem x b) (.classMem (.cv x) (synCun (.cv a) (.cv c)))))))
      p0181_e00_recanon p0180
  have p0182 :=
    @gN3bitr4i (.neg syntaxFormula0106)
      (.neg (synWex x
          (.neg (synWb (.objMem x b) (.classMem (.cv x) (synCun (.cv a) (.cv c)))))))
      syntaxFormula0107 (.classEq (.cv b) (synCun (.cv a) (.cv c))) p0177 p0178 p0181
  have p0183 :=
    @gAnbi12i syntaxFormula0086 (.classEq (synCin (.cv a) (.cv c)) (synC0))
      syntaxFormula0107 (.classEq (.cv b) (synCun (.cv a) (.cv c))) p0119 p0182
  have p0184 :=
    @gBitri syntaxFormula0108 (synWa syntaxFormula0086 syntaxFormula0107)
      syntaxFormula0109 p0104 p0183
  have p0185 :=
    @gAnbi12i syntaxFormula0084 (synWa (.objMem a n) (.objMem c n)) syntaxFormula0108
      syntaxFormula0109 p0103 p0184
  have p0186 :=
    @gN3bitri syntaxFormula0078 syntaxFormula0081
      (synWa syntaxFormula0084 syntaxFormula0108)
      (synWa (synWa (.objMem a n) (.objMem c n)) syntaxFormula0109) p0088 p0089 p0185
  have p0187 :=
    @gExbii syntaxFormula0078
      (synWa (synWa (.objMem a n) (.objMem c n)) syntaxFormula0109) a p0186
  have p0188 :=
    @gN3bitri syntaxFormula0067 syntaxFormula0070 syntaxFormula0079
      (synWex a (synWa (synWa (.objMem a n) (.objMem c n)) syntaxFormula0109)) p0073
      p0084 p0187
  have p0189 :=
    @gExbii syntaxFormula0067
      (synWex a (synWa (synWa (.objMem a n) (.objMem c n)) syntaxFormula0109)) c p0188
  have p0190 :=
    @gN3bitri syntaxFormula0110 syntaxFormula0066 syntaxFormula0068
      (synWex c (synWex a (synWa (synWa (.objMem a n) (.objMem c n)) syntaxFormula0109)))
      p0061 p0069 p0189
  have p0191 :=
    @gEladdc (.cv b) (.cv n) (.cv n) a c (by exact freshnessCertificate0540)
      (by exact freshnessCertificate0469) (by exact freshnessCertificate0172)
      (by exact freshnessCertificate0471) (by exact freshnessCertificate0172)
      (by exact freshnessCertificate0471) (show a ≠ c from (by exact fresh_a_ne_c))
  have p0192 :=
    @gR2ex syntaxFormula0109 a c (.cv n) (.cv n) (by exact freshnessCertificate0471)
      (show a ≠ c from (by exact fresh_a_ne_c))
  have p0193 :=
    @gExcom (synWa (synWa (.objMem a n) (.objMem c n)) syntaxFormula0109) a c
  have p0194_e01_recanon :
    Nominal.NPrf
      (synWb (synWrex a (.cv n) (synWrex c (.cv n) syntaxFormula0109)) (synWex a
          (synWex c (synWa (synWa (.objMem a n) (.objMem c n)) syntaxFormula0109)))) :=
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
      p0192
  have p0194 :=
    @gN3bitri (.classMem (.cv b) (synCplc (.cv n) (.cv n)))
      (synWrex a (.cv n) (synWrex c (.cv n) syntaxFormula0109))
      (synWex a (synWex c (synWa (synWa (.objMem a n) (.objMem c n)) syntaxFormula0109)))
      (synWex c (synWex a (synWa (synWa (.objMem a n) (.objMem c n)) syntaxFormula0109)))
      p0191 p0194_e01_recanon p0193
  have p0195 :=
    @gBitr4i syntaxFormula0110
      (synWex c (synWex a (synWa (synWa (.objMem a n) (.objMem c n)) syntaxFormula0109)))
      (.classMem (.cv b) (synCplc (.cv n) (.cv n))) p0190 p0194
  have p0196 :=
    @gN3bitri syntaxFormula0111
      (.classMem (synCopk (synCsn (synCsn (synCsn (.cv b))))
          (synCopk (synCsn (.cv a)) (.cv n))) syntaxClass0017)
      syntaxFormula0110 (.classMem (.cv b) (synCplc (.cv n) (.cv n))) p0057 p0059 p0195
  have p0197 :=
    @gOtkelins3k (synCsn (synCsn (synCsn (.cv b))))
      (synCsn (synCsn (synCsn (synCsn (.cv x))))) (synCopk (synCsn (.cv a)) (.cv n))
      (synCcnvk (synCsik (synCsik (synCsik (synCcompl (synCssetk)))))) p0056 p0035
      p0025
  have p0198 :=
    @gOpkelcnvk (synCsn (synCsn (synCsn (.cv b))))
      (synCsn (synCsn (synCsn (synCsn (.cv x)))))
      (synCsik (synCsik (synCsik (synCcompl (synCssetk))))) p0056 p0035
  have p0199 := @gSnex (synCsn (.cv b))
  have p0200 :=
    @gOpksnelsik (synCsn (synCsn (synCsn (.cv x)))) (synCsn (synCsn (.cv b)))
      (synCsik (synCsik (synCcompl (synCssetk)))) p0151 p0199
  have p0201 :=
    @gOpksnelsik (synCsn (synCsn (.cv x))) (synCsn (.cv b))
      (synCsik (synCcompl (synCssetk))) p0138 p0058
  have p0202 :=
    @gOpksnelsik (synCsn (.cv x)) (.cv b) (synCcompl (synCssetk)) p0140 p0141
  have p0203_e00_recanon :
    Nominal.NPrf
      (synWb (.classMem (synCopk (synCsn (.cv x)) (.cv b)) (synCssetk)) (.objMem x b)) :=
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
  have p0203 :=
    @gNotbii (.classMem (synCopk (synCsn (.cv x)) (.cv b)) (synCssetk)) (.objMem x b)
      p0203_e00_recanon
  have p0204 := @gOpkex (synCsn (.cv x)) (.cv b)
  have p0205 := @gElcompl (synCopk (synCsn (.cv x)) (.cv b)) (synCssetk) p0204
  have p0206 := @gElcompl (.cv x) (.cv b) p0002
  have p0207_e02_recanon :
    Nominal.NPrf (synWb (.classMem (.cv x) (synCcompl (.cv b))) (.neg (.objMem x b))) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [synWb, synCcompl, synCnin, synWnan, synWa]
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
      p0206
  have p0207 :=
    @gN3bitr4i (.neg (.classMem (synCopk (synCsn (.cv x)) (.cv b)) (synCssetk)))
      (.neg (.objMem x b))
      (.classMem (synCopk (synCsn (.cv x)) (.cv b)) (synCcompl (synCssetk)))
      (.classMem (.cv x) (synCcompl (.cv b))) p0203 p0205 p0207_e02_recanon
  have p0208 :=
    @gBitri
      (.classMem (synCopk (synCsn (synCsn (.cv x))) (synCsn (.cv b)))
        (synCsik (synCcompl (synCssetk))))
      (.classMem (synCopk (synCsn (.cv x)) (.cv b)) (synCcompl (synCssetk)))
      (.classMem (.cv x) (synCcompl (.cv b))) p0202 p0207
  have p0209 :=
    @gN3bitri syntaxFormula0112
      (.classMem (synCopk (synCsn (synCsn (synCsn (.cv x)))) (synCsn (synCsn (.cv b))))
        (synCsik (synCsik (synCcompl (synCssetk)))))
      (.classMem (synCopk (synCsn (synCsn (.cv x))) (synCsn (.cv b)))
        (synCsik (synCcompl (synCssetk))))
      (.classMem (.cv x) (synCcompl (.cv b))) p0200 p0201 p0208
  have p0210 :=
    @gN3bitri syntaxFormula0113
      (.classMem (synCopk (synCsn (synCsn (synCsn (.cv b))))
          (synCsn (synCsn (synCsn (synCsn (.cv x))))))
        (synCcnvk (synCsik (synCsik (synCsik (synCcompl (synCssetk)))))))
      syntaxFormula0112 (.classMem (.cv x) (synCcompl (.cv b))) p0197 p0198 p0209
  have p0211 :=
    @gAnbi12i syntaxFormula0111 (.classMem (.cv b) (synCplc (.cv n) (.cv n)))
      syntaxFormula0113 (.classMem (.cv x) (synCcompl (.cv b))) p0196 p0210
  have p0212 :=
    @gBitri syntaxFormula0114 (synWa syntaxFormula0111 syntaxFormula0113)
      syntaxFormula0115 p0055 p0211
  have p0213 :=
    @gOpkex (synCsn (synCsn (synCsn (synCsn (synCsn (.cv b)))))) syntaxClass0049
  have p0214 :=
    @gElimak t syntaxClass0022 syntaxClass0010 syntaxClass0060
      (by exact freshnessCertificate0154) (by exact freshnessCertificate0126)
      (by exact freshnessCertificate0463) p0213
  have freshnessCertificate0586 : y ∉ ((Class.cv t)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show y ∉ ({ t } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show y ≠ t from (by exact fresh_y_ne_t)))))
  have p0215 := @gElpw171c y (.cv t) (by exact freshnessCertificate0586)
  have p0216 :=
    @gAnbi1i syntaxFormula0087 (synWex y syntaxFormula0117) syntaxFormula0119 p0215
  have freshnessCertificate0587 : y ∉ ((Class.cv b)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show y ∉ ({ b } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show y ≠ b from (by exact fresh_y_ne_b)))))
  have freshnessCertificate0588 : y ∉ ((synCsn (.cv b))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0587)
  have freshnessCertificate0589 : y ∉ ((synCsn (synCsn (.cv b)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0588)
  have freshnessCertificate0590 : y ∉ ((synCsn (synCsn (synCsn (.cv b))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0589)
  have freshnessCertificate0591 :
    y ∉ ((synCsn (synCsn (synCsn (synCsn (.cv b)))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0590)
  have freshnessCertificate0592 :
    y ∉ ((synCsn (synCsn (synCsn (synCsn (synCsn (.cv b))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0591)
  have freshnessCertificate0593 : y ∉ ((Class.cv x)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show y ∉ ({ x } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show y ≠ x from (by exact fresh_y_ne_x)))))
  have freshnessCertificate0594 : y ∉ ((synCsn (.cv x))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0593)
  have freshnessCertificate0595 : y ∉ ((synCsn (synCsn (.cv x)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0594)
  have freshnessCertificate0596 : y ∉ ((synCsn (synCsn (synCsn (.cv x))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0595)
  have freshnessCertificate0597 :
    y ∉ ((synCsn (synCsn (synCsn (synCsn (.cv x)))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0596)
  have freshnessCertificate0598 : y ∉ ((Class.cv a)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show y ∉ ({ a } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show y ≠ a from (by exact fresh_y_ne_a)))))
  have freshnessCertificate0599 : y ∉ ((synCsn (.cv a))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0598)
  have freshnessCertificate0600 : y ∉ ((Class.cv n)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show y ∉ ({ n } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show y ≠ n from (by exact fresh_y_ne_n)))))
  have freshnessCertificate0601 : y ∉ (((synCsn (.cv a))).fv) ∪ (((Class.cv n)).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0599 freshnessCertificate0600))
  have freshnessCertificate0602 : y ∉ ((synCopk (synCsn (.cv a)) (.cv n))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk];
      exact freshnessCertificate0601)
  have freshnessCertificate0603 :
    y ∉
      (((synCsn (synCsn (synCsn (synCsn (.cv x)))))).fv) ∪
        (((synCopk (synCsn (.cv a)) (.cv n))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0597 freshnessCertificate0602))
  have freshnessCertificate0604 : y ∉ (syntaxClass0049).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk];
      exact freshnessCertificate0603)
  have freshnessCertificate0605 :
    y ∉
      (((synCsn (synCsn (synCsn (synCsn (synCsn (.cv b))))))).fv) ∪
        ((syntaxClass0049).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0592 freshnessCertificate0604))
  have freshnessCertificate0606 : y ∉ (syntaxClass0060).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk];
      exact freshnessCertificate0605)
  have freshnessCertificate0607 : y ∉ (((Class.cv t)).fv) ∪ ((syntaxClass0060).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0586 freshnessCertificate0606))
  have freshnessCertificate0608 : y ∉ (syntaxClass0118).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk];
      exact freshnessCertificate0607)
  have freshnessCertificate0609 : y ∉ ((synCssetk)).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk];
      exact (show y ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))
  have freshnessCertificate0610 : y ∉ ((synCsik (synCssetk))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0609)
  have freshnessCertificate0611 : y ∉ ((synCins3k (synCsik (synCssetk)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0610)
  have freshnessCertificate0612 :
    y ∉ ((synCins2k (synCins3k (synCsik (synCssetk))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0611)
  have freshnessCertificate0613 :
    y ∉ ((synCins2k (synCins2k (synCins3k (synCsik (synCssetk)))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0612)
  have freshnessCertificate0614 : y ∉ ((synCsik (synCsik (synCssetk)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0610)
  have freshnessCertificate0615 :
    y ∉ ((synCsik (synCsik (synCsik (synCssetk))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0614)
  have freshnessCertificate0616 :
    y ∉ ((synCsik (synCsik (synCsik (synCsik (synCssetk)))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0615)
  have freshnessCertificate0617 :
    y ∉ ((synCsik (synCsik (synCsik (synCsik (synCsik (synCssetk))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0616)
  have freshnessCertificate0618 : y ∉ (syntaxClass0007).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0617)
  have freshnessCertificate0619 : y ∉ ((synCidk)).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cidk];
      exact (show y ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))
  have freshnessCertificate0620 : y ∉ ((synCins3k (synCidk))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0619)
  have freshnessCertificate0621 : y ∉ ((synCins2k (synCins3k (synCidk)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0620)
  have freshnessCertificate0622 :
    y ∉ ((syntaxClass0007).fv) ∪ (((synCins2k (synCins3k (synCidk)))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0618 freshnessCertificate0621))
  have freshnessCertificate0623 : y ∉ (syntaxClass0021).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun];
      exact freshnessCertificate0622)
  have freshnessCertificate0624 :
    y ∉
      (((synCins2k (synCins2k (synCins3k (synCsik (synCssetk)))))).fv) ∪
        ((syntaxClass0021).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0613 freshnessCertificate0623))
  have freshnessCertificate0625 : y ∉ (syntaxClass0022).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif];
      exact freshnessCertificate0624)
  have freshnessCertificate0626 : y ∉ ((syntaxClass0118).fv) ∪ ((syntaxClass0022).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0608 freshnessCertificate0625))
  have freshnessCertificate0627 :
    y ∉ ((Wff.classMem syntaxClass0118 syntaxClass0022)).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact freshnessCertificate0626)
  have p0217 :=
    @gN1941v syntaxFormula0117 syntaxFormula0119 y (by exact freshnessCertificate0627)
  have p0218 :=
    @gBitr4i syntaxFormula0120 (synWa (synWex y syntaxFormula0117) syntaxFormula0119)
      syntaxFormula0122 p0216 p0217
  have p0219 := @gExbii syntaxFormula0120 syntaxFormula0122 t p0218
  have p0220 := (Nominal.biimpRefl syntaxFormula0123)
  have p0221 := @gExcom syntaxFormula0121 y t
  have p0222 :=
    @gN3bitr4i (synWex t syntaxFormula0120) (synWex t syntaxFormula0122)
      syntaxFormula0123 syntaxFormula0125 p0219 p0220 p0221
  have p0223 :=
    @gSnex (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (.cv y))))))))
  have p0224 := @gOpkeq1 (.cv t) syntaxClass0116 syntaxClass0060
  have p0225 :=
    @gEleq1d syntaxFormula0117 syntaxClass0118 syntaxClass0126 syntaxClass0022 p0224
  have freshnessCertificate0628 : t ∉ ((Class.cv y)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show t ∉ ({ y } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show t ≠ y from (by exact fresh_t_ne_y)))))
  have freshnessCertificate0629 : t ∉ ((synCsn (.cv y))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0628)
  have freshnessCertificate0630 : t ∉ ((synCsn (synCsn (.cv y)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0629)
  have freshnessCertificate0631 : t ∉ ((synCsn (synCsn (synCsn (.cv y))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0630)
  have freshnessCertificate0632 :
    t ∉ ((synCsn (synCsn (synCsn (synCsn (.cv y)))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0631)
  have freshnessCertificate0633 :
    t ∉ ((synCsn (synCsn (synCsn (synCsn (synCsn (.cv y))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0632)
  have freshnessCertificate0634 :
    t ∉ ((synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (.cv y)))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0633)
  have freshnessCertificate0635 :
    t ∉
      ((synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (.cv y))))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0634)
  have freshnessCertificate0636 : t ∉ (syntaxClass0116).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0635)
  have freshnessCertificate0637 : t ∉ ((syntaxClass0116).fv) ∪ ((syntaxClass0060).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0636 freshnessCertificate0463))
  have freshnessCertificate0638 : t ∉ (syntaxClass0126).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk];
      exact freshnessCertificate0637)
  have freshnessCertificate0639 : t ∉ ((syntaxClass0126).fv) ∪ ((syntaxClass0022).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0638 freshnessCertificate0154))
  have freshnessCertificate0640 :
    t ∉ ((Wff.classMem syntaxClass0126 syntaxClass0022)).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact freshnessCertificate0639)
  have p0226 :=
    @gCeqsexv syntaxFormula0119 syntaxFormula0127 t syntaxClass0116
      (by exact freshnessCertificate0636) (by exact freshnessCertificate0640) p0223 p0225
  have p0227 :=
    @gElsymdif syntaxClass0126
      (synCins2k (synCins2k (synCins3k (synCsik (synCssetk))))) syntaxClass0021
  have p0228 := @gSnex (synCsn (synCsn (synCsn (synCsn (synCsn (.cv y))))))
  have p0229 :=
    @gOtkelins2k (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (.cv y)))))))
      (synCsn (synCsn (synCsn (synCsn (synCsn (.cv b)))))) syntaxClass0049
      (synCins2k (synCins3k (synCsik (synCssetk)))) p0228 p0050 p0039
  have p0230 := @gSnex (synCsn (synCsn (synCsn (.cv y))))
  have p0231 :=
    @gOtkelins2k (synCsn (synCsn (synCsn (synCsn (.cv y)))))
      (synCsn (synCsn (synCsn (synCsn (.cv x))))) (synCopk (synCsn (.cv a)) (.cv n))
      (synCins3k (synCsik (synCssetk))) p0230 p0035 p0025
  have p0232 := @gSnex (synCsn (.cv y))
  have p0233 :=
    @gOtkelins3k (synCsn (synCsn (.cv y))) (synCsn (.cv a)) (.cv n)
      (synCsik (synCssetk)) p0232 p0019 p0020
  have p0234 := @gSnex (.cv y)
  have p0235 := @gOpksnelsik (synCsn (.cv y)) (.cv a) (synCssetk) p0234 p0022
  have p0236 := @gVex y
  have p0237 := @gElssetk (.cv y) (.cv a) p0236 p0022
  have p0238_e02_recanon :
    Nominal.NPrf
      (synWb (.classMem (synCopk (synCsn (.cv y)) (.cv a)) (synCssetk)) (.objMem y a)) :=
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
      p0237
  have p0238 :=
    @gN3bitri
      (.classMem (synCopk (synCsn (synCsn (synCsn (synCsn (.cv y)))))
          (synCopk (synCsn (.cv a)) (.cv n))) (synCins3k (synCsik (synCssetk))))
      (.classMem (synCopk (synCsn (synCsn (.cv y))) (synCsn (.cv a)))
        (synCsik (synCssetk)))
      (.classMem (synCopk (synCsn (.cv y)) (.cv a)) (synCssetk)) (.objMem y a) p0233
      p0235 p0238_e02_recanon
  have p0239 :=
    @gN3bitri syntaxFormula0128
      (.classMem syntaxClass0129 (synCins2k (synCins3k (synCsik (synCssetk)))))
      (.classMem (synCopk (synCsn (synCsn (synCsn (synCsn (.cv y)))))
          (synCopk (synCsn (.cv a)) (.cv n))) (synCins3k (synCsik (synCssetk))))
      (.objMem y a) p0229 p0231 p0238
  have p0240 :=
    @gOtkelins3k (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (.cv y)))))))
      (synCsn (synCsn (synCsn (synCsn (synCsn (.cv b)))))) syntaxClass0049
      (synCsik (synCsik (synCsik (synCsik (synCsik (synCssetk)))))) p0228 p0050
      p0039
  have p0241 := @gSnex (synCsn (synCsn (synCsn (synCsn (.cv y)))))
  have p0242 := @gSnex (synCsn (synCsn (synCsn (.cv b))))
  have p0243 :=
    @gOpksnelsik (synCsn (synCsn (synCsn (synCsn (synCsn (.cv y))))))
      (synCsn (synCsn (synCsn (synCsn (.cv b)))))
      (synCsik (synCsik (synCsik (synCsik (synCssetk))))) p0241 p0242
  have p0244 :=
    @gOpksnelsik (synCsn (synCsn (synCsn (synCsn (.cv y)))))
      (synCsn (synCsn (synCsn (.cv b)))) (synCsik (synCsik (synCsik (synCssetk))))
      p0230 p0056
  have p0245 := @gSnex (synCsn (synCsn (.cv y)))
  have p0246 :=
    @gOpksnelsik (synCsn (synCsn (synCsn (.cv y)))) (synCsn (synCsn (.cv b)))
      (synCsik (synCsik (synCssetk))) p0245 p0199
  have p0247 :=
    @gOpksnelsik (synCsn (synCsn (.cv y))) (synCsn (.cv b)) (synCsik (synCssetk))
      p0232 p0058
  have p0248 := @gOpksnelsik (synCsn (.cv y)) (.cv b) (synCssetk) p0234 p0141
  have p0249 := @gElssetk (.cv y) (.cv b) p0236 p0141
  have p0250_e02_recanon :
    Nominal.NPrf
      (synWb (.classMem (synCopk (synCsn (.cv y)) (.cv b)) (synCssetk)) (.objMem y b)) :=
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
      p0249
  have p0250 :=
    @gN3bitri
      (.classMem (synCopk (synCsn (synCsn (synCsn (.cv y)))) (synCsn (synCsn (.cv b))))
        (synCsik (synCsik (synCssetk))))
      (.classMem (synCopk (synCsn (synCsn (.cv y))) (synCsn (.cv b)))
        (synCsik (synCssetk)))
      (.classMem (synCopk (synCsn (.cv y)) (.cv b)) (synCssetk)) (.objMem y b) p0247
      p0248 p0250_e02_recanon
  have p0251 :=
    @gN3bitri syntaxFormula0130
      (.classMem (synCopk (synCsn (synCsn (synCsn (synCsn (.cv y)))))
          (synCsn (synCsn (synCsn (.cv b))))) (synCsik (synCsik (synCsik (synCssetk)))))
      (.classMem (synCopk (synCsn (synCsn (synCsn (.cv y)))) (synCsn (synCsn (.cv b))))
        (synCsik (synCsik (synCssetk))))
      (.objMem y b) p0244 p0246 p0250
  have p0252 :=
    @gN3bitri syntaxFormula0131
      (.classMem (synCopk (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (.cv y)))))))
          (synCsn (synCsn (synCsn (synCsn (synCsn (.cv b)))))))
        (synCsik (synCsik (synCsik (synCsik (synCsik (synCssetk)))))))
      syntaxFormula0130 (.objMem y b) p0240 p0243 p0251
  have p0253 :=
    @gOtkelins2k (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (.cv y)))))))
      (synCsn (synCsn (synCsn (synCsn (synCsn (.cv b)))))) syntaxClass0049
      (synCins3k (synCidk)) p0228 p0050 p0039
  have p0254 :=
    @gOtkelins3k (synCsn (synCsn (synCsn (synCsn (.cv y)))))
      (synCsn (synCsn (synCsn (synCsn (.cv x))))) (synCopk (synCsn (.cv a)) (.cv n))
      (synCidk) p0230 p0035 p0025
  have p0255 :=
    @gSneqb (synCsn (synCsn (synCsn (.cv y)))) (synCsn (synCsn (synCsn (.cv x))))
      p0245
  have p0256 := @gSneqb (synCsn (synCsn (.cv y))) (synCsn (synCsn (.cv x))) p0232
  have p0257 := @gSneqb (synCsn (.cv y)) (synCsn (.cv x)) p0234
  have p0258 := @gSneqb (.cv y) (.cv x) p0236
  have p0259_e01_recanon :
    Nominal.NPrf (synWb (.classEq (synCsn (.cv y)) (synCsn (.cv x))) (.objEq y x)) :=
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
      p0258
  have p0259 :=
    @gBitri (.classEq (synCsn (synCsn (.cv y))) (synCsn (synCsn (.cv x))))
      (.classEq (synCsn (.cv y)) (synCsn (.cv x))) (.objEq y x) p0257 p0259_e01_recanon
  have p0260 :=
    @gN3bitri syntaxFormula0132
      (.classEq (synCsn (synCsn (synCsn (.cv y)))) (synCsn (synCsn (synCsn (.cv x)))))
      (.classEq (synCsn (synCsn (.cv y))) (synCsn (synCsn (.cv x)))) (.objEq y x)
      p0255 p0256 p0259
  have p0261 :=
    @gOpkelidkg (synCsn (synCsn (synCsn (synCsn (.cv y)))))
      (synCsn (synCsn (synCsn (synCsn (.cv x))))) (synCvv) (synCvv)
  have p0262 :=
    @gMp2an (.classMem (synCsn (synCsn (synCsn (synCsn (.cv y))))) (synCvv))
      (.classMem (synCsn (synCsn (synCsn (synCsn (.cv x))))) (synCvv))
      (synWb syntaxFormula0134 syntaxFormula0132) p0230 p0035 p0261
  have p0263 := @gElsnc (.cv y) (.cv x) p0236
  have p0264_e02_recanon :
    Nominal.NPrf (synWb (.classMem (.cv y) (synCsn (.cv x))) (.objEq y x)) :=
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
      p0263
  have p0264 :=
    @gN3bitr4i syntaxFormula0132 (.objEq y x) syntaxFormula0134
      (.classMem (.cv y) (synCsn (.cv x))) p0260 p0262 p0264_e02_recanon
  have p0265 :=
    @gN3bitri syntaxFormula0135 (.classMem syntaxClass0129 (synCins3k (synCidk)))
      syntaxFormula0134 (.classMem (.cv y) (synCsn (.cv x))) p0253 p0254 p0264
  have p0266 :=
    @gOrbi12i syntaxFormula0131 (.objMem y b) syntaxFormula0135
      (.classMem (.cv y) (synCsn (.cv x))) p0252 p0265
  have p0267 :=
    @gElun syntaxClass0126 syntaxClass0007 (synCins2k (synCins3k (synCidk)))
  have p0268 := @gElun (.cv y) (.cv b) (synCsn (.cv x))
  have p0269_e02_recanon :
    Nominal.NPrf
      (synWb (.classMem (.cv y) (synCun (.cv b) (synCsn (.cv x))))
        (synWo (.objMem y b) (.classMem (.cv y) (synCsn (.cv x))))) :=
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
      p0268
  have p0269 :=
    @gN3bitr4i (synWo syntaxFormula0131 syntaxFormula0135)
      (synWo (.objMem y b) (.classMem (.cv y) (synCsn (.cv x)))) syntaxFormula0136
      (.classMem (.cv y) (synCun (.cv b) (synCsn (.cv x)))) p0266 p0267
      p0269_e02_recanon
  have p0270 :=
    @gBibi12i syntaxFormula0128 (.objMem y a) syntaxFormula0136
      (.classMem (.cv y) (synCun (.cv b) (synCsn (.cv x)))) p0239 p0269
  have p0271 :=
    @gNotbii syntaxFormula0137
      (synWb (.objMem y a) (.classMem (.cv y) (synCun (.cv b) (synCsn (.cv x))))) p0270
  have p0272 :=
    @gN3bitri syntaxFormula0124 syntaxFormula0127 (.neg syntaxFormula0137)
      (.neg (synWb (.objMem y a) (.classMem (.cv y) (synCun (.cv b) (synCsn (.cv x))))))
      p0226 p0227 p0271
  have p0273 :=
    @gExbii syntaxFormula0124
      (.neg (synWb (.objMem y a) (.classMem (.cv y) (synCun (.cv b) (synCsn (.cv x))))))
      y p0272
  have p0274 :=
    @gN3bitri syntaxFormula0138 syntaxFormula0123 syntaxFormula0125
      (synWex y (.neg
          (synWb (.objMem y a) (.classMem (.cv y) (synCun (.cv b) (synCsn (.cv x)))))))
      p0214 p0222 p0273
  have p0275 :=
    @gNotbii syntaxFormula0138
      (synWex y (.neg
          (synWb (.objMem y a) (.classMem (.cv y) (synCun (.cv b) (synCsn (.cv x)))))))
      p0274
  have p0276 := @gElcompl syntaxClass0060 syntaxClass0023 p0213
  have freshnessCertificate0641 : y ∉ (((Class.cv b)).fv) ∪ (((synCsn (.cv x))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0587 freshnessCertificate0594))
  have freshnessCertificate0642 : y ∉ ((synCun (.cv b) (synCsn (.cv x)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun];
      exact freshnessCertificate0641)
  have p0277 :=
    @gDfcleq y (.cv a) (synCun (.cv b) (synCsn (.cv x)))
      (by exact freshnessCertificate0598) (by exact freshnessCertificate0642)
  have p0278 :=
    @gAlex (synWb (.objMem y a) (.classMem (.cv y) (synCun (.cv b) (synCsn (.cv x)))))
      y
  have p0279_e00_recanon :
    Nominal.NPrf
      (synWb (.classEq (.cv a) (synCun (.cv b) (synCsn (.cv x)))) (.all y
          (synWb (.objMem y a) (.classMem (.cv y) (synCun (.cv b) (synCsn (.cv x))))))) :=
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
      p0277
  have p0279 :=
    @gBitri (.classEq (.cv a) (synCun (.cv b) (synCsn (.cv x))))
      (.all y (synWb (.objMem y a) (.classMem (.cv y) (synCun (.cv b) (synCsn (.cv x))))))
      (.neg (synWex y (.neg (synWb (.objMem y a)
              (.classMem (.cv y) (synCun (.cv b) (synCsn (.cv x))))))))
      p0279_e00_recanon p0278
  have p0280 :=
    @gN3bitr4i (.neg syntaxFormula0138)
      (.neg (synWex y (.neg (synWb (.objMem y a)
              (.classMem (.cv y) (synCun (.cv b) (synCsn (.cv x))))))))
      syntaxFormula0139 (.classEq (.cv a) (synCun (.cv b) (synCsn (.cv x)))) p0275 p0276
      p0279
  have p0281 :=
    @gAnbi12i syntaxFormula0114 syntaxFormula0115 syntaxFormula0139
      (.classEq (.cv a) (synCun (.cv b) (synCsn (.cv x)))) p0212 p0280
  have p0282 :=
    @gN3bitri syntaxFormula0058 syntaxFormula0061
      (synWa syntaxFormula0114 syntaxFormula0139) syntaxFormula0140 p0053 p0054 p0281
  have p0283 := @gExbii syntaxFormula0058 syntaxFormula0140 b p0282
  have p0284 :=
    @gN3bitri syntaxFormula0047 syntaxFormula0050 syntaxFormula0059 syntaxFormula0141
      p0038 p0049 p0283
  have p0285 := @gExbii syntaxFormula0047 syntaxFormula0141 x p0284
  have p0286 :=
    @gN3bitri syntaxFormula0142 syntaxFormula0043 syntaxFormula0048 syntaxFormula0143
      p0026 p0034 p0285
  have p0287 :=
    @gOtkelins3k (synCsn (.cv a)) (.cv n) (.cv x) syntaxClass0027 p0019 p0020 p0002
  have freshnessCertificate0643 : b ∉ (((Class.cv n)).fv) ∪ (((Class.cv n)).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0373 freshnessCertificate0373))
  have freshnessCertificate0644 : b ∉ ((synCplc (.cv n) (.cv n))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc];
      exact freshnessCertificate0643)
  have p0288 :=
    @gElsuc x (.cv a) (synCplc (.cv n) (.cv n)) b (by exact freshnessCertificate0371)
      (by exact freshnessCertificate0272) (by exact freshnessCertificate0644)
      (show b ≠ x from (by exact fresh_b_ne_x))
  have freshnessCertificate0645 : x ∉ (((Class.cv n)).fv) ∪ (((Class.cv n)).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0274 freshnessCertificate0274))
  have freshnessCertificate0646 : x ∉ ((synCplc (.cv n) (.cv n))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc];
      exact freshnessCertificate0645)
  have p0289 :=
    @gR2ex (.classEq (.cv a) (synCun (.cv b) (synCsn (.cv x)))) b x
      (synCplc (.cv n) (.cv n)) (synCcompl (.cv b)) (by exact freshnessCertificate0646)
      (show b ≠ x from (by exact fresh_b_ne_x))
  have p0290 := @gExcom syntaxFormula0140 b x
  have p0291 :=
    @gN3bitri (.classMem (.cv a) (synCplc (synCplc (.cv n) (.cv n)) (synC1c)))
      (synWrex b (synCplc (.cv n) (.cv n)) (synWrex x (synCcompl (.cv b))
          (.classEq (.cv a) (synCun (.cv b) (synCsn (.cv x))))))
      (synWex b (synWex x syntaxFormula0140)) syntaxFormula0143 p0288 p0289 p0290
  have p0292 :=
    @gN3bitr4i syntaxFormula0142 syntaxFormula0143 syntaxFormula0144
      (.classMem (.cv a) (synCplc (synCplc (.cv n) (.cv n)) (synC1c))) p0286 p0287
      p0291
  have p0293 :=
    @gBibi12i syntaxFormula0041 (.objMem a x) syntaxFormula0144
      (.classMem (.cv a) (synCplc (synCplc (.cv n) (.cv n)) (synC1c))) p0024 p0292
  have p0294 :=
    @gNotbii syntaxFormula0145
      (synWb (.objMem a x) (.classMem (.cv a) (synCplc (synCplc (.cv n) (.cv n)) (synC1c))))
      p0293
  have p0295 :=
    @gN3bitri syntaxFormula0038 syntaxFormula0040 (.neg syntaxFormula0145)
      (.neg (synWb (.objMem a x)
          (.classMem (.cv a) (synCplc (synCplc (.cv n) (.cv n)) (synC1c)))))
      p0017 p0018 p0294
  have p0296 :=
    @gExbii syntaxFormula0038
      (.neg (synWb (.objMem a x)
          (.classMem (.cv a) (synCplc (synCplc (.cv n) (.cv n)) (synC1c)))))
      a p0295
  have p0297 :=
    @gN3bitri syntaxFormula0146 syntaxFormula0037 syntaxFormula0039
      (synWex a (.neg (synWb (.objMem a x)
            (.classMem (.cv a) (synCplc (synCplc (.cv n) (.cv n)) (synC1c))))))
      p0005 p0013 p0296
  have p0298 :=
    @gNotbii syntaxFormula0146
      (synWex a (.neg (synWb (.objMem a x)
            (.classMem (.cv a) (synCplc (synCplc (.cv n) (.cv n)) (synC1c))))))
      p0297
  have p0299 := @gElcompl (synCopk (.cv n) (.cv x)) syntaxClass0030 p0004
  have freshnessCertificate0647 : a ∉ (((Class.cv n)).fv) ∪ (((Class.cv n)).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0172 freshnessCertificate0172))
  have freshnessCertificate0648 : a ∉ ((synCplc (.cv n) (.cv n))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc];
      exact freshnessCertificate0647)
  have freshnessCertificate0649 :
    a ∉ (((synCplc (.cv n) (.cv n))).fv) ∪ (((synC1c)).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0648 freshnessCertificate0189))
  have freshnessCertificate0650 :
    a ∉ ((synCplc (synCplc (.cv n) (.cv n)) (synC1c))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc];
      exact freshnessCertificate0649)
  have p0300 :=
    @gDfcleq a (.cv x) (synCplc (synCplc (.cv n) (.cv n)) (synC1c))
      (by exact freshnessCertificate0173) (by exact freshnessCertificate0650)
  have p0301 :=
    @gAlex
      (synWb (.objMem a x) (.classMem (.cv a) (synCplc (synCplc (.cv n) (.cv n)) (synC1c))))
      a
  have p0302_e00_recanon :
    Nominal.NPrf
      (synWb (.classEq (.cv x) (synCplc (synCplc (.cv n) (.cv n)) (synC1c))) (.all a
          (synWb (.objMem a x)
            (.classMem (.cv a) (synCplc (synCplc (.cv n) (.cv n)) (synC1c)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [synWb, synCplc, synWrex, synWex, synWa, synC1c]
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
      p0300
  have p0302 :=
    @gBitri (.classEq (.cv x) (synCplc (synCplc (.cv n) (.cv n)) (synC1c)))
      (.all a (synWb (.objMem a x)
          (.classMem (.cv a) (synCplc (synCplc (.cv n) (.cv n)) (synC1c)))))
      (.neg (synWex a (.neg (synWb (.objMem a x)
              (.classMem (.cv a) (synCplc (synCplc (.cv n) (.cv n)) (synC1c)))))))
      p0302_e00_recanon p0301
  have p0303 :=
    @gN3bitr4i (.neg syntaxFormula0146)
      (.neg (synWex a (.neg (synWb (.objMem a x)
              (.classMem (.cv a) (synCplc (synCplc (.cv n) (.cv n)) (synC1c)))))))
      syntaxFormula0147 (.classEq (.cv x) (synCplc (synCplc (.cv n) (.cv n)) (synC1c)))
      p0298 p0299 p0302
  have p0304 :=
    @gRexbii syntaxFormula0147
      (.classEq (.cv x) (synCplc (synCplc (.cv n) (.cv n)) (synC1c))) n (synCnnc)
      p0303
  have p0305 :=
    @gBitri syntaxFormula0148 (synWrex n (synCnnc) syntaxFormula0147) syntaxFormula0149
      p0003 p0304
  have p0306 :=
    @gAnbi1i syntaxFormula0148 syntaxFormula0149 (synWne (.cv x) (synC0)) p0305
  have p0307 :=
    @gBitri (.classMem (.cv x) syntaxClass0150)
      (synWa syntaxFormula0148 (synWne (.cv x) (synC0))) syntaxFormula0151 p0001 p0306
  have freshnessCertificate0651 :
    x ∉ ((syntaxClass0026).fv) ∪ (((synCpw1 (synCpw1 (synCpw1 (synC1c))))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0354 freshnessCertificate0315))
  have freshnessCertificate0652 : x ∉ (syntaxClass0027).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak];
      exact freshnessCertificate0651)
  have freshnessCertificate0653 : x ∉ (syntaxClass0028).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0652)
  have freshnessCertificate0654 :
    x ∉ (((synCins2k (synCssetk))).fv) ∪ ((syntaxClass0028).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0280 freshnessCertificate0653))
  have freshnessCertificate0655 : x ∉ (syntaxClass0029).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif];
      exact freshnessCertificate0654)
  have freshnessCertificate0656 :
    x ∉ ((syntaxClass0029).fv) ∪ (((synCpw1 (synCpw1 (synC1c)))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0655 freshnessCertificate0292))
  have freshnessCertificate0657 : x ∉ (syntaxClass0030).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak];
      exact freshnessCertificate0656)
  have freshnessCertificate0658 : x ∉ (syntaxClass0031).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl];
      exact freshnessCertificate0657)
  have freshnessCertificate0659 : x ∉ ((synCnnc)).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc];
      exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))
  have freshnessCertificate0660 : x ∉ ((syntaxClass0031).fv) ∪ (((synCnnc)).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0658 freshnessCertificate0659))
  have freshnessCertificate0661 : x ∉ (syntaxClass0032).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak];
      exact freshnessCertificate0660)
  have freshnessCertificate0662 : x ∉ ((synC0)).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0];
      exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))
  have freshnessCertificate0663 : x ∉ ((synCsn (synC0))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0662)
  have freshnessCertificate0664 :
    x ∉ ((syntaxClass0032).fv) ∪ (((synCsn (synC0))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0661 freshnessCertificate0663))
  have freshnessCertificate0665 : x ∉ (syntaxClass0150).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif];
      exact freshnessCertificate0664)
  have p0308 :=
    @gEqabi syntaxFormula0151 x syntaxClass0150 (by exact freshnessCertificate0665) p0307
  have p0309 :=
    @gEqtr4i (synCoddfin) (.cab x syntaxFormula0151) syntaxClass0150 p0000 p0308
  have p0310 := @gSsetkex
  have p0311 := @gIns2kex (synCssetk) p0310
  have p0312 := @gIns2kex (synCins2k (synCssetk)) p0311
  have p0313 := @gVvex
  have p0314 := @gXpkex (synCvv) (synCins2k (synCssetk)) p0313 p0311
  have p0315 :=
    @gInex (synCins2k (synCins2k (synCssetk)))
      (synCxpk (synCvv) (synCins2k (synCssetk))) p0312 p0314
  have p0317 := @gIns3kex (synCssetk) p0310
  have p0318 := @gInex (synCins3k (synCssetk)) (synCins2k (synCssetk)) p0317 p0311
  have p0319 := @gN1cex
  have p0320 := @gPw1ex (synC1c) p0319
  have p0321 := @gPw1ex (synCpw1 (synC1c)) p0320
  have p0322 :=
    @gImakex (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
      (synCpw1 (synCpw1 (synC1c))) p0318 p0321
  have p0323 := @gComplex syntaxClass0001 p0322
  have p0324 := @gSikex syntaxClass0002 p0323
  have p0325 := @gSikex syntaxClass0003 p0324
  have p0326 := @gSikex syntaxClass0004 p0325
  have p0327 := @gIns3kex syntaxClass0005 p0326
  have p0329 := @gSikex (synCssetk) p0310
  have p0330 := @gIns3kex (synCsik (synCssetk)) p0329
  have p0331 := @gIns2kex (synCins3k (synCsik (synCssetk))) p0330
  have p0332 := @gIns2kex (synCins2k (synCins3k (synCsik (synCssetk)))) p0331
  have p0333 := @gSikex (synCsik (synCssetk)) p0329
  have p0334 := @gSikex (synCsik (synCsik (synCssetk))) p0333
  have p0335 := @gSikex (synCsik (synCsik (synCsik (synCssetk)))) p0334
  have p0336 := @gSikex (synCsik (synCsik (synCsik (synCsik (synCssetk))))) p0335
  have p0337 :=
    @gIns3kex (synCsik (synCsik (synCsik (synCsik (synCsik (synCssetk)))))) p0336
  have p0338 := @gIns3kex (synCsik (synCsik (synCsik (synCssetk)))) p0334
  have p0339 :=
    @gIns2kex (synCins3k (synCsik (synCsik (synCsik (synCssetk))))) p0338
  have p0340 :=
    @gUnex syntaxClass0007
      (synCins2k (synCins3k (synCsik (synCsik (synCsik (synCssetk)))))) p0337 p0339
  have p0341 :=
    @gSymdifex (synCins2k (synCins2k (synCins3k (synCsik (synCssetk)))))
      syntaxClass0008 p0332 p0340
  have p0342 := @gPw1ex (synCpw1 (synCpw1 (synC1c))) p0321
  have p0343 := @gPw1ex (synCpw1 (synCpw1 (synCpw1 (synC1c)))) p0342
  have p0344 := @gPw1ex (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))) p0343
  have p0345 :=
    @gPw1ex (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))) p0344
  have p0346 :=
    @gPw1ex (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
      p0345
  have p0347 := @gImakex syntaxClass0009 syntaxClass0010 p0341 p0346
  have p0348 := @gComplex syntaxClass0011 p0347
  have p0349 := @gInex syntaxClass0006 syntaxClass0012 p0327 p0348
  have p0350 := @gInex syntaxClass0000 syntaxClass0013 p0315 p0349
  have p0351 :=
    @gImakex syntaxClass0014 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))) p0350
      p0343
  have p0352 := @gImakex syntaxClass0015 (synCpw1 (synCpw1 (synC1c))) p0351 p0321
  have p0353 := @gIns2kex syntaxClass0016 p0352
  have p0354 := @gIns2kex syntaxClass0017 p0353
  have p0356 := @gComplex (synCssetk) p0310
  have p0357 := @gSikex (synCcompl (synCssetk)) p0356
  have p0358 := @gSikex (synCsik (synCcompl (synCssetk))) p0357
  have p0359 := @gSikex (synCsik (synCsik (synCcompl (synCssetk)))) p0358
  have p0360 := @gCnvkex (synCsik (synCsik (synCsik (synCcompl (synCssetk))))) p0359
  have p0361 :=
    @gIns3kex (synCcnvk (synCsik (synCsik (synCsik (synCcompl (synCssetk))))))
      p0360
  have p0362 := @gInex syntaxClass0018 syntaxClass0019 p0354 p0361
  have p0363 := @gIdkex
  have p0364 := @gIns3kex (synCidk) p0363
  have p0365 := @gIns2kex (synCins3k (synCidk)) p0364
  have p0366 := @gUnex syntaxClass0007 (synCins2k (synCins3k (synCidk))) p0337 p0365
  have p0367 :=
    @gSymdifex (synCins2k (synCins2k (synCins3k (synCsik (synCssetk)))))
      syntaxClass0021 p0332 p0366
  have p0368 := @gImakex syntaxClass0022 syntaxClass0010 p0367 p0346
  have p0369 := @gComplex syntaxClass0023 p0368
  have p0370 := @gInex syntaxClass0020 syntaxClass0024 p0362 p0369
  have p0371 :=
    @gImakex syntaxClass0025 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))) p0370
      p0343
  have p0372 :=
    @gImakex syntaxClass0026 (synCpw1 (synCpw1 (synCpw1 (synC1c)))) p0371 p0342
  have p0373 := @gIns3kex syntaxClass0027 p0372
  have p0374 := @gSymdifex (synCins2k (synCssetk)) syntaxClass0028 p0311 p0373
  have p0375 := @gImakex syntaxClass0029 (synCpw1 (synCpw1 (synC1c))) p0374 p0321
  have p0376 := @gComplex syntaxClass0030 p0375
  have p0377 := @gNncex
  have p0378 := @gImakex syntaxClass0031 (synCnnc) p0376 p0377
  have p0379 := @gSnex (synC0)
  have p0380 := @gDifex syntaxClass0032 (synCsn (synC0)) p0378 p0379
  have p0381 := @gEqeltri (synCoddfin) syntaxClass0150 (synCvv) p0309 p0380
  exact p0381


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk009StructuralPart060`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_n_0ceven`. -/
@[expose]
noncomputable def gN0ceven : Nominal.NPrf (.classMem (synC0c) (synCevenfin)) :=
  by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let n : Var := freshVar proofSupport 0
  let x : Var := freshVar proofSupport 1
  have fresh_n_ne_x : n ≠ x :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_x_ne_n : x ≠ n := Ne.symm fresh_n_ne_x
  have p0000 := @gPeano1
  have p0001 := @gAddcid2 (synC0c)
  have p0002 := @gEqcomi (synCplc (synC0c) (synC0c)) (synC0c) p0001
  have p0003 := @gAddceq12 (.cv n) (.cv n) (synC0c) (synC0c)
  have p0004 :=
    @gAnidms (.classEq (.cv n) (synC0c))
      (.classEq (synCplc (.cv n) (.cv n)) (synCplc (synC0c) (synC0c))) p0003
  have p0005 :=
    @gEqeq2d (.classEq (.cv n) (synC0c)) (synCplc (.cv n) (.cv n))
      (synCplc (synC0c) (synC0c)) (synC0c) p0004
  have freeVariableCertificate0 :
    n ∉ ((Wff.classEq (synC0c) (synCplc (synC0c) (synC0c)))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, Finset.mem_union,
      Finset.notMem_empty, or_false, not_false_eq_true]
  have p0006 :=
    @gRspcev (.classEq (synC0c) (synCplc (.cv n) (.cv n)))
      (.classEq (synC0c) (synCplc (synC0c) (synC0c))) n (synC0c) (synCnnc)
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
      freeVariableCertificate0 p0005
  have p0007 :=
    @gMp2an (.classMem (synC0c) (synCnnc))
      (.classEq (synC0c) (synCplc (synC0c) (synC0c)))
      (synWrex n (synCnnc) (.classEq (synC0c) (synCplc (.cv n) (.cv n)))) p0000 p0002
      p0006
  have p0008 := @gN0ex
  have p0009 := @gSnid (synC0) p0008
  have p0010 := (Nominal.classEqRefl (synC0c))
  have p0011 := @gEleqtrri (synC0) (synCsn (synC0)) (synC0c) p0009 p0010
  have p0012 := @gNe0i (synC0c) (synC0)
  have p0013 := Nominal.mp p0011 p0012
  have p0014 := @gN0cex
  have p0015 := @gEqeq1 (.cv x) (synC0c) (synCplc (.cv n) (.cv n))
  have freeVariableCertificate1 : n ∉ ((Wff.classEq (.cv x) (synC0c))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_n_ne_x, or_false,
      not_false_eq_true]
  have p0016 :=
    @gRexbidv (.classEq (.cv x) (synC0c)) (.classEq (.cv x) (synCplc (.cv n) (.cv n)))
      (.classEq (synC0c) (synCplc (.cv n) (.cv n))) n (synCnnc)
      freeVariableCertificate1 p0015
  have p0017 := @gNeeq1 (.cv x) (synC0c) (synC0)
  have p0018 :=
    @gAnbi12d (.classEq (.cv x) (synC0c))
      (synWrex n (synCnnc) (.classEq (.cv x) (synCplc (.cv n) (.cv n))))
      (synWrex n (synCnnc) (.classEq (synC0c) (synCplc (.cv n) (.cv n))))
      (synWne (.cv x) (synC0)) (synWne (synC0c) (synC0)) p0016 p0017
  have p0019 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfEvenfin x n
      (show n ≠ x from (by exact fresh_n_ne_x))
  have freeVariableCertificate2 :
    x ∉
      ((synWa (synWrex n (synCnnc) (.classEq (synC0c) (synCplc (.cv n) (.cv n))))
          (synWne (synC0c) (synC0)))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union,
      Finset.mem_erase, Finset.mem_singleton, Finset.notMem_empty, fresh_x_ne_n, or_false,
      and_false, not_false_eq_true]
  have p0020 :=
    @gElab2
      (synWa (synWrex n (synCnnc) (.classEq (.cv x) (synCplc (.cv n) (.cv n))))
        (synWne (.cv x) (synC0)))
      (synWa (synWrex n (synCnnc) (.classEq (synC0c) (synCplc (.cv n) (.cv n))))
        (synWne (synC0c) (synC0)))
      x (synC0c) (synCevenfin)
      (by
        exact
          (show x ∉ ((synC0c)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c];
              exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
      freeVariableCertificate2 p0014 p0018 p0019
  have p0021 :=
    @gMpbir2an (.classMem (synC0c) (synCevenfin))
      (synWrex n (synCnnc) (.classEq (synC0c) (synCplc (.cv n) (.cv n))))
      (synWne (synC0c) (synC0)) p0007 p0013 p0020
  exact p0021

/-- Checked nominal proof certificate identified upstream as `g_evennn`. -/
@[expose]
noncomputable def gEvennn (A : Class) :
    Nominal.NPrf (.imp (.classMem A (synCevenfin)) (.classMem A (synCnnc))) :=
  by
  let proofSupport : Finset Var := A.fv
  let n : Var := freshVar proofSupport 0
  let x : Var := freshVar proofSupport 1
  have fresh_n : n ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_n_not_A : n ∉ A.fv := by
    intro h
    exact fresh_n (h)
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (h)
  have fresh_n_ne_x : n ≠ x :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_x_ne_n : x ≠ n := Ne.symm fresh_n_ne_x
  have p0000 := @gEqeq1 (.cv x) A (synCplc (.cv n) (.cv n))
  have freeVariableCertificate0 : n ∉ ((Wff.classEq (.cv x) A)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      fresh_n_ne_x, fresh_n_not_A, or_false, not_false_eq_true]
  have p0001 :=
    @gRexbidv (.classEq (.cv x) A) (.classEq (.cv x) (synCplc (.cv n) (.cv n)))
      (.classEq A (synCplc (.cv n) (.cv n))) n (synCnnc) freeVariableCertificate0 p0000
  have p0002 := @gNeeq1 (.cv x) A (synC0)
  have p0003 :=
    @gAnbi12d (.classEq (.cv x) A)
      (synWrex n (synCnnc) (.classEq (.cv x) (synCplc (.cv n) (.cv n))))
      (synWrex n (synCnnc) (.classEq A (synCplc (.cv n) (.cv n))))
      (synWne (.cv x) (synC0)) (synWne A (synC0)) p0001 p0002
  have p0004 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfEvenfin x n
      (show n ≠ x from (by exact fresh_n_ne_x))
  have freeVariableCertificate1 :
    x ∉
      ((synWa (synWrex n (synCnnc) (.classEq A (synCplc (.cv n) (.cv n))))
          (synWne A (synC0)))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union,
      Finset.mem_erase, Finset.mem_singleton, Finset.notMem_empty, fresh_x_not_A,
      fresh_x_ne_n, or_false, and_false, not_false_eq_true]
  have p0005 :=
    @gElab2g
      (synWa (synWrex n (synCnnc) (.classEq (.cv x) (synCplc (.cv n) (.cv n))))
        (synWne (.cv x) (synC0)))
      (synWa (synWrex n (synCnnc) (.classEq A (synCplc (.cv n) (.cv n))))
        (synWne A (synC0)))
      x A (synCevenfin) (synCevenfin)
      (by exact (show x ∉ (A).fv from (by exact fresh_x_not_A))) freeVariableCertificate1
      p0003 p0004
  have p0006 :=
    @gIbi (.classMem A (synCevenfin))
      (synWa (synWrex n (synCnnc) (.classEq A (synCplc (.cv n) (.cv n))))
        (synWne A (synC0)))
      p0005
  have p0007 := @gNncaddccl (.cv n) (.cv n)
  have p0008 :=
    @gAnidms (.classMem (.cv n) (synCnnc))
      (.classMem (synCplc (.cv n) (.cv n)) (synCnnc)) p0007
  have p0009 := @gEleq1a (synCplc (.cv n) (.cv n)) (synCnnc) A
  have p0010 :=
    @gSyl (.classMem (.cv n) (synCnnc))
      (.classMem (synCplc (.cv n) (.cv n)) (synCnnc))
      (.imp (.classEq A (synCplc (.cv n) (.cv n))) (.classMem A (synCnnc))) p0008 p0009
  have freeVariableCertificate2 : n ∉ ((Wff.classMem A (synCnnc))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union,
      Finset.notMem_empty, fresh_n_not_A, or_false, not_false_eq_true]
  have p0011 :=
    @gRexlimiv (.classEq A (synCplc (.cv n) (.cv n))) (.classMem A (synCnnc)) n
      (synCnnc) freeVariableCertificate2 p0010
  have p0012 :=
    @gAdantr (synWrex n (synCnnc) (.classEq A (synCplc (.cv n) (.cv n))))
      (.classMem A (synCnnc)) (synWne A (synC0)) p0011
  have p0013 :=
    @gSyl (.classMem A (synCevenfin))
      (synWa (synWrex n (synCnnc) (.classEq A (synCplc (.cv n) (.cv n))))
        (synWne A (synC0)))
      (.classMem A (synCnnc)) p0006 p0012
  exact p0013


end NFChoice.DirectNominalPrf.WPPReplay

end
