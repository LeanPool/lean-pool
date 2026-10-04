/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NominalWPPReplayChunk009StructuralBlock011

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NominalWPPReplayChunk009StructuralPart053`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_eqtfinrelk`. -/
@[expose]
noncomputable def gEqtfinrelk (M : Class) (X : Class)
    (hyp_eqtfinrelk_1 : Nominal.NPrf (.classMem M (synCvv)))
    (hyp_eqtfinrelk_2 : Nominal.NPrf (.classMem X (synCvv))) :
    Nominal.NPrf
      (synWb (.classMem (synCopk (synCsn M) X)
          (synCun (synCxpk (synCsn (synCsn (synC0))) (synCsn (synC0))) (synCdif
              (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk)) (synCins3k
                      (synCimak (synCdif (synCins3k (synCcnvk (synCssetk))) (synCins2k
                            (synCimak (synCsymdif (synCins2k
                                  (synCin (synCxpk (synCnnc) (synCvv)) (synCimak
                                      (synCin (synCins2k (synCsik (synCssetk))) (synCins3k
        (synCimak (synCin (synCins3k (synCsik (synCdif (synCxpk (synCpw (synC1c))
        (synCvv)) (synCimak (synCsymdif (synCins3k (synCssetk)) (synCins2k
        (synCsik (synCssetk)))) (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
        (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                                      (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                                (synCins3k (synCidk))) (synCpw1 (synC1c)))))
                        (synCpw1 (synC1c))))) (synCpw1 (synCpw1 (synC1c)))))
              (synCxpk (synCsn (synCsn (synC0))) (synCvv)))))
        (.classEq X (synCtfin M))) :=
  by
  let proofSupport : Finset Var := M.fv ∪ X.fv
  let y : Var := freshVar proofSupport 0
  let a : Var := freshVar proofSupport 1
  let z : Var := freshVar proofSupport 2
  let t : Var := freshVar proofSupport 3
  let n : Var := freshVar proofSupport 4
  let x : Var := freshVar proofSupport 5
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_not_M : y ∉ M.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (h))
  have fresh_a : a ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_a_not_M : a ∉ M.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (h))
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_z_not_M : z ∉ M.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (h))
  have fresh_z_not_X : z ∉ X.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have fresh_t : t ∉ proofSupport :=
    by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_t_not_M : t ∉ M.fv := by
    intro h
    exact fresh_t (Finset.mem_union_left _ (h))
  have fresh_t_not_X : t ∉ X.fv := by
    intro h
    exact fresh_t (Finset.mem_union_right _ (h))
  have fresh_n : n ∉ proofSupport :=
    by
    change freshVar proofSupport 4 ∉ proofSupport
    exact freshVar_not_mem proofSupport 4
  have fresh_n_not_M : n ∉ M.fv := by
    intro h
    exact fresh_n (Finset.mem_union_left _ (h))
  have fresh_y_ne_a : y ≠ a :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_a_ne_y : a ≠ y := Ne.symm fresh_y_ne_a
  have fresh_y_ne_z : y ≠ z :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_z_ne_y : z ≠ y := Ne.symm fresh_y_ne_z
  have fresh_y_ne_t : y ≠ t :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_t_ne_y : t ≠ y := Ne.symm fresh_y_ne_t
  have fresh_y_ne_n : y ≠ n :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 0) (j := 4) (by decide)
  have fresh_n_ne_y : n ≠ y := Ne.symm fresh_y_ne_n
  have fresh_y_ne_x : y ≠ x :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 0) (j := 5) (by decide)
  have fresh_x_ne_y : x ≠ y := Ne.symm fresh_y_ne_x
  have fresh_a_ne_z : a ≠ z :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_z_ne_a : z ≠ a := Ne.symm fresh_a_ne_z
  have fresh_a_ne_t : a ≠ t :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_t_ne_a : t ≠ a := Ne.symm fresh_a_ne_t
  have fresh_a_ne_n : a ≠ n :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 1) (j := 4) (by decide)
  have fresh_n_ne_a : n ≠ a := Ne.symm fresh_a_ne_n
  have fresh_a_ne_x : a ≠ x :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 1) (j := 5) (by decide)
  have fresh_x_ne_a : x ≠ a := Ne.symm fresh_a_ne_x
  have fresh_z_ne_t : z ≠ t :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_t_ne_z : t ≠ z := Ne.symm fresh_z_ne_t
  have fresh_z_ne_n : z ≠ n :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 2) (j := 4) (by decide)
  have fresh_n_ne_z : n ≠ z := Ne.symm fresh_z_ne_n
  have fresh_t_ne_n : t ≠ n :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 3) (j := 4) (by decide)
  have fresh_n_ne_t : n ≠ t := Ne.symm fresh_t_ne_n
  have fresh_t_ne_x : t ≠ x :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 3) (j := 5) (by decide)
  have fresh_x_ne_t : x ≠ t := Ne.symm fresh_t_ne_x
  let syntaxFormula0000 : Wff :=
    (.classMem (synCopk (synCsn (synC0)) X)
      (synCxpk (synCsn (synCsn (synC0))) (synCsn (synC0))))
  let syntaxClass0001 : Class :=
    (synCimak (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk))))
      (synCpw1 (synCpw1 (synCpw1 (synC1c)))))
  let syntaxClass0002 : Class :=
    (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) syntaxClass0001)
  let syntaxClass0003 : Class := (synCsik syntaxClass0002)
  let syntaxClass0004 : Class := (synCins3k syntaxClass0003)
  let syntaxClass0005 : Class := (synCin syntaxClass0004 (synCins2k (synCssetk)))
  let syntaxClass0006 : Class :=
    (synCimak syntaxClass0005 (synCpw1 (synCpw1 (synC1c))))
  let syntaxClass0007 : Class := (synCins3k syntaxClass0006)
  let syntaxClass0008 : Class :=
    (synCin (synCins2k (synCsik (synCssetk))) syntaxClass0007)
  let syntaxClass0009 : Class :=
    (synCimak syntaxClass0008 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))
  let syntaxClass0010 : Class := (synCin (synCxpk (synCnnc) (synCvv)) syntaxClass0009)
  let syntaxClass0011 : Class := (synCins2k syntaxClass0010)
  let syntaxClass0012 : Class := (synCsymdif syntaxClass0011 (synCins3k (synCidk)))
  let syntaxClass0013 : Class := (synCimak syntaxClass0012 (synCpw1 (synC1c)))
  let syntaxClass0014 : Class := (synCins2k syntaxClass0013)
  let syntaxClass0015 : Class :=
    (synCdif (synCins3k (synCcnvk (synCssetk))) syntaxClass0014)
  let syntaxClass0016 : Class := (synCimak syntaxClass0015 (synCpw1 (synC1c)))
  let syntaxClass0017 : Class := (synCins3k syntaxClass0016)
  let syntaxClass0018 : Class := (synCsymdif (synCins2k (synCssetk)) syntaxClass0017)
  let syntaxClass0019 : Class :=
    (synCimak syntaxClass0018 (synCpw1 (synCpw1 (synC1c))))
  let syntaxClass0020 : Class := (synCcompl syntaxClass0019)
  let syntaxClass0021 : Class :=
    (synCdif syntaxClass0020 (synCxpk (synCsn (synCsn (synC0))) (synCvv)))
  let syntaxFormula0022 : Wff :=
    (.classMem (synCopk (synCsn (synC0)) X) syntaxClass0021)
  let syntaxFormula0023 : Wff :=
    (.classMem (synCopk (synCsn (synC0)) X)
      (synCxpk (synCsn (synCsn (synC0))) (synCvv)))
  let syntaxFormula0024 : Wff :=
    (.classMem (synCopk (synCsn (synC0)) X) syntaxClass0020)
  let syntaxClass0025 : Class :=
    (synCun (synCxpk (synCsn (synCsn (synC0))) (synCsn (synC0))) syntaxClass0021)
  let syntaxFormula0026 : Wff :=
    (.classMem (synCopk (synCsn (synC0)) X) syntaxClass0025)
  let syntaxFormula0027 : Wff :=
    (synWa (.classMem (.cv y) (synCnnc))
      (synWrex a M (.classMem (synCpw1 (.cv a)) (.cv y))))
  let syntaxClass0028 : Class := (synCio y syntaxFormula0027)
  let syntaxClass0029 : Class := (synCif (.classEq M (synC0)) (synC0) syntaxClass0028)
  let syntaxFormula0030 : Wff := (.classMem (synCopk (synCsn M) X) syntaxClass0025)
  let syntaxFormula0031 : Wff := (.classEq X syntaxClass0029)
  let syntaxFormula0032 : Wff :=
    (.classMem (synCopk (.cv t) (synCopk (synCsn M) X)) syntaxClass0018)
  let syntaxFormula0033 : Wff :=
    (synWa (.classMem (.cv t) (synCpw1 (synCpw1 (synC1c)))) syntaxFormula0032)
  let syntaxFormula0034 : Wff :=
    (synWa (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv z))))) syntaxFormula0032)
  let syntaxFormula0035 : Wff := (synWex z syntaxFormula0034)
  let syntaxFormula0036 : Wff :=
    (synWrex t (synCpw1 (synCpw1 (synC1c))) syntaxFormula0032)
  let syntaxFormula0037 : Wff := (synWex t syntaxFormula0034)
  let syntaxFormula0038 : Wff := (synWex z syntaxFormula0037)
  let syntaxFormula0039 : Wff :=
    (.classMem (synCopk (synCsn (synCsn (synCsn (.cv z)))) (synCopk (synCsn M) X))
      syntaxClass0018)
  let syntaxFormula0040 : Wff :=
    (.classMem (synCopk (synCsn (synCsn (synCsn (.cv z)))) (synCopk (synCsn M) X))
      (synCins2k (synCssetk)))
  let syntaxFormula0041 : Wff :=
    (.classMem (synCopk (.cv t) (synCopk (synCsn (.cv z)) (synCsn M))) syntaxClass0015)
  let syntaxFormula0042 : Wff :=
    (.classMem (synCopk (synCsn (synCsn (.cv n))) (synCopk (synCsn (.cv z)) (synCsn M)))
      syntaxClass0015)
  let syntaxFormula0043 : Wff :=
    (.classMem (synCopk (synCsn (synCsn (.cv n))) (synCopk (synCsn (.cv z)) (synCsn M)))
      (synCins3k (synCcnvk (synCssetk))))
  let syntaxFormula0044 : Wff :=
    (.classMem (synCopk (.cv t) (synCopk (.cv n) (synCsn M))) syntaxClass0012)
  let syntaxFormula0045 : Wff :=
    (synWa (.classMem (.cv t) (synCpw1 (synC1c))) syntaxFormula0044)
  let syntaxFormula0046 : Wff :=
    (synWa (.classEq (.cv t) (synCsn (synCsn (.cv y)))) syntaxFormula0044)
  let syntaxFormula0047 : Wff := (synWex y syntaxFormula0046)
  let syntaxFormula0048 : Wff := (synWrex t (synCpw1 (synC1c)) syntaxFormula0044)
  let syntaxFormula0049 : Wff := (synWex t syntaxFormula0046)
  let syntaxFormula0050 : Wff := (synWex y syntaxFormula0049)
  let syntaxFormula0051 : Wff :=
    (.classMem (synCopk (synCsn (synCsn (.cv y))) (synCopk (.cv n) (synCsn M)))
      syntaxClass0012)
  let syntaxClass0052 : Class :=
    (synCopk (synCsn (synCsn (synCsn (synCsn (.cv a))))) (synCopk (.cv y) (synCsn M)))
  let syntaxFormula0053 : Wff :=
    (.classMem (synCopk (.cv t) (synCopk (.cv y) (synCsn M))) syntaxClass0008)
  let syntaxFormula0054 : Wff := (.classMem syntaxClass0052 syntaxClass0008)
  let syntaxFormula0055 : Wff :=
    (.classMem syntaxClass0052 (synCins2k (synCsik (synCssetk))))
  let syntaxFormula0056 : Wff :=
    (.classMem (synCopk (.cv t) (synCopk (synCsn (synCsn (.cv a))) (.cv y)))
      syntaxClass0005)
  let syntaxFormula0057 : Wff :=
    (synWa (.classMem (.cv t) (synCpw1 (synCpw1 (synC1c)))) syntaxFormula0056)
  let syntaxFormula0058 : Wff :=
    (synWa (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv x))))) syntaxFormula0056)
  let syntaxFormula0059 : Wff := (synWex x syntaxFormula0058)
  let syntaxFormula0060 : Wff :=
    (synWrex t (synCpw1 (synCpw1 (synC1c))) syntaxFormula0056)
  let syntaxFormula0061 : Wff := (synWex t syntaxFormula0058)
  let syntaxFormula0062 : Wff := (synWex x syntaxFormula0061)
  let syntaxClass0063 : Class :=
    (synCopk (synCsn (synCsn (synCsn (.cv x))))
      (synCopk (synCsn (synCsn (.cv a))) (.cv y)))
  let syntaxFormula0064 : Wff := (.classMem syntaxClass0063 syntaxClass0005)
  let syntaxFormula0065 : Wff := (.classMem syntaxClass0063 syntaxClass0004)
  let syntaxFormula0066 : Wff := (.classMem syntaxClass0063 (synCins2k (synCssetk)))
  let syntaxFormula0067 : Wff :=
    (.classMem (synCopk (synCsn (synCsn (.cv a))) (.cv y)) syntaxClass0006)
  let syntaxFormula0068 : Wff := (.classMem syntaxClass0052 syntaxClass0007)
  let syntaxFormula0069 : Wff :=
    (synWa (.classEq (.cv t) (synCsn (synCsn (synCsn (synCsn (.cv a))))))
      syntaxFormula0053)
  let syntaxFormula0070 : Wff := (synWex t syntaxFormula0069)
  let syntaxFormula0071 : Wff :=
    (synWrex t (synCpw1 (synCpw1 (synCpw1 (synC1c)))) syntaxFormula0053)
  let syntaxFormula0072 : Wff :=
    (synWa (.classMem (.cv t) (synCpw1 (synCpw1 (synCpw1 (synC1c))))) syntaxFormula0053)
  let syntaxFormula0073 : Wff := (synWex a syntaxFormula0069)
  let syntaxFormula0074 : Wff := (synWex t syntaxFormula0073)
  let syntaxFormula0075 : Wff :=
    (.classMem (synCopk (.cv y) (synCsn M)) syntaxClass0009)
  let syntaxFormula0076 : Wff := (synWex a syntaxFormula0070)
  let syntaxFormula0077 : Wff :=
    (.classMem (synCopk (synCsn (synCsn (.cv y))) (synCopk (.cv n) (synCsn M)))
      syntaxClass0011)
  let syntaxFormula0078 : Wff :=
    (.classMem (synCopk (synCsn (synCsn (.cv y))) (synCopk (.cv n) (synCsn M)))
      (synCins3k (synCidk)))
  let syntaxFormula0079 : Wff :=
    (.classMem (synCopk (.cv n) (synCsn M)) syntaxClass0013)
  let syntaxFormula0080 : Wff :=
    (.classMem (synCopk (synCsn (synCsn (.cv n))) (synCopk (synCsn (.cv z)) (synCsn M)))
      syntaxClass0014)
  let syntaxFormula0081 : Wff := (.neg syntaxFormula0080)
  let syntaxFormula0082 : Wff :=
    (synWa (.classEq (.cv t) (synCsn (synCsn (.cv n)))) syntaxFormula0041)
  let syntaxFormula0083 : Wff := (synWex t syntaxFormula0082)
  let syntaxFormula0084 : Wff :=
    (synWa (.classMem (.cv t) (synCpw1 (synC1c))) syntaxFormula0041)
  let syntaxFormula0085 : Wff := (synWex n syntaxFormula0082)
  let syntaxFormula0086 : Wff := (synWrex t (synCpw1 (synC1c)) syntaxFormula0041)
  let syntaxFormula0087 : Wff := (synWex n syntaxFormula0083)
  let syntaxFormula0088 : Wff :=
    (.classMem (synCopk (synCsn (synCsn (synCsn (.cv z)))) (synCopk (synCsn M) X))
      syntaxClass0017)
  let syntaxFormula0089 : Wff := (.classMem (.cv z) syntaxClass0028)
  let syntaxFormula0090 : Wff := (synWb (.classMem (.cv z) X) syntaxFormula0089)
  let syntaxFormula0091 : Wff := (.neg syntaxFormula0090)
  let syntaxFormula0092 : Wff := (.classMem (synCopk (synCsn M) X) syntaxClass0019)
  let syntaxFormula0093 : Wff := (synWex z syntaxFormula0091)
  let syntaxFormula0094 : Wff := (.classEq X syntaxClass0028)
  let syntaxFormula0095 : Wff := (.neg syntaxFormula0093)
  let syntaxFormula0096 : Wff := (.classMem (synCopk (synCsn M) X) syntaxClass0020)
  let syntaxFormula0097 : Wff :=
    (.classMem (synCopk (synCsn M) X) (synCxpk (synCsn (synCsn (synC0))) (synCvv)))
  let syntaxFormula0098 : Wff := (.neg syntaxFormula0097)
  let syntaxFormula0099 : Wff := (synWa syntaxFormula0096 syntaxFormula0098)
  let syntaxFormula0100 : Wff :=
    (synWo (synWa (.classEq M (synC0)) (.classEq X (synC0))) syntaxFormula0099)
  let syntaxFormula0101 : Wff :=
    (.classMem (synCopk (synCsn M) X)
      (synCxpk (synCsn (synCsn (synC0))) (synCsn (synC0))))
  let syntaxFormula0102 : Wff := (.classMem (synCopk (synCsn M) X) syntaxClass0021)
  let syntaxFormula0103 : Wff := (synWo syntaxFormula0101 syntaxFormula0102)
  have p0000 := @gSnex (synC0)
  have p0001 := @gSnid (synCsn (synC0)) p0000
  have p0002 :=
    @gOpkelxpk (synCsn (synC0)) X (synCsn (synCsn (synC0))) (synCsn (synC0)) p0000
      hyp_eqtfinrelk_2
  have p0003 :=
    @gMpbiran syntaxFormula0000
      (.classMem (synCsn (synC0)) (synCsn (synCsn (synC0))))
      (.classMem X (synCsn (synC0))) p0001 p0002
  have p0004 := @gElsnc X (synC0) hyp_eqtfinrelk_2
  have p0005 :=
    @gBitri syntaxFormula0000 (.classMem X (synCsn (synC0))) (.classEq X (synC0))
      p0003 p0004
  have p0006 := @gOrbi1i syntaxFormula0000 (.classEq X (synC0)) syntaxFormula0022 p0005
  have p0007 :=
    @gElun (synCopk (synCsn (synC0)) X)
      (synCxpk (synCsn (synCsn (synC0))) (synCsn (synC0))) syntaxClass0021
  have p0008 :=
    @gOpkelxpk (synCsn (synC0)) X (synCsn (synCsn (synC0))) (synCvv) p0000
      hyp_eqtfinrelk_2
  have p0009 :=
    @gMpbir2an syntaxFormula0023
      (.classMem (synCsn (synC0)) (synCsn (synCsn (synC0)))) (.classMem X (synCvv))
      p0001 hyp_eqtfinrelk_2 p0008
  have p0010 := @gNotnoti syntaxFormula0023 p0009
  have p0011 := @gIntnan (.neg syntaxFormula0023) syntaxFormula0024 p0010
  have p0012 :=
    @gEldif (synCopk (synCsn (synC0)) X) syntaxClass0020
      (synCxpk (synCsn (synCsn (synC0))) (synCvv))
  have p0013 :=
    @gMtbir syntaxFormula0022 (synWa syntaxFormula0024 (.neg syntaxFormula0023)) p0011
      p0012
  have p0014 := @gBiorfi syntaxFormula0022 (.classEq X (synC0)) p0013
  have p0015 :=
    @gN3bitr4i (synWo syntaxFormula0000 syntaxFormula0022)
      (synWo (.classEq X (synC0)) syntaxFormula0022) syntaxFormula0026
      (.classEq X (synC0)) p0006 p0007 p0014
  have p0016 :=
    @gA1i (synWb syntaxFormula0026 (.classEq X (synC0))) (.classEq M (synC0)) p0015
  have p0017 := @gSneq M (synC0)
  have p0018 := @gOpkeq1d (.classEq M (synC0)) (synCsn M) (synCsn (synC0)) X p0017
  have p0019 :=
    @gEleq1d (.classEq M (synC0)) (synCopk (synCsn M) X)
      (synCopk (synCsn (synC0)) X) syntaxClass0025 p0018
  have p0020 := @gIftrue (.classEq M (synC0)) (synC0) syntaxClass0028
  have p0021 := @gEqeq2d (.classEq M (synC0)) syntaxClass0029 (synC0) X p0020
  have p0022 :=
    @gN3bitr4d (.classEq M (synC0)) syntaxFormula0026 (.classEq X (synC0))
      syntaxFormula0030 syntaxFormula0031 p0016 p0019 p0021
  have p0023 := @gIffalse (.classEq M (synC0)) (synC0) syntaxClass0028
  have p0024 :=
    @gEqeq2d (.neg (.classEq M (synC0))) syntaxClass0029 syntaxClass0028 X p0023
  have p0025 := @gOpkex (synCsn M) X
  have freeVariableCertificate0 : t ∉ (syntaxClass0018).fv := by
    simp only [syntaxClass0001, syntaxClass0002, syntaxClass0003, syntaxClass0004,
      syntaxClass0005, syntaxClass0006, syntaxClass0007, syntaxClass0008, syntaxClass0009,
      syntaxClass0010, syntaxClass0011, syntaxClass0012, syntaxClass0013, syntaxClass0014,
      syntaxClass0015, syntaxClass0016, syntaxClass0017, syntaxClass0018,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cidk, Finset.mem_union,
      Finset.notMem_empty, or_false, not_false_eq_true]
  have freeVariableCertificate1 : t ∉ ((synCpw1 (synCpw1 (synC1c)))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.notMem_empty,
      not_false_eq_true]
  have freeVariableCertificate2 : t ∉ ((synCopk (synCsn M) X)).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
      fresh_t_not_M, fresh_t_not_X, or_false, not_false_eq_true]
  have p0026 :=
    @gElimak t syntaxClass0018 (synCpw1 (synCpw1 (synC1c))) (synCopk (synCsn M) X)
      freeVariableCertificate0 freeVariableCertificate1 freeVariableCertificate2 p0025
  have freeVariableCertificate3 : z ∉ ((Class.cv t)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_z_ne_t, not_false_eq_true]
  have p0027 := @gElpw121c z (.cv t) freeVariableCertificate3
  have p0028 :=
    @gAnbi1i (.classMem (.cv t) (synCpw1 (synCpw1 (synC1c))))
      (synWex z (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv z))))))
      syntaxFormula0032 p0027
  have freeVariableCertificate4 :
    z ∉ ((Wff.classMem (synCopk (.cv t) (synCopk (synCsn M) X)) syntaxClass0018)).fv :=
    by
    simp only [syntaxClass0001, syntaxClass0002, syntaxClass0003, syntaxClass0004,
      syntaxClass0005, syntaxClass0006, syntaxClass0007, syntaxClass0008, syntaxClass0009,
      syntaxClass0010, syntaxClass0011, syntaxClass0012, syntaxClass0013, syntaxClass0014,
      syntaxClass0015, syntaxClass0016, syntaxClass0017, syntaxClass0018,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cidk, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_z_ne_t, fresh_z_not_M,
      fresh_z_not_X, or_false, not_false_eq_true]
  have p0029 :=
    @gN1941v (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv z))))) syntaxFormula0032
      z freeVariableCertificate4
  have p0030 :=
    @gBitr4i syntaxFormula0033
      (synWa (synWex z (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv z))))))
        syntaxFormula0032)
      syntaxFormula0035 p0028 p0029
  have p0031 := @gExbii syntaxFormula0033 syntaxFormula0035 t p0030
  have p0032 := (Nominal.biimpRefl syntaxFormula0036)
  have p0033 := @gExcom syntaxFormula0034 z t
  have p0034 :=
    @gN3bitr4i (synWex t syntaxFormula0033) (synWex t syntaxFormula0035)
      syntaxFormula0036 syntaxFormula0038 p0031 p0032 p0033
  have p0035 := @gSnex (synCsn (synCsn (.cv z)))
  have p0036 :=
    @gOpkeq1 (.cv t) (synCsn (synCsn (synCsn (.cv z)))) (synCopk (synCsn M) X)
  have p0037 :=
    @gEleq1d (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv z)))))
      (synCopk (.cv t) (synCopk (synCsn M) X))
      (synCopk (synCsn (synCsn (synCsn (.cv z)))) (synCopk (synCsn M) X))
      syntaxClass0018 p0036
  have freeVariableCertificate5 : t ∉ ((synCsn (synCsn (synCsn (.cv z))))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_t_ne_z,
      not_false_eq_true]
  have freeVariableCertificate6 :
    t ∉
      ((Wff.classMem (synCopk (synCsn (synCsn (synCsn (.cv z)))) (synCopk (synCsn M) X))
          syntaxClass0018)).fv :=
    by
    simp only [syntaxClass0001, syntaxClass0002, syntaxClass0003, syntaxClass0004,
      syntaxClass0005, syntaxClass0006, syntaxClass0007, syntaxClass0008, syntaxClass0009,
      syntaxClass0010, syntaxClass0011, syntaxClass0012, syntaxClass0013, syntaxClass0014,
      syntaxClass0015, syntaxClass0016, syntaxClass0017, syntaxClass0018,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cidk, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_t_ne_z, fresh_t_not_M,
      fresh_t_not_X, or_false, not_false_eq_true]
  have p0038 :=
    @gCeqsexv syntaxFormula0032 syntaxFormula0039 t (synCsn (synCsn (synCsn (.cv z))))
      freeVariableCertificate5 freeVariableCertificate6 p0035 p0037
  have p0039 :=
    @gElsymdif (synCopk (synCsn (synCsn (synCsn (.cv z)))) (synCopk (synCsn M) X))
      (synCins2k (synCssetk)) syntaxClass0017
  have p0040 := @gSnex (.cv z)
  have p0041 := @gSnex M
  have p0042 :=
    @gOtkelins2k (synCsn (.cv z)) (synCsn M) X (synCssetk) p0040 p0041
      hyp_eqtfinrelk_2
  have p0043 := @gVex z
  have p0044 := @gElssetk (.cv z) X p0043 hyp_eqtfinrelk_2
  have p0045 :=
    @gBitri syntaxFormula0040 (.classMem (synCopk (synCsn (.cv z)) X) (synCssetk))
      (.classMem (.cv z) X) p0042 p0044
  have p0046 := @gSnex (synCsn (.cv n))
  have p0047 :=
    @gOpkeq1 (.cv t) (synCsn (synCsn (.cv n))) (synCopk (synCsn (.cv z)) (synCsn M))
  have p0048 :=
    @gEleq1d (.classEq (.cv t) (synCsn (synCsn (.cv n))))
      (synCopk (.cv t) (synCopk (synCsn (.cv z)) (synCsn M)))
      (synCopk (synCsn (synCsn (.cv n))) (synCopk (synCsn (.cv z)) (synCsn M)))
      syntaxClass0015 p0047
  have freeVariableCertificate7 : t ∉ ((synCsn (synCsn (.cv n)))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_t_ne_n,
      not_false_eq_true]
  have freeVariableCertificate8 :
    t ∉
      ((Wff.classMem
          (synCopk (synCsn (synCsn (.cv n))) (synCopk (synCsn (.cv z)) (synCsn M)))
          syntaxClass0015)).fv :=
    by
    simp only [syntaxClass0001, syntaxClass0002, syntaxClass0003, syntaxClass0004,
      syntaxClass0005, syntaxClass0006, syntaxClass0007, syntaxClass0008, syntaxClass0009,
      syntaxClass0010, syntaxClass0011, syntaxClass0012, syntaxClass0013, syntaxClass0014,
      syntaxClass0015, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cidk, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_t_ne_n, fresh_t_ne_z,
      fresh_t_not_M, or_false, not_false_eq_true]
  have p0049 :=
    @gCeqsexv syntaxFormula0041 syntaxFormula0042 t (synCsn (synCsn (.cv n)))
      freeVariableCertificate7 freeVariableCertificate8 p0046 p0048
  have p0050 :=
    @gEldif
      (synCopk (synCsn (synCsn (.cv n))) (synCopk (synCsn (.cv z)) (synCsn M)))
      (synCins3k (synCcnvk (synCssetk))) syntaxClass0014
  have p0051 := @gVex n
  have p0052 :=
    @gOtkelins3k (.cv n) (synCsn (.cv z)) (synCsn M) (synCcnvk (synCssetk)) p0051
      p0040 p0041
  have p0053 := @gOpkelcnvk (.cv n) (synCsn (.cv z)) (synCssetk) p0051 p0040
  have p0054 := @gElssetk (.cv z) (.cv n) p0043 p0051
  have p0055_e02_recanon :
    Nominal.NPrf
      (synWb (.classMem (synCopk (synCsn (.cv z)) (.cv n)) (synCssetk)) (.objMem z n)) :=
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
      p0054
  have p0055 :=
    @gN3bitri syntaxFormula0043
      (.classMem (synCopk (.cv n) (synCsn (.cv z))) (synCcnvk (synCssetk)))
      (.classMem (synCopk (synCsn (.cv z)) (.cv n)) (synCssetk)) (.objMem z n) p0052
      p0053 p0055_e02_recanon
  have p0056 :=
    @gOtkelins2k (.cv n) (synCsn (.cv z)) (synCsn M) syntaxClass0013 p0051 p0040 p0041
  have p0057 := @gOpkex (.cv n) (synCsn M)
  have freeVariableCertificate9 : t ∉ (syntaxClass0012).fv := by
    simp only [syntaxClass0001, syntaxClass0002, syntaxClass0003, syntaxClass0004,
      syntaxClass0005, syntaxClass0006, syntaxClass0007, syntaxClass0008, syntaxClass0009,
      syntaxClass0010, syntaxClass0011, syntaxClass0012,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cidk, Finset.mem_union,
      Finset.notMem_empty, or_false, not_false_eq_true]
  have freeVariableCertificate10 : t ∉ ((synCpw1 (synC1c))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.notMem_empty,
      not_false_eq_true]
  have freeVariableCertificate11 : t ∉ ((synCopk (.cv n) (synCsn M))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
      Finset.mem_singleton, fresh_t_ne_n, fresh_t_not_M, or_false, not_false_eq_true]
  have p0058 :=
    @gElimak t syntaxClass0012 (synCpw1 (synC1c)) (synCopk (.cv n) (synCsn M))
      freeVariableCertificate9 freeVariableCertificate10 freeVariableCertificate11 p0057
  have freeVariableCertificate12 : y ∉ ((Class.cv t)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_y_ne_t, not_false_eq_true]
  have p0059 := @gElpw11c y (.cv t) freeVariableCertificate12
  have p0060 :=
    @gAnbi1i (.classMem (.cv t) (synCpw1 (synC1c)))
      (synWex y (.classEq (.cv t) (synCsn (synCsn (.cv y))))) syntaxFormula0044 p0059
  have freeVariableCertificate13 :
    y ∉
      ((Wff.classMem (synCopk (.cv t) (synCopk (.cv n) (synCsn M))) syntaxClass0012)).fv :=
    by
    simp only [syntaxClass0001, syntaxClass0002, syntaxClass0003, syntaxClass0004,
      syntaxClass0005, syntaxClass0006, syntaxClass0007, syntaxClass0008, syntaxClass0009,
      syntaxClass0010, syntaxClass0011, syntaxClass0012,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cidk, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_y_ne_t, fresh_y_ne_n,
      fresh_y_not_M, or_false, not_false_eq_true]
  have p0061 :=
    @gN1941v (.classEq (.cv t) (synCsn (synCsn (.cv y)))) syntaxFormula0044 y
      freeVariableCertificate13
  have p0062 :=
    @gBitr4i syntaxFormula0045
      (synWa (synWex y (.classEq (.cv t) (synCsn (synCsn (.cv y))))) syntaxFormula0044)
      syntaxFormula0047 p0060 p0061
  have p0063 := @gExbii syntaxFormula0045 syntaxFormula0047 t p0062
  have p0064 := (Nominal.biimpRefl syntaxFormula0048)
  have p0065 := @gExcom syntaxFormula0046 y t
  have p0066 :=
    @gN3bitr4i (synWex t syntaxFormula0045) (synWex t syntaxFormula0047)
      syntaxFormula0048 syntaxFormula0050 p0063 p0064 p0065
  have p0067 := @gSnex (synCsn (.cv y))
  have p0068 :=
    @gOpkeq1 (.cv t) (synCsn (synCsn (.cv y))) (synCopk (.cv n) (synCsn M))
  have p0069 :=
    @gEleq1d (.classEq (.cv t) (synCsn (synCsn (.cv y))))
      (synCopk (.cv t) (synCopk (.cv n) (synCsn M)))
      (synCopk (synCsn (synCsn (.cv y))) (synCopk (.cv n) (synCsn M)))
      syntaxClass0012 p0068
  have freeVariableCertificate14 : t ∉ ((synCsn (synCsn (.cv y)))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_t_ne_y,
      not_false_eq_true]
  have freeVariableCertificate15 :
    t ∉
      ((Wff.classMem (synCopk (synCsn (synCsn (.cv y))) (synCopk (.cv n) (synCsn M)))
          syntaxClass0012)).fv :=
    by
    simp only [syntaxClass0001, syntaxClass0002, syntaxClass0003, syntaxClass0004,
      syntaxClass0005, syntaxClass0006, syntaxClass0007, syntaxClass0008, syntaxClass0009,
      syntaxClass0010, syntaxClass0011, syntaxClass0012,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cidk, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_t_ne_y, fresh_t_ne_n,
      fresh_t_not_M, or_false, not_false_eq_true]
  have p0070 :=
    @gCeqsexv syntaxFormula0044 syntaxFormula0051 t (synCsn (synCsn (.cv y)))
      freeVariableCertificate14 freeVariableCertificate15 p0067 p0069
  have p0071 :=
    @gElsymdif (synCopk (synCsn (synCsn (.cv y))) (synCopk (.cv n) (synCsn M)))
      syntaxClass0011 (synCins3k (synCidk))
  have p0072 := @gVex y
  have p0073 :=
    @gOtkelins2k (.cv y) (.cv n) (synCsn M) syntaxClass0010 p0072 p0051 p0041
  have p0074 :=
    @gElin (synCopk (.cv y) (synCsn M)) (synCxpk (synCnnc) (synCvv)) syntaxClass0009
  have p0075 := @gOpkelxpk (.cv y) (synCsn M) (synCnnc) (synCvv) p0072 p0041
  have p0076 :=
    @gMpbiran2 (.classMem (synCopk (.cv y) (synCsn M)) (synCxpk (synCnnc) (synCvv)))
      (.classMem (.cv y) (synCnnc)) (.classMem (synCsn M) (synCvv)) p0041 p0075
  have p0077 := @gSnex (synCsn (synCsn (synCsn (.cv a))))
  have p0078 :=
    @gOpkeq1 (.cv t) (synCsn (synCsn (synCsn (synCsn (.cv a)))))
      (synCopk (.cv y) (synCsn M))
  have p0079 :=
    @gEleq1d (.classEq (.cv t) (synCsn (synCsn (synCsn (synCsn (.cv a))))))
      (synCopk (.cv t) (synCopk (.cv y) (synCsn M))) syntaxClass0052 syntaxClass0008
      p0078
  have freeVariableCertificate16 :
    t ∉ ((synCsn (synCsn (synCsn (synCsn (.cv a)))))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_t_ne_a,
      not_false_eq_true]
  have freeVariableCertificate17 :
    t ∉ ((Wff.classMem syntaxClass0052 syntaxClass0008)).fv := by
    simp only [syntaxClass0001, syntaxClass0002, syntaxClass0003, syntaxClass0004,
      syntaxClass0005, syntaxClass0006, syntaxClass0007, syntaxClass0008, syntaxClass0052,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_t_ne_a, fresh_t_ne_y,
      fresh_t_not_M, or_false, not_false_eq_true]
  have p0080 :=
    @gCeqsexv syntaxFormula0053 syntaxFormula0054 t
      (synCsn (synCsn (synCsn (synCsn (.cv a))))) freeVariableCertificate16
      freeVariableCertificate17 p0077 p0079
  have p0081 :=
    @gElin syntaxClass0052 (synCins2k (synCsik (synCssetk))) syntaxClass0007
  have p0082 := @gSnex (synCsn (.cv a))
  have p0083 :=
    @gOtkelins2k (synCsn (synCsn (.cv a))) (.cv y) (synCsn M) (synCsik (synCssetk))
      p0082 p0072 p0041
  have p0084 := @gSnex (.cv a)
  have p0085 := @gOpksnelsik (synCsn (.cv a)) M (synCssetk) p0084 hyp_eqtfinrelk_1
  have p0086 := @gVex a
  have p0087 := @gElssetk (.cv a) M p0086 hyp_eqtfinrelk_1
  have p0088 :=
    @gN3bitri syntaxFormula0055
      (.classMem (synCopk (synCsn (synCsn (.cv a))) (synCsn M)) (synCsik (synCssetk)))
      (.classMem (synCopk (synCsn (.cv a)) M) (synCssetk)) (.classMem (.cv a) M) p0083
      p0085 p0087
  have p0089 := @gOpkex (synCsn (synCsn (.cv a))) (.cv y)
  have freeVariableCertificate18 : t ∉ (syntaxClass0005).fv := by
    simp only [syntaxClass0001, syntaxClass0002, syntaxClass0003, syntaxClass0004,
      syntaxClass0005, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
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
  have freeVariableCertificate19 :
    t ∉ ((synCopk (synCsn (synCsn (.cv a))) (.cv y))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      fresh_t_ne_a, fresh_t_ne_y, or_false, not_false_eq_true]
  have p0090 :=
    @gElimak t syntaxClass0005 (synCpw1 (synCpw1 (synC1c)))
      (synCopk (synCsn (synCsn (.cv a))) (.cv y)) freeVariableCertificate18
      freeVariableCertificate1 freeVariableCertificate19 p0089
  have freeVariableCertificate20 : x ∉ ((Class.cv t)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_x_ne_t, not_false_eq_true]
  have p0091 := @gElpw121c x (.cv t) freeVariableCertificate20
  have p0092 :=
    @gAnbi1i (.classMem (.cv t) (synCpw1 (synCpw1 (synC1c))))
      (synWex x (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv x))))))
      syntaxFormula0056 p0091
  have freeVariableCertificate21 :
    x ∉
      ((Wff.classMem (synCopk (.cv t) (synCopk (synCsn (synCsn (.cv a))) (.cv y)))
          syntaxClass0005)).fv :=
    by
    simp only [syntaxClass0001, syntaxClass0002, syntaxClass0003, syntaxClass0004,
      syntaxClass0005, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
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
      Finset.mem_singleton, Finset.notMem_empty, fresh_x_ne_t, fresh_x_ne_a, fresh_x_ne_y,
      or_false, not_false_eq_true]
  have p0093 :=
    @gN1941v (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv x))))) syntaxFormula0056
      x freeVariableCertificate21
  have p0094 :=
    @gBitr4i syntaxFormula0057
      (synWa (synWex x (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv x))))))
        syntaxFormula0056)
      syntaxFormula0059 p0092 p0093
  have p0095 := @gExbii syntaxFormula0057 syntaxFormula0059 t p0094
  have p0096 := (Nominal.biimpRefl syntaxFormula0060)
  have p0097 := @gExcom syntaxFormula0058 x t
  have p0098 :=
    @gN3bitr4i (synWex t syntaxFormula0057) (synWex t syntaxFormula0059)
      syntaxFormula0060 syntaxFormula0062 p0095 p0096 p0097
  have p0099 := @gSnex (synCsn (synCsn (.cv x)))
  have p0100 :=
    @gOpkeq1 (.cv t) (synCsn (synCsn (synCsn (.cv x))))
      (synCopk (synCsn (synCsn (.cv a))) (.cv y))
  have p0101 :=
    @gEleq1d (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv x)))))
      (synCopk (.cv t) (synCopk (synCsn (synCsn (.cv a))) (.cv y))) syntaxClass0063
      syntaxClass0005 p0100
  have freeVariableCertificate22 : t ∉ ((synCsn (synCsn (synCsn (.cv x))))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_t_ne_x,
      not_false_eq_true]
  have freeVariableCertificate23 :
    t ∉ ((Wff.classMem syntaxClass0063 syntaxClass0005)).fv := by
    simp only [syntaxClass0001, syntaxClass0002, syntaxClass0003, syntaxClass0004,
      syntaxClass0005, syntaxClass0063, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
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
      Finset.mem_singleton, Finset.notMem_empty, fresh_t_ne_x, fresh_t_ne_a, fresh_t_ne_y,
      or_false, not_false_eq_true]
  have p0102 :=
    @gCeqsexv syntaxFormula0056 syntaxFormula0064 t (synCsn (synCsn (synCsn (.cv x))))
      freeVariableCertificate22 freeVariableCertificate23 p0099 p0101
  have p0103 := @gElin syntaxClass0063 syntaxClass0004 (synCins2k (synCssetk))
  have p0104 := @gSnex (.cv x)
  have p0105 :=
    @gOtkelins3k (synCsn (.cv x)) (synCsn (synCsn (.cv a))) (.cv y) syntaxClass0003
      p0104 p0082 p0072
  have p0106 := @gVex x
  have p0107 := @gOpksnelsik (.cv x) (synCsn (.cv a)) syntaxClass0002 p0106 p0084
  have p0108 := @gEqpw1relk (.cv x) (.cv a) p0106 p0086
  have p0109 :=
    @gN3bitri syntaxFormula0065
      (.classMem (synCopk (synCsn (.cv x)) (synCsn (synCsn (.cv a)))) syntaxClass0003)
      (.classMem (synCopk (.cv x) (synCsn (.cv a))) syntaxClass0002)
      (.classEq (.cv x) (synCpw1 (.cv a))) p0105 p0107 p0108
  have p0110 :=
    @gOtkelins2k (synCsn (.cv x)) (synCsn (synCsn (.cv a))) (.cv y) (synCssetk) p0104
      p0082 p0072
  have p0111 := @gElssetk (.cv x) (.cv y) p0106 p0072
  have p0112_e01_recanon :
    Nominal.NPrf
      (synWb (.classMem (synCopk (synCsn (.cv x)) (.cv y)) (synCssetk)) (.objMem x y)) :=
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
      p0111
  have p0112 :=
    @gBitri syntaxFormula0066
      (.classMem (synCopk (synCsn (.cv x)) (.cv y)) (synCssetk)) (.objMem x y) p0110
      p0112_e01_recanon
  have p0113 :=
    @gAnbi12i syntaxFormula0065 (.classEq (.cv x) (synCpw1 (.cv a))) syntaxFormula0066
      (.objMem x y) p0109 p0112
  have p0114 :=
    @gN3bitri syntaxFormula0061 syntaxFormula0064
      (synWa syntaxFormula0065 syntaxFormula0066)
      (synWa (.classEq (.cv x) (synCpw1 (.cv a))) (.objMem x y)) p0102 p0103 p0113
  have p0115 :=
    @gExbii syntaxFormula0061
      (synWa (.classEq (.cv x) (synCpw1 (.cv a))) (.objMem x y)) x p0114
  have p0116 :=
    @gN3bitri syntaxFormula0067 syntaxFormula0060 syntaxFormula0062
      (synWex x (synWa (.classEq (.cv x) (synCpw1 (.cv a))) (.objMem x y))) p0090 p0098
      p0115
  have p0117 :=
    @gOtkelins3k (synCsn (synCsn (.cv a))) (.cv y) (synCsn M) syntaxClass0006 p0082
      p0072 p0041
  have freeVariableCertificate24 : x ∉ ((synCpw1 (.cv a))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_x_ne_a,
      not_false_eq_true]
  have freeVariableCertificate25 : x ∉ ((Class.cv y)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_x_ne_y, not_false_eq_true]
  have p0118 :=
    (NFChoice.DirectNominalPrf.Nominal.DefinitionLeafHandlersCanonical001.dfClelOfDV x
      (synCpw1 (.cv a)) (.cv y) freeVariableCertificate24 freeVariableCertificate25)
  have p0119_e02_recanon :
    Nominal.NPrf
      (synWb (.classMem (synCpw1 (.cv a)) (.cv y))
        (synWex x (synWa (.classEq (.cv x) (synCpw1 (.cv a))) (.objMem x y)))) :=
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
      p0118
  have p0119 :=
    @gN3bitr4i syntaxFormula0067
      (synWex x (synWa (.classEq (.cv x) (synCpw1 (.cv a))) (.objMem x y)))
      syntaxFormula0068 (.classMem (synCpw1 (.cv a)) (.cv y)) p0116 p0117
      p0119_e02_recanon
  have p0120 :=
    @gAnbi12i syntaxFormula0055 (.classMem (.cv a) M) syntaxFormula0068
      (.classMem (synCpw1 (.cv a)) (.cv y)) p0088 p0119
  have p0121 :=
    @gN3bitri syntaxFormula0070 syntaxFormula0054
      (synWa syntaxFormula0055 syntaxFormula0068)
      (synWa (.classMem (.cv a) M) (.classMem (synCpw1 (.cv a)) (.cv y))) p0080 p0081
      p0120
  have p0122 :=
    @gExbii syntaxFormula0070
      (synWa (.classMem (.cv a) M) (.classMem (synCpw1 (.cv a)) (.cv y))) a p0121
  have p0123 := (Nominal.biimpRefl syntaxFormula0071)
  have freeVariableCertificate26 : a ∉ ((Class.cv t)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_a_ne_t, not_false_eq_true]
  have p0124 := @gElpw131c a (.cv t) freeVariableCertificate26
  have p0125 :=
    @gAnbi1i (.classMem (.cv t) (synCpw1 (synCpw1 (synCpw1 (synC1c)))))
      (synWex a (.classEq (.cv t) (synCsn (synCsn (synCsn (synCsn (.cv a)))))))
      syntaxFormula0053 p0124
  have freeVariableCertificate27 :
    a ∉
      ((Wff.classMem (synCopk (.cv t) (synCopk (.cv y) (synCsn M))) syntaxClass0008)).fv :=
    by
    simp only [syntaxClass0001, syntaxClass0002, syntaxClass0003, syntaxClass0004,
      syntaxClass0005, syntaxClass0006, syntaxClass0007, syntaxClass0008,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_a_ne_t, fresh_a_ne_y,
      fresh_a_not_M, or_false, not_false_eq_true]
  have p0126 :=
    @gN1941v (.classEq (.cv t) (synCsn (synCsn (synCsn (synCsn (.cv a))))))
      syntaxFormula0053 a freeVariableCertificate27
  have p0127 :=
    @gBitr4i syntaxFormula0072
      (synWa (synWex a (.classEq (.cv t) (synCsn (synCsn (synCsn (synCsn (.cv a)))))))
        syntaxFormula0053)
      syntaxFormula0073 p0125 p0126
  have p0128 := @gExbii syntaxFormula0072 syntaxFormula0073 t p0127
  have p0129 :=
    @gBitri syntaxFormula0071 (synWex t syntaxFormula0072) syntaxFormula0074 p0123 p0128
  have p0130 := @gOpkex (.cv y) (synCsn M)
  have freeVariableCertificate28 : t ∉ (syntaxClass0008).fv := by
    simp only [syntaxClass0001, syntaxClass0002, syntaxClass0003, syntaxClass0004,
      syntaxClass0005, syntaxClass0006, syntaxClass0007, syntaxClass0008,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union,
      Finset.notMem_empty, or_false, not_false_eq_true]
  have freeVariableCertificate29 : t ∉ ((synCpw1 (synCpw1 (synCpw1 (synC1c))))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.notMem_empty,
      not_false_eq_true]
  have freeVariableCertificate30 : t ∉ ((synCopk (.cv y) (synCsn M))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
      Finset.mem_singleton, fresh_t_ne_y, fresh_t_not_M, or_false, not_false_eq_true]
  have p0131 :=
    @gElimak t syntaxClass0008 (synCpw1 (synCpw1 (synCpw1 (synC1c))))
      (synCopk (.cv y) (synCsn M)) freeVariableCertificate28 freeVariableCertificate29
      freeVariableCertificate30 p0130
  have p0132 := @gExcom syntaxFormula0069 a t
  have p0133 :=
    @gN3bitr4i syntaxFormula0071 syntaxFormula0074 syntaxFormula0075 syntaxFormula0076
      p0129 p0131 p0132
  have p0134 := (Nominal.biimpRefl (synWrex a M (.classMem (synCpw1 (.cv a)) (.cv y))))
  have p0135 :=
    @gN3bitr4i syntaxFormula0076
      (synWex a (synWa (.classMem (.cv a) M) (.classMem (synCpw1 (.cv a)) (.cv y))))
      syntaxFormula0075 (synWrex a M (.classMem (synCpw1 (.cv a)) (.cv y))) p0122 p0133
      p0134
  have p0136 :=
    @gAnbi12i (.classMem (synCopk (.cv y) (synCsn M)) (synCxpk (synCnnc) (synCvv)))
      (.classMem (.cv y) (synCnnc)) syntaxFormula0075
      (synWrex a M (.classMem (synCpw1 (.cv a)) (.cv y))) p0076 p0135
  have p0137 :=
    @gN3bitri syntaxFormula0077
      (.classMem (synCopk (.cv y) (synCsn M)) syntaxClass0010)
      (synWa (.classMem (synCopk (.cv y) (synCsn M)) (synCxpk (synCnnc) (synCvv)))
        syntaxFormula0075)
      syntaxFormula0027 p0073 p0074 p0136
  have p0138 := @gOtkelins3k (.cv y) (.cv n) (synCsn M) (synCidk) p0072 p0051 p0041
  have p0139 := @gOpkelidkg (.cv y) (.cv n) (synCvv) (synCvv)
  have p0140_e02_recanon :
    Nominal.NPrf
      (.imp (synWa (.classMem (.cv y) (synCvv)) (.classMem (.cv n) (synCvv)))
        (synWb (.classMem (synCopk (.cv y) (.cv n)) (synCidk)) (.objEq y n))) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [synWa, synCvv, synWb, synCopk, synCpr, synCun, synCnin,
          synWnan, synCcompl, synCsn, synCidk, synWex]
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
      p0139
  have p0140 :=
    @gMp2an (.classMem (.cv y) (synCvv)) (.classMem (.cv n) (synCvv))
      (synWb (.classMem (synCopk (.cv y) (.cv n)) (synCidk)) (.objEq y n)) p0072 p0051
      p0140_e02_recanon
  have p0141 :=
    @gBitri syntaxFormula0078 (.classMem (synCopk (.cv y) (.cv n)) (synCidk))
      (.objEq y n) p0138 p0140
  have p0142 :=
    @gBibi12i syntaxFormula0077 syntaxFormula0027 syntaxFormula0078 (.objEq y n) p0137
      p0141
  have p0143 :=
    @gXchbinx syntaxFormula0051 (synWb syntaxFormula0077 syntaxFormula0078)
      (synWb syntaxFormula0027 (.objEq y n)) p0071 p0142
  have p0144 :=
    @gBitri syntaxFormula0049 syntaxFormula0051
      (.neg (synWb syntaxFormula0027 (.objEq y n))) p0070 p0143
  have p0145 :=
    @gExbii syntaxFormula0049 (.neg (synWb syntaxFormula0027 (.objEq y n))) y p0144
  have p0146 :=
    @gN3bitri syntaxFormula0079 syntaxFormula0048 syntaxFormula0050
      (synWex y (.neg (synWb syntaxFormula0027 (.objEq y n)))) p0058 p0066 p0145
  have p0147 := @gExnal (synWb syntaxFormula0027 (.objEq y n)) y
  have p0148 :=
    @gN3bitrri syntaxFormula0080 syntaxFormula0079
      (synWex y (.neg (synWb syntaxFormula0027 (.objEq y n))))
      (.neg (.all y (synWb syntaxFormula0027 (.objEq y n)))) p0056 p0146 p0147
  have p0149 :=
    @gCon1bii (.all y (synWb syntaxFormula0027 (.objEq y n))) syntaxFormula0080 p0148
  have p0150 :=
    @gAnbi12i syntaxFormula0043 (.objMem z n) syntaxFormula0081
      (.all y (synWb syntaxFormula0027 (.objEq y n))) p0055 p0149
  have p0151 :=
    @gN3bitri syntaxFormula0083 syntaxFormula0042
      (synWa syntaxFormula0043 syntaxFormula0081)
      (synWa (.objMem z n) (.all y (synWb syntaxFormula0027 (.objEq y n)))) p0049 p0050
      p0150
  have p0152 :=
    @gExbii syntaxFormula0083
      (synWa (.objMem z n) (.all y (synWb syntaxFormula0027 (.objEq y n)))) n p0151
  have p0153 :=
    @gOtkelins3k (synCsn (.cv z)) (synCsn M) X syntaxClass0016 p0040 p0041
      hyp_eqtfinrelk_2
  have p0154 := @gOpkex (synCsn (.cv z)) (synCsn M)
  have freeVariableCertificate31 : t ∉ (syntaxClass0015).fv := by
    simp only [syntaxClass0001, syntaxClass0002, syntaxClass0003, syntaxClass0004,
      syntaxClass0005, syntaxClass0006, syntaxClass0007, syntaxClass0008, syntaxClass0009,
      syntaxClass0010, syntaxClass0011, syntaxClass0012, syntaxClass0013, syntaxClass0014,
      syntaxClass0015, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cidk, Finset.mem_union,
      Finset.notMem_empty, or_false, not_false_eq_true]
  have freeVariableCertificate32 : t ∉ ((synCopk (synCsn (.cv z)) (synCsn M))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      fresh_t_ne_z, fresh_t_not_M, or_false, not_false_eq_true]
  have p0155 :=
    @gElimak t syntaxClass0015 (synCpw1 (synC1c))
      (synCopk (synCsn (.cv z)) (synCsn M)) freeVariableCertificate31
      freeVariableCertificate10 freeVariableCertificate32 p0154
  have freeVariableCertificate33 : n ∉ ((Class.cv t)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_n_ne_t, not_false_eq_true]
  have p0156 := @gElpw11c n (.cv t) freeVariableCertificate33
  have p0157 :=
    @gAnbi1i (.classMem (.cv t) (synCpw1 (synC1c)))
      (synWex n (.classEq (.cv t) (synCsn (synCsn (.cv n))))) syntaxFormula0041 p0156
  have freeVariableCertificate34 :
    n ∉
      ((Wff.classMem (synCopk (.cv t) (synCopk (synCsn (.cv z)) (synCsn M)))
          syntaxClass0015)).fv :=
    by
    simp only [syntaxClass0001, syntaxClass0002, syntaxClass0003, syntaxClass0004,
      syntaxClass0005, syntaxClass0006, syntaxClass0007, syntaxClass0008, syntaxClass0009,
      syntaxClass0010, syntaxClass0011, syntaxClass0012, syntaxClass0013, syntaxClass0014,
      syntaxClass0015, NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cidk, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_n_ne_t, fresh_n_ne_z,
      fresh_n_not_M, or_false, not_false_eq_true]
  have p0158 :=
    @gN1941v (.classEq (.cv t) (synCsn (synCsn (.cv n)))) syntaxFormula0041 n
      freeVariableCertificate34
  have p0159 :=
    @gBitr4i syntaxFormula0084
      (synWa (synWex n (.classEq (.cv t) (synCsn (synCsn (.cv n))))) syntaxFormula0041)
      syntaxFormula0085 p0157 p0158
  have p0160 := @gExbii syntaxFormula0084 syntaxFormula0085 t p0159
  have p0161 := (Nominal.biimpRefl syntaxFormula0086)
  have p0162 := @gExcom syntaxFormula0082 n t
  have p0163 :=
    @gN3bitr4i (synWex t syntaxFormula0084) (synWex t syntaxFormula0085)
      syntaxFormula0086 syntaxFormula0087 p0160 p0161 p0162
  have p0164 :=
    @gN3bitri syntaxFormula0088
      (.classMem (synCopk (synCsn (.cv z)) (synCsn M)) syntaxClass0016)
      syntaxFormula0086 syntaxFormula0087 p0153 p0155 p0163
  have freeVariableCertificate35 : n ∉ (syntaxFormula0027).fv := by
    simp only [syntaxFormula0027, NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union,
      Finset.mem_erase, Finset.mem_singleton, Finset.notMem_empty, fresh_n_ne_y,
      fresh_n_not_M, fresh_n_ne_a, or_false, and_false, not_false_eq_true]
  have p0165 :=
    @gDfiota2 syntaxFormula0027 y n freeVariableCertificate35
      (show y ≠ n from (by exact fresh_y_ne_n))
  have p0166 :=
    @gEleq2i syntaxClass0028
      (synCuni (.cab n (.all y (synWb syntaxFormula0027 (.objEq y n))))) (.cv z) p0165
  have freeVariableCertificate36 : n ∉ ((Class.cv z)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_n_ne_z, not_false_eq_true]
  have p0167 :=
    @gEluniab (.all y (synWb syntaxFormula0027 (.objEq y n))) n (.cv z)
      freeVariableCertificate36
  have p0168_e01_recanon :
    Nominal.NPrf
      (synWb (.classMem (.cv z)
          (synCuni (.cab n (.all y (synWb syntaxFormula0027 (.objEq y n)))))) (synWex n
          (synWa (.objMem z n) (.all y (synWb syntaxFormula0027 (.objEq y n)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [synWb, synCuni, synWex, synWa]
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cab,
          NFChoice.Compiler.CoreFVSimp.fv_wff_all]
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
      p0167
  have p0168 :=
    @gBitri syntaxFormula0089
      (.classMem (.cv z) (synCuni (.cab n (.all y (synWb syntaxFormula0027 (.objEq y n))))))
      (synWex n (synWa (.objMem z n) (.all y (synWb syntaxFormula0027 (.objEq y n)))))
      p0166 p0168_e01_recanon
  have p0169 :=
    @gN3bitr4i syntaxFormula0087
      (synWex n (synWa (.objMem z n) (.all y (synWb syntaxFormula0027 (.objEq y n)))))
      syntaxFormula0088 syntaxFormula0089 p0152 p0164 p0168
  have p0170 :=
    @gBibi12i syntaxFormula0040 (.classMem (.cv z) X) syntaxFormula0088 syntaxFormula0089
      p0045 p0169
  have p0171 :=
    @gXchbinx syntaxFormula0039 (synWb syntaxFormula0040 syntaxFormula0088)
      syntaxFormula0090 p0039 p0170
  have p0172 := @gBitri syntaxFormula0037 syntaxFormula0039 syntaxFormula0091 p0038 p0171
  have p0173 := @gExbii syntaxFormula0037 syntaxFormula0091 z p0172
  have p0174 :=
    @gN3bitri syntaxFormula0092 syntaxFormula0036 syntaxFormula0038 syntaxFormula0093
      p0026 p0034 p0173
  have p0175 := @gNotbii syntaxFormula0092 syntaxFormula0093 p0174
  have p0176 := @gElcompl (synCopk (synCsn M) X) syntaxClass0019 p0025
  have freeVariableCertificate37 : z ∉ (syntaxClass0028).fv := by
    simp only [syntaxFormula0027, syntaxClass0028,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cio,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union,
      Finset.mem_erase, Finset.mem_singleton, Finset.notMem_empty, fresh_z_ne_y,
      fresh_z_not_M, fresh_z_ne_a, or_false, and_false, not_false_eq_true]
  have p0177 :=
    @gDfcleq z X syntaxClass0028
      (by exact (show z ∉ (X).fv from (by exact fresh_z_not_X))) freeVariableCertificate37
  have p0178 := @gAlex syntaxFormula0090 z
  have p0179 :=
    @gBitri syntaxFormula0094 (.all z syntaxFormula0090) syntaxFormula0095 p0177 p0178
  have p0180 :=
    @gN3bitr4i (.neg syntaxFormula0092) syntaxFormula0095 syntaxFormula0096
      syntaxFormula0094 p0175 p0176 p0179
  have p0181 :=
    @gA1i (synWb syntaxFormula0096 syntaxFormula0094) (.neg (.classEq M (synC0))) p0180
  have p0182 :=
    @gOpkelxpk (synCsn M) X (synCsn (synCsn (synC0))) (synCvv) p0041
      hyp_eqtfinrelk_2
  have p0183 :=
    @gBiantru (.classMem X (synCvv))
      (.classMem (synCsn M) (synCsn (synCsn (synC0)))) hyp_eqtfinrelk_2
  have p0184 := @gElsnc (synCsn M) (synCsn (synC0)) p0041
  have p0185 := @gSneqb M (synC0) hyp_eqtfinrelk_1
  have p0186 :=
    @gBitri (.classMem (synCsn M) (synCsn (synCsn (synC0))))
      (.classEq (synCsn M) (synCsn (synC0))) (.classEq M (synC0)) p0184 p0185
  have p0187 :=
    @gN3bitr2i syntaxFormula0097
      (synWa (.classMem (synCsn M) (synCsn (synCsn (synC0)))) (.classMem X (synCvv)))
      (.classMem (synCsn M) (synCsn (synCsn (synC0)))) (.classEq M (synC0)) p0182
      p0183 p0186
  have p0188 := @gBiimpi syntaxFormula0097 (.classEq M (synC0)) p0187
  have p0189 := @gCon3i syntaxFormula0097 (.classEq M (synC0)) p0188
  have p0190 :=
    @gBiantrud (.neg (.classEq M (synC0))) syntaxFormula0098 syntaxFormula0096 p0189
  have p0191 := @gSimpl (.classEq M (synC0)) (.classEq X (synC0))
  have p0192 :=
    @gCon3i (synWa (.classEq M (synC0)) (.classEq X (synC0))) (.classEq M (synC0))
      p0191
  have p0193 :=
    @gBiorf (synWa (.classEq M (synC0)) (.classEq X (synC0))) syntaxFormula0099
  have p0194 :=
    @gSyl (.neg (.classEq M (synC0)))
      (.neg (synWa (.classEq M (synC0)) (.classEq X (synC0))))
      (synWb syntaxFormula0099 syntaxFormula0100) p0192 p0193
  have p0195 :=
    @gBitrd (.neg (.classEq M (synC0))) syntaxFormula0096 syntaxFormula0099
      syntaxFormula0100 p0190 p0194
  have p0196 :=
    @gOpkelxpk (synCsn M) X (synCsn (synCsn (synC0))) (synCsn (synC0)) p0041
      hyp_eqtfinrelk_2
  have p0197 :=
    @gAnbi12i (.classMem (synCsn M) (synCsn (synCsn (synC0)))) (.classEq M (synC0))
      (.classMem X (synCsn (synC0))) (.classEq X (synC0)) p0186 p0004
  have p0198 :=
    @gBitri syntaxFormula0101
      (synWa (.classMem (synCsn M) (synCsn (synCsn (synC0))))
        (.classMem X (synCsn (synC0))))
      (synWa (.classEq M (synC0)) (.classEq X (synC0))) p0196 p0197
  have p0199 :=
    @gEldif (synCopk (synCsn M) X) syntaxClass0020
      (synCxpk (synCsn (synCsn (synC0))) (synCvv))
  have p0200 :=
    @gOrbi12i syntaxFormula0101 (synWa (.classEq M (synC0)) (.classEq X (synC0)))
      syntaxFormula0102 syntaxFormula0099 p0198 p0199
  have p0201 :=
    @gSyl6bbr (.neg (.classEq M (synC0))) syntaxFormula0096 syntaxFormula0100
      syntaxFormula0103 p0195 p0200
  have p0202 :=
    @gElun (synCopk (synCsn M) X)
      (synCxpk (synCsn (synCsn (synC0))) (synCsn (synC0))) syntaxClass0021
  have p0203 :=
    @gSyl6bbr (.neg (.classEq M (synC0))) syntaxFormula0096 syntaxFormula0103
      syntaxFormula0030 p0201 p0202
  have p0204 :=
    @gN3bitr2rd (.neg (.classEq M (synC0))) syntaxFormula0031 syntaxFormula0094
      syntaxFormula0096 syntaxFormula0030 p0024 p0181 p0203
  have p0205 :=
    @gPm261i (.classEq M (synC0)) (synWb syntaxFormula0030 syntaxFormula0031) p0022
      p0204
  have p0206 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfTfin y M a
      (by exact (show a ∉ (M).fv from (by exact fresh_a_not_M)))
      (by exact (show y ∉ (M).fv from (by exact fresh_y_not_M)))
      (show a ≠ y from (by exact fresh_a_ne_y))
  have p0207 := @gEqeq2i (synCtfin M) syntaxClass0029 X p0206
  have p0208 :=
    @gBitr4i syntaxFormula0030 syntaxFormula0031 (.classEq X (synCtfin M)) p0205 p0207
  exact p0208


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk009StructuralPart054`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_tfinrelkex`. -/
@[expose]
noncomputable def gTfinrelkex :
    Nominal.NPrf
      (.classMem (synCun (synCxpk (synCsn (synCsn (synC0))) (synCsn (synC0))) (synCdif
            (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCimak
                      (synCdif (synCins3k (synCcnvk (synCssetk))) (synCins2k (synCimak
                            (synCsymdif (synCins2k (synCin (synCxpk (synCnnc) (synCvv))
                                  (synCimak (synCin (synCins2k (synCsik (synCssetk)))
                                      (synCins3k (synCimak (synCin (synCins3k (synCsik
        (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak
        (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk)))) (synCpw1
        (synCpw1 (synCpw1 (synC1c)))))))) (synCins2k (synCssetk)))
        (synCpw1 (synCpw1 (synC1c)))))) (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                              (synCins3k (synCidk))) (synCpw1 (synC1c)))))
                      (synCpw1 (synC1c))))) (synCpw1 (synCpw1 (synC1c)))))
            (synCxpk (synCsn (synCsn (synC0))) (synCvv)))) (synCvv)) :=
  by
  have p0000 := @gSnex (synCsn (synC0))
  have p0001 := @gSnex (synC0)
  have p0002 := @gXpkex (synCsn (synCsn (synC0))) (synCsn (synC0)) p0000 p0001
  have p0003 := @gSsetkex
  have p0004 := @gIns2kex (synCssetk) p0003
  have p0006 := @gCnvkex (synCssetk) p0003
  have p0007 := @gIns3kex (synCcnvk (synCssetk)) p0006
  have p0008 := @gNncex
  have p0009 := @gVvex
  have p0010 := @gXpkex (synCnnc) (synCvv) p0008 p0009
  have p0012 := @gSikex (synCssetk) p0003
  have p0013 := @gIns2kex (synCsik (synCssetk)) p0012
  have p0014 := @gN1cex
  have p0015 := @gPwex (synC1c) p0014
  have p0017 := @gXpkex (synCpw (synC1c)) (synCvv) p0015 p0009
  have p0019 := @gIns3kex (synCssetk) p0003
  have p0020 :=
    @gSymdifex (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk))) p0019 p0013
  have p0022 := @gPw1ex (synC1c) p0014
  have p0023 := @gPw1ex (synCpw1 (synC1c)) p0022
  have p0024 := @gPw1ex (synCpw1 (synCpw1 (synC1c))) p0023
  have p0025 :=
    @gImakex (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk))))
      (synCpw1 (synCpw1 (synCpw1 (synC1c)))) p0020 p0024
  have p0026 :=
    @gDifex (synCxpk (synCpw (synC1c)) (synCvv))
      (synCimak (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk))))
        (synCpw1 (synCpw1 (synCpw1 (synC1c)))))
      p0017 p0025
  have p0027 :=
    @gSikex
      (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak
          (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk))))
          (synCpw1 (synCpw1 (synCpw1 (synC1c))))))
      p0026
  have p0028 :=
    @gIns3kex
      (synCsik (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak
            (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk))))
            (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
      p0027
  have p0029 :=
    @gInex
      (synCins3k (synCsik (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak
              (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk))))
              (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
      (synCins2k (synCssetk)) p0028 p0004
  have p0030 :=
    @gImakex
      (synCin (synCins3k (synCsik (synCdif (synCxpk (synCpw (synC1c)) (synCvv))
              (synCimak (synCsymdif (synCins3k (synCssetk))
                  (synCins2k (synCsik (synCssetk))))
                (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))) (synCins2k (synCssetk)))
      (synCpw1 (synCpw1 (synC1c))) p0029 p0023
  have p0031 :=
    @gIns3kex
      (synCimak (synCin (synCins3k (synCsik
              (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak
                  (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk))))
                  (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))) (synCins2k (synCssetk)))
        (synCpw1 (synCpw1 (synC1c))))
      p0030
  have p0032 :=
    @gInex (synCins2k (synCsik (synCssetk)))
      (synCins3k (synCimak (synCin (synCins3k (synCsik
                (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak
                    (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk))))
                    (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))) (synCins2k (synCssetk)))
          (synCpw1 (synCpw1 (synC1c)))))
      p0013 p0031
  have p0033 :=
    @gImakex
      (synCin (synCins2k (synCsik (synCssetk))) (synCins3k (synCimak (synCin (synCins3k
                (synCsik (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak
                      (synCsymdif (synCins3k (synCssetk))
                        (synCins2k (synCsik (synCssetk))))
                      (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))) (synCins2k (synCssetk)))
            (synCpw1 (synCpw1 (synC1c))))))
      (synCpw1 (synCpw1 (synCpw1 (synC1c)))) p0032 p0024
  have p0034 :=
    @gInex (synCxpk (synCnnc) (synCvv))
      (synCimak (synCin (synCins2k (synCsik (synCssetk))) (synCins3k (synCimak (synCin
                (synCins3k (synCsik (synCdif (synCxpk (synCpw (synC1c)) (synCvv))
                      (synCimak (synCsymdif (synCins3k (synCssetk))
                          (synCins2k (synCsik (synCssetk))))
                        (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
        (synCpw1 (synCpw1 (synCpw1 (synC1c)))))
      p0010 p0033
  have p0035 :=
    @gIns2kex
      (synCin (synCxpk (synCnnc) (synCvv)) (synCimak
          (synCin (synCins2k (synCsik (synCssetk))) (synCins3k (synCimak (synCin
                  (synCins3k (synCsik (synCdif (synCxpk (synCpw (synC1c)) (synCvv))
                        (synCimak (synCsymdif (synCins3k (synCssetk))
                            (synCins2k (synCsik (synCssetk))))
                          (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                  (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
          (synCpw1 (synCpw1 (synCpw1 (synC1c))))))
      p0034
  have p0036 := @gIdkex
  have p0037 := @gIns3kex (synCidk) p0036
  have p0038 :=
    @gSymdifex
      (synCins2k (synCin (synCxpk (synCnnc) (synCvv)) (synCimak
            (synCin (synCins2k (synCsik (synCssetk))) (synCins3k (synCimak (synCin
                    (synCins3k (synCsik (synCdif (synCxpk (synCpw (synC1c)) (synCvv))
                          (synCimak (synCsymdif (synCins3k (synCssetk))
                              (synCins2k (synCsik (synCssetk))))
                            (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                    (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
            (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
      (synCins3k (synCidk)) p0035 p0037
  have p0039 :=
    @gImakex
      (synCsymdif (synCins2k (synCin (synCxpk (synCnnc) (synCvv)) (synCimak
              (synCin (synCins2k (synCsik (synCssetk))) (synCins3k (synCimak (synCin
                      (synCins3k (synCsik (synCdif (synCxpk (synCpw (synC1c)) (synCvv))
                            (synCimak (synCsymdif (synCins3k (synCssetk))
                                (synCins2k (synCsik (synCssetk))))
                              (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                      (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
              (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCins3k (synCidk)))
      (synCpw1 (synC1c)) p0038 p0022
  have p0040 :=
    @gIns2kex
      (synCimak (synCsymdif (synCins2k (synCin (synCxpk (synCnnc) (synCvv)) (synCimak
                (synCin (synCins2k (synCsik (synCssetk))) (synCins3k (synCimak (synCin
                        (synCins3k (synCsik (synCdif (synCxpk (synCpw (synC1c)) (synCvv))
                              (synCimak (synCsymdif (synCins3k (synCssetk))
                                  (synCins2k (synCsik (synCssetk))))
                                (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                        (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCins3k (synCidk)))
        (synCpw1 (synC1c)))
      p0039
  have p0041 :=
    @gDifex (synCins3k (synCcnvk (synCssetk)))
      (synCins2k (synCimak (synCsymdif (synCins2k (synCin (synCxpk (synCnnc) (synCvv))
                (synCimak (synCin (synCins2k (synCsik (synCssetk))) (synCins3k (synCimak
                        (synCin (synCins3k (synCsik
                              (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak
                                  (synCsymdif (synCins3k (synCssetk))
                                    (synCins2k (synCsik (synCssetk))))
                                  (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                          (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                  (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCins3k (synCidk)))
          (synCpw1 (synC1c))))
      p0007 p0040
  have p0042 :=
    @gImakex
      (synCdif (synCins3k (synCcnvk (synCssetk))) (synCins2k (synCimak (synCsymdif
              (synCins2k (synCin (synCxpk (synCnnc) (synCvv)) (synCimak
                    (synCin (synCins2k (synCsik (synCssetk))) (synCins3k (synCimak
                          (synCin (synCins3k (synCsik
                                (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak
                                    (synCsymdif (synCins3k (synCssetk))
                                      (synCins2k (synCsik (synCssetk))))
                                    (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                            (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                    (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCins3k (synCidk)))
            (synCpw1 (synC1c)))))
      (synCpw1 (synC1c)) p0041 p0022
  have p0043 :=
    @gIns3kex
      (synCimak (synCdif (synCins3k (synCcnvk (synCssetk))) (synCins2k (synCimak
              (synCsymdif (synCins2k (synCin (synCxpk (synCnnc) (synCvv)) (synCimak
                      (synCin (synCins2k (synCsik (synCssetk))) (synCins3k (synCimak
                            (synCin (synCins3k (synCsik
                                  (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak
                                      (synCsymdif (synCins3k (synCssetk))
                                        (synCins2k (synCsik (synCssetk))))
                                      (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                              (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                      (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCins3k (synCidk)))
              (synCpw1 (synC1c))))) (synCpw1 (synC1c)))
      p0042
  have p0044 :=
    @gSymdifex (synCins2k (synCssetk))
      (synCins3k (synCimak (synCdif (synCins3k (synCcnvk (synCssetk))) (synCins2k
              (synCimak (synCsymdif (synCins2k (synCin (synCxpk (synCnnc) (synCvv))
                      (synCimak (synCin (synCins2k (synCsik (synCssetk))) (synCins3k
                            (synCimak (synCin (synCins3k (synCsik
                                    (synCdif (synCxpk (synCpw (synC1c)) (synCvv))
                                      (synCimak (synCsymdif (synCins3k (synCssetk))
        (synCins2k (synCsik (synCssetk)))) (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                                (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                        (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCins3k (synCidk)))
                (synCpw1 (synC1c))))) (synCpw1 (synC1c))))
      p0004 p0043
  have p0045 :=
    @gImakex
      (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCimak
            (synCdif (synCins3k (synCcnvk (synCssetk))) (synCins2k (synCimak (synCsymdif
                    (synCins2k (synCin (synCxpk (synCnnc) (synCvv)) (synCimak
                          (synCin (synCins2k (synCsik (synCssetk))) (synCins3k (synCimak
                                (synCin (synCins3k (synCsik
                                      (synCdif (synCxpk (synCpw (synC1c)) (synCvv))
                                        (synCimak (synCsymdif (synCins3k (synCssetk))
        (synCins2k (synCsik (synCssetk)))) (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                                  (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                          (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCins3k (synCidk)))
                  (synCpw1 (synC1c))))) (synCpw1 (synC1c)))))
      (synCpw1 (synCpw1 (synC1c))) p0044 p0023
  have p0046 :=
    @gComplex
      (synCimak (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCimak
              (synCdif (synCins3k (synCcnvk (synCssetk))) (synCins2k (synCimak
                    (synCsymdif (synCins2k (synCin (synCxpk (synCnnc) (synCvv)) (synCimak
                            (synCin (synCins2k (synCsik (synCssetk))) (synCins3k (synCimak
                                  (synCin (synCins3k (synCsik
                                        (synCdif (synCxpk (synCpw (synC1c)) (synCvv))
        (synCimak (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk))))
        (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))) (synCins2k (synCssetk)))
                                  (synCpw1 (synCpw1 (synC1c))))))
                            (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                      (synCins3k (synCidk))) (synCpw1 (synC1c))))) (synCpw1 (synC1c)))))
        (synCpw1 (synCpw1 (synC1c))))
      p0045
  have p0048 := @gXpkex (synCsn (synCsn (synC0))) (synCvv) p0000 p0009
  have p0049 :=
    @gDifex
      (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCimak
                (synCdif (synCins3k (synCcnvk (synCssetk))) (synCins2k (synCimak
                      (synCsymdif (synCins2k (synCin (synCxpk (synCnnc) (synCvv))
                            (synCimak (synCin (synCins2k (synCsik (synCssetk))) (synCins3k
                                  (synCimak (synCin (synCins3k (synCsik (synCdif
        (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak
        (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk)))) (synCpw1
        (synCpw1 (synCpw1 (synC1c)))))))) (synCins2k (synCssetk)))
                                    (synCpw1 (synCpw1 (synC1c))))))
                              (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                        (synCins3k (synCidk))) (synCpw1 (synC1c))))) (synCpw1 (synC1c)))))
          (synCpw1 (synCpw1 (synC1c)))))
      (synCxpk (synCsn (synCsn (synC0))) (synCvv)) p0046 p0048
  have p0050 :=
    @gUnex (synCxpk (synCsn (synCsn (synC0))) (synCsn (synC0)))
      (synCdif (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk)) (synCins3k
                (synCimak (synCdif (synCins3k (synCcnvk (synCssetk))) (synCins2k
                      (synCimak (synCsymdif (synCins2k
                            (synCin (synCxpk (synCnnc) (synCvv)) (synCimak
                                (synCin (synCins2k (synCsik (synCssetk))) (synCins3k
                                    (synCimak (synCin (synCins3k (synCsik (synCdif
        (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak
        (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk)))) (synCpw1
        (synCpw1 (synCpw1 (synC1c)))))))) (synCins2k (synCssetk)))
                                      (synCpw1 (synCpw1 (synC1c))))))
                                (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                          (synCins3k (synCidk))) (synCpw1 (synC1c)))))
                  (synCpw1 (synC1c))))) (synCpw1 (synCpw1 (synC1c)))))
        (synCxpk (synCsn (synCsn (synC0))) (synCvv)))
      p0002 p0049
  exact p0050

/-- Checked nominal proof certificate identified upstream as `g_tfineq`. -/
@[expose]
noncomputable def gTfineq (A : Class) (B : Class) :
    Nominal.NPrf (.imp (.classEq A B) (.classEq (synCtfin A) (synCtfin B))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
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
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (h))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x := Ne.symm fresh_x_ne_y
  have p0000 := @gEqeq1 A B (synC0)
  have p0001 :=
    @gRexeq (.classMem (synCpw1 (.cv y)) (.cv x)) y A B
      (by exact (show y ∉ (A).fv from (by exact fresh_y_not_A)))
      (by exact (show y ∉ (B).fv from (by exact fresh_y_not_B)))
  have p0002 :=
    @gAnbi2d (.classEq A B) (synWrex y A (.classMem (synCpw1 (.cv y)) (.cv x)))
      (synWrex y B (.classMem (synCpw1 (.cv y)) (.cv x))) (.classMem (.cv x) (synCnnc))
      p0001
  have freeVariableCertificate0 : x ∉ ((Wff.classEq A B)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union,
      fresh_x_not_A, fresh_x_not_B, or_false, not_false_eq_true]
  have p0003 :=
    @gIotabidv (.classEq A B)
      (synWa (.classMem (.cv x) (synCnnc))
        (synWrex y A (.classMem (synCpw1 (.cv y)) (.cv x))))
      (synWa (.classMem (.cv x) (synCnnc))
        (synWrex y B (.classMem (synCpw1 (.cv y)) (.cv x))))
      x freeVariableCertificate0 p0002
  have p0004 :=
    @gIfbieq2d (.classEq A B) (.classEq A (synC0)) (.classEq B (synC0))
      (synCio x (synWa (.classMem (.cv x) (synCnnc))
          (synWrex y A (.classMem (synCpw1 (.cv y)) (.cv x)))))
      (synCio x (synWa (.classMem (.cv x) (synCnnc))
          (synWrex y B (.classMem (synCpw1 (.cv y)) (.cv x)))))
      (synC0) p0000 p0003
  have p0005 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfTfin x A y
      (by exact (show y ∉ (A).fv from (by exact fresh_y_not_A)))
      (by exact (show x ∉ (A).fv from (by exact fresh_x_not_A)))
      (show y ≠ x from (by exact fresh_y_ne_x))
  have p0006 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfTfin x B y
      (by exact (show y ∉ (B).fv from (by exact fresh_y_not_B)))
      (by exact (show x ∉ (B).fv from (by exact fresh_x_not_B)))
      (show y ≠ x from (by exact fresh_y_ne_x))
  have p0007 :=
    @gN3eqtr4g (.classEq A B)
      (synCif (.classEq A (synC0)) (synC0) (synCio x (synWa (.classMem (.cv x) (synCnnc))
            (synWrex y A (.classMem (synCpw1 (.cv y)) (.cv x))))))
      (synCif (.classEq B (synC0)) (synC0) (synCio x (synWa (.classMem (.cv x) (synCnnc))
            (synWrex y B (.classMem (synCpw1 (.cv y)) (.cv x))))))
      (synCtfin A) (synCtfin B) p0004 p0005 p0006
  exact p0007

/-- Checked nominal proof certificate identified upstream as `g_tfinprop`. -/
@[expose]
noncomputable def gTfinprop (M : Class) (a : Var) (dv_M_a : a ∉ M.fv) :
    Nominal.NPrf
      (.imp (synWa (.classMem M (synCnnc)) (synWne M (synC0)))
        (synWa (.classMem (synCtfin M) (synCnnc))
          (synWrex a M (.classMem (synCpw1 (.cv a)) (synCtfin M))))) :=
  by
  let proofSupport : Finset Var := M.fv ∪ ({ a } : Finset Var)
  let n : Var := freshVar proofSupport 0
  have fresh_n : n ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_n_not_M : n ∉ M.fv := by
    intro h
    exact fresh_n (Finset.mem_union_left _ (h))
  have fresh_n_ne_a : n ≠ a := by
    intro h
    exact fresh_n (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_a_ne_n : a ≠ n := Ne.symm fresh_n_ne_a
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfTfin n M a
      (by exact (show a ∉ (M).fv from (by exact dv_M_a)))
      (by exact (show n ∉ (M).fv from (by exact fresh_n_not_M)))
      (show a ≠ n from (by exact fresh_a_ne_n))
  have p0001 := (Nominal.biimpRefl (synWne M (synC0)))
  have p0002 :=
    @gIffalse (.classEq M (synC0)) (synC0)
      (synCio n (synWa (.classMem (.cv n) (synCnnc))
          (synWrex a M (.classMem (synCpw1 (.cv a)) (.cv n)))))
  have p0003 :=
    @gSylbi (synWne M (synC0)) (.neg (.classEq M (synC0)))
      (.classEq (synCif (.classEq M (synC0)) (synC0) (synCio n
            (synWa (.classMem (.cv n) (synCnnc))
              (synWrex a M (.classMem (synCpw1 (.cv a)) (.cv n)))))) (synCio n
          (synWa (.classMem (.cv n) (synCnnc))
            (synWrex a M (.classMem (synCpw1 (.cv a)) (.cv n))))))
      p0001 p0002
  have p0004 :=
    @gAdantl (synWne M (synC0))
      (.classEq (synCif (.classEq M (synC0)) (synC0) (synCio n
            (synWa (.classMem (.cv n) (synCnnc))
              (synWrex a M (.classMem (synCpw1 (.cv a)) (.cv n)))))) (synCio n
          (synWa (.classMem (.cv n) (synCnnc))
            (synWrex a M (.classMem (synCpw1 (.cv a)) (.cv n))))))
      (.classMem M (synCnnc)) p0003
  have p0005 :=
    @gNnpw1ex n M a (by exact (show a ∉ (M).fv from (by exact dv_M_a)))
      (by exact (show n ∉ (M).fv from (by exact fresh_n_not_M)))
      (show a ≠ n from (by exact fresh_a_ne_n))
  have p0006 :=
    @gReiotacl (synWrex a M (.classMem (synCpw1 (.cv a)) (.cv n))) n (synCnnc)
      (by
        exact
          (show n ∉ ((synCnnc)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc];
              exact (show n ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
  have p0007 :=
    @gSyl (synWa (.classMem M (synCnnc)) (synWne M (synC0)))
      (synWreu n (synCnnc) (synWrex a M (.classMem (synCpw1 (.cv a)) (.cv n))))
      (.classMem (synCio n (synWa (.classMem (.cv n) (synCnnc))
            (synWrex a M (.classMem (synCpw1 (.cv a)) (.cv n))))) (synCnnc))
      p0005 p0006
  have p0008 :=
    @gEqeltrd (synWa (.classMem M (synCnnc)) (synWne M (synC0)))
      (synCif (.classEq M (synC0)) (synC0) (synCio n (synWa (.classMem (.cv n) (synCnnc))
            (synWrex a M (.classMem (synCpw1 (.cv a)) (.cv n))))))
      (synCio n (synWa (.classMem (.cv n) (synCnnc))
          (synWrex a M (.classMem (synCpw1 (.cv a)) (.cv n)))))
      (synCnnc) p0004 p0007
  have p0009 :=
    @gSyl5eqel (synWa (.classMem M (synCnnc)) (synWne M (synC0))) (synCtfin M)
      (synCif (.classEq M (synC0)) (synC0) (synCio n (synWa (.classMem (.cv n) (synCnnc))
            (synWrex a M (.classMem (synCpw1 (.cv a)) (.cv n))))))
      (synCnnc) p0000 p0008
  have p0010 :=
    @gSyl5req (synWa (.classMem M (synCnnc)) (synWne M (synC0))) (synCtfin M)
      (synCif (.classEq M (synC0)) (synC0) (synCio n (synWa (.classMem (.cv n) (synCnnc))
            (synWrex a M (.classMem (synCpw1 (.cv a)) (.cv n))))))
      (synCio n (synWa (.classMem (.cv n) (synCnnc))
          (synWrex a M (.classMem (synCpw1 (.cv a)) (.cv n)))))
      p0000 p0004
  have p0011 :=
    @gJca (synWa (.classMem M (synCnnc)) (synWne M (synC0)))
      (.classMem (synCtfin M) (synCnnc))
      (synWreu n (synCnnc) (synWrex a M (.classMem (synCpw1 (.cv a)) (.cv n)))) p0009
      p0005
  have p0012 := @gEleq2 (.cv n) (synCtfin M) (synCpw1 (.cv a))
  have freeVariableCertificate0 : a ∉ ((Wff.classEq (.cv n) (synCtfin M))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin, Finset.mem_union,
      Finset.mem_singleton, fresh_a_ne_n, dv_M_a, or_false, not_false_eq_true]
  have p0013 :=
    @gRexbidv (.classEq (.cv n) (synCtfin M)) (.classMem (synCpw1 (.cv a)) (.cv n))
      (.classMem (synCpw1 (.cv a)) (synCtfin M)) a M freeVariableCertificate0 p0012
  have freeVariableCertificate1 :
    n ∉ ((synWrex a M (.classMem (synCpw1 (.cv a)) (synCtfin M)))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin, Finset.mem_union,
      Finset.mem_erase, Finset.mem_singleton, fresh_n_not_M, fresh_n_ne_a, or_false,
      and_false, not_false_eq_true]
  have p0014 :=
    @gReiota2 (synWrex a M (.classMem (synCpw1 (.cv a)) (.cv n)))
      (synWrex a M (.classMem (synCpw1 (.cv a)) (synCtfin M))) n (synCnnc)
      (synCtfin M)
      (by
        exact
          (show n ∉ ((synCnnc)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc];
              exact (show n ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
      (by
        exact
          (show n ∉ ((synCtfin M)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin];
              exact (show n ∉ (M).fv from (by exact fresh_n_not_M)))))
      freeVariableCertificate1 p0013
  have p0015 :=
    @gSyl (synWa (.classMem M (synCnnc)) (synWne M (synC0)))
      (synWa (.classMem (synCtfin M) (synCnnc))
        (synWreu n (synCnnc) (synWrex a M (.classMem (synCpw1 (.cv a)) (.cv n)))))
      (synWb (synWrex a M (.classMem (synCpw1 (.cv a)) (synCtfin M))) (.classEq (synCio n
            (synWa (.classMem (.cv n) (synCnnc))
              (synWrex a M (.classMem (synCpw1 (.cv a)) (.cv n))))) (synCtfin M)))
      p0011 p0014
  have p0016 :=
    @gMpbird (synWa (.classMem M (synCnnc)) (synWne M (synC0)))
      (synWrex a M (.classMem (synCpw1 (.cv a)) (synCtfin M)))
      (.classEq (synCio n (synWa (.classMem (.cv n) (synCnnc))
            (synWrex a M (.classMem (synCpw1 (.cv a)) (.cv n))))) (synCtfin M))
      p0010 p0015
  have p0017 :=
    @gJca (synWa (.classMem M (synCnnc)) (synWne M (synC0)))
      (.classMem (synCtfin M) (synCnnc))
      (synWrex a M (.classMem (synCpw1 (.cv a)) (synCtfin M))) p0009 p0016
  exact p0017

/-- Checked nominal proof certificate identified upstream as `g_tfinnnul`. -/
@[expose]
noncomputable def gTfinnnul (M : Class) :
    Nominal.NPrf
      (.imp (synWa (.classMem M (synCnnc)) (synWne M (synC0)))
        (synWne (synCtfin M) (synC0))) :=
  by
  let proofSupport : Finset Var := M.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_M : x ∉ M.fv := by
    intro h
    exact fresh_x (h)
  have p0000 := @gTfinprop M x (by exact (show x ∉ (M).fv from (by exact fresh_x_not_M)))
  have p0001 := @gNe0i (synCtfin M) (synCpw1 (.cv x))
  have freeVariableCertificate0 : x ∉ ((synWne (synCtfin M) (synC0))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union,
      Finset.notMem_empty, fresh_x_not_M, or_false, not_false_eq_true]
  have p0002 :=
    @gRexlimivw (.classMem (synCpw1 (.cv x)) (synCtfin M))
      (synWne (synCtfin M) (synC0)) x M freeVariableCertificate0 p0001
  have p0003 :=
    @gAdantl (synWrex x M (.classMem (synCpw1 (.cv x)) (synCtfin M)))
      (synWne (synCtfin M) (synC0)) (.classMem (synCtfin M) (synCnnc)) p0002
  have p0004 :=
    @gSyl (synWa (.classMem M (synCnnc)) (synWne M (synC0)))
      (synWa (.classMem (synCtfin M) (synCnnc))
        (synWrex x M (.classMem (synCpw1 (.cv x)) (synCtfin M))))
      (synWne (synCtfin M) (synC0)) p0000 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_tfinnul`. -/
@[expose]
noncomputable def gTfinnul : Nominal.NPrf (.classEq (synCtfin (synC0)) (synC0)) :=
  by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x := Ne.symm fresh_x_ne_y
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfTfin x (synC0) y
      (by
        exact
          (show y ∉ ((synC0)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0];
              exact (show y ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
      (by
        exact
          (show x ∉ ((synC0)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0];
              exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
      (show y ≠ x from (by exact fresh_y_ne_x))
  have p0001 := @gEqid (synC0)
  have p0002 :=
    @gIftrue (.classEq (synC0) (synC0)) (synC0)
      (synCio x (synWa (.classMem (.cv x) (synCnnc))
          (synWrex y (synC0) (.classMem (synCpw1 (.cv y)) (.cv x)))))
  have p0003 := Nominal.mp p0001 p0002
  have p0004 :=
    @gEqtri (synCtfin (synC0))
      (synCif (.classEq (synC0) (synC0)) (synC0) (synCio x
          (synWa (.classMem (.cv x) (synCnnc))
            (synWrex y (synC0) (.classMem (synCpw1 (.cv y)) (.cv x))))))
      (synC0) p0000 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_tfincl`. -/
@[expose]
noncomputable def gTfincl (N : Class) :
    Nominal.NPrf (.imp (.classMem N (synCnnc)) (.classMem (synCtfin N) (synCnnc))) :=
  by
  let proofSupport : Finset Var := N.fv
  let a : Var := freshVar proofSupport 0
  have fresh_a : a ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_a_not_N : a ∉ N.fv := by
    intro h
    exact fresh_a (h)
  have p0000 := @gTfinnul
  have p0001 := @gTfineq N (synC0)
  have p0002 := @gId (.classEq N (synC0))
  have p0003 :=
    @gN3eqtr4a (.classEq N (synC0)) (synCtfin (synC0)) (synC0) (synCtfin N) N p0000
      p0001 p0002
  have p0004 := @gEleq1d (.classEq N (synC0)) (synCtfin N) N (synCnnc) p0003
  have p0005 :=
    @gBiimprd (.classEq N (synC0)) (.classMem (synCtfin N) (synCnnc))
      (.classMem N (synCnnc)) p0004
  have p0006 := @gTfinprop N a (by exact (show a ∉ (N).fv from (by exact fresh_a_not_N)))
  have p0007 :=
    @gSimpld (synWa (.classMem N (synCnnc)) (synWne N (synC0)))
      (.classMem (synCtfin N) (synCnnc))
      (synWrex a N (.classMem (synCpw1 (.cv a)) (synCtfin N))) p0006
  have p0008 :=
    @gExpcom (.classMem N (synCnnc)) (synWne N (synC0))
      (.classMem (synCtfin N) (synCnnc)) p0007
  have p0009 :=
    @gPm261ine (.imp (.classMem N (synCnnc)) (.classMem (synCtfin N) (synCnnc))) N
      (synC0) p0005 p0008
  exact p0009


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk009StructuralPart055`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_tfin11`. -/
@[expose]
noncomputable def gTfin11 (M : Class) (N : Class) :
    Nominal.NPrf
      (.imp (synW3a (.classMem M (synCnnc)) (.classMem N (synCnnc))
          (.classEq (synCtfin M) (synCtfin N))) (.classEq M N)) :=
  by
  let proofSupport : Finset Var := M.fv ∪ N.fv
  let a : Var := freshVar proofSupport 0
  let b : Var := freshVar proofSupport 1
  let p : Var := freshVar proofSupport 2
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
  have fresh_p : p ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_p_not_M : p ∉ M.fv := by
    intro h
    exact fresh_p (Finset.mem_union_left _ (h))
  have fresh_p_not_N : p ∉ N.fv := by
    intro h
    exact fresh_p (Finset.mem_union_right _ (h))
  have fresh_a_ne_b : a ≠ b :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_b_ne_a : b ≠ a := Ne.symm fresh_a_ne_b
  have fresh_a_ne_p : a ≠ p :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_p_ne_a : p ≠ a := Ne.symm fresh_a_ne_p
  have fresh_b_ne_p : b ≠ p :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_p_ne_b : p ≠ b := Ne.symm fresh_b_ne_p
  have p0000 := @gTfinnnul M
  have p0001 :=
    @gEx (.classMem M (synCnnc)) (synWne M (synC0)) (synWne (synCtfin M) (synC0))
      p0000
  have p0002 :=
    @gNecon4d (.classMem M (synCnnc)) M (synC0) (synCtfin M) (synC0) p0001
  have p0003 :=
    @gN3ad2ant1 (.classMem M (synCnnc)) (.classMem N (synCnnc))
      (.imp (.classEq (synCtfin M) (synC0)) (.classEq M (synC0)))
      (.classEq (synCtfin M) (synCtfin N)) p0002
  have p0004 :=
    @gImpcom
      (synW3a (.classMem M (synCnnc)) (.classMem N (synCnnc))
        (.classEq (synCtfin M) (synCtfin N)))
      (.classEq (synCtfin M) (synC0)) (.classEq M (synC0)) p0003
  have p0005 := @gEqeq1 (synCtfin M) (synCtfin N) (synC0)
  have p0006 :=
    @gAdantl (.classEq (synCtfin M) (synCtfin N))
      (synWb (.classEq (synCtfin M) (synC0)) (.classEq (synCtfin N) (synC0)))
      (.classMem N (synCnnc)) p0005
  have p0007 := @gTfinnnul N
  have p0008 :=
    @gEx (.classMem N (synCnnc)) (synWne N (synC0)) (synWne (synCtfin N) (synC0))
      p0007
  have p0009 :=
    @gNecon4d (.classMem N (synCnnc)) N (synC0) (synCtfin N) (synC0) p0008
  have p0010 :=
    @gAdantr (.classMem N (synCnnc))
      (.imp (.classEq (synCtfin N) (synC0)) (.classEq N (synC0)))
      (.classEq (synCtfin M) (synCtfin N)) p0009
  have p0011 :=
    @gSylbid (synWa (.classMem N (synCnnc)) (.classEq (synCtfin M) (synCtfin N)))
      (.classEq (synCtfin M) (synC0)) (.classEq (synCtfin N) (synC0))
      (.classEq N (synC0)) p0006 p0010
  have p0012 :=
    @gN3adant1 (.classMem N (synCnnc)) (.classEq (synCtfin M) (synCtfin N))
      (.imp (.classEq (synCtfin M) (synC0)) (.classEq N (synC0)))
      (.classMem M (synCnnc)) p0011
  have p0013 :=
    @gImpcom
      (synW3a (.classMem M (synCnnc)) (.classMem N (synCnnc))
        (.classEq (synCtfin M) (synCtfin N)))
      (.classEq (synCtfin M) (synC0)) (.classEq N (synC0)) p0012
  have p0014 :=
    @gEqtr4d
      (synWa (.classEq (synCtfin M) (synC0))
        (synW3a (.classMem M (synCnnc)) (.classMem N (synCnnc))
          (.classEq (synCtfin M) (synCtfin N))))
      M (synC0) N p0004 p0013
  have p0015 :=
    @gEx (.classEq (synCtfin M) (synC0))
      (synW3a (.classMem M (synCnnc)) (.classMem N (synCnnc))
        (.classEq (synCtfin M) (synCtfin N)))
      (.classEq M N) p0014
  have p0016 := @gNeeq1 (synCtfin M) (synCtfin N) (synC0)
  have p0017 :=
    @gBiimpd (.classEq (synCtfin M) (synCtfin N)) (synWne (synCtfin M) (synC0))
      (synWne (synCtfin N) (synC0)) p0016
  have p0018 :=
    @gAncld (.classEq (synCtfin M) (synCtfin N)) (synWne (synCtfin M) (synC0))
      (synWne (synCtfin N) (synC0)) p0017
  have p0019 := @gTfineq M (synC0)
  have p0020 := @gTfinnul
  have p0021 :=
    @gSyl6eq (.classEq M (synC0)) (synCtfin M) (synCtfin (synC0)) (synC0) p0019
      p0020
  have p0022 := @gNecon3i M (synC0) (synCtfin M) (synC0) p0021
  have p0023 := @gTfineq N (synC0)
  have p0025 :=
    @gSyl6eq (.classEq N (synC0)) (synCtfin N) (synCtfin (synC0)) (synC0) p0023
      p0020
  have p0026 := @gNecon3i N (synC0) (synCtfin N) (synC0) p0025
  have p0027 :=
    @gAnim12i (synWne (synCtfin M) (synC0)) (synWne M (synC0))
      (synWne (synCtfin N) (synC0)) (synWne N (synC0)) p0022 p0026
  have p0028 :=
    @gSyl6 (.classEq (synCtfin M) (synCtfin N)) (synWne (synCtfin M) (synC0))
      (synWa (synWne (synCtfin M) (synC0)) (synWne (synCtfin N) (synC0)))
      (synWa (synWne M (synC0)) (synWne N (synC0))) p0018 p0027
  have p0029 :=
    @gN3ad2ant3 (.classEq (synCtfin M) (synCtfin N)) (.classMem M (synCnnc))
      (.imp (synWne (synCtfin M) (synC0)) (synWa (synWne M (synC0)) (synWne N (synC0))))
      (.classMem N (synCnnc)) p0028
  have p0030 := @gTfinprop M a (by exact (show a ∉ (M).fv from (by exact fresh_a_not_M)))
  have p0031 :=
    @gEx (.classMem M (synCnnc)) (synWne M (synC0))
      (synWa (.classMem (synCtfin M) (synCnnc))
        (synWrex a M (.classMem (synCpw1 (.cv a)) (synCtfin M))))
      p0030
  have p0032 :=
    @gN3ad2ant1 (.classMem M (synCnnc)) (.classMem N (synCnnc))
      (.imp (synWne M (synC0)) (synWa (.classMem (synCtfin M) (synCnnc))
          (synWrex a M (.classMem (synCpw1 (.cv a)) (synCtfin M)))))
      (.classEq (synCtfin M) (synCtfin N)) p0031
  have p0033 := @gTfinprop N b (by exact (show b ∉ (N).fv from (by exact fresh_b_not_N)))
  have p0034 :=
    @gEx (.classMem N (synCnnc)) (synWne N (synC0))
      (synWa (.classMem (synCtfin N) (synCnnc))
        (synWrex b N (.classMem (synCpw1 (.cv b)) (synCtfin N))))
      p0033
  have p0035 :=
    @gN3ad2ant2 (.classMem N (synCnnc)) (.classMem M (synCnnc))
      (.imp (synWne N (synC0)) (synWa (.classMem (synCtfin N) (synCnnc))
          (synWrex b N (.classMem (synCpw1 (.cv b)) (synCtfin N)))))
      (.classEq (synCtfin M) (synCtfin N)) p0034
  have freeVariableCertificate0 :
    b ∉ ((Wff.classMem (synCpw1 (.cv a)) (synCtfin M))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin, Finset.mem_union,
      Finset.mem_singleton, fresh_b_ne_a, fresh_b_not_M, or_false, not_false_eq_true]
  have freeVariableCertificate1 :
    a ∉ ((Wff.classMem (synCpw1 (.cv b)) (synCtfin N))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin, Finset.mem_union,
      Finset.mem_singleton, fresh_a_ne_b, fresh_a_not_N, or_false, not_false_eq_true]
  have p0036 :=
    @gReeanv (.classMem (synCpw1 (.cv a)) (synCtfin M))
      (.classMem (synCpw1 (.cv b)) (synCtfin N)) a b M N
      (by exact (show b ∉ (M).fv from (by exact fresh_b_not_M)))
      (by exact (show a ∉ (N).fv from (by exact fresh_a_not_N))) freeVariableCertificate0
      freeVariableCertificate1 (show a ≠ b from (by exact fresh_a_ne_b))
  have p0037 :=
    @gSimp31 (synWa (.classMem (.cv a) M) (.classMem (.cv b) N))
      (synWa (.classMem (synCpw1 (.cv a)) (synCtfin M))
        (.classMem (synCpw1 (.cv b)) (synCtfin N)))
      (.classMem M (synCnnc)) (.classMem N (synCnnc))
      (.classEq (synCtfin M) (synCtfin N))
  have p0038 := @gTfincl M
  have p0039 :=
    @gSyl
      (synW3a (synWa (.classMem (.cv a) M) (.classMem (.cv b) N))
        (synWa (.classMem (synCpw1 (.cv a)) (synCtfin M))
          (.classMem (synCpw1 (.cv b)) (synCtfin N)))
        (synW3a (.classMem M (synCnnc)) (.classMem N (synCnnc))
          (.classEq (synCtfin M) (synCtfin N))))
      (.classMem M (synCnnc)) (.classMem (synCtfin M) (synCnnc)) p0037 p0038
  have p0040 :=
    @gSimp2l (synWa (.classMem (.cv a) M) (.classMem (.cv b) N))
      (.classMem (synCpw1 (.cv a)) (synCtfin M))
      (.classMem (synCpw1 (.cv b)) (synCtfin N))
      (synW3a (.classMem M (synCnnc)) (.classMem N (synCnnc))
        (.classEq (synCtfin M) (synCtfin N)))
  have p0041 :=
    @gSimp2r (synWa (.classMem (.cv a) M) (.classMem (.cv b) N))
      (.classMem (synCpw1 (.cv a)) (synCtfin M))
      (.classMem (synCpw1 (.cv b)) (synCtfin N))
      (synW3a (.classMem M (synCnnc)) (.classMem N (synCnnc))
        (.classEq (synCtfin M) (synCtfin N)))
  have p0042 :=
    @gSimp33 (synWa (.classMem (.cv a) M) (.classMem (.cv b) N))
      (synWa (.classMem (synCpw1 (.cv a)) (synCtfin M))
        (.classMem (synCpw1 (.cv b)) (synCtfin N)))
      (.classMem M (synCnnc)) (.classMem N (synCnnc))
      (.classEq (synCtfin M) (synCtfin N))
  have p0043 :=
    @gEleqtrrd
      (synW3a (synWa (.classMem (.cv a) M) (.classMem (.cv b) N))
        (synWa (.classMem (synCpw1 (.cv a)) (synCtfin M))
          (.classMem (synCpw1 (.cv b)) (synCtfin N)))
        (synW3a (.classMem M (synCnnc)) (.classMem N (synCnnc))
          (.classEq (synCtfin M) (synCtfin N))))
      (synCpw1 (.cv b)) (synCtfin N) (synCtfin M) p0041 p0042
  have freeVariableCertificate2 : p ∉ ((Class.cv a)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_p_ne_a, not_false_eq_true]
  have freeVariableCertificate3 : p ∉ ((Class.cv b)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_p_ne_b, not_false_eq_true]
  have p0044 :=
    @gNcfinlower (.cv a) (.cv b) p (synCtfin M) freeVariableCertificate2
      freeVariableCertificate3
  have p0045_e03_recanon :
    Nominal.NPrf
      (.imp (synW3a (.classMem (synCtfin M) (synCnnc))
          (.classMem (synCpw1 (.cv a)) (synCtfin M))
          (.classMem (synCpw1 (.cv b)) (synCtfin M)))
        (synWrex p (synCnnc) (synWa (.objMem a p) (.objMem b p)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synW3a synWa synCtfin synCif synWo synC0 synCdif synCin synCcompl
          synCnin synWnan synCvv synCio synCuni synWex synCsn synCnnc synCint
          synCpw1 synWrex
        simp (config :=
          {
            failIfUnchanged :=
              false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa]
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
      p0044
  have p0045 :=
    @gSyl3anc
      (synW3a (synWa (.classMem (.cv a) M) (.classMem (.cv b) N))
        (synWa (.classMem (synCpw1 (.cv a)) (synCtfin M))
          (.classMem (synCpw1 (.cv b)) (synCtfin N)))
        (synW3a (.classMem M (synCnnc)) (.classMem N (synCnnc))
          (.classEq (synCtfin M) (synCtfin N))))
      (.classMem (synCtfin M) (synCnnc)) (.classMem (synCpw1 (.cv a)) (synCtfin M))
      (.classMem (synCpw1 (.cv b)) (synCtfin M))
      (synWrex p (synCnnc) (synWa (.objMem a p) (.objMem b p))) p0039 p0040 p0043
      p0045_e03_recanon
  have p0046 :=
    @gSimpl31 (.classMem M (synCnnc)) (.classMem N (synCnnc))
      (.classEq (synCtfin M) (synCtfin N))
      (synWa (.classMem (.cv a) M) (.classMem (.cv b) N))
      (synWa (.classMem (synCpw1 (.cv a)) (synCtfin M))
        (.classMem (synCpw1 (.cv b)) (synCtfin N)))
      (synWa (.classMem (.cv p) (synCnnc)) (synWa (.objMem a p) (.objMem b p)))
  have p0047 :=
    @gSimprl
      (synW3a (synWa (.classMem (.cv a) M) (.classMem (.cv b) N))
        (synWa (.classMem (synCpw1 (.cv a)) (synCtfin M))
          (.classMem (synCpw1 (.cv b)) (synCtfin N)))
        (synW3a (.classMem M (synCnnc)) (.classMem N (synCnnc))
          (.classEq (synCtfin M) (synCtfin N))))
      (.classMem (.cv p) (synCnnc)) (synWa (.objMem a p) (.objMem b p))
  have p0048 :=
    @gSimpl1l (.classMem (.cv a) M) (.classMem (.cv b) N)
      (synWa (.classMem (synCpw1 (.cv a)) (synCtfin M))
        (.classMem (synCpw1 (.cv b)) (synCtfin N)))
      (synW3a (.classMem M (synCnnc)) (.classMem N (synCnnc))
        (.classEq (synCtfin M) (synCtfin N)))
      (synWa (.classMem (.cv p) (synCnnc)) (synWa (.objMem a p) (.objMem b p)))
  have p0049 :=
    @gSimprrl
      (synW3a (synWa (.classMem (.cv a) M) (.classMem (.cv b) N))
        (synWa (.classMem (synCpw1 (.cv a)) (synCtfin M))
          (.classMem (synCpw1 (.cv b)) (synCtfin N)))
        (synW3a (.classMem M (synCnnc)) (.classMem N (synCnnc))
          (.classEq (synCtfin M) (synCtfin N))))
      (.classMem (.cv p) (synCnnc)) (.objMem a p) (.objMem b p)
  have p0050 := @gNnceleq (.cv a) M (.cv p)
  have p0051_e04_recanon :
    Nominal.NPrf
      (.imp (synWa (synWa (.classMem M (synCnnc)) (.classMem (.cv p) (synCnnc)))
          (synWa (.classMem (.cv a) M) (.objMem a p))) (.classEq M (.cv p))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWa
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0050
  have p0051 :=
    @gSyl22anc
      (synWa (synW3a (synWa (.classMem (.cv a) M) (.classMem (.cv b) N))
          (synWa (.classMem (synCpw1 (.cv a)) (synCtfin M))
            (.classMem (synCpw1 (.cv b)) (synCtfin N)))
          (synW3a (.classMem M (synCnnc)) (.classMem N (synCnnc))
            (.classEq (synCtfin M) (synCtfin N))))
        (synWa (.classMem (.cv p) (synCnnc)) (synWa (.objMem a p) (.objMem b p))))
      (.classMem M (synCnnc)) (.classMem (.cv p) (synCnnc)) (.classMem (.cv a) M)
      (.objMem a p) (.classEq M (.cv p)) p0046 p0047 p0048 p0049 p0051_e04_recanon
  have p0052 :=
    @gSimpl32 (.classMem M (synCnnc)) (.classMem N (synCnnc))
      (.classEq (synCtfin M) (synCtfin N))
      (synWa (.classMem (.cv a) M) (.classMem (.cv b) N))
      (synWa (.classMem (synCpw1 (.cv a)) (synCtfin M))
        (.classMem (synCpw1 (.cv b)) (synCtfin N)))
      (synWa (.classMem (.cv p) (synCnnc)) (synWa (.objMem a p) (.objMem b p)))
  have p0053 :=
    @gSimpl1r (.classMem (.cv a) M) (.classMem (.cv b) N)
      (synWa (.classMem (synCpw1 (.cv a)) (synCtfin M))
        (.classMem (synCpw1 (.cv b)) (synCtfin N)))
      (synW3a (.classMem M (synCnnc)) (.classMem N (synCnnc))
        (.classEq (synCtfin M) (synCtfin N)))
      (synWa (.classMem (.cv p) (synCnnc)) (synWa (.objMem a p) (.objMem b p)))
  have p0054 :=
    @gSimprrr
      (synW3a (synWa (.classMem (.cv a) M) (.classMem (.cv b) N))
        (synWa (.classMem (synCpw1 (.cv a)) (synCtfin M))
          (.classMem (synCpw1 (.cv b)) (synCtfin N)))
        (synW3a (.classMem M (synCnnc)) (.classMem N (synCnnc))
          (.classEq (synCtfin M) (synCtfin N))))
      (.classMem (.cv p) (synCnnc)) (.objMem a p) (.objMem b p)
  have p0055 := @gNnceleq (.cv b) N (.cv p)
  have p0056_e04_recanon :
    Nominal.NPrf
      (.imp (synWa (synWa (.classMem N (synCnnc)) (.classMem (.cv p) (synCnnc)))
          (synWa (.classMem (.cv b) N) (.objMem b p))) (.classEq N (.cv p))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWa
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0055
  have p0056 :=
    @gSyl22anc
      (synWa (synW3a (synWa (.classMem (.cv a) M) (.classMem (.cv b) N))
          (synWa (.classMem (synCpw1 (.cv a)) (synCtfin M))
            (.classMem (synCpw1 (.cv b)) (synCtfin N)))
          (synW3a (.classMem M (synCnnc)) (.classMem N (synCnnc))
            (.classEq (synCtfin M) (synCtfin N))))
        (synWa (.classMem (.cv p) (synCnnc)) (synWa (.objMem a p) (.objMem b p))))
      (.classMem N (synCnnc)) (.classMem (.cv p) (synCnnc)) (.classMem (.cv b) N)
      (.objMem b p) (.classEq N (.cv p)) p0052 p0047 p0053 p0054 p0056_e04_recanon
  have p0057 :=
    @gEqtr4d
      (synWa (synW3a (synWa (.classMem (.cv a) M) (.classMem (.cv b) N))
          (synWa (.classMem (synCpw1 (.cv a)) (synCtfin M))
            (.classMem (synCpw1 (.cv b)) (synCtfin N)))
          (synW3a (.classMem M (synCnnc)) (.classMem N (synCnnc))
            (.classEq (synCtfin M) (synCtfin N))))
        (synWa (.classMem (.cv p) (synCnnc)) (synWa (.objMem a p) (.objMem b p))))
      M (.cv p) N p0051 p0056
  have p0058 :=
    @gExpr
      (synW3a (synWa (.classMem (.cv a) M) (.classMem (.cv b) N))
        (synWa (.classMem (synCpw1 (.cv a)) (synCtfin M))
          (.classMem (synCpw1 (.cv b)) (synCtfin N)))
        (synW3a (.classMem M (synCnnc)) (.classMem N (synCnnc))
          (.classEq (synCtfin M) (synCtfin N))))
      (.classMem (.cv p) (synCnnc)) (synWa (.objMem a p) (.objMem b p)) (.classEq M N)
      p0057
  have freeVariableCertificate4 : p ∉ ((Wff.classEq M N)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union,
      fresh_p_not_M, fresh_p_not_N, or_false, not_false_eq_true]
  have freeVariableCertificate5 :
    p ∉
      ((synW3a (synWa (.classMem (.cv a) M) (.classMem (.cv b) N))
          (synWa (.classMem (synCpw1 (.cv a)) (synCtfin M))
            (.classMem (synCpw1 (.cv b)) (synCtfin N)))
          (synW3a (.classMem M (synCnnc)) (.classMem N (synCnnc))
            (.classEq (synCtfin M) (synCtfin N))))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_p_not_M, fresh_p_not_N,
      fresh_p_ne_a, fresh_p_ne_b, or_false, not_false_eq_true]
  have p0059 :=
    @gRexlimdva
      (synW3a (synWa (.classMem (.cv a) M) (.classMem (.cv b) N))
        (synWa (.classMem (synCpw1 (.cv a)) (synCtfin M))
          (.classMem (synCpw1 (.cv b)) (synCtfin N)))
        (synW3a (.classMem M (synCnnc)) (.classMem N (synCnnc))
          (.classEq (synCtfin M) (synCtfin N))))
      (synWa (.objMem a p) (.objMem b p)) (.classEq M N) p (synCnnc)
      freeVariableCertificate4 freeVariableCertificate5 p0058
  have p0060 :=
    @gMpd
      (synW3a (synWa (.classMem (.cv a) M) (.classMem (.cv b) N))
        (synWa (.classMem (synCpw1 (.cv a)) (synCtfin M))
          (.classMem (synCpw1 (.cv b)) (synCtfin N)))
        (synW3a (.classMem M (synCnnc)) (.classMem N (synCnnc))
          (.classEq (synCtfin M) (synCtfin N))))
      (synWrex p (synCnnc) (synWa (.objMem a p) (.objMem b p))) (.classEq M N) p0045
      p0059
  have p0061 :=
    @gN3exp (synWa (.classMem (.cv a) M) (.classMem (.cv b) N))
      (synWa (.classMem (synCpw1 (.cv a)) (synCtfin M))
        (.classMem (synCpw1 (.cv b)) (synCtfin N)))
      (synW3a (.classMem M (synCnnc)) (.classMem N (synCnnc))
        (.classEq (synCtfin M) (synCtfin N)))
      (.classEq M N) p0060
  have freeVariableCertificate6 :
    a ∉
      ((Wff.imp (synW3a (.classMem M (synCnnc)) (.classMem N (synCnnc))
            (.classEq (synCtfin M) (synCtfin N))) (.classEq M N))).fv :=
    by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union,
      Finset.notMem_empty, fresh_a_not_M, fresh_a_not_N, or_false, not_false_eq_true]
  have freeVariableCertificate7 :
    b ∉
      ((Wff.imp (synW3a (.classMem M (synCnnc)) (.classMem N (synCnnc))
            (.classEq (synCtfin M) (synCtfin N))) (.classEq M N))).fv :=
    by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union,
      Finset.notMem_empty, fresh_b_not_M, fresh_b_not_N, or_false, not_false_eq_true]
  have p0062 :=
    @gRexlimivv
      (synWa (.classMem (synCpw1 (.cv a)) (synCtfin M))
        (.classMem (synCpw1 (.cv b)) (synCtfin N)))
      (.imp (synW3a (.classMem M (synCnnc)) (.classMem N (synCnnc))
          (.classEq (synCtfin M) (synCtfin N))) (.classEq M N))
      a b M N (by exact (show b ∉ (M).fv from (by exact fresh_b_not_M)))
      freeVariableCertificate6 freeVariableCertificate7
      (show a ≠ b from (by exact fresh_a_ne_b)) p0061
  have p0063 :=
    @gSylbir
      (synWa (synWrex a M (.classMem (synCpw1 (.cv a)) (synCtfin M)))
        (synWrex b N (.classMem (synCpw1 (.cv b)) (synCtfin N))))
      (synWrex a M (synWrex b N (synWa (.classMem (synCpw1 (.cv a)) (synCtfin M))
            (.classMem (synCpw1 (.cv b)) (synCtfin N)))))
      (.imp (synW3a (.classMem M (synCnnc)) (.classMem N (synCnnc))
          (.classEq (synCtfin M) (synCtfin N))) (.classEq M N))
      p0036 p0062
  have p0064 :=
    @gAd2ant2l (synWrex a M (.classMem (synCpw1 (.cv a)) (synCtfin M)))
      (synWrex b N (.classMem (synCpw1 (.cv b)) (synCtfin N)))
      (.imp (synW3a (.classMem M (synCnnc)) (.classMem N (synCnnc))
          (.classEq (synCtfin M) (synCtfin N))) (.classEq M N))
      (.classMem (synCtfin M) (synCnnc)) (.classMem (synCtfin N) (synCnnc)) p0063
  have p0065 :=
    @gCom12
      (synWa (synWa (.classMem (synCtfin M) (synCnnc))
          (synWrex a M (.classMem (synCpw1 (.cv a)) (synCtfin M))))
        (synWa (.classMem (synCtfin N) (synCnnc))
          (synWrex b N (.classMem (synCpw1 (.cv b)) (synCtfin N)))))
      (synW3a (.classMem M (synCnnc)) (.classMem N (synCnnc))
        (.classEq (synCtfin M) (synCtfin N)))
      (.classEq M N) p0064
  have p0066 :=
    @gSyl2and
      (synW3a (.classMem M (synCnnc)) (.classMem N (synCnnc))
        (.classEq (synCtfin M) (synCtfin N)))
      (synWne M (synC0))
      (synWa (.classMem (synCtfin M) (synCnnc))
        (synWrex a M (.classMem (synCpw1 (.cv a)) (synCtfin M))))
      (synWne N (synC0))
      (synWa (.classMem (synCtfin N) (synCnnc))
        (synWrex b N (.classMem (synCpw1 (.cv b)) (synCtfin N))))
      (.classEq M N) p0032 p0035 p0065
  have p0067 :=
    @gSyld
      (synW3a (.classMem M (synCnnc)) (.classMem N (synCnnc))
        (.classEq (synCtfin M) (synCtfin N)))
      (synWne (synCtfin M) (synC0)) (synWa (synWne M (synC0)) (synWne N (synC0)))
      (.classEq M N) p0029 p0066
  have p0068 :=
    @gCom12
      (synW3a (.classMem M (synCnnc)) (.classMem N (synCnnc))
        (.classEq (synCtfin M) (synCtfin N)))
      (synWne (synCtfin M) (synC0)) (.classEq M N) p0067
  have p0069 :=
    @gPm261ine
      (.imp (synW3a (.classMem M (synCnnc)) (.classMem N (synCnnc))
          (.classEq (synCtfin M) (synCtfin N))) (.classEq M N))
      (synCtfin M) (synC0) p0015 p0068
  exact p0069

/-- Checked nominal proof certificate identified upstream as `g_tfinpw1`. -/
@[expose]
noncomputable def gTfinpw1 (A : Class) (M : Class) :
    Nominal.NPrf
      (.imp (synWa (.classMem M (synCnnc)) (.classMem A M))
        (.classMem (synCpw1 A) (synCtfin M))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ M.fv
  let b : Var := freshVar proofSupport 0
  let n : Var := freshVar proofSupport 1
  have fresh_b : b ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_b_not_A : b ∉ A.fv := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (h))
  have fresh_b_not_M : b ∉ M.fv := by
    intro h
    exact fresh_b (Finset.mem_union_right _ (h))
  have fresh_n : n ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_n_not_A : n ∉ A.fv := by
    intro h
    exact fresh_n (Finset.mem_union_left _ (h))
  have fresh_n_not_M : n ∉ M.fv := by
    intro h
    exact fresh_n (Finset.mem_union_right _ (h))
  have fresh_b_ne_n : b ≠ n :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_n_ne_b : n ≠ b := Ne.symm fresh_b_ne_n
  have p0000 := @gNe0i M A
  have p0001 := @gTfinprop M b (by exact (show b ∉ (M).fv from (by exact fresh_b_not_M)))
  have p0002 :=
    @gSylan2 (.classMem A M) (.classMem M (synCnnc)) (synWne M (synC0))
      (synWa (.classMem (synCtfin M) (synCnnc))
        (synWrex b M (.classMem (synCpw1 (.cv b)) (synCtfin M))))
      p0000 p0001
  have freeVariableCertificate0 : n ∉ ((Class.cv b)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_n_ne_b, not_false_eq_true]
  have p0003 :=
    @gNcfinraise A (.cv b) n M (by exact (show n ∉ (A).fv from (by exact fresh_n_not_A)))
      freeVariableCertificate0
  have p0004 :=
    @gN3expa (.classMem M (synCnnc)) (.classMem A M) (.classMem (.cv b) M)
      (synWrex n (synCnnc)
        (synWa (.classMem (synCpw1 A) (.cv n)) (.classMem (synCpw1 (.cv b)) (.cv n))))
      p0003
  have p0005 :=
    @gAdantrr (synWa (.classMem M (synCnnc)) (.classMem A M)) (.classMem (.cv b) M)
      (synWrex n (synCnnc)
        (synWa (.classMem (synCpw1 A) (.cv n)) (.classMem (synCpw1 (.cv b)) (.cv n))))
      (.classMem (synCpw1 (.cv b)) (synCtfin M)) p0004
  have p0006 :=
    @gSimp3rl (.classMem (synCpw1 A) (.cv n)) (.classMem (synCpw1 (.cv b)) (.cv n))
      (.classMem (.cv n) (synCnnc)) (synWa (.classMem M (synCnnc)) (.classMem A M))
      (synWa (.classMem (.cv b) M) (.classMem (synCpw1 (.cv b)) (synCtfin M)))
  have p0007 :=
    @gSimp3l (synWa (.classMem M (synCnnc)) (.classMem A M))
      (synWa (.classMem (.cv b) M) (.classMem (synCpw1 (.cv b)) (synCtfin M)))
      (.classMem (.cv n) (synCnnc))
      (synWa (.classMem (synCpw1 A) (.cv n)) (.classMem (synCpw1 (.cv b)) (.cv n)))
  have p0008 :=
    @gSimp1l (.classMem M (synCnnc)) (.classMem A M)
      (synWa (.classMem (.cv b) M) (.classMem (synCpw1 (.cv b)) (synCtfin M)))
      (synWa (.classMem (.cv n) (synCnnc))
        (synWa (.classMem (synCpw1 A) (.cv n)) (.classMem (synCpw1 (.cv b)) (.cv n))))
  have p0009 := @gTfincl M
  have p0010 :=
    @gSyl
      (synW3a (synWa (.classMem M (synCnnc)) (.classMem A M))
        (synWa (.classMem (.cv b) M) (.classMem (synCpw1 (.cv b)) (synCtfin M)))
        (synWa (.classMem (.cv n) (synCnnc)) (synWa (.classMem (synCpw1 A) (.cv n))
            (.classMem (synCpw1 (.cv b)) (.cv n)))))
      (.classMem M (synCnnc)) (.classMem (synCtfin M) (synCnnc)) p0008 p0009
  have p0011 :=
    @gSimp3rr (.classMem (synCpw1 A) (.cv n)) (.classMem (synCpw1 (.cv b)) (.cv n))
      (.classMem (.cv n) (synCnnc)) (synWa (.classMem M (synCnnc)) (.classMem A M))
      (synWa (.classMem (.cv b) M) (.classMem (synCpw1 (.cv b)) (synCtfin M)))
  have p0012 :=
    @gSimp2r (synWa (.classMem M (synCnnc)) (.classMem A M)) (.classMem (.cv b) M)
      (.classMem (synCpw1 (.cv b)) (synCtfin M))
      (synWa (.classMem (.cv n) (synCnnc))
        (synWa (.classMem (synCpw1 A) (.cv n)) (.classMem (synCpw1 (.cv b)) (.cv n))))
  have p0013 := @gNnceleq (synCpw1 (.cv b)) (.cv n) (synCtfin M)
  have p0014 :=
    @gSyl22anc
      (synW3a (synWa (.classMem M (synCnnc)) (.classMem A M))
        (synWa (.classMem (.cv b) M) (.classMem (synCpw1 (.cv b)) (synCtfin M)))
        (synWa (.classMem (.cv n) (synCnnc)) (synWa (.classMem (synCpw1 A) (.cv n))
            (.classMem (synCpw1 (.cv b)) (.cv n)))))
      (.classMem (.cv n) (synCnnc)) (.classMem (synCtfin M) (synCnnc))
      (.classMem (synCpw1 (.cv b)) (.cv n)) (.classMem (synCpw1 (.cv b)) (synCtfin M))
      (.classEq (.cv n) (synCtfin M)) p0007 p0010 p0011 p0012 p0013
  have p0015 :=
    @gEleqtrd
      (synW3a (synWa (.classMem M (synCnnc)) (.classMem A M))
        (synWa (.classMem (.cv b) M) (.classMem (synCpw1 (.cv b)) (synCtfin M)))
        (synWa (.classMem (.cv n) (synCnnc)) (synWa (.classMem (synCpw1 A) (.cv n))
            (.classMem (synCpw1 (.cv b)) (.cv n)))))
      (synCpw1 A) (.cv n) (synCtfin M) p0006 p0014
  have p0016 :=
    @gN3expa (synWa (.classMem M (synCnnc)) (.classMem A M))
      (synWa (.classMem (.cv b) M) (.classMem (synCpw1 (.cv b)) (synCtfin M)))
      (synWa (.classMem (.cv n) (synCnnc))
        (synWa (.classMem (synCpw1 A) (.cv n)) (.classMem (synCpw1 (.cv b)) (.cv n))))
      (.classMem (synCpw1 A) (synCtfin M)) p0015
  have p0017 :=
    @gExpr
      (synWa (synWa (.classMem M (synCnnc)) (.classMem A M))
        (synWa (.classMem (.cv b) M) (.classMem (synCpw1 (.cv b)) (synCtfin M))))
      (.classMem (.cv n) (synCnnc))
      (synWa (.classMem (synCpw1 A) (.cv n)) (.classMem (synCpw1 (.cv b)) (.cv n)))
      (.classMem (synCpw1 A) (synCtfin M)) p0016
  have freeVariableCertificate1 : n ∉ ((Wff.classMem (synCpw1 A) (synCtfin M))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin, Finset.mem_union,
      fresh_n_not_A, fresh_n_not_M, or_false, not_false_eq_true]
  have freeVariableCertificate2 :
    n ∉
      ((synWa (synWa (.classMem M (synCnnc)) (.classMem A M)) (synWa (.classMem (.cv b) M)
            (.classMem (synCpw1 (.cv b)) (synCtfin M))))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_n_not_M, fresh_n_not_A,
      fresh_n_ne_b, or_false, not_false_eq_true]
  have p0018 :=
    @gRexlimdva
      (synWa (synWa (.classMem M (synCnnc)) (.classMem A M))
        (synWa (.classMem (.cv b) M) (.classMem (synCpw1 (.cv b)) (synCtfin M))))
      (synWa (.classMem (synCpw1 A) (.cv n)) (.classMem (synCpw1 (.cv b)) (.cv n)))
      (.classMem (synCpw1 A) (synCtfin M)) n (synCnnc) freeVariableCertificate1
      freeVariableCertificate2 p0017
  have p0019 :=
    @gMpd
      (synWa (synWa (.classMem M (synCnnc)) (.classMem A M))
        (synWa (.classMem (.cv b) M) (.classMem (synCpw1 (.cv b)) (synCtfin M))))
      (synWrex n (synCnnc)
        (synWa (.classMem (synCpw1 A) (.cv n)) (.classMem (synCpw1 (.cv b)) (.cv n))))
      (.classMem (synCpw1 A) (synCtfin M)) p0005 p0018
  have p0020 :=
    @gExpr (synWa (.classMem M (synCnnc)) (.classMem A M)) (.classMem (.cv b) M)
      (.classMem (synCpw1 (.cv b)) (synCtfin M)) (.classMem (synCpw1 A) (synCtfin M))
      p0019
  have freeVariableCertificate3 : b ∉ ((Wff.classMem (synCpw1 A) (synCtfin M))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin, Finset.mem_union,
      fresh_b_not_A, fresh_b_not_M, or_false, not_false_eq_true]
  have freeVariableCertificate4 :
    b ∉ ((synWa (.classMem M (synCnnc)) (.classMem A M))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union,
      Finset.notMem_empty, fresh_b_not_M, fresh_b_not_A, or_false, not_false_eq_true]
  have p0021 :=
    @gRexlimdva (synWa (.classMem M (synCnnc)) (.classMem A M))
      (.classMem (synCpw1 (.cv b)) (synCtfin M)) (.classMem (synCpw1 A) (synCtfin M))
      b M freeVariableCertificate3 freeVariableCertificate4 p0020
  have p0022 :=
    @gAdantld (synWa (.classMem M (synCnnc)) (.classMem A M))
      (synWrex b M (.classMem (synCpw1 (.cv b)) (synCtfin M)))
      (.classMem (synCpw1 A) (synCtfin M)) (.classMem (synCtfin M) (synCnnc)) p0021
  have p0023 :=
    @gMpd (synWa (.classMem M (synCnnc)) (.classMem A M))
      (synWa (.classMem (synCtfin M) (synCnnc))
        (synWrex b M (.classMem (synCpw1 (.cv b)) (synCtfin M))))
      (.classMem (synCpw1 A) (synCtfin M)) p0002 p0022
  exact p0023

/-- Checked nominal proof certificate identified upstream as `g_ncfintfin`. -/
@[expose]
noncomputable def gNcfintfin (A : Class) (V : Class) :
    Nominal.NPrf
      (.imp (synWa (.classMem (synCvv) (synCfin)) (.classMem A V))
        (.classEq (synCtfin (synCncfin A)) (synCncfin (synCpw1 A)))) :=
  by
  have p0000 := @gNcfinprop A V
  have p0001 :=
    @gSimpld (synWa (.classMem (synCvv) (synCfin)) (.classMem A V))
      (.classMem (synCncfin A) (synCnnc)) (.classMem A (synCncfin A)) p0000
  have p0002 := @gTfincl (synCncfin A)
  have p0003 :=
    @gSyl (synWa (.classMem (synCvv) (synCfin)) (.classMem A V))
      (.classMem (synCncfin A) (synCnnc))
      (.classMem (synCtfin (synCncfin A)) (synCnnc)) p0001 p0002
  have p0004 := @gPw1exg A V
  have p0005 := @gNcfinprop (synCpw1 A) (synCvv)
  have p0006 :=
    @gSylan2 (.classMem A V) (.classMem (synCvv) (synCfin))
      (.classMem (synCpw1 A) (synCvv))
      (synWa (.classMem (synCncfin (synCpw1 A)) (synCnnc))
        (.classMem (synCpw1 A) (synCncfin (synCpw1 A))))
      p0004 p0005
  have p0007 :=
    @gSimpld (synWa (.classMem (synCvv) (synCfin)) (.classMem A V))
      (.classMem (synCncfin (synCpw1 A)) (synCnnc))
      (.classMem (synCpw1 A) (synCncfin (synCpw1 A))) p0006
  have p0008 := @gTfinpw1 A (synCncfin A)
  have p0009 :=
    @gSyl (synWa (.classMem (synCvv) (synCfin)) (.classMem A V))
      (synWa (.classMem (synCncfin A) (synCnnc)) (.classMem A (synCncfin A)))
      (.classMem (synCpw1 A) (synCtfin (synCncfin A))) p0000 p0008
  have p0010 :=
    @gSimprd (synWa (.classMem (synCvv) (synCfin)) (.classMem A V))
      (.classMem (synCncfin (synCpw1 A)) (synCnnc))
      (.classMem (synCpw1 A) (synCncfin (synCpw1 A))) p0006
  have p0011 :=
    @gNnceleq (synCpw1 A) (synCtfin (synCncfin A)) (synCncfin (synCpw1 A))
  have p0012 :=
    @gSyl22anc (synWa (.classMem (synCvv) (synCfin)) (.classMem A V))
      (.classMem (synCtfin (synCncfin A)) (synCnnc))
      (.classMem (synCncfin (synCpw1 A)) (synCnnc))
      (.classMem (synCpw1 A) (synCtfin (synCncfin A)))
      (.classMem (synCpw1 A) (synCncfin (synCpw1 A)))
      (.classEq (synCtfin (synCncfin A)) (synCncfin (synCpw1 A))) p0003 p0007 p0009
      p0010 p0011
  exact p0012


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk009StructuralPart056`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_tfindi`. -/
@[expose]
noncomputable def gTfindi (M : Class) (N : Class) :
    Nominal.NPrf
      (.imp (synW3a (.classMem M (synCnnc)) (.classMem N (synCnnc))
          (synWne (synCplc M N) (synC0)))
        (.classEq (synCtfin (synCplc M N)) (synCplc (synCtfin M) (synCtfin N)))) :=
  by
  let proofSupport : Finset Var := M.fv ∪ N.fv
  let a : Var := freshVar proofSupport 0
  let b : Var := freshVar proofSupport 1
  let c : Var := freshVar proofSupport 2
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
  have fresh_c : c ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_c_not_M : c ∉ M.fv := by
    intro h
    exact fresh_c (Finset.mem_union_left _ (h))
  have fresh_c_not_N : c ∉ N.fv := by
    intro h
    exact fresh_c (Finset.mem_union_right _ (h))
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
  have freeVariableCertificate0 : a ∉ ((synCplc M N)).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, Finset.mem_union,
      fresh_a_not_M, fresh_a_not_N, or_false, not_false_eq_true]
  have p0000 := @gN0 a (synCplc M N) freeVariableCertificate0
  have p0001 := @gNncaddccl M N
  have p0002 := @gTfincl (synCplc M N)
  have p0003 :=
    @gSyl (synWa (.classMem M (synCnnc)) (.classMem N (synCnnc)))
      (.classMem (synCplc M N) (synCnnc))
      (.classMem (synCtfin (synCplc M N)) (synCnnc)) p0001 p0002
  have p0004 :=
    @gN3adant3 (.classMem M (synCnnc)) (.classMem N (synCnnc))
      (.classMem (synCtfin (synCplc M N)) (synCnnc)) (.classMem (.cv a) (synCplc M N))
      p0003
  have p0005 := @gTfincl M
  have p0006 := @gTfincl N
  have p0007 := @gNncaddccl (synCtfin M) (synCtfin N)
  have p0008 :=
    @gSyl2an (.classMem M (synCnnc)) (.classMem (synCtfin M) (synCnnc))
      (.classMem (synCtfin N) (synCnnc))
      (.classMem (synCplc (synCtfin M) (synCtfin N)) (synCnnc))
      (.classMem N (synCnnc)) p0005 p0006 p0007
  have p0009 :=
    @gN3adant3 (.classMem M (synCnnc)) (.classMem N (synCnnc))
      (.classMem (synCplc (synCtfin M) (synCtfin N)) (synCnnc))
      (.classMem (.cv a) (synCplc M N)) p0008
  have p0010 :=
    @gN3adant3 (.classMem M (synCnnc)) (.classMem N (synCnnc))
      (.classMem (synCplc M N) (synCnnc)) (.classMem (.cv a) (synCplc M N)) p0001
  have p0011 :=
    @gSimp3 (.classMem M (synCnnc)) (.classMem N (synCnnc))
      (.classMem (.cv a) (synCplc M N))
  have p0012 := @gTfinpw1 (.cv a) (synCplc M N)
  have p0013 :=
    @gSyl2anc
      (synW3a (.classMem M (synCnnc)) (.classMem N (synCnnc))
        (.classMem (.cv a) (synCplc M N)))
      (.classMem (synCplc M N) (synCnnc)) (.classMem (.cv a) (synCplc M N))
      (.classMem (synCpw1 (.cv a)) (synCtfin (synCplc M N))) p0010 p0011 p0012
  have freeVariableCertificate1 : b ∉ ((Class.cv a)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_b_ne_a, not_false_eq_true]
  have freeVariableCertificate2 : c ∉ ((Class.cv a)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_c_ne_a, not_false_eq_true]
  have p0014 :=
    @gEladdc (.cv a) M N b c freeVariableCertificate1 freeVariableCertificate2
      (by exact (show b ∉ (M).fv from (by exact fresh_b_not_M)))
      (by exact (show c ∉ (M).fv from (by exact fresh_c_not_M)))
      (by exact (show b ∉ (N).fv from (by exact fresh_b_not_N)))
      (by exact (show c ∉ (N).fv from (by exact fresh_c_not_N)))
      (show b ≠ c from (by exact fresh_b_ne_c))
  have p0015 :=
    @gSimplll (.classMem M (synCnnc)) (.classMem N (synCnnc))
      (synWa (.classMem (.cv b) M) (.classMem (.cv c) N))
      (.classEq (synCin (.cv b) (.cv c)) (synC0))
  have p0016 :=
    @gSimplrl (synWa (.classMem M (synCnnc)) (.classMem N (synCnnc)))
      (.classMem (.cv b) M) (.classMem (.cv c) N)
      (.classEq (synCin (.cv b) (.cv c)) (synC0))
  have p0017 := @gTfinpw1 (.cv b) M
  have p0018 :=
    @gSyl2anc
      (synWa (synWa (synWa (.classMem M (synCnnc)) (.classMem N (synCnnc)))
          (synWa (.classMem (.cv b) M) (.classMem (.cv c) N)))
        (.classEq (synCin (.cv b) (.cv c)) (synC0)))
      (.classMem M (synCnnc)) (.classMem (.cv b) M)
      (.classMem (synCpw1 (.cv b)) (synCtfin M)) p0015 p0016 p0017
  have p0019 :=
    @gSimpllr (.classMem M (synCnnc)) (.classMem N (synCnnc))
      (synWa (.classMem (.cv b) M) (.classMem (.cv c) N))
      (.classEq (synCin (.cv b) (.cv c)) (synC0))
  have p0020 :=
    @gSimplrr (synWa (.classMem M (synCnnc)) (.classMem N (synCnnc)))
      (.classMem (.cv b) M) (.classMem (.cv c) N)
      (.classEq (synCin (.cv b) (.cv c)) (synC0))
  have p0021 := @gTfinpw1 (.cv c) N
  have p0022 :=
    @gSyl2anc
      (synWa (synWa (synWa (.classMem M (synCnnc)) (.classMem N (synCnnc)))
          (synWa (.classMem (.cv b) M) (.classMem (.cv c) N)))
        (.classEq (synCin (.cv b) (.cv c)) (synC0)))
      (.classMem N (synCnnc)) (.classMem (.cv c) N)
      (.classMem (synCpw1 (.cv c)) (synCtfin N)) p0019 p0020 p0021
  have p0023 := @gPw1eq (synCin (.cv b) (.cv c)) (synC0)
  have p0024 := @gPw1in (.cv b) (.cv c)
  have p0025 := @gPw10
  have p0026 :=
    @gN3eqtr3g (.classEq (synCin (.cv b) (.cv c)) (synC0))
      (synCpw1 (synCin (.cv b) (.cv c))) (synCpw1 (synC0))
      (synCin (synCpw1 (.cv b)) (synCpw1 (.cv c))) (synC0) p0023 p0024 p0025
  have p0027 :=
    @gAdantl (.classEq (synCin (.cv b) (.cv c)) (synC0))
      (.classEq (synCin (synCpw1 (.cv b)) (synCpw1 (.cv c))) (synC0))
      (synWa (synWa (.classMem M (synCnnc)) (.classMem N (synCnnc)))
        (synWa (.classMem (.cv b) M) (.classMem (.cv c) N)))
      p0026
  have p0028 :=
    @gEladdci (synCpw1 (.cv b)) (synCpw1 (.cv c)) (synCtfin M) (synCtfin N)
  have p0029 :=
    @gSyl3anc
      (synWa (synWa (synWa (.classMem M (synCnnc)) (.classMem N (synCnnc)))
          (synWa (.classMem (.cv b) M) (.classMem (.cv c) N)))
        (.classEq (synCin (.cv b) (.cv c)) (synC0)))
      (.classMem (synCpw1 (.cv b)) (synCtfin M))
      (.classMem (synCpw1 (.cv c)) (synCtfin N))
      (.classEq (synCin (synCpw1 (.cv b)) (synCpw1 (.cv c))) (synC0))
      (.classMem (synCun (synCpw1 (.cv b)) (synCpw1 (.cv c)))
        (synCplc (synCtfin M) (synCtfin N)))
      p0018 p0022 p0027 p0028
  have p0030 := @gPw1eq (.cv a) (synCun (.cv b) (.cv c))
  have p0031 := @gPw1un (.cv b) (.cv c)
  have p0032 :=
    @gSyl6eq (.classEq (.cv a) (synCun (.cv b) (.cv c))) (synCpw1 (.cv a))
      (synCpw1 (synCun (.cv b) (.cv c))) (synCun (synCpw1 (.cv b)) (synCpw1 (.cv c)))
      p0030 p0031
  have p0033 :=
    @gEleq1d (.classEq (.cv a) (synCun (.cv b) (.cv c))) (synCpw1 (.cv a))
      (synCun (synCpw1 (.cv b)) (synCpw1 (.cv c)))
      (synCplc (synCtfin M) (synCtfin N)) p0032
  have p0034 :=
    @gSyl5ibrcom
      (synWa (synWa (synWa (.classMem M (synCnnc)) (.classMem N (synCnnc)))
          (synWa (.classMem (.cv b) M) (.classMem (.cv c) N)))
        (.classEq (synCin (.cv b) (.cv c)) (synC0)))
      (.classMem (synCpw1 (.cv a)) (synCplc (synCtfin M) (synCtfin N)))
      (.classEq (.cv a) (synCun (.cv b) (.cv c)))
      (.classMem (synCun (synCpw1 (.cv b)) (synCpw1 (.cv c)))
        (synCplc (synCtfin M) (synCtfin N)))
      p0029 p0033
  have p0035 :=
    @gExpimpd
      (synWa (synWa (.classMem M (synCnnc)) (.classMem N (synCnnc)))
        (synWa (.classMem (.cv b) M) (.classMem (.cv c) N)))
      (.classEq (synCin (.cv b) (.cv c)) (synC0))
      (.classEq (.cv a) (synCun (.cv b) (.cv c)))
      (.classMem (synCpw1 (.cv a)) (synCplc (synCtfin M) (synCtfin N))) p0034
  have freeVariableCertificate3 :
    b ∉ ((Wff.classMem (synCpw1 (.cv a)) (synCplc (synCtfin M) (synCtfin N)))).fv :=
    by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin, Finset.mem_union,
      Finset.mem_singleton, fresh_b_ne_a, fresh_b_not_M, fresh_b_not_N, or_false,
      not_false_eq_true]
  have freeVariableCertificate4 :
    c ∉ ((Wff.classMem (synCpw1 (.cv a)) (synCplc (synCtfin M) (synCtfin N)))).fv :=
    by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin, Finset.mem_union,
      Finset.mem_singleton, fresh_c_ne_a, fresh_c_not_M, fresh_c_not_N, or_false,
      not_false_eq_true]
  have freeVariableCertificate5 :
    b ∉ ((synWa (.classMem M (synCnnc)) (.classMem N (synCnnc)))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union,
      Finset.notMem_empty, fresh_b_not_M, fresh_b_not_N, or_false, not_false_eq_true]
  have freeVariableCertificate6 :
    c ∉ ((synWa (.classMem M (synCnnc)) (.classMem N (synCnnc)))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union,
      Finset.notMem_empty, fresh_c_not_M, fresh_c_not_N, or_false, not_false_eq_true]
  have p0036 :=
    @gRexlimdvva (synWa (.classMem M (synCnnc)) (.classMem N (synCnnc)))
      (synWa (.classEq (synCin (.cv b) (.cv c)) (synC0))
        (.classEq (.cv a) (synCun (.cv b) (.cv c))))
      (.classMem (synCpw1 (.cv a)) (synCplc (synCtfin M) (synCtfin N))) b c M N
      (by exact (show c ∉ (M).fv from (by exact fresh_c_not_M))) freeVariableCertificate3
      freeVariableCertificate4 freeVariableCertificate5 freeVariableCertificate6
      (show b ≠ c from (by exact fresh_b_ne_c)) p0035
  have p0037 :=
    @gSyl5bi (.classMem (.cv a) (synCplc M N))
      (synWrex b M (synWrex c N (synWa (.classEq (synCin (.cv b) (.cv c)) (synC0))
            (.classEq (.cv a) (synCun (.cv b) (.cv c))))))
      (synWa (.classMem M (synCnnc)) (.classMem N (synCnnc)))
      (.classMem (synCpw1 (.cv a)) (synCplc (synCtfin M) (synCtfin N))) p0014 p0036
  have p0038 :=
    @gN3impia (.classMem M (synCnnc)) (.classMem N (synCnnc))
      (.classMem (.cv a) (synCplc M N))
      (.classMem (synCpw1 (.cv a)) (synCplc (synCtfin M) (synCtfin N))) p0037
  have p0039 :=
    @gNnceleq (synCpw1 (.cv a)) (synCtfin (synCplc M N))
      (synCplc (synCtfin M) (synCtfin N))
  have p0040 :=
    @gSyl22anc
      (synW3a (.classMem M (synCnnc)) (.classMem N (synCnnc))
        (.classMem (.cv a) (synCplc M N)))
      (.classMem (synCtfin (synCplc M N)) (synCnnc))
      (.classMem (synCplc (synCtfin M) (synCtfin N)) (synCnnc))
      (.classMem (synCpw1 (.cv a)) (synCtfin (synCplc M N)))
      (.classMem (synCpw1 (.cv a)) (synCplc (synCtfin M) (synCtfin N)))
      (.classEq (synCtfin (synCplc M N)) (synCplc (synCtfin M) (synCtfin N))) p0004
      p0009 p0013 p0038 p0039
  have p0041 :=
    @gN3expia (.classMem M (synCnnc)) (.classMem N (synCnnc))
      (.classMem (.cv a) (synCplc M N))
      (.classEq (synCtfin (synCplc M N)) (synCplc (synCtfin M) (synCtfin N))) p0040
  have freeVariableCertificate7 :
    a ∉
      ((Wff.classEq (synCtfin (synCplc M N)) (synCplc (synCtfin M) (synCtfin N)))).fv :=
    by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, Finset.mem_union,
      fresh_a_not_M, fresh_a_not_N, or_false, not_false_eq_true]
  have freeVariableCertificate8 :
    a ∉ ((synWa (.classMem M (synCnnc)) (.classMem N (synCnnc)))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union,
      Finset.notMem_empty, fresh_a_not_M, fresh_a_not_N, or_false, not_false_eq_true]
  have p0042 :=
    @gExlimdv (synWa (.classMem M (synCnnc)) (.classMem N (synCnnc)))
      (.classMem (.cv a) (synCplc M N))
      (.classEq (synCtfin (synCplc M N)) (synCplc (synCtfin M) (synCtfin N))) a
      freeVariableCertificate7 freeVariableCertificate8 p0041
  have p0043 :=
    @gSyl5bi (synWne (synCplc M N) (synC0))
      (synWex a (.classMem (.cv a) (synCplc M N)))
      (synWa (.classMem M (synCnnc)) (.classMem N (synCnnc)))
      (.classEq (synCtfin (synCplc M N)) (synCplc (synCtfin M) (synCtfin N))) p0000
      p0042
  have p0044 :=
    @gN3impia (.classMem M (synCnnc)) (.classMem N (synCnnc))
      (synWne (synCplc M N) (synC0))
      (.classEq (synCtfin (synCplc M N)) (synCplc (synCtfin M) (synCtfin N))) p0043
  exact p0044

/-- Checked nominal proof certificate identified upstream as `g_tfin0c`. -/
@[expose]
noncomputable def gTfin0c : Nominal.NPrf (.classEq (synCtfin (synC0c)) (synC0c)) :=
  by
  have p0000 := @gPeano1
  have p0001 := @gTfincl (synC0c)
  have p0002 := Nominal.mp p0000 p0001
  have p0004 := @gPw10
  have p0006 := @gNulel0c
  have p0007 := @gTfinpw1 (synC0) (synC0c)
  have p0008 :=
    @gMp2an (.classMem (synC0c) (synCnnc)) (.classMem (synC0) (synC0c))
      (.classMem (synCpw1 (synC0)) (synCtfin (synC0c))) p0000 p0006 p0007
  have p0009 := @gEqeltrri (synCpw1 (synC0)) (synC0) (synCtfin (synC0c)) p0004 p0008
  have p0011 := @gNnceleq (synC0) (synCtfin (synC0c)) (synC0c)
  have p0012 :=
    @gMp4an (.classMem (synCtfin (synC0c)) (synCnnc)) (.classMem (synC0c) (synCnnc))
      (.classMem (synC0) (synCtfin (synC0c))) (.classMem (synC0) (synC0c))
      (.classEq (synCtfin (synC0c)) (synC0c)) p0002 p0000 p0009 p0006 p0011
  exact p0012

/-- Checked nominal proof certificate identified upstream as `g_tfinsuc`. -/
@[expose]
noncomputable def gTfinsuc (A : Class) :
    Nominal.NPrf
      (.imp (synWa (.classMem A (synCnnc)) (synWne (synCplc A (synC1c)) (synC0)))
        (.classEq (synCtfin (synCplc A (synC1c))) (synCplc (synCtfin A) (synC1c)))) :=
  by
  let proofSupport : Finset Var := A.fv
  let a : Var := freshVar proofSupport 0
  let b : Var := freshVar proofSupport 1
  let x : Var := freshVar proofSupport 2
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
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (h)
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
  have freeVariableCertificate0 : a ∉ ((synCplc A (synC1c))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
      Finset.notMem_empty, fresh_a_not_A, or_false, not_false_eq_true]
  have p0000 := @gN0 a (synCplc A (synC1c)) freeVariableCertificate0
  have p0001 := @gPeano2 A
  have p0002 := @gTfincl (synCplc A (synC1c))
  have p0003 :=
    @gSyl (.classMem A (synCnnc)) (.classMem (synCplc A (synC1c)) (synCnnc))
      (.classMem (synCtfin (synCplc A (synC1c))) (synCnnc)) p0001 p0002
  have p0004 :=
    @gAdantr (.classMem A (synCnnc))
      (.classMem (synCtfin (synCplc A (synC1c))) (synCnnc))
      (.classMem (.cv a) (synCplc A (synC1c))) p0003
  have p0005 := @gTfincl A
  have p0006 := @gPeano2 (synCtfin A)
  have p0007 :=
    @gSyl (.classMem A (synCnnc)) (.classMem (synCtfin A) (synCnnc))
      (.classMem (synCplc (synCtfin A) (synC1c)) (synCnnc)) p0005 p0006
  have p0008 :=
    @gAdantr (.classMem A (synCnnc))
      (.classMem (synCplc (synCtfin A) (synC1c)) (synCnnc))
      (.classMem (.cv a) (synCplc A (synC1c))) p0007
  have p0009 := @gTfinpw1 (.cv a) (synCplc A (synC1c))
  have p0010 :=
    @gSylan (.classMem A (synCnnc)) (.classMem (synCplc A (synC1c)) (synCnnc))
      (.classMem (.cv a) (synCplc A (synC1c)))
      (.classMem (synCpw1 (.cv a)) (synCtfin (synCplc A (synC1c)))) p0001 p0009
  have freeVariableCertificate1 : b ∉ ((Class.cv a)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_b_ne_a, not_false_eq_true]
  have freeVariableCertificate2 : x ∉ ((Class.cv a)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_x_ne_a, not_false_eq_true]
  have p0011 :=
    @gElsuc x (.cv a) A b freeVariableCertificate1 freeVariableCertificate2
      (by exact (show b ∉ (A).fv from (by exact fresh_b_not_A)))
      (show b ≠ x from (by exact fresh_b_ne_x))
  have p0012 := @gTfinpw1 (.cv b) A
  have p0013 :=
    @gAdantrr (.classMem A (synCnnc)) (.classMem (.cv b) A)
      (.classMem (synCpw1 (.cv b)) (synCtfin A))
      (.classMem (.cv x) (synCcompl (.cv b))) p0012
  have p0014 := @gVex x
  have p0015 := @gElcompl (.cv x) (.cv b) p0014
  have p0016 := @gSnelpw1 (.cv x) (.cv b)
  have p0017_e00_recanon :
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
      p0015
  have p0017_e01_recanon :
    Nominal.NPrf
      (synWb (.classMem (synCsn (.cv x)) (synCpw1 (.cv b))) (.objMem x b)) :=
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
      p0016
  have p0017 :=
    @gXchbinxr (.classMem (.cv x) (synCcompl (.cv b))) (.objMem x b)
      (.classMem (synCsn (.cv x)) (synCpw1 (.cv b))) p0017_e00_recanon p0017_e01_recanon
  have p0018 :=
    @gBiimpi (.classMem (.cv x) (synCcompl (.cv b)))
      (.neg (.classMem (synCsn (.cv x)) (synCpw1 (.cv b)))) p0017
  have p0019 :=
    @gAd2antll (.classMem (.cv x) (synCcompl (.cv b)))
      (.neg (.classMem (synCsn (.cv x)) (synCpw1 (.cv b)))) (.classMem A (synCnnc))
      (.classMem (.cv b) A) p0018
  have p0020 := @gSnex (.cv x)
  have p0021 := @gElsuci (synCpw1 (.cv b)) (synCtfin A) (synCsn (.cv x)) p0020
  have p0022 :=
    @gSyl2anc
      (synWa (.classMem A (synCnnc))
        (synWa (.classMem (.cv b) A) (.classMem (.cv x) (synCcompl (.cv b)))))
      (.classMem (synCpw1 (.cv b)) (synCtfin A))
      (.neg (.classMem (synCsn (.cv x)) (synCpw1 (.cv b))))
      (.classMem (synCun (synCpw1 (.cv b)) (synCsn (synCsn (.cv x))))
        (synCplc (synCtfin A) (synC1c)))
      p0013 p0019 p0021
  have p0023 := @gPw1eq (.cv a) (synCun (.cv b) (synCsn (.cv x)))
  have p0024 := @gPw1un (.cv b) (synCsn (.cv x))
  have p0025 := @gPw1sn (.cv x) p0014
  have p0026 :=
    @gUneq2i (synCpw1 (synCsn (.cv x))) (synCsn (synCsn (.cv x))) (synCpw1 (.cv b))
      p0025
  have p0027 :=
    @gEqtri (synCpw1 (synCun (.cv b) (synCsn (.cv x))))
      (synCun (synCpw1 (.cv b)) (synCpw1 (synCsn (.cv x))))
      (synCun (synCpw1 (.cv b)) (synCsn (synCsn (.cv x)))) p0024 p0026
  have p0028 :=
    @gSyl6eq (.classEq (.cv a) (synCun (.cv b) (synCsn (.cv x)))) (synCpw1 (.cv a))
      (synCpw1 (synCun (.cv b) (synCsn (.cv x))))
      (synCun (synCpw1 (.cv b)) (synCsn (synCsn (.cv x)))) p0023 p0027
  have p0029 :=
    @gEleq1d (.classEq (.cv a) (synCun (.cv b) (synCsn (.cv x)))) (synCpw1 (.cv a))
      (synCun (synCpw1 (.cv b)) (synCsn (synCsn (.cv x))))
      (synCplc (synCtfin A) (synC1c)) p0028
  have p0030 :=
    @gSyl5ibrcom
      (synWa (.classMem A (synCnnc))
        (synWa (.classMem (.cv b) A) (.classMem (.cv x) (synCcompl (.cv b)))))
      (.classMem (synCpw1 (.cv a)) (synCplc (synCtfin A) (synC1c)))
      (.classEq (.cv a) (synCun (.cv b) (synCsn (.cv x))))
      (.classMem (synCun (synCpw1 (.cv b)) (synCsn (synCsn (.cv x))))
        (synCplc (synCtfin A) (synC1c)))
      p0022 p0029
  have freeVariableCertificate3 :
    b ∉ ((Wff.classMem (synCpw1 (.cv a)) (synCplc (synCtfin A) (synC1c)))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_b_ne_a, fresh_b_not_A, or_false,
      not_false_eq_true]
  have freeVariableCertificate4 :
    x ∉ ((Wff.classMem (synCpw1 (.cv a)) (synCplc (synCtfin A) (synC1c)))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_x_ne_a, fresh_x_not_A, or_false,
      not_false_eq_true]
  have freeVariableCertificate5 : b ∉ ((Wff.classMem A (synCnnc))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union,
      Finset.notMem_empty, fresh_b_not_A, or_false, not_false_eq_true]
  have freeVariableCertificate6 : x ∉ ((Wff.classMem A (synCnnc))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union,
      Finset.notMem_empty, fresh_x_not_A, or_false, not_false_eq_true]
  have p0031 :=
    @gRexlimdvva (.classMem A (synCnnc))
      (.classEq (.cv a) (synCun (.cv b) (synCsn (.cv x))))
      (.classMem (synCpw1 (.cv a)) (synCplc (synCtfin A) (synC1c))) b x A
      (synCcompl (.cv b)) (by exact (show x ∉ (A).fv from (by exact fresh_x_not_A)))
      freeVariableCertificate3 freeVariableCertificate4 freeVariableCertificate5
      freeVariableCertificate6 (show b ≠ x from (by exact fresh_b_ne_x)) p0030
  have p0032 :=
    @gSyl5bi (.classMem (.cv a) (synCplc A (synC1c)))
      (synWrex b A (synWrex x (synCcompl (.cv b))
          (.classEq (.cv a) (synCun (.cv b) (synCsn (.cv x))))))
      (.classMem A (synCnnc))
      (.classMem (synCpw1 (.cv a)) (synCplc (synCtfin A) (synC1c))) p0011 p0031
  have p0033 :=
    @gImp (.classMem A (synCnnc)) (.classMem (.cv a) (synCplc A (synC1c)))
      (.classMem (synCpw1 (.cv a)) (synCplc (synCtfin A) (synC1c))) p0032
  have p0034 :=
    @gNnceleq (synCpw1 (.cv a)) (synCtfin (synCplc A (synC1c)))
      (synCplc (synCtfin A) (synC1c))
  have p0035 :=
    @gSyl22anc
      (synWa (.classMem A (synCnnc)) (.classMem (.cv a) (synCplc A (synC1c))))
      (.classMem (synCtfin (synCplc A (synC1c))) (synCnnc))
      (.classMem (synCplc (synCtfin A) (synC1c)) (synCnnc))
      (.classMem (synCpw1 (.cv a)) (synCtfin (synCplc A (synC1c))))
      (.classMem (synCpw1 (.cv a)) (synCplc (synCtfin A) (synC1c)))
      (.classEq (synCtfin (synCplc A (synC1c))) (synCplc (synCtfin A) (synC1c)))
      p0004 p0008 p0010 p0033 p0034
  have p0036 :=
    @gEx (.classMem A (synCnnc)) (.classMem (.cv a) (synCplc A (synC1c)))
      (.classEq (synCtfin (synCplc A (synC1c))) (synCplc (synCtfin A) (synC1c)))
      p0035
  have freeVariableCertificate7 :
    a ∉
      ((Wff.classEq (synCtfin (synCplc A (synC1c)))
          (synCplc (synCtfin A) (synC1c)))).fv :=
    by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
      Finset.notMem_empty, fresh_a_not_A, or_false, not_false_eq_true]
  have freeVariableCertificate8 : a ∉ ((Wff.classMem A (synCnnc))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union,
      Finset.notMem_empty, fresh_a_not_A, or_false, not_false_eq_true]
  have p0037 :=
    @gExlimdv (.classMem A (synCnnc)) (.classMem (.cv a) (synCplc A (synC1c)))
      (.classEq (synCtfin (synCplc A (synC1c))) (synCplc (synCtfin A) (synC1c))) a
      freeVariableCertificate7 freeVariableCertificate8 p0036
  have p0038 :=
    @gSyl5bi (synWne (synCplc A (synC1c)) (synC0))
      (synWex a (.classMem (.cv a) (synCplc A (synC1c)))) (.classMem A (synCnnc))
      (.classEq (synCtfin (synCplc A (synC1c))) (synCplc (synCtfin A) (synC1c)))
      p0000 p0037
  have p0039 :=
    @gImp (.classMem A (synCnnc)) (synWne (synCplc A (synC1c)) (synC0))
      (.classEq (synCtfin (synCplc A (synC1c))) (synCplc (synCtfin A) (synC1c)))
      p0038
  exact p0039

/-- Checked nominal proof certificate identified upstream as `g_tfin1c`. -/
@[expose]
noncomputable def gTfin1c : Nominal.NPrf (.classEq (synCtfin (synC1c)) (synC1c)) :=
  by
  have p0000 := @gPeano1
  have p0001 := @gAddcid2 (synC1c)
  have p0002 := @gN1cex
  have p0003 := @gSnel1c (synC1c) p0002
  have p0004 := @gNe0i (synC1c) (synCsn (synC1c))
  have p0005 := Nominal.mp p0003 p0004
  have p0006 := @gEqnetri (synCplc (synC0c) (synC1c)) (synC1c) (synC0) p0001 p0005
  have p0007 := @gTfinsuc (synC0c)
  have p0008 :=
    @gMp2an (.classMem (synC0c) (synCnnc))
      (synWne (synCplc (synC0c) (synC1c)) (synC0))
      (.classEq (synCtfin (synCplc (synC0c) (synC1c)))
        (synCplc (synCtfin (synC0c)) (synC1c)))
      p0000 p0006 p0007
  have p0009 := @gTfineq (synCplc (synC0c) (synC1c)) (synC1c)
  have p0010 := Nominal.mp p0001 p0009
  have p0011 := @gTfin0c
  have p0012 := @gAddceq1i (synCtfin (synC0c)) (synC0c) (synC1c) p0011
  have p0013 :=
    @gEqtri (synCplc (synCtfin (synC0c)) (synC1c)) (synCplc (synC0c) (synC1c))
      (synC1c) p0012 p0001
  have p0014 :=
    @gN3eqtr3i (synCtfin (synCplc (synC0c) (synC1c)))
      (synCplc (synCtfin (synC0c)) (synC1c)) (synCtfin (synC1c)) (synC1c) p0008
      p0010 p0013
  exact p0014


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk009StructuralPart057`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_tfinltfinlem1`. -/
@[expose]
noncomputable def gTfinltfinlem1 (M : Class) (N : Class) :
    Nominal.NPrf
      (.imp (synWa (.classMem M (synCnnc)) (.classMem N (synCnnc)))
        (.imp (.classMem (synCopk M N) (synCltfin))
          (.classMem (synCopk (synCtfin M) (synCtfin N)) (synCltfin)))) :=
  by
  let proofSupport : Finset Var := M.fv ∪ N.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_M : x ∉ M.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_not_N : x ∉ N.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_M : y ∉ M.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (h))
  have fresh_y_not_N : y ∉ N.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x := Ne.symm fresh_x_ne_y
  have p0000 := @gTfinnnul M
  have p0001 :=
    @gEx (.classMem M (synCnnc)) (synWne M (synC0)) (synWne (synCtfin M) (synC0))
      p0000
  have p0002 :=
    @gAdantrd (.classMem M (synCnnc)) (synWne M (synC0))
      (synWne (synCtfin M) (synC0))
      (synWrex x (synCnnc) (.classEq N (synCplc (synCplc M (.cv x)) (synC1c)))) p0001
  have p0003 :=
    @gAdantr (.classMem M (synCnnc))
      (.imp (synWa (synWne M (synC0))
          (synWrex x (synCnnc) (.classEq N (synCplc (synCplc M (.cv x)) (synC1c)))))
        (synWne (synCtfin M) (synC0)))
      (.classMem N (synCnnc)) p0002
  have p0004 := @gAddcnul1 (synC1c)
  have p0005 := @gAddccom (synC1c) (synC0)
  have p0006 :=
    @gEqtr3i (synCplc (synC1c) (synC0)) (synC0) (synCplc (synC0) (synC1c)) p0004
      p0005
  have p0007 := @gAddceq2 (.cv y) (synC0) (synCtfin M)
  have p0008 := @gAddcnul1 (synCtfin M)
  have p0009 :=
    @gSyl6eq (.classEq (.cv y) (synC0)) (synCplc (synCtfin M) (.cv y))
      (synCplc (synCtfin M) (synC0)) (synC0) p0007 p0008
  have p0010 :=
    @gAddceq1d (.classEq (.cv y) (synC0)) (synCplc (synCtfin M) (.cv y)) (synC0)
      (synC1c) p0009
  have p0011 :=
    @gEqeq2d (.classEq (.cv y) (synC0))
      (synCplc (synCplc (synCtfin M) (.cv y)) (synC1c)) (synCplc (synC0) (synC1c))
      (synC0) p0010
  have freeVariableCertificate0 :
    y ∉ ((Wff.classEq (synC0) (synCplc (synC0) (synC1c)))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
      Finset.notMem_empty, or_false, not_false_eq_true]
  have p0012 :=
    @gRspcev (.classEq (synC0) (synCplc (synCplc (synCtfin M) (.cv y)) (synC1c)))
      (.classEq (synC0) (synCplc (synC0) (synC1c))) y (synC0) (synCnnc)
      (by
        exact
          (show y ∉ ((synC0)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0];
              exact (show y ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
      (by
        exact
          (show y ∉ ((synCnnc)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc];
              exact (show y ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
      freeVariableCertificate0 p0011
  have p0013 :=
    @gMpan2 (.classMem (synC0) (synCnnc))
      (.classEq (synC0) (synCplc (synC0) (synC1c)))
      (synWrex y (synCnnc)
        (.classEq (synC0) (synCplc (synCplc (synCtfin M) (.cv y)) (synC1c))))
      p0006 p0012
  have p0014 := @gEleq1 N (synC0) (synCnnc)
  have p0015 := @gTfineq N (synC0)
  have p0016 := @gTfinnul
  have p0017 :=
    @gSyl6eq (.classEq N (synC0)) (synCtfin N) (synCtfin (synC0)) (synC0) p0015
      p0016
  have p0018 :=
    @gEqeq1d (.classEq N (synC0)) (synCtfin N) (synC0)
      (synCplc (synCplc (synCtfin M) (.cv y)) (synC1c)) p0017
  have freeVariableCertificate1 : y ∉ ((Wff.classEq N (synC0))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union,
      Finset.notMem_empty, fresh_y_not_N, or_false, not_false_eq_true]
  have p0019 :=
    @gRexbidv (.classEq N (synC0))
      (.classEq (synCtfin N) (synCplc (synCplc (synCtfin M) (.cv y)) (synC1c)))
      (.classEq (synC0) (synCplc (synCplc (synCtfin M) (.cv y)) (synC1c))) y
      (synCnnc) freeVariableCertificate1 p0018
  have p0020 :=
    @gImbi12d (.classEq N (synC0)) (.classMem N (synCnnc))
      (.classMem (synC0) (synCnnc))
      (synWrex y (synCnnc)
        (.classEq (synCtfin N) (synCplc (synCplc (synCtfin M) (.cv y)) (synC1c))))
      (synWrex y (synCnnc)
        (.classEq (synC0) (synCplc (synCplc (synCtfin M) (.cv y)) (synC1c))))
      p0014 p0019
  have p0021 :=
    @gMpbiri (.classEq N (synC0))
      (.imp (.classMem N (synCnnc)) (synWrex y (synCnnc)
          (.classEq (synCtfin N) (synCplc (synCplc (synCtfin M) (.cv y)) (synC1c)))))
      (.imp (.classMem (synC0) (synCnnc)) (synWrex y (synCnnc)
          (.classEq (synC0) (synCplc (synCplc (synCtfin M) (.cv y)) (synC1c)))))
      p0013 p0020
  have p0022 :=
    @gAdantld (.classEq N (synC0)) (.classMem N (synCnnc))
      (synWrex y (synCnnc)
        (.classEq (synCtfin N) (synCplc (synCplc (synCtfin M) (.cv y)) (synC1c))))
      (.classMem M (synCnnc)) p0021
  have p0023 :=
    @gAdantrd (.classEq N (synC0))
      (synWa (.classMem M (synCnnc)) (.classMem N (synCnnc)))
      (synWrex y (synCnnc)
        (.classEq (synCtfin N) (synCplc (synCplc (synCtfin M) (.cv y)) (synC1c))))
      (synWa (synWne M (synC0)) (.classMem (.cv x) (synCnnc))) p0022
  have p0024 :=
    @gA1dd (.classEq N (synC0))
      (synWa (synWa (.classMem M (synCnnc)) (.classMem N (synCnnc)))
        (synWa (synWne M (synC0)) (.classMem (.cv x) (synCnnc))))
      (synWrex y (synCnnc)
        (.classEq (synCtfin N) (synCplc (synCplc (synCtfin M) (.cv y)) (synC1c))))
      (.classEq N (synCplc (synCplc M (.cv x)) (synC1c))) p0023
  have p0025 :=
    @gSimp2r (synWa (.classMem M (synCnnc)) (.classMem N (synCnnc)))
      (synWne M (synC0)) (.classMem (.cv x) (synCnnc))
      (synWa (synWne N (synC0)) (.classEq N (synCplc (synCplc M (.cv x)) (synC1c))))
  have p0026 :=
    @gSimp3r (synWa (.classMem M (synCnnc)) (.classMem N (synCnnc)))
      (synWa (synWne M (synC0)) (.classMem (.cv x) (synCnnc))) (synWne N (synC0))
      (.classEq N (synCplc (synCplc M (.cv x)) (synC1c)))
  have p0027 :=
    @gSimp3l (synWa (.classMem M (synCnnc)) (.classMem N (synCnnc)))
      (synWa (synWne M (synC0)) (.classMem (.cv x) (synCnnc))) (synWne N (synC0))
      (.classEq N (synCplc (synCplc M (.cv x)) (synC1c)))
  have p0028 :=
    @gEqnetrrd
      (synW3a (synWa (.classMem M (synCnnc)) (.classMem N (synCnnc)))
        (synWa (synWne M (synC0)) (.classMem (.cv x) (synCnnc)))
        (synWa (synWne N (synC0)) (.classEq N (synCplc (synCplc M (.cv x)) (synC1c)))))
      N (synCplc (synCplc M (.cv x)) (synC1c)) (synC0) p0026 p0027
  have p0029 := @gAddcnnul (synCplc M (.cv x)) (synC1c)
  have p0030 :=
    @gSyl
      (synW3a (synWa (.classMem M (synCnnc)) (.classMem N (synCnnc)))
        (synWa (synWne M (synC0)) (.classMem (.cv x) (synCnnc)))
        (synWa (synWne N (synC0)) (.classEq N (synCplc (synCplc M (.cv x)) (synC1c)))))
      (synWne (synCplc (synCplc M (.cv x)) (synC1c)) (synC0))
      (synWa (synWne (synCplc M (.cv x)) (synC0)) (synWne (synC1c) (synC0))) p0028
      p0029
  have p0031 :=
    @gSimpld
      (synW3a (synWa (.classMem M (synCnnc)) (.classMem N (synCnnc)))
        (synWa (synWne M (synC0)) (.classMem (.cv x) (synCnnc)))
        (synWa (synWne N (synC0)) (.classEq N (synCplc (synCplc M (.cv x)) (synC1c)))))
      (synWne (synCplc M (.cv x)) (synC0)) (synWne (synC1c) (synC0)) p0030
  have p0032 := @gAddcnnul M (.cv x)
  have p0033 :=
    @gSyl
      (synW3a (synWa (.classMem M (synCnnc)) (.classMem N (synCnnc)))
        (synWa (synWne M (synC0)) (.classMem (.cv x) (synCnnc)))
        (synWa (synWne N (synC0)) (.classEq N (synCplc (synCplc M (.cv x)) (synC1c)))))
      (synWne (synCplc M (.cv x)) (synC0))
      (synWa (synWne M (synC0)) (synWne (.cv x) (synC0))) p0031 p0032
  have p0034 :=
    @gSimprd
      (synW3a (synWa (.classMem M (synCnnc)) (.classMem N (synCnnc)))
        (synWa (synWne M (synC0)) (.classMem (.cv x) (synCnnc)))
        (synWa (synWne N (synC0)) (.classEq N (synCplc (synCplc M (.cv x)) (synC1c)))))
      (synWne M (synC0)) (synWne (.cv x) (synC0)) p0033
  have freeVariableCertificate2 : y ∉ ((Class.cv x)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_y_ne_x, not_false_eq_true]
  have p0035 := @gTfinprop (.cv x) y freeVariableCertificate2
  have p0036 :=
    @gSimpld (synWa (.classMem (.cv x) (synCnnc)) (synWne (.cv x) (synC0)))
      (.classMem (synCtfin (.cv x)) (synCnnc))
      (synWrex y (.cv x) (.classMem (synCpw1 (.cv y)) (synCtfin (.cv x)))) p0035
  have p0037 :=
    @gSyl2anc
      (synW3a (synWa (.classMem M (synCnnc)) (.classMem N (synCnnc)))
        (synWa (synWne M (synC0)) (.classMem (.cv x) (synCnnc)))
        (synWa (synWne N (synC0)) (.classEq N (synCplc (synCplc M (.cv x)) (synC1c)))))
      (.classMem (.cv x) (synCnnc)) (synWne (.cv x) (synC0))
      (.classMem (synCtfin (.cv x)) (synCnnc)) p0025 p0034 p0036
  have p0038 := @gTfineq N (synCplc (synCplc M (.cv x)) (synC1c))
  have p0039 :=
    @gAdantl (.classEq N (synCplc (synCplc M (.cv x)) (synC1c)))
      (.classEq (synCtfin N) (synCtfin (synCplc (synCplc M (.cv x)) (synC1c))))
      (synWne N (synC0)) p0038
  have p0040 :=
    @gN3ad2ant3
      (synWa (synWne N (synC0)) (.classEq N (synCplc (synCplc M (.cv x)) (synC1c))))
      (synWa (.classMem M (synCnnc)) (.classMem N (synCnnc)))
      (.classEq (synCtfin N) (synCtfin (synCplc (synCplc M (.cv x)) (synC1c))))
      (synWa (synWne M (synC0)) (.classMem (.cv x) (synCnnc))) p0039
  have p0041 :=
    @gSimp1l (.classMem M (synCnnc)) (.classMem N (synCnnc))
      (synWa (synWne M (synC0)) (.classMem (.cv x) (synCnnc)))
      (synWa (synWne N (synC0)) (.classEq N (synCplc (synCplc M (.cv x)) (synC1c))))
  have p0042 := @gNncaddccl M (.cv x)
  have p0043 :=
    @gSyl2anc
      (synW3a (synWa (.classMem M (synCnnc)) (.classMem N (synCnnc)))
        (synWa (synWne M (synC0)) (.classMem (.cv x) (synCnnc)))
        (synWa (synWne N (synC0)) (.classEq N (synCplc (synCplc M (.cv x)) (synC1c)))))
      (.classMem M (synCnnc)) (.classMem (.cv x) (synCnnc))
      (.classMem (synCplc M (.cv x)) (synCnnc)) p0041 p0025 p0042
  have p0044 := @gTfinsuc (synCplc M (.cv x))
  have p0045 :=
    @gSyl2anc
      (synW3a (synWa (.classMem M (synCnnc)) (.classMem N (synCnnc)))
        (synWa (synWne M (synC0)) (.classMem (.cv x) (synCnnc)))
        (synWa (synWne N (synC0)) (.classEq N (synCplc (synCplc M (.cv x)) (synC1c)))))
      (.classMem (synCplc M (.cv x)) (synCnnc))
      (synWne (synCplc (synCplc M (.cv x)) (synC1c)) (synC0))
      (.classEq (synCtfin (synCplc (synCplc M (.cv x)) (synC1c)))
        (synCplc (synCtfin (synCplc M (.cv x))) (synC1c)))
      p0043 p0028 p0044
  have p0046 :=
    @gEqtrd
      (synW3a (synWa (.classMem M (synCnnc)) (.classMem N (synCnnc)))
        (synWa (synWne M (synC0)) (.classMem (.cv x) (synCnnc)))
        (synWa (synWne N (synC0)) (.classEq N (synCplc (synCplc M (.cv x)) (synC1c)))))
      (synCtfin N) (synCtfin (synCplc (synCplc M (.cv x)) (synC1c)))
      (synCplc (synCtfin (synCplc M (.cv x))) (synC1c)) p0040 p0045
  have p0047 := @gTfindi M (.cv x)
  have p0048 :=
    @gSyl3anc
      (synW3a (synWa (.classMem M (synCnnc)) (.classMem N (synCnnc)))
        (synWa (synWne M (synC0)) (.classMem (.cv x) (synCnnc)))
        (synWa (synWne N (synC0)) (.classEq N (synCplc (synCplc M (.cv x)) (synC1c)))))
      (.classMem M (synCnnc)) (.classMem (.cv x) (synCnnc))
      (synWne (synCplc M (.cv x)) (synC0))
      (.classEq (synCtfin (synCplc M (.cv x))) (synCplc (synCtfin M) (synCtfin (.cv x))))
      p0041 p0025 p0031 p0047
  have p0049 :=
    @gAddceq1d
      (synW3a (synWa (.classMem M (synCnnc)) (.classMem N (synCnnc)))
        (synWa (synWne M (synC0)) (.classMem (.cv x) (synCnnc)))
        (synWa (synWne N (synC0)) (.classEq N (synCplc (synCplc M (.cv x)) (synC1c)))))
      (synCtfin (synCplc M (.cv x))) (synCplc (synCtfin M) (synCtfin (.cv x)))
      (synC1c) p0048
  have p0050 :=
    @gEqtrd
      (synW3a (synWa (.classMem M (synCnnc)) (.classMem N (synCnnc)))
        (synWa (synWne M (synC0)) (.classMem (.cv x) (synCnnc)))
        (synWa (synWne N (synC0)) (.classEq N (synCplc (synCplc M (.cv x)) (synC1c)))))
      (synCtfin N) (synCplc (synCtfin (synCplc M (.cv x))) (synC1c))
      (synCplc (synCplc (synCtfin M) (synCtfin (.cv x))) (synC1c)) p0046 p0049
  have p0051 := @gAddceq2 (.cv y) (synCtfin (.cv x)) (synCtfin M)
  have p0052 :=
    @gAddceq1d (.classEq (.cv y) (synCtfin (.cv x))) (synCplc (synCtfin M) (.cv y))
      (synCplc (synCtfin M) (synCtfin (.cv x))) (synC1c) p0051
  have p0053 :=
    @gEqeq2d (.classEq (.cv y) (synCtfin (.cv x)))
      (synCplc (synCplc (synCtfin M) (.cv y)) (synC1c))
      (synCplc (synCplc (synCtfin M) (synCtfin (.cv x))) (synC1c)) (synCtfin N)
      p0052
  have freeVariableCertificate3 : y ∉ ((synCtfin (.cv x))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_y_ne_x,
      not_false_eq_true]
  have freeVariableCertificate4 :
    y ∉
      ((Wff.classEq (synCtfin N)
          (synCplc (synCplc (synCtfin M) (synCtfin (.cv x))) (synC1c)))).fv :=
    by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_y_not_N, fresh_y_not_M,
      fresh_y_ne_x, or_false, not_false_eq_true]
  have p0054 :=
    @gRspcev
      (.classEq (synCtfin N) (synCplc (synCplc (synCtfin M) (.cv y)) (synC1c)))
      (.classEq (synCtfin N) (synCplc (synCplc (synCtfin M) (synCtfin (.cv x))) (synC1c)))
      y (synCtfin (.cv x)) (synCnnc) freeVariableCertificate3
      (by
        exact
          (show y ∉ ((synCnnc)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc];
              exact (show y ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
      freeVariableCertificate4 p0053
  have p0055 :=
    @gSyl2anc
      (synW3a (synWa (.classMem M (synCnnc)) (.classMem N (synCnnc)))
        (synWa (synWne M (synC0)) (.classMem (.cv x) (synCnnc)))
        (synWa (synWne N (synC0)) (.classEq N (synCplc (synCplc M (.cv x)) (synC1c)))))
      (.classMem (synCtfin (.cv x)) (synCnnc))
      (.classEq (synCtfin N) (synCplc (synCplc (synCtfin M) (synCtfin (.cv x))) (synC1c)))
      (synWrex y (synCnnc)
        (.classEq (synCtfin N) (synCplc (synCplc (synCtfin M) (.cv y)) (synC1c))))
      p0037 p0050 p0054
  have p0056 :=
    @gN3expa (synWa (.classMem M (synCnnc)) (.classMem N (synCnnc)))
      (synWa (synWne M (synC0)) (.classMem (.cv x) (synCnnc)))
      (synWa (synWne N (synC0)) (.classEq N (synCplc (synCplc M (.cv x)) (synC1c))))
      (synWrex y (synCnnc)
        (.classEq (synCtfin N) (synCplc (synCplc (synCtfin M) (.cv y)) (synC1c))))
      p0055
  have p0057 :=
    @gExp32
      (synWa (synWa (.classMem M (synCnnc)) (.classMem N (synCnnc)))
        (synWa (synWne M (synC0)) (.classMem (.cv x) (synCnnc))))
      (synWne N (synC0)) (.classEq N (synCplc (synCplc M (.cv x)) (synC1c)))
      (synWrex y (synCnnc)
        (.classEq (synCtfin N) (synCplc (synCplc (synCtfin M) (.cv y)) (synC1c))))
      p0056
  have p0058 :=
    @gCom12
      (synWa (synWa (.classMem M (synCnnc)) (.classMem N (synCnnc)))
        (synWa (synWne M (synC0)) (.classMem (.cv x) (synCnnc))))
      (synWne N (synC0))
      (.imp (.classEq N (synCplc (synCplc M (.cv x)) (synC1c))) (synWrex y (synCnnc)
          (.classEq (synCtfin N) (synCplc (synCplc (synCtfin M) (.cv y)) (synC1c)))))
      p0057
  have p0059 :=
    @gPm261ine
      (.imp (synWa (synWa (.classMem M (synCnnc)) (.classMem N (synCnnc)))
          (synWa (synWne M (synC0)) (.classMem (.cv x) (synCnnc))))
        (.imp (.classEq N (synCplc (synCplc M (.cv x)) (synC1c))) (synWrex y (synCnnc)
            (.classEq (synCtfin N) (synCplc (synCplc (synCtfin M) (.cv y)) (synC1c))))))
      N (synC0) p0024 p0058
  have p0060 :=
    @gExpr (synWa (.classMem M (synCnnc)) (.classMem N (synCnnc)))
      (synWne M (synC0)) (.classMem (.cv x) (synCnnc))
      (.imp (.classEq N (synCplc (synCplc M (.cv x)) (synC1c))) (synWrex y (synCnnc)
          (.classEq (synCtfin N) (synCplc (synCplc (synCtfin M) (.cv y)) (synC1c)))))
      p0059
  have freeVariableCertificate5 :
    x ∉
      ((synWrex y (synCnnc) (.classEq (synCtfin N)
            (synCplc (synCplc (synCtfin M) (.cv y)) (synC1c))))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
      Finset.mem_erase, Finset.mem_singleton, Finset.notMem_empty, fresh_x_not_N,
      fresh_x_not_M, fresh_x_ne_y, or_false, and_false, not_false_eq_true]
  have freeVariableCertificate6 :
    x ∉
      ((synWa (synWa (.classMem M (synCnnc)) (.classMem N (synCnnc)))
          (synWne M (synC0)))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union,
      Finset.notMem_empty, fresh_x_not_M, fresh_x_not_N, or_false, not_false_eq_true]
  have p0061 :=
    @gRexlimdv
      (synWa (synWa (.classMem M (synCnnc)) (.classMem N (synCnnc))) (synWne M (synC0)))
      (.classEq N (synCplc (synCplc M (.cv x)) (synC1c)))
      (synWrex y (synCnnc)
        (.classEq (synCtfin N) (synCplc (synCplc (synCtfin M) (.cv y)) (synC1c))))
      x (synCnnc) freeVariableCertificate5 freeVariableCertificate6 p0060
  have p0062 :=
    @gEx (synWa (.classMem M (synCnnc)) (.classMem N (synCnnc))) (synWne M (synC0))
      (.imp (synWrex x (synCnnc) (.classEq N (synCplc (synCplc M (.cv x)) (synC1c))))
        (synWrex y (synCnnc)
          (.classEq (synCtfin N) (synCplc (synCplc (synCtfin M) (.cv y)) (synC1c)))))
      p0061
  have p0063 :=
    @gImp3a (synWa (.classMem M (synCnnc)) (.classMem N (synCnnc)))
      (synWne M (synC0))
      (synWrex x (synCnnc) (.classEq N (synCplc (synCplc M (.cv x)) (synC1c))))
      (synWrex y (synCnnc)
        (.classEq (synCtfin N) (synCplc (synCplc (synCtfin M) (.cv y)) (synC1c))))
      p0062
  have p0064 :=
    @gJcad (synWa (.classMem M (synCnnc)) (.classMem N (synCnnc)))
      (synWa (synWne M (synC0))
        (synWrex x (synCnnc) (.classEq N (synCplc (synCplc M (.cv x)) (synC1c)))))
      (synWne (synCtfin M) (synC0))
      (synWrex y (synCnnc)
        (.classEq (synCtfin N) (synCplc (synCplc (synCtfin M) (.cv y)) (synC1c))))
      p0003 p0063
  have p0065 :=
    @gOpkltfing x M N (synCnnc) (synCnnc)
      (by exact (show x ∉ (M).fv from (by exact fresh_x_not_M)))
      (by exact (show x ∉ (N).fv from (by exact fresh_x_not_N)))
  have p0066 := @gTfinex M
  have p0067 := @gTfinex N
  have p0068 :=
    @gOpkltfing y (synCtfin M) (synCtfin N) (synCvv) (synCvv)
      (by
        exact
          (show y ∉ ((synCtfin M)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin];
              exact (show y ∉ (M).fv from (by exact fresh_y_not_M)))))
      (by
        exact
          (show y ∉ ((synCtfin N)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin];
              exact (show y ∉ (N).fv from (by exact fresh_y_not_N)))))
  have p0069 :=
    @gMp2an (.classMem (synCtfin M) (synCvv)) (.classMem (synCtfin N) (synCvv))
      (synWb (.classMem (synCopk (synCtfin M) (synCtfin N)) (synCltfin))
        (synWa (synWne (synCtfin M) (synC0)) (synWrex y (synCnnc) (.classEq (synCtfin N)
              (synCplc (synCplc (synCtfin M) (.cv y)) (synC1c))))))
      p0066 p0067 p0068
  have p0070 :=
    @gA1i
      (synWb (.classMem (synCopk (synCtfin M) (synCtfin N)) (synCltfin))
        (synWa (synWne (synCtfin M) (synC0)) (synWrex y (synCnnc) (.classEq (synCtfin N)
              (synCplc (synCplc (synCtfin M) (.cv y)) (synC1c))))))
      (synWa (.classMem M (synCnnc)) (.classMem N (synCnnc))) p0069
  have p0071 :=
    @gN3imtr4d (synWa (.classMem M (synCnnc)) (.classMem N (synCnnc)))
      (synWa (synWne M (synC0))
        (synWrex x (synCnnc) (.classEq N (synCplc (synCplc M (.cv x)) (synC1c)))))
      (synWa (synWne (synCtfin M) (synC0)) (synWrex y (synCnnc)
          (.classEq (synCtfin N) (synCplc (synCplc (synCtfin M) (.cv y)) (synC1c)))))
      (.classMem (synCopk M N) (synCltfin))
      (.classMem (synCopk (synCtfin M) (synCtfin N)) (synCltfin)) p0064 p0065 p0070
  exact p0071

/-- Checked nominal proof certificate identified upstream as `g_tfinltfin`. -/
@[expose]
noncomputable def gTfinltfin (M : Class) (N : Class) :
    Nominal.NPrf
      (.imp (synWa (.classMem M (synCnnc)) (.classMem N (synCnnc)))
        (synWb (.classMem (synCopk M N) (synCltfin))
          (.classMem (synCopk (synCtfin M) (synCtfin N)) (synCltfin)))) :=
  by
  let proofSupport : Finset Var := M.fv ∪ N.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_M : x ∉ M.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_not_N : x ∉ N.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_M : y ∉ M.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (h))
  have fresh_y_not_N : y ∉ N.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have p0000 := @gTfinltfinlem1 M N
  have p0001 := @gTfineq M (synC0)
  have p0002 := @gTfinnul
  have p0003 :=
    @gSyl6eq (.classEq M (synC0)) (synCtfin M) (synCtfin (synC0)) (synC0) p0001
      p0002
  have p0004 := (Nominal.biimpRefl (synWne (synCtfin M) (synC0)))
  have p0005 :=
    @gCon2bii (synWne (synCtfin M) (synC0)) (.classEq (synCtfin M) (synC0)) p0004
  have p0006 :=
    @gSylib (.classEq M (synC0)) (.classEq (synCtfin M) (synC0))
      (.neg (synWne (synCtfin M) (synC0))) p0003 p0005
  have p0007 :=
    @gIntnanrd (.classEq M (synC0)) (synWne (synCtfin M) (synC0))
      (synWrex x (synCnnc)
        (.classEq (synCtfin N) (synCplc (synCplc (synCtfin M) (.cv x)) (synC1c))))
      p0006
  have p0008 := @gTfinex M
  have p0009 := @gTfinex N
  have p0010 :=
    @gOpkltfing x (synCtfin M) (synCtfin N) (synCvv) (synCvv)
      (by
        exact
          (show x ∉ ((synCtfin M)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin];
              exact (show x ∉ (M).fv from (by exact fresh_x_not_M)))))
      (by
        exact
          (show x ∉ ((synCtfin N)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin];
              exact (show x ∉ (N).fv from (by exact fresh_x_not_N)))))
  have p0011 :=
    @gMp2an (.classMem (synCtfin M) (synCvv)) (.classMem (synCtfin N) (synCvv))
      (synWb (.classMem (synCopk (synCtfin M) (synCtfin N)) (synCltfin))
        (synWa (synWne (synCtfin M) (synC0)) (synWrex x (synCnnc) (.classEq (synCtfin N)
              (synCplc (synCplc (synCtfin M) (.cv x)) (synC1c))))))
      p0008 p0009 p0010
  have p0012 :=
    @gSylnibr (.classEq M (synC0))
      (synWa (synWne (synCtfin M) (synC0)) (synWrex x (synCnnc)
          (.classEq (synCtfin N) (synCplc (synCplc (synCtfin M) (.cv x)) (synC1c)))))
      (.classMem (synCopk (synCtfin M) (synCtfin N)) (synCltfin)) p0007 p0011
  have p0013 :=
    @gPm221d (.classEq M (synC0))
      (.classMem (synCopk (synCtfin M) (synCtfin N)) (synCltfin))
      (.classMem (synCopk M N) (synCltfin)) p0012
  have p0014 :=
    @gA1d (.classEq M (synC0))
      (.imp (.classMem (synCopk (synCtfin M) (synCtfin N)) (synCltfin))
        (.classMem (synCopk M N) (synCltfin)))
      (synWa (.classMem M (synCnnc)) (.classMem N (synCnnc))) p0013
  have p0015 := @gTfinprop M y (by exact (show y ∉ (M).fv from (by exact fresh_y_not_M)))
  have p0016 :=
    @gSimpld (synWa (.classMem M (synCnnc)) (synWne M (synC0)))
      (.classMem (synCtfin M) (synCnnc))
      (synWrex y M (.classMem (synCpw1 (.cv y)) (synCtfin M))) p0015
  have p0017 := @gLtfinirr (synCtfin M)
  have p0018 :=
    @gSyl (synWa (.classMem M (synCnnc)) (synWne M (synC0)))
      (.classMem (synCtfin M) (synCnnc))
      (.neg (.classMem (synCopk (synCtfin M) (synCtfin M)) (synCltfin))) p0016 p0017
  have p0019 :=
    @gN3adant2 (.classMem M (synCnnc)) (synWne M (synC0))
      (.neg (.classMem (synCopk (synCtfin M) (synCtfin M)) (synCltfin)))
      (.classMem N (synCnnc)) p0018
  have p0020 := @gOpkeq2 (synCtfin M) (synCtfin N) (synCtfin M)
  have p0021 :=
    @gEleq1d (.classEq (synCtfin M) (synCtfin N))
      (synCopk (synCtfin M) (synCtfin M)) (synCopk (synCtfin M) (synCtfin N))
      (synCltfin) p0020
  have p0022 :=
    @gNotbid (.classEq (synCtfin M) (synCtfin N))
      (.classMem (synCopk (synCtfin M) (synCtfin M)) (synCltfin))
      (.classMem (synCopk (synCtfin M) (synCtfin N)) (synCltfin)) p0021
  have p0023 :=
    @gSyl5ibcom
      (synW3a (.classMem M (synCnnc)) (.classMem N (synCnnc)) (synWne M (synC0)))
      (.neg (.classMem (synCopk (synCtfin M) (synCtfin M)) (synCltfin)))
      (.classEq (synCtfin M) (synCtfin N))
      (.neg (.classMem (synCopk (synCtfin M) (synCtfin N)) (synCltfin))) p0019 p0022
  have p0024 :=
    @gCon2d
      (synW3a (.classMem M (synCnnc)) (.classMem N (synCnnc)) (synWne M (synC0)))
      (.classEq (synCtfin M) (synCtfin N))
      (.classMem (synCopk (synCtfin M) (synCtfin N)) (synCltfin)) p0023
  have p0025 :=
    @gImp
      (synW3a (.classMem M (synCnnc)) (.classMem N (synCnnc)) (synWne M (synC0)))
      (.classMem (synCopk (synCtfin M) (synCtfin N)) (synCltfin))
      (.neg (.classEq (synCtfin M) (synCtfin N))) p0024
  have p0026 := @gTfineq M N
  have p0027 :=
    @gNsyl
      (synWa (synW3a (.classMem M (synCnnc)) (.classMem N (synCnnc)) (synWne M (synC0)))
        (.classMem (synCopk (synCtfin M) (synCtfin N)) (synCltfin)))
      (.classEq (synCtfin M) (synCtfin N)) (.classEq M N) p0025 p0026
  have p0028 :=
    @gSimpl1 (.classMem M (synCnnc)) (.classMem N (synCnnc)) (synWne M (synC0))
      (synWa (.classMem (synCopk (synCtfin M) (synCtfin N)) (synCltfin))
        (synWne N (synC0)))
  have p0029 :=
    @gSimpl3 (.classMem M (synCnnc)) (.classMem N (synCnnc)) (synWne M (synC0))
      (synWa (.classMem (synCopk (synCtfin M) (synCtfin N)) (synCltfin))
        (synWne N (synC0)))
  have p0030 :=
    @gSyl2anc
      (synWa (synW3a (.classMem M (synCnnc)) (.classMem N (synCnnc)) (synWne M (synC0)))
        (synWa (.classMem (synCopk (synCtfin M) (synCtfin N)) (synCltfin))
          (synWne N (synC0))))
      (.classMem M (synCnnc)) (synWne M (synC0)) (.classMem (synCtfin M) (synCnnc))
      p0028 p0029 p0016
  have p0031 :=
    @gSimpl2 (.classMem M (synCnnc)) (.classMem N (synCnnc)) (synWne M (synC0))
      (synWa (.classMem (synCopk (synCtfin M) (synCtfin N)) (synCltfin))
        (synWne N (synC0)))
  have p0032 :=
    @gSimprr
      (synW3a (.classMem M (synCnnc)) (.classMem N (synCnnc)) (synWne M (synC0)))
      (.classMem (synCopk (synCtfin M) (synCtfin N)) (synCltfin)) (synWne N (synC0))
  have p0033 := @gTfinprop N y (by exact (show y ∉ (N).fv from (by exact fresh_y_not_N)))
  have p0034 :=
    @gSimpld (synWa (.classMem N (synCnnc)) (synWne N (synC0)))
      (.classMem (synCtfin N) (synCnnc))
      (synWrex y N (.classMem (synCpw1 (.cv y)) (synCtfin N))) p0033
  have p0035 :=
    @gSyl2anc
      (synWa (synW3a (.classMem M (synCnnc)) (.classMem N (synCnnc)) (synWne M (synC0)))
        (synWa (.classMem (synCopk (synCtfin M) (synCtfin N)) (synCltfin))
          (synWne N (synC0))))
      (.classMem N (synCnnc)) (synWne N (synC0)) (.classMem (synCtfin N) (synCnnc))
      p0031 p0032 p0034
  have p0036 :=
    @gJca
      (synWa (synW3a (.classMem M (synCnnc)) (.classMem N (synCnnc)) (synWne M (synC0)))
        (synWa (.classMem (synCopk (synCtfin M) (synCtfin N)) (synCltfin))
          (synWne N (synC0))))
      (.classMem (synCtfin M) (synCnnc)) (.classMem (synCtfin N) (synCnnc)) p0030
      p0035
  have p0037 :=
    @gSimprl
      (synW3a (.classMem M (synCnnc)) (.classMem N (synCnnc)) (synWne M (synC0)))
      (.classMem (synCopk (synCtfin M) (synCtfin N)) (synCltfin)) (synWne N (synC0))
  have p0038 := @gLtfinasym (synCtfin M) (synCtfin N)
  have p0039 :=
    @gSylc
      (synWa (synW3a (.classMem M (synCnnc)) (.classMem N (synCnnc)) (synWne M (synC0)))
        (synWa (.classMem (synCopk (synCtfin M) (synCtfin N)) (synCltfin))
          (synWne N (synC0))))
      (synWa (.classMem (synCtfin M) (synCnnc)) (.classMem (synCtfin N) (synCnnc)))
      (.classMem (synCopk (synCtfin M) (synCtfin N)) (synCltfin))
      (.neg (.classMem (synCopk (synCtfin N) (synCtfin M)) (synCltfin))) p0036 p0037
      p0038
  have p0040 :=
    @gExpr
      (synW3a (.classMem M (synCnnc)) (.classMem N (synCnnc)) (synWne M (synC0)))
      (.classMem (synCopk (synCtfin M) (synCtfin N)) (synCltfin)) (synWne N (synC0))
      (.neg (.classMem (synCopk (synCtfin N) (synCtfin M)) (synCltfin))) p0039
  have p0041 :=
    @gImnan (synWne N (synC0))
      (.classMem (synCopk (synCtfin N) (synCtfin M)) (synCltfin))
  have p0042 :=
    @gSylib
      (synWa (synW3a (.classMem M (synCnnc)) (.classMem N (synCnnc)) (synWne M (synC0)))
        (.classMem (synCopk (synCtfin M) (synCtfin N)) (synCltfin)))
      (.imp (synWne N (synC0))
        (.neg (.classMem (synCopk (synCtfin N) (synCtfin M)) (synCltfin))))
      (.neg (synWa (synWne N (synC0))
          (.classMem (synCopk (synCtfin N) (synCtfin M)) (synCltfin))))
      p0040 p0041
  have p0043 :=
    @gOpkltfing y N M (synCnnc) (synCnnc)
      (by exact (show y ∉ (N).fv from (by exact fresh_y_not_N)))
      (by exact (show y ∉ (M).fv from (by exact fresh_y_not_M)))
  have p0044 :=
    @gAncoms (.classMem N (synCnnc)) (.classMem M (synCnnc))
      (synWb (.classMem (synCopk N M) (synCltfin)) (synWa (synWne N (synC0))
          (synWrex y (synCnnc) (.classEq M (synCplc (synCplc N (.cv y)) (synC1c))))))
      p0043
  have p0045 :=
    @gN3adant3 (.classMem M (synCnnc)) (.classMem N (synCnnc))
      (synWb (.classMem (synCopk N M) (synCltfin)) (synWa (synWne N (synC0))
          (synWrex y (synCnnc) (.classEq M (synCplc (synCplc N (.cv y)) (synC1c))))))
      (synWne M (synC0)) p0044
  have p0046 :=
    @gSimprbda
      (synW3a (.classMem M (synCnnc)) (.classMem N (synCnnc)) (synWne M (synC0)))
      (.classMem (synCopk N M) (synCltfin)) (synWne N (synC0))
      (synWrex y (synCnnc) (.classEq M (synCplc (synCplc N (.cv y)) (synC1c)))) p0045
  have p0047 :=
    @gAdantrl
      (synW3a (.classMem M (synCnnc)) (.classMem N (synCnnc)) (synWne M (synC0)))
      (.classMem (synCopk N M) (synCltfin)) (synWne N (synC0))
      (.classMem (synCopk (synCtfin M) (synCtfin N)) (synCltfin)) p0046
  have p0048 :=
    @gSimpl2 (.classMem M (synCnnc)) (.classMem N (synCnnc)) (synWne M (synC0))
      (synWa (.classMem (synCopk (synCtfin M) (synCtfin N)) (synCltfin))
        (.classMem (synCopk N M) (synCltfin)))
  have p0049 :=
    @gSimpl1 (.classMem M (synCnnc)) (.classMem N (synCnnc)) (synWne M (synC0))
      (synWa (.classMem (synCopk (synCtfin M) (synCtfin N)) (synCltfin))
        (.classMem (synCopk N M) (synCltfin)))
  have p0050 :=
    @gJca
      (synWa (synW3a (.classMem M (synCnnc)) (.classMem N (synCnnc)) (synWne M (synC0)))
        (synWa (.classMem (synCopk (synCtfin M) (synCtfin N)) (synCltfin))
          (.classMem (synCopk N M) (synCltfin))))
      (.classMem N (synCnnc)) (.classMem M (synCnnc)) p0048 p0049
  have p0051 :=
    @gSimprr
      (synW3a (.classMem M (synCnnc)) (.classMem N (synCnnc)) (synWne M (synC0)))
      (.classMem (synCopk (synCtfin M) (synCtfin N)) (synCltfin))
      (.classMem (synCopk N M) (synCltfin))
  have p0052 := @gTfinltfinlem1 N M
  have p0053 :=
    @gSylc
      (synWa (synW3a (.classMem M (synCnnc)) (.classMem N (synCnnc)) (synWne M (synC0)))
        (synWa (.classMem (synCopk (synCtfin M) (synCtfin N)) (synCltfin))
          (.classMem (synCopk N M) (synCltfin))))
      (synWa (.classMem N (synCnnc)) (.classMem M (synCnnc)))
      (.classMem (synCopk N M) (synCltfin))
      (.classMem (synCopk (synCtfin N) (synCtfin M)) (synCltfin)) p0050 p0051 p0052
  have p0054 :=
    @gJca
      (synWa (synW3a (.classMem M (synCnnc)) (.classMem N (synCnnc)) (synWne M (synC0)))
        (synWa (.classMem (synCopk (synCtfin M) (synCtfin N)) (synCltfin))
          (.classMem (synCopk N M) (synCltfin))))
      (synWne N (synC0)) (.classMem (synCopk (synCtfin N) (synCtfin M)) (synCltfin))
      p0047 p0053
  have p0055 :=
    @gExpr
      (synW3a (.classMem M (synCnnc)) (.classMem N (synCnnc)) (synWne M (synC0)))
      (.classMem (synCopk (synCtfin M) (synCtfin N)) (synCltfin))
      (.classMem (synCopk N M) (synCltfin))
      (synWa (synWne N (synC0))
        (.classMem (synCopk (synCtfin N) (synCtfin M)) (synCltfin)))
      p0054
  have p0056 :=
    @gMtod
      (synWa (synW3a (.classMem M (synCnnc)) (.classMem N (synCnnc)) (synWne M (synC0)))
        (.classMem (synCopk (synCtfin M) (synCtfin N)) (synCltfin)))
      (.classMem (synCopk N M) (synCltfin))
      (synWa (synWne N (synC0))
        (.classMem (synCopk (synCtfin N) (synCtfin M)) (synCltfin)))
      p0042 p0055
  have p0057 := @gLtfintri M N
  have p0058 :=
    @gAdantr
      (synW3a (.classMem M (synCnnc)) (.classMem N (synCnnc)) (synWne M (synC0)))
      (synW3o (.classMem (synCopk M N) (synCltfin)) (.classEq M N)
        (.classMem (synCopk N M) (synCltfin)))
      (.classMem (synCopk (synCtfin M) (synCtfin N)) (synCltfin)) p0057
  have p0059 :=
    @gEcase23d
      (synWa (synW3a (.classMem M (synCnnc)) (.classMem N (synCnnc)) (synWne M (synC0)))
        (.classMem (synCopk (synCtfin M) (synCtfin N)) (synCltfin)))
      (.classMem (synCopk M N) (synCltfin)) (.classEq M N)
      (.classMem (synCopk N M) (synCltfin)) p0027 p0056 p0058
  have p0060 :=
    @gEx (synW3a (.classMem M (synCnnc)) (.classMem N (synCnnc)) (synWne M (synC0)))
      (.classMem (synCopk (synCtfin M) (synCtfin N)) (synCltfin))
      (.classMem (synCopk M N) (synCltfin)) p0059
  have p0061 :=
    @gN3expa (.classMem M (synCnnc)) (.classMem N (synCnnc)) (synWne M (synC0))
      (.imp (.classMem (synCopk (synCtfin M) (synCtfin N)) (synCltfin))
        (.classMem (synCopk M N) (synCltfin)))
      p0060
  have p0062 :=
    @gExpcom (synWa (.classMem M (synCnnc)) (.classMem N (synCnnc)))
      (synWne M (synC0))
      (.imp (.classMem (synCopk (synCtfin M) (synCtfin N)) (synCltfin))
        (.classMem (synCopk M N) (synCltfin)))
      p0061
  have p0063 :=
    @gPm261ine
      (.imp (synWa (.classMem M (synCnnc)) (.classMem N (synCnnc)))
        (.imp (.classMem (synCopk (synCtfin M) (synCtfin N)) (synCltfin))
          (.classMem (synCopk M N) (synCltfin))))
      M (synC0) p0014 p0062
  have p0064 :=
    @gImpbid (synWa (.classMem M (synCnnc)) (.classMem N (synCnnc)))
      (.classMem (synCopk M N) (synCltfin))
      (.classMem (synCopk (synCtfin M) (synCtfin N)) (synCltfin)) p0000 p0063
  exact p0064

/-- Checked nominal proof certificate identified upstream as `g_tfinlefin`. -/
@[expose]
noncomputable def gTfinlefin (M : Class) (N : Class) :
    Nominal.NPrf
      (.imp (synWa (.classMem M (synCnnc)) (.classMem N (synCnnc)))
        (synWb (.classMem (synCopk M N) (synClefin))
          (.classMem (synCopk (synCtfin M) (synCtfin N)) (synClefin)))) :=
  by
  have p0000 := @gTfinltfin N M
  have p0001 :=
    @gAncoms (.classMem N (synCnnc)) (.classMem M (synCnnc))
      (synWb (.classMem (synCopk N M) (synCltfin))
        (.classMem (synCopk (synCtfin N) (synCtfin M)) (synCltfin)))
      p0000
  have p0002 :=
    @gNotbid (synWa (.classMem M (synCnnc)) (.classMem N (synCnnc)))
      (.classMem (synCopk N M) (synCltfin))
      (.classMem (synCopk (synCtfin N) (synCtfin M)) (synCltfin)) p0001
  have p0003 := @gLenltfin M N
  have p0004 := @gTfincl M
  have p0005 := @gTfincl N
  have p0006 := @gLenltfin (synCtfin M) (synCtfin N)
  have p0007 :=
    @gSyl2an (.classMem M (synCnnc)) (.classMem (synCtfin M) (synCnnc))
      (.classMem (synCtfin N) (synCnnc))
      (synWb (.classMem (synCopk (synCtfin M) (synCtfin N)) (synClefin))
        (.neg (.classMem (synCopk (synCtfin N) (synCtfin M)) (synCltfin))))
      (.classMem N (synCnnc)) p0004 p0005 p0006
  have p0008 :=
    @gN3bitr4d (synWa (.classMem M (synCnnc)) (.classMem N (synCnnc)))
      (.neg (.classMem (synCopk N M) (synCltfin)))
      (.neg (.classMem (synCopk (synCtfin N) (synCtfin M)) (synCltfin)))
      (.classMem (synCopk M N) (synClefin))
      (.classMem (synCopk (synCtfin M) (synCtfin N)) (synClefin)) p0002 p0003 p0007
  exact p0008


end NFChoice.DirectNominalPrf.WPPReplay

end
