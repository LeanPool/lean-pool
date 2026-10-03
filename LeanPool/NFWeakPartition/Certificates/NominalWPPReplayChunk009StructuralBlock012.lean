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

@[expose]
noncomputable def g_eqtfinrelk (M : Class) (X : Class)
    (hyp_eqtfinrelk_1 : Nominal.NPrf (.classMem M (syn_cvv)))
    (hyp_eqtfinrelk_2 : Nominal.NPrf (.classMem X (syn_cvv))) :
    Nominal.NPrf
      (syn_wb (.classMem (syn_copk (syn_csn M) X)
          (syn_cun (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0))) (syn_cdif
              (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
                      (syn_cimak (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k
                            (syn_cimak (syn_csymdif (syn_cins2k
                                  (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak
                                      (syn_cin (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k
        (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c))
        (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k
        (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
        (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                                      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                                (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c)))))
                        (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
              (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv)))))
        (.classEq X (syn_ctfin M))) :=
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
    (.classMem (syn_copk (syn_csn (syn_c0)) X)
      (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0))))
  let syntaxClass0001 : Class :=
    (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk))))
      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))
  let syntaxClass0002 : Class :=
    (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) syntaxClass0001)
  let syntaxClass0003 : Class := (syn_csik syntaxClass0002)
  let syntaxClass0004 : Class := (syn_cins3k syntaxClass0003)
  let syntaxClass0005 : Class := (syn_cin syntaxClass0004 (syn_cins2k (syn_cssetk)))
  let syntaxClass0006 : Class :=
    (syn_cimak syntaxClass0005 (syn_cpw1 (syn_cpw1 (syn_c1c))))
  let syntaxClass0007 : Class := (syn_cins3k syntaxClass0006)
  let syntaxClass0008 : Class :=
    (syn_cin (syn_cins2k (syn_csik (syn_cssetk))) syntaxClass0007)
  let syntaxClass0009 : Class :=
    (syn_cimak syntaxClass0008 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))
  let syntaxClass0010 : Class := (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) syntaxClass0009)
  let syntaxClass0011 : Class := (syn_cins2k syntaxClass0010)
  let syntaxClass0012 : Class := (syn_csymdif syntaxClass0011 (syn_cins3k (syn_cidk)))
  let syntaxClass0013 : Class := (syn_cimak syntaxClass0012 (syn_cpw1 (syn_c1c)))
  let syntaxClass0014 : Class := (syn_cins2k syntaxClass0013)
  let syntaxClass0015 : Class :=
    (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) syntaxClass0014)
  let syntaxClass0016 : Class := (syn_cimak syntaxClass0015 (syn_cpw1 (syn_c1c)))
  let syntaxClass0017 : Class := (syn_cins3k syntaxClass0016)
  let syntaxClass0018 : Class := (syn_csymdif (syn_cins2k (syn_cssetk)) syntaxClass0017)
  let syntaxClass0019 : Class :=
    (syn_cimak syntaxClass0018 (syn_cpw1 (syn_cpw1 (syn_c1c))))
  let syntaxClass0020 : Class := (syn_ccompl syntaxClass0019)
  let syntaxClass0021 : Class :=
    (syn_cdif syntaxClass0020 (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv)))
  let syntaxFormula0022 : Wff :=
    (.classMem (syn_copk (syn_csn (syn_c0)) X) syntaxClass0021)
  let syntaxFormula0023 : Wff :=
    (.classMem (syn_copk (syn_csn (syn_c0)) X)
      (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv)))
  let syntaxFormula0024 : Wff :=
    (.classMem (syn_copk (syn_csn (syn_c0)) X) syntaxClass0020)
  let syntaxClass0025 : Class :=
    (syn_cun (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0))) syntaxClass0021)
  let syntaxFormula0026 : Wff :=
    (.classMem (syn_copk (syn_csn (syn_c0)) X) syntaxClass0025)
  let syntaxFormula0027 : Wff :=
    (syn_wa (.classMem (.cv y) (syn_cnnc))
      (syn_wrex a M (.classMem (syn_cpw1 (.cv a)) (.cv y))))
  let syntaxClass0028 : Class := (syn_cio y syntaxFormula0027)
  let syntaxClass0029 : Class := (syn_cif (.classEq M (syn_c0)) (syn_c0) syntaxClass0028)
  let syntaxFormula0030 : Wff := (.classMem (syn_copk (syn_csn M) X) syntaxClass0025)
  let syntaxFormula0031 : Wff := (.classEq X syntaxClass0029)
  let syntaxFormula0032 : Wff :=
    (.classMem (syn_copk (.cv t) (syn_copk (syn_csn M) X)) syntaxClass0018)
  let syntaxFormula0033 : Wff :=
    (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_cpw1 (syn_c1c)))) syntaxFormula0032)
  let syntaxFormula0034 : Wff :=
    (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv z))))) syntaxFormula0032)
  let syntaxFormula0035 : Wff := (syn_wex z syntaxFormula0034)
  let syntaxFormula0036 : Wff :=
    (syn_wrex t (syn_cpw1 (syn_cpw1 (syn_c1c))) syntaxFormula0032)
  let syntaxFormula0037 : Wff := (syn_wex t syntaxFormula0034)
  let syntaxFormula0038 : Wff := (syn_wex z syntaxFormula0037)
  let syntaxFormula0039 : Wff :=
    (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv z)))) (syn_copk (syn_csn M) X))
      syntaxClass0018)
  let syntaxFormula0040 : Wff :=
    (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv z)))) (syn_copk (syn_csn M) X))
      (syn_cins2k (syn_cssetk)))
  let syntaxFormula0041 : Wff :=
    (.classMem (syn_copk (.cv t) (syn_copk (syn_csn (.cv z)) (syn_csn M))) syntaxClass0015)
  let syntaxFormula0042 : Wff :=
    (.classMem (syn_copk (syn_csn (syn_csn (.cv n))) (syn_copk (syn_csn (.cv z)) (syn_csn M)))
      syntaxClass0015)
  let syntaxFormula0043 : Wff :=
    (.classMem (syn_copk (syn_csn (syn_csn (.cv n))) (syn_copk (syn_csn (.cv z)) (syn_csn M)))
      (syn_cins3k (syn_ccnvk (syn_cssetk))))
  let syntaxFormula0044 : Wff :=
    (.classMem (syn_copk (.cv t) (syn_copk (.cv n) (syn_csn M))) syntaxClass0012)
  let syntaxFormula0045 : Wff :=
    (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_c1c))) syntaxFormula0044)
  let syntaxFormula0046 : Wff :=
    (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (.cv y)))) syntaxFormula0044)
  let syntaxFormula0047 : Wff := (syn_wex y syntaxFormula0046)
  let syntaxFormula0048 : Wff := (syn_wrex t (syn_cpw1 (syn_c1c)) syntaxFormula0044)
  let syntaxFormula0049 : Wff := (syn_wex t syntaxFormula0046)
  let syntaxFormula0050 : Wff := (syn_wex y syntaxFormula0049)
  let syntaxFormula0051 : Wff :=
    (.classMem (syn_copk (syn_csn (syn_csn (.cv y))) (syn_copk (.cv n) (syn_csn M)))
      syntaxClass0012)
  let syntaxClass0052 : Class :=
    (syn_copk (syn_csn (syn_csn (syn_csn (syn_csn (.cv a))))) (syn_copk (.cv y) (syn_csn M)))
  let syntaxFormula0053 : Wff :=
    (.classMem (syn_copk (.cv t) (syn_copk (.cv y) (syn_csn M))) syntaxClass0008)
  let syntaxFormula0054 : Wff := (.classMem syntaxClass0052 syntaxClass0008)
  let syntaxFormula0055 : Wff :=
    (.classMem syntaxClass0052 (syn_cins2k (syn_csik (syn_cssetk))))
  let syntaxFormula0056 : Wff :=
    (.classMem (syn_copk (.cv t) (syn_copk (syn_csn (syn_csn (.cv a))) (.cv y)))
      syntaxClass0005)
  let syntaxFormula0057 : Wff :=
    (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_cpw1 (syn_c1c)))) syntaxFormula0056)
  let syntaxFormula0058 : Wff :=
    (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv x))))) syntaxFormula0056)
  let syntaxFormula0059 : Wff := (syn_wex x syntaxFormula0058)
  let syntaxFormula0060 : Wff :=
    (syn_wrex t (syn_cpw1 (syn_cpw1 (syn_c1c))) syntaxFormula0056)
  let syntaxFormula0061 : Wff := (syn_wex t syntaxFormula0058)
  let syntaxFormula0062 : Wff := (syn_wex x syntaxFormula0061)
  let syntaxClass0063 : Class :=
    (syn_copk (syn_csn (syn_csn (syn_csn (.cv x))))
      (syn_copk (syn_csn (syn_csn (.cv a))) (.cv y)))
  let syntaxFormula0064 : Wff := (.classMem syntaxClass0063 syntaxClass0005)
  let syntaxFormula0065 : Wff := (.classMem syntaxClass0063 syntaxClass0004)
  let syntaxFormula0066 : Wff := (.classMem syntaxClass0063 (syn_cins2k (syn_cssetk)))
  let syntaxFormula0067 : Wff :=
    (.classMem (syn_copk (syn_csn (syn_csn (.cv a))) (.cv y)) syntaxClass0006)
  let syntaxFormula0068 : Wff := (.classMem syntaxClass0052 syntaxClass0007)
  let syntaxFormula0069 : Wff :=
    (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (syn_csn (.cv a))))))
      syntaxFormula0053)
  let syntaxFormula0070 : Wff := (syn_wex t syntaxFormula0069)
  let syntaxFormula0071 : Wff :=
    (syn_wrex t (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))) syntaxFormula0053)
  let syntaxFormula0072 : Wff :=
    (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))) syntaxFormula0053)
  let syntaxFormula0073 : Wff := (syn_wex a syntaxFormula0069)
  let syntaxFormula0074 : Wff := (syn_wex t syntaxFormula0073)
  let syntaxFormula0075 : Wff :=
    (.classMem (syn_copk (.cv y) (syn_csn M)) syntaxClass0009)
  let syntaxFormula0076 : Wff := (syn_wex a syntaxFormula0070)
  let syntaxFormula0077 : Wff :=
    (.classMem (syn_copk (syn_csn (syn_csn (.cv y))) (syn_copk (.cv n) (syn_csn M)))
      syntaxClass0011)
  let syntaxFormula0078 : Wff :=
    (.classMem (syn_copk (syn_csn (syn_csn (.cv y))) (syn_copk (.cv n) (syn_csn M)))
      (syn_cins3k (syn_cidk)))
  let syntaxFormula0079 : Wff :=
    (.classMem (syn_copk (.cv n) (syn_csn M)) syntaxClass0013)
  let syntaxFormula0080 : Wff :=
    (.classMem (syn_copk (syn_csn (syn_csn (.cv n))) (syn_copk (syn_csn (.cv z)) (syn_csn M)))
      syntaxClass0014)
  let syntaxFormula0081 : Wff := (.neg syntaxFormula0080)
  let syntaxFormula0082 : Wff :=
    (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (.cv n)))) syntaxFormula0041)
  let syntaxFormula0083 : Wff := (syn_wex t syntaxFormula0082)
  let syntaxFormula0084 : Wff :=
    (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_c1c))) syntaxFormula0041)
  let syntaxFormula0085 : Wff := (syn_wex n syntaxFormula0082)
  let syntaxFormula0086 : Wff := (syn_wrex t (syn_cpw1 (syn_c1c)) syntaxFormula0041)
  let syntaxFormula0087 : Wff := (syn_wex n syntaxFormula0083)
  let syntaxFormula0088 : Wff :=
    (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv z)))) (syn_copk (syn_csn M) X))
      syntaxClass0017)
  let syntaxFormula0089 : Wff := (.classMem (.cv z) syntaxClass0028)
  let syntaxFormula0090 : Wff := (syn_wb (.classMem (.cv z) X) syntaxFormula0089)
  let syntaxFormula0091 : Wff := (.neg syntaxFormula0090)
  let syntaxFormula0092 : Wff := (.classMem (syn_copk (syn_csn M) X) syntaxClass0019)
  let syntaxFormula0093 : Wff := (syn_wex z syntaxFormula0091)
  let syntaxFormula0094 : Wff := (.classEq X syntaxClass0028)
  let syntaxFormula0095 : Wff := (.neg syntaxFormula0093)
  let syntaxFormula0096 : Wff := (.classMem (syn_copk (syn_csn M) X) syntaxClass0020)
  let syntaxFormula0097 : Wff :=
    (.classMem (syn_copk (syn_csn M) X) (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv)))
  let syntaxFormula0098 : Wff := (.neg syntaxFormula0097)
  let syntaxFormula0099 : Wff := (syn_wa syntaxFormula0096 syntaxFormula0098)
  let syntaxFormula0100 : Wff :=
    (syn_wo (syn_wa (.classEq M (syn_c0)) (.classEq X (syn_c0))) syntaxFormula0099)
  let syntaxFormula0101 : Wff :=
    (.classMem (syn_copk (syn_csn M) X)
      (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0))))
  let syntaxFormula0102 : Wff := (.classMem (syn_copk (syn_csn M) X) syntaxClass0021)
  let syntaxFormula0103 : Wff := (syn_wo syntaxFormula0101 syntaxFormula0102)
  have p0000 := @g_snex (syn_c0)
  have p0001 := @g_snid (syn_csn (syn_c0)) p0000
  have p0002 :=
    @g_opkelxpk (syn_csn (syn_c0)) X (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0)) p0000
      hyp_eqtfinrelk_2
  have p0003 :=
    @g_mpbiran syntaxFormula0000
      (.classMem (syn_csn (syn_c0)) (syn_csn (syn_csn (syn_c0))))
      (.classMem X (syn_csn (syn_c0))) p0001 p0002
  have p0004 := @g_elsnc X (syn_c0) hyp_eqtfinrelk_2
  have p0005 :=
    @g_bitri syntaxFormula0000 (.classMem X (syn_csn (syn_c0))) (.classEq X (syn_c0))
      p0003 p0004
  have p0006 := @g_orbi1i syntaxFormula0000 (.classEq X (syn_c0)) syntaxFormula0022 p0005
  have p0007 :=
    @g_elun (syn_copk (syn_csn (syn_c0)) X)
      (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0))) syntaxClass0021
  have p0008 :=
    @g_opkelxpk (syn_csn (syn_c0)) X (syn_csn (syn_csn (syn_c0))) (syn_cvv) p0000
      hyp_eqtfinrelk_2
  have p0009 :=
    @g_mpbir2an syntaxFormula0023
      (.classMem (syn_csn (syn_c0)) (syn_csn (syn_csn (syn_c0)))) (.classMem X (syn_cvv))
      p0001 hyp_eqtfinrelk_2 p0008
  have p0010 := @g_notnoti syntaxFormula0023 p0009
  have p0011 := @g_intnan (.neg syntaxFormula0023) syntaxFormula0024 p0010
  have p0012 :=
    @g_eldif (syn_copk (syn_csn (syn_c0)) X) syntaxClass0020
      (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv))
  have p0013 :=
    @g_mtbir syntaxFormula0022 (syn_wa syntaxFormula0024 (.neg syntaxFormula0023)) p0011
      p0012
  have p0014 := @g_biorfi syntaxFormula0022 (.classEq X (syn_c0)) p0013
  have p0015 :=
    @g_n_3bitr4i (syn_wo syntaxFormula0000 syntaxFormula0022)
      (syn_wo (.classEq X (syn_c0)) syntaxFormula0022) syntaxFormula0026
      (.classEq X (syn_c0)) p0006 p0007 p0014
  have p0016 :=
    @g_a1i (syn_wb syntaxFormula0026 (.classEq X (syn_c0))) (.classEq M (syn_c0)) p0015
  have p0017 := @g_sneq M (syn_c0)
  have p0018 := @g_opkeq1d (.classEq M (syn_c0)) (syn_csn M) (syn_csn (syn_c0)) X p0017
  have p0019 :=
    @g_eleq1d (.classEq M (syn_c0)) (syn_copk (syn_csn M) X)
      (syn_copk (syn_csn (syn_c0)) X) syntaxClass0025 p0018
  have p0020 := @g_iftrue (.classEq M (syn_c0)) (syn_c0) syntaxClass0028
  have p0021 := @g_eqeq2d (.classEq M (syn_c0)) syntaxClass0029 (syn_c0) X p0020
  have p0022 :=
    @g_n_3bitr4d (.classEq M (syn_c0)) syntaxFormula0026 (.classEq X (syn_c0))
      syntaxFormula0030 syntaxFormula0031 p0016 p0019 p0021
  have p0023 := @g_iffalse (.classEq M (syn_c0)) (syn_c0) syntaxClass0028
  have p0024 :=
    @g_eqeq2d (.neg (.classEq M (syn_c0))) syntaxClass0029 syntaxClass0028 X p0023
  have p0025 := @g_opkex (syn_csn M) X
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
  have freeVariableCertificate1 : t ∉ ((syn_cpw1 (syn_cpw1 (syn_c1c)))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.notMem_empty,
      not_false_eq_true]
  have freeVariableCertificate2 : t ∉ ((syn_copk (syn_csn M) X)).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
      fresh_t_not_M, fresh_t_not_X, or_false, not_false_eq_true]
  have p0026 :=
    @g_elimak t syntaxClass0018 (syn_cpw1 (syn_cpw1 (syn_c1c))) (syn_copk (syn_csn M) X)
      freeVariableCertificate0 freeVariableCertificate1 freeVariableCertificate2 p0025
  have freeVariableCertificate3 : z ∉ ((Class.cv t)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_z_ne_t, not_false_eq_true]
  have p0027 := @g_elpw121c z (.cv t) freeVariableCertificate3
  have p0028 :=
    @g_anbi1i (.classMem (.cv t) (syn_cpw1 (syn_cpw1 (syn_c1c))))
      (syn_wex z (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv z))))))
      syntaxFormula0032 p0027
  have freeVariableCertificate4 :
    z ∉ ((Wff.classMem (syn_copk (.cv t) (syn_copk (syn_csn M) X)) syntaxClass0018)).fv :=
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
    @g_n_19_41v (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv z))))) syntaxFormula0032
      z freeVariableCertificate4
  have p0030 :=
    @g_bitr4i syntaxFormula0033
      (syn_wa (syn_wex z (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv z))))))
        syntaxFormula0032)
      syntaxFormula0035 p0028 p0029
  have p0031 := @g_exbii syntaxFormula0033 syntaxFormula0035 t p0030
  have p0032 := (Nominal.biimpRefl syntaxFormula0036)
  have p0033 := @g_excom syntaxFormula0034 z t
  have p0034 :=
    @g_n_3bitr4i (syn_wex t syntaxFormula0033) (syn_wex t syntaxFormula0035)
      syntaxFormula0036 syntaxFormula0038 p0031 p0032 p0033
  have p0035 := @g_snex (syn_csn (syn_csn (.cv z)))
  have p0036 :=
    @g_opkeq1 (.cv t) (syn_csn (syn_csn (syn_csn (.cv z)))) (syn_copk (syn_csn M) X)
  have p0037 :=
    @g_eleq1d (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv z)))))
      (syn_copk (.cv t) (syn_copk (syn_csn M) X))
      (syn_copk (syn_csn (syn_csn (syn_csn (.cv z)))) (syn_copk (syn_csn M) X))
      syntaxClass0018 p0036
  have freeVariableCertificate5 : t ∉ ((syn_csn (syn_csn (syn_csn (.cv z))))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_t_ne_z,
      not_false_eq_true]
  have freeVariableCertificate6 :
    t ∉
      ((Wff.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv z)))) (syn_copk (syn_csn M) X))
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
    @g_ceqsexv syntaxFormula0032 syntaxFormula0039 t (syn_csn (syn_csn (syn_csn (.cv z))))
      freeVariableCertificate5 freeVariableCertificate6 p0035 p0037
  have p0039 :=
    @g_elsymdif (syn_copk (syn_csn (syn_csn (syn_csn (.cv z)))) (syn_copk (syn_csn M) X))
      (syn_cins2k (syn_cssetk)) syntaxClass0017
  have p0040 := @g_snex (.cv z)
  have p0041 := @g_snex M
  have p0042 :=
    @g_otkelins2k (syn_csn (.cv z)) (syn_csn M) X (syn_cssetk) p0040 p0041
      hyp_eqtfinrelk_2
  have p0043 := @g_vex z
  have p0044 := @g_elssetk (.cv z) X p0043 hyp_eqtfinrelk_2
  have p0045 :=
    @g_bitri syntaxFormula0040 (.classMem (syn_copk (syn_csn (.cv z)) X) (syn_cssetk))
      (.classMem (.cv z) X) p0042 p0044
  have p0046 := @g_snex (syn_csn (.cv n))
  have p0047 :=
    @g_opkeq1 (.cv t) (syn_csn (syn_csn (.cv n))) (syn_copk (syn_csn (.cv z)) (syn_csn M))
  have p0048 :=
    @g_eleq1d (.classEq (.cv t) (syn_csn (syn_csn (.cv n))))
      (syn_copk (.cv t) (syn_copk (syn_csn (.cv z)) (syn_csn M)))
      (syn_copk (syn_csn (syn_csn (.cv n))) (syn_copk (syn_csn (.cv z)) (syn_csn M)))
      syntaxClass0015 p0047
  have freeVariableCertificate7 : t ∉ ((syn_csn (syn_csn (.cv n)))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_t_ne_n,
      not_false_eq_true]
  have freeVariableCertificate8 :
    t ∉
      ((Wff.classMem
          (syn_copk (syn_csn (syn_csn (.cv n))) (syn_copk (syn_csn (.cv z)) (syn_csn M)))
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
    @g_ceqsexv syntaxFormula0041 syntaxFormula0042 t (syn_csn (syn_csn (.cv n)))
      freeVariableCertificate7 freeVariableCertificate8 p0046 p0048
  have p0050 :=
    @g_eldif
      (syn_copk (syn_csn (syn_csn (.cv n))) (syn_copk (syn_csn (.cv z)) (syn_csn M)))
      (syn_cins3k (syn_ccnvk (syn_cssetk))) syntaxClass0014
  have p0051 := @g_vex n
  have p0052 :=
    @g_otkelins3k (.cv n) (syn_csn (.cv z)) (syn_csn M) (syn_ccnvk (syn_cssetk)) p0051
      p0040 p0041
  have p0053 := @g_opkelcnvk (.cv n) (syn_csn (.cv z)) (syn_cssetk) p0051 p0040
  have p0054 := @g_elssetk (.cv z) (.cv n) p0043 p0051
  have p0055_e02_recanon :
    Nominal.NPrf
      (syn_wb (.classMem (syn_copk (syn_csn (.cv z)) (.cv n)) (syn_cssetk)) (.objMem z n)) :=
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
      p0054
  have p0055 :=
    @g_n_3bitri syntaxFormula0043
      (.classMem (syn_copk (.cv n) (syn_csn (.cv z))) (syn_ccnvk (syn_cssetk)))
      (.classMem (syn_copk (syn_csn (.cv z)) (.cv n)) (syn_cssetk)) (.objMem z n) p0052
      p0053 p0055_e02_recanon
  have p0056 :=
    @g_otkelins2k (.cv n) (syn_csn (.cv z)) (syn_csn M) syntaxClass0013 p0051 p0040 p0041
  have p0057 := @g_opkex (.cv n) (syn_csn M)
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
  have freeVariableCertificate10 : t ∉ ((syn_cpw1 (syn_c1c))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.notMem_empty,
      not_false_eq_true]
  have freeVariableCertificate11 : t ∉ ((syn_copk (.cv n) (syn_csn M))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
      Finset.mem_singleton, fresh_t_ne_n, fresh_t_not_M, or_false, not_false_eq_true]
  have p0058 :=
    @g_elimak t syntaxClass0012 (syn_cpw1 (syn_c1c)) (syn_copk (.cv n) (syn_csn M))
      freeVariableCertificate9 freeVariableCertificate10 freeVariableCertificate11 p0057
  have freeVariableCertificate12 : y ∉ ((Class.cv t)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_y_ne_t, not_false_eq_true]
  have p0059 := @g_elpw11c y (.cv t) freeVariableCertificate12
  have p0060 :=
    @g_anbi1i (.classMem (.cv t) (syn_cpw1 (syn_c1c)))
      (syn_wex y (.classEq (.cv t) (syn_csn (syn_csn (.cv y))))) syntaxFormula0044 p0059
  have freeVariableCertificate13 :
    y ∉
      ((Wff.classMem (syn_copk (.cv t) (syn_copk (.cv n) (syn_csn M))) syntaxClass0012)).fv :=
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
    @g_n_19_41v (.classEq (.cv t) (syn_csn (syn_csn (.cv y)))) syntaxFormula0044 y
      freeVariableCertificate13
  have p0062 :=
    @g_bitr4i syntaxFormula0045
      (syn_wa (syn_wex y (.classEq (.cv t) (syn_csn (syn_csn (.cv y))))) syntaxFormula0044)
      syntaxFormula0047 p0060 p0061
  have p0063 := @g_exbii syntaxFormula0045 syntaxFormula0047 t p0062
  have p0064 := (Nominal.biimpRefl syntaxFormula0048)
  have p0065 := @g_excom syntaxFormula0046 y t
  have p0066 :=
    @g_n_3bitr4i (syn_wex t syntaxFormula0045) (syn_wex t syntaxFormula0047)
      syntaxFormula0048 syntaxFormula0050 p0063 p0064 p0065
  have p0067 := @g_snex (syn_csn (.cv y))
  have p0068 :=
    @g_opkeq1 (.cv t) (syn_csn (syn_csn (.cv y))) (syn_copk (.cv n) (syn_csn M))
  have p0069 :=
    @g_eleq1d (.classEq (.cv t) (syn_csn (syn_csn (.cv y))))
      (syn_copk (.cv t) (syn_copk (.cv n) (syn_csn M)))
      (syn_copk (syn_csn (syn_csn (.cv y))) (syn_copk (.cv n) (syn_csn M)))
      syntaxClass0012 p0068
  have freeVariableCertificate14 : t ∉ ((syn_csn (syn_csn (.cv y)))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_t_ne_y,
      not_false_eq_true]
  have freeVariableCertificate15 :
    t ∉
      ((Wff.classMem (syn_copk (syn_csn (syn_csn (.cv y))) (syn_copk (.cv n) (syn_csn M)))
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
    @g_ceqsexv syntaxFormula0044 syntaxFormula0051 t (syn_csn (syn_csn (.cv y)))
      freeVariableCertificate14 freeVariableCertificate15 p0067 p0069
  have p0071 :=
    @g_elsymdif (syn_copk (syn_csn (syn_csn (.cv y))) (syn_copk (.cv n) (syn_csn M)))
      syntaxClass0011 (syn_cins3k (syn_cidk))
  have p0072 := @g_vex y
  have p0073 :=
    @g_otkelins2k (.cv y) (.cv n) (syn_csn M) syntaxClass0010 p0072 p0051 p0041
  have p0074 :=
    @g_elin (syn_copk (.cv y) (syn_csn M)) (syn_cxpk (syn_cnnc) (syn_cvv)) syntaxClass0009
  have p0075 := @g_opkelxpk (.cv y) (syn_csn M) (syn_cnnc) (syn_cvv) p0072 p0041
  have p0076 :=
    @g_mpbiran2 (.classMem (syn_copk (.cv y) (syn_csn M)) (syn_cxpk (syn_cnnc) (syn_cvv)))
      (.classMem (.cv y) (syn_cnnc)) (.classMem (syn_csn M) (syn_cvv)) p0041 p0075
  have p0077 := @g_snex (syn_csn (syn_csn (syn_csn (.cv a))))
  have p0078 :=
    @g_opkeq1 (.cv t) (syn_csn (syn_csn (syn_csn (syn_csn (.cv a)))))
      (syn_copk (.cv y) (syn_csn M))
  have p0079 :=
    @g_eleq1d (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (syn_csn (.cv a))))))
      (syn_copk (.cv t) (syn_copk (.cv y) (syn_csn M))) syntaxClass0052 syntaxClass0008
      p0078
  have freeVariableCertificate16 :
    t ∉ ((syn_csn (syn_csn (syn_csn (syn_csn (.cv a)))))).fv := by
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
    @g_ceqsexv syntaxFormula0053 syntaxFormula0054 t
      (syn_csn (syn_csn (syn_csn (syn_csn (.cv a))))) freeVariableCertificate16
      freeVariableCertificate17 p0077 p0079
  have p0081 :=
    @g_elin syntaxClass0052 (syn_cins2k (syn_csik (syn_cssetk))) syntaxClass0007
  have p0082 := @g_snex (syn_csn (.cv a))
  have p0083 :=
    @g_otkelins2k (syn_csn (syn_csn (.cv a))) (.cv y) (syn_csn M) (syn_csik (syn_cssetk))
      p0082 p0072 p0041
  have p0084 := @g_snex (.cv a)
  have p0085 := @g_opksnelsik (syn_csn (.cv a)) M (syn_cssetk) p0084 hyp_eqtfinrelk_1
  have p0086 := @g_vex a
  have p0087 := @g_elssetk (.cv a) M p0086 hyp_eqtfinrelk_1
  have p0088 :=
    @g_n_3bitri syntaxFormula0055
      (.classMem (syn_copk (syn_csn (syn_csn (.cv a))) (syn_csn M)) (syn_csik (syn_cssetk)))
      (.classMem (syn_copk (syn_csn (.cv a)) M) (syn_cssetk)) (.classMem (.cv a) M) p0083
      p0085 p0087
  have p0089 := @g_opkex (syn_csn (syn_csn (.cv a))) (.cv y)
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
    t ∉ ((syn_copk (syn_csn (syn_csn (.cv a))) (.cv y))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      fresh_t_ne_a, fresh_t_ne_y, or_false, not_false_eq_true]
  have p0090 :=
    @g_elimak t syntaxClass0005 (syn_cpw1 (syn_cpw1 (syn_c1c)))
      (syn_copk (syn_csn (syn_csn (.cv a))) (.cv y)) freeVariableCertificate18
      freeVariableCertificate1 freeVariableCertificate19 p0089
  have freeVariableCertificate20 : x ∉ ((Class.cv t)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_x_ne_t, not_false_eq_true]
  have p0091 := @g_elpw121c x (.cv t) freeVariableCertificate20
  have p0092 :=
    @g_anbi1i (.classMem (.cv t) (syn_cpw1 (syn_cpw1 (syn_c1c))))
      (syn_wex x (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv x))))))
      syntaxFormula0056 p0091
  have freeVariableCertificate21 :
    x ∉
      ((Wff.classMem (syn_copk (.cv t) (syn_copk (syn_csn (syn_csn (.cv a))) (.cv y)))
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
    @g_n_19_41v (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv x))))) syntaxFormula0056
      x freeVariableCertificate21
  have p0094 :=
    @g_bitr4i syntaxFormula0057
      (syn_wa (syn_wex x (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv x))))))
        syntaxFormula0056)
      syntaxFormula0059 p0092 p0093
  have p0095 := @g_exbii syntaxFormula0057 syntaxFormula0059 t p0094
  have p0096 := (Nominal.biimpRefl syntaxFormula0060)
  have p0097 := @g_excom syntaxFormula0058 x t
  have p0098 :=
    @g_n_3bitr4i (syn_wex t syntaxFormula0057) (syn_wex t syntaxFormula0059)
      syntaxFormula0060 syntaxFormula0062 p0095 p0096 p0097
  have p0099 := @g_snex (syn_csn (syn_csn (.cv x)))
  have p0100 :=
    @g_opkeq1 (.cv t) (syn_csn (syn_csn (syn_csn (.cv x))))
      (syn_copk (syn_csn (syn_csn (.cv a))) (.cv y))
  have p0101 :=
    @g_eleq1d (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv x)))))
      (syn_copk (.cv t) (syn_copk (syn_csn (syn_csn (.cv a))) (.cv y))) syntaxClass0063
      syntaxClass0005 p0100
  have freeVariableCertificate22 : t ∉ ((syn_csn (syn_csn (syn_csn (.cv x))))).fv := by
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
    @g_ceqsexv syntaxFormula0056 syntaxFormula0064 t (syn_csn (syn_csn (syn_csn (.cv x))))
      freeVariableCertificate22 freeVariableCertificate23 p0099 p0101
  have p0103 := @g_elin syntaxClass0063 syntaxClass0004 (syn_cins2k (syn_cssetk))
  have p0104 := @g_snex (.cv x)
  have p0105 :=
    @g_otkelins3k (syn_csn (.cv x)) (syn_csn (syn_csn (.cv a))) (.cv y) syntaxClass0003
      p0104 p0082 p0072
  have p0106 := @g_vex x
  have p0107 := @g_opksnelsik (.cv x) (syn_csn (.cv a)) syntaxClass0002 p0106 p0084
  have p0108 := @g_eqpw1relk (.cv x) (.cv a) p0106 p0086
  have p0109 :=
    @g_n_3bitri syntaxFormula0065
      (.classMem (syn_copk (syn_csn (.cv x)) (syn_csn (syn_csn (.cv a)))) syntaxClass0003)
      (.classMem (syn_copk (.cv x) (syn_csn (.cv a))) syntaxClass0002)
      (.classEq (.cv x) (syn_cpw1 (.cv a))) p0105 p0107 p0108
  have p0110 :=
    @g_otkelins2k (syn_csn (.cv x)) (syn_csn (syn_csn (.cv a))) (.cv y) (syn_cssetk) p0104
      p0082 p0072
  have p0111 := @g_elssetk (.cv x) (.cv y) p0106 p0072
  have p0112_e01_recanon :
    Nominal.NPrf
      (syn_wb (.classMem (syn_copk (syn_csn (.cv x)) (.cv y)) (syn_cssetk)) (.objMem x y)) :=
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
      p0111
  have p0112 :=
    @g_bitri syntaxFormula0066
      (.classMem (syn_copk (syn_csn (.cv x)) (.cv y)) (syn_cssetk)) (.objMem x y) p0110
      p0112_e01_recanon
  have p0113 :=
    @g_anbi12i syntaxFormula0065 (.classEq (.cv x) (syn_cpw1 (.cv a))) syntaxFormula0066
      (.objMem x y) p0109 p0112
  have p0114 :=
    @g_n_3bitri syntaxFormula0061 syntaxFormula0064
      (syn_wa syntaxFormula0065 syntaxFormula0066)
      (syn_wa (.classEq (.cv x) (syn_cpw1 (.cv a))) (.objMem x y)) p0102 p0103 p0113
  have p0115 :=
    @g_exbii syntaxFormula0061
      (syn_wa (.classEq (.cv x) (syn_cpw1 (.cv a))) (.objMem x y)) x p0114
  have p0116 :=
    @g_n_3bitri syntaxFormula0067 syntaxFormula0060 syntaxFormula0062
      (syn_wex x (syn_wa (.classEq (.cv x) (syn_cpw1 (.cv a))) (.objMem x y))) p0090 p0098
      p0115
  have p0117 :=
    @g_otkelins3k (syn_csn (syn_csn (.cv a))) (.cv y) (syn_csn M) syntaxClass0006 p0082
      p0072 p0041
  have freeVariableCertificate24 : x ∉ ((syn_cpw1 (.cv a))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_x_ne_a,
      not_false_eq_true]
  have freeVariableCertificate25 : x ∉ ((Class.cv y)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_x_ne_y, not_false_eq_true]
  have p0118 :=
    (NFChoice.DirectNominalPrf.Nominal.DefinitionLeafHandlersCanonical001.dfClelOfDV x
      (syn_cpw1 (.cv a)) (.cv y) freeVariableCertificate24 freeVariableCertificate25)
  have p0119_e02_recanon :
    Nominal.NPrf
      (syn_wb (.classMem (syn_cpw1 (.cv a)) (.cv y))
        (syn_wex x (syn_wa (.classEq (.cv x) (syn_cpw1 (.cv a))) (.objMem x y)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [syn_wb, syn_cpw1, syn_cin, syn_ccompl, syn_cnin, syn_wnan, syn_wa,
          syn_cpw, syn_wss, syn_c1c, syn_wex, syn_csn]
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
    @g_n_3bitr4i syntaxFormula0067
      (syn_wex x (syn_wa (.classEq (.cv x) (syn_cpw1 (.cv a))) (.objMem x y)))
      syntaxFormula0068 (.classMem (syn_cpw1 (.cv a)) (.cv y)) p0116 p0117
      p0119_e02_recanon
  have p0120 :=
    @g_anbi12i syntaxFormula0055 (.classMem (.cv a) M) syntaxFormula0068
      (.classMem (syn_cpw1 (.cv a)) (.cv y)) p0088 p0119
  have p0121 :=
    @g_n_3bitri syntaxFormula0070 syntaxFormula0054
      (syn_wa syntaxFormula0055 syntaxFormula0068)
      (syn_wa (.classMem (.cv a) M) (.classMem (syn_cpw1 (.cv a)) (.cv y))) p0080 p0081
      p0120
  have p0122 :=
    @g_exbii syntaxFormula0070
      (syn_wa (.classMem (.cv a) M) (.classMem (syn_cpw1 (.cv a)) (.cv y))) a p0121
  have p0123 := (Nominal.biimpRefl syntaxFormula0071)
  have freeVariableCertificate26 : a ∉ ((Class.cv t)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_a_ne_t, not_false_eq_true]
  have p0124 := @g_elpw131c a (.cv t) freeVariableCertificate26
  have p0125 :=
    @g_anbi1i (.classMem (.cv t) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))
      (syn_wex a (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (syn_csn (.cv a)))))))
      syntaxFormula0053 p0124
  have freeVariableCertificate27 :
    a ∉
      ((Wff.classMem (syn_copk (.cv t) (syn_copk (.cv y) (syn_csn M))) syntaxClass0008)).fv :=
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
    @g_n_19_41v (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (syn_csn (.cv a))))))
      syntaxFormula0053 a freeVariableCertificate27
  have p0127 :=
    @g_bitr4i syntaxFormula0072
      (syn_wa (syn_wex a (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (syn_csn (.cv a)))))))
        syntaxFormula0053)
      syntaxFormula0073 p0125 p0126
  have p0128 := @g_exbii syntaxFormula0072 syntaxFormula0073 t p0127
  have p0129 :=
    @g_bitri syntaxFormula0071 (syn_wex t syntaxFormula0072) syntaxFormula0074 p0123 p0128
  have p0130 := @g_opkex (.cv y) (syn_csn M)
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
  have freeVariableCertificate29 : t ∉ ((syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.notMem_empty,
      not_false_eq_true]
  have freeVariableCertificate30 : t ∉ ((syn_copk (.cv y) (syn_csn M))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
      Finset.mem_singleton, fresh_t_ne_y, fresh_t_not_M, or_false, not_false_eq_true]
  have p0131 :=
    @g_elimak t syntaxClass0008 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))
      (syn_copk (.cv y) (syn_csn M)) freeVariableCertificate28 freeVariableCertificate29
      freeVariableCertificate30 p0130
  have p0132 := @g_excom syntaxFormula0069 a t
  have p0133 :=
    @g_n_3bitr4i syntaxFormula0071 syntaxFormula0074 syntaxFormula0075 syntaxFormula0076
      p0129 p0131 p0132
  have p0134 := (Nominal.biimpRefl (syn_wrex a M (.classMem (syn_cpw1 (.cv a)) (.cv y))))
  have p0135 :=
    @g_n_3bitr4i syntaxFormula0076
      (syn_wex a (syn_wa (.classMem (.cv a) M) (.classMem (syn_cpw1 (.cv a)) (.cv y))))
      syntaxFormula0075 (syn_wrex a M (.classMem (syn_cpw1 (.cv a)) (.cv y))) p0122 p0133
      p0134
  have p0136 :=
    @g_anbi12i (.classMem (syn_copk (.cv y) (syn_csn M)) (syn_cxpk (syn_cnnc) (syn_cvv)))
      (.classMem (.cv y) (syn_cnnc)) syntaxFormula0075
      (syn_wrex a M (.classMem (syn_cpw1 (.cv a)) (.cv y))) p0076 p0135
  have p0137 :=
    @g_n_3bitri syntaxFormula0077
      (.classMem (syn_copk (.cv y) (syn_csn M)) syntaxClass0010)
      (syn_wa (.classMem (syn_copk (.cv y) (syn_csn M)) (syn_cxpk (syn_cnnc) (syn_cvv)))
        syntaxFormula0075)
      syntaxFormula0027 p0073 p0074 p0136
  have p0138 := @g_otkelins3k (.cv y) (.cv n) (syn_csn M) (syn_cidk) p0072 p0051 p0041
  have p0139 := @g_opkelidkg (.cv y) (.cv n) (syn_cvv) (syn_cvv)
  have p0140_e02_recanon :
    Nominal.NPrf
      (.imp (syn_wa (.classMem (.cv y) (syn_cvv)) (.classMem (.cv n) (syn_cvv)))
        (syn_wb (.classMem (syn_copk (.cv y) (.cv n)) (syn_cidk)) (.objEq y n))) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [syn_wa, syn_cvv, syn_wb, syn_copk, syn_cpr, syn_cun, syn_cnin,
          syn_wnan, syn_ccompl, syn_csn, syn_cidk, syn_wex]
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
    @g_mp2an (.classMem (.cv y) (syn_cvv)) (.classMem (.cv n) (syn_cvv))
      (syn_wb (.classMem (syn_copk (.cv y) (.cv n)) (syn_cidk)) (.objEq y n)) p0072 p0051
      p0140_e02_recanon
  have p0141 :=
    @g_bitri syntaxFormula0078 (.classMem (syn_copk (.cv y) (.cv n)) (syn_cidk))
      (.objEq y n) p0138 p0140
  have p0142 :=
    @g_bibi12i syntaxFormula0077 syntaxFormula0027 syntaxFormula0078 (.objEq y n) p0137
      p0141
  have p0143 :=
    @g_xchbinx syntaxFormula0051 (syn_wb syntaxFormula0077 syntaxFormula0078)
      (syn_wb syntaxFormula0027 (.objEq y n)) p0071 p0142
  have p0144 :=
    @g_bitri syntaxFormula0049 syntaxFormula0051
      (.neg (syn_wb syntaxFormula0027 (.objEq y n))) p0070 p0143
  have p0145 :=
    @g_exbii syntaxFormula0049 (.neg (syn_wb syntaxFormula0027 (.objEq y n))) y p0144
  have p0146 :=
    @g_n_3bitri syntaxFormula0079 syntaxFormula0048 syntaxFormula0050
      (syn_wex y (.neg (syn_wb syntaxFormula0027 (.objEq y n)))) p0058 p0066 p0145
  have p0147 := @g_exnal (syn_wb syntaxFormula0027 (.objEq y n)) y
  have p0148 :=
    @g_n_3bitrri syntaxFormula0080 syntaxFormula0079
      (syn_wex y (.neg (syn_wb syntaxFormula0027 (.objEq y n))))
      (.neg (.all y (syn_wb syntaxFormula0027 (.objEq y n)))) p0056 p0146 p0147
  have p0149 :=
    @g_con1bii (.all y (syn_wb syntaxFormula0027 (.objEq y n))) syntaxFormula0080 p0148
  have p0150 :=
    @g_anbi12i syntaxFormula0043 (.objMem z n) syntaxFormula0081
      (.all y (syn_wb syntaxFormula0027 (.objEq y n))) p0055 p0149
  have p0151 :=
    @g_n_3bitri syntaxFormula0083 syntaxFormula0042
      (syn_wa syntaxFormula0043 syntaxFormula0081)
      (syn_wa (.objMem z n) (.all y (syn_wb syntaxFormula0027 (.objEq y n)))) p0049 p0050
      p0150
  have p0152 :=
    @g_exbii syntaxFormula0083
      (syn_wa (.objMem z n) (.all y (syn_wb syntaxFormula0027 (.objEq y n)))) n p0151
  have p0153 :=
    @g_otkelins3k (syn_csn (.cv z)) (syn_csn M) X syntaxClass0016 p0040 p0041
      hyp_eqtfinrelk_2
  have p0154 := @g_opkex (syn_csn (.cv z)) (syn_csn M)
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
  have freeVariableCertificate32 : t ∉ ((syn_copk (syn_csn (.cv z)) (syn_csn M))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      fresh_t_ne_z, fresh_t_not_M, or_false, not_false_eq_true]
  have p0155 :=
    @g_elimak t syntaxClass0015 (syn_cpw1 (syn_c1c))
      (syn_copk (syn_csn (.cv z)) (syn_csn M)) freeVariableCertificate31
      freeVariableCertificate10 freeVariableCertificate32 p0154
  have freeVariableCertificate33 : n ∉ ((Class.cv t)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_n_ne_t, not_false_eq_true]
  have p0156 := @g_elpw11c n (.cv t) freeVariableCertificate33
  have p0157 :=
    @g_anbi1i (.classMem (.cv t) (syn_cpw1 (syn_c1c)))
      (syn_wex n (.classEq (.cv t) (syn_csn (syn_csn (.cv n))))) syntaxFormula0041 p0156
  have freeVariableCertificate34 :
    n ∉
      ((Wff.classMem (syn_copk (.cv t) (syn_copk (syn_csn (.cv z)) (syn_csn M)))
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
    @g_n_19_41v (.classEq (.cv t) (syn_csn (syn_csn (.cv n)))) syntaxFormula0041 n
      freeVariableCertificate34
  have p0159 :=
    @g_bitr4i syntaxFormula0084
      (syn_wa (syn_wex n (.classEq (.cv t) (syn_csn (syn_csn (.cv n))))) syntaxFormula0041)
      syntaxFormula0085 p0157 p0158
  have p0160 := @g_exbii syntaxFormula0084 syntaxFormula0085 t p0159
  have p0161 := (Nominal.biimpRefl syntaxFormula0086)
  have p0162 := @g_excom syntaxFormula0082 n t
  have p0163 :=
    @g_n_3bitr4i (syn_wex t syntaxFormula0084) (syn_wex t syntaxFormula0085)
      syntaxFormula0086 syntaxFormula0087 p0160 p0161 p0162
  have p0164 :=
    @g_n_3bitri syntaxFormula0088
      (.classMem (syn_copk (syn_csn (.cv z)) (syn_csn M)) syntaxClass0016)
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
    @g_dfiota2 syntaxFormula0027 y n freeVariableCertificate35
      (show y ≠ n from (by exact fresh_y_ne_n))
  have p0166 :=
    @g_eleq2i syntaxClass0028
      (syn_cuni (.cab n (.all y (syn_wb syntaxFormula0027 (.objEq y n))))) (.cv z) p0165
  have freeVariableCertificate36 : n ∉ ((Class.cv z)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_n_ne_z, not_false_eq_true]
  have p0167 :=
    @g_eluniab (.all y (syn_wb syntaxFormula0027 (.objEq y n))) n (.cv z)
      freeVariableCertificate36
  have p0168_e01_recanon :
    Nominal.NPrf
      (syn_wb (.classMem (.cv z)
          (syn_cuni (.cab n (.all y (syn_wb syntaxFormula0027 (.objEq y n)))))) (syn_wex n
          (syn_wa (.objMem z n) (.all y (syn_wb syntaxFormula0027 (.objEq y n)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [syn_wb, syn_cuni, syn_wex, syn_wa]
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
    @g_bitri syntaxFormula0089
      (.classMem (.cv z) (syn_cuni (.cab n (.all y (syn_wb syntaxFormula0027 (.objEq y n))))))
      (syn_wex n (syn_wa (.objMem z n) (.all y (syn_wb syntaxFormula0027 (.objEq y n)))))
      p0166 p0168_e01_recanon
  have p0169 :=
    @g_n_3bitr4i syntaxFormula0087
      (syn_wex n (syn_wa (.objMem z n) (.all y (syn_wb syntaxFormula0027 (.objEq y n)))))
      syntaxFormula0088 syntaxFormula0089 p0152 p0164 p0168
  have p0170 :=
    @g_bibi12i syntaxFormula0040 (.classMem (.cv z) X) syntaxFormula0088 syntaxFormula0089
      p0045 p0169
  have p0171 :=
    @g_xchbinx syntaxFormula0039 (syn_wb syntaxFormula0040 syntaxFormula0088)
      syntaxFormula0090 p0039 p0170
  have p0172 := @g_bitri syntaxFormula0037 syntaxFormula0039 syntaxFormula0091 p0038 p0171
  have p0173 := @g_exbii syntaxFormula0037 syntaxFormula0091 z p0172
  have p0174 :=
    @g_n_3bitri syntaxFormula0092 syntaxFormula0036 syntaxFormula0038 syntaxFormula0093
      p0026 p0034 p0173
  have p0175 := @g_notbii syntaxFormula0092 syntaxFormula0093 p0174
  have p0176 := @g_elcompl (syn_copk (syn_csn M) X) syntaxClass0019 p0025
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
    @g_dfcleq z X syntaxClass0028
      (by exact (show z ∉ (X).fv from (by exact fresh_z_not_X))) freeVariableCertificate37
  have p0178 := @g_alex syntaxFormula0090 z
  have p0179 :=
    @g_bitri syntaxFormula0094 (.all z syntaxFormula0090) syntaxFormula0095 p0177 p0178
  have p0180 :=
    @g_n_3bitr4i (.neg syntaxFormula0092) syntaxFormula0095 syntaxFormula0096
      syntaxFormula0094 p0175 p0176 p0179
  have p0181 :=
    @g_a1i (syn_wb syntaxFormula0096 syntaxFormula0094) (.neg (.classEq M (syn_c0))) p0180
  have p0182 :=
    @g_opkelxpk (syn_csn M) X (syn_csn (syn_csn (syn_c0))) (syn_cvv) p0041
      hyp_eqtfinrelk_2
  have p0183 :=
    @g_biantru (.classMem X (syn_cvv))
      (.classMem (syn_csn M) (syn_csn (syn_csn (syn_c0)))) hyp_eqtfinrelk_2
  have p0184 := @g_elsnc (syn_csn M) (syn_csn (syn_c0)) p0041
  have p0185 := @g_sneqb M (syn_c0) hyp_eqtfinrelk_1
  have p0186 :=
    @g_bitri (.classMem (syn_csn M) (syn_csn (syn_csn (syn_c0))))
      (.classEq (syn_csn M) (syn_csn (syn_c0))) (.classEq M (syn_c0)) p0184 p0185
  have p0187 :=
    @g_n_3bitr2i syntaxFormula0097
      (syn_wa (.classMem (syn_csn M) (syn_csn (syn_csn (syn_c0)))) (.classMem X (syn_cvv)))
      (.classMem (syn_csn M) (syn_csn (syn_csn (syn_c0)))) (.classEq M (syn_c0)) p0182
      p0183 p0186
  have p0188 := @g_biimpi syntaxFormula0097 (.classEq M (syn_c0)) p0187
  have p0189 := @g_con3i syntaxFormula0097 (.classEq M (syn_c0)) p0188
  have p0190 :=
    @g_biantrud (.neg (.classEq M (syn_c0))) syntaxFormula0098 syntaxFormula0096 p0189
  have p0191 := @g_simpl (.classEq M (syn_c0)) (.classEq X (syn_c0))
  have p0192 :=
    @g_con3i (syn_wa (.classEq M (syn_c0)) (.classEq X (syn_c0))) (.classEq M (syn_c0))
      p0191
  have p0193 :=
    @g_biorf (syn_wa (.classEq M (syn_c0)) (.classEq X (syn_c0))) syntaxFormula0099
  have p0194 :=
    @g_syl (.neg (.classEq M (syn_c0)))
      (.neg (syn_wa (.classEq M (syn_c0)) (.classEq X (syn_c0))))
      (syn_wb syntaxFormula0099 syntaxFormula0100) p0192 p0193
  have p0195 :=
    @g_bitrd (.neg (.classEq M (syn_c0))) syntaxFormula0096 syntaxFormula0099
      syntaxFormula0100 p0190 p0194
  have p0196 :=
    @g_opkelxpk (syn_csn M) X (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0)) p0041
      hyp_eqtfinrelk_2
  have p0197 :=
    @g_anbi12i (.classMem (syn_csn M) (syn_csn (syn_csn (syn_c0)))) (.classEq M (syn_c0))
      (.classMem X (syn_csn (syn_c0))) (.classEq X (syn_c0)) p0186 p0004
  have p0198 :=
    @g_bitri syntaxFormula0101
      (syn_wa (.classMem (syn_csn M) (syn_csn (syn_csn (syn_c0))))
        (.classMem X (syn_csn (syn_c0))))
      (syn_wa (.classEq M (syn_c0)) (.classEq X (syn_c0))) p0196 p0197
  have p0199 :=
    @g_eldif (syn_copk (syn_csn M) X) syntaxClass0020
      (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv))
  have p0200 :=
    @g_orbi12i syntaxFormula0101 (syn_wa (.classEq M (syn_c0)) (.classEq X (syn_c0)))
      syntaxFormula0102 syntaxFormula0099 p0198 p0199
  have p0201 :=
    @g_syl6bbr (.neg (.classEq M (syn_c0))) syntaxFormula0096 syntaxFormula0100
      syntaxFormula0103 p0195 p0200
  have p0202 :=
    @g_elun (syn_copk (syn_csn M) X)
      (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0))) syntaxClass0021
  have p0203 :=
    @g_syl6bbr (.neg (.classEq M (syn_c0))) syntaxFormula0096 syntaxFormula0103
      syntaxFormula0030 p0201 p0202
  have p0204 :=
    @g_n_3bitr2rd (.neg (.classEq M (syn_c0))) syntaxFormula0031 syntaxFormula0094
      syntaxFormula0096 syntaxFormula0030 p0024 p0181 p0203
  have p0205 :=
    @g_pm2_61i (.classEq M (syn_c0)) (syn_wb syntaxFormula0030 syntaxFormula0031) p0022
      p0204
  have p0206 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_tfin y M a
      (by exact (show a ∉ (M).fv from (by exact fresh_a_not_M)))
      (by exact (show y ∉ (M).fv from (by exact fresh_y_not_M)))
      (show a ≠ y from (by exact fresh_a_ne_y))
  have p0207 := @g_eqeq2i (syn_ctfin M) syntaxClass0029 X p0206
  have p0208 :=
    @g_bitr4i syntaxFormula0030 syntaxFormula0031 (.classEq X (syn_ctfin M)) p0205 p0207
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

@[expose]
noncomputable def g_tfinrelkex :
    Nominal.NPrf
      (.classMem (syn_cun (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0))) (syn_cdif
            (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cimak
                      (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k (syn_cimak
                            (syn_csymdif (syn_cins2k (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv))
                                  (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_cssetk)))
                                      (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik
        (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak
        (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                              (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c)))))
                      (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
            (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv)))) (syn_cvv)) :=
  by
  have p0000 := @g_snex (syn_csn (syn_c0))
  have p0001 := @g_snex (syn_c0)
  have p0002 := @g_xpkex (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0)) p0000 p0001
  have p0003 := @g_ssetkex
  have p0004 := @g_ins2kex (syn_cssetk) p0003
  have p0006 := @g_cnvkex (syn_cssetk) p0003
  have p0007 := @g_ins3kex (syn_ccnvk (syn_cssetk)) p0006
  have p0008 := @g_nncex
  have p0009 := @g_vvex
  have p0010 := @g_xpkex (syn_cnnc) (syn_cvv) p0008 p0009
  have p0012 := @g_sikex (syn_cssetk) p0003
  have p0013 := @g_ins2kex (syn_csik (syn_cssetk)) p0012
  have p0014 := @g_n_1cex
  have p0015 := @g_pwex (syn_c1c) p0014
  have p0017 := @g_xpkex (syn_cpw (syn_c1c)) (syn_cvv) p0015 p0009
  have p0019 := @g_ins3kex (syn_cssetk) p0003
  have p0020 :=
    @g_symdifex (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk))) p0019 p0013
  have p0022 := @g_pw1ex (syn_c1c) p0014
  have p0023 := @g_pw1ex (syn_cpw1 (syn_c1c)) p0022
  have p0024 := @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_c1c))) p0023
  have p0025 :=
    @g_imakex (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk))))
      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))) p0020 p0024
  have p0026 :=
    @g_difex (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv))
      (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk))))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))
      p0017 p0025
  have p0027 :=
    @g_sikex
      (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak
          (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk))))
          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))
      p0026
  have p0028 :=
    @g_ins3kex
      (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak
            (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk))))
            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
      p0027
  have p0029 :=
    @g_inex
      (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak
              (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk))))
              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
      (syn_cins2k (syn_cssetk)) p0028 p0004
  have p0030 :=
    @g_imakex
      (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv))
              (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk))
                  (syn_cins2k (syn_csik (syn_cssetk))))
                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk)))
      (syn_cpw1 (syn_cpw1 (syn_c1c))) p0029 p0023
  have p0031 :=
    @g_ins3kex
      (syn_cimak (syn_cin (syn_cins3k (syn_csik
              (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak
                  (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk))))
                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c))))
      p0030
  have p0032 :=
    @g_inex (syn_cins2k (syn_csik (syn_cssetk)))
      (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik
                (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak
                    (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk))))
                    (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk)))
          (syn_cpw1 (syn_cpw1 (syn_c1c)))))
      p0013 p0031
  have p0033 :=
    @g_imakex
      (syn_cin (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin (syn_cins3k
                (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak
                      (syn_csymdif (syn_cins3k (syn_cssetk))
                        (syn_cins2k (syn_csik (syn_cssetk))))
                      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk)))
            (syn_cpw1 (syn_cpw1 (syn_c1c))))))
      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))) p0032 p0024
  have p0034 :=
    @g_inex (syn_cxpk (syn_cnnc) (syn_cvv))
      (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin
                (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv))
                      (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk))
                          (syn_cins2k (syn_csik (syn_cssetk))))
                        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))
      p0010 p0033
  have p0035 :=
    @g_ins2kex
      (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak
          (syn_cin (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin
                  (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv))
                        (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk))
                            (syn_cins2k (syn_csik (syn_cssetk))))
                          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                  (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))
      p0034
  have p0036 := @g_idkex
  have p0037 := @g_ins3kex (syn_cidk) p0036
  have p0038 :=
    @g_symdifex
      (syn_cins2k (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak
            (syn_cin (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin
                    (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv))
                          (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk))
                              (syn_cins2k (syn_csik (syn_cssetk))))
                            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                    (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
      (syn_cins3k (syn_cidk)) p0035 p0037
  have p0039 :=
    @g_imakex
      (syn_csymdif (syn_cins2k (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak
              (syn_cin (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin
                      (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv))
                            (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk))
                                (syn_cins2k (syn_csik (syn_cssetk))))
                              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                      (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins3k (syn_cidk)))
      (syn_cpw1 (syn_c1c)) p0038 p0022
  have p0040 :=
    @g_ins2kex
      (syn_cimak (syn_csymdif (syn_cins2k (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak
                (syn_cin (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin
                        (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv))
                              (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk))
                                  (syn_cins2k (syn_csik (syn_cssetk))))
                                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                        (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins3k (syn_cidk)))
        (syn_cpw1 (syn_c1c)))
      p0039
  have p0041 :=
    @g_difex (syn_cins3k (syn_ccnvk (syn_cssetk)))
      (syn_cins2k (syn_cimak (syn_csymdif (syn_cins2k (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv))
                (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak
                        (syn_cin (syn_cins3k (syn_csik
                              (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak
                                  (syn_csymdif (syn_cins3k (syn_cssetk))
                                    (syn_cins2k (syn_csik (syn_cssetk))))
                                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                          (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins3k (syn_cidk)))
          (syn_cpw1 (syn_c1c))))
      p0007 p0040
  have p0042 :=
    @g_imakex
      (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k (syn_cimak (syn_csymdif
              (syn_cins2k (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak
                    (syn_cin (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak
                          (syn_cin (syn_cins3k (syn_csik
                                (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak
                                    (syn_csymdif (syn_cins3k (syn_cssetk))
                                      (syn_cins2k (syn_csik (syn_cssetk))))
                                    (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                            (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                    (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins3k (syn_cidk)))
            (syn_cpw1 (syn_c1c)))))
      (syn_cpw1 (syn_c1c)) p0041 p0022
  have p0043 :=
    @g_ins3kex
      (syn_cimak (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k (syn_cimak
              (syn_csymdif (syn_cins2k (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak
                      (syn_cin (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak
                            (syn_cin (syn_cins3k (syn_csik
                                  (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak
                                      (syn_csymdif (syn_cins3k (syn_cssetk))
                                        (syn_cins2k (syn_csik (syn_cssetk))))
                                      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                              (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins3k (syn_cidk)))
              (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_c1c)))
      p0042
  have p0044 :=
    @g_symdifex (syn_cins2k (syn_cssetk))
      (syn_cins3k (syn_cimak (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k
              (syn_cimak (syn_csymdif (syn_cins2k (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv))
                      (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k
                            (syn_cimak (syn_cin (syn_cins3k (syn_csik
                                    (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv))
                                      (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk))
        (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                                (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins3k (syn_cidk)))
                (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_c1c))))
      p0004 p0043
  have p0045 :=
    @g_imakex
      (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cimak
            (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k (syn_cimak (syn_csymdif
                    (syn_cins2k (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak
                          (syn_cin (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak
                                (syn_cin (syn_cins3k (syn_csik
                                      (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv))
                                        (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk))
        (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                                  (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins3k (syn_cidk)))
                  (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_c1c)))))
      (syn_cpw1 (syn_cpw1 (syn_c1c))) p0044 p0023
  have p0046 :=
    @g_complex
      (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cimak
              (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k (syn_cimak
                    (syn_csymdif (syn_cins2k (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak
                            (syn_cin (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak
                                  (syn_cin (syn_cins3k (syn_csik
                                        (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv))
        (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk))))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk)))
                                  (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                      (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_c1c)))))
        (syn_cpw1 (syn_cpw1 (syn_c1c))))
      p0045
  have p0048 := @g_xpkex (syn_csn (syn_csn (syn_c0))) (syn_cvv) p0000 p0009
  have p0049 :=
    @g_difex
      (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cimak
                (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k (syn_cimak
                      (syn_csymdif (syn_cins2k (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv))
                            (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k
                                  (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif
        (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak
        (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk)))
                                    (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                        (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_c1c)))))
          (syn_cpw1 (syn_cpw1 (syn_c1c)))))
      (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv)) p0046 p0048
  have p0050 :=
    @g_unex (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0)))
      (syn_cdif (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
                (syn_cimak (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k
                      (syn_cimak (syn_csymdif (syn_cins2k
                            (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak
                                (syn_cin (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k
                                    (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif
        (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak
        (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk)))
                                      (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                          (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c)))))
                  (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
        (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv)))
      p0002 p0049
  exact p0050

@[expose]
noncomputable def g_tfineq (A : Class) (B : Class) :
    Nominal.NPrf (.imp (.classEq A B) (.classEq (syn_ctfin A) (syn_ctfin B))) :=
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
  have p0000 := @g_eqeq1 A B (syn_c0)
  have p0001 :=
    @g_rexeq (.classMem (syn_cpw1 (.cv y)) (.cv x)) y A B
      (by exact (show y ∉ (A).fv from (by exact fresh_y_not_A)))
      (by exact (show y ∉ (B).fv from (by exact fresh_y_not_B)))
  have p0002 :=
    @g_anbi2d (.classEq A B) (syn_wrex y A (.classMem (syn_cpw1 (.cv y)) (.cv x)))
      (syn_wrex y B (.classMem (syn_cpw1 (.cv y)) (.cv x))) (.classMem (.cv x) (syn_cnnc))
      p0001
  have freeVariableCertificate0 : x ∉ ((Wff.classEq A B)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union,
      fresh_x_not_A, fresh_x_not_B, or_false, not_false_eq_true]
  have p0003 :=
    @g_iotabidv (.classEq A B)
      (syn_wa (.classMem (.cv x) (syn_cnnc))
        (syn_wrex y A (.classMem (syn_cpw1 (.cv y)) (.cv x))))
      (syn_wa (.classMem (.cv x) (syn_cnnc))
        (syn_wrex y B (.classMem (syn_cpw1 (.cv y)) (.cv x))))
      x freeVariableCertificate0 p0002
  have p0004 :=
    @g_ifbieq2d (.classEq A B) (.classEq A (syn_c0)) (.classEq B (syn_c0))
      (syn_cio x (syn_wa (.classMem (.cv x) (syn_cnnc))
          (syn_wrex y A (.classMem (syn_cpw1 (.cv y)) (.cv x)))))
      (syn_cio x (syn_wa (.classMem (.cv x) (syn_cnnc))
          (syn_wrex y B (.classMem (syn_cpw1 (.cv y)) (.cv x)))))
      (syn_c0) p0000 p0003
  have p0005 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_tfin x A y
      (by exact (show y ∉ (A).fv from (by exact fresh_y_not_A)))
      (by exact (show x ∉ (A).fv from (by exact fresh_x_not_A)))
      (show y ≠ x from (by exact fresh_y_ne_x))
  have p0006 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_tfin x B y
      (by exact (show y ∉ (B).fv from (by exact fresh_y_not_B)))
      (by exact (show x ∉ (B).fv from (by exact fresh_x_not_B)))
      (show y ≠ x from (by exact fresh_y_ne_x))
  have p0007 :=
    @g_n_3eqtr4g (.classEq A B)
      (syn_cif (.classEq A (syn_c0)) (syn_c0) (syn_cio x (syn_wa (.classMem (.cv x) (syn_cnnc))
            (syn_wrex y A (.classMem (syn_cpw1 (.cv y)) (.cv x))))))
      (syn_cif (.classEq B (syn_c0)) (syn_c0) (syn_cio x (syn_wa (.classMem (.cv x) (syn_cnnc))
            (syn_wrex y B (.classMem (syn_cpw1 (.cv y)) (.cv x))))))
      (syn_ctfin A) (syn_ctfin B) p0004 p0005 p0006
  exact p0007

@[expose]
noncomputable def g_tfinprop (M : Class) (a : Var) (dv_M_a : a ∉ M.fv) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem M (syn_cnnc)) (syn_wne M (syn_c0)))
        (syn_wa (.classMem (syn_ctfin M) (syn_cnnc))
          (syn_wrex a M (.classMem (syn_cpw1 (.cv a)) (syn_ctfin M))))) :=
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
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_tfin n M a
      (by exact (show a ∉ (M).fv from (by exact dv_M_a)))
      (by exact (show n ∉ (M).fv from (by exact fresh_n_not_M)))
      (show a ≠ n from (by exact fresh_a_ne_n))
  have p0001 := (Nominal.biimpRefl (syn_wne M (syn_c0)))
  have p0002 :=
    @g_iffalse (.classEq M (syn_c0)) (syn_c0)
      (syn_cio n (syn_wa (.classMem (.cv n) (syn_cnnc))
          (syn_wrex a M (.classMem (syn_cpw1 (.cv a)) (.cv n)))))
  have p0003 :=
    @g_sylbi (syn_wne M (syn_c0)) (.neg (.classEq M (syn_c0)))
      (.classEq (syn_cif (.classEq M (syn_c0)) (syn_c0) (syn_cio n
            (syn_wa (.classMem (.cv n) (syn_cnnc))
              (syn_wrex a M (.classMem (syn_cpw1 (.cv a)) (.cv n)))))) (syn_cio n
          (syn_wa (.classMem (.cv n) (syn_cnnc))
            (syn_wrex a M (.classMem (syn_cpw1 (.cv a)) (.cv n))))))
      p0001 p0002
  have p0004 :=
    @g_adantl (syn_wne M (syn_c0))
      (.classEq (syn_cif (.classEq M (syn_c0)) (syn_c0) (syn_cio n
            (syn_wa (.classMem (.cv n) (syn_cnnc))
              (syn_wrex a M (.classMem (syn_cpw1 (.cv a)) (.cv n)))))) (syn_cio n
          (syn_wa (.classMem (.cv n) (syn_cnnc))
            (syn_wrex a M (.classMem (syn_cpw1 (.cv a)) (.cv n))))))
      (.classMem M (syn_cnnc)) p0003
  have p0005 :=
    @g_nnpw1ex n M a (by exact (show a ∉ (M).fv from (by exact dv_M_a)))
      (by exact (show n ∉ (M).fv from (by exact fresh_n_not_M)))
      (show a ≠ n from (by exact fresh_a_ne_n))
  have p0006 :=
    @g_reiotacl (syn_wrex a M (.classMem (syn_cpw1 (.cv a)) (.cv n))) n (syn_cnnc)
      (by
        exact
          (show n ∉ ((syn_cnnc)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc];
              exact (show n ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
  have p0007 :=
    @g_syl (syn_wa (.classMem M (syn_cnnc)) (syn_wne M (syn_c0)))
      (syn_wreu n (syn_cnnc) (syn_wrex a M (.classMem (syn_cpw1 (.cv a)) (.cv n))))
      (.classMem (syn_cio n (syn_wa (.classMem (.cv n) (syn_cnnc))
            (syn_wrex a M (.classMem (syn_cpw1 (.cv a)) (.cv n))))) (syn_cnnc))
      p0005 p0006
  have p0008 :=
    @g_eqeltrd (syn_wa (.classMem M (syn_cnnc)) (syn_wne M (syn_c0)))
      (syn_cif (.classEq M (syn_c0)) (syn_c0) (syn_cio n (syn_wa (.classMem (.cv n) (syn_cnnc))
            (syn_wrex a M (.classMem (syn_cpw1 (.cv a)) (.cv n))))))
      (syn_cio n (syn_wa (.classMem (.cv n) (syn_cnnc))
          (syn_wrex a M (.classMem (syn_cpw1 (.cv a)) (.cv n)))))
      (syn_cnnc) p0004 p0007
  have p0009 :=
    @g_syl5eqel (syn_wa (.classMem M (syn_cnnc)) (syn_wne M (syn_c0))) (syn_ctfin M)
      (syn_cif (.classEq M (syn_c0)) (syn_c0) (syn_cio n (syn_wa (.classMem (.cv n) (syn_cnnc))
            (syn_wrex a M (.classMem (syn_cpw1 (.cv a)) (.cv n))))))
      (syn_cnnc) p0000 p0008
  have p0010 :=
    @g_syl5req (syn_wa (.classMem M (syn_cnnc)) (syn_wne M (syn_c0))) (syn_ctfin M)
      (syn_cif (.classEq M (syn_c0)) (syn_c0) (syn_cio n (syn_wa (.classMem (.cv n) (syn_cnnc))
            (syn_wrex a M (.classMem (syn_cpw1 (.cv a)) (.cv n))))))
      (syn_cio n (syn_wa (.classMem (.cv n) (syn_cnnc))
          (syn_wrex a M (.classMem (syn_cpw1 (.cv a)) (.cv n)))))
      p0000 p0004
  have p0011 :=
    @g_jca (syn_wa (.classMem M (syn_cnnc)) (syn_wne M (syn_c0)))
      (.classMem (syn_ctfin M) (syn_cnnc))
      (syn_wreu n (syn_cnnc) (syn_wrex a M (.classMem (syn_cpw1 (.cv a)) (.cv n)))) p0009
      p0005
  have p0012 := @g_eleq2 (.cv n) (syn_ctfin M) (syn_cpw1 (.cv a))
  have freeVariableCertificate0 : a ∉ ((Wff.classEq (.cv n) (syn_ctfin M))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin, Finset.mem_union,
      Finset.mem_singleton, fresh_a_ne_n, dv_M_a, or_false, not_false_eq_true]
  have p0013 :=
    @g_rexbidv (.classEq (.cv n) (syn_ctfin M)) (.classMem (syn_cpw1 (.cv a)) (.cv n))
      (.classMem (syn_cpw1 (.cv a)) (syn_ctfin M)) a M freeVariableCertificate0 p0012
  have freeVariableCertificate1 :
    n ∉ ((syn_wrex a M (.classMem (syn_cpw1 (.cv a)) (syn_ctfin M)))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin, Finset.mem_union,
      Finset.mem_erase, Finset.mem_singleton, fresh_n_not_M, fresh_n_ne_a, or_false,
      and_false, not_false_eq_true]
  have p0014 :=
    @g_reiota2 (syn_wrex a M (.classMem (syn_cpw1 (.cv a)) (.cv n)))
      (syn_wrex a M (.classMem (syn_cpw1 (.cv a)) (syn_ctfin M))) n (syn_cnnc)
      (syn_ctfin M)
      (by
        exact
          (show n ∉ ((syn_cnnc)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc];
              exact (show n ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
      (by
        exact
          (show n ∉ ((syn_ctfin M)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin];
              exact (show n ∉ (M).fv from (by exact fresh_n_not_M)))))
      freeVariableCertificate1 p0013
  have p0015 :=
    @g_syl (syn_wa (.classMem M (syn_cnnc)) (syn_wne M (syn_c0)))
      (syn_wa (.classMem (syn_ctfin M) (syn_cnnc))
        (syn_wreu n (syn_cnnc) (syn_wrex a M (.classMem (syn_cpw1 (.cv a)) (.cv n)))))
      (syn_wb (syn_wrex a M (.classMem (syn_cpw1 (.cv a)) (syn_ctfin M))) (.classEq (syn_cio n
            (syn_wa (.classMem (.cv n) (syn_cnnc))
              (syn_wrex a M (.classMem (syn_cpw1 (.cv a)) (.cv n))))) (syn_ctfin M)))
      p0011 p0014
  have p0016 :=
    @g_mpbird (syn_wa (.classMem M (syn_cnnc)) (syn_wne M (syn_c0)))
      (syn_wrex a M (.classMem (syn_cpw1 (.cv a)) (syn_ctfin M)))
      (.classEq (syn_cio n (syn_wa (.classMem (.cv n) (syn_cnnc))
            (syn_wrex a M (.classMem (syn_cpw1 (.cv a)) (.cv n))))) (syn_ctfin M))
      p0010 p0015
  have p0017 :=
    @g_jca (syn_wa (.classMem M (syn_cnnc)) (syn_wne M (syn_c0)))
      (.classMem (syn_ctfin M) (syn_cnnc))
      (syn_wrex a M (.classMem (syn_cpw1 (.cv a)) (syn_ctfin M))) p0009 p0016
  exact p0017

@[expose]
noncomputable def g_tfinnnul (M : Class) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem M (syn_cnnc)) (syn_wne M (syn_c0)))
        (syn_wne (syn_ctfin M) (syn_c0))) :=
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
  have p0000 := @g_tfinprop M x (by exact (show x ∉ (M).fv from (by exact fresh_x_not_M)))
  have p0001 := @g_ne0i (syn_ctfin M) (syn_cpw1 (.cv x))
  have freeVariableCertificate0 : x ∉ ((syn_wne (syn_ctfin M) (syn_c0))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union,
      Finset.notMem_empty, fresh_x_not_M, or_false, not_false_eq_true]
  have p0002 :=
    @g_rexlimivw (.classMem (syn_cpw1 (.cv x)) (syn_ctfin M))
      (syn_wne (syn_ctfin M) (syn_c0)) x M freeVariableCertificate0 p0001
  have p0003 :=
    @g_adantl (syn_wrex x M (.classMem (syn_cpw1 (.cv x)) (syn_ctfin M)))
      (syn_wne (syn_ctfin M) (syn_c0)) (.classMem (syn_ctfin M) (syn_cnnc)) p0002
  have p0004 :=
    @g_syl (syn_wa (.classMem M (syn_cnnc)) (syn_wne M (syn_c0)))
      (syn_wa (.classMem (syn_ctfin M) (syn_cnnc))
        (syn_wrex x M (.classMem (syn_cpw1 (.cv x)) (syn_ctfin M))))
      (syn_wne (syn_ctfin M) (syn_c0)) p0000 p0003
  exact p0004

@[expose]
noncomputable def g_tfinnul : Nominal.NPrf (.classEq (syn_ctfin (syn_c0)) (syn_c0)) :=
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
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_tfin x (syn_c0) y
      (by
        exact
          (show y ∉ ((syn_c0)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0];
              exact (show y ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
      (by
        exact
          (show x ∉ ((syn_c0)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0];
              exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
      (show y ≠ x from (by exact fresh_y_ne_x))
  have p0001 := @g_eqid (syn_c0)
  have p0002 :=
    @g_iftrue (.classEq (syn_c0) (syn_c0)) (syn_c0)
      (syn_cio x (syn_wa (.classMem (.cv x) (syn_cnnc))
          (syn_wrex y (syn_c0) (.classMem (syn_cpw1 (.cv y)) (.cv x)))))
  have p0003 := Nominal.mp p0001 p0002
  have p0004 :=
    @g_eqtri (syn_ctfin (syn_c0))
      (syn_cif (.classEq (syn_c0) (syn_c0)) (syn_c0) (syn_cio x
          (syn_wa (.classMem (.cv x) (syn_cnnc))
            (syn_wrex y (syn_c0) (.classMem (syn_cpw1 (.cv y)) (.cv x))))))
      (syn_c0) p0000 p0003
  exact p0004

@[expose]
noncomputable def g_tfincl (N : Class) :
    Nominal.NPrf (.imp (.classMem N (syn_cnnc)) (.classMem (syn_ctfin N) (syn_cnnc))) :=
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
  have p0000 := @g_tfinnul
  have p0001 := @g_tfineq N (syn_c0)
  have p0002 := @g_id (.classEq N (syn_c0))
  have p0003 :=
    @g_n_3eqtr4a (.classEq N (syn_c0)) (syn_ctfin (syn_c0)) (syn_c0) (syn_ctfin N) N p0000
      p0001 p0002
  have p0004 := @g_eleq1d (.classEq N (syn_c0)) (syn_ctfin N) N (syn_cnnc) p0003
  have p0005 :=
    @g_biimprd (.classEq N (syn_c0)) (.classMem (syn_ctfin N) (syn_cnnc))
      (.classMem N (syn_cnnc)) p0004
  have p0006 := @g_tfinprop N a (by exact (show a ∉ (N).fv from (by exact fresh_a_not_N)))
  have p0007 :=
    @g_simpld (syn_wa (.classMem N (syn_cnnc)) (syn_wne N (syn_c0)))
      (.classMem (syn_ctfin N) (syn_cnnc))
      (syn_wrex a N (.classMem (syn_cpw1 (.cv a)) (syn_ctfin N))) p0006
  have p0008 :=
    @g_expcom (.classMem N (syn_cnnc)) (syn_wne N (syn_c0))
      (.classMem (syn_ctfin N) (syn_cnnc)) p0007
  have p0009 :=
    @g_pm2_61ine (.imp (.classMem N (syn_cnnc)) (.classMem (syn_ctfin N) (syn_cnnc))) N
      (syn_c0) p0005 p0008
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

@[expose]
noncomputable def g_tfin11 (M : Class) (N : Class) :
    Nominal.NPrf
      (.imp (syn_w3a (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))
          (.classEq (syn_ctfin M) (syn_ctfin N))) (.classEq M N)) :=
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
  have p0000 := @g_tfinnnul M
  have p0001 :=
    @g_ex (.classMem M (syn_cnnc)) (syn_wne M (syn_c0)) (syn_wne (syn_ctfin M) (syn_c0))
      p0000
  have p0002 :=
    @g_necon4d (.classMem M (syn_cnnc)) M (syn_c0) (syn_ctfin M) (syn_c0) p0001
  have p0003 :=
    @g_n_3ad2ant1 (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))
      (.imp (.classEq (syn_ctfin M) (syn_c0)) (.classEq M (syn_c0)))
      (.classEq (syn_ctfin M) (syn_ctfin N)) p0002
  have p0004 :=
    @g_impcom
      (syn_w3a (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))
        (.classEq (syn_ctfin M) (syn_ctfin N)))
      (.classEq (syn_ctfin M) (syn_c0)) (.classEq M (syn_c0)) p0003
  have p0005 := @g_eqeq1 (syn_ctfin M) (syn_ctfin N) (syn_c0)
  have p0006 :=
    @g_adantl (.classEq (syn_ctfin M) (syn_ctfin N))
      (syn_wb (.classEq (syn_ctfin M) (syn_c0)) (.classEq (syn_ctfin N) (syn_c0)))
      (.classMem N (syn_cnnc)) p0005
  have p0007 := @g_tfinnnul N
  have p0008 :=
    @g_ex (.classMem N (syn_cnnc)) (syn_wne N (syn_c0)) (syn_wne (syn_ctfin N) (syn_c0))
      p0007
  have p0009 :=
    @g_necon4d (.classMem N (syn_cnnc)) N (syn_c0) (syn_ctfin N) (syn_c0) p0008
  have p0010 :=
    @g_adantr (.classMem N (syn_cnnc))
      (.imp (.classEq (syn_ctfin N) (syn_c0)) (.classEq N (syn_c0)))
      (.classEq (syn_ctfin M) (syn_ctfin N)) p0009
  have p0011 :=
    @g_sylbid (syn_wa (.classMem N (syn_cnnc)) (.classEq (syn_ctfin M) (syn_ctfin N)))
      (.classEq (syn_ctfin M) (syn_c0)) (.classEq (syn_ctfin N) (syn_c0))
      (.classEq N (syn_c0)) p0006 p0010
  have p0012 :=
    @g_n_3adant1 (.classMem N (syn_cnnc)) (.classEq (syn_ctfin M) (syn_ctfin N))
      (.imp (.classEq (syn_ctfin M) (syn_c0)) (.classEq N (syn_c0)))
      (.classMem M (syn_cnnc)) p0011
  have p0013 :=
    @g_impcom
      (syn_w3a (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))
        (.classEq (syn_ctfin M) (syn_ctfin N)))
      (.classEq (syn_ctfin M) (syn_c0)) (.classEq N (syn_c0)) p0012
  have p0014 :=
    @g_eqtr4d
      (syn_wa (.classEq (syn_ctfin M) (syn_c0))
        (syn_w3a (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))
          (.classEq (syn_ctfin M) (syn_ctfin N))))
      M (syn_c0) N p0004 p0013
  have p0015 :=
    @g_ex (.classEq (syn_ctfin M) (syn_c0))
      (syn_w3a (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))
        (.classEq (syn_ctfin M) (syn_ctfin N)))
      (.classEq M N) p0014
  have p0016 := @g_neeq1 (syn_ctfin M) (syn_ctfin N) (syn_c0)
  have p0017 :=
    @g_biimpd (.classEq (syn_ctfin M) (syn_ctfin N)) (syn_wne (syn_ctfin M) (syn_c0))
      (syn_wne (syn_ctfin N) (syn_c0)) p0016
  have p0018 :=
    @g_ancld (.classEq (syn_ctfin M) (syn_ctfin N)) (syn_wne (syn_ctfin M) (syn_c0))
      (syn_wne (syn_ctfin N) (syn_c0)) p0017
  have p0019 := @g_tfineq M (syn_c0)
  have p0020 := @g_tfinnul
  have p0021 :=
    @g_syl6eq (.classEq M (syn_c0)) (syn_ctfin M) (syn_ctfin (syn_c0)) (syn_c0) p0019
      p0020
  have p0022 := @g_necon3i M (syn_c0) (syn_ctfin M) (syn_c0) p0021
  have p0023 := @g_tfineq N (syn_c0)
  have p0025 :=
    @g_syl6eq (.classEq N (syn_c0)) (syn_ctfin N) (syn_ctfin (syn_c0)) (syn_c0) p0023
      p0020
  have p0026 := @g_necon3i N (syn_c0) (syn_ctfin N) (syn_c0) p0025
  have p0027 :=
    @g_anim12i (syn_wne (syn_ctfin M) (syn_c0)) (syn_wne M (syn_c0))
      (syn_wne (syn_ctfin N) (syn_c0)) (syn_wne N (syn_c0)) p0022 p0026
  have p0028 :=
    @g_syl6 (.classEq (syn_ctfin M) (syn_ctfin N)) (syn_wne (syn_ctfin M) (syn_c0))
      (syn_wa (syn_wne (syn_ctfin M) (syn_c0)) (syn_wne (syn_ctfin N) (syn_c0)))
      (syn_wa (syn_wne M (syn_c0)) (syn_wne N (syn_c0))) p0018 p0027
  have p0029 :=
    @g_n_3ad2ant3 (.classEq (syn_ctfin M) (syn_ctfin N)) (.classMem M (syn_cnnc))
      (.imp (syn_wne (syn_ctfin M) (syn_c0)) (syn_wa (syn_wne M (syn_c0)) (syn_wne N (syn_c0))))
      (.classMem N (syn_cnnc)) p0028
  have p0030 := @g_tfinprop M a (by exact (show a ∉ (M).fv from (by exact fresh_a_not_M)))
  have p0031 :=
    @g_ex (.classMem M (syn_cnnc)) (syn_wne M (syn_c0))
      (syn_wa (.classMem (syn_ctfin M) (syn_cnnc))
        (syn_wrex a M (.classMem (syn_cpw1 (.cv a)) (syn_ctfin M))))
      p0030
  have p0032 :=
    @g_n_3ad2ant1 (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))
      (.imp (syn_wne M (syn_c0)) (syn_wa (.classMem (syn_ctfin M) (syn_cnnc))
          (syn_wrex a M (.classMem (syn_cpw1 (.cv a)) (syn_ctfin M)))))
      (.classEq (syn_ctfin M) (syn_ctfin N)) p0031
  have p0033 := @g_tfinprop N b (by exact (show b ∉ (N).fv from (by exact fresh_b_not_N)))
  have p0034 :=
    @g_ex (.classMem N (syn_cnnc)) (syn_wne N (syn_c0))
      (syn_wa (.classMem (syn_ctfin N) (syn_cnnc))
        (syn_wrex b N (.classMem (syn_cpw1 (.cv b)) (syn_ctfin N))))
      p0033
  have p0035 :=
    @g_n_3ad2ant2 (.classMem N (syn_cnnc)) (.classMem M (syn_cnnc))
      (.imp (syn_wne N (syn_c0)) (syn_wa (.classMem (syn_ctfin N) (syn_cnnc))
          (syn_wrex b N (.classMem (syn_cpw1 (.cv b)) (syn_ctfin N)))))
      (.classEq (syn_ctfin M) (syn_ctfin N)) p0034
  have freeVariableCertificate0 :
    b ∉ ((Wff.classMem (syn_cpw1 (.cv a)) (syn_ctfin M))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin, Finset.mem_union,
      Finset.mem_singleton, fresh_b_ne_a, fresh_b_not_M, or_false, not_false_eq_true]
  have freeVariableCertificate1 :
    a ∉ ((Wff.classMem (syn_cpw1 (.cv b)) (syn_ctfin N))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin, Finset.mem_union,
      Finset.mem_singleton, fresh_a_ne_b, fresh_a_not_N, or_false, not_false_eq_true]
  have p0036 :=
    @g_reeanv (.classMem (syn_cpw1 (.cv a)) (syn_ctfin M))
      (.classMem (syn_cpw1 (.cv b)) (syn_ctfin N)) a b M N
      (by exact (show b ∉ (M).fv from (by exact fresh_b_not_M)))
      (by exact (show a ∉ (N).fv from (by exact fresh_a_not_N))) freeVariableCertificate0
      freeVariableCertificate1 (show a ≠ b from (by exact fresh_a_ne_b))
  have p0037 :=
    @g_simp31 (syn_wa (.classMem (.cv a) M) (.classMem (.cv b) N))
      (syn_wa (.classMem (syn_cpw1 (.cv a)) (syn_ctfin M))
        (.classMem (syn_cpw1 (.cv b)) (syn_ctfin N)))
      (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))
      (.classEq (syn_ctfin M) (syn_ctfin N))
  have p0038 := @g_tfincl M
  have p0039 :=
    @g_syl
      (syn_w3a (syn_wa (.classMem (.cv a) M) (.classMem (.cv b) N))
        (syn_wa (.classMem (syn_cpw1 (.cv a)) (syn_ctfin M))
          (.classMem (syn_cpw1 (.cv b)) (syn_ctfin N)))
        (syn_w3a (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))
          (.classEq (syn_ctfin M) (syn_ctfin N))))
      (.classMem M (syn_cnnc)) (.classMem (syn_ctfin M) (syn_cnnc)) p0037 p0038
  have p0040 :=
    @g_simp2l (syn_wa (.classMem (.cv a) M) (.classMem (.cv b) N))
      (.classMem (syn_cpw1 (.cv a)) (syn_ctfin M))
      (.classMem (syn_cpw1 (.cv b)) (syn_ctfin N))
      (syn_w3a (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))
        (.classEq (syn_ctfin M) (syn_ctfin N)))
  have p0041 :=
    @g_simp2r (syn_wa (.classMem (.cv a) M) (.classMem (.cv b) N))
      (.classMem (syn_cpw1 (.cv a)) (syn_ctfin M))
      (.classMem (syn_cpw1 (.cv b)) (syn_ctfin N))
      (syn_w3a (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))
        (.classEq (syn_ctfin M) (syn_ctfin N)))
  have p0042 :=
    @g_simp33 (syn_wa (.classMem (.cv a) M) (.classMem (.cv b) N))
      (syn_wa (.classMem (syn_cpw1 (.cv a)) (syn_ctfin M))
        (.classMem (syn_cpw1 (.cv b)) (syn_ctfin N)))
      (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))
      (.classEq (syn_ctfin M) (syn_ctfin N))
  have p0043 :=
    @g_eleqtrrd
      (syn_w3a (syn_wa (.classMem (.cv a) M) (.classMem (.cv b) N))
        (syn_wa (.classMem (syn_cpw1 (.cv a)) (syn_ctfin M))
          (.classMem (syn_cpw1 (.cv b)) (syn_ctfin N)))
        (syn_w3a (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))
          (.classEq (syn_ctfin M) (syn_ctfin N))))
      (syn_cpw1 (.cv b)) (syn_ctfin N) (syn_ctfin M) p0041 p0042
  have freeVariableCertificate2 : p ∉ ((Class.cv a)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_p_ne_a, not_false_eq_true]
  have freeVariableCertificate3 : p ∉ ((Class.cv b)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_p_ne_b, not_false_eq_true]
  have p0044 :=
    @g_ncfinlower (.cv a) (.cv b) p (syn_ctfin M) freeVariableCertificate2
      freeVariableCertificate3
  have p0045_e03_recanon :
    Nominal.NPrf
      (.imp (syn_w3a (.classMem (syn_ctfin M) (syn_cnnc))
          (.classMem (syn_cpw1 (.cv a)) (syn_ctfin M))
          (.classMem (syn_cpw1 (.cv b)) (syn_ctfin M)))
        (syn_wrex p (syn_cnnc) (syn_wa (.objMem a p) (.objMem b p)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_w3a syn_wa syn_ctfin syn_cif syn_wo syn_c0 syn_cdif syn_cin syn_ccompl
          syn_cnin syn_wnan syn_cvv syn_cio syn_cuni syn_wex syn_csn syn_cnnc syn_cint
          syn_cpw1 syn_wrex
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
    @g_syl3anc
      (syn_w3a (syn_wa (.classMem (.cv a) M) (.classMem (.cv b) N))
        (syn_wa (.classMem (syn_cpw1 (.cv a)) (syn_ctfin M))
          (.classMem (syn_cpw1 (.cv b)) (syn_ctfin N)))
        (syn_w3a (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))
          (.classEq (syn_ctfin M) (syn_ctfin N))))
      (.classMem (syn_ctfin M) (syn_cnnc)) (.classMem (syn_cpw1 (.cv a)) (syn_ctfin M))
      (.classMem (syn_cpw1 (.cv b)) (syn_ctfin M))
      (syn_wrex p (syn_cnnc) (syn_wa (.objMem a p) (.objMem b p))) p0039 p0040 p0043
      p0045_e03_recanon
  have p0046 :=
    @g_simpl31 (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))
      (.classEq (syn_ctfin M) (syn_ctfin N))
      (syn_wa (.classMem (.cv a) M) (.classMem (.cv b) N))
      (syn_wa (.classMem (syn_cpw1 (.cv a)) (syn_ctfin M))
        (.classMem (syn_cpw1 (.cv b)) (syn_ctfin N)))
      (syn_wa (.classMem (.cv p) (syn_cnnc)) (syn_wa (.objMem a p) (.objMem b p)))
  have p0047 :=
    @g_simprl
      (syn_w3a (syn_wa (.classMem (.cv a) M) (.classMem (.cv b) N))
        (syn_wa (.classMem (syn_cpw1 (.cv a)) (syn_ctfin M))
          (.classMem (syn_cpw1 (.cv b)) (syn_ctfin N)))
        (syn_w3a (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))
          (.classEq (syn_ctfin M) (syn_ctfin N))))
      (.classMem (.cv p) (syn_cnnc)) (syn_wa (.objMem a p) (.objMem b p))
  have p0048 :=
    @g_simpl1l (.classMem (.cv a) M) (.classMem (.cv b) N)
      (syn_wa (.classMem (syn_cpw1 (.cv a)) (syn_ctfin M))
        (.classMem (syn_cpw1 (.cv b)) (syn_ctfin N)))
      (syn_w3a (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))
        (.classEq (syn_ctfin M) (syn_ctfin N)))
      (syn_wa (.classMem (.cv p) (syn_cnnc)) (syn_wa (.objMem a p) (.objMem b p)))
  have p0049 :=
    @g_simprrl
      (syn_w3a (syn_wa (.classMem (.cv a) M) (.classMem (.cv b) N))
        (syn_wa (.classMem (syn_cpw1 (.cv a)) (syn_ctfin M))
          (.classMem (syn_cpw1 (.cv b)) (syn_ctfin N)))
        (syn_w3a (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))
          (.classEq (syn_ctfin M) (syn_ctfin N))))
      (.classMem (.cv p) (syn_cnnc)) (.objMem a p) (.objMem b p)
  have p0050 := @g_nnceleq (.cv a) M (.cv p)
  have p0051_e04_recanon :
    Nominal.NPrf
      (.imp (syn_wa (syn_wa (.classMem M (syn_cnnc)) (.classMem (.cv p) (syn_cnnc)))
          (syn_wa (.classMem (.cv a) M) (.objMem a p))) (.classEq M (.cv p))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wa
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
    @g_syl22anc
      (syn_wa (syn_w3a (syn_wa (.classMem (.cv a) M) (.classMem (.cv b) N))
          (syn_wa (.classMem (syn_cpw1 (.cv a)) (syn_ctfin M))
            (.classMem (syn_cpw1 (.cv b)) (syn_ctfin N)))
          (syn_w3a (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))
            (.classEq (syn_ctfin M) (syn_ctfin N))))
        (syn_wa (.classMem (.cv p) (syn_cnnc)) (syn_wa (.objMem a p) (.objMem b p))))
      (.classMem M (syn_cnnc)) (.classMem (.cv p) (syn_cnnc)) (.classMem (.cv a) M)
      (.objMem a p) (.classEq M (.cv p)) p0046 p0047 p0048 p0049 p0051_e04_recanon
  have p0052 :=
    @g_simpl32 (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))
      (.classEq (syn_ctfin M) (syn_ctfin N))
      (syn_wa (.classMem (.cv a) M) (.classMem (.cv b) N))
      (syn_wa (.classMem (syn_cpw1 (.cv a)) (syn_ctfin M))
        (.classMem (syn_cpw1 (.cv b)) (syn_ctfin N)))
      (syn_wa (.classMem (.cv p) (syn_cnnc)) (syn_wa (.objMem a p) (.objMem b p)))
  have p0053 :=
    @g_simpl1r (.classMem (.cv a) M) (.classMem (.cv b) N)
      (syn_wa (.classMem (syn_cpw1 (.cv a)) (syn_ctfin M))
        (.classMem (syn_cpw1 (.cv b)) (syn_ctfin N)))
      (syn_w3a (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))
        (.classEq (syn_ctfin M) (syn_ctfin N)))
      (syn_wa (.classMem (.cv p) (syn_cnnc)) (syn_wa (.objMem a p) (.objMem b p)))
  have p0054 :=
    @g_simprrr
      (syn_w3a (syn_wa (.classMem (.cv a) M) (.classMem (.cv b) N))
        (syn_wa (.classMem (syn_cpw1 (.cv a)) (syn_ctfin M))
          (.classMem (syn_cpw1 (.cv b)) (syn_ctfin N)))
        (syn_w3a (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))
          (.classEq (syn_ctfin M) (syn_ctfin N))))
      (.classMem (.cv p) (syn_cnnc)) (.objMem a p) (.objMem b p)
  have p0055 := @g_nnceleq (.cv b) N (.cv p)
  have p0056_e04_recanon :
    Nominal.NPrf
      (.imp (syn_wa (syn_wa (.classMem N (syn_cnnc)) (.classMem (.cv p) (syn_cnnc)))
          (syn_wa (.classMem (.cv b) N) (.objMem b p))) (.classEq N (.cv p))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wa
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
    @g_syl22anc
      (syn_wa (syn_w3a (syn_wa (.classMem (.cv a) M) (.classMem (.cv b) N))
          (syn_wa (.classMem (syn_cpw1 (.cv a)) (syn_ctfin M))
            (.classMem (syn_cpw1 (.cv b)) (syn_ctfin N)))
          (syn_w3a (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))
            (.classEq (syn_ctfin M) (syn_ctfin N))))
        (syn_wa (.classMem (.cv p) (syn_cnnc)) (syn_wa (.objMem a p) (.objMem b p))))
      (.classMem N (syn_cnnc)) (.classMem (.cv p) (syn_cnnc)) (.classMem (.cv b) N)
      (.objMem b p) (.classEq N (.cv p)) p0052 p0047 p0053 p0054 p0056_e04_recanon
  have p0057 :=
    @g_eqtr4d
      (syn_wa (syn_w3a (syn_wa (.classMem (.cv a) M) (.classMem (.cv b) N))
          (syn_wa (.classMem (syn_cpw1 (.cv a)) (syn_ctfin M))
            (.classMem (syn_cpw1 (.cv b)) (syn_ctfin N)))
          (syn_w3a (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))
            (.classEq (syn_ctfin M) (syn_ctfin N))))
        (syn_wa (.classMem (.cv p) (syn_cnnc)) (syn_wa (.objMem a p) (.objMem b p))))
      M (.cv p) N p0051 p0056
  have p0058 :=
    @g_expr
      (syn_w3a (syn_wa (.classMem (.cv a) M) (.classMem (.cv b) N))
        (syn_wa (.classMem (syn_cpw1 (.cv a)) (syn_ctfin M))
          (.classMem (syn_cpw1 (.cv b)) (syn_ctfin N)))
        (syn_w3a (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))
          (.classEq (syn_ctfin M) (syn_ctfin N))))
      (.classMem (.cv p) (syn_cnnc)) (syn_wa (.objMem a p) (.objMem b p)) (.classEq M N)
      p0057
  have freeVariableCertificate4 : p ∉ ((Wff.classEq M N)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union,
      fresh_p_not_M, fresh_p_not_N, or_false, not_false_eq_true]
  have freeVariableCertificate5 :
    p ∉
      ((syn_w3a (syn_wa (.classMem (.cv a) M) (.classMem (.cv b) N))
          (syn_wa (.classMem (syn_cpw1 (.cv a)) (syn_ctfin M))
            (.classMem (syn_cpw1 (.cv b)) (syn_ctfin N)))
          (syn_w3a (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))
            (.classEq (syn_ctfin M) (syn_ctfin N))))).fv :=
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
    @g_rexlimdva
      (syn_w3a (syn_wa (.classMem (.cv a) M) (.classMem (.cv b) N))
        (syn_wa (.classMem (syn_cpw1 (.cv a)) (syn_ctfin M))
          (.classMem (syn_cpw1 (.cv b)) (syn_ctfin N)))
        (syn_w3a (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))
          (.classEq (syn_ctfin M) (syn_ctfin N))))
      (syn_wa (.objMem a p) (.objMem b p)) (.classEq M N) p (syn_cnnc)
      freeVariableCertificate4 freeVariableCertificate5 p0058
  have p0060 :=
    @g_mpd
      (syn_w3a (syn_wa (.classMem (.cv a) M) (.classMem (.cv b) N))
        (syn_wa (.classMem (syn_cpw1 (.cv a)) (syn_ctfin M))
          (.classMem (syn_cpw1 (.cv b)) (syn_ctfin N)))
        (syn_w3a (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))
          (.classEq (syn_ctfin M) (syn_ctfin N))))
      (syn_wrex p (syn_cnnc) (syn_wa (.objMem a p) (.objMem b p))) (.classEq M N) p0045
      p0059
  have p0061 :=
    @g_n_3exp (syn_wa (.classMem (.cv a) M) (.classMem (.cv b) N))
      (syn_wa (.classMem (syn_cpw1 (.cv a)) (syn_ctfin M))
        (.classMem (syn_cpw1 (.cv b)) (syn_ctfin N)))
      (syn_w3a (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))
        (.classEq (syn_ctfin M) (syn_ctfin N)))
      (.classEq M N) p0060
  have freeVariableCertificate6 :
    a ∉
      ((Wff.imp (syn_w3a (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))
            (.classEq (syn_ctfin M) (syn_ctfin N))) (.classEq M N))).fv :=
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
      ((Wff.imp (syn_w3a (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))
            (.classEq (syn_ctfin M) (syn_ctfin N))) (.classEq M N))).fv :=
    by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union,
      Finset.notMem_empty, fresh_b_not_M, fresh_b_not_N, or_false, not_false_eq_true]
  have p0062 :=
    @g_rexlimivv
      (syn_wa (.classMem (syn_cpw1 (.cv a)) (syn_ctfin M))
        (.classMem (syn_cpw1 (.cv b)) (syn_ctfin N)))
      (.imp (syn_w3a (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))
          (.classEq (syn_ctfin M) (syn_ctfin N))) (.classEq M N))
      a b M N (by exact (show b ∉ (M).fv from (by exact fresh_b_not_M)))
      freeVariableCertificate6 freeVariableCertificate7
      (show a ≠ b from (by exact fresh_a_ne_b)) p0061
  have p0063 :=
    @g_sylbir
      (syn_wa (syn_wrex a M (.classMem (syn_cpw1 (.cv a)) (syn_ctfin M)))
        (syn_wrex b N (.classMem (syn_cpw1 (.cv b)) (syn_ctfin N))))
      (syn_wrex a M (syn_wrex b N (syn_wa (.classMem (syn_cpw1 (.cv a)) (syn_ctfin M))
            (.classMem (syn_cpw1 (.cv b)) (syn_ctfin N)))))
      (.imp (syn_w3a (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))
          (.classEq (syn_ctfin M) (syn_ctfin N))) (.classEq M N))
      p0036 p0062
  have p0064 :=
    @g_ad2ant2l (syn_wrex a M (.classMem (syn_cpw1 (.cv a)) (syn_ctfin M)))
      (syn_wrex b N (.classMem (syn_cpw1 (.cv b)) (syn_ctfin N)))
      (.imp (syn_w3a (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))
          (.classEq (syn_ctfin M) (syn_ctfin N))) (.classEq M N))
      (.classMem (syn_ctfin M) (syn_cnnc)) (.classMem (syn_ctfin N) (syn_cnnc)) p0063
  have p0065 :=
    @g_com12
      (syn_wa (syn_wa (.classMem (syn_ctfin M) (syn_cnnc))
          (syn_wrex a M (.classMem (syn_cpw1 (.cv a)) (syn_ctfin M))))
        (syn_wa (.classMem (syn_ctfin N) (syn_cnnc))
          (syn_wrex b N (.classMem (syn_cpw1 (.cv b)) (syn_ctfin N)))))
      (syn_w3a (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))
        (.classEq (syn_ctfin M) (syn_ctfin N)))
      (.classEq M N) p0064
  have p0066 :=
    @g_syl2and
      (syn_w3a (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))
        (.classEq (syn_ctfin M) (syn_ctfin N)))
      (syn_wne M (syn_c0))
      (syn_wa (.classMem (syn_ctfin M) (syn_cnnc))
        (syn_wrex a M (.classMem (syn_cpw1 (.cv a)) (syn_ctfin M))))
      (syn_wne N (syn_c0))
      (syn_wa (.classMem (syn_ctfin N) (syn_cnnc))
        (syn_wrex b N (.classMem (syn_cpw1 (.cv b)) (syn_ctfin N))))
      (.classEq M N) p0032 p0035 p0065
  have p0067 :=
    @g_syld
      (syn_w3a (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))
        (.classEq (syn_ctfin M) (syn_ctfin N)))
      (syn_wne (syn_ctfin M) (syn_c0)) (syn_wa (syn_wne M (syn_c0)) (syn_wne N (syn_c0)))
      (.classEq M N) p0029 p0066
  have p0068 :=
    @g_com12
      (syn_w3a (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))
        (.classEq (syn_ctfin M) (syn_ctfin N)))
      (syn_wne (syn_ctfin M) (syn_c0)) (.classEq M N) p0067
  have p0069 :=
    @g_pm2_61ine
      (.imp (syn_w3a (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))
          (.classEq (syn_ctfin M) (syn_ctfin N))) (.classEq M N))
      (syn_ctfin M) (syn_c0) p0015 p0068
  exact p0069

@[expose]
noncomputable def g_tfinpw1 (A : Class) (M : Class) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem M (syn_cnnc)) (.classMem A M))
        (.classMem (syn_cpw1 A) (syn_ctfin M))) :=
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
  have p0000 := @g_ne0i M A
  have p0001 := @g_tfinprop M b (by exact (show b ∉ (M).fv from (by exact fresh_b_not_M)))
  have p0002 :=
    @g_sylan2 (.classMem A M) (.classMem M (syn_cnnc)) (syn_wne M (syn_c0))
      (syn_wa (.classMem (syn_ctfin M) (syn_cnnc))
        (syn_wrex b M (.classMem (syn_cpw1 (.cv b)) (syn_ctfin M))))
      p0000 p0001
  have freeVariableCertificate0 : n ∉ ((Class.cv b)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_n_ne_b, not_false_eq_true]
  have p0003 :=
    @g_ncfinraise A (.cv b) n M (by exact (show n ∉ (A).fv from (by exact fresh_n_not_A)))
      freeVariableCertificate0
  have p0004 :=
    @g_n_3expa (.classMem M (syn_cnnc)) (.classMem A M) (.classMem (.cv b) M)
      (syn_wrex n (syn_cnnc)
        (syn_wa (.classMem (syn_cpw1 A) (.cv n)) (.classMem (syn_cpw1 (.cv b)) (.cv n))))
      p0003
  have p0005 :=
    @g_adantrr (syn_wa (.classMem M (syn_cnnc)) (.classMem A M)) (.classMem (.cv b) M)
      (syn_wrex n (syn_cnnc)
        (syn_wa (.classMem (syn_cpw1 A) (.cv n)) (.classMem (syn_cpw1 (.cv b)) (.cv n))))
      (.classMem (syn_cpw1 (.cv b)) (syn_ctfin M)) p0004
  have p0006 :=
    @g_simp3rl (.classMem (syn_cpw1 A) (.cv n)) (.classMem (syn_cpw1 (.cv b)) (.cv n))
      (.classMem (.cv n) (syn_cnnc)) (syn_wa (.classMem M (syn_cnnc)) (.classMem A M))
      (syn_wa (.classMem (.cv b) M) (.classMem (syn_cpw1 (.cv b)) (syn_ctfin M)))
  have p0007 :=
    @g_simp3l (syn_wa (.classMem M (syn_cnnc)) (.classMem A M))
      (syn_wa (.classMem (.cv b) M) (.classMem (syn_cpw1 (.cv b)) (syn_ctfin M)))
      (.classMem (.cv n) (syn_cnnc))
      (syn_wa (.classMem (syn_cpw1 A) (.cv n)) (.classMem (syn_cpw1 (.cv b)) (.cv n)))
  have p0008 :=
    @g_simp1l (.classMem M (syn_cnnc)) (.classMem A M)
      (syn_wa (.classMem (.cv b) M) (.classMem (syn_cpw1 (.cv b)) (syn_ctfin M)))
      (syn_wa (.classMem (.cv n) (syn_cnnc))
        (syn_wa (.classMem (syn_cpw1 A) (.cv n)) (.classMem (syn_cpw1 (.cv b)) (.cv n))))
  have p0009 := @g_tfincl M
  have p0010 :=
    @g_syl
      (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem A M))
        (syn_wa (.classMem (.cv b) M) (.classMem (syn_cpw1 (.cv b)) (syn_ctfin M)))
        (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wa (.classMem (syn_cpw1 A) (.cv n))
            (.classMem (syn_cpw1 (.cv b)) (.cv n)))))
      (.classMem M (syn_cnnc)) (.classMem (syn_ctfin M) (syn_cnnc)) p0008 p0009
  have p0011 :=
    @g_simp3rr (.classMem (syn_cpw1 A) (.cv n)) (.classMem (syn_cpw1 (.cv b)) (.cv n))
      (.classMem (.cv n) (syn_cnnc)) (syn_wa (.classMem M (syn_cnnc)) (.classMem A M))
      (syn_wa (.classMem (.cv b) M) (.classMem (syn_cpw1 (.cv b)) (syn_ctfin M)))
  have p0012 :=
    @g_simp2r (syn_wa (.classMem M (syn_cnnc)) (.classMem A M)) (.classMem (.cv b) M)
      (.classMem (syn_cpw1 (.cv b)) (syn_ctfin M))
      (syn_wa (.classMem (.cv n) (syn_cnnc))
        (syn_wa (.classMem (syn_cpw1 A) (.cv n)) (.classMem (syn_cpw1 (.cv b)) (.cv n))))
  have p0013 := @g_nnceleq (syn_cpw1 (.cv b)) (.cv n) (syn_ctfin M)
  have p0014 :=
    @g_syl22anc
      (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem A M))
        (syn_wa (.classMem (.cv b) M) (.classMem (syn_cpw1 (.cv b)) (syn_ctfin M)))
        (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wa (.classMem (syn_cpw1 A) (.cv n))
            (.classMem (syn_cpw1 (.cv b)) (.cv n)))))
      (.classMem (.cv n) (syn_cnnc)) (.classMem (syn_ctfin M) (syn_cnnc))
      (.classMem (syn_cpw1 (.cv b)) (.cv n)) (.classMem (syn_cpw1 (.cv b)) (syn_ctfin M))
      (.classEq (.cv n) (syn_ctfin M)) p0007 p0010 p0011 p0012 p0013
  have p0015 :=
    @g_eleqtrd
      (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem A M))
        (syn_wa (.classMem (.cv b) M) (.classMem (syn_cpw1 (.cv b)) (syn_ctfin M)))
        (syn_wa (.classMem (.cv n) (syn_cnnc)) (syn_wa (.classMem (syn_cpw1 A) (.cv n))
            (.classMem (syn_cpw1 (.cv b)) (.cv n)))))
      (syn_cpw1 A) (.cv n) (syn_ctfin M) p0006 p0014
  have p0016 :=
    @g_n_3expa (syn_wa (.classMem M (syn_cnnc)) (.classMem A M))
      (syn_wa (.classMem (.cv b) M) (.classMem (syn_cpw1 (.cv b)) (syn_ctfin M)))
      (syn_wa (.classMem (.cv n) (syn_cnnc))
        (syn_wa (.classMem (syn_cpw1 A) (.cv n)) (.classMem (syn_cpw1 (.cv b)) (.cv n))))
      (.classMem (syn_cpw1 A) (syn_ctfin M)) p0015
  have p0017 :=
    @g_expr
      (syn_wa (syn_wa (.classMem M (syn_cnnc)) (.classMem A M))
        (syn_wa (.classMem (.cv b) M) (.classMem (syn_cpw1 (.cv b)) (syn_ctfin M))))
      (.classMem (.cv n) (syn_cnnc))
      (syn_wa (.classMem (syn_cpw1 A) (.cv n)) (.classMem (syn_cpw1 (.cv b)) (.cv n)))
      (.classMem (syn_cpw1 A) (syn_ctfin M)) p0016
  have freeVariableCertificate1 : n ∉ ((Wff.classMem (syn_cpw1 A) (syn_ctfin M))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin, Finset.mem_union,
      fresh_n_not_A, fresh_n_not_M, or_false, not_false_eq_true]
  have freeVariableCertificate2 :
    n ∉
      ((syn_wa (syn_wa (.classMem M (syn_cnnc)) (.classMem A M)) (syn_wa (.classMem (.cv b) M)
            (.classMem (syn_cpw1 (.cv b)) (syn_ctfin M))))).fv :=
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
    @g_rexlimdva
      (syn_wa (syn_wa (.classMem M (syn_cnnc)) (.classMem A M))
        (syn_wa (.classMem (.cv b) M) (.classMem (syn_cpw1 (.cv b)) (syn_ctfin M))))
      (syn_wa (.classMem (syn_cpw1 A) (.cv n)) (.classMem (syn_cpw1 (.cv b)) (.cv n)))
      (.classMem (syn_cpw1 A) (syn_ctfin M)) n (syn_cnnc) freeVariableCertificate1
      freeVariableCertificate2 p0017
  have p0019 :=
    @g_mpd
      (syn_wa (syn_wa (.classMem M (syn_cnnc)) (.classMem A M))
        (syn_wa (.classMem (.cv b) M) (.classMem (syn_cpw1 (.cv b)) (syn_ctfin M))))
      (syn_wrex n (syn_cnnc)
        (syn_wa (.classMem (syn_cpw1 A) (.cv n)) (.classMem (syn_cpw1 (.cv b)) (.cv n))))
      (.classMem (syn_cpw1 A) (syn_ctfin M)) p0005 p0018
  have p0020 :=
    @g_expr (syn_wa (.classMem M (syn_cnnc)) (.classMem A M)) (.classMem (.cv b) M)
      (.classMem (syn_cpw1 (.cv b)) (syn_ctfin M)) (.classMem (syn_cpw1 A) (syn_ctfin M))
      p0019
  have freeVariableCertificate3 : b ∉ ((Wff.classMem (syn_cpw1 A) (syn_ctfin M))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin, Finset.mem_union,
      fresh_b_not_A, fresh_b_not_M, or_false, not_false_eq_true]
  have freeVariableCertificate4 :
    b ∉ ((syn_wa (.classMem M (syn_cnnc)) (.classMem A M))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union,
      Finset.notMem_empty, fresh_b_not_M, fresh_b_not_A, or_false, not_false_eq_true]
  have p0021 :=
    @g_rexlimdva (syn_wa (.classMem M (syn_cnnc)) (.classMem A M))
      (.classMem (syn_cpw1 (.cv b)) (syn_ctfin M)) (.classMem (syn_cpw1 A) (syn_ctfin M))
      b M freeVariableCertificate3 freeVariableCertificate4 p0020
  have p0022 :=
    @g_adantld (syn_wa (.classMem M (syn_cnnc)) (.classMem A M))
      (syn_wrex b M (.classMem (syn_cpw1 (.cv b)) (syn_ctfin M)))
      (.classMem (syn_cpw1 A) (syn_ctfin M)) (.classMem (syn_ctfin M) (syn_cnnc)) p0021
  have p0023 :=
    @g_mpd (syn_wa (.classMem M (syn_cnnc)) (.classMem A M))
      (syn_wa (.classMem (syn_ctfin M) (syn_cnnc))
        (syn_wrex b M (.classMem (syn_cpw1 (.cv b)) (syn_ctfin M))))
      (.classMem (syn_cpw1 A) (syn_ctfin M)) p0002 p0022
  exact p0023

@[expose]
noncomputable def g_ncfintfin (A : Class) (V : Class) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem (syn_cvv) (syn_cfin)) (.classMem A V))
        (.classEq (syn_ctfin (syn_cncfin A)) (syn_cncfin (syn_cpw1 A)))) :=
  by
  have p0000 := @g_ncfinprop A V
  have p0001 :=
    @g_simpld (syn_wa (.classMem (syn_cvv) (syn_cfin)) (.classMem A V))
      (.classMem (syn_cncfin A) (syn_cnnc)) (.classMem A (syn_cncfin A)) p0000
  have p0002 := @g_tfincl (syn_cncfin A)
  have p0003 :=
    @g_syl (syn_wa (.classMem (syn_cvv) (syn_cfin)) (.classMem A V))
      (.classMem (syn_cncfin A) (syn_cnnc))
      (.classMem (syn_ctfin (syn_cncfin A)) (syn_cnnc)) p0001 p0002
  have p0004 := @g_pw1exg A V
  have p0005 := @g_ncfinprop (syn_cpw1 A) (syn_cvv)
  have p0006 :=
    @g_sylan2 (.classMem A V) (.classMem (syn_cvv) (syn_cfin))
      (.classMem (syn_cpw1 A) (syn_cvv))
      (syn_wa (.classMem (syn_cncfin (syn_cpw1 A)) (syn_cnnc))
        (.classMem (syn_cpw1 A) (syn_cncfin (syn_cpw1 A))))
      p0004 p0005
  have p0007 :=
    @g_simpld (syn_wa (.classMem (syn_cvv) (syn_cfin)) (.classMem A V))
      (.classMem (syn_cncfin (syn_cpw1 A)) (syn_cnnc))
      (.classMem (syn_cpw1 A) (syn_cncfin (syn_cpw1 A))) p0006
  have p0008 := @g_tfinpw1 A (syn_cncfin A)
  have p0009 :=
    @g_syl (syn_wa (.classMem (syn_cvv) (syn_cfin)) (.classMem A V))
      (syn_wa (.classMem (syn_cncfin A) (syn_cnnc)) (.classMem A (syn_cncfin A)))
      (.classMem (syn_cpw1 A) (syn_ctfin (syn_cncfin A))) p0000 p0008
  have p0010 :=
    @g_simprd (syn_wa (.classMem (syn_cvv) (syn_cfin)) (.classMem A V))
      (.classMem (syn_cncfin (syn_cpw1 A)) (syn_cnnc))
      (.classMem (syn_cpw1 A) (syn_cncfin (syn_cpw1 A))) p0006
  have p0011 :=
    @g_nnceleq (syn_cpw1 A) (syn_ctfin (syn_cncfin A)) (syn_cncfin (syn_cpw1 A))
  have p0012 :=
    @g_syl22anc (syn_wa (.classMem (syn_cvv) (syn_cfin)) (.classMem A V))
      (.classMem (syn_ctfin (syn_cncfin A)) (syn_cnnc))
      (.classMem (syn_cncfin (syn_cpw1 A)) (syn_cnnc))
      (.classMem (syn_cpw1 A) (syn_ctfin (syn_cncfin A)))
      (.classMem (syn_cpw1 A) (syn_cncfin (syn_cpw1 A)))
      (.classEq (syn_ctfin (syn_cncfin A)) (syn_cncfin (syn_cpw1 A))) p0003 p0007 p0009
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

@[expose]
noncomputable def g_tfindi (M : Class) (N : Class) :
    Nominal.NPrf
      (.imp (syn_w3a (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))
          (syn_wne (syn_cplc M N) (syn_c0)))
        (.classEq (syn_ctfin (syn_cplc M N)) (syn_cplc (syn_ctfin M) (syn_ctfin N)))) :=
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
  have freeVariableCertificate0 : a ∉ ((syn_cplc M N)).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, Finset.mem_union,
      fresh_a_not_M, fresh_a_not_N, or_false, not_false_eq_true]
  have p0000 := @g_n0 a (syn_cplc M N) freeVariableCertificate0
  have p0001 := @g_nncaddccl M N
  have p0002 := @g_tfincl (syn_cplc M N)
  have p0003 :=
    @g_syl (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)))
      (.classMem (syn_cplc M N) (syn_cnnc))
      (.classMem (syn_ctfin (syn_cplc M N)) (syn_cnnc)) p0001 p0002
  have p0004 :=
    @g_n_3adant3 (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))
      (.classMem (syn_ctfin (syn_cplc M N)) (syn_cnnc)) (.classMem (.cv a) (syn_cplc M N))
      p0003
  have p0005 := @g_tfincl M
  have p0006 := @g_tfincl N
  have p0007 := @g_nncaddccl (syn_ctfin M) (syn_ctfin N)
  have p0008 :=
    @g_syl2an (.classMem M (syn_cnnc)) (.classMem (syn_ctfin M) (syn_cnnc))
      (.classMem (syn_ctfin N) (syn_cnnc))
      (.classMem (syn_cplc (syn_ctfin M) (syn_ctfin N)) (syn_cnnc))
      (.classMem N (syn_cnnc)) p0005 p0006 p0007
  have p0009 :=
    @g_n_3adant3 (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))
      (.classMem (syn_cplc (syn_ctfin M) (syn_ctfin N)) (syn_cnnc))
      (.classMem (.cv a) (syn_cplc M N)) p0008
  have p0010 :=
    @g_n_3adant3 (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))
      (.classMem (syn_cplc M N) (syn_cnnc)) (.classMem (.cv a) (syn_cplc M N)) p0001
  have p0011 :=
    @g_simp3 (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))
      (.classMem (.cv a) (syn_cplc M N))
  have p0012 := @g_tfinpw1 (.cv a) (syn_cplc M N)
  have p0013 :=
    @g_syl2anc
      (syn_w3a (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))
        (.classMem (.cv a) (syn_cplc M N)))
      (.classMem (syn_cplc M N) (syn_cnnc)) (.classMem (.cv a) (syn_cplc M N))
      (.classMem (syn_cpw1 (.cv a)) (syn_ctfin (syn_cplc M N))) p0010 p0011 p0012
  have freeVariableCertificate1 : b ∉ ((Class.cv a)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_b_ne_a, not_false_eq_true]
  have freeVariableCertificate2 : c ∉ ((Class.cv a)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_c_ne_a, not_false_eq_true]
  have p0014 :=
    @g_eladdc (.cv a) M N b c freeVariableCertificate1 freeVariableCertificate2
      (by exact (show b ∉ (M).fv from (by exact fresh_b_not_M)))
      (by exact (show c ∉ (M).fv from (by exact fresh_c_not_M)))
      (by exact (show b ∉ (N).fv from (by exact fresh_b_not_N)))
      (by exact (show c ∉ (N).fv from (by exact fresh_c_not_N)))
      (show b ≠ c from (by exact fresh_b_ne_c))
  have p0015 :=
    @g_simplll (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))
      (syn_wa (.classMem (.cv b) M) (.classMem (.cv c) N))
      (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0))
  have p0016 :=
    @g_simplrl (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)))
      (.classMem (.cv b) M) (.classMem (.cv c) N)
      (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0))
  have p0017 := @g_tfinpw1 (.cv b) M
  have p0018 :=
    @g_syl2anc
      (syn_wa (syn_wa (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)))
          (syn_wa (.classMem (.cv b) M) (.classMem (.cv c) N)))
        (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0)))
      (.classMem M (syn_cnnc)) (.classMem (.cv b) M)
      (.classMem (syn_cpw1 (.cv b)) (syn_ctfin M)) p0015 p0016 p0017
  have p0019 :=
    @g_simpllr (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))
      (syn_wa (.classMem (.cv b) M) (.classMem (.cv c) N))
      (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0))
  have p0020 :=
    @g_simplrr (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)))
      (.classMem (.cv b) M) (.classMem (.cv c) N)
      (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0))
  have p0021 := @g_tfinpw1 (.cv c) N
  have p0022 :=
    @g_syl2anc
      (syn_wa (syn_wa (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)))
          (syn_wa (.classMem (.cv b) M) (.classMem (.cv c) N)))
        (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0)))
      (.classMem N (syn_cnnc)) (.classMem (.cv c) N)
      (.classMem (syn_cpw1 (.cv c)) (syn_ctfin N)) p0019 p0020 p0021
  have p0023 := @g_pw1eq (syn_cin (.cv b) (.cv c)) (syn_c0)
  have p0024 := @g_pw1in (.cv b) (.cv c)
  have p0025 := @g_pw10
  have p0026 :=
    @g_n_3eqtr3g (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0))
      (syn_cpw1 (syn_cin (.cv b) (.cv c))) (syn_cpw1 (syn_c0))
      (syn_cin (syn_cpw1 (.cv b)) (syn_cpw1 (.cv c))) (syn_c0) p0023 p0024 p0025
  have p0027 :=
    @g_adantl (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0))
      (.classEq (syn_cin (syn_cpw1 (.cv b)) (syn_cpw1 (.cv c))) (syn_c0))
      (syn_wa (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)))
        (syn_wa (.classMem (.cv b) M) (.classMem (.cv c) N)))
      p0026
  have p0028 :=
    @g_eladdci (syn_cpw1 (.cv b)) (syn_cpw1 (.cv c)) (syn_ctfin M) (syn_ctfin N)
  have p0029 :=
    @g_syl3anc
      (syn_wa (syn_wa (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)))
          (syn_wa (.classMem (.cv b) M) (.classMem (.cv c) N)))
        (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0)))
      (.classMem (syn_cpw1 (.cv b)) (syn_ctfin M))
      (.classMem (syn_cpw1 (.cv c)) (syn_ctfin N))
      (.classEq (syn_cin (syn_cpw1 (.cv b)) (syn_cpw1 (.cv c))) (syn_c0))
      (.classMem (syn_cun (syn_cpw1 (.cv b)) (syn_cpw1 (.cv c)))
        (syn_cplc (syn_ctfin M) (syn_ctfin N)))
      p0018 p0022 p0027 p0028
  have p0030 := @g_pw1eq (.cv a) (syn_cun (.cv b) (.cv c))
  have p0031 := @g_pw1un (.cv b) (.cv c)
  have p0032 :=
    @g_syl6eq (.classEq (.cv a) (syn_cun (.cv b) (.cv c))) (syn_cpw1 (.cv a))
      (syn_cpw1 (syn_cun (.cv b) (.cv c))) (syn_cun (syn_cpw1 (.cv b)) (syn_cpw1 (.cv c)))
      p0030 p0031
  have p0033 :=
    @g_eleq1d (.classEq (.cv a) (syn_cun (.cv b) (.cv c))) (syn_cpw1 (.cv a))
      (syn_cun (syn_cpw1 (.cv b)) (syn_cpw1 (.cv c)))
      (syn_cplc (syn_ctfin M) (syn_ctfin N)) p0032
  have p0034 :=
    @g_syl5ibrcom
      (syn_wa (syn_wa (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)))
          (syn_wa (.classMem (.cv b) M) (.classMem (.cv c) N)))
        (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0)))
      (.classMem (syn_cpw1 (.cv a)) (syn_cplc (syn_ctfin M) (syn_ctfin N)))
      (.classEq (.cv a) (syn_cun (.cv b) (.cv c)))
      (.classMem (syn_cun (syn_cpw1 (.cv b)) (syn_cpw1 (.cv c)))
        (syn_cplc (syn_ctfin M) (syn_ctfin N)))
      p0029 p0033
  have p0035 :=
    @g_expimpd
      (syn_wa (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)))
        (syn_wa (.classMem (.cv b) M) (.classMem (.cv c) N)))
      (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0))
      (.classEq (.cv a) (syn_cun (.cv b) (.cv c)))
      (.classMem (syn_cpw1 (.cv a)) (syn_cplc (syn_ctfin M) (syn_ctfin N))) p0034
  have freeVariableCertificate3 :
    b ∉ ((Wff.classMem (syn_cpw1 (.cv a)) (syn_cplc (syn_ctfin M) (syn_ctfin N)))).fv :=
    by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin, Finset.mem_union,
      Finset.mem_singleton, fresh_b_ne_a, fresh_b_not_M, fresh_b_not_N, or_false,
      not_false_eq_true]
  have freeVariableCertificate4 :
    c ∉ ((Wff.classMem (syn_cpw1 (.cv a)) (syn_cplc (syn_ctfin M) (syn_ctfin N)))).fv :=
    by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin, Finset.mem_union,
      Finset.mem_singleton, fresh_c_ne_a, fresh_c_not_M, fresh_c_not_N, or_false,
      not_false_eq_true]
  have freeVariableCertificate5 :
    b ∉ ((syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union,
      Finset.notMem_empty, fresh_b_not_M, fresh_b_not_N, or_false, not_false_eq_true]
  have freeVariableCertificate6 :
    c ∉ ((syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union,
      Finset.notMem_empty, fresh_c_not_M, fresh_c_not_N, or_false, not_false_eq_true]
  have p0036 :=
    @g_rexlimdvva (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)))
      (syn_wa (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0))
        (.classEq (.cv a) (syn_cun (.cv b) (.cv c))))
      (.classMem (syn_cpw1 (.cv a)) (syn_cplc (syn_ctfin M) (syn_ctfin N))) b c M N
      (by exact (show c ∉ (M).fv from (by exact fresh_c_not_M))) freeVariableCertificate3
      freeVariableCertificate4 freeVariableCertificate5 freeVariableCertificate6
      (show b ≠ c from (by exact fresh_b_ne_c)) p0035
  have p0037 :=
    @g_syl5bi (.classMem (.cv a) (syn_cplc M N))
      (syn_wrex b M (syn_wrex c N (syn_wa (.classEq (syn_cin (.cv b) (.cv c)) (syn_c0))
            (.classEq (.cv a) (syn_cun (.cv b) (.cv c))))))
      (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)))
      (.classMem (syn_cpw1 (.cv a)) (syn_cplc (syn_ctfin M) (syn_ctfin N))) p0014 p0036
  have p0038 :=
    @g_n_3impia (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))
      (.classMem (.cv a) (syn_cplc M N))
      (.classMem (syn_cpw1 (.cv a)) (syn_cplc (syn_ctfin M) (syn_ctfin N))) p0037
  have p0039 :=
    @g_nnceleq (syn_cpw1 (.cv a)) (syn_ctfin (syn_cplc M N))
      (syn_cplc (syn_ctfin M) (syn_ctfin N))
  have p0040 :=
    @g_syl22anc
      (syn_w3a (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))
        (.classMem (.cv a) (syn_cplc M N)))
      (.classMem (syn_ctfin (syn_cplc M N)) (syn_cnnc))
      (.classMem (syn_cplc (syn_ctfin M) (syn_ctfin N)) (syn_cnnc))
      (.classMem (syn_cpw1 (.cv a)) (syn_ctfin (syn_cplc M N)))
      (.classMem (syn_cpw1 (.cv a)) (syn_cplc (syn_ctfin M) (syn_ctfin N)))
      (.classEq (syn_ctfin (syn_cplc M N)) (syn_cplc (syn_ctfin M) (syn_ctfin N))) p0004
      p0009 p0013 p0038 p0039
  have p0041 :=
    @g_n_3expia (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))
      (.classMem (.cv a) (syn_cplc M N))
      (.classEq (syn_ctfin (syn_cplc M N)) (syn_cplc (syn_ctfin M) (syn_ctfin N))) p0040
  have freeVariableCertificate7 :
    a ∉
      ((Wff.classEq (syn_ctfin (syn_cplc M N)) (syn_cplc (syn_ctfin M) (syn_ctfin N)))).fv :=
    by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, Finset.mem_union,
      fresh_a_not_M, fresh_a_not_N, or_false, not_false_eq_true]
  have freeVariableCertificate8 :
    a ∉ ((syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union,
      Finset.notMem_empty, fresh_a_not_M, fresh_a_not_N, or_false, not_false_eq_true]
  have p0042 :=
    @g_exlimdv (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)))
      (.classMem (.cv a) (syn_cplc M N))
      (.classEq (syn_ctfin (syn_cplc M N)) (syn_cplc (syn_ctfin M) (syn_ctfin N))) a
      freeVariableCertificate7 freeVariableCertificate8 p0041
  have p0043 :=
    @g_syl5bi (syn_wne (syn_cplc M N) (syn_c0))
      (syn_wex a (.classMem (.cv a) (syn_cplc M N)))
      (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)))
      (.classEq (syn_ctfin (syn_cplc M N)) (syn_cplc (syn_ctfin M) (syn_ctfin N))) p0000
      p0042
  have p0044 :=
    @g_n_3impia (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))
      (syn_wne (syn_cplc M N) (syn_c0))
      (.classEq (syn_ctfin (syn_cplc M N)) (syn_cplc (syn_ctfin M) (syn_ctfin N))) p0043
  exact p0044

@[expose]
noncomputable def g_tfin0c : Nominal.NPrf (.classEq (syn_ctfin (syn_c0c)) (syn_c0c)) :=
  by
  have p0000 := @g_peano1
  have p0001 := @g_tfincl (syn_c0c)
  have p0002 := Nominal.mp p0000 p0001
  have p0004 := @g_pw10
  have p0006 := @g_nulel0c
  have p0007 := @g_tfinpw1 (syn_c0) (syn_c0c)
  have p0008 :=
    @g_mp2an (.classMem (syn_c0c) (syn_cnnc)) (.classMem (syn_c0) (syn_c0c))
      (.classMem (syn_cpw1 (syn_c0)) (syn_ctfin (syn_c0c))) p0000 p0006 p0007
  have p0009 := @g_eqeltrri (syn_cpw1 (syn_c0)) (syn_c0) (syn_ctfin (syn_c0c)) p0004 p0008
  have p0011 := @g_nnceleq (syn_c0) (syn_ctfin (syn_c0c)) (syn_c0c)
  have p0012 :=
    @g_mp4an (.classMem (syn_ctfin (syn_c0c)) (syn_cnnc)) (.classMem (syn_c0c) (syn_cnnc))
      (.classMem (syn_c0) (syn_ctfin (syn_c0c))) (.classMem (syn_c0) (syn_c0c))
      (.classEq (syn_ctfin (syn_c0c)) (syn_c0c)) p0002 p0000 p0009 p0006 p0011
  exact p0012

@[expose]
noncomputable def g_tfinsuc (A : Class) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem A (syn_cnnc)) (syn_wne (syn_cplc A (syn_c1c)) (syn_c0)))
        (.classEq (syn_ctfin (syn_cplc A (syn_c1c))) (syn_cplc (syn_ctfin A) (syn_c1c)))) :=
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
  have freeVariableCertificate0 : a ∉ ((syn_cplc A (syn_c1c))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
      Finset.notMem_empty, fresh_a_not_A, or_false, not_false_eq_true]
  have p0000 := @g_n0 a (syn_cplc A (syn_c1c)) freeVariableCertificate0
  have p0001 := @g_peano2 A
  have p0002 := @g_tfincl (syn_cplc A (syn_c1c))
  have p0003 :=
    @g_syl (.classMem A (syn_cnnc)) (.classMem (syn_cplc A (syn_c1c)) (syn_cnnc))
      (.classMem (syn_ctfin (syn_cplc A (syn_c1c))) (syn_cnnc)) p0001 p0002
  have p0004 :=
    @g_adantr (.classMem A (syn_cnnc))
      (.classMem (syn_ctfin (syn_cplc A (syn_c1c))) (syn_cnnc))
      (.classMem (.cv a) (syn_cplc A (syn_c1c))) p0003
  have p0005 := @g_tfincl A
  have p0006 := @g_peano2 (syn_ctfin A)
  have p0007 :=
    @g_syl (.classMem A (syn_cnnc)) (.classMem (syn_ctfin A) (syn_cnnc))
      (.classMem (syn_cplc (syn_ctfin A) (syn_c1c)) (syn_cnnc)) p0005 p0006
  have p0008 :=
    @g_adantr (.classMem A (syn_cnnc))
      (.classMem (syn_cplc (syn_ctfin A) (syn_c1c)) (syn_cnnc))
      (.classMem (.cv a) (syn_cplc A (syn_c1c))) p0007
  have p0009 := @g_tfinpw1 (.cv a) (syn_cplc A (syn_c1c))
  have p0010 :=
    @g_sylan (.classMem A (syn_cnnc)) (.classMem (syn_cplc A (syn_c1c)) (syn_cnnc))
      (.classMem (.cv a) (syn_cplc A (syn_c1c)))
      (.classMem (syn_cpw1 (.cv a)) (syn_ctfin (syn_cplc A (syn_c1c)))) p0001 p0009
  have freeVariableCertificate1 : b ∉ ((Class.cv a)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_b_ne_a, not_false_eq_true]
  have freeVariableCertificate2 : x ∉ ((Class.cv a)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_x_ne_a, not_false_eq_true]
  have p0011 :=
    @g_elsuc x (.cv a) A b freeVariableCertificate1 freeVariableCertificate2
      (by exact (show b ∉ (A).fv from (by exact fresh_b_not_A)))
      (show b ≠ x from (by exact fresh_b_ne_x))
  have p0012 := @g_tfinpw1 (.cv b) A
  have p0013 :=
    @g_adantrr (.classMem A (syn_cnnc)) (.classMem (.cv b) A)
      (.classMem (syn_cpw1 (.cv b)) (syn_ctfin A))
      (.classMem (.cv x) (syn_ccompl (.cv b))) p0012
  have p0014 := @g_vex x
  have p0015 := @g_elcompl (.cv x) (.cv b) p0014
  have p0016 := @g_snelpw1 (.cv x) (.cv b)
  have p0017_e00_recanon :
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
      p0015
  have p0017_e01_recanon :
    Nominal.NPrf
      (syn_wb (.classMem (syn_csn (.cv x)) (syn_cpw1 (.cv b))) (.objMem x b)) :=
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
      p0016
  have p0017 :=
    @g_xchbinxr (.classMem (.cv x) (syn_ccompl (.cv b))) (.objMem x b)
      (.classMem (syn_csn (.cv x)) (syn_cpw1 (.cv b))) p0017_e00_recanon p0017_e01_recanon
  have p0018 :=
    @g_biimpi (.classMem (.cv x) (syn_ccompl (.cv b)))
      (.neg (.classMem (syn_csn (.cv x)) (syn_cpw1 (.cv b)))) p0017
  have p0019 :=
    @g_ad2antll (.classMem (.cv x) (syn_ccompl (.cv b)))
      (.neg (.classMem (syn_csn (.cv x)) (syn_cpw1 (.cv b)))) (.classMem A (syn_cnnc))
      (.classMem (.cv b) A) p0018
  have p0020 := @g_snex (.cv x)
  have p0021 := @g_elsuci (syn_cpw1 (.cv b)) (syn_ctfin A) (syn_csn (.cv x)) p0020
  have p0022 :=
    @g_syl2anc
      (syn_wa (.classMem A (syn_cnnc))
        (syn_wa (.classMem (.cv b) A) (.classMem (.cv x) (syn_ccompl (.cv b)))))
      (.classMem (syn_cpw1 (.cv b)) (syn_ctfin A))
      (.neg (.classMem (syn_csn (.cv x)) (syn_cpw1 (.cv b))))
      (.classMem (syn_cun (syn_cpw1 (.cv b)) (syn_csn (syn_csn (.cv x))))
        (syn_cplc (syn_ctfin A) (syn_c1c)))
      p0013 p0019 p0021
  have p0023 := @g_pw1eq (.cv a) (syn_cun (.cv b) (syn_csn (.cv x)))
  have p0024 := @g_pw1un (.cv b) (syn_csn (.cv x))
  have p0025 := @g_pw1sn (.cv x) p0014
  have p0026 :=
    @g_uneq2i (syn_cpw1 (syn_csn (.cv x))) (syn_csn (syn_csn (.cv x))) (syn_cpw1 (.cv b))
      p0025
  have p0027 :=
    @g_eqtri (syn_cpw1 (syn_cun (.cv b) (syn_csn (.cv x))))
      (syn_cun (syn_cpw1 (.cv b)) (syn_cpw1 (syn_csn (.cv x))))
      (syn_cun (syn_cpw1 (.cv b)) (syn_csn (syn_csn (.cv x)))) p0024 p0026
  have p0028 :=
    @g_syl6eq (.classEq (.cv a) (syn_cun (.cv b) (syn_csn (.cv x)))) (syn_cpw1 (.cv a))
      (syn_cpw1 (syn_cun (.cv b) (syn_csn (.cv x))))
      (syn_cun (syn_cpw1 (.cv b)) (syn_csn (syn_csn (.cv x)))) p0023 p0027
  have p0029 :=
    @g_eleq1d (.classEq (.cv a) (syn_cun (.cv b) (syn_csn (.cv x)))) (syn_cpw1 (.cv a))
      (syn_cun (syn_cpw1 (.cv b)) (syn_csn (syn_csn (.cv x))))
      (syn_cplc (syn_ctfin A) (syn_c1c)) p0028
  have p0030 :=
    @g_syl5ibrcom
      (syn_wa (.classMem A (syn_cnnc))
        (syn_wa (.classMem (.cv b) A) (.classMem (.cv x) (syn_ccompl (.cv b)))))
      (.classMem (syn_cpw1 (.cv a)) (syn_cplc (syn_ctfin A) (syn_c1c)))
      (.classEq (.cv a) (syn_cun (.cv b) (syn_csn (.cv x))))
      (.classMem (syn_cun (syn_cpw1 (.cv b)) (syn_csn (syn_csn (.cv x))))
        (syn_cplc (syn_ctfin A) (syn_c1c)))
      p0022 p0029
  have freeVariableCertificate3 :
    b ∉ ((Wff.classMem (syn_cpw1 (.cv a)) (syn_cplc (syn_ctfin A) (syn_c1c)))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_b_ne_a, fresh_b_not_A, or_false,
      not_false_eq_true]
  have freeVariableCertificate4 :
    x ∉ ((Wff.classMem (syn_cpw1 (.cv a)) (syn_cplc (syn_ctfin A) (syn_c1c)))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_x_ne_a, fresh_x_not_A, or_false,
      not_false_eq_true]
  have freeVariableCertificate5 : b ∉ ((Wff.classMem A (syn_cnnc))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union,
      Finset.notMem_empty, fresh_b_not_A, or_false, not_false_eq_true]
  have freeVariableCertificate6 : x ∉ ((Wff.classMem A (syn_cnnc))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union,
      Finset.notMem_empty, fresh_x_not_A, or_false, not_false_eq_true]
  have p0031 :=
    @g_rexlimdvva (.classMem A (syn_cnnc))
      (.classEq (.cv a) (syn_cun (.cv b) (syn_csn (.cv x))))
      (.classMem (syn_cpw1 (.cv a)) (syn_cplc (syn_ctfin A) (syn_c1c))) b x A
      (syn_ccompl (.cv b)) (by exact (show x ∉ (A).fv from (by exact fresh_x_not_A)))
      freeVariableCertificate3 freeVariableCertificate4 freeVariableCertificate5
      freeVariableCertificate6 (show b ≠ x from (by exact fresh_b_ne_x)) p0030
  have p0032 :=
    @g_syl5bi (.classMem (.cv a) (syn_cplc A (syn_c1c)))
      (syn_wrex b A (syn_wrex x (syn_ccompl (.cv b))
          (.classEq (.cv a) (syn_cun (.cv b) (syn_csn (.cv x))))))
      (.classMem A (syn_cnnc))
      (.classMem (syn_cpw1 (.cv a)) (syn_cplc (syn_ctfin A) (syn_c1c))) p0011 p0031
  have p0033 :=
    @g_imp (.classMem A (syn_cnnc)) (.classMem (.cv a) (syn_cplc A (syn_c1c)))
      (.classMem (syn_cpw1 (.cv a)) (syn_cplc (syn_ctfin A) (syn_c1c))) p0032
  have p0034 :=
    @g_nnceleq (syn_cpw1 (.cv a)) (syn_ctfin (syn_cplc A (syn_c1c)))
      (syn_cplc (syn_ctfin A) (syn_c1c))
  have p0035 :=
    @g_syl22anc
      (syn_wa (.classMem A (syn_cnnc)) (.classMem (.cv a) (syn_cplc A (syn_c1c))))
      (.classMem (syn_ctfin (syn_cplc A (syn_c1c))) (syn_cnnc))
      (.classMem (syn_cplc (syn_ctfin A) (syn_c1c)) (syn_cnnc))
      (.classMem (syn_cpw1 (.cv a)) (syn_ctfin (syn_cplc A (syn_c1c))))
      (.classMem (syn_cpw1 (.cv a)) (syn_cplc (syn_ctfin A) (syn_c1c)))
      (.classEq (syn_ctfin (syn_cplc A (syn_c1c))) (syn_cplc (syn_ctfin A) (syn_c1c)))
      p0004 p0008 p0010 p0033 p0034
  have p0036 :=
    @g_ex (.classMem A (syn_cnnc)) (.classMem (.cv a) (syn_cplc A (syn_c1c)))
      (.classEq (syn_ctfin (syn_cplc A (syn_c1c))) (syn_cplc (syn_ctfin A) (syn_c1c)))
      p0035
  have freeVariableCertificate7 :
    a ∉
      ((Wff.classEq (syn_ctfin (syn_cplc A (syn_c1c)))
          (syn_cplc (syn_ctfin A) (syn_c1c)))).fv :=
    by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
      Finset.notMem_empty, fresh_a_not_A, or_false, not_false_eq_true]
  have freeVariableCertificate8 : a ∉ ((Wff.classMem A (syn_cnnc))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union,
      Finset.notMem_empty, fresh_a_not_A, or_false, not_false_eq_true]
  have p0037 :=
    @g_exlimdv (.classMem A (syn_cnnc)) (.classMem (.cv a) (syn_cplc A (syn_c1c)))
      (.classEq (syn_ctfin (syn_cplc A (syn_c1c))) (syn_cplc (syn_ctfin A) (syn_c1c))) a
      freeVariableCertificate7 freeVariableCertificate8 p0036
  have p0038 :=
    @g_syl5bi (syn_wne (syn_cplc A (syn_c1c)) (syn_c0))
      (syn_wex a (.classMem (.cv a) (syn_cplc A (syn_c1c)))) (.classMem A (syn_cnnc))
      (.classEq (syn_ctfin (syn_cplc A (syn_c1c))) (syn_cplc (syn_ctfin A) (syn_c1c)))
      p0000 p0037
  have p0039 :=
    @g_imp (.classMem A (syn_cnnc)) (syn_wne (syn_cplc A (syn_c1c)) (syn_c0))
      (.classEq (syn_ctfin (syn_cplc A (syn_c1c))) (syn_cplc (syn_ctfin A) (syn_c1c)))
      p0038
  exact p0039

@[expose]
noncomputable def g_tfin1c : Nominal.NPrf (.classEq (syn_ctfin (syn_c1c)) (syn_c1c)) :=
  by
  have p0000 := @g_peano1
  have p0001 := @g_addcid2 (syn_c1c)
  have p0002 := @g_n_1cex
  have p0003 := @g_snel1c (syn_c1c) p0002
  have p0004 := @g_ne0i (syn_c1c) (syn_csn (syn_c1c))
  have p0005 := Nominal.mp p0003 p0004
  have p0006 := @g_eqnetri (syn_cplc (syn_c0c) (syn_c1c)) (syn_c1c) (syn_c0) p0001 p0005
  have p0007 := @g_tfinsuc (syn_c0c)
  have p0008 :=
    @g_mp2an (.classMem (syn_c0c) (syn_cnnc))
      (syn_wne (syn_cplc (syn_c0c) (syn_c1c)) (syn_c0))
      (.classEq (syn_ctfin (syn_cplc (syn_c0c) (syn_c1c)))
        (syn_cplc (syn_ctfin (syn_c0c)) (syn_c1c)))
      p0000 p0006 p0007
  have p0009 := @g_tfineq (syn_cplc (syn_c0c) (syn_c1c)) (syn_c1c)
  have p0010 := Nominal.mp p0001 p0009
  have p0011 := @g_tfin0c
  have p0012 := @g_addceq1i (syn_ctfin (syn_c0c)) (syn_c0c) (syn_c1c) p0011
  have p0013 :=
    @g_eqtri (syn_cplc (syn_ctfin (syn_c0c)) (syn_c1c)) (syn_cplc (syn_c0c) (syn_c1c))
      (syn_c1c) p0012 p0001
  have p0014 :=
    @g_n_3eqtr3i (syn_ctfin (syn_cplc (syn_c0c) (syn_c1c)))
      (syn_cplc (syn_ctfin (syn_c0c)) (syn_c1c)) (syn_ctfin (syn_c1c)) (syn_c1c) p0008
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

@[expose]
noncomputable def g_tfinltfinlem1 (M : Class) (N : Class) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)))
        (.imp (.classMem (syn_copk M N) (syn_cltfin))
          (.classMem (syn_copk (syn_ctfin M) (syn_ctfin N)) (syn_cltfin)))) :=
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
  have p0000 := @g_tfinnnul M
  have p0001 :=
    @g_ex (.classMem M (syn_cnnc)) (syn_wne M (syn_c0)) (syn_wne (syn_ctfin M) (syn_c0))
      p0000
  have p0002 :=
    @g_adantrd (.classMem M (syn_cnnc)) (syn_wne M (syn_c0))
      (syn_wne (syn_ctfin M) (syn_c0))
      (syn_wrex x (syn_cnnc) (.classEq N (syn_cplc (syn_cplc M (.cv x)) (syn_c1c)))) p0001
  have p0003 :=
    @g_adantr (.classMem M (syn_cnnc))
      (.imp (syn_wa (syn_wne M (syn_c0))
          (syn_wrex x (syn_cnnc) (.classEq N (syn_cplc (syn_cplc M (.cv x)) (syn_c1c)))))
        (syn_wne (syn_ctfin M) (syn_c0)))
      (.classMem N (syn_cnnc)) p0002
  have p0004 := @g_addcnul1 (syn_c1c)
  have p0005 := @g_addccom (syn_c1c) (syn_c0)
  have p0006 :=
    @g_eqtr3i (syn_cplc (syn_c1c) (syn_c0)) (syn_c0) (syn_cplc (syn_c0) (syn_c1c)) p0004
      p0005
  have p0007 := @g_addceq2 (.cv y) (syn_c0) (syn_ctfin M)
  have p0008 := @g_addcnul1 (syn_ctfin M)
  have p0009 :=
    @g_syl6eq (.classEq (.cv y) (syn_c0)) (syn_cplc (syn_ctfin M) (.cv y))
      (syn_cplc (syn_ctfin M) (syn_c0)) (syn_c0) p0007 p0008
  have p0010 :=
    @g_addceq1d (.classEq (.cv y) (syn_c0)) (syn_cplc (syn_ctfin M) (.cv y)) (syn_c0)
      (syn_c1c) p0009
  have p0011 :=
    @g_eqeq2d (.classEq (.cv y) (syn_c0))
      (syn_cplc (syn_cplc (syn_ctfin M) (.cv y)) (syn_c1c)) (syn_cplc (syn_c0) (syn_c1c))
      (syn_c0) p0010
  have freeVariableCertificate0 :
    y ∉ ((Wff.classEq (syn_c0) (syn_cplc (syn_c0) (syn_c1c)))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
      Finset.notMem_empty, or_false, not_false_eq_true]
  have p0012 :=
    @g_rspcev (.classEq (syn_c0) (syn_cplc (syn_cplc (syn_ctfin M) (.cv y)) (syn_c1c)))
      (.classEq (syn_c0) (syn_cplc (syn_c0) (syn_c1c))) y (syn_c0) (syn_cnnc)
      (by
        exact
          (show y ∉ ((syn_c0)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0];
              exact (show y ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
      (by
        exact
          (show y ∉ ((syn_cnnc)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc];
              exact (show y ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
      freeVariableCertificate0 p0011
  have p0013 :=
    @g_mpan2 (.classMem (syn_c0) (syn_cnnc))
      (.classEq (syn_c0) (syn_cplc (syn_c0) (syn_c1c)))
      (syn_wrex y (syn_cnnc)
        (.classEq (syn_c0) (syn_cplc (syn_cplc (syn_ctfin M) (.cv y)) (syn_c1c))))
      p0006 p0012
  have p0014 := @g_eleq1 N (syn_c0) (syn_cnnc)
  have p0015 := @g_tfineq N (syn_c0)
  have p0016 := @g_tfinnul
  have p0017 :=
    @g_syl6eq (.classEq N (syn_c0)) (syn_ctfin N) (syn_ctfin (syn_c0)) (syn_c0) p0015
      p0016
  have p0018 :=
    @g_eqeq1d (.classEq N (syn_c0)) (syn_ctfin N) (syn_c0)
      (syn_cplc (syn_cplc (syn_ctfin M) (.cv y)) (syn_c1c)) p0017
  have freeVariableCertificate1 : y ∉ ((Wff.classEq N (syn_c0))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union,
      Finset.notMem_empty, fresh_y_not_N, or_false, not_false_eq_true]
  have p0019 :=
    @g_rexbidv (.classEq N (syn_c0))
      (.classEq (syn_ctfin N) (syn_cplc (syn_cplc (syn_ctfin M) (.cv y)) (syn_c1c)))
      (.classEq (syn_c0) (syn_cplc (syn_cplc (syn_ctfin M) (.cv y)) (syn_c1c))) y
      (syn_cnnc) freeVariableCertificate1 p0018
  have p0020 :=
    @g_imbi12d (.classEq N (syn_c0)) (.classMem N (syn_cnnc))
      (.classMem (syn_c0) (syn_cnnc))
      (syn_wrex y (syn_cnnc)
        (.classEq (syn_ctfin N) (syn_cplc (syn_cplc (syn_ctfin M) (.cv y)) (syn_c1c))))
      (syn_wrex y (syn_cnnc)
        (.classEq (syn_c0) (syn_cplc (syn_cplc (syn_ctfin M) (.cv y)) (syn_c1c))))
      p0014 p0019
  have p0021 :=
    @g_mpbiri (.classEq N (syn_c0))
      (.imp (.classMem N (syn_cnnc)) (syn_wrex y (syn_cnnc)
          (.classEq (syn_ctfin N) (syn_cplc (syn_cplc (syn_ctfin M) (.cv y)) (syn_c1c)))))
      (.imp (.classMem (syn_c0) (syn_cnnc)) (syn_wrex y (syn_cnnc)
          (.classEq (syn_c0) (syn_cplc (syn_cplc (syn_ctfin M) (.cv y)) (syn_c1c)))))
      p0013 p0020
  have p0022 :=
    @g_adantld (.classEq N (syn_c0)) (.classMem N (syn_cnnc))
      (syn_wrex y (syn_cnnc)
        (.classEq (syn_ctfin N) (syn_cplc (syn_cplc (syn_ctfin M) (.cv y)) (syn_c1c))))
      (.classMem M (syn_cnnc)) p0021
  have p0023 :=
    @g_adantrd (.classEq N (syn_c0))
      (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)))
      (syn_wrex y (syn_cnnc)
        (.classEq (syn_ctfin N) (syn_cplc (syn_cplc (syn_ctfin M) (.cv y)) (syn_c1c))))
      (syn_wa (syn_wne M (syn_c0)) (.classMem (.cv x) (syn_cnnc))) p0022
  have p0024 :=
    @g_a1dd (.classEq N (syn_c0))
      (syn_wa (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)))
        (syn_wa (syn_wne M (syn_c0)) (.classMem (.cv x) (syn_cnnc))))
      (syn_wrex y (syn_cnnc)
        (.classEq (syn_ctfin N) (syn_cplc (syn_cplc (syn_ctfin M) (.cv y)) (syn_c1c))))
      (.classEq N (syn_cplc (syn_cplc M (.cv x)) (syn_c1c))) p0023
  have p0025 :=
    @g_simp2r (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)))
      (syn_wne M (syn_c0)) (.classMem (.cv x) (syn_cnnc))
      (syn_wa (syn_wne N (syn_c0)) (.classEq N (syn_cplc (syn_cplc M (.cv x)) (syn_c1c))))
  have p0026 :=
    @g_simp3r (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)))
      (syn_wa (syn_wne M (syn_c0)) (.classMem (.cv x) (syn_cnnc))) (syn_wne N (syn_c0))
      (.classEq N (syn_cplc (syn_cplc M (.cv x)) (syn_c1c)))
  have p0027 :=
    @g_simp3l (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)))
      (syn_wa (syn_wne M (syn_c0)) (.classMem (.cv x) (syn_cnnc))) (syn_wne N (syn_c0))
      (.classEq N (syn_cplc (syn_cplc M (.cv x)) (syn_c1c)))
  have p0028 :=
    @g_eqnetrrd
      (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)))
        (syn_wa (syn_wne M (syn_c0)) (.classMem (.cv x) (syn_cnnc)))
        (syn_wa (syn_wne N (syn_c0)) (.classEq N (syn_cplc (syn_cplc M (.cv x)) (syn_c1c)))))
      N (syn_cplc (syn_cplc M (.cv x)) (syn_c1c)) (syn_c0) p0026 p0027
  have p0029 := @g_addcnnul (syn_cplc M (.cv x)) (syn_c1c)
  have p0030 :=
    @g_syl
      (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)))
        (syn_wa (syn_wne M (syn_c0)) (.classMem (.cv x) (syn_cnnc)))
        (syn_wa (syn_wne N (syn_c0)) (.classEq N (syn_cplc (syn_cplc M (.cv x)) (syn_c1c)))))
      (syn_wne (syn_cplc (syn_cplc M (.cv x)) (syn_c1c)) (syn_c0))
      (syn_wa (syn_wne (syn_cplc M (.cv x)) (syn_c0)) (syn_wne (syn_c1c) (syn_c0))) p0028
      p0029
  have p0031 :=
    @g_simpld
      (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)))
        (syn_wa (syn_wne M (syn_c0)) (.classMem (.cv x) (syn_cnnc)))
        (syn_wa (syn_wne N (syn_c0)) (.classEq N (syn_cplc (syn_cplc M (.cv x)) (syn_c1c)))))
      (syn_wne (syn_cplc M (.cv x)) (syn_c0)) (syn_wne (syn_c1c) (syn_c0)) p0030
  have p0032 := @g_addcnnul M (.cv x)
  have p0033 :=
    @g_syl
      (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)))
        (syn_wa (syn_wne M (syn_c0)) (.classMem (.cv x) (syn_cnnc)))
        (syn_wa (syn_wne N (syn_c0)) (.classEq N (syn_cplc (syn_cplc M (.cv x)) (syn_c1c)))))
      (syn_wne (syn_cplc M (.cv x)) (syn_c0))
      (syn_wa (syn_wne M (syn_c0)) (syn_wne (.cv x) (syn_c0))) p0031 p0032
  have p0034 :=
    @g_simprd
      (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)))
        (syn_wa (syn_wne M (syn_c0)) (.classMem (.cv x) (syn_cnnc)))
        (syn_wa (syn_wne N (syn_c0)) (.classEq N (syn_cplc (syn_cplc M (.cv x)) (syn_c1c)))))
      (syn_wne M (syn_c0)) (syn_wne (.cv x) (syn_c0)) p0033
  have freeVariableCertificate2 : y ∉ ((Class.cv x)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_y_ne_x, not_false_eq_true]
  have p0035 := @g_tfinprop (.cv x) y freeVariableCertificate2
  have p0036 :=
    @g_simpld (syn_wa (.classMem (.cv x) (syn_cnnc)) (syn_wne (.cv x) (syn_c0)))
      (.classMem (syn_ctfin (.cv x)) (syn_cnnc))
      (syn_wrex y (.cv x) (.classMem (syn_cpw1 (.cv y)) (syn_ctfin (.cv x)))) p0035
  have p0037 :=
    @g_syl2anc
      (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)))
        (syn_wa (syn_wne M (syn_c0)) (.classMem (.cv x) (syn_cnnc)))
        (syn_wa (syn_wne N (syn_c0)) (.classEq N (syn_cplc (syn_cplc M (.cv x)) (syn_c1c)))))
      (.classMem (.cv x) (syn_cnnc)) (syn_wne (.cv x) (syn_c0))
      (.classMem (syn_ctfin (.cv x)) (syn_cnnc)) p0025 p0034 p0036
  have p0038 := @g_tfineq N (syn_cplc (syn_cplc M (.cv x)) (syn_c1c))
  have p0039 :=
    @g_adantl (.classEq N (syn_cplc (syn_cplc M (.cv x)) (syn_c1c)))
      (.classEq (syn_ctfin N) (syn_ctfin (syn_cplc (syn_cplc M (.cv x)) (syn_c1c))))
      (syn_wne N (syn_c0)) p0038
  have p0040 :=
    @g_n_3ad2ant3
      (syn_wa (syn_wne N (syn_c0)) (.classEq N (syn_cplc (syn_cplc M (.cv x)) (syn_c1c))))
      (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)))
      (.classEq (syn_ctfin N) (syn_ctfin (syn_cplc (syn_cplc M (.cv x)) (syn_c1c))))
      (syn_wa (syn_wne M (syn_c0)) (.classMem (.cv x) (syn_cnnc))) p0039
  have p0041 :=
    @g_simp1l (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))
      (syn_wa (syn_wne M (syn_c0)) (.classMem (.cv x) (syn_cnnc)))
      (syn_wa (syn_wne N (syn_c0)) (.classEq N (syn_cplc (syn_cplc M (.cv x)) (syn_c1c))))
  have p0042 := @g_nncaddccl M (.cv x)
  have p0043 :=
    @g_syl2anc
      (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)))
        (syn_wa (syn_wne M (syn_c0)) (.classMem (.cv x) (syn_cnnc)))
        (syn_wa (syn_wne N (syn_c0)) (.classEq N (syn_cplc (syn_cplc M (.cv x)) (syn_c1c)))))
      (.classMem M (syn_cnnc)) (.classMem (.cv x) (syn_cnnc))
      (.classMem (syn_cplc M (.cv x)) (syn_cnnc)) p0041 p0025 p0042
  have p0044 := @g_tfinsuc (syn_cplc M (.cv x))
  have p0045 :=
    @g_syl2anc
      (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)))
        (syn_wa (syn_wne M (syn_c0)) (.classMem (.cv x) (syn_cnnc)))
        (syn_wa (syn_wne N (syn_c0)) (.classEq N (syn_cplc (syn_cplc M (.cv x)) (syn_c1c)))))
      (.classMem (syn_cplc M (.cv x)) (syn_cnnc))
      (syn_wne (syn_cplc (syn_cplc M (.cv x)) (syn_c1c)) (syn_c0))
      (.classEq (syn_ctfin (syn_cplc (syn_cplc M (.cv x)) (syn_c1c)))
        (syn_cplc (syn_ctfin (syn_cplc M (.cv x))) (syn_c1c)))
      p0043 p0028 p0044
  have p0046 :=
    @g_eqtrd
      (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)))
        (syn_wa (syn_wne M (syn_c0)) (.classMem (.cv x) (syn_cnnc)))
        (syn_wa (syn_wne N (syn_c0)) (.classEq N (syn_cplc (syn_cplc M (.cv x)) (syn_c1c)))))
      (syn_ctfin N) (syn_ctfin (syn_cplc (syn_cplc M (.cv x)) (syn_c1c)))
      (syn_cplc (syn_ctfin (syn_cplc M (.cv x))) (syn_c1c)) p0040 p0045
  have p0047 := @g_tfindi M (.cv x)
  have p0048 :=
    @g_syl3anc
      (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)))
        (syn_wa (syn_wne M (syn_c0)) (.classMem (.cv x) (syn_cnnc)))
        (syn_wa (syn_wne N (syn_c0)) (.classEq N (syn_cplc (syn_cplc M (.cv x)) (syn_c1c)))))
      (.classMem M (syn_cnnc)) (.classMem (.cv x) (syn_cnnc))
      (syn_wne (syn_cplc M (.cv x)) (syn_c0))
      (.classEq (syn_ctfin (syn_cplc M (.cv x))) (syn_cplc (syn_ctfin M) (syn_ctfin (.cv x))))
      p0041 p0025 p0031 p0047
  have p0049 :=
    @g_addceq1d
      (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)))
        (syn_wa (syn_wne M (syn_c0)) (.classMem (.cv x) (syn_cnnc)))
        (syn_wa (syn_wne N (syn_c0)) (.classEq N (syn_cplc (syn_cplc M (.cv x)) (syn_c1c)))))
      (syn_ctfin (syn_cplc M (.cv x))) (syn_cplc (syn_ctfin M) (syn_ctfin (.cv x)))
      (syn_c1c) p0048
  have p0050 :=
    @g_eqtrd
      (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)))
        (syn_wa (syn_wne M (syn_c0)) (.classMem (.cv x) (syn_cnnc)))
        (syn_wa (syn_wne N (syn_c0)) (.classEq N (syn_cplc (syn_cplc M (.cv x)) (syn_c1c)))))
      (syn_ctfin N) (syn_cplc (syn_ctfin (syn_cplc M (.cv x))) (syn_c1c))
      (syn_cplc (syn_cplc (syn_ctfin M) (syn_ctfin (.cv x))) (syn_c1c)) p0046 p0049
  have p0051 := @g_addceq2 (.cv y) (syn_ctfin (.cv x)) (syn_ctfin M)
  have p0052 :=
    @g_addceq1d (.classEq (.cv y) (syn_ctfin (.cv x))) (syn_cplc (syn_ctfin M) (.cv y))
      (syn_cplc (syn_ctfin M) (syn_ctfin (.cv x))) (syn_c1c) p0051
  have p0053 :=
    @g_eqeq2d (.classEq (.cv y) (syn_ctfin (.cv x)))
      (syn_cplc (syn_cplc (syn_ctfin M) (.cv y)) (syn_c1c))
      (syn_cplc (syn_cplc (syn_ctfin M) (syn_ctfin (.cv x))) (syn_c1c)) (syn_ctfin N)
      p0052
  have freeVariableCertificate3 : y ∉ ((syn_ctfin (.cv x))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_y_ne_x,
      not_false_eq_true]
  have freeVariableCertificate4 :
    y ∉
      ((Wff.classEq (syn_ctfin N)
          (syn_cplc (syn_cplc (syn_ctfin M) (syn_ctfin (.cv x))) (syn_c1c)))).fv :=
    by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_y_not_N, fresh_y_not_M,
      fresh_y_ne_x, or_false, not_false_eq_true]
  have p0054 :=
    @g_rspcev
      (.classEq (syn_ctfin N) (syn_cplc (syn_cplc (syn_ctfin M) (.cv y)) (syn_c1c)))
      (.classEq (syn_ctfin N) (syn_cplc (syn_cplc (syn_ctfin M) (syn_ctfin (.cv x))) (syn_c1c)))
      y (syn_ctfin (.cv x)) (syn_cnnc) freeVariableCertificate3
      (by
        exact
          (show y ∉ ((syn_cnnc)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc];
              exact (show y ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
      freeVariableCertificate4 p0053
  have p0055 :=
    @g_syl2anc
      (syn_w3a (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)))
        (syn_wa (syn_wne M (syn_c0)) (.classMem (.cv x) (syn_cnnc)))
        (syn_wa (syn_wne N (syn_c0)) (.classEq N (syn_cplc (syn_cplc M (.cv x)) (syn_c1c)))))
      (.classMem (syn_ctfin (.cv x)) (syn_cnnc))
      (.classEq (syn_ctfin N) (syn_cplc (syn_cplc (syn_ctfin M) (syn_ctfin (.cv x))) (syn_c1c)))
      (syn_wrex y (syn_cnnc)
        (.classEq (syn_ctfin N) (syn_cplc (syn_cplc (syn_ctfin M) (.cv y)) (syn_c1c))))
      p0037 p0050 p0054
  have p0056 :=
    @g_n_3expa (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)))
      (syn_wa (syn_wne M (syn_c0)) (.classMem (.cv x) (syn_cnnc)))
      (syn_wa (syn_wne N (syn_c0)) (.classEq N (syn_cplc (syn_cplc M (.cv x)) (syn_c1c))))
      (syn_wrex y (syn_cnnc)
        (.classEq (syn_ctfin N) (syn_cplc (syn_cplc (syn_ctfin M) (.cv y)) (syn_c1c))))
      p0055
  have p0057 :=
    @g_exp32
      (syn_wa (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)))
        (syn_wa (syn_wne M (syn_c0)) (.classMem (.cv x) (syn_cnnc))))
      (syn_wne N (syn_c0)) (.classEq N (syn_cplc (syn_cplc M (.cv x)) (syn_c1c)))
      (syn_wrex y (syn_cnnc)
        (.classEq (syn_ctfin N) (syn_cplc (syn_cplc (syn_ctfin M) (.cv y)) (syn_c1c))))
      p0056
  have p0058 :=
    @g_com12
      (syn_wa (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)))
        (syn_wa (syn_wne M (syn_c0)) (.classMem (.cv x) (syn_cnnc))))
      (syn_wne N (syn_c0))
      (.imp (.classEq N (syn_cplc (syn_cplc M (.cv x)) (syn_c1c))) (syn_wrex y (syn_cnnc)
          (.classEq (syn_ctfin N) (syn_cplc (syn_cplc (syn_ctfin M) (.cv y)) (syn_c1c)))))
      p0057
  have p0059 :=
    @g_pm2_61ine
      (.imp (syn_wa (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)))
          (syn_wa (syn_wne M (syn_c0)) (.classMem (.cv x) (syn_cnnc))))
        (.imp (.classEq N (syn_cplc (syn_cplc M (.cv x)) (syn_c1c))) (syn_wrex y (syn_cnnc)
            (.classEq (syn_ctfin N) (syn_cplc (syn_cplc (syn_ctfin M) (.cv y)) (syn_c1c))))))
      N (syn_c0) p0024 p0058
  have p0060 :=
    @g_expr (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)))
      (syn_wne M (syn_c0)) (.classMem (.cv x) (syn_cnnc))
      (.imp (.classEq N (syn_cplc (syn_cplc M (.cv x)) (syn_c1c))) (syn_wrex y (syn_cnnc)
          (.classEq (syn_ctfin N) (syn_cplc (syn_cplc (syn_ctfin M) (.cv y)) (syn_c1c)))))
      p0059
  have freeVariableCertificate5 :
    x ∉
      ((syn_wrex y (syn_cnnc) (.classEq (syn_ctfin N)
            (syn_cplc (syn_cplc (syn_ctfin M) (.cv y)) (syn_c1c))))).fv :=
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
      ((syn_wa (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)))
          (syn_wne M (syn_c0)))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union,
      Finset.notMem_empty, fresh_x_not_M, fresh_x_not_N, or_false, not_false_eq_true]
  have p0061 :=
    @g_rexlimdv
      (syn_wa (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))) (syn_wne M (syn_c0)))
      (.classEq N (syn_cplc (syn_cplc M (.cv x)) (syn_c1c)))
      (syn_wrex y (syn_cnnc)
        (.classEq (syn_ctfin N) (syn_cplc (syn_cplc (syn_ctfin M) (.cv y)) (syn_c1c))))
      x (syn_cnnc) freeVariableCertificate5 freeVariableCertificate6 p0060
  have p0062 :=
    @g_ex (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))) (syn_wne M (syn_c0))
      (.imp (syn_wrex x (syn_cnnc) (.classEq N (syn_cplc (syn_cplc M (.cv x)) (syn_c1c))))
        (syn_wrex y (syn_cnnc)
          (.classEq (syn_ctfin N) (syn_cplc (syn_cplc (syn_ctfin M) (.cv y)) (syn_c1c)))))
      p0061
  have p0063 :=
    @g_imp3a (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)))
      (syn_wne M (syn_c0))
      (syn_wrex x (syn_cnnc) (.classEq N (syn_cplc (syn_cplc M (.cv x)) (syn_c1c))))
      (syn_wrex y (syn_cnnc)
        (.classEq (syn_ctfin N) (syn_cplc (syn_cplc (syn_ctfin M) (.cv y)) (syn_c1c))))
      p0062
  have p0064 :=
    @g_jcad (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)))
      (syn_wa (syn_wne M (syn_c0))
        (syn_wrex x (syn_cnnc) (.classEq N (syn_cplc (syn_cplc M (.cv x)) (syn_c1c)))))
      (syn_wne (syn_ctfin M) (syn_c0))
      (syn_wrex y (syn_cnnc)
        (.classEq (syn_ctfin N) (syn_cplc (syn_cplc (syn_ctfin M) (.cv y)) (syn_c1c))))
      p0003 p0063
  have p0065 :=
    @g_opkltfing x M N (syn_cnnc) (syn_cnnc)
      (by exact (show x ∉ (M).fv from (by exact fresh_x_not_M)))
      (by exact (show x ∉ (N).fv from (by exact fresh_x_not_N)))
  have p0066 := @g_tfinex M
  have p0067 := @g_tfinex N
  have p0068 :=
    @g_opkltfing y (syn_ctfin M) (syn_ctfin N) (syn_cvv) (syn_cvv)
      (by
        exact
          (show y ∉ ((syn_ctfin M)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin];
              exact (show y ∉ (M).fv from (by exact fresh_y_not_M)))))
      (by
        exact
          (show y ∉ ((syn_ctfin N)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin];
              exact (show y ∉ (N).fv from (by exact fresh_y_not_N)))))
  have p0069 :=
    @g_mp2an (.classMem (syn_ctfin M) (syn_cvv)) (.classMem (syn_ctfin N) (syn_cvv))
      (syn_wb (.classMem (syn_copk (syn_ctfin M) (syn_ctfin N)) (syn_cltfin))
        (syn_wa (syn_wne (syn_ctfin M) (syn_c0)) (syn_wrex y (syn_cnnc) (.classEq (syn_ctfin N)
              (syn_cplc (syn_cplc (syn_ctfin M) (.cv y)) (syn_c1c))))))
      p0066 p0067 p0068
  have p0070 :=
    @g_a1i
      (syn_wb (.classMem (syn_copk (syn_ctfin M) (syn_ctfin N)) (syn_cltfin))
        (syn_wa (syn_wne (syn_ctfin M) (syn_c0)) (syn_wrex y (syn_cnnc) (.classEq (syn_ctfin N)
              (syn_cplc (syn_cplc (syn_ctfin M) (.cv y)) (syn_c1c))))))
      (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))) p0069
  have p0071 :=
    @g_n_3imtr4d (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)))
      (syn_wa (syn_wne M (syn_c0))
        (syn_wrex x (syn_cnnc) (.classEq N (syn_cplc (syn_cplc M (.cv x)) (syn_c1c)))))
      (syn_wa (syn_wne (syn_ctfin M) (syn_c0)) (syn_wrex y (syn_cnnc)
          (.classEq (syn_ctfin N) (syn_cplc (syn_cplc (syn_ctfin M) (.cv y)) (syn_c1c)))))
      (.classMem (syn_copk M N) (syn_cltfin))
      (.classMem (syn_copk (syn_ctfin M) (syn_ctfin N)) (syn_cltfin)) p0064 p0065 p0070
  exact p0071

@[expose]
noncomputable def g_tfinltfin (M : Class) (N : Class) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)))
        (syn_wb (.classMem (syn_copk M N) (syn_cltfin))
          (.classMem (syn_copk (syn_ctfin M) (syn_ctfin N)) (syn_cltfin)))) :=
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
  have p0000 := @g_tfinltfinlem1 M N
  have p0001 := @g_tfineq M (syn_c0)
  have p0002 := @g_tfinnul
  have p0003 :=
    @g_syl6eq (.classEq M (syn_c0)) (syn_ctfin M) (syn_ctfin (syn_c0)) (syn_c0) p0001
      p0002
  have p0004 := (Nominal.biimpRefl (syn_wne (syn_ctfin M) (syn_c0)))
  have p0005 :=
    @g_con2bii (syn_wne (syn_ctfin M) (syn_c0)) (.classEq (syn_ctfin M) (syn_c0)) p0004
  have p0006 :=
    @g_sylib (.classEq M (syn_c0)) (.classEq (syn_ctfin M) (syn_c0))
      (.neg (syn_wne (syn_ctfin M) (syn_c0))) p0003 p0005
  have p0007 :=
    @g_intnanrd (.classEq M (syn_c0)) (syn_wne (syn_ctfin M) (syn_c0))
      (syn_wrex x (syn_cnnc)
        (.classEq (syn_ctfin N) (syn_cplc (syn_cplc (syn_ctfin M) (.cv x)) (syn_c1c))))
      p0006
  have p0008 := @g_tfinex M
  have p0009 := @g_tfinex N
  have p0010 :=
    @g_opkltfing x (syn_ctfin M) (syn_ctfin N) (syn_cvv) (syn_cvv)
      (by
        exact
          (show x ∉ ((syn_ctfin M)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin];
              exact (show x ∉ (M).fv from (by exact fresh_x_not_M)))))
      (by
        exact
          (show x ∉ ((syn_ctfin N)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin];
              exact (show x ∉ (N).fv from (by exact fresh_x_not_N)))))
  have p0011 :=
    @g_mp2an (.classMem (syn_ctfin M) (syn_cvv)) (.classMem (syn_ctfin N) (syn_cvv))
      (syn_wb (.classMem (syn_copk (syn_ctfin M) (syn_ctfin N)) (syn_cltfin))
        (syn_wa (syn_wne (syn_ctfin M) (syn_c0)) (syn_wrex x (syn_cnnc) (.classEq (syn_ctfin N)
              (syn_cplc (syn_cplc (syn_ctfin M) (.cv x)) (syn_c1c))))))
      p0008 p0009 p0010
  have p0012 :=
    @g_sylnibr (.classEq M (syn_c0))
      (syn_wa (syn_wne (syn_ctfin M) (syn_c0)) (syn_wrex x (syn_cnnc)
          (.classEq (syn_ctfin N) (syn_cplc (syn_cplc (syn_ctfin M) (.cv x)) (syn_c1c)))))
      (.classMem (syn_copk (syn_ctfin M) (syn_ctfin N)) (syn_cltfin)) p0007 p0011
  have p0013 :=
    @g_pm2_21d (.classEq M (syn_c0))
      (.classMem (syn_copk (syn_ctfin M) (syn_ctfin N)) (syn_cltfin))
      (.classMem (syn_copk M N) (syn_cltfin)) p0012
  have p0014 :=
    @g_a1d (.classEq M (syn_c0))
      (.imp (.classMem (syn_copk (syn_ctfin M) (syn_ctfin N)) (syn_cltfin))
        (.classMem (syn_copk M N) (syn_cltfin)))
      (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))) p0013
  have p0015 := @g_tfinprop M y (by exact (show y ∉ (M).fv from (by exact fresh_y_not_M)))
  have p0016 :=
    @g_simpld (syn_wa (.classMem M (syn_cnnc)) (syn_wne M (syn_c0)))
      (.classMem (syn_ctfin M) (syn_cnnc))
      (syn_wrex y M (.classMem (syn_cpw1 (.cv y)) (syn_ctfin M))) p0015
  have p0017 := @g_ltfinirr (syn_ctfin M)
  have p0018 :=
    @g_syl (syn_wa (.classMem M (syn_cnnc)) (syn_wne M (syn_c0)))
      (.classMem (syn_ctfin M) (syn_cnnc))
      (.neg (.classMem (syn_copk (syn_ctfin M) (syn_ctfin M)) (syn_cltfin))) p0016 p0017
  have p0019 :=
    @g_n_3adant2 (.classMem M (syn_cnnc)) (syn_wne M (syn_c0))
      (.neg (.classMem (syn_copk (syn_ctfin M) (syn_ctfin M)) (syn_cltfin)))
      (.classMem N (syn_cnnc)) p0018
  have p0020 := @g_opkeq2 (syn_ctfin M) (syn_ctfin N) (syn_ctfin M)
  have p0021 :=
    @g_eleq1d (.classEq (syn_ctfin M) (syn_ctfin N))
      (syn_copk (syn_ctfin M) (syn_ctfin M)) (syn_copk (syn_ctfin M) (syn_ctfin N))
      (syn_cltfin) p0020
  have p0022 :=
    @g_notbid (.classEq (syn_ctfin M) (syn_ctfin N))
      (.classMem (syn_copk (syn_ctfin M) (syn_ctfin M)) (syn_cltfin))
      (.classMem (syn_copk (syn_ctfin M) (syn_ctfin N)) (syn_cltfin)) p0021
  have p0023 :=
    @g_syl5ibcom
      (syn_w3a (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)) (syn_wne M (syn_c0)))
      (.neg (.classMem (syn_copk (syn_ctfin M) (syn_ctfin M)) (syn_cltfin)))
      (.classEq (syn_ctfin M) (syn_ctfin N))
      (.neg (.classMem (syn_copk (syn_ctfin M) (syn_ctfin N)) (syn_cltfin))) p0019 p0022
  have p0024 :=
    @g_con2d
      (syn_w3a (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)) (syn_wne M (syn_c0)))
      (.classEq (syn_ctfin M) (syn_ctfin N))
      (.classMem (syn_copk (syn_ctfin M) (syn_ctfin N)) (syn_cltfin)) p0023
  have p0025 :=
    @g_imp
      (syn_w3a (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)) (syn_wne M (syn_c0)))
      (.classMem (syn_copk (syn_ctfin M) (syn_ctfin N)) (syn_cltfin))
      (.neg (.classEq (syn_ctfin M) (syn_ctfin N))) p0024
  have p0026 := @g_tfineq M N
  have p0027 :=
    @g_nsyl
      (syn_wa (syn_w3a (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)) (syn_wne M (syn_c0)))
        (.classMem (syn_copk (syn_ctfin M) (syn_ctfin N)) (syn_cltfin)))
      (.classEq (syn_ctfin M) (syn_ctfin N)) (.classEq M N) p0025 p0026
  have p0028 :=
    @g_simpl1 (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)) (syn_wne M (syn_c0))
      (syn_wa (.classMem (syn_copk (syn_ctfin M) (syn_ctfin N)) (syn_cltfin))
        (syn_wne N (syn_c0)))
  have p0029 :=
    @g_simpl3 (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)) (syn_wne M (syn_c0))
      (syn_wa (.classMem (syn_copk (syn_ctfin M) (syn_ctfin N)) (syn_cltfin))
        (syn_wne N (syn_c0)))
  have p0030 :=
    @g_syl2anc
      (syn_wa (syn_w3a (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)) (syn_wne M (syn_c0)))
        (syn_wa (.classMem (syn_copk (syn_ctfin M) (syn_ctfin N)) (syn_cltfin))
          (syn_wne N (syn_c0))))
      (.classMem M (syn_cnnc)) (syn_wne M (syn_c0)) (.classMem (syn_ctfin M) (syn_cnnc))
      p0028 p0029 p0016
  have p0031 :=
    @g_simpl2 (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)) (syn_wne M (syn_c0))
      (syn_wa (.classMem (syn_copk (syn_ctfin M) (syn_ctfin N)) (syn_cltfin))
        (syn_wne N (syn_c0)))
  have p0032 :=
    @g_simprr
      (syn_w3a (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)) (syn_wne M (syn_c0)))
      (.classMem (syn_copk (syn_ctfin M) (syn_ctfin N)) (syn_cltfin)) (syn_wne N (syn_c0))
  have p0033 := @g_tfinprop N y (by exact (show y ∉ (N).fv from (by exact fresh_y_not_N)))
  have p0034 :=
    @g_simpld (syn_wa (.classMem N (syn_cnnc)) (syn_wne N (syn_c0)))
      (.classMem (syn_ctfin N) (syn_cnnc))
      (syn_wrex y N (.classMem (syn_cpw1 (.cv y)) (syn_ctfin N))) p0033
  have p0035 :=
    @g_syl2anc
      (syn_wa (syn_w3a (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)) (syn_wne M (syn_c0)))
        (syn_wa (.classMem (syn_copk (syn_ctfin M) (syn_ctfin N)) (syn_cltfin))
          (syn_wne N (syn_c0))))
      (.classMem N (syn_cnnc)) (syn_wne N (syn_c0)) (.classMem (syn_ctfin N) (syn_cnnc))
      p0031 p0032 p0034
  have p0036 :=
    @g_jca
      (syn_wa (syn_w3a (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)) (syn_wne M (syn_c0)))
        (syn_wa (.classMem (syn_copk (syn_ctfin M) (syn_ctfin N)) (syn_cltfin))
          (syn_wne N (syn_c0))))
      (.classMem (syn_ctfin M) (syn_cnnc)) (.classMem (syn_ctfin N) (syn_cnnc)) p0030
      p0035
  have p0037 :=
    @g_simprl
      (syn_w3a (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)) (syn_wne M (syn_c0)))
      (.classMem (syn_copk (syn_ctfin M) (syn_ctfin N)) (syn_cltfin)) (syn_wne N (syn_c0))
  have p0038 := @g_ltfinasym (syn_ctfin M) (syn_ctfin N)
  have p0039 :=
    @g_sylc
      (syn_wa (syn_w3a (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)) (syn_wne M (syn_c0)))
        (syn_wa (.classMem (syn_copk (syn_ctfin M) (syn_ctfin N)) (syn_cltfin))
          (syn_wne N (syn_c0))))
      (syn_wa (.classMem (syn_ctfin M) (syn_cnnc)) (.classMem (syn_ctfin N) (syn_cnnc)))
      (.classMem (syn_copk (syn_ctfin M) (syn_ctfin N)) (syn_cltfin))
      (.neg (.classMem (syn_copk (syn_ctfin N) (syn_ctfin M)) (syn_cltfin))) p0036 p0037
      p0038
  have p0040 :=
    @g_expr
      (syn_w3a (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)) (syn_wne M (syn_c0)))
      (.classMem (syn_copk (syn_ctfin M) (syn_ctfin N)) (syn_cltfin)) (syn_wne N (syn_c0))
      (.neg (.classMem (syn_copk (syn_ctfin N) (syn_ctfin M)) (syn_cltfin))) p0039
  have p0041 :=
    @g_imnan (syn_wne N (syn_c0))
      (.classMem (syn_copk (syn_ctfin N) (syn_ctfin M)) (syn_cltfin))
  have p0042 :=
    @g_sylib
      (syn_wa (syn_w3a (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)) (syn_wne M (syn_c0)))
        (.classMem (syn_copk (syn_ctfin M) (syn_ctfin N)) (syn_cltfin)))
      (.imp (syn_wne N (syn_c0))
        (.neg (.classMem (syn_copk (syn_ctfin N) (syn_ctfin M)) (syn_cltfin))))
      (.neg (syn_wa (syn_wne N (syn_c0))
          (.classMem (syn_copk (syn_ctfin N) (syn_ctfin M)) (syn_cltfin))))
      p0040 p0041
  have p0043 :=
    @g_opkltfing y N M (syn_cnnc) (syn_cnnc)
      (by exact (show y ∉ (N).fv from (by exact fresh_y_not_N)))
      (by exact (show y ∉ (M).fv from (by exact fresh_y_not_M)))
  have p0044 :=
    @g_ancoms (.classMem N (syn_cnnc)) (.classMem M (syn_cnnc))
      (syn_wb (.classMem (syn_copk N M) (syn_cltfin)) (syn_wa (syn_wne N (syn_c0))
          (syn_wrex y (syn_cnnc) (.classEq M (syn_cplc (syn_cplc N (.cv y)) (syn_c1c))))))
      p0043
  have p0045 :=
    @g_n_3adant3 (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))
      (syn_wb (.classMem (syn_copk N M) (syn_cltfin)) (syn_wa (syn_wne N (syn_c0))
          (syn_wrex y (syn_cnnc) (.classEq M (syn_cplc (syn_cplc N (.cv y)) (syn_c1c))))))
      (syn_wne M (syn_c0)) p0044
  have p0046 :=
    @g_simprbda
      (syn_w3a (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)) (syn_wne M (syn_c0)))
      (.classMem (syn_copk N M) (syn_cltfin)) (syn_wne N (syn_c0))
      (syn_wrex y (syn_cnnc) (.classEq M (syn_cplc (syn_cplc N (.cv y)) (syn_c1c)))) p0045
  have p0047 :=
    @g_adantrl
      (syn_w3a (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)) (syn_wne M (syn_c0)))
      (.classMem (syn_copk N M) (syn_cltfin)) (syn_wne N (syn_c0))
      (.classMem (syn_copk (syn_ctfin M) (syn_ctfin N)) (syn_cltfin)) p0046
  have p0048 :=
    @g_simpl2 (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)) (syn_wne M (syn_c0))
      (syn_wa (.classMem (syn_copk (syn_ctfin M) (syn_ctfin N)) (syn_cltfin))
        (.classMem (syn_copk N M) (syn_cltfin)))
  have p0049 :=
    @g_simpl1 (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)) (syn_wne M (syn_c0))
      (syn_wa (.classMem (syn_copk (syn_ctfin M) (syn_ctfin N)) (syn_cltfin))
        (.classMem (syn_copk N M) (syn_cltfin)))
  have p0050 :=
    @g_jca
      (syn_wa (syn_w3a (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)) (syn_wne M (syn_c0)))
        (syn_wa (.classMem (syn_copk (syn_ctfin M) (syn_ctfin N)) (syn_cltfin))
          (.classMem (syn_copk N M) (syn_cltfin))))
      (.classMem N (syn_cnnc)) (.classMem M (syn_cnnc)) p0048 p0049
  have p0051 :=
    @g_simprr
      (syn_w3a (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)) (syn_wne M (syn_c0)))
      (.classMem (syn_copk (syn_ctfin M) (syn_ctfin N)) (syn_cltfin))
      (.classMem (syn_copk N M) (syn_cltfin))
  have p0052 := @g_tfinltfinlem1 N M
  have p0053 :=
    @g_sylc
      (syn_wa (syn_w3a (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)) (syn_wne M (syn_c0)))
        (syn_wa (.classMem (syn_copk (syn_ctfin M) (syn_ctfin N)) (syn_cltfin))
          (.classMem (syn_copk N M) (syn_cltfin))))
      (syn_wa (.classMem N (syn_cnnc)) (.classMem M (syn_cnnc)))
      (.classMem (syn_copk N M) (syn_cltfin))
      (.classMem (syn_copk (syn_ctfin N) (syn_ctfin M)) (syn_cltfin)) p0050 p0051 p0052
  have p0054 :=
    @g_jca
      (syn_wa (syn_w3a (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)) (syn_wne M (syn_c0)))
        (syn_wa (.classMem (syn_copk (syn_ctfin M) (syn_ctfin N)) (syn_cltfin))
          (.classMem (syn_copk N M) (syn_cltfin))))
      (syn_wne N (syn_c0)) (.classMem (syn_copk (syn_ctfin N) (syn_ctfin M)) (syn_cltfin))
      p0047 p0053
  have p0055 :=
    @g_expr
      (syn_w3a (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)) (syn_wne M (syn_c0)))
      (.classMem (syn_copk (syn_ctfin M) (syn_ctfin N)) (syn_cltfin))
      (.classMem (syn_copk N M) (syn_cltfin))
      (syn_wa (syn_wne N (syn_c0))
        (.classMem (syn_copk (syn_ctfin N) (syn_ctfin M)) (syn_cltfin)))
      p0054
  have p0056 :=
    @g_mtod
      (syn_wa (syn_w3a (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)) (syn_wne M (syn_c0)))
        (.classMem (syn_copk (syn_ctfin M) (syn_ctfin N)) (syn_cltfin)))
      (.classMem (syn_copk N M) (syn_cltfin))
      (syn_wa (syn_wne N (syn_c0))
        (.classMem (syn_copk (syn_ctfin N) (syn_ctfin M)) (syn_cltfin)))
      p0042 p0055
  have p0057 := @g_ltfintri M N
  have p0058 :=
    @g_adantr
      (syn_w3a (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)) (syn_wne M (syn_c0)))
      (syn_w3o (.classMem (syn_copk M N) (syn_cltfin)) (.classEq M N)
        (.classMem (syn_copk N M) (syn_cltfin)))
      (.classMem (syn_copk (syn_ctfin M) (syn_ctfin N)) (syn_cltfin)) p0057
  have p0059 :=
    @g_ecase23d
      (syn_wa (syn_w3a (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)) (syn_wne M (syn_c0)))
        (.classMem (syn_copk (syn_ctfin M) (syn_ctfin N)) (syn_cltfin)))
      (.classMem (syn_copk M N) (syn_cltfin)) (.classEq M N)
      (.classMem (syn_copk N M) (syn_cltfin)) p0027 p0056 p0058
  have p0060 :=
    @g_ex (syn_w3a (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)) (syn_wne M (syn_c0)))
      (.classMem (syn_copk (syn_ctfin M) (syn_ctfin N)) (syn_cltfin))
      (.classMem (syn_copk M N) (syn_cltfin)) p0059
  have p0061 :=
    @g_n_3expa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)) (syn_wne M (syn_c0))
      (.imp (.classMem (syn_copk (syn_ctfin M) (syn_ctfin N)) (syn_cltfin))
        (.classMem (syn_copk M N) (syn_cltfin)))
      p0060
  have p0062 :=
    @g_expcom (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)))
      (syn_wne M (syn_c0))
      (.imp (.classMem (syn_copk (syn_ctfin M) (syn_ctfin N)) (syn_cltfin))
        (.classMem (syn_copk M N) (syn_cltfin)))
      p0061
  have p0063 :=
    @g_pm2_61ine
      (.imp (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)))
        (.imp (.classMem (syn_copk (syn_ctfin M) (syn_ctfin N)) (syn_cltfin))
          (.classMem (syn_copk M N) (syn_cltfin))))
      M (syn_c0) p0014 p0062
  have p0064 :=
    @g_impbid (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)))
      (.classMem (syn_copk M N) (syn_cltfin))
      (.classMem (syn_copk (syn_ctfin M) (syn_ctfin N)) (syn_cltfin)) p0000 p0063
  exact p0064

@[expose]
noncomputable def g_tfinlefin (M : Class) (N : Class) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)))
        (syn_wb (.classMem (syn_copk M N) (syn_clefin))
          (.classMem (syn_copk (syn_ctfin M) (syn_ctfin N)) (syn_clefin)))) :=
  by
  have p0000 := @g_tfinltfin N M
  have p0001 :=
    @g_ancoms (.classMem N (syn_cnnc)) (.classMem M (syn_cnnc))
      (syn_wb (.classMem (syn_copk N M) (syn_cltfin))
        (.classMem (syn_copk (syn_ctfin N) (syn_ctfin M)) (syn_cltfin)))
      p0000
  have p0002 :=
    @g_notbid (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)))
      (.classMem (syn_copk N M) (syn_cltfin))
      (.classMem (syn_copk (syn_ctfin N) (syn_ctfin M)) (syn_cltfin)) p0001
  have p0003 := @g_lenltfin M N
  have p0004 := @g_tfincl M
  have p0005 := @g_tfincl N
  have p0006 := @g_lenltfin (syn_ctfin M) (syn_ctfin N)
  have p0007 :=
    @g_syl2an (.classMem M (syn_cnnc)) (.classMem (syn_ctfin M) (syn_cnnc))
      (.classMem (syn_ctfin N) (syn_cnnc))
      (syn_wb (.classMem (syn_copk (syn_ctfin M) (syn_ctfin N)) (syn_clefin))
        (.neg (.classMem (syn_copk (syn_ctfin N) (syn_ctfin M)) (syn_cltfin))))
      (.classMem N (syn_cnnc)) p0004 p0005 p0006
  have p0008 :=
    @g_n_3bitr4d (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)))
      (.neg (.classMem (syn_copk N M) (syn_cltfin)))
      (.neg (.classMem (syn_copk (syn_ctfin N) (syn_ctfin M)) (syn_cltfin)))
      (.classMem (syn_copk M N) (syn_clefin))
      (.classMem (syn_copk (syn_ctfin M) (syn_ctfin N)) (syn_clefin)) p0002 p0003 p0007
  exact p0008


end NFChoice.DirectNominalPrf.WPPReplay

end
