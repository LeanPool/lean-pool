/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C074C001Block002

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C074C001Part010`. -/


section

namespace NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

open scoped Fol
open NFChoice.Foundation
open NFChoice.Foundation.ExactLiteralTrial
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax
open NFChoice.Compiler.CompactSyntaxFVExplicit
open NFChoice.Compiler.WPPCompactSyntaxFVExplicit
open NFChoice.Compiler.CoreFVSimp
open NFChoice.DefinitionLeaves.AlphaFocusedSupport
open NFChoice.DefinitionLeaves.AlphaFocusedFV
open NFChoice.DirectNominalPrf
open NFChoice.DirectNominalPrf.Nominal

@[expose]
noncomputable def nb074_split_alpha_0006 (x : Var) :
    TAlphaWff
      [((nb074_alpha_dummy_119), (nb074_alpha_dummy_120 x)),
        ((nb074_alpha_dummy_088), (nb074_alpha_dummy_090 x)),
        ((nb074_alpha_dummy_087), (nb074_alpha_dummy_089 x)),
        ((nb074_alpha_dummy_117), (nb074_alpha_dummy_118 x)),
        ((nb074_alpha_dummy_091), (nb074_alpha_dummy_092 x)),
        ((nb074_alpha_dummy_082), (nb074_alpha_dummy_084 x)),
        ((nb074_alpha_dummy_081), (nb074_alpha_dummy_083 x)),
        ((nb074_alpha_dummy_085), (nb074_alpha_dummy_086 x)),
        ((nb074_alpha_dummy_042), (nb074_alpha_dummy_044 x)),
        ((nb074_alpha_dummy_041), (nb074_alpha_dummy_043 x)),
        ((nb074_alpha_dummy_001), (nb074_alpha_dummy_002 x)),
        ((nb074_alpha_dummy_000), x),
        ((nb074_alpha_dummy_003), (nb074_alpha_dummy_004 x))]
      (Wff.imp (Wff.classMem (Class.cv (nb074_alpha_dummy_119))
          (syn_ccompl (syn_cphi (Class.cv (nb074_alpha_dummy_088))))) (Wff.neg
          (Wff.classMem (Class.cv (nb074_alpha_dummy_119)) (syn_ccompl (syn_csn (syn_c0c))))))
      (Wff.imp (Wff.classMem (Class.cv (nb074_alpha_dummy_120 x))
          (syn_ccompl (syn_cphi (Class.cv (nb074_alpha_dummy_090 x))))) (Wff.neg
          (Wff.classMem (Class.cv (nb074_alpha_dummy_120 x))
            (syn_ccompl (syn_csn (syn_c0c)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb074_alpha_dummy_088) ≠ (nb074_alpha_dummy_095) from (by
                              unfold nb074_alpha_dummy_095;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb074_support_mem_0092) 0))))
                          (show (nb074_alpha_dummy_090 x) ≠ (nb074_alpha_dummy_097 x) from (by
                              unfold nb074_alpha_dummy_097;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb074_support_mem_0093 x) 0))))
                          (TAlphaVar.there
                            (show (nb074_alpha_dummy_088) ≠ (nb074_alpha_dummy_096) from (by
                                unfold nb074_alpha_dummy_096;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb074_support_mem_0092) 1))))
                            (show (nb074_alpha_dummy_090 x) ≠ (nb074_alpha_dummy_098 x) from (by
                                unfold nb074_alpha_dummy_098;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb074_support_mem_0093 x) 1))))
                            (TAlphaVar.there
                              (show (nb074_alpha_dummy_088) ≠ (nb074_alpha_dummy_121) from (by
                                  unfold nb074_alpha_dummy_121;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb074_support_mem_0122) 0))))
                              (show (nb074_alpha_dummy_090 x) ≠ (nb074_alpha_dummy_122 x) from
                                (by
                                  unfold nb074_alpha_dummy_122;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb074_support_mem_0123 x) 0))))
                              (TAlphaVar.there
                                (show (nb074_alpha_dummy_088) ≠ (nb074_alpha_dummy_119) from (by
                                    unfold nb074_alpha_dummy_119;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb074_support_mem_0120) 0)))) (show
                                  (nb074_alpha_dummy_090 x) ≠ (nb074_alpha_dummy_120 x) from (by
                                    unfold nb074_alpha_dummy_120;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb074_support_mem_0121 x)
                                            0)))) (TAlphaVar.here _ _ _)))))))
                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb074_alpha_dummy_088))).fv)
                            (by decide))
                          (freshVar_injective (((Class.cv (nb074_alpha_dummy_090 x))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb074_alpha_dummy_095) ≠ (nb074_alpha_dummy_102) from (by
          unfold nb074_alpha_dummy_102;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0096) 1)))) (show (nb074_alpha_dummy_097 x) ≠
        (nb074_alpha_dummy_105 x) from (by
          unfold nb074_alpha_dummy_105;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0097 x) 1)))) (TAlphaVar.there (show
        (nb074_alpha_dummy_095) ≠ (nb074_alpha_dummy_101) from (by
          unfold nb074_alpha_dummy_101;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0096) 0)))) (show (nb074_alpha_dummy_097 x) ≠
        (nb074_alpha_dummy_104 x) from (by
          unfold nb074_alpha_dummy_104;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0097 x) 0)))) (TAlphaVar.there (show
        (nb074_alpha_dummy_095) ≠ (nb074_alpha_dummy_099) from (by
          unfold nb074_alpha_dummy_099;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0094) 0)))) (show (nb074_alpha_dummy_097 x) ≠
        (nb074_alpha_dummy_100 x) from (by
          unfold nb074_alpha_dummy_100;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0095 x)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb074_alpha_dummy_103), (nb074_alpha_dummy_106 x)), ((nb074_alpha_dummy_102),
        (nb074_alpha_dummy_105 x)), ((nb074_alpha_dummy_101), (nb074_alpha_dummy_104 x)),
        ((nb074_alpha_dummy_099), (nb074_alpha_dummy_100 x)), ((nb074_alpha_dummy_095),
        (nb074_alpha_dummy_097 x)), ((nb074_alpha_dummy_096), (nb074_alpha_dummy_098 x)),
        ((nb074_alpha_dummy_121), (nb074_alpha_dummy_122 x)), ((nb074_alpha_dummy_119),
        (nb074_alpha_dummy_120 x)), ((nb074_alpha_dummy_088), (nb074_alpha_dummy_090 x)),
        ((nb074_alpha_dummy_087), (nb074_alpha_dummy_089 x)), ((nb074_alpha_dummy_117),
        (nb074_alpha_dummy_118 x)), ((nb074_alpha_dummy_091), (nb074_alpha_dummy_092 x)),
        ((nb074_alpha_dummy_082), (nb074_alpha_dummy_084 x)), ((nb074_alpha_dummy_081),
        (nb074_alpha_dummy_083 x)), ((nb074_alpha_dummy_085), (nb074_alpha_dummy_086 x)),
        ((nb074_alpha_dummy_042), (nb074_alpha_dummy_044 x)), ((nb074_alpha_dummy_041),
        (nb074_alpha_dummy_043 x)), ((nb074_alpha_dummy_001), (nb074_alpha_dummy_002 x)),
        ((nb074_alpha_dummy_000), x), ((nb074_alpha_dummy_003), (nb074_alpha_dummy_004 x))]
        (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb074_alpha_dummy_102) ≠ (nb074_alpha_dummy_109) from (by
          unfold
            nb074_alpha_dummy_109;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0100)
                  0)))) (show (nb074_alpha_dummy_105 x) ≠ (nb074_alpha_dummy_110 x) from (by
          unfold
            nb074_alpha_dummy_110;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0101
                    x)
                  0)))) (TAlphaVar.there (show (nb074_alpha_dummy_102) ≠ (nb074_alpha_dummy_107)
        from (by
          unfold
            nb074_alpha_dummy_107;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0098)
                  0)))) (show (nb074_alpha_dummy_105 x) ≠ (nb074_alpha_dummy_108 x) from (by
          unfold
            nb074_alpha_dummy_108;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0099
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb074_alpha_dummy_095))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb074_alpha_dummy_097 x))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb074_alpha_dummy_103) ≠ (nb074_alpha_dummy_109)
        from (by
          unfold
            nb074_alpha_dummy_109;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0104)
                  0)))) (show (nb074_alpha_dummy_106 x) ≠ (nb074_alpha_dummy_110 x) from (by
          unfold
            nb074_alpha_dummy_110;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0105
                    x)
                  0)))) (TAlphaVar.there (show (nb074_alpha_dummy_103) ≠ (nb074_alpha_dummy_107)
        from (by
          unfold
            nb074_alpha_dummy_107;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0102)
                  0)))) (show (nb074_alpha_dummy_106 x) ≠ (nb074_alpha_dummy_108 x) from (by
          unfold
            nb074_alpha_dummy_108;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0103
                    x)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb074_alpha_dummy_102) ≠ (nb074_alpha_dummy_109) from (by
          unfold
            nb074_alpha_dummy_109;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0100)
                  0)))) (show (nb074_alpha_dummy_105 x) ≠ (nb074_alpha_dummy_110 x) from (by
          unfold
            nb074_alpha_dummy_110;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0101
                    x)
                  0)))) (TAlphaVar.there (show (nb074_alpha_dummy_102) ≠ (nb074_alpha_dummy_107)
        from (by
          unfold
            nb074_alpha_dummy_107;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0098)
                  0)))) (show (nb074_alpha_dummy_105 x) ≠ (nb074_alpha_dummy_108 x) from (by
          unfold
            nb074_alpha_dummy_108;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0099
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb074_alpha_dummy_095))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb074_alpha_dummy_097 x))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb074_alpha_dummy_103) ≠ (nb074_alpha_dummy_109)
        from (by
          unfold
            nb074_alpha_dummy_109;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0104)
                  0)))) (show (nb074_alpha_dummy_106 x) ≠ (nb074_alpha_dummy_110 x) from (by
          unfold
            nb074_alpha_dummy_110;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0105
                    x)
                  0)))) (TAlphaVar.there (show (nb074_alpha_dummy_103) ≠ (nb074_alpha_dummy_107)
        from (by
          unfold
            nb074_alpha_dummy_107;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0102)
                  0)))) (show (nb074_alpha_dummy_106 x) ≠ (nb074_alpha_dummy_108 x) from (by
          unfold
            nb074_alpha_dummy_108;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0103
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb074_alpha_dummy_103), (nb074_alpha_dummy_106 x)), ((nb074_alpha_dummy_102),
        (nb074_alpha_dummy_105 x)), ((nb074_alpha_dummy_101), (nb074_alpha_dummy_104 x)),
        ((nb074_alpha_dummy_099), (nb074_alpha_dummy_100 x)), ((nb074_alpha_dummy_095),
        (nb074_alpha_dummy_097 x)), ((nb074_alpha_dummy_096), (nb074_alpha_dummy_098 x)),
        ((nb074_alpha_dummy_121), (nb074_alpha_dummy_122 x)), ((nb074_alpha_dummy_119),
        (nb074_alpha_dummy_120 x)), ((nb074_alpha_dummy_088), (nb074_alpha_dummy_090 x)),
        ((nb074_alpha_dummy_087), (nb074_alpha_dummy_089 x)), ((nb074_alpha_dummy_117),
        (nb074_alpha_dummy_118 x)), ((nb074_alpha_dummy_091), (nb074_alpha_dummy_092 x)),
        ((nb074_alpha_dummy_082), (nb074_alpha_dummy_084 x)), ((nb074_alpha_dummy_081),
        (nb074_alpha_dummy_083 x)), ((nb074_alpha_dummy_085), (nb074_alpha_dummy_086 x)),
        ((nb074_alpha_dummy_042), (nb074_alpha_dummy_044 x)), ((nb074_alpha_dummy_041),
        (nb074_alpha_dummy_043 x)), ((nb074_alpha_dummy_001), (nb074_alpha_dummy_002 x)),
        ((nb074_alpha_dummy_000), x), ((nb074_alpha_dummy_003), (nb074_alpha_dummy_004 x))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb074_alpha_dummy_095))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb074_alpha_dummy_097 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb074_alpha_dummy_095))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb074_alpha_dummy_097 x))).fv ∪
        ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb074_alpha_dummy_102) ≠
        (nb074_alpha_dummy_113) from (by
          unfold
            nb074_alpha_dummy_113;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0108)
                  0)))) (show (nb074_alpha_dummy_105 x) ≠ (nb074_alpha_dummy_114 x) from (by
          unfold
            nb074_alpha_dummy_114;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0109
                    x)
                  0)))) (TAlphaVar.there (show (nb074_alpha_dummy_102) ≠ (nb074_alpha_dummy_111)
        from (by
          unfold
            nb074_alpha_dummy_111;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0106)
                  0)))) (show (nb074_alpha_dummy_105 x) ≠ (nb074_alpha_dummy_112 x) from (by
          unfold
            nb074_alpha_dummy_112;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0107
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb074_alpha_dummy_095))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb074_alpha_dummy_097 x))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb074_alpha_dummy_102) ≠ (nb074_alpha_dummy_113)
        from (by
          unfold
            nb074_alpha_dummy_113;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0108)
                  0)))) (show (nb074_alpha_dummy_105 x) ≠ (nb074_alpha_dummy_114 x) from (by
          unfold
            nb074_alpha_dummy_114;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0109
                    x)
                  0)))) (TAlphaVar.there (show (nb074_alpha_dummy_102) ≠ (nb074_alpha_dummy_111)
        from (by
          unfold
            nb074_alpha_dummy_111;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0106)
                  0)))) (show (nb074_alpha_dummy_105 x) ≠ (nb074_alpha_dummy_112 x) from (by
          unfold
            nb074_alpha_dummy_112;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0107
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb074_alpha_dummy_095))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb074_alpha_dummy_097 x))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb074_alpha_dummy_103) ≠ (nb074_alpha_dummy_115) from (by
          unfold
            nb074_alpha_dummy_115;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0112)
                  0)))) (show (nb074_alpha_dummy_106 x) ≠ (nb074_alpha_dummy_116 x) from (by
          unfold
            nb074_alpha_dummy_116;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0113
                    x)
                  0)))) (TAlphaVar.there (show (nb074_alpha_dummy_103) ≠ (nb074_alpha_dummy_111)
        from (by
          unfold
            nb074_alpha_dummy_111;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0110)
                  0)))) (show (nb074_alpha_dummy_106 x) ≠ (nb074_alpha_dummy_112 x) from (by
          unfold
            nb074_alpha_dummy_112;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0111
                    x)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb074_alpha_dummy_103) ≠
        (nb074_alpha_dummy_115) from (by
          unfold
            nb074_alpha_dummy_115;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0112)
                  0)))) (show (nb074_alpha_dummy_106 x) ≠ (nb074_alpha_dummy_116 x) from (by
          unfold
            nb074_alpha_dummy_116;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0113
                    x)
                  0)))) (TAlphaVar.there (show (nb074_alpha_dummy_103) ≠ (nb074_alpha_dummy_111)
        from (by
          unfold
            nb074_alpha_dummy_111;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0110)
                  0)))) (show (nb074_alpha_dummy_106 x) ≠ (nb074_alpha_dummy_112 x) from (by
          unfold
            nb074_alpha_dummy_112;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0111
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb074_alpha_dummy_095) ≠ (nb074_alpha_dummy_099) from (by
                                        unfold nb074_alpha_dummy_099;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb074_support_mem_0094)
                                                0)))) (show (nb074_alpha_dummy_097 x) ≠
                                        (nb074_alpha_dummy_100 x) from (by
                                        unfold nb074_alpha_dummy_100;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb074_support_mem_0095 x)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
                                  [((nb074_alpha_dummy_099), (nb074_alpha_dummy_100 x)),
                                    ((nb074_alpha_dummy_095), (nb074_alpha_dummy_097 x)),
                                    ((nb074_alpha_dummy_096), (nb074_alpha_dummy_098 x)),
                                    ((nb074_alpha_dummy_121), (nb074_alpha_dummy_122 x)),
                                    ((nb074_alpha_dummy_119), (nb074_alpha_dummy_120 x)),
                                    ((nb074_alpha_dummy_088), (nb074_alpha_dummy_090 x)),
                                    ((nb074_alpha_dummy_087), (nb074_alpha_dummy_089 x)),
                                    ((nb074_alpha_dummy_117), (nb074_alpha_dummy_118 x)),
                                    ((nb074_alpha_dummy_091), (nb074_alpha_dummy_092 x)),
                                    ((nb074_alpha_dummy_082), (nb074_alpha_dummy_084 x)),
                                    ((nb074_alpha_dummy_081), (nb074_alpha_dummy_083 x)),
                                    ((nb074_alpha_dummy_085), (nb074_alpha_dummy_086 x)),
                                    ((nb074_alpha_dummy_042), (nb074_alpha_dummy_044 x)),
                                    ((nb074_alpha_dummy_041), (nb074_alpha_dummy_043 x)),
                                    ((nb074_alpha_dummy_001), (nb074_alpha_dummy_002 x)),
                                    ((nb074_alpha_dummy_000), x),
                                    ((nb074_alpha_dummy_003), (nb074_alpha_dummy_004 x))]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb074_alpha_dummy_095) ≠ (nb074_alpha_dummy_099) from
                                    (by
                                      unfold nb074_alpha_dummy_099;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb074_support_mem_0094)
                                              0)))) (show
                                    (nb074_alpha_dummy_097 x) ≠ (nb074_alpha_dummy_100 x) from
                                    (by
                                      unfold nb074_alpha_dummy_100;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb074_support_mem_0095 x)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb074_alpha_dummy_095) ≠ (nb074_alpha_dummy_099) from (by
                                        unfold nb074_alpha_dummy_099;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb074_support_mem_0094)
                                                0)))) (show (nb074_alpha_dummy_097 x) ≠
                                        (nb074_alpha_dummy_100 x) from (by
                                        unfold nb074_alpha_dummy_100;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb074_support_mem_0095 x)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
                                  [((nb074_alpha_dummy_099), (nb074_alpha_dummy_100 x)),
                                    ((nb074_alpha_dummy_095), (nb074_alpha_dummy_097 x)),
                                    ((nb074_alpha_dummy_096), (nb074_alpha_dummy_098 x)),
                                    ((nb074_alpha_dummy_121), (nb074_alpha_dummy_122 x)),
                                    ((nb074_alpha_dummy_119), (nb074_alpha_dummy_120 x)),
                                    ((nb074_alpha_dummy_088), (nb074_alpha_dummy_090 x)),
                                    ((nb074_alpha_dummy_087), (nb074_alpha_dummy_089 x)),
                                    ((nb074_alpha_dummy_117), (nb074_alpha_dummy_118 x)),
                                    ((nb074_alpha_dummy_091), (nb074_alpha_dummy_092 x)),
                                    ((nb074_alpha_dummy_082), (nb074_alpha_dummy_084 x)),
                                    ((nb074_alpha_dummy_081), (nb074_alpha_dummy_083 x)),
                                    ((nb074_alpha_dummy_085), (nb074_alpha_dummy_086 x)),
                                    ((nb074_alpha_dummy_042), (nb074_alpha_dummy_044 x)),
                                    ((nb074_alpha_dummy_041), (nb074_alpha_dummy_043 x)),
                                    ((nb074_alpha_dummy_001), (nb074_alpha_dummy_002 x)),
                                    ((nb074_alpha_dummy_000), x),
                                    ((nb074_alpha_dummy_003), (nb074_alpha_dummy_004 x))]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb074_alpha_dummy_088) ≠ (nb074_alpha_dummy_095) from (by
                              unfold nb074_alpha_dummy_095;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb074_support_mem_0092) 0))))
                          (show (nb074_alpha_dummy_090 x) ≠ (nb074_alpha_dummy_097 x) from (by
                              unfold nb074_alpha_dummy_097;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb074_support_mem_0093 x) 0))))
                          (TAlphaVar.there
                            (show (nb074_alpha_dummy_088) ≠ (nb074_alpha_dummy_096) from (by
                                unfold nb074_alpha_dummy_096;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb074_support_mem_0092) 1))))
                            (show (nb074_alpha_dummy_090 x) ≠ (nb074_alpha_dummy_098 x) from (by
                                unfold nb074_alpha_dummy_098;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb074_support_mem_0093 x) 1))))
                            (TAlphaVar.there
                              (show (nb074_alpha_dummy_088) ≠ (nb074_alpha_dummy_121) from (by
                                  unfold nb074_alpha_dummy_121;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb074_support_mem_0122) 0))))
                              (show (nb074_alpha_dummy_090 x) ≠ (nb074_alpha_dummy_122 x) from
                                (by
                                  unfold nb074_alpha_dummy_122;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb074_support_mem_0123 x) 0))))
                              (TAlphaVar.there
                                (show (nb074_alpha_dummy_088) ≠ (nb074_alpha_dummy_119) from (by
                                    unfold nb074_alpha_dummy_119;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb074_support_mem_0120) 0)))) (show
                                  (nb074_alpha_dummy_090 x) ≠ (nb074_alpha_dummy_120 x) from (by
                                    unfold nb074_alpha_dummy_120;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb074_support_mem_0121 x)
                                            0)))) (TAlphaVar.here _ _ _)))))))
                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb074_alpha_dummy_088))).fv)
                            (by decide))
                          (freshVar_injective (((Class.cv (nb074_alpha_dummy_090 x))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb074_alpha_dummy_095) ≠ (nb074_alpha_dummy_102) from (by
          unfold nb074_alpha_dummy_102;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0096) 1)))) (show (nb074_alpha_dummy_097 x) ≠
        (nb074_alpha_dummy_105 x) from (by
          unfold nb074_alpha_dummy_105;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0097 x) 1)))) (TAlphaVar.there (show
        (nb074_alpha_dummy_095) ≠ (nb074_alpha_dummy_101) from (by
          unfold nb074_alpha_dummy_101;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0096) 0)))) (show (nb074_alpha_dummy_097 x) ≠
        (nb074_alpha_dummy_104 x) from (by
          unfold nb074_alpha_dummy_104;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0097 x) 0)))) (TAlphaVar.there (show
        (nb074_alpha_dummy_095) ≠ (nb074_alpha_dummy_099) from (by
          unfold nb074_alpha_dummy_099;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0094) 0)))) (show (nb074_alpha_dummy_097 x) ≠
        (nb074_alpha_dummy_100 x) from (by
          unfold nb074_alpha_dummy_100;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0095 x)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb074_alpha_dummy_103), (nb074_alpha_dummy_106 x)), ((nb074_alpha_dummy_102),
        (nb074_alpha_dummy_105 x)), ((nb074_alpha_dummy_101), (nb074_alpha_dummy_104 x)),
        ((nb074_alpha_dummy_099), (nb074_alpha_dummy_100 x)), ((nb074_alpha_dummy_095),
        (nb074_alpha_dummy_097 x)), ((nb074_alpha_dummy_096), (nb074_alpha_dummy_098 x)),
        ((nb074_alpha_dummy_121), (nb074_alpha_dummy_122 x)), ((nb074_alpha_dummy_119),
        (nb074_alpha_dummy_120 x)), ((nb074_alpha_dummy_088), (nb074_alpha_dummy_090 x)),
        ((nb074_alpha_dummy_087), (nb074_alpha_dummy_089 x)), ((nb074_alpha_dummy_117),
        (nb074_alpha_dummy_118 x)), ((nb074_alpha_dummy_091), (nb074_alpha_dummy_092 x)),
        ((nb074_alpha_dummy_082), (nb074_alpha_dummy_084 x)), ((nb074_alpha_dummy_081),
        (nb074_alpha_dummy_083 x)), ((nb074_alpha_dummy_085), (nb074_alpha_dummy_086 x)),
        ((nb074_alpha_dummy_042), (nb074_alpha_dummy_044 x)), ((nb074_alpha_dummy_041),
        (nb074_alpha_dummy_043 x)), ((nb074_alpha_dummy_001), (nb074_alpha_dummy_002 x)),
        ((nb074_alpha_dummy_000), x), ((nb074_alpha_dummy_003), (nb074_alpha_dummy_004 x))]
        (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb074_alpha_dummy_102) ≠ (nb074_alpha_dummy_109) from (by
          unfold
            nb074_alpha_dummy_109;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0100)
                  0)))) (show (nb074_alpha_dummy_105 x) ≠ (nb074_alpha_dummy_110 x) from (by
          unfold
            nb074_alpha_dummy_110;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0101
                    x)
                  0)))) (TAlphaVar.there (show (nb074_alpha_dummy_102) ≠ (nb074_alpha_dummy_107)
        from (by
          unfold
            nb074_alpha_dummy_107;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0098)
                  0)))) (show (nb074_alpha_dummy_105 x) ≠ (nb074_alpha_dummy_108 x) from (by
          unfold
            nb074_alpha_dummy_108;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0099
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb074_alpha_dummy_095))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb074_alpha_dummy_097 x))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb074_alpha_dummy_103) ≠ (nb074_alpha_dummy_109)
        from (by
          unfold
            nb074_alpha_dummy_109;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0104)
                  0)))) (show (nb074_alpha_dummy_106 x) ≠ (nb074_alpha_dummy_110 x) from (by
          unfold
            nb074_alpha_dummy_110;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0105
                    x)
                  0)))) (TAlphaVar.there (show (nb074_alpha_dummy_103) ≠ (nb074_alpha_dummy_107)
        from (by
          unfold
            nb074_alpha_dummy_107;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0102)
                  0)))) (show (nb074_alpha_dummy_106 x) ≠ (nb074_alpha_dummy_108 x) from (by
          unfold
            nb074_alpha_dummy_108;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0103
                    x)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb074_alpha_dummy_102) ≠ (nb074_alpha_dummy_109) from (by
          unfold
            nb074_alpha_dummy_109;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0100)
                  0)))) (show (nb074_alpha_dummy_105 x) ≠ (nb074_alpha_dummy_110 x) from (by
          unfold
            nb074_alpha_dummy_110;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0101
                    x)
                  0)))) (TAlphaVar.there (show (nb074_alpha_dummy_102) ≠ (nb074_alpha_dummy_107)
        from (by
          unfold
            nb074_alpha_dummy_107;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0098)
                  0)))) (show (nb074_alpha_dummy_105 x) ≠ (nb074_alpha_dummy_108 x) from (by
          unfold
            nb074_alpha_dummy_108;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0099
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb074_alpha_dummy_095))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb074_alpha_dummy_097 x))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb074_alpha_dummy_103) ≠ (nb074_alpha_dummy_109)
        from (by
          unfold
            nb074_alpha_dummy_109;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0104)
                  0)))) (show (nb074_alpha_dummy_106 x) ≠ (nb074_alpha_dummy_110 x) from (by
          unfold
            nb074_alpha_dummy_110;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0105
                    x)
                  0)))) (TAlphaVar.there (show (nb074_alpha_dummy_103) ≠ (nb074_alpha_dummy_107)
        from (by
          unfold
            nb074_alpha_dummy_107;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0102)
                  0)))) (show (nb074_alpha_dummy_106 x) ≠ (nb074_alpha_dummy_108 x) from (by
          unfold
            nb074_alpha_dummy_108;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0103
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb074_alpha_dummy_103), (nb074_alpha_dummy_106 x)), ((nb074_alpha_dummy_102),
        (nb074_alpha_dummy_105 x)), ((nb074_alpha_dummy_101), (nb074_alpha_dummy_104 x)),
        ((nb074_alpha_dummy_099), (nb074_alpha_dummy_100 x)), ((nb074_alpha_dummy_095),
        (nb074_alpha_dummy_097 x)), ((nb074_alpha_dummy_096), (nb074_alpha_dummy_098 x)),
        ((nb074_alpha_dummy_121), (nb074_alpha_dummy_122 x)), ((nb074_alpha_dummy_119),
        (nb074_alpha_dummy_120 x)), ((nb074_alpha_dummy_088), (nb074_alpha_dummy_090 x)),
        ((nb074_alpha_dummy_087), (nb074_alpha_dummy_089 x)), ((nb074_alpha_dummy_117),
        (nb074_alpha_dummy_118 x)), ((nb074_alpha_dummy_091), (nb074_alpha_dummy_092 x)),
        ((nb074_alpha_dummy_082), (nb074_alpha_dummy_084 x)), ((nb074_alpha_dummy_081),
        (nb074_alpha_dummy_083 x)), ((nb074_alpha_dummy_085), (nb074_alpha_dummy_086 x)),
        ((nb074_alpha_dummy_042), (nb074_alpha_dummy_044 x)), ((nb074_alpha_dummy_041),
        (nb074_alpha_dummy_043 x)), ((nb074_alpha_dummy_001), (nb074_alpha_dummy_002 x)),
        ((nb074_alpha_dummy_000), x), ((nb074_alpha_dummy_003), (nb074_alpha_dummy_004 x))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb074_alpha_dummy_095))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb074_alpha_dummy_097 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb074_alpha_dummy_095))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb074_alpha_dummy_097 x))).fv ∪
        ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb074_alpha_dummy_102) ≠
        (nb074_alpha_dummy_113) from (by
          unfold
            nb074_alpha_dummy_113;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0108)
                  0)))) (show (nb074_alpha_dummy_105 x) ≠ (nb074_alpha_dummy_114 x) from (by
          unfold
            nb074_alpha_dummy_114;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0109
                    x)
                  0)))) (TAlphaVar.there (show (nb074_alpha_dummy_102) ≠ (nb074_alpha_dummy_111)
        from (by
          unfold
            nb074_alpha_dummy_111;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0106)
                  0)))) (show (nb074_alpha_dummy_105 x) ≠ (nb074_alpha_dummy_112 x) from (by
          unfold
            nb074_alpha_dummy_112;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0107
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb074_alpha_dummy_095))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb074_alpha_dummy_097 x))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb074_alpha_dummy_102) ≠ (nb074_alpha_dummy_113)
        from (by
          unfold
            nb074_alpha_dummy_113;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0108)
                  0)))) (show (nb074_alpha_dummy_105 x) ≠ (nb074_alpha_dummy_114 x) from (by
          unfold
            nb074_alpha_dummy_114;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0109
                    x)
                  0)))) (TAlphaVar.there (show (nb074_alpha_dummy_102) ≠ (nb074_alpha_dummy_111)
        from (by
          unfold
            nb074_alpha_dummy_111;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0106)
                  0)))) (show (nb074_alpha_dummy_105 x) ≠ (nb074_alpha_dummy_112 x) from (by
          unfold
            nb074_alpha_dummy_112;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0107
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb074_alpha_dummy_095))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb074_alpha_dummy_097 x))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb074_alpha_dummy_103) ≠ (nb074_alpha_dummy_115) from (by
          unfold
            nb074_alpha_dummy_115;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0112)
                  0)))) (show (nb074_alpha_dummy_106 x) ≠ (nb074_alpha_dummy_116 x) from (by
          unfold
            nb074_alpha_dummy_116;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0113
                    x)
                  0)))) (TAlphaVar.there (show (nb074_alpha_dummy_103) ≠ (nb074_alpha_dummy_111)
        from (by
          unfold
            nb074_alpha_dummy_111;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0110)
                  0)))) (show (nb074_alpha_dummy_106 x) ≠ (nb074_alpha_dummy_112 x) from (by
          unfold
            nb074_alpha_dummy_112;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0111
                    x)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb074_alpha_dummy_103) ≠
        (nb074_alpha_dummy_115) from (by
          unfold
            nb074_alpha_dummy_115;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0112)
                  0)))) (show (nb074_alpha_dummy_106 x) ≠ (nb074_alpha_dummy_116 x) from (by
          unfold
            nb074_alpha_dummy_116;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0113
                    x)
                  0)))) (TAlphaVar.there (show (nb074_alpha_dummy_103) ≠ (nb074_alpha_dummy_111)
        from (by
          unfold
            nb074_alpha_dummy_111;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0110)
                  0)))) (show (nb074_alpha_dummy_106 x) ≠ (nb074_alpha_dummy_112 x) from (by
          unfold
            nb074_alpha_dummy_112;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0111
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb074_alpha_dummy_095) ≠ (nb074_alpha_dummy_099) from (by
                                        unfold nb074_alpha_dummy_099;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb074_support_mem_0094)
                                                0)))) (show (nb074_alpha_dummy_097 x) ≠
                                        (nb074_alpha_dummy_100 x) from (by
                                        unfold nb074_alpha_dummy_100;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb074_support_mem_0095 x)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
                                  [((nb074_alpha_dummy_099), (nb074_alpha_dummy_100 x)),
                                    ((nb074_alpha_dummy_095), (nb074_alpha_dummy_097 x)),
                                    ((nb074_alpha_dummy_096), (nb074_alpha_dummy_098 x)),
                                    ((nb074_alpha_dummy_121), (nb074_alpha_dummy_122 x)),
                                    ((nb074_alpha_dummy_119), (nb074_alpha_dummy_120 x)),
                                    ((nb074_alpha_dummy_088), (nb074_alpha_dummy_090 x)),
                                    ((nb074_alpha_dummy_087), (nb074_alpha_dummy_089 x)),
                                    ((nb074_alpha_dummy_117), (nb074_alpha_dummy_118 x)),
                                    ((nb074_alpha_dummy_091), (nb074_alpha_dummy_092 x)),
                                    ((nb074_alpha_dummy_082), (nb074_alpha_dummy_084 x)),
                                    ((nb074_alpha_dummy_081), (nb074_alpha_dummy_083 x)),
                                    ((nb074_alpha_dummy_085), (nb074_alpha_dummy_086 x)),
                                    ((nb074_alpha_dummy_042), (nb074_alpha_dummy_044 x)),
                                    ((nb074_alpha_dummy_041), (nb074_alpha_dummy_043 x)),
                                    ((nb074_alpha_dummy_001), (nb074_alpha_dummy_002 x)),
                                    ((nb074_alpha_dummy_000), x),
                                    ((nb074_alpha_dummy_003), (nb074_alpha_dummy_004 x))]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb074_alpha_dummy_095) ≠ (nb074_alpha_dummy_099) from
                                    (by
                                      unfold nb074_alpha_dummy_099;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb074_support_mem_0094)
                                              0)))) (show
                                    (nb074_alpha_dummy_097 x) ≠ (nb074_alpha_dummy_100 x) from
                                    (by
                                      unfold nb074_alpha_dummy_100;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb074_support_mem_0095 x)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb074_alpha_dummy_095) ≠ (nb074_alpha_dummy_099) from (by
                                        unfold nb074_alpha_dummy_099;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb074_support_mem_0094)
                                                0)))) (show (nb074_alpha_dummy_097 x) ≠
                                        (nb074_alpha_dummy_100 x) from (by
                                        unfold nb074_alpha_dummy_100;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb074_support_mem_0095 x)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
                                  [((nb074_alpha_dummy_099), (nb074_alpha_dummy_100 x)),
                                    ((nb074_alpha_dummy_095), (nb074_alpha_dummy_097 x)),
                                    ((nb074_alpha_dummy_096), (nb074_alpha_dummy_098 x)),
                                    ((nb074_alpha_dummy_121), (nb074_alpha_dummy_122 x)),
                                    ((nb074_alpha_dummy_119), (nb074_alpha_dummy_120 x)),
                                    ((nb074_alpha_dummy_088), (nb074_alpha_dummy_090 x)),
                                    ((nb074_alpha_dummy_087), (nb074_alpha_dummy_089 x)),
                                    ((nb074_alpha_dummy_117), (nb074_alpha_dummy_118 x)),
                                    ((nb074_alpha_dummy_091), (nb074_alpha_dummy_092 x)),
                                    ((nb074_alpha_dummy_082), (nb074_alpha_dummy_084 x)),
                                    ((nb074_alpha_dummy_081), (nb074_alpha_dummy_083 x)),
                                    ((nb074_alpha_dummy_085), (nb074_alpha_dummy_086 x)),
                                    ((nb074_alpha_dummy_042), (nb074_alpha_dummy_044 x)),
                                    ((nb074_alpha_dummy_041), (nb074_alpha_dummy_043 x)),
                                    ((nb074_alpha_dummy_001), (nb074_alpha_dummy_002 x)),
                                    ((nb074_alpha_dummy_000), x),
                                    ((nb074_alpha_dummy_003), (nb074_alpha_dummy_004 x))]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.refl_of_closed [((nb074_alpha_dummy_119), (nb074_alpha_dummy_120 x)),
            ((nb074_alpha_dummy_088), (nb074_alpha_dummy_090 x)),
            ((nb074_alpha_dummy_087), (nb074_alpha_dummy_089 x)),
            ((nb074_alpha_dummy_117), (nb074_alpha_dummy_118 x)),
            ((nb074_alpha_dummy_091), (nb074_alpha_dummy_092 x)),
            ((nb074_alpha_dummy_082), (nb074_alpha_dummy_084 x)),
            ((nb074_alpha_dummy_081), (nb074_alpha_dummy_083 x)),
            ((nb074_alpha_dummy_085), (nb074_alpha_dummy_086 x)),
            ((nb074_alpha_dummy_042), (nb074_alpha_dummy_044 x)),
            ((nb074_alpha_dummy_041), (nb074_alpha_dummy_043 x)),
            ((nb074_alpha_dummy_001), (nb074_alpha_dummy_002 x)), ((nb074_alpha_dummy_000), x),
            ((nb074_alpha_dummy_003), (nb074_alpha_dummy_004 x))]
          (syn_ccompl (syn_csn (syn_c0c)))
          (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C074C001Part011`. -/


section

namespace NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

open scoped Fol
open NFChoice.Foundation
open NFChoice.Foundation.ExactLiteralTrial
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax
open NFChoice.Compiler.CompactSyntaxFVExplicit
open NFChoice.Compiler.WPPCompactSyntaxFVExplicit
open NFChoice.Compiler.CoreFVSimp
open NFChoice.DefinitionLeaves.AlphaFocusedSupport
open NFChoice.DefinitionLeaves.AlphaFocusedFV
open NFChoice.DirectNominalPrf
open NFChoice.DirectNominalPrf.Nominal

@[expose]
noncomputable def nb074_split_alpha_0007 (x : Var) :
    TAlphaWff
      [((nb074_alpha_dummy_129), (nb074_alpha_dummy_130 x)),
        ((nb074_alpha_dummy_127), (nb074_alpha_dummy_128 x)),
        ((nb074_alpha_dummy_082), (nb074_alpha_dummy_084 x)),
        ((nb074_alpha_dummy_081), (nb074_alpha_dummy_083 x)),
        ((nb074_alpha_dummy_085), (nb074_alpha_dummy_086 x)),
        ((nb074_alpha_dummy_042), (nb074_alpha_dummy_044 x)),
        ((nb074_alpha_dummy_041), (nb074_alpha_dummy_043 x)),
        ((nb074_alpha_dummy_001), (nb074_alpha_dummy_002 x)),
        ((nb074_alpha_dummy_000), x),
        ((nb074_alpha_dummy_003), (nb074_alpha_dummy_004 x))]
      (Wff.imp (Wff.classMem (Class.cv (nb074_alpha_dummy_129))
          (Class.cab (nb074_alpha_dummy_123)
            (syn_wrex (nb074_alpha_dummy_124) (Class.cv (nb074_alpha_dummy_082))
              (Wff.classEq (Class.cv (nb074_alpha_dummy_123))
                (syn_cphi (Class.cv (nb074_alpha_dummy_124))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb074_alpha_dummy_129)) (Class.cab (nb074_alpha_dummy_123)
              (syn_wrex (nb074_alpha_dummy_124) (Class.cv (nb074_alpha_dummy_082))
                (Wff.classEq (Class.cv (nb074_alpha_dummy_123))
                  (syn_cphi (Class.cv (nb074_alpha_dummy_124)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb074_alpha_dummy_130 x))
          (Class.cab (nb074_alpha_dummy_125 x)
            (syn_wrex (nb074_alpha_dummy_126 x) (Class.cv (nb074_alpha_dummy_084 x))
              (Wff.classEq (Class.cv (nb074_alpha_dummy_125 x))
                (syn_cphi (Class.cv (nb074_alpha_dummy_126 x))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb074_alpha_dummy_130 x))
            (Class.cab (nb074_alpha_dummy_125 x)
              (syn_wrex (nb074_alpha_dummy_126 x) (Class.cv (nb074_alpha_dummy_084 x))
                (Wff.classEq (Class.cv (nb074_alpha_dummy_125 x))
                  (syn_cphi (Class.cv (nb074_alpha_dummy_126 x))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb074_alpha_dummy_082) ≠ (nb074_alpha_dummy_124) from
                    (by
                      unfold nb074_alpha_dummy_124;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0124) 1))))
                  (show (nb074_alpha_dummy_084 x) ≠ (nb074_alpha_dummy_126 x) from (by
                      unfold nb074_alpha_dummy_126;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0126 x) 1))))
                  (TAlphaVar.there (show (nb074_alpha_dummy_082) ≠ (nb074_alpha_dummy_123) from
                      (by
                        unfold nb074_alpha_dummy_123;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0124) 0))))
                    (show (nb074_alpha_dummy_084 x) ≠ (nb074_alpha_dummy_125 x) from (by
                        unfold nb074_alpha_dummy_125;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb074_support_mem_0126 x) 0)))) (TAlphaVar.there
                      (show (nb074_alpha_dummy_082) ≠ (nb074_alpha_dummy_129) from (by
                          unfold nb074_alpha_dummy_129;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb074_support_mem_0128) 0))))
                      (show (nb074_alpha_dummy_084 x) ≠ (nb074_alpha_dummy_130 x) from (by
                          unfold nb074_alpha_dummy_130;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb074_support_mem_0129 x) 0))))
                      (TAlphaVar.there
                        (show (nb074_alpha_dummy_082) ≠ (nb074_alpha_dummy_127) from (by
                            unfold nb074_alpha_dummy_127;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb074_support_mem_0125) 0))))
                        (show (nb074_alpha_dummy_084 x) ≠ (nb074_alpha_dummy_128 x) from (by
                            unfold nb074_alpha_dummy_128;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb074_support_mem_0127 x) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb074_alpha_dummy_082))).fv ∪
                      ((Class.cv (nb074_alpha_dummy_081))).fv) (by decide)) (freshVar_injective
                    (((Class.cv (nb074_alpha_dummy_084 x))).fv ∪
                      ((Class.cv (nb074_alpha_dummy_083 x))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb074_alpha_dummy_124) ≠ (nb074_alpha_dummy_131) from (by
                              unfold nb074_alpha_dummy_131;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb074_support_mem_0130) 0))))
                          (show (nb074_alpha_dummy_126 x) ≠ (nb074_alpha_dummy_133 x) from (by
                              unfold nb074_alpha_dummy_133;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb074_support_mem_0131 x) 0))))
                          (TAlphaVar.there
                            (show (nb074_alpha_dummy_124) ≠ (nb074_alpha_dummy_132) from (by
                                unfold nb074_alpha_dummy_132;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb074_support_mem_0130) 1))))
                            (show (nb074_alpha_dummy_126 x) ≠ (nb074_alpha_dummy_134 x) from (by
                                unfold nb074_alpha_dummy_134;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb074_support_mem_0131 x) 1))))
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb074_alpha_dummy_124))).fv)
                            (by decide))
                          (freshVar_injective (((Class.cv (nb074_alpha_dummy_126 x))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb074_alpha_dummy_131) ≠ (nb074_alpha_dummy_138) from (by
          unfold nb074_alpha_dummy_138;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0134) 1)))) (show (nb074_alpha_dummy_133 x) ≠
        (nb074_alpha_dummy_141 x) from (by
          unfold nb074_alpha_dummy_141;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0135 x) 1)))) (TAlphaVar.there (show
        (nb074_alpha_dummy_131) ≠ (nb074_alpha_dummy_137) from (by
          unfold nb074_alpha_dummy_137;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0134) 0)))) (show (nb074_alpha_dummy_133 x) ≠
        (nb074_alpha_dummy_140 x) from (by
          unfold nb074_alpha_dummy_140;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0135 x) 0)))) (TAlphaVar.there (show
        (nb074_alpha_dummy_131) ≠ (nb074_alpha_dummy_135) from (by
          unfold nb074_alpha_dummy_135;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0132) 0)))) (show (nb074_alpha_dummy_133 x) ≠
        (nb074_alpha_dummy_136 x) from (by
          unfold nb074_alpha_dummy_136;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0133 x)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb074_alpha_dummy_139), (nb074_alpha_dummy_142 x)), ((nb074_alpha_dummy_138),
        (nb074_alpha_dummy_141 x)), ((nb074_alpha_dummy_137), (nb074_alpha_dummy_140 x)),
        ((nb074_alpha_dummy_135), (nb074_alpha_dummy_136 x)), ((nb074_alpha_dummy_131),
        (nb074_alpha_dummy_133 x)), ((nb074_alpha_dummy_132), (nb074_alpha_dummy_134 x)),
        ((nb074_alpha_dummy_124), (nb074_alpha_dummy_126 x)), ((nb074_alpha_dummy_123),
        (nb074_alpha_dummy_125 x)), ((nb074_alpha_dummy_129), (nb074_alpha_dummy_130 x)),
        ((nb074_alpha_dummy_127), (nb074_alpha_dummy_128 x)), ((nb074_alpha_dummy_082),
        (nb074_alpha_dummy_084 x)), ((nb074_alpha_dummy_081), (nb074_alpha_dummy_083 x)),
        ((nb074_alpha_dummy_085), (nb074_alpha_dummy_086 x)), ((nb074_alpha_dummy_042),
        (nb074_alpha_dummy_044 x)), ((nb074_alpha_dummy_041), (nb074_alpha_dummy_043 x)),
        ((nb074_alpha_dummy_001), (nb074_alpha_dummy_002 x)), ((nb074_alpha_dummy_000), x),
        ((nb074_alpha_dummy_003), (nb074_alpha_dummy_004 x))]
        (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb074_alpha_dummy_138) ≠ (nb074_alpha_dummy_145) from (by
          unfold
            nb074_alpha_dummy_145;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0138)
                  0)))) (show (nb074_alpha_dummy_141 x) ≠ (nb074_alpha_dummy_146 x) from (by
          unfold
            nb074_alpha_dummy_146;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0139
                    x)
                  0)))) (TAlphaVar.there (show (nb074_alpha_dummy_138) ≠ (nb074_alpha_dummy_143)
        from (by
          unfold
            nb074_alpha_dummy_143;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0136)
                  0)))) (show (nb074_alpha_dummy_141 x) ≠ (nb074_alpha_dummy_144 x) from (by
          unfold
            nb074_alpha_dummy_144;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0137
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb074_alpha_dummy_131))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb074_alpha_dummy_133 x))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb074_alpha_dummy_139) ≠ (nb074_alpha_dummy_145)
        from (by
          unfold
            nb074_alpha_dummy_145;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0142)
                  0)))) (show (nb074_alpha_dummy_142 x) ≠ (nb074_alpha_dummy_146 x) from (by
          unfold
            nb074_alpha_dummy_146;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0143
                    x)
                  0)))) (TAlphaVar.there (show (nb074_alpha_dummy_139) ≠ (nb074_alpha_dummy_143)
        from (by
          unfold
            nb074_alpha_dummy_143;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0140)
                  0)))) (show (nb074_alpha_dummy_142 x) ≠ (nb074_alpha_dummy_144 x) from (by
          unfold
            nb074_alpha_dummy_144;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0141
                    x)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb074_alpha_dummy_138) ≠ (nb074_alpha_dummy_145) from (by
          unfold
            nb074_alpha_dummy_145;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0138)
                  0)))) (show (nb074_alpha_dummy_141 x) ≠ (nb074_alpha_dummy_146 x) from (by
          unfold
            nb074_alpha_dummy_146;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0139
                    x)
                  0)))) (TAlphaVar.there (show (nb074_alpha_dummy_138) ≠ (nb074_alpha_dummy_143)
        from (by
          unfold
            nb074_alpha_dummy_143;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0136)
                  0)))) (show (nb074_alpha_dummy_141 x) ≠ (nb074_alpha_dummy_144 x) from (by
          unfold
            nb074_alpha_dummy_144;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0137
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb074_alpha_dummy_131))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb074_alpha_dummy_133 x))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb074_alpha_dummy_139) ≠ (nb074_alpha_dummy_145)
        from (by
          unfold
            nb074_alpha_dummy_145;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0142)
                  0)))) (show (nb074_alpha_dummy_142 x) ≠ (nb074_alpha_dummy_146 x) from (by
          unfold
            nb074_alpha_dummy_146;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0143
                    x)
                  0)))) (TAlphaVar.there (show (nb074_alpha_dummy_139) ≠ (nb074_alpha_dummy_143)
        from (by
          unfold
            nb074_alpha_dummy_143;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0140)
                  0)))) (show (nb074_alpha_dummy_142 x) ≠ (nb074_alpha_dummy_144 x) from (by
          unfold
            nb074_alpha_dummy_144;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0141
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb074_alpha_dummy_139), (nb074_alpha_dummy_142 x)), ((nb074_alpha_dummy_138),
        (nb074_alpha_dummy_141 x)), ((nb074_alpha_dummy_137), (nb074_alpha_dummy_140 x)),
        ((nb074_alpha_dummy_135), (nb074_alpha_dummy_136 x)), ((nb074_alpha_dummy_131),
        (nb074_alpha_dummy_133 x)), ((nb074_alpha_dummy_132), (nb074_alpha_dummy_134 x)),
        ((nb074_alpha_dummy_124), (nb074_alpha_dummy_126 x)), ((nb074_alpha_dummy_123),
        (nb074_alpha_dummy_125 x)), ((nb074_alpha_dummy_129), (nb074_alpha_dummy_130 x)),
        ((nb074_alpha_dummy_127), (nb074_alpha_dummy_128 x)), ((nb074_alpha_dummy_082),
        (nb074_alpha_dummy_084 x)), ((nb074_alpha_dummy_081), (nb074_alpha_dummy_083 x)),
        ((nb074_alpha_dummy_085), (nb074_alpha_dummy_086 x)), ((nb074_alpha_dummy_042),
        (nb074_alpha_dummy_044 x)), ((nb074_alpha_dummy_041), (nb074_alpha_dummy_043 x)),
        ((nb074_alpha_dummy_001), (nb074_alpha_dummy_002 x)), ((nb074_alpha_dummy_000), x),
        ((nb074_alpha_dummy_003), (nb074_alpha_dummy_004 x))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb074_alpha_dummy_131))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb074_alpha_dummy_133 x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb074_alpha_dummy_131))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb074_alpha_dummy_133 x))).fv ∪
        ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb074_alpha_dummy_138) ≠
        (nb074_alpha_dummy_149) from (by
          unfold
            nb074_alpha_dummy_149;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0146)
                  0)))) (show (nb074_alpha_dummy_141 x) ≠ (nb074_alpha_dummy_150 x) from (by
          unfold
            nb074_alpha_dummy_150;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0147
                    x)
                  0)))) (TAlphaVar.there (show (nb074_alpha_dummy_138) ≠ (nb074_alpha_dummy_147)
        from (by
          unfold
            nb074_alpha_dummy_147;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0144)
                  0)))) (show (nb074_alpha_dummy_141 x) ≠ (nb074_alpha_dummy_148 x) from (by
          unfold
            nb074_alpha_dummy_148;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0145
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb074_alpha_dummy_131))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb074_alpha_dummy_133 x))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb074_alpha_dummy_138) ≠ (nb074_alpha_dummy_149)
        from (by
          unfold
            nb074_alpha_dummy_149;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0146)
                  0)))) (show (nb074_alpha_dummy_141 x) ≠ (nb074_alpha_dummy_150 x) from (by
          unfold
            nb074_alpha_dummy_150;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0147
                    x)
                  0)))) (TAlphaVar.there (show (nb074_alpha_dummy_138) ≠ (nb074_alpha_dummy_147)
        from (by
          unfold
            nb074_alpha_dummy_147;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0144)
                  0)))) (show (nb074_alpha_dummy_141 x) ≠ (nb074_alpha_dummy_148 x) from (by
          unfold
            nb074_alpha_dummy_148;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0145
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb074_alpha_dummy_131))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb074_alpha_dummy_133 x))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb074_alpha_dummy_139) ≠ (nb074_alpha_dummy_151) from (by
          unfold
            nb074_alpha_dummy_151;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0150)
                  0)))) (show (nb074_alpha_dummy_142 x) ≠ (nb074_alpha_dummy_152 x) from (by
          unfold
            nb074_alpha_dummy_152;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0151
                    x)
                  0)))) (TAlphaVar.there (show (nb074_alpha_dummy_139) ≠ (nb074_alpha_dummy_147)
        from (by
          unfold
            nb074_alpha_dummy_147;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0148)
                  0)))) (show (nb074_alpha_dummy_142 x) ≠ (nb074_alpha_dummy_148 x) from (by
          unfold
            nb074_alpha_dummy_148;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0149
                    x)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb074_alpha_dummy_139) ≠
        (nb074_alpha_dummy_151) from (by
          unfold
            nb074_alpha_dummy_151;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0150)
                  0)))) (show (nb074_alpha_dummy_142 x) ≠ (nb074_alpha_dummy_152 x) from (by
          unfold
            nb074_alpha_dummy_152;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0151
                    x)
                  0)))) (TAlphaVar.there (show (nb074_alpha_dummy_139) ≠ (nb074_alpha_dummy_147)
        from (by
          unfold
            nb074_alpha_dummy_147;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0148)
                  0)))) (show (nb074_alpha_dummy_142 x) ≠ (nb074_alpha_dummy_148 x) from (by
          unfold
            nb074_alpha_dummy_148;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0149
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb074_alpha_dummy_131) ≠ (nb074_alpha_dummy_135) from (by
                                        unfold nb074_alpha_dummy_135;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb074_support_mem_0132)
                                                0)))) (show (nb074_alpha_dummy_133 x) ≠
                                        (nb074_alpha_dummy_136 x) from (by
                                        unfold nb074_alpha_dummy_136;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb074_support_mem_0133 x)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
                                  [((nb074_alpha_dummy_135), (nb074_alpha_dummy_136 x)),
                                    ((nb074_alpha_dummy_131), (nb074_alpha_dummy_133 x)),
                                    ((nb074_alpha_dummy_132), (nb074_alpha_dummy_134 x)),
                                    ((nb074_alpha_dummy_124), (nb074_alpha_dummy_126 x)),
                                    ((nb074_alpha_dummy_123), (nb074_alpha_dummy_125 x)),
                                    ((nb074_alpha_dummy_129), (nb074_alpha_dummy_130 x)),
                                    ((nb074_alpha_dummy_127), (nb074_alpha_dummy_128 x)),
                                    ((nb074_alpha_dummy_082), (nb074_alpha_dummy_084 x)),
                                    ((nb074_alpha_dummy_081), (nb074_alpha_dummy_083 x)),
                                    ((nb074_alpha_dummy_085), (nb074_alpha_dummy_086 x)),
                                    ((nb074_alpha_dummy_042), (nb074_alpha_dummy_044 x)),
                                    ((nb074_alpha_dummy_041), (nb074_alpha_dummy_043 x)),
                                    ((nb074_alpha_dummy_001), (nb074_alpha_dummy_002 x)),
                                    ((nb074_alpha_dummy_000), x),
                                    ((nb074_alpha_dummy_003), (nb074_alpha_dummy_004 x))]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb074_alpha_dummy_131) ≠ (nb074_alpha_dummy_135) from
                                    (by
                                      unfold nb074_alpha_dummy_135;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb074_support_mem_0132)
                                              0)))) (show
                                    (nb074_alpha_dummy_133 x) ≠ (nb074_alpha_dummy_136 x) from
                                    (by
                                      unfold nb074_alpha_dummy_136;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb074_support_mem_0133 x)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb074_alpha_dummy_131) ≠ (nb074_alpha_dummy_135) from (by
                                        unfold nb074_alpha_dummy_135;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb074_support_mem_0132)
                                                0)))) (show (nb074_alpha_dummy_133 x) ≠
                                        (nb074_alpha_dummy_136 x) from (by
                                        unfold nb074_alpha_dummy_136;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb074_support_mem_0133 x)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
                                  [((nb074_alpha_dummy_135), (nb074_alpha_dummy_136 x)),
                                    ((nb074_alpha_dummy_131), (nb074_alpha_dummy_133 x)),
                                    ((nb074_alpha_dummy_132), (nb074_alpha_dummy_134 x)),
                                    ((nb074_alpha_dummy_124), (nb074_alpha_dummy_126 x)),
                                    ((nb074_alpha_dummy_123), (nb074_alpha_dummy_125 x)),
                                    ((nb074_alpha_dummy_129), (nb074_alpha_dummy_130 x)),
                                    ((nb074_alpha_dummy_127), (nb074_alpha_dummy_128 x)),
                                    ((nb074_alpha_dummy_082), (nb074_alpha_dummy_084 x)),
                                    ((nb074_alpha_dummy_081), (nb074_alpha_dummy_083 x)),
                                    ((nb074_alpha_dummy_085), (nb074_alpha_dummy_086 x)),
                                    ((nb074_alpha_dummy_042), (nb074_alpha_dummy_044 x)),
                                    ((nb074_alpha_dummy_041), (nb074_alpha_dummy_043 x)),
                                    ((nb074_alpha_dummy_001), (nb074_alpha_dummy_002 x)),
                                    ((nb074_alpha_dummy_000), x),
                                    ((nb074_alpha_dummy_003), (nb074_alpha_dummy_004 x))]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb074_alpha_dummy_082) ≠ (nb074_alpha_dummy_124) from
                      (by
                        unfold nb074_alpha_dummy_124;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb074_support_mem_0124) 1))))
                    (show (nb074_alpha_dummy_084 x) ≠ (nb074_alpha_dummy_126 x) from (by
                        unfold nb074_alpha_dummy_126;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb074_support_mem_0126 x) 1)))) (TAlphaVar.there
                      (show (nb074_alpha_dummy_082) ≠ (nb074_alpha_dummy_123) from (by
                          unfold nb074_alpha_dummy_123;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb074_support_mem_0124) 0))))
                      (show (nb074_alpha_dummy_084 x) ≠ (nb074_alpha_dummy_125 x) from (by
                          unfold nb074_alpha_dummy_125;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb074_support_mem_0126 x) 0))))
                      (TAlphaVar.there
                        (show (nb074_alpha_dummy_082) ≠ (nb074_alpha_dummy_129) from (by
                            unfold nb074_alpha_dummy_129;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb074_support_mem_0128) 0))))
                        (show (nb074_alpha_dummy_084 x) ≠ (nb074_alpha_dummy_130 x) from (by
                            unfold nb074_alpha_dummy_130;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb074_support_mem_0129 x) 0))))
                        (TAlphaVar.there
                          (show (nb074_alpha_dummy_082) ≠ (nb074_alpha_dummy_127) from (by
                              unfold nb074_alpha_dummy_127;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb074_support_mem_0125) 0))))
                          (show (nb074_alpha_dummy_084 x) ≠ (nb074_alpha_dummy_128 x) from (by
                              unfold nb074_alpha_dummy_128;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb074_support_mem_0127 x) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb074_alpha_dummy_082))).fv ∪
                        ((Class.cv (nb074_alpha_dummy_081))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb074_alpha_dummy_084 x))).fv ∪
                        ((Class.cv (nb074_alpha_dummy_083 x))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb074_alpha_dummy_124) ≠ (nb074_alpha_dummy_131) from (by
                                unfold nb074_alpha_dummy_131;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb074_support_mem_0130) 0))))
                            (show (nb074_alpha_dummy_126 x) ≠ (nb074_alpha_dummy_133 x) from (by
                                unfold nb074_alpha_dummy_133;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb074_support_mem_0131 x) 0))))
                            (TAlphaVar.there
                              (show (nb074_alpha_dummy_124) ≠ (nb074_alpha_dummy_132) from (by
                                  unfold nb074_alpha_dummy_132;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb074_support_mem_0130) 1))))
                              (show (nb074_alpha_dummy_126 x) ≠ (nb074_alpha_dummy_134 x) from
                                (by
                                  unfold nb074_alpha_dummy_134;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb074_support_mem_0131 x) 1))))
                              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there
                            (freshVar_injective (((Class.cv (nb074_alpha_dummy_124))).fv)
                              (by decide)) (freshVar_injective
                              (((Class.cv (nb074_alpha_dummy_126 x))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb074_alpha_dummy_131) ≠ (nb074_alpha_dummy_138) from (by
          unfold nb074_alpha_dummy_138;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0134) 1)))) (show (nb074_alpha_dummy_133 x) ≠
        (nb074_alpha_dummy_141 x) from (by
          unfold nb074_alpha_dummy_141;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0135 x) 1)))) (TAlphaVar.there (show
        (nb074_alpha_dummy_131) ≠ (nb074_alpha_dummy_137) from (by
          unfold nb074_alpha_dummy_137;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0134) 0)))) (show (nb074_alpha_dummy_133 x) ≠
        (nb074_alpha_dummy_140 x) from (by
          unfold nb074_alpha_dummy_140;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0135 x)
                  0)))) (TAlphaVar.there (show (nb074_alpha_dummy_131) ≠ (nb074_alpha_dummy_135)
        from (by
          unfold nb074_alpha_dummy_135;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0132)
                  0)))) (show (nb074_alpha_dummy_133 x) ≠ (nb074_alpha_dummy_136 x) from (by
          unfold nb074_alpha_dummy_136;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0133 x)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb074_alpha_dummy_139), (nb074_alpha_dummy_142 x)), ((nb074_alpha_dummy_138),
        (nb074_alpha_dummy_141 x)), ((nb074_alpha_dummy_137), (nb074_alpha_dummy_140 x)),
        ((nb074_alpha_dummy_135), (nb074_alpha_dummy_136 x)), ((nb074_alpha_dummy_131),
        (nb074_alpha_dummy_133 x)), ((nb074_alpha_dummy_132), (nb074_alpha_dummy_134 x)),
        ((nb074_alpha_dummy_124), (nb074_alpha_dummy_126 x)), ((nb074_alpha_dummy_123),
        (nb074_alpha_dummy_125 x)), ((nb074_alpha_dummy_129), (nb074_alpha_dummy_130 x)),
        ((nb074_alpha_dummy_127), (nb074_alpha_dummy_128 x)), ((nb074_alpha_dummy_082),
        (nb074_alpha_dummy_084 x)), ((nb074_alpha_dummy_081), (nb074_alpha_dummy_083 x)),
        ((nb074_alpha_dummy_085), (nb074_alpha_dummy_086 x)), ((nb074_alpha_dummy_042),
        (nb074_alpha_dummy_044 x)), ((nb074_alpha_dummy_041), (nb074_alpha_dummy_043 x)),
        ((nb074_alpha_dummy_001), (nb074_alpha_dummy_002 x)), ((nb074_alpha_dummy_000), x),
        ((nb074_alpha_dummy_003), (nb074_alpha_dummy_004 x))]
        (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb074_alpha_dummy_138) ≠ (nb074_alpha_dummy_145) from (by
          unfold
            nb074_alpha_dummy_145;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0138)
                  0)))) (show (nb074_alpha_dummy_141 x) ≠ (nb074_alpha_dummy_146 x) from (by
          unfold
            nb074_alpha_dummy_146;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0139
                    x)
                  0)))) (TAlphaVar.there (show (nb074_alpha_dummy_138) ≠ (nb074_alpha_dummy_143)
        from (by
          unfold
            nb074_alpha_dummy_143;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0136)
                  0)))) (show (nb074_alpha_dummy_141 x) ≠ (nb074_alpha_dummy_144 x) from (by
          unfold
            nb074_alpha_dummy_144;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0137
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb074_alpha_dummy_131))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb074_alpha_dummy_133 x))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb074_alpha_dummy_139) ≠ (nb074_alpha_dummy_145)
        from (by
          unfold
            nb074_alpha_dummy_145;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0142)
                  0)))) (show (nb074_alpha_dummy_142 x) ≠ (nb074_alpha_dummy_146 x) from (by
          unfold
            nb074_alpha_dummy_146;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0143
                    x)
                  0)))) (TAlphaVar.there (show (nb074_alpha_dummy_139) ≠ (nb074_alpha_dummy_143)
        from (by
          unfold
            nb074_alpha_dummy_143;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0140)
                  0)))) (show (nb074_alpha_dummy_142 x) ≠ (nb074_alpha_dummy_144 x) from (by
          unfold
            nb074_alpha_dummy_144;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0141
                    x)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb074_alpha_dummy_138) ≠ (nb074_alpha_dummy_145) from (by
          unfold
            nb074_alpha_dummy_145;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0138)
                  0)))) (show (nb074_alpha_dummy_141 x) ≠ (nb074_alpha_dummy_146 x) from (by
          unfold
            nb074_alpha_dummy_146;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0139
                    x)
                  0)))) (TAlphaVar.there (show (nb074_alpha_dummy_138) ≠ (nb074_alpha_dummy_143)
        from (by
          unfold
            nb074_alpha_dummy_143;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0136)
                  0)))) (show (nb074_alpha_dummy_141 x) ≠ (nb074_alpha_dummy_144 x) from (by
          unfold
            nb074_alpha_dummy_144;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0137
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb074_alpha_dummy_131))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb074_alpha_dummy_133 x))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb074_alpha_dummy_139) ≠ (nb074_alpha_dummy_145)
        from (by
          unfold
            nb074_alpha_dummy_145;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0142)
                  0)))) (show (nb074_alpha_dummy_142 x) ≠ (nb074_alpha_dummy_146 x) from (by
          unfold
            nb074_alpha_dummy_146;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0143
                    x)
                  0)))) (TAlphaVar.there (show (nb074_alpha_dummy_139) ≠ (nb074_alpha_dummy_143)
        from (by
          unfold
            nb074_alpha_dummy_143;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0140)
                  0)))) (show (nb074_alpha_dummy_142 x) ≠ (nb074_alpha_dummy_144 x) from (by
          unfold
            nb074_alpha_dummy_144;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0141
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb074_alpha_dummy_139), (nb074_alpha_dummy_142 x)), ((nb074_alpha_dummy_138),
        (nb074_alpha_dummy_141 x)), ((nb074_alpha_dummy_137), (nb074_alpha_dummy_140 x)),
        ((nb074_alpha_dummy_135), (nb074_alpha_dummy_136 x)), ((nb074_alpha_dummy_131),
        (nb074_alpha_dummy_133 x)), ((nb074_alpha_dummy_132), (nb074_alpha_dummy_134 x)),
        ((nb074_alpha_dummy_124), (nb074_alpha_dummy_126 x)), ((nb074_alpha_dummy_123),
        (nb074_alpha_dummy_125 x)), ((nb074_alpha_dummy_129), (nb074_alpha_dummy_130 x)),
        ((nb074_alpha_dummy_127), (nb074_alpha_dummy_128 x)), ((nb074_alpha_dummy_082),
        (nb074_alpha_dummy_084 x)), ((nb074_alpha_dummy_081), (nb074_alpha_dummy_083 x)),
        ((nb074_alpha_dummy_085), (nb074_alpha_dummy_086 x)), ((nb074_alpha_dummy_042),
        (nb074_alpha_dummy_044 x)), ((nb074_alpha_dummy_041), (nb074_alpha_dummy_043 x)),
        ((nb074_alpha_dummy_001), (nb074_alpha_dummy_002 x)), ((nb074_alpha_dummy_000), x),
        ((nb074_alpha_dummy_003), (nb074_alpha_dummy_004 x))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb074_alpha_dummy_131))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb074_alpha_dummy_133
        x))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb074_alpha_dummy_131))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb074_alpha_dummy_133 x))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb074_alpha_dummy_138) ≠
        (nb074_alpha_dummy_149) from (by
          unfold
            nb074_alpha_dummy_149;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0146)
                  0)))) (show (nb074_alpha_dummy_141 x) ≠ (nb074_alpha_dummy_150 x) from (by
          unfold
            nb074_alpha_dummy_150;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0147
                    x)
                  0)))) (TAlphaVar.there (show (nb074_alpha_dummy_138) ≠ (nb074_alpha_dummy_147)
        from (by
          unfold
            nb074_alpha_dummy_147;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0144)
                  0)))) (show (nb074_alpha_dummy_141 x) ≠ (nb074_alpha_dummy_148 x) from (by
          unfold
            nb074_alpha_dummy_148;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0145
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb074_alpha_dummy_131))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb074_alpha_dummy_133 x))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb074_alpha_dummy_138) ≠ (nb074_alpha_dummy_149)
        from (by
          unfold
            nb074_alpha_dummy_149;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0146)
                  0)))) (show (nb074_alpha_dummy_141 x) ≠ (nb074_alpha_dummy_150 x) from (by
          unfold
            nb074_alpha_dummy_150;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0147
                    x)
                  0)))) (TAlphaVar.there (show (nb074_alpha_dummy_138) ≠ (nb074_alpha_dummy_147)
        from (by
          unfold
            nb074_alpha_dummy_147;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0144)
                  0)))) (show (nb074_alpha_dummy_141 x) ≠ (nb074_alpha_dummy_148 x) from (by
          unfold
            nb074_alpha_dummy_148;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0145
                    x)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb074_alpha_dummy_131))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb074_alpha_dummy_133 x))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb074_alpha_dummy_139) ≠ (nb074_alpha_dummy_151) from (by
          unfold
            nb074_alpha_dummy_151;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0150)
                  0)))) (show (nb074_alpha_dummy_142 x) ≠ (nb074_alpha_dummy_152 x) from (by
          unfold
            nb074_alpha_dummy_152;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0151
                    x)
                  0)))) (TAlphaVar.there (show (nb074_alpha_dummy_139) ≠ (nb074_alpha_dummy_147)
        from (by
          unfold
            nb074_alpha_dummy_147;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0148)
                  0)))) (show (nb074_alpha_dummy_142 x) ≠ (nb074_alpha_dummy_148 x) from (by
          unfold
            nb074_alpha_dummy_148;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0149
                    x)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb074_alpha_dummy_139) ≠
        (nb074_alpha_dummy_151) from (by
          unfold
            nb074_alpha_dummy_151;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0150)
                  0)))) (show (nb074_alpha_dummy_142 x) ≠ (nb074_alpha_dummy_152 x) from (by
          unfold
            nb074_alpha_dummy_152;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0151
                    x)
                  0)))) (TAlphaVar.there (show (nb074_alpha_dummy_139) ≠ (nb074_alpha_dummy_147)
        from (by
          unfold
            nb074_alpha_dummy_147;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0148)
                  0)))) (show (nb074_alpha_dummy_142 x) ≠ (nb074_alpha_dummy_148 x) from (by
          unfold
            nb074_alpha_dummy_148;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb074_support_mem_0149
                    x)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb074_alpha_dummy_131) ≠ (nb074_alpha_dummy_135) from
                                        (by
                                          unfold nb074_alpha_dummy_135;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb074_support_mem_0132)
                                                  0)))) (show (nb074_alpha_dummy_133 x) ≠
        (nb074_alpha_dummy_136 x) from (by
                                          unfold nb074_alpha_dummy_136;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb074_support_mem_0133 x) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb074_alpha_dummy_135), (nb074_alpha_dummy_136 x)),
                                      ((nb074_alpha_dummy_131), (nb074_alpha_dummy_133 x)),
                                      ((nb074_alpha_dummy_132), (nb074_alpha_dummy_134 x)),
                                      ((nb074_alpha_dummy_124), (nb074_alpha_dummy_126 x)),
                                      ((nb074_alpha_dummy_123), (nb074_alpha_dummy_125 x)),
                                      ((nb074_alpha_dummy_129), (nb074_alpha_dummy_130 x)),
                                      ((nb074_alpha_dummy_127), (nb074_alpha_dummy_128 x)),
                                      ((nb074_alpha_dummy_082), (nb074_alpha_dummy_084 x)),
                                      ((nb074_alpha_dummy_081), (nb074_alpha_dummy_083 x)),
                                      ((nb074_alpha_dummy_085), (nb074_alpha_dummy_086 x)),
                                      ((nb074_alpha_dummy_042), (nb074_alpha_dummy_044 x)),
                                      ((nb074_alpha_dummy_041), (nb074_alpha_dummy_043 x)),
                                      ((nb074_alpha_dummy_001), (nb074_alpha_dummy_002 x)),
                                      ((nb074_alpha_dummy_000), x), ((nb074_alpha_dummy_003),
                                        (nb074_alpha_dummy_004 x))]
                                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb074_alpha_dummy_131) ≠ (nb074_alpha_dummy_135) from (by
                                        unfold nb074_alpha_dummy_135;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb074_support_mem_0132)
                                                0)))) (show (nb074_alpha_dummy_133 x) ≠
                                        (nb074_alpha_dummy_136 x) from (by
                                        unfold nb074_alpha_dummy_136;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb074_support_mem_0133 x)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb074_alpha_dummy_131) ≠ (nb074_alpha_dummy_135) from
                                        (by
                                          unfold nb074_alpha_dummy_135;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb074_support_mem_0132)
                                                  0)))) (show (nb074_alpha_dummy_133 x) ≠
        (nb074_alpha_dummy_136 x) from (by
                                          unfold nb074_alpha_dummy_136;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb074_support_mem_0133 x) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb074_alpha_dummy_135), (nb074_alpha_dummy_136 x)),
                                      ((nb074_alpha_dummy_131), (nb074_alpha_dummy_133 x)),
                                      ((nb074_alpha_dummy_132), (nb074_alpha_dummy_134 x)),
                                      ((nb074_alpha_dummy_124), (nb074_alpha_dummy_126 x)),
                                      ((nb074_alpha_dummy_123), (nb074_alpha_dummy_125 x)),
                                      ((nb074_alpha_dummy_129), (nb074_alpha_dummy_130 x)),
                                      ((nb074_alpha_dummy_127), (nb074_alpha_dummy_128 x)),
                                      ((nb074_alpha_dummy_082), (nb074_alpha_dummy_084 x)),
                                      ((nb074_alpha_dummy_081), (nb074_alpha_dummy_083 x)),
                                      ((nb074_alpha_dummy_085), (nb074_alpha_dummy_086 x)),
                                      ((nb074_alpha_dummy_042), (nb074_alpha_dummy_044 x)),
                                      ((nb074_alpha_dummy_041), (nb074_alpha_dummy_043 x)),
                                      ((nb074_alpha_dummy_001), (nb074_alpha_dummy_002 x)),
                                      ((nb074_alpha_dummy_000), x), ((nb074_alpha_dummy_003),
                                        (nb074_alpha_dummy_004 x))] (syn_cnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
