/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C090C001Block007

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C090C001Part028`. -/


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
noncomputable def nb090_split_alpha_0004 (v : Var) (u : Var) (A : Class) (h : Var) :
    TAlphaWff
      [((nb090_alpha_dummy_127 A), (nb090_alpha_dummy_128 h)),
        ((nb090_alpha_dummy_125 A), (nb090_alpha_dummy_126 h)),
        ((nb090_alpha_dummy_094 A), (nb090_alpha_dummy_096 h)),
        ((nb090_alpha_dummy_093 A), (nb090_alpha_dummy_095 h)),
        ((nb090_alpha_dummy_123 A), (nb090_alpha_dummy_124 h)),
        ((nb090_alpha_dummy_097 A), (nb090_alpha_dummy_098 h)),
        ((nb090_alpha_dummy_051 A), (nb090_alpha_dummy_054 h)),
        ((nb090_alpha_dummy_050 A), (nb090_alpha_dummy_053 h)),
        ((nb090_alpha_dummy_049 A), (nb090_alpha_dummy_052 h)),
        ((nb090_alpha_dummy_055 A), (nb090_alpha_dummy_056 h)),
        ((nb090_alpha_dummy_047 A), (nb090_alpha_dummy_048 h)),
        ((nb090_alpha_dummy_045 A), (nb090_alpha_dummy_046 h)),
        ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
        ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
      (Wff.imp (Wff.classMem (Class.cv (nb090_alpha_dummy_127 A))
          (syn_cphi (Class.cv (nb090_alpha_dummy_094 A)))) (Wff.neg
          (Wff.classMem (Class.cv (nb090_alpha_dummy_127 A))
            (syn_cphi (Class.cv (nb090_alpha_dummy_094 A))))))
      (Wff.imp (Wff.classMem (Class.cv (nb090_alpha_dummy_128 h))
          (syn_cphi (Class.cv (nb090_alpha_dummy_096 h)))) (Wff.neg
          (Wff.classMem (Class.cv (nb090_alpha_dummy_128 h))
            (syn_cphi (Class.cv (nb090_alpha_dummy_096 h)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there
                  (show (nb090_alpha_dummy_094 A) ≠ (nb090_alpha_dummy_101 A) from (by
                      unfold nb090_alpha_dummy_101;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0090 A) 0))))
                  (show (nb090_alpha_dummy_096 h) ≠ (nb090_alpha_dummy_103 h) from (by
                      unfold nb090_alpha_dummy_103;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0091 h) 0))))
                  (TAlphaVar.there
                    (show (nb090_alpha_dummy_094 A) ≠ (nb090_alpha_dummy_102 A) from (by
                        unfold nb090_alpha_dummy_102;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0090 A) 1))))
                    (show (nb090_alpha_dummy_096 h) ≠ (nb090_alpha_dummy_104 h) from (by
                        unfold nb090_alpha_dummy_104;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0091 h) 1)))) (TAlphaVar.there
                      (show (nb090_alpha_dummy_094 A) ≠ (nb090_alpha_dummy_127 A) from (by
                          unfold nb090_alpha_dummy_127;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0120 A) 0))))
                      (show (nb090_alpha_dummy_096 h) ≠ (nb090_alpha_dummy_128 h) from (by
                          unfold nb090_alpha_dummy_128;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0121 h) 0))))
                      (TAlphaVar.there
                        (show (nb090_alpha_dummy_094 A) ≠ (nb090_alpha_dummy_125 A) from (by
                            unfold nb090_alpha_dummy_125;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0118 A) 0))))
                        (show (nb090_alpha_dummy_096 h) ≠ (nb090_alpha_dummy_126 h) from (by
                            unfold nb090_alpha_dummy_126;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0119 h) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_094 A))).fv)
                    (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_096 h))).fv)
                    (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090_alpha_dummy_101 A) ≠ (nb090_alpha_dummy_108 A) from
                                      (by
                                        unfold nb090_alpha_dummy_108;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0094 A)
                                                1)))) (show (nb090_alpha_dummy_103 h) ≠
                                        (nb090_alpha_dummy_111 h) from (by
                                        unfold nb090_alpha_dummy_111;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0095 h)
                                                1)))) (TAlphaVar.there (show
                                        (nb090_alpha_dummy_101 A) ≠ (nb090_alpha_dummy_107 A)
                                        from (by
                                          unfold nb090_alpha_dummy_107;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0094 A) 0)))) (show
                                        (nb090_alpha_dummy_103 h) ≠ (nb090_alpha_dummy_110 h)
                                        from (by
                                          unfold nb090_alpha_dummy_110;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0095 h) 0))))
                                      (TAlphaVar.there (show (nb090_alpha_dummy_101 A) ≠
        (nb090_alpha_dummy_105 A) from (by
          unfold nb090_alpha_dummy_105;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0092 A) 0)))) (show (nb090_alpha_dummy_103 h) ≠
        (nb090_alpha_dummy_106 h) from (by
          unfold nb090_alpha_dummy_106;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0093 h) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.refl_of_closed [((nb090_alpha_dummy_109 A),
        (nb090_alpha_dummy_112 h)), ((nb090_alpha_dummy_108 A), (nb090_alpha_dummy_111 h)),
                                        ((nb090_alpha_dummy_107 A), (nb090_alpha_dummy_110 h)),
                                        ((nb090_alpha_dummy_105 A), (nb090_alpha_dummy_106 h)),
                                        ((nb090_alpha_dummy_101 A), (nb090_alpha_dummy_103 h)),
                                        ((nb090_alpha_dummy_102 A), (nb090_alpha_dummy_104 h)),
                                        ((nb090_alpha_dummy_127 A), (nb090_alpha_dummy_128 h)),
                                        ((nb090_alpha_dummy_125 A), (nb090_alpha_dummy_126 h)),
                                        ((nb090_alpha_dummy_094 A), (nb090_alpha_dummy_096 h)),
                                        ((nb090_alpha_dummy_093 A), (nb090_alpha_dummy_095 h)),
                                        ((nb090_alpha_dummy_123 A), (nb090_alpha_dummy_124 h)),
                                        ((nb090_alpha_dummy_097 A), (nb090_alpha_dummy_098 h)),
                                        ((nb090_alpha_dummy_051 A), (nb090_alpha_dummy_054 h)),
                                        ((nb090_alpha_dummy_050 A), (nb090_alpha_dummy_053 h)),
                                        ((nb090_alpha_dummy_049 A), (nb090_alpha_dummy_052 h)),
                                        ((nb090_alpha_dummy_055 A), (nb090_alpha_dummy_056 h)),
                                        ((nb090_alpha_dummy_047 A), (nb090_alpha_dummy_048 h)),
                                        ((nb090_alpha_dummy_045 A), (nb090_alpha_dummy_046 h)),
                                        ((nb090_alpha_dummy_000 A), h),
                                        ((nb090_alpha_dummy_002 A), v),
                                        ((nb090_alpha_dummy_001 A), u),
                                        ((nb090_alpha_dummy_003 A),
        (nb090_alpha_dummy_004 v u A h))] (syn_c1c) (by simp only [fv_syn_c1c])))
                                  (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
                                        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_108 A) ≠ (nb090_alpha_dummy_115 A) from (by
          unfold
            nb090_alpha_dummy_115;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0098
                    A)
                  0)))) (show (nb090_alpha_dummy_111 h) ≠ (nb090_alpha_dummy_116 h) from (by
          unfold
            nb090_alpha_dummy_116;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0099
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_108 A) ≠
        (nb090_alpha_dummy_113 A) from (by
          unfold
            nb090_alpha_dummy_113;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0096
                    A)
                  0)))) (show (nb090_alpha_dummy_111 h) ≠ (nb090_alpha_dummy_114 h) from (by
          unfold
            nb090_alpha_dummy_114;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0097
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_101
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_103 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_109 A) ≠
        (nb090_alpha_dummy_115 A) from (by
          unfold
            nb090_alpha_dummy_115;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0102
                    A)
                  0)))) (show (nb090_alpha_dummy_112 h) ≠ (nb090_alpha_dummy_116 h) from (by
          unfold
            nb090_alpha_dummy_116;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0103
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_109 A) ≠
        (nb090_alpha_dummy_113 A) from (by
          unfold
            nb090_alpha_dummy_113;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0100
                    A)
                  0)))) (show (nb090_alpha_dummy_112 h) ≠ (nb090_alpha_dummy_114 h) from (by
          unfold
            nb090_alpha_dummy_114;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0101
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_108 A) ≠ (nb090_alpha_dummy_115 A) from (by
          unfold
            nb090_alpha_dummy_115;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0098
                    A)
                  0)))) (show (nb090_alpha_dummy_111 h) ≠ (nb090_alpha_dummy_116 h) from (by
          unfold
            nb090_alpha_dummy_116;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0099
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_108 A) ≠
        (nb090_alpha_dummy_113 A) from (by
          unfold
            nb090_alpha_dummy_113;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0096
                    A)
                  0)))) (show (nb090_alpha_dummy_111 h) ≠ (nb090_alpha_dummy_114 h) from (by
          unfold
            nb090_alpha_dummy_114;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0097
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_101
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_103 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_109 A) ≠
        (nb090_alpha_dummy_115 A) from (by
          unfold
            nb090_alpha_dummy_115;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0102
                    A)
                  0)))) (show (nb090_alpha_dummy_112 h) ≠ (nb090_alpha_dummy_116 h) from (by
          unfold
            nb090_alpha_dummy_116;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0103
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_109 A) ≠
        (nb090_alpha_dummy_113 A) from (by
          unfold
            nb090_alpha_dummy_113;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0100
                    A)
                  0)))) (show (nb090_alpha_dummy_112 h) ≠ (nb090_alpha_dummy_114 h) from (by
          unfold
            nb090_alpha_dummy_114;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0101
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
                                        [((nb090_alpha_dummy_109 A), (nb090_alpha_dummy_112 h)),
        ((nb090_alpha_dummy_108 A), (nb090_alpha_dummy_111 h)), ((nb090_alpha_dummy_107 A),
        (nb090_alpha_dummy_110 h)), ((nb090_alpha_dummy_105 A), (nb090_alpha_dummy_106 h)),
        ((nb090_alpha_dummy_101 A), (nb090_alpha_dummy_103 h)), ((nb090_alpha_dummy_102 A),
        (nb090_alpha_dummy_104 h)), ((nb090_alpha_dummy_127 A), (nb090_alpha_dummy_128 h)),
        ((nb090_alpha_dummy_125 A), (nb090_alpha_dummy_126 h)), ((nb090_alpha_dummy_094 A),
        (nb090_alpha_dummy_096 h)), ((nb090_alpha_dummy_093 A), (nb090_alpha_dummy_095 h)),
        ((nb090_alpha_dummy_123 A), (nb090_alpha_dummy_124 h)), ((nb090_alpha_dummy_097 A),
        (nb090_alpha_dummy_098 h)), ((nb090_alpha_dummy_051 A), (nb090_alpha_dummy_054 h)),
        ((nb090_alpha_dummy_050 A), (nb090_alpha_dummy_053 h)), ((nb090_alpha_dummy_049 A),
        (nb090_alpha_dummy_052 h)), ((nb090_alpha_dummy_055 A), (nb090_alpha_dummy_056 h)),
        ((nb090_alpha_dummy_047 A), (nb090_alpha_dummy_048 h)), ((nb090_alpha_dummy_045 A),
        (nb090_alpha_dummy_046 h)), ((nb090_alpha_dummy_000 A), h),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
                                        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
                                      (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb090_alpha_dummy_101 A))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb090_alpha_dummy_103 h))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb090_alpha_dummy_101 A))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb090_alpha_dummy_103 h))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090_alpha_dummy_108 A) ≠ (nb090_alpha_dummy_119 A) from (by
          unfold
            nb090_alpha_dummy_119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0106
                    A)
                  0)))) (show (nb090_alpha_dummy_111 h) ≠ (nb090_alpha_dummy_120 h) from (by
          unfold
            nb090_alpha_dummy_120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0107
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_108 A) ≠
        (nb090_alpha_dummy_117 A) from (by
          unfold
            nb090_alpha_dummy_117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0104
                    A)
                  0)))) (show (nb090_alpha_dummy_111 h) ≠ (nb090_alpha_dummy_118 h) from (by
          unfold
            nb090_alpha_dummy_118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0105
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_101
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_103 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_108 A) ≠
        (nb090_alpha_dummy_119 A) from (by
          unfold
            nb090_alpha_dummy_119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0106
                    A)
                  0)))) (show (nb090_alpha_dummy_111 h) ≠ (nb090_alpha_dummy_120 h) from (by
          unfold
            nb090_alpha_dummy_120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0107
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_108 A) ≠
        (nb090_alpha_dummy_117 A) from (by
          unfold
            nb090_alpha_dummy_117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0104
                    A)
                  0)))) (show (nb090_alpha_dummy_111 h) ≠ (nb090_alpha_dummy_118 h) from (by
          unfold
            nb090_alpha_dummy_118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0105
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_101
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_103 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090_alpha_dummy_109 A) ≠ (nb090_alpha_dummy_121 A) from (by
          unfold
            nb090_alpha_dummy_121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0110
                    A)
                  0)))) (show (nb090_alpha_dummy_112 h) ≠ (nb090_alpha_dummy_122 h) from (by
          unfold
            nb090_alpha_dummy_122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0111
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_109 A) ≠
        (nb090_alpha_dummy_117 A) from (by
          unfold
            nb090_alpha_dummy_117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0108
                    A)
                  0)))) (show (nb090_alpha_dummy_112 h) ≠ (nb090_alpha_dummy_118 h) from (by
          unfold
            nb090_alpha_dummy_118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0109
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090_alpha_dummy_109 A) ≠ (nb090_alpha_dummy_121 A) from (by
          unfold
            nb090_alpha_dummy_121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0110
                    A)
                  0)))) (show (nb090_alpha_dummy_112 h) ≠ (nb090_alpha_dummy_122 h) from (by
          unfold
            nb090_alpha_dummy_122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0111
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_109 A) ≠
        (nb090_alpha_dummy_117 A) from (by
          unfold
            nb090_alpha_dummy_117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0108
                    A)
                  0)))) (show (nb090_alpha_dummy_112 h) ≠ (nb090_alpha_dummy_118 h) from (by
          unfold
            nb090_alpha_dummy_118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0109
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb090_alpha_dummy_101 A) ≠ (nb090_alpha_dummy_105 A) from (by
                                unfold nb090_alpha_dummy_105;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0092 A) 0))))
                            (show (nb090_alpha_dummy_103 h) ≠ (nb090_alpha_dummy_106 h) from (by
                                unfold nb090_alpha_dummy_106;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0093 h) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                          [((nb090_alpha_dummy_105 A), (nb090_alpha_dummy_106 h)),
                            ((nb090_alpha_dummy_101 A), (nb090_alpha_dummy_103 h)),
                            ((nb090_alpha_dummy_102 A), (nb090_alpha_dummy_104 h)),
                            ((nb090_alpha_dummy_127 A), (nb090_alpha_dummy_128 h)),
                            ((nb090_alpha_dummy_125 A), (nb090_alpha_dummy_126 h)),
                            ((nb090_alpha_dummy_094 A), (nb090_alpha_dummy_096 h)),
                            ((nb090_alpha_dummy_093 A), (nb090_alpha_dummy_095 h)),
                            ((nb090_alpha_dummy_123 A), (nb090_alpha_dummy_124 h)),
                            ((nb090_alpha_dummy_097 A), (nb090_alpha_dummy_098 h)),
                            ((nb090_alpha_dummy_051 A), (nb090_alpha_dummy_054 h)),
                            ((nb090_alpha_dummy_050 A), (nb090_alpha_dummy_053 h)),
                            ((nb090_alpha_dummy_049 A), (nb090_alpha_dummy_052 h)),
                            ((nb090_alpha_dummy_055 A), (nb090_alpha_dummy_056 h)),
                            ((nb090_alpha_dummy_047 A), (nb090_alpha_dummy_048 h)),
                            ((nb090_alpha_dummy_045 A), (nb090_alpha_dummy_046 h)),
                            ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
                            ((nb090_alpha_dummy_001 A), u),
                            ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
                          (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb090_alpha_dummy_101 A) ≠ (nb090_alpha_dummy_105 A) from (by
                              unfold nb090_alpha_dummy_105;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0092 A) 0))))
                          (show (nb090_alpha_dummy_103 h) ≠ (nb090_alpha_dummy_106 h) from (by
                              unfold nb090_alpha_dummy_106;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0093 h) 0))))
                          (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb090_alpha_dummy_101 A) ≠ (nb090_alpha_dummy_105 A) from (by
                                unfold nb090_alpha_dummy_105;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0092 A) 0))))
                            (show (nb090_alpha_dummy_103 h) ≠ (nb090_alpha_dummy_106 h) from (by
                                unfold nb090_alpha_dummy_106;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0093 h) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                          [((nb090_alpha_dummy_105 A), (nb090_alpha_dummy_106 h)),
                            ((nb090_alpha_dummy_101 A), (nb090_alpha_dummy_103 h)),
                            ((nb090_alpha_dummy_102 A), (nb090_alpha_dummy_104 h)),
                            ((nb090_alpha_dummy_127 A), (nb090_alpha_dummy_128 h)),
                            ((nb090_alpha_dummy_125 A), (nb090_alpha_dummy_126 h)),
                            ((nb090_alpha_dummy_094 A), (nb090_alpha_dummy_096 h)),
                            ((nb090_alpha_dummy_093 A), (nb090_alpha_dummy_095 h)),
                            ((nb090_alpha_dummy_123 A), (nb090_alpha_dummy_124 h)),
                            ((nb090_alpha_dummy_097 A), (nb090_alpha_dummy_098 h)),
                            ((nb090_alpha_dummy_051 A), (nb090_alpha_dummy_054 h)),
                            ((nb090_alpha_dummy_050 A), (nb090_alpha_dummy_053 h)),
                            ((nb090_alpha_dummy_049 A), (nb090_alpha_dummy_052 h)),
                            ((nb090_alpha_dummy_055 A), (nb090_alpha_dummy_056 h)),
                            ((nb090_alpha_dummy_047 A), (nb090_alpha_dummy_048 h)),
                            ((nb090_alpha_dummy_045 A), (nb090_alpha_dummy_046 h)),
                            ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
                            ((nb090_alpha_dummy_001 A), u),
                            ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
                          (syn_cnnc) (by simp only [fv_syn_cnnc])))))))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cv (TAlphaVar.there
                    (show (nb090_alpha_dummy_094 A) ≠ (nb090_alpha_dummy_101 A) from (by
                        unfold nb090_alpha_dummy_101;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0090 A) 0))))
                    (show (nb090_alpha_dummy_096 h) ≠ (nb090_alpha_dummy_103 h) from (by
                        unfold nb090_alpha_dummy_103;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0091 h) 0)))) (TAlphaVar.there
                      (show (nb090_alpha_dummy_094 A) ≠ (nb090_alpha_dummy_102 A) from (by
                          unfold nb090_alpha_dummy_102;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0090 A) 1))))
                      (show (nb090_alpha_dummy_096 h) ≠ (nb090_alpha_dummy_104 h) from (by
                          unfold nb090_alpha_dummy_104;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0091 h) 1))))
                      (TAlphaVar.there
                        (show (nb090_alpha_dummy_094 A) ≠ (nb090_alpha_dummy_127 A) from (by
                            unfold nb090_alpha_dummy_127;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0120 A) 0))))
                        (show (nb090_alpha_dummy_096 h) ≠ (nb090_alpha_dummy_128 h) from (by
                            unfold nb090_alpha_dummy_128;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0121 h) 0))))
                        (TAlphaVar.there
                          (show (nb090_alpha_dummy_094 A) ≠ (nb090_alpha_dummy_125 A) from (by
                              unfold nb090_alpha_dummy_125;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0118 A) 0))))
                          (show (nb090_alpha_dummy_096 h) ≠ (nb090_alpha_dummy_126 h) from (by
                              unfold nb090_alpha_dummy_126;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0119 h) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there
                    (freshVar_injective (((Class.cv (nb090_alpha_dummy_094 A))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb090_alpha_dummy_096 h))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                      (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (show (nb090_alpha_dummy_101 A) ≠
        (nb090_alpha_dummy_108 A) from (by
                                          unfold nb090_alpha_dummy_108;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0094 A) 1)))) (show
                                        (nb090_alpha_dummy_103 h) ≠ (nb090_alpha_dummy_111 h)
                                        from (by
                                          unfold nb090_alpha_dummy_111;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0095 h) 1))))
                                      (TAlphaVar.there (show (nb090_alpha_dummy_101 A) ≠
        (nb090_alpha_dummy_107 A) from (by
          unfold nb090_alpha_dummy_107;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0094 A) 0)))) (show (nb090_alpha_dummy_103 h) ≠
        (nb090_alpha_dummy_110 h) from (by
          unfold nb090_alpha_dummy_110;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0095 h) 0)))) (TAlphaVar.there (show
        (nb090_alpha_dummy_101 A) ≠ (nb090_alpha_dummy_105 A) from (by
          unfold nb090_alpha_dummy_105;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0092 A) 0)))) (show (nb090_alpha_dummy_103 h) ≠
        (nb090_alpha_dummy_106 h) from (by
          unfold nb090_alpha_dummy_106;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0093 h) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.refl_of_closed [((nb090_alpha_dummy_109 A),
        (nb090_alpha_dummy_112 h)), ((nb090_alpha_dummy_108 A), (nb090_alpha_dummy_111 h)),
        ((nb090_alpha_dummy_107 A), (nb090_alpha_dummy_110 h)), ((nb090_alpha_dummy_105 A),
        (nb090_alpha_dummy_106 h)), ((nb090_alpha_dummy_101 A), (nb090_alpha_dummy_103 h)),
        ((nb090_alpha_dummy_102 A), (nb090_alpha_dummy_104 h)), ((nb090_alpha_dummy_127 A),
        (nb090_alpha_dummy_128 h)), ((nb090_alpha_dummy_125 A), (nb090_alpha_dummy_126 h)),
        ((nb090_alpha_dummy_094 A), (nb090_alpha_dummy_096 h)), ((nb090_alpha_dummy_093 A),
        (nb090_alpha_dummy_095 h)), ((nb090_alpha_dummy_123 A), (nb090_alpha_dummy_124 h)),
        ((nb090_alpha_dummy_097 A), (nb090_alpha_dummy_098 h)), ((nb090_alpha_dummy_051 A),
        (nb090_alpha_dummy_054 h)), ((nb090_alpha_dummy_050 A), (nb090_alpha_dummy_053 h)),
        ((nb090_alpha_dummy_049 A), (nb090_alpha_dummy_052 h)), ((nb090_alpha_dummy_055 A),
        (nb090_alpha_dummy_056 h)), ((nb090_alpha_dummy_047 A), (nb090_alpha_dummy_048 h)),
        ((nb090_alpha_dummy_045 A), (nb090_alpha_dummy_046 h)), ((nb090_alpha_dummy_000 A), h),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
                                        (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
                                      (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090_alpha_dummy_108 A) ≠ (nb090_alpha_dummy_115 A) from (by
          unfold
            nb090_alpha_dummy_115;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0098
                    A)
                  0)))) (show (nb090_alpha_dummy_111 h) ≠ (nb090_alpha_dummy_116 h) from (by
          unfold
            nb090_alpha_dummy_116;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0099
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_108 A) ≠
        (nb090_alpha_dummy_113 A) from (by
          unfold
            nb090_alpha_dummy_113;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0096
                    A)
                  0)))) (show (nb090_alpha_dummy_111 h) ≠ (nb090_alpha_dummy_114 h) from (by
          unfold
            nb090_alpha_dummy_114;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0097
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_101
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_103 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_109 A) ≠ (nb090_alpha_dummy_115 A) from (by
          unfold
            nb090_alpha_dummy_115;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0102
                    A)
                  0)))) (show (nb090_alpha_dummy_112 h) ≠ (nb090_alpha_dummy_116 h) from (by
          unfold
            nb090_alpha_dummy_116;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0103
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_109 A) ≠
        (nb090_alpha_dummy_113 A) from (by
          unfold
            nb090_alpha_dummy_113;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0100
                    A)
                  0)))) (show (nb090_alpha_dummy_112 h) ≠ (nb090_alpha_dummy_114 h) from (by
          unfold
            nb090_alpha_dummy_114;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0101
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_108 A) ≠ (nb090_alpha_dummy_115 A) from (by
          unfold
            nb090_alpha_dummy_115;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0098
                    A)
                  0)))) (show (nb090_alpha_dummy_111 h) ≠ (nb090_alpha_dummy_116 h) from (by
          unfold
            nb090_alpha_dummy_116;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0099
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_108 A) ≠
        (nb090_alpha_dummy_113 A) from (by
          unfold
            nb090_alpha_dummy_113;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0096
                    A)
                  0)))) (show (nb090_alpha_dummy_111 h) ≠ (nb090_alpha_dummy_114 h) from (by
          unfold
            nb090_alpha_dummy_114;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0097
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_101
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_103 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_109 A) ≠ (nb090_alpha_dummy_115 A) from (by
          unfold
            nb090_alpha_dummy_115;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0102
                    A)
                  0)))) (show (nb090_alpha_dummy_112 h) ≠ (nb090_alpha_dummy_116 h) from (by
          unfold
            nb090_alpha_dummy_116;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0103
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_109 A) ≠
        (nb090_alpha_dummy_113 A) from (by
          unfold
            nb090_alpha_dummy_113;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0100
                    A)
                  0)))) (show (nb090_alpha_dummy_112 h) ≠ (nb090_alpha_dummy_114 h) from (by
          unfold
            nb090_alpha_dummy_114;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0101
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_109 A), (nb090_alpha_dummy_112 h)), ((nb090_alpha_dummy_108 A),
        (nb090_alpha_dummy_111 h)), ((nb090_alpha_dummy_107 A), (nb090_alpha_dummy_110 h)),
        ((nb090_alpha_dummy_105 A), (nb090_alpha_dummy_106 h)), ((nb090_alpha_dummy_101 A),
        (nb090_alpha_dummy_103 h)), ((nb090_alpha_dummy_102 A), (nb090_alpha_dummy_104 h)),
        ((nb090_alpha_dummy_127 A), (nb090_alpha_dummy_128 h)), ((nb090_alpha_dummy_125 A),
        (nb090_alpha_dummy_126 h)), ((nb090_alpha_dummy_094 A), (nb090_alpha_dummy_096 h)),
        ((nb090_alpha_dummy_093 A), (nb090_alpha_dummy_095 h)), ((nb090_alpha_dummy_123 A),
        (nb090_alpha_dummy_124 h)), ((nb090_alpha_dummy_097 A), (nb090_alpha_dummy_098 h)),
        ((nb090_alpha_dummy_051 A), (nb090_alpha_dummy_054 h)), ((nb090_alpha_dummy_050 A),
        (nb090_alpha_dummy_053 h)), ((nb090_alpha_dummy_049 A), (nb090_alpha_dummy_052 h)),
        ((nb090_alpha_dummy_055 A), (nb090_alpha_dummy_056 h)), ((nb090_alpha_dummy_047 A),
        (nb090_alpha_dummy_048 h)), ((nb090_alpha_dummy_045 A), (nb090_alpha_dummy_046 h)),
        ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
        ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A),
        (nb090_alpha_dummy_004 v u A h))] (syn_c0) (by simp only [fv_syn_c0])))
                                      (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb090_alpha_dummy_101 A))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_103 h))).fv ∪
        ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_101 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb090_alpha_dummy_103 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090_alpha_dummy_108 A) ≠ (nb090_alpha_dummy_119 A) from (by
          unfold
            nb090_alpha_dummy_119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0106
                    A)
                  0)))) (show (nb090_alpha_dummy_111 h) ≠ (nb090_alpha_dummy_120 h) from (by
          unfold
            nb090_alpha_dummy_120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0107
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_108 A) ≠
        (nb090_alpha_dummy_117 A) from (by
          unfold
            nb090_alpha_dummy_117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0104
                    A)
                  0)))) (show (nb090_alpha_dummy_111 h) ≠ (nb090_alpha_dummy_118 h) from (by
          unfold
            nb090_alpha_dummy_118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0105
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_101
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_103 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_108 A) ≠ (nb090_alpha_dummy_119 A) from (by
          unfold
            nb090_alpha_dummy_119;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0106
                    A)
                  0)))) (show (nb090_alpha_dummy_111 h) ≠ (nb090_alpha_dummy_120 h) from (by
          unfold
            nb090_alpha_dummy_120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0107
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_108 A) ≠
        (nb090_alpha_dummy_117 A) from (by
          unfold
            nb090_alpha_dummy_117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0104
                    A)
                  0)))) (show (nb090_alpha_dummy_111 h) ≠ (nb090_alpha_dummy_118 h) from (by
          unfold
            nb090_alpha_dummy_118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0105
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_101
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_103 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090_alpha_dummy_109 A) ≠ (nb090_alpha_dummy_121 A) from (by
          unfold
            nb090_alpha_dummy_121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0110
                    A)
                  0)))) (show (nb090_alpha_dummy_112 h) ≠ (nb090_alpha_dummy_122 h) from (by
          unfold
            nb090_alpha_dummy_122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0111
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_109 A) ≠
        (nb090_alpha_dummy_117 A) from (by
          unfold
            nb090_alpha_dummy_117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0108
                    A)
                  0)))) (show (nb090_alpha_dummy_112 h) ≠ (nb090_alpha_dummy_118 h) from (by
          unfold
            nb090_alpha_dummy_118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0109
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090_alpha_dummy_109 A) ≠ (nb090_alpha_dummy_121 A) from (by
          unfold
            nb090_alpha_dummy_121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0110
                    A)
                  0)))) (show (nb090_alpha_dummy_112 h) ≠ (nb090_alpha_dummy_122 h) from (by
          unfold
            nb090_alpha_dummy_122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0111
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_109 A) ≠
        (nb090_alpha_dummy_117 A) from (by
          unfold
            nb090_alpha_dummy_117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0108
                    A)
                  0)))) (show (nb090_alpha_dummy_112 h) ≠ (nb090_alpha_dummy_118 h) from (by
          unfold
            nb090_alpha_dummy_118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0109
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb090_alpha_dummy_101 A) ≠ (nb090_alpha_dummy_105 A) from
                                (by
                                  unfold nb090_alpha_dummy_105;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0092 A) 0))))
                              (show (nb090_alpha_dummy_103 h) ≠ (nb090_alpha_dummy_106 h) from
                                (by
                                  unfold nb090_alpha_dummy_106;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0093 h) 0))))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                            [((nb090_alpha_dummy_105 A), (nb090_alpha_dummy_106 h)),
                              ((nb090_alpha_dummy_101 A), (nb090_alpha_dummy_103 h)),
                              ((nb090_alpha_dummy_102 A), (nb090_alpha_dummy_104 h)),
                              ((nb090_alpha_dummy_127 A), (nb090_alpha_dummy_128 h)),
                              ((nb090_alpha_dummy_125 A), (nb090_alpha_dummy_126 h)),
                              ((nb090_alpha_dummy_094 A), (nb090_alpha_dummy_096 h)),
                              ((nb090_alpha_dummy_093 A), (nb090_alpha_dummy_095 h)),
                              ((nb090_alpha_dummy_123 A), (nb090_alpha_dummy_124 h)),
                              ((nb090_alpha_dummy_097 A), (nb090_alpha_dummy_098 h)),
                              ((nb090_alpha_dummy_051 A), (nb090_alpha_dummy_054 h)),
                              ((nb090_alpha_dummy_050 A), (nb090_alpha_dummy_053 h)),
                              ((nb090_alpha_dummy_049 A), (nb090_alpha_dummy_052 h)),
                              ((nb090_alpha_dummy_055 A), (nb090_alpha_dummy_056 h)),
                              ((nb090_alpha_dummy_047 A), (nb090_alpha_dummy_048 h)),
                              ((nb090_alpha_dummy_045 A), (nb090_alpha_dummy_046 h)),
                              ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
                              ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A),
                                (nb090_alpha_dummy_004 v u A h))]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb090_alpha_dummy_101 A) ≠ (nb090_alpha_dummy_105 A) from (by
                                unfold nb090_alpha_dummy_105;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0092 A) 0))))
                            (show (nb090_alpha_dummy_103 h) ≠ (nb090_alpha_dummy_106 h) from (by
                                unfold nb090_alpha_dummy_106;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0093 h) 0))))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb090_alpha_dummy_101 A) ≠ (nb090_alpha_dummy_105 A) from
                                (by
                                  unfold nb090_alpha_dummy_105;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0092 A) 0))))
                              (show (nb090_alpha_dummy_103 h) ≠ (nb090_alpha_dummy_106 h) from
                                (by
                                  unfold nb090_alpha_dummy_106;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0093 h) 0))))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                            [((nb090_alpha_dummy_105 A), (nb090_alpha_dummy_106 h)),
                              ((nb090_alpha_dummy_101 A), (nb090_alpha_dummy_103 h)),
                              ((nb090_alpha_dummy_102 A), (nb090_alpha_dummy_104 h)),
                              ((nb090_alpha_dummy_127 A), (nb090_alpha_dummy_128 h)),
                              ((nb090_alpha_dummy_125 A), (nb090_alpha_dummy_126 h)),
                              ((nb090_alpha_dummy_094 A), (nb090_alpha_dummy_096 h)),
                              ((nb090_alpha_dummy_093 A), (nb090_alpha_dummy_095 h)),
                              ((nb090_alpha_dummy_123 A), (nb090_alpha_dummy_124 h)),
                              ((nb090_alpha_dummy_097 A), (nb090_alpha_dummy_098 h)),
                              ((nb090_alpha_dummy_051 A), (nb090_alpha_dummy_054 h)),
                              ((nb090_alpha_dummy_050 A), (nb090_alpha_dummy_053 h)),
                              ((nb090_alpha_dummy_049 A), (nb090_alpha_dummy_052 h)),
                              ((nb090_alpha_dummy_055 A), (nb090_alpha_dummy_056 h)),
                              ((nb090_alpha_dummy_047 A), (nb090_alpha_dummy_048 h)),
                              ((nb090_alpha_dummy_045 A), (nb090_alpha_dummy_046 h)),
                              ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
                              ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A),
                                (nb090_alpha_dummy_004 v u A h))]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C090C001Part029`. -/


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
noncomputable def nb090_split_alpha_0005 (v : Var) (u : Var) (A : Class) (h : Var) :
    TAlphaWff
      [((nb090_alpha_dummy_141 A), (nb090_alpha_dummy_142 h)),
        ((nb090_alpha_dummy_139 A), (nb090_alpha_dummy_140 h)),
        ((nb090_alpha_dummy_130 A), (nb090_alpha_dummy_132 h)),
        ((nb090_alpha_dummy_129 A), (nb090_alpha_dummy_131 h)),
        ((nb090_alpha_dummy_133 A), (nb090_alpha_dummy_134 h)),
        ((nb090_alpha_dummy_051 A), (nb090_alpha_dummy_054 h)),
        ((nb090_alpha_dummy_050 A), (nb090_alpha_dummy_053 h)),
        ((nb090_alpha_dummy_049 A), (nb090_alpha_dummy_052 h)),
        ((nb090_alpha_dummy_055 A), (nb090_alpha_dummy_056 h)),
        ((nb090_alpha_dummy_047 A), (nb090_alpha_dummy_048 h)),
        ((nb090_alpha_dummy_045 A), (nb090_alpha_dummy_046 h)),
        ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
        ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
      (Wff.imp (Wff.classMem (Class.cv (nb090_alpha_dummy_141 A))
          (Class.cab (nb090_alpha_dummy_135 A)
            (syn_wrex (nb090_alpha_dummy_136 A) (Class.cv (nb090_alpha_dummy_129 A))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_135 A))
                (syn_cphi (Class.cv (nb090_alpha_dummy_136 A))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb090_alpha_dummy_141 A))
            (Class.cab (nb090_alpha_dummy_135 A)
              (syn_wrex (nb090_alpha_dummy_136 A) (Class.cv (nb090_alpha_dummy_129 A))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_135 A))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_136 A)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb090_alpha_dummy_142 h))
          (Class.cab (nb090_alpha_dummy_137 h)
            (syn_wrex (nb090_alpha_dummy_138 h) (Class.cv (nb090_alpha_dummy_131 h))
              (Wff.classEq (Class.cv (nb090_alpha_dummy_137 h))
                (syn_cphi (Class.cv (nb090_alpha_dummy_138 h))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb090_alpha_dummy_142 h))
            (Class.cab (nb090_alpha_dummy_137 h)
              (syn_wrex (nb090_alpha_dummy_138 h) (Class.cv (nb090_alpha_dummy_131 h))
                (Wff.classEq (Class.cv (nb090_alpha_dummy_137 h))
                  (syn_cphi (Class.cv (nb090_alpha_dummy_138 h))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there
                  (show (nb090_alpha_dummy_129 A) ≠ (nb090_alpha_dummy_136 A) from (by
                      unfold nb090_alpha_dummy_136;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0126 A) 1))))
                  (show (nb090_alpha_dummy_131 h) ≠ (nb090_alpha_dummy_138 h) from (by
                      unfold nb090_alpha_dummy_138;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0128 h) 1))))
                  (TAlphaVar.there
                    (show (nb090_alpha_dummy_129 A) ≠ (nb090_alpha_dummy_135 A) from (by
                        unfold nb090_alpha_dummy_135;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0126 A) 0))))
                    (show (nb090_alpha_dummy_131 h) ≠ (nb090_alpha_dummy_137 h) from (by
                        unfold nb090_alpha_dummy_137;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0128 h) 0)))) (TAlphaVar.there
                      (show (nb090_alpha_dummy_129 A) ≠ (nb090_alpha_dummy_141 A) from (by
                          unfold nb090_alpha_dummy_141;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0130 A) 0))))
                      (show (nb090_alpha_dummy_131 h) ≠ (nb090_alpha_dummy_142 h) from (by
                          unfold nb090_alpha_dummy_142;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0131 h) 0))))
                      (TAlphaVar.there
                        (show (nb090_alpha_dummy_129 A) ≠ (nb090_alpha_dummy_139 A) from (by
                            unfold nb090_alpha_dummy_139;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0127 A) 0))))
                        (show (nb090_alpha_dummy_131 h) ≠ (nb090_alpha_dummy_140 h) from (by
                            unfold nb090_alpha_dummy_140;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0129 h) 0))))
                        (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb090_alpha_dummy_000 A))).fv)
                            (by decide)) (freshVar_injective (((Class.cv h)).fv) (by decide))
                          (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb090_alpha_dummy_129 A))).fv ∪
                      ((Class.cv (nb090_alpha_dummy_130 A))).fv) (by decide))
                  (freshVar_injective (((Class.cv (nb090_alpha_dummy_131 h))).fv ∪
                      ((Class.cv (nb090_alpha_dummy_132 h))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb090_alpha_dummy_136 A) ≠ (nb090_alpha_dummy_143 A) from (by
                              unfold nb090_alpha_dummy_143;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0132 A) 0))))
                          (show (nb090_alpha_dummy_138 h) ≠ (nb090_alpha_dummy_145 h) from (by
                              unfold nb090_alpha_dummy_145;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0133 h) 0))))
                          (TAlphaVar.there
                            (show (nb090_alpha_dummy_136 A) ≠ (nb090_alpha_dummy_144 A) from (by
                                unfold nb090_alpha_dummy_144;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0132 A) 1))))
                            (show (nb090_alpha_dummy_138 h) ≠ (nb090_alpha_dummy_146 h) from (by
                                unfold nb090_alpha_dummy_146;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0133 h) 1))))
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb090_alpha_dummy_136 A))).fv)
                            (by decide))
                          (freshVar_injective (((Class.cv (nb090_alpha_dummy_138 h))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_143 A) ≠ (nb090_alpha_dummy_150 A) from (by
          unfold nb090_alpha_dummy_150;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0136 A) 1)))) (show (nb090_alpha_dummy_145 h) ≠
        (nb090_alpha_dummy_153 h) from (by
          unfold nb090_alpha_dummy_153;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0137 h) 1)))) (TAlphaVar.there (show
        (nb090_alpha_dummy_143 A) ≠ (nb090_alpha_dummy_149 A) from (by
          unfold nb090_alpha_dummy_149;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0136 A) 0)))) (show (nb090_alpha_dummy_145 h) ≠
        (nb090_alpha_dummy_152 h) from (by
          unfold nb090_alpha_dummy_152;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0137 h) 0)))) (TAlphaVar.there (show
        (nb090_alpha_dummy_143 A) ≠ (nb090_alpha_dummy_147 A) from (by
          unfold nb090_alpha_dummy_147;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0134 A)
                  0)))) (show (nb090_alpha_dummy_145 h) ≠ (nb090_alpha_dummy_148 h) from (by
          unfold nb090_alpha_dummy_148;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0135 h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_151 A), (nb090_alpha_dummy_154 h)), ((nb090_alpha_dummy_150 A),
        (nb090_alpha_dummy_153 h)), ((nb090_alpha_dummy_149 A), (nb090_alpha_dummy_152 h)),
        ((nb090_alpha_dummy_147 A), (nb090_alpha_dummy_148 h)), ((nb090_alpha_dummy_143 A),
        (nb090_alpha_dummy_145 h)), ((nb090_alpha_dummy_144 A), (nb090_alpha_dummy_146 h)),
        ((nb090_alpha_dummy_136 A), (nb090_alpha_dummy_138 h)), ((nb090_alpha_dummy_135 A),
        (nb090_alpha_dummy_137 h)), ((nb090_alpha_dummy_141 A), (nb090_alpha_dummy_142 h)),
        ((nb090_alpha_dummy_139 A), (nb090_alpha_dummy_140 h)), ((nb090_alpha_dummy_130 A),
        (nb090_alpha_dummy_132 h)), ((nb090_alpha_dummy_129 A), (nb090_alpha_dummy_131 h)),
        ((nb090_alpha_dummy_133 A), (nb090_alpha_dummy_134 h)), ((nb090_alpha_dummy_051 A),
        (nb090_alpha_dummy_054 h)), ((nb090_alpha_dummy_050 A), (nb090_alpha_dummy_053 h)),
        ((nb090_alpha_dummy_049 A), (nb090_alpha_dummy_052 h)), ((nb090_alpha_dummy_055 A),
        (nb090_alpha_dummy_056 h)), ((nb090_alpha_dummy_047 A), (nb090_alpha_dummy_048 h)),
        ((nb090_alpha_dummy_045 A), (nb090_alpha_dummy_046 h)), ((nb090_alpha_dummy_000 A), h),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
        (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_150 A) ≠ (nb090_alpha_dummy_157 A) from (by
          unfold
            nb090_alpha_dummy_157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0140
                    A)
                  0)))) (show (nb090_alpha_dummy_153 h) ≠ (nb090_alpha_dummy_158 h) from (by
          unfold
            nb090_alpha_dummy_158;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0141
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_150 A) ≠
        (nb090_alpha_dummy_155 A) from (by
          unfold
            nb090_alpha_dummy_155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0138
                    A)
                  0)))) (show (nb090_alpha_dummy_153 h) ≠ (nb090_alpha_dummy_156 h) from (by
          unfold
            nb090_alpha_dummy_156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0139
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_143
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_145 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_151 A) ≠ (nb090_alpha_dummy_157 A) from (by
          unfold
            nb090_alpha_dummy_157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0144
                    A)
                  0)))) (show (nb090_alpha_dummy_154 h) ≠ (nb090_alpha_dummy_158 h) from (by
          unfold
            nb090_alpha_dummy_158;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0145
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_151 A) ≠
        (nb090_alpha_dummy_155 A) from (by
          unfold
            nb090_alpha_dummy_155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0142
                    A)
                  0)))) (show (nb090_alpha_dummy_154 h) ≠ (nb090_alpha_dummy_156 h) from (by
          unfold
            nb090_alpha_dummy_156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0143
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_150 A) ≠ (nb090_alpha_dummy_157 A) from (by
          unfold
            nb090_alpha_dummy_157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0140
                    A)
                  0)))) (show (nb090_alpha_dummy_153 h) ≠ (nb090_alpha_dummy_158 h) from (by
          unfold
            nb090_alpha_dummy_158;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0141
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_150 A) ≠
        (nb090_alpha_dummy_155 A) from (by
          unfold
            nb090_alpha_dummy_155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0138
                    A)
                  0)))) (show (nb090_alpha_dummy_153 h) ≠ (nb090_alpha_dummy_156 h) from (by
          unfold
            nb090_alpha_dummy_156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0139
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_143
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_145 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_151 A) ≠ (nb090_alpha_dummy_157 A) from (by
          unfold
            nb090_alpha_dummy_157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0144
                    A)
                  0)))) (show (nb090_alpha_dummy_154 h) ≠ (nb090_alpha_dummy_158 h) from (by
          unfold
            nb090_alpha_dummy_158;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0145
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_151 A) ≠
        (nb090_alpha_dummy_155 A) from (by
          unfold
            nb090_alpha_dummy_155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0142
                    A)
                  0)))) (show (nb090_alpha_dummy_154 h) ≠ (nb090_alpha_dummy_156 h) from (by
          unfold
            nb090_alpha_dummy_156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0143
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_151 A), (nb090_alpha_dummy_154 h)), ((nb090_alpha_dummy_150 A),
        (nb090_alpha_dummy_153 h)), ((nb090_alpha_dummy_149 A), (nb090_alpha_dummy_152 h)),
        ((nb090_alpha_dummy_147 A), (nb090_alpha_dummy_148 h)), ((nb090_alpha_dummy_143 A),
        (nb090_alpha_dummy_145 h)), ((nb090_alpha_dummy_144 A), (nb090_alpha_dummy_146 h)),
        ((nb090_alpha_dummy_136 A), (nb090_alpha_dummy_138 h)), ((nb090_alpha_dummy_135 A),
        (nb090_alpha_dummy_137 h)), ((nb090_alpha_dummy_141 A), (nb090_alpha_dummy_142 h)),
        ((nb090_alpha_dummy_139 A), (nb090_alpha_dummy_140 h)), ((nb090_alpha_dummy_130 A),
        (nb090_alpha_dummy_132 h)), ((nb090_alpha_dummy_129 A), (nb090_alpha_dummy_131 h)),
        ((nb090_alpha_dummy_133 A), (nb090_alpha_dummy_134 h)), ((nb090_alpha_dummy_051 A),
        (nb090_alpha_dummy_054 h)), ((nb090_alpha_dummy_050 A), (nb090_alpha_dummy_053 h)),
        ((nb090_alpha_dummy_049 A), (nb090_alpha_dummy_052 h)), ((nb090_alpha_dummy_055 A),
        (nb090_alpha_dummy_056 h)), ((nb090_alpha_dummy_047 A), (nb090_alpha_dummy_048 h)),
        ((nb090_alpha_dummy_045 A), (nb090_alpha_dummy_046 h)), ((nb090_alpha_dummy_000 A), h),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_143 A))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_145 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb090_alpha_dummy_143 A))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_145 h))).fv ∪
        ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_150
        A) ≠ (nb090_alpha_dummy_161 A) from (by
          unfold
            nb090_alpha_dummy_161;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0148
                    A)
                  0)))) (show (nb090_alpha_dummy_153 h) ≠ (nb090_alpha_dummy_162 h) from (by
          unfold
            nb090_alpha_dummy_162;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0149
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_150 A) ≠
        (nb090_alpha_dummy_159 A) from (by
          unfold
            nb090_alpha_dummy_159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0146
                    A)
                  0)))) (show (nb090_alpha_dummy_153 h) ≠ (nb090_alpha_dummy_160 h) from (by
          unfold
            nb090_alpha_dummy_160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0147
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_143
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_145 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_150 A) ≠ (nb090_alpha_dummy_161 A) from (by
          unfold
            nb090_alpha_dummy_161;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0148
                    A)
                  0)))) (show (nb090_alpha_dummy_153 h) ≠ (nb090_alpha_dummy_162 h) from (by
          unfold
            nb090_alpha_dummy_162;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0149
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_150 A) ≠
        (nb090_alpha_dummy_159 A) from (by
          unfold
            nb090_alpha_dummy_159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0146
                    A)
                  0)))) (show (nb090_alpha_dummy_153 h) ≠ (nb090_alpha_dummy_160 h) from (by
          unfold
            nb090_alpha_dummy_160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0147
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_143
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_145 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_151
        A) ≠ (nb090_alpha_dummy_163 A) from (by
          unfold
            nb090_alpha_dummy_163;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0152
                    A)
                  0)))) (show (nb090_alpha_dummy_154 h) ≠ (nb090_alpha_dummy_164 h) from (by
          unfold
            nb090_alpha_dummy_164;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0153
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_151 A) ≠
        (nb090_alpha_dummy_159 A) from (by
          unfold
            nb090_alpha_dummy_159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0150
                    A)
                  0)))) (show (nb090_alpha_dummy_154 h) ≠ (nb090_alpha_dummy_160 h) from (by
          unfold
            nb090_alpha_dummy_160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0151
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_151
        A) ≠ (nb090_alpha_dummy_163 A) from (by
          unfold
            nb090_alpha_dummy_163;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0152
                    A)
                  0)))) (show (nb090_alpha_dummy_154 h) ≠ (nb090_alpha_dummy_164 h) from (by
          unfold
            nb090_alpha_dummy_164;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0153
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_151 A) ≠
        (nb090_alpha_dummy_159 A) from (by
          unfold
            nb090_alpha_dummy_159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0150
                    A)
                  0)))) (show (nb090_alpha_dummy_154 h) ≠ (nb090_alpha_dummy_160 h) from (by
          unfold
            nb090_alpha_dummy_160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0151
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090_alpha_dummy_143 A) ≠ (nb090_alpha_dummy_147 A) from
                                      (by
                                        unfold nb090_alpha_dummy_147;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0134 A)
                                                0)))) (show (nb090_alpha_dummy_145 h) ≠
                                        (nb090_alpha_dummy_148 h) from (by
                                        unfold nb090_alpha_dummy_148;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0135 h)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
                                  [((nb090_alpha_dummy_147 A), (nb090_alpha_dummy_148 h)),
                                    ((nb090_alpha_dummy_143 A), (nb090_alpha_dummy_145 h)),
                                    ((nb090_alpha_dummy_144 A), (nb090_alpha_dummy_146 h)),
                                    ((nb090_alpha_dummy_136 A), (nb090_alpha_dummy_138 h)),
                                    ((nb090_alpha_dummy_135 A), (nb090_alpha_dummy_137 h)),
                                    ((nb090_alpha_dummy_141 A), (nb090_alpha_dummy_142 h)),
                                    ((nb090_alpha_dummy_139 A), (nb090_alpha_dummy_140 h)),
                                    ((nb090_alpha_dummy_130 A), (nb090_alpha_dummy_132 h)),
                                    ((nb090_alpha_dummy_129 A), (nb090_alpha_dummy_131 h)),
                                    ((nb090_alpha_dummy_133 A), (nb090_alpha_dummy_134 h)),
                                    ((nb090_alpha_dummy_051 A), (nb090_alpha_dummy_054 h)),
                                    ((nb090_alpha_dummy_050 A), (nb090_alpha_dummy_053 h)),
                                    ((nb090_alpha_dummy_049 A), (nb090_alpha_dummy_052 h)),
                                    ((nb090_alpha_dummy_055 A), (nb090_alpha_dummy_056 h)),
                                    ((nb090_alpha_dummy_047 A), (nb090_alpha_dummy_048 h)),
                                    ((nb090_alpha_dummy_045 A), (nb090_alpha_dummy_046 h)),
                                    ((nb090_alpha_dummy_000 A), h),
                                    ((nb090_alpha_dummy_002 A), v),
                                    ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A),
                                      (nb090_alpha_dummy_004 v u A h))]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb090_alpha_dummy_143 A) ≠ (nb090_alpha_dummy_147 A) from
                                    (by
                                      unfold nb090_alpha_dummy_147;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0134 A)
                                              0)))) (show
                                    (nb090_alpha_dummy_145 h) ≠ (nb090_alpha_dummy_148 h) from
                                    (by
                                      unfold nb090_alpha_dummy_148;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb090_support_mem_0135 h)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090_alpha_dummy_143 A) ≠ (nb090_alpha_dummy_147 A) from
                                      (by
                                        unfold nb090_alpha_dummy_147;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0134 A)
                                                0)))) (show (nb090_alpha_dummy_145 h) ≠
                                        (nb090_alpha_dummy_148 h) from (by
                                        unfold nb090_alpha_dummy_148;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0135 h)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
                                  [((nb090_alpha_dummy_147 A), (nb090_alpha_dummy_148 h)),
                                    ((nb090_alpha_dummy_143 A), (nb090_alpha_dummy_145 h)),
                                    ((nb090_alpha_dummy_144 A), (nb090_alpha_dummy_146 h)),
                                    ((nb090_alpha_dummy_136 A), (nb090_alpha_dummy_138 h)),
                                    ((nb090_alpha_dummy_135 A), (nb090_alpha_dummy_137 h)),
                                    ((nb090_alpha_dummy_141 A), (nb090_alpha_dummy_142 h)),
                                    ((nb090_alpha_dummy_139 A), (nb090_alpha_dummy_140 h)),
                                    ((nb090_alpha_dummy_130 A), (nb090_alpha_dummy_132 h)),
                                    ((nb090_alpha_dummy_129 A), (nb090_alpha_dummy_131 h)),
                                    ((nb090_alpha_dummy_133 A), (nb090_alpha_dummy_134 h)),
                                    ((nb090_alpha_dummy_051 A), (nb090_alpha_dummy_054 h)),
                                    ((nb090_alpha_dummy_050 A), (nb090_alpha_dummy_053 h)),
                                    ((nb090_alpha_dummy_049 A), (nb090_alpha_dummy_052 h)),
                                    ((nb090_alpha_dummy_055 A), (nb090_alpha_dummy_056 h)),
                                    ((nb090_alpha_dummy_047 A), (nb090_alpha_dummy_048 h)),
                                    ((nb090_alpha_dummy_045 A), (nb090_alpha_dummy_046 h)),
                                    ((nb090_alpha_dummy_000 A), h),
                                    ((nb090_alpha_dummy_002 A), v),
                                    ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A),
                                      (nb090_alpha_dummy_004 v u A h))]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there
                    (show (nb090_alpha_dummy_129 A) ≠ (nb090_alpha_dummy_136 A) from (by
                        unfold nb090_alpha_dummy_136;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0126 A) 1))))
                    (show (nb090_alpha_dummy_131 h) ≠ (nb090_alpha_dummy_138 h) from (by
                        unfold nb090_alpha_dummy_138;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0128 h) 1)))) (TAlphaVar.there
                      (show (nb090_alpha_dummy_129 A) ≠ (nb090_alpha_dummy_135 A) from (by
                          unfold nb090_alpha_dummy_135;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0126 A) 0))))
                      (show (nb090_alpha_dummy_131 h) ≠ (nb090_alpha_dummy_137 h) from (by
                          unfold nb090_alpha_dummy_137;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0128 h) 0))))
                      (TAlphaVar.there
                        (show (nb090_alpha_dummy_129 A) ≠ (nb090_alpha_dummy_141 A) from (by
                            unfold nb090_alpha_dummy_141;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0130 A) 0))))
                        (show (nb090_alpha_dummy_131 h) ≠ (nb090_alpha_dummy_142 h) from (by
                            unfold nb090_alpha_dummy_142;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0131 h) 0))))
                        (TAlphaVar.there
                          (show (nb090_alpha_dummy_129 A) ≠ (nb090_alpha_dummy_139 A) from (by
                              unfold nb090_alpha_dummy_139;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0127 A) 0))))
                          (show (nb090_alpha_dummy_131 h) ≠ (nb090_alpha_dummy_140 h) from (by
                              unfold nb090_alpha_dummy_140;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0129 h) 0))))
                          (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb090_alpha_dummy_000 A))).fv) (by decide))
                            (freshVar_injective (((Class.cv h)).fv) (by decide))
                            (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb090_alpha_dummy_129 A))).fv ∪
                        ((Class.cv (nb090_alpha_dummy_130 A))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb090_alpha_dummy_131 h))).fv ∪
                        ((Class.cv (nb090_alpha_dummy_132 h))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb090_alpha_dummy_136 A) ≠ (nb090_alpha_dummy_143 A) from (by
                                unfold nb090_alpha_dummy_143;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0132 A) 0))))
                            (show (nb090_alpha_dummy_138 h) ≠ (nb090_alpha_dummy_145 h) from (by
                                unfold nb090_alpha_dummy_145;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0133 h) 0))))
                            (TAlphaVar.there
                              (show (nb090_alpha_dummy_136 A) ≠ (nb090_alpha_dummy_144 A) from
                                (by
                                  unfold nb090_alpha_dummy_144;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0132 A) 1))))
                              (show (nb090_alpha_dummy_138 h) ≠ (nb090_alpha_dummy_146 h) from
                                (by
                                  unfold nb090_alpha_dummy_146;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0133 h) 1))))
                              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb090_alpha_dummy_136 A))).fv) (by decide))
                            (freshVar_injective
                              (((Class.cv (nb090_alpha_dummy_138 h))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090_alpha_dummy_143 A) ≠ (nb090_alpha_dummy_150 A) from (by
          unfold nb090_alpha_dummy_150;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0136 A) 1)))) (show (nb090_alpha_dummy_145 h) ≠
        (nb090_alpha_dummy_153 h) from (by
          unfold nb090_alpha_dummy_153;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0137 h) 1)))) (TAlphaVar.there (show
        (nb090_alpha_dummy_143 A) ≠ (nb090_alpha_dummy_149 A) from (by
          unfold nb090_alpha_dummy_149;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0136 A)
                  0)))) (show (nb090_alpha_dummy_145 h) ≠ (nb090_alpha_dummy_152 h) from (by
          unfold nb090_alpha_dummy_152;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0137 h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_143 A) ≠
        (nb090_alpha_dummy_147 A) from (by
          unfold nb090_alpha_dummy_147;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0134 A)
                  0)))) (show (nb090_alpha_dummy_145 h) ≠ (nb090_alpha_dummy_148 h) from (by
          unfold nb090_alpha_dummy_148;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0135 h)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_151 A), (nb090_alpha_dummy_154 h)), ((nb090_alpha_dummy_150 A),
        (nb090_alpha_dummy_153 h)), ((nb090_alpha_dummy_149 A), (nb090_alpha_dummy_152 h)),
        ((nb090_alpha_dummy_147 A), (nb090_alpha_dummy_148 h)), ((nb090_alpha_dummy_143 A),
        (nb090_alpha_dummy_145 h)), ((nb090_alpha_dummy_144 A), (nb090_alpha_dummy_146 h)),
        ((nb090_alpha_dummy_136 A), (nb090_alpha_dummy_138 h)), ((nb090_alpha_dummy_135 A),
        (nb090_alpha_dummy_137 h)), ((nb090_alpha_dummy_141 A), (nb090_alpha_dummy_142 h)),
        ((nb090_alpha_dummy_139 A), (nb090_alpha_dummy_140 h)), ((nb090_alpha_dummy_130 A),
        (nb090_alpha_dummy_132 h)), ((nb090_alpha_dummy_129 A), (nb090_alpha_dummy_131 h)),
        ((nb090_alpha_dummy_133 A), (nb090_alpha_dummy_134 h)), ((nb090_alpha_dummy_051 A),
        (nb090_alpha_dummy_054 h)), ((nb090_alpha_dummy_050 A), (nb090_alpha_dummy_053 h)),
        ((nb090_alpha_dummy_049 A), (nb090_alpha_dummy_052 h)), ((nb090_alpha_dummy_055 A),
        (nb090_alpha_dummy_056 h)), ((nb090_alpha_dummy_047 A), (nb090_alpha_dummy_048 h)),
        ((nb090_alpha_dummy_045 A), (nb090_alpha_dummy_046 h)), ((nb090_alpha_dummy_000 A), h),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
        (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_150 A) ≠ (nb090_alpha_dummy_157 A) from (by
          unfold
            nb090_alpha_dummy_157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0140
                    A)
                  0)))) (show (nb090_alpha_dummy_153 h) ≠ (nb090_alpha_dummy_158 h) from (by
          unfold
            nb090_alpha_dummy_158;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0141
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_150 A) ≠
        (nb090_alpha_dummy_155 A) from (by
          unfold
            nb090_alpha_dummy_155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0138
                    A)
                  0)))) (show (nb090_alpha_dummy_153 h) ≠ (nb090_alpha_dummy_156 h) from (by
          unfold
            nb090_alpha_dummy_156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0139
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_143
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_145 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_151 A) ≠ (nb090_alpha_dummy_157 A) from (by
          unfold
            nb090_alpha_dummy_157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0144
                    A)
                  0)))) (show (nb090_alpha_dummy_154 h) ≠ (nb090_alpha_dummy_158 h) from (by
          unfold
            nb090_alpha_dummy_158;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0145
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_151 A) ≠
        (nb090_alpha_dummy_155 A) from (by
          unfold
            nb090_alpha_dummy_155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0142
                    A)
                  0)))) (show (nb090_alpha_dummy_154 h) ≠ (nb090_alpha_dummy_156 h) from (by
          unfold
            nb090_alpha_dummy_156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0143
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_150 A) ≠ (nb090_alpha_dummy_157 A) from (by
          unfold
            nb090_alpha_dummy_157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0140
                    A)
                  0)))) (show (nb090_alpha_dummy_153 h) ≠ (nb090_alpha_dummy_158 h) from (by
          unfold
            nb090_alpha_dummy_158;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0141
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_150 A) ≠
        (nb090_alpha_dummy_155 A) from (by
          unfold
            nb090_alpha_dummy_155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0138
                    A)
                  0)))) (show (nb090_alpha_dummy_153 h) ≠ (nb090_alpha_dummy_156 h) from (by
          unfold
            nb090_alpha_dummy_156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0139
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_143
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_145 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_151 A) ≠ (nb090_alpha_dummy_157 A) from (by
          unfold
            nb090_alpha_dummy_157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0144
                    A)
                  0)))) (show (nb090_alpha_dummy_154 h) ≠ (nb090_alpha_dummy_158 h) from (by
          unfold
            nb090_alpha_dummy_158;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0145
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_151 A) ≠
        (nb090_alpha_dummy_155 A) from (by
          unfold
            nb090_alpha_dummy_155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0142
                    A)
                  0)))) (show (nb090_alpha_dummy_154 h) ≠ (nb090_alpha_dummy_156 h) from (by
          unfold
            nb090_alpha_dummy_156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0143
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_151 A), (nb090_alpha_dummy_154 h)), ((nb090_alpha_dummy_150 A),
        (nb090_alpha_dummy_153 h)), ((nb090_alpha_dummy_149 A), (nb090_alpha_dummy_152 h)),
        ((nb090_alpha_dummy_147 A), (nb090_alpha_dummy_148 h)), ((nb090_alpha_dummy_143 A),
        (nb090_alpha_dummy_145 h)), ((nb090_alpha_dummy_144 A), (nb090_alpha_dummy_146 h)),
        ((nb090_alpha_dummy_136 A), (nb090_alpha_dummy_138 h)), ((nb090_alpha_dummy_135 A),
        (nb090_alpha_dummy_137 h)), ((nb090_alpha_dummy_141 A), (nb090_alpha_dummy_142 h)),
        ((nb090_alpha_dummy_139 A), (nb090_alpha_dummy_140 h)), ((nb090_alpha_dummy_130 A),
        (nb090_alpha_dummy_132 h)), ((nb090_alpha_dummy_129 A), (nb090_alpha_dummy_131 h)),
        ((nb090_alpha_dummy_133 A), (nb090_alpha_dummy_134 h)), ((nb090_alpha_dummy_051 A),
        (nb090_alpha_dummy_054 h)), ((nb090_alpha_dummy_050 A), (nb090_alpha_dummy_053 h)),
        ((nb090_alpha_dummy_049 A), (nb090_alpha_dummy_052 h)), ((nb090_alpha_dummy_055 A),
        (nb090_alpha_dummy_056 h)), ((nb090_alpha_dummy_047 A), (nb090_alpha_dummy_048 h)),
        ((nb090_alpha_dummy_045 A), (nb090_alpha_dummy_046 h)), ((nb090_alpha_dummy_000 A), h),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_143 A))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_145
        h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_143 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb090_alpha_dummy_145 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_150
        A) ≠ (nb090_alpha_dummy_161 A) from (by
          unfold
            nb090_alpha_dummy_161;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0148
                    A)
                  0)))) (show (nb090_alpha_dummy_153 h) ≠ (nb090_alpha_dummy_162 h) from (by
          unfold
            nb090_alpha_dummy_162;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0149
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_150 A) ≠
        (nb090_alpha_dummy_159 A) from (by
          unfold
            nb090_alpha_dummy_159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0146
                    A)
                  0)))) (show (nb090_alpha_dummy_153 h) ≠ (nb090_alpha_dummy_160 h) from (by
          unfold
            nb090_alpha_dummy_160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0147
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_143
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_145 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_150 A) ≠ (nb090_alpha_dummy_161 A) from (by
          unfold
            nb090_alpha_dummy_161;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0148
                    A)
                  0)))) (show (nb090_alpha_dummy_153 h) ≠ (nb090_alpha_dummy_162 h) from (by
          unfold
            nb090_alpha_dummy_162;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0149
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_150 A) ≠
        (nb090_alpha_dummy_159 A) from (by
          unfold
            nb090_alpha_dummy_159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0146
                    A)
                  0)))) (show (nb090_alpha_dummy_153 h) ≠ (nb090_alpha_dummy_160 h) from (by
          unfold
            nb090_alpha_dummy_160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0147
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_143
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_145 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_151
        A) ≠ (nb090_alpha_dummy_163 A) from (by
          unfold
            nb090_alpha_dummy_163;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0152
                    A)
                  0)))) (show (nb090_alpha_dummy_154 h) ≠ (nb090_alpha_dummy_164 h) from (by
          unfold
            nb090_alpha_dummy_164;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0153
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_151 A) ≠
        (nb090_alpha_dummy_159 A) from (by
          unfold
            nb090_alpha_dummy_159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0150
                    A)
                  0)))) (show (nb090_alpha_dummy_154 h) ≠ (nb090_alpha_dummy_160 h) from (by
          unfold
            nb090_alpha_dummy_160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0151
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_151
        A) ≠ (nb090_alpha_dummy_163 A) from (by
          unfold
            nb090_alpha_dummy_163;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0152
                    A)
                  0)))) (show (nb090_alpha_dummy_154 h) ≠ (nb090_alpha_dummy_164 h) from (by
          unfold
            nb090_alpha_dummy_164;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0153
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_151 A) ≠
        (nb090_alpha_dummy_159 A) from (by
          unfold
            nb090_alpha_dummy_159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0150
                    A)
                  0)))) (show (nb090_alpha_dummy_154 h) ≠ (nb090_alpha_dummy_160 h) from (by
          unfold
            nb090_alpha_dummy_160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0151
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb090_alpha_dummy_143 A) ≠ (nb090_alpha_dummy_147 A)
                                        from (by
                                          unfold nb090_alpha_dummy_147;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0134 A) 0)))) (show
                                        (nb090_alpha_dummy_145 h) ≠ (nb090_alpha_dummy_148 h)
                                        from (by
                                          unfold nb090_alpha_dummy_148;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0135 h) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb090_alpha_dummy_147 A), (nb090_alpha_dummy_148 h)),
                                      ((nb090_alpha_dummy_143 A), (nb090_alpha_dummy_145 h)),
                                      ((nb090_alpha_dummy_144 A), (nb090_alpha_dummy_146 h)),
                                      ((nb090_alpha_dummy_136 A), (nb090_alpha_dummy_138 h)),
                                      ((nb090_alpha_dummy_135 A), (nb090_alpha_dummy_137 h)),
                                      ((nb090_alpha_dummy_141 A), (nb090_alpha_dummy_142 h)),
                                      ((nb090_alpha_dummy_139 A), (nb090_alpha_dummy_140 h)),
                                      ((nb090_alpha_dummy_130 A), (nb090_alpha_dummy_132 h)),
                                      ((nb090_alpha_dummy_129 A), (nb090_alpha_dummy_131 h)),
                                      ((nb090_alpha_dummy_133 A), (nb090_alpha_dummy_134 h)),
                                      ((nb090_alpha_dummy_051 A), (nb090_alpha_dummy_054 h)),
                                      ((nb090_alpha_dummy_050 A), (nb090_alpha_dummy_053 h)),
                                      ((nb090_alpha_dummy_049 A), (nb090_alpha_dummy_052 h)),
                                      ((nb090_alpha_dummy_055 A), (nb090_alpha_dummy_056 h)),
                                      ((nb090_alpha_dummy_047 A), (nb090_alpha_dummy_048 h)),
                                      ((nb090_alpha_dummy_045 A), (nb090_alpha_dummy_046 h)),
                                      ((nb090_alpha_dummy_000 A), h),
                                      ((nb090_alpha_dummy_002 A), v),
                                      ((nb090_alpha_dummy_001 A), u),
                                      ((nb090_alpha_dummy_003 A),
                                        (nb090_alpha_dummy_004 v u A h))]
                                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090_alpha_dummy_143 A) ≠ (nb090_alpha_dummy_147 A) from
                                      (by
                                        unfold nb090_alpha_dummy_147;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0134 A)
                                                0)))) (show (nb090_alpha_dummy_145 h) ≠
                                        (nb090_alpha_dummy_148 h) from (by
                                        unfold nb090_alpha_dummy_148;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0135 h)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb090_alpha_dummy_143 A) ≠ (nb090_alpha_dummy_147 A)
                                        from (by
                                          unfold nb090_alpha_dummy_147;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0134 A) 0)))) (show
                                        (nb090_alpha_dummy_145 h) ≠ (nb090_alpha_dummy_148 h)
                                        from (by
                                          unfold nb090_alpha_dummy_148;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0135 h) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb090_alpha_dummy_147 A), (nb090_alpha_dummy_148 h)),
                                      ((nb090_alpha_dummy_143 A), (nb090_alpha_dummy_145 h)),
                                      ((nb090_alpha_dummy_144 A), (nb090_alpha_dummy_146 h)),
                                      ((nb090_alpha_dummy_136 A), (nb090_alpha_dummy_138 h)),
                                      ((nb090_alpha_dummy_135 A), (nb090_alpha_dummy_137 h)),
                                      ((nb090_alpha_dummy_141 A), (nb090_alpha_dummy_142 h)),
                                      ((nb090_alpha_dummy_139 A), (nb090_alpha_dummy_140 h)),
                                      ((nb090_alpha_dummy_130 A), (nb090_alpha_dummy_132 h)),
                                      ((nb090_alpha_dummy_129 A), (nb090_alpha_dummy_131 h)),
                                      ((nb090_alpha_dummy_133 A), (nb090_alpha_dummy_134 h)),
                                      ((nb090_alpha_dummy_051 A), (nb090_alpha_dummy_054 h)),
                                      ((nb090_alpha_dummy_050 A), (nb090_alpha_dummy_053 h)),
                                      ((nb090_alpha_dummy_049 A), (nb090_alpha_dummy_052 h)),
                                      ((nb090_alpha_dummy_055 A), (nb090_alpha_dummy_056 h)),
                                      ((nb090_alpha_dummy_047 A), (nb090_alpha_dummy_048 h)),
                                      ((nb090_alpha_dummy_045 A), (nb090_alpha_dummy_046 h)),
                                      ((nb090_alpha_dummy_000 A), h),
                                      ((nb090_alpha_dummy_002 A), v),
                                      ((nb090_alpha_dummy_001 A), u),
                                      ((nb090_alpha_dummy_003 A),
                                        (nb090_alpha_dummy_004 v u A h))] (syn_cnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C090C001Part030`. -/


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
noncomputable def nb090_split_alpha_0006 (v : Var) (u : Var) (A : Class) (h : Var) :
    TAlphaWff
      [((nb090_alpha_dummy_169 A), (nb090_alpha_dummy_170 h)),
        ((nb090_alpha_dummy_167 A), (nb090_alpha_dummy_168 h)),
        ((nb090_alpha_dummy_136 A), (nb090_alpha_dummy_138 h)),
        ((nb090_alpha_dummy_135 A), (nb090_alpha_dummy_137 h)),
        ((nb090_alpha_dummy_165 A), (nb090_alpha_dummy_166 h)),
        ((nb090_alpha_dummy_139 A), (nb090_alpha_dummy_140 h)),
        ((nb090_alpha_dummy_130 A), (nb090_alpha_dummy_132 h)),
        ((nb090_alpha_dummy_129 A), (nb090_alpha_dummy_131 h)),
        ((nb090_alpha_dummy_133 A), (nb090_alpha_dummy_134 h)),
        ((nb090_alpha_dummy_051 A), (nb090_alpha_dummy_054 h)),
        ((nb090_alpha_dummy_050 A), (nb090_alpha_dummy_053 h)),
        ((nb090_alpha_dummy_049 A), (nb090_alpha_dummy_052 h)),
        ((nb090_alpha_dummy_055 A), (nb090_alpha_dummy_056 h)),
        ((nb090_alpha_dummy_047 A), (nb090_alpha_dummy_048 h)),
        ((nb090_alpha_dummy_045 A), (nb090_alpha_dummy_046 h)),
        ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
        ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
      (Wff.imp (Wff.classMem (Class.cv (nb090_alpha_dummy_169 A))
          (syn_cphi (Class.cv (nb090_alpha_dummy_136 A)))) (Wff.neg
          (Wff.classMem (Class.cv (nb090_alpha_dummy_169 A))
            (syn_cphi (Class.cv (nb090_alpha_dummy_136 A))))))
      (Wff.imp (Wff.classMem (Class.cv (nb090_alpha_dummy_170 h))
          (syn_cphi (Class.cv (nb090_alpha_dummy_138 h)))) (Wff.neg
          (Wff.classMem (Class.cv (nb090_alpha_dummy_170 h))
            (syn_cphi (Class.cv (nb090_alpha_dummy_138 h)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there
                  (show (nb090_alpha_dummy_136 A) ≠ (nb090_alpha_dummy_143 A) from (by
                      unfold nb090_alpha_dummy_143;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0132 A) 0))))
                  (show (nb090_alpha_dummy_138 h) ≠ (nb090_alpha_dummy_145 h) from (by
                      unfold nb090_alpha_dummy_145;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb090_support_mem_0133 h) 0))))
                  (TAlphaVar.there
                    (show (nb090_alpha_dummy_136 A) ≠ (nb090_alpha_dummy_144 A) from (by
                        unfold nb090_alpha_dummy_144;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0132 A) 1))))
                    (show (nb090_alpha_dummy_138 h) ≠ (nb090_alpha_dummy_146 h) from (by
                        unfold nb090_alpha_dummy_146;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0133 h) 1)))) (TAlphaVar.there
                      (show (nb090_alpha_dummy_136 A) ≠ (nb090_alpha_dummy_169 A) from (by
                          unfold nb090_alpha_dummy_169;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0162 A) 0))))
                      (show (nb090_alpha_dummy_138 h) ≠ (nb090_alpha_dummy_170 h) from (by
                          unfold nb090_alpha_dummy_170;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0163 h) 0))))
                      (TAlphaVar.there
                        (show (nb090_alpha_dummy_136 A) ≠ (nb090_alpha_dummy_167 A) from (by
                            unfold nb090_alpha_dummy_167;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0160 A) 0))))
                        (show (nb090_alpha_dummy_138 h) ≠ (nb090_alpha_dummy_168 h) from (by
                            unfold nb090_alpha_dummy_168;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0161 h) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_136 A))).fv)
                    (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_138 h))).fv)
                    (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb090_alpha_dummy_143 A) ≠ (nb090_alpha_dummy_150 A) from
                                      (by
                                        unfold nb090_alpha_dummy_150;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0136 A)
                                                1)))) (show (nb090_alpha_dummy_145 h) ≠
                                        (nb090_alpha_dummy_153 h) from (by
                                        unfold nb090_alpha_dummy_153;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb090_support_mem_0137 h)
                                                1)))) (TAlphaVar.there (show
                                        (nb090_alpha_dummy_143 A) ≠ (nb090_alpha_dummy_149 A)
                                        from (by
                                          unfold nb090_alpha_dummy_149;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0136 A) 0)))) (show
                                        (nb090_alpha_dummy_145 h) ≠ (nb090_alpha_dummy_152 h)
                                        from (by
                                          unfold nb090_alpha_dummy_152;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0137 h) 0))))
                                      (TAlphaVar.there (show (nb090_alpha_dummy_143 A) ≠
        (nb090_alpha_dummy_147 A) from (by
          unfold nb090_alpha_dummy_147;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0134 A) 0)))) (show (nb090_alpha_dummy_145 h) ≠
        (nb090_alpha_dummy_148 h) from (by
          unfold nb090_alpha_dummy_148;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0135 h) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.refl_of_closed [((nb090_alpha_dummy_151 A),
        (nb090_alpha_dummy_154 h)), ((nb090_alpha_dummy_150 A), (nb090_alpha_dummy_153 h)),
                                        ((nb090_alpha_dummy_149 A), (nb090_alpha_dummy_152 h)),
                                        ((nb090_alpha_dummy_147 A), (nb090_alpha_dummy_148 h)),
                                        ((nb090_alpha_dummy_143 A), (nb090_alpha_dummy_145 h)),
                                        ((nb090_alpha_dummy_144 A), (nb090_alpha_dummy_146 h)),
                                        ((nb090_alpha_dummy_169 A), (nb090_alpha_dummy_170 h)),
                                        ((nb090_alpha_dummy_167 A), (nb090_alpha_dummy_168 h)),
                                        ((nb090_alpha_dummy_136 A), (nb090_alpha_dummy_138 h)),
                                        ((nb090_alpha_dummy_135 A), (nb090_alpha_dummy_137 h)),
                                        ((nb090_alpha_dummy_165 A), (nb090_alpha_dummy_166 h)),
                                        ((nb090_alpha_dummy_139 A), (nb090_alpha_dummy_140 h)),
                                        ((nb090_alpha_dummy_130 A), (nb090_alpha_dummy_132 h)),
                                        ((nb090_alpha_dummy_129 A), (nb090_alpha_dummy_131 h)),
                                        ((nb090_alpha_dummy_133 A), (nb090_alpha_dummy_134 h)),
                                        ((nb090_alpha_dummy_051 A), (nb090_alpha_dummy_054 h)),
                                        ((nb090_alpha_dummy_050 A), (nb090_alpha_dummy_053 h)),
                                        ((nb090_alpha_dummy_049 A), (nb090_alpha_dummy_052 h)),
                                        ((nb090_alpha_dummy_055 A), (nb090_alpha_dummy_056 h)),
                                        ((nb090_alpha_dummy_047 A), (nb090_alpha_dummy_048 h)),
                                        ((nb090_alpha_dummy_045 A), (nb090_alpha_dummy_046 h)),
                                        ((nb090_alpha_dummy_000 A), h),
                                        ((nb090_alpha_dummy_002 A), v),
                                        ((nb090_alpha_dummy_001 A), u),
                                        ((nb090_alpha_dummy_003 A),
        (nb090_alpha_dummy_004 v u A h))] (syn_c1c) (by simp only [fv_syn_c1c])))
                                  (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cab
                                        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_150 A) ≠ (nb090_alpha_dummy_157 A) from (by
          unfold
            nb090_alpha_dummy_157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0140
                    A)
                  0)))) (show (nb090_alpha_dummy_153 h) ≠ (nb090_alpha_dummy_158 h) from (by
          unfold
            nb090_alpha_dummy_158;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0141
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_150 A) ≠
        (nb090_alpha_dummy_155 A) from (by
          unfold
            nb090_alpha_dummy_155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0138
                    A)
                  0)))) (show (nb090_alpha_dummy_153 h) ≠ (nb090_alpha_dummy_156 h) from (by
          unfold
            nb090_alpha_dummy_156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0139
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_143
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_145 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_151 A) ≠
        (nb090_alpha_dummy_157 A) from (by
          unfold
            nb090_alpha_dummy_157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0144
                    A)
                  0)))) (show (nb090_alpha_dummy_154 h) ≠ (nb090_alpha_dummy_158 h) from (by
          unfold
            nb090_alpha_dummy_158;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0145
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_151 A) ≠
        (nb090_alpha_dummy_155 A) from (by
          unfold
            nb090_alpha_dummy_155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0142
                    A)
                  0)))) (show (nb090_alpha_dummy_154 h) ≠ (nb090_alpha_dummy_156 h) from (by
          unfold
            nb090_alpha_dummy_156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0143
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_150 A) ≠ (nb090_alpha_dummy_157 A) from (by
          unfold
            nb090_alpha_dummy_157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0140
                    A)
                  0)))) (show (nb090_alpha_dummy_153 h) ≠ (nb090_alpha_dummy_158 h) from (by
          unfold
            nb090_alpha_dummy_158;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0141
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_150 A) ≠
        (nb090_alpha_dummy_155 A) from (by
          unfold
            nb090_alpha_dummy_155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0138
                    A)
                  0)))) (show (nb090_alpha_dummy_153 h) ≠ (nb090_alpha_dummy_156 h) from (by
          unfold
            nb090_alpha_dummy_156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0139
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_143
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_145 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_151 A) ≠
        (nb090_alpha_dummy_157 A) from (by
          unfold
            nb090_alpha_dummy_157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0144
                    A)
                  0)))) (show (nb090_alpha_dummy_154 h) ≠ (nb090_alpha_dummy_158 h) from (by
          unfold
            nb090_alpha_dummy_158;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0145
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_151 A) ≠
        (nb090_alpha_dummy_155 A) from (by
          unfold
            nb090_alpha_dummy_155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0142
                    A)
                  0)))) (show (nb090_alpha_dummy_154 h) ≠ (nb090_alpha_dummy_156 h) from (by
          unfold
            nb090_alpha_dummy_156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0143
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
                                        [((nb090_alpha_dummy_151 A), (nb090_alpha_dummy_154 h)),
        ((nb090_alpha_dummy_150 A), (nb090_alpha_dummy_153 h)), ((nb090_alpha_dummy_149 A),
        (nb090_alpha_dummy_152 h)), ((nb090_alpha_dummy_147 A), (nb090_alpha_dummy_148 h)),
        ((nb090_alpha_dummy_143 A), (nb090_alpha_dummy_145 h)), ((nb090_alpha_dummy_144 A),
        (nb090_alpha_dummy_146 h)), ((nb090_alpha_dummy_169 A), (nb090_alpha_dummy_170 h)),
        ((nb090_alpha_dummy_167 A), (nb090_alpha_dummy_168 h)), ((nb090_alpha_dummy_136 A),
        (nb090_alpha_dummy_138 h)), ((nb090_alpha_dummy_135 A), (nb090_alpha_dummy_137 h)),
        ((nb090_alpha_dummy_165 A), (nb090_alpha_dummy_166 h)), ((nb090_alpha_dummy_139 A),
        (nb090_alpha_dummy_140 h)), ((nb090_alpha_dummy_130 A), (nb090_alpha_dummy_132 h)),
        ((nb090_alpha_dummy_129 A), (nb090_alpha_dummy_131 h)), ((nb090_alpha_dummy_133 A),
        (nb090_alpha_dummy_134 h)), ((nb090_alpha_dummy_051 A), (nb090_alpha_dummy_054 h)),
        ((nb090_alpha_dummy_050 A), (nb090_alpha_dummy_053 h)), ((nb090_alpha_dummy_049 A),
        (nb090_alpha_dummy_052 h)), ((nb090_alpha_dummy_055 A), (nb090_alpha_dummy_056 h)),
        ((nb090_alpha_dummy_047 A), (nb090_alpha_dummy_048 h)), ((nb090_alpha_dummy_045 A),
        (nb090_alpha_dummy_046 h)), ((nb090_alpha_dummy_000 A), h),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
                                        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
                                      (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb090_alpha_dummy_143 A))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb090_alpha_dummy_145 h))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb090_alpha_dummy_143 A))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb090_alpha_dummy_145 h))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090_alpha_dummy_150 A) ≠ (nb090_alpha_dummy_161 A) from (by
          unfold
            nb090_alpha_dummy_161;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0148
                    A)
                  0)))) (show (nb090_alpha_dummy_153 h) ≠ (nb090_alpha_dummy_162 h) from (by
          unfold
            nb090_alpha_dummy_162;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0149
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_150 A) ≠
        (nb090_alpha_dummy_159 A) from (by
          unfold
            nb090_alpha_dummy_159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0146
                    A)
                  0)))) (show (nb090_alpha_dummy_153 h) ≠ (nb090_alpha_dummy_160 h) from (by
          unfold
            nb090_alpha_dummy_160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0147
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_143
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_145 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb090_alpha_dummy_150 A) ≠
        (nb090_alpha_dummy_161 A) from (by
          unfold
            nb090_alpha_dummy_161;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0148
                    A)
                  0)))) (show (nb090_alpha_dummy_153 h) ≠ (nb090_alpha_dummy_162 h) from (by
          unfold
            nb090_alpha_dummy_162;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0149
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_150 A) ≠
        (nb090_alpha_dummy_159 A) from (by
          unfold
            nb090_alpha_dummy_159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0146
                    A)
                  0)))) (show (nb090_alpha_dummy_153 h) ≠ (nb090_alpha_dummy_160 h) from (by
          unfold
            nb090_alpha_dummy_160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0147
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_143
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_145 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090_alpha_dummy_151 A) ≠ (nb090_alpha_dummy_163 A) from (by
          unfold
            nb090_alpha_dummy_163;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0152
                    A)
                  0)))) (show (nb090_alpha_dummy_154 h) ≠ (nb090_alpha_dummy_164 h) from (by
          unfold
            nb090_alpha_dummy_164;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0153
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_151 A) ≠
        (nb090_alpha_dummy_159 A) from (by
          unfold
            nb090_alpha_dummy_159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0150
                    A)
                  0)))) (show (nb090_alpha_dummy_154 h) ≠ (nb090_alpha_dummy_160 h) from (by
          unfold
            nb090_alpha_dummy_160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0151
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090_alpha_dummy_151 A) ≠ (nb090_alpha_dummy_163 A) from (by
          unfold
            nb090_alpha_dummy_163;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0152
                    A)
                  0)))) (show (nb090_alpha_dummy_154 h) ≠ (nb090_alpha_dummy_164 h) from (by
          unfold
            nb090_alpha_dummy_164;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0153
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_151 A) ≠
        (nb090_alpha_dummy_159 A) from (by
          unfold
            nb090_alpha_dummy_159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0150
                    A)
                  0)))) (show (nb090_alpha_dummy_154 h) ≠ (nb090_alpha_dummy_160 h) from (by
          unfold
            nb090_alpha_dummy_160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0151
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb090_alpha_dummy_143 A) ≠ (nb090_alpha_dummy_147 A) from (by
                                unfold nb090_alpha_dummy_147;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0134 A) 0))))
                            (show (nb090_alpha_dummy_145 h) ≠ (nb090_alpha_dummy_148 h) from (by
                                unfold nb090_alpha_dummy_148;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0135 h) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                          [((nb090_alpha_dummy_147 A), (nb090_alpha_dummy_148 h)),
                            ((nb090_alpha_dummy_143 A), (nb090_alpha_dummy_145 h)),
                            ((nb090_alpha_dummy_144 A), (nb090_alpha_dummy_146 h)),
                            ((nb090_alpha_dummy_169 A), (nb090_alpha_dummy_170 h)),
                            ((nb090_alpha_dummy_167 A), (nb090_alpha_dummy_168 h)),
                            ((nb090_alpha_dummy_136 A), (nb090_alpha_dummy_138 h)),
                            ((nb090_alpha_dummy_135 A), (nb090_alpha_dummy_137 h)),
                            ((nb090_alpha_dummy_165 A), (nb090_alpha_dummy_166 h)),
                            ((nb090_alpha_dummy_139 A), (nb090_alpha_dummy_140 h)),
                            ((nb090_alpha_dummy_130 A), (nb090_alpha_dummy_132 h)),
                            ((nb090_alpha_dummy_129 A), (nb090_alpha_dummy_131 h)),
                            ((nb090_alpha_dummy_133 A), (nb090_alpha_dummy_134 h)),
                            ((nb090_alpha_dummy_051 A), (nb090_alpha_dummy_054 h)),
                            ((nb090_alpha_dummy_050 A), (nb090_alpha_dummy_053 h)),
                            ((nb090_alpha_dummy_049 A), (nb090_alpha_dummy_052 h)),
                            ((nb090_alpha_dummy_055 A), (nb090_alpha_dummy_056 h)),
                            ((nb090_alpha_dummy_047 A), (nb090_alpha_dummy_048 h)),
                            ((nb090_alpha_dummy_045 A), (nb090_alpha_dummy_046 h)),
                            ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
                            ((nb090_alpha_dummy_001 A), u),
                            ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
                          (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb090_alpha_dummy_143 A) ≠ (nb090_alpha_dummy_147 A) from (by
                              unfold nb090_alpha_dummy_147;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0134 A) 0))))
                          (show (nb090_alpha_dummy_145 h) ≠ (nb090_alpha_dummy_148 h) from (by
                              unfold nb090_alpha_dummy_148;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0135 h) 0))))
                          (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb090_alpha_dummy_143 A) ≠ (nb090_alpha_dummy_147 A) from (by
                                unfold nb090_alpha_dummy_147;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0134 A) 0))))
                            (show (nb090_alpha_dummy_145 h) ≠ (nb090_alpha_dummy_148 h) from (by
                                unfold nb090_alpha_dummy_148;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0135 h) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                          [((nb090_alpha_dummy_147 A), (nb090_alpha_dummy_148 h)),
                            ((nb090_alpha_dummy_143 A), (nb090_alpha_dummy_145 h)),
                            ((nb090_alpha_dummy_144 A), (nb090_alpha_dummy_146 h)),
                            ((nb090_alpha_dummy_169 A), (nb090_alpha_dummy_170 h)),
                            ((nb090_alpha_dummy_167 A), (nb090_alpha_dummy_168 h)),
                            ((nb090_alpha_dummy_136 A), (nb090_alpha_dummy_138 h)),
                            ((nb090_alpha_dummy_135 A), (nb090_alpha_dummy_137 h)),
                            ((nb090_alpha_dummy_165 A), (nb090_alpha_dummy_166 h)),
                            ((nb090_alpha_dummy_139 A), (nb090_alpha_dummy_140 h)),
                            ((nb090_alpha_dummy_130 A), (nb090_alpha_dummy_132 h)),
                            ((nb090_alpha_dummy_129 A), (nb090_alpha_dummy_131 h)),
                            ((nb090_alpha_dummy_133 A), (nb090_alpha_dummy_134 h)),
                            ((nb090_alpha_dummy_051 A), (nb090_alpha_dummy_054 h)),
                            ((nb090_alpha_dummy_050 A), (nb090_alpha_dummy_053 h)),
                            ((nb090_alpha_dummy_049 A), (nb090_alpha_dummy_052 h)),
                            ((nb090_alpha_dummy_055 A), (nb090_alpha_dummy_056 h)),
                            ((nb090_alpha_dummy_047 A), (nb090_alpha_dummy_048 h)),
                            ((nb090_alpha_dummy_045 A), (nb090_alpha_dummy_046 h)),
                            ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
                            ((nb090_alpha_dummy_001 A), u),
                            ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
                          (syn_cnnc) (by simp only [fv_syn_cnnc])))))))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cv (TAlphaVar.there
                    (show (nb090_alpha_dummy_136 A) ≠ (nb090_alpha_dummy_143 A) from (by
                        unfold nb090_alpha_dummy_143;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0132 A) 0))))
                    (show (nb090_alpha_dummy_138 h) ≠ (nb090_alpha_dummy_145 h) from (by
                        unfold nb090_alpha_dummy_145;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb090_support_mem_0133 h) 0)))) (TAlphaVar.there
                      (show (nb090_alpha_dummy_136 A) ≠ (nb090_alpha_dummy_144 A) from (by
                          unfold nb090_alpha_dummy_144;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0132 A) 1))))
                      (show (nb090_alpha_dummy_138 h) ≠ (nb090_alpha_dummy_146 h) from (by
                          unfold nb090_alpha_dummy_146;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb090_support_mem_0133 h) 1))))
                      (TAlphaVar.there
                        (show (nb090_alpha_dummy_136 A) ≠ (nb090_alpha_dummy_169 A) from (by
                            unfold nb090_alpha_dummy_169;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0162 A) 0))))
                        (show (nb090_alpha_dummy_138 h) ≠ (nb090_alpha_dummy_170 h) from (by
                            unfold nb090_alpha_dummy_170;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb090_support_mem_0163 h) 0))))
                        (TAlphaVar.there
                          (show (nb090_alpha_dummy_136 A) ≠ (nb090_alpha_dummy_167 A) from (by
                              unfold nb090_alpha_dummy_167;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0160 A) 0))))
                          (show (nb090_alpha_dummy_138 h) ≠ (nb090_alpha_dummy_168 h) from (by
                              unfold nb090_alpha_dummy_168;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb090_support_mem_0161 h) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there
                    (freshVar_injective (((Class.cv (nb090_alpha_dummy_136 A))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb090_alpha_dummy_138 h))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                      (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (show (nb090_alpha_dummy_143 A) ≠
        (nb090_alpha_dummy_150 A) from (by
                                          unfold nb090_alpha_dummy_150;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0136 A) 1)))) (show
                                        (nb090_alpha_dummy_145 h) ≠ (nb090_alpha_dummy_153 h)
                                        from (by
                                          unfold nb090_alpha_dummy_153;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb090_support_mem_0137 h) 1))))
                                      (TAlphaVar.there (show (nb090_alpha_dummy_143 A) ≠
        (nb090_alpha_dummy_149 A) from (by
          unfold nb090_alpha_dummy_149;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0136 A) 0)))) (show (nb090_alpha_dummy_145 h) ≠
        (nb090_alpha_dummy_152 h) from (by
          unfold nb090_alpha_dummy_152;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0137 h) 0)))) (TAlphaVar.there (show
        (nb090_alpha_dummy_143 A) ≠ (nb090_alpha_dummy_147 A) from (by
          unfold nb090_alpha_dummy_147;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0134 A) 0)))) (show (nb090_alpha_dummy_145 h) ≠
        (nb090_alpha_dummy_148 h) from (by
          unfold nb090_alpha_dummy_148;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0135 h) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.refl_of_closed [((nb090_alpha_dummy_151 A),
        (nb090_alpha_dummy_154 h)), ((nb090_alpha_dummy_150 A), (nb090_alpha_dummy_153 h)),
        ((nb090_alpha_dummy_149 A), (nb090_alpha_dummy_152 h)), ((nb090_alpha_dummy_147 A),
        (nb090_alpha_dummy_148 h)), ((nb090_alpha_dummy_143 A), (nb090_alpha_dummy_145 h)),
        ((nb090_alpha_dummy_144 A), (nb090_alpha_dummy_146 h)), ((nb090_alpha_dummy_169 A),
        (nb090_alpha_dummy_170 h)), ((nb090_alpha_dummy_167 A), (nb090_alpha_dummy_168 h)),
        ((nb090_alpha_dummy_136 A), (nb090_alpha_dummy_138 h)), ((nb090_alpha_dummy_135 A),
        (nb090_alpha_dummy_137 h)), ((nb090_alpha_dummy_165 A), (nb090_alpha_dummy_166 h)),
        ((nb090_alpha_dummy_139 A), (nb090_alpha_dummy_140 h)), ((nb090_alpha_dummy_130 A),
        (nb090_alpha_dummy_132 h)), ((nb090_alpha_dummy_129 A), (nb090_alpha_dummy_131 h)),
        ((nb090_alpha_dummy_133 A), (nb090_alpha_dummy_134 h)), ((nb090_alpha_dummy_051 A),
        (nb090_alpha_dummy_054 h)), ((nb090_alpha_dummy_050 A), (nb090_alpha_dummy_053 h)),
        ((nb090_alpha_dummy_049 A), (nb090_alpha_dummy_052 h)), ((nb090_alpha_dummy_055 A),
        (nb090_alpha_dummy_056 h)), ((nb090_alpha_dummy_047 A), (nb090_alpha_dummy_048 h)),
        ((nb090_alpha_dummy_045 A), (nb090_alpha_dummy_046 h)), ((nb090_alpha_dummy_000 A), h),
        ((nb090_alpha_dummy_002 A), v), ((nb090_alpha_dummy_001 A), u),
        ((nb090_alpha_dummy_003 A), (nb090_alpha_dummy_004 v u A h))]
                                        (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
                                      (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090_alpha_dummy_150 A) ≠ (nb090_alpha_dummy_157 A) from (by
          unfold
            nb090_alpha_dummy_157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0140
                    A)
                  0)))) (show (nb090_alpha_dummy_153 h) ≠ (nb090_alpha_dummy_158 h) from (by
          unfold
            nb090_alpha_dummy_158;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0141
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_150 A) ≠
        (nb090_alpha_dummy_155 A) from (by
          unfold
            nb090_alpha_dummy_155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0138
                    A)
                  0)))) (show (nb090_alpha_dummy_153 h) ≠ (nb090_alpha_dummy_156 h) from (by
          unfold
            nb090_alpha_dummy_156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0139
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_143
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_145 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_151 A) ≠ (nb090_alpha_dummy_157 A) from (by
          unfold
            nb090_alpha_dummy_157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0144
                    A)
                  0)))) (show (nb090_alpha_dummy_154 h) ≠ (nb090_alpha_dummy_158 h) from (by
          unfold
            nb090_alpha_dummy_158;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0145
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_151 A) ≠
        (nb090_alpha_dummy_155 A) from (by
          unfold
            nb090_alpha_dummy_155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0142
                    A)
                  0)))) (show (nb090_alpha_dummy_154 h) ≠ (nb090_alpha_dummy_156 h) from (by
          unfold
            nb090_alpha_dummy_156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0143
                    h)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_150 A) ≠ (nb090_alpha_dummy_157 A) from (by
          unfold
            nb090_alpha_dummy_157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0140
                    A)
                  0)))) (show (nb090_alpha_dummy_153 h) ≠ (nb090_alpha_dummy_158 h) from (by
          unfold
            nb090_alpha_dummy_158;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0141
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_150 A) ≠
        (nb090_alpha_dummy_155 A) from (by
          unfold
            nb090_alpha_dummy_155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0138
                    A)
                  0)))) (show (nb090_alpha_dummy_153 h) ≠ (nb090_alpha_dummy_156 h) from (by
          unfold
            nb090_alpha_dummy_156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0139
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_143
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_145 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_151 A) ≠ (nb090_alpha_dummy_157 A) from (by
          unfold
            nb090_alpha_dummy_157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0144
                    A)
                  0)))) (show (nb090_alpha_dummy_154 h) ≠ (nb090_alpha_dummy_158 h) from (by
          unfold
            nb090_alpha_dummy_158;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0145
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_151 A) ≠
        (nb090_alpha_dummy_155 A) from (by
          unfold
            nb090_alpha_dummy_155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0142
                    A)
                  0)))) (show (nb090_alpha_dummy_154 h) ≠ (nb090_alpha_dummy_156 h) from (by
          unfold
            nb090_alpha_dummy_156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0143
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb090_alpha_dummy_151 A), (nb090_alpha_dummy_154 h)), ((nb090_alpha_dummy_150 A),
        (nb090_alpha_dummy_153 h)), ((nb090_alpha_dummy_149 A), (nb090_alpha_dummy_152 h)),
        ((nb090_alpha_dummy_147 A), (nb090_alpha_dummy_148 h)), ((nb090_alpha_dummy_143 A),
        (nb090_alpha_dummy_145 h)), ((nb090_alpha_dummy_144 A), (nb090_alpha_dummy_146 h)),
        ((nb090_alpha_dummy_169 A), (nb090_alpha_dummy_170 h)), ((nb090_alpha_dummy_167 A),
        (nb090_alpha_dummy_168 h)), ((nb090_alpha_dummy_136 A), (nb090_alpha_dummy_138 h)),
        ((nb090_alpha_dummy_135 A), (nb090_alpha_dummy_137 h)), ((nb090_alpha_dummy_165 A),
        (nb090_alpha_dummy_166 h)), ((nb090_alpha_dummy_139 A), (nb090_alpha_dummy_140 h)),
        ((nb090_alpha_dummy_130 A), (nb090_alpha_dummy_132 h)), ((nb090_alpha_dummy_129 A),
        (nb090_alpha_dummy_131 h)), ((nb090_alpha_dummy_133 A), (nb090_alpha_dummy_134 h)),
        ((nb090_alpha_dummy_051 A), (nb090_alpha_dummy_054 h)), ((nb090_alpha_dummy_050 A),
        (nb090_alpha_dummy_053 h)), ((nb090_alpha_dummy_049 A), (nb090_alpha_dummy_052 h)),
        ((nb090_alpha_dummy_055 A), (nb090_alpha_dummy_056 h)), ((nb090_alpha_dummy_047 A),
        (nb090_alpha_dummy_048 h)), ((nb090_alpha_dummy_045 A), (nb090_alpha_dummy_046 h)),
        ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
        ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A),
        (nb090_alpha_dummy_004 v u A h))] (syn_c0) (by simp only [fv_syn_c0])))
                                      (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb090_alpha_dummy_143 A))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb090_alpha_dummy_145 h))).fv ∪
        ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_143 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb090_alpha_dummy_145 h))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090_alpha_dummy_150 A) ≠ (nb090_alpha_dummy_161 A) from (by
          unfold
            nb090_alpha_dummy_161;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0148
                    A)
                  0)))) (show (nb090_alpha_dummy_153 h) ≠ (nb090_alpha_dummy_162 h) from (by
          unfold
            nb090_alpha_dummy_162;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0149
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_150 A) ≠
        (nb090_alpha_dummy_159 A) from (by
          unfold
            nb090_alpha_dummy_159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0146
                    A)
                  0)))) (show (nb090_alpha_dummy_153 h) ≠ (nb090_alpha_dummy_160 h) from (by
          unfold
            nb090_alpha_dummy_160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0147
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_143
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_145 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb090_alpha_dummy_150 A) ≠ (nb090_alpha_dummy_161 A) from (by
          unfold
            nb090_alpha_dummy_161;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0148
                    A)
                  0)))) (show (nb090_alpha_dummy_153 h) ≠ (nb090_alpha_dummy_162 h) from (by
          unfold
            nb090_alpha_dummy_162;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0149
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_150 A) ≠
        (nb090_alpha_dummy_159 A) from (by
          unfold
            nb090_alpha_dummy_159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0146
                    A)
                  0)))) (show (nb090_alpha_dummy_153 h) ≠ (nb090_alpha_dummy_160 h) from (by
          unfold
            nb090_alpha_dummy_160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0147
                    h)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb090_alpha_dummy_143
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb090_alpha_dummy_145 h))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090_alpha_dummy_151 A) ≠ (nb090_alpha_dummy_163 A) from (by
          unfold
            nb090_alpha_dummy_163;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0152
                    A)
                  0)))) (show (nb090_alpha_dummy_154 h) ≠ (nb090_alpha_dummy_164 h) from (by
          unfold
            nb090_alpha_dummy_164;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0153
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_151 A) ≠
        (nb090_alpha_dummy_159 A) from (by
          unfold
            nb090_alpha_dummy_159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0150
                    A)
                  0)))) (show (nb090_alpha_dummy_154 h) ≠ (nb090_alpha_dummy_160 h) from (by
          unfold
            nb090_alpha_dummy_160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0151
                    h)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb090_alpha_dummy_151 A) ≠ (nb090_alpha_dummy_163 A) from (by
          unfold
            nb090_alpha_dummy_163;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0152
                    A)
                  0)))) (show (nb090_alpha_dummy_154 h) ≠ (nb090_alpha_dummy_164 h) from (by
          unfold
            nb090_alpha_dummy_164;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0153
                    h)
                  0)))) (TAlphaVar.there (show (nb090_alpha_dummy_151 A) ≠
        (nb090_alpha_dummy_159 A) from (by
          unfold
            nb090_alpha_dummy_159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0150
                    A)
                  0)))) (show (nb090_alpha_dummy_154 h) ≠ (nb090_alpha_dummy_160 h) from (by
          unfold
            nb090_alpha_dummy_160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb090_support_mem_0151
                    h)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb090_alpha_dummy_143 A) ≠ (nb090_alpha_dummy_147 A) from
                                (by
                                  unfold nb090_alpha_dummy_147;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0134 A) 0))))
                              (show (nb090_alpha_dummy_145 h) ≠ (nb090_alpha_dummy_148 h) from
                                (by
                                  unfold nb090_alpha_dummy_148;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0135 h) 0))))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                            [((nb090_alpha_dummy_147 A), (nb090_alpha_dummy_148 h)),
                              ((nb090_alpha_dummy_143 A), (nb090_alpha_dummy_145 h)),
                              ((nb090_alpha_dummy_144 A), (nb090_alpha_dummy_146 h)),
                              ((nb090_alpha_dummy_169 A), (nb090_alpha_dummy_170 h)),
                              ((nb090_alpha_dummy_167 A), (nb090_alpha_dummy_168 h)),
                              ((nb090_alpha_dummy_136 A), (nb090_alpha_dummy_138 h)),
                              ((nb090_alpha_dummy_135 A), (nb090_alpha_dummy_137 h)),
                              ((nb090_alpha_dummy_165 A), (nb090_alpha_dummy_166 h)),
                              ((nb090_alpha_dummy_139 A), (nb090_alpha_dummy_140 h)),
                              ((nb090_alpha_dummy_130 A), (nb090_alpha_dummy_132 h)),
                              ((nb090_alpha_dummy_129 A), (nb090_alpha_dummy_131 h)),
                              ((nb090_alpha_dummy_133 A), (nb090_alpha_dummy_134 h)),
                              ((nb090_alpha_dummy_051 A), (nb090_alpha_dummy_054 h)),
                              ((nb090_alpha_dummy_050 A), (nb090_alpha_dummy_053 h)),
                              ((nb090_alpha_dummy_049 A), (nb090_alpha_dummy_052 h)),
                              ((nb090_alpha_dummy_055 A), (nb090_alpha_dummy_056 h)),
                              ((nb090_alpha_dummy_047 A), (nb090_alpha_dummy_048 h)),
                              ((nb090_alpha_dummy_045 A), (nb090_alpha_dummy_046 h)),
                              ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
                              ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A),
                                (nb090_alpha_dummy_004 v u A h))]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb090_alpha_dummy_143 A) ≠ (nb090_alpha_dummy_147 A) from (by
                                unfold nb090_alpha_dummy_147;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0134 A) 0))))
                            (show (nb090_alpha_dummy_145 h) ≠ (nb090_alpha_dummy_148 h) from (by
                                unfold nb090_alpha_dummy_148;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb090_support_mem_0135 h) 0))))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb090_alpha_dummy_143 A) ≠ (nb090_alpha_dummy_147 A) from
                                (by
                                  unfold nb090_alpha_dummy_147;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0134 A) 0))))
                              (show (nb090_alpha_dummy_145 h) ≠ (nb090_alpha_dummy_148 h) from
                                (by
                                  unfold nb090_alpha_dummy_148;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb090_support_mem_0135 h) 0))))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                            [((nb090_alpha_dummy_147 A), (nb090_alpha_dummy_148 h)),
                              ((nb090_alpha_dummy_143 A), (nb090_alpha_dummy_145 h)),
                              ((nb090_alpha_dummy_144 A), (nb090_alpha_dummy_146 h)),
                              ((nb090_alpha_dummy_169 A), (nb090_alpha_dummy_170 h)),
                              ((nb090_alpha_dummy_167 A), (nb090_alpha_dummy_168 h)),
                              ((nb090_alpha_dummy_136 A), (nb090_alpha_dummy_138 h)),
                              ((nb090_alpha_dummy_135 A), (nb090_alpha_dummy_137 h)),
                              ((nb090_alpha_dummy_165 A), (nb090_alpha_dummy_166 h)),
                              ((nb090_alpha_dummy_139 A), (nb090_alpha_dummy_140 h)),
                              ((nb090_alpha_dummy_130 A), (nb090_alpha_dummy_132 h)),
                              ((nb090_alpha_dummy_129 A), (nb090_alpha_dummy_131 h)),
                              ((nb090_alpha_dummy_133 A), (nb090_alpha_dummy_134 h)),
                              ((nb090_alpha_dummy_051 A), (nb090_alpha_dummy_054 h)),
                              ((nb090_alpha_dummy_050 A), (nb090_alpha_dummy_053 h)),
                              ((nb090_alpha_dummy_049 A), (nb090_alpha_dummy_052 h)),
                              ((nb090_alpha_dummy_055 A), (nb090_alpha_dummy_056 h)),
                              ((nb090_alpha_dummy_047 A), (nb090_alpha_dummy_048 h)),
                              ((nb090_alpha_dummy_045 A), (nb090_alpha_dummy_046 h)),
                              ((nb090_alpha_dummy_000 A), h), ((nb090_alpha_dummy_002 A), v),
                              ((nb090_alpha_dummy_001 A), u), ((nb090_alpha_dummy_003 A),
                                (nb090_alpha_dummy_004 v u A h))]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
