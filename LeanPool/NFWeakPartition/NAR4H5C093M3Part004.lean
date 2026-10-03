/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NAR4H5C093M3Part003

/-! NF weak partition development: NAR4H5C093M3Part004. -/


public section


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
noncomputable def nb093_split_alpha_0004 (A : Class) (r : Var) (d : Var) :
    TAlphaWff
      [((nb093_alpha_dummy_106 A), (nb093_alpha_dummy_107 r)),
        ((nb093_alpha_dummy_104 A), (nb093_alpha_dummy_105 r)),
        ((nb093_alpha_dummy_059 A), (nb093_alpha_dummy_061 r)),
        ((nb093_alpha_dummy_058 A), (nb093_alpha_dummy_060 r)),
        ((nb093_alpha_dummy_062 A), (nb093_alpha_dummy_063 r)),
        ((nb093_alpha_dummy_056 A), (nb093_alpha_dummy_057 r)),
        ((nb093_alpha_dummy_054 A), (nb093_alpha_dummy_055 r)),
        ((nb093_alpha_dummy_052 A), (nb093_alpha_dummy_053 r)),
        ((nb093_alpha_dummy_045 A), (nb093_alpha_dummy_047 r d)),
        ((nb093_alpha_dummy_044 A), (nb093_alpha_dummy_046 r d)),
        ((nb093_alpha_dummy_050 A), (nb093_alpha_dummy_051 r d)),
        ((nb093_alpha_dummy_048 A), (nb093_alpha_dummy_049 r d)),
        ((nb093_alpha_dummy_000 A), d), ((nb093_alpha_dummy_001 A), r),
        ((nb093_alpha_dummy_006 A), (nb093_alpha_dummy_007 r d)),
        ((nb093_alpha_dummy_004 A), (nb093_alpha_dummy_005 A r d)),
        ((nb093_alpha_dummy_002 A), (nb093_alpha_dummy_003 A r d))]
      (Wff.imp (Wff.classMem (Class.cv (nb093_alpha_dummy_106 A))
          (Class.cab (nb093_alpha_dummy_100 A)
            (syn_wrex (nb093_alpha_dummy_101 A) (Class.cv (nb093_alpha_dummy_059 A))
              (Wff.classEq (Class.cv (nb093_alpha_dummy_100 A))
                (syn_cphi (Class.cv (nb093_alpha_dummy_101 A))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb093_alpha_dummy_106 A))
            (Class.cab (nb093_alpha_dummy_100 A)
              (syn_wrex (nb093_alpha_dummy_101 A) (Class.cv (nb093_alpha_dummy_059 A))
                (Wff.classEq (Class.cv (nb093_alpha_dummy_100 A))
                  (syn_cphi (Class.cv (nb093_alpha_dummy_101 A)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb093_alpha_dummy_107 r))
          (Class.cab (nb093_alpha_dummy_102 r)
            (syn_wrex (nb093_alpha_dummy_103 r) (Class.cv (nb093_alpha_dummy_061 r))
              (Wff.classEq (Class.cv (nb093_alpha_dummy_102 r))
                (syn_cphi (Class.cv (nb093_alpha_dummy_103 r))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb093_alpha_dummy_107 r))
            (Class.cab (nb093_alpha_dummy_102 r)
              (syn_wrex (nb093_alpha_dummy_103 r) (Class.cv (nb093_alpha_dummy_061 r))
                (Wff.classEq (Class.cv (nb093_alpha_dummy_102 r))
                  (syn_cphi (Class.cv (nb093_alpha_dummy_103 r))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there
                  (show (nb093_alpha_dummy_059 A) ≠ (nb093_alpha_dummy_101 A) from (by
                      unfold nb093_alpha_dummy_101;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0094 A) 1))))
                  (show (nb093_alpha_dummy_061 r) ≠ (nb093_alpha_dummy_103 r) from (by
                      unfold nb093_alpha_dummy_103;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0096 r) 1))))
                  (TAlphaVar.there
                    (show (nb093_alpha_dummy_059 A) ≠ (nb093_alpha_dummy_100 A) from (by
                        unfold nb093_alpha_dummy_100;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb093_support_mem_0094 A) 0))))
                    (show (nb093_alpha_dummy_061 r) ≠ (nb093_alpha_dummy_102 r) from (by
                        unfold nb093_alpha_dummy_102;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb093_support_mem_0096 r) 0)))) (TAlphaVar.there
                      (show (nb093_alpha_dummy_059 A) ≠ (nb093_alpha_dummy_106 A) from (by
                          unfold nb093_alpha_dummy_106;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb093_support_mem_0098 A) 0))))
                      (show (nb093_alpha_dummy_061 r) ≠ (nb093_alpha_dummy_107 r) from (by
                          unfold nb093_alpha_dummy_107;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb093_support_mem_0099 r) 0))))
                      (TAlphaVar.there
                        (show (nb093_alpha_dummy_059 A) ≠ (nb093_alpha_dummy_104 A) from (by
                            unfold nb093_alpha_dummy_104;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb093_support_mem_0095 A) 0))))
                        (show (nb093_alpha_dummy_061 r) ≠ (nb093_alpha_dummy_105 r) from (by
                            unfold nb093_alpha_dummy_105;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb093_support_mem_0097 r) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb093_alpha_dummy_059 A))).fv ∪
                      ((Class.cv (nb093_alpha_dummy_058 A))).fv) (by decide))
                  (freshVar_injective (((Class.cv (nb093_alpha_dummy_061 r))).fv ∪
                      ((Class.cv (nb093_alpha_dummy_060 r))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb093_alpha_dummy_101 A) ≠ (nb093_alpha_dummy_108 A) from (by
                              unfold nb093_alpha_dummy_108;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb093_support_mem_0100 A) 0))))
                          (show (nb093_alpha_dummy_103 r) ≠ (nb093_alpha_dummy_110 r) from (by
                              unfold nb093_alpha_dummy_110;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb093_support_mem_0101 r) 0))))
                          (TAlphaVar.there
                            (show (nb093_alpha_dummy_101 A) ≠ (nb093_alpha_dummy_109 A) from (by
                                unfold nb093_alpha_dummy_109;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb093_support_mem_0100 A) 1))))
                            (show (nb093_alpha_dummy_103 r) ≠ (nb093_alpha_dummy_111 r) from (by
                                unfold nb093_alpha_dummy_111;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb093_support_mem_0101 r) 1))))
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb093_alpha_dummy_101 A))).fv)
                            (by decide))
                          (freshVar_injective (((Class.cv (nb093_alpha_dummy_103 r))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb093_alpha_dummy_108 A) ≠ (nb093_alpha_dummy_115 A) from (by
          unfold nb093_alpha_dummy_115;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0104 A) 1)))) (show (nb093_alpha_dummy_110 r) ≠
        (nb093_alpha_dummy_118 r) from (by
          unfold nb093_alpha_dummy_118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0105 r) 1)))) (TAlphaVar.there (show
        (nb093_alpha_dummy_108 A) ≠ (nb093_alpha_dummy_114 A) from (by
          unfold nb093_alpha_dummy_114;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0104 A) 0)))) (show (nb093_alpha_dummy_110 r) ≠
        (nb093_alpha_dummy_117 r) from (by
          unfold nb093_alpha_dummy_117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0105 r) 0)))) (TAlphaVar.there (show
        (nb093_alpha_dummy_108 A) ≠ (nb093_alpha_dummy_112 A) from (by
          unfold nb093_alpha_dummy_112;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0102 A)
                  0)))) (show (nb093_alpha_dummy_110 r) ≠ (nb093_alpha_dummy_113 r) from (by
          unfold nb093_alpha_dummy_113;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0103 r)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb093_alpha_dummy_116 A), (nb093_alpha_dummy_119 r)), ((nb093_alpha_dummy_115 A),
        (nb093_alpha_dummy_118 r)), ((nb093_alpha_dummy_114 A), (nb093_alpha_dummy_117 r)),
        ((nb093_alpha_dummy_112 A), (nb093_alpha_dummy_113 r)), ((nb093_alpha_dummy_108 A),
        (nb093_alpha_dummy_110 r)), ((nb093_alpha_dummy_109 A), (nb093_alpha_dummy_111 r)),
        ((nb093_alpha_dummy_101 A), (nb093_alpha_dummy_103 r)), ((nb093_alpha_dummy_100 A),
        (nb093_alpha_dummy_102 r)), ((nb093_alpha_dummy_106 A), (nb093_alpha_dummy_107 r)),
        ((nb093_alpha_dummy_104 A), (nb093_alpha_dummy_105 r)), ((nb093_alpha_dummy_059 A),
        (nb093_alpha_dummy_061 r)), ((nb093_alpha_dummy_058 A), (nb093_alpha_dummy_060 r)),
        ((nb093_alpha_dummy_062 A), (nb093_alpha_dummy_063 r)), ((nb093_alpha_dummy_056 A),
        (nb093_alpha_dummy_057 r)), ((nb093_alpha_dummy_054 A), (nb093_alpha_dummy_055 r)),
        ((nb093_alpha_dummy_052 A), (nb093_alpha_dummy_053 r)), ((nb093_alpha_dummy_045 A),
        (nb093_alpha_dummy_047 r d)), ((nb093_alpha_dummy_044 A), (nb093_alpha_dummy_046 r d)),
        ((nb093_alpha_dummy_050 A), (nb093_alpha_dummy_051 r d)), ((nb093_alpha_dummy_048 A),
        (nb093_alpha_dummy_049 r d)), ((nb093_alpha_dummy_000 A), d),
        ((nb093_alpha_dummy_001 A), r), ((nb093_alpha_dummy_006 A),
        (nb093_alpha_dummy_007 r d)), ((nb093_alpha_dummy_004 A),
        (nb093_alpha_dummy_005 A r d)), ((nb093_alpha_dummy_002 A),
        (nb093_alpha_dummy_003 A r d))] (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb093_alpha_dummy_115 A) ≠ (nb093_alpha_dummy_122 A) from (by
          unfold
            nb093_alpha_dummy_122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0108
                    A)
                  0)))) (show (nb093_alpha_dummy_118 r) ≠ (nb093_alpha_dummy_123 r) from (by
          unfold
            nb093_alpha_dummy_123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0109
                    r)
                  0)))) (TAlphaVar.there (show (nb093_alpha_dummy_115 A) ≠
        (nb093_alpha_dummy_120 A) from (by
          unfold
            nb093_alpha_dummy_120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0106
                    A)
                  0)))) (show (nb093_alpha_dummy_118 r) ≠ (nb093_alpha_dummy_121 r) from (by
          unfold
            nb093_alpha_dummy_121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0107
                    r)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093_alpha_dummy_108
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb093_alpha_dummy_110 r))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb093_alpha_dummy_116 A) ≠ (nb093_alpha_dummy_122 A) from (by
          unfold
            nb093_alpha_dummy_122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0112
                    A)
                  0)))) (show (nb093_alpha_dummy_119 r) ≠ (nb093_alpha_dummy_123 r) from (by
          unfold
            nb093_alpha_dummy_123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0113
                    r)
                  0)))) (TAlphaVar.there (show (nb093_alpha_dummy_116 A) ≠
        (nb093_alpha_dummy_120 A) from (by
          unfold
            nb093_alpha_dummy_120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0110
                    A)
                  0)))) (show (nb093_alpha_dummy_119 r) ≠ (nb093_alpha_dummy_121 r) from (by
          unfold
            nb093_alpha_dummy_121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0111
                    r)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb093_alpha_dummy_115 A) ≠ (nb093_alpha_dummy_122 A) from (by
          unfold
            nb093_alpha_dummy_122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0108
                    A)
                  0)))) (show (nb093_alpha_dummy_118 r) ≠ (nb093_alpha_dummy_123 r) from (by
          unfold
            nb093_alpha_dummy_123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0109
                    r)
                  0)))) (TAlphaVar.there (show (nb093_alpha_dummy_115 A) ≠
        (nb093_alpha_dummy_120 A) from (by
          unfold
            nb093_alpha_dummy_120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0106
                    A)
                  0)))) (show (nb093_alpha_dummy_118 r) ≠ (nb093_alpha_dummy_121 r) from (by
          unfold
            nb093_alpha_dummy_121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0107
                    r)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093_alpha_dummy_108
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb093_alpha_dummy_110 r))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb093_alpha_dummy_116 A) ≠ (nb093_alpha_dummy_122 A) from (by
          unfold
            nb093_alpha_dummy_122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0112
                    A)
                  0)))) (show (nb093_alpha_dummy_119 r) ≠ (nb093_alpha_dummy_123 r) from (by
          unfold
            nb093_alpha_dummy_123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0113
                    r)
                  0)))) (TAlphaVar.there (show (nb093_alpha_dummy_116 A) ≠
        (nb093_alpha_dummy_120 A) from (by
          unfold
            nb093_alpha_dummy_120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0110
                    A)
                  0)))) (show (nb093_alpha_dummy_119 r) ≠ (nb093_alpha_dummy_121 r) from (by
          unfold
            nb093_alpha_dummy_121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0111
                    r)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb093_alpha_dummy_116 A), (nb093_alpha_dummy_119 r)), ((nb093_alpha_dummy_115 A),
        (nb093_alpha_dummy_118 r)), ((nb093_alpha_dummy_114 A), (nb093_alpha_dummy_117 r)),
        ((nb093_alpha_dummy_112 A), (nb093_alpha_dummy_113 r)), ((nb093_alpha_dummy_108 A),
        (nb093_alpha_dummy_110 r)), ((nb093_alpha_dummy_109 A), (nb093_alpha_dummy_111 r)),
        ((nb093_alpha_dummy_101 A), (nb093_alpha_dummy_103 r)), ((nb093_alpha_dummy_100 A),
        (nb093_alpha_dummy_102 r)), ((nb093_alpha_dummy_106 A), (nb093_alpha_dummy_107 r)),
        ((nb093_alpha_dummy_104 A), (nb093_alpha_dummy_105 r)), ((nb093_alpha_dummy_059 A),
        (nb093_alpha_dummy_061 r)), ((nb093_alpha_dummy_058 A), (nb093_alpha_dummy_060 r)),
        ((nb093_alpha_dummy_062 A), (nb093_alpha_dummy_063 r)), ((nb093_alpha_dummy_056 A),
        (nb093_alpha_dummy_057 r)), ((nb093_alpha_dummy_054 A), (nb093_alpha_dummy_055 r)),
        ((nb093_alpha_dummy_052 A), (nb093_alpha_dummy_053 r)), ((nb093_alpha_dummy_045 A),
        (nb093_alpha_dummy_047 r d)), ((nb093_alpha_dummy_044 A), (nb093_alpha_dummy_046 r d)),
        ((nb093_alpha_dummy_050 A), (nb093_alpha_dummy_051 r d)), ((nb093_alpha_dummy_048 A),
        (nb093_alpha_dummy_049 r d)), ((nb093_alpha_dummy_000 A), d),
        ((nb093_alpha_dummy_001 A), r), ((nb093_alpha_dummy_006 A),
        (nb093_alpha_dummy_007 r d)), ((nb093_alpha_dummy_004 A),
        (nb093_alpha_dummy_005 A r d)), ((nb093_alpha_dummy_002 A),
        (nb093_alpha_dummy_003 A r d))] (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb093_alpha_dummy_108 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb093_alpha_dummy_110 r))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb093_alpha_dummy_108 A))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb093_alpha_dummy_110
        r))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb093_alpha_dummy_115 A) ≠ (nb093_alpha_dummy_126 A) from (by
          unfold
            nb093_alpha_dummy_126;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0116
                    A)
                  0)))) (show (nb093_alpha_dummy_118 r) ≠ (nb093_alpha_dummy_127 r) from (by
          unfold
            nb093_alpha_dummy_127;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0117
                    r)
                  0)))) (TAlphaVar.there (show (nb093_alpha_dummy_115 A) ≠
        (nb093_alpha_dummy_124 A) from (by
          unfold
            nb093_alpha_dummy_124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0114
                    A)
                  0)))) (show (nb093_alpha_dummy_118 r) ≠ (nb093_alpha_dummy_125 r) from (by
          unfold
            nb093_alpha_dummy_125;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0115
                    r)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093_alpha_dummy_108
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb093_alpha_dummy_110 r))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb093_alpha_dummy_115 A) ≠ (nb093_alpha_dummy_126 A) from (by
          unfold
            nb093_alpha_dummy_126;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0116
                    A)
                  0)))) (show (nb093_alpha_dummy_118 r) ≠ (nb093_alpha_dummy_127 r) from (by
          unfold
            nb093_alpha_dummy_127;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0117
                    r)
                  0)))) (TAlphaVar.there (show (nb093_alpha_dummy_115 A) ≠
        (nb093_alpha_dummy_124 A) from (by
          unfold
            nb093_alpha_dummy_124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0114
                    A)
                  0)))) (show (nb093_alpha_dummy_118 r) ≠ (nb093_alpha_dummy_125 r) from (by
          unfold
            nb093_alpha_dummy_125;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0115
                    r)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093_alpha_dummy_108
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb093_alpha_dummy_110 r))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb093_alpha_dummy_116
        A) ≠ (nb093_alpha_dummy_128 A) from (by
          unfold
            nb093_alpha_dummy_128;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0120
                    A)
                  0)))) (show (nb093_alpha_dummy_119 r) ≠ (nb093_alpha_dummy_129 r) from (by
          unfold
            nb093_alpha_dummy_129;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0121
                    r)
                  0)))) (TAlphaVar.there (show (nb093_alpha_dummy_116 A) ≠
        (nb093_alpha_dummy_124 A) from (by
          unfold
            nb093_alpha_dummy_124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0118
                    A)
                  0)))) (show (nb093_alpha_dummy_119 r) ≠ (nb093_alpha_dummy_125 r) from (by
          unfold
            nb093_alpha_dummy_125;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0119
                    r)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb093_alpha_dummy_116
        A) ≠ (nb093_alpha_dummy_128 A) from (by
          unfold
            nb093_alpha_dummy_128;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0120
                    A)
                  0)))) (show (nb093_alpha_dummy_119 r) ≠ (nb093_alpha_dummy_129 r) from (by
          unfold
            nb093_alpha_dummy_129;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0121
                    r)
                  0)))) (TAlphaVar.there (show (nb093_alpha_dummy_116 A) ≠
        (nb093_alpha_dummy_124 A) from (by
          unfold
            nb093_alpha_dummy_124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0118
                    A)
                  0)))) (show (nb093_alpha_dummy_119 r) ≠ (nb093_alpha_dummy_125 r) from (by
          unfold
            nb093_alpha_dummy_125;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0119
                    r)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb093_alpha_dummy_108 A) ≠ (nb093_alpha_dummy_112 A) from
                                      (by
                                        unfold nb093_alpha_dummy_112;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb093_support_mem_0102 A)
                                                0)))) (show (nb093_alpha_dummy_110 r) ≠
                                        (nb093_alpha_dummy_113 r) from (by
                                        unfold nb093_alpha_dummy_113;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb093_support_mem_0103 r)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
                                  [((nb093_alpha_dummy_112 A), (nb093_alpha_dummy_113 r)),
                                    ((nb093_alpha_dummy_108 A), (nb093_alpha_dummy_110 r)),
                                    ((nb093_alpha_dummy_109 A), (nb093_alpha_dummy_111 r)),
                                    ((nb093_alpha_dummy_101 A), (nb093_alpha_dummy_103 r)),
                                    ((nb093_alpha_dummy_100 A), (nb093_alpha_dummy_102 r)),
                                    ((nb093_alpha_dummy_106 A), (nb093_alpha_dummy_107 r)),
                                    ((nb093_alpha_dummy_104 A), (nb093_alpha_dummy_105 r)),
                                    ((nb093_alpha_dummy_059 A), (nb093_alpha_dummy_061 r)),
                                    ((nb093_alpha_dummy_058 A), (nb093_alpha_dummy_060 r)),
                                    ((nb093_alpha_dummy_062 A), (nb093_alpha_dummy_063 r)),
                                    ((nb093_alpha_dummy_056 A), (nb093_alpha_dummy_057 r)),
                                    ((nb093_alpha_dummy_054 A), (nb093_alpha_dummy_055 r)),
                                    ((nb093_alpha_dummy_052 A), (nb093_alpha_dummy_053 r)),
                                    ((nb093_alpha_dummy_045 A), (nb093_alpha_dummy_047 r d)),
                                    ((nb093_alpha_dummy_044 A), (nb093_alpha_dummy_046 r d)),
                                    ((nb093_alpha_dummy_050 A), (nb093_alpha_dummy_051 r d)),
                                    ((nb093_alpha_dummy_048 A), (nb093_alpha_dummy_049 r d)),
                                    ((nb093_alpha_dummy_000 A), d),
                                    ((nb093_alpha_dummy_001 A), r), ((nb093_alpha_dummy_006 A),
                                      (nb093_alpha_dummy_007 r d)), ((nb093_alpha_dummy_004 A),
                                      (nb093_alpha_dummy_005 A r d)),
                                    ((nb093_alpha_dummy_002 A), (nb093_alpha_dummy_003 A r d))]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb093_alpha_dummy_108 A) ≠ (nb093_alpha_dummy_112 A) from
                                    (by
                                      unfold nb093_alpha_dummy_112;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb093_support_mem_0102 A)
                                              0)))) (show
                                    (nb093_alpha_dummy_110 r) ≠ (nb093_alpha_dummy_113 r) from
                                    (by
                                      unfold nb093_alpha_dummy_113;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb093_support_mem_0103 r)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb093_alpha_dummy_108 A) ≠ (nb093_alpha_dummy_112 A) from
                                      (by
                                        unfold nb093_alpha_dummy_112;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb093_support_mem_0102 A)
                                                0)))) (show (nb093_alpha_dummy_110 r) ≠
                                        (nb093_alpha_dummy_113 r) from (by
                                        unfold nb093_alpha_dummy_113;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb093_support_mem_0103 r)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
                                  [((nb093_alpha_dummy_112 A), (nb093_alpha_dummy_113 r)),
                                    ((nb093_alpha_dummy_108 A), (nb093_alpha_dummy_110 r)),
                                    ((nb093_alpha_dummy_109 A), (nb093_alpha_dummy_111 r)),
                                    ((nb093_alpha_dummy_101 A), (nb093_alpha_dummy_103 r)),
                                    ((nb093_alpha_dummy_100 A), (nb093_alpha_dummy_102 r)),
                                    ((nb093_alpha_dummy_106 A), (nb093_alpha_dummy_107 r)),
                                    ((nb093_alpha_dummy_104 A), (nb093_alpha_dummy_105 r)),
                                    ((nb093_alpha_dummy_059 A), (nb093_alpha_dummy_061 r)),
                                    ((nb093_alpha_dummy_058 A), (nb093_alpha_dummy_060 r)),
                                    ((nb093_alpha_dummy_062 A), (nb093_alpha_dummy_063 r)),
                                    ((nb093_alpha_dummy_056 A), (nb093_alpha_dummy_057 r)),
                                    ((nb093_alpha_dummy_054 A), (nb093_alpha_dummy_055 r)),
                                    ((nb093_alpha_dummy_052 A), (nb093_alpha_dummy_053 r)),
                                    ((nb093_alpha_dummy_045 A), (nb093_alpha_dummy_047 r d)),
                                    ((nb093_alpha_dummy_044 A), (nb093_alpha_dummy_046 r d)),
                                    ((nb093_alpha_dummy_050 A), (nb093_alpha_dummy_051 r d)),
                                    ((nb093_alpha_dummy_048 A), (nb093_alpha_dummy_049 r d)),
                                    ((nb093_alpha_dummy_000 A), d),
                                    ((nb093_alpha_dummy_001 A), r), ((nb093_alpha_dummy_006 A),
                                      (nb093_alpha_dummy_007 r d)), ((nb093_alpha_dummy_004 A),
                                      (nb093_alpha_dummy_005 A r d)),
                                    ((nb093_alpha_dummy_002 A), (nb093_alpha_dummy_003 A r d))]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there
                    (show (nb093_alpha_dummy_059 A) ≠ (nb093_alpha_dummy_101 A) from (by
                        unfold nb093_alpha_dummy_101;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb093_support_mem_0094 A) 1))))
                    (show (nb093_alpha_dummy_061 r) ≠ (nb093_alpha_dummy_103 r) from (by
                        unfold nb093_alpha_dummy_103;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb093_support_mem_0096 r) 1)))) (TAlphaVar.there
                      (show (nb093_alpha_dummy_059 A) ≠ (nb093_alpha_dummy_100 A) from (by
                          unfold nb093_alpha_dummy_100;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb093_support_mem_0094 A) 0))))
                      (show (nb093_alpha_dummy_061 r) ≠ (nb093_alpha_dummy_102 r) from (by
                          unfold nb093_alpha_dummy_102;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb093_support_mem_0096 r) 0))))
                      (TAlphaVar.there
                        (show (nb093_alpha_dummy_059 A) ≠ (nb093_alpha_dummy_106 A) from (by
                            unfold nb093_alpha_dummy_106;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb093_support_mem_0098 A) 0))))
                        (show (nb093_alpha_dummy_061 r) ≠ (nb093_alpha_dummy_107 r) from (by
                            unfold nb093_alpha_dummy_107;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb093_support_mem_0099 r) 0))))
                        (TAlphaVar.there
                          (show (nb093_alpha_dummy_059 A) ≠ (nb093_alpha_dummy_104 A) from (by
                              unfold nb093_alpha_dummy_104;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb093_support_mem_0095 A) 0))))
                          (show (nb093_alpha_dummy_061 r) ≠ (nb093_alpha_dummy_105 r) from (by
                              unfold nb093_alpha_dummy_105;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb093_support_mem_0097 r) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb093_alpha_dummy_059 A))).fv ∪
                        ((Class.cv (nb093_alpha_dummy_058 A))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb093_alpha_dummy_061 r))).fv ∪
                        ((Class.cv (nb093_alpha_dummy_060 r))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb093_alpha_dummy_101 A) ≠ (nb093_alpha_dummy_108 A) from (by
                                unfold nb093_alpha_dummy_108;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb093_support_mem_0100 A) 0))))
                            (show (nb093_alpha_dummy_103 r) ≠ (nb093_alpha_dummy_110 r) from (by
                                unfold nb093_alpha_dummy_110;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb093_support_mem_0101 r) 0))))
                            (TAlphaVar.there
                              (show (nb093_alpha_dummy_101 A) ≠ (nb093_alpha_dummy_109 A) from
                                (by
                                  unfold nb093_alpha_dummy_109;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb093_support_mem_0100 A) 1))))
                              (show (nb093_alpha_dummy_103 r) ≠ (nb093_alpha_dummy_111 r) from
                                (by
                                  unfold nb093_alpha_dummy_111;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb093_support_mem_0101 r) 1))))
                              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb093_alpha_dummy_101 A))).fv) (by decide))
                            (freshVar_injective
                              (((Class.cv (nb093_alpha_dummy_103 r))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb093_alpha_dummy_108 A) ≠ (nb093_alpha_dummy_115 A) from (by
          unfold nb093_alpha_dummy_115;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0104 A) 1)))) (show (nb093_alpha_dummy_110 r) ≠
        (nb093_alpha_dummy_118 r) from (by
          unfold nb093_alpha_dummy_118;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0105 r) 1)))) (TAlphaVar.there (show
        (nb093_alpha_dummy_108 A) ≠ (nb093_alpha_dummy_114 A) from (by
          unfold nb093_alpha_dummy_114;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0104 A)
                  0)))) (show (nb093_alpha_dummy_110 r) ≠ (nb093_alpha_dummy_117 r) from (by
          unfold nb093_alpha_dummy_117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0105 r)
                  0)))) (TAlphaVar.there (show (nb093_alpha_dummy_108 A) ≠
        (nb093_alpha_dummy_112 A) from (by
          unfold nb093_alpha_dummy_112;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0102 A)
                  0)))) (show (nb093_alpha_dummy_110 r) ≠ (nb093_alpha_dummy_113 r) from (by
          unfold nb093_alpha_dummy_113;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0103 r)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb093_alpha_dummy_116 A), (nb093_alpha_dummy_119 r)), ((nb093_alpha_dummy_115 A),
        (nb093_alpha_dummy_118 r)), ((nb093_alpha_dummy_114 A), (nb093_alpha_dummy_117 r)),
        ((nb093_alpha_dummy_112 A), (nb093_alpha_dummy_113 r)), ((nb093_alpha_dummy_108 A),
        (nb093_alpha_dummy_110 r)), ((nb093_alpha_dummy_109 A), (nb093_alpha_dummy_111 r)),
        ((nb093_alpha_dummy_101 A), (nb093_alpha_dummy_103 r)), ((nb093_alpha_dummy_100 A),
        (nb093_alpha_dummy_102 r)), ((nb093_alpha_dummy_106 A), (nb093_alpha_dummy_107 r)),
        ((nb093_alpha_dummy_104 A), (nb093_alpha_dummy_105 r)), ((nb093_alpha_dummy_059 A),
        (nb093_alpha_dummy_061 r)), ((nb093_alpha_dummy_058 A), (nb093_alpha_dummy_060 r)),
        ((nb093_alpha_dummy_062 A), (nb093_alpha_dummy_063 r)), ((nb093_alpha_dummy_056 A),
        (nb093_alpha_dummy_057 r)), ((nb093_alpha_dummy_054 A), (nb093_alpha_dummy_055 r)),
        ((nb093_alpha_dummy_052 A), (nb093_alpha_dummy_053 r)), ((nb093_alpha_dummy_045 A),
        (nb093_alpha_dummy_047 r d)), ((nb093_alpha_dummy_044 A), (nb093_alpha_dummy_046 r d)),
        ((nb093_alpha_dummy_050 A), (nb093_alpha_dummy_051 r d)), ((nb093_alpha_dummy_048 A),
        (nb093_alpha_dummy_049 r d)), ((nb093_alpha_dummy_000 A), d),
        ((nb093_alpha_dummy_001 A), r), ((nb093_alpha_dummy_006 A),
        (nb093_alpha_dummy_007 r d)), ((nb093_alpha_dummy_004 A),
        (nb093_alpha_dummy_005 A r d)), ((nb093_alpha_dummy_002 A),
        (nb093_alpha_dummy_003 A r d))] (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb093_alpha_dummy_115 A) ≠ (nb093_alpha_dummy_122 A) from (by
          unfold
            nb093_alpha_dummy_122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0108
                    A)
                  0)))) (show (nb093_alpha_dummy_118 r) ≠ (nb093_alpha_dummy_123 r) from (by
          unfold
            nb093_alpha_dummy_123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0109
                    r)
                  0)))) (TAlphaVar.there (show (nb093_alpha_dummy_115 A) ≠
        (nb093_alpha_dummy_120 A) from (by
          unfold
            nb093_alpha_dummy_120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0106
                    A)
                  0)))) (show (nb093_alpha_dummy_118 r) ≠ (nb093_alpha_dummy_121 r) from (by
          unfold
            nb093_alpha_dummy_121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0107
                    r)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093_alpha_dummy_108
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb093_alpha_dummy_110 r))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb093_alpha_dummy_116 A) ≠ (nb093_alpha_dummy_122 A) from (by
          unfold
            nb093_alpha_dummy_122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0112
                    A)
                  0)))) (show (nb093_alpha_dummy_119 r) ≠ (nb093_alpha_dummy_123 r) from (by
          unfold
            nb093_alpha_dummy_123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0113
                    r)
                  0)))) (TAlphaVar.there (show (nb093_alpha_dummy_116 A) ≠
        (nb093_alpha_dummy_120 A) from (by
          unfold
            nb093_alpha_dummy_120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0110
                    A)
                  0)))) (show (nb093_alpha_dummy_119 r) ≠ (nb093_alpha_dummy_121 r) from (by
          unfold
            nb093_alpha_dummy_121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0111
                    r)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb093_alpha_dummy_115 A) ≠ (nb093_alpha_dummy_122 A) from (by
          unfold
            nb093_alpha_dummy_122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0108
                    A)
                  0)))) (show (nb093_alpha_dummy_118 r) ≠ (nb093_alpha_dummy_123 r) from (by
          unfold
            nb093_alpha_dummy_123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0109
                    r)
                  0)))) (TAlphaVar.there (show (nb093_alpha_dummy_115 A) ≠
        (nb093_alpha_dummy_120 A) from (by
          unfold
            nb093_alpha_dummy_120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0106
                    A)
                  0)))) (show (nb093_alpha_dummy_118 r) ≠ (nb093_alpha_dummy_121 r) from (by
          unfold
            nb093_alpha_dummy_121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0107
                    r)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093_alpha_dummy_108
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb093_alpha_dummy_110 r))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb093_alpha_dummy_116 A) ≠ (nb093_alpha_dummy_122 A) from (by
          unfold
            nb093_alpha_dummy_122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0112
                    A)
                  0)))) (show (nb093_alpha_dummy_119 r) ≠ (nb093_alpha_dummy_123 r) from (by
          unfold
            nb093_alpha_dummy_123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0113
                    r)
                  0)))) (TAlphaVar.there (show (nb093_alpha_dummy_116 A) ≠
        (nb093_alpha_dummy_120 A) from (by
          unfold
            nb093_alpha_dummy_120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0110
                    A)
                  0)))) (show (nb093_alpha_dummy_119 r) ≠ (nb093_alpha_dummy_121 r) from (by
          unfold
            nb093_alpha_dummy_121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0111
                    r)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb093_alpha_dummy_116 A), (nb093_alpha_dummy_119 r)), ((nb093_alpha_dummy_115 A),
        (nb093_alpha_dummy_118 r)), ((nb093_alpha_dummy_114 A), (nb093_alpha_dummy_117 r)),
        ((nb093_alpha_dummy_112 A), (nb093_alpha_dummy_113 r)), ((nb093_alpha_dummy_108 A),
        (nb093_alpha_dummy_110 r)), ((nb093_alpha_dummy_109 A), (nb093_alpha_dummy_111 r)),
        ((nb093_alpha_dummy_101 A), (nb093_alpha_dummy_103 r)), ((nb093_alpha_dummy_100 A),
        (nb093_alpha_dummy_102 r)), ((nb093_alpha_dummy_106 A), (nb093_alpha_dummy_107 r)),
        ((nb093_alpha_dummy_104 A), (nb093_alpha_dummy_105 r)), ((nb093_alpha_dummy_059 A),
        (nb093_alpha_dummy_061 r)), ((nb093_alpha_dummy_058 A), (nb093_alpha_dummy_060 r)),
        ((nb093_alpha_dummy_062 A), (nb093_alpha_dummy_063 r)), ((nb093_alpha_dummy_056 A),
        (nb093_alpha_dummy_057 r)), ((nb093_alpha_dummy_054 A), (nb093_alpha_dummy_055 r)),
        ((nb093_alpha_dummy_052 A), (nb093_alpha_dummy_053 r)), ((nb093_alpha_dummy_045 A),
        (nb093_alpha_dummy_047 r d)), ((nb093_alpha_dummy_044 A), (nb093_alpha_dummy_046 r d)),
        ((nb093_alpha_dummy_050 A), (nb093_alpha_dummy_051 r d)), ((nb093_alpha_dummy_048 A),
        (nb093_alpha_dummy_049 r d)), ((nb093_alpha_dummy_000 A), d),
        ((nb093_alpha_dummy_001 A), r), ((nb093_alpha_dummy_006 A),
        (nb093_alpha_dummy_007 r d)), ((nb093_alpha_dummy_004 A),
        (nb093_alpha_dummy_005 A r d)), ((nb093_alpha_dummy_002 A),
        (nb093_alpha_dummy_003 A r d))] (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv (nb093_alpha_dummy_108
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb093_alpha_dummy_110 r))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb093_alpha_dummy_108 A))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb093_alpha_dummy_110 r))).fv ∪
        ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb093_alpha_dummy_115
        A) ≠ (nb093_alpha_dummy_126 A) from (by
          unfold
            nb093_alpha_dummy_126;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0116
                    A)
                  0)))) (show (nb093_alpha_dummy_118 r) ≠ (nb093_alpha_dummy_127 r) from (by
          unfold
            nb093_alpha_dummy_127;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0117
                    r)
                  0)))) (TAlphaVar.there (show (nb093_alpha_dummy_115 A) ≠
        (nb093_alpha_dummy_124 A) from (by
          unfold
            nb093_alpha_dummy_124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0114
                    A)
                  0)))) (show (nb093_alpha_dummy_118 r) ≠ (nb093_alpha_dummy_125 r) from (by
          unfold
            nb093_alpha_dummy_125;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0115
                    r)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093_alpha_dummy_108
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb093_alpha_dummy_110 r))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb093_alpha_dummy_115 A) ≠ (nb093_alpha_dummy_126 A) from (by
          unfold
            nb093_alpha_dummy_126;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0116
                    A)
                  0)))) (show (nb093_alpha_dummy_118 r) ≠ (nb093_alpha_dummy_127 r) from (by
          unfold
            nb093_alpha_dummy_127;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0117
                    r)
                  0)))) (TAlphaVar.there (show (nb093_alpha_dummy_115 A) ≠
        (nb093_alpha_dummy_124 A) from (by
          unfold
            nb093_alpha_dummy_124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0114
                    A)
                  0)))) (show (nb093_alpha_dummy_118 r) ≠ (nb093_alpha_dummy_125 r) from (by
          unfold
            nb093_alpha_dummy_125;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0115
                    r)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093_alpha_dummy_108
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb093_alpha_dummy_110 r))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb093_alpha_dummy_116
        A) ≠ (nb093_alpha_dummy_128 A) from (by
          unfold
            nb093_alpha_dummy_128;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0120
                    A)
                  0)))) (show (nb093_alpha_dummy_119 r) ≠ (nb093_alpha_dummy_129 r) from (by
          unfold
            nb093_alpha_dummy_129;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0121
                    r)
                  0)))) (TAlphaVar.there (show (nb093_alpha_dummy_116 A) ≠
        (nb093_alpha_dummy_124 A) from (by
          unfold
            nb093_alpha_dummy_124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0118
                    A)
                  0)))) (show (nb093_alpha_dummy_119 r) ≠ (nb093_alpha_dummy_125 r) from (by
          unfold
            nb093_alpha_dummy_125;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0119
                    r)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb093_alpha_dummy_116
        A) ≠ (nb093_alpha_dummy_128 A) from (by
          unfold
            nb093_alpha_dummy_128;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0120
                    A)
                  0)))) (show (nb093_alpha_dummy_119 r) ≠ (nb093_alpha_dummy_129 r) from (by
          unfold
            nb093_alpha_dummy_129;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0121
                    r)
                  0)))) (TAlphaVar.there (show (nb093_alpha_dummy_116 A) ≠
        (nb093_alpha_dummy_124 A) from (by
          unfold
            nb093_alpha_dummy_124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0118
                    A)
                  0)))) (show (nb093_alpha_dummy_119 r) ≠ (nb093_alpha_dummy_125 r) from (by
          unfold
            nb093_alpha_dummy_125;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0119
                    r)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb093_alpha_dummy_108 A) ≠ (nb093_alpha_dummy_112 A)
                                        from (by
                                          unfold nb093_alpha_dummy_112;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb093_support_mem_0102 A) 0)))) (show
                                        (nb093_alpha_dummy_110 r) ≠ (nb093_alpha_dummy_113 r)
                                        from (by
                                          unfold nb093_alpha_dummy_113;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb093_support_mem_0103 r) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb093_alpha_dummy_112 A), (nb093_alpha_dummy_113 r)),
                                      ((nb093_alpha_dummy_108 A), (nb093_alpha_dummy_110 r)),
                                      ((nb093_alpha_dummy_109 A), (nb093_alpha_dummy_111 r)),
                                      ((nb093_alpha_dummy_101 A), (nb093_alpha_dummy_103 r)),
                                      ((nb093_alpha_dummy_100 A), (nb093_alpha_dummy_102 r)),
                                      ((nb093_alpha_dummy_106 A), (nb093_alpha_dummy_107 r)),
                                      ((nb093_alpha_dummy_104 A), (nb093_alpha_dummy_105 r)),
                                      ((nb093_alpha_dummy_059 A), (nb093_alpha_dummy_061 r)),
                                      ((nb093_alpha_dummy_058 A), (nb093_alpha_dummy_060 r)),
                                      ((nb093_alpha_dummy_062 A), (nb093_alpha_dummy_063 r)),
                                      ((nb093_alpha_dummy_056 A), (nb093_alpha_dummy_057 r)),
                                      ((nb093_alpha_dummy_054 A), (nb093_alpha_dummy_055 r)),
                                      ((nb093_alpha_dummy_052 A), (nb093_alpha_dummy_053 r)),
                                      ((nb093_alpha_dummy_045 A), (nb093_alpha_dummy_047 r d)),
                                      ((nb093_alpha_dummy_044 A), (nb093_alpha_dummy_046 r d)),
                                      ((nb093_alpha_dummy_050 A), (nb093_alpha_dummy_051 r d)),
                                      ((nb093_alpha_dummy_048 A), (nb093_alpha_dummy_049 r d)),
                                      ((nb093_alpha_dummy_000 A), d),
                                      ((nb093_alpha_dummy_001 A), r),
                                      ((nb093_alpha_dummy_006 A), (nb093_alpha_dummy_007 r d)),
                                      ((nb093_alpha_dummy_004 A),
                                        (nb093_alpha_dummy_005 A r d)),
                                      ((nb093_alpha_dummy_002 A),
                                        (nb093_alpha_dummy_003 A r d))]
                                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb093_alpha_dummy_108 A) ≠ (nb093_alpha_dummy_112 A) from
                                      (by
                                        unfold nb093_alpha_dummy_112;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb093_support_mem_0102 A)
                                                0)))) (show (nb093_alpha_dummy_110 r) ≠
                                        (nb093_alpha_dummy_113 r) from (by
                                        unfold nb093_alpha_dummy_113;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb093_support_mem_0103 r)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb093_alpha_dummy_108 A) ≠ (nb093_alpha_dummy_112 A)
                                        from (by
                                          unfold nb093_alpha_dummy_112;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb093_support_mem_0102 A) 0)))) (show
                                        (nb093_alpha_dummy_110 r) ≠ (nb093_alpha_dummy_113 r)
                                        from (by
                                          unfold nb093_alpha_dummy_113;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb093_support_mem_0103 r) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb093_alpha_dummy_112 A), (nb093_alpha_dummy_113 r)),
                                      ((nb093_alpha_dummy_108 A), (nb093_alpha_dummy_110 r)),
                                      ((nb093_alpha_dummy_109 A), (nb093_alpha_dummy_111 r)),
                                      ((nb093_alpha_dummy_101 A), (nb093_alpha_dummy_103 r)),
                                      ((nb093_alpha_dummy_100 A), (nb093_alpha_dummy_102 r)),
                                      ((nb093_alpha_dummy_106 A), (nb093_alpha_dummy_107 r)),
                                      ((nb093_alpha_dummy_104 A), (nb093_alpha_dummy_105 r)),
                                      ((nb093_alpha_dummy_059 A), (nb093_alpha_dummy_061 r)),
                                      ((nb093_alpha_dummy_058 A), (nb093_alpha_dummy_060 r)),
                                      ((nb093_alpha_dummy_062 A), (nb093_alpha_dummy_063 r)),
                                      ((nb093_alpha_dummy_056 A), (nb093_alpha_dummy_057 r)),
                                      ((nb093_alpha_dummy_054 A), (nb093_alpha_dummy_055 r)),
                                      ((nb093_alpha_dummy_052 A), (nb093_alpha_dummy_053 r)),
                                      ((nb093_alpha_dummy_045 A), (nb093_alpha_dummy_047 r d)),
                                      ((nb093_alpha_dummy_044 A), (nb093_alpha_dummy_046 r d)),
                                      ((nb093_alpha_dummy_050 A), (nb093_alpha_dummy_051 r d)),
                                      ((nb093_alpha_dummy_048 A), (nb093_alpha_dummy_049 r d)),
                                      ((nb093_alpha_dummy_000 A), d),
                                      ((nb093_alpha_dummy_001 A), r),
                                      ((nb093_alpha_dummy_006 A), (nb093_alpha_dummy_007 r d)),
                                      ((nb093_alpha_dummy_004 A),
                                        (nb093_alpha_dummy_005 A r d)),
                                      ((nb093_alpha_dummy_002 A),
                                        (nb093_alpha_dummy_003 A r d))] (syn_cnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))

@[expose]
noncomputable def nb093_split_alpha_0005 (A : Class) (r : Var) (d : Var) :
    TAlphaWff
      [((nb093_alpha_dummy_134 A), (nb093_alpha_dummy_135 r)),
        ((nb093_alpha_dummy_132 A), (nb093_alpha_dummy_133 r)),
        ((nb093_alpha_dummy_101 A), (nb093_alpha_dummy_103 r)),
        ((nb093_alpha_dummy_100 A), (nb093_alpha_dummy_102 r)),
        ((nb093_alpha_dummy_130 A), (nb093_alpha_dummy_131 r)),
        ((nb093_alpha_dummy_104 A), (nb093_alpha_dummy_105 r)),
        ((nb093_alpha_dummy_059 A), (nb093_alpha_dummy_061 r)),
        ((nb093_alpha_dummy_058 A), (nb093_alpha_dummy_060 r)),
        ((nb093_alpha_dummy_062 A), (nb093_alpha_dummy_063 r)),
        ((nb093_alpha_dummy_056 A), (nb093_alpha_dummy_057 r)),
        ((nb093_alpha_dummy_054 A), (nb093_alpha_dummy_055 r)),
        ((nb093_alpha_dummy_052 A), (nb093_alpha_dummy_053 r)),
        ((nb093_alpha_dummy_045 A), (nb093_alpha_dummy_047 r d)),
        ((nb093_alpha_dummy_044 A), (nb093_alpha_dummy_046 r d)),
        ((nb093_alpha_dummy_050 A), (nb093_alpha_dummy_051 r d)),
        ((nb093_alpha_dummy_048 A), (nb093_alpha_dummy_049 r d)),
        ((nb093_alpha_dummy_000 A), d), ((nb093_alpha_dummy_001 A), r),
        ((nb093_alpha_dummy_006 A), (nb093_alpha_dummy_007 r d)),
        ((nb093_alpha_dummy_004 A), (nb093_alpha_dummy_005 A r d)),
        ((nb093_alpha_dummy_002 A), (nb093_alpha_dummy_003 A r d))]
      (Wff.imp (Wff.classMem (Class.cv (nb093_alpha_dummy_134 A))
          (syn_cphi (Class.cv (nb093_alpha_dummy_101 A)))) (Wff.neg
          (Wff.classMem (Class.cv (nb093_alpha_dummy_134 A))
            (syn_cphi (Class.cv (nb093_alpha_dummy_101 A))))))
      (Wff.imp (Wff.classMem (Class.cv (nb093_alpha_dummy_135 r))
          (syn_cphi (Class.cv (nb093_alpha_dummy_103 r)))) (Wff.neg
          (Wff.classMem (Class.cv (nb093_alpha_dummy_135 r))
            (syn_cphi (Class.cv (nb093_alpha_dummy_103 r)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there
                  (show (nb093_alpha_dummy_101 A) ≠ (nb093_alpha_dummy_108 A) from (by
                      unfold nb093_alpha_dummy_108;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0100 A) 0))))
                  (show (nb093_alpha_dummy_103 r) ≠ (nb093_alpha_dummy_110 r) from (by
                      unfold nb093_alpha_dummy_110;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb093_support_mem_0101 r) 0))))
                  (TAlphaVar.there
                    (show (nb093_alpha_dummy_101 A) ≠ (nb093_alpha_dummy_109 A) from (by
                        unfold nb093_alpha_dummy_109;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb093_support_mem_0100 A) 1))))
                    (show (nb093_alpha_dummy_103 r) ≠ (nb093_alpha_dummy_111 r) from (by
                        unfold nb093_alpha_dummy_111;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb093_support_mem_0101 r) 1)))) (TAlphaVar.there
                      (show (nb093_alpha_dummy_101 A) ≠ (nb093_alpha_dummy_134 A) from (by
                          unfold nb093_alpha_dummy_134;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb093_support_mem_0130 A) 0))))
                      (show (nb093_alpha_dummy_103 r) ≠ (nb093_alpha_dummy_135 r) from (by
                          unfold nb093_alpha_dummy_135;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb093_support_mem_0131 r) 0))))
                      (TAlphaVar.there
                        (show (nb093_alpha_dummy_101 A) ≠ (nb093_alpha_dummy_132 A) from (by
                            unfold nb093_alpha_dummy_132;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb093_support_mem_0128 A) 0))))
                        (show (nb093_alpha_dummy_103 r) ≠ (nb093_alpha_dummy_133 r) from (by
                            unfold nb093_alpha_dummy_133;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb093_support_mem_0129 r) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb093_alpha_dummy_101 A))).fv)
                    (by decide)) (freshVar_injective (((Class.cv (nb093_alpha_dummy_103 r))).fv)
                    (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb093_alpha_dummy_108 A) ≠ (nb093_alpha_dummy_115 A) from
                                      (by
                                        unfold nb093_alpha_dummy_115;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb093_support_mem_0104 A)
                                                1)))) (show (nb093_alpha_dummy_110 r) ≠
                                        (nb093_alpha_dummy_118 r) from (by
                                        unfold nb093_alpha_dummy_118;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb093_support_mem_0105 r)
                                                1)))) (TAlphaVar.there (show
                                        (nb093_alpha_dummy_108 A) ≠ (nb093_alpha_dummy_114 A)
                                        from (by
                                          unfold nb093_alpha_dummy_114;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb093_support_mem_0104 A) 0)))) (show
                                        (nb093_alpha_dummy_110 r) ≠ (nb093_alpha_dummy_117 r)
                                        from (by
                                          unfold nb093_alpha_dummy_117;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb093_support_mem_0105 r) 0))))
                                      (TAlphaVar.there (show (nb093_alpha_dummy_108 A) ≠
        (nb093_alpha_dummy_112 A) from (by
          unfold nb093_alpha_dummy_112;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0102 A) 0)))) (show (nb093_alpha_dummy_110 r) ≠
        (nb093_alpha_dummy_113 r) from (by
          unfold nb093_alpha_dummy_113;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0103 r) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.refl_of_closed [((nb093_alpha_dummy_116 A),
        (nb093_alpha_dummy_119 r)), ((nb093_alpha_dummy_115 A), (nb093_alpha_dummy_118 r)),
                                        ((nb093_alpha_dummy_114 A), (nb093_alpha_dummy_117 r)),
                                        ((nb093_alpha_dummy_112 A), (nb093_alpha_dummy_113 r)),
                                        ((nb093_alpha_dummy_108 A), (nb093_alpha_dummy_110 r)),
                                        ((nb093_alpha_dummy_109 A), (nb093_alpha_dummy_111 r)),
                                        ((nb093_alpha_dummy_134 A), (nb093_alpha_dummy_135 r)),
                                        ((nb093_alpha_dummy_132 A), (nb093_alpha_dummy_133 r)),
                                        ((nb093_alpha_dummy_101 A), (nb093_alpha_dummy_103 r)),
                                        ((nb093_alpha_dummy_100 A), (nb093_alpha_dummy_102 r)),
                                        ((nb093_alpha_dummy_130 A), (nb093_alpha_dummy_131 r)),
                                        ((nb093_alpha_dummy_104 A), (nb093_alpha_dummy_105 r)),
                                        ((nb093_alpha_dummy_059 A), (nb093_alpha_dummy_061 r)),
                                        ((nb093_alpha_dummy_058 A), (nb093_alpha_dummy_060 r)),
                                        ((nb093_alpha_dummy_062 A), (nb093_alpha_dummy_063 r)),
                                        ((nb093_alpha_dummy_056 A), (nb093_alpha_dummy_057 r)),
                                        ((nb093_alpha_dummy_054 A), (nb093_alpha_dummy_055 r)),
                                        ((nb093_alpha_dummy_052 A), (nb093_alpha_dummy_053 r)),
                                        ((nb093_alpha_dummy_045 A),
        (nb093_alpha_dummy_047 r d)), ((nb093_alpha_dummy_044 A), (nb093_alpha_dummy_046 r d)),
                                        ((nb093_alpha_dummy_050 A),
        (nb093_alpha_dummy_051 r d)), ((nb093_alpha_dummy_048 A), (nb093_alpha_dummy_049 r d)),
                                        ((nb093_alpha_dummy_000 A), d),
                                        ((nb093_alpha_dummy_001 A), r),
                                        ((nb093_alpha_dummy_006 A),
        (nb093_alpha_dummy_007 r d)), ((nb093_alpha_dummy_004 A),
        (nb093_alpha_dummy_005 A r d)), ((nb093_alpha_dummy_002 A),
        (nb093_alpha_dummy_003 A r d))] (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
                                    (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb093_alpha_dummy_115 A) ≠ (nb093_alpha_dummy_122 A) from (by
          unfold
            nb093_alpha_dummy_122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0108
                    A)
                  0)))) (show (nb093_alpha_dummy_118 r) ≠ (nb093_alpha_dummy_123 r) from (by
          unfold
            nb093_alpha_dummy_123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0109
                    r)
                  0)))) (TAlphaVar.there (show (nb093_alpha_dummy_115 A) ≠
        (nb093_alpha_dummy_120 A) from (by
          unfold
            nb093_alpha_dummy_120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0106
                    A)
                  0)))) (show (nb093_alpha_dummy_118 r) ≠ (nb093_alpha_dummy_121 r) from (by
          unfold
            nb093_alpha_dummy_121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0107
                    r)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093_alpha_dummy_108
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb093_alpha_dummy_110 r))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb093_alpha_dummy_116 A) ≠
        (nb093_alpha_dummy_122 A) from (by
          unfold
            nb093_alpha_dummy_122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0112
                    A)
                  0)))) (show (nb093_alpha_dummy_119 r) ≠ (nb093_alpha_dummy_123 r) from (by
          unfold
            nb093_alpha_dummy_123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0113
                    r)
                  0)))) (TAlphaVar.there (show (nb093_alpha_dummy_116 A) ≠
        (nb093_alpha_dummy_120 A) from (by
          unfold
            nb093_alpha_dummy_120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0110
                    A)
                  0)))) (show (nb093_alpha_dummy_119 r) ≠ (nb093_alpha_dummy_121 r) from (by
          unfold
            nb093_alpha_dummy_121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0111
                    r)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb093_alpha_dummy_115 A) ≠ (nb093_alpha_dummy_122 A) from (by
          unfold
            nb093_alpha_dummy_122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0108
                    A)
                  0)))) (show (nb093_alpha_dummy_118 r) ≠ (nb093_alpha_dummy_123 r) from (by
          unfold
            nb093_alpha_dummy_123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0109
                    r)
                  0)))) (TAlphaVar.there (show (nb093_alpha_dummy_115 A) ≠
        (nb093_alpha_dummy_120 A) from (by
          unfold
            nb093_alpha_dummy_120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0106
                    A)
                  0)))) (show (nb093_alpha_dummy_118 r) ≠ (nb093_alpha_dummy_121 r) from (by
          unfold
            nb093_alpha_dummy_121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0107
                    r)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093_alpha_dummy_108
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb093_alpha_dummy_110 r))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb093_alpha_dummy_116 A) ≠
        (nb093_alpha_dummy_122 A) from (by
          unfold
            nb093_alpha_dummy_122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0112
                    A)
                  0)))) (show (nb093_alpha_dummy_119 r) ≠ (nb093_alpha_dummy_123 r) from (by
          unfold
            nb093_alpha_dummy_123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0113
                    r)
                  0)))) (TAlphaVar.there (show (nb093_alpha_dummy_116 A) ≠
        (nb093_alpha_dummy_120 A) from (by
          unfold
            nb093_alpha_dummy_120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0110
                    A)
                  0)))) (show (nb093_alpha_dummy_119 r) ≠ (nb093_alpha_dummy_121 r) from (by
          unfold
            nb093_alpha_dummy_121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0111
                    r)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
                                        [((nb093_alpha_dummy_116 A), (nb093_alpha_dummy_119 r)),
        ((nb093_alpha_dummy_115 A), (nb093_alpha_dummy_118 r)), ((nb093_alpha_dummy_114 A),
        (nb093_alpha_dummy_117 r)), ((nb093_alpha_dummy_112 A), (nb093_alpha_dummy_113 r)),
        ((nb093_alpha_dummy_108 A), (nb093_alpha_dummy_110 r)), ((nb093_alpha_dummy_109 A),
        (nb093_alpha_dummy_111 r)), ((nb093_alpha_dummy_134 A), (nb093_alpha_dummy_135 r)),
        ((nb093_alpha_dummy_132 A), (nb093_alpha_dummy_133 r)), ((nb093_alpha_dummy_101 A),
        (nb093_alpha_dummy_103 r)), ((nb093_alpha_dummy_100 A), (nb093_alpha_dummy_102 r)),
        ((nb093_alpha_dummy_130 A), (nb093_alpha_dummy_131 r)), ((nb093_alpha_dummy_104 A),
        (nb093_alpha_dummy_105 r)), ((nb093_alpha_dummy_059 A), (nb093_alpha_dummy_061 r)),
        ((nb093_alpha_dummy_058 A), (nb093_alpha_dummy_060 r)), ((nb093_alpha_dummy_062 A),
        (nb093_alpha_dummy_063 r)), ((nb093_alpha_dummy_056 A), (nb093_alpha_dummy_057 r)),
        ((nb093_alpha_dummy_054 A), (nb093_alpha_dummy_055 r)), ((nb093_alpha_dummy_052 A),
        (nb093_alpha_dummy_053 r)), ((nb093_alpha_dummy_045 A), (nb093_alpha_dummy_047 r d)),
        ((nb093_alpha_dummy_044 A), (nb093_alpha_dummy_046 r d)), ((nb093_alpha_dummy_050 A),
        (nb093_alpha_dummy_051 r d)), ((nb093_alpha_dummy_048 A), (nb093_alpha_dummy_049 r d)),
        ((nb093_alpha_dummy_000 A), d), ((nb093_alpha_dummy_001 A), r),
        ((nb093_alpha_dummy_006 A), (nb093_alpha_dummy_007 r d)), ((nb093_alpha_dummy_004 A),
        (nb093_alpha_dummy_005 A r d)), ((nb093_alpha_dummy_002 A),
        (nb093_alpha_dummy_003 A r d))] (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
                                      (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb093_alpha_dummy_108 A))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb093_alpha_dummy_110 r))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb093_alpha_dummy_108 A))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb093_alpha_dummy_110 r))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb093_alpha_dummy_115 A) ≠ (nb093_alpha_dummy_126 A) from (by
          unfold
            nb093_alpha_dummy_126;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0116
                    A)
                  0)))) (show (nb093_alpha_dummy_118 r) ≠ (nb093_alpha_dummy_127 r) from (by
          unfold
            nb093_alpha_dummy_127;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0117
                    r)
                  0)))) (TAlphaVar.there (show (nb093_alpha_dummy_115 A) ≠
        (nb093_alpha_dummy_124 A) from (by
          unfold
            nb093_alpha_dummy_124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0114
                    A)
                  0)))) (show (nb093_alpha_dummy_118 r) ≠ (nb093_alpha_dummy_125 r) from (by
          unfold
            nb093_alpha_dummy_125;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0115
                    r)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093_alpha_dummy_108
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb093_alpha_dummy_110 r))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb093_alpha_dummy_115 A) ≠
        (nb093_alpha_dummy_126 A) from (by
          unfold
            nb093_alpha_dummy_126;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0116
                    A)
                  0)))) (show (nb093_alpha_dummy_118 r) ≠ (nb093_alpha_dummy_127 r) from (by
          unfold
            nb093_alpha_dummy_127;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0117
                    r)
                  0)))) (TAlphaVar.there (show (nb093_alpha_dummy_115 A) ≠
        (nb093_alpha_dummy_124 A) from (by
          unfold
            nb093_alpha_dummy_124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0114
                    A)
                  0)))) (show (nb093_alpha_dummy_118 r) ≠ (nb093_alpha_dummy_125 r) from (by
          unfold
            nb093_alpha_dummy_125;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0115
                    r)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093_alpha_dummy_108
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb093_alpha_dummy_110 r))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb093_alpha_dummy_116 A) ≠ (nb093_alpha_dummy_128 A) from (by
          unfold
            nb093_alpha_dummy_128;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0120
                    A)
                  0)))) (show (nb093_alpha_dummy_119 r) ≠ (nb093_alpha_dummy_129 r) from (by
          unfold
            nb093_alpha_dummy_129;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0121
                    r)
                  0)))) (TAlphaVar.there (show (nb093_alpha_dummy_116 A) ≠
        (nb093_alpha_dummy_124 A) from (by
          unfold
            nb093_alpha_dummy_124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0118
                    A)
                  0)))) (show (nb093_alpha_dummy_119 r) ≠ (nb093_alpha_dummy_125 r) from (by
          unfold
            nb093_alpha_dummy_125;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0119
                    r)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb093_alpha_dummy_116 A) ≠ (nb093_alpha_dummy_128 A) from (by
          unfold
            nb093_alpha_dummy_128;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0120
                    A)
                  0)))) (show (nb093_alpha_dummy_119 r) ≠ (nb093_alpha_dummy_129 r) from (by
          unfold
            nb093_alpha_dummy_129;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0121
                    r)
                  0)))) (TAlphaVar.there (show (nb093_alpha_dummy_116 A) ≠
        (nb093_alpha_dummy_124 A) from (by
          unfold
            nb093_alpha_dummy_124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0118
                    A)
                  0)))) (show (nb093_alpha_dummy_119 r) ≠ (nb093_alpha_dummy_125 r) from (by
          unfold
            nb093_alpha_dummy_125;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0119
                    r)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb093_alpha_dummy_108 A) ≠ (nb093_alpha_dummy_112 A) from (by
                                unfold nb093_alpha_dummy_112;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb093_support_mem_0102 A) 0))))
                            (show (nb093_alpha_dummy_110 r) ≠ (nb093_alpha_dummy_113 r) from (by
                                unfold nb093_alpha_dummy_113;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb093_support_mem_0103 r) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                          [((nb093_alpha_dummy_112 A), (nb093_alpha_dummy_113 r)),
                            ((nb093_alpha_dummy_108 A), (nb093_alpha_dummy_110 r)),
                            ((nb093_alpha_dummy_109 A), (nb093_alpha_dummy_111 r)),
                            ((nb093_alpha_dummy_134 A), (nb093_alpha_dummy_135 r)),
                            ((nb093_alpha_dummy_132 A), (nb093_alpha_dummy_133 r)),
                            ((nb093_alpha_dummy_101 A), (nb093_alpha_dummy_103 r)),
                            ((nb093_alpha_dummy_100 A), (nb093_alpha_dummy_102 r)),
                            ((nb093_alpha_dummy_130 A), (nb093_alpha_dummy_131 r)),
                            ((nb093_alpha_dummy_104 A), (nb093_alpha_dummy_105 r)),
                            ((nb093_alpha_dummy_059 A), (nb093_alpha_dummy_061 r)),
                            ((nb093_alpha_dummy_058 A), (nb093_alpha_dummy_060 r)),
                            ((nb093_alpha_dummy_062 A), (nb093_alpha_dummy_063 r)),
                            ((nb093_alpha_dummy_056 A), (nb093_alpha_dummy_057 r)),
                            ((nb093_alpha_dummy_054 A), (nb093_alpha_dummy_055 r)),
                            ((nb093_alpha_dummy_052 A), (nb093_alpha_dummy_053 r)),
                            ((nb093_alpha_dummy_045 A), (nb093_alpha_dummy_047 r d)),
                            ((nb093_alpha_dummy_044 A), (nb093_alpha_dummy_046 r d)),
                            ((nb093_alpha_dummy_050 A), (nb093_alpha_dummy_051 r d)),
                            ((nb093_alpha_dummy_048 A), (nb093_alpha_dummy_049 r d)),
                            ((nb093_alpha_dummy_000 A), d), ((nb093_alpha_dummy_001 A), r),
                            ((nb093_alpha_dummy_006 A), (nb093_alpha_dummy_007 r d)),
                            ((nb093_alpha_dummy_004 A), (nb093_alpha_dummy_005 A r d)),
                            ((nb093_alpha_dummy_002 A), (nb093_alpha_dummy_003 A r d))]
                          (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb093_alpha_dummy_108 A) ≠ (nb093_alpha_dummy_112 A) from (by
                              unfold nb093_alpha_dummy_112;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb093_support_mem_0102 A) 0))))
                          (show (nb093_alpha_dummy_110 r) ≠ (nb093_alpha_dummy_113 r) from (by
                              unfold nb093_alpha_dummy_113;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb093_support_mem_0103 r) 0))))
                          (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb093_alpha_dummy_108 A) ≠ (nb093_alpha_dummy_112 A) from (by
                                unfold nb093_alpha_dummy_112;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb093_support_mem_0102 A) 0))))
                            (show (nb093_alpha_dummy_110 r) ≠ (nb093_alpha_dummy_113 r) from (by
                                unfold nb093_alpha_dummy_113;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb093_support_mem_0103 r) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                          [((nb093_alpha_dummy_112 A), (nb093_alpha_dummy_113 r)),
                            ((nb093_alpha_dummy_108 A), (nb093_alpha_dummy_110 r)),
                            ((nb093_alpha_dummy_109 A), (nb093_alpha_dummy_111 r)),
                            ((nb093_alpha_dummy_134 A), (nb093_alpha_dummy_135 r)),
                            ((nb093_alpha_dummy_132 A), (nb093_alpha_dummy_133 r)),
                            ((nb093_alpha_dummy_101 A), (nb093_alpha_dummy_103 r)),
                            ((nb093_alpha_dummy_100 A), (nb093_alpha_dummy_102 r)),
                            ((nb093_alpha_dummy_130 A), (nb093_alpha_dummy_131 r)),
                            ((nb093_alpha_dummy_104 A), (nb093_alpha_dummy_105 r)),
                            ((nb093_alpha_dummy_059 A), (nb093_alpha_dummy_061 r)),
                            ((nb093_alpha_dummy_058 A), (nb093_alpha_dummy_060 r)),
                            ((nb093_alpha_dummy_062 A), (nb093_alpha_dummy_063 r)),
                            ((nb093_alpha_dummy_056 A), (nb093_alpha_dummy_057 r)),
                            ((nb093_alpha_dummy_054 A), (nb093_alpha_dummy_055 r)),
                            ((nb093_alpha_dummy_052 A), (nb093_alpha_dummy_053 r)),
                            ((nb093_alpha_dummy_045 A), (nb093_alpha_dummy_047 r d)),
                            ((nb093_alpha_dummy_044 A), (nb093_alpha_dummy_046 r d)),
                            ((nb093_alpha_dummy_050 A), (nb093_alpha_dummy_051 r d)),
                            ((nb093_alpha_dummy_048 A), (nb093_alpha_dummy_049 r d)),
                            ((nb093_alpha_dummy_000 A), d), ((nb093_alpha_dummy_001 A), r),
                            ((nb093_alpha_dummy_006 A), (nb093_alpha_dummy_007 r d)),
                            ((nb093_alpha_dummy_004 A), (nb093_alpha_dummy_005 A r d)),
                            ((nb093_alpha_dummy_002 A), (nb093_alpha_dummy_003 A r d))]
                          (syn_cnnc) (by simp only [fv_syn_cnnc])))))))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cv (TAlphaVar.there
                    (show (nb093_alpha_dummy_101 A) ≠ (nb093_alpha_dummy_108 A) from (by
                        unfold nb093_alpha_dummy_108;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb093_support_mem_0100 A) 0))))
                    (show (nb093_alpha_dummy_103 r) ≠ (nb093_alpha_dummy_110 r) from (by
                        unfold nb093_alpha_dummy_110;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb093_support_mem_0101 r) 0)))) (TAlphaVar.there
                      (show (nb093_alpha_dummy_101 A) ≠ (nb093_alpha_dummy_109 A) from (by
                          unfold nb093_alpha_dummy_109;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb093_support_mem_0100 A) 1))))
                      (show (nb093_alpha_dummy_103 r) ≠ (nb093_alpha_dummy_111 r) from (by
                          unfold nb093_alpha_dummy_111;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb093_support_mem_0101 r) 1))))
                      (TAlphaVar.there
                        (show (nb093_alpha_dummy_101 A) ≠ (nb093_alpha_dummy_134 A) from (by
                            unfold nb093_alpha_dummy_134;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb093_support_mem_0130 A) 0))))
                        (show (nb093_alpha_dummy_103 r) ≠ (nb093_alpha_dummy_135 r) from (by
                            unfold nb093_alpha_dummy_135;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb093_support_mem_0131 r) 0))))
                        (TAlphaVar.there
                          (show (nb093_alpha_dummy_101 A) ≠ (nb093_alpha_dummy_132 A) from (by
                              unfold nb093_alpha_dummy_132;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb093_support_mem_0128 A) 0))))
                          (show (nb093_alpha_dummy_103 r) ≠ (nb093_alpha_dummy_133 r) from (by
                              unfold nb093_alpha_dummy_133;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb093_support_mem_0129 r) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there
                    (freshVar_injective (((Class.cv (nb093_alpha_dummy_101 A))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb093_alpha_dummy_103 r))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                      (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (show (nb093_alpha_dummy_108 A) ≠
        (nb093_alpha_dummy_115 A) from (by
                                          unfold nb093_alpha_dummy_115;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb093_support_mem_0104 A) 1)))) (show
                                        (nb093_alpha_dummy_110 r) ≠ (nb093_alpha_dummy_118 r)
                                        from (by
                                          unfold nb093_alpha_dummy_118;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb093_support_mem_0105 r) 1))))
                                      (TAlphaVar.there (show (nb093_alpha_dummy_108 A) ≠
        (nb093_alpha_dummy_114 A) from (by
          unfold nb093_alpha_dummy_114;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0104 A) 0)))) (show (nb093_alpha_dummy_110 r) ≠
        (nb093_alpha_dummy_117 r) from (by
          unfold nb093_alpha_dummy_117;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0105 r) 0)))) (TAlphaVar.there (show
        (nb093_alpha_dummy_108 A) ≠ (nb093_alpha_dummy_112 A) from (by
          unfold nb093_alpha_dummy_112;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0102 A) 0)))) (show (nb093_alpha_dummy_110 r) ≠
        (nb093_alpha_dummy_113 r) from (by
          unfold nb093_alpha_dummy_113;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0103 r) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.refl_of_closed [((nb093_alpha_dummy_116 A),
        (nb093_alpha_dummy_119 r)), ((nb093_alpha_dummy_115 A), (nb093_alpha_dummy_118 r)),
        ((nb093_alpha_dummy_114 A), (nb093_alpha_dummy_117 r)), ((nb093_alpha_dummy_112 A),
        (nb093_alpha_dummy_113 r)), ((nb093_alpha_dummy_108 A), (nb093_alpha_dummy_110 r)),
        ((nb093_alpha_dummy_109 A), (nb093_alpha_dummy_111 r)), ((nb093_alpha_dummy_134 A),
        (nb093_alpha_dummy_135 r)), ((nb093_alpha_dummy_132 A), (nb093_alpha_dummy_133 r)),
        ((nb093_alpha_dummy_101 A), (nb093_alpha_dummy_103 r)), ((nb093_alpha_dummy_100 A),
        (nb093_alpha_dummy_102 r)), ((nb093_alpha_dummy_130 A), (nb093_alpha_dummy_131 r)),
        ((nb093_alpha_dummy_104 A), (nb093_alpha_dummy_105 r)), ((nb093_alpha_dummy_059 A),
        (nb093_alpha_dummy_061 r)), ((nb093_alpha_dummy_058 A), (nb093_alpha_dummy_060 r)),
        ((nb093_alpha_dummy_062 A), (nb093_alpha_dummy_063 r)), ((nb093_alpha_dummy_056 A),
        (nb093_alpha_dummy_057 r)), ((nb093_alpha_dummy_054 A), (nb093_alpha_dummy_055 r)),
        ((nb093_alpha_dummy_052 A), (nb093_alpha_dummy_053 r)), ((nb093_alpha_dummy_045 A),
        (nb093_alpha_dummy_047 r d)), ((nb093_alpha_dummy_044 A), (nb093_alpha_dummy_046 r d)),
        ((nb093_alpha_dummy_050 A), (nb093_alpha_dummy_051 r d)), ((nb093_alpha_dummy_048 A),
        (nb093_alpha_dummy_049 r d)), ((nb093_alpha_dummy_000 A), d),
        ((nb093_alpha_dummy_001 A), r), ((nb093_alpha_dummy_006 A),
        (nb093_alpha_dummy_007 r d)), ((nb093_alpha_dummy_004 A),
        (nb093_alpha_dummy_005 A r d)), ((nb093_alpha_dummy_002 A),
        (nb093_alpha_dummy_003 A r d))] (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
                                      (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb093_alpha_dummy_115 A) ≠ (nb093_alpha_dummy_122 A) from (by
          unfold
            nb093_alpha_dummy_122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0108
                    A)
                  0)))) (show (nb093_alpha_dummy_118 r) ≠ (nb093_alpha_dummy_123 r) from (by
          unfold
            nb093_alpha_dummy_123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0109
                    r)
                  0)))) (TAlphaVar.there (show (nb093_alpha_dummy_115 A) ≠
        (nb093_alpha_dummy_120 A) from (by
          unfold
            nb093_alpha_dummy_120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0106
                    A)
                  0)))) (show (nb093_alpha_dummy_118 r) ≠ (nb093_alpha_dummy_121 r) from (by
          unfold
            nb093_alpha_dummy_121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0107
                    r)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093_alpha_dummy_108
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb093_alpha_dummy_110 r))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb093_alpha_dummy_116 A) ≠ (nb093_alpha_dummy_122 A) from (by
          unfold
            nb093_alpha_dummy_122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0112
                    A)
                  0)))) (show (nb093_alpha_dummy_119 r) ≠ (nb093_alpha_dummy_123 r) from (by
          unfold
            nb093_alpha_dummy_123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0113
                    r)
                  0)))) (TAlphaVar.there (show (nb093_alpha_dummy_116 A) ≠
        (nb093_alpha_dummy_120 A) from (by
          unfold
            nb093_alpha_dummy_120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0110
                    A)
                  0)))) (show (nb093_alpha_dummy_119 r) ≠ (nb093_alpha_dummy_121 r) from (by
          unfold
            nb093_alpha_dummy_121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0111
                    r)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb093_alpha_dummy_115 A) ≠ (nb093_alpha_dummy_122 A) from (by
          unfold
            nb093_alpha_dummy_122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0108
                    A)
                  0)))) (show (nb093_alpha_dummy_118 r) ≠ (nb093_alpha_dummy_123 r) from (by
          unfold
            nb093_alpha_dummy_123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0109
                    r)
                  0)))) (TAlphaVar.there (show (nb093_alpha_dummy_115 A) ≠
        (nb093_alpha_dummy_120 A) from (by
          unfold
            nb093_alpha_dummy_120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0106
                    A)
                  0)))) (show (nb093_alpha_dummy_118 r) ≠ (nb093_alpha_dummy_121 r) from (by
          unfold
            nb093_alpha_dummy_121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0107
                    r)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093_alpha_dummy_108
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb093_alpha_dummy_110 r))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb093_alpha_dummy_116 A) ≠ (nb093_alpha_dummy_122 A) from (by
          unfold
            nb093_alpha_dummy_122;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0112
                    A)
                  0)))) (show (nb093_alpha_dummy_119 r) ≠ (nb093_alpha_dummy_123 r) from (by
          unfold
            nb093_alpha_dummy_123;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0113
                    r)
                  0)))) (TAlphaVar.there (show (nb093_alpha_dummy_116 A) ≠
        (nb093_alpha_dummy_120 A) from (by
          unfold
            nb093_alpha_dummy_120;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0110
                    A)
                  0)))) (show (nb093_alpha_dummy_119 r) ≠ (nb093_alpha_dummy_121 r) from (by
          unfold
            nb093_alpha_dummy_121;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0111
                    r)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb093_alpha_dummy_116 A), (nb093_alpha_dummy_119 r)), ((nb093_alpha_dummy_115 A),
        (nb093_alpha_dummy_118 r)), ((nb093_alpha_dummy_114 A), (nb093_alpha_dummy_117 r)),
        ((nb093_alpha_dummy_112 A), (nb093_alpha_dummy_113 r)), ((nb093_alpha_dummy_108 A),
        (nb093_alpha_dummy_110 r)), ((nb093_alpha_dummy_109 A), (nb093_alpha_dummy_111 r)),
        ((nb093_alpha_dummy_134 A), (nb093_alpha_dummy_135 r)), ((nb093_alpha_dummy_132 A),
        (nb093_alpha_dummy_133 r)), ((nb093_alpha_dummy_101 A), (nb093_alpha_dummy_103 r)),
        ((nb093_alpha_dummy_100 A), (nb093_alpha_dummy_102 r)), ((nb093_alpha_dummy_130 A),
        (nb093_alpha_dummy_131 r)), ((nb093_alpha_dummy_104 A), (nb093_alpha_dummy_105 r)),
        ((nb093_alpha_dummy_059 A), (nb093_alpha_dummy_061 r)), ((nb093_alpha_dummy_058 A),
        (nb093_alpha_dummy_060 r)), ((nb093_alpha_dummy_062 A), (nb093_alpha_dummy_063 r)),
        ((nb093_alpha_dummy_056 A), (nb093_alpha_dummy_057 r)), ((nb093_alpha_dummy_054 A),
        (nb093_alpha_dummy_055 r)), ((nb093_alpha_dummy_052 A), (nb093_alpha_dummy_053 r)),
        ((nb093_alpha_dummy_045 A), (nb093_alpha_dummy_047 r d)), ((nb093_alpha_dummy_044 A),
        (nb093_alpha_dummy_046 r d)), ((nb093_alpha_dummy_050 A), (nb093_alpha_dummy_051 r d)),
        ((nb093_alpha_dummy_048 A), (nb093_alpha_dummy_049 r d)),
        ((nb093_alpha_dummy_000 A), d), ((nb093_alpha_dummy_001 A), r),
        ((nb093_alpha_dummy_006 A), (nb093_alpha_dummy_007 r d)), ((nb093_alpha_dummy_004 A),
        (nb093_alpha_dummy_005 A r d)), ((nb093_alpha_dummy_002 A),
        (nb093_alpha_dummy_003 A r d))] (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
                                        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb093_alpha_dummy_108 A))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb093_alpha_dummy_110 r))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb093_alpha_dummy_108 A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb093_alpha_dummy_110 r))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb093_alpha_dummy_115 A) ≠ (nb093_alpha_dummy_126 A) from (by
          unfold
            nb093_alpha_dummy_126;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0116
                    A)
                  0)))) (show (nb093_alpha_dummy_118 r) ≠ (nb093_alpha_dummy_127 r) from (by
          unfold
            nb093_alpha_dummy_127;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0117
                    r)
                  0)))) (TAlphaVar.there (show (nb093_alpha_dummy_115 A) ≠
        (nb093_alpha_dummy_124 A) from (by
          unfold
            nb093_alpha_dummy_124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0114
                    A)
                  0)))) (show (nb093_alpha_dummy_118 r) ≠ (nb093_alpha_dummy_125 r) from (by
          unfold
            nb093_alpha_dummy_125;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0115
                    r)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093_alpha_dummy_108
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb093_alpha_dummy_110 r))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb093_alpha_dummy_115 A) ≠ (nb093_alpha_dummy_126 A) from (by
          unfold
            nb093_alpha_dummy_126;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0116
                    A)
                  0)))) (show (nb093_alpha_dummy_118 r) ≠ (nb093_alpha_dummy_127 r) from (by
          unfold
            nb093_alpha_dummy_127;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0117
                    r)
                  0)))) (TAlphaVar.there (show (nb093_alpha_dummy_115 A) ≠
        (nb093_alpha_dummy_124 A) from (by
          unfold
            nb093_alpha_dummy_124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0114
                    A)
                  0)))) (show (nb093_alpha_dummy_118 r) ≠ (nb093_alpha_dummy_125 r) from (by
          unfold
            nb093_alpha_dummy_125;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0115
                    r)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093_alpha_dummy_108
        A))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb093_alpha_dummy_110 r))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb093_alpha_dummy_116 A) ≠ (nb093_alpha_dummy_128 A) from (by
          unfold
            nb093_alpha_dummy_128;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0120
                    A)
                  0)))) (show (nb093_alpha_dummy_119 r) ≠ (nb093_alpha_dummy_129 r) from (by
          unfold
            nb093_alpha_dummy_129;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0121
                    r)
                  0)))) (TAlphaVar.there (show (nb093_alpha_dummy_116 A) ≠
        (nb093_alpha_dummy_124 A) from (by
          unfold
            nb093_alpha_dummy_124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0118
                    A)
                  0)))) (show (nb093_alpha_dummy_119 r) ≠ (nb093_alpha_dummy_125 r) from (by
          unfold
            nb093_alpha_dummy_125;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0119
                    r)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb093_alpha_dummy_116 A) ≠ (nb093_alpha_dummy_128 A) from (by
          unfold
            nb093_alpha_dummy_128;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0120
                    A)
                  0)))) (show (nb093_alpha_dummy_119 r) ≠ (nb093_alpha_dummy_129 r) from (by
          unfold
            nb093_alpha_dummy_129;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0121
                    r)
                  0)))) (TAlphaVar.there (show (nb093_alpha_dummy_116 A) ≠
        (nb093_alpha_dummy_124 A) from (by
          unfold
            nb093_alpha_dummy_124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0118
                    A)
                  0)))) (show (nb093_alpha_dummy_119 r) ≠ (nb093_alpha_dummy_125 r) from (by
          unfold
            nb093_alpha_dummy_125;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0119
                    r)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb093_alpha_dummy_108 A) ≠ (nb093_alpha_dummy_112 A) from
                                (by
                                  unfold nb093_alpha_dummy_112;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb093_support_mem_0102 A) 0))))
                              (show (nb093_alpha_dummy_110 r) ≠ (nb093_alpha_dummy_113 r) from
                                (by
                                  unfold nb093_alpha_dummy_113;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb093_support_mem_0103 r) 0))))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                            [((nb093_alpha_dummy_112 A), (nb093_alpha_dummy_113 r)),
                              ((nb093_alpha_dummy_108 A), (nb093_alpha_dummy_110 r)),
                              ((nb093_alpha_dummy_109 A), (nb093_alpha_dummy_111 r)),
                              ((nb093_alpha_dummy_134 A), (nb093_alpha_dummy_135 r)),
                              ((nb093_alpha_dummy_132 A), (nb093_alpha_dummy_133 r)),
                              ((nb093_alpha_dummy_101 A), (nb093_alpha_dummy_103 r)),
                              ((nb093_alpha_dummy_100 A), (nb093_alpha_dummy_102 r)),
                              ((nb093_alpha_dummy_130 A), (nb093_alpha_dummy_131 r)),
                              ((nb093_alpha_dummy_104 A), (nb093_alpha_dummy_105 r)),
                              ((nb093_alpha_dummy_059 A), (nb093_alpha_dummy_061 r)),
                              ((nb093_alpha_dummy_058 A), (nb093_alpha_dummy_060 r)),
                              ((nb093_alpha_dummy_062 A), (nb093_alpha_dummy_063 r)),
                              ((nb093_alpha_dummy_056 A), (nb093_alpha_dummy_057 r)),
                              ((nb093_alpha_dummy_054 A), (nb093_alpha_dummy_055 r)),
                              ((nb093_alpha_dummy_052 A), (nb093_alpha_dummy_053 r)),
                              ((nb093_alpha_dummy_045 A), (nb093_alpha_dummy_047 r d)),
                              ((nb093_alpha_dummy_044 A), (nb093_alpha_dummy_046 r d)),
                              ((nb093_alpha_dummy_050 A), (nb093_alpha_dummy_051 r d)),
                              ((nb093_alpha_dummy_048 A), (nb093_alpha_dummy_049 r d)),
                              ((nb093_alpha_dummy_000 A), d), ((nb093_alpha_dummy_001 A), r),
                              ((nb093_alpha_dummy_006 A), (nb093_alpha_dummy_007 r d)),
                              ((nb093_alpha_dummy_004 A), (nb093_alpha_dummy_005 A r d)),
                              ((nb093_alpha_dummy_002 A), (nb093_alpha_dummy_003 A r d))]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb093_alpha_dummy_108 A) ≠ (nb093_alpha_dummy_112 A) from (by
                                unfold nb093_alpha_dummy_112;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb093_support_mem_0102 A) 0))))
                            (show (nb093_alpha_dummy_110 r) ≠ (nb093_alpha_dummy_113 r) from (by
                                unfold nb093_alpha_dummy_113;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb093_support_mem_0103 r) 0))))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb093_alpha_dummy_108 A) ≠ (nb093_alpha_dummy_112 A) from
                                (by
                                  unfold nb093_alpha_dummy_112;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb093_support_mem_0102 A) 0))))
                              (show (nb093_alpha_dummy_110 r) ≠ (nb093_alpha_dummy_113 r) from
                                (by
                                  unfold nb093_alpha_dummy_113;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb093_support_mem_0103 r) 0))))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                            [((nb093_alpha_dummy_112 A), (nb093_alpha_dummy_113 r)),
                              ((nb093_alpha_dummy_108 A), (nb093_alpha_dummy_110 r)),
                              ((nb093_alpha_dummy_109 A), (nb093_alpha_dummy_111 r)),
                              ((nb093_alpha_dummy_134 A), (nb093_alpha_dummy_135 r)),
                              ((nb093_alpha_dummy_132 A), (nb093_alpha_dummy_133 r)),
                              ((nb093_alpha_dummy_101 A), (nb093_alpha_dummy_103 r)),
                              ((nb093_alpha_dummy_100 A), (nb093_alpha_dummy_102 r)),
                              ((nb093_alpha_dummy_130 A), (nb093_alpha_dummy_131 r)),
                              ((nb093_alpha_dummy_104 A), (nb093_alpha_dummy_105 r)),
                              ((nb093_alpha_dummy_059 A), (nb093_alpha_dummy_061 r)),
                              ((nb093_alpha_dummy_058 A), (nb093_alpha_dummy_060 r)),
                              ((nb093_alpha_dummy_062 A), (nb093_alpha_dummy_063 r)),
                              ((nb093_alpha_dummy_056 A), (nb093_alpha_dummy_057 r)),
                              ((nb093_alpha_dummy_054 A), (nb093_alpha_dummy_055 r)),
                              ((nb093_alpha_dummy_052 A), (nb093_alpha_dummy_053 r)),
                              ((nb093_alpha_dummy_045 A), (nb093_alpha_dummy_047 r d)),
                              ((nb093_alpha_dummy_044 A), (nb093_alpha_dummy_046 r d)),
                              ((nb093_alpha_dummy_050 A), (nb093_alpha_dummy_051 r d)),
                              ((nb093_alpha_dummy_048 A), (nb093_alpha_dummy_049 r d)),
                              ((nb093_alpha_dummy_000 A), d), ((nb093_alpha_dummy_001 A), r),
                              ((nb093_alpha_dummy_006 A), (nb093_alpha_dummy_007 r d)),
                              ((nb093_alpha_dummy_004 A), (nb093_alpha_dummy_005 A r d)),
                              ((nb093_alpha_dummy_002 A), (nb093_alpha_dummy_003 A r d))]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))

@[expose]
noncomputable def nb093_split_alpha_0006 (A : Class) (r : Var) (d : Var)
    (dv_d_r : d ≠ r) :
    TAlphaWff
      [((nb093_alpha_dummy_056 A), (nb093_alpha_dummy_057 r)),
        ((nb093_alpha_dummy_054 A), (nb093_alpha_dummy_055 r)),
        ((nb093_alpha_dummy_052 A), (nb093_alpha_dummy_053 r)),
        ((nb093_alpha_dummy_045 A), (nb093_alpha_dummy_047 r d)),
        ((nb093_alpha_dummy_044 A), (nb093_alpha_dummy_046 r d)),
        ((nb093_alpha_dummy_050 A), (nb093_alpha_dummy_051 r d)),
        ((nb093_alpha_dummy_048 A), (nb093_alpha_dummy_049 r d)),
        ((nb093_alpha_dummy_000 A), d), ((nb093_alpha_dummy_001 A), r),
        ((nb093_alpha_dummy_006 A), (nb093_alpha_dummy_007 r d)),
        ((nb093_alpha_dummy_004 A), (nb093_alpha_dummy_005 A r d)),
        ((nb093_alpha_dummy_002 A), (nb093_alpha_dummy_003 A r d))]
      (Wff.imp (Wff.classMem (Class.cv (nb093_alpha_dummy_056 A))
          (syn_ccnv (Class.cv (nb093_alpha_dummy_001 A)))) (Wff.neg
          (Wff.classMem (Class.cv (nb093_alpha_dummy_056 A))
            (syn_ccnv (Class.cv (nb093_alpha_dummy_001 A))))))
      (Wff.imp (Wff.classMem (Class.cv (nb093_alpha_dummy_057 r)) (syn_ccnv (Class.cv r)))
        (Wff.neg
          (Wff.classMem (Class.cv (nb093_alpha_dummy_057 r)) (syn_ccnv (Class.cv r))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (Ne.symm
                      (show (nb093_alpha_dummy_059 A) ≠ (nb093_alpha_dummy_062 A) from (by
                          unfold nb093_alpha_dummy_062;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb093_support_mem_0054 A) 0))))) (Ne.symm
                      (show (nb093_alpha_dummy_061 r) ≠ (nb093_alpha_dummy_063 r) from (by
                          unfold nb093_alpha_dummy_063;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb093_support_mem_0055 r) 0)))))
                    (TAlphaVar.there (Ne.symm
                        (show (nb093_alpha_dummy_058 A) ≠ (nb093_alpha_dummy_062 A) from (by
                            unfold nb093_alpha_dummy_062;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb093_support_mem_0052 A) 0))))) (Ne.symm
                        (show (nb093_alpha_dummy_060 r) ≠ (nb093_alpha_dummy_063 r) from (by
                            unfold nb093_alpha_dummy_063;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb093_support_mem_0053 r) 0)))))
                      (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab
                          (TAlphaWff.neg (TAlphaWff.neg (nb093_split_alpha_0002 A r d)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb093_alpha_dummy_059 A) ≠ (nb093_alpha_dummy_065 A) from (by
          unfold nb093_alpha_dummy_065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0084 A) 1)))) (show (nb093_alpha_dummy_061 r) ≠
        (nb093_alpha_dummy_067 r) from (by
          unfold nb093_alpha_dummy_067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0086 r) 1)))) (TAlphaVar.there (show
        (nb093_alpha_dummy_059 A) ≠ (nb093_alpha_dummy_064 A) from (by
          unfold nb093_alpha_dummy_064;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0084 A) 0)))) (show (nb093_alpha_dummy_061 r) ≠
        (nb093_alpha_dummy_066 r) from (by
          unfold nb093_alpha_dummy_066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0086 r) 0)))) (TAlphaVar.there (show
        (nb093_alpha_dummy_059 A) ≠ (nb093_alpha_dummy_094 A) from (by
          unfold nb093_alpha_dummy_094;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0088 A)
                  0)))) (show (nb093_alpha_dummy_061 r) ≠ (nb093_alpha_dummy_095 r) from (by
          unfold nb093_alpha_dummy_095;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0089 r)
                  0)))) (TAlphaVar.there (show (nb093_alpha_dummy_059 A) ≠
        (nb093_alpha_dummy_068 A) from (by
          unfold nb093_alpha_dummy_068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0085 A)
                  0)))) (show (nb093_alpha_dummy_061 r) ≠ (nb093_alpha_dummy_069 r) from (by
          unfold nb093_alpha_dummy_069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0087 r)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb093_alpha_dummy_058 A))).fv ∪
        ((Class.cv (nb093_alpha_dummy_059 A))).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb093_alpha_dummy_060 r))).fv ∪ ((Class.cv (nb093_alpha_dummy_061 r))).fv)
        (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb093_split_alpha_0003 A r d))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb093_alpha_dummy_096 A), (nb093_alpha_dummy_097 r)), ((nb093_alpha_dummy_065 A),
        (nb093_alpha_dummy_067 r)), ((nb093_alpha_dummy_064 A), (nb093_alpha_dummy_066 r)),
        ((nb093_alpha_dummy_094 A), (nb093_alpha_dummy_095 r)), ((nb093_alpha_dummy_068 A),
        (nb093_alpha_dummy_069 r)), ((nb093_alpha_dummy_059 A), (nb093_alpha_dummy_061 r)),
        ((nb093_alpha_dummy_058 A), (nb093_alpha_dummy_060 r)), ((nb093_alpha_dummy_062 A),
        (nb093_alpha_dummy_063 r)), ((nb093_alpha_dummy_056 A), (nb093_alpha_dummy_057 r)),
        ((nb093_alpha_dummy_054 A), (nb093_alpha_dummy_055 r)), ((nb093_alpha_dummy_052 A),
        (nb093_alpha_dummy_053 r)), ((nb093_alpha_dummy_045 A), (nb093_alpha_dummy_047 r d)),
        ((nb093_alpha_dummy_044 A), (nb093_alpha_dummy_046 r d)), ((nb093_alpha_dummy_050 A),
        (nb093_alpha_dummy_051 r d)), ((nb093_alpha_dummy_048 A), (nb093_alpha_dummy_049 r d)),
        ((nb093_alpha_dummy_000 A), d), ((nb093_alpha_dummy_001 A), r),
        ((nb093_alpha_dummy_006 A), (nb093_alpha_dummy_007 r d)), ((nb093_alpha_dummy_004 A),
        (nb093_alpha_dummy_005 A r d)), ((nb093_alpha_dummy_002 A),
        (nb093_alpha_dummy_003 A r d))] (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl, fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb093_alpha_dummy_059 A) ≠ (nb093_alpha_dummy_065 A) from (by
          unfold nb093_alpha_dummy_065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0084 A) 1)))) (show (nb093_alpha_dummy_061 r) ≠
        (nb093_alpha_dummy_067 r) from (by
          unfold nb093_alpha_dummy_067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0086 r) 1)))) (TAlphaVar.there (show
        (nb093_alpha_dummy_059 A) ≠ (nb093_alpha_dummy_064 A) from (by
          unfold nb093_alpha_dummy_064;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0084 A) 0)))) (show (nb093_alpha_dummy_061 r) ≠
        (nb093_alpha_dummy_066 r) from (by
          unfold nb093_alpha_dummy_066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0086 r) 0)))) (TAlphaVar.there (show
        (nb093_alpha_dummy_059 A) ≠ (nb093_alpha_dummy_094 A) from (by
          unfold nb093_alpha_dummy_094;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0088 A)
                  0)))) (show (nb093_alpha_dummy_061 r) ≠ (nb093_alpha_dummy_095 r) from (by
          unfold nb093_alpha_dummy_095;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0089 r)
                  0)))) (TAlphaVar.there (show (nb093_alpha_dummy_059 A) ≠
        (nb093_alpha_dummy_068 A) from (by
          unfold nb093_alpha_dummy_068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0085 A)
                  0)))) (show (nb093_alpha_dummy_061 r) ≠ (nb093_alpha_dummy_069 r) from (by
          unfold nb093_alpha_dummy_069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0087 r)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb093_alpha_dummy_058 A))).fv ∪
        ((Class.cv (nb093_alpha_dummy_059 A))).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb093_alpha_dummy_060 r))).fv ∪ ((Class.cv (nb093_alpha_dummy_061 r))).fv)
        (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb093_split_alpha_0003 A r d))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb093_alpha_dummy_096 A), (nb093_alpha_dummy_097 r)), ((nb093_alpha_dummy_065 A),
        (nb093_alpha_dummy_067 r)), ((nb093_alpha_dummy_064 A), (nb093_alpha_dummy_066 r)),
        ((nb093_alpha_dummy_094 A), (nb093_alpha_dummy_095 r)), ((nb093_alpha_dummy_068 A),
        (nb093_alpha_dummy_069 r)), ((nb093_alpha_dummy_059 A), (nb093_alpha_dummy_061 r)),
        ((nb093_alpha_dummy_058 A), (nb093_alpha_dummy_060 r)), ((nb093_alpha_dummy_062 A),
        (nb093_alpha_dummy_063 r)), ((nb093_alpha_dummy_056 A), (nb093_alpha_dummy_057 r)),
        ((nb093_alpha_dummy_054 A), (nb093_alpha_dummy_055 r)), ((nb093_alpha_dummy_052 A),
        (nb093_alpha_dummy_053 r)), ((nb093_alpha_dummy_045 A), (nb093_alpha_dummy_047 r d)),
        ((nb093_alpha_dummy_044 A), (nb093_alpha_dummy_046 r d)), ((nb093_alpha_dummy_050 A),
        (nb093_alpha_dummy_051 r d)), ((nb093_alpha_dummy_048 A), (nb093_alpha_dummy_049 r d)),
        ((nb093_alpha_dummy_000 A), d), ((nb093_alpha_dummy_001 A), r),
        ((nb093_alpha_dummy_006 A), (nb093_alpha_dummy_007 r d)), ((nb093_alpha_dummy_004 A),
        (nb093_alpha_dummy_005 A r d)), ((nb093_alpha_dummy_002 A),
        (nb093_alpha_dummy_003 A r d))] (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl, fv_syn_csn,
            fv_syn_c0c]))))))))))))))))))) (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg
                    (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab
                          (TAlphaWff.neg (TAlphaWff.neg (nb093_split_alpha_0004 A r d)))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb093_alpha_dummy_058 A) ≠ (nb093_alpha_dummy_101 A) from (by
          unfold nb093_alpha_dummy_101;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0122 A) 1)))) (show (nb093_alpha_dummy_060 r) ≠
        (nb093_alpha_dummy_103 r) from (by
          unfold nb093_alpha_dummy_103;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0124 r) 1)))) (TAlphaVar.there (show
        (nb093_alpha_dummy_058 A) ≠ (nb093_alpha_dummy_100 A) from (by
          unfold nb093_alpha_dummy_100;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0122 A) 0)))) (show (nb093_alpha_dummy_060 r) ≠
        (nb093_alpha_dummy_102 r) from (by
          unfold nb093_alpha_dummy_102;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0124 r) 0)))) (TAlphaVar.there (show
        (nb093_alpha_dummy_058 A) ≠ (nb093_alpha_dummy_130 A) from (by
          unfold nb093_alpha_dummy_130;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0126 A)
                  0)))) (show (nb093_alpha_dummy_060 r) ≠ (nb093_alpha_dummy_131 r) from (by
          unfold nb093_alpha_dummy_131;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0127 r)
                  0)))) (TAlphaVar.there (show (nb093_alpha_dummy_058 A) ≠
        (nb093_alpha_dummy_104 A) from (by
          unfold nb093_alpha_dummy_104;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0123 A)
                  0)))) (show (nb093_alpha_dummy_060 r) ≠ (nb093_alpha_dummy_105 r) from (by
          unfold nb093_alpha_dummy_105;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0125 r)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb093_alpha_dummy_001 A))).fv) (by decide)) (freshVar_injective
        (((Class.cv r)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq
                                        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb093_alpha_dummy_059 A))).fv ∪ ((Class.cv (nb093_alpha_dummy_058 A))).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb093_alpha_dummy_061 r))).fv ∪
        ((Class.cv (nb093_alpha_dummy_060 r))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb093_split_alpha_0005 A r d))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb093_alpha_dummy_132 A), (nb093_alpha_dummy_133 r)), ((nb093_alpha_dummy_101 A),
        (nb093_alpha_dummy_103 r)), ((nb093_alpha_dummy_100 A), (nb093_alpha_dummy_102 r)),
        ((nb093_alpha_dummy_130 A), (nb093_alpha_dummy_131 r)), ((nb093_alpha_dummy_104 A),
        (nb093_alpha_dummy_105 r)), ((nb093_alpha_dummy_059 A), (nb093_alpha_dummy_061 r)),
        ((nb093_alpha_dummy_058 A), (nb093_alpha_dummy_060 r)), ((nb093_alpha_dummy_062 A),
        (nb093_alpha_dummy_063 r)), ((nb093_alpha_dummy_056 A), (nb093_alpha_dummy_057 r)),
        ((nb093_alpha_dummy_054 A), (nb093_alpha_dummy_055 r)), ((nb093_alpha_dummy_052 A),
        (nb093_alpha_dummy_053 r)), ((nb093_alpha_dummy_045 A), (nb093_alpha_dummy_047 r d)),
        ((nb093_alpha_dummy_044 A), (nb093_alpha_dummy_046 r d)), ((nb093_alpha_dummy_050 A),
        (nb093_alpha_dummy_051 r d)), ((nb093_alpha_dummy_048 A), (nb093_alpha_dummy_049 r d)),
        ((nb093_alpha_dummy_000 A), d), ((nb093_alpha_dummy_001 A), r),
        ((nb093_alpha_dummy_006 A), (nb093_alpha_dummy_007 r d)), ((nb093_alpha_dummy_004 A),
        (nb093_alpha_dummy_005 A r d)), ((nb093_alpha_dummy_002 A),
        (nb093_alpha_dummy_003 A r d))] (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl, fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb093_alpha_dummy_058 A) ≠ (nb093_alpha_dummy_101 A) from (by
          unfold nb093_alpha_dummy_101;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0122 A) 1)))) (show (nb093_alpha_dummy_060 r) ≠
        (nb093_alpha_dummy_103 r) from (by
          unfold nb093_alpha_dummy_103;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0124 r) 1)))) (TAlphaVar.there (show
        (nb093_alpha_dummy_058 A) ≠ (nb093_alpha_dummy_100 A) from (by
          unfold nb093_alpha_dummy_100;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0122 A) 0)))) (show (nb093_alpha_dummy_060 r) ≠
        (nb093_alpha_dummy_102 r) from (by
          unfold nb093_alpha_dummy_102;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0124 r) 0)))) (TAlphaVar.there (show
        (nb093_alpha_dummy_058 A) ≠ (nb093_alpha_dummy_130 A) from (by
          unfold nb093_alpha_dummy_130;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0126 A)
                  0)))) (show (nb093_alpha_dummy_060 r) ≠ (nb093_alpha_dummy_131 r) from (by
          unfold nb093_alpha_dummy_131;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0127 r)
                  0)))) (TAlphaVar.there (show (nb093_alpha_dummy_058 A) ≠
        (nb093_alpha_dummy_104 A) from (by
          unfold nb093_alpha_dummy_104;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0123 A)
                  0)))) (show (nb093_alpha_dummy_060 r) ≠ (nb093_alpha_dummy_105 r) from (by
          unfold nb093_alpha_dummy_105;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0125 r)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb093_alpha_dummy_001 A))).fv) (by decide)) (freshVar_injective
        (((Class.cv r)).fv) (by decide)) (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq
                                        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb093_alpha_dummy_059 A))).fv ∪ ((Class.cv (nb093_alpha_dummy_058 A))).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb093_alpha_dummy_061 r))).fv ∪
        ((Class.cv (nb093_alpha_dummy_060 r))).fv) (by decide)) (TAlphaVar.here _ _ _)))
                                        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb093_split_alpha_0005 A r d))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb093_alpha_dummy_132 A), (nb093_alpha_dummy_133 r)), ((nb093_alpha_dummy_101 A),
        (nb093_alpha_dummy_103 r)), ((nb093_alpha_dummy_100 A), (nb093_alpha_dummy_102 r)),
        ((nb093_alpha_dummy_130 A), (nb093_alpha_dummy_131 r)), ((nb093_alpha_dummy_104 A),
        (nb093_alpha_dummy_105 r)), ((nb093_alpha_dummy_059 A), (nb093_alpha_dummy_061 r)),
        ((nb093_alpha_dummy_058 A), (nb093_alpha_dummy_060 r)), ((nb093_alpha_dummy_062 A),
        (nb093_alpha_dummy_063 r)), ((nb093_alpha_dummy_056 A), (nb093_alpha_dummy_057 r)),
        ((nb093_alpha_dummy_054 A), (nb093_alpha_dummy_055 r)), ((nb093_alpha_dummy_052 A),
        (nb093_alpha_dummy_053 r)), ((nb093_alpha_dummy_045 A), (nb093_alpha_dummy_047 r d)),
        ((nb093_alpha_dummy_044 A), (nb093_alpha_dummy_046 r d)), ((nb093_alpha_dummy_050 A),
        (nb093_alpha_dummy_051 r d)), ((nb093_alpha_dummy_048 A), (nb093_alpha_dummy_049 r d)),
        ((nb093_alpha_dummy_000 A), d), ((nb093_alpha_dummy_001 A), r),
        ((nb093_alpha_dummy_006 A), (nb093_alpha_dummy_007 r d)), ((nb093_alpha_dummy_004 A),
        (nb093_alpha_dummy_005 A r d)), ((nb093_alpha_dummy_002 A),
        (nb093_alpha_dummy_003 A r d))] (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl, fv_syn_csn,
            fv_syn_c0c])))))))))))))))))) (TAlphaClass.cv (TAlphaVar.there
                    (show (nb093_alpha_dummy_001 A) ≠ (nb093_alpha_dummy_059 A) from (by
                        unfold nb093_alpha_dummy_059;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb093_support_mem_0136 A) 1))))
                    (show r ≠ (nb093_alpha_dummy_061 r) from (by
                        unfold nb093_alpha_dummy_061;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb093_support_mem_0137 r) 1)))) (TAlphaVar.there
                      (show (nb093_alpha_dummy_001 A) ≠ (nb093_alpha_dummy_058 A) from (by
                          unfold nb093_alpha_dummy_058;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb093_support_mem_0136 A) 0))))
                      (show r ≠ (nb093_alpha_dummy_060 r) from (by
                          unfold nb093_alpha_dummy_060;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb093_support_mem_0137 r) 0))))
                      (TAlphaVar.there
                        (show (nb093_alpha_dummy_001 A) ≠ (nb093_alpha_dummy_062 A) from (by
                            unfold nb093_alpha_dummy_062;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb093_support_mem_0134 A) 0))))
                        (show r ≠ (nb093_alpha_dummy_063 r) from (by
                            unfold nb093_alpha_dummy_063;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb093_support_mem_0135 r) 0))))
                        (TAlphaVar.there
                          (show (nb093_alpha_dummy_001 A) ≠ (nb093_alpha_dummy_056 A) from (by
                              unfold nb093_alpha_dummy_056;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb093_support_mem_0132 A) 0))))
                          (show r ≠ (nb093_alpha_dummy_057 r) from (by
                              unfold nb093_alpha_dummy_057;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb093_support_mem_0133 r) 0))))
                          (TAlphaVar.there
                            (show (nb093_alpha_dummy_001 A) ≠ (nb093_alpha_dummy_054 A) from (by
                                unfold nb093_alpha_dummy_054;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb093_support_mem_0050 A) 0))))
                            (show r ≠ (nb093_alpha_dummy_055 r) from (by
                                unfold nb093_alpha_dummy_055;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb093_support_mem_0051 r) 0))))
                            (TAlphaVar.there
                              (show (nb093_alpha_dummy_001 A) ≠ (nb093_alpha_dummy_052 A) from
                                (by
                                  unfold nb093_alpha_dummy_052;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb093_support_mem_0048 A) 0))))
                              (show r ≠ (nb093_alpha_dummy_053 r) from (by
                                  unfold nb093_alpha_dummy_053;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb093_support_mem_0049 r) 0))))
                              (TAlphaVar.there (show
                                  (nb093_alpha_dummy_001 A) ≠ (nb093_alpha_dummy_045 A) from (by
                                    unfold nb093_alpha_dummy_045;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb093_support_mem_0042 A)
                                            1)))) (show r ≠ (nb093_alpha_dummy_047 r d) from (by
                                    unfold nb093_alpha_dummy_047;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb093_support_mem_0044 r d)
                                            1)))) (TAlphaVar.there (show
                                    (nb093_alpha_dummy_001 A) ≠ (nb093_alpha_dummy_044 A) from
                                    (by
                                      unfold nb093_alpha_dummy_044;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb093_support_mem_0042 A)
                                              0)))) (show r ≠ (nb093_alpha_dummy_046 r d) from
                                    (by
                                      unfold nb093_alpha_dummy_046;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb093_support_mem_0044 r d)
                                              0)))) (TAlphaVar.there (show
                                      (nb093_alpha_dummy_001 A) ≠ (nb093_alpha_dummy_050 A) from
                                      (by
                                        unfold nb093_alpha_dummy_050;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb093_support_mem_0046 A)
                                                0)))) (show r ≠ (nb093_alpha_dummy_051 r d) from
                                      (by
                                        unfold nb093_alpha_dummy_051;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb093_support_mem_0047 r d) 0))))
                                    (TAlphaVar.there (show (nb093_alpha_dummy_001 A) ≠
        (nb093_alpha_dummy_048 A) from (by
                                          unfold nb093_alpha_dummy_048;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb093_support_mem_0043 A) 0))))
                                      (show r ≠ (nb093_alpha_dummy_049 r d) from (by
                                          unfold nb093_alpha_dummy_049;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb093_support_mem_0045 r d) 0))))
                                      (TAlphaVar.there (freshVar_injective ((A).fv) (by decide))
                                        (Ne.symm dv_d_r)
                                        (TAlphaVar.here _ _ _))))))))))))))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex
            (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                      (Ne.symm (show (nb093_alpha_dummy_059 A) ≠ (nb093_alpha_dummy_062 A) from
                          (by
                            unfold nb093_alpha_dummy_062;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb093_support_mem_0054 A) 0))))) (Ne.symm
                        (show (nb093_alpha_dummy_061 r) ≠ (nb093_alpha_dummy_063 r) from (by
                            unfold nb093_alpha_dummy_063;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb093_support_mem_0055 r) 0)))))
                      (TAlphaVar.there (Ne.symm
                          (show (nb093_alpha_dummy_058 A) ≠ (nb093_alpha_dummy_062 A) from (by
                              unfold nb093_alpha_dummy_062;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb093_support_mem_0052 A) 0))))) (Ne.symm
                          (show (nb093_alpha_dummy_060 r) ≠ (nb093_alpha_dummy_063 r) from (by
                              unfold nb093_alpha_dummy_063;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb093_support_mem_0053 r) 0)))))
                        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
                      (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.neg
                              (TAlphaWff.neg (nb093_split_alpha_0002 A r d)))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb093_alpha_dummy_059 A) ≠ (nb093_alpha_dummy_065 A) from (by
          unfold nb093_alpha_dummy_065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0084 A) 1)))) (show (nb093_alpha_dummy_061 r) ≠
        (nb093_alpha_dummy_067 r) from (by
          unfold nb093_alpha_dummy_067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0086 r) 1)))) (TAlphaVar.there (show
        (nb093_alpha_dummy_059 A) ≠ (nb093_alpha_dummy_064 A) from (by
          unfold nb093_alpha_dummy_064;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0084 A)
                  0)))) (show (nb093_alpha_dummy_061 r) ≠ (nb093_alpha_dummy_066 r) from (by
          unfold nb093_alpha_dummy_066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0086 r)
                  0)))) (TAlphaVar.there (show (nb093_alpha_dummy_059 A) ≠
        (nb093_alpha_dummy_094 A) from (by
          unfold nb093_alpha_dummy_094;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0088 A)
                  0)))) (show (nb093_alpha_dummy_061 r) ≠ (nb093_alpha_dummy_095 r) from (by
          unfold nb093_alpha_dummy_095;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0089 r)
                  0)))) (TAlphaVar.there (show (nb093_alpha_dummy_059 A) ≠
        (nb093_alpha_dummy_068 A) from (by
          unfold nb093_alpha_dummy_068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0085 A)
                  0)))) (show (nb093_alpha_dummy_061 r) ≠ (nb093_alpha_dummy_069 r) from (by
          unfold nb093_alpha_dummy_069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0087 r)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb093_alpha_dummy_058 A))).fv ∪
        ((Class.cv (nb093_alpha_dummy_059 A))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb093_alpha_dummy_060 r))).fv ∪ ((Class.cv (nb093_alpha_dummy_061 r))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb093_split_alpha_0003 A r d))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb093_alpha_dummy_096 A), (nb093_alpha_dummy_097 r)), ((nb093_alpha_dummy_065 A),
        (nb093_alpha_dummy_067 r)), ((nb093_alpha_dummy_064 A), (nb093_alpha_dummy_066 r)),
        ((nb093_alpha_dummy_094 A), (nb093_alpha_dummy_095 r)), ((nb093_alpha_dummy_068 A),
        (nb093_alpha_dummy_069 r)), ((nb093_alpha_dummy_059 A), (nb093_alpha_dummy_061 r)),
        ((nb093_alpha_dummy_058 A), (nb093_alpha_dummy_060 r)), ((nb093_alpha_dummy_062 A),
        (nb093_alpha_dummy_063 r)), ((nb093_alpha_dummy_056 A), (nb093_alpha_dummy_057 r)),
        ((nb093_alpha_dummy_054 A), (nb093_alpha_dummy_055 r)), ((nb093_alpha_dummy_052 A),
        (nb093_alpha_dummy_053 r)), ((nb093_alpha_dummy_045 A), (nb093_alpha_dummy_047 r d)),
        ((nb093_alpha_dummy_044 A), (nb093_alpha_dummy_046 r d)), ((nb093_alpha_dummy_050 A),
        (nb093_alpha_dummy_051 r d)), ((nb093_alpha_dummy_048 A), (nb093_alpha_dummy_049 r d)),
        ((nb093_alpha_dummy_000 A), d), ((nb093_alpha_dummy_001 A), r),
        ((nb093_alpha_dummy_006 A), (nb093_alpha_dummy_007 r d)), ((nb093_alpha_dummy_004 A),
        (nb093_alpha_dummy_005 A r d)), ((nb093_alpha_dummy_002 A),
        (nb093_alpha_dummy_003 A r d))] (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn, fv_syn_c0c]))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb093_alpha_dummy_059 A) ≠ (nb093_alpha_dummy_065 A) from (by
          unfold nb093_alpha_dummy_065;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0084 A) 1)))) (show (nb093_alpha_dummy_061 r) ≠
        (nb093_alpha_dummy_067 r) from (by
          unfold nb093_alpha_dummy_067;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0086 r) 1)))) (TAlphaVar.there (show
        (nb093_alpha_dummy_059 A) ≠ (nb093_alpha_dummy_064 A) from (by
          unfold nb093_alpha_dummy_064;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0084 A)
                  0)))) (show (nb093_alpha_dummy_061 r) ≠ (nb093_alpha_dummy_066 r) from (by
          unfold nb093_alpha_dummy_066;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0086 r)
                  0)))) (TAlphaVar.there (show (nb093_alpha_dummy_059 A) ≠
        (nb093_alpha_dummy_094 A) from (by
          unfold nb093_alpha_dummy_094;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0088 A)
                  0)))) (show (nb093_alpha_dummy_061 r) ≠ (nb093_alpha_dummy_095 r) from (by
          unfold nb093_alpha_dummy_095;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0089 r)
                  0)))) (TAlphaVar.there (show (nb093_alpha_dummy_059 A) ≠
        (nb093_alpha_dummy_068 A) from (by
          unfold nb093_alpha_dummy_068;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0085 A)
                  0)))) (show (nb093_alpha_dummy_061 r) ≠ (nb093_alpha_dummy_069 r) from (by
          unfold nb093_alpha_dummy_069;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0087 r)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb093_alpha_dummy_058 A))).fv ∪
        ((Class.cv (nb093_alpha_dummy_059 A))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb093_alpha_dummy_060 r))).fv ∪ ((Class.cv (nb093_alpha_dummy_061 r))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb093_split_alpha_0003 A r d))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb093_alpha_dummy_096 A), (nb093_alpha_dummy_097 r)), ((nb093_alpha_dummy_065 A),
        (nb093_alpha_dummy_067 r)), ((nb093_alpha_dummy_064 A), (nb093_alpha_dummy_066 r)),
        ((nb093_alpha_dummy_094 A), (nb093_alpha_dummy_095 r)), ((nb093_alpha_dummy_068 A),
        (nb093_alpha_dummy_069 r)), ((nb093_alpha_dummy_059 A), (nb093_alpha_dummy_061 r)),
        ((nb093_alpha_dummy_058 A), (nb093_alpha_dummy_060 r)), ((nb093_alpha_dummy_062 A),
        (nb093_alpha_dummy_063 r)), ((nb093_alpha_dummy_056 A), (nb093_alpha_dummy_057 r)),
        ((nb093_alpha_dummy_054 A), (nb093_alpha_dummy_055 r)), ((nb093_alpha_dummy_052 A),
        (nb093_alpha_dummy_053 r)), ((nb093_alpha_dummy_045 A), (nb093_alpha_dummy_047 r d)),
        ((nb093_alpha_dummy_044 A), (nb093_alpha_dummy_046 r d)), ((nb093_alpha_dummy_050 A),
        (nb093_alpha_dummy_051 r d)), ((nb093_alpha_dummy_048 A), (nb093_alpha_dummy_049 r d)),
        ((nb093_alpha_dummy_000 A), d), ((nb093_alpha_dummy_001 A), r),
        ((nb093_alpha_dummy_006 A), (nb093_alpha_dummy_007 r d)), ((nb093_alpha_dummy_004 A),
        (nb093_alpha_dummy_005 A r d)), ((nb093_alpha_dummy_002 A),
        (nb093_alpha_dummy_003 A r d))] (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))))))))))) (TAlphaWff.classMem (TAlphaClass.cab (TAlphaWff.neg
                      (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.neg
                              (TAlphaWff.neg (nb093_split_alpha_0004 A r d)))))
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb093_alpha_dummy_058 A) ≠ (nb093_alpha_dummy_101 A) from (by
          unfold nb093_alpha_dummy_101;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0122 A) 1)))) (show (nb093_alpha_dummy_060 r) ≠
        (nb093_alpha_dummy_103 r) from (by
          unfold nb093_alpha_dummy_103;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0124 r) 1)))) (TAlphaVar.there (show
        (nb093_alpha_dummy_058 A) ≠ (nb093_alpha_dummy_100 A) from (by
          unfold nb093_alpha_dummy_100;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0122 A)
                  0)))) (show (nb093_alpha_dummy_060 r) ≠ (nb093_alpha_dummy_102 r) from (by
          unfold nb093_alpha_dummy_102;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0124 r)
                  0)))) (TAlphaVar.there (show (nb093_alpha_dummy_058 A) ≠
        (nb093_alpha_dummy_130 A) from (by
          unfold nb093_alpha_dummy_130;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0126 A)
                  0)))) (show (nb093_alpha_dummy_060 r) ≠ (nb093_alpha_dummy_131 r) from (by
          unfold nb093_alpha_dummy_131;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0127 r)
                  0)))) (TAlphaVar.there (show (nb093_alpha_dummy_058 A) ≠
        (nb093_alpha_dummy_104 A) from (by
          unfold nb093_alpha_dummy_104;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0123 A)
                  0)))) (show (nb093_alpha_dummy_060 r) ≠ (nb093_alpha_dummy_105 r) from (by
          unfold nb093_alpha_dummy_105;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0125 r)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093_alpha_dummy_001
        A))).fv) (by decide)) (freshVar_injective (((Class.cv r)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb093_alpha_dummy_059 A))).fv ∪ ((Class.cv
        (nb093_alpha_dummy_058 A))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb093_alpha_dummy_061 r))).fv ∪ ((Class.cv (nb093_alpha_dummy_060 r))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb093_split_alpha_0005 A r d))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb093_alpha_dummy_132 A), (nb093_alpha_dummy_133 r)), ((nb093_alpha_dummy_101 A),
        (nb093_alpha_dummy_103 r)), ((nb093_alpha_dummy_100 A), (nb093_alpha_dummy_102 r)),
        ((nb093_alpha_dummy_130 A), (nb093_alpha_dummy_131 r)), ((nb093_alpha_dummy_104 A),
        (nb093_alpha_dummy_105 r)), ((nb093_alpha_dummy_059 A), (nb093_alpha_dummy_061 r)),
        ((nb093_alpha_dummy_058 A), (nb093_alpha_dummy_060 r)), ((nb093_alpha_dummy_062 A),
        (nb093_alpha_dummy_063 r)), ((nb093_alpha_dummy_056 A), (nb093_alpha_dummy_057 r)),
        ((nb093_alpha_dummy_054 A), (nb093_alpha_dummy_055 r)), ((nb093_alpha_dummy_052 A),
        (nb093_alpha_dummy_053 r)), ((nb093_alpha_dummy_045 A), (nb093_alpha_dummy_047 r d)),
        ((nb093_alpha_dummy_044 A), (nb093_alpha_dummy_046 r d)), ((nb093_alpha_dummy_050 A),
        (nb093_alpha_dummy_051 r d)), ((nb093_alpha_dummy_048 A), (nb093_alpha_dummy_049 r d)),
        ((nb093_alpha_dummy_000 A), d), ((nb093_alpha_dummy_001 A), r),
        ((nb093_alpha_dummy_006 A), (nb093_alpha_dummy_007 r d)), ((nb093_alpha_dummy_004 A),
        (nb093_alpha_dummy_005 A r d)), ((nb093_alpha_dummy_002 A),
        (nb093_alpha_dummy_003 A r d))] (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn, fv_syn_c0c]))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb093_alpha_dummy_058 A) ≠ (nb093_alpha_dummy_101 A) from (by
          unfold nb093_alpha_dummy_101;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0122 A) 1)))) (show (nb093_alpha_dummy_060 r) ≠
        (nb093_alpha_dummy_103 r) from (by
          unfold nb093_alpha_dummy_103;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0124 r) 1)))) (TAlphaVar.there (show
        (nb093_alpha_dummy_058 A) ≠ (nb093_alpha_dummy_100 A) from (by
          unfold nb093_alpha_dummy_100;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0122 A)
                  0)))) (show (nb093_alpha_dummy_060 r) ≠ (nb093_alpha_dummy_102 r) from (by
          unfold nb093_alpha_dummy_102;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0124 r)
                  0)))) (TAlphaVar.there (show (nb093_alpha_dummy_058 A) ≠
        (nb093_alpha_dummy_130 A) from (by
          unfold nb093_alpha_dummy_130;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0126 A)
                  0)))) (show (nb093_alpha_dummy_060 r) ≠ (nb093_alpha_dummy_131 r) from (by
          unfold nb093_alpha_dummy_131;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0127 r)
                  0)))) (TAlphaVar.there (show (nb093_alpha_dummy_058 A) ≠
        (nb093_alpha_dummy_104 A) from (by
          unfold nb093_alpha_dummy_104;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0123 A)
                  0)))) (show (nb093_alpha_dummy_060 r) ≠ (nb093_alpha_dummy_105 r) from (by
          unfold nb093_alpha_dummy_105;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0125 r)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb093_alpha_dummy_001
        A))).fv) (by decide)) (freshVar_injective (((Class.cv r)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))) (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb093_alpha_dummy_059 A))).fv ∪ ((Class.cv
        (nb093_alpha_dummy_058 A))).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb093_alpha_dummy_061 r))).fv ∪ ((Class.cv (nb093_alpha_dummy_060 r))).fv) (by decide))
        (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb093_split_alpha_0005 A r d))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb093_alpha_dummy_132 A), (nb093_alpha_dummy_133 r)), ((nb093_alpha_dummy_101 A),
        (nb093_alpha_dummy_103 r)), ((nb093_alpha_dummy_100 A), (nb093_alpha_dummy_102 r)),
        ((nb093_alpha_dummy_130 A), (nb093_alpha_dummy_131 r)), ((nb093_alpha_dummy_104 A),
        (nb093_alpha_dummy_105 r)), ((nb093_alpha_dummy_059 A), (nb093_alpha_dummy_061 r)),
        ((nb093_alpha_dummy_058 A), (nb093_alpha_dummy_060 r)), ((nb093_alpha_dummy_062 A),
        (nb093_alpha_dummy_063 r)), ((nb093_alpha_dummy_056 A), (nb093_alpha_dummy_057 r)),
        ((nb093_alpha_dummy_054 A), (nb093_alpha_dummy_055 r)), ((nb093_alpha_dummy_052 A),
        (nb093_alpha_dummy_053 r)), ((nb093_alpha_dummy_045 A), (nb093_alpha_dummy_047 r d)),
        ((nb093_alpha_dummy_044 A), (nb093_alpha_dummy_046 r d)), ((nb093_alpha_dummy_050 A),
        (nb093_alpha_dummy_051 r d)), ((nb093_alpha_dummy_048 A), (nb093_alpha_dummy_049 r d)),
        ((nb093_alpha_dummy_000 A), d), ((nb093_alpha_dummy_001 A), r),
        ((nb093_alpha_dummy_006 A), (nb093_alpha_dummy_007 r d)), ((nb093_alpha_dummy_004 A),
        (nb093_alpha_dummy_005 A r d)), ((nb093_alpha_dummy_002 A),
        (nb093_alpha_dummy_003 A r d))] (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c])))))))))))))))))) (TAlphaClass.cv (TAlphaVar.there
                      (show (nb093_alpha_dummy_001 A) ≠ (nb093_alpha_dummy_059 A) from (by
                          unfold nb093_alpha_dummy_059;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb093_support_mem_0136 A) 1))))
                      (show r ≠ (nb093_alpha_dummy_061 r) from (by
                          unfold nb093_alpha_dummy_061;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb093_support_mem_0137 r) 1))))
                      (TAlphaVar.there
                        (show (nb093_alpha_dummy_001 A) ≠ (nb093_alpha_dummy_058 A) from (by
                            unfold nb093_alpha_dummy_058;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb093_support_mem_0136 A) 0))))
                        (show r ≠ (nb093_alpha_dummy_060 r) from (by
                            unfold nb093_alpha_dummy_060;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb093_support_mem_0137 r) 0))))
                        (TAlphaVar.there
                          (show (nb093_alpha_dummy_001 A) ≠ (nb093_alpha_dummy_062 A) from (by
                              unfold nb093_alpha_dummy_062;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb093_support_mem_0134 A) 0))))
                          (show r ≠ (nb093_alpha_dummy_063 r) from (by
                              unfold nb093_alpha_dummy_063;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb093_support_mem_0135 r) 0))))
                          (TAlphaVar.there
                            (show (nb093_alpha_dummy_001 A) ≠ (nb093_alpha_dummy_056 A) from (by
                                unfold nb093_alpha_dummy_056;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb093_support_mem_0132 A) 0))))
                            (show r ≠ (nb093_alpha_dummy_057 r) from (by
                                unfold nb093_alpha_dummy_057;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb093_support_mem_0133 r) 0))))
                            (TAlphaVar.there
                              (show (nb093_alpha_dummy_001 A) ≠ (nb093_alpha_dummy_054 A) from
                                (by
                                  unfold nb093_alpha_dummy_054;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb093_support_mem_0050 A) 0))))
                              (show r ≠ (nb093_alpha_dummy_055 r) from (by
                                  unfold nb093_alpha_dummy_055;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb093_support_mem_0051 r) 0))))
                              (TAlphaVar.there (show
                                  (nb093_alpha_dummy_001 A) ≠ (nb093_alpha_dummy_052 A) from (by
                                    unfold nb093_alpha_dummy_052;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb093_support_mem_0048 A)
                                            0)))) (show r ≠ (nb093_alpha_dummy_053 r) from (by
                                    unfold nb093_alpha_dummy_053;
                                    with_reducible
                                      exact
                                        (Nat.ne_of_lt
                                          (mem_lt_freshVar (nb093_support_mem_0049 r)
                                            0)))) (TAlphaVar.there (show
                                    (nb093_alpha_dummy_001 A) ≠ (nb093_alpha_dummy_045 A) from
                                    (by
                                      unfold nb093_alpha_dummy_045;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb093_support_mem_0042 A)
                                              1)))) (show r ≠ (nb093_alpha_dummy_047 r d) from
                                    (by
                                      unfold nb093_alpha_dummy_047;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb093_support_mem_0044 r d)
                                              1)))) (TAlphaVar.there (show
                                      (nb093_alpha_dummy_001 A) ≠ (nb093_alpha_dummy_044 A) from
                                      (by
                                        unfold nb093_alpha_dummy_044;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb093_support_mem_0042 A)
                                                0)))) (show r ≠ (nb093_alpha_dummy_046 r d) from
                                      (by
                                        unfold nb093_alpha_dummy_046;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb093_support_mem_0044 r d) 0))))
                                    (TAlphaVar.there (show (nb093_alpha_dummy_001 A) ≠
        (nb093_alpha_dummy_050 A) from (by
                                          unfold nb093_alpha_dummy_050;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb093_support_mem_0046 A) 0))))
                                      (show r ≠ (nb093_alpha_dummy_051 r d) from (by
                                          unfold nb093_alpha_dummy_051;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb093_support_mem_0047 r d) 0))))
                                      (TAlphaVar.there (show (nb093_alpha_dummy_001 A) ≠
        (nb093_alpha_dummy_048 A) from (by
          unfold nb093_alpha_dummy_048;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0043 A) 0)))) (show r ≠ (nb093_alpha_dummy_049 r d) from
        (by
          unfold nb093_alpha_dummy_049;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb093_support_mem_0045 r d) 0)))) (TAlphaVar.there
        (freshVar_injective ((A).fv) (by decide)) (Ne.symm dv_d_r)
        (TAlphaVar.here _ _ _)))))))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
