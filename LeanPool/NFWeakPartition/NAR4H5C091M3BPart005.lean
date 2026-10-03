/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NAR4H5C091M3BPart004

/-! NF weak partition development: NAR4H5C091M3BPart005. -/


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
noncomputable def nb091_split_alpha_0005 (D : Class) (R : Class) (p : Var) :
    TAlphaWff
      [((nb091_alpha_dummy_125 D R), (nb091_alpha_dummy_126 R p)),
        ((nb091_alpha_dummy_123 D R), (nb091_alpha_dummy_124 R p)),
        ((nb091_alpha_dummy_106 D R), (nb091_alpha_dummy_108 R p)),
        ((nb091_alpha_dummy_105 D R), (nb091_alpha_dummy_107 R p)),
        ((nb091_alpha_dummy_103 D R), (nb091_alpha_dummy_104 D R p)),
        ((nb091_alpha_dummy_101 D R), (nb091_alpha_dummy_102 D R p)),
        ((nb091_alpha_dummy_060 D R), (nb091_alpha_dummy_062 D R p)),
        ((nb091_alpha_dummy_059 D R), (nb091_alpha_dummy_061 D R p)),
        ((nb091_alpha_dummy_063 D R), (nb091_alpha_dummy_064 D R p)),
        ((nb091_alpha_dummy_057 D R), (nb091_alpha_dummy_058 D R p)),
        ((nb091_alpha_dummy_055 D R), (nb091_alpha_dummy_056 D R p)),
        ((nb091_alpha_dummy_048 D R), (nb091_alpha_dummy_050 D R p)),
        ((nb091_alpha_dummy_047 D R), (nb091_alpha_dummy_049 D R p)),
        ((nb091_alpha_dummy_053 D R), (nb091_alpha_dummy_054 D R p)),
        ((nb091_alpha_dummy_051 D R), (nb091_alpha_dummy_052 D R p)),
        ((nb091_alpha_dummy_045 D R), (nb091_alpha_dummy_046 D R p)),
        ((nb091_alpha_dummy_042 D R), (nb091_alpha_dummy_044 D R p)),
        ((nb091_alpha_dummy_041 D R), (nb091_alpha_dummy_043 D R p)),
        ((nb091_alpha_dummy_001 D R), (nb091_alpha_dummy_002 D R p)),
        ((nb091_alpha_dummy_000 D R), p),
        ((nb091_alpha_dummy_003 D R), (nb091_alpha_dummy_004 D R p))]
      (Wff.imp (Wff.classMem (Class.cv (nb091_alpha_dummy_125 D R))
          (Class.cab (nb091_alpha_dummy_119 D R)
            (syn_wrex (nb091_alpha_dummy_120 D R) (Class.cv (nb091_alpha_dummy_106 D R))
              (Wff.classEq (Class.cv (nb091_alpha_dummy_119 D R))
                (syn_cphi (Class.cv (nb091_alpha_dummy_120 D R))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb091_alpha_dummy_125 D R))
            (Class.cab (nb091_alpha_dummy_119 D R)
              (syn_wrex (nb091_alpha_dummy_120 D R) (Class.cv (nb091_alpha_dummy_106 D R))
                (Wff.classEq (Class.cv (nb091_alpha_dummy_119 D R))
                  (syn_cphi (Class.cv (nb091_alpha_dummy_120 D R)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb091_alpha_dummy_126 R p))
          (Class.cab (nb091_alpha_dummy_121 R p)
            (syn_wrex (nb091_alpha_dummy_122 R p) (Class.cv (nb091_alpha_dummy_108 R p))
              (Wff.classEq (Class.cv (nb091_alpha_dummy_121 R p))
                (syn_cphi (Class.cv (nb091_alpha_dummy_122 R p))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb091_alpha_dummy_126 R p))
            (Class.cab (nb091_alpha_dummy_121 R p)
              (syn_wrex (nb091_alpha_dummy_122 R p) (Class.cv (nb091_alpha_dummy_108 R p))
                (Wff.classEq (Class.cv (nb091_alpha_dummy_121 R p))
                  (syn_cphi (Class.cv (nb091_alpha_dummy_122 R p))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there
                  (show (nb091_alpha_dummy_106 D R) ≠ (nb091_alpha_dummy_120 D R) from (by
                      unfold nb091_alpha_dummy_120;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb091_support_mem_0116 D R) 1))))
                  (show (nb091_alpha_dummy_108 R p) ≠ (nb091_alpha_dummy_122 R p) from (by
                      unfold nb091_alpha_dummy_122;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb091_support_mem_0118 R p) 1)))) (TAlphaVar.there
                    (show (nb091_alpha_dummy_106 D R) ≠ (nb091_alpha_dummy_119 D R) from (by
                        unfold nb091_alpha_dummy_119;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb091_support_mem_0116 D R) 0))))
                    (show (nb091_alpha_dummy_108 R p) ≠ (nb091_alpha_dummy_121 R p) from (by
                        unfold nb091_alpha_dummy_121;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb091_support_mem_0118 R p) 0))))
                    (TAlphaVar.there
                      (show (nb091_alpha_dummy_106 D R) ≠ (nb091_alpha_dummy_125 D R) from (by
                          unfold nb091_alpha_dummy_125;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb091_support_mem_0120 D R) 0))))
                      (show (nb091_alpha_dummy_108 R p) ≠ (nb091_alpha_dummy_126 R p) from (by
                          unfold nb091_alpha_dummy_126;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb091_support_mem_0121 R p) 0))))
                      (TAlphaVar.there
                        (show (nb091_alpha_dummy_106 D R) ≠ (nb091_alpha_dummy_123 D R) from (by
                            unfold nb091_alpha_dummy_123;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb091_support_mem_0117 D R) 0))))
                        (show (nb091_alpha_dummy_108 R p) ≠ (nb091_alpha_dummy_124 R p) from (by
                            unfold nb091_alpha_dummy_124;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb091_support_mem_0119 R p) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective
                    (((Class.cv (nb091_alpha_dummy_106 D R))).fv ∪
                      ((Class.cv (nb091_alpha_dummy_105 D R))).fv) (by decide))
                  (freshVar_injective (((Class.cv (nb091_alpha_dummy_108 R p))).fv ∪
                      ((Class.cv (nb091_alpha_dummy_107 R p))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb091_alpha_dummy_120 D R) ≠ (nb091_alpha_dummy_127 D R) from
                            (by
                              unfold nb091_alpha_dummy_127;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb091_support_mem_0122 D R) 0))))
                          (show (nb091_alpha_dummy_122 R p) ≠ (nb091_alpha_dummy_129 R p) from
                            (by
                              unfold nb091_alpha_dummy_129;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb091_support_mem_0123 R p) 0))))
                          (TAlphaVar.there (show
                              (nb091_alpha_dummy_120 D R) ≠ (nb091_alpha_dummy_128 D R) from (by
                                unfold nb091_alpha_dummy_128;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb091_support_mem_0122 D R) 1)))) (show
                              (nb091_alpha_dummy_122 R p) ≠ (nb091_alpha_dummy_130 R p) from (by
                                unfold nb091_alpha_dummy_130;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb091_support_mem_0123 R p) 1))))
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there (freshVar_injective
                            (((Class.cv (nb091_alpha_dummy_120 D R))).fv) (by decide))
                          (freshVar_injective
                            (((Class.cv (nb091_alpha_dummy_122 R p))).fv) (by decide))
                          (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                          (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb091_alpha_dummy_127 D R) ≠ (nb091_alpha_dummy_134 D R) from
        (by
          unfold nb091_alpha_dummy_134;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0126 D R) 1)))) (show (nb091_alpha_dummy_129 R p) ≠
        (nb091_alpha_dummy_137 R p) from (by
          unfold nb091_alpha_dummy_137;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0127 R p) 1)))) (TAlphaVar.there (show
        (nb091_alpha_dummy_127 D R) ≠ (nb091_alpha_dummy_133 D R) from (by
          unfold nb091_alpha_dummy_133;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0126 D R)
                  0)))) (show (nb091_alpha_dummy_129 R p) ≠ (nb091_alpha_dummy_136 R p) from (by
          unfold nb091_alpha_dummy_136;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0127 R p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_127 D R) ≠
        (nb091_alpha_dummy_131 D R) from (by
          unfold nb091_alpha_dummy_131;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0124 D R)
                  0)))) (show (nb091_alpha_dummy_129 R p) ≠ (nb091_alpha_dummy_132 R p) from (by
          unfold nb091_alpha_dummy_132;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0125 R p)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb091_alpha_dummy_135 D R), (nb091_alpha_dummy_138 R p)),
        ((nb091_alpha_dummy_134 D R), (nb091_alpha_dummy_137 R p)),
        ((nb091_alpha_dummy_133 D R), (nb091_alpha_dummy_136 R p)),
        ((nb091_alpha_dummy_131 D R), (nb091_alpha_dummy_132 R p)),
        ((nb091_alpha_dummy_127 D R), (nb091_alpha_dummy_129 R p)),
        ((nb091_alpha_dummy_128 D R), (nb091_alpha_dummy_130 R p)),
        ((nb091_alpha_dummy_120 D R), (nb091_alpha_dummy_122 R p)),
        ((nb091_alpha_dummy_119 D R), (nb091_alpha_dummy_121 R p)),
        ((nb091_alpha_dummy_125 D R), (nb091_alpha_dummy_126 R p)),
        ((nb091_alpha_dummy_123 D R), (nb091_alpha_dummy_124 R p)),
        ((nb091_alpha_dummy_106 D R), (nb091_alpha_dummy_108 R p)),
        ((nb091_alpha_dummy_105 D R), (nb091_alpha_dummy_107 R p)),
        ((nb091_alpha_dummy_103 D R), (nb091_alpha_dummy_104 D R p)),
        ((nb091_alpha_dummy_101 D R), (nb091_alpha_dummy_102 D R p)),
        ((nb091_alpha_dummy_060 D R), (nb091_alpha_dummy_062 D R p)),
        ((nb091_alpha_dummy_059 D R), (nb091_alpha_dummy_061 D R p)),
        ((nb091_alpha_dummy_063 D R), (nb091_alpha_dummy_064 D R p)),
        ((nb091_alpha_dummy_057 D R), (nb091_alpha_dummy_058 D R p)),
        ((nb091_alpha_dummy_055 D R), (nb091_alpha_dummy_056 D R p)),
        ((nb091_alpha_dummy_048 D R), (nb091_alpha_dummy_050 D R p)),
        ((nb091_alpha_dummy_047 D R), (nb091_alpha_dummy_049 D R p)),
        ((nb091_alpha_dummy_053 D R), (nb091_alpha_dummy_054 D R p)),
        ((nb091_alpha_dummy_051 D R), (nb091_alpha_dummy_052 D R p)),
        ((nb091_alpha_dummy_045 D R), (nb091_alpha_dummy_046 D R p)),
        ((nb091_alpha_dummy_042 D R), (nb091_alpha_dummy_044 D R p)),
        ((nb091_alpha_dummy_041 D R), (nb091_alpha_dummy_043 D R p)),
        ((nb091_alpha_dummy_001 D R), (nb091_alpha_dummy_002 D R p)),
        ((nb091_alpha_dummy_000 D R), p), ((nb091_alpha_dummy_003 D R),
        (nb091_alpha_dummy_004 D R p))] (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb091_alpha_dummy_134 D R) ≠ (nb091_alpha_dummy_141 D R) from
        (by
          unfold
            nb091_alpha_dummy_141;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0130
                    D R)
                  0)))) (show (nb091_alpha_dummy_137 R p) ≠ (nb091_alpha_dummy_142 R p) from (by
          unfold
            nb091_alpha_dummy_142;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0131
                    R p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_134 D R) ≠
        (nb091_alpha_dummy_139 D R) from (by
          unfold
            nb091_alpha_dummy_139;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0128
                    D R)
                  0)))) (show (nb091_alpha_dummy_137 R p) ≠ (nb091_alpha_dummy_140 R p) from (by
          unfold
            nb091_alpha_dummy_140;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0129
                    R p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb091_alpha_dummy_127
        D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb091_alpha_dummy_129 R p))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb091_alpha_dummy_135 D R) ≠ (nb091_alpha_dummy_141 D R) from
        (by
          unfold
            nb091_alpha_dummy_141;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0134
                    D R)
                  0)))) (show (nb091_alpha_dummy_138 R p) ≠ (nb091_alpha_dummy_142 R p) from (by
          unfold
            nb091_alpha_dummy_142;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0135
                    R p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_135 D R) ≠
        (nb091_alpha_dummy_139 D R) from (by
          unfold
            nb091_alpha_dummy_139;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0132
                    D R)
                  0)))) (show (nb091_alpha_dummy_138 R p) ≠ (nb091_alpha_dummy_140 R p) from (by
          unfold
            nb091_alpha_dummy_140;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0133
                    R p)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb091_alpha_dummy_134 D R) ≠ (nb091_alpha_dummy_141 D R) from
        (by
          unfold
            nb091_alpha_dummy_141;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0130
                    D R)
                  0)))) (show (nb091_alpha_dummy_137 R p) ≠ (nb091_alpha_dummy_142 R p) from (by
          unfold
            nb091_alpha_dummy_142;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0131
                    R p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_134 D R) ≠
        (nb091_alpha_dummy_139 D R) from (by
          unfold
            nb091_alpha_dummy_139;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0128
                    D R)
                  0)))) (show (nb091_alpha_dummy_137 R p) ≠ (nb091_alpha_dummy_140 R p) from (by
          unfold
            nb091_alpha_dummy_140;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0129
                    R p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb091_alpha_dummy_127
        D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb091_alpha_dummy_129 R p))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb091_alpha_dummy_135 D R) ≠ (nb091_alpha_dummy_141 D R) from
        (by
          unfold
            nb091_alpha_dummy_141;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0134
                    D R)
                  0)))) (show (nb091_alpha_dummy_138 R p) ≠ (nb091_alpha_dummy_142 R p) from (by
          unfold
            nb091_alpha_dummy_142;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0135
                    R p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_135 D R) ≠
        (nb091_alpha_dummy_139 D R) from (by
          unfold
            nb091_alpha_dummy_139;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0132
                    D R)
                  0)))) (show (nb091_alpha_dummy_138 R p) ≠ (nb091_alpha_dummy_140 R p) from (by
          unfold
            nb091_alpha_dummy_140;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0133
                    R p)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb091_alpha_dummy_135 D R), (nb091_alpha_dummy_138 R p)),
        ((nb091_alpha_dummy_134 D R), (nb091_alpha_dummy_137 R p)),
        ((nb091_alpha_dummy_133 D R), (nb091_alpha_dummy_136 R p)),
        ((nb091_alpha_dummy_131 D R), (nb091_alpha_dummy_132 R p)),
        ((nb091_alpha_dummy_127 D R), (nb091_alpha_dummy_129 R p)),
        ((nb091_alpha_dummy_128 D R), (nb091_alpha_dummy_130 R p)),
        ((nb091_alpha_dummy_120 D R), (nb091_alpha_dummy_122 R p)),
        ((nb091_alpha_dummy_119 D R), (nb091_alpha_dummy_121 R p)),
        ((nb091_alpha_dummy_125 D R), (nb091_alpha_dummy_126 R p)),
        ((nb091_alpha_dummy_123 D R), (nb091_alpha_dummy_124 R p)),
        ((nb091_alpha_dummy_106 D R), (nb091_alpha_dummy_108 R p)),
        ((nb091_alpha_dummy_105 D R), (nb091_alpha_dummy_107 R p)),
        ((nb091_alpha_dummy_103 D R), (nb091_alpha_dummy_104 D R p)),
        ((nb091_alpha_dummy_101 D R), (nb091_alpha_dummy_102 D R p)),
        ((nb091_alpha_dummy_060 D R), (nb091_alpha_dummy_062 D R p)),
        ((nb091_alpha_dummy_059 D R), (nb091_alpha_dummy_061 D R p)),
        ((nb091_alpha_dummy_063 D R), (nb091_alpha_dummy_064 D R p)),
        ((nb091_alpha_dummy_057 D R), (nb091_alpha_dummy_058 D R p)),
        ((nb091_alpha_dummy_055 D R), (nb091_alpha_dummy_056 D R p)),
        ((nb091_alpha_dummy_048 D R), (nb091_alpha_dummy_050 D R p)),
        ((nb091_alpha_dummy_047 D R), (nb091_alpha_dummy_049 D R p)),
        ((nb091_alpha_dummy_053 D R), (nb091_alpha_dummy_054 D R p)),
        ((nb091_alpha_dummy_051 D R), (nb091_alpha_dummy_052 D R p)),
        ((nb091_alpha_dummy_045 D R), (nb091_alpha_dummy_046 D R p)),
        ((nb091_alpha_dummy_042 D R), (nb091_alpha_dummy_044 D R p)),
        ((nb091_alpha_dummy_041 D R), (nb091_alpha_dummy_043 D R p)),
        ((nb091_alpha_dummy_001 D R), (nb091_alpha_dummy_002 D R p)),
        ((nb091_alpha_dummy_000 D R), p), ((nb091_alpha_dummy_003 D R),
        (nb091_alpha_dummy_004 D R p))] (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb091_alpha_dummy_127 D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb091_alpha_dummy_129 R p))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb091_alpha_dummy_127 D R))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb091_alpha_dummy_129 R
        p))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb091_alpha_dummy_134 D R) ≠ (nb091_alpha_dummy_145 D R) from
        (by
          unfold
            nb091_alpha_dummy_145;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0138
                    D R)
                  0)))) (show (nb091_alpha_dummy_137 R p) ≠ (nb091_alpha_dummy_146 R p) from (by
          unfold
            nb091_alpha_dummy_146;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0139
                    R p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_134 D R) ≠
        (nb091_alpha_dummy_143 D R) from (by
          unfold
            nb091_alpha_dummy_143;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0136
                    D R)
                  0)))) (show (nb091_alpha_dummy_137 R p) ≠ (nb091_alpha_dummy_144 R p) from (by
          unfold
            nb091_alpha_dummy_144;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0137
                    R p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb091_alpha_dummy_127
        D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb091_alpha_dummy_129 R p))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb091_alpha_dummy_134 D R) ≠ (nb091_alpha_dummy_145 D R) from
        (by
          unfold
            nb091_alpha_dummy_145;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0138
                    D R)
                  0)))) (show (nb091_alpha_dummy_137 R p) ≠ (nb091_alpha_dummy_146 R p) from (by
          unfold
            nb091_alpha_dummy_146;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0139
                    R p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_134 D R) ≠
        (nb091_alpha_dummy_143 D R) from (by
          unfold
            nb091_alpha_dummy_143;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0136
                    D R)
                  0)))) (show (nb091_alpha_dummy_137 R p) ≠ (nb091_alpha_dummy_144 R p) from (by
          unfold
            nb091_alpha_dummy_144;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0137
                    R p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb091_alpha_dummy_127
        D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb091_alpha_dummy_129 R p))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb091_alpha_dummy_135
        D R) ≠ (nb091_alpha_dummy_147 D R) from (by
          unfold
            nb091_alpha_dummy_147;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0142
                    D R)
                  0)))) (show (nb091_alpha_dummy_138 R p) ≠ (nb091_alpha_dummy_148 R p) from (by
          unfold
            nb091_alpha_dummy_148;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0143
                    R p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_135 D R) ≠
        (nb091_alpha_dummy_143 D R) from (by
          unfold
            nb091_alpha_dummy_143;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0140
                    D R)
                  0)))) (show (nb091_alpha_dummy_138 R p) ≠ (nb091_alpha_dummy_144 R p) from (by
          unfold
            nb091_alpha_dummy_144;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0141
                    R p)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb091_alpha_dummy_135
        D R) ≠ (nb091_alpha_dummy_147 D R) from (by
          unfold
            nb091_alpha_dummy_147;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0142
                    D R)
                  0)))) (show (nb091_alpha_dummy_138 R p) ≠ (nb091_alpha_dummy_148 R p) from (by
          unfold
            nb091_alpha_dummy_148;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0143
                    R p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_135 D R) ≠
        (nb091_alpha_dummy_143 D R) from (by
          unfold
            nb091_alpha_dummy_143;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0140
                    D R)
                  0)))) (show (nb091_alpha_dummy_138 R p) ≠ (nb091_alpha_dummy_144 R p) from (by
          unfold
            nb091_alpha_dummy_144;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0141
                    R p)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb091_alpha_dummy_127 D R) ≠ (nb091_alpha_dummy_131 D R)
                                      from (by
                                        unfold nb091_alpha_dummy_131;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb091_support_mem_0124 D R) 0)))) (show
                                      (nb091_alpha_dummy_129 R p) ≠ (nb091_alpha_dummy_132 R p)
                                      from (by
                                        unfold nb091_alpha_dummy_132;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb091_support_mem_0125 R p) 0))))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                  [((nb091_alpha_dummy_131 D R), (nb091_alpha_dummy_132 R p)),
                                    ((nb091_alpha_dummy_127 D R), (nb091_alpha_dummy_129 R p)),
                                    ((nb091_alpha_dummy_128 D R), (nb091_alpha_dummy_130 R p)),
                                    ((nb091_alpha_dummy_120 D R), (nb091_alpha_dummy_122 R p)),
                                    ((nb091_alpha_dummy_119 D R), (nb091_alpha_dummy_121 R p)),
                                    ((nb091_alpha_dummy_125 D R), (nb091_alpha_dummy_126 R p)),
                                    ((nb091_alpha_dummy_123 D R), (nb091_alpha_dummy_124 R p)),
                                    ((nb091_alpha_dummy_106 D R), (nb091_alpha_dummy_108 R p)),
                                    ((nb091_alpha_dummy_105 D R), (nb091_alpha_dummy_107 R p)),
                                    ((nb091_alpha_dummy_103 D R),
                                      (nb091_alpha_dummy_104 D R p)),
                                    ((nb091_alpha_dummy_101 D R),
                                      (nb091_alpha_dummy_102 D R p)),
                                    ((nb091_alpha_dummy_060 D R),
                                      (nb091_alpha_dummy_062 D R p)),
                                    ((nb091_alpha_dummy_059 D R),
                                      (nb091_alpha_dummy_061 D R p)),
                                    ((nb091_alpha_dummy_063 D R),
                                      (nb091_alpha_dummy_064 D R p)),
                                    ((nb091_alpha_dummy_057 D R),
                                      (nb091_alpha_dummy_058 D R p)),
                                    ((nb091_alpha_dummy_055 D R),
                                      (nb091_alpha_dummy_056 D R p)),
                                    ((nb091_alpha_dummy_048 D R),
                                      (nb091_alpha_dummy_050 D R p)),
                                    ((nb091_alpha_dummy_047 D R),
                                      (nb091_alpha_dummy_049 D R p)),
                                    ((nb091_alpha_dummy_053 D R),
                                      (nb091_alpha_dummy_054 D R p)),
                                    ((nb091_alpha_dummy_051 D R),
                                      (nb091_alpha_dummy_052 D R p)),
                                    ((nb091_alpha_dummy_045 D R),
                                      (nb091_alpha_dummy_046 D R p)),
                                    ((nb091_alpha_dummy_042 D R),
                                      (nb091_alpha_dummy_044 D R p)),
                                    ((nb091_alpha_dummy_041 D R),
                                      (nb091_alpha_dummy_043 D R p)),
                                    ((nb091_alpha_dummy_001 D R),
                                      (nb091_alpha_dummy_002 D R p)),
                                    ((nb091_alpha_dummy_000 D R), p),
                                    ((nb091_alpha_dummy_003 D R),
                                      (nb091_alpha_dummy_004 D R p))]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there (show
                                    (nb091_alpha_dummy_127 D R) ≠ (nb091_alpha_dummy_131 D R)
                                    from (by
                                      unfold nb091_alpha_dummy_131;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb091_support_mem_0124 D R)
                                              0)))) (show (nb091_alpha_dummy_129 R p) ≠
                                      (nb091_alpha_dummy_132 R p) from (by
                                      unfold nb091_alpha_dummy_132;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb091_support_mem_0125 R p)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb091_alpha_dummy_127 D R) ≠ (nb091_alpha_dummy_131 D R)
                                      from (by
                                        unfold nb091_alpha_dummy_131;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb091_support_mem_0124 D R) 0)))) (show
                                      (nb091_alpha_dummy_129 R p) ≠ (nb091_alpha_dummy_132 R p)
                                      from (by
                                        unfold nb091_alpha_dummy_132;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb091_support_mem_0125 R p) 0))))
                                    (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                  [((nb091_alpha_dummy_131 D R), (nb091_alpha_dummy_132 R p)),
                                    ((nb091_alpha_dummy_127 D R), (nb091_alpha_dummy_129 R p)),
                                    ((nb091_alpha_dummy_128 D R), (nb091_alpha_dummy_130 R p)),
                                    ((nb091_alpha_dummy_120 D R), (nb091_alpha_dummy_122 R p)),
                                    ((nb091_alpha_dummy_119 D R), (nb091_alpha_dummy_121 R p)),
                                    ((nb091_alpha_dummy_125 D R), (nb091_alpha_dummy_126 R p)),
                                    ((nb091_alpha_dummy_123 D R), (nb091_alpha_dummy_124 R p)),
                                    ((nb091_alpha_dummy_106 D R), (nb091_alpha_dummy_108 R p)),
                                    ((nb091_alpha_dummy_105 D R), (nb091_alpha_dummy_107 R p)),
                                    ((nb091_alpha_dummy_103 D R),
                                      (nb091_alpha_dummy_104 D R p)),
                                    ((nb091_alpha_dummy_101 D R),
                                      (nb091_alpha_dummy_102 D R p)),
                                    ((nb091_alpha_dummy_060 D R),
                                      (nb091_alpha_dummy_062 D R p)),
                                    ((nb091_alpha_dummy_059 D R),
                                      (nb091_alpha_dummy_061 D R p)),
                                    ((nb091_alpha_dummy_063 D R),
                                      (nb091_alpha_dummy_064 D R p)),
                                    ((nb091_alpha_dummy_057 D R),
                                      (nb091_alpha_dummy_058 D R p)),
                                    ((nb091_alpha_dummy_055 D R),
                                      (nb091_alpha_dummy_056 D R p)),
                                    ((nb091_alpha_dummy_048 D R),
                                      (nb091_alpha_dummy_050 D R p)),
                                    ((nb091_alpha_dummy_047 D R),
                                      (nb091_alpha_dummy_049 D R p)),
                                    ((nb091_alpha_dummy_053 D R),
                                      (nb091_alpha_dummy_054 D R p)),
                                    ((nb091_alpha_dummy_051 D R),
                                      (nb091_alpha_dummy_052 D R p)),
                                    ((nb091_alpha_dummy_045 D R),
                                      (nb091_alpha_dummy_046 D R p)),
                                    ((nb091_alpha_dummy_042 D R),
                                      (nb091_alpha_dummy_044 D R p)),
                                    ((nb091_alpha_dummy_041 D R),
                                      (nb091_alpha_dummy_043 D R p)),
                                    ((nb091_alpha_dummy_001 D R),
                                      (nb091_alpha_dummy_002 D R p)),
                                    ((nb091_alpha_dummy_000 D R), p),
                                    ((nb091_alpha_dummy_003 D R),
                                      (nb091_alpha_dummy_004 D R p))]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there
                    (show (nb091_alpha_dummy_106 D R) ≠ (nb091_alpha_dummy_120 D R) from (by
                        unfold nb091_alpha_dummy_120;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb091_support_mem_0116 D R) 1))))
                    (show (nb091_alpha_dummy_108 R p) ≠ (nb091_alpha_dummy_122 R p) from (by
                        unfold nb091_alpha_dummy_122;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb091_support_mem_0118 R p) 1))))
                    (TAlphaVar.there
                      (show (nb091_alpha_dummy_106 D R) ≠ (nb091_alpha_dummy_119 D R) from (by
                          unfold nb091_alpha_dummy_119;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb091_support_mem_0116 D R) 0))))
                      (show (nb091_alpha_dummy_108 R p) ≠ (nb091_alpha_dummy_121 R p) from (by
                          unfold nb091_alpha_dummy_121;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb091_support_mem_0118 R p) 0))))
                      (TAlphaVar.there
                        (show (nb091_alpha_dummy_106 D R) ≠ (nb091_alpha_dummy_125 D R) from (by
                            unfold nb091_alpha_dummy_125;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb091_support_mem_0120 D R) 0))))
                        (show (nb091_alpha_dummy_108 R p) ≠ (nb091_alpha_dummy_126 R p) from (by
                            unfold nb091_alpha_dummy_126;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb091_support_mem_0121 R p) 0))))
                        (TAlphaVar.there
                          (show (nb091_alpha_dummy_106 D R) ≠ (nb091_alpha_dummy_123 D R) from
                            (by
                              unfold nb091_alpha_dummy_123;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb091_support_mem_0117 D R) 0))))
                          (show (nb091_alpha_dummy_108 R p) ≠ (nb091_alpha_dummy_124 R p) from
                            (by
                              unfold nb091_alpha_dummy_124;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb091_support_mem_0119 R p) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb091_alpha_dummy_106 D R))).fv ∪
                        ((Class.cv (nb091_alpha_dummy_105 D R))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb091_alpha_dummy_108 R p))).fv ∪
                        ((Class.cv (nb091_alpha_dummy_107 R p))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb091_alpha_dummy_120 D R) ≠ (nb091_alpha_dummy_127 D R) from (by
                                unfold nb091_alpha_dummy_127;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb091_support_mem_0122 D R) 0)))) (show
                              (nb091_alpha_dummy_122 R p) ≠ (nb091_alpha_dummy_129 R p) from (by
                                unfold nb091_alpha_dummy_129;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb091_support_mem_0123 R p) 0))))
                            (TAlphaVar.there (show
                                (nb091_alpha_dummy_120 D R) ≠ (nb091_alpha_dummy_128 D R) from
                                (by
                                  unfold nb091_alpha_dummy_128;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb091_support_mem_0122 D R)
                                          1)))) (show
                                (nb091_alpha_dummy_122 R p) ≠ (nb091_alpha_dummy_130 R p) from
                                (by
                                  unfold nb091_alpha_dummy_130;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb091_support_mem_0123 R p)
                                          1)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq
                        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
                              (((Class.cv (nb091_alpha_dummy_120 D R))).fv) (by decide))
                            (freshVar_injective
                              (((Class.cv (nb091_alpha_dummy_122 R p))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb091_alpha_dummy_127 D R) ≠ (nb091_alpha_dummy_134 D R) from (by
          unfold nb091_alpha_dummy_134;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0126 D R)
                  1)))) (show (nb091_alpha_dummy_129 R p) ≠ (nb091_alpha_dummy_137 R p) from (by
          unfold nb091_alpha_dummy_137;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0127 R p)
                  1)))) (TAlphaVar.there (show (nb091_alpha_dummy_127 D R) ≠
        (nb091_alpha_dummy_133 D R) from (by
          unfold nb091_alpha_dummy_133;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0126 D R)
                  0)))) (show (nb091_alpha_dummy_129 R p) ≠ (nb091_alpha_dummy_136 R p) from (by
          unfold nb091_alpha_dummy_136;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0127 R p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_127 D R) ≠
        (nb091_alpha_dummy_131 D R) from (by
          unfold nb091_alpha_dummy_131;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0124 D R)
                  0)))) (show (nb091_alpha_dummy_129 R p) ≠ (nb091_alpha_dummy_132 R p) from (by
          unfold nb091_alpha_dummy_132;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0125 R p)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb091_alpha_dummy_135 D R), (nb091_alpha_dummy_138 R p)),
        ((nb091_alpha_dummy_134 D R), (nb091_alpha_dummy_137 R p)),
        ((nb091_alpha_dummy_133 D R), (nb091_alpha_dummy_136 R p)),
        ((nb091_alpha_dummy_131 D R), (nb091_alpha_dummy_132 R p)),
        ((nb091_alpha_dummy_127 D R), (nb091_alpha_dummy_129 R p)),
        ((nb091_alpha_dummy_128 D R), (nb091_alpha_dummy_130 R p)),
        ((nb091_alpha_dummy_120 D R), (nb091_alpha_dummy_122 R p)),
        ((nb091_alpha_dummy_119 D R), (nb091_alpha_dummy_121 R p)),
        ((nb091_alpha_dummy_125 D R), (nb091_alpha_dummy_126 R p)),
        ((nb091_alpha_dummy_123 D R), (nb091_alpha_dummy_124 R p)),
        ((nb091_alpha_dummy_106 D R), (nb091_alpha_dummy_108 R p)),
        ((nb091_alpha_dummy_105 D R), (nb091_alpha_dummy_107 R p)),
        ((nb091_alpha_dummy_103 D R), (nb091_alpha_dummy_104 D R p)),
        ((nb091_alpha_dummy_101 D R), (nb091_alpha_dummy_102 D R p)),
        ((nb091_alpha_dummy_060 D R), (nb091_alpha_dummy_062 D R p)),
        ((nb091_alpha_dummy_059 D R), (nb091_alpha_dummy_061 D R p)),
        ((nb091_alpha_dummy_063 D R), (nb091_alpha_dummy_064 D R p)),
        ((nb091_alpha_dummy_057 D R), (nb091_alpha_dummy_058 D R p)),
        ((nb091_alpha_dummy_055 D R), (nb091_alpha_dummy_056 D R p)),
        ((nb091_alpha_dummy_048 D R), (nb091_alpha_dummy_050 D R p)),
        ((nb091_alpha_dummy_047 D R), (nb091_alpha_dummy_049 D R p)),
        ((nb091_alpha_dummy_053 D R), (nb091_alpha_dummy_054 D R p)),
        ((nb091_alpha_dummy_051 D R), (nb091_alpha_dummy_052 D R p)),
        ((nb091_alpha_dummy_045 D R), (nb091_alpha_dummy_046 D R p)),
        ((nb091_alpha_dummy_042 D R), (nb091_alpha_dummy_044 D R p)),
        ((nb091_alpha_dummy_041 D R), (nb091_alpha_dummy_043 D R p)),
        ((nb091_alpha_dummy_001 D R), (nb091_alpha_dummy_002 D R p)),
        ((nb091_alpha_dummy_000 D R), p), ((nb091_alpha_dummy_003 D R),
        (nb091_alpha_dummy_004 D R p))] (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
        (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb091_alpha_dummy_134 D R) ≠ (nb091_alpha_dummy_141 D R) from
        (by
          unfold
            nb091_alpha_dummy_141;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0130
                    D R)
                  0)))) (show (nb091_alpha_dummy_137 R p) ≠ (nb091_alpha_dummy_142 R p) from (by
          unfold
            nb091_alpha_dummy_142;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0131
                    R p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_134 D R) ≠
        (nb091_alpha_dummy_139 D R) from (by
          unfold
            nb091_alpha_dummy_139;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0128
                    D R)
                  0)))) (show (nb091_alpha_dummy_137 R p) ≠ (nb091_alpha_dummy_140 R p) from (by
          unfold
            nb091_alpha_dummy_140;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0129
                    R p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb091_alpha_dummy_127
        D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb091_alpha_dummy_129 R p))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb091_alpha_dummy_135 D R) ≠ (nb091_alpha_dummy_141 D R) from
        (by
          unfold
            nb091_alpha_dummy_141;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0134
                    D R)
                  0)))) (show (nb091_alpha_dummy_138 R p) ≠ (nb091_alpha_dummy_142 R p) from (by
          unfold
            nb091_alpha_dummy_142;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0135
                    R p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_135 D R) ≠
        (nb091_alpha_dummy_139 D R) from (by
          unfold
            nb091_alpha_dummy_139;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0132
                    D R)
                  0)))) (show (nb091_alpha_dummy_138 R p) ≠ (nb091_alpha_dummy_140 R p) from (by
          unfold
            nb091_alpha_dummy_140;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0133
                    R p)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb091_alpha_dummy_134 D R) ≠ (nb091_alpha_dummy_141 D R) from
        (by
          unfold
            nb091_alpha_dummy_141;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0130
                    D R)
                  0)))) (show (nb091_alpha_dummy_137 R p) ≠ (nb091_alpha_dummy_142 R p) from (by
          unfold
            nb091_alpha_dummy_142;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0131
                    R p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_134 D R) ≠
        (nb091_alpha_dummy_139 D R) from (by
          unfold
            nb091_alpha_dummy_139;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0128
                    D R)
                  0)))) (show (nb091_alpha_dummy_137 R p) ≠ (nb091_alpha_dummy_140 R p) from (by
          unfold
            nb091_alpha_dummy_140;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0129
                    R p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb091_alpha_dummy_127
        D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb091_alpha_dummy_129 R p))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb091_alpha_dummy_135 D R) ≠ (nb091_alpha_dummy_141 D R) from
        (by
          unfold
            nb091_alpha_dummy_141;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0134
                    D R)
                  0)))) (show (nb091_alpha_dummy_138 R p) ≠ (nb091_alpha_dummy_142 R p) from (by
          unfold
            nb091_alpha_dummy_142;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0135
                    R p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_135 D R) ≠
        (nb091_alpha_dummy_139 D R) from (by
          unfold
            nb091_alpha_dummy_139;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0132
                    D R)
                  0)))) (show (nb091_alpha_dummy_138 R p) ≠ (nb091_alpha_dummy_140 R p) from (by
          unfold
            nb091_alpha_dummy_140;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0133
                    R p)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb091_alpha_dummy_135 D R), (nb091_alpha_dummy_138 R p)),
        ((nb091_alpha_dummy_134 D R), (nb091_alpha_dummy_137 R p)),
        ((nb091_alpha_dummy_133 D R), (nb091_alpha_dummy_136 R p)),
        ((nb091_alpha_dummy_131 D R), (nb091_alpha_dummy_132 R p)),
        ((nb091_alpha_dummy_127 D R), (nb091_alpha_dummy_129 R p)),
        ((nb091_alpha_dummy_128 D R), (nb091_alpha_dummy_130 R p)),
        ((nb091_alpha_dummy_120 D R), (nb091_alpha_dummy_122 R p)),
        ((nb091_alpha_dummy_119 D R), (nb091_alpha_dummy_121 R p)),
        ((nb091_alpha_dummy_125 D R), (nb091_alpha_dummy_126 R p)),
        ((nb091_alpha_dummy_123 D R), (nb091_alpha_dummy_124 R p)),
        ((nb091_alpha_dummy_106 D R), (nb091_alpha_dummy_108 R p)),
        ((nb091_alpha_dummy_105 D R), (nb091_alpha_dummy_107 R p)),
        ((nb091_alpha_dummy_103 D R), (nb091_alpha_dummy_104 D R p)),
        ((nb091_alpha_dummy_101 D R), (nb091_alpha_dummy_102 D R p)),
        ((nb091_alpha_dummy_060 D R), (nb091_alpha_dummy_062 D R p)),
        ((nb091_alpha_dummy_059 D R), (nb091_alpha_dummy_061 D R p)),
        ((nb091_alpha_dummy_063 D R), (nb091_alpha_dummy_064 D R p)),
        ((nb091_alpha_dummy_057 D R), (nb091_alpha_dummy_058 D R p)),
        ((nb091_alpha_dummy_055 D R), (nb091_alpha_dummy_056 D R p)),
        ((nb091_alpha_dummy_048 D R), (nb091_alpha_dummy_050 D R p)),
        ((nb091_alpha_dummy_047 D R), (nb091_alpha_dummy_049 D R p)),
        ((nb091_alpha_dummy_053 D R), (nb091_alpha_dummy_054 D R p)),
        ((nb091_alpha_dummy_051 D R), (nb091_alpha_dummy_052 D R p)),
        ((nb091_alpha_dummy_045 D R), (nb091_alpha_dummy_046 D R p)),
        ((nb091_alpha_dummy_042 D R), (nb091_alpha_dummy_044 D R p)),
        ((nb091_alpha_dummy_041 D R), (nb091_alpha_dummy_043 D R p)),
        ((nb091_alpha_dummy_001 D R), (nb091_alpha_dummy_002 D R p)),
        ((nb091_alpha_dummy_000 D R), p), ((nb091_alpha_dummy_003 D R),
        (nb091_alpha_dummy_004 D R p))] (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb091_alpha_dummy_127 D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb091_alpha_dummy_129 R p))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb091_alpha_dummy_127 D R))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb091_alpha_dummy_129 R
        p))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb091_alpha_dummy_134 D R) ≠ (nb091_alpha_dummy_145 D R) from
        (by
          unfold
            nb091_alpha_dummy_145;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0138
                    D R)
                  0)))) (show (nb091_alpha_dummy_137 R p) ≠ (nb091_alpha_dummy_146 R p) from (by
          unfold
            nb091_alpha_dummy_146;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0139
                    R p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_134 D R) ≠
        (nb091_alpha_dummy_143 D R) from (by
          unfold
            nb091_alpha_dummy_143;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0136
                    D R)
                  0)))) (show (nb091_alpha_dummy_137 R p) ≠ (nb091_alpha_dummy_144 R p) from (by
          unfold
            nb091_alpha_dummy_144;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0137
                    R p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb091_alpha_dummy_127
        D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb091_alpha_dummy_129 R p))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb091_alpha_dummy_134 D R) ≠ (nb091_alpha_dummy_145 D R) from
        (by
          unfold
            nb091_alpha_dummy_145;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0138
                    D R)
                  0)))) (show (nb091_alpha_dummy_137 R p) ≠ (nb091_alpha_dummy_146 R p) from (by
          unfold
            nb091_alpha_dummy_146;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0139
                    R p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_134 D R) ≠
        (nb091_alpha_dummy_143 D R) from (by
          unfold
            nb091_alpha_dummy_143;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0136
                    D R)
                  0)))) (show (nb091_alpha_dummy_137 R p) ≠ (nb091_alpha_dummy_144 R p) from (by
          unfold
            nb091_alpha_dummy_144;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0137
                    R p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb091_alpha_dummy_127
        D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb091_alpha_dummy_129 R p))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _
        _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb091_alpha_dummy_135
        D R) ≠ (nb091_alpha_dummy_147 D R) from (by
          unfold
            nb091_alpha_dummy_147;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0142
                    D R)
                  0)))) (show (nb091_alpha_dummy_138 R p) ≠ (nb091_alpha_dummy_148 R p) from (by
          unfold
            nb091_alpha_dummy_148;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0143
                    R p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_135 D R) ≠
        (nb091_alpha_dummy_143 D R) from (by
          unfold
            nb091_alpha_dummy_143;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0140
                    D R)
                  0)))) (show (nb091_alpha_dummy_138 R p) ≠ (nb091_alpha_dummy_144 R p) from (by
          unfold
            nb091_alpha_dummy_144;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0141
                    R p)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb091_alpha_dummy_135
        D R) ≠ (nb091_alpha_dummy_147 D R) from (by
          unfold
            nb091_alpha_dummy_147;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0142
                    D R)
                  0)))) (show (nb091_alpha_dummy_138 R p) ≠ (nb091_alpha_dummy_148 R p) from (by
          unfold
            nb091_alpha_dummy_148;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0143
                    R p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_135 D R) ≠
        (nb091_alpha_dummy_143 D R) from (by
          unfold
            nb091_alpha_dummy_143;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0140
                    D R)
                  0)))) (show (nb091_alpha_dummy_138 R p) ≠ (nb091_alpha_dummy_144 R p) from (by
          unfold
            nb091_alpha_dummy_144;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0141
                    R p)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb091_alpha_dummy_127 D R) ≠
        (nb091_alpha_dummy_131 D R) from (by
                                          unfold nb091_alpha_dummy_131;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb091_support_mem_0124 D R) 0)))) (show
                                        (nb091_alpha_dummy_129 R p) ≠
        (nb091_alpha_dummy_132 R p) from (by
                                          unfold nb091_alpha_dummy_132;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb091_support_mem_0125 R p) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb091_alpha_dummy_131 D R), (nb091_alpha_dummy_132 R p)),
                                      ((nb091_alpha_dummy_127 D R),
                                        (nb091_alpha_dummy_129 R p)),
                                      ((nb091_alpha_dummy_128 D R),
                                        (nb091_alpha_dummy_130 R p)),
                                      ((nb091_alpha_dummy_120 D R),
                                        (nb091_alpha_dummy_122 R p)),
                                      ((nb091_alpha_dummy_119 D R),
                                        (nb091_alpha_dummy_121 R p)),
                                      ((nb091_alpha_dummy_125 D R),
                                        (nb091_alpha_dummy_126 R p)),
                                      ((nb091_alpha_dummy_123 D R),
                                        (nb091_alpha_dummy_124 R p)),
                                      ((nb091_alpha_dummy_106 D R),
                                        (nb091_alpha_dummy_108 R p)),
                                      ((nb091_alpha_dummy_105 D R),
                                        (nb091_alpha_dummy_107 R p)),
                                      ((nb091_alpha_dummy_103 D R),
                                        (nb091_alpha_dummy_104 D R p)),
                                      ((nb091_alpha_dummy_101 D R),
                                        (nb091_alpha_dummy_102 D R p)),
                                      ((nb091_alpha_dummy_060 D R),
                                        (nb091_alpha_dummy_062 D R p)),
                                      ((nb091_alpha_dummy_059 D R),
                                        (nb091_alpha_dummy_061 D R p)),
                                      ((nb091_alpha_dummy_063 D R),
                                        (nb091_alpha_dummy_064 D R p)),
                                      ((nb091_alpha_dummy_057 D R),
                                        (nb091_alpha_dummy_058 D R p)),
                                      ((nb091_alpha_dummy_055 D R),
                                        (nb091_alpha_dummy_056 D R p)),
                                      ((nb091_alpha_dummy_048 D R),
                                        (nb091_alpha_dummy_050 D R p)),
                                      ((nb091_alpha_dummy_047 D R),
                                        (nb091_alpha_dummy_049 D R p)),
                                      ((nb091_alpha_dummy_053 D R),
                                        (nb091_alpha_dummy_054 D R p)),
                                      ((nb091_alpha_dummy_051 D R),
                                        (nb091_alpha_dummy_052 D R p)),
                                      ((nb091_alpha_dummy_045 D R),
                                        (nb091_alpha_dummy_046 D R p)),
                                      ((nb091_alpha_dummy_042 D R),
                                        (nb091_alpha_dummy_044 D R p)),
                                      ((nb091_alpha_dummy_041 D R),
                                        (nb091_alpha_dummy_043 D R p)),
                                      ((nb091_alpha_dummy_001 D R),
                                        (nb091_alpha_dummy_002 D R p)),
                                      ((nb091_alpha_dummy_000 D R), p),
                                      ((nb091_alpha_dummy_003 D R),
                                        (nb091_alpha_dummy_004 D R p))]
                                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb091_alpha_dummy_127 D R) ≠ (nb091_alpha_dummy_131 D R)
                                      from (by
                                        unfold nb091_alpha_dummy_131;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb091_support_mem_0124 D R) 0)))) (show
                                      (nb091_alpha_dummy_129 R p) ≠ (nb091_alpha_dummy_132 R p)
                                      from (by
                                        unfold nb091_alpha_dummy_132;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb091_support_mem_0125 R p) 0))))
                                    (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb091_alpha_dummy_127 D R) ≠
        (nb091_alpha_dummy_131 D R) from (by
                                          unfold nb091_alpha_dummy_131;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb091_support_mem_0124 D R) 0)))) (show
                                        (nb091_alpha_dummy_129 R p) ≠
        (nb091_alpha_dummy_132 R p) from (by
                                          unfold nb091_alpha_dummy_132;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb091_support_mem_0125 R p) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb091_alpha_dummy_131 D R), (nb091_alpha_dummy_132 R p)),
                                      ((nb091_alpha_dummy_127 D R),
                                        (nb091_alpha_dummy_129 R p)),
                                      ((nb091_alpha_dummy_128 D R),
                                        (nb091_alpha_dummy_130 R p)),
                                      ((nb091_alpha_dummy_120 D R),
                                        (nb091_alpha_dummy_122 R p)),
                                      ((nb091_alpha_dummy_119 D R),
                                        (nb091_alpha_dummy_121 R p)),
                                      ((nb091_alpha_dummy_125 D R),
                                        (nb091_alpha_dummy_126 R p)),
                                      ((nb091_alpha_dummy_123 D R),
                                        (nb091_alpha_dummy_124 R p)),
                                      ((nb091_alpha_dummy_106 D R),
                                        (nb091_alpha_dummy_108 R p)),
                                      ((nb091_alpha_dummy_105 D R),
                                        (nb091_alpha_dummy_107 R p)),
                                      ((nb091_alpha_dummy_103 D R),
                                        (nb091_alpha_dummy_104 D R p)),
                                      ((nb091_alpha_dummy_101 D R),
                                        (nb091_alpha_dummy_102 D R p)),
                                      ((nb091_alpha_dummy_060 D R),
                                        (nb091_alpha_dummy_062 D R p)),
                                      ((nb091_alpha_dummy_059 D R),
                                        (nb091_alpha_dummy_061 D R p)),
                                      ((nb091_alpha_dummy_063 D R),
                                        (nb091_alpha_dummy_064 D R p)),
                                      ((nb091_alpha_dummy_057 D R),
                                        (nb091_alpha_dummy_058 D R p)),
                                      ((nb091_alpha_dummy_055 D R),
                                        (nb091_alpha_dummy_056 D R p)),
                                      ((nb091_alpha_dummy_048 D R),
                                        (nb091_alpha_dummy_050 D R p)),
                                      ((nb091_alpha_dummy_047 D R),
                                        (nb091_alpha_dummy_049 D R p)),
                                      ((nb091_alpha_dummy_053 D R),
                                        (nb091_alpha_dummy_054 D R p)),
                                      ((nb091_alpha_dummy_051 D R),
                                        (nb091_alpha_dummy_052 D R p)),
                                      ((nb091_alpha_dummy_045 D R),
                                        (nb091_alpha_dummy_046 D R p)),
                                      ((nb091_alpha_dummy_042 D R),
                                        (nb091_alpha_dummy_044 D R p)),
                                      ((nb091_alpha_dummy_041 D R),
                                        (nb091_alpha_dummy_043 D R p)),
                                      ((nb091_alpha_dummy_001 D R),
                                        (nb091_alpha_dummy_002 D R p)),
                                      ((nb091_alpha_dummy_000 D R), p),
                                      ((nb091_alpha_dummy_003 D R),
                                        (nb091_alpha_dummy_004 D R p))] (syn_cnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))

@[expose]
noncomputable def nb091_split_alpha_0006 (D : Class) (R : Class) (p : Var) :
    TAlphaWff
      [((nb091_alpha_dummy_153 D R), (nb091_alpha_dummy_154 R p)),
        ((nb091_alpha_dummy_151 D R), (nb091_alpha_dummy_152 R p)),
        ((nb091_alpha_dummy_120 D R), (nb091_alpha_dummy_122 R p)),
        ((nb091_alpha_dummy_119 D R), (nb091_alpha_dummy_121 R p)),
        ((nb091_alpha_dummy_149 D R), (nb091_alpha_dummy_150 R p)),
        ((nb091_alpha_dummy_123 D R), (nb091_alpha_dummy_124 R p)),
        ((nb091_alpha_dummy_106 D R), (nb091_alpha_dummy_108 R p)),
        ((nb091_alpha_dummy_105 D R), (nb091_alpha_dummy_107 R p)),
        ((nb091_alpha_dummy_103 D R), (nb091_alpha_dummy_104 D R p)),
        ((nb091_alpha_dummy_101 D R), (nb091_alpha_dummy_102 D R p)),
        ((nb091_alpha_dummy_060 D R), (nb091_alpha_dummy_062 D R p)),
        ((nb091_alpha_dummy_059 D R), (nb091_alpha_dummy_061 D R p)),
        ((nb091_alpha_dummy_063 D R), (nb091_alpha_dummy_064 D R p)),
        ((nb091_alpha_dummy_057 D R), (nb091_alpha_dummy_058 D R p)),
        ((nb091_alpha_dummy_055 D R), (nb091_alpha_dummy_056 D R p)),
        ((nb091_alpha_dummy_048 D R), (nb091_alpha_dummy_050 D R p)),
        ((nb091_alpha_dummy_047 D R), (nb091_alpha_dummy_049 D R p)),
        ((nb091_alpha_dummy_053 D R), (nb091_alpha_dummy_054 D R p)),
        ((nb091_alpha_dummy_051 D R), (nb091_alpha_dummy_052 D R p)),
        ((nb091_alpha_dummy_045 D R), (nb091_alpha_dummy_046 D R p)),
        ((nb091_alpha_dummy_042 D R), (nb091_alpha_dummy_044 D R p)),
        ((nb091_alpha_dummy_041 D R), (nb091_alpha_dummy_043 D R p)),
        ((nb091_alpha_dummy_001 D R), (nb091_alpha_dummy_002 D R p)),
        ((nb091_alpha_dummy_000 D R), p),
        ((nb091_alpha_dummy_003 D R), (nb091_alpha_dummy_004 D R p))]
      (Wff.imp (Wff.classMem (Class.cv (nb091_alpha_dummy_153 D R))
          (syn_cphi (Class.cv (nb091_alpha_dummy_120 D R)))) (Wff.neg
          (Wff.classMem (Class.cv (nb091_alpha_dummy_153 D R))
            (syn_cphi (Class.cv (nb091_alpha_dummy_120 D R))))))
      (Wff.imp (Wff.classMem (Class.cv (nb091_alpha_dummy_154 R p))
          (syn_cphi (Class.cv (nb091_alpha_dummy_122 R p)))) (Wff.neg
          (Wff.classMem (Class.cv (nb091_alpha_dummy_154 R p))
            (syn_cphi (Class.cv (nb091_alpha_dummy_122 R p)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there
                  (show (nb091_alpha_dummy_120 D R) ≠ (nb091_alpha_dummy_127 D R) from (by
                      unfold nb091_alpha_dummy_127;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb091_support_mem_0122 D R) 0))))
                  (show (nb091_alpha_dummy_122 R p) ≠ (nb091_alpha_dummy_129 R p) from (by
                      unfold nb091_alpha_dummy_129;
                      with_reducible
                        exact
                          (Nat.ne_of_lt
                            (mem_lt_freshVar (nb091_support_mem_0123 R p) 0)))) (TAlphaVar.there
                    (show (nb091_alpha_dummy_120 D R) ≠ (nb091_alpha_dummy_128 D R) from (by
                        unfold nb091_alpha_dummy_128;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb091_support_mem_0122 D R) 1))))
                    (show (nb091_alpha_dummy_122 R p) ≠ (nb091_alpha_dummy_130 R p) from (by
                        unfold nb091_alpha_dummy_130;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb091_support_mem_0123 R p) 1))))
                    (TAlphaVar.there
                      (show (nb091_alpha_dummy_120 D R) ≠ (nb091_alpha_dummy_153 D R) from (by
                          unfold nb091_alpha_dummy_153;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb091_support_mem_0152 D R) 0))))
                      (show (nb091_alpha_dummy_122 R p) ≠ (nb091_alpha_dummy_154 R p) from (by
                          unfold nb091_alpha_dummy_154;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb091_support_mem_0153 R p) 0))))
                      (TAlphaVar.there
                        (show (nb091_alpha_dummy_120 D R) ≠ (nb091_alpha_dummy_151 D R) from (by
                            unfold nb091_alpha_dummy_151;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb091_support_mem_0150 D R) 0))))
                        (show (nb091_alpha_dummy_122 R p) ≠ (nb091_alpha_dummy_152 R p) from (by
                            unfold nb091_alpha_dummy_152;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb091_support_mem_0151 R p) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there
                  (freshVar_injective (((Class.cv (nb091_alpha_dummy_120 D R))).fv) (by decide))
                  (freshVar_injective (((Class.cv (nb091_alpha_dummy_122 R p))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                    (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb091_alpha_dummy_127 D R) ≠ (nb091_alpha_dummy_134 D R)
                                      from (by
                                        unfold nb091_alpha_dummy_134;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb091_support_mem_0126 D R) 1)))) (show
                                      (nb091_alpha_dummy_129 R p) ≠ (nb091_alpha_dummy_137 R p)
                                      from (by
                                        unfold nb091_alpha_dummy_137;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb091_support_mem_0127 R p) 1))))
                                    (TAlphaVar.there (show (nb091_alpha_dummy_127 D R) ≠
        (nb091_alpha_dummy_133 D R) from (by
                                          unfold nb091_alpha_dummy_133;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb091_support_mem_0126 D R) 0)))) (show
                                        (nb091_alpha_dummy_129 R p) ≠
        (nb091_alpha_dummy_136 R p) from (by
                                          unfold nb091_alpha_dummy_136;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb091_support_mem_0127 R p) 0))))
                                      (TAlphaVar.there (show (nb091_alpha_dummy_127 D R) ≠
        (nb091_alpha_dummy_131 D R) from (by
          unfold nb091_alpha_dummy_131;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0124 D R) 0)))) (show (nb091_alpha_dummy_129 R p) ≠
        (nb091_alpha_dummy_132 R p) from (by
          unfold nb091_alpha_dummy_132;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0125 R p) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.refl_of_closed [((nb091_alpha_dummy_135 D R),
        (nb091_alpha_dummy_138 R p)), ((nb091_alpha_dummy_134 D R),
        (nb091_alpha_dummy_137 R p)), ((nb091_alpha_dummy_133 D R),
        (nb091_alpha_dummy_136 R p)), ((nb091_alpha_dummy_131 D R),
        (nb091_alpha_dummy_132 R p)), ((nb091_alpha_dummy_127 D R),
        (nb091_alpha_dummy_129 R p)), ((nb091_alpha_dummy_128 D R),
        (nb091_alpha_dummy_130 R p)), ((nb091_alpha_dummy_153 D R),
        (nb091_alpha_dummy_154 R p)), ((nb091_alpha_dummy_151 D R),
        (nb091_alpha_dummy_152 R p)), ((nb091_alpha_dummy_120 D R),
        (nb091_alpha_dummy_122 R p)), ((nb091_alpha_dummy_119 D R),
        (nb091_alpha_dummy_121 R p)), ((nb091_alpha_dummy_149 D R),
        (nb091_alpha_dummy_150 R p)), ((nb091_alpha_dummy_123 D R),
        (nb091_alpha_dummy_124 R p)), ((nb091_alpha_dummy_106 D R),
        (nb091_alpha_dummy_108 R p)), ((nb091_alpha_dummy_105 D R),
        (nb091_alpha_dummy_107 R p)), ((nb091_alpha_dummy_103 D R),
        (nb091_alpha_dummy_104 D R p)), ((nb091_alpha_dummy_101 D R),
        (nb091_alpha_dummy_102 D R p)), ((nb091_alpha_dummy_060 D R),
        (nb091_alpha_dummy_062 D R p)), ((nb091_alpha_dummy_059 D R),
        (nb091_alpha_dummy_061 D R p)), ((nb091_alpha_dummy_063 D R),
        (nb091_alpha_dummy_064 D R p)), ((nb091_alpha_dummy_057 D R),
        (nb091_alpha_dummy_058 D R p)), ((nb091_alpha_dummy_055 D R),
        (nb091_alpha_dummy_056 D R p)), ((nb091_alpha_dummy_048 D R),
        (nb091_alpha_dummy_050 D R p)), ((nb091_alpha_dummy_047 D R),
        (nb091_alpha_dummy_049 D R p)), ((nb091_alpha_dummy_053 D R),
        (nb091_alpha_dummy_054 D R p)), ((nb091_alpha_dummy_051 D R),
        (nb091_alpha_dummy_052 D R p)), ((nb091_alpha_dummy_045 D R),
        (nb091_alpha_dummy_046 D R p)), ((nb091_alpha_dummy_042 D R),
        (nb091_alpha_dummy_044 D R p)), ((nb091_alpha_dummy_041 D R),
        (nb091_alpha_dummy_043 D R p)), ((nb091_alpha_dummy_001 D R),
        (nb091_alpha_dummy_002 D R p)), ((nb091_alpha_dummy_000 D R), p),
                                        ((nb091_alpha_dummy_003 D R),
        (nb091_alpha_dummy_004 D R p))] (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
                                    (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb091_alpha_dummy_134 D R) ≠ (nb091_alpha_dummy_141 D R) from (by
          unfold
            nb091_alpha_dummy_141;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0130
                    D R)
                  0)))) (show (nb091_alpha_dummy_137 R p) ≠ (nb091_alpha_dummy_142 R p) from (by
          unfold
            nb091_alpha_dummy_142;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0131
                    R p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_134 D R) ≠
        (nb091_alpha_dummy_139 D R) from (by
          unfold
            nb091_alpha_dummy_139;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0128
                    D R)
                  0)))) (show (nb091_alpha_dummy_137 R p) ≠ (nb091_alpha_dummy_140 R p) from (by
          unfold
            nb091_alpha_dummy_140;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0129
                    R p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb091_alpha_dummy_127
        D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb091_alpha_dummy_129 R p))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb091_alpha_dummy_135 D R) ≠
        (nb091_alpha_dummy_141 D R) from (by
          unfold
            nb091_alpha_dummy_141;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0134
                    D R)
                  0)))) (show (nb091_alpha_dummy_138 R p) ≠ (nb091_alpha_dummy_142 R p) from (by
          unfold
            nb091_alpha_dummy_142;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0135
                    R p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_135 D R) ≠
        (nb091_alpha_dummy_139 D R) from (by
          unfold
            nb091_alpha_dummy_139;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0132
                    D R)
                  0)))) (show (nb091_alpha_dummy_138 R p) ≠ (nb091_alpha_dummy_140 R p) from (by
          unfold
            nb091_alpha_dummy_140;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0133
                    R p)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb091_alpha_dummy_134 D R) ≠ (nb091_alpha_dummy_141 D R) from
        (by
          unfold
            nb091_alpha_dummy_141;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0130
                    D R)
                  0)))) (show (nb091_alpha_dummy_137 R p) ≠ (nb091_alpha_dummy_142 R p) from (by
          unfold
            nb091_alpha_dummy_142;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0131
                    R p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_134 D R) ≠
        (nb091_alpha_dummy_139 D R) from (by
          unfold
            nb091_alpha_dummy_139;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0128
                    D R)
                  0)))) (show (nb091_alpha_dummy_137 R p) ≠ (nb091_alpha_dummy_140 R p) from (by
          unfold
            nb091_alpha_dummy_140;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0129
                    R p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb091_alpha_dummy_127
        D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb091_alpha_dummy_129 R p))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb091_alpha_dummy_135 D R) ≠
        (nb091_alpha_dummy_141 D R) from (by
          unfold
            nb091_alpha_dummy_141;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0134
                    D R)
                  0)))) (show (nb091_alpha_dummy_138 R p) ≠ (nb091_alpha_dummy_142 R p) from (by
          unfold
            nb091_alpha_dummy_142;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0135
                    R p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_135 D R) ≠
        (nb091_alpha_dummy_139 D R) from (by
          unfold
            nb091_alpha_dummy_139;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0132
                    D R)
                  0)))) (show (nb091_alpha_dummy_138 R p) ≠ (nb091_alpha_dummy_140 R p) from (by
          unfold
            nb091_alpha_dummy_140;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0133
                    R p)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
                                        [((nb091_alpha_dummy_135 D R),
        (nb091_alpha_dummy_138 R p)), ((nb091_alpha_dummy_134 D R),
        (nb091_alpha_dummy_137 R p)), ((nb091_alpha_dummy_133 D R),
        (nb091_alpha_dummy_136 R p)), ((nb091_alpha_dummy_131 D R),
        (nb091_alpha_dummy_132 R p)), ((nb091_alpha_dummy_127 D R),
        (nb091_alpha_dummy_129 R p)), ((nb091_alpha_dummy_128 D R),
        (nb091_alpha_dummy_130 R p)), ((nb091_alpha_dummy_153 D R),
        (nb091_alpha_dummy_154 R p)), ((nb091_alpha_dummy_151 D R),
        (nb091_alpha_dummy_152 R p)), ((nb091_alpha_dummy_120 D R),
        (nb091_alpha_dummy_122 R p)), ((nb091_alpha_dummy_119 D R),
        (nb091_alpha_dummy_121 R p)), ((nb091_alpha_dummy_149 D R),
        (nb091_alpha_dummy_150 R p)), ((nb091_alpha_dummy_123 D R),
        (nb091_alpha_dummy_124 R p)), ((nb091_alpha_dummy_106 D R),
        (nb091_alpha_dummy_108 R p)), ((nb091_alpha_dummy_105 D R),
        (nb091_alpha_dummy_107 R p)), ((nb091_alpha_dummy_103 D R),
        (nb091_alpha_dummy_104 D R p)), ((nb091_alpha_dummy_101 D R),
        (nb091_alpha_dummy_102 D R p)), ((nb091_alpha_dummy_060 D R),
        (nb091_alpha_dummy_062 D R p)), ((nb091_alpha_dummy_059 D R),
        (nb091_alpha_dummy_061 D R p)), ((nb091_alpha_dummy_063 D R),
        (nb091_alpha_dummy_064 D R p)), ((nb091_alpha_dummy_057 D R),
        (nb091_alpha_dummy_058 D R p)), ((nb091_alpha_dummy_055 D R),
        (nb091_alpha_dummy_056 D R p)), ((nb091_alpha_dummy_048 D R),
        (nb091_alpha_dummy_050 D R p)), ((nb091_alpha_dummy_047 D R),
        (nb091_alpha_dummy_049 D R p)), ((nb091_alpha_dummy_053 D R),
        (nb091_alpha_dummy_054 D R p)), ((nb091_alpha_dummy_051 D R),
        (nb091_alpha_dummy_052 D R p)), ((nb091_alpha_dummy_045 D R),
        (nb091_alpha_dummy_046 D R p)), ((nb091_alpha_dummy_042 D R),
        (nb091_alpha_dummy_044 D R p)), ((nb091_alpha_dummy_041 D R),
        (nb091_alpha_dummy_043 D R p)), ((nb091_alpha_dummy_001 D R),
        (nb091_alpha_dummy_002 D R p)), ((nb091_alpha_dummy_000 D R), p),
        ((nb091_alpha_dummy_003 D R), (nb091_alpha_dummy_004 D R p))]
                                        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
                                      (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb091_alpha_dummy_127 D R))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb091_alpha_dummy_129 R p))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb091_alpha_dummy_127 D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb091_alpha_dummy_129 R p))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb091_alpha_dummy_134 D R) ≠ (nb091_alpha_dummy_145 D R) from (by
          unfold
            nb091_alpha_dummy_145;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0138
                    D R)
                  0)))) (show (nb091_alpha_dummy_137 R p) ≠ (nb091_alpha_dummy_146 R p) from (by
          unfold
            nb091_alpha_dummy_146;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0139
                    R p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_134 D R) ≠
        (nb091_alpha_dummy_143 D R) from (by
          unfold
            nb091_alpha_dummy_143;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0136
                    D R)
                  0)))) (show (nb091_alpha_dummy_137 R p) ≠ (nb091_alpha_dummy_144 R p) from (by
          unfold
            nb091_alpha_dummy_144;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0137
                    R p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb091_alpha_dummy_127
        D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb091_alpha_dummy_129 R p))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb091_alpha_dummy_134 D R) ≠
        (nb091_alpha_dummy_145 D R) from (by
          unfold
            nb091_alpha_dummy_145;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0138
                    D R)
                  0)))) (show (nb091_alpha_dummy_137 R p) ≠ (nb091_alpha_dummy_146 R p) from (by
          unfold
            nb091_alpha_dummy_146;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0139
                    R p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_134 D R) ≠
        (nb091_alpha_dummy_143 D R) from (by
          unfold
            nb091_alpha_dummy_143;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0136
                    D R)
                  0)))) (show (nb091_alpha_dummy_137 R p) ≠ (nb091_alpha_dummy_144 R p) from (by
          unfold
            nb091_alpha_dummy_144;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0137
                    R p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb091_alpha_dummy_127
        D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb091_alpha_dummy_129 R p))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb091_alpha_dummy_135 D R) ≠ (nb091_alpha_dummy_147 D R) from (by
          unfold
            nb091_alpha_dummy_147;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0142
                    D R)
                  0)))) (show (nb091_alpha_dummy_138 R p) ≠ (nb091_alpha_dummy_148 R p) from (by
          unfold
            nb091_alpha_dummy_148;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0143
                    R p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_135 D R) ≠
        (nb091_alpha_dummy_143 D R) from (by
          unfold
            nb091_alpha_dummy_143;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0140
                    D R)
                  0)))) (show (nb091_alpha_dummy_138 R p) ≠ (nb091_alpha_dummy_144 R p) from (by
          unfold
            nb091_alpha_dummy_144;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0141
                    R p)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb091_alpha_dummy_135 D R) ≠ (nb091_alpha_dummy_147 D R) from (by
          unfold
            nb091_alpha_dummy_147;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0142
                    D R)
                  0)))) (show (nb091_alpha_dummy_138 R p) ≠ (nb091_alpha_dummy_148 R p) from (by
          unfold
            nb091_alpha_dummy_148;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0143
                    R p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_135 D R) ≠
        (nb091_alpha_dummy_143 D R) from (by
          unfold
            nb091_alpha_dummy_143;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0140
                    D R)
                  0)))) (show (nb091_alpha_dummy_138 R p) ≠ (nb091_alpha_dummy_144 R p) from (by
          unfold
            nb091_alpha_dummy_144;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0141
                    R p)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb091_alpha_dummy_127 D R) ≠ (nb091_alpha_dummy_131 D R) from (by
                                unfold nb091_alpha_dummy_131;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb091_support_mem_0124 D R) 0)))) (show
                              (nb091_alpha_dummy_129 R p) ≠ (nb091_alpha_dummy_132 R p) from (by
                                unfold nb091_alpha_dummy_132;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb091_support_mem_0125 R p) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                          [((nb091_alpha_dummy_131 D R), (nb091_alpha_dummy_132 R p)),
                            ((nb091_alpha_dummy_127 D R), (nb091_alpha_dummy_129 R p)),
                            ((nb091_alpha_dummy_128 D R), (nb091_alpha_dummy_130 R p)),
                            ((nb091_alpha_dummy_153 D R), (nb091_alpha_dummy_154 R p)),
                            ((nb091_alpha_dummy_151 D R), (nb091_alpha_dummy_152 R p)),
                            ((nb091_alpha_dummy_120 D R), (nb091_alpha_dummy_122 R p)),
                            ((nb091_alpha_dummy_119 D R), (nb091_alpha_dummy_121 R p)),
                            ((nb091_alpha_dummy_149 D R), (nb091_alpha_dummy_150 R p)),
                            ((nb091_alpha_dummy_123 D R), (nb091_alpha_dummy_124 R p)),
                            ((nb091_alpha_dummy_106 D R), (nb091_alpha_dummy_108 R p)),
                            ((nb091_alpha_dummy_105 D R), (nb091_alpha_dummy_107 R p)),
                            ((nb091_alpha_dummy_103 D R), (nb091_alpha_dummy_104 D R p)),
                            ((nb091_alpha_dummy_101 D R), (nb091_alpha_dummy_102 D R p)),
                            ((nb091_alpha_dummy_060 D R), (nb091_alpha_dummy_062 D R p)),
                            ((nb091_alpha_dummy_059 D R), (nb091_alpha_dummy_061 D R p)),
                            ((nb091_alpha_dummy_063 D R), (nb091_alpha_dummy_064 D R p)),
                            ((nb091_alpha_dummy_057 D R), (nb091_alpha_dummy_058 D R p)),
                            ((nb091_alpha_dummy_055 D R), (nb091_alpha_dummy_056 D R p)),
                            ((nb091_alpha_dummy_048 D R), (nb091_alpha_dummy_050 D R p)),
                            ((nb091_alpha_dummy_047 D R), (nb091_alpha_dummy_049 D R p)),
                            ((nb091_alpha_dummy_053 D R), (nb091_alpha_dummy_054 D R p)),
                            ((nb091_alpha_dummy_051 D R), (nb091_alpha_dummy_052 D R p)),
                            ((nb091_alpha_dummy_045 D R), (nb091_alpha_dummy_046 D R p)),
                            ((nb091_alpha_dummy_042 D R), (nb091_alpha_dummy_044 D R p)),
                            ((nb091_alpha_dummy_041 D R), (nb091_alpha_dummy_043 D R p)),
                            ((nb091_alpha_dummy_001 D R), (nb091_alpha_dummy_002 D R p)),
                            ((nb091_alpha_dummy_000 D R), p),
                            ((nb091_alpha_dummy_003 D R), (nb091_alpha_dummy_004 D R p))]
                          (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb091_alpha_dummy_127 D R) ≠ (nb091_alpha_dummy_131 D R) from
                            (by
                              unfold nb091_alpha_dummy_131;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb091_support_mem_0124 D R) 0))))
                          (show (nb091_alpha_dummy_129 R p) ≠ (nb091_alpha_dummy_132 R p) from
                            (by
                              unfold nb091_alpha_dummy_132;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb091_support_mem_0125 R p) 0))))
                          (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb091_alpha_dummy_127 D R) ≠ (nb091_alpha_dummy_131 D R) from (by
                                unfold nb091_alpha_dummy_131;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb091_support_mem_0124 D R) 0)))) (show
                              (nb091_alpha_dummy_129 R p) ≠ (nb091_alpha_dummy_132 R p) from (by
                                unfold nb091_alpha_dummy_132;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb091_support_mem_0125 R p) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                          [((nb091_alpha_dummy_131 D R), (nb091_alpha_dummy_132 R p)),
                            ((nb091_alpha_dummy_127 D R), (nb091_alpha_dummy_129 R p)),
                            ((nb091_alpha_dummy_128 D R), (nb091_alpha_dummy_130 R p)),
                            ((nb091_alpha_dummy_153 D R), (nb091_alpha_dummy_154 R p)),
                            ((nb091_alpha_dummy_151 D R), (nb091_alpha_dummy_152 R p)),
                            ((nb091_alpha_dummy_120 D R), (nb091_alpha_dummy_122 R p)),
                            ((nb091_alpha_dummy_119 D R), (nb091_alpha_dummy_121 R p)),
                            ((nb091_alpha_dummy_149 D R), (nb091_alpha_dummy_150 R p)),
                            ((nb091_alpha_dummy_123 D R), (nb091_alpha_dummy_124 R p)),
                            ((nb091_alpha_dummy_106 D R), (nb091_alpha_dummy_108 R p)),
                            ((nb091_alpha_dummy_105 D R), (nb091_alpha_dummy_107 R p)),
                            ((nb091_alpha_dummy_103 D R), (nb091_alpha_dummy_104 D R p)),
                            ((nb091_alpha_dummy_101 D R), (nb091_alpha_dummy_102 D R p)),
                            ((nb091_alpha_dummy_060 D R), (nb091_alpha_dummy_062 D R p)),
                            ((nb091_alpha_dummy_059 D R), (nb091_alpha_dummy_061 D R p)),
                            ((nb091_alpha_dummy_063 D R), (nb091_alpha_dummy_064 D R p)),
                            ((nb091_alpha_dummy_057 D R), (nb091_alpha_dummy_058 D R p)),
                            ((nb091_alpha_dummy_055 D R), (nb091_alpha_dummy_056 D R p)),
                            ((nb091_alpha_dummy_048 D R), (nb091_alpha_dummy_050 D R p)),
                            ((nb091_alpha_dummy_047 D R), (nb091_alpha_dummy_049 D R p)),
                            ((nb091_alpha_dummy_053 D R), (nb091_alpha_dummy_054 D R p)),
                            ((nb091_alpha_dummy_051 D R), (nb091_alpha_dummy_052 D R p)),
                            ((nb091_alpha_dummy_045 D R), (nb091_alpha_dummy_046 D R p)),
                            ((nb091_alpha_dummy_042 D R), (nb091_alpha_dummy_044 D R p)),
                            ((nb091_alpha_dummy_041 D R), (nb091_alpha_dummy_043 D R p)),
                            ((nb091_alpha_dummy_001 D R), (nb091_alpha_dummy_002 D R p)),
                            ((nb091_alpha_dummy_000 D R), p),
                            ((nb091_alpha_dummy_003 D R), (nb091_alpha_dummy_004 D R p))]
                          (syn_cnnc) (by simp only [fv_syn_cnnc])))))))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cv (TAlphaVar.there
                    (show (nb091_alpha_dummy_120 D R) ≠ (nb091_alpha_dummy_127 D R) from (by
                        unfold nb091_alpha_dummy_127;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb091_support_mem_0122 D R) 0))))
                    (show (nb091_alpha_dummy_122 R p) ≠ (nb091_alpha_dummy_129 R p) from (by
                        unfold nb091_alpha_dummy_129;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb091_support_mem_0123 R p) 0))))
                    (TAlphaVar.there
                      (show (nb091_alpha_dummy_120 D R) ≠ (nb091_alpha_dummy_128 D R) from (by
                          unfold nb091_alpha_dummy_128;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb091_support_mem_0122 D R) 1))))
                      (show (nb091_alpha_dummy_122 R p) ≠ (nb091_alpha_dummy_130 R p) from (by
                          unfold nb091_alpha_dummy_130;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb091_support_mem_0123 R p) 1))))
                      (TAlphaVar.there
                        (show (nb091_alpha_dummy_120 D R) ≠ (nb091_alpha_dummy_153 D R) from (by
                            unfold nb091_alpha_dummy_153;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb091_support_mem_0152 D R) 0))))
                        (show (nb091_alpha_dummy_122 R p) ≠ (nb091_alpha_dummy_154 R p) from (by
                            unfold nb091_alpha_dummy_154;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb091_support_mem_0153 R p) 0))))
                        (TAlphaVar.there
                          (show (nb091_alpha_dummy_120 D R) ≠ (nb091_alpha_dummy_151 D R) from
                            (by
                              unfold nb091_alpha_dummy_151;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb091_support_mem_0150 D R) 0))))
                          (show (nb091_alpha_dummy_122 R p) ≠ (nb091_alpha_dummy_152 R p) from
                            (by
                              unfold nb091_alpha_dummy_152;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb091_support_mem_0151 R p) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there
                    (freshVar_injective (((Class.cv (nb091_alpha_dummy_120 D R))).fv)
                      (by decide))
                    (freshVar_injective (((Class.cv (nb091_alpha_dummy_122 R p))).fv)
                      (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                    (TAlphaWff.neg (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (show (nb091_alpha_dummy_127 D R) ≠
        (nb091_alpha_dummy_134 D R) from (by
                                          unfold nb091_alpha_dummy_134;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb091_support_mem_0126 D R) 1)))) (show
                                        (nb091_alpha_dummy_129 R p) ≠
        (nb091_alpha_dummy_137 R p) from (by
                                          unfold nb091_alpha_dummy_137;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb091_support_mem_0127 R p) 1))))
                                      (TAlphaVar.there (show (nb091_alpha_dummy_127 D R) ≠
        (nb091_alpha_dummy_133 D R) from (by
          unfold nb091_alpha_dummy_133;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0126 D R) 0)))) (show (nb091_alpha_dummy_129 R p) ≠
        (nb091_alpha_dummy_136 R p) from (by
          unfold nb091_alpha_dummy_136;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0127 R p) 0)))) (TAlphaVar.there (show
        (nb091_alpha_dummy_127 D R) ≠ (nb091_alpha_dummy_131 D R) from (by
          unfold nb091_alpha_dummy_131;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0124 D R) 0)))) (show (nb091_alpha_dummy_129 R p) ≠
        (nb091_alpha_dummy_132 R p) from (by
          unfold nb091_alpha_dummy_132;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0125 R p) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.refl_of_closed [((nb091_alpha_dummy_135 D R),
        (nb091_alpha_dummy_138 R p)), ((nb091_alpha_dummy_134 D R),
        (nb091_alpha_dummy_137 R p)), ((nb091_alpha_dummy_133 D R),
        (nb091_alpha_dummy_136 R p)), ((nb091_alpha_dummy_131 D R),
        (nb091_alpha_dummy_132 R p)), ((nb091_alpha_dummy_127 D R),
        (nb091_alpha_dummy_129 R p)), ((nb091_alpha_dummy_128 D R),
        (nb091_alpha_dummy_130 R p)), ((nb091_alpha_dummy_153 D R),
        (nb091_alpha_dummy_154 R p)), ((nb091_alpha_dummy_151 D R),
        (nb091_alpha_dummy_152 R p)), ((nb091_alpha_dummy_120 D R),
        (nb091_alpha_dummy_122 R p)), ((nb091_alpha_dummy_119 D R),
        (nb091_alpha_dummy_121 R p)), ((nb091_alpha_dummy_149 D R),
        (nb091_alpha_dummy_150 R p)), ((nb091_alpha_dummy_123 D R),
        (nb091_alpha_dummy_124 R p)), ((nb091_alpha_dummy_106 D R),
        (nb091_alpha_dummy_108 R p)), ((nb091_alpha_dummy_105 D R),
        (nb091_alpha_dummy_107 R p)), ((nb091_alpha_dummy_103 D R),
        (nb091_alpha_dummy_104 D R p)), ((nb091_alpha_dummy_101 D R),
        (nb091_alpha_dummy_102 D R p)), ((nb091_alpha_dummy_060 D R),
        (nb091_alpha_dummy_062 D R p)), ((nb091_alpha_dummy_059 D R),
        (nb091_alpha_dummy_061 D R p)), ((nb091_alpha_dummy_063 D R),
        (nb091_alpha_dummy_064 D R p)), ((nb091_alpha_dummy_057 D R),
        (nb091_alpha_dummy_058 D R p)), ((nb091_alpha_dummy_055 D R),
        (nb091_alpha_dummy_056 D R p)), ((nb091_alpha_dummy_048 D R),
        (nb091_alpha_dummy_050 D R p)), ((nb091_alpha_dummy_047 D R),
        (nb091_alpha_dummy_049 D R p)), ((nb091_alpha_dummy_053 D R),
        (nb091_alpha_dummy_054 D R p)), ((nb091_alpha_dummy_051 D R),
        (nb091_alpha_dummy_052 D R p)), ((nb091_alpha_dummy_045 D R),
        (nb091_alpha_dummy_046 D R p)), ((nb091_alpha_dummy_042 D R),
        (nb091_alpha_dummy_044 D R p)), ((nb091_alpha_dummy_041 D R),
        (nb091_alpha_dummy_043 D R p)), ((nb091_alpha_dummy_001 D R),
        (nb091_alpha_dummy_002 D R p)), ((nb091_alpha_dummy_000 D R), p),
        ((nb091_alpha_dummy_003 D R), (nb091_alpha_dummy_004 D R p))]
                                        (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
                                      (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb091_alpha_dummy_134 D
        R) ≠ (nb091_alpha_dummy_141 D R) from (by
          unfold
            nb091_alpha_dummy_141;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0130
                    D R)
                  0)))) (show (nb091_alpha_dummy_137 R p) ≠ (nb091_alpha_dummy_142 R p) from (by
          unfold
            nb091_alpha_dummy_142;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0131
                    R p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_134 D R) ≠
        (nb091_alpha_dummy_139 D R) from (by
          unfold
            nb091_alpha_dummy_139;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0128
                    D R)
                  0)))) (show (nb091_alpha_dummy_137 R p) ≠ (nb091_alpha_dummy_140 R p) from (by
          unfold
            nb091_alpha_dummy_140;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0129
                    R p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb091_alpha_dummy_127
        D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb091_alpha_dummy_129 R p))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb091_alpha_dummy_135 D R) ≠ (nb091_alpha_dummy_141 D R) from
        (by
          unfold
            nb091_alpha_dummy_141;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0134
                    D R)
                  0)))) (show (nb091_alpha_dummy_138 R p) ≠ (nb091_alpha_dummy_142 R p) from (by
          unfold
            nb091_alpha_dummy_142;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0135
                    R p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_135 D R) ≠
        (nb091_alpha_dummy_139 D R) from (by
          unfold
            nb091_alpha_dummy_139;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0132
                    D R)
                  0)))) (show (nb091_alpha_dummy_138 R p) ≠ (nb091_alpha_dummy_140 R p) from (by
          unfold
            nb091_alpha_dummy_140;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0133
                    R p)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb091_alpha_dummy_134 D R) ≠ (nb091_alpha_dummy_141 D R) from
        (by
          unfold
            nb091_alpha_dummy_141;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0130
                    D R)
                  0)))) (show (nb091_alpha_dummy_137 R p) ≠ (nb091_alpha_dummy_142 R p) from (by
          unfold
            nb091_alpha_dummy_142;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0131
                    R p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_134 D R) ≠
        (nb091_alpha_dummy_139 D R) from (by
          unfold
            nb091_alpha_dummy_139;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0128
                    D R)
                  0)))) (show (nb091_alpha_dummy_137 R p) ≠ (nb091_alpha_dummy_140 R p) from (by
          unfold
            nb091_alpha_dummy_140;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0129
                    R p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb091_alpha_dummy_127
        D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb091_alpha_dummy_129 R p))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb091_alpha_dummy_135 D R) ≠ (nb091_alpha_dummy_141 D R) from
        (by
          unfold
            nb091_alpha_dummy_141;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0134
                    D R)
                  0)))) (show (nb091_alpha_dummy_138 R p) ≠ (nb091_alpha_dummy_142 R p) from (by
          unfold
            nb091_alpha_dummy_142;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0135
                    R p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_135 D R) ≠
        (nb091_alpha_dummy_139 D R) from (by
          unfold
            nb091_alpha_dummy_139;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0132
                    D R)
                  0)))) (show (nb091_alpha_dummy_138 R p) ≠ (nb091_alpha_dummy_140 R p) from (by
          unfold
            nb091_alpha_dummy_140;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0133
                    R p)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb091_alpha_dummy_135 D R), (nb091_alpha_dummy_138 R p)),
        ((nb091_alpha_dummy_134 D R), (nb091_alpha_dummy_137 R p)),
        ((nb091_alpha_dummy_133 D R), (nb091_alpha_dummy_136 R p)),
        ((nb091_alpha_dummy_131 D R), (nb091_alpha_dummy_132 R p)),
        ((nb091_alpha_dummy_127 D R), (nb091_alpha_dummy_129 R p)),
        ((nb091_alpha_dummy_128 D R), (nb091_alpha_dummy_130 R p)),
        ((nb091_alpha_dummy_153 D R), (nb091_alpha_dummy_154 R p)),
        ((nb091_alpha_dummy_151 D R), (nb091_alpha_dummy_152 R p)),
        ((nb091_alpha_dummy_120 D R), (nb091_alpha_dummy_122 R p)),
        ((nb091_alpha_dummy_119 D R), (nb091_alpha_dummy_121 R p)),
        ((nb091_alpha_dummy_149 D R), (nb091_alpha_dummy_150 R p)),
        ((nb091_alpha_dummy_123 D R), (nb091_alpha_dummy_124 R p)),
        ((nb091_alpha_dummy_106 D R), (nb091_alpha_dummy_108 R p)),
        ((nb091_alpha_dummy_105 D R), (nb091_alpha_dummy_107 R p)),
        ((nb091_alpha_dummy_103 D R), (nb091_alpha_dummy_104 D R p)),
        ((nb091_alpha_dummy_101 D R), (nb091_alpha_dummy_102 D R p)),
        ((nb091_alpha_dummy_060 D R), (nb091_alpha_dummy_062 D R p)),
        ((nb091_alpha_dummy_059 D R), (nb091_alpha_dummy_061 D R p)),
        ((nb091_alpha_dummy_063 D R), (nb091_alpha_dummy_064 D R p)),
        ((nb091_alpha_dummy_057 D R), (nb091_alpha_dummy_058 D R p)),
        ((nb091_alpha_dummy_055 D R), (nb091_alpha_dummy_056 D R p)),
        ((nb091_alpha_dummy_048 D R), (nb091_alpha_dummy_050 D R p)),
        ((nb091_alpha_dummy_047 D R), (nb091_alpha_dummy_049 D R p)),
        ((nb091_alpha_dummy_053 D R), (nb091_alpha_dummy_054 D R p)),
        ((nb091_alpha_dummy_051 D R), (nb091_alpha_dummy_052 D R p)),
        ((nb091_alpha_dummy_045 D R), (nb091_alpha_dummy_046 D R p)),
        ((nb091_alpha_dummy_042 D R), (nb091_alpha_dummy_044 D R p)),
        ((nb091_alpha_dummy_041 D R), (nb091_alpha_dummy_043 D R p)),
        ((nb091_alpha_dummy_001 D R), (nb091_alpha_dummy_002 D R p)),
        ((nb091_alpha_dummy_000 D R), p), ((nb091_alpha_dummy_003 D R),
        (nb091_alpha_dummy_004 D R p))] (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
                                        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb091_alpha_dummy_127 D R))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb091_alpha_dummy_129 R p))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb091_alpha_dummy_127 D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb091_alpha_dummy_129 R p))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb091_alpha_dummy_134 D
        R) ≠ (nb091_alpha_dummy_145 D R) from (by
          unfold
            nb091_alpha_dummy_145;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0138
                    D R)
                  0)))) (show (nb091_alpha_dummy_137 R p) ≠ (nb091_alpha_dummy_146 R p) from (by
          unfold
            nb091_alpha_dummy_146;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0139
                    R p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_134 D R) ≠
        (nb091_alpha_dummy_143 D R) from (by
          unfold
            nb091_alpha_dummy_143;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0136
                    D R)
                  0)))) (show (nb091_alpha_dummy_137 R p) ≠ (nb091_alpha_dummy_144 R p) from (by
          unfold
            nb091_alpha_dummy_144;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0137
                    R p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb091_alpha_dummy_127
        D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb091_alpha_dummy_129 R p))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb091_alpha_dummy_134 D R) ≠ (nb091_alpha_dummy_145 D R) from
        (by
          unfold
            nb091_alpha_dummy_145;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0138
                    D R)
                  0)))) (show (nb091_alpha_dummy_137 R p) ≠ (nb091_alpha_dummy_146 R p) from (by
          unfold
            nb091_alpha_dummy_146;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0139
                    R p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_134 D R) ≠
        (nb091_alpha_dummy_143 D R) from (by
          unfold
            nb091_alpha_dummy_143;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0136
                    D R)
                  0)))) (show (nb091_alpha_dummy_137 R p) ≠ (nb091_alpha_dummy_144 R p) from (by
          unfold
            nb091_alpha_dummy_144;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0137
                    R p)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb091_alpha_dummy_127
        D R))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb091_alpha_dummy_129 R p))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _
        _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb091_alpha_dummy_135 D
        R) ≠ (nb091_alpha_dummy_147 D R) from (by
          unfold
            nb091_alpha_dummy_147;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0142
                    D R)
                  0)))) (show (nb091_alpha_dummy_138 R p) ≠ (nb091_alpha_dummy_148 R p) from (by
          unfold
            nb091_alpha_dummy_148;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0143
                    R p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_135 D R) ≠
        (nb091_alpha_dummy_143 D R) from (by
          unfold
            nb091_alpha_dummy_143;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0140
                    D R)
                  0)))) (show (nb091_alpha_dummy_138 R p) ≠ (nb091_alpha_dummy_144 R p) from (by
          unfold
            nb091_alpha_dummy_144;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0141
                    R p)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb091_alpha_dummy_135 D
        R) ≠ (nb091_alpha_dummy_147 D R) from (by
          unfold
            nb091_alpha_dummy_147;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0142
                    D R)
                  0)))) (show (nb091_alpha_dummy_138 R p) ≠ (nb091_alpha_dummy_148 R p) from (by
          unfold
            nb091_alpha_dummy_148;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0143
                    R p)
                  0)))) (TAlphaVar.there (show (nb091_alpha_dummy_135 D R) ≠
        (nb091_alpha_dummy_143 D R) from (by
          unfold
            nb091_alpha_dummy_143;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0140
                    D R)
                  0)))) (show (nb091_alpha_dummy_138 R p) ≠ (nb091_alpha_dummy_144 R p) from (by
          unfold
            nb091_alpha_dummy_144;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb091_support_mem_0141
                    R p)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there (show
                                (nb091_alpha_dummy_127 D R) ≠ (nb091_alpha_dummy_131 D R) from
                                (by
                                  unfold nb091_alpha_dummy_131;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb091_support_mem_0124 D R)
                                          0)))) (show
                                (nb091_alpha_dummy_129 R p) ≠ (nb091_alpha_dummy_132 R p) from
                                (by
                                  unfold nb091_alpha_dummy_132;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb091_support_mem_0125 R p)
                                          0)))) (TAlphaVar.here _ _ _)))
                          (TAlphaClass.refl_of_closed
                            [((nb091_alpha_dummy_131 D R), (nb091_alpha_dummy_132 R p)),
                              ((nb091_alpha_dummy_127 D R), (nb091_alpha_dummy_129 R p)),
                              ((nb091_alpha_dummy_128 D R), (nb091_alpha_dummy_130 R p)),
                              ((nb091_alpha_dummy_153 D R), (nb091_alpha_dummy_154 R p)),
                              ((nb091_alpha_dummy_151 D R), (nb091_alpha_dummy_152 R p)),
                              ((nb091_alpha_dummy_120 D R), (nb091_alpha_dummy_122 R p)),
                              ((nb091_alpha_dummy_119 D R), (nb091_alpha_dummy_121 R p)),
                              ((nb091_alpha_dummy_149 D R), (nb091_alpha_dummy_150 R p)),
                              ((nb091_alpha_dummy_123 D R), (nb091_alpha_dummy_124 R p)),
                              ((nb091_alpha_dummy_106 D R), (nb091_alpha_dummy_108 R p)),
                              ((nb091_alpha_dummy_105 D R), (nb091_alpha_dummy_107 R p)),
                              ((nb091_alpha_dummy_103 D R), (nb091_alpha_dummy_104 D R p)),
                              ((nb091_alpha_dummy_101 D R), (nb091_alpha_dummy_102 D R p)),
                              ((nb091_alpha_dummy_060 D R), (nb091_alpha_dummy_062 D R p)),
                              ((nb091_alpha_dummy_059 D R), (nb091_alpha_dummy_061 D R p)),
                              ((nb091_alpha_dummy_063 D R), (nb091_alpha_dummy_064 D R p)),
                              ((nb091_alpha_dummy_057 D R), (nb091_alpha_dummy_058 D R p)),
                              ((nb091_alpha_dummy_055 D R), (nb091_alpha_dummy_056 D R p)),
                              ((nb091_alpha_dummy_048 D R), (nb091_alpha_dummy_050 D R p)),
                              ((nb091_alpha_dummy_047 D R), (nb091_alpha_dummy_049 D R p)),
                              ((nb091_alpha_dummy_053 D R), (nb091_alpha_dummy_054 D R p)),
                              ((nb091_alpha_dummy_051 D R), (nb091_alpha_dummy_052 D R p)),
                              ((nb091_alpha_dummy_045 D R), (nb091_alpha_dummy_046 D R p)),
                              ((nb091_alpha_dummy_042 D R), (nb091_alpha_dummy_044 D R p)),
                              ((nb091_alpha_dummy_041 D R), (nb091_alpha_dummy_043 D R p)),
                              ((nb091_alpha_dummy_001 D R), (nb091_alpha_dummy_002 D R p)),
                              ((nb091_alpha_dummy_000 D R), p), ((nb091_alpha_dummy_003 D R),
                                (nb091_alpha_dummy_004 D R p))]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there (show
                              (nb091_alpha_dummy_127 D R) ≠ (nb091_alpha_dummy_131 D R) from (by
                                unfold nb091_alpha_dummy_131;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb091_support_mem_0124 D R) 0)))) (show
                              (nb091_alpha_dummy_129 R p) ≠ (nb091_alpha_dummy_132 R p) from (by
                                unfold nb091_alpha_dummy_132;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb091_support_mem_0125 R p) 0))))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there (show
                                (nb091_alpha_dummy_127 D R) ≠ (nb091_alpha_dummy_131 D R) from
                                (by
                                  unfold nb091_alpha_dummy_131;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb091_support_mem_0124 D R)
                                          0)))) (show
                                (nb091_alpha_dummy_129 R p) ≠ (nb091_alpha_dummy_132 R p) from
                                (by
                                  unfold nb091_alpha_dummy_132;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb091_support_mem_0125 R p)
                                          0)))) (TAlphaVar.here _ _ _)))
                          (TAlphaClass.refl_of_closed
                            [((nb091_alpha_dummy_131 D R), (nb091_alpha_dummy_132 R p)),
                              ((nb091_alpha_dummy_127 D R), (nb091_alpha_dummy_129 R p)),
                              ((nb091_alpha_dummy_128 D R), (nb091_alpha_dummy_130 R p)),
                              ((nb091_alpha_dummy_153 D R), (nb091_alpha_dummy_154 R p)),
                              ((nb091_alpha_dummy_151 D R), (nb091_alpha_dummy_152 R p)),
                              ((nb091_alpha_dummy_120 D R), (nb091_alpha_dummy_122 R p)),
                              ((nb091_alpha_dummy_119 D R), (nb091_alpha_dummy_121 R p)),
                              ((nb091_alpha_dummy_149 D R), (nb091_alpha_dummy_150 R p)),
                              ((nb091_alpha_dummy_123 D R), (nb091_alpha_dummy_124 R p)),
                              ((nb091_alpha_dummy_106 D R), (nb091_alpha_dummy_108 R p)),
                              ((nb091_alpha_dummy_105 D R), (nb091_alpha_dummy_107 R p)),
                              ((nb091_alpha_dummy_103 D R), (nb091_alpha_dummy_104 D R p)),
                              ((nb091_alpha_dummy_101 D R), (nb091_alpha_dummy_102 D R p)),
                              ((nb091_alpha_dummy_060 D R), (nb091_alpha_dummy_062 D R p)),
                              ((nb091_alpha_dummy_059 D R), (nb091_alpha_dummy_061 D R p)),
                              ((nb091_alpha_dummy_063 D R), (nb091_alpha_dummy_064 D R p)),
                              ((nb091_alpha_dummy_057 D R), (nb091_alpha_dummy_058 D R p)),
                              ((nb091_alpha_dummy_055 D R), (nb091_alpha_dummy_056 D R p)),
                              ((nb091_alpha_dummy_048 D R), (nb091_alpha_dummy_050 D R p)),
                              ((nb091_alpha_dummy_047 D R), (nb091_alpha_dummy_049 D R p)),
                              ((nb091_alpha_dummy_053 D R), (nb091_alpha_dummy_054 D R p)),
                              ((nb091_alpha_dummy_051 D R), (nb091_alpha_dummy_052 D R p)),
                              ((nb091_alpha_dummy_045 D R), (nb091_alpha_dummy_046 D R p)),
                              ((nb091_alpha_dummy_042 D R), (nb091_alpha_dummy_044 D R p)),
                              ((nb091_alpha_dummy_041 D R), (nb091_alpha_dummy_043 D R p)),
                              ((nb091_alpha_dummy_001 D R), (nb091_alpha_dummy_002 D R p)),
                              ((nb091_alpha_dummy_000 D R), p), ((nb091_alpha_dummy_003 D R),
                                (nb091_alpha_dummy_004 D R p))]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))

theorem nb091_focused_notmem_0056 (D : Class) (R : Class) :
    (nb091_alpha_dummy_106 D R) ∉ R.fv :=
  by
  change
    freshVar
        (((syn_ccnv (syn_cdif R (syn_cid)))).fv ∪
          ((syn_csn (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))).fv)
        1 ∉
      R.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_ccnv (syn_cdif R (syn_cid))]
  rw [fv_syn_cdif R (syn_cid)]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb091_wpp_notmem_0404 (D : Class) (R : Class) :
    (nb091_alpha_dummy_106 D R) ∉ ((syn_ccnv (syn_cdif R (syn_cid)))).fv := by
  simpa only [nb091_alpha_dummy_106, fv_syn_ccnv, fv_syn_cdif, Finset.mem_union,
    fv_syn_cid, not_or] using
    (And.intro (nb091_focused_notmem_0056 D R) (nb091_compact_fv_empty_0102 D R))

theorem nb091_focused_notmem_0057 (R : Class) (p : Var) :
    (nb091_alpha_dummy_108 R p) ∉ R.fv :=
  by
  change
    freshVar
        (((syn_ccnv (syn_cdif R (syn_cid)))).fv ∪
          ((syn_csn (syn_cuni (syn_cuni (Class.cv p))))).fv)
        1 ∉
      R.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_ccnv (syn_cdif R (syn_cid))]
  rw [fv_syn_cdif R (syn_cid)]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb091_wpp_notmem_0405 (R : Class) (p : Var) :
    (nb091_alpha_dummy_108 R p) ∉ ((syn_ccnv (syn_cdif R (syn_cid)))).fv := by
  simpa only [nb091_alpha_dummy_108, fv_syn_ccnv, fv_syn_cdif, Finset.mem_union,
    fv_syn_cid, not_or] using
    (And.intro (nb091_focused_notmem_0057 R p) (nb091_compact_fv_empty_0103 R p))

theorem nb091_focused_notmem_0058 (D : Class) (R : Class) :
    (nb091_alpha_dummy_105 D R) ∉ R.fv :=
  by
  change
    freshVar
        (((syn_ccnv (syn_cdif R (syn_cid)))).fv ∪
          ((syn_csn (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))).fv)
        0 ∉
      R.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_ccnv (syn_cdif R (syn_cid))]
  rw [fv_syn_cdif R (syn_cid)]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb091_wpp_notmem_0406 (D : Class) (R : Class) :
    (nb091_alpha_dummy_105 D R) ∉ ((syn_ccnv (syn_cdif R (syn_cid)))).fv := by
  simpa only [nb091_alpha_dummy_105, fv_syn_ccnv, fv_syn_cdif, Finset.mem_union,
    fv_syn_cid, not_or] using
    (And.intro (nb091_focused_notmem_0058 D R) (nb091_compact_fv_empty_0104 D R))

theorem nb091_focused_notmem_0059 (R : Class) (p : Var) :
    (nb091_alpha_dummy_107 R p) ∉ R.fv :=
  by
  change
    freshVar
        (((syn_ccnv (syn_cdif R (syn_cid)))).fv ∪
          ((syn_csn (syn_cuni (syn_cuni (Class.cv p))))).fv)
        0 ∉
      R.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_ccnv (syn_cdif R (syn_cid))]
  rw [fv_syn_cdif R (syn_cid)]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb091_wpp_notmem_0407 (R : Class) (p : Var) :
    (nb091_alpha_dummy_107 R p) ∉ ((syn_ccnv (syn_cdif R (syn_cid)))).fv := by
  simpa only [nb091_alpha_dummy_107, fv_syn_ccnv, fv_syn_cdif, Finset.mem_union,
    fv_syn_cid, not_or] using
    (And.intro (nb091_focused_notmem_0059 R p) (nb091_compact_fv_empty_0105 R p))

theorem nb091_focused_notmem_0060 (D : Class) (R : Class) :
    (nb091_alpha_dummy_103 D R) ∉ R.fv :=
  by
  change
    freshVar
        ((D).fv ∪ ((syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
              (syn_csn (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R))))))).fv)
        0 ∉
      R.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
      (syn_csn (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_ccnv (syn_cdif R (syn_cid))]
  rw [fv_syn_cdif R (syn_cid)]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb091_wpp_notmem_0408 (D : Class) (R : Class) :
    (nb091_alpha_dummy_103 D R) ∉ ((syn_ccnv (syn_cdif R (syn_cid)))).fv := by
  simpa only [nb091_alpha_dummy_103, fv_syn_ccnv, fv_syn_cdif, Finset.mem_union,
    fv_syn_cid, not_or] using
    (And.intro (nb091_focused_notmem_0060 D R) (nb091_compact_fv_empty_0106 D R))

theorem nb091_focused_notmem_0061 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_104 D R p) ∉ R.fv :=
  by
  change
    freshVar
        ((D).fv ∪ ((syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
              (syn_csn (syn_cuni (syn_cuni (Class.cv p)))))).fv)
        0 ∉
      R.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  right
  rw [fv_syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
      (syn_csn (syn_cuni (syn_cuni (Class.cv p))))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_ccnv (syn_cdif R (syn_cid))]
  rw [fv_syn_cdif R (syn_cid)]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb091_wpp_notmem_0409 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_104 D R p) ∉ ((syn_ccnv (syn_cdif R (syn_cid)))).fv := by
  simpa only [nb091_alpha_dummy_104, fv_syn_ccnv, fv_syn_cdif, Finset.mem_union,
    fv_syn_cid, not_or] using
    (And.intro (nb091_focused_notmem_0061 D R p) (nb091_compact_fv_empty_0107 D R p))

theorem nb091_focused_notmem_0062 (D : Class) (R : Class) :
    (nb091_alpha_dummy_101 D R) ∉ R.fv :=
  by
  change
    freshVar
        (((syn_cnin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn
                  (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))).fv ∪
          ((syn_cnin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn
                  (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))))).fv)
        0 ∉
      R.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_cnin D
      (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
        (syn_csn (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R))))))]
  rw [Finset.mem_union]
  right
  rw [fv_syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
      (syn_csn (syn_cuni (syn_cuni (Class.cv (nb091_alpha_dummy_000 D R)))))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_ccnv (syn_cdif R (syn_cid))]
  rw [fv_syn_cdif R (syn_cid)]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb091_wpp_notmem_0410 (D : Class) (R : Class) :
    (nb091_alpha_dummy_101 D R) ∉ ((syn_ccnv (syn_cdif R (syn_cid)))).fv := by
  simpa only [nb091_alpha_dummy_101, fv_syn_ccnv, fv_syn_cdif, Finset.mem_union,
    fv_syn_cid, not_or] using
    (And.intro (nb091_focused_notmem_0062 D R) (nb091_compact_fv_empty_0108 D R))

theorem nb091_focused_notmem_0063 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_102 D R p) ∉ R.fv :=
  by
  change
    freshVar
        (((syn_cnin D (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (Class.cv p))))))).fv ∪ ((syn_cnin D
              (syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
                (syn_csn (syn_cuni (syn_cuni (Class.cv p))))))).fv)
        0 ∉
      R.fv
  refine NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0 ?_
  intro supportVariable hu
  rw [Finset.mem_union]
  left
  rw [fv_syn_cnin D
      (syn_cima (syn_ccnv (syn_cdif R (syn_cid))) (syn_csn (syn_cuni (syn_cuni (Class.cv p)))))]
  rw [Finset.mem_union]
  right
  rw [fv_syn_cima (syn_ccnv (syn_cdif R (syn_cid)))
      (syn_csn (syn_cuni (syn_cuni (Class.cv p))))]
  rw [Finset.mem_union]
  left
  rw [fv_syn_ccnv (syn_cdif R (syn_cid))]
  rw [fv_syn_cdif R (syn_cid)]
  rw [Finset.mem_union]
  left
  exact hu

theorem nb091_wpp_notmem_0411 (D : Class) (R : Class) (p : Var) :
    (nb091_alpha_dummy_102 D R p) ∉ ((syn_ccnv (syn_cdif R (syn_cid)))).fv := by
  simpa only [nb091_alpha_dummy_102, fv_syn_ccnv, fv_syn_cdif, Finset.mem_union,
    fv_syn_cid, not_or] using
    (And.intro (nb091_focused_notmem_0063 D R p) (nb091_compact_fv_empty_0109 D R p))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
