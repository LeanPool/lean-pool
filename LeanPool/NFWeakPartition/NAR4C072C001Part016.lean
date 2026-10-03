/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C072C001Block004

/-! NF weak partition development: NAR4C072C001Part016. -/


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
noncomputable def nb072_split_alpha_0006 (x : Var) (y : Var) (A : Class) (B : Class)
    (R : Class) (S_cls : Class) (H : Class) (dv_H_x : x ∉ H.fv) (dv_H_y : y ∉ H.fv) :
    TAlphaWff
      [((nb072_alpha_dummy_039 A B R S_cls H), (nb072_alpha_dummy_041 x y H)),
        ((nb072_alpha_dummy_038 A B R S_cls H), (nb072_alpha_dummy_040 x y H)),
        ((nb072_alpha_dummy_114 A B R S_cls H), (nb072_alpha_dummy_115 x y H)),
        ((nb072_alpha_dummy_042 A B R S_cls H), (nb072_alpha_dummy_043 x y H)),
        ((nb072_alpha_dummy_001 A B R S_cls H), y),
        ((nb072_alpha_dummy_000 A B R S_cls H), x)]
      (Wff.imp (Wff.classMem (Class.cv (nb072_alpha_dummy_039 A B R S_cls H))
          (syn_cfv H (Class.cv (nb072_alpha_dummy_001 A B R S_cls H)))) (Wff.neg
          (Wff.classEq (Class.cv (nb072_alpha_dummy_038 A B R S_cls H))
            (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_039 A B R S_cls H)))
              (syn_csn (syn_c0c))))))
      (Wff.imp (Wff.classMem (Class.cv (nb072_alpha_dummy_041 x y H)) (syn_cfv H (Class.cv y)))
        (Wff.neg (Wff.classEq (Class.cv (nb072_alpha_dummy_040 x y H))
            (syn_cun (syn_cphi (Class.cv (nb072_alpha_dummy_041 x y H)))
              (syn_csn (syn_c0c)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.objMem (TAlphaVar.there (freshVar_injective
                  (((Class.cab (nb072_alpha_dummy_118 A B R S_cls H) (Wff.classEq
                        (Class.cab (nb072_alpha_dummy_116 A B R S_cls H)
                          (syn_wbr (Class.cv (nb072_alpha_dummy_001 A B R S_cls H)) H
                            (Class.cv (nb072_alpha_dummy_116 A B R S_cls H))))
                        (syn_csn (Class.cv (nb072_alpha_dummy_118 A B R S_cls H)))))).fv)
                  (by decide)) (freshVar_injective (((Class.cab (nb072_alpha_dummy_119 y H)
                      (Wff.classEq (Class.cab (nb072_alpha_dummy_117 y H)
                          (syn_wbr (Class.cv y) H (Class.cv (nb072_alpha_dummy_117 y H))))
                        (syn_csn (Class.cv (nb072_alpha_dummy_119 y H)))))).fv) (by decide))
                (TAlphaVar.here _ _ _)) (TAlphaVar.here _ _ _))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.classMem (TAlphaClass.cab
                        (TAlphaWff.neg (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.neg
                                    (nb072_split_alpha_0004 x y A B R S_cls H)))))
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
                                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb072_alpha_dummy_116 A B R S_cls H) ≠
        (nb072_alpha_dummy_125 A B R S_cls H) from (by
          unfold nb072_alpha_dummy_125;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0152 A B
                    R S_cls H)
                  1)))) (show (nb072_alpha_dummy_117 y H) ≠ (nb072_alpha_dummy_127 y H) from (by
          unfold nb072_alpha_dummy_127;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0154 y H)
                  1)))) (TAlphaVar.there (show (nb072_alpha_dummy_116 A B R S_cls H) ≠
        (nb072_alpha_dummy_124 A B R S_cls H) from (by
          unfold nb072_alpha_dummy_124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0152 A
                    B R S_cls H)
                  0)))) (show (nb072_alpha_dummy_117 y H) ≠ (nb072_alpha_dummy_126 y H) from (by
          unfold nb072_alpha_dummy_126;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0154 y
                    H)
                  0)))) (TAlphaVar.there (show (nb072_alpha_dummy_116 A B R S_cls H) ≠
        (nb072_alpha_dummy_154 A B R S_cls H) from (by
          unfold nb072_alpha_dummy_154;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0156
                    A B R S_cls H)
                  0)))) (show (nb072_alpha_dummy_117 y H) ≠ (nb072_alpha_dummy_155 y H) from (by
          unfold nb072_alpha_dummy_155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0157
                    y H)
                  0)))) (TAlphaVar.there (show (nb072_alpha_dummy_116 A B R S_cls H) ≠
        (nb072_alpha_dummy_128 A B R S_cls H) from (by
          unfold nb072_alpha_dummy_128;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0153
                    A B R S_cls H)
                  0)))) (show (nb072_alpha_dummy_117 y H) ≠ (nb072_alpha_dummy_129 y H) from (by
          unfold nb072_alpha_dummy_129;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0155
                    y H)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb072_alpha_dummy_001 A B R
        S_cls H))).fv ∪ ((Class.cv (nb072_alpha_dummy_116 A B R S_cls H))).fv) (by decide))
        (freshVar_injective (((Class.cv y)).fv ∪ ((Class.cv (nb072_alpha_dummy_117 y H))).fv)
        (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb072_split_alpha_0005 x y A B R S_cls H)))))
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb072_alpha_dummy_156 A B R S_cls H), (nb072_alpha_dummy_157 y H)),
        ((nb072_alpha_dummy_125 A B R S_cls H), (nb072_alpha_dummy_127 y H)),
        ((nb072_alpha_dummy_124 A B R S_cls H), (nb072_alpha_dummy_126 y H)),
        ((nb072_alpha_dummy_154 A B R S_cls H), (nb072_alpha_dummy_155 y H)),
        ((nb072_alpha_dummy_128 A B R S_cls H), (nb072_alpha_dummy_129 y H)),
        ((nb072_alpha_dummy_116 A B R S_cls H), (nb072_alpha_dummy_117 y H)),
        ((nb072_alpha_dummy_118 A B R S_cls H), (nb072_alpha_dummy_119 y H)),
        ((nb072_alpha_dummy_121 A B R S_cls H), (nb072_alpha_dummy_123 y H)),
        ((nb072_alpha_dummy_120 A B R S_cls H), (nb072_alpha_dummy_122 y H)),
        ((nb072_alpha_dummy_039 A B R S_cls H), (nb072_alpha_dummy_041 x y H)),
        ((nb072_alpha_dummy_038 A B R S_cls H), (nb072_alpha_dummy_040 x y H)),
        ((nb072_alpha_dummy_114 A B R S_cls H), (nb072_alpha_dummy_115 x y H)),
        ((nb072_alpha_dummy_042 A B R S_cls H), (nb072_alpha_dummy_043 x y H)),
        ((nb072_alpha_dummy_001 A B R S_cls H), y), ((nb072_alpha_dummy_000 A B R S_cls H), x)]
        (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c]))))))))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb072_alpha_dummy_116 A B R S_cls H) ≠
        (nb072_alpha_dummy_125 A B R S_cls H) from (by
          unfold nb072_alpha_dummy_125;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0152 A B
                    R S_cls H)
                  1)))) (show (nb072_alpha_dummy_117 y H) ≠ (nb072_alpha_dummy_127 y H) from (by
          unfold nb072_alpha_dummy_127;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0154 y H)
                  1)))) (TAlphaVar.there (show (nb072_alpha_dummy_116 A B R S_cls H) ≠
        (nb072_alpha_dummy_124 A B R S_cls H) from (by
          unfold nb072_alpha_dummy_124;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0152 A
                    B R S_cls H)
                  0)))) (show (nb072_alpha_dummy_117 y H) ≠ (nb072_alpha_dummy_126 y H) from (by
          unfold nb072_alpha_dummy_126;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0154 y
                    H)
                  0)))) (TAlphaVar.there (show (nb072_alpha_dummy_116 A B R S_cls H) ≠
        (nb072_alpha_dummy_154 A B R S_cls H) from (by
          unfold nb072_alpha_dummy_154;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0156
                    A B R S_cls H)
                  0)))) (show (nb072_alpha_dummy_117 y H) ≠ (nb072_alpha_dummy_155 y H) from (by
          unfold nb072_alpha_dummy_155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0157
                    y H)
                  0)))) (TAlphaVar.there (show (nb072_alpha_dummy_116 A B R S_cls H) ≠
        (nb072_alpha_dummy_128 A B R S_cls H) from (by
          unfold nb072_alpha_dummy_128;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0153
                    A B R S_cls H)
                  0)))) (show (nb072_alpha_dummy_117 y H) ≠ (nb072_alpha_dummy_129 y H) from (by
          unfold nb072_alpha_dummy_129;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0155
                    y H)
                  0)))) (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb072_alpha_dummy_001 A B R
        S_cls H))).fv ∪ ((Class.cv (nb072_alpha_dummy_116 A B R S_cls H))).fv) (by decide))
        (freshVar_injective (((Class.cv y)).fv ∪ ((Class.cv (nb072_alpha_dummy_117 y H))).fv)
        (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.neg (nb072_split_alpha_0005 x y A B R S_cls H)))))
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb072_alpha_dummy_156 A B R S_cls H), (nb072_alpha_dummy_157 y H)),
        ((nb072_alpha_dummy_125 A B R S_cls H), (nb072_alpha_dummy_127 y H)),
        ((nb072_alpha_dummy_124 A B R S_cls H), (nb072_alpha_dummy_126 y H)),
        ((nb072_alpha_dummy_154 A B R S_cls H), (nb072_alpha_dummy_155 y H)),
        ((nb072_alpha_dummy_128 A B R S_cls H), (nb072_alpha_dummy_129 y H)),
        ((nb072_alpha_dummy_116 A B R S_cls H), (nb072_alpha_dummy_117 y H)),
        ((nb072_alpha_dummy_118 A B R S_cls H), (nb072_alpha_dummy_119 y H)),
        ((nb072_alpha_dummy_121 A B R S_cls H), (nb072_alpha_dummy_123 y H)),
        ((nb072_alpha_dummy_120 A B R S_cls H), (nb072_alpha_dummy_122 y H)),
        ((nb072_alpha_dummy_039 A B R S_cls H), (nb072_alpha_dummy_041 x y H)),
        ((nb072_alpha_dummy_038 A B R S_cls H), (nb072_alpha_dummy_040 x y H)),
        ((nb072_alpha_dummy_114 A B R S_cls H), (nb072_alpha_dummy_115 x y H)),
        ((nb072_alpha_dummy_042 A B R S_cls H), (nb072_alpha_dummy_043 x y H)),
        ((nb072_alpha_dummy_001 A B R S_cls H), y), ((nb072_alpha_dummy_000 A B R S_cls H), x)]
        (syn_ccompl (syn_csn (syn_c0c))) (by
          simp only [fv_syn_ccompl,
            fv_syn_csn,
            fv_syn_c0c])))))))))))))))))) (TAlphaClass.refl_of_reflOn
                        [((nb072_alpha_dummy_116 A B R S_cls H), (nb072_alpha_dummy_117 y H)),
                          ((nb072_alpha_dummy_118 A B R S_cls H), (nb072_alpha_dummy_119 y H)),
                          ((nb072_alpha_dummy_121 A B R S_cls H), (nb072_alpha_dummy_123 y H)),
                          ((nb072_alpha_dummy_120 A B R S_cls H), (nb072_alpha_dummy_122 y H)),
                          ((nb072_alpha_dummy_039 A B R S_cls H),
                            (nb072_alpha_dummy_041 x y H)),
                          ((nb072_alpha_dummy_038 A B R S_cls H),
                            (nb072_alpha_dummy_040 x y H)),
                          ((nb072_alpha_dummy_114 A B R S_cls H),
                            (nb072_alpha_dummy_115 x y H)),
                          ((nb072_alpha_dummy_042 A B R S_cls H),
                            (nb072_alpha_dummy_043 x y H)),
                          ((nb072_alpha_dummy_001 A B R S_cls H), y),
                          ((nb072_alpha_dummy_000 A B R S_cls H), x)]
                        H (nb072_focused_refl_0004 x y A B R S_cls H dv_H_x dv_H_y))))
                  (TAlphaClass.cab (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _))
                      (TAlphaClass.cv (TAlphaVar.there (show
                            (nb072_alpha_dummy_118 A B R S_cls H) ≠
                              (nb072_alpha_dummy_160 A B R S_cls H) from (by
                              unfold nb072_alpha_dummy_160;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar
                                      (nb072_support_mem_0162 A B R S_cls H) 0))))
                          (show (nb072_alpha_dummy_119 y H) ≠ (nb072_alpha_dummy_161 y H) from
                            (by
                              unfold nb072_alpha_dummy_161;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb072_support_mem_0163 y H) 0))))
                          (TAlphaVar.here _ _ _)))))))))))) (TAlphaWff.neg (TAlphaWff.classEq
        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
              (((syn_cfv H (Class.cv (nb072_alpha_dummy_000 A B R S_cls H)))).fv ∪
                ((syn_cfv H (Class.cv (nb072_alpha_dummy_001 A B R S_cls H)))).fv) (by decide))
            (freshVar_injective
              (((syn_cfv H (Class.cv x))).fv ∪ ((syn_cfv H (Class.cv y))).fv) (by decide))
            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb072_alpha_dummy_039 A B R S_cls H) ≠
                                        (nb072_alpha_dummy_092 A B R S_cls H) from (by
                                        unfold nb072_alpha_dummy_092;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb072_support_mem_0090 A B R S_cls H)
                                                0)))) (show (nb072_alpha_dummy_041 x y H) ≠
                                        (nb072_alpha_dummy_094 x y H) from (by
                                        unfold nb072_alpha_dummy_094;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb072_support_mem_0091 x y H) 0))))
                                    (TAlphaVar.there (show
                                        (nb072_alpha_dummy_039 A B R S_cls H) ≠
        (nb072_alpha_dummy_093 A B R S_cls H) from (by
                                          unfold nb072_alpha_dummy_093;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb072_support_mem_0090 A B R S_cls H)
                                                  1)))) (show (nb072_alpha_dummy_041 x y H) ≠
        (nb072_alpha_dummy_095 x y H) from (by
                                          unfold nb072_alpha_dummy_095;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb072_support_mem_0091 x y H) 1))))
                                      (TAlphaVar.there (show
        (nb072_alpha_dummy_039 A B R S_cls H) ≠ (nb072_alpha_dummy_164 A B R S_cls H) from (by
          unfold nb072_alpha_dummy_164;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0166 A B R S_cls H)
                  0)))) (show (nb072_alpha_dummy_041 x y H) ≠ (nb072_alpha_dummy_165 x y H) from
        (by
          unfold nb072_alpha_dummy_165;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0167 x y H) 0)))) (TAlphaVar.there (show
        (nb072_alpha_dummy_039 A B R S_cls H) ≠ (nb072_alpha_dummy_162 A B R S_cls H) from (by
          unfold nb072_alpha_dummy_162;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0164 A B R S_cls
                    H)
                  0)))) (show (nb072_alpha_dummy_041 x y H) ≠ (nb072_alpha_dummy_163 x y H) from
        (by
          unfold nb072_alpha_dummy_163;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0165 x y H) 0)))) (TAlphaVar.here _ _ _)))))))
                              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                    (freshVar_injective (((Class.cv
        (nb072_alpha_dummy_039 A B R S_cls H))).fv) (by decide)) (freshVar_injective
                                      (((Class.cv (nb072_alpha_dummy_041 x y H))).fv)
                                      (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                                  (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                                        (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb072_alpha_dummy_092 A B R S_cls H) ≠
        (nb072_alpha_dummy_099 A B R S_cls H) from (by
          unfold nb072_alpha_dummy_099;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0094
                    A B R S_cls H)
                  1)))) (show (nb072_alpha_dummy_094 x y H) ≠ (nb072_alpha_dummy_102 x y H) from
        (by
          unfold nb072_alpha_dummy_102;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0095
                    x y H)
                  1)))) (TAlphaVar.there (show (nb072_alpha_dummy_092 A B R S_cls H) ≠
        (nb072_alpha_dummy_098 A B R S_cls H) from (by
          unfold nb072_alpha_dummy_098;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0094
                    A B R S_cls H)
                  0)))) (show (nb072_alpha_dummy_094 x y H) ≠ (nb072_alpha_dummy_101 x y H) from
        (by
          unfold nb072_alpha_dummy_101;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0095
                    x y H)
                  0)))) (TAlphaVar.there (show (nb072_alpha_dummy_092 A B R S_cls H) ≠
        (nb072_alpha_dummy_096 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_096;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0092
                    A B R S_cls H)
                  0)))) (show (nb072_alpha_dummy_094 x y H) ≠ (nb072_alpha_dummy_097 x y H) from
        (by
          unfold
            nb072_alpha_dummy_097;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0093
                    x y H)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb072_alpha_dummy_100 A B R S_cls H), (nb072_alpha_dummy_103 x y H)),
        ((nb072_alpha_dummy_099 A B R S_cls H), (nb072_alpha_dummy_102 x y H)),
        ((nb072_alpha_dummy_098 A B R S_cls H), (nb072_alpha_dummy_101 x y H)),
        ((nb072_alpha_dummy_096 A B R S_cls H), (nb072_alpha_dummy_097 x y H)),
        ((nb072_alpha_dummy_092 A B R S_cls H), (nb072_alpha_dummy_094 x y H)),
        ((nb072_alpha_dummy_093 A B R S_cls H), (nb072_alpha_dummy_095 x y H)),
        ((nb072_alpha_dummy_164 A B R S_cls H), (nb072_alpha_dummy_165 x y H)),
        ((nb072_alpha_dummy_162 A B R S_cls H), (nb072_alpha_dummy_163 x y H)),
        ((nb072_alpha_dummy_039 A B R S_cls H), (nb072_alpha_dummy_041 x y H)),
        ((nb072_alpha_dummy_038 A B R S_cls H), (nb072_alpha_dummy_040 x y H)),
        ((nb072_alpha_dummy_114 A B R S_cls H), (nb072_alpha_dummy_115 x y H)),
        ((nb072_alpha_dummy_042 A B R S_cls H), (nb072_alpha_dummy_043 x y H)),
        ((nb072_alpha_dummy_001 A B R S_cls H), y), ((nb072_alpha_dummy_000 A B R S_cls H), x)]
        (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb072_alpha_dummy_099 A B R S_cls H) ≠ (nb072_alpha_dummy_106
        A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_106;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0098
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072_alpha_dummy_102 x y H) ≠ (nb072_alpha_dummy_107 x y H) from
        (by
          unfold
            nb072_alpha_dummy_107;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0099
                    x
                    y
                    H)
                  0)))) (TAlphaVar.there (show (nb072_alpha_dummy_099 A B R S_cls H) ≠
        (nb072_alpha_dummy_104 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_104;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0096
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072_alpha_dummy_102 x y H) ≠ (nb072_alpha_dummy_105 x y H) from
        (by
          unfold
            nb072_alpha_dummy_105;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0097
                    x
                    y
                    H)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb072_alpha_dummy_092
        A B R S_cls H))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb072_alpha_dummy_094 x y H))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb072_alpha_dummy_100
        A B R S_cls H) ≠ (nb072_alpha_dummy_106 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_106;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0102
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072_alpha_dummy_103 x y H) ≠ (nb072_alpha_dummy_107 x y H) from
        (by
          unfold
            nb072_alpha_dummy_107;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0103
                    x
                    y
                    H)
                  0)))) (TAlphaVar.there (show (nb072_alpha_dummy_100 A B R S_cls H) ≠
        (nb072_alpha_dummy_104 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_104;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0100
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072_alpha_dummy_103 x y H) ≠ (nb072_alpha_dummy_105 x y H) from
        (by
          unfold
            nb072_alpha_dummy_105;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0101
                    x
                    y
                    H)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb072_alpha_dummy_099 A B R S_cls H) ≠ (nb072_alpha_dummy_106
        A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_106;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0098
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072_alpha_dummy_102 x y H) ≠ (nb072_alpha_dummy_107 x y H) from
        (by
          unfold
            nb072_alpha_dummy_107;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0099
                    x
                    y
                    H)
                  0)))) (TAlphaVar.there (show (nb072_alpha_dummy_099 A B R S_cls H) ≠
        (nb072_alpha_dummy_104 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_104;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0096
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072_alpha_dummy_102 x y H) ≠ (nb072_alpha_dummy_105 x y H) from
        (by
          unfold
            nb072_alpha_dummy_105;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0097
                    x
                    y
                    H)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb072_alpha_dummy_092
        A B R S_cls H))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb072_alpha_dummy_094 x y H))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb072_alpha_dummy_100
        A B R S_cls H) ≠ (nb072_alpha_dummy_106 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_106;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0102
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072_alpha_dummy_103 x y H) ≠ (nb072_alpha_dummy_107 x y H) from
        (by
          unfold
            nb072_alpha_dummy_107;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0103
                    x
                    y
                    H)
                  0)))) (TAlphaVar.there (show (nb072_alpha_dummy_100 A B R S_cls H) ≠
        (nb072_alpha_dummy_104 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_104;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0100
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072_alpha_dummy_103 x y H) ≠ (nb072_alpha_dummy_105 x y H) from
        (by
          unfold
            nb072_alpha_dummy_105;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0101
                    x
                    y
                    H)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb072_alpha_dummy_100 A B R S_cls H), (nb072_alpha_dummy_103 x y H)),
        ((nb072_alpha_dummy_099 A B R S_cls H), (nb072_alpha_dummy_102 x y H)),
        ((nb072_alpha_dummy_098 A B R S_cls H), (nb072_alpha_dummy_101 x y H)),
        ((nb072_alpha_dummy_096 A B R S_cls H), (nb072_alpha_dummy_097 x y H)),
        ((nb072_alpha_dummy_092 A B R S_cls H), (nb072_alpha_dummy_094 x y H)),
        ((nb072_alpha_dummy_093 A B R S_cls H), (nb072_alpha_dummy_095 x y H)),
        ((nb072_alpha_dummy_164 A B R S_cls H), (nb072_alpha_dummy_165 x y H)),
        ((nb072_alpha_dummy_162 A B R S_cls H), (nb072_alpha_dummy_163 x y H)),
        ((nb072_alpha_dummy_039 A B R S_cls H), (nb072_alpha_dummy_041 x y H)),
        ((nb072_alpha_dummy_038 A B R S_cls H), (nb072_alpha_dummy_040 x y H)),
        ((nb072_alpha_dummy_114 A B R S_cls H), (nb072_alpha_dummy_115 x y H)),
        ((nb072_alpha_dummy_042 A B R S_cls H), (nb072_alpha_dummy_043 x y H)),
        ((nb072_alpha_dummy_001 A B R S_cls H), y), ((nb072_alpha_dummy_000 A B R S_cls H), x)]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb072_alpha_dummy_092 A B R S_cls
        H))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb072_alpha_dummy_094 x y H))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb072_alpha_dummy_092 A B R S_cls H))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb072_alpha_dummy_094
        x y H))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb072_alpha_dummy_099 A B R S_cls H) ≠ (nb072_alpha_dummy_110
        A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_110;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0106
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072_alpha_dummy_102 x y H) ≠ (nb072_alpha_dummy_111 x y H) from
        (by
          unfold
            nb072_alpha_dummy_111;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0107
                    x
                    y
                    H)
                  0)))) (TAlphaVar.there (show (nb072_alpha_dummy_099 A B R S_cls H) ≠
        (nb072_alpha_dummy_108 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_108;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0104
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072_alpha_dummy_102 x y H) ≠ (nb072_alpha_dummy_109 x y H) from
        (by
          unfold
            nb072_alpha_dummy_109;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0105
                    x
                    y
                    H)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb072_alpha_dummy_092
        A B R S_cls H))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb072_alpha_dummy_094 x y H))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb072_alpha_dummy_099
        A B R S_cls H) ≠ (nb072_alpha_dummy_110 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_110;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0106
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072_alpha_dummy_102 x y H) ≠ (nb072_alpha_dummy_111 x y H) from
        (by
          unfold
            nb072_alpha_dummy_111;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0107
                    x
                    y
                    H)
                  0)))) (TAlphaVar.there (show (nb072_alpha_dummy_099 A B R S_cls H) ≠
        (nb072_alpha_dummy_108 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_108;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0104
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072_alpha_dummy_102 x y H) ≠ (nb072_alpha_dummy_109 x y H) from
        (by
          unfold
            nb072_alpha_dummy_109;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0105
                    x
                    y
                    H)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb072_alpha_dummy_092
        A B R S_cls H))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb072_alpha_dummy_094 x y H))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb072_alpha_dummy_100 A B R S_cls H) ≠ (nb072_alpha_dummy_112
        A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_112;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0110
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072_alpha_dummy_103 x y H) ≠ (nb072_alpha_dummy_113 x y H) from
        (by
          unfold
            nb072_alpha_dummy_113;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0111
                    x
                    y
                    H)
                  0)))) (TAlphaVar.there (show (nb072_alpha_dummy_100 A B R S_cls H) ≠
        (nb072_alpha_dummy_108 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_108;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0108
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072_alpha_dummy_103 x y H) ≠ (nb072_alpha_dummy_109 x y H) from
        (by
          unfold
            nb072_alpha_dummy_109;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0109
                    x
                    y
                    H)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb072_alpha_dummy_100
        A B R S_cls H) ≠ (nb072_alpha_dummy_112 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_112;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0110
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072_alpha_dummy_103 x y H) ≠ (nb072_alpha_dummy_113 x y H) from
        (by
          unfold
            nb072_alpha_dummy_113;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0111
                    x
                    y
                    H)
                  0)))) (TAlphaVar.there (show (nb072_alpha_dummy_100 A B R S_cls H) ≠
        (nb072_alpha_dummy_108 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_108;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0108
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072_alpha_dummy_103 x y H) ≠ (nb072_alpha_dummy_109 x y H) from
        (by
          unfold
            nb072_alpha_dummy_109;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0109
                    x
                    y
                    H)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb072_alpha_dummy_092 A B R S_cls H) ≠
        (nb072_alpha_dummy_096 A B R S_cls H) from (by
          unfold nb072_alpha_dummy_096;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0092 A B R
                    S_cls H)
                  0)))) (show (nb072_alpha_dummy_094 x y H) ≠ (nb072_alpha_dummy_097 x y H) from
        (by
          unfold nb072_alpha_dummy_097;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0093 x y H)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb072_alpha_dummy_096 A B R S_cls H), (nb072_alpha_dummy_097 x y H)),
        ((nb072_alpha_dummy_092 A B R S_cls H), (nb072_alpha_dummy_094 x y H)),
        ((nb072_alpha_dummy_093 A B R S_cls H), (nb072_alpha_dummy_095 x y H)),
        ((nb072_alpha_dummy_164 A B R S_cls H), (nb072_alpha_dummy_165 x y H)),
        ((nb072_alpha_dummy_162 A B R S_cls H), (nb072_alpha_dummy_163 x y H)),
        ((nb072_alpha_dummy_039 A B R S_cls H), (nb072_alpha_dummy_041 x y H)),
        ((nb072_alpha_dummy_038 A B R S_cls H), (nb072_alpha_dummy_040 x y H)),
        ((nb072_alpha_dummy_114 A B R S_cls H), (nb072_alpha_dummy_115 x y H)),
        ((nb072_alpha_dummy_042 A B R S_cls H), (nb072_alpha_dummy_043 x y H)),
        ((nb072_alpha_dummy_001 A B R S_cls H), y), ((nb072_alpha_dummy_000 A B R S_cls H), x)]
        (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb072_alpha_dummy_092 A B R S_cls H) ≠
        (nb072_alpha_dummy_096 A B R S_cls H) from (by
          unfold nb072_alpha_dummy_096;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0092 A B R
                    S_cls H)
                  0)))) (show (nb072_alpha_dummy_094 x y H) ≠ (nb072_alpha_dummy_097 x y H) from
        (by
          unfold nb072_alpha_dummy_097;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0093 x y H)
                  0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb072_alpha_dummy_092 A B R S_cls H) ≠
        (nb072_alpha_dummy_096 A B R S_cls H) from (by
          unfold nb072_alpha_dummy_096;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0092 A B R
                    S_cls H)
                  0)))) (show (nb072_alpha_dummy_094 x y H) ≠ (nb072_alpha_dummy_097 x y H) from
        (by
          unfold nb072_alpha_dummy_097;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0093 x y H)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb072_alpha_dummy_096 A B R S_cls H), (nb072_alpha_dummy_097 x y H)),
        ((nb072_alpha_dummy_092 A B R S_cls H), (nb072_alpha_dummy_094 x y H)),
        ((nb072_alpha_dummy_093 A B R S_cls H), (nb072_alpha_dummy_095 x y H)),
        ((nb072_alpha_dummy_164 A B R S_cls H), (nb072_alpha_dummy_165 x y H)),
        ((nb072_alpha_dummy_162 A B R S_cls H), (nb072_alpha_dummy_163 x y H)),
        ((nb072_alpha_dummy_039 A B R S_cls H), (nb072_alpha_dummy_041 x y H)),
        ((nb072_alpha_dummy_038 A B R S_cls H), (nb072_alpha_dummy_040 x y H)),
        ((nb072_alpha_dummy_114 A B R S_cls H), (nb072_alpha_dummy_115 x y H)),
        ((nb072_alpha_dummy_042 A B R S_cls H), (nb072_alpha_dummy_043 x y H)),
        ((nb072_alpha_dummy_001 A B R S_cls H), y), ((nb072_alpha_dummy_000 A B R S_cls H), x)]
        (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb072_alpha_dummy_039 A B R S_cls H) ≠
                                        (nb072_alpha_dummy_092 A B R S_cls H) from (by
                                        unfold nb072_alpha_dummy_092;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb072_support_mem_0090 A B R S_cls H)
                                                0)))) (show (nb072_alpha_dummy_041 x y H) ≠
                                        (nb072_alpha_dummy_094 x y H) from (by
                                        unfold nb072_alpha_dummy_094;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar
                                                (nb072_support_mem_0091 x y H) 0))))
                                    (TAlphaVar.there (show
                                        (nb072_alpha_dummy_039 A B R S_cls H) ≠
        (nb072_alpha_dummy_093 A B R S_cls H) from (by
                                          unfold nb072_alpha_dummy_093;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb072_support_mem_0090 A B R S_cls H)
                                                  1)))) (show (nb072_alpha_dummy_041 x y H) ≠
        (nb072_alpha_dummy_095 x y H) from (by
                                          unfold nb072_alpha_dummy_095;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb072_support_mem_0091 x y H) 1))))
                                      (TAlphaVar.there (show
        (nb072_alpha_dummy_039 A B R S_cls H) ≠ (nb072_alpha_dummy_164 A B R S_cls H) from (by
          unfold nb072_alpha_dummy_164;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0166 A B R S_cls H)
                  0)))) (show (nb072_alpha_dummy_041 x y H) ≠ (nb072_alpha_dummy_165 x y H) from
        (by
          unfold nb072_alpha_dummy_165;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0167 x y H) 0)))) (TAlphaVar.there (show
        (nb072_alpha_dummy_039 A B R S_cls H) ≠ (nb072_alpha_dummy_162 A B R S_cls H) from (by
          unfold nb072_alpha_dummy_162;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0164 A B R S_cls
                    H)
                  0)))) (show (nb072_alpha_dummy_041 x y H) ≠ (nb072_alpha_dummy_163 x y H) from
        (by
          unfold nb072_alpha_dummy_163;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0165 x y H) 0)))) (TAlphaVar.here _ _ _)))))))
                              (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.there
                                    (freshVar_injective (((Class.cv
        (nb072_alpha_dummy_039 A B R S_cls H))).fv) (by decide)) (freshVar_injective
                                      (((Class.cv (nb072_alpha_dummy_041 x y H))).fv)
                                      (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                                  (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                                        (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb072_alpha_dummy_092 A B R S_cls H) ≠
        (nb072_alpha_dummy_099 A B R S_cls H) from (by
          unfold nb072_alpha_dummy_099;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0094
                    A B R S_cls H)
                  1)))) (show (nb072_alpha_dummy_094 x y H) ≠ (nb072_alpha_dummy_102 x y H) from
        (by
          unfold nb072_alpha_dummy_102;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0095
                    x y H)
                  1)))) (TAlphaVar.there (show (nb072_alpha_dummy_092 A B R S_cls H) ≠
        (nb072_alpha_dummy_098 A B R S_cls H) from (by
          unfold nb072_alpha_dummy_098;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0094
                    A B R S_cls H)
                  0)))) (show (nb072_alpha_dummy_094 x y H) ≠ (nb072_alpha_dummy_101 x y H) from
        (by
          unfold nb072_alpha_dummy_101;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0095
                    x y H)
                  0)))) (TAlphaVar.there (show (nb072_alpha_dummy_092 A B R S_cls H) ≠
        (nb072_alpha_dummy_096 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_096;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0092
                    A B R S_cls H)
                  0)))) (show (nb072_alpha_dummy_094 x y H) ≠ (nb072_alpha_dummy_097 x y H) from
        (by
          unfold
            nb072_alpha_dummy_097;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0093
                    x y H)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb072_alpha_dummy_100 A B R S_cls H), (nb072_alpha_dummy_103 x y H)),
        ((nb072_alpha_dummy_099 A B R S_cls H), (nb072_alpha_dummy_102 x y H)),
        ((nb072_alpha_dummy_098 A B R S_cls H), (nb072_alpha_dummy_101 x y H)),
        ((nb072_alpha_dummy_096 A B R S_cls H), (nb072_alpha_dummy_097 x y H)),
        ((nb072_alpha_dummy_092 A B R S_cls H), (nb072_alpha_dummy_094 x y H)),
        ((nb072_alpha_dummy_093 A B R S_cls H), (nb072_alpha_dummy_095 x y H)),
        ((nb072_alpha_dummy_164 A B R S_cls H), (nb072_alpha_dummy_165 x y H)),
        ((nb072_alpha_dummy_162 A B R S_cls H), (nb072_alpha_dummy_163 x y H)),
        ((nb072_alpha_dummy_039 A B R S_cls H), (nb072_alpha_dummy_041 x y H)),
        ((nb072_alpha_dummy_038 A B R S_cls H), (nb072_alpha_dummy_040 x y H)),
        ((nb072_alpha_dummy_114 A B R S_cls H), (nb072_alpha_dummy_115 x y H)),
        ((nb072_alpha_dummy_042 A B R S_cls H), (nb072_alpha_dummy_043 x y H)),
        ((nb072_alpha_dummy_001 A B R S_cls H), y), ((nb072_alpha_dummy_000 A B R S_cls H), x)]
        (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb072_alpha_dummy_099 A B R S_cls H) ≠ (nb072_alpha_dummy_106
        A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_106;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0098
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072_alpha_dummy_102 x y H) ≠ (nb072_alpha_dummy_107 x y H) from
        (by
          unfold
            nb072_alpha_dummy_107;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0099
                    x
                    y
                    H)
                  0)))) (TAlphaVar.there (show (nb072_alpha_dummy_099 A B R S_cls H) ≠
        (nb072_alpha_dummy_104 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_104;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0096
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072_alpha_dummy_102 x y H) ≠ (nb072_alpha_dummy_105 x y H) from
        (by
          unfold
            nb072_alpha_dummy_105;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0097
                    x
                    y
                    H)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb072_alpha_dummy_092
        A B R S_cls H))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb072_alpha_dummy_094 x y H))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb072_alpha_dummy_100
        A B R S_cls H) ≠ (nb072_alpha_dummy_106 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_106;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0102
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072_alpha_dummy_103 x y H) ≠ (nb072_alpha_dummy_107 x y H) from
        (by
          unfold
            nb072_alpha_dummy_107;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0103
                    x
                    y
                    H)
                  0)))) (TAlphaVar.there (show (nb072_alpha_dummy_100 A B R S_cls H) ≠
        (nb072_alpha_dummy_104 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_104;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0100
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072_alpha_dummy_103 x y H) ≠ (nb072_alpha_dummy_105 x y H) from
        (by
          unfold
            nb072_alpha_dummy_105;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0101
                    x
                    y
                    H)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb072_alpha_dummy_099 A B R S_cls H) ≠ (nb072_alpha_dummy_106
        A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_106;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0098
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072_alpha_dummy_102 x y H) ≠ (nb072_alpha_dummy_107 x y H) from
        (by
          unfold
            nb072_alpha_dummy_107;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0099
                    x
                    y
                    H)
                  0)))) (TAlphaVar.there (show (nb072_alpha_dummy_099 A B R S_cls H) ≠
        (nb072_alpha_dummy_104 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_104;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0096
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072_alpha_dummy_102 x y H) ≠ (nb072_alpha_dummy_105 x y H) from
        (by
          unfold
            nb072_alpha_dummy_105;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0097
                    x
                    y
                    H)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb072_alpha_dummy_092
        A B R S_cls H))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb072_alpha_dummy_094 x y H))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb072_alpha_dummy_100
        A B R S_cls H) ≠ (nb072_alpha_dummy_106 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_106;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0102
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072_alpha_dummy_103 x y H) ≠ (nb072_alpha_dummy_107 x y H) from
        (by
          unfold
            nb072_alpha_dummy_107;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0103
                    x
                    y
                    H)
                  0)))) (TAlphaVar.there (show (nb072_alpha_dummy_100 A B R S_cls H) ≠
        (nb072_alpha_dummy_104 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_104;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0100
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072_alpha_dummy_103 x y H) ≠ (nb072_alpha_dummy_105 x y H) from
        (by
          unfold
            nb072_alpha_dummy_105;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0101
                    x
                    y
                    H)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb072_alpha_dummy_100 A B R S_cls H), (nb072_alpha_dummy_103 x y H)),
        ((nb072_alpha_dummy_099 A B R S_cls H), (nb072_alpha_dummy_102 x y H)),
        ((nb072_alpha_dummy_098 A B R S_cls H), (nb072_alpha_dummy_101 x y H)),
        ((nb072_alpha_dummy_096 A B R S_cls H), (nb072_alpha_dummy_097 x y H)),
        ((nb072_alpha_dummy_092 A B R S_cls H), (nb072_alpha_dummy_094 x y H)),
        ((nb072_alpha_dummy_093 A B R S_cls H), (nb072_alpha_dummy_095 x y H)),
        ((nb072_alpha_dummy_164 A B R S_cls H), (nb072_alpha_dummy_165 x y H)),
        ((nb072_alpha_dummy_162 A B R S_cls H), (nb072_alpha_dummy_163 x y H)),
        ((nb072_alpha_dummy_039 A B R S_cls H), (nb072_alpha_dummy_041 x y H)),
        ((nb072_alpha_dummy_038 A B R S_cls H), (nb072_alpha_dummy_040 x y H)),
        ((nb072_alpha_dummy_114 A B R S_cls H), (nb072_alpha_dummy_115 x y H)),
        ((nb072_alpha_dummy_042 A B R S_cls H), (nb072_alpha_dummy_043 x y H)),
        ((nb072_alpha_dummy_001 A B R S_cls H), y), ((nb072_alpha_dummy_000 A B R S_cls H), x)]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb072_alpha_dummy_092 A B R S_cls
        H))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb072_alpha_dummy_094 x y H))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb072_alpha_dummy_092 A B R S_cls H))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb072_alpha_dummy_094
        x y H))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb072_alpha_dummy_099 A B R S_cls H) ≠ (nb072_alpha_dummy_110
        A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_110;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0106
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072_alpha_dummy_102 x y H) ≠ (nb072_alpha_dummy_111 x y H) from
        (by
          unfold
            nb072_alpha_dummy_111;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0107
                    x
                    y
                    H)
                  0)))) (TAlphaVar.there (show (nb072_alpha_dummy_099 A B R S_cls H) ≠
        (nb072_alpha_dummy_108 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_108;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0104
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072_alpha_dummy_102 x y H) ≠ (nb072_alpha_dummy_109 x y H) from
        (by
          unfold
            nb072_alpha_dummy_109;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0105
                    x
                    y
                    H)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb072_alpha_dummy_092
        A B R S_cls H))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb072_alpha_dummy_094 x y H))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb072_alpha_dummy_099
        A B R S_cls H) ≠ (nb072_alpha_dummy_110 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_110;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0106
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072_alpha_dummy_102 x y H) ≠ (nb072_alpha_dummy_111 x y H) from
        (by
          unfold
            nb072_alpha_dummy_111;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0107
                    x
                    y
                    H)
                  0)))) (TAlphaVar.there (show (nb072_alpha_dummy_099 A B R S_cls H) ≠
        (nb072_alpha_dummy_108 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_108;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0104
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072_alpha_dummy_102 x y H) ≠ (nb072_alpha_dummy_109 x y H) from
        (by
          unfold
            nb072_alpha_dummy_109;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0105
                    x
                    y
                    H)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv (nb072_alpha_dummy_092
        A B R S_cls H))).fv ∪ ((syn_c1c)).fv) (by
          decide)) (freshVar_injective (((Class.cv (nb072_alpha_dummy_094 x y H))).fv ∪
        ((syn_c1c)).fv) (by
          decide)) (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb072_alpha_dummy_100 A B R S_cls H) ≠ (nb072_alpha_dummy_112
        A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_112;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0110
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072_alpha_dummy_103 x y H) ≠ (nb072_alpha_dummy_113 x y H) from
        (by
          unfold
            nb072_alpha_dummy_113;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0111
                    x
                    y
                    H)
                  0)))) (TAlphaVar.there (show (nb072_alpha_dummy_100 A B R S_cls H) ≠
        (nb072_alpha_dummy_108 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_108;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0108
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072_alpha_dummy_103 x y H) ≠ (nb072_alpha_dummy_109 x y H) from
        (by
          unfold
            nb072_alpha_dummy_109;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0109
                    x
                    y
                    H)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb072_alpha_dummy_100
        A B R S_cls H) ≠ (nb072_alpha_dummy_112 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_112;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0110
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072_alpha_dummy_103 x y H) ≠ (nb072_alpha_dummy_113 x y H) from
        (by
          unfold
            nb072_alpha_dummy_113;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0111
                    x
                    y
                    H)
                  0)))) (TAlphaVar.there (show (nb072_alpha_dummy_100 A B R S_cls H) ≠
        (nb072_alpha_dummy_108 A B R S_cls H) from (by
          unfold
            nb072_alpha_dummy_108;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0108
                    A
                    B
                    R
                    S_cls
                    H)
                  0)))) (show (nb072_alpha_dummy_103 x y H) ≠ (nb072_alpha_dummy_109 x y H) from
        (by
          unfold
            nb072_alpha_dummy_109;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0109
                    x
                    y
                    H)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb072_alpha_dummy_092 A B R S_cls H) ≠
        (nb072_alpha_dummy_096 A B R S_cls H) from (by
          unfold nb072_alpha_dummy_096;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0092 A B R
                    S_cls H)
                  0)))) (show (nb072_alpha_dummy_094 x y H) ≠ (nb072_alpha_dummy_097 x y H) from
        (by
          unfold nb072_alpha_dummy_097;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0093 x y H)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb072_alpha_dummy_096 A B R S_cls H), (nb072_alpha_dummy_097 x y H)),
        ((nb072_alpha_dummy_092 A B R S_cls H), (nb072_alpha_dummy_094 x y H)),
        ((nb072_alpha_dummy_093 A B R S_cls H), (nb072_alpha_dummy_095 x y H)),
        ((nb072_alpha_dummy_164 A B R S_cls H), (nb072_alpha_dummy_165 x y H)),
        ((nb072_alpha_dummy_162 A B R S_cls H), (nb072_alpha_dummy_163 x y H)),
        ((nb072_alpha_dummy_039 A B R S_cls H), (nb072_alpha_dummy_041 x y H)),
        ((nb072_alpha_dummy_038 A B R S_cls H), (nb072_alpha_dummy_040 x y H)),
        ((nb072_alpha_dummy_114 A B R S_cls H), (nb072_alpha_dummy_115 x y H)),
        ((nb072_alpha_dummy_042 A B R S_cls H), (nb072_alpha_dummy_043 x y H)),
        ((nb072_alpha_dummy_001 A B R S_cls H), y), ((nb072_alpha_dummy_000 A B R S_cls H), x)]
        (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb072_alpha_dummy_092 A B R S_cls H) ≠
        (nb072_alpha_dummy_096 A B R S_cls H) from (by
          unfold nb072_alpha_dummy_096;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0092 A B R
                    S_cls H)
                  0)))) (show (nb072_alpha_dummy_094 x y H) ≠ (nb072_alpha_dummy_097 x y H) from
        (by
          unfold nb072_alpha_dummy_097;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0093 x y H)
                  0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.there (show (nb072_alpha_dummy_092 A B R S_cls H) ≠
        (nb072_alpha_dummy_096 A B R S_cls H) from (by
          unfold nb072_alpha_dummy_096;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0092 A B R
                    S_cls H)
                  0)))) (show (nb072_alpha_dummy_094 x y H) ≠ (nb072_alpha_dummy_097 x y H) from
        (by
          unfold nb072_alpha_dummy_097;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb072_support_mem_0093 x y H)
                  0)))) (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
        [((nb072_alpha_dummy_096 A B R S_cls H), (nb072_alpha_dummy_097 x y H)),
        ((nb072_alpha_dummy_092 A B R S_cls H), (nb072_alpha_dummy_094 x y H)),
        ((nb072_alpha_dummy_093 A B R S_cls H), (nb072_alpha_dummy_095 x y H)),
        ((nb072_alpha_dummy_164 A B R S_cls H), (nb072_alpha_dummy_165 x y H)),
        ((nb072_alpha_dummy_162 A B R S_cls H), (nb072_alpha_dummy_163 x y H)),
        ((nb072_alpha_dummy_039 A B R S_cls H), (nb072_alpha_dummy_041 x y H)),
        ((nb072_alpha_dummy_038 A B R S_cls H), (nb072_alpha_dummy_040 x y H)),
        ((nb072_alpha_dummy_114 A B R S_cls H), (nb072_alpha_dummy_115 x y H)),
        ((nb072_alpha_dummy_042 A B R S_cls H), (nb072_alpha_dummy_043 x y H)),
        ((nb072_alpha_dummy_001 A B R S_cls H), y), ((nb072_alpha_dummy_000 A B R S_cls H), x)]
        (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.refl_of_closed
                  [((nb072_alpha_dummy_162 A B R S_cls H), (nb072_alpha_dummy_163 x y H)),
                    ((nb072_alpha_dummy_039 A B R S_cls H), (nb072_alpha_dummy_041 x y H)),
                    ((nb072_alpha_dummy_038 A B R S_cls H), (nb072_alpha_dummy_040 x y H)),
                    ((nb072_alpha_dummy_114 A B R S_cls H), (nb072_alpha_dummy_115 x y H)),
                    ((nb072_alpha_dummy_042 A B R S_cls H), (nb072_alpha_dummy_043 x y H)),
                    ((nb072_alpha_dummy_001 A B R S_cls H), y),
                    ((nb072_alpha_dummy_000 A B R S_cls H), x)] (syn_ccompl (syn_csn (syn_c0c)))
                  (by simp only [fv_syn_ccompl, fv_syn_csn, fv_syn_c0c])))))))))

theorem nb072_focused_notmem_0032 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) : (nb072_alpha_dummy_001 A B R S_cls H) ∉ S_cls.fv :=
  by
  change freshVar ((H).fv ∪ (R).fv ∪ (S_cls).fv ∪ (A).fv ∪ (B).fv) 1 ∉ S_cls.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 1
      (fun u hu =>
        Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (hu))))

theorem nb072_focused_notmem_0033 (A : Class) (B : Class) (R : Class) (S_cls : Class)
    (H : Class) : (nb072_alpha_dummy_000 A B R S_cls H) ∉ S_cls.fv :=
  by
  change freshVar ((H).fv ∪ (R).fv ∪ (S_cls).fv ∪ (A).fv ∪ (B).fv) 0 ∉ S_cls.fv
  exact
    NFChoice.DefinitionLeaves.AlphaFocusedSupport.freshVar_not_mem_of_subset 0
      (fun u hu =>
        Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (hu))))

theorem nb072_compact_envfresh_0034 (x : Var) (y : Var) (A : Class) (B : Class)
    (R : Class) (S_cls : Class) (H : Class) (dv_S_x : x ∉ S_cls.fv)
    (dv_S_y : y ∉ S_cls.fv) :
    TEnvFresh
      [((nb072_alpha_dummy_001 A B R S_cls H), y),
        ((nb072_alpha_dummy_000 A B R S_cls H), x)]
      S_cls.fv :=
  by
  exact
    (TEnvFresh.consFresh (nb072_alpha_dummy_001 A B R S_cls H) y
      (nb072_focused_notmem_0032 A B R S_cls H) dv_S_y
      (TEnvFresh.consFresh (nb072_alpha_dummy_000 A B R S_cls H) x
        (nb072_focused_notmem_0033 A B R S_cls H) dv_S_x (TEnvFresh.nil S_cls.fv)))

@[expose]
noncomputable def nb072_focused_refl_0005 (x : Var) (y : Var) (A : Class) (B : Class)
    (R : Class) (S_cls : Class) (H : Class) (dv_S_x : x ∉ S_cls.fv)
    (dv_S_y : y ∉ S_cls.fv) :
    TReflOn
      [((nb072_alpha_dummy_001 A B R S_cls H), y),
        ((nb072_alpha_dummy_000 A B R S_cls H), x)]
      S_cls.fv :=
  TEnvFresh.reflOn (nb072_compact_envfresh_0034 x y A B R S_cls H dv_S_x dv_S_y)

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
