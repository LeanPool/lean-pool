/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C078C001Block011

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C078C001Part038`. -/


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
noncomputable def nb078_split_alpha_0006 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb078_alpha_dummy_137), (nb078_alpha_dummy_138 f)),
        ((nb078_alpha_dummy_135), (nb078_alpha_dummy_136 f)),
        ((nb078_alpha_dummy_090), (nb078_alpha_dummy_092 f)),
        ((nb078_alpha_dummy_089), (nb078_alpha_dummy_091 f)),
        ((nb078_alpha_dummy_093), (nb078_alpha_dummy_094 f)),
        ((nb078_alpha_dummy_011), (nb078_alpha_dummy_014 f)),
        ((nb078_alpha_dummy_010), (nb078_alpha_dummy_013 f)),
        ((nb078_alpha_dummy_009), (nb078_alpha_dummy_012 f)),
        ((nb078_alpha_dummy_015), (nb078_alpha_dummy_016 f)),
        ((nb078_alpha_dummy_007), (nb078_alpha_dummy_008 f)),
        ((nb078_alpha_dummy_005), (nb078_alpha_dummy_006 f)),
        ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)]
      (Wff.imp (Wff.classMem (Class.cv (nb078_alpha_dummy_137))
          (Class.cab (nb078_alpha_dummy_131)
            (syn_wrex (nb078_alpha_dummy_132) (Class.cv (nb078_alpha_dummy_090))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_131))
                (syn_cphi (Class.cv (nb078_alpha_dummy_132))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078_alpha_dummy_137)) (Class.cab (nb078_alpha_dummy_131)
              (syn_wrex (nb078_alpha_dummy_132) (Class.cv (nb078_alpha_dummy_090))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_131))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_132)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb078_alpha_dummy_138 f))
          (Class.cab (nb078_alpha_dummy_133 f)
            (syn_wrex (nb078_alpha_dummy_134 f) (Class.cv (nb078_alpha_dummy_092 f))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_133 f))
                (syn_cphi (Class.cv (nb078_alpha_dummy_134 f))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078_alpha_dummy_138 f))
            (Class.cab (nb078_alpha_dummy_133 f)
              (syn_wrex (nb078_alpha_dummy_134 f) (Class.cv (nb078_alpha_dummy_092 f))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_133 f))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_134 f))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb078_alpha_dummy_090) ≠ (nb078_alpha_dummy_132) from
                    (by
                      unfold nb078_alpha_dummy_132;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0122) 1))))
                  (show (nb078_alpha_dummy_092 f) ≠ (nb078_alpha_dummy_134 f) from (by
                      unfold nb078_alpha_dummy_134;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0124 f) 1))))
                  (TAlphaVar.there (show (nb078_alpha_dummy_090) ≠ (nb078_alpha_dummy_131) from
                      (by
                        unfold nb078_alpha_dummy_131;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0122) 0))))
                    (show (nb078_alpha_dummy_092 f) ≠ (nb078_alpha_dummy_133 f) from (by
                        unfold nb078_alpha_dummy_133;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_0124 f) 0)))) (TAlphaVar.there
                      (show (nb078_alpha_dummy_090) ≠ (nb078_alpha_dummy_137) from (by
                          unfold nb078_alpha_dummy_137;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0126) 0))))
                      (show (nb078_alpha_dummy_092 f) ≠ (nb078_alpha_dummy_138 f) from (by
                          unfold nb078_alpha_dummy_138;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0127 f) 0))))
                      (TAlphaVar.there
                        (show (nb078_alpha_dummy_090) ≠ (nb078_alpha_dummy_135) from (by
                            unfold nb078_alpha_dummy_135;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0123) 0))))
                        (show (nb078_alpha_dummy_092 f) ≠ (nb078_alpha_dummy_136 f) from (by
                            unfold nb078_alpha_dummy_136;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0125 f) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_090))).fv ∪
                      ((Class.cv (nb078_alpha_dummy_089))).fv) (by decide)) (freshVar_injective
                    (((Class.cv (nb078_alpha_dummy_092 f))).fv ∪
                      ((Class.cv (nb078_alpha_dummy_091 f))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb078_alpha_dummy_132) ≠ (nb078_alpha_dummy_139) from (by
                              unfold nb078_alpha_dummy_139;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0128) 0))))
                          (show (nb078_alpha_dummy_134 f) ≠ (nb078_alpha_dummy_141 f) from (by
                              unfold nb078_alpha_dummy_141;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0129 f) 0))))
                          (TAlphaVar.there
                            (show (nb078_alpha_dummy_132) ≠ (nb078_alpha_dummy_140) from (by
                                unfold nb078_alpha_dummy_140;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0128) 1))))
                            (show (nb078_alpha_dummy_134 f) ≠ (nb078_alpha_dummy_142 f) from (by
                                unfold nb078_alpha_dummy_142;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0129 f) 1))))
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb078_alpha_dummy_132))).fv)
                            (by decide))
                          (freshVar_injective (((Class.cv (nb078_alpha_dummy_134 f))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_139) ≠ (nb078_alpha_dummy_146) from (by
          unfold nb078_alpha_dummy_146;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0132) 1)))) (show (nb078_alpha_dummy_141 f) ≠
        (nb078_alpha_dummy_149 f) from (by
          unfold nb078_alpha_dummy_149;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0133 f) 1)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_139) ≠ (nb078_alpha_dummy_145) from (by
          unfold nb078_alpha_dummy_145;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0132) 0)))) (show (nb078_alpha_dummy_141 f) ≠
        (nb078_alpha_dummy_148 f) from (by
          unfold nb078_alpha_dummy_148;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0133 f) 0)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_139) ≠ (nb078_alpha_dummy_143) from (by
          unfold nb078_alpha_dummy_143;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0130) 0)))) (show (nb078_alpha_dummy_141 f) ≠
        (nb078_alpha_dummy_144 f) from (by
          unfold nb078_alpha_dummy_144;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0131 f)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_147), (nb078_alpha_dummy_150 f)), ((nb078_alpha_dummy_146),
        (nb078_alpha_dummy_149 f)), ((nb078_alpha_dummy_145), (nb078_alpha_dummy_148 f)),
        ((nb078_alpha_dummy_143), (nb078_alpha_dummy_144 f)), ((nb078_alpha_dummy_139),
        (nb078_alpha_dummy_141 f)), ((nb078_alpha_dummy_140), (nb078_alpha_dummy_142 f)),
        ((nb078_alpha_dummy_132), (nb078_alpha_dummy_134 f)), ((nb078_alpha_dummy_131),
        (nb078_alpha_dummy_133 f)), ((nb078_alpha_dummy_137), (nb078_alpha_dummy_138 f)),
        ((nb078_alpha_dummy_135), (nb078_alpha_dummy_136 f)), ((nb078_alpha_dummy_090),
        (nb078_alpha_dummy_092 f)), ((nb078_alpha_dummy_089), (nb078_alpha_dummy_091 f)),
        ((nb078_alpha_dummy_093), (nb078_alpha_dummy_094 f)), ((nb078_alpha_dummy_011),
        (nb078_alpha_dummy_014 f)), ((nb078_alpha_dummy_010), (nb078_alpha_dummy_013 f)),
        ((nb078_alpha_dummy_009), (nb078_alpha_dummy_012 f)), ((nb078_alpha_dummy_015),
        (nb078_alpha_dummy_016 f)), ((nb078_alpha_dummy_007), (nb078_alpha_dummy_008 f)),
        ((nb078_alpha_dummy_005), (nb078_alpha_dummy_006 f)), ((nb078_alpha_dummy_000), f),
        ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)]
        (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_146) ≠ (nb078_alpha_dummy_153) from (by
          unfold
            nb078_alpha_dummy_153;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0136)
                  0)))) (show (nb078_alpha_dummy_149 f) ≠ (nb078_alpha_dummy_154 f) from (by
          unfold
            nb078_alpha_dummy_154;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0137
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_146) ≠ (nb078_alpha_dummy_151)
        from (by
          unfold
            nb078_alpha_dummy_151;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0134)
                  0)))) (show (nb078_alpha_dummy_149 f) ≠ (nb078_alpha_dummy_152 f) from (by
          unfold
            nb078_alpha_dummy_152;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0135
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_139))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_141 f))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_147) ≠ (nb078_alpha_dummy_153)
        from (by
          unfold
            nb078_alpha_dummy_153;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0140)
                  0)))) (show (nb078_alpha_dummy_150 f) ≠ (nb078_alpha_dummy_154 f) from (by
          unfold
            nb078_alpha_dummy_154;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0141
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_147) ≠ (nb078_alpha_dummy_151)
        from (by
          unfold
            nb078_alpha_dummy_151;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0138)
                  0)))) (show (nb078_alpha_dummy_150 f) ≠ (nb078_alpha_dummy_152 f) from (by
          unfold
            nb078_alpha_dummy_152;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0139
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_146) ≠ (nb078_alpha_dummy_153) from (by
          unfold
            nb078_alpha_dummy_153;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0136)
                  0)))) (show (nb078_alpha_dummy_149 f) ≠ (nb078_alpha_dummy_154 f) from (by
          unfold
            nb078_alpha_dummy_154;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0137
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_146) ≠ (nb078_alpha_dummy_151)
        from (by
          unfold
            nb078_alpha_dummy_151;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0134)
                  0)))) (show (nb078_alpha_dummy_149 f) ≠ (nb078_alpha_dummy_152 f) from (by
          unfold
            nb078_alpha_dummy_152;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0135
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_139))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_141 f))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_147) ≠ (nb078_alpha_dummy_153)
        from (by
          unfold
            nb078_alpha_dummy_153;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0140)
                  0)))) (show (nb078_alpha_dummy_150 f) ≠ (nb078_alpha_dummy_154 f) from (by
          unfold
            nb078_alpha_dummy_154;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0141
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_147) ≠ (nb078_alpha_dummy_151)
        from (by
          unfold
            nb078_alpha_dummy_151;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0138)
                  0)))) (show (nb078_alpha_dummy_150 f) ≠ (nb078_alpha_dummy_152 f) from (by
          unfold
            nb078_alpha_dummy_152;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0139
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_147), (nb078_alpha_dummy_150 f)), ((nb078_alpha_dummy_146),
        (nb078_alpha_dummy_149 f)), ((nb078_alpha_dummy_145), (nb078_alpha_dummy_148 f)),
        ((nb078_alpha_dummy_143), (nb078_alpha_dummy_144 f)), ((nb078_alpha_dummy_139),
        (nb078_alpha_dummy_141 f)), ((nb078_alpha_dummy_140), (nb078_alpha_dummy_142 f)),
        ((nb078_alpha_dummy_132), (nb078_alpha_dummy_134 f)), ((nb078_alpha_dummy_131),
        (nb078_alpha_dummy_133 f)), ((nb078_alpha_dummy_137), (nb078_alpha_dummy_138 f)),
        ((nb078_alpha_dummy_135), (nb078_alpha_dummy_136 f)), ((nb078_alpha_dummy_090),
        (nb078_alpha_dummy_092 f)), ((nb078_alpha_dummy_089), (nb078_alpha_dummy_091 f)),
        ((nb078_alpha_dummy_093), (nb078_alpha_dummy_094 f)), ((nb078_alpha_dummy_011),
        (nb078_alpha_dummy_014 f)), ((nb078_alpha_dummy_010), (nb078_alpha_dummy_013 f)),
        ((nb078_alpha_dummy_009), (nb078_alpha_dummy_012 f)), ((nb078_alpha_dummy_015),
        (nb078_alpha_dummy_016 f)), ((nb078_alpha_dummy_007), (nb078_alpha_dummy_008 f)),
        ((nb078_alpha_dummy_005), (nb078_alpha_dummy_006 f)), ((nb078_alpha_dummy_000), f),
        ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_139))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_141 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb078_alpha_dummy_139))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_141 f))).fv ∪
        ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_146) ≠
        (nb078_alpha_dummy_157) from (by
          unfold
            nb078_alpha_dummy_157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0144)
                  0)))) (show (nb078_alpha_dummy_149 f) ≠ (nb078_alpha_dummy_158 f) from (by
          unfold
            nb078_alpha_dummy_158;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0145
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_146) ≠ (nb078_alpha_dummy_155)
        from (by
          unfold
            nb078_alpha_dummy_155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0142)
                  0)))) (show (nb078_alpha_dummy_149 f) ≠ (nb078_alpha_dummy_156 f) from (by
          unfold
            nb078_alpha_dummy_156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0143
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_139))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_141 f))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_146) ≠ (nb078_alpha_dummy_157)
        from (by
          unfold
            nb078_alpha_dummy_157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0144)
                  0)))) (show (nb078_alpha_dummy_149 f) ≠ (nb078_alpha_dummy_158 f) from (by
          unfold
            nb078_alpha_dummy_158;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0145
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_146) ≠ (nb078_alpha_dummy_155)
        from (by
          unfold
            nb078_alpha_dummy_155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0142)
                  0)))) (show (nb078_alpha_dummy_149 f) ≠ (nb078_alpha_dummy_156 f) from (by
          unfold
            nb078_alpha_dummy_156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0143
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_139))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_141 f))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_147) ≠ (nb078_alpha_dummy_159) from (by
          unfold
            nb078_alpha_dummy_159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0148)
                  0)))) (show (nb078_alpha_dummy_150 f) ≠ (nb078_alpha_dummy_160 f) from (by
          unfold
            nb078_alpha_dummy_160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0149
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_147) ≠ (nb078_alpha_dummy_155)
        from (by
          unfold
            nb078_alpha_dummy_155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0146)
                  0)))) (show (nb078_alpha_dummy_150 f) ≠ (nb078_alpha_dummy_156 f) from (by
          unfold
            nb078_alpha_dummy_156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0147
                    f)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_147) ≠
        (nb078_alpha_dummy_159) from (by
          unfold
            nb078_alpha_dummy_159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0148)
                  0)))) (show (nb078_alpha_dummy_150 f) ≠ (nb078_alpha_dummy_160 f) from (by
          unfold
            nb078_alpha_dummy_160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0149
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_147) ≠ (nb078_alpha_dummy_155)
        from (by
          unfold
            nb078_alpha_dummy_155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0146)
                  0)))) (show (nb078_alpha_dummy_150 f) ≠ (nb078_alpha_dummy_156 f) from (by
          unfold
            nb078_alpha_dummy_156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0147
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078_alpha_dummy_139) ≠ (nb078_alpha_dummy_143) from (by
                                        unfold nb078_alpha_dummy_143;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0130)
                                                0)))) (show (nb078_alpha_dummy_141 f) ≠
                                        (nb078_alpha_dummy_144 f) from (by
                                        unfold nb078_alpha_dummy_144;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0131 f)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
                                  [((nb078_alpha_dummy_143), (nb078_alpha_dummy_144 f)),
                                    ((nb078_alpha_dummy_139), (nb078_alpha_dummy_141 f)),
                                    ((nb078_alpha_dummy_140), (nb078_alpha_dummy_142 f)),
                                    ((nb078_alpha_dummy_132), (nb078_alpha_dummy_134 f)),
                                    ((nb078_alpha_dummy_131), (nb078_alpha_dummy_133 f)),
                                    ((nb078_alpha_dummy_137), (nb078_alpha_dummy_138 f)),
                                    ((nb078_alpha_dummy_135), (nb078_alpha_dummy_136 f)),
                                    ((nb078_alpha_dummy_090), (nb078_alpha_dummy_092 f)),
                                    ((nb078_alpha_dummy_089), (nb078_alpha_dummy_091 f)),
                                    ((nb078_alpha_dummy_093), (nb078_alpha_dummy_094 f)),
                                    ((nb078_alpha_dummy_011), (nb078_alpha_dummy_014 f)),
                                    ((nb078_alpha_dummy_010), (nb078_alpha_dummy_013 f)),
                                    ((nb078_alpha_dummy_009), (nb078_alpha_dummy_012 f)),
                                    ((nb078_alpha_dummy_015), (nb078_alpha_dummy_016 f)),
                                    ((nb078_alpha_dummy_007), (nb078_alpha_dummy_008 f)),
                                    ((nb078_alpha_dummy_005), (nb078_alpha_dummy_006 f)),
                                    ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y),
                                    ((nb078_alpha_dummy_003), x)]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb078_alpha_dummy_139) ≠ (nb078_alpha_dummy_143) from
                                    (by
                                      unfold nb078_alpha_dummy_143;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0130)
                                              0)))) (show
                                    (nb078_alpha_dummy_141 f) ≠ (nb078_alpha_dummy_144 f) from
                                    (by
                                      unfold nb078_alpha_dummy_144;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0131 f)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078_alpha_dummy_139) ≠ (nb078_alpha_dummy_143) from (by
                                        unfold nb078_alpha_dummy_143;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0130)
                                                0)))) (show (nb078_alpha_dummy_141 f) ≠
                                        (nb078_alpha_dummy_144 f) from (by
                                        unfold nb078_alpha_dummy_144;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0131 f)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
                                  [((nb078_alpha_dummy_143), (nb078_alpha_dummy_144 f)),
                                    ((nb078_alpha_dummy_139), (nb078_alpha_dummy_141 f)),
                                    ((nb078_alpha_dummy_140), (nb078_alpha_dummy_142 f)),
                                    ((nb078_alpha_dummy_132), (nb078_alpha_dummy_134 f)),
                                    ((nb078_alpha_dummy_131), (nb078_alpha_dummy_133 f)),
                                    ((nb078_alpha_dummy_137), (nb078_alpha_dummy_138 f)),
                                    ((nb078_alpha_dummy_135), (nb078_alpha_dummy_136 f)),
                                    ((nb078_alpha_dummy_090), (nb078_alpha_dummy_092 f)),
                                    ((nb078_alpha_dummy_089), (nb078_alpha_dummy_091 f)),
                                    ((nb078_alpha_dummy_093), (nb078_alpha_dummy_094 f)),
                                    ((nb078_alpha_dummy_011), (nb078_alpha_dummy_014 f)),
                                    ((nb078_alpha_dummy_010), (nb078_alpha_dummy_013 f)),
                                    ((nb078_alpha_dummy_009), (nb078_alpha_dummy_012 f)),
                                    ((nb078_alpha_dummy_015), (nb078_alpha_dummy_016 f)),
                                    ((nb078_alpha_dummy_007), (nb078_alpha_dummy_008 f)),
                                    ((nb078_alpha_dummy_005), (nb078_alpha_dummy_006 f)),
                                    ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y),
                                    ((nb078_alpha_dummy_003), x)]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb078_alpha_dummy_090) ≠ (nb078_alpha_dummy_132) from
                      (by
                        unfold nb078_alpha_dummy_132;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0122) 1))))
                    (show (nb078_alpha_dummy_092 f) ≠ (nb078_alpha_dummy_134 f) from (by
                        unfold nb078_alpha_dummy_134;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_0124 f) 1)))) (TAlphaVar.there
                      (show (nb078_alpha_dummy_090) ≠ (nb078_alpha_dummy_131) from (by
                          unfold nb078_alpha_dummy_131;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0122) 0))))
                      (show (nb078_alpha_dummy_092 f) ≠ (nb078_alpha_dummy_133 f) from (by
                          unfold nb078_alpha_dummy_133;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0124 f) 0))))
                      (TAlphaVar.there
                        (show (nb078_alpha_dummy_090) ≠ (nb078_alpha_dummy_137) from (by
                            unfold nb078_alpha_dummy_137;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0126) 0))))
                        (show (nb078_alpha_dummy_092 f) ≠ (nb078_alpha_dummy_138 f) from (by
                            unfold nb078_alpha_dummy_138;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0127 f) 0))))
                        (TAlphaVar.there
                          (show (nb078_alpha_dummy_090) ≠ (nb078_alpha_dummy_135) from (by
                              unfold nb078_alpha_dummy_135;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0123) 0))))
                          (show (nb078_alpha_dummy_092 f) ≠ (nb078_alpha_dummy_136 f) from (by
                              unfold nb078_alpha_dummy_136;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0125 f) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb078_alpha_dummy_090))).fv ∪
                        ((Class.cv (nb078_alpha_dummy_089))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb078_alpha_dummy_092 f))).fv ∪
                        ((Class.cv (nb078_alpha_dummy_091 f))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb078_alpha_dummy_132) ≠ (nb078_alpha_dummy_139) from (by
                                unfold nb078_alpha_dummy_139;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0128) 0))))
                            (show (nb078_alpha_dummy_134 f) ≠ (nb078_alpha_dummy_141 f) from (by
                                unfold nb078_alpha_dummy_141;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0129 f) 0))))
                            (TAlphaVar.there
                              (show (nb078_alpha_dummy_132) ≠ (nb078_alpha_dummy_140) from (by
                                  unfold nb078_alpha_dummy_140;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0128) 1))))
                              (show (nb078_alpha_dummy_134 f) ≠ (nb078_alpha_dummy_142 f) from
                                (by
                                  unfold nb078_alpha_dummy_142;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0129 f) 1))))
                              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there
                            (freshVar_injective (((Class.cv (nb078_alpha_dummy_132))).fv)
                              (by decide)) (freshVar_injective
                              (((Class.cv (nb078_alpha_dummy_134 f))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078_alpha_dummy_139) ≠ (nb078_alpha_dummy_146) from (by
          unfold nb078_alpha_dummy_146;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0132) 1)))) (show (nb078_alpha_dummy_141 f) ≠
        (nb078_alpha_dummy_149 f) from (by
          unfold nb078_alpha_dummy_149;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0133 f) 1)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_139) ≠ (nb078_alpha_dummy_145) from (by
          unfold nb078_alpha_dummy_145;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0132) 0)))) (show (nb078_alpha_dummy_141 f) ≠
        (nb078_alpha_dummy_148 f) from (by
          unfold nb078_alpha_dummy_148;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0133 f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_139) ≠ (nb078_alpha_dummy_143)
        from (by
          unfold nb078_alpha_dummy_143;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0130)
                  0)))) (show (nb078_alpha_dummy_141 f) ≠ (nb078_alpha_dummy_144 f) from (by
          unfold nb078_alpha_dummy_144;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0131 f)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_147), (nb078_alpha_dummy_150 f)), ((nb078_alpha_dummy_146),
        (nb078_alpha_dummy_149 f)), ((nb078_alpha_dummy_145), (nb078_alpha_dummy_148 f)),
        ((nb078_alpha_dummy_143), (nb078_alpha_dummy_144 f)), ((nb078_alpha_dummy_139),
        (nb078_alpha_dummy_141 f)), ((nb078_alpha_dummy_140), (nb078_alpha_dummy_142 f)),
        ((nb078_alpha_dummy_132), (nb078_alpha_dummy_134 f)), ((nb078_alpha_dummy_131),
        (nb078_alpha_dummy_133 f)), ((nb078_alpha_dummy_137), (nb078_alpha_dummy_138 f)),
        ((nb078_alpha_dummy_135), (nb078_alpha_dummy_136 f)), ((nb078_alpha_dummy_090),
        (nb078_alpha_dummy_092 f)), ((nb078_alpha_dummy_089), (nb078_alpha_dummy_091 f)),
        ((nb078_alpha_dummy_093), (nb078_alpha_dummy_094 f)), ((nb078_alpha_dummy_011),
        (nb078_alpha_dummy_014 f)), ((nb078_alpha_dummy_010), (nb078_alpha_dummy_013 f)),
        ((nb078_alpha_dummy_009), (nb078_alpha_dummy_012 f)), ((nb078_alpha_dummy_015),
        (nb078_alpha_dummy_016 f)), ((nb078_alpha_dummy_007), (nb078_alpha_dummy_008 f)),
        ((nb078_alpha_dummy_005), (nb078_alpha_dummy_006 f)), ((nb078_alpha_dummy_000), f),
        ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)]
        (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_146) ≠ (nb078_alpha_dummy_153) from (by
          unfold
            nb078_alpha_dummy_153;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0136)
                  0)))) (show (nb078_alpha_dummy_149 f) ≠ (nb078_alpha_dummy_154 f) from (by
          unfold
            nb078_alpha_dummy_154;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0137
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_146) ≠ (nb078_alpha_dummy_151)
        from (by
          unfold
            nb078_alpha_dummy_151;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0134)
                  0)))) (show (nb078_alpha_dummy_149 f) ≠ (nb078_alpha_dummy_152 f) from (by
          unfold
            nb078_alpha_dummy_152;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0135
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_139))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_141 f))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_147) ≠ (nb078_alpha_dummy_153)
        from (by
          unfold
            nb078_alpha_dummy_153;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0140)
                  0)))) (show (nb078_alpha_dummy_150 f) ≠ (nb078_alpha_dummy_154 f) from (by
          unfold
            nb078_alpha_dummy_154;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0141
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_147) ≠ (nb078_alpha_dummy_151)
        from (by
          unfold
            nb078_alpha_dummy_151;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0138)
                  0)))) (show (nb078_alpha_dummy_150 f) ≠ (nb078_alpha_dummy_152 f) from (by
          unfold
            nb078_alpha_dummy_152;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0139
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_146) ≠ (nb078_alpha_dummy_153) from (by
          unfold
            nb078_alpha_dummy_153;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0136)
                  0)))) (show (nb078_alpha_dummy_149 f) ≠ (nb078_alpha_dummy_154 f) from (by
          unfold
            nb078_alpha_dummy_154;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0137
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_146) ≠ (nb078_alpha_dummy_151)
        from (by
          unfold
            nb078_alpha_dummy_151;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0134)
                  0)))) (show (nb078_alpha_dummy_149 f) ≠ (nb078_alpha_dummy_152 f) from (by
          unfold
            nb078_alpha_dummy_152;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0135
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_139))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_141 f))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_147) ≠ (nb078_alpha_dummy_153)
        from (by
          unfold
            nb078_alpha_dummy_153;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0140)
                  0)))) (show (nb078_alpha_dummy_150 f) ≠ (nb078_alpha_dummy_154 f) from (by
          unfold
            nb078_alpha_dummy_154;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0141
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_147) ≠ (nb078_alpha_dummy_151)
        from (by
          unfold
            nb078_alpha_dummy_151;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0138)
                  0)))) (show (nb078_alpha_dummy_150 f) ≠ (nb078_alpha_dummy_152 f) from (by
          unfold
            nb078_alpha_dummy_152;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0139
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_147), (nb078_alpha_dummy_150 f)), ((nb078_alpha_dummy_146),
        (nb078_alpha_dummy_149 f)), ((nb078_alpha_dummy_145), (nb078_alpha_dummy_148 f)),
        ((nb078_alpha_dummy_143), (nb078_alpha_dummy_144 f)), ((nb078_alpha_dummy_139),
        (nb078_alpha_dummy_141 f)), ((nb078_alpha_dummy_140), (nb078_alpha_dummy_142 f)),
        ((nb078_alpha_dummy_132), (nb078_alpha_dummy_134 f)), ((nb078_alpha_dummy_131),
        (nb078_alpha_dummy_133 f)), ((nb078_alpha_dummy_137), (nb078_alpha_dummy_138 f)),
        ((nb078_alpha_dummy_135), (nb078_alpha_dummy_136 f)), ((nb078_alpha_dummy_090),
        (nb078_alpha_dummy_092 f)), ((nb078_alpha_dummy_089), (nb078_alpha_dummy_091 f)),
        ((nb078_alpha_dummy_093), (nb078_alpha_dummy_094 f)), ((nb078_alpha_dummy_011),
        (nb078_alpha_dummy_014 f)), ((nb078_alpha_dummy_010), (nb078_alpha_dummy_013 f)),
        ((nb078_alpha_dummy_009), (nb078_alpha_dummy_012 f)), ((nb078_alpha_dummy_015),
        (nb078_alpha_dummy_016 f)), ((nb078_alpha_dummy_007), (nb078_alpha_dummy_008 f)),
        ((nb078_alpha_dummy_005), (nb078_alpha_dummy_006 f)), ((nb078_alpha_dummy_000), f),
        ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_139))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_141
        f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_139))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_141 f))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_146) ≠
        (nb078_alpha_dummy_157) from (by
          unfold
            nb078_alpha_dummy_157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0144)
                  0)))) (show (nb078_alpha_dummy_149 f) ≠ (nb078_alpha_dummy_158 f) from (by
          unfold
            nb078_alpha_dummy_158;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0145
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_146) ≠ (nb078_alpha_dummy_155)
        from (by
          unfold
            nb078_alpha_dummy_155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0142)
                  0)))) (show (nb078_alpha_dummy_149 f) ≠ (nb078_alpha_dummy_156 f) from (by
          unfold
            nb078_alpha_dummy_156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0143
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_139))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_141 f))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_146) ≠ (nb078_alpha_dummy_157)
        from (by
          unfold
            nb078_alpha_dummy_157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0144)
                  0)))) (show (nb078_alpha_dummy_149 f) ≠ (nb078_alpha_dummy_158 f) from (by
          unfold
            nb078_alpha_dummy_158;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0145
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_146) ≠ (nb078_alpha_dummy_155)
        from (by
          unfold
            nb078_alpha_dummy_155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0142)
                  0)))) (show (nb078_alpha_dummy_149 f) ≠ (nb078_alpha_dummy_156 f) from (by
          unfold
            nb078_alpha_dummy_156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0143
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_139))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_141 f))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_147) ≠ (nb078_alpha_dummy_159) from (by
          unfold
            nb078_alpha_dummy_159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0148)
                  0)))) (show (nb078_alpha_dummy_150 f) ≠ (nb078_alpha_dummy_160 f) from (by
          unfold
            nb078_alpha_dummy_160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0149
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_147) ≠ (nb078_alpha_dummy_155)
        from (by
          unfold
            nb078_alpha_dummy_155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0146)
                  0)))) (show (nb078_alpha_dummy_150 f) ≠ (nb078_alpha_dummy_156 f) from (by
          unfold
            nb078_alpha_dummy_156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0147
                    f)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_147) ≠
        (nb078_alpha_dummy_159) from (by
          unfold
            nb078_alpha_dummy_159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0148)
                  0)))) (show (nb078_alpha_dummy_150 f) ≠ (nb078_alpha_dummy_160 f) from (by
          unfold
            nb078_alpha_dummy_160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0149
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_147) ≠ (nb078_alpha_dummy_155)
        from (by
          unfold
            nb078_alpha_dummy_155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0146)
                  0)))) (show (nb078_alpha_dummy_150 f) ≠ (nb078_alpha_dummy_156 f) from (by
          unfold
            nb078_alpha_dummy_156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0147
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb078_alpha_dummy_139) ≠ (nb078_alpha_dummy_143) from
                                        (by
                                          unfold nb078_alpha_dummy_143;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0130)
                                                  0)))) (show (nb078_alpha_dummy_141 f) ≠
        (nb078_alpha_dummy_144 f) from (by
                                          unfold nb078_alpha_dummy_144;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0131 f) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb078_alpha_dummy_143), (nb078_alpha_dummy_144 f)),
                                      ((nb078_alpha_dummy_139), (nb078_alpha_dummy_141 f)),
                                      ((nb078_alpha_dummy_140), (nb078_alpha_dummy_142 f)),
                                      ((nb078_alpha_dummy_132), (nb078_alpha_dummy_134 f)),
                                      ((nb078_alpha_dummy_131), (nb078_alpha_dummy_133 f)),
                                      ((nb078_alpha_dummy_137), (nb078_alpha_dummy_138 f)),
                                      ((nb078_alpha_dummy_135), (nb078_alpha_dummy_136 f)),
                                      ((nb078_alpha_dummy_090), (nb078_alpha_dummy_092 f)),
                                      ((nb078_alpha_dummy_089), (nb078_alpha_dummy_091 f)),
                                      ((nb078_alpha_dummy_093), (nb078_alpha_dummy_094 f)),
                                      ((nb078_alpha_dummy_011), (nb078_alpha_dummy_014 f)),
                                      ((nb078_alpha_dummy_010), (nb078_alpha_dummy_013 f)),
                                      ((nb078_alpha_dummy_009), (nb078_alpha_dummy_012 f)),
                                      ((nb078_alpha_dummy_015), (nb078_alpha_dummy_016 f)),
                                      ((nb078_alpha_dummy_007), (nb078_alpha_dummy_008 f)),
                                      ((nb078_alpha_dummy_005), (nb078_alpha_dummy_006 f)),
                                      ((nb078_alpha_dummy_000), f),
                                      ((nb078_alpha_dummy_004), y),
                                      ((nb078_alpha_dummy_003), x)]
                                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078_alpha_dummy_139) ≠ (nb078_alpha_dummy_143) from (by
                                        unfold nb078_alpha_dummy_143;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0130)
                                                0)))) (show (nb078_alpha_dummy_141 f) ≠
                                        (nb078_alpha_dummy_144 f) from (by
                                        unfold nb078_alpha_dummy_144;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0131 f)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb078_alpha_dummy_139) ≠ (nb078_alpha_dummy_143) from
                                        (by
                                          unfold nb078_alpha_dummy_143;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0130)
                                                  0)))) (show (nb078_alpha_dummy_141 f) ≠
        (nb078_alpha_dummy_144 f) from (by
                                          unfold nb078_alpha_dummy_144;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0131 f) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb078_alpha_dummy_143), (nb078_alpha_dummy_144 f)),
                                      ((nb078_alpha_dummy_139), (nb078_alpha_dummy_141 f)),
                                      ((nb078_alpha_dummy_140), (nb078_alpha_dummy_142 f)),
                                      ((nb078_alpha_dummy_132), (nb078_alpha_dummy_134 f)),
                                      ((nb078_alpha_dummy_131), (nb078_alpha_dummy_133 f)),
                                      ((nb078_alpha_dummy_137), (nb078_alpha_dummy_138 f)),
                                      ((nb078_alpha_dummy_135), (nb078_alpha_dummy_136 f)),
                                      ((nb078_alpha_dummy_090), (nb078_alpha_dummy_092 f)),
                                      ((nb078_alpha_dummy_089), (nb078_alpha_dummy_091 f)),
                                      ((nb078_alpha_dummy_093), (nb078_alpha_dummy_094 f)),
                                      ((nb078_alpha_dummy_011), (nb078_alpha_dummy_014 f)),
                                      ((nb078_alpha_dummy_010), (nb078_alpha_dummy_013 f)),
                                      ((nb078_alpha_dummy_009), (nb078_alpha_dummy_012 f)),
                                      ((nb078_alpha_dummy_015), (nb078_alpha_dummy_016 f)),
                                      ((nb078_alpha_dummy_007), (nb078_alpha_dummy_008 f)),
                                      ((nb078_alpha_dummy_005), (nb078_alpha_dummy_006 f)),
                                      ((nb078_alpha_dummy_000), f),
                                      ((nb078_alpha_dummy_004), y),
                                      ((nb078_alpha_dummy_003), x)] (syn_cnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C078C001Part039`. -/


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
noncomputable def nb078_split_alpha_0007 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb078_alpha_dummy_165), (nb078_alpha_dummy_166 f)),
        ((nb078_alpha_dummy_163), (nb078_alpha_dummy_164 f)),
        ((nb078_alpha_dummy_132), (nb078_alpha_dummy_134 f)),
        ((nb078_alpha_dummy_131), (nb078_alpha_dummy_133 f)),
        ((nb078_alpha_dummy_161), (nb078_alpha_dummy_162 f)),
        ((nb078_alpha_dummy_135), (nb078_alpha_dummy_136 f)),
        ((nb078_alpha_dummy_090), (nb078_alpha_dummy_092 f)),
        ((nb078_alpha_dummy_089), (nb078_alpha_dummy_091 f)),
        ((nb078_alpha_dummy_093), (nb078_alpha_dummy_094 f)),
        ((nb078_alpha_dummy_011), (nb078_alpha_dummy_014 f)),
        ((nb078_alpha_dummy_010), (nb078_alpha_dummy_013 f)),
        ((nb078_alpha_dummy_009), (nb078_alpha_dummy_012 f)),
        ((nb078_alpha_dummy_015), (nb078_alpha_dummy_016 f)),
        ((nb078_alpha_dummy_007), (nb078_alpha_dummy_008 f)),
        ((nb078_alpha_dummy_005), (nb078_alpha_dummy_006 f)),
        ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)]
      (Wff.imp (Wff.classMem (Class.cv (nb078_alpha_dummy_165))
          (syn_cphi (Class.cv (nb078_alpha_dummy_132)))) (Wff.neg
          (Wff.classMem (Class.cv (nb078_alpha_dummy_165))
            (syn_cphi (Class.cv (nb078_alpha_dummy_132))))))
      (Wff.imp (Wff.classMem (Class.cv (nb078_alpha_dummy_166 f))
          (syn_cphi (Class.cv (nb078_alpha_dummy_134 f)))) (Wff.neg
          (Wff.classMem (Class.cv (nb078_alpha_dummy_166 f))
            (syn_cphi (Class.cv (nb078_alpha_dummy_134 f)))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb078_alpha_dummy_132) ≠ (nb078_alpha_dummy_139) from
                    (by
                      unfold nb078_alpha_dummy_139;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0128) 0))))
                  (show (nb078_alpha_dummy_134 f) ≠ (nb078_alpha_dummy_141 f) from (by
                      unfold nb078_alpha_dummy_141;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0129 f) 0))))
                  (TAlphaVar.there (show (nb078_alpha_dummy_132) ≠ (nb078_alpha_dummy_140) from
                      (by
                        unfold nb078_alpha_dummy_140;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0128) 1))))
                    (show (nb078_alpha_dummy_134 f) ≠ (nb078_alpha_dummy_142 f) from (by
                        unfold nb078_alpha_dummy_142;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_0129 f) 1)))) (TAlphaVar.there
                      (show (nb078_alpha_dummy_132) ≠ (nb078_alpha_dummy_165) from (by
                          unfold nb078_alpha_dummy_165;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0158) 0))))
                      (show (nb078_alpha_dummy_134 f) ≠ (nb078_alpha_dummy_166 f) from (by
                          unfold nb078_alpha_dummy_166;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0159 f) 0))))
                      (TAlphaVar.there
                        (show (nb078_alpha_dummy_132) ≠ (nb078_alpha_dummy_163) from (by
                            unfold nb078_alpha_dummy_163;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0156) 0))))
                        (show (nb078_alpha_dummy_134 f) ≠ (nb078_alpha_dummy_164 f) from (by
                            unfold nb078_alpha_dummy_164;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0157 f) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_132))).fv)
                    (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_134 f))).fv)
                    (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                  (TAlphaWff.neg (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078_alpha_dummy_139) ≠ (nb078_alpha_dummy_146) from (by
                                        unfold nb078_alpha_dummy_146;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0132)
                                                1)))) (show (nb078_alpha_dummy_141 f) ≠
                                        (nb078_alpha_dummy_149 f) from (by
                                        unfold nb078_alpha_dummy_149;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0133 f)
                                                1)))) (TAlphaVar.there (show
                                        (nb078_alpha_dummy_139) ≠ (nb078_alpha_dummy_145) from
                                        (by
                                          unfold nb078_alpha_dummy_145;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0132)
                                                  0)))) (show (nb078_alpha_dummy_141 f) ≠
        (nb078_alpha_dummy_148 f) from (by
                                          unfold nb078_alpha_dummy_148;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0133 f) 0))))
                                      (TAlphaVar.there (show (nb078_alpha_dummy_139) ≠
        (nb078_alpha_dummy_143) from (by
          unfold nb078_alpha_dummy_143;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0130) 0)))) (show (nb078_alpha_dummy_141 f) ≠
        (nb078_alpha_dummy_144 f) from (by
          unfold nb078_alpha_dummy_144;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0131 f) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                (TAlphaWff.conj (TAlphaWff.classMem
                                    (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                    (TAlphaClass.refl_of_closed [((nb078_alpha_dummy_147),
        (nb078_alpha_dummy_150 f)), ((nb078_alpha_dummy_146), (nb078_alpha_dummy_149 f)),
                                        ((nb078_alpha_dummy_145), (nb078_alpha_dummy_148 f)),
                                        ((nb078_alpha_dummy_143), (nb078_alpha_dummy_144 f)),
                                        ((nb078_alpha_dummy_139), (nb078_alpha_dummy_141 f)),
                                        ((nb078_alpha_dummy_140), (nb078_alpha_dummy_142 f)),
                                        ((nb078_alpha_dummy_165), (nb078_alpha_dummy_166 f)),
                                        ((nb078_alpha_dummy_163), (nb078_alpha_dummy_164 f)),
                                        ((nb078_alpha_dummy_132), (nb078_alpha_dummy_134 f)),
                                        ((nb078_alpha_dummy_131), (nb078_alpha_dummy_133 f)),
                                        ((nb078_alpha_dummy_161), (nb078_alpha_dummy_162 f)),
                                        ((nb078_alpha_dummy_135), (nb078_alpha_dummy_136 f)),
                                        ((nb078_alpha_dummy_090), (nb078_alpha_dummy_092 f)),
                                        ((nb078_alpha_dummy_089), (nb078_alpha_dummy_091 f)),
                                        ((nb078_alpha_dummy_093), (nb078_alpha_dummy_094 f)),
                                        ((nb078_alpha_dummy_011), (nb078_alpha_dummy_014 f)),
                                        ((nb078_alpha_dummy_010), (nb078_alpha_dummy_013 f)),
                                        ((nb078_alpha_dummy_009), (nb078_alpha_dummy_012 f)),
                                        ((nb078_alpha_dummy_015), (nb078_alpha_dummy_016 f)),
                                        ((nb078_alpha_dummy_007), (nb078_alpha_dummy_008 f)),
                                        ((nb078_alpha_dummy_005), (nb078_alpha_dummy_006 f)),
                                        ((nb078_alpha_dummy_000), f),
                                        ((nb078_alpha_dummy_004), y),
                                        ((nb078_alpha_dummy_003), x)]
                                      (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
                                    (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_146) ≠
        (nb078_alpha_dummy_153) from (by
          unfold
            nb078_alpha_dummy_153;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0136)
                  0)))) (show (nb078_alpha_dummy_149 f) ≠ (nb078_alpha_dummy_154 f) from (by
          unfold
            nb078_alpha_dummy_154;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0137
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_146) ≠ (nb078_alpha_dummy_151)
        from (by
          unfold
            nb078_alpha_dummy_151;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0134)
                  0)))) (show (nb078_alpha_dummy_149 f) ≠ (nb078_alpha_dummy_152 f) from (by
          unfold
            nb078_alpha_dummy_152;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0135
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_139))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_141 f))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_147) ≠ (nb078_alpha_dummy_153)
        from (by
          unfold
            nb078_alpha_dummy_153;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0140)
                  0)))) (show (nb078_alpha_dummy_150 f) ≠ (nb078_alpha_dummy_154 f) from (by
          unfold
            nb078_alpha_dummy_154;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0141
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_147) ≠ (nb078_alpha_dummy_151)
        from (by
          unfold
            nb078_alpha_dummy_151;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0138)
                  0)))) (show (nb078_alpha_dummy_150 f) ≠ (nb078_alpha_dummy_152 f) from (by
          unfold
            nb078_alpha_dummy_152;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0139
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_146) ≠ (nb078_alpha_dummy_153) from (by
          unfold
            nb078_alpha_dummy_153;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0136)
                  0)))) (show (nb078_alpha_dummy_149 f) ≠ (nb078_alpha_dummy_154 f) from (by
          unfold
            nb078_alpha_dummy_154;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0137
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_146) ≠ (nb078_alpha_dummy_151)
        from (by
          unfold
            nb078_alpha_dummy_151;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0134)
                  0)))) (show (nb078_alpha_dummy_149 f) ≠ (nb078_alpha_dummy_152 f) from (by
          unfold
            nb078_alpha_dummy_152;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0135
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_139))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_141 f))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_147) ≠ (nb078_alpha_dummy_153)
        from (by
          unfold
            nb078_alpha_dummy_153;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0140)
                  0)))) (show (nb078_alpha_dummy_150 f) ≠ (nb078_alpha_dummy_154 f) from (by
          unfold
            nb078_alpha_dummy_154;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0141
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_147) ≠ (nb078_alpha_dummy_151)
        from (by
          unfold
            nb078_alpha_dummy_151;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0138)
                  0)))) (show (nb078_alpha_dummy_150 f) ≠ (nb078_alpha_dummy_152 f) from (by
          unfold
            nb078_alpha_dummy_152;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0139
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
                                        [((nb078_alpha_dummy_147), (nb078_alpha_dummy_150 f)),
        ((nb078_alpha_dummy_146), (nb078_alpha_dummy_149 f)), ((nb078_alpha_dummy_145),
        (nb078_alpha_dummy_148 f)), ((nb078_alpha_dummy_143), (nb078_alpha_dummy_144 f)),
        ((nb078_alpha_dummy_139), (nb078_alpha_dummy_141 f)), ((nb078_alpha_dummy_140),
        (nb078_alpha_dummy_142 f)), ((nb078_alpha_dummy_165), (nb078_alpha_dummy_166 f)),
        ((nb078_alpha_dummy_163), (nb078_alpha_dummy_164 f)), ((nb078_alpha_dummy_132),
        (nb078_alpha_dummy_134 f)), ((nb078_alpha_dummy_131), (nb078_alpha_dummy_133 f)),
        ((nb078_alpha_dummy_161), (nb078_alpha_dummy_162 f)), ((nb078_alpha_dummy_135),
        (nb078_alpha_dummy_136 f)), ((nb078_alpha_dummy_090), (nb078_alpha_dummy_092 f)),
        ((nb078_alpha_dummy_089), (nb078_alpha_dummy_091 f)), ((nb078_alpha_dummy_093),
        (nb078_alpha_dummy_094 f)), ((nb078_alpha_dummy_011), (nb078_alpha_dummy_014 f)),
        ((nb078_alpha_dummy_010), (nb078_alpha_dummy_013 f)), ((nb078_alpha_dummy_009),
        (nb078_alpha_dummy_012 f)), ((nb078_alpha_dummy_015), (nb078_alpha_dummy_016 f)),
        ((nb078_alpha_dummy_007), (nb078_alpha_dummy_008 f)), ((nb078_alpha_dummy_005),
        (nb078_alpha_dummy_006 f)), ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
                                      (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_139))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb078_alpha_dummy_141 f))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_139))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb078_alpha_dummy_141 f))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_146) ≠
        (nb078_alpha_dummy_157) from (by
          unfold
            nb078_alpha_dummy_157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0144)
                  0)))) (show (nb078_alpha_dummy_149 f) ≠ (nb078_alpha_dummy_158 f) from (by
          unfold
            nb078_alpha_dummy_158;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0145
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_146) ≠ (nb078_alpha_dummy_155)
        from (by
          unfold
            nb078_alpha_dummy_155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0142)
                  0)))) (show (nb078_alpha_dummy_149 f) ≠ (nb078_alpha_dummy_156 f) from (by
          unfold
            nb078_alpha_dummy_156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0143
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_139))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_141 f))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_146) ≠ (nb078_alpha_dummy_157)
        from (by
          unfold
            nb078_alpha_dummy_157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0144)
                  0)))) (show (nb078_alpha_dummy_149 f) ≠ (nb078_alpha_dummy_158 f) from (by
          unfold
            nb078_alpha_dummy_158;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0145
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_146) ≠ (nb078_alpha_dummy_155)
        from (by
          unfold
            nb078_alpha_dummy_155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0142)
                  0)))) (show (nb078_alpha_dummy_149 f) ≠ (nb078_alpha_dummy_156 f) from (by
          unfold
            nb078_alpha_dummy_156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0143
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_139))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_141 f))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_147) ≠ (nb078_alpha_dummy_159) from (by
          unfold
            nb078_alpha_dummy_159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0148)
                  0)))) (show (nb078_alpha_dummy_150 f) ≠ (nb078_alpha_dummy_160 f) from (by
          unfold
            nb078_alpha_dummy_160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0149
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_147) ≠ (nb078_alpha_dummy_155)
        from (by
          unfold
            nb078_alpha_dummy_155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0146)
                  0)))) (show (nb078_alpha_dummy_150 f) ≠ (nb078_alpha_dummy_156 f) from (by
          unfold
            nb078_alpha_dummy_156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0147
                    f)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_147) ≠
        (nb078_alpha_dummy_159) from (by
          unfold
            nb078_alpha_dummy_159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0148)
                  0)))) (show (nb078_alpha_dummy_150 f) ≠ (nb078_alpha_dummy_160 f) from (by
          unfold
            nb078_alpha_dummy_160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0149
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_147) ≠ (nb078_alpha_dummy_155)
        from (by
          unfold
            nb078_alpha_dummy_155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0146)
                  0)))) (show (nb078_alpha_dummy_150 f) ≠ (nb078_alpha_dummy_156 f) from (by
          unfold
            nb078_alpha_dummy_156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0147
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb078_alpha_dummy_139) ≠ (nb078_alpha_dummy_143) from (by
                                unfold nb078_alpha_dummy_143;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0130) 0))))
                            (show (nb078_alpha_dummy_141 f) ≠ (nb078_alpha_dummy_144 f) from (by
                                unfold nb078_alpha_dummy_144;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0131 f) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                          [((nb078_alpha_dummy_143), (nb078_alpha_dummy_144 f)),
                            ((nb078_alpha_dummy_139), (nb078_alpha_dummy_141 f)),
                            ((nb078_alpha_dummy_140), (nb078_alpha_dummy_142 f)),
                            ((nb078_alpha_dummy_165), (nb078_alpha_dummy_166 f)),
                            ((nb078_alpha_dummy_163), (nb078_alpha_dummy_164 f)),
                            ((nb078_alpha_dummy_132), (nb078_alpha_dummy_134 f)),
                            ((nb078_alpha_dummy_131), (nb078_alpha_dummy_133 f)),
                            ((nb078_alpha_dummy_161), (nb078_alpha_dummy_162 f)),
                            ((nb078_alpha_dummy_135), (nb078_alpha_dummy_136 f)),
                            ((nb078_alpha_dummy_090), (nb078_alpha_dummy_092 f)),
                            ((nb078_alpha_dummy_089), (nb078_alpha_dummy_091 f)),
                            ((nb078_alpha_dummy_093), (nb078_alpha_dummy_094 f)),
                            ((nb078_alpha_dummy_011), (nb078_alpha_dummy_014 f)),
                            ((nb078_alpha_dummy_010), (nb078_alpha_dummy_013 f)),
                            ((nb078_alpha_dummy_009), (nb078_alpha_dummy_012 f)),
                            ((nb078_alpha_dummy_015), (nb078_alpha_dummy_016 f)),
                            ((nb078_alpha_dummy_007), (nb078_alpha_dummy_008 f)),
                            ((nb078_alpha_dummy_005), (nb078_alpha_dummy_006 f)),
                            ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y),
                            ((nb078_alpha_dummy_003), x)]
                          (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb078_alpha_dummy_139) ≠ (nb078_alpha_dummy_143) from (by
                              unfold nb078_alpha_dummy_143;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0130) 0))))
                          (show (nb078_alpha_dummy_141 f) ≠ (nb078_alpha_dummy_144 f) from (by
                              unfold nb078_alpha_dummy_144;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0131 f) 0))))
                          (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb078_alpha_dummy_139) ≠ (nb078_alpha_dummy_143) from (by
                                unfold nb078_alpha_dummy_143;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0130) 0))))
                            (show (nb078_alpha_dummy_141 f) ≠ (nb078_alpha_dummy_144 f) from (by
                                unfold nb078_alpha_dummy_144;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0131 f) 0))))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                          [((nb078_alpha_dummy_143), (nb078_alpha_dummy_144 f)),
                            ((nb078_alpha_dummy_139), (nb078_alpha_dummy_141 f)),
                            ((nb078_alpha_dummy_140), (nb078_alpha_dummy_142 f)),
                            ((nb078_alpha_dummy_165), (nb078_alpha_dummy_166 f)),
                            ((nb078_alpha_dummy_163), (nb078_alpha_dummy_164 f)),
                            ((nb078_alpha_dummy_132), (nb078_alpha_dummy_134 f)),
                            ((nb078_alpha_dummy_131), (nb078_alpha_dummy_133 f)),
                            ((nb078_alpha_dummy_161), (nb078_alpha_dummy_162 f)),
                            ((nb078_alpha_dummy_135), (nb078_alpha_dummy_136 f)),
                            ((nb078_alpha_dummy_090), (nb078_alpha_dummy_092 f)),
                            ((nb078_alpha_dummy_089), (nb078_alpha_dummy_091 f)),
                            ((nb078_alpha_dummy_093), (nb078_alpha_dummy_094 f)),
                            ((nb078_alpha_dummy_011), (nb078_alpha_dummy_014 f)),
                            ((nb078_alpha_dummy_010), (nb078_alpha_dummy_013 f)),
                            ((nb078_alpha_dummy_009), (nb078_alpha_dummy_012 f)),
                            ((nb078_alpha_dummy_015), (nb078_alpha_dummy_016 f)),
                            ((nb078_alpha_dummy_007), (nb078_alpha_dummy_008 f)),
                            ((nb078_alpha_dummy_005), (nb078_alpha_dummy_006 f)),
                            ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y),
                            ((nb078_alpha_dummy_003), x)]
                          (syn_cnnc) (by simp only [fv_syn_cnnc])))))))))))) (TAlphaWff.neg
      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.ex
            (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                (TAlphaClass.cv (TAlphaVar.there
                    (show (nb078_alpha_dummy_132) ≠ (nb078_alpha_dummy_139) from (by
                        unfold nb078_alpha_dummy_139;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0128) 0))))
                    (show (nb078_alpha_dummy_134 f) ≠ (nb078_alpha_dummy_141 f) from (by
                        unfold nb078_alpha_dummy_141;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_0129 f) 0)))) (TAlphaVar.there
                      (show (nb078_alpha_dummy_132) ≠ (nb078_alpha_dummy_140) from (by
                          unfold nb078_alpha_dummy_140;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0128) 1))))
                      (show (nb078_alpha_dummy_134 f) ≠ (nb078_alpha_dummy_142 f) from (by
                          unfold nb078_alpha_dummy_142;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0129 f) 1))))
                      (TAlphaVar.there
                        (show (nb078_alpha_dummy_132) ≠ (nb078_alpha_dummy_165) from (by
                            unfold nb078_alpha_dummy_165;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0158) 0))))
                        (show (nb078_alpha_dummy_134 f) ≠ (nb078_alpha_dummy_166 f) from (by
                            unfold nb078_alpha_dummy_166;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0159 f) 0))))
                        (TAlphaVar.there
                          (show (nb078_alpha_dummy_132) ≠ (nb078_alpha_dummy_163) from (by
                              unfold nb078_alpha_dummy_163;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0156) 0))))
                          (show (nb078_alpha_dummy_134 f) ≠ (nb078_alpha_dummy_164 f) from (by
                              unfold nb078_alpha_dummy_164;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0157 f) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_132))).fv)
                      (by decide))
                    (freshVar_injective (((Class.cv (nb078_alpha_dummy_134 f))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp (TAlphaWff.neg
                      (TAlphaWff.conj
                        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                          (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                                    (TAlphaVar.there (show
                                        (nb078_alpha_dummy_139) ≠ (nb078_alpha_dummy_146) from
                                        (by
                                          unfold nb078_alpha_dummy_146;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0132)
                                                  1)))) (show (nb078_alpha_dummy_141 f) ≠
        (nb078_alpha_dummy_149 f) from (by
                                          unfold nb078_alpha_dummy_149;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0133 f) 1))))
                                      (TAlphaVar.there (show (nb078_alpha_dummy_139) ≠
        (nb078_alpha_dummy_145) from (by
          unfold nb078_alpha_dummy_145;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0132) 0)))) (show (nb078_alpha_dummy_141 f) ≠
        (nb078_alpha_dummy_148 f) from (by
          unfold nb078_alpha_dummy_148;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0133 f) 0)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_139) ≠ (nb078_alpha_dummy_143) from (by
          unfold nb078_alpha_dummy_143;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0130) 0)))) (show (nb078_alpha_dummy_141 f) ≠
        (nb078_alpha_dummy_144 f) from (by
          unfold nb078_alpha_dummy_144;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0131 f) 0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex
                                  (TAlphaWff.conj (TAlphaWff.classMem
                                      (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                      (TAlphaClass.refl_of_closed [((nb078_alpha_dummy_147),
        (nb078_alpha_dummy_150 f)), ((nb078_alpha_dummy_146), (nb078_alpha_dummy_149 f)),
        ((nb078_alpha_dummy_145), (nb078_alpha_dummy_148 f)), ((nb078_alpha_dummy_143),
        (nb078_alpha_dummy_144 f)), ((nb078_alpha_dummy_139), (nb078_alpha_dummy_141 f)),
        ((nb078_alpha_dummy_140), (nb078_alpha_dummy_142 f)), ((nb078_alpha_dummy_165),
        (nb078_alpha_dummy_166 f)), ((nb078_alpha_dummy_163), (nb078_alpha_dummy_164 f)),
        ((nb078_alpha_dummy_132), (nb078_alpha_dummy_134 f)), ((nb078_alpha_dummy_131),
        (nb078_alpha_dummy_133 f)), ((nb078_alpha_dummy_161), (nb078_alpha_dummy_162 f)),
        ((nb078_alpha_dummy_135), (nb078_alpha_dummy_136 f)), ((nb078_alpha_dummy_090),
        (nb078_alpha_dummy_092 f)), ((nb078_alpha_dummy_089), (nb078_alpha_dummy_091 f)),
        ((nb078_alpha_dummy_093), (nb078_alpha_dummy_094 f)), ((nb078_alpha_dummy_011),
        (nb078_alpha_dummy_014 f)), ((nb078_alpha_dummy_010), (nb078_alpha_dummy_013 f)),
        ((nb078_alpha_dummy_009), (nb078_alpha_dummy_012 f)), ((nb078_alpha_dummy_015),
        (nb078_alpha_dummy_016 f)), ((nb078_alpha_dummy_007), (nb078_alpha_dummy_008 f)),
        ((nb078_alpha_dummy_005), (nb078_alpha_dummy_006 f)), ((nb078_alpha_dummy_000), f),
        ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)]
                                        (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj
                                      (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_146) ≠
        (nb078_alpha_dummy_153) from (by
          unfold
            nb078_alpha_dummy_153;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0136)
                  0)))) (show (nb078_alpha_dummy_149 f) ≠ (nb078_alpha_dummy_154 f) from (by
          unfold
            nb078_alpha_dummy_154;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0137
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_146) ≠ (nb078_alpha_dummy_151)
        from (by
          unfold
            nb078_alpha_dummy_151;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0134)
                  0)))) (show (nb078_alpha_dummy_149 f) ≠ (nb078_alpha_dummy_152 f) from (by
          unfold
            nb078_alpha_dummy_152;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0135
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_139))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_141 f))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_147) ≠ (nb078_alpha_dummy_153)
        from (by
          unfold
            nb078_alpha_dummy_153;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0140)
                  0)))) (show (nb078_alpha_dummy_150 f) ≠ (nb078_alpha_dummy_154 f) from (by
          unfold
            nb078_alpha_dummy_154;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0141
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_147) ≠ (nb078_alpha_dummy_151)
        from (by
          unfold
            nb078_alpha_dummy_151;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0138)
                  0)))) (show (nb078_alpha_dummy_150 f) ≠ (nb078_alpha_dummy_152 f) from (by
          unfold
            nb078_alpha_dummy_152;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0139
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_146) ≠ (nb078_alpha_dummy_153) from (by
          unfold
            nb078_alpha_dummy_153;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0136)
                  0)))) (show (nb078_alpha_dummy_149 f) ≠ (nb078_alpha_dummy_154 f) from (by
          unfold
            nb078_alpha_dummy_154;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0137
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_146) ≠ (nb078_alpha_dummy_151)
        from (by
          unfold
            nb078_alpha_dummy_151;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0134)
                  0)))) (show (nb078_alpha_dummy_149 f) ≠ (nb078_alpha_dummy_152 f) from (by
          unfold
            nb078_alpha_dummy_152;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0135
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_139))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_141 f))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_147) ≠ (nb078_alpha_dummy_153)
        from (by
          unfold
            nb078_alpha_dummy_153;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0140)
                  0)))) (show (nb078_alpha_dummy_150 f) ≠ (nb078_alpha_dummy_154 f) from (by
          unfold
            nb078_alpha_dummy_154;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0141
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_147) ≠ (nb078_alpha_dummy_151)
        from (by
          unfold
            nb078_alpha_dummy_151;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0138)
                  0)))) (show (nb078_alpha_dummy_150 f) ≠ (nb078_alpha_dummy_152 f) from (by
          unfold
            nb078_alpha_dummy_152;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0139
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_147), (nb078_alpha_dummy_150 f)), ((nb078_alpha_dummy_146),
        (nb078_alpha_dummy_149 f)), ((nb078_alpha_dummy_145), (nb078_alpha_dummy_148 f)),
        ((nb078_alpha_dummy_143), (nb078_alpha_dummy_144 f)), ((nb078_alpha_dummy_139),
        (nb078_alpha_dummy_141 f)), ((nb078_alpha_dummy_140), (nb078_alpha_dummy_142 f)),
        ((nb078_alpha_dummy_165), (nb078_alpha_dummy_166 f)), ((nb078_alpha_dummy_163),
        (nb078_alpha_dummy_164 f)), ((nb078_alpha_dummy_132), (nb078_alpha_dummy_134 f)),
        ((nb078_alpha_dummy_131), (nb078_alpha_dummy_133 f)), ((nb078_alpha_dummy_161),
        (nb078_alpha_dummy_162 f)), ((nb078_alpha_dummy_135), (nb078_alpha_dummy_136 f)),
        ((nb078_alpha_dummy_090), (nb078_alpha_dummy_092 f)), ((nb078_alpha_dummy_089),
        (nb078_alpha_dummy_091 f)), ((nb078_alpha_dummy_093), (nb078_alpha_dummy_094 f)),
        ((nb078_alpha_dummy_011), (nb078_alpha_dummy_014 f)), ((nb078_alpha_dummy_010),
        (nb078_alpha_dummy_013 f)), ((nb078_alpha_dummy_009), (nb078_alpha_dummy_012 f)),
        ((nb078_alpha_dummy_015), (nb078_alpha_dummy_016 f)), ((nb078_alpha_dummy_007),
        (nb078_alpha_dummy_008 f)), ((nb078_alpha_dummy_005), (nb078_alpha_dummy_006 f)),
        ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)] (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq
                                        (TAlphaClass.cv (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_139))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb078_alpha_dummy_141 f))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.there (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_139))).fv ∪ ((syn_c1c)).fv) (by decide))
        (freshVar_injective (((Class.cv (nb078_alpha_dummy_141 f))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_146) ≠
        (nb078_alpha_dummy_157) from (by
          unfold
            nb078_alpha_dummy_157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0144)
                  0)))) (show (nb078_alpha_dummy_149 f) ≠ (nb078_alpha_dummy_158 f) from (by
          unfold
            nb078_alpha_dummy_158;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0145
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_146) ≠ (nb078_alpha_dummy_155)
        from (by
          unfold
            nb078_alpha_dummy_155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0142)
                  0)))) (show (nb078_alpha_dummy_149 f) ≠ (nb078_alpha_dummy_156 f) from (by
          unfold
            nb078_alpha_dummy_156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0143
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_139))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_141 f))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_146) ≠ (nb078_alpha_dummy_157)
        from (by
          unfold
            nb078_alpha_dummy_157;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0144)
                  0)))) (show (nb078_alpha_dummy_149 f) ≠ (nb078_alpha_dummy_158 f) from (by
          unfold
            nb078_alpha_dummy_158;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0145
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_146) ≠ (nb078_alpha_dummy_155)
        from (by
          unfold
            nb078_alpha_dummy_155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0142)
                  0)))) (show (nb078_alpha_dummy_149 f) ≠ (nb078_alpha_dummy_156 f) from (by
          unfold
            nb078_alpha_dummy_156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0143
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_139))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_141 f))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_147) ≠ (nb078_alpha_dummy_159) from (by
          unfold
            nb078_alpha_dummy_159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0148)
                  0)))) (show (nb078_alpha_dummy_150 f) ≠ (nb078_alpha_dummy_160 f) from (by
          unfold
            nb078_alpha_dummy_160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0149
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_147) ≠ (nb078_alpha_dummy_155)
        from (by
          unfold
            nb078_alpha_dummy_155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0146)
                  0)))) (show (nb078_alpha_dummy_150 f) ≠ (nb078_alpha_dummy_156 f) from (by
          unfold
            nb078_alpha_dummy_156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0147
                    f)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_147) ≠
        (nb078_alpha_dummy_159) from (by
          unfold
            nb078_alpha_dummy_159;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0148)
                  0)))) (show (nb078_alpha_dummy_150 f) ≠ (nb078_alpha_dummy_160 f) from (by
          unfold
            nb078_alpha_dummy_160;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0149
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_147) ≠ (nb078_alpha_dummy_155)
        from (by
          unfold
            nb078_alpha_dummy_155;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0146)
                  0)))) (show (nb078_alpha_dummy_150 f) ≠ (nb078_alpha_dummy_156 f) from (by
          unfold
            nb078_alpha_dummy_156;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0147
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb078_alpha_dummy_139) ≠ (nb078_alpha_dummy_143) from (by
                                  unfold nb078_alpha_dummy_143;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0130) 0))))
                              (show (nb078_alpha_dummy_141 f) ≠ (nb078_alpha_dummy_144 f) from
                                (by
                                  unfold nb078_alpha_dummy_144;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0131 f) 0))))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                            [((nb078_alpha_dummy_143), (nb078_alpha_dummy_144 f)),
                              ((nb078_alpha_dummy_139), (nb078_alpha_dummy_141 f)),
                              ((nb078_alpha_dummy_140), (nb078_alpha_dummy_142 f)),
                              ((nb078_alpha_dummy_165), (nb078_alpha_dummy_166 f)),
                              ((nb078_alpha_dummy_163), (nb078_alpha_dummy_164 f)),
                              ((nb078_alpha_dummy_132), (nb078_alpha_dummy_134 f)),
                              ((nb078_alpha_dummy_131), (nb078_alpha_dummy_133 f)),
                              ((nb078_alpha_dummy_161), (nb078_alpha_dummy_162 f)),
                              ((nb078_alpha_dummy_135), (nb078_alpha_dummy_136 f)),
                              ((nb078_alpha_dummy_090), (nb078_alpha_dummy_092 f)),
                              ((nb078_alpha_dummy_089), (nb078_alpha_dummy_091 f)),
                              ((nb078_alpha_dummy_093), (nb078_alpha_dummy_094 f)),
                              ((nb078_alpha_dummy_011), (nb078_alpha_dummy_014 f)),
                              ((nb078_alpha_dummy_010), (nb078_alpha_dummy_013 f)),
                              ((nb078_alpha_dummy_009), (nb078_alpha_dummy_012 f)),
                              ((nb078_alpha_dummy_015), (nb078_alpha_dummy_016 f)),
                              ((nb078_alpha_dummy_007), (nb078_alpha_dummy_008 f)),
                              ((nb078_alpha_dummy_005), (nb078_alpha_dummy_006 f)),
                              ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y),
                              ((nb078_alpha_dummy_003), x)]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb078_alpha_dummy_139) ≠ (nb078_alpha_dummy_143) from (by
                                unfold nb078_alpha_dummy_143;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0130) 0))))
                            (show (nb078_alpha_dummy_141 f) ≠ (nb078_alpha_dummy_144 f) from (by
                                unfold nb078_alpha_dummy_144;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0131 f) 0))))
                            (TAlphaVar.here _ _ _)))) (TAlphaWff.neg (TAlphaWff.classMem
                          (TAlphaClass.cv (TAlphaVar.there
                              (show (nb078_alpha_dummy_139) ≠ (nb078_alpha_dummy_143) from (by
                                  unfold nb078_alpha_dummy_143;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0130) 0))))
                              (show (nb078_alpha_dummy_141 f) ≠ (nb078_alpha_dummy_144 f) from
                                (by
                                  unfold nb078_alpha_dummy_144;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0131 f) 0))))
                              (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                            [((nb078_alpha_dummy_143), (nb078_alpha_dummy_144 f)),
                              ((nb078_alpha_dummy_139), (nb078_alpha_dummy_141 f)),
                              ((nb078_alpha_dummy_140), (nb078_alpha_dummy_142 f)),
                              ((nb078_alpha_dummy_165), (nb078_alpha_dummy_166 f)),
                              ((nb078_alpha_dummy_163), (nb078_alpha_dummy_164 f)),
                              ((nb078_alpha_dummy_132), (nb078_alpha_dummy_134 f)),
                              ((nb078_alpha_dummy_131), (nb078_alpha_dummy_133 f)),
                              ((nb078_alpha_dummy_161), (nb078_alpha_dummy_162 f)),
                              ((nb078_alpha_dummy_135), (nb078_alpha_dummy_136 f)),
                              ((nb078_alpha_dummy_090), (nb078_alpha_dummy_092 f)),
                              ((nb078_alpha_dummy_089), (nb078_alpha_dummy_091 f)),
                              ((nb078_alpha_dummy_093), (nb078_alpha_dummy_094 f)),
                              ((nb078_alpha_dummy_011), (nb078_alpha_dummy_014 f)),
                              ((nb078_alpha_dummy_010), (nb078_alpha_dummy_013 f)),
                              ((nb078_alpha_dummy_009), (nb078_alpha_dummy_012 f)),
                              ((nb078_alpha_dummy_015), (nb078_alpha_dummy_016 f)),
                              ((nb078_alpha_dummy_007), (nb078_alpha_dummy_008 f)),
                              ((nb078_alpha_dummy_005), (nb078_alpha_dummy_006 f)),
                              ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y),
                              ((nb078_alpha_dummy_003), x)]
                            (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C078C001Part040`. -/


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
noncomputable def nb078_split_alpha_0008 (x : Var) (y : Var) (f : Var) :
    TAlphaWff
      [((nb078_alpha_dummy_173), (nb078_alpha_dummy_174 f)),
        ((nb078_alpha_dummy_171), (nb078_alpha_dummy_172 f)),
        ((nb078_alpha_dummy_011), (nb078_alpha_dummy_014 f)),
        ((nb078_alpha_dummy_010), (nb078_alpha_dummy_013 f)),
        ((nb078_alpha_dummy_009), (nb078_alpha_dummy_012 f)),
        ((nb078_alpha_dummy_015), (nb078_alpha_dummy_016 f)),
        ((nb078_alpha_dummy_007), (nb078_alpha_dummy_008 f)),
        ((nb078_alpha_dummy_005), (nb078_alpha_dummy_006 f)),
        ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y),
        ((nb078_alpha_dummy_003), x)]
      (Wff.imp (Wff.classMem (Class.cv (nb078_alpha_dummy_173))
          (Class.cab (nb078_alpha_dummy_167)
            (syn_wrex (nb078_alpha_dummy_168) (Class.cv (nb078_alpha_dummy_011))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_167))
                (syn_cphi (Class.cv (nb078_alpha_dummy_168))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078_alpha_dummy_173)) (Class.cab (nb078_alpha_dummy_167)
              (syn_wrex (nb078_alpha_dummy_168) (Class.cv (nb078_alpha_dummy_011))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_167))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_168)))))))))
      (Wff.imp (Wff.classMem (Class.cv (nb078_alpha_dummy_174 f))
          (Class.cab (nb078_alpha_dummy_169 f)
            (syn_wrex (nb078_alpha_dummy_170 f) (Class.cv (nb078_alpha_dummy_014 f))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_169 f))
                (syn_cphi (Class.cv (nb078_alpha_dummy_170 f))))))) (Wff.neg
          (Wff.classMem (Class.cv (nb078_alpha_dummy_174 f))
            (Class.cab (nb078_alpha_dummy_169 f)
              (syn_wrex (nb078_alpha_dummy_170 f) (Class.cv (nb078_alpha_dummy_014 f))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_169 f))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_170 f))))))))) :=
  (TAlphaWff.imp (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.ex (TAlphaWff.conj
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                (TAlphaVar.there (show (nb078_alpha_dummy_011) ≠ (nb078_alpha_dummy_168) from
                    (by
                      unfold nb078_alpha_dummy_168;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0172) 1))))
                  (show (nb078_alpha_dummy_014 f) ≠ (nb078_alpha_dummy_170 f) from (by
                      unfold nb078_alpha_dummy_170;
                      with_reducible
                        exact
                          (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0174 f) 1))))
                  (TAlphaVar.there (show (nb078_alpha_dummy_011) ≠ (nb078_alpha_dummy_167) from
                      (by
                        unfold nb078_alpha_dummy_167;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0172) 0))))
                    (show (nb078_alpha_dummy_014 f) ≠ (nb078_alpha_dummy_169 f) from (by
                        unfold nb078_alpha_dummy_169;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_0174 f) 0)))) (TAlphaVar.there
                      (show (nb078_alpha_dummy_011) ≠ (nb078_alpha_dummy_173) from (by
                          unfold nb078_alpha_dummy_173;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0176) 0))))
                      (show (nb078_alpha_dummy_014 f) ≠ (nb078_alpha_dummy_174 f) from (by
                          unfold nb078_alpha_dummy_174;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0177 f) 0))))
                      (TAlphaVar.there
                        (show (nb078_alpha_dummy_011) ≠ (nb078_alpha_dummy_171) from (by
                            unfold nb078_alpha_dummy_171;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0173) 0))))
                        (show (nb078_alpha_dummy_014 f) ≠ (nb078_alpha_dummy_172 f) from (by
                            unfold nb078_alpha_dummy_172;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0175 f) 0))))
                        (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_011))).fv ∪
                      ((Class.cv (nb078_alpha_dummy_010))).fv) (by decide)) (freshVar_injective
                    (((Class.cv (nb078_alpha_dummy_014 f))).fv ∪
                      ((Class.cv (nb078_alpha_dummy_013 f))).fv) (by decide))
                  (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                    (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there
                          (show (nb078_alpha_dummy_168) ≠ (nb078_alpha_dummy_175) from (by
                              unfold nb078_alpha_dummy_175;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0178) 0))))
                          (show (nb078_alpha_dummy_170 f) ≠ (nb078_alpha_dummy_177 f) from (by
                              unfold nb078_alpha_dummy_177;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0179 f) 0))))
                          (TAlphaVar.there
                            (show (nb078_alpha_dummy_168) ≠ (nb078_alpha_dummy_176) from (by
                                unfold nb078_alpha_dummy_176;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0178) 1))))
                            (show (nb078_alpha_dummy_170 f) ≠ (nb078_alpha_dummy_178 f) from (by
                                unfold nb078_alpha_dummy_178;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0179 f) 1))))
                            (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                        (TAlphaVar.there
                          (freshVar_injective (((Class.cv (nb078_alpha_dummy_168))).fv)
                            (by decide))
                          (freshVar_injective (((Class.cv (nb078_alpha_dummy_170 f))).fv)
                            (by decide)) (TAlphaVar.here _ _ _))) (TAlphaClass.cab
                        (TAlphaWff.imp (TAlphaWff.neg (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                                      (TAlphaWff.classMem
                                        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_175) ≠ (nb078_alpha_dummy_182) from (by
          unfold nb078_alpha_dummy_182;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0182) 1)))) (show (nb078_alpha_dummy_177 f) ≠
        (nb078_alpha_dummy_185 f) from (by
          unfold nb078_alpha_dummy_185;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0183 f) 1)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_175) ≠ (nb078_alpha_dummy_181) from (by
          unfold nb078_alpha_dummy_181;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0182) 0)))) (show (nb078_alpha_dummy_177 f) ≠
        (nb078_alpha_dummy_184 f) from (by
          unfold nb078_alpha_dummy_184;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0183 f) 0)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_175) ≠ (nb078_alpha_dummy_179) from (by
          unfold nb078_alpha_dummy_179;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0180) 0)))) (show (nb078_alpha_dummy_177 f) ≠
        (nb078_alpha_dummy_180 f) from (by
          unfold nb078_alpha_dummy_180;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0181 f)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_183), (nb078_alpha_dummy_186 f)), ((nb078_alpha_dummy_182),
        (nb078_alpha_dummy_185 f)), ((nb078_alpha_dummy_181), (nb078_alpha_dummy_184 f)),
        ((nb078_alpha_dummy_179), (nb078_alpha_dummy_180 f)), ((nb078_alpha_dummy_175),
        (nb078_alpha_dummy_177 f)), ((nb078_alpha_dummy_176), (nb078_alpha_dummy_178 f)),
        ((nb078_alpha_dummy_168), (nb078_alpha_dummy_170 f)), ((nb078_alpha_dummy_167),
        (nb078_alpha_dummy_169 f)), ((nb078_alpha_dummy_173), (nb078_alpha_dummy_174 f)),
        ((nb078_alpha_dummy_171), (nb078_alpha_dummy_172 f)), ((nb078_alpha_dummy_011),
        (nb078_alpha_dummy_014 f)), ((nb078_alpha_dummy_010), (nb078_alpha_dummy_013 f)),
        ((nb078_alpha_dummy_009), (nb078_alpha_dummy_012 f)), ((nb078_alpha_dummy_015),
        (nb078_alpha_dummy_016 f)), ((nb078_alpha_dummy_007), (nb078_alpha_dummy_008 f)),
        ((nb078_alpha_dummy_005), (nb078_alpha_dummy_006 f)), ((nb078_alpha_dummy_000), f),
        ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)]
        (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_182) ≠ (nb078_alpha_dummy_189) from (by
          unfold
            nb078_alpha_dummy_189;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0186)
                  0)))) (show (nb078_alpha_dummy_185 f) ≠ (nb078_alpha_dummy_190 f) from (by
          unfold
            nb078_alpha_dummy_190;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0187
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_182) ≠ (nb078_alpha_dummy_187)
        from (by
          unfold
            nb078_alpha_dummy_187;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0184)
                  0)))) (show (nb078_alpha_dummy_185 f) ≠ (nb078_alpha_dummy_188 f) from (by
          unfold
            nb078_alpha_dummy_188;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0185
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_175))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_177 f))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_183) ≠ (nb078_alpha_dummy_189)
        from (by
          unfold
            nb078_alpha_dummy_189;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0190)
                  0)))) (show (nb078_alpha_dummy_186 f) ≠ (nb078_alpha_dummy_190 f) from (by
          unfold
            nb078_alpha_dummy_190;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0191
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_183) ≠ (nb078_alpha_dummy_187)
        from (by
          unfold
            nb078_alpha_dummy_187;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0188)
                  0)))) (show (nb078_alpha_dummy_186 f) ≠ (nb078_alpha_dummy_188 f) from (by
          unfold
            nb078_alpha_dummy_188;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0189
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_182) ≠ (nb078_alpha_dummy_189) from (by
          unfold
            nb078_alpha_dummy_189;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0186)
                  0)))) (show (nb078_alpha_dummy_185 f) ≠ (nb078_alpha_dummy_190 f) from (by
          unfold
            nb078_alpha_dummy_190;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0187
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_182) ≠ (nb078_alpha_dummy_187)
        from (by
          unfold
            nb078_alpha_dummy_187;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0184)
                  0)))) (show (nb078_alpha_dummy_185 f) ≠ (nb078_alpha_dummy_188 f) from (by
          unfold
            nb078_alpha_dummy_188;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0185
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_175))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_177 f))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_183) ≠ (nb078_alpha_dummy_189)
        from (by
          unfold
            nb078_alpha_dummy_189;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0190)
                  0)))) (show (nb078_alpha_dummy_186 f) ≠ (nb078_alpha_dummy_190 f) from (by
          unfold
            nb078_alpha_dummy_190;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0191
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_183) ≠ (nb078_alpha_dummy_187)
        from (by
          unfold
            nb078_alpha_dummy_187;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0188)
                  0)))) (show (nb078_alpha_dummy_186 f) ≠ (nb078_alpha_dummy_188 f) from (by
          unfold
            nb078_alpha_dummy_188;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0189
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_183), (nb078_alpha_dummy_186 f)), ((nb078_alpha_dummy_182),
        (nb078_alpha_dummy_185 f)), ((nb078_alpha_dummy_181), (nb078_alpha_dummy_184 f)),
        ((nb078_alpha_dummy_179), (nb078_alpha_dummy_180 f)), ((nb078_alpha_dummy_175),
        (nb078_alpha_dummy_177 f)), ((nb078_alpha_dummy_176), (nb078_alpha_dummy_178 f)),
        ((nb078_alpha_dummy_168), (nb078_alpha_dummy_170 f)), ((nb078_alpha_dummy_167),
        (nb078_alpha_dummy_169 f)), ((nb078_alpha_dummy_173), (nb078_alpha_dummy_174 f)),
        ((nb078_alpha_dummy_171), (nb078_alpha_dummy_172 f)), ((nb078_alpha_dummy_011),
        (nb078_alpha_dummy_014 f)), ((nb078_alpha_dummy_010), (nb078_alpha_dummy_013 f)),
        ((nb078_alpha_dummy_009), (nb078_alpha_dummy_012 f)), ((nb078_alpha_dummy_015),
        (nb078_alpha_dummy_016 f)), ((nb078_alpha_dummy_007), (nb078_alpha_dummy_008 f)),
        ((nb078_alpha_dummy_005), (nb078_alpha_dummy_006 f)), ((nb078_alpha_dummy_000), f),
        ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_175))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_177 f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there
        (freshVar_injective (((Class.cv (nb078_alpha_dummy_175))).fv ∪ ((syn_c1c)).fv)
        (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_177 f))).fv ∪
        ((syn_c1c)).fv) (by decide)) (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg
        (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_182) ≠
        (nb078_alpha_dummy_193) from (by
          unfold
            nb078_alpha_dummy_193;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0194)
                  0)))) (show (nb078_alpha_dummy_185 f) ≠ (nb078_alpha_dummy_194 f) from (by
          unfold
            nb078_alpha_dummy_194;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0195
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_182) ≠ (nb078_alpha_dummy_191)
        from (by
          unfold
            nb078_alpha_dummy_191;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0192)
                  0)))) (show (nb078_alpha_dummy_185 f) ≠ (nb078_alpha_dummy_192 f) from (by
          unfold
            nb078_alpha_dummy_192;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0193
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_175))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_177 f))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_182) ≠ (nb078_alpha_dummy_193)
        from (by
          unfold
            nb078_alpha_dummy_193;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0194)
                  0)))) (show (nb078_alpha_dummy_185 f) ≠ (nb078_alpha_dummy_194 f) from (by
          unfold
            nb078_alpha_dummy_194;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0195
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_182) ≠ (nb078_alpha_dummy_191)
        from (by
          unfold
            nb078_alpha_dummy_191;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0192)
                  0)))) (show (nb078_alpha_dummy_185 f) ≠ (nb078_alpha_dummy_192 f) from (by
          unfold
            nb078_alpha_dummy_192;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0193
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_175))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_177 f))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_183) ≠ (nb078_alpha_dummy_195) from (by
          unfold
            nb078_alpha_dummy_195;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0198)
                  0)))) (show (nb078_alpha_dummy_186 f) ≠ (nb078_alpha_dummy_196 f) from (by
          unfold
            nb078_alpha_dummy_196;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0199
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_183) ≠ (nb078_alpha_dummy_191)
        from (by
          unfold
            nb078_alpha_dummy_191;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0196)
                  0)))) (show (nb078_alpha_dummy_186 f) ≠ (nb078_alpha_dummy_192 f) from (by
          unfold
            nb078_alpha_dummy_192;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0197
                    f)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_183) ≠
        (nb078_alpha_dummy_195) from (by
          unfold
            nb078_alpha_dummy_195;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0198)
                  0)))) (show (nb078_alpha_dummy_186 f) ≠ (nb078_alpha_dummy_196 f) from (by
          unfold
            nb078_alpha_dummy_196;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0199
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_183) ≠ (nb078_alpha_dummy_191)
        from (by
          unfold
            nb078_alpha_dummy_191;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0196)
                  0)))) (show (nb078_alpha_dummy_186 f) ≠ (nb078_alpha_dummy_192 f) from (by
          unfold
            nb078_alpha_dummy_192;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0197
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078_alpha_dummy_175) ≠ (nb078_alpha_dummy_179) from (by
                                        unfold nb078_alpha_dummy_179;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0180)
                                                0)))) (show (nb078_alpha_dummy_177 f) ≠
                                        (nb078_alpha_dummy_180 f) from (by
                                        unfold nb078_alpha_dummy_180;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0181 f)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
                                  [((nb078_alpha_dummy_179), (nb078_alpha_dummy_180 f)),
                                    ((nb078_alpha_dummy_175), (nb078_alpha_dummy_177 f)),
                                    ((nb078_alpha_dummy_176), (nb078_alpha_dummy_178 f)),
                                    ((nb078_alpha_dummy_168), (nb078_alpha_dummy_170 f)),
                                    ((nb078_alpha_dummy_167), (nb078_alpha_dummy_169 f)),
                                    ((nb078_alpha_dummy_173), (nb078_alpha_dummy_174 f)),
                                    ((nb078_alpha_dummy_171), (nb078_alpha_dummy_172 f)),
                                    ((nb078_alpha_dummy_011), (nb078_alpha_dummy_014 f)),
                                    ((nb078_alpha_dummy_010), (nb078_alpha_dummy_013 f)),
                                    ((nb078_alpha_dummy_009), (nb078_alpha_dummy_012 f)),
                                    ((nb078_alpha_dummy_015), (nb078_alpha_dummy_016 f)),
                                    ((nb078_alpha_dummy_007), (nb078_alpha_dummy_008 f)),
                                    ((nb078_alpha_dummy_005), (nb078_alpha_dummy_006 f)),
                                    ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y),
                                    ((nb078_alpha_dummy_003), x)]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                              (TAlphaClass.cv (TAlphaVar.there
                                  (show (nb078_alpha_dummy_175) ≠ (nb078_alpha_dummy_179) from
                                    (by
                                      unfold nb078_alpha_dummy_179;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0180)
                                              0)))) (show
                                    (nb078_alpha_dummy_177 f) ≠ (nb078_alpha_dummy_180 f) from
                                    (by
                                      unfold nb078_alpha_dummy_180;
                                      with_reducible
                                        exact
                                          (Nat.ne_of_lt
                                            (mem_lt_freshVar (nb078_support_mem_0181 f)
                                              0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078_alpha_dummy_175) ≠ (nb078_alpha_dummy_179) from (by
                                        unfold nb078_alpha_dummy_179;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0180)
                                                0)))) (show (nb078_alpha_dummy_177 f) ≠
                                        (nb078_alpha_dummy_180 f) from (by
                                        unfold nb078_alpha_dummy_180;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0181 f)
                                                0)))) (TAlphaVar.here _ _ _)))
                                (TAlphaClass.refl_of_closed
                                  [((nb078_alpha_dummy_179), (nb078_alpha_dummy_180 f)),
                                    ((nb078_alpha_dummy_175), (nb078_alpha_dummy_177 f)),
                                    ((nb078_alpha_dummy_176), (nb078_alpha_dummy_178 f)),
                                    ((nb078_alpha_dummy_168), (nb078_alpha_dummy_170 f)),
                                    ((nb078_alpha_dummy_167), (nb078_alpha_dummy_169 f)),
                                    ((nb078_alpha_dummy_173), (nb078_alpha_dummy_174 f)),
                                    ((nb078_alpha_dummy_171), (nb078_alpha_dummy_172 f)),
                                    ((nb078_alpha_dummy_011), (nb078_alpha_dummy_014 f)),
                                    ((nb078_alpha_dummy_010), (nb078_alpha_dummy_013 f)),
                                    ((nb078_alpha_dummy_009), (nb078_alpha_dummy_012 f)),
                                    ((nb078_alpha_dummy_015), (nb078_alpha_dummy_016 f)),
                                    ((nb078_alpha_dummy_007), (nb078_alpha_dummy_008 f)),
                                    ((nb078_alpha_dummy_005), (nb078_alpha_dummy_006 f)),
                                    ((nb078_alpha_dummy_000), f), ((nb078_alpha_dummy_004), y),
                                    ((nb078_alpha_dummy_003), x)]
                                  (syn_cnnc) (by simp only [fv_syn_cnnc]))))))))))))))))
    (TAlphaWff.neg (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
          (TAlphaWff.ex (TAlphaWff.conj
              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                  (TAlphaVar.there (show (nb078_alpha_dummy_011) ≠ (nb078_alpha_dummy_168) from
                      (by
                        unfold nb078_alpha_dummy_168;
                        with_reducible
                          exact
                            (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_0172) 1))))
                    (show (nb078_alpha_dummy_014 f) ≠ (nb078_alpha_dummy_170 f) from (by
                        unfold nb078_alpha_dummy_170;
                        with_reducible
                          exact
                            (Nat.ne_of_lt
                              (mem_lt_freshVar (nb078_support_mem_0174 f) 1)))) (TAlphaVar.there
                      (show (nb078_alpha_dummy_011) ≠ (nb078_alpha_dummy_167) from (by
                          unfold nb078_alpha_dummy_167;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0172) 0))))
                      (show (nb078_alpha_dummy_014 f) ≠ (nb078_alpha_dummy_169 f) from (by
                          unfold nb078_alpha_dummy_169;
                          with_reducible
                            exact
                              (Nat.ne_of_lt
                                (mem_lt_freshVar (nb078_support_mem_0174 f) 0))))
                      (TAlphaVar.there
                        (show (nb078_alpha_dummy_011) ≠ (nb078_alpha_dummy_173) from (by
                            unfold nb078_alpha_dummy_173;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0176) 0))))
                        (show (nb078_alpha_dummy_014 f) ≠ (nb078_alpha_dummy_174 f) from (by
                            unfold nb078_alpha_dummy_174;
                            with_reducible
                              exact
                                (Nat.ne_of_lt
                                  (mem_lt_freshVar (nb078_support_mem_0177 f) 0))))
                        (TAlphaVar.there
                          (show (nb078_alpha_dummy_011) ≠ (nb078_alpha_dummy_171) from (by
                              unfold nb078_alpha_dummy_171;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0173) 0))))
                          (show (nb078_alpha_dummy_014 f) ≠ (nb078_alpha_dummy_172 f) from (by
                              unfold nb078_alpha_dummy_172;
                              with_reducible
                                exact
                                  (Nat.ne_of_lt
                                    (mem_lt_freshVar (nb078_support_mem_0175 f) 0))))
                          (TAlphaVar.here _ _ _))))))) (TAlphaWff.classEq (TAlphaClass.cv
                  (TAlphaVar.there (freshVar_injective
                      (((Class.cv (nb078_alpha_dummy_011))).fv ∪
                        ((Class.cv (nb078_alpha_dummy_010))).fv) (by decide))
                    (freshVar_injective (((Class.cv (nb078_alpha_dummy_014 f))).fv ∪
                        ((Class.cv (nb078_alpha_dummy_013 f))).fv) (by decide))
                    (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj
                      (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                        (TAlphaClass.cv (TAlphaVar.there
                            (show (nb078_alpha_dummy_168) ≠ (nb078_alpha_dummy_175) from (by
                                unfold nb078_alpha_dummy_175;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0178) 0))))
                            (show (nb078_alpha_dummy_170 f) ≠ (nb078_alpha_dummy_177 f) from (by
                                unfold nb078_alpha_dummy_177;
                                with_reducible
                                  exact
                                    (Nat.ne_of_lt
                                      (mem_lt_freshVar (nb078_support_mem_0179 f) 0))))
                            (TAlphaVar.there
                              (show (nb078_alpha_dummy_168) ≠ (nb078_alpha_dummy_176) from (by
                                  unfold nb078_alpha_dummy_176;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0178) 1))))
                              (show (nb078_alpha_dummy_170 f) ≠ (nb078_alpha_dummy_178 f) from
                                (by
                                  unfold nb078_alpha_dummy_178;
                                  with_reducible
                                    exact
                                      (Nat.ne_of_lt
                                        (mem_lt_freshVar (nb078_support_mem_0179 f) 1))))
                              (TAlphaVar.here _ _ _))))) (TAlphaWff.classEq (TAlphaClass.cv
                          (TAlphaVar.there
                            (freshVar_injective (((Class.cv (nb078_alpha_dummy_168))).fv)
                              (by decide)) (freshVar_injective
                              (((Class.cv (nb078_alpha_dummy_170 f))).fv) (by decide))
                            (TAlphaVar.here _ _ _))) (TAlphaClass.cab (TAlphaWff.imp
                            (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                                    (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.classMem
        (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show
        (nb078_alpha_dummy_175) ≠ (nb078_alpha_dummy_182) from (by
          unfold nb078_alpha_dummy_182;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0182) 1)))) (show (nb078_alpha_dummy_177 f) ≠
        (nb078_alpha_dummy_185 f) from (by
          unfold nb078_alpha_dummy_185;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0183 f) 1)))) (TAlphaVar.there (show
        (nb078_alpha_dummy_175) ≠ (nb078_alpha_dummy_181) from (by
          unfold nb078_alpha_dummy_181;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0182) 0)))) (show (nb078_alpha_dummy_177 f) ≠
        (nb078_alpha_dummy_184 f) from (by
          unfold nb078_alpha_dummy_184;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0183 f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_175) ≠ (nb078_alpha_dummy_179)
        from (by
          unfold nb078_alpha_dummy_179;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0180)
                  0)))) (show (nb078_alpha_dummy_177 f) ≠ (nb078_alpha_dummy_180 f) from (by
          unfold nb078_alpha_dummy_180;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0181 f)
                  0)))) (TAlphaVar.here _ _ _)))))) (TAlphaWff.ex (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_183), (nb078_alpha_dummy_186 f)), ((nb078_alpha_dummy_182),
        (nb078_alpha_dummy_185 f)), ((nb078_alpha_dummy_181), (nb078_alpha_dummy_184 f)),
        ((nb078_alpha_dummy_179), (nb078_alpha_dummy_180 f)), ((nb078_alpha_dummy_175),
        (nb078_alpha_dummy_177 f)), ((nb078_alpha_dummy_176), (nb078_alpha_dummy_178 f)),
        ((nb078_alpha_dummy_168), (nb078_alpha_dummy_170 f)), ((nb078_alpha_dummy_167),
        (nb078_alpha_dummy_169 f)), ((nb078_alpha_dummy_173), (nb078_alpha_dummy_174 f)),
        ((nb078_alpha_dummy_171), (nb078_alpha_dummy_172 f)), ((nb078_alpha_dummy_011),
        (nb078_alpha_dummy_014 f)), ((nb078_alpha_dummy_010), (nb078_alpha_dummy_013 f)),
        ((nb078_alpha_dummy_009), (nb078_alpha_dummy_012 f)), ((nb078_alpha_dummy_015),
        (nb078_alpha_dummy_016 f)), ((nb078_alpha_dummy_007), (nb078_alpha_dummy_008 f)),
        ((nb078_alpha_dummy_005), (nb078_alpha_dummy_006 f)), ((nb078_alpha_dummy_000), f),
        ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)]
        (syn_c1c) (by simp only [fv_syn_c1c]))) (TAlphaWff.conj (TAlphaWff.classEq
        (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_182) ≠ (nb078_alpha_dummy_189) from (by
          unfold
            nb078_alpha_dummy_189;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0186)
                  0)))) (show (nb078_alpha_dummy_185 f) ≠ (nb078_alpha_dummy_190 f) from (by
          unfold
            nb078_alpha_dummy_190;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0187
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_182) ≠ (nb078_alpha_dummy_187)
        from (by
          unfold
            nb078_alpha_dummy_187;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0184)
                  0)))) (show (nb078_alpha_dummy_185 f) ≠ (nb078_alpha_dummy_188 f) from (by
          unfold
            nb078_alpha_dummy_188;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0185
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_175))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_177 f))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_183) ≠ (nb078_alpha_dummy_189)
        from (by
          unfold
            nb078_alpha_dummy_189;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0190)
                  0)))) (show (nb078_alpha_dummy_186 f) ≠ (nb078_alpha_dummy_190 f) from (by
          unfold
            nb078_alpha_dummy_190;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0191
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_183) ≠ (nb078_alpha_dummy_187)
        from (by
          unfold
            nb078_alpha_dummy_187;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0188)
                  0)))) (show (nb078_alpha_dummy_186 f) ≠ (nb078_alpha_dummy_188 f) from (by
          unfold
            nb078_alpha_dummy_188;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0189
                    f)
                  0)))) (TAlphaVar.here _ _ _))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_182) ≠ (nb078_alpha_dummy_189) from (by
          unfold
            nb078_alpha_dummy_189;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0186)
                  0)))) (show (nb078_alpha_dummy_185 f) ≠ (nb078_alpha_dummy_190 f) from (by
          unfold
            nb078_alpha_dummy_190;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0187
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_182) ≠ (nb078_alpha_dummy_187)
        from (by
          unfold
            nb078_alpha_dummy_187;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0184)
                  0)))) (show (nb078_alpha_dummy_185 f) ≠ (nb078_alpha_dummy_188 f) from (by
          unfold
            nb078_alpha_dummy_188;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0185
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_175))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_177 f))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_183) ≠ (nb078_alpha_dummy_189)
        from (by
          unfold
            nb078_alpha_dummy_189;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0190)
                  0)))) (show (nb078_alpha_dummy_186 f) ≠ (nb078_alpha_dummy_190 f) from (by
          unfold
            nb078_alpha_dummy_190;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0191
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_183) ≠ (nb078_alpha_dummy_187)
        from (by
          unfold
            nb078_alpha_dummy_187;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0188)
                  0)))) (show (nb078_alpha_dummy_186 f) ≠ (nb078_alpha_dummy_188 f) from (by
          unfold
            nb078_alpha_dummy_188;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0189
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))) (TAlphaClass.refl_of_closed
        [((nb078_alpha_dummy_183), (nb078_alpha_dummy_186 f)), ((nb078_alpha_dummy_182),
        (nb078_alpha_dummy_185 f)), ((nb078_alpha_dummy_181), (nb078_alpha_dummy_184 f)),
        ((nb078_alpha_dummy_179), (nb078_alpha_dummy_180 f)), ((nb078_alpha_dummy_175),
        (nb078_alpha_dummy_177 f)), ((nb078_alpha_dummy_176), (nb078_alpha_dummy_178 f)),
        ((nb078_alpha_dummy_168), (nb078_alpha_dummy_170 f)), ((nb078_alpha_dummy_167),
        (nb078_alpha_dummy_169 f)), ((nb078_alpha_dummy_173), (nb078_alpha_dummy_174 f)),
        ((nb078_alpha_dummy_171), (nb078_alpha_dummy_172 f)), ((nb078_alpha_dummy_011),
        (nb078_alpha_dummy_014 f)), ((nb078_alpha_dummy_010), (nb078_alpha_dummy_013 f)),
        ((nb078_alpha_dummy_009), (nb078_alpha_dummy_012 f)), ((nb078_alpha_dummy_015),
        (nb078_alpha_dummy_016 f)), ((nb078_alpha_dummy_007), (nb078_alpha_dummy_008 f)),
        ((nb078_alpha_dummy_005), (nb078_alpha_dummy_006 f)), ((nb078_alpha_dummy_000), f),
        ((nb078_alpha_dummy_004), y), ((nb078_alpha_dummy_003), x)]
        (syn_c0) (by simp only [fv_syn_c0]))) (TAlphaWff.classEq (TAlphaClass.cv
        (TAlphaVar.there (freshVar_injective (((Class.cv (nb078_alpha_dummy_175))).fv ∪
        ((syn_c1c)).fv) (by decide)) (freshVar_injective (((Class.cv (nb078_alpha_dummy_177
        f))).fv ∪ ((syn_c1c)).fv) (by decide)) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_175))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_177 f))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
        (TAlphaWff.neg (TAlphaWff.conj (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_182) ≠
        (nb078_alpha_dummy_193) from (by
          unfold
            nb078_alpha_dummy_193;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0194)
                  0)))) (show (nb078_alpha_dummy_185 f) ≠ (nb078_alpha_dummy_194 f) from (by
          unfold
            nb078_alpha_dummy_194;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0195
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_182) ≠ (nb078_alpha_dummy_191)
        from (by
          unfold
            nb078_alpha_dummy_191;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0192)
                  0)))) (show (nb078_alpha_dummy_185 f) ≠ (nb078_alpha_dummy_192 f) from (by
          unfold
            nb078_alpha_dummy_192;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0193
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_175))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_177 f))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))) (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
        (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_182) ≠ (nb078_alpha_dummy_193)
        from (by
          unfold
            nb078_alpha_dummy_193;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0194)
                  0)))) (show (nb078_alpha_dummy_185 f) ≠ (nb078_alpha_dummy_194 f) from (by
          unfold
            nb078_alpha_dummy_194;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0195
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_182) ≠ (nb078_alpha_dummy_191)
        from (by
          unfold
            nb078_alpha_dummy_191;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0192)
                  0)))) (show (nb078_alpha_dummy_185 f) ≠ (nb078_alpha_dummy_192 f) from (by
          unfold
            nb078_alpha_dummy_192;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0193
                    f)
                  0)))) (TAlphaVar.there (freshVar_injective (((Class.cv
        (nb078_alpha_dummy_175))).fv ∪ ((syn_c1c)).fv) (by decide)) (freshVar_injective
        (((Class.cv (nb078_alpha_dummy_177 f))).fv ∪ ((syn_c1c)).fv) (by decide))
        (TAlphaVar.here _ _ _)))))))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cab (TAlphaWff.neg (TAlphaWff.conj
        (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
        (TAlphaVar.there (show (nb078_alpha_dummy_183) ≠ (nb078_alpha_dummy_195) from (by
          unfold
            nb078_alpha_dummy_195;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0198)
                  0)))) (show (nb078_alpha_dummy_186 f) ≠ (nb078_alpha_dummy_196 f) from (by
          unfold
            nb078_alpha_dummy_196;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0199
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_183) ≠ (nb078_alpha_dummy_191)
        from (by
          unfold
            nb078_alpha_dummy_191;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0196)
                  0)))) (show (nb078_alpha_dummy_186 f) ≠ (nb078_alpha_dummy_192 f) from (by
          unfold
            nb078_alpha_dummy_192;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0197
                    f)
                  0)))) (TAlphaVar.here _ _ _))))) (TAlphaWff.classMem (TAlphaClass.cv
        (TAlphaVar.here _ _ _)) (TAlphaClass.cv (TAlphaVar.there (show (nb078_alpha_dummy_183) ≠
        (nb078_alpha_dummy_195) from (by
          unfold
            nb078_alpha_dummy_195;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0198)
                  0)))) (show (nb078_alpha_dummy_186 f) ≠ (nb078_alpha_dummy_196 f) from (by
          unfold
            nb078_alpha_dummy_196;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0199
                    f)
                  0)))) (TAlphaVar.there (show (nb078_alpha_dummy_183) ≠ (nb078_alpha_dummy_191)
        from (by
          unfold
            nb078_alpha_dummy_191;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0196)
                  0)))) (show (nb078_alpha_dummy_186 f) ≠ (nb078_alpha_dummy_192 f) from (by
          unfold
            nb078_alpha_dummy_192;
          with_reducible
            exact
              (Nat.ne_of_lt
                (mem_lt_freshVar
                  (nb078_support_mem_0197
                    f)
                  0)))) (TAlphaVar.here _ _ _)))))))))))))))))))) (TAlphaWff.classMem
                                  (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb078_alpha_dummy_175) ≠ (nb078_alpha_dummy_179) from
                                        (by
                                          unfold nb078_alpha_dummy_179;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0180)
                                                  0)))) (show (nb078_alpha_dummy_177 f) ≠
        (nb078_alpha_dummy_180 f) from (by
                                          unfold nb078_alpha_dummy_180;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0181 f) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb078_alpha_dummy_179), (nb078_alpha_dummy_180 f)),
                                      ((nb078_alpha_dummy_175), (nb078_alpha_dummy_177 f)),
                                      ((nb078_alpha_dummy_176), (nb078_alpha_dummy_178 f)),
                                      ((nb078_alpha_dummy_168), (nb078_alpha_dummy_170 f)),
                                      ((nb078_alpha_dummy_167), (nb078_alpha_dummy_169 f)),
                                      ((nb078_alpha_dummy_173), (nb078_alpha_dummy_174 f)),
                                      ((nb078_alpha_dummy_171), (nb078_alpha_dummy_172 f)),
                                      ((nb078_alpha_dummy_011), (nb078_alpha_dummy_014 f)),
                                      ((nb078_alpha_dummy_010), (nb078_alpha_dummy_013 f)),
                                      ((nb078_alpha_dummy_009), (nb078_alpha_dummy_012 f)),
                                      ((nb078_alpha_dummy_015), (nb078_alpha_dummy_016 f)),
                                      ((nb078_alpha_dummy_007), (nb078_alpha_dummy_008 f)),
                                      ((nb078_alpha_dummy_005), (nb078_alpha_dummy_006 f)),
                                      ((nb078_alpha_dummy_000), f),
                                      ((nb078_alpha_dummy_004), y),
                                      ((nb078_alpha_dummy_003), x)]
                                    (syn_cnnc) (by simp only [fv_syn_cnnc]))))) (TAlphaWff.conj
                              (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _))
                                (TAlphaClass.cv (TAlphaVar.there (show
                                      (nb078_alpha_dummy_175) ≠ (nb078_alpha_dummy_179) from (by
                                        unfold nb078_alpha_dummy_179;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0180)
                                                0)))) (show (nb078_alpha_dummy_177 f) ≠
                                        (nb078_alpha_dummy_180 f) from (by
                                        unfold nb078_alpha_dummy_180;
                                        with_reducible
                                          exact
                                            (Nat.ne_of_lt
                                              (mem_lt_freshVar (nb078_support_mem_0181 f)
                                                0)))) (TAlphaVar.here _ _ _)))) (TAlphaWff.neg
                                (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.there (show
                                        (nb078_alpha_dummy_175) ≠ (nb078_alpha_dummy_179) from
                                        (by
                                          unfold nb078_alpha_dummy_179;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar (nb078_support_mem_0180)
                                                  0)))) (show (nb078_alpha_dummy_177 f) ≠
        (nb078_alpha_dummy_180 f) from (by
                                          unfold nb078_alpha_dummy_180;
                                          with_reducible
                                            exact
                                              (Nat.ne_of_lt
                                                (mem_lt_freshVar
                                                  (nb078_support_mem_0181 f) 0))))
                                      (TAlphaVar.here _ _ _))) (TAlphaClass.refl_of_closed
                                    [((nb078_alpha_dummy_179), (nb078_alpha_dummy_180 f)),
                                      ((nb078_alpha_dummy_175), (nb078_alpha_dummy_177 f)),
                                      ((nb078_alpha_dummy_176), (nb078_alpha_dummy_178 f)),
                                      ((nb078_alpha_dummy_168), (nb078_alpha_dummy_170 f)),
                                      ((nb078_alpha_dummy_167), (nb078_alpha_dummy_169 f)),
                                      ((nb078_alpha_dummy_173), (nb078_alpha_dummy_174 f)),
                                      ((nb078_alpha_dummy_171), (nb078_alpha_dummy_172 f)),
                                      ((nb078_alpha_dummy_011), (nb078_alpha_dummy_014 f)),
                                      ((nb078_alpha_dummy_010), (nb078_alpha_dummy_013 f)),
                                      ((nb078_alpha_dummy_009), (nb078_alpha_dummy_012 f)),
                                      ((nb078_alpha_dummy_015), (nb078_alpha_dummy_016 f)),
                                      ((nb078_alpha_dummy_007), (nb078_alpha_dummy_008 f)),
                                      ((nb078_alpha_dummy_005), (nb078_alpha_dummy_006 f)),
                                      ((nb078_alpha_dummy_000), f),
                                      ((nb078_alpha_dummy_004), y),
                                      ((nb078_alpha_dummy_003), x)] (syn_cnnc)
                                    (by simp only [fv_syn_cnnc]))))))))))))))))))


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
